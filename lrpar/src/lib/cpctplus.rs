use std::{
    cmp::Ordering,
    collections::HashSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    time::Instant,
};

use cactus::Cactus;
use cfgrammar::TIdx;
use lrtable::{Action, StIdx};
use num_traits::{AsPrimitive, PrimInt, Unsigned};

use super::{
    dijkstra::dijkstra,
    parser::{AStackType, ParseRepair, Parser, Recoverer},
    Lexeme, Span,
};

const PARSE_AT_LEAST: usize = 3; // N in Corchuelo et al.
const TRY_PARSE_AT_MOST: usize = 250;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Repair<StorageT> {
    /// Insert a `Symbol::Token` with idx `token_idx`.
    InsertTerm(TIdx<StorageT>),
    /// Delete a symbol.
    Delete,
    /// Shift a symbol.
    Shift,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RepairMerge<StorageT> {
    Repair(Repair<StorageT>),
    Merge(Repair<StorageT>, Cactus<Cactus<RepairMerge<StorageT>>>),
    Terminator,
}

#[derive(Clone, Debug)]
struct PathFNode<StorageT> {
    pstack: Cactus<StIdx>,
    laidx: usize,
    repairs: Cactus<RepairMerge<StorageT>>,
    cf: u16,
}

impl<StorageT: PrimInt + Unsigned> PathFNode<StorageT> {
    fn last_repair(&self) -> Option<Repair<StorageT>> {
        match *self.repairs.val().unwrap() {
            RepairMerge::Repair(r) => Some(r),
            RepairMerge::Merge(x, _) => Some(x),
            RepairMerge::Terminator => None,
        }
    }
}

impl<StorageT: PrimInt + Unsigned> Hash for PathFNode<StorageT> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.pstack.hash(state);
        self.laidx.hash(state);
    }
}

impl<StorageT: PrimInt + Unsigned> PartialEq for PathFNode<StorageT> {
    fn eq(&self, other: &PathFNode<StorageT>) -> bool {
        if self.laidx != other.laidx || self.pstack != other.pstack {
            return false;
        }
        // The rest of this function is subtle: we're not looking for repair sequences which are
        // exactly equivalent, but ones that are compatible. This is necessary so that we can merge
        // compatible nodes. Our definition of compatible repair sequences is: they must end with
        // exactly the same number of shifts (ending with zero shifts is fine); and if one repair
        // sequence ends in a delete, the other must do so as well.

        match (self.last_repair(), other.last_repair()) {
            (Some(Repair::Delete), Some(Repair::Delete)) => (),
            (Some(Repair::Delete), _) | (_, Some(Repair::Delete)) => return false,
            (_, _) => (),
        }

        let num_shifts = |c: &Cactus<RepairMerge<StorageT>>| {
            let mut n = 0;
            for r in c.vals() {
                match *r {
                    RepairMerge::Repair(Repair::Shift) | RepairMerge::Merge(Repair::Shift, _) => {
                        n += 1
                    }
                    _ => break,
                }
            }
            n
        };
        let self_shifts = num_shifts(&self.repairs);
        let other_shifts = num_shifts(&other.repairs);
        self_shifts == other_shifts
    }
}

impl<StorageT: PrimInt + Unsigned> Eq for PathFNode<StorageT> {}

struct CPCTPlus<
    'a,
    'b: 'a,
    'input: 'b,
    LexemeT: Lexeme<StorageT>,
    StorageT: 'static + Eq + Hash,
    ActionT: 'a,
    ParamT: Copy,
> {
    parser: &'a Parser<'a, 'b, 'input, LexemeT, StorageT, ActionT, ParamT>,
}

pub(super) fn recoverer<
    'a,
    LexemeT: Lexeme<StorageT>,
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    ActionT: 'a,
    ParamT: Copy,
>(
    parser: &'a Parser<LexemeT, StorageT, ActionT, ParamT>,
) -> Box<dyn Recoverer<LexemeT, StorageT, ActionT, ParamT> + 'a>
where
    usize: AsPrimitive<StorageT>,
{
    Box::new(CPCTPlus { parser })
}

impl<
        'a,
        'b: 'a,
        'input: 'b,
        LexemeT: Lexeme<StorageT>,
        StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
        ActionT: 'a,
        ParamT: Copy,
    > Recoverer<LexemeT, StorageT, ActionT, ParamT>
    for CPCTPlus<'a, 'b, 'input, LexemeT, StorageT, ActionT, ParamT>
where
    usize: AsPrimitive<StorageT>,
{
    fn recover(
        &self,
        finish_by: Instant,
        parser: &Parser<LexemeT, StorageT, ActionT, ParamT>,
        in_laidx: usize,
        in_pstack: &mut Vec<StIdx>,
        astack: &mut Vec<AStackType<LexemeT, ActionT>>,
        spans: &mut Vec<Span>,
    ) -> (usize, Vec<Vec<ParseRepair<LexemeT, StorageT>>>) {
        // This function implements a minor variant of the algorithm from "Repairing syntax errors
        // in LR parsers" by Rafael Corchuelo, Jose A. Perez, Antonio Ruiz, and Miguel Toro.
        //
        // The major differences are: we change the shift() function (see the comment therein)
        // along the lines suggested by KimYi; and we simplify the criteria for a successful node
        // (since the numbers in the Corchuelo paper don't scale well to arbitrary grammars).
        //
        // Because we want to create a parse tree even when error recovery has happened, we can be
        // a bit clever. In our first stage, we try and find repair sequences using a cactus stack
        // to represent the parse stack, but we don't try and create/alter the parse tree. Once
        // we've found valid repairs, we select one arbitrarily (as do Corchuelo) and then replay
        // it, this time turning on parse tree creation/alteration. Thus we only pay the costs of
        // creating the parse tree for the one parse that we need it. This has a vaguely similar
        // flavour to part of the ALL(*) algorithm (where, when the LL parser gets to a point of
        // ambiguity, it fires up non-LL sub-parsers, which then tell the LL parser which path it
        // should take).
        let mut start_cactus_pstack = Cactus::new();
        for st in in_pstack.iter() {
            start_cactus_pstack = start_cactus_pstack.child(*st);
        }

        let start_node = PathFNode {
            pstack: start_cactus_pstack,
            laidx: in_laidx,
            repairs: Cactus::new().child(RepairMerge::Terminator),
            cf: 0,
        };
        let astar_cnds = dijkstra(
            start_node,
            |explore_all, n, nbrs| {
                // Calculate n's neighbours.

                if Instant::now() >= finish_by {
                    return false;
                }

                match n.last_repair() {
                    Some(Repair::Delete) => {
                        // We follow Corcheulo et al.'s suggestions and never follow Deletes with
                        // Inserts.
                    }
                    _ => {
                        if explore_all {
                            self.insert(n, nbrs);
                        }
                    }
                }
                if explore_all {
                    self.delete(n, nbrs);
                }
                self.shift(n, nbrs);
                true
            },
            |old, new| {
                // merge new_n into old_n

                if old.repairs == new.repairs {
                    // If the repair sequences are identical, then merging is pointless.
                    return;
                }
                let merge = match *old.repairs.val().unwrap() {
                    RepairMerge::Repair(r) => {
                        RepairMerge::Merge(r, Cactus::new().child(new.repairs))
                    }
                    RepairMerge::Merge(r, ref v) => RepairMerge::Merge(r, v.child(new.repairs)),
                    _ => unreachable!(),
                };
                old.repairs = old.repairs.parent().unwrap().child(merge);
            },
            |n| {
                // Is n a success node?

                // As presented in both Corchuelo et al. and Kim Yi, one type of success is if N
                // symbols are parsed in one go. Indeed, without such a check, the search space
                // quickly becomes too big. There isn't a way of encoding this check in r3s_n, so
                // we check instead for its result: if the last N ('PARSE_AT_LEAST' in this
                // library) repairs are shifts, then we've found a success node.
                if ends_with_parse_at_least_shifts(&n.repairs) {
                    return true;
                }

                matches!(
                    parser
                        .stable
                        .action(*n.pstack.val().unwrap(), parser.next_tidx(n.laidx)),
                    Action::Accept
                )
            },
        );

        if astar_cnds.is_empty() {
            return (in_laidx, vec![]);
        }

        let full_rprs = self.collect_repairs(in_laidx, astar_cnds);
        let mut rnk_rprs = rank_cnds(parser, finish_by, in_laidx, in_pstack, full_rprs);
        if rnk_rprs.is_empty() {
            return (in_laidx, vec![]);
        }
        simplify_repairs(parser, &mut rnk_rprs);
        let laidx = apply_repairs(
            parser,
            in_laidx,
            in_pstack,
            &mut Some(astack),
            &mut Some(spans),
            &rnk_rprs[0],
        );

        (laidx, rnk_rprs)
    }
}

impl<
        'a,
        'b: 'a,
        'input: 'b,
        LexemeT: Lexeme<StorageT>,
        StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
        ActionT: 'a,
        ParamT: Copy,
    > CPCTPlus<'a, 'b, 'input, LexemeT, StorageT, ActionT, ParamT>
where
    usize: AsPrimitive<StorageT>,
{
    fn insert(&self, n: &PathFNode<StorageT>, nbrs: &mut Vec<(u16, PathFNode<StorageT>)>) {
        let laidx = n.laidx;
        for tidx in self.parser.stable.state_actions(*n.pstack.val().unwrap()) {
            if tidx == self.parser.grm.eof_token_idx() {
                continue;
            }

            let next_lexeme = self.parser.next_lexeme(n.laidx);
            let new_lexeme = Lexeme::new_faulty(
                StorageT::from(u32::from(tidx)).unwrap(),
                next_lexeme.span().start(),
                0,
            );
            let (new_laidx, n_pstack) = self.parser.lr_cactus(
                Some(new_lexeme),
                laidx,
                laidx + 1,
                n.pstack.clone(),
                &mut None,
            );
            if new_laidx > laidx {
                let nn = PathFNode {
                    pstack: n_pstack,
                    laidx: n.laidx,
                    repairs: n
                        .repairs
                        .child(RepairMerge::Repair(Repair::InsertTerm(tidx))),
                    cf: n
                        .cf
                        .checked_add(u16::from((self.parser.token_cost)(tidx)))
                        .unwrap(),
                };
                nbrs.push((nn.cf, nn));
            }
        }
    }

    fn delete(&self, n: &PathFNode<StorageT>, nbrs: &mut Vec<(u16, PathFNode<StorageT>)>) {
        if n.laidx == self.parser.lexemes.len() {
            return;
        }

        let la_tidx = self.parser.next_tidx(n.laidx);
        let cost = (self.parser.token_cost)(la_tidx);
        let nn = PathFNode {
            pstack: n.pstack.clone(),
            laidx: n.laidx + 1,
            repairs: n.repairs.child(RepairMerge::Repair(Repair::Delete)),
            cf: n.cf.checked_add(u16::from(cost)).unwrap(),
        };
        nbrs.push((nn.cf, nn));
    }

    fn shift(&self, n: &PathFNode<StorageT>, nbrs: &mut Vec<(u16, PathFNode<StorageT>)>) {
        // Forward move rule (ER3)
        //
        // Note the rule in Corchuelo et al. is confusing and, I think, wrong. It reads:
        //   (S, I) \rightarrow_{LR*} (S', I')
        //   \wedge (j = N \vee 0 < j < N \wedge f(q_r, t_{j + 1} \in {accept, error})
        // First I think the bracketing would be clearer if written as:
        //   j = N \vee (0 < j < N \wedge f(q_r, t_{j + 1} \in {accept, error})
        // And I think the condition should be:
        //   j = N \vee (0 <= j < N \wedge f(q_r, t_{j + 1} \in {accept, error})
        // because there's no reason that any symbols need to be shifted in order for an accept
        // (or, indeed an error) state to be reached.
        //
        // So the full rule should, I think, be:
        //   (S, I) \rightarrow_{LR*} (S', I')
        //   \wedge (j = N \vee (0 <= j < N \wedge f(q_r, t_{j + 1} \in {accept, error}))
        //
        // That said, as KimYi somewhat obliquely mention, generating multiple shifts in one go is
        // a bad idea: it means that we miss out on some minimal cost repairs. Instead, we should
        // only generate one shift at a time. So the adjusted rule we implement is:
        //
        //   (S, I) \rightarrow_{LR*} (S', I')
        //   \wedge 0 <= j < 1 \wedge S != S'

        let laidx = n.laidx;
        let (new_laidx, n_pstack) =
            self.parser
                .lr_cactus(None, laidx, laidx + 1, n.pstack.clone(), &mut None);
        if n.pstack != n_pstack {
            let n_repairs = if new_laidx > laidx {
                n.repairs.child(RepairMerge::Repair(Repair::Shift))
            } else {
                n.repairs.clone()
            };
            let nn = PathFNode {
                pstack: n_pstack,
                laidx: new_laidx,
                repairs: n_repairs,
                cf: n.cf,
            };
            nbrs.push((nn.cf, nn));
        }
    }

    /// Convert the output from `astar_all` into something more usable.
    fn collect_repairs(
        &self,
        in_laidx: usize,
        cnds: Vec<PathFNode<StorageT>>,
    ) -> Vec<Vec<Vec<ParseRepair<LexemeT, StorageT>>>> {
        fn traverse<StorageT: PrimInt>(
            rm: &Cactus<RepairMerge<StorageT>>,
        ) -> Vec<Vec<Repair<StorageT>>> {
            let mut out = Vec::new();
            match *rm.val().unwrap() {
                RepairMerge::Repair(r) => {
                    let parents = traverse(&rm.parent().unwrap());
                    if parents.is_empty() {
                        out.push(vec![r]);
                    } else {
                        for mut pc in parents {
                            pc.push(r);
                            out.push(pc);
                        }
                    }
                }
                RepairMerge::Merge(r, ref vc) => {
                    let parents = traverse(&rm.parent().unwrap());
                    if parents.is_empty() {
                        out.push(vec![r]);
                    } else {
                        for mut pc in parents {
                            pc.push(r);
                            out.push(pc);
                        }
                    }
                    for c in vc.vals() {
                        for pc in traverse(c) {
                            out.push(pc);
                        }
                    }
                }
                RepairMerge::Terminator => (),
            }
            out
        }

        let mut all_rprs = Vec::with_capacity(cnds.len());
        for cnd in cnds {
            all_rprs.push(
                traverse(&cnd.repairs)
                    .into_iter()
                    .map(|x| self.repair_to_parse_repair(in_laidx, &x))
                    .collect::<Vec<_>>(),
            );
        }
        all_rprs
    }

    fn repair_to_parse_repair(
        &self,
        mut laidx: usize,
        from: &[Repair<StorageT>],
    ) -> Vec<ParseRepair<LexemeT, StorageT>> {
        from.iter()
            .map(|y| match *y {
                Repair::InsertTerm(token_idx) => ParseRepair::Insert(token_idx),
                Repair::Delete => {
                    let rpr = ParseRepair::Delete(self.parser.next_lexeme(laidx));
                    laidx += 1;
                    rpr
                }
                Repair::Shift => {
                    let rpr = ParseRepair::Shift(self.parser.next_lexeme(laidx));
                    laidx += 1;
                    rpr
                }
            })
            .collect()
    }
}

/// Apply the `repairs` to `pstack` starting at position `laidx`: return the resulting parse
/// distance and a new pstack.
fn apply_repairs<
    'a,
    LexemeT: Lexeme<StorageT>,
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    ActionT: 'a,
    ParamT: Copy,
>(
    parser: &Parser<LexemeT, StorageT, ActionT, ParamT>,
    mut laidx: usize,
    pstack: &mut Vec<StIdx>,
    astack: &mut Option<&mut Vec<AStackType<LexemeT, ActionT>>>,
    spans: &mut Option<&mut Vec<Span>>,
    repairs: &[ParseRepair<LexemeT, StorageT>],
) -> usize
where
    usize: AsPrimitive<StorageT>,
{
    for r in repairs.iter() {
        match *r {
            ParseRepair::Insert(tidx) => {
                let next_lexeme = parser.next_lexeme(laidx);
                let new_lexeme = Lexeme::new_faulty(
                    StorageT::from(u32::from(tidx)).unwrap(),
                    next_lexeme.span().start(),
                    0,
                );
                parser.lr_upto(Some(new_lexeme), laidx, laidx + 1, pstack, astack, spans);
            }
            ParseRepair::Delete(_) => {
                laidx += 1;
            }
            ParseRepair::Shift(_) => {
                laidx = parser.lr_upto(None, laidx, laidx + 1, pstack, astack, spans);
            }
        }
    }
    laidx
}

/// Simplifies repair sequences, removes duplicates, and sorts them into order.
fn simplify_repairs<
    LexemeT: Lexeme<StorageT>,
    StorageT: 'static + Hash + PrimInt + Unsigned,
    ActionT,
    ParamT: Copy,
>(
    parser: &Parser<LexemeT, StorageT, ActionT, ParamT>,
    all_rprs: &mut Vec<Vec<ParseRepair<LexemeT, StorageT>>>,
) where
    usize: AsPrimitive<StorageT>,
{
    for rprs in &mut all_rprs.iter_mut() {
        // Remove shifts from the end of repairs
        while !rprs.is_empty() {
            if let ParseRepair::Shift(_) = rprs[rprs.len() - 1] {
                rprs.pop();
            } else {
                break;
            }
        }
    }

    // Use a HashSet as a quick way of deduplicating repair sequences: occasionally we can end up
    // with hundreds of thousands (!), and we don't have a sensible ordering on ParseRepair to make
    // it plausible to do a sort and dedup.
    let mut hs: HashSet<Vec<ParseRepair<LexemeT, StorageT>>> = all_rprs.drain(..).collect();
    all_rprs.extend(hs.drain());

    // Sort repair sequences:
    //   1) by whether they contain Inserts that are %insert_avoid
    //   2) by the number of repairs they contain
    let contains_avoid_insert = |rprs: &Vec<ParseRepair<LexemeT, StorageT>>| -> bool {
        for r in rprs.iter() {
            if let ParseRepair::Insert(tidx) = r {
                if parser.grm.avoid_insert(*tidx) {
                    return true;
                }
            }
        }
        false
    };
    all_rprs.sort_unstable_by(|x, y| {
        let x_cai = contains_avoid_insert(x);
        let y_cai = contains_avoid_insert(y);
        if x_cai && !y_cai {
            Ordering::Greater
        } else if !x_cai && y_cai {
            Ordering::Less
        } else {
            x.len().cmp(&y.len())
        }
    });
}

/// Convert `PathFNode` candidates in `cnds` into vectors of `ParseRepairs`s and rank them (from
/// highest to lowest) by the distance they allow parsing to continue without error. If two or more
/// `ParseRepair`s allow the same distance of parsing, then the `ParseRepair` which requires
/// repairs over the shortest distance is preferred. Amongst `ParseRepair`s of the same rank, the
/// ordering is non-deterministic.
fn rank_cnds<
    'a,
    LexemeT: Lexeme<StorageT>,
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    ActionT: 'a,
    ParamT: Copy,
>(
    parser: &Parser<LexemeT, StorageT, ActionT, ParamT>,
    finish_by: Instant,
    in_laidx: usize,
    in_pstack: &[StIdx],
    in_cnds: Vec<Vec<Vec<ParseRepair<LexemeT, StorageT>>>>,
) -> Vec<Vec<ParseRepair<LexemeT, StorageT>>>
where
    usize: AsPrimitive<StorageT>,
{
    let mut cnds = Vec::new();
    let mut furthest = 0;
    for rpr_seqs in in_cnds {
        if Instant::now() >= finish_by {
            return vec![];
        }
        let mut pstack = in_pstack.to_owned();
        let mut laidx = apply_repairs(
            parser,
            in_laidx,
            &mut pstack,
            &mut None,
            &mut None,
            &rpr_seqs[0],
        );
        laidx = parser.lr_upto(
            None,
            laidx,
            in_laidx + TRY_PARSE_AT_MOST,
            &mut pstack,
            &mut None,
            &mut None,
        );
        if laidx >= furthest {
            furthest = laidx;
        }
        cnds.push((pstack, laidx, rpr_seqs));
    }

    // Remove any elements except those which parsed as far as possible.
    cnds = cnds
        .into_iter()
        .filter(|x| x.1 == furthest)
        .collect::<Vec<_>>();

    cnds.into_iter().flat_map(|x| x.2).collect::<Vec<_>>()
}

/// Do `repairs` end with enough Shift repairs to be considered a success node?
fn ends_with_parse_at_least_shifts<StorageT: PrimInt + Unsigned>(
    repairs: &Cactus<RepairMerge<StorageT>>,
) -> bool {
    let mut shfts = 0;
    for x in repairs.vals().take(PARSE_AT_LEAST) {
        match *x {
            RepairMerge::Repair(Repair::Shift) => shfts += 1,
            RepairMerge::Merge(Repair::Shift, _) => shfts += 1,
            _ => return false,
        }
    }
    shfts == PARSE_AT_LEAST
}

#[cfg(test)]
mod test {
    use std::{fmt::Debug, hash::Hash};

    use cfgrammar::yacc::YaccGrammar;
    use num_traits::{AsPrimitive, PrimInt, ToPrimitive, Unsigned};

    use crate::{
        parser::{test::do_parse, ParseRepair, RecoveryKind},
        LexParseError, Lexeme,
    };

    fn pp_repairs<LexemeT: Lexeme<StorageT>, StorageT: 'static + Hash + PrimInt + Unsigned>(
        grm: &YaccGrammar<StorageT>,
        repairs: &[ParseRepair<LexemeT, StorageT>],
    ) -> String
    where
        usize: AsPrimitive<StorageT>,
    {
        let mut out = vec![];
        for r in repairs.iter() {
            match *r {
                ParseRepair::Insert(token_idx) => {
                    out.push(format!("Insert \"{}\"", grm.token_epp(token_idx).unwrap()))
                }
                ParseRepair::Delete(_) => out.push("Delete".to_owned()),
                ParseRepair::Shift(_) => out.push("Shift".to_owned()),
            }
        }
        out.join(", ")
    }

    fn check_all_repairs<
        LexemeT: Lexeme<StorageT>,
        StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    >(
        grm: &YaccGrammar<StorageT>,
        err: &LexParseError<LexemeT, StorageT>,
        expected: &[&str],
    ) where
        usize: AsPrimitive<StorageT>,
    {
        match err {
            LexParseError::ParseError(e) => {
                assert_eq!(
                    e.repairs().len(),
                    expected.len(),
                    "{:?}\nhas a different number of entries to:\n{:?}",
                    e.repairs(),
                    expected
                );
                for i in 0..e.repairs().len() {
                    if !expected
                        .iter()
                        .any(|x| *x == pp_repairs(grm, &e.repairs()[i]))
                    {
                        panic!(
                            "No match found for:\n  {}",
                            pp_repairs(grm, &e.repairs()[i])
                        );
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn corchuelo_example() {
        // The example from the Curchuelo paper
        let lexs = "\\( '('
                    \\) ')'
                    \\+ '+'
                    n 'N'";
        let grms = "%start E
%%
E : 'N'
  | E '+' 'N'
  | '(' E ')'
  ;
";

        let us = "(nn";
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlus, lexs, grms, us);
        let (pt, errs) = pr.unwrap_err();
        let pp = pt.unwrap().pp(&grm, us);
        // Note that:
        //   E
        //    ( (
        //    E
        //     E
        //      N n
        //     +
        //     N n
        //    )
        // is also the result of a valid minimal-cost repair, but, since the repair involves a
        // Shift, rank_cnds will always put this too low down the list for us to ever see it.
        if !vec![
            "E
 ( (
 E
  N n
 ) 
",
            "E
 E
  ( (
  E
   N n
  ) 
 + 
 N n
",
        ]
        .iter()
        .any(|x| *x == pp)
        {
            panic!("Can't find a match for {}", pp);
        }

        assert_eq!(errs.len(), 1);
        let err_tok_id = u32::from(grm.token_idx("N").unwrap()).to_u16().unwrap();
        match &errs[0] {
            LexParseError::ParseError(e) => {
                assert_eq!(e.lexeme(), &Lexeme::new(err_tok_id, 2, 1))
            }
            _ => unreachable!(),
        }
        check_all_repairs(
            &grm,
            &errs[0],
            &[
                "Insert \")\", Insert \"+\"",
                "Insert \")\", Delete",
                "Insert \"+\", Shift, Insert \")\"",
            ],
        );

        let (grm, pr) = do_parse(RecoveryKind::CPCTPlus, lexs, grms, "n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_all_repairs(&grm, &errs[0], &["Delete"]);
        check_all_repairs(&grm, &errs[1], &["Delete"]);

        let (grm, pr) = do_parse(RecoveryKind::CPCTPlus, lexs, grms, "(((+n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_all_repairs(&grm, &errs[0], &["Insert \"N\"", "Delete"]);
        check_all_repairs(&grm, &errs[1], &["Insert \")\""]);
    }

    #[test]
    fn test_merge() {
        let lexs = "a 'a'
                    b 'b'
                    c 'c'
                    d 'd'";

        let grms = "%start S
%%
S: T U;
T: T1 | 'b' | T2;
T1: 'a';
T2: 'c' | 'a' 'b' 'c';
U: 'd';
";

        let us = "";
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlus, lexs, grms, us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(
            &grm,
            &errs[0],
            &[
                "Insert \"a\", Insert \"d\"",
                "Insert \"b\", Insert \"d\"",
                "Insert \"c\", Insert \"d\"",
            ],
        );
    }
}
