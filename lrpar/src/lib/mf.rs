use std::{
    cmp::Ordering,
    collections::HashSet,
    fmt::Debug,
    hash::{Hash, Hasher},
    iter::FromIterator,
    marker::PhantomData,
    mem,
    time::Instant
};

use cactus::Cactus;
use cfgrammar::{yacc::YaccGrammar, Symbol, TIdx};
use lrtable::{Action, StIdx, StIdxStorageT, StateGraph, StateTable};
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use packedvec::PackedVec;
use vob::Vob;

use crate::{
    astar::astar_all,
    lex::Lexeme,
    parser::{AStackType, ParseRepair, Parser, Recoverer},
    Span
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
    Shift
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RepairMerge<StorageT> {
    Repair(Repair<StorageT>),
    Merge(Repair<StorageT>, Cactus<Cactus<RepairMerge<StorageT>>>),
    Terminator
}

#[derive(Clone, Debug)]
struct PathFNode<StorageT> {
    pstack: Cactus<StIdx>,
    laidx: usize,
    repairs: Cactus<RepairMerge<StorageT>>,
    cf: u16,
    cg: u16
}

impl<StorageT: PrimInt + Unsigned> PathFNode<StorageT> {
    fn last_repair(&self) -> Option<Repair<StorageT>> {
        match *self.repairs.val().unwrap() {
            RepairMerge::Repair(r) => Some(r),
            RepairMerge::Merge(x, _) => Some(x),
            RepairMerge::Terminator => None
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
            (_, _) => ()
        }

        let num_shifts = |c: &Cactus<RepairMerge<StorageT>>| {
            let mut n = 0;
            for r in c.vals() {
                match *r {
                    RepairMerge::Repair(Repair::Shift) | RepairMerge::Merge(Repair::Shift, _) => {
                        n += 1
                    }
                    _ => break
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

struct MF<'a, 'b: 'a, 'input: 'b, StorageT: 'static + Eq + Hash, ActionT: 'a> {
    dist: Dist<StorageT>,
    parser: &'a Parser<'a, 'b, 'input, StorageT, ActionT>
}

pub(crate) fn recoverer<
    'a,
    'b: 'a,
    'input: 'b,
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    ActionT: 'a
>(
    parser: &'a Parser<'a, 'b, 'input, StorageT, ActionT>
) -> Box<dyn Recoverer<StorageT, ActionT> + 'a>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    let dist = Dist::new(
        parser.grm,
        parser.sgraph,
        parser.stable,
        parser.token_cost.as_ref()
    );
    Box::new(MF { dist, parser })
}

impl<
        'a,
        'b: 'a,
        'input: 'b,
        StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
        ActionT: 'a
    > Recoverer<StorageT, ActionT> for MF<'a, 'b, 'input, StorageT, ActionT>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    fn recover(
        &self,
        finish_by: Instant,
        parser: &Parser<StorageT, ActionT>,
        in_laidx: usize,
        mut in_pstack: &mut Vec<StIdx>,
        mut astack: &mut Vec<AStackType<ActionT, StorageT>>,
        mut span: &mut Vec<Span>
    ) -> (usize, Vec<Vec<ParseRepair<StorageT>>>) {
        let mut start_cactus_pstack = Cactus::new();
        for st in in_pstack.iter() {
            start_cactus_pstack = start_cactus_pstack.child(*st);
        }

        let start_node = PathFNode {
            pstack: start_cactus_pstack,
            laidx: in_laidx,
            repairs: Cactus::new().child(RepairMerge::Terminator),
            cf: 0,
            cg: 0
        };

        let astar_cnds = astar_all(
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
                        if explore_all || n.cg > 0 {
                            self.insert(n, nbrs);
                        }
                        self.reduce(n, nbrs);
                    }
                }
                if explore_all || n.cg > 0 {
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
                    _ => unreachable!()
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

                match parser
                    .stable
                    .action(*n.pstack.val().unwrap(), parser.next_tidx(n.laidx))
                {
                    Action::Accept => true,
                    _ => false
                }
            }
        );

        if astar_cnds.is_empty() {
            return (in_laidx, vec![]);
        }

        let full_rprs = self.collect_repairs(in_laidx, astar_cnds);
        let mut rnk_rprs = rank_cnds(parser, finish_by, in_laidx, &in_pstack, full_rprs);
        if rnk_rprs.is_empty() {
            return (in_laidx, vec![]);
        }
        simplify_repairs(parser, &mut rnk_rprs);
        let laidx = apply_repairs(
            parser,
            in_laidx,
            &mut in_pstack,
            &mut Some(&mut astack),
            &mut Some(&mut span),
            &rnk_rprs[0]
        );

        (laidx, rnk_rprs)
    }
}

impl<
        'a,
        'b: 'a,
        'input: 'b,
        StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
        ActionT: 'a
    > MF<'a, 'b, 'input, StorageT, ActionT>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    fn insert(&self, n: &PathFNode<StorageT>, nbrs: &mut Vec<(u16, u16, PathFNode<StorageT>)>) {
        let top_pstack = *n.pstack.val().unwrap();
        for tidx in self.parser.stable.state_shifts(top_pstack) {
            if tidx == self.parser.grm.eof_token_idx() {
                continue;
            }

            let t_stidx = match self.parser.stable.action(top_pstack, tidx) {
                Action::Shift(stidx) => stidx,
                _ => unreachable!()
            };
            let n_repairs = n
                .repairs
                .child(RepairMerge::Repair(Repair::InsertTerm(tidx)));
            if let Some(d) = self.dyn_dist(&n_repairs, t_stidx, n.laidx) {
                assert!(n.cg == 0 || d >= n.cg - u16::from((self.parser.token_cost)(tidx)));
                let nn = PathFNode {
                    pstack: n.pstack.child(t_stidx),
                    laidx: n.laidx,
                    repairs: n_repairs,
                    cf: n
                        .cf
                        .checked_add(u16::from((self.parser.token_cost)(tidx)))
                        .unwrap(),
                    cg: d
                };
                nbrs.push((nn.cf, nn.cg, nn));
            }
        }
    }

    fn reduce(&self, n: &PathFNode<StorageT>, nbrs: &mut Vec<(u16, u16, PathFNode<StorageT>)>) {
        let top_pstack = *n.pstack.val().unwrap();
        for pidx in self.parser.stable.core_reduces(top_pstack) {
            let sym_off = self.parser.grm.prod(pidx).len();
            let ridx = self.parser.grm.prod_to_rule(pidx);
            let mut qi_minus_alpha = n.pstack.clone();
            for _ in 0..sym_off {
                qi_minus_alpha = qi_minus_alpha.parent().unwrap();
            }

            if let Some(mut goto_stidx) = self
                .parser
                .stable
                .goto(*qi_minus_alpha.val().unwrap(), ridx)
            {
                // We want to reduce/goto goto_stidx. However if that state only contains
                // reductions and if all reductions are the same, we can skip over it.
                while self.parser.stable.reduce_only_state(goto_stidx) {
                    let pidx = self.parser.stable.core_reduces(goto_stidx).last().unwrap();
                    let sym_off = self.parser.grm.prod(pidx).len();
                    let ridx = self.parser.grm.prod_to_rule(pidx);
                    // Technically we should push goto_stidx, and then pop sym_off elements, but
                    // we can avoid the push in cases where sym_off is greater than 0, compensating
                    // for that by poping (sym_off - 1) elements.
                    if sym_off == 0 {
                        qi_minus_alpha = qi_minus_alpha.child(goto_stidx);
                    } else {
                        for _ in 0..sym_off - 1 {
                            qi_minus_alpha = qi_minus_alpha.parent().unwrap();
                        }
                    }
                    if let Some(x) = self
                        .parser
                        .stable
                        .goto(*qi_minus_alpha.val().unwrap(), ridx)
                    {
                        goto_stidx = x;
                    } else {
                        return;
                    }
                }

                if let Some(d) = self.dyn_dist(&n.repairs, goto_stidx, n.laidx) {
                    let nn = PathFNode {
                        pstack: qi_minus_alpha.child(goto_stidx),
                        laidx: n.laidx,
                        repairs: n.repairs.clone(),
                        cf: n.cf,
                        cg: d
                    };
                    nbrs.push((nn.cf, nn.cg, nn));
                }
            }
        }
    }

    fn delete(&self, n: &PathFNode<StorageT>, nbrs: &mut Vec<(u16, u16, PathFNode<StorageT>)>) {
        if n.laidx == self.parser.lexemes.len() {
            return;
        }

        let n_repairs = n.repairs.child(RepairMerge::Repair(Repair::Delete));
        if let Some(d) = self.dyn_dist(&n_repairs, *n.pstack.val().unwrap(), n.laidx + 1) {
            let la_tidx = self.parser.next_tidx(n.laidx);
            let cost = (self.parser.token_cost)(la_tidx);
            let nn = PathFNode {
                pstack: n.pstack.clone(),
                laidx: n.laidx + 1,
                repairs: n_repairs,
                cf: n.cf.checked_add(u16::from(cost)).unwrap(),
                cg: d
            };
            nbrs.push((nn.cf, nn.cg, nn));
        }
    }

    fn shift(&self, n: &PathFNode<StorageT>, nbrs: &mut Vec<(u16, u16, PathFNode<StorageT>)>) {
        let la_tidx = self.parser.next_tidx(n.laidx);
        let top_pstack = *n.pstack.val().unwrap();
        if let Action::Shift(state_id) = self.parser.stable.action(top_pstack, la_tidx) {
            let n_repairs = n.repairs.child(RepairMerge::Repair(Repair::Shift));
            let new_laidx = n.laidx + 1;
            if let Some(d) = self.dyn_dist(&n_repairs, state_id, new_laidx) {
                let nn = PathFNode {
                    pstack: n.pstack.child(state_id),
                    laidx: new_laidx,
                    repairs: n_repairs,
                    cf: n.cf,
                    cg: d
                };
                nbrs.push((nn.cf, nn.cg, nn));
            }
        }
    }

    /// Convert the output from `astar_all` into something more usable.
    fn collect_repairs(
        &self,
        in_laidx: usize,
        cnds: Vec<PathFNode<StorageT>>
    ) -> Vec<Vec<Vec<ParseRepair<StorageT>>>> {
        fn traverse<StorageT: PrimInt + Unsigned>(
            rm: &Cactus<RepairMerge<StorageT>>
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
                RepairMerge::Terminator => ()
            }
            out
        }

        let mut all_rprs = Vec::with_capacity(cnds.len());
        for cnd in cnds {
            all_rprs.push(
                traverse(&cnd.repairs)
                    .into_iter()
                    .map(|x| self.repair_to_parse_repair(in_laidx, &x))
                    .collect::<Vec<_>>()
            );
        }
        all_rprs
    }

    fn repair_to_parse_repair(
        &self,
        mut laidx: usize,
        from: &[Repair<StorageT>]
    ) -> Vec<ParseRepair<StorageT>> {
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

    /// Return the distance from `stidx` at input position `laidx`, given the current `repairs`.
    /// Returns `None` if no route can be found.
    fn dyn_dist(
        &self,
        repairs: &Cactus<RepairMerge<StorageT>>,
        stidx: StIdx,
        laidx: usize
    ) -> Option<u16> {
        // This function is very different than anything in KimYi: it estimates the distance to a
        // success node based in part on dynamic properties of the input as well as static
        // properties of the grammar.

        // We first deal with a subtle case: one way of a sequence of repairs succeeding is if it
        // shifts PARSE_AT_LEAST lexemes (in other words: we've found a sequence of repairs
        // successful enough to allow us to parse at least PARSE_AT_LEAST lexemes without hitting
        // another error). We have to catch this explicitly and return a distance of 0 so that the
        // resulting node can be checked for success [if we were to leave this to chance, it's
        // possible that the PARSE_AT_LEAST+1 symbol is something which has a distance > 0 (or,
        // worse, no route!), which would then confuse the astar function, since a success node
        // would have a distance > 0.]
        if ends_with_parse_at_least_shifts(repairs) {
            return Some(0);
        }

        // Now we deal with the "main" case: dealing with distances in the face of possible
        // deletions. Imagine that there are two lexemes starting at position laidx: (in order) T
        // and U, both with a token_cost of 1. Assume the dist() from stidx to T is 2 and the
        // dist() from stidx to U is 0. If we delete T then the distance to U is 1, which is a
        // shorter distance than T. We therefore need to return a distance of 1, even though that
        // is the distance to the second lexeme.
        //
        // Imagine we have the Java input "x = } y;". The distance from "=" to "}" is 2 (at a
        // minimum you need an int/string/etc followed by a semi-colon); however the distance from
        // "=" to "y" is 0. Assuming the deletion cost of "}" is 1, it's therefore cheaper to
        // delete "}" and add that to the distance from "=" to "y". Thus the cheapest distance is
        // 1.
        let mut ld = u16::max_value(); // ld == Current least distance
        let mut dc = 0; // Cumulative deletion cost
        for i in laidx..self.parser.lexemes.len() + 1 {
            let tidx = self.parser.next_tidx(i);
            let d = self.dist.dist(stidx, tidx);
            if d < u16::max_value() && dc + d < ld {
                ld = dc + d;
            }
            dc += u16::from((self.parser.token_cost)(tidx));
            if dc >= ld {
                // Once the cumulative cost of deleting lexemes is bigger than the current least
                // distance, there is no chance of finding a subsequent lexeme which could produce
                // a lower cost.
                break;
            }
        }
        if ld == u16::max_value() {
            None
        } else {
            Some(ld)
        }
    }
}

/// Do `repairs` end with enough Shift repairs to be considered a success node?
fn ends_with_parse_at_least_shifts<StorageT>(repairs: &Cactus<RepairMerge<StorageT>>) -> bool {
    let mut shfts = 0;
    for x in repairs.vals().take(PARSE_AT_LEAST) {
        match x {
            RepairMerge::Repair(Repair::Shift) => shfts += 1,
            RepairMerge::Merge(Repair::Shift, _) => shfts += 1,
            _ => return false
        }
    }
    shfts == PARSE_AT_LEAST
}

/// Convert `PathFNode` candidates in `cnds` into vectors of `ParseRepairs`s and rank them (from
/// highest to lowest) by the distance they allow parsing to continue without error. If two or more
/// `ParseRepair`s allow the same distance of parsing, then the `ParseRepair` which requires
/// repairs over the shortest distance is preferred. Amongst `ParseRepair`s of the same rank, the
/// ordering is non-deterministic.
pub(crate) fn rank_cnds<'a, StorageT: 'static + Debug + Hash + PrimInt + Unsigned, ActionT: 'a>(
    parser: &Parser<StorageT, ActionT>,
    finish_by: Instant,
    in_laidx: usize,
    in_pstack: &[StIdx],
    in_cnds: Vec<Vec<Vec<ParseRepair<StorageT>>>>
) -> Vec<Vec<ParseRepair<StorageT>>>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
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
            &rpr_seqs[0]
        );
        laidx = parser.lr_upto(
            None,
            laidx,
            in_laidx + TRY_PARSE_AT_MOST,
            &mut pstack,
            &mut None,
            &mut None
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

/// Apply the `repairs` to `pstack` starting at position `laidx`: return the resulting parse
/// distance and a new pstack.
pub(crate) fn apply_repairs<
    'a,
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    ActionT: 'a
>(
    parser: &Parser<StorageT, ActionT>,
    mut laidx: usize,
    mut pstack: &mut Vec<StIdx>,
    mut astack: &mut Option<&mut Vec<AStackType<ActionT, StorageT>>>,
    mut spans: &mut Option<&mut Vec<Span>>,
    repairs: &[ParseRepair<StorageT>]
) -> usize
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    for r in repairs.iter() {
        match *r {
            ParseRepair::Insert(tidx) => {
                let next_lexeme = parser.next_lexeme(laidx);
                let new_lexeme = Lexeme::new(
                    StorageT::from(u32::from(tidx)).unwrap(),
                    next_lexeme.span().start(),
                    None
                );
                parser.lr_upto(
                    Some(new_lexeme),
                    laidx,
                    laidx + 1,
                    &mut pstack,
                    &mut astack,
                    &mut spans
                );
            }
            ParseRepair::Delete(_) => {
                laidx += 1;
            }
            ParseRepair::Shift(_) => {
                laidx =
                    parser.lr_upto(None, laidx, laidx + 1, &mut pstack, &mut astack, &mut spans);
            }
        }
    }
    laidx
}

/// Simplifies repair sequences, removes duplicates, and sorts them into order.
pub(crate) fn simplify_repairs<StorageT: 'static + Hash + PrimInt + Unsigned, ActionT>(
    parser: &Parser<StorageT, ActionT>,
    all_rprs: &mut Vec<Vec<ParseRepair<StorageT>>>
) where
    usize: AsPrimitive<StorageT>
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
    let mut hs: HashSet<Vec<ParseRepair<StorageT>>> = HashSet::from_iter(all_rprs.drain(..));
    all_rprs.extend(hs.drain());

    // Sort repair sequences:
    //   1) by whether they contain Inserts that are %insert_avoid
    //   2) by the number of repairs they contain
    let contains_avoid_insert = |rprs: &Vec<ParseRepair<StorageT>>| -> bool {
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

pub(crate) struct Dist<StorageT> {
    tokens_len: TIdx<StorageT>,
    table: PackedVec<u16>,
    infinity: u16,
    phantom: PhantomData<StorageT>
}

impl<StorageT: 'static + Hash + PrimInt + Unsigned> Dist<StorageT>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    pub(crate) fn new<F>(
        grm: &YaccGrammar<StorageT>,
        sgraph: &StateGraph<StorageT>,
        stable: &StateTable<StorageT>,
        token_cost: F
    ) -> Dist<StorageT>
    where
        F: Fn(TIdx<StorageT>) -> u8
    {
        // This is an extension of dist from the KimYi paper: it also takes into account reductions
        // and gotos in the distances it reports back. Note that it is conservative, sometimes
        // undercounting the distance. Consider the KimYi paper, Figure 10: from state 0 it is
        // clearly the case that the distance to ')' is 2 since we would need to encounter the
        // tokens "(", {"a", "b"} before encountering a ')'. However, this algorithm gives the
        // distance as 1. This is because state 0 is a reduction target of state 3, but state 3
        // also has a reduction target of state 5: thus state state 0 ends up with the minimum
        // distances of itself and state 5.

        let tokens_len = usize::from(grm.tokens_len());
        let states_len = usize::from(sgraph.all_states_len());
        let sengen = grm.sentence_generator(&token_cost);
        let goto_states = Dist::goto_states(grm, sgraph, stable);

        let mut table = Vec::new();
        table.resize(states_len * tokens_len, u16::max_value());
        table[usize::from(stable.final_state) * tokens_len + usize::from(grm.eof_token_idx())] = 0;
        loop {
            let mut chgd = false;
            for stidx in sgraph.iter_stidxs() {
                // The first phase is KimYi's dist algorithm.
                for (&sym, &sym_stidx) in sgraph.edges(stidx).iter() {
                    let d = match sym {
                        Symbol::Rule(ridx) => sengen.min_sentence_cost(ridx),
                        Symbol::Token(tidx) => {
                            let off = usize::from(stidx) * tokens_len + usize::from(tidx);
                            if table[off] != 0 {
                                table[off] = 0;
                                chgd = true;
                            }
                            u16::from(token_cost(tidx))
                        }
                    };

                    for tidx in grm.iter_tidxs() {
                        let this_off = usize::from(stidx) * tokens_len + usize::from(tidx);
                        let other_off = usize::from(sym_stidx) * tokens_len + usize::from(tidx);

                        if table[other_off] != u16::max_value()
                            && table[other_off] + d < table[this_off]
                        {
                            table[this_off] = table[other_off] + d;
                            chgd = true;
                        }
                    }
                }

                // The second phase takes into account reductions and gotos.
                for goto_stidx in goto_states[usize::from(stidx)]
                    .iter_set_bits(..)
                    // goto_states[i].len() == states.len(), which we know fits into StIdxStorageT,
                    // hence the cast below is safe.
                    .map(|x| StIdx::from(x as StIdxStorageT))
                {
                    for tidx in grm.iter_tidxs() {
                        let this_off = usize::from(stidx) * tokens_len + usize::from(tidx);
                        let other_off = usize::from(goto_stidx) * tokens_len + usize::from(tidx);

                        if table[other_off] != u16::max_value()
                            && table[other_off] < table[this_off]
                        {
                            table[this_off] = table[other_off];
                            chgd = true;
                        }
                    }
                }
            }
            if !chgd {
                break;
            }
        }

        // If we keep u16::max_value() as our signifier of infinity, PackedVec can't do anything
        // useful with the distance table. We therefore map infinity to the largest value in the
        // table + 1.
        let m = *table
            .iter()
            .max_by_key(|&x| if *x == u16::max_value() { 0 } else { *x })
            .unwrap()
            + 1;
        let table = PackedVec::<u16, _>::new(
            table
                .iter()
                .map(|&x| if x == u16::max_value() { m } else { x })
                .collect()
        );
        Dist {
            tokens_len: grm.tokens_len(),
            infinity: m,
            table,
            phantom: PhantomData
        }
    }

    pub(crate) fn dist(&self, stidx: StIdx, tidx: TIdx<StorageT>) -> u16 {
        let d = self
            .table
            .get(usize::from(stidx) * usize::from(self.tokens_len) + usize::from(tidx))
            .unwrap();
        if d == self.infinity {
            u16::max_value()
        } else {
            d
        }
    }

    /// rev_edges allows us to walk backwards over the stategraph.
    fn rev_edges(sgraph: &StateGraph<StorageT>) -> Vec<Vob> {
        let states_len = sgraph.all_states_len();
        let mut rev_edges = Vec::with_capacity(usize::from(states_len));
        rev_edges.resize(
            usize::from(states_len),
            Vob::from_elem(usize::from(sgraph.all_states_len()), false)
        );
        for stidx in sgraph.iter_stidxs() {
            for (_, &sym_stidx) in sgraph.edges(stidx).iter() {
                rev_edges[usize::from(sym_stidx)].set(usize::from(stidx), true);
            }
        }
        rev_edges
    }

    /// goto_states allows us to quickly determine all the states reachable after an entry in a
    /// given state has been reduced and performed a goto.
    fn goto_states(
        grm: &YaccGrammar<StorageT>,
        sgraph: &StateGraph<StorageT>,
        stable: &StateTable<StorageT>
    ) -> Vec<Vob> {
        let rev_edges = Dist::rev_edges(sgraph);
        let states_len = usize::from(sgraph.all_states_len());
        let mut goto_states = Vec::with_capacity(states_len);
        goto_states.resize(states_len, Vob::from_elem(states_len, false));
        // prev and next are hoist here to lessen memory allocation in a core loop below.
        let mut prev = Vob::from_elem(states_len, false);
        let mut next = Vob::from_elem(states_len, false);
        for stidx in sgraph.iter_stidxs() {
            for &(pidx, sym_off) in sgraph.core_state(stidx).items.keys() {
                let prod = grm.prod(pidx);
                if usize::from(sym_off) < prod.len() {
                    continue;
                }
                let ridx = grm.prod_to_rule(pidx);

                // We've found an item in a core state where the dot is at the end of the rule:
                // what we now do is reach backwards in the stategraph to find all of the
                // possible states the reduction and subsequent goto might reach.

                // First find all the possible states the reductions might end up in. We search
                // back prod.len() states in the stategraph to do this: the final result will end
                // up in prev.
                prev.set_all(false);
                prev.set(usize::from(stidx), true);
                for _ in 0..prod.len() {
                    next.set_all(false);
                    for prev_stidx in prev.iter_set_bits(..) {
                        next.or(&rev_edges[prev_stidx]);
                    }
                    mem::swap(&mut prev, &mut next);
                }

                // From the reduction states, find all the goto states.
                for prev_stidx in prev.iter_set_bits(..) {
                    // prev.len() == states_len, which we know fits into StIdxStorageT, hence the
                    // cast below is safe.
                    if let Some(goto_stidx) =
                        stable.goto(StIdx::from(prev_stidx as StIdxStorageT), ridx)
                    {
                        goto_states[usize::from(stidx)].set(usize::from(goto_stidx), true);
                    }
                }
            }
        }
        goto_states
    }
}

#[cfg(test)]
mod test {
    use std::{collections::HashMap, fmt::Debug, hash::Hash};

    use cactus::Cactus;
    use cfgrammar::{
        yacc::{YaccGrammar, YaccKind, YaccOriginalActionKind},
        Symbol
    };
    use lrtable::{from_yacc, Minimiser, StIdx, StIdxStorageT};
    use num_traits::{AsPrimitive, PrimInt, ToPrimitive, Unsigned, Zero};

    use crate::{
        lex::Lexeme,
        parser::{
            test::{do_parse, do_parse_with_costs},
            LexParseError, ParseRepair, RecoveryKind
        }
    };

    use super::{ends_with_parse_at_least_shifts, Dist, Repair, RepairMerge, PARSE_AT_LEAST};

    fn pp_repairs<StorageT: 'static + Hash + PrimInt + Unsigned>(
        grm: &YaccGrammar<StorageT>,
        repairs: &[ParseRepair<StorageT>]
    ) -> String
    where
        usize: AsPrimitive<StorageT>
    {
        let mut out = vec![];
        for r in repairs.iter() {
            match *r {
                ParseRepair::Insert(token_idx) => {
                    out.push(format!("Insert \"{}\"", grm.token_epp(token_idx).unwrap()))
                }
                ParseRepair::Delete(_) => out.push("Delete".to_owned()),
                ParseRepair::Shift(_) => out.push("Shift".to_owned())
            }
        }
        out.join(", ")
    }

    #[test]
    #[rustfmt::skip]
    fn dist_kimyi() {
        let grms = "%start A
%%
A: '(' A ')'
 | 'a'
 | 'b'
 ;
";

        let grm = YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, &stable, |_| 1);
        let s0 = StIdx::from(StIdxStorageT::zero());
        assert_eq!(d.dist(s0, grm.token_idx("(").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.token_idx(")").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.token_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.token_idx("b").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.eof_token_idx()), 1);

        let s1 = sgraph.edge(s0, Symbol::Rule(grm.rule_idx("A").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.token_idx("(").unwrap()), u16::max_value());
        assert_eq!(d.dist(s1, grm.token_idx(")").unwrap()), u16::max_value());
        assert_eq!(d.dist(s1, grm.token_idx("a").unwrap()), u16::max_value());
        assert_eq!(d.dist(s1, grm.token_idx("b").unwrap()), u16::max_value());
        assert_eq!(d.dist(s1, grm.eof_token_idx()), 0);

        let s2 = sgraph.edge(s0, Symbol::Token(grm.token_idx("a").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.token_idx("(").unwrap()), u16::max_value());
        assert_eq!(d.dist(s2, grm.token_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s2, grm.token_idx("a").unwrap()), u16::max_value());
        assert_eq!(d.dist(s2, grm.token_idx("b").unwrap()), u16::max_value());
        assert_eq!(d.dist(s2, grm.eof_token_idx()), 0);

        let s3 = sgraph.edge(s0, Symbol::Token(grm.token_idx("b").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.token_idx("(").unwrap()), u16::max_value());
        assert_eq!(d.dist(s3, grm.token_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.token_idx("a").unwrap()), u16::max_value());
        assert_eq!(d.dist(s3, grm.token_idx("b").unwrap()), u16::max_value());
        assert_eq!(d.dist(s3, grm.eof_token_idx()), 0);

        let s5 = sgraph.edge(s0, Symbol::Token(grm.token_idx("(").unwrap())).unwrap();
        assert_eq!(d.dist(s5, grm.token_idx("(").unwrap()), 0);
        assert_eq!(d.dist(s5, grm.token_idx(")").unwrap()), 1);
        assert_eq!(d.dist(s5, grm.token_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s5, grm.token_idx("b").unwrap()), 0);
        assert_eq!(d.dist(s5, grm.eof_token_idx()), 1);

        let s6 = sgraph.edge(s5, Symbol::Rule(grm.rule_idx("A").unwrap())).unwrap();
        assert_eq!(d.dist(s6, grm.token_idx("(").unwrap()), u16::max_value());
        assert_eq!(d.dist(s6, grm.token_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s6, grm.token_idx("a").unwrap()), u16::max_value());
        assert_eq!(d.dist(s6, grm.token_idx("b").unwrap()), u16::max_value());
        assert_eq!(d.dist(s6, grm.eof_token_idx()), 1);

        let s4 = sgraph.edge(s6, Symbol::Token(grm.token_idx(")").unwrap())).unwrap();
        assert_eq!(d.dist(s4, grm.token_idx("(").unwrap()), u16::max_value());
        assert_eq!(d.dist(s4, grm.token_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s4, grm.token_idx("a").unwrap()), u16::max_value());
        assert_eq!(d.dist(s4, grm.token_idx("b").unwrap()), u16::max_value());
        assert_eq!(d.dist(s4, grm.eof_token_idx()), 0);
    }

    #[test]
    #[rustfmt::skip]
    fn dist_short() {
        let grms = "%start S
%%
S: T U 'C';
T: 'A';
U: 'B';
";

        let grm = YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, &stable, |_| 1);

        // This only tests a subset of all the states and distances but, I believe, it tests all
        // more interesting edge cases that the example from the Kim/Yi paper.

        let s0 = StIdx::from(StIdxStorageT::zero());
        assert_eq!(d.dist(s0, grm.token_idx("A").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.token_idx("B").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.token_idx("C").unwrap()), 2);

        let s1 = sgraph.edge(s0, Symbol::Rule(grm.rule_idx("T").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.token_idx("A").unwrap()), u16::max_value());
        assert_eq!(d.dist(s1, grm.token_idx("B").unwrap()), 0);
        assert_eq!(d.dist(s1, grm.token_idx("C").unwrap()), 1);

        let s2 = sgraph.edge(s0, Symbol::Rule(grm.rule_idx("S").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.token_idx("A").unwrap()), u16::max_value());
        assert_eq!(d.dist(s2, grm.token_idx("B").unwrap()), u16::max_value());
        assert_eq!(d.dist(s2, grm.token_idx("C").unwrap()), u16::max_value());

        let s3 = sgraph.edge(s0, Symbol::Token(grm.token_idx("A").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.token_idx("A").unwrap()), u16::max_value());
        assert_eq!(d.dist(s3, grm.token_idx("B").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.token_idx("C").unwrap()), 1);

        let s4 = sgraph.edge(s1, Symbol::Rule(grm.rule_idx("U").unwrap())).unwrap();
        assert_eq!(d.dist(s4, grm.token_idx("A").unwrap()), u16::max_value());
        assert_eq!(d.dist(s4, grm.token_idx("B").unwrap()), u16::max_value());
        assert_eq!(d.dist(s4, grm.token_idx("C").unwrap()), 0);

        let s5 = sgraph.edge(s1, Symbol::Token(grm.token_idx("B").unwrap())).unwrap();
        assert_eq!(d.dist(s5, grm.token_idx("A").unwrap()), u16::max_value());
        assert_eq!(d.dist(s5, grm.token_idx("B").unwrap()), u16::max_value());
        assert_eq!(d.dist(s5, grm.token_idx("C").unwrap()), 0);

        let s6 = sgraph.edge(s4, Symbol::Token(grm.token_idx("C").unwrap())).unwrap();
        assert_eq!(d.dist(s6, grm.token_idx("A").unwrap()), u16::max_value());
        assert_eq!(d.dist(s6, grm.token_idx("B").unwrap()), u16::max_value());
        assert_eq!(d.dist(s6, grm.token_idx("C").unwrap()), u16::max_value());
    }

    #[test]
    #[rustfmt::skip]
    fn dist_large() {
        let grms = "%start Expr
%%
Expr: Term '+' Expr
    | Term ;

Term: Factor '*' Term
    | Factor ;

Factor: '(' Expr ')'
      | 'INT' ;
";

        let grm = YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, &stable, |_| 1);

        // This only tests a subset of all the states and distances but, I believe, it tests all
        // more interesting edge cases that the example from the Kim/Yi paper.

        let s0 = StIdx::from(StIdxStorageT::zero());
        assert_eq!(d.dist(s0, grm.token_idx("+").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.token_idx("*").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.token_idx("(").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.token_idx(")").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.token_idx("INT").unwrap()), 0);

        let s1 = sgraph.edge(s0, Symbol::Token(grm.token_idx("(").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.token_idx("+").unwrap()), 1);
        assert_eq!(d.dist(s1, grm.token_idx("*").unwrap()), 1);
        assert_eq!(d.dist(s1, grm.token_idx("(").unwrap()), 0);
        assert_eq!(d.dist(s1, grm.token_idx(")").unwrap()), 1);
        assert_eq!(d.dist(s1, grm.token_idx("INT").unwrap()), 0);

        let s2 = sgraph.edge(s0, Symbol::Rule(grm.rule_idx("Factor").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.token_idx("+").unwrap()), 0);
        assert_eq!(d.dist(s2, grm.token_idx("*").unwrap()), 0);
        assert_eq!(d.dist(s2, grm.token_idx("(").unwrap()), 1);
        assert_eq!(d.dist(s2, grm.token_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s2, grm.token_idx("INT").unwrap()), 1);

        let s3 = sgraph.edge(s0, Symbol::Token(grm.token_idx("INT").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.token_idx("+").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.token_idx("*").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.token_idx("(").unwrap()), 1);
        assert_eq!(d.dist(s3, grm.token_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.token_idx("INT").unwrap()), 1);
    }

    #[test]
    #[rustfmt::skip]
    fn dist_nested() {
        let grms = "%start S
%%
S : T;
T : T U | ;
U : V W;
V: 'a' ;
W: 'b' ;
";

        // 0: [^ -> . S, {'$'}]
        //    T -> 1
        //    S -> 2
        // 1: [S -> T ., {'$'}]
        //    [T -> T . U, {'a', '$'}]
        //    U -> 4
        //    'a' -> 3
        //    V -> 5
        // 2: [^ -> S ., {'$'}]
        // 3: [V -> 'a' ., {'b'}]
        // 4: [T -> T U ., {'a', '$'}]
        // 5: [U -> V . W, {'a', '$'}]
        //    'b' -> 7
        //    W -> 6
        // 6: [U -> V W ., {'a', '$'}]
        // 7: [W -> 'b' ., {'a', '$'}]

        let grm = YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, &stable, |_| 1);

        let s0 = StIdx::from(StIdxStorageT::zero());
        assert_eq!(d.dist(s0, grm.token_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.token_idx("b").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.eof_token_idx()), 0);

        let s1 = sgraph.edge(s0, Symbol::Rule(grm.rule_idx("T").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.token_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s1, grm.token_idx("b").unwrap()), 1);
        assert_eq!(d.dist(s1, grm.eof_token_idx()), 0);

        let s2 = sgraph.edge(s0, Symbol::Rule(grm.rule_idx("S").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.token_idx("a").unwrap()), u16::max_value());
        assert_eq!(d.dist(s2, grm.token_idx("b").unwrap()), u16::max_value());
        assert_eq!(d.dist(s2, grm.eof_token_idx()), 0);

        let s3 = sgraph.edge(s1, Symbol::Token(grm.token_idx("a").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.token_idx("a").unwrap()), 1);
        assert_eq!(d.dist(s3, grm.token_idx("b").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.eof_token_idx()), 1);

        let s4 = sgraph.edge(s1, Symbol::Rule(grm.rule_idx("U").unwrap())).unwrap();
        assert_eq!(d.dist(s4, grm.token_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s4, grm.token_idx("b").unwrap()), 1);
        assert_eq!(d.dist(s4, grm.eof_token_idx()), 0);

        let s5 = sgraph.edge(s1, Symbol::Rule(grm.rule_idx("V").unwrap())).unwrap();
        assert_eq!(d.dist(s5, grm.token_idx("a").unwrap()), 1);
        assert_eq!(d.dist(s5, grm.token_idx("b").unwrap()), 0);
        assert_eq!(d.dist(s5, grm.eof_token_idx()), 1);

        let s6 = sgraph.edge(s5, Symbol::Token(grm.token_idx("b").unwrap())).unwrap();
        assert_eq!(d.dist(s6, grm.token_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s6, grm.token_idx("b").unwrap()), 1);
        assert_eq!(d.dist(s6, grm.eof_token_idx()), 0);

        let s7 = sgraph.edge(s5, Symbol::Rule(grm.rule_idx("W").unwrap())).unwrap();
        assert_eq!(d.dist(s7, grm.token_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s7, grm.token_idx("b").unwrap()), 1);
        assert_eq!(d.dist(s7, grm.eof_token_idx()), 0);
    }

    fn check_some_repairs<StorageT: 'static + Hash + PrimInt + Unsigned>(
        grm: &YaccGrammar<StorageT>,
        err: &LexParseError<StorageT>,
        expected: &[&str]
    ) where
        usize: AsPrimitive<StorageT>
    {
        match err {
            LexParseError::ParseError(e) => {
                for exp in expected {
                    if e.repairs()
                        .iter()
                        .find(|x| &pp_repairs(&grm, x) == exp)
                        .is_none()
                    {
                        panic!("No match found for:\n  {}", exp);
                    }
                }
            }
            _ => unreachable!()
        }
    }

    fn check_all_repairs<StorageT: 'static + Debug + Hash + PrimInt + Unsigned>(
        grm: &YaccGrammar<StorageT>,
        err: &LexParseError<StorageT>,
        expected: &[&str]
    ) where
        usize: AsPrimitive<StorageT>
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
                    if expected
                        .iter()
                        .find(|x| **x == pp_repairs(&grm, &e.repairs()[i]))
                        .is_none()
                    {
                        panic!(
                            "No match found for:\n  {}",
                            pp_repairs(&grm, &e.repairs()[i])
                        );
                    }
                }
            }
            _ => unreachable!()
        }
    }

    #[test]
    #[rustfmt::skip]
    fn corchuelo_example() {
        // The example from the Corchuelo paper
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
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, us);
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
"]
            .iter()
            .any(|x| *x == pp) {
            panic!("Can't find a match for {}", pp);
        }

        assert_eq!(errs.len(), 1);
        let err_tok_id = u32::from(grm.token_idx("N").unwrap()).to_u16().unwrap();
        match &errs[0] {
            LexParseError::ParseError(e) => assert_eq!(e.lexeme(), &Lexeme::new(err_tok_id, 2, Some(1))),
            _ => unreachable!()
        }
        check_all_repairs(
            &grm,
            &errs[0],
            &[
                "Insert \")\", Insert \"+\"",
                "Insert \")\", Delete",
                "Insert \"+\", Shift, Insert \")\"",
            ]
        );

        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, "n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_all_repairs(&grm, &errs[0], &["Delete"]);
        check_all_repairs(&grm, &errs[1], &["Delete"]);

        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, "(((+n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_all_repairs(&grm, &errs[0], &["Insert \"N\"", "Delete"]);
        check_all_repairs(&grm, &errs[1], &["Insert \")\""]);
    }

    fn kimyi_lex_grm() -> (&'static str, &'static str) {
        // The example from the KimYi paper, with a bit of alpha-renaming to make it clearer. The
        // paper uses "A" as a rule name and "a" as a token name, which are then easily
        // confused. Here we use "E" as the rule name, and keep "a" as the token name.
        let lexs = "\\( '('
                    \\) ')'
                    a 'A'
                    b 'B'";
        let grms = "%start E
%%
E: '(' E ')'
 | 'A'
 | 'B' ;
";

        (lexs, grms)
    }

    #[test]
    fn kimyi_example() {
        let (lexs, grms) = kimyi_lex_grm();
        let us = "((";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (pt, errs) = pr.unwrap_err();
        let pp = pt.unwrap().pp(&grm, &us);
        if !vec![
            "E
 ( (
 E
  ( (
  E
   A 
  ) 
 ) 
",
            "E
 ( (
 E
  ( (
  E
   B 
  ) 
 ) 
",
        ]
        .iter()
        .any(|x| *x == pp)
        {
            panic!("Can't find a match for {}", pp);
        }
        assert_eq!(errs.len(), 1);
        let err_tok_id = u32::from(grm.eof_token_idx()).to_u16().unwrap();
        match &errs[0] {
            LexParseError::ParseError(e) => {
                assert_eq!(e.lexeme(), &Lexeme::new(err_tok_id, 2, None))
            }
            _ => unreachable!()
        }
        check_all_repairs(
            &grm,
            &errs[0],
            &vec![
                "Insert \"A\", Insert \")\", Insert \")\"",
                "Insert \"B\", Insert \")\", Insert \")\"",
            ]
        );
    }

    fn calc_grammar() -> (&'static str, &'static str) {
        let lexs = "\\( '('
                    \\) ')'
                    \\+ '+'
                    \\* '*'
                    [0-9] 'INT'";

        let grms = "%start Expr
%avoid_insert 'INT'
%%
Expr: Term '+' Expr
    | Term ;

Term: Factor '*' Term
    | Factor ;

Factor: '(' Expr ')'
      | 'INT' ;
";

        (lexs, grms)
    }

    #[test]
    fn test_exprs() {
        let (lexs, grms) = calc_grammar();
        let us = "(23";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(
            &grm,
            &errs[0],
            &[
                "Insert \")\", Insert \"+\"",
                "Insert \")\", Insert \"*\"",
                "Insert \")\", Delete",
                "Insert \"+\", Shift, Insert \")\"",
                "Insert \"*\", Shift, Insert \")\""
            ]
        );

        let us = "(+++++)";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_some_repairs(
            &grm,
            &errs[0],
            &["Insert \"INT\", Delete, Delete, Delete, Delete, Delete"]
        );
    }

    #[test]
    fn test_bias() {
        // If ranking biasing fails, this test will fail 50% of the time, so test it enough times
        // that we're likely to capture failure.
        for _ in 0..10 {
            let (lexs, grms) = calc_grammar();
            let us = "2++3";
            let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
            let (_, errs) = pr.unwrap_err();
            check_all_repairs(&grm, &errs[0], &vec!["Delete", "Insert \"INT\""]);
            if let LexParseError::ParseError(e) = &errs[0] {
                if let ParseRepair::Insert(_) = &e.repairs()[0][0] {
                    panic!("Ranking biasing failed");
                }
            }
        }
    }

    #[test]
    fn find_shortest() {
        let lexs = "a 'A'
                    b 'B'
                    c 'C'";

        let grms = "%start S
%%
S: T U 'C';
T: 'A';
U: 'B';
";

        let us = "c";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm, &errs[0], &["Insert \"A\", Insert \"B\""]);
    }

    #[test]
    fn deletes_after_inserts() {
        let lexs = "a 'A'
                    b 'B'
                    c 'C'
                    d 'D'";

        let grms = "%start S
%%
S:  'A' 'B' 'D' | 'A' 'B' 'C' 'A' 'A' 'D';
";

        let us = "acd";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm, &errs[0], &["Insert \"B\", Delete"]);
    }

    #[test]
    fn repair_empty_string() {
        let lexs = "a 'A'";

        let grms = "%start S
%%
S: 'A';
";

        let us = "";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm, &errs[0], &["Insert \"A\""]);
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
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(
            &grm,
            &errs[0],
            &[
                "Insert \"a\", Insert \"d\"",
                "Insert \"b\", Insert \"d\"",
                "Insert \"c\", Insert \"d\""
            ]
        );
    }

    #[test]
    fn test_cerecke_loop_limit() {
        // Example taken from p57 of Locally least-cost error repair in LR parsers, Carl Cerecke
        let lexs = "a 'a'
                    b 'b'
                    c 'c'";

        let grms = "%start S
%%
S: 'a' S 'b'
 | 'a' 'a' S 'c'
 | 'a';
";

        // The thesis incorrectly says that this can be repaired by inserting aaaaaa (i.e. 6 "a"s)
        // at the beginning: but the grammar only allows odd numbers of "a"s if the input ends with
        // a c, hence the actual repair should be aaaaaaa (i.e. 7 "a"s).
        let us = "ccc";
        let mut costs = HashMap::new();
        costs.insert("c", 3);
        let (grm, pr) = do_parse_with_costs(RecoveryKind::MF, &lexs, &grms, &us, &costs);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          &errs[0],
                          &["Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\""]);
    }

    #[test]
    fn test_cerecke_lr2() {
        // Example taken from p54 of Locally least-cost error repair in LR parsers, Carl Cerecke
        let lexs = "a 'a'
                    b 'b'
                    c 'c'
                    d 'd'
                    e 'e'";

        let grms = "%start S
%%
S: A 'c' 'd'
 | B 'c' 'e';
A: 'a';
B: 'a'
 | 'b';
A: 'b';
";

        do_parse(RecoveryKind::MF, &lexs, &grms, &"acd").1.unwrap();
        do_parse(RecoveryKind::MF, &lexs, &grms, &"bce").1.unwrap();
        let us = "ce";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm, &errs[0], &["Insert \"b\""]);
        let us = "cd";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm, &errs[0], &["Insert \"a\""]);
    }

    #[test]
    fn test_bertsch_nederhof1() {
        // Example from p5 of Bertsch and Nederhof "On Failure of the Pruning Technique in 'Error
        // Repair in Shift-reduce Parsers'"
        let lexs = "a 'a'
                    b 'b'
                    c 'c'
                    d 'd'";

        let grms = "%start S
%%
S: A A 'a' | 'b';
A: 'c' 'd';
";

        let us = "";
        let mut costs = HashMap::new();
        costs.insert("a", 1);
        costs.insert("b", 6);
        costs.insert("c", 1);
        costs.insert("d", 1);
        let (grm, pr) = do_parse_with_costs(RecoveryKind::MF, &lexs, &grms, &us, &costs);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(
            &grm,
            &errs[0],
            &["Insert \"c\", Insert \"d\", Insert \"c\", Insert \"d\", Insert \"a\""]
        );
    }

    #[test]
    fn test_bertsch_nederhof2() {
        // Example from p5 of Bertsch and Nederhof "On Failure of the Pruning Technique in 'Error
        // Repair in Shift-reduce Parsers'"
        let lexs = "a 'a'
                    c 'c'
                    d 'd'";

        let grms = "%start S
%%
S: A A 'a';
A: 'c' 'd';
";

        let us = "";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(
            &grm,
            &errs[0],
            &["Insert \"c\", Insert \"d\", Insert \"c\", Insert \"d\", Insert \"a\""]
        );
    }

    #[test]
    fn test_bertsch_nederhof3() {
        // Example from p8 of Bertsch and Nederhof "On Failure of the Pruning Technique in 'Error
        // Repair in Shift-reduce Parsers'"
        let lexs = "a 'a'
                    b 'b'
                    c 'c'
                    d 'd'";

        let grms = "%start S
%%
S: C D 'a' | D C 'b';
C: 'c';
D: 'd';
";

        let us = "";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(
            &grm,
            &errs[0],
            &[
                "Insert \"c\", Insert \"d\", Insert \"a\"",
                "Insert \"d\", Insert \"c\", Insert \"b\""
            ]
        );
    }

    #[test]
    fn test_counting_shifts() {
        let mut c: Cactus<RepairMerge<u8>> = Cactus::new();
        assert_eq!(ends_with_parse_at_least_shifts(&c), false);
        for _ in 0..PARSE_AT_LEAST - 1 {
            c = c.child(RepairMerge::Repair(Repair::Shift));
            assert_eq!(ends_with_parse_at_least_shifts(&c), false);
        }
        c = c.child(RepairMerge::Repair(Repair::Shift));
        assert_eq!(ends_with_parse_at_least_shifts(&c), true);

        let mut c: Cactus<RepairMerge<u8>> = Cactus::new();
        assert_eq!(ends_with_parse_at_least_shifts(&c), false);
        c = c.child(RepairMerge::Repair(Repair::Delete));
        for _ in 0..PARSE_AT_LEAST - 1 {
            c = c.child(RepairMerge::Repair(Repair::Shift));
            assert_eq!(ends_with_parse_at_least_shifts(&c), false);
        }
        c = c.child(RepairMerge::Repair(Repair::Shift));
        assert_eq!(ends_with_parse_at_least_shifts(&c), true);
    }
}
