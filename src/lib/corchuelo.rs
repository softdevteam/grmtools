// Copyright (c) 2017 King's College London
// created by the Software Development Team <http://soft-dev.org/>
//
// The Universal Permissive License (UPL), Version 1.0
//
// Subject to the condition set forth below, permission is hereby granted to any person obtaining a
// copy of this software, associated documentation and/or data (collectively the "Software"), free
// of charge and under any and all copyright rights in the Software, and any and all patent rights
// owned or freely licensable by each licensor hereunder covering either (i) the unmodified
// Software as contributed to or provided by such licensor, or (ii) the Larger Works (as defined
// below), to deal in both
//
// (a) the Software, and
// (b) any piece of software and/or hardware listed in the lrgrwrks.txt file
// if one is included with the Software (each a "Larger Work" to which the Software is contributed
// by such licensors),
//
// without restriction, including without limitation the rights to copy, create derivative works
// of, display, perform, and distribute the Software and make, use, sell, offer for sale, import,
// export, have made, and have sold the Software and the Larger Work(s), and to sublicense the
// foregoing rights on either these or other terms.
//
// This license is subject to the following condition: The above copyright notice and either this
// complete permission notice or at a minimum a reference to the UPL must be included in all copies
// or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING
// BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
// DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::time::Instant;

use cactus::Cactus;
use cfgrammar::{Symbol, TIdx};
use lrlex::Lexeme;
use lrtable::{Action, StIdx};
use num_traits::{PrimInt, Unsigned};

use astar::dijkstra;
use mf::apply_repairs;
use parser::{Node, Parser, ParseRepair, Recoverer};

const PARSE_AT_LEAST: usize = 3; // N in Corchuelo et al.
const PORTION_THRESHOLD: usize = 5; // N_t in Corchuelo et al.
const TRY_PARSE_AT_MOST: usize = 250;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Repair {
    /// Insert a `Symbol::Term` with idx `term_idx`.
    InsertTerm(TIdx),
    /// Delete a symbol.
    Delete,
    /// Shift a symbol.
    Shift
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum RepairMerge {
    Repair(Repair),
    Merge(Repair, Cactus<Cactus<RepairMerge>>),
    Terminator
}

#[derive(Clone, Debug, Eq)]
struct PathFNode {
    pstack: Cactus<StIdx>,
    la_idx: usize,
    repairs: Cactus<RepairMerge>,
    cf: u32
}

impl PathFNode {
    fn last_repair(&self) -> Option<Repair> {
        match self.repairs.val().unwrap() {
            &RepairMerge::Repair(r) => Some(r),
            &RepairMerge::Merge(x, _) => Some(x),
            &RepairMerge::Terminator => None
        }
    }
}

impl Hash for PathFNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.pstack.hash(state);
        self.la_idx.hash(state);
    }
}

impl PartialEq for PathFNode {
    fn eq(&self, other: &PathFNode) -> bool {
        if self.la_idx != other.la_idx || self.pstack != other.pstack {
            return false;
        }
        // The rest of this function is subtle: we're not looking for repairs which are exactly
        // equivalent, but ones that are compatible. This is necessary so that we can merge
        // compatible nodes. Our definition of compatible repairs is simple: they must end with
        // exactly the same number of shifts. Ending with zero shifts is fine: so two repair
        // sequences that end with (say) a Delete and an InsertTerm are compatible by definition.
        for (srm, orm) in self.repairs.vals().zip(other.repairs.vals()) {
            match (srm, orm) {
                (&RepairMerge::Repair(sr), &RepairMerge::Repair(or))
                | (&RepairMerge::Merge(sr, _), &RepairMerge::Repair(or))
                | (&RepairMerge::Repair(sr), &RepairMerge::Merge(or, _))
                | (&RepairMerge::Merge(sr, _), &RepairMerge::Merge(or, _)) => {
                    match (sr, or) {
                        (Repair::Shift, Repair::Shift) => (),
                        (Repair::Shift, _) | (_, Repair::Shift) => return false,
                        _ => {
                            // As soon as we come across two repairs which aren't shifts, we know
                            // that we must have satisfied the "must end with the same number of
                            // shifts" constraint and can bail out.
                            return true;
                        }
                    }
                },
                (&RepairMerge::Terminator, &RepairMerge::Terminator)
                    => return true,
                (&RepairMerge::Terminator, _) | (_, &RepairMerge::Terminator)
                    => return false
            }
        }
        unreachable!()
    }
}

struct Corchuelo<'a, TokId: PrimInt + Unsigned> where TokId: 'a {
    parser: &'a Parser<'a, TokId>
}

pub(crate) fn recoverer<'a, TokId: PrimInt + Unsigned>
                       (parser: &'a Parser<TokId>)
                     -> Box<Recoverer<TokId> + 'a>
{
    Box::new(Corchuelo{parser})
}

impl<'a, TokId: PrimInt + Unsigned> Recoverer<TokId> for Corchuelo<'a, TokId>

{
    fn recover(&self,
               finish_by: Instant,
               parser: &Parser<TokId>,
               in_la_idx: usize,
               in_pstack: &mut Vec<StIdx>,
               mut tstack: &mut Vec<Node<TokId>>)
           -> (usize, Vec<Vec<ParseRepair>>)
    {
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
        for st in in_pstack.drain(..) {
            start_cactus_pstack = start_cactus_pstack.child(st);
        }

        let start_node = PathFNode{pstack: start_cactus_pstack.clone(),
                                   la_idx: in_la_idx,
                                   repairs: Cactus::new().child(RepairMerge::Terminator),
                                   cf: 0};
        let astar_cnds = dijkstra(
            start_node,
            |explore_all, n, nbrs| {
                // Calculate n's neighbours.

                if Instant::now() >= finish_by {
                    return false;
                }

                if n.la_idx > in_la_idx + PORTION_THRESHOLD {
                    return true;
                }

                match n.last_repair() {
                    Some(Repair::Delete) => {
                        // We follow Corcheulo et al.'s suggestions and never follow Deletes with
                        // Inserts.
                    },
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
                let merge = match old.repairs.val().unwrap() {
                    &RepairMerge::Repair(r) => {
                        RepairMerge::Merge(r, Cactus::new().child(new.repairs))
                    },
                    &RepairMerge::Merge(r, ref v) => {
                        RepairMerge::Merge(r, v.child(new.repairs))
                    },
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

                match parser.stable.action(*n.pstack.val().unwrap(),
                                           parser.next_tidx(n.la_idx)) {
                    Some(Action::Accept) => true,
                    _ => false,
                }
            });

        if astar_cnds.is_empty() {
            return (in_la_idx, vec![]);
        }

        let full_rprs = self.collect_repairs(astar_cnds);
        let smpl_rprs = self.simplify_repairs(full_rprs);
        let rnk_rprs = self.rank_cnds(in_la_idx,
                                      &start_cactus_pstack,
                                      smpl_rprs);
        let (la_idx, mut rpr_pstack) = apply_repairs(parser,
                                                     in_la_idx,
                                                     start_cactus_pstack,
                                                     &mut Some(&mut tstack),
                                                     &rnk_rprs[0]);

        in_pstack.clear();
        while !rpr_pstack.is_empty() {
            let p = rpr_pstack.parent().unwrap();
            in_pstack.push(rpr_pstack.try_unwrap()
                                     .unwrap_or_else(|c| *c.val()
                                                           .unwrap()));
            rpr_pstack = p;
        }
        in_pstack.reverse();

        (la_idx, rnk_rprs)
    }
}

impl<'a, TokId: PrimInt + Unsigned> Corchuelo<'a, TokId> {
    fn insert(&self,
             n: &PathFNode,
             nbrs: &mut Vec<(u32, PathFNode)>)
    {
        let la_idx = n.la_idx;
        for sym in self.parser.stable.state_actions(*n.pstack.val().unwrap()) {
            if let Symbol::Term(t_idx) = sym {
                if t_idx == self.parser.grm.eof_term_idx() {
                    continue;
                }

                if let Some(Repair::Shift) = n.last_repair() {
                    debug_assert!(n.la_idx > 0);
                    // If we're about to insert term T and the next terminal in the user's
                    // input is T, we could potentially end up with two similar repair
                    // sequences:
                    //   Insert T, Shift
                    //   Shift, Insert T
                    // From a user's perspective, both of those are equivalent. From our point
                    // of view, the duplication is inefficient. We prefer the former sequence
                    // because we want to find PARSE_AT_LEAST consecutive shifts. At this
                    // point, we see if we're about to Insert T after a Shift of T and, if so,
                    // avoid doing so.
                    let prev_tidx = self.parser.next_tidx(la_idx - 1);
                    if prev_tidx == t_idx {
                        continue;
                    }
                }

                let next_lexeme = self.parser.next_lexeme(n.la_idx);
                let new_lexeme = Lexeme::new(TokId::from(u32::from(t_idx)).unwrap(),
                                             next_lexeme.start(), 0);
                let (new_la_idx, n_pstack) =
                    self.parser.lr_cactus(Some(new_lexeme), la_idx, la_idx + 1,
                                          n.pstack.clone(), &mut None);
                if new_la_idx > la_idx {
                    let nn = PathFNode{
                        pstack: n_pstack,
                        la_idx: n.la_idx,
                        repairs: n.repairs.child(RepairMerge::Repair(Repair::InsertTerm(t_idx))),
                        cf: n.cf.checked_add((self.parser.term_cost)(t_idx) as u32).unwrap()};
                    nbrs.push((nn.cf, nn));
                }
            }
        }
    }

    fn delete(&self,
           n: &PathFNode,
           nbrs: &mut Vec<(u32, PathFNode)>)
    {
        if n.la_idx == self.parser.lexemes.len() {
            return;
        }

        let la_tidx = self.parser.next_tidx(n.la_idx);
        let cost = (self.parser.term_cost)(la_tidx);
        let nn = PathFNode{pstack: n.pstack.clone(),
                           la_idx: n.la_idx + 1,
                           repairs: n.repairs.child(RepairMerge::Repair(Repair::Delete)),
                           cf: n.cf.checked_add(cost as u32).unwrap()};
        nbrs.push((nn.cf, nn));
    }

    fn shift(&self,
             n: &PathFNode,
             nbrs: &mut Vec<(u32, PathFNode)>)
    {
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

        let la_idx = n.la_idx;
        let (new_la_idx, n_pstack) = self.parser.lr_cactus(None,
                                                           la_idx,
                                                           la_idx + 1,
                                                           n.pstack.clone(),
                                                           &mut None);
        if n.pstack != n_pstack {
            let n_repairs = if new_la_idx > la_idx {
                n.repairs.child(RepairMerge::Repair(Repair::Shift))
            } else {
                n.repairs.clone()
            };
            let nn = PathFNode{
                pstack: n_pstack,
                la_idx: new_la_idx,
                repairs: n_repairs,
                cf: n.cf};
            nbrs.push((nn.cf, nn));
        }
    }

    /// Convert the output from `astar_all` into something more usable.
    fn collect_repairs(&self, cnds: Vec<PathFNode>) -> Vec<Vec<Repair>>
    {
        fn traverse(rm: &Cactus<RepairMerge>) -> Vec<Vec<Repair>> {
            let mut out = Vec::new();
            match rm.val().unwrap() {
                &RepairMerge::Repair(r) => {
                    let parents = traverse(&rm.parent().unwrap());
                    if parents.is_empty() {
                        out.push(vec![r]);
                    } else {
                        for mut pc in parents {
                            pc.push(r);
                            out.push(pc);
                        }
                    }
                },
                &RepairMerge::Merge(r, ref vc) => {
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
                        for mut pc in traverse(c) {
                            out.push(pc);
                        }
                    }
                }
                &RepairMerge::Terminator => ()
            }
            out
        }

        let mut all_rprs = Vec::with_capacity(cnds.len());
        for cnd in cnds {
            all_rprs.extend(traverse(&cnd.repairs));
        }
        all_rprs
    }

    /// Take an (unordered) set of parse repairs and return a simplified (unordered) set of parse
    /// repairs. Note that the caller must make no assumptions about the size or contents of the output
    /// set: this function might delete, expand, or do other things to repairs.
    fn simplify_repairs(&self,
                        mut all_rprs: Vec<Vec<Repair>>)
                     -> Vec<Vec<ParseRepair>>
    {
        for i in 0..all_rprs.len() {
            {
                // Remove shifts from the end of repairs
                let mut rprs = &mut all_rprs[i];
                while !rprs.is_empty() {
                    if let Repair::Shift = rprs[rprs.len() - 1] {
                        rprs.pop();
                    } else {
                        break;
                    }
                }
            }
        }

        // The simplifications above can mean that we now end up with equivalent repairs. Remove
        // duplicates.

        let mut i = 0;
        while i < all_rprs.len() {
            let mut j = i + 1;
            while j < all_rprs.len() {
                if all_rprs[i] == all_rprs[j] {
                    all_rprs.remove(j);
                } else {
                    j += 1;
                }
            }
            i += 1;
        }

        all_rprs.iter()
                .map(|x| x.iter()
                          .map(|y| {
                                        match *y {
                                            Repair::InsertTerm(term_idx) =>
                                                ParseRepair::Insert(term_idx),
                                            Repair::Delete => ParseRepair::Delete,
                                            Repair::Shift => ParseRepair::Shift,
                                        }
                               })
                          .collect())
                      .collect()
    }

    /// Convert `PathFNode` candidates in `cnds` into vectors of `ParseRepairs`s and rank them (from
    /// highest to lowest) by the distance they allow parsing to continue without error. If two or more
    /// `ParseRepair`s allow the same distance of parsing, then the `ParseRepair` which requires
    /// repairs over the shortest distance is preferred. Amongst `ParseRepair`s of the same rank, the
    /// ordering is non-deterministic.
    fn rank_cnds(&self,
                 in_la_idx: usize,
                 start_pstack: &Cactus<StIdx>,
                 in_cnds: Vec<Vec<ParseRepair>>)
              -> Vec<Vec<ParseRepair>>
    {
        let mut cnds = in_cnds.into_iter()
                              .map(|rprs| {
                                   let (la_idx, pstack) = apply_repairs(self.parser,
                                                                        in_la_idx,
                                                                        start_pstack.clone(),
                                                                        &mut None,
                                                                        &rprs);
                                   (pstack, la_idx, rprs)
                               })
                              .collect::<Vec<(Cactus<StIdx>, usize, Vec<ParseRepair>)>>();

        // First try parsing each candidate repair until it hits an error or exceeds TRY_PARSE_AT_MOST
        // lexemes.

        let mut todo = Vec::new();
        todo.resize(cnds.len(), true);
        let mut remng = cnds.len(); // Remaining items in todo
        let mut i = 0;
        while i < TRY_PARSE_AT_MOST && remng > 1 {
            let mut j = 0;
            while j < todo.len() {
                if !todo[j] {
                    j += 1;
                    continue;
                }
                let cnd = &mut cnds[j];
                if cnd.1 > in_la_idx + i {
                    j += 1;
                    continue;
                }
                let (new_la_idx, new_pstack) = self.parser.lr_cactus(None,
                                                                     in_la_idx + i,
                                                                     in_la_idx + i + 1,
                                                                     cnd.0.clone(),
                                                                     &mut None);
                if new_la_idx == in_la_idx + i {
                    todo[j] = false;
                    remng -= 1;
                } else {
                    cnd.0 = new_pstack;
                    cnd.1 += 1;
                }
                j += 1;
            }
            i += 1;
        }

        // Now rank the candidates into descending order, first by how far they are able to parse, then
        // by the number of actions in the repairs (the latter is somewhat arbitrary, but matches the
        // intuition that "repairs which affect the shortest part of the string are preferable").
        cnds.sort_unstable_by(|x, y| {
            match y.1.cmp(&x.1) {
                Ordering::Equal => {
                    x.2.len().cmp(&y.2.len())
                },
                a => a
            }
        });

        cnds.into_iter()
            .map(|x| x.2)
            .collect::<Vec<Vec<ParseRepair>>>()
    }
}

/// Do `repairs` end with enough Shift repairs to be considered a success node?
fn ends_with_parse_at_least_shifts(repairs: &Cactus<RepairMerge>) -> bool {
    let mut shfts = 0;
    for x in repairs.vals().take(PARSE_AT_LEAST) {
        match x {
            &RepairMerge::Repair(Repair::Shift) => shfts += 1,
            &RepairMerge::Merge(Repair::Shift, _) => shfts += 1,
            _ => return false
        }
    }
    shfts == PARSE_AT_LEAST
}

#[cfg(test)]
mod test {
    use cfgrammar::yacc::YaccGrammar;
    use lrlex::Lexeme;
    use num_traits::ToPrimitive;
    use parser::{ParseRepair, RecoveryKind};
    use parser::test::do_parse;

    fn pp_repairs(grm: &YaccGrammar, repairs: &Vec<ParseRepair>) -> String {
        let mut out = vec![];
        for r in repairs.iter() {
            match *r {
                ParseRepair::InsertSeq{..} => panic!("Internal error"),
                ParseRepair::Insert(term_idx) =>
                    out.push(format!("Insert \"{}\"", grm.term_name(term_idx).unwrap())),
                ParseRepair::Delete =>
                    out.push(format!("Delete")),
                ParseRepair::Shift =>
                    out.push(format!("Shift"))
            }
        }
        out.join(", ")
    }

    fn check_all_repairs(grm: &YaccGrammar,
                                    repairs: &Vec<Vec<ParseRepair>>,
                                    expected: &[&str]) {
        assert_eq!(repairs.len(), expected.len(),
                   "{:?}\nhas a different number of entries to:\n{:?}", repairs, expected);
        for i in 0..repairs.len() {
            if expected.iter().find(|x| **x == pp_repairs(&grm, &repairs[i])).is_none() {
                panic!("No match found for:\n  {}", pp_repairs(&grm, &repairs[i]));
            }
        }
    }

    #[test]
    fn corchuelo_example() {
        // The example from the Curchuelo paper
        let lexs = "%%
[(] OPEN_BRACKET
[)] CLOSE_BRACKET
[+] PLUS
n N
";
        let grms = "%start E
%%
E : 'N'
  | E 'PLUS' 'N'
  | 'OPEN_BRACKET' E 'CLOSE_BRACKET'
  ;
";

        let us = "(nn";
        let (grm, pr) = do_parse(RecoveryKind::Corchuelo, &lexs, &grms, us);
        let (pt, errs) = pr.unwrap_err();
        let pp = pt.unwrap().pp(&grm, us);
        // Note that:
        //   E
        //    OPEN_BRACKET (
        //    E
        //     E
        //      N n
        //     PLUS 
        //     N n
        //    CLOSE_BRACKET 
        // is also the result of a valid minimal-cost repair, but, since the repair involves a
        // Shift, rank_cnds will always put this too low down the list for us to ever see it.
        if !vec![
"E
 OPEN_BRACKET (
 E
  N n
 CLOSE_BRACKET 
",
"E
 E
  OPEN_BRACKET (
  E
   N n
  CLOSE_BRACKET 
 PLUS 
 N n
"]
            .iter()
            .any(|x| *x == pp) {
            panic!("Can't find a match for {}", pp);
        }

        assert_eq!(errs.len(), 1);
        let err_tok_id = u32::from(grm.term_idx("N").unwrap()).to_u16().unwrap();
        assert_eq!(errs[0].lexeme(), &Lexeme::new(err_tok_id, 2, 1));
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"CLOSE_BRACKET\", Insert \"PLUS\"",
                                "Insert \"CLOSE_BRACKET\", Delete",
                                "Insert \"PLUS\", Shift, Insert \"CLOSE_BRACKET\""]);

        let (grm, pr) = do_parse(RecoveryKind::Corchuelo, &lexs, &grms, "n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Delete"]);
        check_all_repairs(&grm,
                          errs[1].repairs(),
                          &vec!["Delete"]);

        let (grm, pr) = do_parse(RecoveryKind::Corchuelo, &lexs, &grms, "(((+n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"N\"",
                                "Delete"]);
        check_all_repairs(&grm,
                          errs[1].repairs(),
                          &vec!["Insert \"CLOSE_BRACKET\""]);
    }

    #[test]
    fn test_merge() {
        let lexs = "%%
a a
b b
c c
d d
";

        let grms = "%start S
%%
S: T U;
T: T1 | 'b' | T2;
T1: 'a';
T2: 'c' | 'a' 'b' 'c';
U: 'd';
";

        let us = "";
        let (grm, pr) = do_parse(RecoveryKind::Corchuelo, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"a\", Insert \"d\"",
                                "Insert \"b\", Insert \"d\"",
                                "Insert \"c\", Insert \"d\""]);
    }
}
