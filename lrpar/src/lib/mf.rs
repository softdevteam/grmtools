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

use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::mem;
use std::time::Instant;

use cactus::Cactus;
use cfgrammar::{Grammar, Symbol, TIdx};
use cfgrammar::yacc::YaccGrammar;
use lrlex::Lexeme;
use lrtable::{Action, StateGraph, StateTable, StIdx};
use num_traits::{PrimInt, Unsigned};
use vob::Vob;

use astar::astar_all;
use parser::{Node, Parser, ParseRepair, Recoverer};

const PARSE_AT_LEAST: usize = 3; // N in Corchuelo et al.
const TRY_PARSE_AT_MOST: usize = 250;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
enum Repair<StorageT> {
    /// Insert a `Symbol::Term` with idx `term_idx`.
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
    la_idx: usize,
    repairs: Cactus<RepairMerge<StorageT>>,
    cf: u32,
    cg: u32
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
        self.la_idx.hash(state);
    }
}

impl<StorageT: PrimInt + Unsigned> PartialEq for PathFNode<StorageT> {
    fn eq(&self, other: &PathFNode<StorageT>) -> bool {
        if self.la_idx != other.la_idx || self.pstack != other.pstack {
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
                      RepairMerge::Repair(Repair::Shift)
                    | RepairMerge::Merge(Repair::Shift, _) => n += 1,
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

impl<StorageT: PrimInt + Unsigned> Eq for PathFNode<StorageT> { }

struct MF<'a, StorageT: 'a + Eq + Hash, TokId: 'a> {
    dist: Dist<StorageT>,
    parser: &'a Parser<'a, StorageT, TokId>
}

pub(crate) fn recoverer<'a,
                        StorageT: Debug + Hash + PrimInt + Unsigned,
                        TokId: PrimInt + Unsigned>
                       (parser: &'a Parser<StorageT, TokId>)
                     -> Box<Recoverer<StorageT, TokId> + 'a>
{
    let dist = Dist::new(parser.grm, parser.sgraph, parser.stable, parser.term_cost);
    Box::new(MF{dist, parser})
}

impl<'a,
     StorageT: Debug + Hash + PrimInt + Unsigned,
     TokId: PrimInt + Unsigned>
Recoverer<StorageT, TokId> for MF<'a, StorageT, TokId>
{
    fn recover(&self,
               finish_by: Instant,
               parser: &Parser<StorageT, TokId>,
               in_la_idx: usize,
               mut in_pstack: &mut Vec<StIdx>,
               mut tstack: &mut Vec<Node<StorageT, TokId>>)
           -> (usize, Vec<Vec<ParseRepair<StorageT>>>)
    {
        let mut start_cactus_pstack = Cactus::new();
        for st in in_pstack.iter() {
            start_cactus_pstack = start_cactus_pstack.child(*st);
        }

        let start_node = PathFNode{pstack: start_cactus_pstack.clone(),
                                   la_idx: in_la_idx,
                                   repairs: Cactus::new().child(RepairMerge::Terminator),
                                   cf: 0,
                                   cg: 0};

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
                    },
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
                    },
                    RepairMerge::Merge(r, ref v) => {
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
        let mut rnk_rprs = rank_cnds(parser,
                                     finish_by,
                                     in_la_idx,
                                     &in_pstack,
                                     full_rprs);
        if rnk_rprs.is_empty() {
            return (in_la_idx, vec![]);
        }
        simplify_repairs(&mut rnk_rprs);
        let la_idx = apply_repairs(parser,
                                   in_la_idx,
                                   &mut in_pstack,
                                   &mut Some(&mut tstack),
                                   &rnk_rprs[0]);

        (la_idx, rnk_rprs)
    }
}

impl<'a,
     StorageT: Debug + Hash + PrimInt + Unsigned,
     TokId: PrimInt + Unsigned>
MF<'a, StorageT, TokId>
{
    fn insert(&self,
              n: &PathFNode<StorageT>,
              nbrs: &mut Vec<(u32, u32, PathFNode<StorageT>)>)
    {
        let top_pstack = *n.pstack.val().unwrap();
        for t_idx in self.parser.stable.state_shifts(top_pstack) {
            if t_idx == self.parser.grm.eof_term_idx() {
                continue;
            }

            let t_st_idx = match self.parser.stable.action(top_pstack, t_idx).unwrap() {
                Action::Shift(s_idx) => s_idx,
                _ => unreachable!()
            };
            let n_repairs = n.repairs.child(RepairMerge::Repair(Repair::InsertTerm(t_idx)));
            if let Some(d) = self.dyn_dist(&n_repairs, t_st_idx, n.la_idx) {
                assert!(n.cg == 0 || d >= n.cg - u32::from((self.parser.term_cost)(t_idx)));
                let nn = PathFNode{
                    pstack: n.pstack.child(t_st_idx),
                    la_idx: n.la_idx,
                    repairs: n_repairs,
                    cf: n.cf.checked_add(u32::from((self.parser.term_cost)(t_idx))).unwrap(),
                    cg: d};
                nbrs.push((nn.cf, nn.cg, nn));
            }
        }
    }

    fn reduce(&self,
              n: &PathFNode<StorageT>,
              nbrs: &mut Vec<(u32, u32, PathFNode<StorageT>)>)
    {
        let top_pstack = *n.pstack.val().unwrap();
        for p_idx in self.parser.stable.core_reduces(top_pstack) {
            let sym_off = self.parser.grm.prod(p_idx).len();
            let nt_idx = self.parser.grm.prod_to_nonterm(p_idx);
            let mut qi_minus_alpha = n.pstack.clone();
            for _ in 0..sym_off {
                qi_minus_alpha = qi_minus_alpha.parent().unwrap();
            }

            if let Some(mut goto_st_idx) = self.parser.stable
                                                  .goto(*qi_minus_alpha.val().unwrap(),
                                                        nt_idx) {
                // We want to reduce/goto goto_st_idx. However if that state only contains
                // reductions and if all reductions are the same, we can skip over it.
                while self.parser.stable.reduce_only_state(goto_st_idx) {
                    let p_idx = self.parser.stable.core_reduces(goto_st_idx).last().unwrap();
                    let sym_off = self.parser.grm.prod(p_idx).len();
                    let nt_idx = self.parser.grm.prod_to_nonterm(p_idx);
                    // Technically we should push goto_st_idx, and then pop sym_off elements, but
                    // we can avoid the push in cases where sym_off is greater than 0, compensating
                    // for that by poping (sym_off - 1) elements.
                    if sym_off == 0 {
                        qi_minus_alpha = qi_minus_alpha.child(goto_st_idx);
                    } else {
                        for _ in 0..sym_off - 1 {
                            qi_minus_alpha = qi_minus_alpha.parent().unwrap();
                        }
                    }
                    if let Some(x) = self.parser.stable.goto(*qi_minus_alpha.val().unwrap(),
                                                             nt_idx) {
                        goto_st_idx = x;
                    } else {
                        return;
                    }
                }

                if let Some(d) = self.dyn_dist(&n.repairs, goto_st_idx, n.la_idx) {
                    let nn = PathFNode{
                        pstack: qi_minus_alpha.child(goto_st_idx),
                        la_idx: n.la_idx,
                        repairs: n.repairs.clone(),
                        cf: n.cf,
                        cg: d};
                    nbrs.push((nn.cf, nn.cg, nn));
                }
            }
        }
    }

    fn delete(&self,
              n: &PathFNode<StorageT>,
              nbrs: &mut Vec<(u32, u32, PathFNode<StorageT>)>)
    {
        if n.la_idx == self.parser.lexemes.len() {
            return;
        }

        let n_repairs = n.repairs.child(RepairMerge::Repair(Repair::Delete));
        if let Some(d) = self.dyn_dist(&n_repairs, *n.pstack.val().unwrap(), n.la_idx + 1) {
            let la_tidx = self.parser.next_tidx(n.la_idx);
            let cost = (self.parser.term_cost)(la_tidx);
            let nn = PathFNode{pstack: n.pstack.clone(),
                               la_idx: n.la_idx + 1,
                               repairs: n_repairs,
                               cf: n.cf.checked_add(u32::from(cost)).unwrap(),
                               cg: d};
            nbrs.push((nn.cf, nn.cg, nn));
        }
    }

    fn shift(&self,
             n: &PathFNode<StorageT>,
             nbrs: &mut Vec<(u32, u32, PathFNode<StorageT>)>)
    {
        let la_tidx = self.parser.next_tidx(n.la_idx);
        let top_pstack = *n.pstack.val().unwrap();
        if let Some(Action::Shift(state_id)) = self.parser.stable.action(top_pstack,
                                                                         la_tidx) {
            let n_repairs = n.repairs.child(RepairMerge::Repair(Repair::Shift));
            let new_la_idx = n.la_idx + 1;
            if let Some(d) = self.dyn_dist(&n_repairs, state_id, new_la_idx) {
                let nn = PathFNode{
                    pstack: n.pstack.child(state_id),
                    la_idx: new_la_idx,
                    repairs: n_repairs,
                    cf: n.cf,
                    cg: d};
                nbrs.push((nn.cf, nn.cg, nn));
            }
        }
    }

    /// Convert the output from `astar_all` into something more usable.
    fn collect_repairs(&self, cnds: Vec<PathFNode<StorageT>>) -> Vec<Vec<Vec<ParseRepair<StorageT>>>>
    {
        fn traverse<StorageT: PrimInt + Unsigned>
                   (rm: &Cactus<RepairMerge<StorageT>>)
                 -> Vec<Vec<Repair<StorageT>>> {
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
                },
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
                        for mut pc in traverse(c) {
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
            all_rprs.push(traverse(&cnd.repairs).into_iter()
                                                .map(|x| self.repair_to_parse_repair(x))
                                                .collect::<Vec<_>>());
        }
        all_rprs
    }

    fn repair_to_parse_repair(&self,
                              from: Vec<Repair<StorageT>>)
                           -> Vec<ParseRepair<StorageT>> {
        from.iter()
            .map(|y| {
                 match *y {
                     Repair::InsertTerm(term_idx) =>
                         ParseRepair::Insert(term_idx),
                     Repair::Delete => ParseRepair::Delete,
                     Repair::Shift => ParseRepair::Shift,
                 }
             })
            .collect()
    }

    /// Return the distance from `st_idx` at input position `la_idx`, given the current `repairs`.
    /// Returns `None` if no route can be found.
    fn dyn_dist(&self,
                repairs: &Cactus<RepairMerge<StorageT>>,
                st_idx: StIdx,
                la_idx: usize)
              -> Option<u32>
    {
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
        // deletions. Imagine that there are two lexemes starting at position la_idx: (in order) T
        // and U, both with a term_cost of 1. Assume the dist() from st_idx to T is 2 and the
        // dist() from st_idx to U is 0. If we delete T then the distance to U is 1, which is a
        // shorter distance than T. We therefore need to return a distance of 1, even though that
        // is the distance to the second lexeme.
        //
        // Imagine we have the Java input "x = } y;". The distance from "=" to "}" is 2 (at a
        // minimum you need an int/string/etc followed by a semi-colon); however the distance from
        // "=" to "y" is 0. Assuming the deletion cost of "}" is 1, it's therefore cheaper to
        // delete "}" and add that to the distance from "=" to "y". Thus the cheapest distance is
        // 1.
        let mut ld = u32::max_value(); // ld == Current least distance
        let mut dc = 0; // Cumulative deletion cost
        for i in la_idx..self.parser.lexemes.len() + 1 {
            let t_idx = self.parser.next_tidx(i);
            let d = self.dist.dist(st_idx, t_idx);
            if d < u32::max_value() && dc + d < ld {
                ld = dc + d;
            }
            dc += u32::from((self.parser.term_cost)(t_idx));
            if dc >= ld {
                // Once the cumulative cost of deleting lexemes is bigger than the current least
                // distance, there is no chance of finding a subsequent lexeme which could produce
                // a lower cost.
                break;
            }
        }
        if ld == u32::max_value() {
            None
        } else {
            Some(ld)
        }
    }
}

/// Do `repairs` end with enough Shift repairs to be considered a success node?
fn ends_with_parse_at_least_shifts<StorageT>
                                  (repairs: &Cactus<RepairMerge<StorageT>>)
                                -> bool
{
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

/// Convert `PathFNode` candidates in `cnds` into vectors of `ParseRepairs`s and rank them (from
/// highest to lowest) by the distance they allow parsing to continue without error. If two or more
/// `ParseRepair`s allow the same distance of parsing, then the `ParseRepair` which requires
/// repairs over the shortest distance is preferred. Amongst `ParseRepair`s of the same rank, the
/// ordering is non-deterministic.
pub(crate) fn rank_cnds<StorageT: Debug + Hash + PrimInt + Unsigned,
                        TokId: PrimInt + Unsigned>
                       (parser: &Parser<StorageT, TokId>,
                        finish_by: Instant,
                        in_la_idx: usize,
                        in_pstack: &Vec<StIdx>,
                        in_cnds: Vec<Vec<Vec<ParseRepair<StorageT>>>>)
                     -> Vec<Vec<ParseRepair<StorageT>>>
{
    let mut cnds = Vec::new();
    let mut furthest = 0;
    for rpr_seqs in in_cnds {
        if Instant::now() >= finish_by {
            return vec![];
        }
        let mut pstack = in_pstack.clone();
        let mut la_idx = apply_repairs(parser,
                                       in_la_idx,
                                       &mut pstack,
                                       &mut None,
                                       &rpr_seqs[0]);
        la_idx = parser.lr_upto(None,
                                la_idx,
                                in_la_idx + TRY_PARSE_AT_MOST,
                                &mut pstack,
                                &mut None);
        if la_idx >= furthest {
            furthest = la_idx;
        }
        cnds.push((pstack, la_idx, rpr_seqs));
    }

    // Remove any elements except those which parsed as far as possible.
    cnds = cnds.into_iter().filter(|x| x.1 == furthest).collect::<Vec<_>>();

    cnds.into_iter()
        .flat_map(|x| x.2)
        .collect::<Vec<_>>()
}

/// Apply the `repairs` to `pstack` starting at position `la_idx`: return the resulting parse
/// distance and a new pstack.
pub(crate) fn apply_repairs<StorageT: Debug + Hash + PrimInt + Unsigned,
                            TokId: PrimInt + Unsigned>
                           (parser: &Parser<StorageT, TokId>,
                            mut la_idx: usize,
                            mut pstack: &mut Vec<StIdx>,
                            mut tstack: &mut Option<&mut Vec<Node<StorageT, TokId>>>,
                            repairs: &[ParseRepair<StorageT>])
                         -> usize
{
    for r in repairs.iter() {
        match *r {
            ParseRepair::InsertSeq(_) => unreachable!(),
            ParseRepair::Insert(t_idx) => {
                let next_lexeme = parser.next_lexeme(la_idx);
                let new_lexeme = Lexeme::new(TokId::from(u32::from(t_idx)).unwrap(),
                                             next_lexeme.start(), 0);
                parser.lr_upto(Some(new_lexeme),
                               la_idx,
                               la_idx + 1,
                               &mut pstack,
                               &mut tstack);
            },
            ParseRepair::Delete => {
                la_idx += 1;
            }
            ParseRepair::Shift => {
                la_idx = parser.lr_upto(None,
                                        la_idx,
                                        la_idx + 1,
                                        &mut pstack,
                                        &mut tstack);
            }
        }
    }
    la_idx
}

/// Simplifies repair sequences, removes duplicates, and sorts them into order.
pub(crate) fn simplify_repairs<StorageT: PrimInt + Unsigned>
                              (all_rprs: &mut Vec<Vec<ParseRepair<StorageT>>>)
{
    for rprs in &mut all_rprs.iter_mut() {
        // Remove shifts from the end of repairs
        while !rprs.is_empty() {
            if let ParseRepair::Shift = rprs[rprs.len() - 1] {
                rprs.pop();
            } else {
                break;
            }
        }
    }

    all_rprs.sort_unstable_by(|x, y| {
                 x.len()
                  .cmp(&y.len())
                  .then_with(|| x.cmp(&y))
            });
    all_rprs.dedup();
}

pub(crate) struct Dist<StorageT> {
    terms_len: u32,
    table: Vec<u32>,
    phantom: PhantomData<StorageT>
}

impl<StorageT: Hash + PrimInt + Unsigned> Dist<StorageT> {
    pub(crate) fn new<F>
                     (grm: &YaccGrammar<StorageT>,
                      sgraph: &StateGraph<StorageT>,
                      stable: &StateTable<StorageT>,
                      term_cost: F)
                   -> Dist<StorageT>
                   where F: Fn(TIdx<StorageT>) -> u8
    {
        // This is an extension of dist from the KimYi paper: it also takes into account reductions
        // and gotos in the distances it reports back. Note that it is conservative, sometimes
        // undercounting the distance. Consider the KimYi paper, Figure 10: from state 0 it is
        // clearly the case that the distance to ')' is 2 since we would need to encounter the
        // tokens "(", {"a", "b"} before encountering a ')'. However, this algorithm gives the
        // distance as 1. This is because state 0 is a reduction target of state 3, but state 3
        // also has a reduction target of state 5: thus state state 0 ends up with the minimum
        // distances of itself and state 5.

        let terms_len = grm.terms_len() as usize;
        let states_len = sgraph.all_states_len() as usize;
        let sengen = grm.sentence_generator(&term_cost);
        let goto_states = Dist::goto_states(grm, sgraph, stable);

        let mut table = Vec::new();
        table.resize(states_len as usize * terms_len, u32::max_value());
        table[usize::from(stable.final_state) * terms_len + usize::from(grm.eof_term_idx())] = 0;
        loop {
            let mut chgd = false;
            for i in 0..states_len as usize {
                // The first phase is KimYi's dist algorithm.
                for (&sym, &sym_st_idx) in sgraph.edges(StIdx::from(i)).iter() {
                    let d = match sym {
                        Symbol::Nonterm(nt_idx) => sengen.min_sentence_cost(nt_idx),
                        Symbol::Term(t_idx) => {
                            let off = i * terms_len + usize::from(t_idx);
                            if table[off] != 0 {
                                table[off] = 0;
                                chgd = true;
                            }
                            u32::from(term_cost(t_idx))
                        }
                    };

                    for j in 0..terms_len {
                        let this_off = i * terms_len + j;
                        let other_off = usize::from(sym_st_idx) * terms_len + j;

                        if table[other_off] != u32::max_value()
                           && table[other_off] + d < table[this_off]
                        {
                            table[this_off] = table[other_off] + d;
                            chgd = true;
                        }
                    }
                }

                // The second phase takes into account reductions and gotos.
                for st_idx in goto_states[i].iter_set_bits(..) {
                    for j in 0..terms_len {
                        let this_off = i * terms_len + j;
                        let other_off = st_idx * terms_len + j;

                        if table[other_off] != u32::max_value()
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

        Dist{terms_len: grm.terms_len(), table, phantom: PhantomData}
    }

    pub(crate) fn dist(&self, st_idx: StIdx, t_idx: TIdx<StorageT>) -> u32 {
        self.table[usize::from(st_idx) * self.terms_len as usize + usize::from(t_idx)]
    }

    /// rev_edges allows us to walk backwards over the stategraph.
    fn rev_edges(sgraph: &StateGraph<StorageT>) -> Vec<Vob>
    {
        let states_len = sgraph.all_states_len();
        let mut rev_edges = Vec::with_capacity(states_len as usize);
        rev_edges.resize(states_len as usize, Vob::from_elem(sgraph.all_states_len() as usize, false));
        for i in 0..states_len {
            for (_, &sym_st_idx) in sgraph.edges(StIdx::from(i)).iter() {
                rev_edges[usize::from(sym_st_idx)].set(i as usize, true);
            }
        }
        rev_edges
    }

    /// goto_states allows us to quickly determine all the states reachable after an entry in a
    /// given state has been reduced and performed a goto.
    fn goto_states(grm: &YaccGrammar<StorageT>,
                   sgraph: &StateGraph<StorageT>,
                   stable: &StateTable<StorageT>)
                -> Vec<Vob>
    {
        let rev_edges = Dist::rev_edges(sgraph);
        let states_len = sgraph.all_states_len() as usize;
        let mut goto_states = Vec::with_capacity(states_len as usize);
        goto_states.resize(states_len as usize,
                           Vob::from_elem(sgraph.all_states_len() as usize,
                           false));
        // prev and next are hoist here to lessen memory allocation in a core loop below.
        let mut prev = Vob::from_elem(states_len, false);
        let mut next = Vob::from_elem(states_len, false);
        for i in 0..states_len {
            for &(p_idx, sym_off) in sgraph.core_state(StIdx::from(i)).items.keys() {
                let prod = grm.prod(p_idx);
                if usize::from(sym_off) < prod.len() {
                    continue;
                }
                let nt_idx = grm.prod_to_nonterm(p_idx);

                // We've found an item in a core state where the dot is at the end of the rule:
                // what we now do is reach backwards in the stategraph to find all of the
                // possible states the reduction and subsequent goto might reach.

                // First find all the possible states the reductions might end up in. We search
                // back prod.len() states in the stategraph to do this: the final result will end
                // up in prev.
                prev.set_all(false);
                prev.set(i, true);
                for _ in 0..prod.len() {
                    next.set_all(false);
                    for st_idx in prev.iter_set_bits(..) {
                        next.or(&rev_edges[st_idx]);
                    }
                    mem::swap(&mut prev, &mut next);
                }

                // From the reduction states, find all the goto states.
                for st_idx in prev.iter_set_bits(..) {
                    if let Some(goto_st_idx) = stable.goto(StIdx::from(st_idx), nt_idx) {
                        goto_states[i].set(usize::from(goto_st_idx), true);
                    }
                }
            }
        }
        goto_states
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;
    use std::fmt::Debug;

    use num_traits::{PrimInt, ToPrimitive, Unsigned};
    use test::{Bencher, black_box};

    use cactus::Cactus;
    use cfgrammar::Symbol;
    use cfgrammar::yacc::{YaccGrammar, YaccKind};
    use lrlex::Lexeme;
    use lrtable::{Minimiser, from_yacc, StIdx};

    use parser::{ParseRepair, RecoveryKind};
    use parser::test::{do_parse, do_parse_with_costs};

    use super::{ends_with_parse_at_least_shifts, Dist, PARSE_AT_LEAST, Repair, RepairMerge};

    fn pp_repairs<StorageT: PrimInt + Unsigned>
                 (grm: &YaccGrammar<StorageT>, repairs: &Vec<ParseRepair<StorageT>>)
               -> String
    {
        let mut out = vec![];
        for r in repairs.iter() {
            match *r {
                ParseRepair::InsertSeq(ref seqs) => {
                    let mut s = String::new();
                    s.push_str("Insert {");
                    for (i, seq) in seqs.iter().enumerate() {
                        if i > 0 {
                            s.push_str(", ");
                        }
                        for (j, t_idx) in seq.iter().enumerate() {
                            if j > 0 {
                                s.push_str(" ");
                            }
                            s.push_str(&format!("\"{}\"", grm.term_name(*t_idx).unwrap()));
                        }
                    }
                    s.push_str("}");
                    out.push(s);
                },
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

    #[test]
    fn dist_kimyi() {
        let grms = "%start A
%%
A: '(' A ')'
 | 'a'
 | 'b'
 ;
";

        let grm = YaccGrammar::new(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, &stable, |_| 1);
        let s0 = StIdx::from(0u32);
        assert_eq!(d.dist(s0, grm.term_idx("(").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.term_idx(")").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.term_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.term_idx("b").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.eof_term_idx()), 1);

        let s1 = sgraph.edge(s0, Symbol::Nonterm(grm.nonterm_idx("A").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.term_idx("(").unwrap()), u32::max_value());
        assert_eq!(d.dist(s1, grm.term_idx(")").unwrap()), u32::max_value());
        assert_eq!(d.dist(s1, grm.term_idx("a").unwrap()), u32::max_value());
        assert_eq!(d.dist(s1, grm.term_idx("b").unwrap()), u32::max_value());
        assert_eq!(d.dist(s1, grm.eof_term_idx()), 0);

        let s2 = sgraph.edge(s0, Symbol::Term(grm.term_idx("a").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.term_idx("(").unwrap()), u32::max_value());
        assert_eq!(d.dist(s2, grm.term_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s2, grm.term_idx("a").unwrap()), u32::max_value());
        assert_eq!(d.dist(s2, grm.term_idx("b").unwrap()), u32::max_value());
        assert_eq!(d.dist(s2, grm.eof_term_idx()), 0);

        let s3 = sgraph.edge(s0, Symbol::Term(grm.term_idx("b").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.term_idx("(").unwrap()), u32::max_value());
        assert_eq!(d.dist(s3, grm.term_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.term_idx("a").unwrap()), u32::max_value());
        assert_eq!(d.dist(s3, grm.term_idx("b").unwrap()), u32::max_value());
        assert_eq!(d.dist(s3, grm.eof_term_idx()), 0);

        let s5 = sgraph.edge(s0, Symbol::Term(grm.term_idx("(").unwrap())).unwrap();
        assert_eq!(d.dist(s5, grm.term_idx("(").unwrap()), 0);
        assert_eq!(d.dist(s5, grm.term_idx(")").unwrap()), 1);
        assert_eq!(d.dist(s5, grm.term_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s5, grm.term_idx("b").unwrap()), 0);
        assert_eq!(d.dist(s5, grm.eof_term_idx()), 1);

        let s6 = sgraph.edge(s5, Symbol::Nonterm(grm.nonterm_idx("A").unwrap())).unwrap();
        assert_eq!(d.dist(s6, grm.term_idx("(").unwrap()), u32::max_value());
        assert_eq!(d.dist(s6, grm.term_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s6, grm.term_idx("a").unwrap()), u32::max_value());
        assert_eq!(d.dist(s6, grm.term_idx("b").unwrap()), u32::max_value());
        assert_eq!(d.dist(s6, grm.eof_term_idx()), 1);

        let s4 = sgraph.edge(s6, Symbol::Term(grm.term_idx(")").unwrap())).unwrap();
        assert_eq!(d.dist(s4, grm.term_idx("(").unwrap()), u32::max_value());
        assert_eq!(d.dist(s4, grm.term_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s4, grm.term_idx("a").unwrap()), u32::max_value());
        assert_eq!(d.dist(s4, grm.term_idx("b").unwrap()), u32::max_value());
        assert_eq!(d.dist(s4, grm.eof_term_idx()), 0);
    }

    #[test]
    fn dist_short() {
        let grms = "%start S
%%
S: T U 'C';
T: 'A';
U: 'B';
";

        let grm = YaccGrammar::new(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, &stable, |_| 1);

        // This only tests a subset of all the states and distances but, I believe, it tests all
        // more interesting edge cases that the example from the Kim/Yi paper.

        let s0 = StIdx::from(0u32);
        assert_eq!(d.dist(s0, grm.term_idx("A").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.term_idx("B").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.term_idx("C").unwrap()), 2);

        let s1 = sgraph.edge(s0, Symbol::Nonterm(grm.nonterm_idx("T").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.term_idx("A").unwrap()), u32::max_value());
        assert_eq!(d.dist(s1, grm.term_idx("B").unwrap()), 0);
        assert_eq!(d.dist(s1, grm.term_idx("C").unwrap()), 1);

        let s2 = sgraph.edge(s0, Symbol::Nonterm(grm.nonterm_idx("S").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.term_idx("A").unwrap()), u32::max_value());
        assert_eq!(d.dist(s2, grm.term_idx("B").unwrap()), u32::max_value());
        assert_eq!(d.dist(s2, grm.term_idx("C").unwrap()), u32::max_value());

        let s3 = sgraph.edge(s0, Symbol::Term(grm.term_idx("A").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.term_idx("A").unwrap()), u32::max_value());
        assert_eq!(d.dist(s3, grm.term_idx("B").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.term_idx("C").unwrap()), 1);

        let s4 = sgraph.edge(s1, Symbol::Nonterm(grm.nonterm_idx("U").unwrap())).unwrap();
        assert_eq!(d.dist(s4, grm.term_idx("A").unwrap()), u32::max_value());
        assert_eq!(d.dist(s4, grm.term_idx("B").unwrap()), u32::max_value());
        assert_eq!(d.dist(s4, grm.term_idx("C").unwrap()), 0);

        let s5 = sgraph.edge(s1, Symbol::Term(grm.term_idx("B").unwrap())).unwrap();
        assert_eq!(d.dist(s5, grm.term_idx("A").unwrap()), u32::max_value());
        assert_eq!(d.dist(s5, grm.term_idx("B").unwrap()), u32::max_value());
        assert_eq!(d.dist(s5, grm.term_idx("C").unwrap()), 0);

        let s6 = sgraph.edge(s4, Symbol::Term(grm.term_idx("C").unwrap())).unwrap();
        assert_eq!(d.dist(s6, grm.term_idx("A").unwrap()), u32::max_value());
        assert_eq!(d.dist(s6, grm.term_idx("B").unwrap()), u32::max_value());
        assert_eq!(d.dist(s6, grm.term_idx("C").unwrap()), u32::max_value());
    }

    #[test]
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

        let grm = YaccGrammar::new(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, &stable, |_| 1);

        // This only tests a subset of all the states and distances but, I believe, it tests all
        // more interesting edge cases that the example from the Kim/Yi paper.

        let s0 = StIdx::from(0u32);
        assert_eq!(d.dist(s0, grm.term_idx("+").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.term_idx("*").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.term_idx("(").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.term_idx(")").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.term_idx("INT").unwrap()), 0);

        let s1 = sgraph.edge(s0, Symbol::Term(grm.term_idx("(").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.term_idx("+").unwrap()), 1);
        assert_eq!(d.dist(s1, grm.term_idx("*").unwrap()), 1);
        assert_eq!(d.dist(s1, grm.term_idx("(").unwrap()), 0);
        assert_eq!(d.dist(s1, grm.term_idx(")").unwrap()), 1);
        assert_eq!(d.dist(s1, grm.term_idx("INT").unwrap()), 0);

        let s2 = sgraph.edge(s0, Symbol::Nonterm(grm.nonterm_idx("Factor").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.term_idx("+").unwrap()), 0);
        assert_eq!(d.dist(s2, grm.term_idx("*").unwrap()), 0);
        assert_eq!(d.dist(s2, grm.term_idx("(").unwrap()), 1);
        assert_eq!(d.dist(s2, grm.term_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s2, grm.term_idx("INT").unwrap()), 1);

        let s3 = sgraph.edge(s0, Symbol::Term(grm.term_idx("INT").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.term_idx("+").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.term_idx("*").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.term_idx("(").unwrap()), 1);
        assert_eq!(d.dist(s3, grm.term_idx(")").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.term_idx("INT").unwrap()), 1);
    }

    #[test]
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

        let grm = YaccGrammar::new(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, &stable, |_| 1);

        let s0 = StIdx::from(0u32);
        assert_eq!(d.dist(s0, grm.term_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s0, grm.term_idx("b").unwrap()), 1);
        assert_eq!(d.dist(s0, grm.eof_term_idx()), 0);

        let s1 = sgraph.edge(s0, Symbol::Nonterm(grm.nonterm_idx("T").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.term_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s1, grm.term_idx("b").unwrap()), 1);
        assert_eq!(d.dist(s1, grm.eof_term_idx()), 0);

        let s2 = sgraph.edge(s0, Symbol::Nonterm(grm.nonterm_idx("S").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.term_idx("a").unwrap()), u32::max_value());
        assert_eq!(d.dist(s2, grm.term_idx("b").unwrap()), u32::max_value());
        assert_eq!(d.dist(s2, grm.eof_term_idx()), 0);

        let s3 = sgraph.edge(s1, Symbol::Term(grm.term_idx("a").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.term_idx("a").unwrap()), 1);
        assert_eq!(d.dist(s3, grm.term_idx("b").unwrap()), 0);
        assert_eq!(d.dist(s3, grm.eof_term_idx()), 1);

        let s4 = sgraph.edge(s1, Symbol::Nonterm(grm.nonterm_idx("U").unwrap())).unwrap();
        assert_eq!(d.dist(s4, grm.term_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s4, grm.term_idx("b").unwrap()), 1);
        assert_eq!(d.dist(s4, grm.eof_term_idx()), 0);

        let s5 = sgraph.edge(s1, Symbol::Nonterm(grm.nonterm_idx("V").unwrap())).unwrap();
        assert_eq!(d.dist(s5, grm.term_idx("a").unwrap()), 1);
        assert_eq!(d.dist(s5, grm.term_idx("b").unwrap()), 0);
        assert_eq!(d.dist(s5, grm.eof_term_idx()), 1);

        let s6 = sgraph.edge(s5, Symbol::Term(grm.term_idx("b").unwrap())).unwrap();
        assert_eq!(d.dist(s6, grm.term_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s6, grm.term_idx("b").unwrap()), 1);
        assert_eq!(d.dist(s6, grm.eof_term_idx()), 0);

        let s7 = sgraph.edge(s5, Symbol::Nonterm(grm.nonterm_idx("W").unwrap())).unwrap();
        assert_eq!(d.dist(s7, grm.term_idx("a").unwrap()), 0);
        assert_eq!(d.dist(s7, grm.term_idx("b").unwrap()), 1);
        assert_eq!(d.dist(s7, grm.eof_term_idx()), 0);
    }

    #[bench]
    fn bench_dist(b: &mut Bencher) {
        let grms = "%start A
%%
A: '(' A ')'
 | 'a'
 | 'b'
 ;
";
        let grm = YaccGrammar::new(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        b.iter(|| {
            for _ in 0..10000 {
                black_box(Dist::new(&grm, &sgraph, &stable, |_| 1));
            }
        });
    }

    fn check_some_repairs<StorageT: PrimInt + Unsigned>
                         (grm: &YaccGrammar<StorageT>,
                          repairs: &Vec<Vec<ParseRepair<StorageT>>>,
                          expected: &[&str]) {
        for i in 0..expected.len() {
            if repairs.iter().find(|x| pp_repairs(&grm, x) == expected[i]).is_none() {
                panic!("No match found for:\n  {}", expected[i]);
            }
        }
    }

    fn check_all_repairs<StorageT: Debug + PrimInt + Unsigned>
                        (grm: &YaccGrammar<StorageT>,
                         repairs: &Vec<Vec<ParseRepair<StorageT>>>,
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
        // The example from the Corchuelo paper
        let lexs = "%%
\\( '('
\\) ')'
\\+ '+'
n 'N'
";
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
        let err_tok_id = u32::from(grm.term_idx("N").unwrap()).to_u16().unwrap();
        assert_eq!(errs[0].lexeme(), &Lexeme::new(err_tok_id, 2, 1));
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \")\", Insert \"+\"",
                                "Insert \")\", Delete",
                                "Insert \"+\", Shift, Insert \")\""]);

        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, "n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Delete"]);
        check_all_repairs(&grm,
                          errs[1].repairs(),
                          &vec!["Delete"]);

        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, "(((+n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"N\"",
                                "Delete"]);
        check_all_repairs(&grm,
                          errs[1].repairs(),
                          &vec!["Insert \")\""]);
    }

    fn kimyi_lex_grm() -> (&'static str, &'static str) {
        // The example from the KimYi paper, with a bit of alpha-renaming to make it clearer. The
        // paper uses "A" as a nonterminal name and "a" as a terminal name, which are then easily
        // confused. Here we use "E" as the nonterminal name, and keep "a" as the terminal name.
        let lexs = "%%
\\( '('
\\) ')'
a 'A'
b 'B'
";
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
"]
            .iter()
            .any(|x| *x == pp) {
            panic!("Can't find a match for {}", pp);
        }
        assert_eq!(errs.len(), 1);
        let err_tok_id = u32::from(grm.eof_term_idx()).to_u16().unwrap();
        assert_eq!(errs[0].lexeme(), &Lexeme::new(err_tok_id, 2, 0));
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"A\", Insert \")\", Insert \")\"",
                                "Insert \"B\", Insert \")\", Insert \")\""]);
    }

    #[test]
    fn expr_grammar() {
        let lexs = "%%
\\( '('
\\) ')'
\\+ '+'
\\* '*'
[0-9]+ 'INT'
[ ] ;
";

        let grms = "%start Expr
%%
Expr: Term '+' Expr
    | Term ;

Term: Factor '*' Term
    | Factor ;

Factor: '(' Expr ')'
      | 'INT' ;
";

        let us = "(2 3";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \")\", Insert \"+\"",
                                "Insert \")\", Insert \"*\"",
                                "Insert \")\", Delete",
                                "Insert \"+\", Shift, Insert \")\"",
                                "Insert \"*\", Shift, Insert \")\""]);

        let us = "(+++++)";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_some_repairs(&grm,
                           errs[0].repairs(),
                           &vec!["Insert \"INT\", Delete, Delete, Delete, Delete, Delete"]);
    }

    #[test]
    fn find_shortest() {
        let lexs = "%%
a 'A'
b 'B'
c 'C'
";

        let grms = "%start S
%%
S: T U 'C';
T: 'A';
U: 'B';
";

        let us = "c";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"A\", Insert \"B\""]);
    }

    #[test]
    fn deletes_after_inserts() {
        let lexs = "%%
a 'A'
b 'B'
c 'C'
d 'D'
";

        let grms = "%start S
%%
S:  'A' 'B' 'D' | 'A' 'B' 'C' 'A' 'A' 'D';
";

        let us = "acd";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"B\", Delete"]);
    }

    #[test]
    fn repair_empty_string() {
        let lexs = "%%
a 'A'
";

        let grms = "%start S
%%
S: 'A';
";

        let us = "";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"A\""]);
    }

    #[test]
    fn test_merge() {
        let lexs = "%%
a 'a'
b 'b'
c 'c'
d 'd'
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
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"a\", Insert \"d\"",
                                "Insert \"b\", Insert \"d\"",
                                "Insert \"c\", Insert \"d\""]);
    }

    #[test]
    fn test_cerecke_loop_limit() {
        // Example taken from p57 of Locally least-cost error repair in LR parsers, Carl Cerecke
        let lexs = "%%
a 'a'
b 'b'
c 'c'
";

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
                          errs[0].repairs(),
                          &vec!["Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\""]);
    }

    #[test]
    fn test_cerecke_lr2() {
        // Example taken from p54 of Locally least-cost error repair in LR parsers, Carl Cerecke
        let lexs = "%%
a 'a'
b 'b'
c 'c'
d 'd'
e 'e'
";

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
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"b\""]);
        let us = "cd";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"a\""]);
    }

    #[test]
    fn test_bertsch_nederhof1() {
        // Example from p5 of Bertsch and Nederhof "On Failure of the Pruning Technique in 'Error
        // Repair in Shift-reduce Parsers'"
        let lexs = "%%
a 'a'
b 'b'
c 'c'
d 'd'
";

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
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"c\", Insert \"d\", Insert \"c\", Insert \"d\", Insert \"a\""]);
    }

    #[test]
    fn test_bertsch_nederhof2() {
        // Example from p5 of Bertsch and Nederhof "On Failure of the Pruning Technique in 'Error
        // Repair in Shift-reduce Parsers'"
        let lexs = "%%
a 'a'
c 'c'
d 'd'
";

        let grms = "%start S
%%
S: A A 'a';
A: 'c' 'd';
";

        let us = "";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"c\", Insert \"d\", Insert \"c\", Insert \"d\", Insert \"a\""]);
    }

    #[test]
    fn test_bertsch_nederhof3() {
        // Example from p8 of Bertsch and Nederhof "On Failure of the Pruning Technique in 'Error
        // Repair in Shift-reduce Parsers'"
        let lexs = "%%
a 'a'
b 'b'
c 'c'
d 'd'
";

        let grms = "%start S
%%
S: C D 'a' | D C 'b';
C: 'c';
D: 'd';
";

        let us = "";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"c\", Insert \"d\", Insert \"a\"",
                                "Insert \"d\", Insert \"c\", Insert \"b\""]);
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
