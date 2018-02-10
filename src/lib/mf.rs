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
use std::collections::{HashMap, HashSet};
use std::convert::{TryFrom, TryInto};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};

use cactus::Cactus;
use cfgrammar::{Grammar, PIdx, Symbol, TIdx};
use cfgrammar::yacc::YaccGrammar;
use lrtable::{Action, StateGraph, StateTable, StIdx};
use astar::astar_all;

use kimyi::{apply_repairs, Repair};
use parser::{Node, Parser, ParseRepair, Recoverer};

const PARSE_AT_LEAST: usize = 4; // N in Corchuelo et al.
const PORTION_THRESHOLD: usize = 10; // N_t in Corchuelo et al.
const TRY_PARSE_AT_MOST: usize = 250;

#[derive(Clone, Debug, Eq)]
struct PathFNode {
    pstack: Cactus<StIdx>,
    la_idx: usize,
    repairs: Cactus<Repair>,
    cf: u32,
    cg: u32
}

impl Hash for PathFNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.pstack.hash(state);
        self.la_idx.hash(state);
        self.repairs.hash(state);
    }
}

impl PartialEq for PathFNode {
    fn eq(&self, other: &PathFNode) -> bool {
        self.pstack == other.pstack && self.repairs == other.repairs && self.la_idx == other.la_idx
    }
}

pub(crate) struct MF<'a, TokId: Clone + Copy + TryFrom<usize> + TryInto<usize>> where TokId: 'a {
    dist: Dist,
    parser: &'a Parser<'a, TokId>
}

pub(crate) fn recoverer<'a, TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
                       (parser: &'a Parser<TokId>)
                     -> Box<Recoverer<TokId> + 'a>
{
    let dist = Dist::new(parser.grm, parser.sgraph, parser.stable, parser.term_cost);
    Box::new(MF{dist, parser: &parser})
}

impl<'a, TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
    Recoverer<TokId> for MF<'a, TokId>
{
    fn recover(&self,
               parser: &Parser<TokId>,
               in_la_idx: usize,
               in_pstack: &mut Vec<StIdx>,
               mut tstack: &mut Vec<Node<TokId>>)
           -> (usize, Vec<Vec<ParseRepair>>)
    {
        let mut start_cactus_pstack = Cactus::new();
        for st in in_pstack.drain(..) {
            start_cactus_pstack = start_cactus_pstack.child(st);
        }

        let start_node = PathFNode{pstack: start_cactus_pstack.clone(),
                                   la_idx: in_la_idx,
                                   repairs: Cactus::new(),
                                   cf: 0,
                                   cg: 0};
        let astar_cnds = astar_all(
            start_node,
            |n| {
                // Calculate n's neighbours.

                if n.la_idx > in_la_idx + PORTION_THRESHOLD {
                    return vec![];
                }

                let mut nbrs = Vec::new();
                match n.repairs.val() {
                    Some(&Repair::Delete) => {
                        // We follow Corcheulo et al.'s suggestions and never follow Deletes with
                        // Inserts.
                    },
                    _ => {
                        self.r3is(&n, &mut nbrs);
                        self.r3ir(&n, &mut nbrs);
                    }
                }
                self.r3d(&n, &mut nbrs);
                self.r3s_n(&n, &mut nbrs);

                let v = nbrs.into_iter()
                            .map(|x| {
                                    let cf = x.cf;
                                    let cg = x.cg;
                                    (cf, cg, x)
                                 })
                            .collect::<Vec<(_, _, PathFNode)>>();
                v
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

                let la_tidx = parser.next_tidx(n.la_idx);
                match parser.stable.action(*n.pstack.val().unwrap(), Symbol::Term(la_tidx)) {
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
                                      start_cactus_pstack.clone(),
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
                                     .unwrap_or_else(|c| c.val()
                                                          .unwrap()
                                                          .clone()));
            rpr_pstack = p;
        }
        in_pstack.reverse();

        (la_idx, rnk_rprs)
    }
}

impl<'a, TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq> MF<'a, TokId> {
    fn r3is(&self,
            n: &PathFNode,
            nbrs: &mut Vec<PathFNode>)
    {
        let top_pstack = *n.pstack.val().unwrap();
        for (&sym, &sym_st_idx) in self.parser.sgraph.edges(top_pstack).iter() {
            if let Symbol::Term(term_idx) = sym {
                if term_idx == self.parser.grm.eof_term_idx() {
                    continue;
                }

                let n_repairs = n.repairs.child(Repair::InsertTerm(term_idx));
                if let Some(d) = self.dyn_dist(&n_repairs, sym_st_idx, n.la_idx) {
                    if let Some(&Repair::Shift) = n.repairs.val() {
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
                        let prev_tidx = self.parser.next_tidx(n.la_idx - 1);
                        if prev_tidx == term_idx {
                            continue;
                        }
                    }

                    assert!(n.cg == 0 || d >= n.cg - (self.parser.term_cost)(term_idx) as u32);
                    let nn = PathFNode{
                        pstack: n.pstack.child(sym_st_idx),
                        la_idx: n.la_idx,
                        repairs: n_repairs,
                        cf: n.cf.checked_add((self.parser.term_cost)(term_idx) as u32).unwrap(),
                        cg: d};
                    nbrs.push(nn);
                }
            }
        }
    }

    fn r3ir(&self,
            n: &PathFNode,
            nbrs: &mut Vec<PathFNode>)
    {
        // This is different than KimYi's r3ir: their r3ir inserts symbols if the dot in a state is not
        // at the end. This is unneeded in our setup (indeed, doing so causes duplicates): all we need
        // to do is reduce states where the dot is at the end.

        let top_pstack = *n.pstack.val().unwrap();
        for &(p_idx, sym_off) in self.parser.sgraph.closed_state(top_pstack).items.keys() {
            if usize::from(sym_off) != self.parser.grm.prod(p_idx).len() {
                continue;
            }

            let nt_idx = self.parser.grm.prod_to_nonterm(p_idx);
            let mut qi_minus_alpha = n.pstack.clone();
            for _ in 0..usize::from(sym_off) {
                qi_minus_alpha = qi_minus_alpha.parent().unwrap();
            }

            if let Some(goto_st_idx) = self.parser.stable
                                                  .goto(*qi_minus_alpha.val().unwrap(),
                                                        nt_idx) {
                if let Some(d) = self.dyn_dist(&n.repairs, goto_st_idx, n.la_idx) {
                    let nn = PathFNode{
                        pstack: qi_minus_alpha.child(goto_st_idx),
                        la_idx: n.la_idx,
                        repairs: n.repairs.clone(),
                        cf: n.cf,
                        cg: d};
                    nbrs.push(nn);
                }
            }
        }
    }

    fn r3d(&self,
           n: &PathFNode,
           nbrs: &mut Vec<PathFNode>)
    {
        if n.la_idx == self.parser.lexemes.len() {
            return;
        }

        let n_repairs = n.repairs.child(Repair::Delete);
        if let Some(d) = self.dyn_dist(&n_repairs, *n.pstack.val().unwrap(), n.la_idx + 1) {
            let la_tidx = self.parser.next_tidx(n.la_idx);
            let cost = (self.parser.term_cost)(la_tidx);
            let nn = PathFNode{pstack: n.pstack.clone(),
                               la_idx: n.la_idx + 1,
                               repairs: n_repairs,
                               cf: n.cf.checked_add(cost as u32).unwrap(),
                               cg: d};
            nbrs.push(nn);
        }
    }

    fn r3s_n(&self,
             n: &PathFNode,
             nbrs: &mut Vec<PathFNode>)
    {
        let la_tidx = self.parser.next_tidx(n.la_idx);
        let top_pstack = *n.pstack.val().unwrap();
        if let Some(Action::Shift(state_id)) = self.parser.stable.action(top_pstack,
                                                                         Symbol::Term(la_tidx)) {
            let n_repairs = n.repairs.child(Repair::Shift);
            let new_la_idx = n.la_idx + 1;
            if let Some(d) = self.dyn_dist(&n_repairs, state_id, new_la_idx) {
                let nn = PathFNode{
                    pstack: n.pstack.child(state_id),
                    la_idx: new_la_idx,
                    repairs: n_repairs,
                    cf: n.cf,
                    cg: d};
                nbrs.push(nn);
            }
        }
    }

    /// Convert the output from `astar_bag` into something more usable.
    fn collect_repairs(&self, cnds: Vec<PathFNode>) -> Vec<Vec<Repair>>
    {
        cnds.into_iter()
            .map(|x| {
                let mut rprs = x.repairs
                                .vals()
                                .cloned()
                                .collect::<Vec<Repair>>();
                rprs.reverse();
                rprs
            })
            .collect::<Vec<Vec<Repair>>>()
    }

    /// Take an (unordered) set of parse repairs and return a simplified (unordered) set of parse
    /// repairs. Note that the caller must make no assumptions about the size or contents of the output
    /// set: this function might delete, expand, or do other things to repairs.
    fn simplify_repairs(&self,
                        mut all_rprs: Vec<Vec<Repair>>)
                     -> Vec<Vec<ParseRepair>>
    {
        let sg = self.parser.grm.sentence_generator(self.parser.term_cost);
        for i in 0..all_rprs.len() {
            {
                // Remove all inserts of nonterms which have a minimal sentence cost of 0.
                let mut rprs = all_rprs.get_mut(i).unwrap();
                let mut j = 0;
                while j < rprs.len() {
                    if let Repair::InsertNonterm(nonterm_idx) = rprs[j] {
                        if sg.min_sentence_cost(nonterm_idx) == 0 {
                            rprs.remove(j);
                        } else {
                            j += 1;
                        }
                    } else {
                        j += 1;
                    }
                }
            }

            {
                // Remove shifts from the end of repairs
                let mut rprs = all_rprs.get_mut(i).unwrap();
                while rprs.len() > 0 {
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
                                            Repair::InsertNonterm(nonterm_idx) =>
                                                ParseRepair::InsertSeq(sg.min_sentences(nonterm_idx)),
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
                 start_pstack: Cactus<StIdx>,
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
                let cnd = cnds.get_mut(j).unwrap();
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

    /// Return the distance from `st_idx` at input position `la_idx`, given the current `repairs`.
    /// Returns `None` if no route can be found.
    fn dyn_dist(&self,
                repairs: &Cactus<Repair>,
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
        let frst_tidx = self.parser.next_tidx(la_idx);
        let mut ld = self.dist.dist(st_idx, frst_tidx)
                              .unwrap_or(u32::max_value()); // ld == Current least distance
        let mut dc = (self.parser.term_cost)(frst_tidx) as u32; // Cumulative deletion cost
        for i in la_idx + 1..self.parser.lexemes.len() + 1 {
            if dc >= ld {
                // Once the cumulative cost of deleting lexemes is bigger than the current least
                // distance, there is no chance of finding a subsequent lexeme which could produce
                // a lower cost.
                break;
            }
            let t_idx = self.parser.next_tidx(i);
            if let Some(d) = self.dist.dist(st_idx, t_idx) {
                if dc.checked_add(d).unwrap() < ld {
                    ld = dc + d;
                }
            }
            dc = dc.checked_add((self.parser.term_cost)(t_idx) as u32).unwrap();
        }
        if ld == u32::max_value() {
            None
        } else {
            Some(ld)
        }
    }
}

/// Do `repairs` end with enough Shift repairs to be considered a success node?
fn ends_with_parse_at_least_shifts(repairs: &Cactus<Repair>) -> bool {
    if repairs.len() >= PARSE_AT_LEAST {
        for x in repairs.vals().take(PARSE_AT_LEAST) {
            if let Repair::Shift = *x {
                continue;
            }
            return false;
        }
        true
    } else {
       false
    }
}

pub(crate) struct Dist {
    terms_len: u32,
    table: Vec<u32>
}

impl Dist {
    pub(crate) fn new<F>(grm: &YaccGrammar, sgraph: &StateGraph, stable: &StateTable, term_cost: F) -> Dist
              where F: Fn(TIdx) -> u8
    {
        // This is an extension of dist from the KimYi paper: it also takes into account reductions
        // and gotos in the distances it reports back. Note that it is conservative, sometimes
        // undercounting the distance. Consider the KimYi paper, Figure 10: from state 0 it is
        // clearly the case that the distance to ')' is 2 since we would need to encounter the
        // tokens "(", {"a", "b"} before encountering a ')'. However, this algorithm gives the
        // distance as 1. This is because state 0 is a reduction target of state 3, but state 3
        // also has a reduction target of state 5: thus state state 0 ends up with the minimum
        // distances of itself and state 5. Put another way, state 0 and state 5 end up with the
        // same set of distances, even though a more clever algorithm could work out that this
        // needn't be so. That's for another day...

        let terms_len = grm.terms_len() as usize;
        let states_len = sgraph.all_states_len();
        let sengen = grm.sentence_generator(&term_cost);
        let mut table = Vec::new();
        table.resize(states_len as usize * terms_len, u32::max_value());
        table[usize::from(stable.final_state) * terms_len + usize::from(grm.eof_term_idx())] = 0;

        let rev_edges = Dist::rev_edges(&sgraph);
        let goto_edges = Dist::goto_edges(grm, sgraph, stable, &rev_edges);

        // We can now interleave KimYi's original dist algorithm with our addition which takes into
        // account goto_edges.
        loop {
            let mut chgd = false; // Has anything changed?

            for i in 0..states_len as usize {
                // The first phase is KimYi's dist algorithm.
                let edges = sgraph.edges(StIdx::from(i));
                for (&sym, &sym_st_idx) in edges.iter() {
                    let d = match sym {
                        Symbol::Nonterm(nt_idx) => sengen.min_sentence_cost(nt_idx),
                        Symbol::Term(t_idx) => {
                            let off = i * terms_len + usize::from(t_idx);
                            if table[off] != 0 {
                                table[off] = 0;
                                chgd = true;
                            }
                            term_cost(t_idx) as u32
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

                // The second phase takes into account gotos.
                for &(p_idx, sym_off) in sgraph.core_state(StIdx::from(i)).items.keys() {
                    let prod = grm.prod(p_idx);
                    if usize::from(sym_off) == prod.len() {
                        for goto_idx in goto_edges.get(&(StIdx::from(i), p_idx)).unwrap() {
                            for j in 0..terms_len {
                                let this_off = i * terms_len + j;
                                let other_off = usize::from(*goto_idx) * terms_len + j;

                                if table[other_off] != u32::max_value() &&
                                    table[other_off] < table[this_off] {
                                    table[this_off] = table[other_off];
                                    chgd = true;
                                }
                            }
                        }
                    }
                }
            }
            if !chgd {
                break;
            }
        }

        Dist{terms_len: grm.terms_len(), table}
    }

    pub(crate) fn dist(&self, st_idx: StIdx, t_idx: TIdx) -> Option<u32> {
        let e = self.table[usize::from(st_idx) * self.terms_len as usize + usize::from(t_idx)];
        if e == u32::max_value() {
            None
        } else {
            Some(e as u32)
        }
    }

    /// rev_edges allows us to walk backwards over the stategraph
    fn rev_edges(sgraph: &StateGraph) -> Vec<HashSet<StIdx>> {
        let states_len = sgraph.all_states_len();
        let mut rev_edges = Vec::with_capacity(states_len as usize);
        rev_edges.resize(states_len as usize, HashSet::new());
        for i in 0..states_len {
            for (_, &sym_st_idx) in sgraph.edges(StIdx::from(i)).iter() {
                rev_edges[usize::from(sym_st_idx)].insert(StIdx::from(i));
            }
        }
        rev_edges
    }

    /// goto_edges is a map from a core state ready for reduction (i.e. where the dot is at the
    /// end of the production and thus sym_off == prod.len()) represented as a tuple
    /// (state_index, production_index) to a set of state indexes. The latter represents all the
    /// states which after (possibly recursive and intertwined) reductions and gotos the parser
    /// might end up in.
    fn goto_edges(grm: &YaccGrammar,
                  sgraph: &StateGraph,
                  stable: &StateTable,
                  rev_edges: &Vec<HashSet<StIdx>>)
               -> HashMap<(StIdx, PIdx), HashSet<StIdx>>
    {
        // We calculate this for a state i, production p_idx, by iterating backwards over the
        // stategraph (using rev_edges) finding all routes of length grm.prod(p_idx).len() which
        // could lead back to i, and then storing their goto state indexes. Since further
        // reductions and gotos could then happen, we then have to recursively search those goto
        // state indexes from scratch.
        //
        // This loop is currently comically inefficient, but it is relatively straightforward.
        let mut goto_edges = HashMap::new();
        for i in 0..sgraph.all_states_len() as usize {
            for &(p_idx, sym_off) in sgraph.core_state(StIdx::from(i)).items.keys() {
                let prod = grm.prod(p_idx);
                if usize::from(sym_off) == prod.len() {
                    let mut todo = HashSet::new(); // (StIdx, PIdx)
                    let mut done = HashSet::new(); // Which (StIdx, PIdx) pairs have we processed?
                    let mut ge = HashSet::new();   // Which StIdx's can we eventually goto?
                    todo.insert((i, p_idx));
                    while todo.len() > 0 {
                        let &(i, p) = todo.iter().nth(0).unwrap();
                        todo.remove(&(i, p));
                        if done.contains(&(i, p)) {
                            continue;
                        }
                        done.insert((i, p));
                        let mut cur = rev_edges[i].clone();
                        let mut next;
                        for _ in 0..grm.prod(p).len() - 1 {
                            next = HashSet::new();
                            for st_idx in cur {
                                next.extend(&rev_edges[usize::from(st_idx)]);
                            }
                            cur = next;
                        }
                        for st_idx in cur {
                            for &(sub_p_idx, sub_sym_off) in sgraph.core_state(StIdx::from(st_idx))
                                                                   .items
                                                                   .keys() {
                                let sub_prod = grm.prod(sub_p_idx);
                                if usize::from(sub_sym_off) == sub_prod.len() {
                                    todo.insert((usize::from(st_idx), sub_p_idx));
                                }
                            }
                            let n = grm.prod_to_nonterm(p);
                            if let Some(goto_idx) = stable.goto(st_idx, n) {
                                ge.insert(goto_idx);
                            }
                        }
                    }
                    goto_edges.insert((StIdx::from(i), p_idx), ge);
                }
            }
        }
        goto_edges
    }
}

#[cfg(test)]
mod test {
    use std::convert::TryFrom;
    use test::{Bencher, black_box};

    use cactus::Cactus;
    use cfgrammar::Symbol;
    use cfgrammar::yacc::{yacc_grm, YaccGrammar, YaccKind};
    use lrlex::Lexeme;
    use lrtable::{Minimiser, from_yacc, StIdx};

    use kimyi::Repair;
    use kimyi::test::pp_repairs;
    use parser::{ParseRepair, RecoveryKind};
    use parser::test::do_parse;

    use super::{ends_with_parse_at_least_shifts, Dist, PARSE_AT_LEAST};

    #[test]
    fn dist_kimyi() {
        let grms = "%start A
%%
A: '(' A ')'
 | 'a'
 | 'b'
 ;
";

        let grm = yacc_grm(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, &stable, |_| 1);
        let s0 = StIdx::from(0 as u32);
        assert_eq!(d.dist(s0, grm.term_idx("(").unwrap()), Some(0));
        assert_eq!(d.dist(s0, grm.term_idx(")").unwrap()), Some(1));
        assert_eq!(d.dist(s0, grm.term_idx("a").unwrap()), Some(0));
        assert_eq!(d.dist(s0, grm.term_idx("b").unwrap()), Some(0));
        assert_eq!(d.dist(s0, grm.eof_term_idx()), Some(1));

        let s1 = sgraph.edge(s0, Symbol::Nonterm(grm.nonterm_idx("A").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.term_idx("(").unwrap()), None);
        assert_eq!(d.dist(s1, grm.term_idx(")").unwrap()), None);
        assert_eq!(d.dist(s1, grm.term_idx("a").unwrap()), None);
        assert_eq!(d.dist(s1, grm.term_idx("b").unwrap()), None);
        assert_eq!(d.dist(s1, grm.eof_term_idx()), Some(0));

        let s2 = sgraph.edge(s0, Symbol::Term(grm.term_idx("a").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.term_idx("(").unwrap()), None);
        assert_eq!(d.dist(s2, grm.term_idx(")").unwrap()), Some(0));
        assert_eq!(d.dist(s2, grm.term_idx("a").unwrap()), None);
        assert_eq!(d.dist(s2, grm.term_idx("b").unwrap()), None);
        assert_eq!(d.dist(s2, grm.eof_term_idx()), Some(0));

        let s3 = sgraph.edge(s0, Symbol::Term(grm.term_idx("b").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.term_idx("(").unwrap()), None);
        assert_eq!(d.dist(s3, grm.term_idx(")").unwrap()), Some(0));
        assert_eq!(d.dist(s3, grm.term_idx("a").unwrap()), None);
        assert_eq!(d.dist(s3, grm.term_idx("b").unwrap()), None);
        assert_eq!(d.dist(s3, grm.eof_term_idx()), Some(0));

        let s5 = sgraph.edge(s0, Symbol::Term(grm.term_idx("(").unwrap())).unwrap();
        assert_eq!(d.dist(s5, grm.term_idx("(").unwrap()), Some(0));
        assert_eq!(d.dist(s5, grm.term_idx(")").unwrap()), Some(1));
        assert_eq!(d.dist(s5, grm.term_idx("a").unwrap()), Some(0));
        assert_eq!(d.dist(s5, grm.term_idx("b").unwrap()), Some(0));
        assert_eq!(d.dist(s5, grm.eof_term_idx()), Some(1));

        let s6 = sgraph.edge(s5, Symbol::Nonterm(grm.nonterm_idx("A").unwrap())).unwrap();
        assert_eq!(d.dist(s6, grm.term_idx("(").unwrap()), None);
        assert_eq!(d.dist(s6, grm.term_idx(")").unwrap()), Some(0));
        assert_eq!(d.dist(s6, grm.term_idx("a").unwrap()), None);
        assert_eq!(d.dist(s6, grm.term_idx("b").unwrap()), None);
        assert_eq!(d.dist(s6, grm.eof_term_idx()), Some(1));

        let s4 = sgraph.edge(s6, Symbol::Term(grm.term_idx(")").unwrap())).unwrap();
        assert_eq!(d.dist(s4, grm.term_idx("(").unwrap()), None);
        assert_eq!(d.dist(s4, grm.term_idx(")").unwrap()), Some(0));
        assert_eq!(d.dist(s4, grm.term_idx("a").unwrap()), None);
        assert_eq!(d.dist(s4, grm.term_idx("b").unwrap()), None);
        assert_eq!(d.dist(s4, grm.eof_term_idx()), Some(0));
    }

    #[test]
    fn dist_short() {
        let grms = "%start S
%%
S: T U 'C';
T: 'A';
U: 'B';
";

        let grm = yacc_grm(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, &stable, |_| 1);

        // This only tests a subset of all the states and distances but, I believe, it tests all
        // more interesting edge cases that the example from the Kim/Yi paper.

        let s0 = StIdx::from(0 as u32);
        assert_eq!(d.dist(s0, grm.term_idx("A").unwrap()), Some(0));
        assert_eq!(d.dist(s0, grm.term_idx("B").unwrap()), Some(1));
        assert_eq!(d.dist(s0, grm.term_idx("C").unwrap()), Some(2));

        let s1 = sgraph.edge(s0, Symbol::Nonterm(grm.nonterm_idx("T").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.term_idx("A").unwrap()), None);
        assert_eq!(d.dist(s1, grm.term_idx("B").unwrap()), Some(0));
        assert_eq!(d.dist(s1, grm.term_idx("C").unwrap()), Some(1));

        let s2 = sgraph.edge(s0, Symbol::Nonterm(grm.nonterm_idx("S").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.term_idx("A").unwrap()), None);
        assert_eq!(d.dist(s2, grm.term_idx("B").unwrap()), None);
        assert_eq!(d.dist(s2, grm.term_idx("C").unwrap()), None);

        let s3 = sgraph.edge(s0, Symbol::Term(grm.term_idx("A").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.term_idx("A").unwrap()), None);
        assert_eq!(d.dist(s3, grm.term_idx("B").unwrap()), Some(0));
        assert_eq!(d.dist(s3, grm.term_idx("C").unwrap()), Some(1));

        let s4 = sgraph.edge(s1, Symbol::Nonterm(grm.nonterm_idx("U").unwrap())).unwrap();
        assert_eq!(d.dist(s4, grm.term_idx("A").unwrap()), None);
        assert_eq!(d.dist(s4, grm.term_idx("B").unwrap()), None);
        assert_eq!(d.dist(s4, grm.term_idx("C").unwrap()), Some(0));

        let s5 = sgraph.edge(s1, Symbol::Term(grm.term_idx("B").unwrap())).unwrap();
        assert_eq!(d.dist(s5, grm.term_idx("A").unwrap()), None);
        assert_eq!(d.dist(s5, grm.term_idx("B").unwrap()), None);
        assert_eq!(d.dist(s5, grm.term_idx("C").unwrap()), Some(0));

        let s6 = sgraph.edge(s4, Symbol::Term(grm.term_idx("C").unwrap())).unwrap();
        assert_eq!(d.dist(s6, grm.term_idx("A").unwrap()), None);
        assert_eq!(d.dist(s6, grm.term_idx("B").unwrap()), None);
        assert_eq!(d.dist(s6, grm.term_idx("C").unwrap()), None);
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

        let grm = yacc_grm(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, &stable, |_| 1);

        // This only tests a subset of all the states and distances but, I believe, it tests all
        // more interesting edge cases that the example from the Kim/Yi paper.

        let s0 = StIdx::from(0 as u32);
        assert_eq!(d.dist(s0, grm.term_idx("+").unwrap()), Some(1));
        assert_eq!(d.dist(s0, grm.term_idx("*").unwrap()), Some(1));
        assert_eq!(d.dist(s0, grm.term_idx("(").unwrap()), Some(0));
        assert_eq!(d.dist(s0, grm.term_idx(")").unwrap()), Some(1));
        assert_eq!(d.dist(s0, grm.term_idx("INT").unwrap()), Some(0));

        let s1 = sgraph.edge(s0, Symbol::Term(grm.term_idx("(").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.term_idx("+").unwrap()), Some(1));
        assert_eq!(d.dist(s1, grm.term_idx("*").unwrap()), Some(1));
        assert_eq!(d.dist(s1, grm.term_idx("(").unwrap()), Some(0));
        assert_eq!(d.dist(s1, grm.term_idx(")").unwrap()), Some(1));
        assert_eq!(d.dist(s1, grm.term_idx("INT").unwrap()), Some(0));

        let s2 = sgraph.edge(s0, Symbol::Nonterm(grm.nonterm_idx("Factor").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.term_idx("+").unwrap()), Some(0));
        assert_eq!(d.dist(s2, grm.term_idx("*").unwrap()), Some(0));
        assert_eq!(d.dist(s2, grm.term_idx("(").unwrap()), Some(1));
        assert_eq!(d.dist(s2, grm.term_idx(")").unwrap()), Some(0));
        assert_eq!(d.dist(s2, grm.term_idx("INT").unwrap()), Some(1));

        let s3 = sgraph.edge(s0, Symbol::Term(grm.term_idx("INT").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.term_idx("+").unwrap()), Some(0));
        assert_eq!(d.dist(s3, grm.term_idx("*").unwrap()), Some(0));
        assert_eq!(d.dist(s3, grm.term_idx("(").unwrap()), Some(1));
        assert_eq!(d.dist(s3, grm.term_idx(")").unwrap()), Some(0));
        assert_eq!(d.dist(s3, grm.term_idx("INT").unwrap()), Some(1));
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
        let grm = yacc_grm(YaccKind::Original, grms).unwrap();
        let (sgraph, stable) = from_yacc(&grm, Minimiser::Pager).unwrap();
        b.iter(|| {
            for _ in 0..10000 {
                black_box(Dist::new(&grm, &sgraph, &stable, |_| 1));
            }
        });
    }

    pub(crate) fn check_all_repairs(grm: &YaccGrammar,
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
        // The example from the Corchuelo paper
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
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, us);
        let (pt, errs) = pr.unwrap_err();
        let pp = pt.unwrap().pp(&grm, us);
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
        let err_tok_id = u16::try_from(usize::from(grm.term_idx("N").unwrap())).ok().unwrap();
        assert_eq!(errs[0].lexeme(), &Lexeme::new(err_tok_id, 2, 1));
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"CLOSE_BRACKET\", Insert \"PLUS\"",
                                "Insert \"CLOSE_BRACKET\", Delete",
                                "Insert \"PLUS\", Shift, Insert \"CLOSE_BRACKET\""]);

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
                          &vec!["Insert \"CLOSE_BRACKET\""]);
    }

    fn kimyi_lex_grm() -> (&'static str, &'static str) {
        // The example from the KimYi paper, with a bit of alpha-renaming to make it clearer. The
        // paper uses "A" as a nonterminal name and "a" as a terminal name, which are then easily
        // confused. Here we use "E" as the nonterminal name, and keep "a" as the terminal name.
        let lexs = "%%
[(] OPEN_BRACKET
[)] CLOSE_BRACKET
a A
b B
";
        let grms = "%start E
%%
E: 'OPEN_BRACKET' E 'CLOSE_BRACKET'
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
 OPEN_BRACKET (
 E
  OPEN_BRACKET (
  E
   A 
  CLOSE_BRACKET 
 CLOSE_BRACKET 
",
"E
 OPEN_BRACKET (
 E
  OPEN_BRACKET (
  E
   B 
  CLOSE_BRACKET 
 CLOSE_BRACKET 
"]
            .iter()
            .any(|x| *x == pp) {
            panic!("Can't find a match for {}", pp);
        }
        assert_eq!(errs.len(), 1);
        let err_tok_id = u16::try_from(usize::from(grm.eof_term_idx())).ok().unwrap();
        assert_eq!(errs[0].lexeme(), &Lexeme::new(err_tok_id, 2, 0));
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"A\", Insert \"CLOSE_BRACKET\", Insert \"CLOSE_BRACKET\"",
                                "Insert \"B\", Insert \"CLOSE_BRACKET\", Insert \"CLOSE_BRACKET\""]);
    }

    #[test]
    fn expr_grammar() {
        let lexs = "%%
[(] OPEN_BRACKET
[)] CLOSE_BRACKET
[+] PLUS
[*] MULT
[0-9]+ INT
[ ] ;
";

        let grms = "%start Expr
%%
Expr: Term 'PLUS' Expr
    | Term ;

Term: Factor 'MULT' Term
    | Factor ;

Factor: 'OPEN_BRACKET' Expr 'CLOSE_BRACKET'
      | 'INT' ;
";

        let us = "(2 3";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"CLOSE_BRACKET\", Insert \"PLUS\"",
                                "Insert \"CLOSE_BRACKET\", Insert \"MULT\"",
                                "Insert \"CLOSE_BRACKET\", Delete",
                                "Insert \"PLUS\", Shift, Insert \"CLOSE_BRACKET\"",
                                "Insert \"MULT\", Shift, Insert \"CLOSE_BRACKET\""]);
    }

    #[test]
    fn find_shortest() {
        let lexs = "%%
a A
b B
c C
";

        let grms = "%start S
%%
S: T U 'C';
T: 'A';
U: 'B';
";

        // We expect this example not to find any repairs with KimYi
        let us = "c";
        let (_, pr) = do_parse(RecoveryKind::KimYiPlus, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs[0].repairs().len(), 0);

        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"A\", Insert \"B\""]);
    }

    #[test]
    fn deletes_after_inserts() {
        let lexs = "%%
a A
b B
c C
d D
";

        let grms = "%start S
%%
S:  'A' 'B' 'D' | 'A' 'B' 'C' 'A' 'A' 'D';
";

        // KimYiPlus incorrectly finds a long repair when a shorter one exists

        let us = "acd";
        let (grm, pr) = do_parse(RecoveryKind::KimYiPlus, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"B\", Shift, Insert \"A\", Insert \"A\""]);

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
a A
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
    fn dont_shift_and_insert_the_same_terminal() {
        let (lexs, grms) = kimyi_lex_grm();
        let us = "(()";
        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"A\", Insert \"CLOSE_BRACKET\"",
                                "Insert \"B\", Insert \"CLOSE_BRACKET\""]);
    }

    #[test]
    fn test_counting_shifts() {
        let mut c = Cactus::new();
        assert_eq!(ends_with_parse_at_least_shifts(&c), false);
        for _ in 0..PARSE_AT_LEAST - 1 {
            c = c.child(Repair::Shift);
            assert_eq!(ends_with_parse_at_least_shifts(&c), false);
        }
        c = c.child(Repair::Shift);
        assert_eq!(ends_with_parse_at_least_shifts(&c), true);

        let mut c = Cactus::new();
        assert_eq!(ends_with_parse_at_least_shifts(&c), false);
        c = c.child(Repair::Delete);
        for _ in 0..PARSE_AT_LEAST - 1 {
            c = c.child(Repair::Shift);
            assert_eq!(ends_with_parse_at_least_shifts(&c), false);
        }
        c = c.child(Repair::Shift);
        assert_eq!(ends_with_parse_at_least_shifts(&c), true);
    }
}
