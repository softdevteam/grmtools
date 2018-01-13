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
use cfgrammar::{Grammar, Symbol, TIdx};
use cfgrammar::yacc::{SentenceGenerator, YaccGrammar};
use lrtable::{Action, StateGraph, StateTable, StIdx};
use pathfinding::astar_bag;

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
    cf: u64,
    cg: u64
}

impl Hash for PathFNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.pstack.hash(state);
        self.la_idx.hash(state);
        self.cf.hash(state);
        self.cg.hash(state);
    }
}

impl PartialEq for PathFNode {
    fn eq(&self, other: &PathFNode) -> bool {
        self.pstack == other.pstack && self.la_idx == other.la_idx && self.cf == other.cf && self.cg == other.cg
    }
}

pub(crate) struct MF<'a> {
    dist: Dist,
    sg: SentenceGenerator<'a>
}

pub(crate) fn recoverer<'a, TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
                       (parser: &'a Parser<TokId>)
                     -> Box<Recoverer<TokId> + 'a>
{
    let dist = Dist::new(parser.grm, parser.sgraph, parser.stable, |x| parser.ic(Symbol::Term(x)));
    let sg = parser.grm.sentence_generator(|x| parser.ic(Symbol::Term(x)));
    Box::new(MF{dist, sg})
}

impl<'a, TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
    Recoverer<TokId> for MF<'a>
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
        let (astar_cnds, _) = astar_bag(
            &start_node,
            |n| {
                // Calculate n's neighbours.

                if n.la_idx > in_la_idx + PORTION_THRESHOLD {
                    return vec![];
                }

                let mut nbrs = HashSet::new();
                match n.repairs.val() {
                    Some(&Repair::Delete) => {
                        // We follow Corcheulo et al.'s suggestions and never follow Deletes with
                        // Inserts.
                    },
                    _ => {
                        r3is(parser, &self.dist, &n, &mut nbrs);
                        r3ir(parser, &self.sg, &n, &mut nbrs);
                    }
                }
                r3d(parser, &n, &mut nbrs);
                r3s_n(parser, &n, &mut nbrs);

                let v = nbrs.into_iter()
                            .map(|x| {
                                    let t = x.cf - n.cf;
                                    (x, t)
                                 })
                            .collect::<Vec<(PathFNode, _)>>();
                v
            },
            |n| n.cg,
            |n| {
                // Is n a success node?

                // As presented in both Corchuelo et al. and Kim Yi, one type of success is if N
                // symbols are parsed in one go. Indeed, without such a check, the search space
                // quickly becomes too big. There isn't a way of encoding this check in r3s_n, so
                // we check instead for its result: if the last N ('PARSE_AT_LEAST' in this
                // library) repairs are shifts, then we've found a success node.
                if n.repairs.len() > PARSE_AT_LEAST {
                    let mut all_shfts = true;
                    for x in n.repairs.vals().take(PARSE_AT_LEAST) {
                        if let Repair::Shift = *x {
                            continue;
                        }
                        all_shfts = false;
                        break;
                    }
                    if all_shfts {
                        return true;
                    }
                }

                let (_, la_term) = parser.next_lexeme(None, n.la_idx);
                match parser.stable.action(*n.pstack.val().unwrap(), la_term) {
                    Some(Action::Accept) => true,
                    _ => false,
                }
            });

        if astar_cnds.is_empty() {
            return (in_la_idx, vec![]);
        }

        let full_rprs = collect_repairs(astar_cnds);
        let smpl_rprs = simplify_repairs(parser, full_rprs);
        let rnk_rprs = rank_cnds(parser,
                                 in_la_idx,
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

fn r3is<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
       (parser: &Parser<TokId>,
        dist: &Dist,
        n: &PathFNode,
        nbrs: &mut HashSet<PathFNode>)
{
    let top_pstack = *n.pstack.val().unwrap();
    let (_, la_term) = parser.next_lexeme(None, n.la_idx);
    if let Symbol::Term(la_term_idx) = la_term {
        for (&sym, &sym_st_idx) in parser.sgraph.edges(top_pstack).iter() {
            if let Symbol::Term(term_idx) = sym {
                if term_idx == parser.grm.eof_term_idx() {
                    continue;
                }

                if let Some(d) = dist.dist(sym_st_idx, la_term_idx) {
                    let nn = PathFNode{
                        pstack: n.pstack.child(sym_st_idx),
                        la_idx: n.la_idx,
                        repairs: n.repairs.child(Repair::InsertTerm(term_idx)),
                        cf: n.cf + parser.ic(Symbol::Term(term_idx)),
                        cg: d};
                    nbrs.insert(nn);
                }
            }
        }
    }
}

fn r3ir<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
       (parser: &Parser<TokId>,
        sg: &SentenceGenerator,
        n: &PathFNode,
        nbrs: &mut HashSet<PathFNode>)
{
    let top_pstack = *n.pstack.val().unwrap();
    for &(p_idx, sym_off) in parser.sgraph.core_state(top_pstack).items.keys() {
        let nt_idx = parser.grm.prod_to_nonterm(p_idx);
        let mut qi_minus_alpha = n.pstack.clone();
        for _ in 0..usize::from(sym_off) {
            qi_minus_alpha = qi_minus_alpha.parent().unwrap();
        }

        if let Some(goto_st_idx) = parser.stable
                                         .goto(*qi_minus_alpha.val().unwrap(),
                                               nt_idx) {
            let mut n_repairs = n.repairs.clone();
            let mut cost = 0;
            for sym in parser.grm.prod(p_idx)
                                 .iter()
                                 .skip(sym_off.into()) {
                match sym {
                    &Symbol::Nonterm(nonterm_idx) => {
                        n_repairs = n_repairs.child(Repair::InsertNonterm(nonterm_idx));
                        cost += sg.min_sentence_cost(nonterm_idx);
                    },
                    &Symbol::Term(term_idx) => {
                        n_repairs = n_repairs.child(Repair::InsertTerm(term_idx));
                        cost += parser.ic(*sym);
                    }
                }
            }
            let nn = PathFNode{
                pstack: qi_minus_alpha.child(goto_st_idx),
                la_idx: n.la_idx,
                repairs: n_repairs,
                cf: n.cf + cost,
                cg: 0};
            nbrs.insert(nn);
        }
    }
}

fn r3d<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
      (parser: &Parser<TokId>,
       n: &PathFNode,
       nbrs: &mut HashSet<PathFNode>)
{
    if n.la_idx == parser.lexemes.len() {
        return;
    }

    let (_, la_term) = parser.next_lexeme(None, n.la_idx);
    let nn = PathFNode{pstack: n.pstack.clone(),
                       la_idx: n.la_idx + 1,
                       repairs: n.repairs.child(Repair::Delete),
                       cf: n.cf + parser.dc(la_term),
                       cg: 0};
    nbrs.insert(nn);
}

fn r3s_n<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
        (parser: &Parser<TokId>,
         n: &PathFNode,
         nbrs: &mut HashSet<PathFNode>)
{
    let (new_la_idx, n_pstack) = parser.lr_cactus(None,
                                                  n.la_idx,
                                                  n.la_idx + 1,
                                                  n.pstack.clone(),
                                                  &mut None);
    if new_la_idx == n.la_idx + 1 {
        let nn = PathFNode{
            pstack: n_pstack,
            la_idx: new_la_idx,
            repairs: n.repairs.child(Repair::Shift),
            cf: n.cf,
            cg: 0};
        nbrs.insert(nn);
    }
}

/// Convert the output from `astar_bag` into something more usable.
fn collect_repairs(cnds: Vec<Vec<PathFNode>>) -> Vec<Vec<Repair>>
{
    let mut all_rprs = Vec::new();
    for mut rprs in cnds.into_iter() {
        let mut y = rprs.pop()
                        .unwrap()
                        .repairs
                        .vals()
                        .cloned()
                        .collect::<Vec<Repair>>();
        y.reverse();
        all_rprs.push(y);
    }
    all_rprs
}

/// Take an (unordered) set of parse repairs and return a simplified (unordered) set of parse
/// repairs. Note that the caller must make no assumptions about the size or contents of the output
/// set: this function might delete, expand, or do other things to repairs.
fn simplify_repairs<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
                   (parser: &Parser<TokId>,
                    mut all_rprs: Vec<Vec<Repair>>)
                 -> Vec<Vec<ParseRepair>>
{
    let sg = parser.grm.sentence_generator(|x| parser.ic(Symbol::Term(x)));
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
fn rank_cnds<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
            (parser: &Parser<TokId>,
             in_la_idx: usize,
             start_pstack: Cactus<StIdx>,
             in_cnds: Vec<Vec<ParseRepair>>)
          -> Vec<Vec<ParseRepair>>
{
    let mut cnds = in_cnds.into_iter()
                          .map(|rprs| {
                               let (la_idx, pstack) = apply_repairs(parser,
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
            let (new_la_idx, new_pstack) = parser.lr_cactus(None,
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

pub(crate) struct Dist {
    terms_len: usize,
    table: Vec<u64>
}

impl Dist {
    pub(crate) fn new<F>(grm: &YaccGrammar, sgraph: &StateGraph, stable: &StateTable, term_cost: F) -> Dist
              where F: Fn(TIdx) -> u64
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

        let terms_len = grm.terms_len();
        let states_len = sgraph.all_states_len();
        let sengen = grm.sentence_generator(&term_cost);
        let mut table = Vec::new();
        table.resize(states_len * terms_len, u64::max_value());
        table[usize::from(stable.final_state) * terms_len + usize::from(grm.eof_term_idx())] = 0;

        // rev_edges allows us to walk backwards over the stategraph
        let mut rev_edges = Vec::with_capacity(states_len);
        rev_edges.resize(states_len, HashSet::new());
        for i in 0..states_len {
            for (_, &sym_st_idx) in sgraph.edges(StIdx::from(i)).iter() {
                rev_edges[usize::from(sym_st_idx)].insert(StIdx::from(i));
            }
        }

        // goto_edges is a map from a core state ready for reduction (i.e. where the dot is at the
        // end of the production and thus sym_off == prod.len()) represented as a tuple
        // (state_index, production_index) to a set of state indexes. The latter represents all the
        // states which after (possibly recursive and intertwined) reductions and gotos the parser
        // might end up in.
        //
        // We calculate this for a state i, production p_idx, by iterating backwards over the
        // stategraph (using rev_edges) finding all routes of length grm.prod(p_idx).len() which
        // could lead back to i, and then storing their goto state indexes. Since further
        // reductions and gotos could then happen, we then have to recursively search those goto
        // state indexes from scratch.
        //
        // This loop is currently comically inefficient, but it is relatively straightforward.
        let mut goto_edges = HashMap::new();
        for i in 0..states_len {
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
                    goto_edges.insert((i, p_idx), ge);
                }
            }
        }

        // We can now interleave KimYi's original dist algorithm with our addition which takes into
        // account goto_edges.
        loop {
            let mut chgd = false; // Has anything changed?

            for i in 0..states_len {
                // The first phase is KimYi's dist algorithm.
                let edges = sgraph.edges(StIdx::from(i));
                for (&sym, &sym_st_idx) in edges.iter() {
                    let d = match sym {
                        Symbol::Nonterm(nt_idx) => sengen.min_sentence_cost(nt_idx),
                        Symbol::Term(t_idx) => {
                            let off = usize::from(i) * terms_len + usize::from(t_idx);
                            if table[off] != 0 {
                                table[off] = 0;
                                chgd = true;
                            }
                            term_cost(t_idx)
                        }
                    };

                    for j in 0..terms_len {
                        let this_off = usize::from(i) * terms_len + usize::from(j);
                        let other_off = usize::from(sym_st_idx) * terms_len + usize::from(j);

                        if table[other_off] != u64::max_value()
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
                        for goto_idx in goto_edges.get(&(i, p_idx)).unwrap() {
                            for j in 0..terms_len {
                                let this_off = usize::from(i) * terms_len + usize::from(j);
                                let other_off = usize::from(*goto_idx) * terms_len + usize::from(j);

                                if table[other_off] != u64::max_value() &&
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

        Dist{terms_len, table}
    }

    pub(crate) fn dist(&self, st_idx: StIdx, t_idx: TIdx) -> Option<u64> {
        let e = self.table[usize::from(st_idx) * self.terms_len + usize::from(t_idx)];
        if e == u64::max_value() {
            None
        } else {
            Some(e as u64)
        }
    }
}

#[cfg(test)]
mod test {
    use std::convert::TryFrom;
    use test::{Bencher, black_box};

    use cfgrammar::Symbol;
    use cfgrammar::yacc::{yacc_grm, YaccGrammar, YaccKind};
    use lrlex::Lexeme;
    use lrtable::{Minimiser, from_yacc, StIdx};

    use parser::{ParseRepair, RecoveryKind};
    use parser::test::do_parse;
    use kimyi::test::pp_repairs;

    use super::Dist;

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
        let s0 = StIdx::from(0);
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

        let s0 = StIdx::from(0);
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

        let s0 = StIdx::from(0);
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


    #[test]
    fn kimyi_example() {
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

        let (grm, pr) = do_parse(RecoveryKind::MF, &lexs, &grms, "((");
        let (pt, errs) = pr.unwrap_err();
        let pp = pt.unwrap().pp(&grm, "((");
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
                                "Insert \"B\", Insert \"CLOSE_BRACKET\", Insert \"CLOSE_BRACKET\"",
                                "Insert {\"A\", \"B\"}, Insert \"CLOSE_BRACKET\", Insert \"CLOSE_BRACKET\""]);
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
}
