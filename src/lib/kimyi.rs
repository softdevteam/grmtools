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

use std::collections::HashSet;
use std::convert::{TryFrom, TryInto};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};

use cactus::Cactus;
use cfgrammar::{Grammar, Symbol, TIdx};
use cfgrammar::yacc::YaccGrammar;
use lrlex::Lexeme;
use lrtable::{Action, StateGraph, StIdx};
use pathfinding::astar;

use parser::{Node, Parser, ParseRepair};

const PARSE_AT_LEAST: usize = 4; // N in Corchuelo et al.
const PORTION_THRESHOLD: usize = 10; // N_t in Corchuelo et al.

#[derive(Clone, Debug, Eq)]
struct PathFNode {
    pstack: Cactus<StIdx>,
    la_idx: usize,
    t: u64,
    repairs: Cactus<ParseRepair>,
    cf: u64,
    cg: u64
}

impl Hash for PathFNode {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.pstack.hash(state);
        self.la_idx.hash(state);
    }
}

impl PartialEq for PathFNode {
    fn eq(&self, other: &PathFNode) -> bool {
        self.pstack == other.pstack && self.repairs == other.repairs && self.la_idx == other.la_idx
    }
}

pub(crate) fn recover<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
                     (parser: &Parser<TokId>, in_la_idx: usize, in_pstack: &mut Vec<StIdx>,
                      mut tstack: &mut Vec<Node<TokId>>)
                  -> (usize, Vec<Vec<ParseRepair>>)
{
    // This function implements the algorithm from "LR error repair using the A* algorithm" by
    // Ik-Soon Kim and Kwangkeun Yi
    //
    // The basic idea is to define the problem of finding repairs as a graph-walking problem: we
    // find the shortest route through the graph to a success node using the standard A* algorithm.
    // Unfortunately, the paper is a hard read: it's sometimes incomplete, often vague, and
    // frequently contains errors. Notably, the example on p13 is absolutely crucial to
    // understanding how the algorithm works, but it is so riddled with errors as to be thoroughly
    // misleading. Fortunately, however, the ideas underlying the paper are worth the effort.
    //
    // This function is, I hope, a fairly faithful implementation. The basic idea behind this
    // implementation is to use the transition rules from Fig 9 (along with the altered version of
    // R3S presented on p12) as a mechanism for dynamically calculating the neighbours of the
    // current node under investigation. As the paper suggests, this only finds a single minimal
    // cost solution to each parser error, so it's highly non-deterministic: sometimes the minimal
    // cost solution it comes up with is good, and sometimes it isn't. It is, however, pretty fast,
    // certainly compared to the Corchuelo et al. algorithm. The biggest extension relative to the
    // paper is that they really only care about finding a repair: they don't seem to care about
    // reporting that to the user. The repairs thus reference non-terminals in the grammar which,
    // to most users, are completely incomprehensible. This commit uses cfgrammar's
    // SentenceGenerator to turn a non-terminal repair into a (possible set) of terminal inserts,
    // which is infinitely easier to understand. Thus whilst KimYi might say a repair is:
    //
    //   InsertNonterm expr
    //
    // this commit will say something like:
    //
    //  InsertTerm {Var, Identifier}, InsertTerm{+, -, *}, InsertTerm {Var, Identifier}

    let mut start_cactus_pstack = Cactus::new();
    for st in in_pstack.drain(..) {
        start_cactus_pstack = start_cactus_pstack.child(st);
    }

    let dist = Dist::new(parser.grm, parser.sgraph, |x| parser.ic(Symbol::Term(x)));
    let start_node = PathFNode{pstack: start_cactus_pstack.clone(),
                               la_idx: in_la_idx,
                               t: 1,
                               repairs: Cactus::new(),
                               cf: 0,
                               cg: 0};
    let astar_opt = astar(
        &start_node,
        |n| {
            // Calculate n's neighbours.

            if n.la_idx > in_la_idx + PORTION_THRESHOLD {
                return vec![];
            }

            let mut nbrs = HashSet::new();
            match n.repairs.val() {
                Some(&ParseRepair::Delete) => {
                    // We follow Corcheulo et al.'s suggestions and never follow Deletes with
                    // Inserts.
                },
                _ => {
                    r3is(parser, &dist, &n, &mut nbrs);
                    r3ir(parser, &n, &mut nbrs);
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
            // symbols are parsed in one go. Indeed, without such a check, the search space quickly
            // becomes too big. There isn't a way of encoding this check in r3s_n, so we check
            // instead for its result: if the last N ('PARSE_AT_LEAST' in this library) repairs are
            // shifts, then we've found a success node.
            if n.repairs.len() > PARSE_AT_LEAST {
                let mut all_shfts = true;
                for x in n.repairs.vals().take(PARSE_AT_LEAST) {
                    if let ParseRepair::Shift = *x {
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

    if astar_opt.is_none() {
        return (in_la_idx, vec![]);
    }

    let full_rprs = collect_repairs(astar_opt.unwrap().0);
    let smpl_rprs = simplify_repairs(parser, full_rprs);
    let (la_idx, mut rpr_pstack) = apply_repairs(parser,
                                                 in_la_idx,
                                                 start_cactus_pstack,
                                                 &mut Some(&mut tstack),
                                                 &smpl_rprs);

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

    (la_idx, vec![smpl_rprs])
}

// The following 4 functions implement the operational semantics presented on pages 11 and 12 of
// the paper.

fn r3is<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
       (parser: &Parser<TokId>, dist: &Dist, n: &PathFNode, nbrs: &mut HashSet<PathFNode>)
{
    let top_pstack = *n.pstack.val().unwrap();
    let (_, la_term) = parser.next_lexeme(None, n.la_idx);
    if let Symbol::Term(la_term_idx) = la_term {
        for (&sym, &sym_st_idx) in parser.sgraph.edges(top_pstack).unwrap().iter() {
            if let Symbol::Term(term_idx) = sym {
                if term_idx == parser.grm.eof_term_idx() {
                    continue;
                }

                if let Some(d) = dist.dist(sym_st_idx, la_term_idx) {
                    let nn = PathFNode{
                        pstack: n.pstack.child(sym_st_idx),
                        la_idx: n.la_idx,
                        t: n.t + 1,
                        repairs: n.repairs.child(ParseRepair::InsertTerm{term_idx}),
                        cf: n.cf + parser.ic(Symbol::Term(term_idx)),
                        cg: d};
                    nbrs.insert(nn);
                }
            }
        }
    }
}

fn r3ir<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
       (parser: &Parser<TokId>, n: &PathFNode, nbrs: &mut HashSet<PathFNode>)
{
    if n.t != 1 {
        return;
    }

    let sg = parser.grm.sentence_generator(|x| parser.ic(Symbol::Term(x)));
    let top_pstack = *n.pstack.val().unwrap();
    for &(p_idx, sym_off) in parser.sgraph.closed_state(top_pstack).unwrap().items.keys() {
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
                                 .unwrap()
                                 .iter()
                                 .skip(sym_off.into()) {
                match sym {
                    &Symbol::Nonterm(nonterm_idx) => {
                        n_repairs = n_repairs.child(ParseRepair::InsertNonterm{nonterm_idx});
                        cost += sg.min_sentence_cost(nonterm_idx);
                    },
                    &Symbol::Term(term_idx) => {
                        n_repairs = n_repairs.child(ParseRepair::InsertTerm{term_idx});
                        cost += parser.ic(*sym);
                    }
                }
            }
            let nn = PathFNode{
                pstack: qi_minus_alpha.child(goto_st_idx),
                la_idx: n.la_idx,
                t: 1,
                repairs: n_repairs,
                cf: n.cf + cost,
                cg: 0};
            nbrs.insert(nn);
        }
    }
}

fn r3d<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
      (parser: &Parser<TokId>, n: &PathFNode, nbrs: &mut HashSet<PathFNode>)
{
    if n.t != 1 || n.la_idx == parser.lexemes.len() {
        return;
    }

    let (_, la_term) = parser.next_lexeme(None, n.la_idx);
    let nn = PathFNode{pstack: n.pstack.clone(),
                       la_idx: n.la_idx + 1,
                       t: 1,
                       repairs: n.repairs.child(ParseRepair::Delete),
                       cf: n.cf + parser.dc(la_term),
                       cg: 0};
    nbrs.insert(nn);
}

// Note that we implement R3S-n (on page 12), *not* R3S (on page 11), since the latter rule clearly
// doesn't work properly in the context of the overall algorithm.

fn r3s_n<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
      (parser: &Parser<TokId>, n: &PathFNode, nbrs: &mut HashSet<PathFNode>)
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
            t: 1,
            repairs: n.repairs.child(ParseRepair::Shift),
            cf: n.cf,
            cg: 0};
        nbrs.insert(nn);
    }
}

/// Convert the output from `astar` into something more usable.
fn collect_repairs(mut rprs: Vec<PathFNode>) -> Vec<ParseRepair>
{
    let mut y = rprs.pop()
                    .unwrap()
                    .repairs
                    .vals()
                    .cloned()
                    .collect::<Vec<ParseRepair>>();
    y.reverse();
    y
}

/// Take a vector of parse repairs and return a simplified version. Note that the caller must make
/// no assumptions about the size or contents of the output: this function might delete, expand, or
/// do other things to repairs.
fn simplify_repairs<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
                   (parser: &Parser<TokId>,
                    mut rprs: Vec<ParseRepair>)
                 -> Vec<ParseRepair>
{
    // Remove shifts from the end of repairs
    let sg = parser.grm.sentence_generator(|x| parser.ic(Symbol::Term(x)));
    while rprs.len() > 0 {
        if let ParseRepair::Shift = rprs[rprs.len() - 1] {
            rprs.pop();
        } else {
            break;
        }
    }

    // Remove all inserts of nonterms which have a minimal sentence cost of 0.
    let mut j = 0;
    while j < rprs.len() {
        if let ParseRepair::InsertNonterm{nonterm_idx} = rprs[j] {
            if sg.min_sentence_cost(nonterm_idx) == 0 {
                rprs.remove(j);
            } else {
                j += 1;
            }
        } else {
            j += 1;
        }
    }

    rprs
}

/// Apply the `repairs` to `pstack` starting at position `la_idx`: return the resulting parse
/// distance and a new pstack.
fn apply_repairs<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
                (parser: &Parser<TokId>,
                 mut la_idx: usize,
                 mut pstack: Cactus<StIdx>,
                 tstack: &mut Option<&mut Vec<Node<TokId>>>,
                 repairs: &Vec<ParseRepair>)
              -> (usize, Cactus<StIdx>)
{
    let sg = parser.grm.sentence_generator(|x| parser.ic(Symbol::Term(x)));
    for r in repairs.iter() {
        match *r {
            ParseRepair::InsertNonterm{nonterm_idx} => {
                let (next_lexeme, _) = parser.next_lexeme(None, la_idx);
                for t_idx in sg.min_sentence(nonterm_idx) {
                    let new_lexeme = Lexeme::new(TokId::try_from(usize::from(t_idx))
                                                                .ok()
                                                                .unwrap(),
                                                 next_lexeme.start(), 0);
                    pstack = parser.lr_cactus(Some(new_lexeme), la_idx, la_idx + 1,
                                              pstack, tstack).1;
                }
            }
            ParseRepair::InsertTerm{term_idx} => {
                let (next_lexeme, _) = parser.next_lexeme(None, la_idx);
                let new_lexeme = Lexeme::new(TokId::try_from(usize::from(term_idx))
                                                            .ok()
                                                            .unwrap(),
                                             next_lexeme.start(), 0);
                pstack = parser.lr_cactus(Some(new_lexeme), la_idx, la_idx + 1,
                                          pstack, tstack).1;
            },
            ParseRepair::Delete => {
                la_idx += 1;
            }
            ParseRepair::Shift => {
                let (new_la_idx, n_pstack) = parser.lr_cactus(None,
                                                              la_idx,
                                                              la_idx + 1,
                                                              pstack,
                                                              tstack);
                assert_eq!(new_la_idx, la_idx + 1);
                la_idx = new_la_idx;
                pstack = n_pstack;
            }
        }
    }
    (la_idx, pstack)
}

struct Dist {
    terms_len: usize,
    table: Vec<u64>
}

impl Dist {
    fn new<F>(grm: &YaccGrammar, sgraph: &StateGraph, term_cost: F) -> Dist
              where F: Fn(TIdx) -> u64
    {
        // This is a very simple, and not very efficient, implementation of dist: one could,
        // for example, cache results of already-seen states.

        let terms_len = grm.terms_len();
        let states_len = sgraph.all_states_len();
        let sengen = grm.sentence_generator(&term_cost);
        let mut table = Vec::new();
        table.resize(states_len * terms_len, u64::max_value());
        loop {
            let mut chgd = false; // Has anything changed?
            for i in 0..states_len {
                let edges = sgraph.edges(StIdx::from(i)).unwrap();
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

    use cfgrammar::Symbol;
    use cfgrammar::yacc::{yacc_grm, YaccKind};
    use lrlex::Lexeme;
    use lrtable::{Minimiser, from_yacc, StIdx};

    use parser::{ParseRepair, RecoveryKind};
    use parser::test::do_parse;
    use super::*;

    fn pp_repairs(grm: &YaccGrammar, repairs: &Vec<ParseRepair>) -> String {
        let mut out = vec![];
        for &r in repairs {
            match r {
                ParseRepair::InsertNonterm{nonterm_idx} =>
                    out.push(format!("InsertNonterm \"{}\"", grm.nonterm_name(nonterm_idx).unwrap())),
                ParseRepair::InsertTerm{term_idx} =>
                    out.push(format!("InsertTerm \"{}\"", grm.term_name(term_idx).unwrap())),
                ParseRepair::Delete =>
                    out.push(format!("Delete")),
                ParseRepair::Shift =>
                    out.push(format!("Shift"))
            }
        }
        out.join(", ")
    }

    fn check_repairs(grm: &YaccGrammar, repairs: &Vec<Vec<ParseRepair>>, expected: &[&str]) {
        for i in 0..repairs.len() {
            // First of all check that all the repairs are unique
            for j in i + 1..repairs.len() {
                assert_ne!(repairs[i], repairs[j]);
            }
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

        let (grm, pr) = do_parse(RecoveryKind::KimYi, &lexs, &grms, "(nn");
        let (pt, errs) = pr.unwrap_err();
        let pp = pt.pp(&grm, "(nn");
        if !vec![
"E
 OPEN_BRACKET (
 E
  E
   N n
  PLUS 
  N n
 CLOSE_BRACKET 
",
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
        check_repairs(&grm,
                      errs[0].repairs(),
                      &vec!["InsertTerm \"CLOSE_BRACKET\", InsertTerm \"PLUS\"",
                            "InsertTerm \"CLOSE_BRACKET\", Delete",
                            "InsertTerm \"PLUS\", Shift, InsertTerm \"CLOSE_BRACKET\""]);

        let (grm, pr) = do_parse(RecoveryKind::KimYi, &lexs, &grms, "n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_repairs(&grm,
                      errs[0].repairs(),
                      &vec!["Delete"]);
        check_repairs(&grm,
                      errs[1].repairs(),
                      &vec!["Delete"]);

        let (grm, pr) = do_parse(RecoveryKind::KimYi, &lexs, &grms, "(((+n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_repairs(&grm,
                      errs[0].repairs(),
                      &vec!["InsertTerm \"N\"",
                            "Delete"]);
        check_repairs(&grm,
                      errs[1].repairs(),
                      &vec!["InsertTerm \"CLOSE_BRACKET\""]);
    }

    #[test]
    fn kimyi_example() {
        // The example from the Corchuelo paper
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

        let (grm, pr) = do_parse(RecoveryKind::KimYi, &lexs, &grms, "((");
        let (pt, errs) = pr.unwrap_err();
        let pp = pt.pp(&grm, "((");
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
        assert_eq!(errs[0].repairs().len(), 1);
        check_repairs(&grm,
                      errs[0].repairs(),
                      &vec!["InsertTerm \"A\", InsertTerm \"CLOSE_BRACKET\", InsertTerm \"CLOSE_BRACKET\"",
                            "InsertTerm \"B\", InsertTerm \"CLOSE_BRACKET\", InsertTerm \"CLOSE_BRACKET\""]);
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

        let grm = yacc_grm(YaccKind::Original, grms).unwrap();
        let (sgraph, _) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, |_| 1);
        let s0 = StIdx::from(0);
        assert_eq!(d.dist(s0, grm.term_idx("(").unwrap()), Some(0));
        assert_eq!(d.dist(s0, grm.term_idx(")").unwrap()), Some(2));
        assert_eq!(d.dist(s0, grm.term_idx("a").unwrap()), Some(0));
        assert_eq!(d.dist(s0, grm.term_idx("b").unwrap()), Some(0));

        let s5 = sgraph.edge(s0, Symbol::Term(grm.term_idx("(").unwrap())).unwrap();
        assert_eq!(d.dist(s5, grm.term_idx("(").unwrap()), Some(0));
        assert_eq!(d.dist(s5, grm.term_idx(")").unwrap()), Some(1));
        assert_eq!(d.dist(s5, grm.term_idx("a").unwrap()), Some(0));
        assert_eq!(d.dist(s5, grm.term_idx("b").unwrap()), Some(0));

        let s6 = sgraph.edge(s5, Symbol::Nonterm(grm.nonterm_idx("A").unwrap())).unwrap();
        assert_eq!(d.dist(s6, grm.term_idx("(").unwrap()), None);
        assert_eq!(d.dist(s6, grm.term_idx(")").unwrap()), Some(0));
        assert_eq!(d.dist(s6, grm.term_idx("a").unwrap()), None);
        assert_eq!(d.dist(s6, grm.term_idx("b").unwrap()), None);
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
        let (sgraph, _) = from_yacc(&grm, Minimiser::Pager).unwrap();
        let d = Dist::new(&grm, &sgraph, |_| 1);

        // This only tests a subset of all the states and distances but, I believe, it tests all
        // more interesting edge cases that the example from the Kim/Yi paper.

        let s0 = StIdx::from(0);
        assert_eq!(d.dist(s0, grm.term_idx("+").unwrap()), Some(1));
        assert_eq!(d.dist(s0, grm.term_idx("*").unwrap()), Some(1));
        assert_eq!(d.dist(s0, grm.term_idx("(").unwrap()), Some(0));
        assert_eq!(d.dist(s0, grm.term_idx(")").unwrap()), Some(2));
        assert_eq!(d.dist(s0, grm.term_idx("INT").unwrap()), Some(0));

        let s1 = sgraph.edge(s0, Symbol::Term(grm.term_idx("(").unwrap())).unwrap();
        assert_eq!(d.dist(s1, grm.term_idx("+").unwrap()), Some(1));
        assert_eq!(d.dist(s1, grm.term_idx("*").unwrap()), Some(1));
        assert_eq!(d.dist(s1, grm.term_idx("(").unwrap()), Some(0));
        assert_eq!(d.dist(s1, grm.term_idx(")").unwrap()), Some(1));
        assert_eq!(d.dist(s1, grm.term_idx("INT").unwrap()), Some(0));

        let s2 = sgraph.edge(s0, Symbol::Nonterm(grm.nonterm_idx("Factor").unwrap())).unwrap();
        assert_eq!(d.dist(s2, grm.term_idx("+").unwrap()), Some(3));
        assert_eq!(d.dist(s2, grm.term_idx("*").unwrap()), Some(0));
        assert_eq!(d.dist(s2, grm.term_idx("(").unwrap()), Some(1));
        assert_eq!(d.dist(s2, grm.term_idx(")").unwrap()), Some(3));
        assert_eq!(d.dist(s2, grm.term_idx("INT").unwrap()), Some(1));

        let s3 = sgraph.edge(s0, Symbol::Term(grm.term_idx("INT").unwrap())).unwrap();
        assert_eq!(d.dist(s3, grm.term_idx("+").unwrap()), None);
        assert_eq!(d.dist(s3, grm.term_idx("*").unwrap()), None);
        assert_eq!(d.dist(s3, grm.term_idx("(").unwrap()), None);
        assert_eq!(d.dist(s3, grm.term_idx(")").unwrap()), None);
        assert_eq!(d.dist(s3, grm.term_idx("INT").unwrap()), None);
    }
}
