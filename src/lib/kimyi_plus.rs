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
use std::collections::HashSet;
use std::convert::{TryFrom, TryInto};
use std::fmt::Debug;

use cactus::Cactus;
use cfgrammar::Symbol;
use lrtable::{Action, StIdx};
use pathfinding::astar_bag;

use kimyi::{apply_repairs, Dist, PathFNode, r3is, r3ir, r3d, r3s_n};
use parser::{Node, Parser, ParseRepair};

const PARSE_AT_LEAST: usize = 4; // N in Corchuelo et al.
const PORTION_THRESHOLD: usize = 10; // N_t in Corchuelo et al.
const TRY_PARSE_AT_MOST: usize = 250;

pub(crate) fn recover<TokId: Clone + Copy + Debug + TryFrom<usize> + TryInto<usize> + PartialEq>
                     (parser: &Parser<TokId>, in_la_idx: usize, in_pstack: &mut Vec<StIdx>,
                      mut tstack: &mut Vec<Node<TokId>>)
                  -> (usize, Vec<Vec<ParseRepair>>)
{
    // This function implements an algorithm whose core is based on that from "LR error repair
    // using the A* algorithm" by Ik-Soon Kim and Kwangkeun Yi. However, we extend it in several
    // ways.
    //
    // The basic idea behind this implementation is to use the transition rules from Fig 9 (along
    // with the altered version of R3S presented on p12) as a mechanism for dynamically calculating
    // the neighbours of the current node under investigation. Unlike KimYi, who
    // non-deterministically return a single repair, this variant evaluates all minimal cost
    // repairs.

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
    let (astar_cnds, _) = astar_bag(
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

/// Convert the output from `astar_bag` into something more usable.
fn collect_repairs(cnds: Vec<Vec<PathFNode>>) -> Vec<Vec<ParseRepair>>
{
    let mut all_rprs = Vec::new();
    for mut rprs in cnds.into_iter() {
        let mut y = rprs.pop()
                        .unwrap()
                        .repairs
                        .vals()
                        .cloned()
                        .collect::<Vec<ParseRepair>>();
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
                    mut all_rprs: Vec<Vec<ParseRepair>>)
                 -> Vec<Vec<ParseRepair>>
{
    let sg = parser.grm.sentence_generator(|x| parser.ic(Symbol::Term(x)));
    for i in 0..all_rprs.len() {
        {
            // Remove all inserts of nonterms which have a minimal sentence cost of 0.
            let mut rprs = all_rprs.get_mut(i).unwrap();
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
        }

        {
            // Remove shifts from the end of repairs
            let mut rprs = all_rprs.get_mut(i).unwrap();
            while rprs.len() > 0 {
                if let ParseRepair::Shift = rprs[rprs.len() - 1] {
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

    all_rprs
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

#[cfg(test)]
mod test {
    use std::convert::TryFrom;

    use cfgrammar::yacc::YaccGrammar;
    use lrlex::Lexeme;

    use parser::{ParseRepair, RecoveryKind};
    use parser::test::do_parse;
    use kimyi::test::{check_repairs, pp_repairs};

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

        let (grm, pr) = do_parse(RecoveryKind::KimYiPlus, &lexs, &grms, "(nn");
        let (pt, errs) = pr.unwrap_err();
        let pp = pt.unwrap().pp(&grm, "(nn");
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
        assert_eq!(errs[0].repairs().len(), 3);
        check_repairs(&grm,
                      errs[0].repairs(),
                      &vec!["InsertTerm \"CLOSE_BRACKET\", InsertTerm \"PLUS\"",
                            "InsertTerm \"CLOSE_BRACKET\", Delete",
                            "InsertTerm \"PLUS\", Shift, InsertTerm \"CLOSE_BRACKET\""]);

        let (grm, pr) = do_parse(RecoveryKind::KimYiPlus, &lexs, &grms, "n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Delete"]);
        check_all_repairs(&grm,
                          errs[1].repairs(),
                          &vec!["Delete"]);

        let (grm, pr) = do_parse(RecoveryKind::KimYiPlus, &lexs, &grms, "(((+n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["InsertTerm \"N\"",
                                "Delete"]);
        check_all_repairs(&grm,
                          errs[1].repairs(),
                          &vec!["InsertTerm \"CLOSE_BRACKET\""]);
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

        let (grm, pr) = do_parse(RecoveryKind::KimYiPlus, &lexs, &grms, "((");
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
        assert_eq!(errs[0].repairs().len(), 1);
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["InsertNonterm \"E\", InsertTerm \"CLOSE_BRACKET\", InsertTerm \"CLOSE_BRACKET\""]);
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
        let (grm, pr) = do_parse(RecoveryKind::KimYiPlus, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["InsertTerm \"CLOSE_BRACKET\", InsertTerm \"PLUS\"",
                                "InsertTerm \"CLOSE_BRACKET\", InsertTerm \"MULT\"",
                                "InsertTerm \"CLOSE_BRACKET\", Delete",
                                "InsertTerm \"PLUS\", Shift, InsertTerm \"CLOSE_BRACKET\"",
                                "InsertTerm \"MULT\", Shift, InsertTerm \"CLOSE_BRACKET\""]);
    }
}
