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

use std::hash::{Hash, Hasher};
use std::time::Instant;

use cactus::Cactus;
use cfgrammar::TIdx;
use lrlex::Lexeme;
use lrtable::{Action, StIdx};
use num_traits::{PrimInt, Unsigned};

use astar::astar_all;
use mf::{apply_repairs, Dist, rank_cnds, simplify_repairs};
use parser::{Node, Parser, ParseRepair, Recoverer};

const PARSE_AT_LEAST: usize = 3; // N in Corchuelo et al.

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
    cf: u32,
    cg: u32
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

        let num_shifts = |c: &Cactus<RepairMerge>| {
            let mut n = 0;
            for r in c.vals() {
                match r {
                      &RepairMerge::Repair(Repair::Shift)
                    | &RepairMerge::Merge(Repair::Shift, _) => n += 1,
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

struct CPCTPlusDynDist<'a, TokId: PrimInt + Unsigned> where TokId: 'a {
    dist: Dist,
    parser: &'a Parser<'a, TokId>
}

pub(crate) fn recoverer<'a, TokId: PrimInt + Unsigned>
                       (parser: &'a Parser<TokId>)
                     -> Box<Recoverer<TokId> + 'a>
{
    let dist = Dist::new(parser.grm, parser.sgraph, parser.stable, parser.term_cost);
    Box::new(CPCTPlusDynDist{dist, parser: parser})
}

impl<'a, TokId: PrimInt + Unsigned> Recoverer<TokId> for CPCTPlusDynDist<'a, TokId>
{
    fn recover(&self,
               finish_by: Instant,
               parser: &Parser<TokId>,
               in_la_idx: usize,
               mut in_pstack: &mut Vec<StIdx>,
               mut tstack: &mut Vec<Node<TokId>>)
           -> (usize, Vec<Vec<ParseRepair>>)
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

impl<'a, TokId: PrimInt + Unsigned> CPCTPlusDynDist<'a, TokId> {
    fn insert(&self,
             n: &PathFNode,
             nbrs: &mut Vec<(u32, u32, PathFNode)>)
    {
        let la_idx = n.la_idx;
        for t_idx in self.parser.stable.state_actions(*n.pstack.val().unwrap()) {
            if t_idx == self.parser.grm.eof_term_idx() {
                continue;
            }

            let next_lexeme = self.parser.next_lexeme(n.la_idx);
            let new_lexeme = Lexeme::new(TokId::from(u32::from(t_idx)).unwrap(),
                                         next_lexeme.start(), 0);
            let (new_la_idx, n_pstack) =
                self.parser.lr_cactus(Some(new_lexeme), la_idx, la_idx + 1,
                                      n.pstack.clone(), &mut None);
            if new_la_idx > la_idx {
                let n_repairs = n.repairs.child(RepairMerge::Repair(Repair::InsertTerm(t_idx)));
                if let Some(d) = self.dyn_dist(&n_repairs, *n_pstack.val().unwrap(), n.la_idx) {
                    let nn = PathFNode{
                        pstack: n_pstack,
                        la_idx: n.la_idx,
                        repairs: n.repairs.child(RepairMerge::Repair(Repair::InsertTerm(t_idx))),
                        cf: n.cf.checked_add((self.parser.term_cost)(t_idx) as u32).unwrap(),
                        cg: d};
                    nbrs.push((nn.cf, nn.cg, nn));
                }
            }
        }
    }

    fn delete(&self,
              n: &PathFNode,
              nbrs: &mut Vec<(u32, u32, PathFNode)>)
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
                               cf: n.cf.checked_add(cost as u32).unwrap(),
                               cg: d};
            nbrs.push((nn.cf, nn.cg, nn));
        }
    }

    fn shift(&self,
             n: &PathFNode,
             nbrs: &mut Vec<(u32, u32, PathFNode)>)
    {
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
            if let Some(d) = self.dyn_dist(&n_repairs, *n_pstack.val().unwrap(), new_la_idx) {
                let nn = PathFNode{
                    pstack: n_pstack,
                    la_idx: new_la_idx,
                    repairs: n_repairs,
                    cf: n.cf,
                    cg: d};
                nbrs.push((nn.cf, nn.cg, nn));
            }
        }
    }

    /// Convert the output from `astar_all` into something more usable.
    fn collect_repairs(&self, cnds: Vec<PathFNode>) -> Vec<Vec<Vec<ParseRepair>>>
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
            all_rprs.push(traverse(&cnd.repairs).into_iter()
                                                .map(|x| self.repair_to_parse_repair(x))
                                                .collect::<Vec<_>>());
        }
        all_rprs
    }

    fn repair_to_parse_repair(&self,
                              from: Vec<Repair>)
                           -> Vec<ParseRepair> {
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
                repairs: &Cactus<RepairMerge>,
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
            dc = dc + (self.parser.term_cost)(t_idx) as u32;
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
    use std::collections::HashMap;

    use cactus::Cactus;
    use cfgrammar::yacc::YaccGrammar;
    use lrlex::Lexeme;
    use num_traits::ToPrimitive;

    use parser::{ParseRepair, RecoveryKind};
    use parser::test::{do_parse, do_parse_with_costs};

    use super::{ends_with_parse_at_least_shifts, PARSE_AT_LEAST, Repair, RepairMerge};

    fn pp_repairs(grm: &YaccGrammar, repairs: &Vec<ParseRepair>) -> String {
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

    fn check_some_repairs(grm: &YaccGrammar,
                          repairs: &Vec<Vec<ParseRepair>>,
                          expected: &[&str]) {
        for i in 0..expected.len() {
            if repairs.iter().find(|x| pp_repairs(&grm, x) == expected[i]).is_none() {
                panic!("No match found for:\n  {}", expected[i]);
            }
        }
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
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, us);
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

        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, "n)+n+n+n)");
        let (_, errs) = pr.unwrap_err();
        assert_eq!(errs.len(), 2);
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Delete"]);
        check_all_repairs(&grm,
                          errs[1].repairs(),
                          &vec!["Delete"]);

        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, "(((+n)+n+n+n)");
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
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us);
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
        let err_tok_id = u32::from(grm.eof_term_idx()).to_u16().unwrap();
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
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"CLOSE_BRACKET\", Insert \"PLUS\"",
                                "Insert \"CLOSE_BRACKET\", Insert \"MULT\"",
                                "Insert \"CLOSE_BRACKET\", Delete",
                                "Insert \"PLUS\", Shift, Insert \"CLOSE_BRACKET\"",
                                "Insert \"MULT\", Shift, Insert \"CLOSE_BRACKET\""]);


        let us = "(+++++)";
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_some_repairs(&grm,
                           errs[0].repairs(),
                           &vec!["Insert \"INT\", Delete, Delete, Delete, Delete, Delete"]);
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

        let us = "c";
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us);
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

        let us = "acd";
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us);
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
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"A\""]);
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
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us);
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
a a
b b
c c
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
        let (grm, pr) = do_parse_with_costs(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us, &costs);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\", Insert \"a\""]);
    }

    #[test]
    fn test_cerecke_lr2() {
        // Example taken from p54 of Locally least-cost error repair in LR parsers, Carl Cerecke
        let lexs = "%%
a a
b b
c c
d d
e e
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

        do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &"acd").1.unwrap();
        do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &"bce").1.unwrap();
        let us = "ce";
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"b\""]);
        let us = "cd";
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us);
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
a a
b b
c c
d d
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
        let (grm, pr) = do_parse_with_costs(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us, &costs);
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
a a
c c
d d
";

        let grms = "%start S
%%
S: A A 'a';
A: 'c' 'd';
";

        let us = "";
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us);
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
a a
b b
c c
d d
";

        let grms = "%start S
%%
S: C D 'a' | D C 'b';
C: 'c';
D: 'd';
";

        let us = "";
        let (grm, pr) = do_parse(RecoveryKind::CPCTPlusDynDist, &lexs, &grms, &us);
        let (_, errs) = pr.unwrap_err();
        check_all_repairs(&grm,
                          errs[0].repairs(),
                          &vec!["Insert \"c\", Insert \"d\", Insert \"a\"",
                                "Insert \"d\", Insert \"c\", Insert \"b\""]);
    }

    #[test]
    fn test_counting_shifts() {
        let mut c = Cactus::new();
        assert_eq!(ends_with_parse_at_least_shifts(&c), false);
        for _ in 0..PARSE_AT_LEAST - 1 {
            c = c.child(RepairMerge::Repair(Repair::Shift));
            assert_eq!(ends_with_parse_at_least_shifts(&c), false);
        }
        c = c.child(RepairMerge::Repair(Repair::Shift));
        assert_eq!(ends_with_parse_at_least_shifts(&c), true);

        let mut c = Cactus::new();
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
