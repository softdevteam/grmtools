use std::collections::hash_map::{Entry, HashMap, OccupiedEntry};

use StIdx;
use grammar::{AssocKind, Grammar, PIdx, NTIdx, SIdx, Symbol, TIdx};
use stategraph::StateGraph;

/// A representation of a `StateTable` for a grammar. `actions` and `gotos` are split into two
/// separate hashmaps, rather than a single table, due to the different types of their values.
#[derive(Debug)]
pub struct StateTable {
    actions          : HashMap<(StIdx, Symbol), Action>,
    gotos            : HashMap<(StIdx, NTIdx), StIdx>,
    /// The number of reduce/reduce errors encountered.
    pub reduce_reduce: u64,
    /// The number of shift/reduce errors encountered.
    pub shift_reduce : u64
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Action {
    /// Shift to state X in the statetable.
    Shift(StIdx),
    /// Reduce production X in the grammar.
    Reduce(PIdx),
    /// Accept this input.
    Accept
}

impl StateTable {
    pub fn new(grm: &Grammar, sg: &StateGraph) -> StateTable {
        let mut actions: HashMap<(StIdx, Symbol), Action> = HashMap::new();
        let mut gotos  : HashMap<(StIdx, NTIdx), StIdx>   = HashMap::new();
        let mut reduce_reduce = 0; // How many automatically resolved reduce/reduces were made?
        let mut shift_reduce  = 0; // How many automatically resolved shift/reduces were made?

        for (state_i, state) in sg.states.iter().enumerate().map(|(x, y)| (StIdx(x), y)) {
            // Populate reduce and accepts
            for (&(prod_i, dot), ctx) in &state.items {
                if dot < SIdx::from(grm.prod(prod_i).unwrap().len()) {
                    continue;
                }
                for (term_i, _) in ctx.iter().enumerate().filter(|&(_, x)| x) {
                    let sym = Symbol::Terminal(TIdx::from(term_i));
                    match actions.entry((state_i, sym)) {
                        Entry::Occupied(mut e) => {
                            match *e.get_mut() {
                                Action::Reduce(prod_j) => {
                                    // By default, Yacc resolves reduce/reduce conflicts in favour
                                    // of the earlier production in the grammar.
                                    if prod_i < prod_j {
                                        reduce_reduce += 1;
                                        e.insert(Action::Reduce(prod_i));
                                    }
                                    else if prod_i > prod_j {
                                        reduce_reduce += 1;
                                    }
                                },
                                _ => panic!("Internal error")
                            }
                        }
                        Entry::Vacant(e) => {
                            if prod_i == grm.start_prod && TIdx::from(term_i) == grm.end_term {
                                e.insert(Action::Accept);
                            }
                            else {
                                e.insert(Action::Reduce(PIdx::from(prod_i)));
                            }
                        }
                    }
                }
            }

            for (&sym, state_j) in &sg.edges[usize::from(state_i)] {
                match sym {
                    Symbol::Nonterminal(nonterm_i) => {
                        // Populate gotos
                        debug_assert!(gotos.get(&(state_i, nonterm_i)).is_none());
                        gotos.insert((state_i, nonterm_i), *state_j);
                    },
                    Symbol::Terminal(term_k) => {
                        // Populate shifts
                        match actions.entry((state_i, sym)) {
                            Entry::Occupied(mut e) => {
                                match *e.get_mut() {
                                    Action::Shift(x) => assert_eq!(*state_j, x),
                                    Action::Reduce(prod_k) => {
                                        shift_reduce += resolve_shift_reduce(grm, e, term_k,
                                                                             prod_k, *state_j);
                                    }
                                    Action::Accept => panic!("Internal error")
                                }
                            },
                            Entry::Vacant(e) => {
                                e.insert(Action::Shift(*state_j));
                            }
                        }
                    }
                }
            }
        }

        StateTable { actions: actions, gotos: gotos, reduce_reduce: reduce_reduce,
                     shift_reduce: shift_reduce }
    }

    /// Return the action for `state_idx` and `sym`, or None if there isn't any.
    pub fn action(&self, state_idx: StIdx, sym: Symbol) -> Option<Action> {
        self.actions.get(&(state_idx, sym)).map_or(None, |x| Some(*x))
    }

    /// Return the goto state for `state_idx` and `nonterm_idx`, or None if there isn't any.
    pub fn goto(&self, state_idx: StIdx, nonterm_idx: NTIdx) -> Option<StIdx> {
        self.gotos.get(&(state_idx, nonterm_idx)).map_or(None, |x| Some(*x))
    }
}

fn resolve_shift_reduce(grm: &Grammar, mut e: OccupiedEntry<(StIdx, Symbol), Action>, term_k: TIdx,
                        prod_k: PIdx, state_j: StIdx) -> u64 {
    let mut shift_reduce = 0;
    let term_k_prec = grm.term_precedence(term_k).unwrap();
    let prod_k_prec = grm.prod_precedence(prod_k).unwrap();
    match (term_k_prec, prod_k_prec) {
        (_, None) | (None, _) => {
            // If the terminal and production don't both have precedences, we use Yacc's default
            // resolution, which is in favour of the shift.
            e.insert(Action::Shift(state_j));
            shift_reduce += 1;
        },
        (Some(term_prec), Some(prod_prec)) => {
            if term_prec.level == prod_prec.level {
                // Both terminal and production have the same level precedence, so we need to look
                // at the precedence kind.
                match (term_prec.kind, prod_prec.kind) {
                    (AssocKind::Left, AssocKind::Left) => {
                        // Left associativity is resolved in favour of the reduce (i.e. leave
                        // as-is).
                    },
                    (AssocKind::Right, AssocKind::Right) => {
                        // Right associativity is resolved in favour of the shift.
                        e.insert(Action::Shift(state_j));
                    },
                    (AssocKind::Nonassoc, AssocKind::Nonassoc) => {
                        // Nonassociativity leads to a run-time parsing error, so we need to remove
                        // the action entirely.
                        e.remove();
                    },
                    (_, _) => {
                        panic!("Not supported.");
                    }
                }
            } else if term_prec.level > prod_prec.level {
                // The terminal has higher level precedence, so resolve in favour of shift.
                e.insert(Action::Shift(state_j));
            }
            // If term_lev < prod_lev, then the production has higher level precedence and we keep
            // the reduce as-is.
        }
    }
    shift_reduce
}

#[cfg(test)]
mod test {
    use StIdx;
    use super::{Action, StateTable};
    use stategraph::StateGraph;
    use grammar::{Grammar, PIdx, Symbol, TIdx};
    use yacc_parser::parse_yacc;

    #[test]
    fn test_statetable() {
        // Taken from p19 of www.cs.umd.edu/~mvz/cmsc430-s07/M10lr.pdf
        let grm = Grammar::new(&parse_yacc(&"
            %start Expr
            %%
            Expr : Term '-' Expr | Term;
            Term : Factor '*' Term | Factor;
            Factor : 'id';
          ".to_string()).unwrap());
        let sg = StateGraph::new(&grm);
        assert_eq!(sg.states.len(), 9);

        let s0 = StIdx(0);
        let s1 = sg.edges[usize::from(s0)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s2 = sg.edges[usize::from(s0)][&Symbol::Nonterminal(grm.nonterminal_off("Term"))];
        let s3 = sg.edges[usize::from(s0)][&Symbol::Nonterminal(grm.nonterminal_off("Factor"))];
        let s4 = sg.edges[usize::from(s0)][&Symbol::Terminal(grm.terminal_off("id"))];
        let s5 = sg.edges[usize::from(s2)][&Symbol::Terminal(grm.terminal_off("-"))];
        let s6 = sg.edges[usize::from(s3)][&Symbol::Terminal(grm.terminal_off("*"))];
        let s7 = sg.edges[usize::from(s5)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s8 = sg.edges[usize::from(s6)][&Symbol::Nonterminal(grm.nonterminal_off("Term"))];

        let st = StateTable::new(&grm, &sg);

        // Actions
        assert_eq!(st.actions.len(), 15);
        let assert_reduce = |state_i: StIdx, term_i: TIdx, rule: &str, prod_off: usize| {
            let prod_i = grm.nonterm_to_prods(grm.nonterminal_off(rule)).unwrap()[prod_off];
            assert_eq!(st.action(state_i, Symbol::Terminal(term_i)).unwrap(), Action::Reduce(PIdx::from(prod_i)));
        };

        assert_eq!(st.action(s0, Symbol::Terminal(grm.terminal_off("id"))).unwrap(), Action::Shift(s4));
        assert_eq!(st.action(s1, Symbol::Terminal(grm.end_term)).unwrap(), Action::Accept);
        assert_eq!(st.action(s2, Symbol::Terminal(grm.terminal_off("-"))).unwrap(), Action::Shift(s5));
        assert_reduce(s2, grm.end_term, "Expr", 1);
        assert_reduce(s3, grm.terminal_off("-"), "Term", 1);
        assert_eq!(st.action(s3, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Shift(s6));
        assert_reduce(s3, grm.end_term, "Term", 1);
        assert_reduce(s4, grm.terminal_off("-"), "Factor", 0);
        assert_reduce(s4, grm.terminal_off("*"), "Factor", 0);
        assert_reduce(s4, grm.end_term, "Factor", 0);
        assert_eq!(st.action(s5, Symbol::Terminal(grm.terminal_off("id"))).unwrap(), Action::Shift(s4));
        assert_eq!(st.action(s6, Symbol::Terminal(grm.terminal_off("id"))).unwrap(), Action::Shift(s4));
        assert_reduce(s7, grm.end_term, "Expr", 0);
        assert_reduce(s8, grm.terminal_off("-"), "Term", 0);
        assert_reduce(s8, grm.end_term, "Term", 0);

        // Gotos
        assert_eq!(st.gotos.len(), 8);
        assert_eq!(st.goto(s0, grm.nonterminal_off("Expr")).unwrap(), s1);
        assert_eq!(st.goto(s0, grm.nonterminal_off("Term")).unwrap(), s2);
        assert_eq!(st.goto(s0, grm.nonterminal_off("Factor")).unwrap(), s3);
        assert_eq!(st.goto(s5, grm.nonterminal_off("Expr")).unwrap(), s7);
        assert_eq!(st.goto(s5, grm.nonterminal_off("Term")).unwrap(), s2);
        assert_eq!(st.goto(s5, grm.nonterminal_off("Factor")).unwrap(), s3);
        assert_eq!(st.goto(s6, grm.nonterminal_off("Term")).unwrap(), s8);
        assert_eq!(st.goto(s6, grm.nonterminal_off("Factor")).unwrap(), s3);
    }

    #[test]
    fn test_default_reduce_reduce() {
        let grm = Grammar::new(&parse_yacc(&"
            %start A
            %%
            A : B 'x' | C 'x' 'x';
            B : 'a';
            C : 'a';
          ".to_string()).unwrap());
        let sg = StateGraph::new(&grm);
        let st = StateTable::new(&grm, &sg);
        assert_eq!(st.actions.len(), 8);

        // We only extract the states necessary to test those rules affected by the reduce/reduce.
        let s0 = StIdx(0);
        let s4 = sg.edges[usize::from(s0)][&Symbol::Terminal(grm.terminal_off("a"))];

        assert_eq!(st.action(s4, Symbol::Terminal(grm.terminal_off("x"))).unwrap(), Action::Reduce(PIdx::from(3)));
    }

    #[test]
    fn test_default_shift_reduce() {
        let grm = Grammar::new(&parse_yacc(&"
            %start Expr
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | 'id' ;
          ".to_string()).unwrap());
        let sg = StateGraph::new(&grm);
        let st = StateTable::new(&grm, &sg);
        assert_eq!(st.actions.len(), 15);

        let s0 = StIdx(0);
        let s1 = sg.edges[usize::from(s0)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s3 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("+"))];
        let s4 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("*"))];
        let s5 = sg.edges[usize::from(s4)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s6 = sg.edges[usize::from(s3)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];

        assert_eq!(st.action(s5, Symbol::Terminal(grm.terminal_off("+"))).unwrap(), Action::Shift(s3));
        assert_eq!(st.action(s5, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Shift(s4));

        assert_eq!(st.action(s6, Symbol::Terminal(grm.terminal_off("+"))).unwrap(), Action::Shift(s3));
        assert_eq!(st.action(s6, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Shift(s4));
    }

    #[test]
    fn test_left_associativity() {
        let grm = Grammar::new(&parse_yacc(&"
            %start Expr
            %left '+'
            %left '*'
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | 'id' ;
          ".to_string()).unwrap());
        let sg = StateGraph::new(&grm);
        let st = StateTable::new(&grm, &sg);
        assert_eq!(st.actions.len(), 15);

        let s0 = StIdx(0);
        let s1 = sg.edges[usize::from(s0)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s3 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("+"))];
        let s4 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("*"))];
        let s5 = sg.edges[usize::from(s4)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s6 = sg.edges[usize::from(s3)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];

        assert_eq!(st.action(s5, Symbol::Terminal(grm.terminal_off("+"))).unwrap(), Action::Reduce(PIdx::from(2)));
        assert_eq!(st.action(s5, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Reduce(PIdx::from(2)));
        assert_eq!(st.action(s5, Symbol::Terminal(grm.end_term)).unwrap(), Action::Reduce(PIdx::from(2)));

        assert_eq!(st.action(s6, Symbol::Terminal(grm.terminal_off("+"))).unwrap(), Action::Reduce(PIdx::from(1)));
        assert_eq!(st.action(s6, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Shift(s4));
        assert_eq!(st.action(s6, Symbol::Terminal(grm.end_term)).unwrap(), Action::Reduce(PIdx::from(1)));
    }

    #[test]
    fn test_left_right_associativity() {
        let grm = Grammar::new(&parse_yacc(&"
            %start Expr
            %right '='
            %left '+'
            %left '*'
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | Expr '=' Expr
                 | 'id' ;
          ".to_string()).unwrap());
        let sg = StateGraph::new(&grm);
        let st = StateTable::new(&grm, &sg);
        assert_eq!(st.actions.len(), 24);

        let s0 = StIdx(0);
        let s1 = sg.edges[usize::from(s0)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s3 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("+"))];
        let s4 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("*"))];
        let s5 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("="))];
        let s6 = sg.edges[usize::from(s5)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s7 = sg.edges[usize::from(s4)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s8 = sg.edges[usize::from(s3)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];

        assert_eq!(st.action(s6, Symbol::Terminal(grm.terminal_off("+"))).unwrap(), Action::Shift(s3));
        assert_eq!(st.action(s6, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Shift(s4));
        assert_eq!(st.action(s6, Symbol::Terminal(grm.terminal_off("="))).unwrap(), Action::Shift(s5));
        assert_eq!(st.action(s6, Symbol::Terminal(grm.end_term)).unwrap(), Action::Reduce(PIdx::from(3)));

        assert_eq!(st.action(s7, Symbol::Terminal(grm.terminal_off("+"))).unwrap(), Action::Reduce(PIdx::from(2)));
        assert_eq!(st.action(s7, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Reduce(PIdx::from(2)));
        assert_eq!(st.action(s7, Symbol::Terminal(grm.terminal_off("="))).unwrap(), Action::Reduce(PIdx::from(2)));
        assert_eq!(st.action(s7, Symbol::Terminal(grm.end_term)).unwrap(), Action::Reduce(PIdx::from(2)));

        assert_eq!(st.action(s8, Symbol::Terminal(grm.terminal_off("+"))).unwrap(), Action::Reduce(PIdx::from(1)));
        assert_eq!(st.action(s8, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Shift(s4));
        assert_eq!(st.action(s8, Symbol::Terminal(grm.terminal_off("="))).unwrap(), Action::Reduce(PIdx::from(1)));
        assert_eq!(st.action(s8, Symbol::Terminal(grm.end_term)).unwrap(), Action::Reduce(PIdx::from(1)));
    }

    #[test]
    fn test_left_right_nonassoc_associativity() {
        let grm = Grammar::new(&parse_yacc(&"
            %start Expr
            %right '='
            %left '+'
            %left '*'
            %nonassoc '~'
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | Expr '=' Expr
                 | Expr '~' Expr
                 | 'id' ;
          ".to_string()).unwrap());
        let sg = StateGraph::new(&grm);
        let st = StateTable::new(&grm, &sg);
        assert_eq!(st.actions.len(), 34);

        let s0 = StIdx(0);
        let s1 = sg.edges[usize::from(s0)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s3 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("+"))];
        let s4 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("*"))];
        let s5 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("="))];
        let s6 = sg.edges[usize::from(s1)][&Symbol::Terminal(grm.terminal_off("~"))];
        let s7 = sg.edges[usize::from(s6)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s8 = sg.edges[usize::from(s5)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s9 = sg.edges[usize::from(s4)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s10 = sg.edges[usize::from(s3)][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];

        assert_eq!(st.action(s7, Symbol::Terminal(grm.terminal_off("+"))).unwrap(), Action::Reduce(PIdx::from(4)));
        assert_eq!(st.action(s7, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Reduce(PIdx::from(4)));
        assert_eq!(st.action(s7, Symbol::Terminal(grm.terminal_off("="))).unwrap(), Action::Reduce(PIdx::from(4)));
        assert_eq!(st.action(s7, Symbol::Terminal(grm.end_term)).unwrap(), Action::Reduce(PIdx::from(4)));

        assert_eq!(st.action(s8, Symbol::Terminal(grm.terminal_off("+"))).unwrap(), Action::Shift(s3));
        assert_eq!(st.action(s8, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Shift(s4));
        assert_eq!(st.action(s8, Symbol::Terminal(grm.terminal_off("="))).unwrap(), Action::Shift(s5));
        assert_eq!(st.action(s8, Symbol::Terminal(grm.terminal_off("~"))).unwrap(), Action::Shift(s6));
        assert_eq!(st.action(s8, Symbol::Terminal(grm.end_term)).unwrap(), Action::Reduce(PIdx::from(3)));

        assert_eq!(st.action(s9, Symbol::Terminal(grm.terminal_off("+"))).unwrap(), Action::Reduce(PIdx::from(2)));
        assert_eq!(st.action(s9, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Reduce(PIdx::from(2)));
        assert_eq!(st.action(s9, Symbol::Terminal(grm.terminal_off("="))).unwrap(), Action::Reduce(PIdx::from(2)));
        assert_eq!(st.action(s9, Symbol::Terminal(grm.terminal_off("~"))).unwrap(), Action::Shift(s6));
        assert_eq!(st.action(s9, Symbol::Terminal(grm.end_term)).unwrap(), Action::Reduce(PIdx::from(2)));

        assert_eq!(st.action(s10, Symbol::Terminal(grm.terminal_off("+"))).unwrap(), Action::Reduce(PIdx::from(1)));
        assert_eq!(st.action(s10, Symbol::Terminal(grm.terminal_off("*"))).unwrap(), Action::Shift(s4));
        assert_eq!(st.action(s10, Symbol::Terminal(grm.terminal_off("="))).unwrap(), Action::Reduce(PIdx::from(1)));
        assert_eq!(st.action(s10, Symbol::Terminal(grm.terminal_off("~"))).unwrap(), Action::Shift(s6));
        assert_eq!(st.action(s10, Symbol::Terminal(grm.end_term)).unwrap(), Action::Reduce(PIdx::from(1)));
    }
}
