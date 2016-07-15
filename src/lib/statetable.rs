use std::collections::hash_map::{Entry, HashMap, OccupiedEntry};

use grammar::{AssocKind, Grammar, PIdx, Symbol, TIdx};
use stategraph::StateGraph;

/// A representation of a StateTable for a grammar. `actions` and `gotos` are split into two
/// separate hashmaps, rather than a single table, due to the different types of their values.
#[derive(Debug)]
pub struct StateTable {
    pub actions      : HashMap<(usize, Symbol), Action>,
    pub gotos        : HashMap<(usize, PIdx), usize>,
    /// The number of reduce/reduce errors encountered.
    pub reduce_reduce: u64,
    /// The number of shift/reduce errors encountered.
    pub shift_reduce : u64
}

#[derive(Debug, PartialEq)]
pub enum Action {
    /// Shift to state X in the statetable.
    Shift(usize),
    /// Reduce production X in the grammar.
    Reduce(usize),
    /// Accept this input.
    Accept
}

impl StateTable {
    pub fn new(grm: &Grammar, sg: &StateGraph) -> StateTable {
        let mut actions: HashMap<(usize, Symbol), Action> = HashMap::new();
        let mut gotos  : HashMap<(usize, PIdx), usize>    = HashMap::new();
        let mut reduce_reduce = 0; // How many automatically resolved reduce/reduces were made?
        let mut shift_reduce  = 0; // How many automatically resolved shift/reduces were made?

        for (state_i, state) in sg.states.iter().enumerate() {
            // Populate reduce and accepts
            for (&(prod_i, dot), ctx) in state.items.iter() {
                if dot < grm.prods[prod_i].len() {
                    continue;
                }
                for (term_i, _) in ctx.iter().enumerate().filter(|&(_, x)| x) {
                    let sym = Symbol::Terminal(term_i);
                    match actions.entry((state_i, sym)) {
                        Entry::Occupied(mut e) => {
                            match e.get_mut() {
                                &mut Action::Reduce(prod_j) => {
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
                            if prod_i == grm.start_prod && term_i == grm.end_term {
                                e.insert(Action::Accept);
                            }
                            else {
                                e.insert(Action::Reduce(prod_i));
                            }
                        }
                    }
                }
            }

            for (&sym, state_j) in sg.edges[state_i].iter() {
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
                                match e.get_mut() {
                                    &mut Action::Shift(x) => assert_eq!(*state_j, x),
                                    &mut Action::Reduce(prod_k) => {
                                        shift_reduce += resolve_shift_reduce(&grm, e, term_k,
                                                                             prod_k, *state_j);
                                    }
                                    &mut Action::Accept => panic!("Internal error")
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

}

fn resolve_shift_reduce(grm: &Grammar, mut e: OccupiedEntry<(usize, Symbol), Action>, term_k: TIdx,
                        prod_k: PIdx, state_j: usize) -> u64 {
    let mut shift_reduce = 0;
    let term_k_prec = grm.terminal_precs[term_k];
    let prod_k_prec = grm.prod_precs[prod_k];
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
    use super::{Action, StateTable};
    use stategraph::StateGraph;
    use grammar::{ast_to_grammar, Symbol, TIdx};
    use yacc::parse_yacc;

    #[test]
    fn test_statetable() {
        // Taken from p19 of www.cs.umd.edu/~mvz/cmsc430-s07/M10lr.pdf
        let grm = ast_to_grammar(&parse_yacc(&"
            %start Expr
            %%
            Expr : Term '-' Expr | Term;
            Term : Factor '*' Term | Factor;
            Factor : 'id';
          ".to_string()).unwrap());
        let sg = StateGraph::new(&grm);
        assert_eq!(sg.states.len(), 9);

        let s0 = 0;
        let s1 = sg.edges[s0][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s2 = sg.edges[s0][&Symbol::Nonterminal(grm.nonterminal_off("Term"))];
        let s3 = sg.edges[s0][&Symbol::Nonterminal(grm.nonterminal_off("Factor"))];
        let s4 = sg.edges[s0][&Symbol::Terminal(grm.terminal_off("id"))];
        let s5 = sg.edges[s2][&Symbol::Terminal(grm.terminal_off("-"))];
        let s6 = sg.edges[s3][&Symbol::Terminal(grm.terminal_off("*"))];
        let s7 = sg.edges[s5][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s8 = sg.edges[s6][&Symbol::Nonterminal(grm.nonterminal_off("Term"))];

        let st = StateTable::new(&grm, &sg);

        // Actions
        assert_eq!(st.actions.len(), 15);
        let assert_reduce = |state_i: usize, term_i: TIdx, rule: &str, prod_off: usize| {
            let prod_i = grm.rules_prods[grm.nonterminal_off(rule)][prod_off];
            assert_eq!(st.actions[&(state_i, Symbol::Terminal(term_i))], Action::Reduce(prod_i));
        };

        assert_eq!(st.actions[&(s0, Symbol::Terminal(grm.terminal_off("id")))], Action::Shift(s4));
        assert_eq!(st.actions[&(s1, Symbol::Terminal(grm.end_term))], Action::Accept);
        assert_eq!(st.actions[&(s2, Symbol::Terminal(grm.terminal_off("-")))], Action::Shift(s5));
        assert_reduce(s2, grm.end_term, "Expr", 1);
        assert_reduce(s3, grm.terminal_off("-"), "Term", 1);
        assert_eq!(st.actions[&(s3, Symbol::Terminal(grm.terminal_off("*")))], Action::Shift(s6));
        assert_reduce(s3, grm.end_term, "Term", 1);
        assert_reduce(s4, grm.terminal_off("-"), "Factor", 0);
        assert_reduce(s4, grm.terminal_off("*"), "Factor", 0);
        assert_reduce(s4, grm.end_term, "Factor", 0);
        assert_eq!(st.actions[&(s5, Symbol::Terminal(grm.terminal_off("id")))], Action::Shift(s4));
        assert_eq!(st.actions[&(s6, Symbol::Terminal(grm.terminal_off("id")))], Action::Shift(s4));
        assert_reduce(s7, grm.end_term, "Expr", 0);
        assert_reduce(s8, grm.terminal_off("-"), "Term", 0);
        assert_reduce(s8, grm.end_term, "Term", 0);

        // Gotos
        assert_eq!(st.gotos.len(), 8);
        assert_eq!(st.gotos[&(s0, grm.nonterminal_off("Expr"))], s1);
        assert_eq!(st.gotos[&(s0, grm.nonterminal_off("Term"))], s2);
        assert_eq!(st.gotos[&(s0, grm.nonterminal_off("Factor"))], s3);
        assert_eq!(st.gotos[&(s5, grm.nonterminal_off("Expr"))], s7);
        assert_eq!(st.gotos[&(s5, grm.nonterminal_off("Term"))], s2);
        assert_eq!(st.gotos[&(s5, grm.nonterminal_off("Factor"))], s3);
        assert_eq!(st.gotos[&(s6, grm.nonterminal_off("Term"))], s8);
        assert_eq!(st.gotos[&(s6, grm.nonterminal_off("Factor"))], s3);
    }

    #[test]
    fn test_default_reduce_reduce() {
        let grm = ast_to_grammar(&parse_yacc(&"
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
        let s0 = 0;
        let s4 = sg.edges[s0][&Symbol::Terminal(grm.terminal_off("a"))];

        assert_eq!(st.actions[&(s4, Symbol::Terminal(grm.terminal_off("x")))], Action::Reduce(3));
    }

    #[test]
    fn test_default_shift_reduce() {
        let grm = ast_to_grammar(&parse_yacc(&"
            %start Expr
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | 'id' ;
          ".to_string()).unwrap());
        let sg = StateGraph::new(&grm);
        let st = StateTable::new(&grm, &sg);
        assert_eq!(st.actions.len(), 15);

        let s0 = 0;
        let s1 = sg.edges[s0][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s3 = sg.edges[s1][&Symbol::Terminal(grm.terminal_off("+"))];
        let s4 = sg.edges[s1][&Symbol::Terminal(grm.terminal_off("*"))];
        let s5 = sg.edges[s4][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s6 = sg.edges[s3][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];

        assert_eq!(st.actions[&(s5, Symbol::Terminal(grm.terminal_off("+")))], Action::Shift(s3));
        assert_eq!(st.actions[&(s5, Symbol::Terminal(grm.terminal_off("*")))], Action::Shift(s4));

        assert_eq!(st.actions[&(s6, Symbol::Terminal(grm.terminal_off("+")))], Action::Shift(s3));
        assert_eq!(st.actions[&(s6, Symbol::Terminal(grm.terminal_off("*")))], Action::Shift(s4));
    }

    #[test]
    fn test_left_associativity() {
        let grm = ast_to_grammar(&parse_yacc(&"
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

        let s0 = 0;
        let s1 = sg.edges[s0][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s3 = sg.edges[s1][&Symbol::Terminal(grm.terminal_off("+"))];
        let s4 = sg.edges[s1][&Symbol::Terminal(grm.terminal_off("*"))];
        let s5 = sg.edges[s4][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s6 = sg.edges[s3][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];

        assert_eq!(st.actions[&(s5, Symbol::Terminal(grm.terminal_off("+")))], Action::Reduce(2));
        assert_eq!(st.actions[&(s5, Symbol::Terminal(grm.terminal_off("*")))], Action::Reduce(2));
        assert_eq!(st.actions[&(s5, Symbol::Terminal(grm.end_term))], Action::Reduce(2));

        assert_eq!(st.actions[&(s6, Symbol::Terminal(grm.terminal_off("+")))], Action::Reduce(1));
        assert_eq!(st.actions[&(s6, Symbol::Terminal(grm.terminal_off("*")))], Action::Shift(s4));
        assert_eq!(st.actions[&(s6, Symbol::Terminal(grm.end_term))], Action::Reduce(1));
    }

    #[test]
    fn test_left_right_associativity() {
        let grm = ast_to_grammar(&parse_yacc(&"
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

        let s0 = 0;
        let s1 = sg.edges[s0][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s3 = sg.edges[s1][&Symbol::Terminal(grm.terminal_off("+"))];
        let s4 = sg.edges[s1][&Symbol::Terminal(grm.terminal_off("*"))];
        let s5 = sg.edges[s1][&Symbol::Terminal(grm.terminal_off("="))];
        let s6 = sg.edges[s5][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s7 = sg.edges[s4][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s8 = sg.edges[s3][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];

        assert_eq!(st.actions[&(s6, Symbol::Terminal(grm.terminal_off("+")))], Action::Shift(s3));
        assert_eq!(st.actions[&(s6, Symbol::Terminal(grm.terminal_off("*")))], Action::Shift(s4));
        assert_eq!(st.actions[&(s6, Symbol::Terminal(grm.terminal_off("=")))], Action::Shift(s5));
        assert_eq!(st.actions[&(s6, Symbol::Terminal(grm.end_term))], Action::Reduce(3));

        assert_eq!(st.actions[&(s7, Symbol::Terminal(grm.terminal_off("+")))], Action::Reduce(2));
        assert_eq!(st.actions[&(s7, Symbol::Terminal(grm.terminal_off("*")))], Action::Reduce(2));
        assert_eq!(st.actions[&(s7, Symbol::Terminal(grm.terminal_off("=")))], Action::Reduce(2));
        assert_eq!(st.actions[&(s7, Symbol::Terminal(grm.end_term))], Action::Reduce(2));

        assert_eq!(st.actions[&(s8, Symbol::Terminal(grm.terminal_off("+")))], Action::Reduce(1));
        assert_eq!(st.actions[&(s8, Symbol::Terminal(grm.terminal_off("*")))], Action::Shift(s4));
        assert_eq!(st.actions[&(s8, Symbol::Terminal(grm.terminal_off("=")))], Action::Reduce(1));
        assert_eq!(st.actions[&(s8, Symbol::Terminal(grm.end_term))], Action::Reduce(1));
    }

    #[test]
    fn test_left_right_nonassoc_associativity() {
        let grm = ast_to_grammar(&parse_yacc(&"
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

        let s0 = 0;
        let s1 = sg.edges[s0][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s3 = sg.edges[s1][&Symbol::Terminal(grm.terminal_off("+"))];
        let s4 = sg.edges[s1][&Symbol::Terminal(grm.terminal_off("*"))];
        let s5 = sg.edges[s1][&Symbol::Terminal(grm.terminal_off("="))];
        let s6 = sg.edges[s1][&Symbol::Terminal(grm.terminal_off("~"))];
        let s7 = sg.edges[s6][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s8 = sg.edges[s5][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s9 = sg.edges[s4][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];
        let s10 = sg.edges[s3][&Symbol::Nonterminal(grm.nonterminal_off("Expr"))];

        assert_eq!(st.actions[&(s7, Symbol::Terminal(grm.terminal_off("+")))], Action::Reduce(4));
        assert_eq!(st.actions[&(s7, Symbol::Terminal(grm.terminal_off("*")))], Action::Reduce(4));
        assert_eq!(st.actions[&(s7, Symbol::Terminal(grm.terminal_off("=")))], Action::Reduce(4));
        assert_eq!(st.actions[&(s7, Symbol::Terminal(grm.end_term))], Action::Reduce(4));

        assert_eq!(st.actions[&(s8, Symbol::Terminal(grm.terminal_off("+")))], Action::Shift(s3));
        assert_eq!(st.actions[&(s8, Symbol::Terminal(grm.terminal_off("*")))], Action::Shift(s4));
        assert_eq!(st.actions[&(s8, Symbol::Terminal(grm.terminal_off("=")))], Action::Shift(s5));
        assert_eq!(st.actions[&(s8, Symbol::Terminal(grm.terminal_off("~")))], Action::Shift(s6));
        assert_eq!(st.actions[&(s8, Symbol::Terminal(grm.end_term))], Action::Reduce(3));

        assert_eq!(st.actions[&(s9, Symbol::Terminal(grm.terminal_off("+")))], Action::Reduce(2));
        assert_eq!(st.actions[&(s9, Symbol::Terminal(grm.terminal_off("*")))], Action::Reduce(2));
        assert_eq!(st.actions[&(s9, Symbol::Terminal(grm.terminal_off("=")))], Action::Reduce(2));
        assert_eq!(st.actions[&(s9, Symbol::Terminal(grm.terminal_off("~")))], Action::Shift(s6));
        assert_eq!(st.actions[&(s9, Symbol::Terminal(grm.end_term))], Action::Reduce(2));

        assert_eq!(st.actions[&(s10, Symbol::Terminal(grm.terminal_off("+")))], Action::Reduce(1));
        assert_eq!(st.actions[&(s10, Symbol::Terminal(grm.terminal_off("*")))], Action::Shift(s4));
        assert_eq!(st.actions[&(s10, Symbol::Terminal(grm.terminal_off("=")))], Action::Reduce(1));
        assert_eq!(st.actions[&(s10, Symbol::Terminal(grm.terminal_off("~")))], Action::Shift(s6));
        assert_eq!(st.actions[&(s10, Symbol::Terminal(grm.end_term))], Action::Reduce(1));
    }
}
