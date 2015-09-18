use std::collections::hash_map::{Entry, HashMap};

use grammar::{AIdx, Grammar, Symbol};
use stategraph::StateGraph;

/// A representation of a StateTable for a grammar. `actions` and `gotos` are split into two
/// separate hashmaps, rather than a single table, due to the different types of their values.
#[derive(Debug)]
pub struct StateTable {
    pub actions: HashMap<(usize, Symbol), Action>,
    pub gotos  : HashMap<(usize, AIdx), usize>
}

#[derive(Debug, PartialEq)]
pub enum Action {
    /// Shift to state X in the statetable.
    Shift(usize),
    /// Reduce alternative X in the grammar.
    Reduce(usize),
    /// Accept this input.
    Accept
}

impl StateTable {
    pub fn new(grm: &Grammar, sg: &StateGraph) -> StateTable {
        let mut actions: HashMap<(usize, Symbol), Action> = HashMap::new();
        let mut gotos  : HashMap<(usize, AIdx), usize>    = HashMap::new();

        for (state_i, state) in sg.states.iter().enumerate() {
            // Populate reduce and accepts
            for (&(alt_i, dot), ctx) in state.items.iter() {
                if dot < grm.alts[alt_i].len() {
                    continue;
                }
                for (term_i, _) in ctx.iter().enumerate().filter(|&(_, x)| x) {
                    let sym = Symbol::Terminal(term_i);
                    match actions.entry((state_i, sym)) {
                        Entry::Occupied(e) => {
                            match e.get() {
                                &Action::Reduce(alt_j) => {
                                    if alt_i != alt_j {
                                        panic!("reduce/reduce error");
                                    }
                                },
                                _ => panic!("Internal error")
                            }
                        }
                        Entry::Vacant(e) => {
                            if alt_i == grm.start_alt && term_i == grm.end_term {
                                e.insert(Action::Accept);
                            }
                            else {
                                e.insert(Action::Reduce(alt_i));
                            }
                        }
                    }
                }
            }
        }

        for (&(state_i, sym), state_j) in sg.edges.iter() {
            match sym {
                Symbol::Nonterminal(nonterm_i) => {
                    // Populate gotos
                    debug_assert!(gotos.get(&(state_i, nonterm_i)).is_none());
                    gotos.insert((state_i, nonterm_i), *state_j);
                },
                Symbol::Terminal(_) => {
                    // Populate shifts
                    match actions.entry((state_i, sym)) {
                        Entry::Occupied(e) => {
                            match e.get() {
                                &Action::Shift(x) => assert_eq!(*state_j, x),
                                &Action::Reduce(_) => panic!("shift/reduce error"),
                                &Action::Accept => panic!("Internal error")
                            }
                        },
                        Entry::Vacant(e) => {
                            e.insert(Action::Shift(*state_j));
                        }
                    }
                }
            }
        }

        StateTable { actions: actions, gotos: gotos }
    }
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
        let assert_reduce = |state_i: usize, term_i: TIdx, rule: &str, alt_off: usize| {
            let alt_i = grm.rules_alts[grm.nonterminal_off(rule)][alt_off];
            assert_eq!(st.actions[&(state_i, Symbol::Terminal(term_i))], Action::Reduce(alt_i));
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
}
