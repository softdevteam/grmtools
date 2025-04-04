use std::{collections::hash_map::HashMap, fmt::Write, hash::Hash};

use cfgrammar::{yacc::YaccGrammar, Symbol, TIdx};
use num_traits::{AsPrimitive, PrimInt, Unsigned};

use crate::{itemset::Itemset, StIdx};

#[derive(Debug)]
pub struct StateGraph<StorageT: Eq + Hash> {
    /// A vector of `(core_states, closed_states)` tuples.
    states: Vec<(Itemset<StorageT>, Itemset<StorageT>)>,
    start_state: StIdx<StorageT>,
    /// For each state in `states`, edges is a hashmap from symbols to state offsets.
    edges: Vec<HashMap<Symbol<StorageT>, StIdx<StorageT>>>,
}

impl<StorageT: 'static + Hash + PrimInt + Unsigned> StateGraph<StorageT>
where
    usize: AsPrimitive<StorageT>,
{
    pub(crate) fn new(
        states: Vec<(Itemset<StorageT>, Itemset<StorageT>)>,
        start_state: StIdx<StorageT>,
        edges: Vec<HashMap<Symbol<StorageT>, StIdx<StorageT>>>,
    ) -> Self {
        assert!(states.len() < num_traits::cast(StorageT::max_value()).unwrap());
        StateGraph {
            states,
            start_state,
            edges,
        }
    }

    /// Return this state graph's start state.
    pub fn start_state(&self) -> StIdx<StorageT> {
        self.start_state
    }

    /// Return an iterator which produces (in order from `StorageT::zero()..self.all_states_len()`)
    /// all this grammar's valid `StIdx`s.
    pub fn iter_stidxs(&self) -> Box<dyn Iterator<Item = StIdx<StorageT>>> {
        // We can use as safely, because we know that we're only generating integers from
        // 0..self.states.len() which we've already checked fits within StIdxStorageT.
        Box::new((0..self.states.len()).map(|x| StIdx(x.as_())))
    }

    /// Return the itemset for closed state `stidx`. Panics if `stidx` doesn't exist.
    pub fn closed_state(&self, stidx: StIdx<StorageT>) -> &Itemset<StorageT> {
        let (_, closed_state) = &self.states[usize::from(stidx)];
        closed_state
    }

    /// Return an iterator over all closed states in this `StateGraph`.
    pub fn iter_closed_states<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = &'a Itemset<StorageT>> + 'a> {
        Box::new(self.states.iter().map(|(_, x)| x))
    }

    /// Return the itemset for core state `stidx` or `None` if it doesn't exist.
    pub fn core_state(&self, stidx: StIdx<StorageT>) -> &Itemset<StorageT> {
        let (core_states, _) = &self.states[usize::from(stidx)];
        core_states
    }

    /// Return an iterator over all core states in this `StateGraph`.
    pub fn iter_core_states<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Itemset<StorageT>> + 'a> {
        Box::new(self.states.iter().map(|(x, _)| x))
    }

    /// How many states does this `StateGraph` contain? NB: By definition the `StateGraph` contains
    /// the same number of core and closed states.
    pub fn all_states_len(&self) -> StIdx<StorageT> {
        // We checked in the constructor that self.states.len() can fit into StIdxStorageT
        StIdx(self.states.len().as_())
    }

    /// Return the state pointed to by `sym` from `stidx` or `None` otherwise.
    pub fn edge(&self, stidx: StIdx<StorageT>, sym: Symbol<StorageT>) -> Option<StIdx<StorageT>> {
        self.edges
            .get(usize::from(stidx))
            .and_then(|x| x.get(&sym))
            .cloned()
    }

    /// Return the edges for state `stidx`. Panics if `stidx` doesn't exist.
    pub fn edges(&self, stidx: StIdx<StorageT>) -> &HashMap<Symbol<StorageT>, StIdx<StorageT>> {
        &self.edges[usize::from(stidx)]
    }

    /// How many edges does this `StateGraph` contain?
    pub fn all_edges_len(&self) -> usize {
        self.edges.iter().fold(0, |a, x| a + x.len())
    }

    /// Pretty print this stategraph as a `String`. If `core_states` is set to true, only the core
    /// states are pretty printed; if set to false, all states (including non-core states) are
    /// pretty printed.
    pub fn pp(&self, grm: &YaccGrammar<StorageT>, core_states: bool) -> String {
        fn num_digits<StorageT: 'static + Hash + PrimInt + Unsigned>(i: StIdx<StorageT>) -> usize
        where
            usize: AsPrimitive<StorageT>,
        {
            if usize::from(i) == 0 {
                1
            } else {
                ((usize::from(i) as f64).log10() as usize) + 1
            }
        }

        fn fmt_sym<StorageT: 'static + PrimInt + Unsigned>(
            grm: &YaccGrammar<StorageT>,
            sym: Symbol<StorageT>,
        ) -> String
        where
            usize: AsPrimitive<StorageT>,
        {
            match sym {
                Symbol::Rule(ridx) => grm.rule_name_str(ridx).to_string(),
                Symbol::Token(tidx) => format!("'{}'", grm.token_name(tidx).unwrap_or("")),
            }
        }

        let mut o = String::new();
        for (stidx, (core_st, closed_st)) in self.iter_stidxs().zip(self.states.iter()) {
            if stidx != self.start_state {
                o.push('\n');
            }
            {
                let padding = num_digits(self.all_states_len()) - num_digits(stidx);
                write!(o, "{}:{}", usize::from(stidx), " ".repeat(padding)).ok();
            }

            let st = if core_states { core_st } else { closed_st };
            for (i, (&(pidx, sidx), ctx)) in st.items.iter().enumerate() {
                let padding = if i == 0 {
                    0
                } else {
                    o.push_str("\n "); // Extra space to compensate for ":" printed above
                    num_digits(self.all_states_len())
                };
                write!(
                    o,
                    "{} [{} ->",
                    " ".repeat(padding),
                    grm.rule_name_str(grm.prod_to_rule(pidx))
                )
                .ok();
                for (i_sidx, i_ssym) in grm.prod(pidx).iter().enumerate() {
                    if i_sidx == usize::from(sidx) {
                        o.push_str(" .");
                    }
                    write!(o, " {}", fmt_sym(grm, *i_ssym)).ok();
                }
                if usize::from(sidx) == grm.prod(pidx).len() {
                    o.push_str(" .");
                }
                o.push_str(", {");
                let mut seen_b = false;
                for bidx in ctx.iter_set_bits(..) {
                    if seen_b {
                        o.push_str(", ");
                    } else {
                        seen_b = true;
                    }
                    // Since ctx is exactly tokens_len bits long, the call to as_ is safe.
                    let tidx = TIdx(bidx.as_());
                    if tidx == grm.eof_token_idx() {
                        o.push_str("'$'");
                    } else {
                        write!(o, "'{}'", grm.token_name(tidx).unwrap()).ok();
                    }
                }
                o.push_str("}]");
            }
            let mut edges = self.edges(stidx).iter().collect::<Vec<_>>();
            edges.sort_by(|(_, x), (_, y)| x.cmp(y));
            for (esym, e_stidx) in edges {
                write!(
                    o,
                    "\n{}{} -> {}",
                    " ".repeat(num_digits(self.all_states_len()) + 2),
                    fmt_sym(grm, *esym),
                    usize::from(*e_stidx)
                )
                .ok();
            }
        }
        o
    }

    /// Return a pretty printed version of the core states, and all edges.
    pub fn pp_core_states(&self, grm: &YaccGrammar<StorageT>) -> String {
        self.pp(grm, true)
    }

    /// Return a pretty printed version of the closed states, and all edges.
    pub fn pp_closed_states(&self, grm: &YaccGrammar<StorageT>) -> String {
        self.pp(grm, false)
    }
}

#[cfg(test)]
use cfgrammar::SIdx;

#[cfg(test)]
pub(crate) fn state_exists<StorageT: 'static + Hash + PrimInt + Unsigned>(
    grm: &YaccGrammar<StorageT>,
    is: &Itemset<StorageT>,
    nt: &str,
    prod_off: usize,
    dot: SIdx<StorageT>,
    la: Vec<&str>,
) where
    usize: AsPrimitive<StorageT>,
{
    let ab_prod_off = grm.rule_to_prods(grm.rule_idx(nt).unwrap())[prod_off];
    let ctx = &is.items[&(ab_prod_off, dot)];
    for tidx in grm.iter_tidxs() {
        let bit = ctx[usize::from(tidx)];
        let mut found = false;
        for t in la.iter() {
            let off = if t == &"$" {
                grm.eof_token_idx()
            } else {
                grm.token_idx(t).unwrap()
            };
            if off == tidx {
                if !bit {
                    panic!("bit for token {}, dot {} is not set in production {} of {} when it should be",
                           t, usize::from(dot), prod_off, nt);
                }
                found = true;
                break;
            }
        }
        if !found && bit {
            panic!(
                "bit for token {}, dot {} is set in production {} of {} when it shouldn't be",
                grm.token_name(tidx).unwrap(),
                usize::from(dot),
                prod_off,
                nt
            );
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{pager::pager_stategraph, StIdx};
    use cfgrammar::{
        header::Header,
        markmap::MergeBehavior,
        yacc::{YaccGrammar, YaccKind, YaccOriginalActionKind},
        Span, Symbol,
    };

    #[test]
    #[rustfmt::skip]
    fn test_statetable_core() {
        // Taken from p13 of https://link.springer.com/article/10.1007/s00236-010-0115-6
        let mut header = Header::new();
        header.contents_mut().set_merge_behavior(&"yacckind".to_string(), MergeBehavior::Ours);
        header.contents_mut().mark_required(&"yacckind".to_string());
        header.contents_mut().insert("yacckind".into(), (Span::new(0, 0), YaccKind::Original(YaccOriginalActionKind::GenericParseTree).into()));
        let grm = YaccGrammar::new(
            header,
            "
            %start A
            %%
            A: 'OPEN_BRACKET' A 'CLOSE_BRACKET'
             | 'a'
             | 'b';
          "
        ).unwrap();
        let sg = pager_stategraph(&grm);
        assert_eq!(sg.all_states_len(), StIdx(7));
        assert_eq!(sg.states.iter().fold(0, |a, (x, _)| a + x.items.len()), 7);
        assert_eq!(sg.all_edges_len(), 9);

        // This follows the (not particularly logical) ordering of state numbers in the paper.
        let s0 = StIdx(0);
        sg.edge(s0, Symbol::Rule(grm.rule_idx("A").unwrap())).unwrap(); // s1
        let s2 = sg.edge(s0, Symbol::Token(grm.token_idx("a").unwrap())).unwrap();
        let s3 = sg.edge(s0, Symbol::Token(grm.token_idx("b").unwrap())).unwrap();
        let s5 = sg.edge(s0, Symbol::Token(grm.token_idx("OPEN_BRACKET").unwrap())).unwrap();
        assert_eq!(s2, sg.edge(s5, Symbol::Token(grm.token_idx("a").unwrap())).unwrap());
        assert_eq!(s3, sg.edge(s5, Symbol::Token(grm.token_idx("b").unwrap())).unwrap());
        assert_eq!(s5, sg.edge(s5, Symbol::Token(grm.token_idx("OPEN_BRACKET").unwrap())).unwrap());
        let s4 = sg.edge(s5, Symbol::Rule(grm.rule_idx("A").unwrap())).unwrap();
        sg.edge(s4, Symbol::Token(grm.token_idx("CLOSE_BRACKET").unwrap())).unwrap(); // s6
    }
}
