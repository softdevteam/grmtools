use std::{
    cmp::Ordering,
    collections::hash_map::HashMap,
    error::Error,
    fmt::{self, Debug},
    hash::Hash,
    marker::PhantomData,
};

use cfgrammar::{
    yacc::{AssocKind, YaccGrammar},
    PIdx, RIdx, Symbol, TIdx,
};
use num_traits::{AsPrimitive, PrimInt, Unsigned};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use sparsevec::SparseVec;
use vob::{IterSetBits, Vob};

use crate::{stategraph::StateGraph, StIdx, StIdxStorageT};

#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[derive(Debug)]
pub struct Conflicts<StorageT> {
    reduce_reduce: Vec<(PIdx<StorageT>, PIdx<StorageT>, StIdx)>,
    shift_reduce: Vec<(TIdx<StorageT>, PIdx<StorageT>, StIdx)>,
}

impl<StorageT: 'static + Hash + PrimInt + Unsigned> Conflicts<StorageT>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>,
{
    /// Return an iterator over all shift/reduce conflicts.
    pub fn sr_conflicts(&self) -> impl Iterator<Item = &(TIdx<StorageT>, PIdx<StorageT>, StIdx)> {
        self.shift_reduce.iter()
    }

    /// Return an iterator over all reduce/reduce conflicts.
    pub fn rr_conflicts(&self) -> impl Iterator<Item = &(PIdx<StorageT>, PIdx<StorageT>, StIdx)> {
        self.reduce_reduce.iter()
    }

    /// How many shift/reduce conflicts are there?
    pub fn sr_len(&self) -> usize {
        self.shift_reduce.len()
    }

    /// How many reduce/reduce conflicts are there?
    pub fn rr_len(&self) -> usize {
        self.reduce_reduce.len()
    }

    /// Returns a pretty-printed version of the conflicts.
    pub fn pp(&self, grm: &YaccGrammar<StorageT>) -> String {
        let mut s = String::new();
        if self.sr_len() > 0 {
            s.push_str("Shift/Reduce conflicts:\n");
            for (tidx, pidx, stidx) in self.sr_conflicts() {
                s.push_str(&format!(
                    "   State {:?}: Shift(\"{}\") / Reduce({})\n",
                    usize::from(*stidx),
                    grm.token_name(*tidx).unwrap(),
                    grm.pp_prod(*pidx)
                ));
            }
        }

        if self.rr_len() > 0 {
            s.push_str("Reduce/Reduce conflicts:\n");
            for (pidx, r_pidx, stidx) in self.rr_conflicts() {
                s.push_str(&format!(
                    "   State {:?}: Reduce({}) / Reduce({})\n",
                    usize::from(*stidx),
                    grm.pp_prod(*pidx),
                    grm.pp_prod(*r_pidx)
                ));
            }
        }
        s
    }
}

/// The various different possible Yacc parser errors.
#[derive(Debug)]
pub enum StateTableErrorKind {
    AcceptReduceConflict,
}

/// Any error from the Yacc parser returns an instance of this struct.
#[derive(Debug)]
pub struct StateTableError<StorageT> {
    pub kind: StateTableErrorKind,
    pub pidx: PIdx<StorageT>,
}

impl<StorageT: Debug> Error for StateTableError<StorageT> {}

impl<StorageT> fmt::Display for StateTableError<StorageT> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s;
        match self.kind {
            StateTableErrorKind::AcceptReduceConflict => s = "Accept/reduce conflict",
        }
        write!(f, "{}", s)
    }
}

/// A representation of a `StateTable` for a grammar. `actions` and `gotos` are split into two
/// separate hashmaps, rather than a single table, due to the different types of their values.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct StateTable<StorageT> {
    actions: SparseVec<usize>,
    state_actions: Vob,
    gotos: SparseVec<usize>,
    start_state: StIdx,
    core_reduces: Vob,
    state_shifts: Vob,
    reduce_states: Vob,
    prods_len: PIdx<StorageT>,
    tokens_len: TIdx<StorageT>,
    conflicts: Option<Conflicts<StorageT>>,
    pub final_state: StIdx,
}

#[derive(Clone, Copy, Debug, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub enum Action<StorageT> {
    /// Shift to state X in the statetable.
    Shift(StIdx),
    /// Reduce production X in the grammar.
    Reduce(PIdx<StorageT>),
    /// Accept this input.
    Accept,
    /// No valid action.
    Error,
}

const SHIFT: usize = 1;
const REDUCE: usize = 2;
const ACCEPT: usize = 3;
const ERROR: usize = 0;

impl<StorageT: 'static + Hash + PrimInt + Unsigned> StateTable<StorageT>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>,
{
    pub fn new(
        grm: &YaccGrammar<StorageT>,
        sg: &StateGraph<StorageT>,
    ) -> Result<Self, StateTableError<StorageT>> {
        let mut state_actions = Vob::from_elem(
            usize::from(sg.all_states_len())
                .checked_mul(usize::from(grm.tokens_len()))
                .unwrap(),
            false,
        );
        let maxa = usize::from(grm.tokens_len()) * usize::from(sg.all_states_len());
        let maxg = usize::from(grm.rules_len()) * usize::from(sg.all_states_len());
        // We only have usize-2 bits to store state IDs and rule indexes
        assert!(usize::from(sg.all_states_len()) < (usize::max_value() - 4));
        assert!(usize::from(grm.rules_len()) < (usize::max_value() - 4));
        let mut actions: Vec<usize> = vec![0; maxa];

        // Since 0 is reserved for the error type, and states are encoded by adding 1, we can only
        // store max_value - 1 states within the goto table
        assert!(usize::from(sg.all_states_len()) < (usize::from(StIdx::max_value()) - 1));
        let mut gotos: Vec<usize> = vec![0; maxg];

        // Store automatically resolved conflicts, so we can print them out later
        let mut reduce_reduce = Vec::new();
        let mut shift_reduce = Vec::new();
        let mut final_state = None;

        for (stidx, state) in sg
            .iter_closed_states()
            .enumerate()
            // x goes from 0..states_len(), and we know the latter can safely fit into an
            // StIdxStorageT, so the cast is safe.
            .map(|(x, y)| (StIdx(x as StIdxStorageT), y))
        {
            // Populate reduce and accepts
            for (&(pidx, dot), ctx) in &state.items {
                if dot < grm.prod_len(pidx) {
                    continue;
                }
                for tidx in ctx.iter_set_bits(..) {
                    let off = actions_offset(
                        grm.tokens_len(),
                        stidx,
                        // Since ctx is exactly tokens_len bits long, the call
                        // to as_ is safe.
                        TIdx(tidx.as_()),
                    );
                    state_actions.set(off, true);
                    match StateTable::decode(actions[off]) {
                        Action::Reduce(r_pidx) => {
                            if pidx == grm.start_prod() && tidx == usize::from(grm.eof_token_idx())
                            {
                                return Err(StateTableError {
                                    kind: StateTableErrorKind::AcceptReduceConflict,
                                    pidx,
                                });
                            }
                            // By default, Yacc resolves reduce/reduce conflicts in favour
                            // of the earlier production in the grammar.
                            match pidx.cmp(&r_pidx) {
                                Ordering::Less => {
                                    reduce_reduce.push((pidx, r_pidx, stidx));
                                    actions[off] = StateTable::encode(Action::Reduce(pidx));
                                }
                                Ordering::Greater => reduce_reduce.push((r_pidx, pidx, stidx)),
                                Ordering::Equal => (),
                            }
                        }
                        Action::Accept => {
                            return Err(StateTableError {
                                kind: StateTableErrorKind::AcceptReduceConflict,
                                pidx,
                            });
                        }
                        Action::Error => {
                            if pidx == grm.start_prod() && tidx == usize::from(grm.eof_token_idx())
                            {
                                assert!(final_state.is_none());
                                final_state = Some(stidx);
                                actions[off] = StateTable::encode(Action::Accept);
                            } else {
                                actions[off] = StateTable::encode(Action::Reduce(pidx));
                            }
                        }
                        _ => panic!("Internal error"),
                    }
                }
            }

            let nt_len = grm.rules_len();
            for (&sym, ref_stidx) in sg.edges(stidx) {
                match sym {
                    Symbol::Rule(s_ridx) => {
                        // Populate gotos
                        let off = (usize::from(stidx) * usize::from(nt_len)) + usize::from(s_ridx);
                        debug_assert!(gotos[off] == 0);
                        // Since 0 is reserved for no entry, encode states by adding 1
                        gotos[off] = usize::from(*ref_stidx) + 1;
                    }
                    Symbol::Token(s_tidx) => {
                        // Populate shifts
                        let off = actions_offset(grm.tokens_len(), stidx, s_tidx);
                        state_actions.set(off, true);
                        match StateTable::decode(actions[off]) {
                            Action::Shift(x) => assert_eq!(*ref_stidx, x),
                            Action::Reduce(r_pidx) => {
                                resolve_shift_reduce(
                                    grm,
                                    &mut actions,
                                    off,
                                    s_tidx,
                                    r_pidx,
                                    *ref_stidx,
                                    &mut shift_reduce,
                                    stidx,
                                );
                            }
                            Action::Accept => panic!("Internal error"),
                            Action::Error => {
                                actions[off] = StateTable::encode(Action::Shift(*ref_stidx));
                            }
                        }
                    }
                }
            }
        }
        assert!(final_state.is_some());

        let mut nt_depth = HashMap::new();
        let mut core_reduces = Vob::from_elem(
            usize::from(sg.all_states_len())
                .checked_mul(usize::from(grm.prods_len()))
                .unwrap(),
            false,
        );
        let mut state_shifts = Vob::from_elem(
            usize::from(sg.all_states_len())
                .checked_mul(usize::from(grm.tokens_len()))
                .unwrap(),
            false,
        );
        let mut reduce_states = Vob::from_elem(usize::from(sg.all_states_len()), false);
        for stidx in sg.iter_stidxs() {
            nt_depth.clear();
            let mut only_reduces = true;
            for tidx in grm.iter_tidxs() {
                let off = actions_offset(grm.tokens_len(), stidx, tidx);
                match StateTable::decode(actions[off]) {
                    Action::Reduce(pidx) => {
                        let prod_len = grm.prod(pidx).len();
                        let ridx = grm.prod_to_rule(pidx);
                        nt_depth.insert((ridx, prod_len), pidx);
                    }
                    Action::Shift(_) => {
                        only_reduces = false;
                        state_shifts.set(off, true);
                    }
                    Action::Accept => {
                        only_reduces = false;
                    }
                    Action::Error => (),
                }
            }

            let mut distinct_reduces = 0; // How many distinct reductions do we have?
            for &pidx in nt_depth.values() {
                let off = usize::from(stidx)
                    .checked_mul(usize::from(grm.prods_len()))
                    .unwrap()
                    .checked_add(usize::from(pidx))
                    .unwrap();
                if core_reduces.set(off, true) {
                    distinct_reduces += 1;
                }
            }

            if only_reduces && distinct_reduces == 1 {
                reduce_states.set(usize::from(stidx), true);
            }
        }

        let actions_sv = SparseVec::<usize>::from(&actions, 0, usize::from(grm.tokens_len()));
        let gotos_sv = SparseVec::<usize>::from(&gotos, 0, usize::from(grm.rules_len()));

        let conflicts = if !(reduce_reduce.is_empty() && shift_reduce.is_empty()) {
            Some(Conflicts {
                reduce_reduce,
                shift_reduce,
            })
        } else {
            None
        };

        Ok(StateTable {
            actions: actions_sv,
            state_actions,
            gotos: gotos_sv,
            start_state: sg.start_state(),
            state_shifts,
            core_reduces,
            reduce_states,
            prods_len: grm.prods_len(),
            tokens_len: grm.tokens_len(),
            conflicts,
            final_state: final_state.unwrap(),
        })
    }

    fn decode(bits: usize) -> Action<StorageT> {
        let action = bits & 0b11;
        let val = bits >> 2;

        match action {
            SHIFT => {
                // Since val was originally stored in an StIdxStorageT, we know that it's safe to
                // cast it back to an StIdxStorageT here.
                Action::Shift(StIdx::from(val as StIdxStorageT))
            }
            REDUCE => Action::Reduce(PIdx(val.as_())),
            ACCEPT => Action::Accept,
            ERROR => Action::Error,
            _ => unreachable!(),
        }
    }

    fn encode(action: Action<StorageT>) -> usize {
        match action {
            Action::Shift(stidx) => SHIFT | (usize::from(stidx) << 2),
            Action::Reduce(ridx) => REDUCE | (usize::from(ridx) << 2),
            Action::Accept => ACCEPT,
            Action::Error => ERROR,
        }
    }

    /// Return the action for `stidx` and `sym`, or `None` if there isn't any.
    pub fn action(&self, stidx: StIdx, tidx: TIdx<StorageT>) -> Action<StorageT> {
        StateTable::decode(
            self.actions
                .get(usize::from(stidx), usize::from(tidx))
                .unwrap(),
        )
    }

    /// Return an iterator over the indexes of all non-empty actions of `stidx`.
    pub fn state_actions(&self, stidx: StIdx) -> StateActionsIterator<StorageT> {
        let start = usize::from(stidx) * usize::from(self.tokens_len);
        let end = start + usize::from(self.tokens_len);
        StateActionsIterator {
            iter: self.state_actions.iter_set_bits(start..end),
            start,
            phantom: PhantomData,
        }
    }

    /// Return an iterator over the indexes of all shift actions of `stidx`. By definition this
    /// is a subset of the indexes produced by [`state_actions`](#method.state_actions).
    pub fn state_shifts(&self, stidx: StIdx) -> StateActionsIterator<StorageT> {
        let start = usize::from(stidx) * usize::from(self.tokens_len);
        let end = start + usize::from(self.tokens_len);
        StateActionsIterator {
            iter: self.state_shifts.iter_set_bits(start..end),
            start,
            phantom: PhantomData,
        }
    }

    /// Does the state `stidx` 1) only contain reduce (and error) actions 2) do those
    /// reductions all reduce to the same production?
    pub fn reduce_only_state(&self, stidx: StIdx) -> bool {
        self.reduce_states[usize::from(stidx)]
    }

    /// Return an iterator over a set of "core" reduces of `stidx`. This is a minimal set of
    /// reduce actions which explore all possible reductions from a given state. Note that these
    /// are chosen non-deterministically from a set of equivalent reduce actions: you must not rely
    /// on always seeing the same reduce actions. For example if a state has these three items:
    ///
    ///   [E -> a ., $]
    ///   [E -> b ., $]
    ///   [F -> c ., $]
    ///
    /// then the core reduces will be:
    ///
    ///   One of: [E -> a., $] or [E -> b., $]
    ///   And:    [F -> c., $]
    ///
    /// since the two [E -> ...] items both have the same effects on a parse stack.
    pub fn core_reduces(&self, stidx: StIdx) -> CoreReducesIterator<StorageT> {
        let start = usize::from(stidx) * usize::from(self.prods_len);
        let end = start + usize::from(self.prods_len);
        CoreReducesIterator {
            iter: self.core_reduces.iter_set_bits(start..end),
            start,
            phantom: PhantomData,
        }
    }

    /// Return the goto state for `stidx` and `ridx`, or `None` if there isn't any.
    pub fn goto(&self, stidx: StIdx, ridx: RIdx<StorageT>) -> Option<StIdx> {
        // Goto entries are encoded by adding 1 to their value, while 0 is reserved for no entry
        // (i.e. error)
        match self.gotos.get(usize::from(stidx), usize::from(ridx)) {
            Some(0) => None,
            // gotos can only contain state id's which we know can fit into StIdxStorageT so this
            // cast is safe
            Some(i) => Some(StIdx((i - 1) as StIdxStorageT)),
            None => unreachable!(),
        }
    }

    /// Return this state table's start state.
    pub fn start_state(&self) -> StIdx {
        self.start_state
    }

    /// Return a struct containing all conflicts or `None` if there aren't any.
    pub fn conflicts(&self) -> Option<&Conflicts<StorageT>> {
        self.conflicts.as_ref()
    }
}

fn actions_offset<StorageT: PrimInt + Unsigned>(
    tokens_len: TIdx<StorageT>,
    stidx: StIdx,
    tidx: TIdx<StorageT>,
) -> usize {
    usize::from(stidx) * usize::from(tokens_len) + usize::from(tidx)
}

pub struct StateActionsIterator<'a, StorageT> {
    iter: IterSetBits<'a, usize>,
    start: usize,
    phantom: PhantomData<StorageT>,
}

impl<'a, StorageT: 'static + PrimInt + Unsigned> Iterator for StateActionsIterator<'a, StorageT>
where
    usize: AsPrimitive<StorageT>,
{
    type Item = TIdx<StorageT>;

    fn next(&mut self) -> Option<TIdx<StorageT>> {
        // Since self.iter's IterSetBits range as exactly tokens_len long, by definition `i -
        // self.start` fits into StorageT and thus the as_ call here is safe.
        self.iter.next().map(|i| TIdx((i - self.start).as_()))
    }
}

pub struct CoreReducesIterator<'a, StorageT> {
    iter: IterSetBits<'a, usize>,
    start: usize,
    phantom: PhantomData<StorageT>,
}

impl<'a, StorageT: 'static + PrimInt + Unsigned> Iterator for CoreReducesIterator<'a, StorageT>
where
    usize: AsPrimitive<StorageT>,
{
    type Item = PIdx<StorageT>;

    fn next(&mut self) -> Option<PIdx<StorageT>> {
        // Since self.iter's IterSetBits range as exactly tokens_len long, by definition `i -
        // self.start` fits into StorageT and thus the as_ call here is safe.
        self.iter.next().map(|i| PIdx((i - self.start).as_()))
    }
}

fn resolve_shift_reduce<StorageT: 'static + Hash + PrimInt + Unsigned>(
    grm: &YaccGrammar<StorageT>,
    actions: &mut Vec<usize>,
    off: usize,
    tidx: TIdx<StorageT>,
    pidx: PIdx<StorageT>,
    stidx: StIdx, // State we want to shift to
    shift_reduce: &mut Vec<(TIdx<StorageT>, PIdx<StorageT>, StIdx)>,
    conflict_stidx: StIdx, // State in which the conflict occured
) where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>,
{
    let tidx_prec = grm.token_precedence(tidx);
    let pidx_prec = grm.prod_precedence(pidx);
    match (tidx_prec, pidx_prec) {
        (_, None) | (None, _) => {
            // If the token and production don't both have precedences, we use Yacc's default
            // resolution, which is in favour of the shift.
            actions[off] = StateTable::encode(Action::Shift(stidx));
            shift_reduce.push((tidx, pidx, conflict_stidx));
        }
        (Some(token_prec), Some(prod_prec)) => {
            match token_prec.level.cmp(&prod_prec.level) {
                Ordering::Equal => {
                    // Both token and production have the same level precedence, so we need to look
                    // at the precedence kind.
                    match (token_prec.kind, prod_prec.kind) {
                        (AssocKind::Left, AssocKind::Left) => {
                            // Left associativity is resolved in favour of the reduce (i.e. leave
                            // as-is).
                        }
                        (AssocKind::Right, AssocKind::Right) => {
                            // Right associativity is resolved in favour of the shift.
                            actions[off] = StateTable::encode(Action::Shift(stidx));
                        }
                        (AssocKind::Nonassoc, AssocKind::Nonassoc) => {
                            // Nonassociativity leads to a run-time parsing error, so we need to
                            // remove the action entirely.
                            actions[off] = StateTable::encode(Action::Error);
                        }
                        (_, _) => {
                            panic!("Not supported.");
                        }
                    }
                }
                Ordering::Greater => {
                    // The token has higher level precedence, so resolve in favour of shift.
                    actions[off] = StateTable::encode(Action::Shift(stidx));
                }
                Ordering::Less => {
                    // If token_lev < prod_lev, then the production has higher level precedence and
                    // we keep the reduce as-is.
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use cfgrammar::{
        yacc::{YaccGrammar, YaccKind, YaccOriginalActionKind},
        PIdx, Symbol, TIdx,
    };
    use std::collections::HashSet;

    use super::{Action, StateTable, StateTableError, StateTableErrorKind};
    use crate::{pager::pager_stategraph, StIdx};

    #[test]
    #[rustfmt::skip]
    fn test_statetable() {
        // Taken from p19 of www.cs.umd.edu/~mvz/cmsc430-s07/M10lr.pdf
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
            %start Expr
            %%
            Expr : Term '-' Expr | Term;
            Term : Factor '*' Term | Factor;
            Factor : 'id';
          "
        ).unwrap();
        let sg = pager_stategraph(&grm);
        assert_eq!(sg.all_states_len(), StIdx(9));

        let s0 = sg.start_state();
        let s1 = sg.edge(s0, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s2 = sg.edge(s0, Symbol::Rule(grm.rule_idx("Term").unwrap())).unwrap();
        let s3 = sg.edge(s0, Symbol::Rule(grm.rule_idx("Factor").unwrap())).unwrap();
        let s4 = sg.edge(s0, Symbol::Token(grm.token_idx("id").unwrap())).unwrap();
        let s5 = sg.edge(s2, Symbol::Token(grm.token_idx("-").unwrap())).unwrap();
        let s6 = sg.edge(s3, Symbol::Token(grm.token_idx("*").unwrap())).unwrap();
        let s7 = sg.edge(s5, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s8 = sg.edge(s6, Symbol::Rule(grm.rule_idx("Term").unwrap())).unwrap();

        let st = StateTable::new(&grm, &sg).unwrap();

        // Actions
        assert_eq!(st.actions.len(), 9*4);
        let assert_reduce = |stidx: StIdx, tidx: TIdx<_>, rule: &str, prod_off: usize| {
            let pidx = grm.rule_to_prods(grm.rule_idx(rule).unwrap())[prod_off];
            assert_eq!(st.action(stidx, tidx), Action::Reduce(pidx));
        };

        assert_eq!(st.action(s0, grm.token_idx("id").unwrap()), Action::Shift(s4));
        assert_eq!(st.action(s1, grm.eof_token_idx()), Action::Accept);
        assert_eq!(st.final_state, s1);
        assert_eq!(st.action(s2, grm.token_idx("-").unwrap()), Action::Shift(s5));
        assert_reduce(s2, grm.eof_token_idx(), "Expr", 1);
        assert_reduce(s3, grm.token_idx("-").unwrap(), "Term", 1);
        assert_eq!(st.action(s3, grm.token_idx("*").unwrap()), Action::Shift(s6));
        assert_reduce(s3, grm.eof_token_idx(), "Term", 1);
        assert_reduce(s4, grm.token_idx("-").unwrap(), "Factor", 0);
        assert_reduce(s4, grm.token_idx("*").unwrap(), "Factor", 0);
        assert_reduce(s4, grm.eof_token_idx(), "Factor", 0);
        assert_eq!(st.action(s5, grm.token_idx("id").unwrap()), Action::Shift(s4));
        assert_eq!(st.action(s6, grm.token_idx("id").unwrap()), Action::Shift(s4));
        assert_reduce(s7, grm.eof_token_idx(), "Expr", 0);
        assert_reduce(s8, grm.token_idx("-").unwrap(), "Term", 0);
        assert_reduce(s8, grm.eof_token_idx(), "Term", 0);

        let mut s4_actions = HashSet::new();
        s4_actions.extend(&[grm.token_idx("-").unwrap(),
                            grm.token_idx("*").unwrap(),
                            grm.eof_token_idx()]);
        assert_eq!(st.state_actions(s4).collect::<HashSet<_>>(), s4_actions);

        let s2_state_shifts = &[grm.token_idx("-").unwrap()]
                               .iter()
                               .cloned()
                               .collect::<HashSet<_>>();
        assert_eq!(st.state_shifts(s2).collect::<HashSet<_>>(), *s2_state_shifts);

        let s4_core_reduces = &[grm.rule_to_prods(grm.rule_idx("Factor").unwrap())[0]]
                              .iter()
                              .cloned()
                              .collect::<HashSet<_>>();
        assert_eq!(st.core_reduces(s4).collect::<HashSet<_>>(), *s4_core_reduces);

        // Gotos
        assert_eq!(st.gotos.len(), 9*4);
        assert_eq!(st.goto(s0, grm.rule_idx("Expr").unwrap()).unwrap(), s1);
        assert_eq!(st.goto(s0, grm.rule_idx("Term").unwrap()).unwrap(), s2);
        assert_eq!(st.goto(s0, grm.rule_idx("Factor").unwrap()).unwrap(), s3);
        assert_eq!(st.goto(s5, grm.rule_idx("Expr").unwrap()).unwrap(), s7);
        assert_eq!(st.goto(s5, grm.rule_idx("Term").unwrap()).unwrap(), s2);
        assert_eq!(st.goto(s5, grm.rule_idx("Factor").unwrap()).unwrap(), s3);
        assert_eq!(st.goto(s6, grm.rule_idx("Term").unwrap()).unwrap(), s8);
        assert_eq!(st.goto(s6, grm.rule_idx("Factor").unwrap()).unwrap(), s3);
    }

    #[test]
    #[rustfmt::skip]
    fn test_default_reduce_reduce() {
        let grm = YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), &"
            %start A
            %%
            A : B 'x' | C 'x' 'x';
            B : 'a';
            C : 'a';
          ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();

        let len = usize::from(grm.tokens_len()) * usize::from(sg.all_states_len());
        assert_eq!(st.actions.len(), len);

        // We only extract the states necessary to test those rules affected by the reduce/reduce.
        let s0 = sg.start_state();
        let s4 = sg.edge(s0, Symbol::Token(grm.token_idx("a").unwrap())).unwrap();

        assert_eq!(st.action(s4, grm.token_idx("x").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("B").unwrap())[0]));
    }

    #[test]
    #[rustfmt::skip]
    fn test_default_shift_reduce() {
        let grm = YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), &"
            %start Expr
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | 'id' ;
          ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        let len = usize::from(grm.tokens_len()) * usize::from(sg.all_states_len());
        assert_eq!(st.actions.len(), len);

        let s0 = sg.start_state();
        let s1 = sg.edge(s0, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Token(grm.token_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Token(grm.token_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s4, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s6 = sg.edge(s3, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s5, grm.token_idx("+").unwrap()), Action::Shift(s3));
        assert_eq!(st.action(s5, grm.token_idx("*").unwrap()), Action::Shift(s4));

        assert_eq!(st.action(s6, grm.token_idx("+").unwrap()), Action::Shift(s3));
        assert_eq!(st.action(s6, grm.token_idx("*").unwrap()), Action::Shift(s4));
    }

    #[test]
    #[rustfmt::skip]
    fn test_conflict_resolution() {
        // Example taken from p54 of Locally least-cost error repair in LR parsers, Carl Cerecke
        let grm = YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), &"
            %start S
            %%
            S: A 'c' 'd'
             | B 'c' 'e';
            A: 'a';
            B: 'a'
             | 'b';
            A: 'b';
            ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        let s0 = sg.start_state();
        let s1 = sg.edge(s0, Symbol::Token(grm.token_idx("a").unwrap())).unwrap();
        let s2 = sg.edge(s0, Symbol::Token(grm.token_idx("b").unwrap())).unwrap();

        assert_eq!(st.action(s1, grm.token_idx("c").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("A").unwrap())[0]));
        assert_eq!(st.action(s2, grm.token_idx("c").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("B").unwrap())[1]));
    }

    #[test]
    #[rustfmt::skip]
    fn test_left_associativity() {
        let grm = YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), &"
            %start Expr
            %left '+'
            %left '*'
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | 'id' ;
          ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        let len = usize::from(grm.tokens_len()) * usize::from(sg.all_states_len());
        assert_eq!(st.actions.len(), len);

        let s0 = sg.start_state();
        let s1 = sg.edge(s0, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Token(grm.token_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Token(grm.token_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s4, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s6 = sg.edge(s3, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s5, grm.token_idx("+").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s5, grm.token_idx("*").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s5, grm.eof_token_idx()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));

        assert_eq!(st.action(s6, grm.token_idx("+").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s6, grm.token_idx("*").unwrap()),
                   Action::Shift(s4));
        assert_eq!(st.action(s6, grm.eof_token_idx()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
    }

    #[test]
    #[rustfmt::skip]
    fn test_left_right_associativity() {
        let grm = &YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), &"
            %start Expr
            %right '='
            %left '+'
            %left '*'
            %%
            Expr : Expr '+' Expr
                 | Expr '*' Expr
                 | Expr '=' Expr
                 | 'id' ;
          ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        let len = usize::from(grm.tokens_len()) * usize::from(sg.all_states_len());
        assert_eq!(st.actions.len(), len);

        let s0 = sg.start_state();
        let s1 = sg.edge(s0, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Token(grm.token_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Token(grm.token_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s1, Symbol::Token(grm.token_idx("=").unwrap())).unwrap();
        let s6 = sg.edge(s5, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s7 = sg.edge(s4, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s8 = sg.edge(s3, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s6, grm.token_idx("+").unwrap()),
                   Action::Shift(s3));
        assert_eq!(st.action(s6, grm.token_idx("*").unwrap()),
                   Action::Shift(s4));
        assert_eq!(st.action(s6, grm.token_idx("=").unwrap()),
                   Action::Shift(s5));
        assert_eq!(st.action(s6, grm.eof_token_idx()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[2]));

        assert_eq!(st.action(s7, grm.token_idx("+").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s7, grm.token_idx("*").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s7, grm.token_idx("=").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s7, grm.eof_token_idx()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));

        assert_eq!(st.action(s8, grm.token_idx("+").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s8, grm.token_idx("*").unwrap()),
                   Action::Shift(s4));
        assert_eq!(st.action(s8, grm.token_idx("=").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s8, grm.eof_token_idx()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
    }

    #[test]
    #[rustfmt::skip]
    fn test_left_right_nonassoc_associativity() {
        let grm = YaccGrammar::new(YaccKind::Original(YaccOriginalActionKind::GenericParseTree), &"
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
          ").unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        let len = usize::from(grm.tokens_len()) * usize::from(sg.all_states_len());
        assert_eq!(st.actions.len(), len);

        let s0 = sg.start_state();
        let s1 = sg.edge(s0, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Token(grm.token_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Token(grm.token_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s1, Symbol::Token(grm.token_idx("=").unwrap())).unwrap();
        let s6 = sg.edge(s1, Symbol::Token(grm.token_idx("~").unwrap())).unwrap();
        let s7 = sg.edge(s6, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s8 = sg.edge(s5, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s9 = sg.edge(s4, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s10 = sg.edge(s3, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s7, grm.token_idx("+").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[3]));
        assert_eq!(st.action(s7, grm.token_idx("*").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[3]));
        assert_eq!(st.action(s7, grm.token_idx("=").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[3]));
        assert_eq!(st.action(s7, grm.eof_token_idx()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[3]));

        assert_eq!(st.action(s8, grm.token_idx("+").unwrap()),
                   Action::Shift(s3));
        assert_eq!(st.action(s8, grm.token_idx("*").unwrap()),
                   Action::Shift(s4));
        assert_eq!(st.action(s8, grm.token_idx("=").unwrap()),
                   Action::Shift(s5));
        assert_eq!(st.action(s8, grm.token_idx("~").unwrap()),
                   Action::Shift(s6));
        assert_eq!(st.action(s8, grm.eof_token_idx()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[2]));

        assert_eq!(st.action(s9, grm.token_idx("+").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s9, grm.token_idx("*").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s9, grm.token_idx("=").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s9, grm.token_idx("~").unwrap()),
                   Action::Shift(s6));
        assert_eq!(st.action(s9, grm.eof_token_idx()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));

        assert_eq!(st.action(s10, grm.token_idx("+").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s10, grm.token_idx("*").unwrap()),
                   Action::Shift(s4));
        assert_eq!(st.action(s10, grm.token_idx("=").unwrap()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s10, grm.token_idx("~").unwrap()),
                   Action::Shift(s6));
        assert_eq!(st.action(s10, grm.eof_token_idx()),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
    }

    #[test]
    fn conflicts() {
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
%start A
%%
A : 'a' 'b' | B 'b';
B : 'a' | C;
C : 'a';
          ",
        )
        .unwrap();
        let sg = pager_stategraph(&grm);
        let st = StateTable::new(&grm, &sg).unwrap();
        let conflicts = st.conflicts().unwrap();
        assert_eq!(conflicts.sr_len(), 1);
        assert_eq!(conflicts.rr_len(), 1);
        assert_eq!(
            conflicts.sr_conflicts().next().unwrap(),
            &(
                grm.token_idx("b").unwrap(),
                grm.rule_to_prods(grm.rule_idx("B").unwrap())[0],
                StIdx::from(2)
            )
        );
        assert_eq!(
            conflicts.rr_conflicts().next().unwrap(),
            &(
                grm.rule_to_prods(grm.rule_idx("B").unwrap())[0],
                grm.rule_to_prods(grm.rule_idx("C").unwrap())[0],
                StIdx::from(2)
            )
        );
    }

    #[test]
    fn accept_reduce_conflict() {
        let grm = YaccGrammar::new(
            YaccKind::Original(YaccOriginalActionKind::GenericParseTree),
            &"
%start D
%%
D : D;
          ",
        )
        .unwrap();
        let sg = pager_stategraph(&grm);
        match StateTable::new(&grm, &sg) {
            Ok(_) => panic!("Infinitely recursive rule let through"),
            Err(StateTableError {
                kind: StateTableErrorKind::AcceptReduceConflict,
                pidx,
            }) if pidx == PIdx(1) => (),
            Err(e) => panic!("Incorrect error returned {:?}", e),
        }
    }
}
