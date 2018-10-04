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

use std::{
    collections::hash_map::{HashMap},
    error::Error,
    fmt::{self, Debug},
    hash::{Hash},
    marker::PhantomData,
    convert::TryFrom
};

use cfgrammar::{
    yacc::{AssocKind, YaccGrammar},
    PIdx, RIdx, Symbol, TIdx
};
use num_traits::{AsPrimitive, PrimInt, Unsigned};
use vob::{IterSetBits, Vob};
use packed_vec::PackedVec;

use {StIdx, StIdxStorageT};
use stategraph::StateGraph;

/// The various different possible Yacc parser errors.
#[derive(Debug)]
pub enum StateTableErrorKind {
    AcceptReduceConflict
}

/// Any error from the Yacc parser returns an instance of this struct.
#[derive(Debug)]
pub struct StateTableError<StorageT> {
    pub kind: StateTableErrorKind,
    pub pidx: PIdx<StorageT>
}

impl<StorageT: Debug> Error for StateTableError<StorageT> {}

impl<StorageT> fmt::Display for StateTableError<StorageT> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s;
        match self.kind {
            StateTableErrorKind::AcceptReduceConflict => s = "Accept/reduce conflict"
        }
        write!(f, "{}", s)
    }
}

/// A representation of a `StateTable` for a grammar. `actions` and `gotos` are split into two
/// separate hashmaps, rather than a single table, due to the different types of their values.
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
pub struct StateTable<StorageT> {
    // For actions, we use a HashMap as a quick representation of a sparse table. We use the normal
    // statetable representation where rows represent states and columns represent tokens. Thus
    // the statetable:
    //        A         B
    //   0  shift 1
    //   1  shift 0  reduce B
    // is represented as a hashtable {0: shift 1, 2: shift 0, 3: reduce 4}.
    actions: PackedVec<usize>,
    state_actions: Vob,
    gotos: Vec<StIdx>,
    core_reduces: Vob,
    state_shifts: Vob,
    reduce_states: Vob,
    rules_len: RIdx<StorageT>,
    prods_len: PIdx<StorageT>,
    tokens_len: TIdx<StorageT>,
    /// The number of reduce/reduce errors encountered.
    pub reduce_reduce: u64,
    /// The number of shift/reduce errors encountered.
    pub shift_reduce: u64,
    pub final_state: StIdx
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
    Error
}

const SHIFT: usize = 1;
const REDUCE: usize = 2;
const ACCEPT: usize = 3;
const ERROR: usize = 0;

impl<StorageT: 'static + Hash + PrimInt + Unsigned> StateTable<StorageT>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    pub fn new(
        grm: &YaccGrammar<StorageT>,
        sg: &StateGraph<StorageT>
    ) -> Result<Self, StateTableError<StorageT>> {
        let mut state_actions = Vob::from_elem(
            usize::from(sg.all_states_len())
                .checked_mul(usize::from(grm.tokens_len()))
                .unwrap(),
            false
        );
        let maxa = usize::from(grm.tokens_len()) * usize::from(sg.all_states_len());
        let maxg = usize::from(grm.rules_len()) * usize::from(sg.all_states_len());
        // We only have usize-2 bits to store state IDs and rule indexes
        assert!(usize::try_from(sg.all_states_len()) < Ok(usize::max_value() - 4));
        assert!(usize::try_from(grm.rules_len()) < Ok(usize::max_value() - 4));
        let mut actions: Vec<usize> = Vec::with_capacity(maxa);
        actions.resize(maxa, 0);
        let mut gotos: Vec<StIdx> = Vec::with_capacity(maxg);
        gotos.resize(maxg, StIdx::max_value());

        let mut reduce_reduce = 0; // How many automatically resolved reduce/reduces were made?
        let mut shift_reduce = 0; // How many automatically resolved shift/reduces were made?
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
                        TIdx(tidx.as_())
                    );
                    state_actions.set(off as usize, true);
                    match StateTable::decode(actions[off as usize]) {
                                Action::Reduce(r_pidx) => {
                                    if pidx == grm.start_prod()
                                        && tidx == usize::from(grm.eof_token_idx())
                                    {
                                        return Err(StateTableError {
                                            kind: StateTableErrorKind::AcceptReduceConflict,
                                            pidx
                                        });
                                    }
                                    // By default, Yacc resolves reduce/reduce conflicts in favour
                                    // of the earlier production in the grammar.
                                    if pidx < r_pidx {
                                        reduce_reduce += 1;
                                        actions[off as usize] = StateTable::encode(Action::Reduce(pidx));
                                    } else if pidx > r_pidx {
                                        reduce_reduce += 1;
                                    }
                                }
                                Action::Accept => {
                                    return Err(StateTableError {
                                        kind: StateTableErrorKind::AcceptReduceConflict,
                                        pidx
                                    })
                                }
                                Action::Error => {
                                    if pidx == grm.start_prod() && tidx == usize::from(grm.eof_token_idx())
                                    {
                                        assert!(final_state.is_none());
                                        final_state = Some(stidx);
                                        actions[off as usize] = StateTable::encode(Action::Accept);
                                    } else {
                                        actions[off as usize] = StateTable::encode(Action::Reduce(pidx));
                                    }
                                }
                                _ => panic!("Internal error")
                    }
                }
            }

            let nt_len = grm.rules_len();
            for (&sym, ref_stidx) in sg.edges(stidx) {
                match sym {
                    Symbol::Rule(s_ridx) => {
                        // Populate gotos
                        let off = (usize::from(stidx) * usize::from(nt_len)) + usize::from(s_ridx);
                        debug_assert!(gotos[off] == StIdx::max_value());
                        gotos[off] = *ref_stidx;
                    }
                    Symbol::Token(s_tidx) => {
                        // Populate shifts
                        let off = actions_offset(grm.tokens_len(), stidx, s_tidx);
                        state_actions.set(off as usize, true);
                        match StateTable::decode(actions[off as usize]) {
                            Action::Shift(x) => assert_eq!(*ref_stidx, x),
                            Action::Reduce(r_pidx) => {
                                shift_reduce +=
                                    resolve_shift_reduce(grm, &mut actions, off as usize, s_tidx, r_pidx, *ref_stidx);
                            }
                            Action::Accept => panic!("Internal error"),
                            Action::Error => {
                                actions[off as usize] = StateTable::encode(Action::Shift(*ref_stidx));
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
            false
        );
        let mut state_shifts = Vob::from_elem(
            usize::from(sg.all_states_len())
                .checked_mul(usize::from(grm.tokens_len()))
                .unwrap(),
            false
        );
        let mut reduce_states = Vob::from_elem(usize::from(sg.all_states_len()), false);
        for stidx in sg.iter_stidxs() {
            nt_depth.clear();
            let mut only_reduces = true;
            for tidx in grm.iter_tidxs() {
                let off = actions_offset(grm.tokens_len(), stidx, tidx);
                match StateTable::decode(actions[off as usize]) {
                    Action::Reduce(pidx) => {
                        let prod_len = grm.prod(pidx).len();
                        let ridx = grm.prod_to_rule(pidx);
                        nt_depth.insert((ridx, prod_len), pidx);
                    }
                    Action::Shift(_) => {
                        only_reduces = false;
                        state_shifts.set(off as usize, true);
                    }
                    Action::Accept => {
                        only_reduces = false;
                    }
                    Action::Error => ()
                }
            }

            let mut distinct_reduces = 0; // How many distinct reductions do we have?
            for &pidx in nt_depth.values() {
                let off = usize::from(stidx)
                    .checked_mul(usize::from(grm.prods_len()))
                    .unwrap()
                    .checked_add(usize::from(pidx))
                    .unwrap();
                if core_reduces.set(off, true) == Some(true) {
                    distinct_reduces += 1;
                }
            }

            if only_reduces && distinct_reduces == 1 {
                reduce_states.set(usize::from(stidx), true);
            }
        }

        let actions = PackedVec::new(actions);

        Ok(StateTable {
            actions,
            state_actions,
            gotos,
            state_shifts,
            core_reduces,
            reduce_states,
            rules_len: grm.rules_len(),
            prods_len: grm.prods_len(),
            tokens_len: grm.tokens_len(),
            reduce_reduce,
            shift_reduce,
            final_state: final_state.unwrap()
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
            },
            REDUCE => Action::Reduce(PIdx(val.as_())),
            ACCEPT => Action::Accept,
            ERROR => Action::Error,
            _ => unreachable!()
        }
    }

    fn encode(action: Action<StorageT>) -> usize {
        match action {
            Action::Shift(stidx) => SHIFT | (usize::from(stidx) << 2),
            Action::Reduce(ridx) => REDUCE | (usize::from(ridx) << 2),
            Action::Accept => ACCEPT,
            Action::Error => ERROR
        }
    }

    /// Return the action for `stidx` and `sym`, or `None` if there isn't any.
    pub fn action(&self, stidx: StIdx, tidx: TIdx<StorageT>) -> Option<Action<StorageT>> {
        let off = actions_offset(self.tokens_len, stidx, tidx);
        // For now leave this as an option so we don't need to touch all the other libraries
        Some(StateTable::decode(self.actions.get(off as usize).unwrap()))
    }

    /// Return an iterator over the indexes of all non-empty actions of `stidx`.
    pub fn state_actions(&self, stidx: StIdx) -> StateActionsIterator<StorageT> {
        let start = usize::from(stidx) * usize::from(self.tokens_len);
        let end = start + usize::from(self.tokens_len);
        StateActionsIterator {
            iter: self.state_actions.iter_set_bits(start..end),
            start,
            phantom: PhantomData
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
            phantom: PhantomData
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
            phantom: PhantomData
        }
    }

    /// Return the goto state for `stidx` and `ridx`, or `None` if there isn't any.
    pub fn goto(&self, stidx: StIdx, ridx: RIdx<StorageT>) -> Option<StIdx> {
        let off = (usize::from(stidx) * usize::from(self.rules_len)) + usize::from(ridx);
        if self.gotos[off] == StIdx::max_value() {
            None
        }
        else {
            Some(self.gotos[off])
        }
    }
}

fn actions_offset<StorageT: PrimInt + Unsigned>(
    tokens_len: TIdx<StorageT>,
    stidx: StIdx,
    tidx: TIdx<StorageT>
) -> usize {
    usize::from(stidx) * usize::from(tokens_len) + usize::from(tidx)
}



pub struct StateActionsIterator<'a, StorageT> {
    iter: IterSetBits<'a, usize>,
    start: usize,
    phantom: PhantomData<StorageT>
}

impl<'a, StorageT: 'static + PrimInt + Unsigned> Iterator for StateActionsIterator<'a, StorageT>
where
    usize: AsPrimitive<StorageT>
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
    phantom: PhantomData<StorageT>
}

impl<'a, StorageT: 'static + PrimInt + Unsigned> Iterator for CoreReducesIterator<'a, StorageT>
where
    usize: AsPrimitive<StorageT>
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
    stidx: StIdx
) -> u64
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    let mut shift_reduce = 0;
    let tidx_prec = grm.token_precedence(tidx);
    let pidx_prec = grm.prod_precedence(pidx);
    match (tidx_prec, pidx_prec) {
        (_, None) | (None, _) => {
            // If the token and production don't both have precedences, we use Yacc's default
            // resolution, which is in favour of the shift.
            actions[off] = StateTable::encode(Action::Shift(stidx));
            shift_reduce += 1;
        }
        (Some(token_prec), Some(prod_prec)) => {
            if token_prec.level == prod_prec.level {
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
                        // Nonassociativity leads to a run-time parsing error, so we need to remove
                        // the action entirely.
                        actions[off] = StateTable::encode(Action::Error);
                    }
                    (_, _) => {
                        panic!("Not supported.");
                    }
                }
            } else if token_prec.level > prod_prec.level {
                // The token has higher level precedence, so resolve in favour of shift.
                actions[off] = StateTable::encode(Action::Shift(stidx));
            }
            // If token_lev < prod_lev, then the production has higher level precedence and we keep
            // the reduce as-is.
        }
    }
    shift_reduce
}

#[cfg(test)]
mod test {
    use super::{Action, StateTable, StateTableError, StateTableErrorKind};
    use cfgrammar::{
        yacc::{YaccGrammar, YaccKind},
        PIdx, Symbol, TIdx
    };
    use pager::pager_stategraph;
    use std::collections::HashSet;
    use StIdx;

    #[test]
    #[rustfmt::skip]
    fn test_statetable() {
        // Taken from p19 of www.cs.umd.edu/~mvz/cmsc430-s07/M10lr.pdf
        let grm = YaccGrammar::new(
            YaccKind::Original,
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

        let s0 = StIdx(0);
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
            assert_eq!(st.action(stidx, tidx).unwrap(), Action::Reduce(pidx.into()));
        };

        assert_eq!(st.action(s0, grm.token_idx("id").unwrap()).unwrap(), Action::Shift(s4));
        assert_eq!(st.action(s1, grm.eof_token_idx()).unwrap(), Action::Accept);
        assert_eq!(st.final_state, s1);
        assert_eq!(st.action(s2, grm.token_idx("-").unwrap()).unwrap(), Action::Shift(s5));
        assert_reduce(s2, grm.eof_token_idx(), "Expr", 1);
        assert_reduce(s3, grm.token_idx("-").unwrap(), "Term", 1);
        assert_eq!(st.action(s3, grm.token_idx("*").unwrap()).unwrap(), Action::Shift(s6));
        assert_reduce(s3, grm.eof_token_idx(), "Term", 1);
        assert_reduce(s4, grm.token_idx("-").unwrap(), "Factor", 0);
        assert_reduce(s4, grm.token_idx("*").unwrap(), "Factor", 0);
        assert_reduce(s4, grm.eof_token_idx(), "Factor", 0);
        assert_eq!(st.action(s5, grm.token_idx("id").unwrap()).unwrap(), Action::Shift(s4));
        assert_eq!(st.action(s6, grm.token_idx("id").unwrap()).unwrap(), Action::Shift(s4));
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
        let grm = YaccGrammar::new(YaccKind::Original, &"
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
        let s0 = StIdx(0);
        let s4 = sg.edge(s0, Symbol::Token(grm.token_idx("a").unwrap())).unwrap();

        assert_eq!(st.action(s4, grm.token_idx("x").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("B").unwrap())[0]));
    }

    #[test]
    #[rustfmt::skip]
    fn test_default_shift_reduce() {
        let grm = YaccGrammar::new(YaccKind::Original, &"
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

        let s0 = StIdx(0);
        let s1 = sg.edge(s0, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Token(grm.token_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Token(grm.token_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s4, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s6 = sg.edge(s3, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s5, grm.token_idx("+").unwrap()).unwrap(), Action::Shift(s3));
        assert_eq!(st.action(s5, grm.token_idx("*").unwrap()).unwrap(), Action::Shift(s4));

        assert_eq!(st.action(s6, grm.token_idx("+").unwrap()).unwrap(), Action::Shift(s3));
        assert_eq!(st.action(s6, grm.token_idx("*").unwrap()).unwrap(), Action::Shift(s4));
    }

    #[test]
    #[rustfmt::skip]
    fn test_conflict_resolution() {
        // Example taken from p54 of Locally least-cost error repair in LR parsers, Carl Cerecke
        let grm = YaccGrammar::new(YaccKind::Original, &"
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
        let s0 = StIdx(0);
        let s1 = sg.edge(s0, Symbol::Token(grm.token_idx("a").unwrap())).unwrap();
        let s2 = sg.edge(s0, Symbol::Token(grm.token_idx("b").unwrap())).unwrap();

        assert_eq!(st.action(s1, grm.token_idx("c").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("A").unwrap())[0]));
        assert_eq!(st.action(s2, grm.token_idx("c").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("B").unwrap())[1]));
    }

    #[test]
    #[rustfmt::skip]
    fn test_left_associativity() {
        let grm = YaccGrammar::new(YaccKind::Original, &"
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

        let s0 = StIdx(0);
        let s1 = sg.edge(s0, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Token(grm.token_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Token(grm.token_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s4, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s6 = sg.edge(s3, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s5, grm.token_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s5, grm.token_idx("*").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s5, grm.eof_token_idx()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));

        assert_eq!(st.action(s6, grm.token_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s6, grm.token_idx("*").unwrap()).unwrap(),
                   Action::Shift(s4));
        assert_eq!(st.action(s6, grm.eof_token_idx()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
    }

    #[test]
    #[rustfmt::skip]
    fn test_left_right_associativity() {
        let grm = &YaccGrammar::new(YaccKind::Original, &"
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

        let s0 = StIdx(0);
        let s1 = sg.edge(s0, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Token(grm.token_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Token(grm.token_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s1, Symbol::Token(grm.token_idx("=").unwrap())).unwrap();
        let s6 = sg.edge(s5, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s7 = sg.edge(s4, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s8 = sg.edge(s3, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s6, grm.token_idx("+").unwrap()).unwrap(),
                   Action::Shift(s3));
        assert_eq!(st.action(s6, grm.token_idx("*").unwrap()).unwrap(),
                   Action::Shift(s4));
        assert_eq!(st.action(s6, grm.token_idx("=").unwrap()).unwrap(),
                   Action::Shift(s5));
        assert_eq!(st.action(s6, grm.eof_token_idx()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[2]));

        assert_eq!(st.action(s7, grm.token_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s7, grm.token_idx("*").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s7, grm.token_idx("=").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s7, grm.eof_token_idx()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));

        assert_eq!(st.action(s8, grm.token_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s8, grm.token_idx("*").unwrap()).unwrap(),
                   Action::Shift(s4));
        assert_eq!(st.action(s8, grm.token_idx("=").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s8, grm.eof_token_idx()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
    }

    #[test]
    #[rustfmt::skip]
    fn test_left_right_nonassoc_associativity() {
        let grm = YaccGrammar::new(YaccKind::Original, &"
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

        let s0 = StIdx(0);
        let s1 = sg.edge(s0, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s3 = sg.edge(s1, Symbol::Token(grm.token_idx("+").unwrap())).unwrap();
        let s4 = sg.edge(s1, Symbol::Token(grm.token_idx("*").unwrap())).unwrap();
        let s5 = sg.edge(s1, Symbol::Token(grm.token_idx("=").unwrap())).unwrap();
        let s6 = sg.edge(s1, Symbol::Token(grm.token_idx("~").unwrap())).unwrap();
        let s7 = sg.edge(s6, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s8 = sg.edge(s5, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s9 = sg.edge(s4, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();
        let s10 = sg.edge(s3, Symbol::Rule(grm.rule_idx("Expr").unwrap())).unwrap();

        assert_eq!(st.action(s7, grm.token_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[3]));
        assert_eq!(st.action(s7, grm.token_idx("*").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[3]));
        assert_eq!(st.action(s7, grm.token_idx("=").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[3]));
        assert_eq!(st.action(s7, grm.eof_token_idx()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[3]));

        assert_eq!(st.action(s8, grm.token_idx("+").unwrap()).unwrap(),
                   Action::Shift(s3));
        assert_eq!(st.action(s8, grm.token_idx("*").unwrap()).unwrap(),
                   Action::Shift(s4));
        assert_eq!(st.action(s8, grm.token_idx("=").unwrap()).unwrap(),
                   Action::Shift(s5));
        assert_eq!(st.action(s8, grm.token_idx("~").unwrap()).unwrap(),
                   Action::Shift(s6));
        assert_eq!(st.action(s8, grm.eof_token_idx()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[2]));

        assert_eq!(st.action(s9, grm.token_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s9, grm.token_idx("*").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s9, grm.token_idx("=").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));
        assert_eq!(st.action(s9, grm.token_idx("~").unwrap()).unwrap(),
                   Action::Shift(s6));
        assert_eq!(st.action(s9, grm.eof_token_idx()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[1]));

        assert_eq!(st.action(s10, grm.token_idx("+").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s10, grm.token_idx("*").unwrap()).unwrap(),
                   Action::Shift(s4));
        assert_eq!(st.action(s10, grm.token_idx("=").unwrap()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
        assert_eq!(st.action(s10, grm.token_idx("~").unwrap()).unwrap(),
                   Action::Shift(s6));
        assert_eq!(st.action(s10, grm.eof_token_idx()).unwrap(),
                   Action::Reduce(grm.rule_to_prods(grm.rule_idx("Expr").unwrap())[0]));
    }

    #[test]
    fn accept_reduce_conflict() {
        let grm = YaccGrammar::new(
            YaccKind::Original,
            &"
%start D
%%
D : D;
          "
        ).unwrap();
        let sg = pager_stategraph(&grm);
        match StateTable::new(&grm, &sg) {
            Ok(_) => panic!("Infinitely recursive rule let through"),
            Err(StateTableError {
                kind: StateTableErrorKind::AcceptReduceConflict,
                pidx
            })
                if pidx == PIdx(1) =>
            {
                ()
            }
            Err(e) => panic!("Incorrect error returned {:?}", e)
        }
    }
}
