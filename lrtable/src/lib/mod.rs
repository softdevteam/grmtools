#![allow(clippy::cognitive_complexity)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::type_complexity)]

use std::{hash::Hash, mem::size_of};

use num_traits::{AsPrimitive, PrimInt, Unsigned};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use static_assertions::const_assert;

mod itemset;
mod pager;
mod stategraph;
pub mod statetable;

pub use crate::{
    stategraph::StateGraph,
    statetable::{Action, StateTable, StateTableError, StateTableErrorKind},
};
use cfgrammar::yacc::YaccGrammar;

/// The type of the inner value of an StIdx.
pub type StIdxStorageT = u16;

/// StIdx is a wrapper for a state index. Its internal type is `StIdxStorageT`. The only guarantee
/// we make about `StIdx' is that it can be infallibly converted to usize.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]

pub struct StIdx(StIdxStorageT);

impl StIdx {
    fn max_value() -> StIdx {
        StIdx(StIdxStorageT::max_value())
    }
}

impl From<StIdxStorageT> for StIdx {
    fn from(v: StIdxStorageT) -> Self {
        StIdx(v)
    }
}

impl From<StIdx> for usize {
    fn from(st: StIdx) -> Self {
        const_assert!(size_of::<usize>() >= size_of::<StIdxStorageT>());
        st.0 as usize
    }
}

impl From<StIdx> for StIdxStorageT {
    fn from(st: StIdx) -> Self {
        st.0 as StIdxStorageT
    }
}

#[derive(Clone, Copy)]
pub enum Minimiser {
    Pager,
}

pub fn from_yacc<StorageT: 'static + Hash + PrimInt + Unsigned>(
    grm: &YaccGrammar<StorageT>,
    m: Minimiser,
) -> Result<(StateGraph<StorageT>, StateTable<StorageT>), StateTableError<StorageT>>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>,
{
    match m {
        Minimiser::Pager => {
            let sg = pager::pager_stategraph(grm);
            let st = StateTable::new(grm, &sg)?;
            Ok((sg, st))
        }
    }
}
