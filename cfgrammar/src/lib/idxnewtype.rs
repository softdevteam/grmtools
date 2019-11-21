// This macro generates a struct which exposes a u32 API (but which may, internally, use a smaller
// storage size).

use std::mem::size_of;

use num_traits::{self, PrimInt, Unsigned};
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

macro_rules! IdxNewtype {
    ($(#[$attr:meta])* $n: ident) => {
        $(#[$attr])*
        #[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
        #[cfg_attr(feature="serde", derive(Serialize, Deserialize))]
        pub struct $n<T>(pub T);

        impl<T: PrimInt + Unsigned> From<$n<T>> for usize {
            fn from(st: $n<T>) -> Self {
                debug_assert!(size_of::<usize>() >= size_of::<T>());
                num_traits::cast(st.0).unwrap()
            }
        }

        impl<T: PrimInt + Unsigned> From<$n<T>> for u32 {
            fn from(st: $n<T>) -> Self {
                debug_assert!(size_of::<u32>() >= size_of::<T>());
                num_traits::cast(st.0).unwrap()
            }
        }

        impl<T: PrimInt + Unsigned> $n<T> {
            pub fn as_storaget(&self) -> T {
                self.0
            }
        }
    }
}

IdxNewtype!(
    /// A type specifically for rule indices.
    ///
    /// It is guaranteed that `RIdx` can be converted, without loss of precision, to `usize` with
    /// the idiom `RIdx::from(x_usize)`. `usize` values can be converted to `RIdx`, causing a
    /// panic if this would lead to a loss of precision with `usize::from(y_ridx)`.
    RIdx
);
IdxNewtype!(
    /// A type specifically for production indices (e.g. a rule `E::=A|B` would
    /// have two productions for the single rule `E`).
    ///
    /// It is guaranteed that `PIdx` can be converted, without loss of precision, to `usize` with
    /// the idiom `PIdx::from(x_usize)`. `usize` values can be converted to `PTIdx`, causing a
    /// panic if this would lead to a loss of precision with `usize::from(y_pidx)`.
    PIdx
);
IdxNewtype!(
    /// A type specifically for symbol indices (within a production).
    ///
    /// It is guaranteed that `SIdx` can be converted, without loss of precision, to `usize` with
    /// the idiom `SIdx::from(x_usize)`. `usize` values can be converted to `RIdx`, causing a
    /// panic if this would lead to a loss of precision with `usize::from(y_sidx)`.
    SIdx
);
IdxNewtype!(
    /// A type specifically for token indices.
    ///
    /// It is guaranteed that `TIdx` can be converted, without loss of precision, to `usize` with
    /// the idiom `TIdx::from(x_usize)`. `usize` values can be converted to `TIdx`, causing a
    /// panic if this would lead to a loss of precision with `usize::from(y_tidx)`.
    TIdx
);
