// Copyright (c) 2018 King's College London
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

// This macro generates a struct which exposes a u32 API (but which may, internally, use a smaller
// storage size).

macro_rules! u32struct {
    ($(#[$attr:meta])* $n: ident, $t: ident) => {
        $(#[$attr])*
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd)]
        pub struct $n {
            v: $t
        }

        impl From<u32> for $n {
            fn from(v: u32) -> Self {
                if v > $t::max_value() as u32 {
                    panic!("Overflow");
                }
                $n{v: v as $t}
            }
        }

        impl From<usize> for $n {
            fn from(v: usize) -> Self {
                if v > $t::max_value() as usize {
                    panic!("Overflow");
                }
                $n{v: v as $t}
            }
        }

        impl From<$n> for usize {
            fn from(st: $n) -> Self {
                st.v as usize
            }
        }

        impl From<$n> for u32 {
            fn from(st: $n) -> Self {
                st.v as u32
            }
        }
    }
}

// Will anyone create a grammar with more than 65535 non-terminals, productions, symbols within a
// production, or terminals? Yes, now that I've said it out loud, they probably will. But all
// practical grammars I know of are comfortably within these limits, so use narrow storage types
// for now, knowing that we can transparently move the storage type from u16 to u32 in the future
// without changing the user visible API.

u32struct!(
    /// A type specifically for nonterminal indices.
    NTIdx,
    u16);
u32struct!(
    /// A type specifically for production indices (e.g. a rule `E::=A|B` would
    /// have two productions for the single rule `E`).
    PIdx,
    u16);
u32struct!(
    /// A type specifically for symbol indices (within a production).
    SIdx,
    u16);
u32struct!(
    /// A type specifically for token indices.
    TIdx,
    u16);
