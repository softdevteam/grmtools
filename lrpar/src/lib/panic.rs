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

use std::{fmt::Debug, hash::Hash, time::Instant};

use lrtable::{Action, StIdx};
use num_traits::{AsPrimitive, PrimInt, Unsigned};

use parser::{Node, ParseRepair, Parser, Recoverer};

struct Panic;

pub(crate) fn recoverer<'a, StorageT: 'static + Debug + Hash + PrimInt + Unsigned>(
    _: &'a Parser<StorageT>
) -> Box<Recoverer<StorageT> + 'a>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    Box::new(Panic)
}

impl<StorageT: 'static + Debug + Hash + PrimInt + Unsigned> Recoverer<StorageT> for Panic
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    fn recover(
        &self,
        finish_by: Instant,
        parser: &Parser<StorageT>,
        in_laidx: usize,
        in_pstack: &mut Vec<StIdx>,
        _: &mut Vec<Node<StorageT>>
    ) -> (usize, Vec<Vec<ParseRepair<StorageT>>>) {
        // This recoverer is based on that in Compiler Design in C by Allen I. Holub p.348.
        //
        // It doesn't really fit into our recoverer mould very well: it can't always flesh out a
        // valid parse tree, and it often recovers in a way that the user can't emulate (i.e. there
        // is no way the user can adjust their input to get the parser into the same state as the
        // recovery algorithm manages).
        let iter_pstack = in_pstack.clone();
        for laidx in in_laidx..parser.lexemes.len() + 1 {
            if Instant::now() >= finish_by {
                break;
            }
            for (st_i, st) in iter_pstack.iter().enumerate().rev() {
                match parser.stable.action(*st, parser.next_tidx(laidx)) {
                    Action::Error => (),
                    _ => {
                        let mut rprs = Vec::with_capacity(laidx - in_laidx);
                        // It's often possible that we found a state that will accept the lexeme at
                        // in_laidx, at which point there are no repairs the user can make which will
                        // emulate this panic mode (i.e. the list of actions they are advised to take
                        // will be empty). There isn't much we can do about this.
                        for j in in_laidx..laidx {
                            rprs.push(ParseRepair::Delete(parser.next_lexeme(j)));
                        }
                        in_pstack.drain(st_i + 1..);
                        return (laidx, vec![rprs]);
                    }
                }
            }
        }
        return (in_laidx, vec![]);
    }
}
