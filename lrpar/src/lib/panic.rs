use std::{fmt::Debug, hash::Hash, time::Instant};

use lrtable::{Action, StIdx};
use num_traits::{AsPrimitive, PrimInt, Unsigned};

use crate::parser::{AStackType, ParseRepair, Parser, Recoverer};

struct Panic;

pub(crate) fn recoverer<
    'a,
    StorageT: 'static + Debug + Hash + PrimInt + Unsigned,
    ActionT: 'static
>(
    _: &'a Parser<StorageT, ActionT>
) -> Box<dyn Recoverer<StorageT, ActionT> + 'a>
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    Box::new(Panic)
}

impl<StorageT: 'static + Debug + Hash + PrimInt + Unsigned, ActionT: 'static>
    Recoverer<StorageT, ActionT> for Panic
where
    usize: AsPrimitive<StorageT>,
    u32: AsPrimitive<StorageT>
{
    fn recover(
        &self,
        finish_by: Instant,
        parser: &Parser<StorageT, ActionT>,
        in_laidx: usize,
        in_pstack: &mut Vec<StIdx>,
        _: &mut Vec<AStackType<ActionT, StorageT>>,
        _: &mut Vec<usize>
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
        (in_laidx, vec![])
    }
}
