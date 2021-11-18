use std::{fmt::Debug, hash::Hash};

use indexmap::{
    indexmap,
    map::{Entry, IndexMap},
};

/// Starting at `start_node`, return, in arbitrary order, all least-cost success nodes.
///
/// * `neighbours` takes a node `n` and returns an iterator consisting of all `n`'s neighbouring
/// nodes.
/// * `success` takes a node `n` and returns `true` if it is a success node or `false` otherwise.
///
/// The name of this function isn't entirely accurate: this isn't Dijkstra's original algorithm or
/// one of its well-known variants. However, unlike the astar_all function it doesn't expect a
/// heuristic and it also filters out some duplicates.
pub(crate) fn dijkstra<N, FM, FN, FS>(
    start_node: N,
    neighbours: FN,
    merge: FM,
    success: FS,
) -> Vec<N>
where
    N: Debug + Clone + Hash + Eq + PartialEq,
    FN: Fn(bool, &N, &mut Vec<(u16, N)>) -> bool,
    FM: Fn(&mut N, N),
    FS: Fn(&N) -> bool,
{
    let mut scs_nodes = Vec::new();
    let mut todo: Vec<IndexMap<N, N>> = vec![indexmap![start_node.clone() => start_node]];
    let mut c: u16 = 0;
    let mut next = Vec::new();
    loop {
        if todo[usize::from(c)].is_empty() {
            c = c.checked_add(1).unwrap();
            if usize::from(c) == todo.len() {
                return Vec::new();
            }
            continue;
        }

        let n = todo[usize::from(c)].pop().unwrap().1;
        if success(&n) {
            scs_nodes.push(n);
            break;
        }

        if !neighbours(true, &n, &mut next) {
            return Vec::new();
        }
        for (nbr_cost, nbr) in next.drain(..) {
            let off = usize::from(nbr_cost);
            todo.resize(todo.len() + off + 1, IndexMap::new());
            match todo[off].entry(nbr.clone()) {
                Entry::Vacant(e) => {
                    e.insert(nbr);
                }
                Entry::Occupied(mut e) => {
                    merge(e.get_mut(), nbr);
                }
            }
        }
    }

    let mut scs_todo = todo
        .drain(usize::from(c)..usize::from(c) + 1)
        .next()
        .unwrap();
    while !scs_todo.is_empty() {
        let n = scs_todo.pop().unwrap().1;
        if success(&n) {
            scs_nodes.push(n);
            continue;
        }
        if !neighbours(false, &n, &mut next) {
            return Vec::new();
        }
        for (nbr_cost, nbr) in next.drain(..) {
            if nbr_cost == c {
                match scs_todo.entry(nbr.clone()) {
                    Entry::Vacant(e) => {
                        e.insert(nbr);
                    }
                    Entry::Occupied(mut e) => {
                        merge(e.get_mut(), nbr);
                    }
                }
            }
        }
    }

    scs_nodes
}
