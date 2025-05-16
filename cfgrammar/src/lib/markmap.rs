use std::borrow::Borrow;
use std::error::Error;
use std::fmt;

/// MarkMap is a key value data structure that uses an API similar to that of
/// `std::collections::HashMap` and `std::collections::BTreeMap`.
///
/// The current implementation is based on a sorted `Vec` is not optimized for
/// storing large number of items.
///
/// On top of the familiar `std::collections` API it has a few additions:
///
/// * Marking a key with a condition.
/// * Marking a key with a merge behavior.
/// * A merge operator.
///
/// The current *conditions* are [`Used`](MarkMap::mark_used) and [`Required`](MarkMap::mark_required).
///
/// The available merge behaviors are [`Theirs`](MergeBehavior::Theirs), [`Ours`](MergeBehavior::Ours),
/// and [`MutuallyExclusive`](MergeBehavior::MutuallyExclusive).
///
/// Merge behaviors configure how the merge operator handles cases where both `MarkMaps` being merged
/// contain a particular key.
#[derive(Debug, PartialEq, Eq)]
#[doc(hidden)]
pub struct MarkMap<K, V> {
    default_merge_behavior: MergeBehavior,
    contents: Vec<(K, u16, Option<V>)>,
}

/// Defines the merge behavior for a single key in the markmap.
#[repr(u8)]
#[derive(Clone, Copy, Eq, PartialEq, Debug)]
#[doc(hidden)]
pub enum MergeBehavior {
    /// The value in `self` takes precedence.
    Theirs = 1 << 0,
    /// The value in `other` takes precedence.
    Ours = 1 << 1,
    /// It is an error if the key is present in both `MarkMaps`.
    /// This is the default if no merge behavior is set.
    MutuallyExclusive = 1 << 2,
}

/// Conflicting values were present while merging, and the
/// merge behavior did not specify a means to resolve them.
#[derive(Debug)]
#[doc(hidden)]
pub enum MergeError<K, V> {
    // Contains the key which was present in both, and the value which was present in `Theirs`.
    Exclusivity(K, V),
}

impl<K: fmt::Debug, V: fmt::Debug> Error for MergeError<K, V> {}

impl<K: fmt::Debug, V> fmt::Display for MergeError<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Exclusivity(k, _) => {
                write!(f, "Merge behavior forbids overriding key: {:?}", k)
            }
        }
    }
}

/// A view into a single entry in a `MarkMap`, which may either be vacant or occupied.
#[doc(hidden)]
pub enum Entry<'a, K, V> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

#[repr(u8)]
#[derive(Clone, Copy)]
#[doc(hidden)]
enum Mark {
    // There are some other interesting marks that could be added based on row polymorphic records.
    // Marks such as `Prohibited` could be used to prove disjointedness.
    Used,
    Required,
    MergeBehavior(MergeBehavior),
}

impl Mark {
    fn repr(self) -> u16 {
        match self {
            Self::Used => 1 << 0,
            Self::Required => 1 << 1,
            Self::MergeBehavior(mb) => (1 << 2) | ((mb as u16) << 8),
        }
    }
}

impl<'a, K: Ord + Clone, V> VacantEntry<'a, K, V> {
    /// Inserts a value into a vacant entry.
    /// Returns a mutable reference to value inserted.
    pub fn insert(self, val: V) -> &'a mut V {
        match self.pos {
            Ok(pos) => {
                self.map.contents[pos].2 = Some(val);
                self.map.contents[pos].2.as_mut().unwrap()
            }
            Err(pos) => {
                self.map.contents.insert(pos, (self.key, 0, Some(val)));
                self.map.contents[pos].2.as_mut().unwrap()
            }
        }
    }

    /// Inserts a value into a vacant entry.
    /// Returns an occupied entry.
    pub fn insert_entry(self, val: V) -> OccupiedEntry<'a, K, V> {
        match self.pos {
            Ok(pos) => {
                self.map.contents[pos].2 = Some(val);
                OccupiedEntry { pos, map: self.map }
            }
            Err(pos) => {
                self.map.contents.insert(pos, (self.key, 0, Some(val)));
                OccupiedEntry { pos, map: self.map }
            }
        }
    }

    /// Marks the key associated with this entry as required.
    pub fn mark_required(&mut self) {
        match self.pos {
            Ok(pos) => {
                let repr = self.map.contents[pos].1;
                self.map.contents[pos].1 = repr | Mark::Required.repr();
            }
            Err(pos) => {
                self.map
                    .contents
                    .insert(pos, (self.key.clone(), Mark::Required.repr(), None));
                self.pos = Ok(pos)
            }
        }
    }

    /// Sets the merge behavior for the key associated with this entry.
    pub fn set_merge_behavior(&mut self, mb: MergeBehavior) {
        match self.pos {
            Ok(pos) => {
                let merge_reprs = Mark::MergeBehavior(MergeBehavior::MutuallyExclusive).repr()
                    | Mark::MergeBehavior(MergeBehavior::Ours).repr()
                    | Mark::MergeBehavior(MergeBehavior::Theirs).repr();
                let mut repr = self.map.contents[pos].1;
                // Zap just the MergeBehavior bits.
                repr ^= repr & merge_reprs;
                repr |= Mark::MergeBehavior(mb).repr();
                self.map.contents[pos].1 = repr;
            }
            Err(pos) => {
                self.map.contents.insert(
                    pos,
                    (self.key.clone(), Mark::MergeBehavior(mb).repr(), None),
                );
                self.pos = Ok(pos)
            }
        }
    }

    /// Returns the key associated with this entry.
    pub fn key(&self) -> &K {
        &self.key
    }
}

impl<K: Ord, V> OccupiedEntry<'_, K, V> {
    /// Returns the value associated with this entry.
    pub fn get(&self) -> &V {
        self.map.contents[self.pos].2.as_ref().unwrap()
    }

    /// Sets the value of the entry, and returns the entry’s old value.
    pub fn insert(self, val: V) -> V {
        let v: Option<V> = self.map.contents[self.pos].2.take();
        self.map.contents[self.pos].2 = Some(val);
        v.unwrap()
    }

    /// Gets the mark associated with the key of this entry.
    pub fn get_mark(&self) -> u16 {
        self.map.contents[self.pos].1
    }

    /// Marks the key associated with this entry as used.
    pub fn mark_used(&mut self) {
        let repr = self.map.contents[self.pos].1 | Mark::Used.repr();
        self.map.contents[self.pos].1 = repr;
    }

    /// Returns whether the key associated with this entry is used.
    pub fn is_used(&self) -> bool {
        self.map.contents[self.pos].1 & Mark::Used.repr() != 0
    }

    /// Marks the key associated with this entry as required.
    pub fn mark_required(&mut self) {
        let repr = self.map.contents[self.pos].1 | Mark::Required.repr();
        self.map.contents[self.pos].1 = repr;
    }

    /// Returns whether the key associated with this entry is required.
    pub fn is_required(&self) -> bool {
        self.map.contents[self.pos].1 & Mark::Required.repr() != 0
    }

    /// Sets the merge behavior for the key associated with this entry.
    pub fn set_merge_behavior(&mut self, mb: MergeBehavior) {
        let mut repr = self.map.contents[self.pos].1;
        let merge_reprs = Mark::MergeBehavior(MergeBehavior::MutuallyExclusive).repr()
            | Mark::MergeBehavior(MergeBehavior::Ours).repr()
            | Mark::MergeBehavior(MergeBehavior::Theirs).repr();
        // Zap just the MergeBehavior bits.
        repr ^= repr & merge_reprs;
        repr |= Mark::MergeBehavior(mb).repr();
        self.map.contents[self.pos].1 = repr;
    }
}

/// A view into an occupied entry in a `MarkMap`. It is part of the `Entry` enum.
#[doc(hidden)]
pub struct OccupiedEntry<'a, K, V> {
    pos: usize,
    map: &'a mut MarkMap<K, V>,
}

/// A view into a vacant entry in a `MarkMap`. It is part of the `Entry` enum.
#[doc(hidden)]
pub struct VacantEntry<'a, K, V> {
    // The values of the `pos` result imply:
    // * When `Ok(pos)` the key was found at `pos`, and it's value was `None`.
    // * When `Err(pos)` the key was not found at `pos`.
    pos: Result<usize, usize>,
    key: K,
    map: &'a mut MarkMap<K, V>,
}

impl<K: Ord + Clone, V> MarkMap<K, V> {
    /// Returns a new `MarkMap`.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        MarkMap {
            default_merge_behavior: MergeBehavior::MutuallyExclusive,
            contents: vec![],
        }
    }

    /// Inserts a `key` `value` pair.
    pub fn insert(&mut self, key: K, val: V) -> Option<V> {
        let pos = self.contents.binary_search_by(|(k, _, _)| k.cmp(&key));
        match pos {
            Ok(pos) => {
                let ret = self.contents[pos].2.take();
                self.contents[pos].2 = Some(val);
                ret
            }
            Err(pos) => {
                self.contents.insert(pos, (key, 0, Some(val)));
                None
            }
        }
    }

    /// Gets the raw mark value, for testing purposes.
    #[cfg(test)]
    pub(crate) fn get_mark(&mut self, key: &K) -> Option<u16> {
        let pos = self.contents.binary_search_by(|(k, _, _)| k.cmp(key));
        match pos {
            Ok(pos) => Some(self.contents[pos].1),
            Err(_) => None,
        }
    }

    /// Marks `key` as used.
    pub fn mark_used(&mut self, key: &K) {
        let pos = self.contents.binary_search_by(|(k, _, _)| k.cmp(key));
        match pos {
            Ok(pos) => {
                let mut repr = self.contents[pos].1;
                repr |= Mark::Used.repr();
                self.contents[pos].1 = repr;
            }
            Err(pos) => {
                self.contents
                    .insert(pos, (key.to_owned(), Mark::Used.repr(), None));
            }
        }
    }

    /// Marks `key` as a required value.
    pub fn mark_required(&mut self, key: &K) {
        let pos = self.contents.binary_search_by(|(k, _, _)| k.cmp(key));
        match pos {
            Ok(pos) => {
                let mut repr = self.contents[pos].1;
                repr |= Mark::Required.repr();
                self.contents[pos].1 = repr;
            }
            Err(pos) => {
                self.contents
                    .insert(pos, (key.to_owned(), Mark::Required.repr(), None));
            }
        }
    }

    /// Returns whether `key` is required.
    pub fn is_required(&self, key: &K) -> bool {
        let pos = self.contents.binary_search_by(|(k, _, _)| k.cmp(key));
        match pos {
            Ok(pos) => self.contents[pos].1 & Mark::Required.repr() != 0,
            _ => false,
        }
    }

    pub fn set_default_merge_behavior(&mut self, mb: MergeBehavior) {
        self.default_merge_behavior = mb;
    }

    /// Sets the merge behavior for `key`.
    pub fn set_merge_behavior(&mut self, key: &K, mb: MergeBehavior) {
        let pos = self.contents.binary_search_by(|(k, _, _)| k.cmp(key));
        match pos {
            Ok(pos) => {
                let mut repr = self.contents[pos].1;
                let merge_reprs = Mark::MergeBehavior(MergeBehavior::MutuallyExclusive).repr()
                    | Mark::MergeBehavior(MergeBehavior::Ours).repr()
                    | Mark::MergeBehavior(MergeBehavior::Theirs).repr();
                // Zap just the MergeBehavior bits.
                repr ^= repr & merge_reprs;
                repr |= Mark::MergeBehavior(mb).repr();
                self.contents[pos].1 = repr;
            }
            Err(pos) => {
                self.contents
                    .insert(pos, (key.to_owned(), Mark::MergeBehavior(mb).repr(), None));
            }
        }
    }

    /// Returns a `Some(value)` associated with `key` if present otherwise `None`.
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        let pos = self.contents.binary_search_by(|(k, _, _)| {
            let q: &Q = k.borrow();
            q.cmp(key)
        });
        match pos {
            Err(_) => None,
            Ok(pos) => self.contents[pos].2.as_ref(),
        }
    }

    /// Returns true if the `MarkMap` contains `key` otherwise false.
    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.get(key).is_some()
    }

    /// Removes `key` from the `MarkMap` and returns the previous value when present.
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let pos = self.contents.binary_search_by(|(k, _, _)| k.cmp(key));
        match pos {
            Err(_) => None,
            Ok(pos) => self.contents.remove(pos).2,
        }
    }

    /// Returns an `Entry` for `key`.
    pub fn entry(&mut self, key: K) -> Entry<K, V> {
        let pos = self.contents.binary_search_by(|(k, _, _)| k.cmp(&key));
        match pos {
            Err(pos) => Entry::Vacant(VacantEntry {
                pos: Err(pos),
                key,
                map: self,
            }),
            Ok(pos) => {
                if self.contents[pos].2.is_some() {
                    Entry::Occupied(OccupiedEntry { pos, map: self })
                } else {
                    Entry::Vacant(VacantEntry {
                        pos: Ok(pos),
                        key,
                        map: self,
                    })
                }
            }
        }
    }

    /// Merges items from `other` into `self`, for each value it checks the `MergeBehavior` of self.
    /// The `MergeBehavior` of other is not considered.
    ///
    /// * `MergeBehavior::Ours`: If a value is set in `other`, a value set in self takes precedence.
    /// * `MergeBehavior::Theirs`: if a value in `other` `is_some()`, then it will overwrite values in self.
    /// * `MergeBehavior::MutuallyExclusive` If a value is set in `other`, that value should be `None` in self.
    /// * If `MergeBehavior` is unset, defaults to `MergeBehavior::MutuallyExclusive`.
    ///
    /// For the behavior of exclusive or mark the behavior as also `Mark::Required`, then after merge call `missing()`
    /// to check all required values.
    pub fn merge_from<U>(&mut self, mut other: MarkMap<K, U>) -> Result<(), MergeError<K, Box<V>>>
    where
        U: Into<V>,
    {
        for (their_key, their_mark, their_val) in other.contents.drain(..) {
            let pos = self.contents.binary_search_by(|x| x.0.cmp(&their_key));
            match pos {
                Ok(pos) => {
                    let (_, my_mark, my_val) = &mut self.contents[pos];
                    let theirs_mark = Mark::MergeBehavior(MergeBehavior::Theirs).repr();
                    let ours_mark = Mark::MergeBehavior(MergeBehavior::Ours).repr();
                    let exclusive_mark =
                        Mark::MergeBehavior(MergeBehavior::MutuallyExclusive).repr();
                    let mut merge_behavior = (*my_mark & exclusive_mark)
                        | (*my_mark & ours_mark)
                        | (*my_mark & theirs_mark);
                    if merge_behavior == 0 {
                        merge_behavior = Mark::MergeBehavior(self.default_merge_behavior).repr();
                    }
                    if merge_behavior == exclusive_mark {
                        // If only clippy could convince me and the borrow checker this is actually unnecessary.
                        #[allow(clippy::unnecessary_unwrap)]
                        if my_val.is_some() && their_val.is_some() {
                            return Err(MergeError::Exclusivity(
                                their_key,
                                Box::new(their_val.unwrap().into()),
                            ));
                        } else if my_val.is_none() {
                            *my_val = their_val.map(|u| u.into());
                        }
                    } else if merge_behavior == theirs_mark && their_val.is_some()
                        || merge_behavior == ours_mark && my_val.is_none()
                    {
                        *my_mark = their_mark;
                        *my_val = their_val.map(|u| u.into());
                    }
                }
                Err(pos) => {
                    self.contents
                        .insert(pos, (their_key, their_mark, their_val.map(|u| u.into())));
                }
            }
        }
        Ok(())
    }

    /// Returns whether `key` has been marked as used.
    pub fn is_used<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        if let Ok(pos) = self.contents.binary_search_by(|x| {
            let k: &Q = x.0.borrow();
            k.borrow().cmp(key)
        }) {
            self.contents[pos].1 & Mark::Used.repr() != 0
        } else {
            false
        }
    }

    /// Returns a `Vec` containing all the keys that are not marked as used.
    pub fn unused(&self) -> Vec<K> {
        let mut ret = Vec::new();
        for (k, mark, v) in &self.contents {
            let used_mark = Mark::Used.repr();
            if v.is_some() && mark & used_mark == 0 {
                ret.push(k.to_owned())
            }
        }
        ret
    }

    /// Returns a `Vec` containing all the keys that are marked as required,
    /// but have values that are not present in the `MarkMap`.
    pub fn missing(&self) -> Vec<&K> {
        let mut ret = Vec::new();
        for (k, mark, v) in &self.contents {
            let required_mark = Mark::Required.repr();
            if v.is_none() && mark & required_mark != 0 {
                ret.push(k)
            }
        }
        ret
    }

    /// Returns an `Iterator` over all the keys of the `MarkMap`.
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys { pos: 0, map: self }
    }
}

/// Iterator over the owned keys and values of a `MarkMap`.
#[doc(hidden)]
pub struct MarkMapIter<K, V> {
    map: MarkMap<K, V>,
}

#[doc(hidden)]
impl<K, V> Iterator for MarkMapIter<K, V> {
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        if !self.map.contents.is_empty() {
            let (k, _, v) = self.map.contents.swap_remove(0);
            v.map(|v| (k, v))
        } else {
            None
        }
    }
}

/// Iterator over references to keys and values of a `MarkMap`.
#[doc(hidden)]
pub struct MarkMapIterRef<'a, K, V> {
    pos: usize,
    map: &'a MarkMap<K, V>,
}

#[doc(hidden)]
impl<'a, K, V> Iterator for MarkMapIterRef<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((k, _, v)) = self.map.contents.get(self.pos) {
            self.pos += 1;
            v.as_ref().map(|v| (k, v))
        } else {
            None
        }
    }
}

#[doc(hidden)]
impl<'a, K, V> IntoIterator for &'a MarkMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = MarkMapIterRef<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        MarkMapIterRef { pos: 0, map: self }
    }
}

/// Iterator over references to keys and values of a `MarkMap`.
#[doc(hidden)]
pub struct Keys<'a, K, V> {
    pos: usize,
    map: &'a MarkMap<K, V>,
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.pos >= self.map.contents.len() {
                return None;
            }
            let pos = self.pos;
            self.pos += 1;
            if self.map.contents[pos].2.is_some() {
                return Some(&self.map.contents[pos].0);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_insert_get_remove() {
        let mut mm = MarkMap::new();
        mm.insert("a", "test");
        assert_eq!(mm.get(&"a"), Some(&"test"));
        assert_eq!(mm.remove(&"a"), Some("test"));
        assert_eq!(mm.get(&"a"), None);
    }

    #[test]
    fn test_entry_occupied() {
        let mut mm = MarkMap::new();
        mm.insert("a", "test");
        assert!(!mm.is_required(&"a"));
        assert!(!mm.is_used(&"a"));
        let ent = mm.entry("a");
        match ent {
            Entry::Occupied(mut o) => {
                assert!(!o.is_required());
                assert!(!o.is_used());
                o.mark_used();
                assert!(o.is_used());
                assert!(!o.is_required());
                o.mark_required();
                assert!(o.is_required());
                assert!(o.is_used());
            }
            Entry::Vacant(_) => {
                panic!("Expected occupied entry");
            }
        }
        assert!(mm.is_required(&"a"));
        assert!(mm.is_used(&"a"));
    }

    #[test]
    fn test_entry_vacant() {
        let mut mm = MarkMap::new();
        mm.insert("a", "test");
        let ent = mm.entry("b");
        match ent {
            Entry::Occupied(_) => {
                panic!("Expected vacant entry");
            }
            Entry::Vacant(v) => {
                v.insert("test b");
            }
        }
    }

    #[test]
    fn test_mark() {
        let mut mm = MarkMap::new();
        assert!(mm.insert("a", "test").is_none());
        mm.mark_used(&"a");
        mm.set_merge_behavior(&"b", MergeBehavior::MutuallyExclusive);
        assert_eq!(mm.get_mark(&"a"), Some(Mark::Used.repr()));
        assert_eq!(
            mm.get_mark(&"b"),
            Some(Mark::MergeBehavior(MergeBehavior::MutuallyExclusive).repr())
        );
        assert_eq!(mm.get_mark(&"c"), None);
        assert_eq!(mm.get(&"a"), Some(&"test"));
        assert_eq!(mm.insert("a", "changed"), Some("test"));
        assert_eq!(mm.get(&"b"), None);
        assert_eq!(mm.insert("b", "added"), None);
        assert_eq!(
            mm.get_mark(&"b"),
            Some(Mark::MergeBehavior(MergeBehavior::MutuallyExclusive).repr())
        );
        assert_eq!(mm.get(&"a"), Some(&"changed"));
        assert_eq!(mm.get(&"c"), None);
    }

    #[test]
    fn test_mark_stable() {
        let mut mm: MarkMap<&str, &str> = MarkMap::new();
        mm.mark_used(&"a");
        assert_eq!(mm.get_mark(&"a"), Some(Mark::Used.repr()));
        mm.mark_required(&"a");
        assert_eq!(
            mm.get_mark(&"a"),
            Some(Mark::Used.repr() | Mark::Required.repr())
        );
        mm.set_merge_behavior(&"a", MergeBehavior::MutuallyExclusive);
        assert_eq!(
            mm.get_mark(&"a"),
            Some(
                Mark::Used.repr()
                    | Mark::Required.repr()
                    | Mark::MergeBehavior(MergeBehavior::MutuallyExclusive).repr()
            )
        );
        mm.set_merge_behavior(&"a", MergeBehavior::Theirs);
        assert_eq!(
            mm.get_mark(&"a"),
            Some(
                Mark::Used.repr()
                    | Mark::Required.repr()
                    | Mark::MergeBehavior(MergeBehavior::Theirs).repr()
            )
        );
        mm.set_merge_behavior(&"a", MergeBehavior::Ours);
        assert_eq!(
            mm.get_mark(&"a"),
            Some(
                Mark::Used.repr()
                    | Mark::Required.repr()
                    | Mark::MergeBehavior(MergeBehavior::Ours).repr()
            )
        );
    }

    #[test]
    fn test_unused() {
        {
            let mut mm = MarkMap::new();
            assert!(mm.insert("a", "test").is_none());
            mm.mark_used(&"a");
            assert_eq!(mm.get_mark(&"a"), Some(Mark::Used.repr()));
            let empty: &[&String] = &[];
            assert_eq!(mm.unused().as_slice(), empty);
        }

        {
            let mut mm = MarkMap::new();
            assert!(mm.insert("a", "test").is_none());
            mm.mark_used(&"a");
            assert!(mm.insert("b", "unused").is_none());
            assert_eq!(mm.get_mark(&"a"), Some(Mark::Used.repr()));
            assert_eq!(mm.get_mark(&"b"), Some(0));
            assert_eq!(mm.unused().as_slice(), &["b"]);
        }
    }

    #[test]
    fn test_required() {
        {
            let mut mm = MarkMap::new();
            let empty: &[&String] = &[];
            mm.mark_required(&"a");
            assert!(mm.insert("a", "test").is_none());
            assert_eq!(mm.get_mark(&"a"), Some(Mark::Required.repr()));
            assert_eq!(mm.missing().as_slice(), empty);
        }

        {
            let mut mm = MarkMap::new();
            mm.mark_required(&"a");
            mm.insert("for", "inference");
            assert_eq!(mm.get_mark(&"a"), Some(Mark::Required.repr()));
            assert_eq!(mm.missing().as_slice(), &[&"a"]);
        }
    }

    #[test]
    fn test_merge_empty() {
        {
            let mut ours: MarkMap<&str, &str> = MarkMap::new();
            let theirs: MarkMap<&str, &str> = MarkMap::new();
            assert!(ours.merge_from(theirs).is_ok());
        }
        {
            let mut ours: MarkMap<&str, &str> = MarkMap::new();
            let theirs: MarkMap<&str, &str> = MarkMap::new();
            ours.mark_required(&"a");
            assert!(ours.merge_from(theirs).is_ok());
            assert_eq!(ours.missing().as_slice(), &[&"a"]);
        }

        {
            let mut ours: MarkMap<&str, &str> = MarkMap::new();
            let theirs: MarkMap<&str, &str> = MarkMap::new();
            ours.mark_required(&"a");
            ours.set_merge_behavior(&"a", MergeBehavior::Ours);
            assert!(ours.merge_from(theirs).is_ok());
            assert_eq!(ours.missing().as_slice(), &[&"a"]);
        }

        {
            let mut ours: MarkMap<&str, &str> = MarkMap::new();
            let theirs: MarkMap<&str, &str> = MarkMap::new();
            ours.mark_required(&"a");
            ours.set_merge_behavior(&"a", MergeBehavior::Theirs);
            assert!(ours.merge_from(theirs).is_ok());
            assert_eq!(ours.missing().as_slice(), &[&"a"]);
        }
    }

    #[test]
    fn test_merge_conflict() {
        {
            let mut ours = MarkMap::new();
            let mut theirs = MarkMap::new();
            ours.insert("a", "ours");
            ours.set_merge_behavior(&"a", MergeBehavior::MutuallyExclusive);
            theirs.insert("a", "theirs");
            assert!(ours.merge_from(theirs).is_err());
            assert_eq!(ours.get(&"a"), Some(&"ours"));
        }
        {
            // Default behavior should match `MutuallyExclusive`
            let mut ours = MarkMap::new();
            let mut theirs = MarkMap::new();
            ours.insert("a", "ours");
            theirs.insert("a", "theirs");
            assert!(ours.merge_from(theirs).is_err());
            assert_eq!(ours.get(&"a"), Some(&"ours"));
        }
    }

    #[test]
    fn test_merge_ours() {
        {
            let mut ours: MarkMap<&str, &str> = MarkMap::new();
            let mut theirs: MarkMap<&str, &str> = MarkMap::new();
            ours.insert("a", "ours");
            theirs.set_merge_behavior(&"a", MergeBehavior::MutuallyExclusive);
            assert!(ours.merge_from(theirs).is_ok());
            assert_eq!(ours.get(&"a"), Some(&"ours"));
        }
        {
            // Default behavior should match MutuallyExclusive
            let mut ours: MarkMap<&str, &str> = MarkMap::new();
            let theirs: MarkMap<&str, &str> = MarkMap::new();
            ours.insert("a", "ours");
            assert!(ours.merge_from(theirs).is_ok());
            assert_eq!(ours.get(&"a"), Some(&"ours"));
        }

        {
            let mut ours: MarkMap<&str, &str> = MarkMap::new();
            let theirs: MarkMap<&str, &str> = MarkMap::new();
            ours.insert("a", "ours");
            ours.set_merge_behavior(&"a", MergeBehavior::MutuallyExclusive);
            assert!(ours.merge_from(theirs).is_ok());
            assert_eq!(ours.get(&"a"), Some(&"ours"));
        }
        {
            let mut ours = MarkMap::new();
            let mut theirs = MarkMap::new();
            ours.insert("a", "ours");
            ours.set_merge_behavior(&"a", MergeBehavior::Ours);
            theirs.insert("a", "theirs");
            assert!(ours.merge_from(theirs).is_ok());
            assert_eq!(ours.get(&"a"), Some(&"ours"));
        }
    }

    #[test]
    fn test_merge_theirs() {
        {
            let mut ours: MarkMap<&str, &str> = MarkMap::new();
            let mut theirs: MarkMap<&str, &str> = MarkMap::new();
            ours.set_merge_behavior(&"a", MergeBehavior::MutuallyExclusive);
            theirs.insert("a", "theirs");
            assert!(ours.merge_from(theirs).is_ok());
            assert_eq!(ours.get(&"a"), Some(&"theirs"));
        }

        {
            // Should match default behavior.
            let mut ours: MarkMap<&str, &str> = MarkMap::new();
            let mut theirs: MarkMap<&str, &str> = MarkMap::new();
            theirs.insert("a", "theirs");
            assert!(ours.merge_from(theirs).is_ok());
            assert_eq!(ours.get(&"a"), Some(&"theirs"));
        }
        {
            let mut ours = MarkMap::new();
            let mut theirs = MarkMap::new();
            ours.insert("a", "ours");
            ours.set_merge_behavior(&"a", MergeBehavior::Theirs);
            theirs.insert("a", "theirs");
            assert!(ours.merge_from(theirs).is_ok());
            assert_eq!(ours.get(&"a"), Some(&"theirs"));
        }
    }

    #[test]
    fn test_merge_both() {
        {
            let mut ours = MarkMap::new();
            let mut theirs = MarkMap::new();
            ours.insert("a", "ours");
            ours.set_merge_behavior(&"a", MergeBehavior::MutuallyExclusive);
            theirs.insert("b", "theirs");
            theirs.set_merge_behavior(&"b", MergeBehavior::MutuallyExclusive);
            assert!(ours.merge_from(theirs).is_ok());
            assert_eq!(ours.get(&"a"), Some(&"ours"));
            assert_eq!(ours.get(&"b"), Some(&"theirs"));
        }
    }

    #[test]
    fn test_vacant() {
        let mut mm = MarkMap::new();
        let v = mm.entry("a");
        match v {
            Entry::Occupied(_) => {
                panic!("Expected vacant entry");
            }
            Entry::Vacant(v) => {
                let mut o = v.insert_entry("ours");
                o.mark_required();
                o.mark_used();
                assert_eq!(o.get(), &"ours");
                assert!(o.is_required());
                assert!(o.is_used());
            }
        }

        assert_eq!(mm.get(&"a"), Some(&"ours"));
        assert!(mm.is_required(&"a"));
        assert!(mm.is_used(&"a"));
    }

    #[test]
    fn test_merge_many() {
        let mut mm = MarkMap::new();
        mm.insert("a", ());
        mm.insert("b", ());

        let mut mm2 = MarkMap::new();
        mm2.insert("x", ());
        mm2.insert("y", ());

        mm.merge_from(mm2).unwrap();
        assert_eq!(
            mm.keys().cloned().collect::<Vec<_>>(),
            vec!["a", "b", "x", "y"]
        );
    }

    #[test]
    fn test_default_merge_behavior() {
        let mut mm = MarkMap::new();
        mm.set_default_merge_behavior(MergeBehavior::Ours);
        mm.insert("a", "mm");
        mm.insert("b", "mm");
        mm.set_merge_behavior(&"b", MergeBehavior::Theirs);

        let mut mm2 = MarkMap::new();
        mm2.insert("x", "mm2");
        mm2.insert("b", "mm2");
        mm2.insert("a", "mm2");

        mm.merge_from(mm2).unwrap();
        assert_eq!(
            mm.into_iter().collect::<Vec<_>>(),
            vec![(&"a", &"mm"), (&"b", &"mm2"), (&"x", &"mm2")]
        );
    }

    #[test]
    fn test_vacant_entry_required() {
        let mut mm = MarkMap::new();
        // To test the first case we want a marked key with no value associated to it.
        mm.mark_used(&"a");
        let e = mm.entry("a");
        match e {
            Entry::Occupied(_) => panic!("Expected unoccupied entry"),
            Entry::Vacant(mut e) => {
                e.mark_required();
                e.insert_entry("a");
            }
        }
        assert!(mm.is_required(&"a"));
        assert!(mm.is_used(&"a"));
        // For the second case we want an unmarked key with another key in it's binary search pos.
        mm.insert("c", "c");
        let e = mm.entry("b");
        match e {
            Entry::Occupied(_) => panic!("Expected unoccupied entry"),
            Entry::Vacant(mut e) => {
                e.mark_required();
            }
        }
        assert!(mm.is_required(&"b"));
        assert!(!mm.is_required(&"c"));
    }

    #[test]
    fn test_vacant_entry_merge_behavior() {
        let mut mm = MarkMap::new();
        // To test the first case we want a marked key with no value associated to it.
        mm.mark_used(&"a");
        let mut mm2 = MarkMap::new();
        mm2.insert("a", "a2");
        mm2.insert("a", "c2");
        let e = mm.entry("a");
        match e {
            Entry::Occupied(_) => panic!("Expected unoccupied entry"),
            Entry::Vacant(mut e) => {
                e.set_merge_behavior(MergeBehavior::Ours);
                e.insert_entry("a1");
            }
        }
        assert_eq!(
            mm.get_mark(&"a"),
            Some(Mark::MergeBehavior(MergeBehavior::Ours).repr() | Mark::Used.repr())
        );
        // For the second case we want an unmarked key with another key in it's binary search pos.
        mm.insert("c", "c");
        let e = mm.entry("b");
        match e {
            Entry::Occupied(_) => panic!("Expected unoccupied entry"),
            Entry::Vacant(mut e) => {
                e.set_merge_behavior(MergeBehavior::Theirs);
            }
        }
        assert_eq!(
            mm.get_mark(&"b"),
            Some(Mark::MergeBehavior(MergeBehavior::Theirs).repr())
        );
        assert_eq!(mm.get_mark(&"c"), Some(0));
    }
}
