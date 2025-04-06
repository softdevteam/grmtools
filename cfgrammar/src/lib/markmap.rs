use quote::{quote, ToTokens};
use std::borrow::Borrow;

#[repr(u8)]
#[derive(Clone, Copy)]
enum Mark {
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

#[repr(u8)]
#[derive(Clone, Copy)]
pub enum MergeBehavior {
    Theirs = 1 << 0,
    Ours = 1 << 1,
    // Only one of Ours or Theirs, never both but sometimes neither.
    // The default if no merge behavior is set.
    MutuallyExclusive = 1 << 2,
}

#[derive(Debug)]
pub enum MergeError<K> {
    // Both theirs and ours were some.
    Exclusivity(K),
}

#[derive(Debug, PartialEq, Eq)]
pub struct MarkMap<K, V> {
    contents: Vec<(K, u16, Option<V>)>,
}

pub enum Entry<'a, K, V> {
    Occupied(OccupiedEntry<'a, K, V>),
    Vacant(VacantEntry<'a, K, V>),
}

impl<'a, K: Ord + Clone, V> VacantEntry<'a, K, V> {
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

    pub fn key(&self) -> &K {
        &self.key
    }
}

impl<K: Ord, V> OccupiedEntry<'_, K, V> {
    pub fn get(&self) -> &V {
        self.map.contents[self.pos].2.as_ref().unwrap()
    }

    pub fn insert(self, val: V) -> V {
        let v: Option<V> = self.map.contents[self.pos].2.take();
        self.map.contents[self.pos].2 = Some(val);
        v.unwrap()
    }

    pub fn get_mark(&self) -> u16 {
        self.map.contents[self.pos].1
    }

    pub fn mark_used(&mut self) {
        let repr = self.map.contents[self.pos].1 | Mark::Used.repr();
        self.map.contents[self.pos].1 = repr;
    }

    pub fn is_used(&self) -> bool {
        self.map.contents[self.pos].1 & Mark::Used.repr() != 0
    }

    pub fn mark_required(&mut self) {
        let repr = self.map.contents[self.pos].1 | Mark::Required.repr();
        self.map.contents[self.pos].1 = repr;
    }

    pub fn is_required(&self) -> bool {
        self.map.contents[self.pos].1 & Mark::Required.repr() != 0
    }

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

pub struct OccupiedEntry<'a, K, V> {
    pos: usize,
    map: &'a mut MarkMap<K, V>,
}

pub struct VacantEntry<'a, K, V> {
    pos: Result<usize, usize>,
    key: K,
    map: &'a mut MarkMap<K, V>,
}

impl<K: Ord + Clone, V> MarkMap<K, V> {
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        MarkMap { contents: vec![] }
    }

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

    #[cfg(test)]
    pub(crate) fn get_mark(&mut self, key: &K) -> Option<u16> {
        let pos = self.contents.binary_search_by(|(k, _, _)| k.cmp(key));
        match pos {
            Ok(pos) => Some(self.contents[pos].1),
            Err(_) => None,
        }
    }

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

    pub fn is_required(&self, key: &K) -> bool {
        let pos = self.contents.binary_search_by(|(k, _, _)| k.cmp(key));
        match pos {
            Ok(pos) => self.contents[pos].1 & Mark::Required.repr() != 0,
            _ => false,
        }
    }

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

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Ord + ?Sized,
    {
        self.get(key).is_some()
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        let pos = self.contents.binary_search_by(|(k, _, _)| k.cmp(key));
        match pos {
            Err(_) => None,
            Ok(pos) => self.contents.remove(pos).2,
        }
    }

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
    pub fn merge_from(&mut self, other: Self) -> Result<(), MergeError<K>> {
        for (their_key, their_mark, their_val) in other.contents {
            let pos = self.contents.binary_search_by(|x| x.0.cmp(&their_key));
            match pos {
                Ok(pos) => {
                    let (_, my_mark, my_val) = &self.contents[pos];
                    let theirs_mark = Mark::MergeBehavior(MergeBehavior::Theirs).repr();
                    let ours_mark = Mark::MergeBehavior(MergeBehavior::Ours).repr();
                    let exclusive_mark =
                        Mark::MergeBehavior(MergeBehavior::MutuallyExclusive).repr();
                    let merge_behavior = (my_mark & exclusive_mark)
                        | (my_mark & ours_mark)
                        | (my_mark & theirs_mark);
                    if merge_behavior == exclusive_mark || merge_behavior == 0 {
                        if my_val.is_some() && their_val.is_some() {
                            return Err(MergeError::Exclusivity(their_key.clone()));
                        } else if my_val.is_none() {
                            self.contents[pos].2 = their_val;
                            return Ok(());
                        }
                    }
                    if merge_behavior == theirs_mark && their_val.is_some() {
                        self.contents[pos].2 = their_val;
                        return Ok(());
                    }

                    if merge_behavior == ours_mark && my_val.is_none() {
                        self.contents[pos].2 = their_val;
                        return Ok(());
                    }
                }
                Err(pos) => {
                    self.contents
                        .insert(pos, (their_key, their_mark, their_val));
                }
            }
        }
        Ok(())
    }

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
}

impl<K, V> ToTokens for MarkMap<K, V>
where
    K: ToTokens,
    V: ToTokens,
{
    fn to_tokens(&self, toks: &mut proc_macro2::TokenStream) {
        for (x, y) in self {
            toks.extend(quote! { (#x, #y) });
        }
    }
}

pub struct MarkMapIter<K, V> {
    map: MarkMap<K, V>,
}

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

pub struct MarkMapIterRef<'a, K, V> {
    pos: usize,
    map: &'a MarkMap<K, V>,
}

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

impl<'a, K, V> IntoIterator for &'a MarkMap<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = MarkMapIterRef<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        MarkMapIterRef { pos: 0, map: self }
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
            let theirs = MarkMap::new();
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
}
