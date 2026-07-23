//! Persistent hash array mapped trie — the O(1)-snapshot map primitive under
//! Grimoire environments (plan §7.1).
//!
//! Structure: a HAMT over the key's 64-bit hash with 5-bit fanout. Branches
//! are bitmap-compressed 32-way nodes; the hash chunks are consumed
//! least-significant-first at shifts `0, 5, …, 60` (13 branch levels cover
//! all 64 bits), after which distinct keys can only share a leaf, which is a
//! collision bucket (`Vec` of pairs).
//!
//! Persistence: every node sits behind an [`Arc`]; `clone` copies the root
//! pointer only, and [`PMap::insert`] / [`PMap::remove`] rebuild exactly the
//! path from the root to the affected leaf, sharing every other subtree with
//! the source map. A snapshot therefore costs O(1) and is immune to later
//! mutation of any other handle.
//!
//! Iteration order is trie order — ascending hash chunks, least-significant
//! chunk first — with full-hash collision buckets ordered by [`PKey`]'s
//! canonical total order. It therefore depends only on the keys present,
//! never on the insertion or scheduling history that built the map.

use std::sync::Arc;

/// Keys carry their own 64-bit hash and a canonical total order.
///
/// The hash must be a pure function of the key's `Eq` identity: equal keys
/// must return equal hashes. `Ord` must be consistent with `Eq`; it is the CGSE
/// tie-break for distinct keys with the same complete hash. Distinct keys may
/// collide; collision-bucket lookup/removal is currently O(b), while insertion
/// performs O(log b) comparisons plus O(b) clone/shift work. Resource-bounding
/// adversarially large buckets is deliberately owned by follow-up `fln-amv.13`.
///
/// `Name` uses its pinned Reference `Name.cmp` order through its `Ord`
/// implementation, never allocation address, insertion order, or randomized
/// hashing.
pub trait PKey: Clone + Eq + Ord {
    fn key_hash(&self) -> u64;
}

/// Bits of hash consumed per branch level.
const BITS: u32 = 5;
/// Mask selecting one `BITS`-wide chunk.
const CHUNK_MASK: u64 = (1 << BITS) - 1;
/// Largest shift at which a branch may exist: chunks at shifts
/// `0, 5, …, 60` cover all 64 hash bits, so two distinct hashes always
/// diverge at some shift `<= MAX_SHIFT`.
const MAX_SHIFT: u32 = 60;
/// Maximum node-path length root→leaf: 13 branch levels plus the leaf.
const MAX_DEPTH: usize = (MAX_SHIFT / BITS) as usize + 2;

/// The `BITS`-wide hash chunk at `shift`. Total (never shifts past the word),
/// though callers only pass `shift <= MAX_SHIFT`.
fn chunk(hash: u64, shift: u32) -> u32 {
    (hash.checked_shr(shift).unwrap_or(0) & CHUNK_MASK) as u32
}

enum Node<K, V> {
    /// Bitmap-compressed branch: bit `i` of `bitmap` is set iff chunk value
    /// `i` is occupied, and `children[popcount(bitmap below bit i)]` is that
    /// child. Invariant: `children.len() == bitmap.count_ones()`, and a
    /// branch reached at shift `s` was built at shift `<= MAX_SHIFT`.
    Branch {
        bitmap: u32,
        children: Vec<Arc<Node<K, V>>>,
    },
    /// All entries whose key hashes to exactly `hash`. Invariant: non-empty,
    /// keys pairwise distinct; entries beyond the first exist only under
    /// full 64-bit hash collision.
    Leaf { hash: u64, entries: Vec<(K, V)> },
}

/// Persistent (immutable, structurally shared) hash map.
///
/// `clone` is O(1) (an `Arc` bump of the root); `insert` and `remove` return
/// new maps sharing all but the rebuilt root-to-leaf path with the receiver.
pub struct PMap<K: PKey, V: Clone> {
    root: Option<Arc<Node<K, V>>>,
    len: usize,
}

impl<K: PKey, V: Clone> PMap<K, V> {
    pub fn new() -> Self {
        PMap { root: None, len: 0 }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let hash = key.key_hash();
        let mut node = self.root.as_ref()?;
        let mut shift = 0u32;
        loop {
            match node.as_ref() {
                Node::Leaf {
                    hash: leaf_hash,
                    entries,
                } => {
                    return if *leaf_hash == hash {
                        entries.iter().find(|(k, _)| k == key).map(|(_, v)| v)
                    } else {
                        None
                    };
                }
                Node::Branch { bitmap, children } => {
                    let bit = 1u32 << chunk(hash, shift);
                    if bitmap & bit == 0 {
                        return None;
                    }
                    let pos = (bitmap & (bit - 1)).count_ones() as usize;
                    node = children.get(pos)?;
                    shift += BITS;
                }
            }
        }
    }

    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Persistent insert: returns the map with `key` bound to `value`,
    /// overwriting any previous binding. The receiver is unchanged.
    pub fn insert(&self, key: K, value: V) -> Self {
        let hash = key.key_hash();
        match &self.root {
            None => PMap {
                root: Some(Arc::new(Node::Leaf {
                    hash,
                    entries: vec![(key, value)],
                })),
                len: 1,
            },
            Some(root) => {
                let (new_root, added) = insert_rec(root, 0, hash, key, value);
                PMap {
                    root: Some(new_root),
                    len: self.len + usize::from(added),
                }
            }
        }
    }

    /// Persistent remove: returns the map without `key`. An absent key
    /// yields an unchanged O(1) clone of the receiver.
    pub fn remove(&self, key: &K) -> Self {
        let hash = key.key_hash();
        match &self.root {
            None => self.clone(),
            Some(root) => match remove_rec(root, 0, hash, key) {
                None => self.clone(),
                Some(new_root) => PMap {
                    root: new_root,
                    len: self.len.saturating_sub(1),
                },
            },
        }
    }

    /// Iterates in deterministic trie order (see the module docs).
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        let mut stack = Vec::with_capacity(MAX_DEPTH);
        if let Some(root) = &self.root {
            stack.push((root.as_ref(), 0usize));
        }
        Iter { stack }
    }

    /// Total node count (branches + leaves); test-only sharing probe.
    #[cfg(test)]
    fn node_count(&self) -> usize {
        fn count<K, V>(node: &Node<K, V>) -> usize {
            match node {
                Node::Leaf { .. } => 1,
                Node::Branch { children, .. } => {
                    1 + children.iter().map(|c| count(c)).sum::<usize>()
                }
            }
        }
        self.root.as_ref().map_or(0, |r| count(r))
    }

    /// Addresses of every node, for pointer-identity sharing checks.
    #[cfg(test)]
    fn node_ptrs(&self) -> Vec<*const ()> {
        fn walk<K, V>(node: &Arc<Node<K, V>>, out: &mut Vec<*const ()>) {
            out.push(Arc::as_ptr(node).cast());
            if let Node::Branch { children, .. } = node.as_ref() {
                for child in children {
                    walk(child, out);
                }
            }
        }
        let mut out = Vec::new();
        if let Some(root) = &self.root {
            walk(root, &mut out);
        }
        out
    }
}

impl<K: PKey, V: Clone> Clone for PMap<K, V> {
    /// O(1): copies the root `Arc` and the cached length.
    fn clone(&self) -> Self {
        PMap {
            root: self.root.clone(),
            len: self.len,
        }
    }
}

impl<K: PKey, V: Clone> Default for PMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: PKey + std::fmt::Debug, V: Clone + std::fmt::Debug> std::fmt::Debug for PMap<K, V> {
    /// Renders entries in iteration (trie) order.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<K: PKey, V: Clone + PartialEq> PartialEq for PMap<K, V> {
    /// Map equality: same key set, equal values — independent of build order
    /// and of bucket order under hash collisions. Shared roots short-circuit.
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        match (&self.root, &other.root) {
            (None, None) => true,
            (Some(a), Some(b)) => {
                Arc::ptr_eq(a, b) || self.iter().all(|(k, v)| other.get(k) == Some(v))
            }
            _ => false,
        }
    }
}

impl<K: PKey, V: Clone + Eq> Eq for PMap<K, V> {}

/// Rebuilds the path from `node` for an insert at `shift`; returns the new
/// subtree and whether the key was new (vs. an overwrite).
fn insert_rec<K: PKey, V: Clone>(
    node: &Arc<Node<K, V>>,
    shift: u32,
    hash: u64,
    key: K,
    value: V,
) -> (Arc<Node<K, V>>, bool) {
    match node.as_ref() {
        Node::Leaf {
            hash: leaf_hash,
            entries,
        } => {
            if *leaf_hash == hash {
                let mut new_entries = entries.clone();
                let added = match new_entries.binary_search_by(|(stored, _)| stored.cmp(&key)) {
                    Ok(pos) => {
                        // `PKey` requires `Ord` to be consistent with `Eq`; keep
                        // the already-published key object and replace only its
                        // value so overwrites cannot perturb bucket identity.
                        debug_assert!(new_entries[pos].0 == key);
                        new_entries[pos].1 = value;
                        false
                    }
                    Err(pos) => {
                        new_entries.insert(pos, (key, value));
                        true
                    }
                };
                (
                    Arc::new(Node::Leaf {
                        hash,
                        entries: new_entries,
                    }),
                    added,
                )
            } else {
                (
                    split_leaf(Arc::clone(node), *leaf_hash, shift, hash, key, value),
                    true,
                )
            }
        }
        Node::Branch { bitmap, children } => {
            let bit = 1u32 << chunk(hash, shift);
            let pos = (bitmap & (bit - 1)).count_ones() as usize;
            if bitmap & bit == 0 {
                let new_leaf = Arc::new(Node::Leaf {
                    hash,
                    entries: vec![(key, value)],
                });
                let mut new_children = Vec::with_capacity(children.len() + 1);
                new_children.extend(children.iter().take(pos).cloned());
                new_children.push(new_leaf);
                new_children.extend(children.iter().skip(pos).cloned());
                (
                    Arc::new(Node::Branch {
                        bitmap: bitmap | bit,
                        children: new_children,
                    }),
                    true,
                )
            } else {
                let (new_child, added) = match children.get(pos) {
                    Some(child) => insert_rec(child, shift + BITS, hash, key, value),
                    // Unreachable by the bitmap/children invariant; repair
                    // with a fresh leaf rather than panic.
                    None => (
                        Arc::new(Node::Leaf {
                            hash,
                            entries: vec![(key, value)],
                        }),
                        true,
                    ),
                };
                let mut new_children = children.clone();
                match new_children.get_mut(pos) {
                    Some(slot) => *slot = new_child,
                    None => new_children.push(new_child),
                }
                (
                    Arc::new(Node::Branch {
                        bitmap: *bitmap,
                        children: new_children,
                    }),
                    added,
                )
            }
        }
    }
}

/// Replaces a leaf whose hash differs from the incoming key's: builds the
/// branch chain from `shift` down to the first differing chunk, reusing the
/// old leaf `Arc` untouched. Caller guarantees `old_hash != hash`, so the
/// hashes diverge at some chunk with shift in `shift..=MAX_SHIFT`.
fn split_leaf<K: PKey, V: Clone>(
    old_leaf: Arc<Node<K, V>>,
    old_hash: u64,
    shift: u32,
    hash: u64,
    key: K,
    value: V,
) -> Arc<Node<K, V>> {
    let diff = old_hash ^ hash;
    debug_assert!(diff != 0, "split_leaf requires distinct hashes");
    let split_shift = (diff.trailing_zeros() / BITS) * BITS;
    let old_chunk = chunk(old_hash, split_shift);
    let new_chunk = chunk(hash, split_shift);
    let new_leaf = Arc::new(Node::Leaf {
        hash,
        entries: vec![(key, value)],
    });
    let bitmap = (1u32 << old_chunk) | (1u32 << new_chunk);
    let children = if old_chunk < new_chunk {
        vec![old_leaf, new_leaf]
    } else {
        vec![new_leaf, old_leaf]
    };
    let mut node = Arc::new(Node::Branch { bitmap, children });
    let mut s = split_shift;
    while s > shift {
        s -= BITS;
        node = Arc::new(Node::Branch {
            bitmap: 1u32 << chunk(hash, s),
            children: vec![node],
        });
    }
    node
}

/// Rebuilds the path from `node` for a remove at `shift`.
///
/// Returns `None` when the key is absent (no change), `Some(None)` when the
/// subtree became empty, and `Some(Some(n))` for a replacement subtree.
/// Branches that shrink to a single leaf child collapse into that leaf,
/// keeping the trie canonical.
#[allow(clippy::type_complexity)]
fn remove_rec<K: PKey, V: Clone>(
    node: &Arc<Node<K, V>>,
    shift: u32,
    hash: u64,
    key: &K,
) -> Option<Option<Arc<Node<K, V>>>> {
    match node.as_ref() {
        Node::Leaf {
            hash: leaf_hash,
            entries,
        } => {
            if *leaf_hash != hash {
                return None;
            }
            entries.iter().position(|(k, _)| k == key)?;
            if entries.len() == 1 {
                return Some(None);
            }
            let kept: Vec<(K, V)> = entries.iter().filter(|(k, _)| k != key).cloned().collect();
            Some(Some(Arc::new(Node::Leaf {
                hash: *leaf_hash,
                entries: kept,
            })))
        }
        Node::Branch { bitmap, children } => {
            let bit = 1u32 << chunk(hash, shift);
            if bitmap & bit == 0 {
                return None;
            }
            let pos = (bitmap & (bit - 1)).count_ones() as usize;
            let child = children.get(pos)?;
            match remove_rec(child, shift + BITS, hash, key)? {
                Some(new_child) => {
                    if children.len() == 1 && matches!(new_child.as_ref(), Node::Leaf { .. }) {
                        return Some(Some(new_child));
                    }
                    let mut new_children = children.clone();
                    match new_children.get_mut(pos) {
                        Some(slot) => *slot = new_child,
                        None => new_children.push(new_child),
                    }
                    Some(Some(Arc::new(Node::Branch {
                        bitmap: *bitmap,
                        children: new_children,
                    })))
                }
                None => {
                    if children.len() <= 1 {
                        return Some(None);
                    }
                    let kept: Vec<Arc<Node<K, V>>> = children
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != pos)
                        .map(|(_, c)| Arc::clone(c))
                        .collect();
                    if let [only] = kept.as_slice()
                        && matches!(only.as_ref(), Node::Leaf { .. })
                    {
                        return Some(Some(Arc::clone(only)));
                    }
                    Some(Some(Arc::new(Node::Branch {
                        bitmap: bitmap & !bit,
                        children: kept,
                    })))
                }
            }
        }
    }
}

/// Depth-first trie-order iterator; each frame is a node plus the index of
/// its next unvisited child (branch) or entry (leaf).
struct Iter<'a, K, V> {
    stack: Vec<(&'a Node<K, V>, usize)>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let (node, idx) = *self.stack.last()?;
            match node {
                Node::Leaf { entries, .. } => {
                    if let Some((k, v)) = entries.get(idx) {
                        if let Some(top) = self.stack.last_mut() {
                            top.1 += 1;
                        }
                        return Some((k, v));
                    }
                    self.stack.pop();
                }
                Node::Branch { children, .. } => match children.get(idx) {
                    Some(child) => {
                        if let Some(top) = self.stack.last_mut() {
                            top.1 += 1;
                        }
                        self.stack.push((child.as_ref(), 0));
                    }
                    None => {
                        self.stack.pop();
                    }
                },
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{AxiomVal, ConstantInfo, ConstantVal};
    use crate::environment::Environment;
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_core::name::{LeafView, Name};
    use fln_core::options::KVMap;
    use fln_hash::domain::{Domain, hash};
    use fln_hash::root::LogicalRoot;
    use std::collections::BTreeMap;
    use std::collections::HashSet;
    use std::sync::Arc;

    /// Deterministic LCG (Knuth MMIX constants).
    fn lcg(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *state
    }

    fn splitmix64(mut x: u64) -> u64 {
        x = x.wrapping_add(0x9E37_79B9_7F4A_7C15);
        x = (x ^ (x >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        x ^ (x >> 31)
    }

    /// Well-distributed test key.
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
    struct HKey(u64);

    impl PKey for HKey {
        fn key_hash(&self) -> u64 {
            splitmix64(self.0)
        }
    }

    /// Adversarial key: every instance collides on the same hash.
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
    struct CollKey(u64);

    impl PKey for CollKey {
        fn key_hash(&self) -> u64 {
            0xDEAD_BEEF
        }
    }

    /// Key with a separately controlled identity order and trie hash.
    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
    struct ShapedKey {
        canonical: u64,
        hash: u64,
    }

    impl PKey for ShapedKey {
        fn key_hash(&self) -> u64 {
            self.hash
        }
    }

    fn sorted_contents(map: &PMap<HKey, u64>) -> Vec<(u64, u64)> {
        let mut v: Vec<(u64, u64)> = map.iter().map(|(k, v)| (k.0, *v)).collect();
        v.sort_unstable();
        v
    }

    #[test]
    fn empty_map_basics() {
        let m: PMap<HKey, u64> = PMap::new();
        assert_eq!(m.len(), 0);
        assert!(m.is_empty());
        assert_eq!(format!("{m:?}"), "{}");
        assert_eq!(m.get(&HKey(7)), None);
        assert!(!m.contains_key(&HKey(7)));
        assert_eq!(m.iter().count(), 0);
        let m2 = m.remove(&HKey(7));
        assert!(m2.is_empty());
        let d: PMap<HKey, u64> = PMap::default();
        assert!(d.is_empty());
        let one = d.insert(HKey(1), 10);
        assert_eq!(one.len(), 1);
        let back = one.remove(&HKey(1));
        assert!(back.is_empty());
        assert_eq!(back.iter().count(), 0);
    }

    #[test]
    fn model_based_mixed_operations() {
        let mut rng = 0x1234_5678_9ABC_DEF0u64;
        let mut map: PMap<HKey, u64> = PMap::new();
        let mut model: BTreeMap<u64, u64> = BTreeMap::new();
        const KEY_SPACE: u64 = 2048;

        for _ in 0..10_000 {
            let r = lcg(&mut rng);
            let key = lcg(&mut rng) % KEY_SPACE;
            if r % 100 < 60 {
                let value = lcg(&mut rng);
                map = map.insert(HKey(key), value);
                model.insert(key, value);
            } else {
                map = map.remove(&HKey(key));
                model.remove(&key);
            }

            assert_eq!(map.len(), model.len());
            assert_eq!(map.is_empty(), model.is_empty());
            for _ in 0..50 {
                let probe = lcg(&mut rng) % KEY_SPACE;
                assert_eq!(map.get(&HKey(probe)), model.get(&probe));
                assert_eq!(map.contains_key(&HKey(probe)), model.contains_key(&probe));
            }
        }

        let model_contents: Vec<(u64, u64)> = model.iter().map(|(k, v)| (*k, *v)).collect();
        assert_eq!(sorted_contents(&map), model_contents);
        assert_eq!(map.iter().count(), map.len());
    }

    #[test]
    fn snapshot_isolation_across_forks() {
        let mut rng = 0xFEED_FACE_CAFE_BEEFu64;
        let mut base: PMap<HKey, u64> = PMap::new();
        let mut base_model: BTreeMap<u64, u64> = BTreeMap::new();
        for _ in 0..200 {
            let key = lcg(&mut rng) % 512;
            let value = lcg(&mut rng);
            base = base.insert(HKey(key), value);
            base_model.insert(key, value);
        }

        let fork = base.clone();
        let frozen = sorted_contents(&fork);
        let frozen_len = fork.len();

        let mut branch_a = base;
        let mut model_a = base_model.clone();
        for _ in 0..1_000 {
            let r = lcg(&mut rng);
            let key = lcg(&mut rng) % 512;
            if r % 100 < 55 {
                let value = lcg(&mut rng);
                branch_a = branch_a.insert(HKey(key), value);
                model_a.insert(key, value);
            } else {
                branch_a = branch_a.remove(&HKey(key));
                model_a.remove(&key);
            }
        }

        assert_eq!(sorted_contents(&fork), frozen);
        assert_eq!(fork.len(), frozen_len);

        let mut branch_b = fork.clone();
        let mut model_b = base_model;
        for _ in 0..500 {
            let r = lcg(&mut rng);
            let key = lcg(&mut rng) % 512;
            if r % 100 < 40 {
                let value = lcg(&mut rng);
                branch_b = branch_b.insert(HKey(key), value);
                model_b.insert(key, value);
            } else {
                branch_b = branch_b.remove(&HKey(key));
                model_b.remove(&key);
            }
        }

        assert_eq!(sorted_contents(&fork), frozen);
        let expect_a: Vec<(u64, u64)> = model_a.iter().map(|(k, v)| (*k, *v)).collect();
        let expect_b: Vec<(u64, u64)> = model_b.iter().map(|(k, v)| (*k, *v)).collect();
        assert_eq!(sorted_contents(&branch_a), expect_a);
        assert_eq!(sorted_contents(&branch_b), expect_b);
    }

    #[test]
    fn snapshot_is_constant_time_and_structurally_shared() {
        let mut map: PMap<HKey, u64> = PMap::new();
        for i in 0..100_000u64 {
            map = map.insert(HKey(i), i.wrapping_mul(3));
        }
        assert_eq!(map.len(), 100_000);

        let root = map
            .root
            .as_ref()
            .expect("map with 100_000 entries has a root");
        let before = Arc::strong_count(root);
        let snapshot = map.clone();
        assert_eq!(Arc::strong_count(root), before + 1);
        assert_eq!(snapshot.len(), map.len());
        drop(snapshot);
        assert_eq!(Arc::strong_count(root), before);

        let old_count = map.node_count();
        let new_map = map.insert(HKey(1_000_000), 42);
        let new_count = new_map.node_count();
        let added_nodes = new_count.saturating_sub(old_count);
        let depth = MAX_DEPTH;
        assert!(
            added_nodes <= depth,
            "insert added {added_nodes} nodes, expected <= depth {depth}"
        );

        let old_ptrs: HashSet<*const ()> = map.node_ptrs().into_iter().collect();
        let new_ptrs = new_map.node_ptrs();
        let fresh = new_ptrs.iter().filter(|p| !old_ptrs.contains(*p)).count();
        let shared = new_ptrs.len() - fresh;
        assert!(
            fresh <= 2 * depth,
            "insert built {fresh} fresh nodes, expected <= 2 * depth = {}",
            2 * depth
        );
        assert!(
            shared >= old_count.saturating_sub(depth),
            "only {shared} of {old_count} old nodes shared"
        );
        println!(
            "sharing evidence: old_nodes={old_count} new_nodes={new_count} \
             fresh={fresh} shared={shared} depth_bound={depth}"
        );
    }

    #[test]
    fn full_hash_collisions_behave_like_model() {
        let mut rng = 0x0BAD_F00D_0DDB_A110u64;
        let mut map: PMap<CollKey, u64> = PMap::new();
        let mut model: BTreeMap<u64, u64> = BTreeMap::new();
        const KEY_SPACE: u64 = 40;

        for _ in 0..500 {
            let r = lcg(&mut rng);
            let key = lcg(&mut rng) % KEY_SPACE;
            if r % 100 < 60 {
                let value = lcg(&mut rng);
                map = map.insert(CollKey(key), value);
                model.insert(key, value);
            } else {
                map = map.remove(&CollKey(key));
                model.remove(&key);
            }

            assert_eq!(map.len(), model.len());
            for probe in 0..KEY_SPACE {
                assert_eq!(map.get(&CollKey(probe)), model.get(&probe));
            }
        }

        let contents: Vec<(u64, u64)> = map.iter().map(|(k, v)| (k.0, *v)).collect();
        let expected: Vec<(u64, u64)> = model.iter().map(|(k, v)| (*k, *v)).collect();
        assert_eq!(contents, expected);
    }

    fn collision_map(order: &[u64]) -> PMap<CollKey, u64> {
        order.iter().fold(PMap::new(), |map, key| {
            map.insert(CollKey(*key), key.wrapping_mul(17))
        })
    }

    fn collision_contents(map: &PMap<CollKey, u64>) -> Vec<(u64, u64)> {
        map.iter().map(|(key, value)| (key.0, *value)).collect()
    }

    #[test]
    fn collision_bucket_lifecycle_is_canonical_under_every_build_order() {
        const CARDINALITY: u64 = 257;
        let forward_order: Vec<u64> = (0..CARDINALITY).collect();
        let reverse_order: Vec<u64> = forward_order.iter().rev().copied().collect();
        let mut shuffled_order = forward_order.clone();
        let mut rng = 0xC011_1510_0BAD_5EEDu64;
        for index in (1..shuffled_order.len()).rev() {
            let swap_with = (lcg(&mut rng) % (index as u64 + 1)) as usize;
            shuffled_order.swap(index, swap_with);
        }

        let mut forward = collision_map(&forward_order);
        let mut reverse = collision_map(&reverse_order);
        let mut shuffled = collision_map(&shuffled_order);
        let expected: Vec<(u64, u64)> = forward_order
            .iter()
            .map(|key| (*key, key.wrapping_mul(17)))
            .collect();

        assert_eq!(collision_contents(&forward), expected);
        assert_eq!(collision_contents(&reverse), expected);
        assert_eq!(collision_contents(&shuffled), expected);
        assert_eq!(format!("{forward:?}"), format!("{reverse:?}"));
        assert_eq!(format!("{forward:?}"), format!("{shuffled:?}"));
        assert_eq!(forward, reverse);
        assert_eq!(forward, shuffled);

        // Overwrite identical keys in opposing orders. Existing key objects stay
        // in their canonical slots; only values change.
        for key in forward_order.iter().step_by(3) {
            forward = forward.insert(CollKey(*key), key.wrapping_mul(31));
        }
        for key in reverse_order.iter().filter(|key| **key % 3 == 0) {
            reverse = reverse.insert(CollKey(*key), key.wrapping_mul(31));
        }
        for key in shuffled_order.iter().filter(|key| **key % 3 == 0) {
            shuffled = shuffled.insert(CollKey(*key), key.wrapping_mul(31));
        }
        assert_eq!(collision_contents(&forward), collision_contents(&reverse));
        assert_eq!(collision_contents(&forward), collision_contents(&shuffled));
        assert_eq!(format!("{forward:?}"), format!("{reverse:?}"));
        assert_eq!(format!("{forward:?}"), format!("{shuffled:?}"));
        assert_eq!(forward, reverse);
        assert_eq!(forward, shuffled);

        // Forks remain immutable while branches remove the same keys in distinct
        // orders, then reinsert them in a third pair of orders.
        let frozen = forward.clone();
        let frozen_contents = collision_contents(&frozen);
        let removed: Vec<u64> = forward_order
            .iter()
            .copied()
            .filter(|key| key % 5 == 0)
            .collect();
        for key in &removed {
            forward = forward.remove(&CollKey(*key));
        }
        for key in removed.iter().rev() {
            reverse = reverse.remove(&CollKey(*key));
        }
        assert_eq!(collision_contents(&forward), collision_contents(&reverse));
        assert_eq!(format!("{forward:?}"), format!("{reverse:?}"));
        assert_eq!(forward, reverse);
        assert_eq!(collision_contents(&frozen), frozen_contents);
        assert_eq!(collision_contents(&frozen), collision_contents(&shuffled));
        assert_eq!(format!("{frozen:?}"), format!("{shuffled:?}"));
        assert_eq!(frozen, shuffled);

        for key in removed.iter().rev() {
            forward = forward.insert(CollKey(*key), key.wrapping_mul(47));
        }
        for key in &removed {
            reverse = reverse.insert(CollKey(*key), key.wrapping_mul(47));
        }
        assert_eq!(collision_contents(&forward), collision_contents(&reverse));
        assert_eq!(format!("{forward:?}"), format!("{reverse:?}"));
        assert_eq!(forward, reverse);
        assert_eq!(forward.len(), CARDINALITY as usize);
    }

    #[test]
    fn near_collision_trie_exercises_every_hash_chunk_including_partial_top_chunk() {
        for shift in (0..=MAX_SHIFT).step_by(BITS as usize) {
            let low = ShapedKey {
                canonical: 0,
                hash: 0,
            };
            let high = ShapedKey {
                canonical: 1,
                hash: 1u64 << shift,
            };
            let forward = PMap::new().insert(low.clone(), 0).insert(high.clone(), 1);
            let reverse = PMap::new().insert(high, 1).insert(low, 0);
            let expected_nodes = (shift / BITS) as usize + 3;
            assert_eq!(forward.node_count(), expected_nodes, "shift={shift}");
            assert_eq!(reverse.node_count(), expected_nodes, "shift={shift}");
            assert_eq!(
                forward.iter().collect::<Vec<_>>(),
                reverse.iter().collect::<Vec<_>>(),
                "shift={shift}"
            );
        }

        // Only four real bits remain at shift 60; the five-bit mask must not
        // manufacture a seventeenth bucket or discard the high nibble.
        assert_eq!(chunk(u64::MAX, MAX_SHIFT), 15);
        let top_nibble = PMap::new()
            .insert(
                ShapedKey {
                    canonical: 0,
                    hash: 0,
                },
                0,
            )
            .insert(
                ShapedKey {
                    canonical: 15,
                    hash: 0xFu64 << MAX_SHIFT,
                },
                15,
            );
        assert_eq!(top_nibble.node_count(), (MAX_SHIFT / BITS) as usize + 3);

        // Exercise all divergence depths together, with a full-hash collision
        // bucket at zero, so insertion order cannot hide interactions between
        // the trie topology and the bucket tie-break.
        let mut mixed_keys = vec![
            ShapedKey {
                canonical: 0,
                hash: 0,
            },
            ShapedKey {
                canonical: 1,
                hash: 0,
            },
        ];
        mixed_keys.extend((0..=MAX_SHIFT).step_by(BITS as usize).enumerate().map(
            |(index, shift)| ShapedKey {
                canonical: index as u64 + 2,
                hash: 1u64 << shift,
            },
        ));
        let mixed_forward = mixed_keys.iter().fold(PMap::new(), |map, key| {
            map.insert(key.clone(), key.canonical)
        });
        let mixed_reverse = mixed_keys.iter().rev().fold(PMap::new(), |map, key| {
            map.insert(key.clone(), key.canonical)
        });
        assert_eq!(
            mixed_forward.iter().collect::<Vec<_>>(),
            mixed_reverse.iter().collect::<Vec<_>>()
        );
        assert_eq!(format!("{mixed_forward:?}"), format!("{mixed_reverse:?}"));
        assert_eq!(mixed_forward, mixed_reverse);
    }

    fn independently_built_deep_name(depth: u64) -> Name {
        (0..depth).fold(Name::anonymous(), Name::num)
    }

    #[test]
    fn pinned_name_order_handles_deep_full_hash_collisions_without_host_recursion() {
        const DEPTH: u64 = 20_000;
        let first = Name::num_overflowing(independently_built_deep_name(DEPTH), 11);
        let second = Name::num_overflowing(independently_built_deep_name(DEPTH), 29);
        assert_eq!(first.hash(), second.hash(), "overflowing Name nums collide");
        assert!(
            first < second,
            "the pinned Name.cmp order is the bucket CGSE"
        );

        let map = PMap::new()
            .insert(second.clone(), 29)
            .insert(first.clone(), 11);
        assert_eq!(numeric_leaf_order(&map), Some(vec![11, 29]));
        assert_eq!(map.get(&first), Some(&11));
        assert_eq!(map.get(&second), Some(&29));
    }

    fn colliding_environment_name(component: u64) -> Name {
        Name::num_overflowing(Name::str(Name::anonymous(), "fln-amv-collision"), component)
    }

    fn collision_axiom(name: Name) -> ConstantInfo {
        ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name,
                level_params: vec![],
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        })
    }

    fn partitioned_insertion_order(
        cardinality: usize,
        partitions: usize,
        rotation: usize,
    ) -> Vec<u64> {
        let mut rows: Vec<Vec<u64>> = (0..partitions)
            .map(|partition| {
                let mut row: Vec<u64> = (partition..cardinality)
                    .step_by(partitions)
                    .map(|index| index as u64)
                    .collect();
                if partition % 2 == 0 {
                    row.reverse();
                }
                row
            })
            .collect();
        rows.rotate_left(rotation % partitions);
        rows.into_iter().flatten().collect()
    }

    fn build_collision_environment(order: &[u64]) -> Option<(PMap<Name, u64>, Environment)> {
        let mut enumeration = PMap::new();
        let mut environment = Environment::new();
        for component in order {
            let name = colliding_environment_name(*component);
            enumeration = enumeration.insert(name.clone(), *component);
            environment = environment.add_decl(collision_axiom(name)).ok()?;
        }
        Some((enumeration, environment))
    }

    fn numeric_leaf_order(map: &PMap<Name, u64>) -> Option<Vec<u64>> {
        map.iter()
            .map(|(name, _)| match name.leaf_view() {
                LeafView::Num(component) => Some(component),
                LeafView::Anonymous | LeafView::Str(_) => None,
            })
            .collect()
    }

    fn json_u64_array(values: &[u64]) -> String {
        let body = values
            .iter()
            .map(u64::to_string)
            .collect::<Vec<_>>()
            .join(",");
        format!("[{body}]")
    }

    fn json_u64_matrix(rows: &[Vec<u64>]) -> String {
        let body = rows
            .iter()
            .map(|row| json_u64_array(row))
            .collect::<Vec<_>>()
            .join(",");
        format!("[{body}]")
    }

    fn json_string(value: &str) -> String {
        let mut encoded = String::from("\"");
        for ch in value.chars() {
            match ch {
                '"' => encoded.push_str("\\\""),
                '\\' => encoded.push_str("\\\\"),
                '\u{08}' => encoded.push_str("\\b"),
                '\u{0c}' => encoded.push_str("\\f"),
                '\n' => encoded.push_str("\\n"),
                '\r' => encoded.push_str("\\r"),
                '\t' => encoded.push_str("\\t"),
                control if control <= '\u{1f}' => {
                    encoded.push_str(&format!("\\u{:04x}", control as u32));
                }
                ordinary => encoded.push(ordinary),
            }
        }
        encoded.push('"');
        encoded
    }

    fn json_string_array(values: &[String]) -> String {
        let body = values
            .iter()
            .map(|value| json_string(value))
            .collect::<Vec<_>>()
            .join(",");
        format!("[{body}]")
    }

    #[test]
    fn robot_json_string_escapes_every_control_character_class() {
        let input: String = [
            '\0', '\u{1f}', '"', '\\', '\n', '\r', '\t', '\u{08}', '\u{0c}',
        ]
        .into_iter()
        .collect();
        assert_eq!(
            json_string(&input),
            "\"\\u0000\\u001f\\\"\\\\\\n\\r\\t\\b\\f\""
        );
    }

    struct ScheduleEvidence {
        insertion_order: Vec<u64>,
        enumeration: Vec<u64>,
        enumeration_nodes: usize,
        environment_entries: usize,
        root: LogicalRoot,
    }

    fn concurrent_schedule_evidence(cardinality: usize, threads: usize) -> Vec<ScheduleEvidence> {
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..threads)
                .map(|worker| {
                    scope.spawn(move || {
                        let insertion_order =
                            partitioned_insertion_order(cardinality, threads, worker);
                        let (enumeration, environment) =
                            build_collision_environment(&insertion_order)?;
                        Some(ScheduleEvidence {
                            insertion_order,
                            enumeration: numeric_leaf_order(&enumeration)?,
                            enumeration_nodes: enumeration.node_count(),
                            environment_entries: environment.len(),
                            root: environment.logical_root(&KVMap::new()),
                        })
                    })
                })
                .collect();
            let mut evidence = Vec::with_capacity(threads);
            for handle in handles {
                if let Ok(Some(row)) = handle.join() {
                    evidence.push(row);
                }
            }
            evidence
        })
    }

    #[test]
    fn environment_collision_e2e_emits_detailed_real_path_evidence() {
        const CARDINALITY: usize = 96;
        const THREAD_MATRIX: [usize; 3] = [1, 8, 32];
        let started = std::time::Instant::now();
        let expected_order: Vec<u64> = (0..CARDINALITY as u64).collect();
        let mut expected_root = None;
        let mut run_id = std::env::var("FLN_ENV_E2E_RUN_ID")
            .unwrap_or_else(|_| "unit".to_string())
            .chars()
            .filter(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_'))
            .collect::<String>();
        if run_id.is_empty() {
            run_id.push_str("unit");
        }
        let mut input_bytes = Vec::with_capacity(CARDINALITY * std::mem::size_of::<u64>());
        for component in &expected_order {
            input_bytes.extend_from_slice(&component.to_le_bytes());
        }
        let canonical_input_root = hash(Domain::Fixture, &input_bytes);
        let cwd = std::env::current_dir()
            .map(|path| path.to_string_lossy().into_owned())
            .unwrap_or_else(|_| "unknown".to_string());
        let artifact_fallback =
            std::env::var("FLN_ENV_E2E_ARTIFACT").unwrap_or_else(|_| "stdout".to_string());
        let stdout_artifact = std::env::var("FLN_ENV_E2E_STDOUT_ARTIFACT")
            .unwrap_or_else(|_| artifact_fallback.clone());
        let stderr_artifact =
            std::env::var("FLN_ENV_E2E_STDERR_ARTIFACT").unwrap_or(artifact_fallback);
        let argv = std::env::var("FLN_ENV_E2E_ARGV").unwrap_or_else(|_| {
            "cargo test -p fln-env pmap::tests::environment_collision_e2e_emits_detailed_real_path_evidence -- --exact --nocapture".to_string()
        });
        let cache_state =
            std::env::var("FLN_ENV_E2E_CACHE_STATE").unwrap_or_else(|_| "uncontrolled".to_string());
        let cwd_json = json_string(&cwd);
        let stdout_artifact_json = json_string(&stdout_artifact);
        let stderr_artifact_json = json_string(&stderr_artifact);
        let argv_json = json_string(&argv);
        let cache_state_json = json_string(&cache_state);

        for threads in THREAD_MATRIX {
            let schedule_started_us = started.elapsed().as_micros();
            let schedules = concurrent_schedule_evidence(CARDINALITY, threads);
            let schedule_finished_us = started.elapsed().as_micros();
            assert_eq!(schedules.len(), threads, "threads={threads}");
            let Some(representative) = schedules.first() else {
                continue;
            };
            for schedule in &schedules {
                assert_eq!(schedule.insertion_order.len(), CARDINALITY);
                assert_eq!(
                    schedule.enumeration, expected_order,
                    "collision enumeration diverged: threads={threads}"
                );
                match expected_root {
                    None => expected_root = Some(schedule.root),
                    Some(expected) => assert_eq!(schedule.root, expected, "threads={threads}"),
                }
            }
            let root = expected_root.unwrap_or(representative.root);
            let distinct_orders = schedules
                .iter()
                .map(|schedule| &schedule.insertion_order)
                .collect::<std::collections::BTreeSet<_>>()
                .len();
            assert_eq!(distinct_orders, threads, "threads={threads}");
            let worker_roots: Vec<String> = schedules
                .iter()
                .map(|schedule| schedule.root.to_string())
                .collect();
            let worker_insertion_orders: Vec<Vec<u64>> = schedules
                .iter()
                .map(|schedule| schedule.insertion_order.clone())
                .collect();
            let worker_enumerations: Vec<Vec<u64>> = schedules
                .iter()
                .map(|schedule| schedule.enumeration.clone())
                .collect();
            let enumeration_nodes: Vec<u64> = schedules
                .iter()
                .map(|schedule| schedule.enumeration_nodes as u64)
                .collect();
            let environment_entries: Vec<u64> = schedules
                .iter()
                .map(|schedule| schedule.environment_entries as u64)
                .collect();
            println!(
                "{{\"schema\":\"fln.e2e.environment-collision\",\"version\":2,\"run_id\":\"{run_id}\",\"bead\":\"fln-amv.10\",\"claim_id\":\"fln-amv.10-collision-canonicality\",\"claim_type\":\"bounded_model\",\"invariant_id\":\"FL-INV-01\",\"invariant_relation\":\"supports-local-pmap-slice\",\"gate_id\":\"PG-5\",\"gate_relation\":\"partial-component-evidence\",\"parity_ledger_row\":\"not_applicable_internal_data_structure_determinism\",\"data_grade\":\"verified\",\"epoch\":\"lean-v4.32.0\",\"mode\":\"sound\",\"profile\":\"e2e\",\"platform\":\"{}-{}\",\"seed\":\"partition-rotation-v1\",\"cache_state\":{cache_state_json},\"canonical_input_root\":\"fln-fixture:{canonical_input_root}\",\"scenario\":\"full-hash-collision-schedule-matrix\",\"schedule_id\":\"partitioned-{threads}\",\"status\":\"pass\",\"cwd\":{cwd_json},\"argv\":[{argv_json}],\"stdout_artifact\":{stdout_artifact_json},\"stderr_artifact\":{stderr_artifact_json},\"collision_cardinality\":{CARDINALITY},\"collision_hash\":\"{:016x}\",\"threads\":{threads},\"workers_built\":{},\"distinct_insertion_orders\":{distinct_orders},\"representative_insertion_order\":{},\"worker_insertion_orders\":{},\"expected_enumeration\":{},\"actual_enumeration\":{},\"worker_enumerations\":{},\"expected_root\":\"{root}\",\"actual_root\":\"{}\",\"worker_roots\":{},\"enumeration_insert_operations\":{},\"environment_insert_operations\":{},\"environment_duplicate_checks\":{},\"observed_enumeration_nodes\":{},\"observed_environment_entries\":{},\"theoretical_fresh_node_bound_per_insert\":{},\"theoretical_replaced_node_bound_per_insert\":{},\"operation_budget\":{{\"max_collision_cardinality\":{CARDINALITY},\"thread_matrix\":[1,8,32]}},\"bucket_policy\":\"PKey-Ord\",\"lookup_complexity\":\"O(bucket)\",\"insert_complexity\":\"O(log(bucket))-comparisons-plus-O(bucket)-clone-shift\",\"resource_followup\":\"fln-amv.13\",\"monotonic_start_us\":{schedule_started_us},\"monotonic_end_us\":{schedule_finished_us},\"duration_us\":{},\"timing_used_as_gate\":false,\"process_exit\":0,\"signal\":null,\"first_divergence\":null,\"cleanup_status\":\"retained_by_policy\",\"final_state\":\"canonical-enumeration-and-root-verified\"}}",
                std::env::consts::OS,
                std::env::consts::ARCH,
                colliding_environment_name(0).hash(),
                schedules.len(),
                json_u64_array(&representative.insertion_order),
                json_u64_matrix(&worker_insertion_orders),
                json_u64_array(&expected_order),
                json_u64_array(&representative.enumeration),
                json_u64_matrix(&worker_enumerations),
                representative.root,
                json_string_array(&worker_roots),
                CARDINALITY * schedules.len(),
                CARDINALITY * schedules.len(),
                CARDINALITY * schedules.len(),
                json_u64_array(&enumeration_nodes),
                json_u64_array(&environment_entries),
                2 * MAX_DEPTH,
                MAX_DEPTH,
                schedule_finished_us - schedule_started_us,
            );
        }
    }

    #[test]
    fn iteration_order_is_insertion_order_independent() {
        let pairs: Vec<(u64, u64)> = (0..500u64).map(|i| (i, i.wrapping_mul(10))).collect();

        let mut forward: PMap<HKey, u64> = PMap::new();
        for (k, v) in &pairs {
            forward = forward.insert(HKey(*k), *v);
        }

        let mut shuffled = pairs.clone();
        let mut rng = 0x5EED_5EED_5EED_5EEDu64;
        for i in (1..shuffled.len()).rev() {
            let j = (lcg(&mut rng) % (i as u64 + 1)) as usize;
            shuffled.swap(i, j);
        }
        assert_ne!(shuffled, pairs);
        let mut permuted: PMap<HKey, u64> = PMap::new();
        for (k, v) in &shuffled {
            permuted = permuted.insert(HKey(*k), *v);
        }

        assert_eq!(forward.len(), permuted.len());
        let order_a: Vec<(u64, u64)> = forward.iter().map(|(k, v)| (k.0, *v)).collect();
        let order_b: Vec<(u64, u64)> = permuted.iter().map(|(k, v)| (k.0, *v)).collect();
        assert_eq!(order_a, order_b);
        assert_eq!(order_a.len(), 500);
        assert_eq!(forward, permuted);
        assert_ne!(forward, forward.remove(&HKey(0)));
    }
}
