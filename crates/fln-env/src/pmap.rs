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
//! chunk first — so it depends only on the key hashes present (plus bucket
//! insertion order for hash-colliding keys), never on the sequence of
//! non-colliding insertions that built the map.

use std::sync::Arc;

/// Keys carry their own 64-bit hash.
///
/// The hash must be a pure function of the key's `Eq` identity: equal keys
/// must return equal hashes. Distinct keys may collide; collisions degrade a
/// leaf to a linear bucket but never affect correctness.
pub trait PKey: Clone + Eq {
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
                let added = match new_entries.iter_mut().find(|(k, _)| *k == key) {
                    Some(slot) => {
                        slot.1 = value;
                        false
                    }
                    None => {
                        new_entries.push((key, value));
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
    #[derive(Clone, PartialEq, Eq, Debug)]
    struct CollKey(u64);

    impl PKey for CollKey {
        fn key_hash(&self) -> u64 {
            0xDEAD_BEEF
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

        let mut contents: Vec<(u64, u64)> = map.iter().map(|(k, v)| (k.0, *v)).collect();
        contents.sort_unstable();
        let expected: Vec<(u64, u64)> = model.iter().map(|(k, v)| (*k, *v)).collect();
        assert_eq!(contents, expected);
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
