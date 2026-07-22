# G0-1 findings memo — layout subtleties of the `.olean` region format at the pin

Bead franken_lean-y24 (§22.1-1). Every subtlety below was discovered or
confirmed by resurrecting **all 2 433 `.olean` files of the pinned toolchain
library** (leanprover/lean4 v4.32.0, commit `8c9756b2…`) with the prototype
reader (`fln_olean::region`): 9 562 406 objects, 158 608 constants, 832 903
environment-extension entries, **zero integrity faults**. Facts already carried
by the generated contracts (`ABI_CONTRACT.md`, `OLEAN_CONTRACT.md`) are cited,
not restated; items marked **(fold)** are candidates for future extractor
enrichment.

1. **Pointer law.** Every stored pointer equals `base_addr + file_offset`,
   where `file_offset` counts from the start of the FILE (header included),
   not from the data region. `base_addr` is 64 KiB-aligned
   (`REGION_ALIGN`), so the low 16 bits of any pointer are its offset within
   the final page — handy for eyeballing hexdumps.
2. **Root slot.** The first `size_t` of the data region (file offset 88) is a
   pointer slot, not an object: allocated first, written last by the
   compactor. The root object itself typically sits near the END of the file.
3. **Header word packing.** The `lean_object` header reads as one LE u64:
   low 32 bits `m_rc` (must be 0 = persistent in a region), high 32 bits pack
   `m_cs_sz` (low 16) | `m_other` (next 8) | `m_tag` (top 8) — GCC/Clang
   low-to-high bitfield order. **(fold** into ABI_CONTRACT as a packed-word
   note; the generated field table records widths but not bit positions.)
4. **`m_cs_sz` in regions.** For small compacted objects the padded byte size
   is stored in `m_cs_sz` (`lean_set_non_heap_header`); e.g. the ModuleData
   ctor (8 header + 5×8 pointers + 1 Bool scalar = 49) is stored with
   `m_cs_sz = 56` — rounded to `LEAN_OBJECT_SIZE_DELTA`. Big objects store 0.
5. **Ctor field order.** Pointer fields first (declaration order among
   pointer-typed fields), then the scalar area (`lean_ctor_scalar_cptr`).
   `ModuleData` therefore lays out as
   `[imports, constNames, constants, extraConstNames, entries][isModule: u8]`
   even though `isModule` is declared FIRST in the Lean structure. **(fold:**
   the generated `MODULE_DATA_FIELDS` table keeps declaration order; the
   pointer/scalar split is a reader-side law worth a generated column.)
6. **Fieldless enum constructors are scalars.** `Name.anonymous`, `Bool.false`
   etc. never appear as objects: they are boxed ctor indices
   (`box(i) = (i<<1)|1`). A "pointer" with bit 0 set is a value, not an
   address — corruption tests must keep seeded bad pointers EVEN or they
   accidentally become legal scalars.
7. **`Name` carries a cached hash.** `Name.str`/`Name.num` ctors have
   `m_other = 2` pointer fields plus a `usize` scalar (the `@[computed_field]`
   hash) in the scalar area — arity from the surface inductive alone would be
   wrong.
8. **String objects.** `m_size` counts bytes INCLUDING the NUL terminator;
   `m_length` is the UTF-8 char count; `m_size == 0` never occurs (empty
   string stores size 1). All 2 433 files hold valid UTF-8 throughout.
9. **Bignums under GMP flag.** Header `flags` bit 0 = 1 in the official
   release: `mpz_object` is `{i32 alloc, i32 size, ptr limbs}` after the
   object header; the compactor copies limbs immediately after the object and
   rewrites exactly that one interior pointer. Limb count = `|size|` (sign of
   `size` is the integer's sign).
10. **Thunk/Task in regions.** Atomics are stored as plain words; thunk
    `m_value`/`m_closure` may be genuinely NULL (0) — a legal null pointer
    position, unlike anywhere else in the graph. Task `m_imp` is not persisted
    as a live pointer.
11. **Absent categories.** Across the whole pinned library: no `Closure`
    (v2 forbids), no `External` (compactor throws), no `StructArray`, no
    `Promise`, no `Task`, no `Ref`, no `Thunk` objects were observed in
    module data; graphs are ctors + arrays + strings + rare mpz. (Thunk/Task/
    Ref support in the reader is exercised only by hostile-input tests today.)
12. **`constNames` redundancy law holds everywhere:**
    `constNames.length == constants.length` in all 2 433 modules — usable as a
    cheap integrity cross-check before decoding `ConstantInfo`.
13. **Aggregator modules** (`Init.olean`, `Std.olean`, `Lean.olean`) carry
    zero constants but non-empty extension entry blocks.
14. **Sharing is real, cycles are not.** The graphs are DAGs (visited-set
    traversal terminates without cycle handling), with heavy structural
    sharing — Prelude's 88 880 distinct objects are referenced far more times
    than once each. A naive tree-walk would blow up; a cycle-tolerant walk is
    still required for hostile inputs.
15. **Version 2 everywhere.** Every file in the pinned library is v2; v3
    (closure-bearing) never occurs in the shipped stdlib. The reader accepts
    the contract's `{2,3}` at the header but types v3 closure payload
    traversal as a follow-up (`ClosureInV2` today).

Typed limitation (honest L-level): the Corpus (mathlib4) is not installed on
this host, so the mathlib-scale acceptance lane runs on the full pinned
toolchain library instead; the reader and rig are Corpus-ready and the E2E
lane picks up mathlib oleans automatically once the Corpus lands.
