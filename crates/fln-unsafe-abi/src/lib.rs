//! **fln-unsafe-abi** — Marrow's boundary crate — object layout, tagged-pointer arithmetic, compacted-region relocation, `dlopen` of Reference-ABI plugins, and the exported `lean_*` symbol surface (plan §6, D3).
//!
//! D3 boundary crate: `unsafe` is permitted here ONLY at narrowly scoped
//! `#[allow(unsafe_code)]` sites, each carrying a `// UNSAFE-LEDGER: FLN-UL-NNNN`
//! marker and a matching row in `ci/UNSAFE_LEDGER.txt` (path, invariant, evidence,
//! safe fallback, no-claim boundary). CI rejects unledgered sites. This crate
//! must never depend on `fln-kernel` or `fln-checker` (D3 law a).
//!
//! Bead fln-lld (slice 1) implements the CompatHeap core: the `lean_object`
//! object model with layouts generated from the pinned contract
//! ([`contract`]), membrane-only allocation with the pin's `LEAN_MIMALLOC`
//! observables ([`membrane`]), per-category constructors/accessors
//! ([`object`]), tri-state reference counting with iterative teardown
//! ([`rc`]), tagged-pointer scalars ([`tagged`]), debug ownership shadows
//! ([`shadow`]), and the safe RAII prototype of the eventual fln-rt surface
//! ([`handle`]). Everything is `pub(crate)`: the exported `lean_*` symbol
//! surface waits for the expansion-aware no-admission export covenant
//! (slice 2, coordinated with the structure guard, bead fln-8mj follow-up).
//!
//! Slice-1 typed restrictions (tracked, never silent):
//! * scheduled tasks/promises (`m_imp != NULL`) — bead fln-3gv (effects on
//!   asupersync);
//! * forcing thunks / applying closures / external `m_foreach` traversal —
//!   bead franken_lean-7xe (Golem apply machinery);
//! * compacted-region loading — bead fln-wgp; the owned allocator — fln-8w8;
//!   mpz arithmetic — the fln-bignum shim (Crucible workstream).

#![deny(unsafe_code)]
// Slice-1 state: the CompatHeap API is `pub(crate)` and consumed by the test
// suites only — the fln-rt safe surface arrives with the slice-2 export
// covenant, at which point this allowance must be removed.
#![cfg_attr(not(test), allow(dead_code))]

// The layout mirrors are exact only under the certified target shape: 64-bit,
// little-endian (C bitfield unit `m_cs_sz:16|m_other:8|m_tag:8` byte-splits
// low-to-high; pointers are 8 bytes; `size_t` is `usize` is 8 bytes).
#[cfg(not(all(target_pointer_width = "64", target_endian = "little")))]
compile_error!(
    "fln-unsafe-abi requires a 64-bit little-endian target; the CompatHeap \
     layout mirrors are byte-exact only on the certified platform matrix"
);

mod contract;
mod handle;
mod layout;
mod membrane;
mod object;
mod rc;
mod shadow;
mod tagged;

#[cfg(test)]
mod tests;
