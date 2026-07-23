//! CompatHeap membrane allocation (plan §6.1b, bead fln-lld).
//!
//! Every CompatHeap object is minted and released ONLY through this module.
//! The size/`m_cs_sz` discipline mirrors the pin's distributed build exactly
//! (`LEAN_MIMALLOC` defined in the toolchain's `include/lean/config.h`):
//!
//! * small path (`lean_alloc_small_object`, `lean.h:409-432`): size is
//!   aligned up to `OBJECT_SIZE_DELTA` and the aligned size is stored in
//!   `m_cs_sz` at allocation time; header init leaves it in place.
//! * big path (`lean_alloc_object`, `object.cpp:355-376` — arrays, scalar
//!   arrays, strings, closures): exact requested size, `m_cs_sz = 0`.
//! * ctor memory (`lean_alloc_ctor_memory`, `lean.h:434-465`): small path
//!   plus zero-initialization of the final word when alignment padded the
//!   request, preserving the sharing-maximizer determinism upstream relies
//!   on (`maxsharing.cpp`/`compact.cpp` comment at `lean.h:441-449`).
//!
//! Allocation failure aborts the process (`std::alloc::handle_alloc_error`),
//! matching `lean_internal_panic_out_of_memory` — an abort, never a Rust
//! panic unwinding toward an ABI boundary (§6.5 panic law). The owned
//! size-classed allocator with the heartbeat hook replaces `std::alloc`
//! underneath this interface in bead fln-8w8; the membrane discipline and
//! observable header facts are already final here.

use crate::contract::{MAX_SMALL_OBJECT_SIZE, OBJECT_SIZE_DELTA, TAG_RESERVED};
use crate::layout::LeanObject;
use crate::shadow;
use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

/// `lean_align` (`lean.h:390-392`) at `OBJECT_SIZE_DELTA` granularity.
#[inline(always)]
pub(crate) fn align_obj_size(sz: usize) -> usize {
    (sz / OBJECT_SIZE_DELTA) * OBJECT_SIZE_DELTA
        + OBJECT_SIZE_DELTA * usize::from(!sz.is_multiple_of(OBJECT_SIZE_DELTA))
}

/// All CompatHeap blocks are 8-aligned: `lean_object` demands 4, every
/// object-model struct field demands at most 8, and the small path's size
/// quantum is `OBJECT_SIZE_DELTA = 8`.
const OBJ_ALIGN: usize = 8;

fn obj_layout(size: usize) -> Layout {
    debug_assert!(size > 0);
    Layout::from_size_align(size, OBJ_ALIGN).expect("object size overflows Layout")
}

/// Small-path allocation: `lean_alloc_small_object` under `LEAN_MIMALLOC`
/// (`lean.h:417-424`). Returns uninitialized memory except `m_cs_sz`, which
/// holds the aligned size exactly as the pin's build leaves it in live
/// objects.
///
/// # Safety
/// Caller must initialize the header (and every salient field) before the
/// object is shared, and must release through this module.
// UNSAFE-LEDGER: FLN-UL-0001
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_small(sz: usize) -> *mut LeanObject {
    let aligned = align_obj_size(sz);
    debug_assert!(aligned <= MAX_SMALL_OBJECT_SIZE);
    let p = unsafe { alloc(obj_layout(aligned)) };
    if p.is_null() {
        handle_alloc_error(obj_layout(aligned));
    }
    let o = p.cast::<LeanObject>();
    // SAFETY: freshly allocated, exclusively owned, at least 8 bytes.
    unsafe { (&raw mut (*o).m_cs_sz).write(aligned as u16) };
    o
}

/// Big-path allocation: `lean_alloc_object` under `LEAN_MIMALLOC`
/// (`object.cpp:364-370`). `m_cs_sz = 0` marks the big path in live headers.
///
/// # Safety
/// As [`alloc_small`]; additionally the caller must retain `sz` knowledge
/// (big-object byte size is recomputed from salient fields at release).
// UNSAFE-LEDGER: FLN-UL-0002
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_big(sz: usize) -> *mut LeanObject {
    let p = unsafe { alloc(obj_layout(sz)) };
    if p.is_null() {
        handle_alloc_error(obj_layout(sz));
    }
    let o = p.cast::<LeanObject>();
    // SAFETY: freshly allocated, exclusively owned, at least 8 bytes.
    unsafe { (&raw mut (*o).m_cs_sz).write(0) };
    o
}

/// `lean_alloc_ctor_memory` under `LEAN_MIMALLOC` (`lean.h:454-461`): small
/// allocation plus deterministic zeroing of the final padded word.
///
/// # Safety
/// As [`alloc_small`].
// UNSAFE-LEDGER: FLN-UL-0003
#[allow(unsafe_code)]
pub(crate) unsafe fn alloc_ctor_memory(sz: usize) -> *mut LeanObject {
    let aligned = align_obj_size(sz);
    let o = unsafe { alloc_small(sz) };
    if aligned > sz {
        // SAFETY: the block is `aligned` bytes; the final word is in-bounds.
        unsafe {
            o.cast::<u8>()
                .add(aligned - size_of::<usize>())
                .cast::<usize>()
                .write(0);
        }
    }
    o
}

/// Release a CompatHeap block of known byte size (small callers pass the
/// header's `m_cs_sz`; big callers pass the recomputed category byte size,
/// mirroring `lean_free_object`, `object.cpp:271-280`).
///
/// Shadow discipline: with shadows enabled the memory is quarantined (header
/// tag poisoned to `TAG_RESERVED`, block retained) and faulty releases are
/// skipped entirely — quarantine, never corruption.
///
/// # Safety
/// `o` must have been minted by this module with byte size `size` and must
/// not be used after this call (shadow mode detects violations; release mode
/// trusts the caller exactly as the Reference does).
// UNSAFE-LEDGER: FLN-UL-0004
#[allow(unsafe_code)]
pub(crate) unsafe fn release_with_size(o: *mut LeanObject, size: usize, op: &'static str) {
    // SAFETY: caller guarantees `o` is a live membrane object; the tag read
    // precedes any state change.
    let category = unsafe { (&raw const (*o).m_tag).read() };
    match shadow::on_free(o as usize, category, op) {
        shadow::FreeVerdict::Release => {
            // SAFETY: minted by alloc_small/alloc_big with exactly this
            // size/alignment pair.
            unsafe { dealloc(o.cast::<u8>(), obj_layout(size)) };
        }
        shadow::FreeVerdict::Quarantine => {
            // SAFETY: block retained; poisoning the tag keeps later misuse
            // deterministically detectable.
            unsafe { (&raw mut (*o).m_tag).write(TAG_RESERVED) };
        }
        shadow::FreeVerdict::Fault => {}
    }
}

/// Record a freshly initialized object with the shadow registry (no-op when
/// shadows are disabled). Called by every constructor after header init.
pub(crate) fn note_alloc(o: *mut LeanObject, size: usize, category: u8) {
    shadow::on_alloc(o as usize, size, category);
}
