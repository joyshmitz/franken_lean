//! The exported `lean_*` C symbol surface (plan §6.5/§6.6, bead
//! franken_lean-83r; the per-symbol census join fln-lld deferred here).
//!
//! Every function in this module is one exported symbol of the pinned ABI:
//! `#[unsafe(export_name = "…")]` under an `extern "C"` signature copied
//! from the generated census (`fln-rt::abi::FUNCTION_CENSUS`, itself
//! extracted from the pinned `lean.h` — Rule D5: derived, never remembered).
//! The reviewed status of every census export symbol lives in
//! `ci/ABI_EXPORT_STATUS.txt`; `tools/structure-guard` enforces the join in
//! both directions (an export without an implemented status row, and an
//! implemented row without an export site, both fail CI) — there is no
//! unclassified symbol (§6.5).
//!
//! **Panic law (§6.5):** no Rust panic crosses these boundaries. Every
//! function is `extern "C"`, so any internal panic aborts the process at
//! the boundary (Rust 2024 abort-on-unwind shim) — termination per policy,
//! never a fabricated Lean result. Where the pin *defines* an observable
//! failure behavior (`lean_internal_panic`'s message + exit path), the
//! wrapper reproduces that behavior exactly.
//!
//! **Membrane support symbols:** under the pin's `LEAN_MIMALLOC` config the
//! `lean.h` inlines call `mi_malloc_small`/`mi_free` directly
//! (`lean.h:436-441`, `490-497`), so generated C — stage0 translation units
//! included — link-demands those two symbols alongside the `lean_*` census.
//! They are exported here as the membrane's raw small heap (status
//! `RawPlatform` in the export-status ledger).
//!
//! Slice-1 typed restrictions (tracked in `ci/ABI_EXPORT_STATUS.txt`, never
//! silent): closure application (`lean_apply_*`) — franken_lean-7xe; tasks /
//! IO (`lean_io_*`, `lean_task_*`) — fln-3gv; bignum arithmetic
//! (`lean_nat_big_*`, `lean_int_big_*`) — the fln-bignum shim; panic-path
//! Lean-buffered stderr and backtrace printing — fln-3gv (messages go to the
//! process stderr until the IO plane exists).

use crate::contract::TAG_MPZ;
use crate::layout::{LeanObject, LeanStringObject};
use crate::membrane;
use crate::object;
use crate::rc;
use crate::tagged::is_scalar;
use core::ffi::{c_char, c_uint, c_void};
use core::sync::atomic::{AtomicBool, Ordering};
use std::cell::Cell;
use std::io::Write;

// ---------------------------------------------------------------- panic core

/// `g_exit_on_panic` (`object.cpp:113`).
static EXIT_ON_PANIC: AtomicBool = AtomicBool::new(false);
/// `g_panic_messages` (`object.cpp:114`).
static PANIC_MESSAGES: AtomicBool = AtomicBool::new(true);

/// `should_abort_on_panic` (`object.cpp`): the `LEAN_ABORT_ON_PANIC`
/// environment probe, checked at panic time exactly as upstream.
fn should_abort_on_panic() -> bool {
    std::env::var_os("LEAN_ABORT_ON_PANIC").is_some()
}

/// `lean_internal_panic`'s body (`object.cpp:91-95`): message to the process
/// stderr, then abort (env) or `exit(1)`.
fn internal_panic_impl(msg: &str) -> ! {
    let mut err = std::io::stderr().lock();
    let _ = writeln!(err, "INTERNAL PANIC: {msg}");
    let _ = err.flush();
    if should_abort_on_panic() {
        std::process::abort();
    }
    std::process::exit(1);
}

/// `lean_panic_impl` (`object.cpp:139-146` shape): optional message, then
/// the exit/abort policy. Slice-1 restriction (status ledger): upstream
/// routes non-fatal messages through the Lean IO stderr buffer
/// (`io_eprintln`) and can print a backtrace; both need the fln-3gv IO
/// plane, so every message goes to the process stderr here.
fn panic_impl(msg: &[u8]) {
    if PANIC_MESSAGES.load(Ordering::Relaxed) {
        let mut err = std::io::stderr().lock();
        let _ = err.write_all(msg);
        let _ = err.write_all(b"\n");
        let _ = err.flush();
    }
    if EXIT_ON_PANIC.load(Ordering::Relaxed) {
        std::process::exit(1);
    }
    if should_abort_on_panic() {
        std::process::abort();
    }
}

thread_local! {
    /// `g_heartbeat` (`interrupt.cpp:18`): thread-local allocation/progress
    /// counter. The calibrated heartbeat *law* (fuel parity) is bead
    /// fln-8w8/G0-6; the counting twin lives here so the exported symbol has
    /// the pin's exact storage discipline from day one.
    static HEARTBEAT: Cell<usize> = const { Cell::new(0) };
}

/// Test hook: current thread's heartbeat count.
#[cfg(test)]
pub(crate) fn heartbeat_value() -> usize {
    HEARTBEAT.with(Cell::get)
}

// ---------------------------------------------------------------- UTF-8 core
// Safe ports of `utf8.cpp` — bit-for-bit the pin's semantics, including its
// deliberate quirks (`get_utf8_size` treats every invalid lead byte as one
// char, so `lean_utf8_strlen` over garbage counts garbage bytes — that IS
// the contract).

/// `get_utf8_size` (`utf8.cpp:16-33`).
fn get_utf8_size(c: u8) -> usize {
    if c & 0x80 == 0 {
        1
    } else if c & 0xE0 == 0xC0 {
        2
    } else if c & 0xF0 == 0xE0 {
        3
    } else if c & 0xF8 == 0xF0 {
        4
    } else if c & 0xFC == 0xF8 {
        5
    } else if c & 0xFE == 0xFC {
        6
    } else {
        1 // 0xFF and stray continuations: 1, exactly as upstream
    }
}

/// `validate_utf8_one` (`utf8.cpp:223-268`).
fn validate_utf8_one(s: &[u8], pos: &mut usize) -> bool {
    let size = s.len();
    let c = u32::from(s[*pos]);
    if c & 0x80 == 0 {
        *pos += 1;
    } else if c & 0xE0 == 0xC0 {
        if *pos + 1 >= size {
            return false;
        }
        let c1 = u32::from(s[*pos + 1]);
        if c1 & 0xC0 != 0x80 {
            return false;
        }
        let r = ((c & 0x1F) << 6) | (c1 & 0x3F);
        if r < 0x80 {
            return false;
        }
        *pos += 2;
    } else if c & 0xF0 == 0xE0 {
        if *pos + 2 >= size {
            return false;
        }
        let c1 = u32::from(s[*pos + 1]);
        let c2 = u32::from(s[*pos + 2]);
        if c1 & 0xC0 != 0x80 || c2 & 0xC0 != 0x80 {
            return false;
        }
        let r = ((c & 0x0F) << 12) | ((c1 & 0x3F) << 6) | (c2 & 0x3F);
        if r < 0x800 || (0xD800..=0xDFFF).contains(&r) {
            return false;
        }
        *pos += 3;
    } else if c & 0xF8 == 0xF0 {
        if *pos + 3 >= size {
            return false;
        }
        let c1 = u32::from(s[*pos + 1]);
        let c2 = u32::from(s[*pos + 2]);
        let c3 = u32::from(s[*pos + 3]);
        if c1 & 0xC0 != 0x80 || c2 & 0xC0 != 0x80 || c3 & 0xC0 != 0x80 {
            return false;
        }
        let r = ((c & 0x07) << 18) | ((c1 & 0x3F) << 12) | ((c2 & 0x3F) << 6) | (c3 & 0x3F);
        if !(0x10000..=0x10FFFF).contains(&r) {
            return false;
        }
        *pos += 4;
    } else {
        return false;
    }
    true
}

/// `validate_utf8` (`utf8.cpp:270-276`): on failure `pos` is the end of the
/// valid prefix and `i` the codepoints seen so far.
fn validate_utf8(s: &[u8], pos: &mut usize, i: &mut usize) -> bool {
    while *pos < s.len() {
        if !validate_utf8_one(s, pos) {
            return false;
        }
        *i += 1;
    }
    true
}

/// `utf8_strlen(str, sz)` = `lean_utf8_n_strlen` (`utf8.cpp:49-58`).
fn utf8_n_strlen_impl(s: &[u8]) -> usize {
    let mut r = 0usize;
    let mut i = 0usize;
    while i < s.len() {
        i += get_utf8_size(s[i]);
        r += 1;
    }
    r
}

/// `lean_mk_string_lossy_recover` (`object.cpp:1989-2002`): the pin's exact
/// U+FFFD replacement walk, `i` counting replacements as codepoints.
///
/// # Safety
/// Only the constructor call is unsafe; the recovered bytes are an owned
/// copy, so the caller owes nothing beyond the slice being readable.
// UNSAFE-LEDGER: FLN-UL-0068
#[allow(unsafe_code)]
unsafe fn mk_string_lossy_recover(s: &[u8], mut pos: usize, mut i: usize) -> *mut LeanObject {
    let mut out: Vec<u8> = s[..pos].to_vec();
    let mut start = pos;
    while pos < s.len() {
        if !validate_utf8_one(s, &mut pos) {
            out.extend_from_slice(&s[start..pos]);
            out.extend_from_slice("\u{FFFD}".as_bytes());
            pos += 1;
            while pos < s.len() && s[pos] & 0xC0 == 0x80 {
                pos += 1;
            }
            start = pos;
        }
        i += 1;
    }
    out.extend_from_slice(&s[start..pos]);
    // SAFETY: constructor over an owned byte copy with the recomputed count.
    unsafe { object::mk_string_unchecked(&out, i) }
}

/// Shared body of `lean_mk_string_from_bytes` (`object.cpp:2005-2012`).
///
/// # Safety
/// `s`/`sz` must describe `sz` readable bytes (or `sz == 0`).
// UNSAFE-LEDGER: FLN-UL-0069
#[allow(unsafe_code)]
unsafe fn mk_string_from_bytes_impl(s: *const c_char, sz: usize) -> *mut LeanObject {
    // SAFETY: caller (C contract) vouches for sz readable bytes.
    let bytes = if sz == 0 {
        &[][..]
    } else {
        unsafe { core::slice::from_raw_parts(s.cast::<u8>(), sz) }
    };
    let mut pos = 0usize;
    let mut i = 0usize;
    if validate_utf8(bytes, &mut pos, &mut i) {
        // SAFETY: constructor over an owned byte copy.
        unsafe { object::mk_string_unchecked(&bytes[..pos], i) }
    } else {
        // SAFETY: bytes readable per this function's own contract.
        unsafe { mk_string_lossy_recover(bytes, pos, i) }
    }
}

/// `strlen` over a NUL-terminated C string.
///
/// # Safety
/// `s` must be a valid NUL-terminated string.
// UNSAFE-LEDGER: FLN-UL-0070
#[allow(unsafe_code)]
unsafe fn c_strlen(s: *const c_char) -> usize {
    // SAFETY: caller vouches for NUL termination; CStr walks to the NUL.
    unsafe { core::ffi::CStr::from_ptr(s).to_bytes().len() }
}

/// String salient reads without copying: `(m_size, data ptr)`.
///
/// # Safety
/// `o` live string object.
// UNSAFE-LEDGER: FLN-UL-0071
#[allow(unsafe_code)]
unsafe fn string_size_and_data(o: *mut LeanObject) -> (usize, *const u8) {
    // SAFETY: live string per caller contract; m_size bytes are salient.
    unsafe {
        let s = o.cast::<LeanStringObject>();
        (
            (&raw const (*s).m_size).read(),
            (&raw const (*s).m_data).cast::<u8>(),
        )
    }
}

// ================================================================ exports
// One `#[unsafe(export_name)]` site per census symbol; signatures are the
// census signatures. Rust-side callers (tests) use the `export_*` names.

// ---- membrane: the small heap ------------------------------------------------

/// `lean_alloc_small` (`lean.h:400`, SMALL_ALLOCATOR surface): raw
/// small-heap block of `sz` bytes; OOM panics like the pin's allocator.
// UNSAFE-LEDGER: FLN-UL-0072
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_alloc_small")]
pub(crate) extern "C" fn export_lean_alloc_small(sz: c_uint, slot_idx: c_uint) -> *mut c_void {
    debug_assert!(sz > 0 && sz.is_multiple_of(8));
    debug_assert!(slot_idx == sz / 8 - 1, "lean_get_slot_idx law (lean.h:394)");
    let _ = slot_idx;
    // SAFETY: sz > 0 per the inline callers' contract (asserted upstream).
    let p = unsafe { membrane::small_alloc_raw(sz as usize) };
    if p.is_null() {
        internal_panic_impl("out of memory");
    }
    p.cast::<c_void>()
}

/// `lean_free_small` (`lean.h:401`): sizeless small-heap release.
// UNSAFE-LEDGER: FLN-UL-0073
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_free_small")]
pub(crate) extern "C" fn export_lean_free_small(p: *mut c_void) {
    // SAFETY: p was minted by the small heap per the ABI contract.
    unsafe { membrane::small_free_raw(p.cast::<u8>()) };
}

/// `lean_small_mem_size` (`lean.h:402`): usable size of a small-heap block.
// UNSAFE-LEDGER: FLN-UL-0074
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_small_mem_size")]
pub(crate) extern "C" fn export_lean_small_mem_size(p: *mut c_void) -> c_uint {
    // SAFETY: p live small-heap block per the ABI contract.
    let sz = unsafe { membrane::small_mem_size_raw(p.cast::<u8>()) };
    sz as c_uint
}

/// `mi_malloc_small` (mimalloc.h:126; membrane support): the pin's
/// `LEAN_MIMALLOC` inlines call this directly (`lean.h:436-441`). Null on
/// exhaustion — the C inline performs the OOM panic itself.
// UNSAFE-LEDGER: FLN-UL-0075
#[allow(unsafe_code)]
#[unsafe(export_name = "mi_malloc_small")]
pub(crate) extern "C" fn export_mi_malloc_small(size: usize) -> *mut c_void {
    if size == 0 {
        // malloc(0) contract: a unique releasable pointer.
        // SAFETY: 8-byte block stands in for the zero-size allocation.
        return unsafe { membrane::small_alloc_raw(8) }.cast::<c_void>();
    }
    // SAFETY: size > 0.
    unsafe { membrane::small_alloc_raw(size) }.cast::<c_void>()
}

/// `mi_free` (mimalloc.h:115; membrane support): sizeless release,
/// null-safe like `free`.
// UNSAFE-LEDGER: FLN-UL-0076
#[allow(unsafe_code)]
#[unsafe(export_name = "mi_free")]
pub(crate) extern "C" fn export_mi_free(p: *mut c_void) {
    if p.is_null() {
        return;
    }
    // SAFETY: non-null p was minted by the small heap per the ABI contract.
    unsafe { membrane::small_free_raw(p.cast::<u8>()) };
}

// ---- membrane: the big heap --------------------------------------------------

/// `lean_alloc_object` (`object.cpp:355-376` under `LEAN_MIMALLOC`): exact
/// `sz` bytes, `m_cs_sz = 0`; OOM = `lean_internal_panic_out_of_memory`.
// UNSAFE-LEDGER: FLN-UL-0077
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_alloc_object")]
pub(crate) extern "C" fn export_lean_alloc_object(sz: usize) -> *mut LeanObject {
    // SAFETY: fresh exclusive block; cs_sz written by the callee.
    let o = unsafe { membrane::alloc_big_nullable(sz) };
    if o.is_null() {
        internal_panic_impl("out of memory");
    }
    o
}

/// `lean_free_object` (`object.cpp:271-280`): category-dispatched release —
/// big categories by recomputed byte size, `LeanMPZ` drops its limbs first,
/// everything else through the small heap.
// UNSAFE-LEDGER: FLN-UL-0078
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_free_object")]
pub(crate) extern "C" fn export_lean_free_object(o: *mut LeanObject) {
    // SAFETY: o is a live membrane object whose storage the caller releases;
    // the byte size is recomputed from salient fields exactly as upstream,
    // and release_with_size discriminates small/big on the header's cs_sz.
    unsafe {
        let h = rc::read_header(o);
        if h.tag == TAG_MPZ {
            object::mpz_drop_limbs(o);
        }
        let sz = rc::object_byte_size(o);
        membrane::release_with_size(o, sz, "export.free_object");
    }
}

// ---- heartbeat ---------------------------------------------------------------

/// `lean_inc_heartbeat` (`interrupt.cpp:28`): thread-local counter.
// UNSAFE-LEDGER: FLN-UL-0079
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_inc_heartbeat")]
pub(crate) extern "C" fn export_lean_inc_heartbeat() {
    HEARTBEAT.with(|h| h.set(h.get().wrapping_add(1)));
}

// ---- reference counting ------------------------------------------------------

/// `lean_dec_ref_cold` (`object.cpp:443-457`): the death test plus the
/// iterative deletion loop.
// UNSAFE-LEDGER: FLN-UL-0080
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_dec_ref_cold")]
pub(crate) extern "C" fn export_lean_dec_ref_cold(o: *mut LeanObject) {
    // SAFETY: caller observed rc == 1 || rc < 0 and gives up one reference
    // (the lean_dec_ref inline's contract, lean.h:574-580).
    unsafe { rc::dec_ref_cold(o) };
}

/// `lean_mark_persistent` (`object.cpp:553-620`).
// UNSAFE-LEDGER: FLN-UL-0081
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mark_persistent")]
pub(crate) extern "C" fn export_lean_mark_persistent(o: *mut LeanObject) {
    // SAFETY: o valid object or boxed scalar; graph not concurrently mutated
    // (upstream's own requirement).
    unsafe { rc::mark_persistent(o) };
}

/// `lean_mark_mt` (`object.cpp:633-681`).
// UNSAFE-LEDGER: FLN-UL-0082
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mark_mt")]
pub(crate) extern "C" fn export_lean_mark_mt(o: *mut LeanObject) {
    // SAFETY: as lean_mark_persistent.
    unsafe { rc::mark_mt(o) };
}

// ---- byte sizes --------------------------------------------------------------

/// `lean_object_byte_size` (`object.cpp:242-259`).
// UNSAFE-LEDGER: FLN-UL-0083
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_object_byte_size")]
pub(crate) extern "C" fn export_lean_object_byte_size(o: *mut LeanObject) -> usize {
    // SAFETY: o live non-scalar object per the ABI contract.
    unsafe { rc::object_byte_size(o) }
}

/// `lean_object_data_byte_size` (`object.cpp:237-259`): salient bytes only —
/// big categories from `m_size` (not capacity), small categories from
/// `m_cs_sz`; the upstream branch structure is kept literally.
// UNSAFE-LEDGER: FLN-UL-0084
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_object_data_byte_size")]
pub(crate) extern "C" fn export_lean_object_data_byte_size(o: *mut LeanObject) -> usize {
    use crate::contract::{TAG_ARRAY, TAG_CLOSURE, TAG_SCALAR_ARRAY, TAG_STRING};
    use crate::layout::{LeanArrayObject, LeanClosureObject, LeanSarrayObject};
    // SAFETY: o live non-scalar object; each arm reads only that category's
    // salient fields, mirroring object.cpp:237-259.
    unsafe {
        let h = rc::read_header(o);
        match h.tag {
            t if t == TAG_ARRAY => {
                size_of::<LeanArrayObject>()
                    + size_of::<*mut LeanObject>() * object::array_fields(o).0
            }
            t if t == TAG_SCALAR_ARRAY => {
                let (elem, size, _, _) = object::sarray_fields(o);
                size_of::<LeanSarrayObject>() + usize::from(elem) * size
            }
            t if t == TAG_STRING => {
                let (size, _) = string_size_and_data(o);
                size_of::<LeanStringObject>() + size
            }
            t if t == TAG_CLOSURE => {
                let c = o.cast::<LeanClosureObject>();
                size_of::<LeanClosureObject>()
                    + size_of::<*mut LeanObject>()
                        * usize::from((&raw const (*c).m_num_fixed).read())
            }
            _ => usize::from(h.cs_sz),
        }
    }
}

// ---- panics ------------------------------------------------------------------

/// `lean_internal_panic` (`object.cpp:91-95`).
// UNSAFE-LEDGER: FLN-UL-0085
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_internal_panic")]
pub(crate) extern "C" fn export_lean_internal_panic(msg: *const c_char) -> ! {
    // SAFETY: msg is a NUL-terminated C string per the contract.
    let text = unsafe { core::ffi::CStr::from_ptr(msg) }.to_string_lossy();
    internal_panic_impl(&text)
}

/// `lean_internal_panic_out_of_memory` (`object.cpp:97-99`).
// UNSAFE-LEDGER: FLN-UL-0086
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_internal_panic_out_of_memory")]
pub(crate) extern "C" fn export_lean_internal_panic_out_of_memory() -> ! {
    internal_panic_impl("out of memory")
}

/// `lean_internal_panic_overflow` (`object.cpp:109-111`).
// UNSAFE-LEDGER: FLN-UL-0087
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_internal_panic_overflow")]
pub(crate) extern "C" fn export_lean_internal_panic_overflow() -> ! {
    internal_panic_impl("integer overflow")
}

/// `lean_internal_panic_rc_overflow` (`object.cpp:105-107`).
// UNSAFE-LEDGER: FLN-UL-0088
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_internal_panic_rc_overflow")]
pub(crate) extern "C" fn export_lean_internal_panic_rc_overflow() -> ! {
    internal_panic_impl("reference counter overflowed")
}

/// `lean_internal_panic_unreachable` (`object.cpp:101-103`).
// UNSAFE-LEDGER: FLN-UL-0089
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_internal_panic_unreachable")]
pub(crate) extern "C" fn export_lean_internal_panic_unreachable() -> ! {
    internal_panic_impl("unreachable code has been reached")
}

/// `lean_panic` (`object.cpp` panic surface).
// UNSAFE-LEDGER: FLN-UL-0090
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_panic")]
pub(crate) extern "C" fn export_lean_panic(msg: *const c_char, force_stderr: bool) {
    let _ = force_stderr; // both routes are the process stderr pre-fln-3gv
    // SAFETY: msg NUL-terminated per the contract.
    let bytes = unsafe { core::ffi::CStr::from_ptr(msg) }.to_bytes();
    panic_impl(bytes);
}

/// `lean_panic_fn` (`object.cpp`): print the Lean string `msg` (consumed),
/// return `default_val` (ownership passes through).
// UNSAFE-LEDGER: FLN-UL-0091
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_panic_fn")]
pub(crate) extern "C" fn export_lean_panic_fn(
    default_val: *mut LeanObject,
    msg: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: msg is a live string object; m_size-1 strips the NUL exactly
    // as upstream; the dec gives up the consumed reference.
    unsafe {
        let (size, data) = string_size_and_data(msg);
        let bytes = core::slice::from_raw_parts(data, size.saturating_sub(1));
        panic_impl(bytes);
        if !is_scalar(msg) {
            rc::dec_ref(msg);
        }
    }
    default_val
}

/// `lean_panic_fn_borrowed` (`object.cpp`): borrowed default is retained
/// before delegating.
// UNSAFE-LEDGER: FLN-UL-0092
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_panic_fn_borrowed")]
pub(crate) extern "C" fn export_lean_panic_fn_borrowed(
    default_val: *mut LeanObject,
    msg: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: default_val live (borrowed) — retaining it mirrors lean_inc.
    unsafe {
        if !is_scalar(default_val) {
            rc::inc_ref_n(default_val, 1);
        }
    }
    export_lean_panic_fn(default_val, msg)
}

/// `lean_set_exit_on_panic` (`object.cpp:116-118`).
// UNSAFE-LEDGER: FLN-UL-0093
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_set_exit_on_panic")]
pub(crate) extern "C" fn export_lean_set_exit_on_panic(flag: bool) {
    EXIT_ON_PANIC.store(flag, Ordering::Relaxed);
}

/// `lean_set_panic_messages` (`object.cpp:125-127`).
// UNSAFE-LEDGER: FLN-UL-0094
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_set_panic_messages")]
pub(crate) extern "C" fn export_lean_set_panic_messages(flag: bool) {
    PANIC_MESSAGES.store(flag, Ordering::Relaxed);
}

// ---- strings -----------------------------------------------------------------

/// `lean_mk_string_unchecked` (`object.cpp:1981-1987`).
// UNSAFE-LEDGER: FLN-UL-0095
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mk_string_unchecked")]
pub(crate) extern "C" fn export_lean_mk_string_unchecked(
    s: *const c_char,
    sz: usize,
    len: usize,
) -> *mut LeanObject {
    // SAFETY: sz readable bytes per the contract; constructor copies them.
    unsafe {
        let bytes = if sz == 0 {
            &[][..]
        } else {
            core::slice::from_raw_parts(s.cast::<u8>(), sz)
        };
        object::mk_string_unchecked(bytes, len)
    }
}

/// `lean_mk_string_from_bytes` (`object.cpp:2005-2012`): validate, else
/// lossy-recover with U+FFFD.
// UNSAFE-LEDGER: FLN-UL-0096
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mk_string_from_bytes")]
pub(crate) extern "C" fn export_lean_mk_string_from_bytes(
    s: *const c_char,
    sz: usize,
) -> *mut LeanObject {
    // SAFETY: sz readable bytes per the contract.
    unsafe { mk_string_from_bytes_impl(s, sz) }
}

/// `lean_mk_string_from_bytes_unchecked` (`object.cpp:2014-2016`).
// UNSAFE-LEDGER: FLN-UL-0097
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mk_string_from_bytes_unchecked")]
pub(crate) extern "C" fn export_lean_mk_string_from_bytes_unchecked(
    s: *const c_char,
    sz: usize,
) -> *mut LeanObject {
    // SAFETY: sz readable bytes per the contract.
    unsafe {
        let bytes = if sz == 0 {
            &[][..]
        } else {
            core::slice::from_raw_parts(s.cast::<u8>(), sz)
        };
        object::mk_string_unchecked(bytes, utf8_n_strlen_impl(bytes))
    }
}

/// `lean_mk_string` (`object.cpp:2018-2020`).
// UNSAFE-LEDGER: FLN-UL-0098
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mk_string")]
pub(crate) extern "C" fn export_lean_mk_string(s: *const c_char) -> *mut LeanObject {
    // SAFETY: NUL-terminated string per the contract.
    unsafe {
        let len = c_strlen(s);
        mk_string_from_bytes_impl(s, len)
    }
}

/// `lean_mk_ascii_string_unchecked` (`object.cpp:2022-2025`).
// UNSAFE-LEDGER: FLN-UL-0099
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_mk_ascii_string_unchecked")]
pub(crate) extern "C" fn export_lean_mk_ascii_string_unchecked(
    s: *const c_char,
) -> *mut LeanObject {
    // SAFETY: NUL-terminated ASCII string per the contract.
    unsafe {
        let len = c_strlen(s);
        let bytes = core::slice::from_raw_parts(s.cast::<u8>(), len);
        object::mk_string_unchecked(bytes, len)
    }
}

/// `lean_utf8_strlen` (`utf8.cpp:35-43`): NUL-terminated walk with the
/// pin's `get_utf8_size` stepping (garbage bytes count — bug-compatible).
// UNSAFE-LEDGER: FLN-UL-0100
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_utf8_strlen")]
pub(crate) extern "C" fn export_lean_utf8_strlen(s: *const c_char) -> usize {
    // SAFETY: NUL-terminated string; the walk can step past the NUL exactly
    // as upstream's pointer walk does when a lead byte overstates its size —
    // the byte range up to (and semantically past) the NUL is readable per
    // the C string contract this symbol inherits from the pin.
    unsafe {
        let mut p = s.cast::<u8>();
        let mut r = 0usize;
        while p.read() != 0 {
            p = p.add(get_utf8_size(p.read()));
            r += 1;
        }
        r
    }
}

/// `lean_utf8_n_strlen` (`utf8.cpp:49-58`).
// UNSAFE-LEDGER: FLN-UL-0101
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_utf8_n_strlen")]
pub(crate) extern "C" fn export_lean_utf8_n_strlen(s: *const c_char, n: usize) -> usize {
    // SAFETY: n readable bytes per the contract.
    unsafe {
        let bytes = if n == 0 {
            &[][..]
        } else {
            core::slice::from_raw_parts(s.cast::<u8>(), n)
        };
        utf8_n_strlen_impl(bytes)
    }
}

/// `lean_string_eq_cold` (`object.cpp`): byte compare over `m_size` bytes
/// (the sizes are already known equal — the inline's fast path checked).
// UNSAFE-LEDGER: FLN-UL-0102
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_eq_cold")]
pub(crate) extern "C" fn export_lean_string_eq_cold(
    s1: *mut LeanObject,
    s2: *mut LeanObject,
) -> bool {
    // SAFETY: both live strings; m_size bytes are salient per the string law.
    unsafe {
        let (n1, d1) = string_size_and_data(s1);
        let (_, d2) = string_size_and_data(s2);
        core::slice::from_raw_parts(d1, n1) == core::slice::from_raw_parts(d2, n1)
    }
}

// ---- extern-census symbols (declared by generated C itself, not lean.h) ------
// The stage0 demand audit surfaced these: generated C emits its own extern
// declarations for @[extern] runtime symbols (contracts/extern_census.tsv
// universe). Status rows use the `extern` kind.

/// `lean_sorry` (`object.cpp:208-211`; extern census `sorryAx`): executing a
/// sorry is an internal panic.
// UNSAFE-LEDGER: FLN-UL-0108
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_sorry")]
pub(crate) extern "C" fn export_lean_sorry(_synthetic: u8) -> *mut LeanObject {
    internal_panic_impl("executed 'sorry'")
}

/// `lean_system_platform_nbits` (`platform.cpp:12-18`; extern census
/// `System.Platform.getNumBits`): boxed 64 on the certified targets (the
/// crate refuses to compile elsewhere). The argument is the opaque unit
/// thunk token — a scalar, never dec'd, exactly as upstream ignores it.
// UNSAFE-LEDGER: FLN-UL-0109
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_system_platform_nbits")]
pub(crate) extern "C" fn export_lean_system_platform_nbits(
    _unit: *mut LeanObject,
) -> *mut LeanObject {
    crate::tagged::boxi(64)
}

/// `lean_string_from_utf8_unchecked` (`object.cpp`; extern census
/// `String.ofByteArray`): consume a byte array, produce a string with the
/// bug-compatible codepoint count.
// UNSAFE-LEDGER: FLN-UL-0110
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_from_utf8_unchecked")]
pub(crate) extern "C" fn export_lean_string_from_utf8_unchecked(
    a: *mut LeanObject,
) -> *mut LeanObject {
    // SAFETY: a is a live byte array whose m_size bytes are salient; the
    // consumed reference is released through the internal rc twin.
    unsafe {
        let (_, size, _, data) = object::sarray_fields(a);
        let bytes = if size == 0 {
            &[][..]
        } else {
            core::slice::from_raw_parts(data.cast_const(), size)
        };
        let r = object::mk_string_unchecked(bytes, utf8_n_strlen_impl(bytes));
        rc::dec_ref(a);
        r
    }
}

/// `lean_string_to_utf8` (`object.cpp`; extern census `String.toByteArray` /
/// `String.toUTF8`): borrowed string to a fresh byte array of its `m_size-1`
/// content bytes.
// UNSAFE-LEDGER: FLN-UL-0111
#[allow(unsafe_code)]
#[unsafe(export_name = "lean_string_to_utf8")]
pub(crate) extern "C" fn export_lean_string_to_utf8(s: *mut LeanObject) -> *mut LeanObject {
    // SAFETY: s is a live (borrowed) string; the new sarray's data bytes are
    // fully initialized by the copy before return.
    unsafe {
        let (size, data) = string_size_and_data(s);
        let sz = size.saturating_sub(1);
        let r = object::alloc_sarray(1, sz, sz);
        let (_, _, _, dst) = object::sarray_fields(r);
        core::ptr::copy_nonoverlapping(data, dst, sz);
        r
    }
}
