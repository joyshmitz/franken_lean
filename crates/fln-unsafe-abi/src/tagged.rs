//! Tagged-pointer scalars — small `Nat`s box as odd pointers exactly as
//! upstream (`lean.h:324-326`): `box(n) = (n << 1) | 1`, `unbox(p) = p >> 1`,
//! `is_scalar(p) = p & 1`. Pure address arithmetic; no dereference, no unsafe.

use crate::layout::LeanObject;

/// `lean_is_scalar` (`lean.h:324`).
#[inline(always)]
pub(crate) fn is_scalar(o: *mut LeanObject) -> bool {
    (o as usize) & 1 == 1
}

/// `lean_box` (`lean.h:325`). The top bit of `n` is discarded exactly as in
/// C's left shift; callers stay within `MAX_SMALL_NAT = usize::MAX >> 1`.
#[inline(always)]
pub(crate) fn boxi(n: usize) -> *mut LeanObject {
    core::ptr::without_provenance_mut((n << 1) | 1)
}

/// `lean_unbox` (`lean.h:326`).
#[inline(always)]
pub(crate) fn unbox(o: *mut LeanObject) -> usize {
    (o as usize) >> 1
}

/// `LEAN_MAX_SMALL_NAT` (`lean.h:1380`, expression `(SIZE_MAX >> 1)` recorded
/// in the contract as `MAX_SMALL_NAT_EXPR`) evaluated for the certified
/// 64-bit targets.
pub(crate) const MAX_SMALL_NAT: usize = usize::MAX >> 1;
