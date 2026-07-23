//! fln-lld slice-1 verification: layout tests GENERATED from the contract
//! tables (never hand-written offsets), RC balance property tests, ownership
//! shadow mutation kills, tri-state transitions, bounded-stack teardown, and
//! the Marrow half of the C4 native-ABI probe rig.
//!
//! Every test takes the crate-wide lock: the shadow registry is global state
//! and the membrane consults it on every release.

use crate::contract::{self, FieldSpec};
use crate::handle::{EXTERNAL_FINALIZED, Obj};
use crate::layout::*;
use crate::membrane::align_obj_size;
use crate::shadow::{self, EventKind};
use crate::tagged;
use std::mem::offset_of;
use std::sync::atomic::Ordering;
use std::sync::{Mutex, MutexGuard};

static TEST_LOCK: Mutex<()> = Mutex::new(());

fn lock() -> MutexGuard<'static, ()> {
    TEST_LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

// ================================================================ layout law

/// (size, align) of a contract C type on the certified 64-bit LE targets.
fn c_type_info(c_type: &str) -> (usize, usize) {
    if c_type.contains('*') || c_type.ends_with("_proc") {
        return (8, 8);
    }
    match c_type {
        "int" | "unsigned" | "uint32_t" => (4, 4),
        "size_t" => (8, 8),
        "uint16_t" => (2, 2),
        "uint8_t" | "char" => (1, 1),
        "lean_object" => (8, 4),
        other => panic!("layout computer: unmapped C type {other:?}"),
    }
}

fn align_up(v: usize, a: usize) -> usize {
    v.div_ceil(a) * a
}

/// Compute field byte offsets and struct size from the generated contract
/// field specs, per the C layout rules (natural alignment; bitfield runs
/// packed LSB-first into their declared unit — G0-1 item 3).
fn c_struct_layout(fields: &[FieldSpec]) -> (Vec<(&'static str, usize)>, usize) {
    let mut offsets = Vec::new();
    let mut cur = 0usize;
    let mut max_align = 1usize;
    let mut i = 0;
    while i < fields.len() {
        let f = &fields[i];
        if let Some(_bits) = f.bits {
            // A run of bitfields sharing one unit of the declared type.
            let (unit_sz, unit_align) = c_type_info(f.c_type);
            let unit_off = align_up(cur, unit_align);
            max_align = max_align.max(unit_align);
            let mut bit_cursor = 0usize;
            while i < fields.len() {
                let Some(b) = fields[i].bits else { break };
                let b = usize::from(b);
                assert!(
                    b.is_multiple_of(8),
                    "contract bitfield {} not byte-aligned",
                    fields[i].name
                );
                assert!(bit_cursor + b <= unit_sz * 8, "bitfield unit overflow");
                offsets.push((fields[i].name, unit_off + bit_cursor / 8));
                bit_cursor += b;
                i += 1;
            }
            cur = unit_off + unit_sz;
            continue;
        }
        let (sz, al) = c_type_info(f.c_type);
        let off = align_up(cur, al);
        offsets.push((f.name, off));
        max_align = max_align.max(al);
        if f.array == Some("[]") {
            // Flexible array member: contributes offset and alignment only.
            cur = off;
        } else {
            cur = off + sz;
        }
        i += 1;
    }
    (offsets, align_up(cur, max_align))
}

/// The mirror registry: contract struct name -> (Rust size, field offsets).
/// The OFFSETS come from the compiler; the EXPECTATIONS come from the
/// contract tables — nothing here is a remembered constant.
fn mirror_layout(name: &str) -> (usize, Vec<(&'static str, usize)>) {
    match name {
        "lean_object" => (
            size_of::<LeanObject>(),
            vec![
                ("m_rc", offset_of!(LeanObject, m_rc)),
                ("m_cs_sz", offset_of!(LeanObject, m_cs_sz)),
                ("m_other", offset_of!(LeanObject, m_other)),
                ("m_tag", offset_of!(LeanObject, m_tag)),
            ],
        ),
        "lean_ctor_object" => (
            size_of::<LeanCtorObject>(),
            vec![
                ("m_header", offset_of!(LeanCtorObject, m_header)),
                ("m_objs", offset_of!(LeanCtorObject, m_objs)),
            ],
        ),
        "lean_array_object" => (
            size_of::<LeanArrayObject>(),
            vec![
                ("m_header", offset_of!(LeanArrayObject, m_header)),
                ("m_size", offset_of!(LeanArrayObject, m_size)),
                ("m_capacity", offset_of!(LeanArrayObject, m_capacity)),
                ("m_data", offset_of!(LeanArrayObject, m_data)),
            ],
        ),
        "lean_sarray_object" => (
            size_of::<LeanSarrayObject>(),
            vec![
                ("m_header", offset_of!(LeanSarrayObject, m_header)),
                ("m_size", offset_of!(LeanSarrayObject, m_size)),
                ("m_capacity", offset_of!(LeanSarrayObject, m_capacity)),
                ("m_data", offset_of!(LeanSarrayObject, m_data)),
            ],
        ),
        "lean_string_object" => (
            size_of::<LeanStringObject>(),
            vec![
                ("m_header", offset_of!(LeanStringObject, m_header)),
                ("m_size", offset_of!(LeanStringObject, m_size)),
                ("m_capacity", offset_of!(LeanStringObject, m_capacity)),
                ("m_length", offset_of!(LeanStringObject, m_length)),
                ("m_data", offset_of!(LeanStringObject, m_data)),
            ],
        ),
        "lean_closure_object" => (
            size_of::<LeanClosureObject>(),
            vec![
                ("m_header", offset_of!(LeanClosureObject, m_header)),
                ("m_fun", offset_of!(LeanClosureObject, m_fun)),
                ("m_arity", offset_of!(LeanClosureObject, m_arity)),
                ("m_num_fixed", offset_of!(LeanClosureObject, m_num_fixed)),
                ("m_objs", offset_of!(LeanClosureObject, m_objs)),
            ],
        ),
        "lean_ref_object" => (
            size_of::<LeanRefObject>(),
            vec![
                ("m_header", offset_of!(LeanRefObject, m_header)),
                ("m_value", offset_of!(LeanRefObject, m_value)),
            ],
        ),
        "lean_thunk_object" => (
            size_of::<LeanThunkObject>(),
            vec![
                ("m_header", offset_of!(LeanThunkObject, m_header)),
                ("m_value", offset_of!(LeanThunkObject, m_value)),
                ("m_closure", offset_of!(LeanThunkObject, m_closure)),
            ],
        ),
        "lean_task_imp" => (
            size_of::<LeanTaskImp>(),
            vec![
                ("m_closure", offset_of!(LeanTaskImp, m_closure)),
                ("m_head_dep", offset_of!(LeanTaskImp, m_head_dep)),
                ("m_next_dep", offset_of!(LeanTaskImp, m_next_dep)),
                ("m_prio", offset_of!(LeanTaskImp, m_prio)),
                ("m_canceled", offset_of!(LeanTaskImp, m_canceled)),
                ("m_keep_alive", offset_of!(LeanTaskImp, m_keep_alive)),
                ("m_deleted", offset_of!(LeanTaskImp, m_deleted)),
            ],
        ),
        "lean_task_object" => (
            size_of::<LeanTaskObject>(),
            vec![
                ("m_header", offset_of!(LeanTaskObject, m_header)),
                ("m_value", offset_of!(LeanTaskObject, m_value)),
                ("m_imp", offset_of!(LeanTaskObject, m_imp)),
            ],
        ),
        "lean_promise_object" => (
            size_of::<LeanPromiseObject>(),
            vec![
                ("m_header", offset_of!(LeanPromiseObject, m_header)),
                ("m_result", offset_of!(LeanPromiseObject, m_result)),
            ],
        ),
        "lean_external_class" => (
            size_of::<LeanExternalClass>(),
            vec![
                ("m_finalize", offset_of!(LeanExternalClass, m_finalize)),
                ("m_foreach", offset_of!(LeanExternalClass, m_foreach)),
            ],
        ),
        "lean_external_object" => (
            size_of::<LeanExternalObject>(),
            vec![
                ("m_header", offset_of!(LeanExternalObject, m_header)),
                ("m_class", offset_of!(LeanExternalObject, m_class)),
                ("m_data", offset_of!(LeanExternalObject, m_data)),
            ],
        ),
        other => panic!("no mirror registered for contract struct {other:?}"),
    }
}

/// Layout tests generated FROM the contract module: every struct, every
/// field, offsets and sizes computed from the generated field specs and
/// compared against the compiler's view of the repr(C) mirrors.
#[test]
fn layout_mirrors_match_contract_tables() {
    let _g = lock();
    for spec in contract::OBJECT_STRUCTS {
        let (expected_fields, expected_size) = c_struct_layout(spec.fields);
        let (mirror_size, mirror_fields) = mirror_layout(spec.name);
        assert_eq!(
            mirror_size, expected_size,
            "sizeof({}) mirror vs contract-computed",
            spec.name
        );
        assert_eq!(
            mirror_fields.len(),
            expected_fields.len(),
            "field count of {} (contract line {})",
            spec.name,
            spec.line
        );
        for ((mf, moff), (cf, coff)) in mirror_fields.iter().zip(expected_fields.iter()) {
            assert_eq!(mf, cf, "field order in {}", spec.name);
            assert_eq!(moff, coff, "offsetof({}, {})", spec.name, mf);
        }
    }
}

/// The header packing law (G0-1 item 3): `m_rc` low word, then
/// `m_cs_sz:16 | m_other:8 | m_tag:8` low-to-high in the second word.
#[test]
fn header_bitfield_packing() {
    let _g = lock();
    assert_eq!(size_of::<LeanObject>(), 8);
    assert_eq!(offset_of!(LeanObject, m_rc), 0);
    assert_eq!(offset_of!(LeanObject, m_cs_sz), 4);
    assert_eq!(offset_of!(LeanObject, m_other), 6);
    assert_eq!(offset_of!(LeanObject, m_tag), 7);
}

// ================================================================ tagged

#[test]
fn tagged_pointer_law() {
    let _g = lock();
    for n in [0usize, 1, 2, 41, 1 << 20, tagged::MAX_SMALL_NAT] {
        let b = Obj::mk_nat(n);
        assert!(b.is_scalar());
        assert_eq!(b.unbox(), n);
        assert_eq!(b.obj_tag(), n); // lean_obj_tag on scalars is the value
    }
}

// ================================================================ objects

#[test]
fn ctor_header_and_scalar_facts() {
    let _g = lock();
    let c = Obj::mk_ctor(
        5,
        vec![Obj::mk_nat(1), Obj::mk_nat(2)],
        &[0xAB, 0xCD, 3, 4, 5, 6, 7, 8, 9],
    );
    let h = c.header();
    assert_eq!(h.tag, 5);
    assert_eq!(h.other, 2, "m_other = pointer-field count");
    assert_eq!(h.rc, 1);
    // Small path under the pin's LEAN_MIMALLOC config: m_cs_sz = aligned size.
    let raw = 8 + 2 * 8 + 9;
    assert_eq!(usize::from(h.cs_sz), align_obj_size(raw));
    assert_eq!(c.byte_size(), align_obj_size(raw));
    assert_eq!(c.ctor_child(0).unbox(), 1);
    assert_eq!(c.ctor_child(1).unbox(), 2);
    // Scalar area begins after the object slots (G0-1 packing law).
    let first = c.ctor_scalar_u64(2 * 8);
    assert_eq!(first & 0xFF, 0xAB);
    assert_eq!((first >> 8) & 0xFF, 0xCD);
}

#[test]
fn ctor_retag_and_scalar_write() {
    let _g = lock();
    let c = Obj::mk_ctor(1, vec![Obj::mk_nat(0)], &[0u8; 8]);
    assert_eq!(c.header().tag, 1);
    c.ctor_retag(9);
    assert_eq!(c.header().tag, 9, "lean_ctor_set_tag semantics");
    c.ctor_scalar_set_u64(8, 0x0123_4567_89AB_CDEF);
    assert_eq!(c.ctor_scalar_u64(8), 0x0123_4567_89AB_CDEF);
}

/// The sharing-maximizer zero law: alignment padding of ctor memory is
/// deterministically zeroed (`lean.h:441-451`).
#[test]
fn ctor_padded_word_is_zeroed() {
    let _g = lock();
    // 8 (header) + 8 (one slot) + 1 (scalar) = 17 -> aligned 24; the final
    // word (bytes 16..24 of the block, i.e. scalar offset 8) must read as the
    // written byte with all padding bytes zero.
    let c = Obj::mk_ctor(0, vec![Obj::mk_nat(3)], &[0x7F]);
    assert_eq!(c.ctor_scalar_u64(8), 0x7F);
}

#[test]
fn string_facts_utf8() {
    let _g = lock();
    let s = Obj::mk_string("héllo∀");
    let bytes = "héllo∀".as_bytes();
    let (size, cap, len, data) = s.string_view();
    assert_eq!(size, bytes.len() + 1, "m_size includes the NUL");
    assert_eq!(cap, bytes.len() + 1);
    assert_eq!(len, 6, "m_length is the codepoint count");
    assert_eq!(&data[..bytes.len()], bytes);
    assert_eq!(data[bytes.len()], 0);
    // Strings ride the big path: m_cs_sz = 0.
    assert_eq!(s.header().cs_sz, 0);

    let empty = Obj::mk_string("");
    let (size, _, len, data) = empty.string_view();
    assert_eq!(
        (size, len),
        (1, 0),
        "empty string stores its NUL (G0-1 item 8)"
    );
    assert_eq!(data, vec![0]);
}

#[test]
fn array_and_sarray_facts() {
    let _g = lock();
    let a = Obj::mk_array(vec![Obj::mk_nat(10), Obj::mk_string("x"), Obj::mk_nat(30)]);
    assert_eq!(a.array_view(), (3, 3));
    assert_eq!(a.header().cs_sz, 0, "arrays ride the big path");
    assert_eq!(a.array_child(0).unbox(), 10);
    assert_eq!(a.array_child(2).unbox(), 30);
    assert_eq!(a.byte_size(), size_of::<LeanArrayObject>() + 3 * 8);

    let sa = Obj::mk_sarray(4, &[1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0]);
    let h = sa.header();
    assert_eq!(h.other, 4, "element size lives in m_other");
    assert_eq!(h.cs_sz, 0);
    assert_eq!(sa.byte_size(), size_of::<LeanSarrayObject>() + 12);
}

#[test]
fn closure_ref_thunk_task_mpz_facts() {
    let _g = lock();
    let cl = Obj::mk_closure(3, vec![Obj::mk_nat(9)]);
    assert_eq!(cl.closure_view(), (3, 1));
    assert_eq!(cl.header().cs_sz, 0, "closures ride the big path");

    let r = Obj::mk_ref(Obj::mk_string("cell"));
    assert_eq!(
        usize::from(r.header().cs_sz),
        align_obj_size(size_of::<LeanRefObject>())
    );

    let t = Obj::mk_thunk_value(Obj::mk_nat(4));
    assert_eq!(t.obj_tag(), usize::from(contract::TAG_THUNK));

    let task = Obj::mk_task_pure(Obj::mk_nat(5));
    assert_eq!(task.obj_tag(), usize::from(contract::TAG_TASK));

    let m = Obj::mk_mpz(&[0xDEAD_BEEF, 0x1], true);
    let (alloc, size, limbs) = m.mpz_view();
    assert_eq!(alloc, 2);
    assert_eq!(size, -2, "sign of the value is the sign of m_size");
    assert_eq!(limbs, vec![0xDEAD_BEEF, 0x1]);
}

#[test]
fn external_finalizer_runs_exactly_once() {
    let _g = lock();
    let before = EXTERNAL_FINALIZED.load(Ordering::SeqCst);
    let e = Obj::mk_external_counting();
    assert_eq!(e.obj_tag(), usize::from(contract::TAG_EXTERNAL));
    drop(e);
    assert_eq!(EXTERNAL_FINALIZED.load(Ordering::SeqCst), before + 1);
}

// ================================================================ tri-state RC

#[test]
fn rc_clone_and_drop_balance() {
    let _g = lock();
    let s = Obj::mk_string("shared");
    assert_eq!(s.header().rc, 1);
    let a = s.clone_ref();
    let b = s.clone_ref();
    assert_eq!(s.header().rc, 3);
    drop(a);
    assert_eq!(s.header().rc, 2);
    drop(b);
    assert_eq!(s.header().rc, 1);
}

#[test]
fn persistent_objects_are_never_counted() {
    let _g = lock();
    let s = Obj::mk_string("immortal");
    s.make_persistent();
    assert_eq!(s.header().rc, 0);
    let c = s.clone_ref();
    assert_eq!(s.header().rc, 0, "inc on persistent is a no-op");
    drop(c);
    assert_eq!(s.header().rc, 0, "dec on persistent is a no-op");
    // The object is deliberately immortal from here on (upstream semantics);
    // Obj's final drop is also a no-op.
}

#[test]
fn mark_persistent_traverses_the_graph() {
    let _g = lock();
    let inner = Obj::mk_string("leaf");
    let keep = inner.clone_ref();
    let c = Obj::mk_ctor(1, vec![inner, Obj::mk_nat(2)], &[]);
    c.make_persistent();
    assert_eq!(c.header().rc, 0);
    assert_eq!(
        keep.header().rc,
        0,
        "children are zeroed too (object.cpp:553)"
    );
}

#[test]
fn mark_mt_negates_and_atomics_conserve() {
    let _g = lock();
    let s = Obj::mk_string("concurrent");
    let extra = s.clone_ref();
    assert_eq!(s.header().rc, 2);
    s.make_mt();
    assert_eq!(s.header().rc, -2, "mark_mt negates the ST count in place");
    s.stress_mt(8, 2000);
    assert_eq!(s.header().rc, -2, "balanced MT traffic conserves the count");
    drop(extra);
    assert_eq!(s.header().rc, -1, "MT dec via atomic fetch_add");
}

#[test]
fn mt_object_dies_on_last_dec() {
    let _g = lock();
    shadow::enable();
    {
        let s = Obj::mk_string("mt-death");
        s.make_mt();
        let c = s.clone_ref();
        drop(s);
        drop(c);
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "the MT object was released exactly once");
    let releases = events
        .iter()
        .filter(|e| e.kind == EventKind::Release)
        .count();
    assert_eq!(releases, 1);
    assert!(
        events
            .iter()
            .all(|e| e.kind != EventKind::DoubleRelease && e.kind != EventKind::ForeignPointer)
    );
}

/// RC balance property: a seeded random object soup — builds, shares, and
/// drops — must tear down completely with zero ownership faults.
#[test]
fn rc_balance_property_random_graphs() {
    let _g = lock();
    // xorshift64* — deterministic, dependency-free.
    let mut state = 0x9E37_79B9_7F4A_7C15u64;
    let mut next = move || {
        state ^= state >> 12;
        state ^= state << 25;
        state ^= state >> 27;
        state = state.wrapping_mul(0x2545_F491_4F6C_DD1D);
        state
    };
    shadow::enable();
    {
        let mut pool: Vec<Obj> = Vec::new();
        for step in 0..400u64 {
            match next() % 6 {
                0 => pool.push(Obj::mk_nat((next() % 1000) as usize)),
                1 => pool.push(Obj::mk_string("prop")),
                2 if !pool.is_empty() => {
                    let i = (next() as usize) % pool.len();
                    pool.push(pool[i].clone_ref());
                }
                3 if pool.len() >= 2 => {
                    let a = pool.remove((next() as usize) % pool.len());
                    let b = pool.remove((next() as usize) % pool.len());
                    let tag = (next() % 4) as u8;
                    pool.push(Obj::mk_ctor(tag, vec![a, b], &[(step & 0xFF) as u8]));
                }
                4 if pool.len() >= 3 => {
                    let a = pool.remove((next() as usize) % pool.len());
                    let b = pool.remove((next() as usize) % pool.len());
                    let c = pool.remove((next() as usize) % pool.len());
                    pool.push(Obj::mk_array(vec![a, b, c]));
                }
                _ if !pool.is_empty() => {
                    let i = (next() as usize) % pool.len();
                    drop(pool.remove(i));
                }
                _ => {}
            }
        }
        drop(pool);
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "every allocation released exactly once");
    assert!(
        events
            .iter()
            .all(|e| e.kind != EventKind::DoubleRelease && e.kind != EventKind::ForeignPointer),
        "no ownership faults in a balanced script"
    );
}

/// Teardown of a deep chain must not recurse: run on a deliberately small
/// stack (the dev-box `ulimit -s unlimited` masks overflow bugs otherwise).
#[test]
fn deep_chain_teardown_bounded_stack() {
    let _g = lock();
    std::thread::Builder::new()
        .name("bounded-teardown".into())
        .stack_size(256 * 1024)
        .spawn(|| {
            let mut o = Obj::mk_nat(0);
            for _ in 0..100_000 {
                o = Obj::mk_ctor(0, vec![o], &[]);
            }
            drop(o); // iterative worklist, or this overflows 256 KiB
        })
        .expect("spawn")
        .join()
        .expect("deep teardown must not overflow the bounded stack");
}

// ================================================================ shadows

#[test]
fn shadow_kills_double_release() {
    let _g = lock();
    shadow::enable();
    Obj::probe_double_release();
    let (events, _) = shadow::disable_and_drain();
    assert!(
        events.iter().any(|e| e.kind == EventKind::DoubleRelease),
        "seeded double release must be detected"
    );
}

#[test]
fn shadow_kills_foreign_pointer() {
    let _g = lock();
    shadow::enable();
    Obj::probe_foreign_pointer();
    let (events, _) = shadow::disable_and_drain();
    assert!(
        events.iter().any(|e| e.kind == EventKind::ForeignPointer),
        "seeded foreign-pointer misuse must be detected"
    );
}

#[test]
fn shadow_quarantine_poisons_headers() {
    let _g = lock();
    shadow::enable();
    let tag = Obj::probe_quarantine_poison();
    let (_, _) = shadow::disable_and_drain();
    assert_eq!(
        tag,
        contract::TAG_RESERVED,
        "quarantined objects read as poisoned"
    );
}

/// Replay determinism: the same operation script yields the same event
/// stream (kinds and provenance tags), independent of addresses.
#[test]
fn shadow_replay_is_deterministic() {
    let _g = lock();
    let script = || {
        shadow::enable();
        let a = Obj::mk_string("replay");
        let b = a.clone_ref();
        let c = Obj::mk_ctor(2, vec![Obj::mk_nat(1)], &[]);
        drop(b);
        drop(c);
        drop(a);
        shadow::disable_and_drain()
    };
    let (run1, live1) = script();
    let (run2, live2) = script();
    assert_eq!(live1, live2);
    assert_eq!(
        run1, run2,
        "event streams must be bit-identical across runs"
    );
}

// ================================================================ C4 probe

/// The Marrow half of the C4 native-ABI probe rig (corpus family C4,
/// plan §18): emits layout and behavior facts as NDJSON when
/// `FLN_C4_EMIT` names an output file. The e2e scenario
/// (`scripts/e2e/marrow_abi_probes.sh`) diffs this against the same facts
/// emitted by a C program compiled against the pinned toolchain's `lean.h`
/// and linked to the real Reference runtime.
#[test]
fn c4_probe_emit_facts() {
    let _g = lock();
    let facts = collect_c4_facts();
    // Internal coherence regardless of emission.
    assert!(!facts.is_empty());
    if let Ok(path) = std::env::var("FLN_C4_EMIT") {
        let mut out = String::new();
        for (k, v) in &facts {
            out.push_str(&format!(
                "{{\"schema\":\"fln-c4-abi-probe/1\",\"probe\":\"{k}\",\"value\":{v}}}\n"
            ));
        }
        std::fs::write(&path, out).expect("write C4 facts");
    }
}

fn collect_c4_facts() -> Vec<(String, i64)> {
    let mut f: Vec<(String, i64)> = Vec::new();
    let mut fact = |k: &str, v: usize| f.push((k.to_string(), i64::try_from(v).expect("fact")));

    // Layout facts: every contract struct, every field, plus sizeof.
    for spec in contract::OBJECT_STRUCTS {
        let (size, fields) = mirror_layout(spec.name);
        fact(&format!("sizeof.{}", spec.name), size);
        for (name, off) in fields {
            fact(&format!("offsetof.{}.{}", spec.name, name), off);
        }
    }

    // Tagged scalars.
    for n in [0usize, 1, 41, 1 << 20] {
        let b = Obj::mk_nat(n);
        fact(&format!("box.{n}.bits"), b.unbox() * 2 + 1);
        fact(&format!("box.{n}.tag"), b.obj_tag());
    }

    // Ctor: header facts + scalar packing + the padded-zero law.
    let c = Obj::mk_ctor(
        7,
        vec![Obj::mk_nat(1), Obj::mk_nat(2)],
        &[0xAB, 0xCD, 0, 0, 0, 0, 0, 0],
    );
    let h = c.header();
    fact("ctor.7_2_8.rc", usize::try_from(h.rc).expect("rc"));
    fact("ctor.7_2_8.cs_sz", usize::from(h.cs_sz));
    fact("ctor.7_2_8.other", usize::from(h.other));
    fact("ctor.7_2_8.tag", usize::from(h.tag));
    fact(
        "ctor.7_2_8.scalar_u64",
        usize::try_from(c.ctor_scalar_u64(16)).expect("scalar"),
    );

    // Padded word: 1 slot + 1 scalar byte -> aligned block, upper bytes zero.
    let p = Obj::mk_ctor(0, vec![Obj::mk_nat(3)], &[0x7F]);
    fact(
        "ctor.padzero.scalar_u64",
        usize::try_from(p.ctor_scalar_u64(8)).expect("pad"),
    );

    // String semantics.
    let s = Obj::mk_string("héllo∀");
    let (size, cap, len, data) = s.string_view();
    fact("string.hello.size", size);
    fact("string.hello.capacity", cap);
    fact("string.hello.length", len);
    fact("string.hello.cs_sz", usize::from(s.header().cs_sz));
    fact("string.hello.byte0", usize::from(data[0]));
    fact("string.hello.nul", usize::from(*data.last().expect("nul")));
    let e = Obj::mk_string("");
    let (size, _, len, _) = e.string_view();
    fact("string.empty.size", size);
    fact("string.empty.length", len);

    // Array / sarray.
    let a = Obj::mk_array(vec![Obj::mk_nat(1), Obj::mk_nat(2), Obj::mk_nat(3)]);
    fact("array.3.size", a.array_view().0);
    fact("array.3.capacity", a.array_view().1);
    fact("array.3.cs_sz", usize::from(a.header().cs_sz));
    let sa = Obj::mk_sarray(4, &[9, 0, 0, 0, 8, 0, 0, 0]);
    fact("sarray.4_2.elem_size", usize::from(sa.header().other));
    fact("sarray.4_2.cs_sz", usize::from(sa.header().cs_sz));

    // Closure.
    let cl = Obj::mk_closure(3, vec![Obj::mk_nat(1)]);
    fact("closure.3_1.arity", usize::from(cl.closure_view().0));
    fact("closure.3_1.num_fixed", usize::from(cl.closure_view().1));
    fact("closure.3_1.cs_sz", usize::from(cl.header().cs_sz));

    // Tri-state RC transitions.
    let r = Obj::mk_string("rc-probe");
    let r2 = r.clone_ref();
    let r3 = r.clone_ref();
    fact(
        "rc.st.after_2inc",
        usize::try_from(r.header().rc).expect("rc"),
    );
    drop(r3);
    fact(
        "rc.st.after_dec",
        usize::try_from(r.header().rc).expect("rc"),
    );
    drop(r2);
    let pers = Obj::mk_string("persist-probe");
    pers.make_persistent();
    fact(
        "rc.persistent.value",
        usize::try_from(pers.header().rc).expect("rc"),
    );
    let keep = pers.clone_ref();
    drop(keep);
    fact(
        "rc.persistent.after_incdec",
        usize::try_from(pers.header().rc).expect("rc"),
    );
    let mt = Obj::mk_string("mt-probe");
    mt.make_mt();
    fact(
        "rc.mt.after_mark",
        usize::try_from(-mt.header().rc).expect("rc"),
    );
    let mtc = mt.clone_ref();
    fact(
        "rc.mt.after_inc",
        usize::try_from(-mt.header().rc).expect("rc"),
    );
    drop(mtc);
    fact(
        "rc.mt.after_dec",
        usize::try_from(-mt.header().rc).expect("rc"),
    );

    f
}
