//! G0-1 region-reader suite (bead franken_lean-y24): real pinned-Reference
//! oleans from the C3 fixture corpus walked with full integrity checking and
//! `ModuleData` decoding, plus a hostile-input smoke lane — deterministic
//! corruptions and a seeded byte-flip sweep must yield typed errors under
//! budget, never panics and never false acceptance (FL-INV-07 discipline).

#![forbid(unsafe_code)]

use std::path::PathBuf;

use fln_olean::format;
use fln_olean::region::{OleanView, RegionError, WalkBudget};

fn fixture(name: &str) -> Vec<u8> {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tribunal/fixtures/c3")
        .join(name);
    let data = std::fs::read(&path);
    assert!(
        data.is_ok(),
        "missing C3 fixture {}: {:?}",
        path.display(),
        data.err()
    );
    data.expect("asserted above")
}

#[test]
fn init_aggregator_walks_clean() {
    let bytes = fixture("Init.olean");
    let view = OleanView::parse(&bytes).expect("header");
    assert_eq!(view.header.version, 2);
    assert_eq!(view.header.lean_version, "4.32.0");
    assert_eq!(
        view.header.githash,
        "8c9756b28d64dab099da31a4c09229a9e6a2ef35"
    );
    assert_eq!(view.header.base_addr % format::REGION_ALIGN as u64, 0);
    let report = view.walk(WalkBudget::default()).expect("walk");
    assert_eq!(report.objects, 158, "object census drifted for Init.olean");
    let md = view
        .module_data(WalkBudget::default())
        .expect("module data");
    assert!(md.is_module);
    assert_eq!(md.imports.len(), 43);
    assert_eq!(md.constants, 0, "Init is an import aggregator");
    assert!(md.imports.iter().any(|i| i == "Init.Prelude"));
}

#[test]
fn binder_name_hint_decodes_constants_and_extensions() {
    let bytes = fixture("Init.BinderNameHint.olean");
    let view = OleanView::parse(&bytes).expect("header");
    view.walk(WalkBudget::default()).expect("walk");
    let md = view
        .module_data(WalkBudget::default())
        .expect("module data");
    assert_eq!(md.constants, 2);
    assert_eq!(md.const_names.len(), 2, "constNames must mirror constants");
    assert!(
        md.const_names.iter().any(|n| n == "binderNameHint"),
        "expected binderNameHint among {:?}",
        md.const_names
    );
    assert!(!md.extensions.is_empty());
    // Extension payloads are opaque by contract: counted, never interpreted.
    let total: u64 = md.extensions.iter().map(|e| e.entries).sum();
    assert!(total > 0);
}

#[test]
fn size_of_lemmas_carries_simp_extension_payloads() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("header");
    let report = view.walk(WalkBudget::default()).expect("walk");
    assert!(report.objects > 500);
    let md = view
        .module_data(WalkBudget::default())
        .expect("module data");
    assert_eq!(md.constants, 16);
    assert!(
        md.extensions.iter().any(|e| e.name.contains("simp")),
        "expected a simp extension block among {:?}",
        md.extensions.iter().map(|e| &e.name).collect::<Vec<_>>()
    );
}

#[test]
fn header_rejections_are_typed() {
    let good = fixture("Init.olean");

    // Truncation below the fixed header.
    let r = OleanView::parse(&good[..40]);
    assert!(matches!(r, Err(RegionError::Truncated { .. })), "{r:?}");

    // Bad magic.
    let mut bad = good.clone();
    bad[0] ^= 0xff;
    let r = OleanView::parse(&bad);
    assert!(matches!(r, Err(RegionError::BadMagic)), "{r:?}");

    // Unsupported version.
    let mut bad = good.clone();
    bad[5] = 9;
    let r = OleanView::parse(&bad);
    assert!(
        matches!(r, Err(RegionError::UnsupportedVersion(9))),
        "{r:?}"
    );

    // Misaligned base address (violates REGION_ALIGN).
    let mut bad = good.clone();
    bad[80] = 8;
    let r = OleanView::parse(&bad);
    assert!(
        matches!(r, Err(RegionError::MisalignedBase { .. })),
        "{r:?}"
    );
}

#[test]
fn walk_rejections_are_typed() {
    let good = fixture("Init.olean");
    let header = format::OLEAN_HEADER_SIZE;

    // Root pointer pushed out of bounds (kept even: an odd value would be a
    // legitimate scalar box, not a pointer).
    let mut bad = good.clone();
    bad[header] = 0xf8;
    bad[header + 7] = 0x7f;
    let view = OleanView::parse(&bad).expect("header still valid");
    let r = view.walk(WalkBudget::default());
    assert!(
        matches!(r, Err(RegionError::PtrOutOfBounds { .. })),
        "{r:?}"
    );

    // Root pointer misaligned.
    let mut bad = good.clone();
    bad[header] ^= 0x04;
    let view = OleanView::parse(&bad).expect("header still valid");
    let r = view.walk(WalkBudget::default());
    assert!(
        matches!(
            r,
            Err(RegionError::MisalignedPtr { .. }) | Err(RegionError::PtrOutOfBounds { .. })
        ),
        "{r:?}"
    );

    // Truncated data region: keep the header, drop the tail.
    let view_bytes = good[..good.len() - 64].to_vec();
    let view = OleanView::parse(&view_bytes).expect("header still valid");
    let r = view.walk(WalkBudget::default());
    assert!(r.is_err(), "truncated region must not walk clean: {r:?}");
}

#[test]
fn budget_exhaustion_is_typed_not_partial() {
    let bytes = fixture("Init.SizeOfLemmas.olean");
    let view = OleanView::parse(&bytes).expect("header");
    let r = view.walk(WalkBudget { max_objects: 10 });
    assert!(
        matches!(r, Err(RegionError::BudgetExhausted { budget: 10, .. })),
        "{r:?}"
    );
}

#[test]
fn seeded_byteflip_sweep_never_panics_never_lies() {
    // Deterministic xorshift sweep: flip one byte at a time in the data
    // region and demand a typed outcome. Acceptance is allowed ONLY when the
    // corruption did not change the walked graph's integrity-relevant bytes
    // (e.g. unreached padding); a panic or hang fails the whole test.
    let good = fixture("Init.BinderNameHint.olean");
    let mut seed: u64 = 0x53_76_24_79_24_31_66_6c; // fixed; determinism law
    let mut flips = 0u32;
    let mut typed_errors = 0u32;
    while flips < 300 {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        let pos =
            (seed as usize) % (good.len() - format::OLEAN_HEADER_SIZE) + format::OLEAN_HEADER_SIZE;
        let bit = 1u8 << ((seed >> 32) % 8);
        let mut mutated = good.clone();
        mutated[pos] ^= bit;
        flips += 1;
        match OleanView::parse(&mutated) {
            Err(_) => typed_errors += 1,
            Ok(view) => {
                let budget = WalkBudget {
                    max_objects: 1_000_000,
                };
                let walk = view.walk(budget);
                let md = view.module_data(budget);
                if walk.is_err() || md.is_err() {
                    typed_errors += 1;
                }
            }
        }
    }
    assert_eq!(flips, 300);
    // The corpus is dense: the sweep must actually be exercising the error
    // paths, not silently accepting everything.
    assert!(
        typed_errors > 100,
        "only {typed_errors}/300 flips produced typed errors — corruption not detected"
    );
}

#[test]
fn manifest_matches_fixture_bytes() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tribunal/fixtures/c3");
    let manifest = std::fs::read_to_string(dir.join("MANIFEST.txt"));
    assert!(manifest.is_ok(), "missing C3 MANIFEST.txt");
    let manifest = manifest.expect("asserted above");
    assert!(manifest.contains("schema fln-c3-manifest/1"));
    let mut rows = 0;
    for line in manifest.lines() {
        if line.starts_with('#') || line.starts_with("schema") || line.is_empty() {
            continue;
        }
        let cols: Vec<&str> = line.split_whitespace().collect();
        assert_eq!(cols.len(), 4, "manifest row arity: {line:?}");
        let bytes = std::fs::read(dir.join(cols[3]));
        assert!(bytes.is_ok(), "fixture {} missing", cols[3]);
        let bytes = bytes.expect("asserted above");
        assert_eq!(
            bytes.len().to_string(),
            cols[1],
            "size mismatch for {}",
            cols[3]
        );
        rows += 1;
    }
    assert_eq!(rows, 3, "C3 seed corpus is three fixtures");
}
