//! **fln-unsafe-region** — mmap and arena primitives beyond asupersync's region heaps (plan D3, §21).
//!
//! Stub crate: charter only. Implementation arrives with its workstream beads;
//! the crate map and layering are governed by `WORKSPACE_GRAPH.txt` (bead fln-8mj).
//!
//! D3 boundary crate: `unsafe` is permitted here ONLY at narrowly scoped
//! `#[allow(unsafe_code)]` sites, each carrying a `// UNSAFE-LEDGER: FLN-UL-NNNN`
//! marker and a matching row in `UNSAFE_LEDGER.txt` (path, invariant, evidence,
//! safe fallback, no-claim boundary). CI rejects unledgered sites. This crate
//! must never depend on `fln-kernel` or `fln-checker` (D3 law a).

#![deny(unsafe_code)]
