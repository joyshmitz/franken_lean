# vendor/

Home of `lean4-src@<pin>` — the vendored upstream Lean sources at the epoch tag named in
`SUITE.lock`, held **byte-identical**, Apache-2.0 NOTICE files carried (plan D5).

Per the Oracle-Only Law (D8), vendored upstream sources serve **exactly three roles**:

1. **Conformance corpus** for the Tribunal's differential rigs,
2. **Census/contract extraction input** (`ABI_CONTRACT.md`, `OLEAN_CONTRACT.md`, the
   extern + builtin censuses — generated, never transcribed),
3. **Source input**: the `Init`/`Std` `.lean` files our native toolchain *elaborates as
   data*, exactly as it elaborates mathlib (§4.3).

They are **never executed as toolchain implementation, never linked, never built**. No
crate in this workspace may reference `vendor/` at build time; release CI proves shipped
binaries cannot locate, spawn, or link the Reference.

The actual pinned checkout lands with the SUITE.lock / contract-extraction beads
(`franken_lean-xwf`, `franken_lean-53v`); this file records the law it will land under.
