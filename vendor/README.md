# vendor/

Home of `lean4-src` — the vendored upstream Lean sources at the epoch tag named in
`SUITE.lock`, held **byte-identical**, with upstream Apache-2.0 `LICENSE` and `LICENSES`
files preserved and project attribution in [`NOTICE`](NOTICE) (plan D5).

Per the Oracle-Only Law (D8), vendored upstream sources serve **exactly three roles**:

1. **Conformance corpus** for the Tribunal's differential rigs,
2. **Census/contract extraction input** (`ABI_CONTRACT.md`, `OLEAN_CONTRACT.md`, the
   extern + builtin censuses — generated, never transcribed),
3. **Source input**: the `Init`/`Std` `.lean` files our native toolchain *elaborates as
   data*, exactly as it elaborates mathlib (§4.3).

They are **never executed as toolchain implementation, never linked, never built**. No
crate in this workspace may reference `vendor/` at build time; release CI proves shipped
binaries cannot locate, spawn, or link the Reference.

The current snapshot is Lean `v4.32.0` at commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`. Its computed Git subtree is
`ba16913719a2f6a15a826918fbe6ba9dd5413e91`, the exact tree named by that commit. The
pin remains governed by `SUITE.lock`; future epoch changes replace it only through the
same reviewed pin ceremony and re-run the tree-identity proof.
