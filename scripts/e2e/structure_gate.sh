#!/usr/bin/env bash
# structure_gate.sh — shared E2E scenario for the structural CI gate (bead fln-8mj).
#
# Real-path, no-mock: builds the real structure-guard binary, runs it against the real
# workspace (expected PASS), then against a full temp-dir copy carrying a seeded illegal
# upward edge (expected FAIL with FLN-STRUCT-005/007), then repairs the copy and re-runs
# (recovery, expected PASS). Emits human logs on stderr and schema-versioned NDJSON on
# a per-run artifact file under target/e2e/.
#
# Exit 0 iff all three scenario steps behave as expected.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="structure-gate-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"
BUILD_TARGET="$ART_DIR/cargo-target"

BEAD="fln-8mj"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"structure_gate","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[structure_gate] $*" >&2; }

copy_fixture() { # copy_fixture <fresh-destination>
  local destination="$1"
  mkdir -p "$destination"
  cp -r "$ROOT/ci" "$destination/ci"
  cp -r "$ROOT/crates" "$destination/crates"
  cp -r "$ROOT/tools" "$destination/tools"
  cp "$ROOT/Cargo.toml" "$ROOT/Cargo.lock" "$ROOT/SUITE.lock" \
    "$ROOT/rust-toolchain.toml" "$destination/"
}

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- step 1: build the real binary ----------------------------------------------------
note "building structure-guard (real binary, no mocks)"
( cd "$ROOT" && CARGO_TARGET_DIR="$BUILD_TARGET" cargo build -p structure-guard --quiet )
GUARD="$BUILD_TARGET/debug/structure-guard"
[ -x "$GUARD" ] || { emit build failed "\"detail\":\"binary missing at $GUARD\""; exit 1; }
emit build passed "\"artifact\":\"target/e2e/$RUN_ID/cargo-target/debug/structure-guard\""

# ---- step 2: the real workspace must be clean ------------------------------------------
note "checking the real workspace"
set +e
"$GUARD" --root "$ROOT" --robot > "$ART_DIR/real.ndjson"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit real_workspace failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"real.ndjson\""
  note "FAIL: real workspace has structural findings (see $ART_DIR/real.ndjson)"
  exit 1
fi
grep -q '"verdict":"pass"' "$ART_DIR/real.ndjson"
emit real_workspace passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"real.ndjson\""

# ---- step 3: seeded illegal edge must fail ---------------------------------------------
# Copy the checkable surface (governance files + crate manifests + roots) into a scratch
# root, then seed an UPWARD dependency fln-core -> fln-kernel without acknowledgment:
# both the snapshot law (005) and — once acknowledged — layering (007) must catch it.
SCRATCH_ROOT="$ART_DIR/fixtures"
UNACKNOWLEDGED="$SCRATCH_ROOT/unacknowledged"
note "seeding illegal edge in retained scratch copy: $UNACKNOWLEDGED"
copy_fixture "$UNACKNOWLEDGED"

printf 'fln-kernel = { path = "../fln-kernel" }\n' >> "$UNACKNOWLEDGED/crates/fln-core/Cargo.toml"

set +e
"$GUARD" --root "$UNACKNOWLEDGED" --robot > "$ART_DIR/seeded-unacknowledged.ndjson"
rc=$?
set -e
if [ "$rc" -ne 1 ] || ! grep -q 'FLN-STRUCT-005' "$ART_DIR/seeded-unacknowledged.ndjson"; then
  emit seeded_unacknowledged failed "\"expected_exit\":1,\"actual_exit\":$rc,\"expected_code\":\"FLN-STRUCT-005\",\"artifact\":\"seeded-unacknowledged.ndjson\""
  note "FAIL: unacknowledged seeded edge was not detected"
  exit 1
fi
emit seeded_unacknowledged passed "\"expected_exit\":1,\"actual_exit\":$rc,\"detected\":\"FLN-STRUCT-005\",\"artifact\":\"seeded-unacknowledged.ndjson\""

# Build a second immutable fixture with the edge acknowledged — layering must still
# refuse it. The failed fixture above is retained byte-for-byte for diagnosis.
ACKNOWLEDGED="$SCRATCH_ROOT/acknowledged"
copy_fixture "$ACKNOWLEDGED"
printf 'fln-kernel = { path = "../fln-kernel" }\n' >> "$ACKNOWLEDGED/crates/fln-core/Cargo.toml"
printf 'edge fln-core -> fln-kernel\n' >> "$ACKNOWLEDGED/ci/WORKSPACE_GRAPH.txt"
set +e
"$GUARD" --root "$ACKNOWLEDGED" --robot > "$ART_DIR/seeded-acknowledged.ndjson"
rc=$?
set -e
if [ "$rc" -ne 1 ] || ! grep -q 'FLN-STRUCT-007' "$ART_DIR/seeded-acknowledged.ndjson"; then
  emit seeded_acknowledged failed "\"expected_exit\":1,\"actual_exit\":$rc,\"expected_code\":\"FLN-STRUCT-007\",\"artifact\":\"seeded-acknowledged.ndjson\""
  note "FAIL: acknowledged upward edge was not refused by layering"
  exit 1
fi
emit seeded_acknowledged passed "\"expected_exit\":1,\"actual_exit\":$rc,\"detected\":\"FLN-STRUCT-007\",\"artifact\":\"seeded-acknowledged.ndjson\""

# ---- step 4: recovery — reconstruct clean state without mutating failed evidence -------
RECOVERED="$SCRATCH_ROOT/recovered"
note "recovery: reconstructing an independent clean fixture at $RECOVERED"
copy_fixture "$RECOVERED"

set +e
"$GUARD" --root "$RECOVERED" --robot > "$ART_DIR/recovered.ndjson"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"recovered.ndjson\""
  note "FAIL: repaired copy still has findings"
  exit 1
fi
emit recovery passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"recovered.ndjson\""

# ---- step 5: unledgered allow(unsafe_code) site must fail (D3 ledger law) --------------
UNLEDGERED="$SCRATCH_ROOT/unledgered"
note "seeding unledgered allow(unsafe_code) site in retained scratch copy: $UNLEDGERED"
copy_fixture "$UNLEDGERED"
printf '\n#[allow(unsafe_code)]\nfn seeded_unledgered_site() {}\n' >> "$UNLEDGERED/crates/fln-unsafe-abi/src/lib.rs"

set +e
"$GUARD" --root "$UNLEDGERED" --robot > "$ART_DIR/seeded-unledgered.ndjson"
rc=$?
set -e
if [ "$rc" -ne 1 ] || ! grep -q 'FLN-STRUCT-013' "$ART_DIR/seeded-unledgered.ndjson"; then
  emit seeded_unledgered failed "\"expected_exit\":1,\"actual_exit\":$rc,\"expected_code\":\"FLN-STRUCT-013\",\"artifact\":\"seeded-unledgered.ndjson\""
  note "FAIL: unledgered allow(unsafe_code) site was not detected"
  exit 1
fi
emit seeded_unledgered passed "\"expected_exit\":1,\"actual_exit\":$rc,\"detected\":\"FLN-STRUCT-013\",\"artifact\":\"seeded-unledgered.ndjson\""

# ---- step 6: recovery — the same site with marker + matching ledger row passes ----------
LEDGERED="$SCRATCH_ROOT/ledgered"
note "recovery: same site with ledger marker + row at $LEDGERED"
copy_fixture "$LEDGERED"
printf '\n// UNSAFE-LEDGER: FLN-UL-9001\n#[allow(unsafe_code)]\nfn seeded_ledgered_site() {}\n' >> "$LEDGERED/crates/fln-unsafe-abi/src/lib.rs"
printf 'row FLN-UL-9001 | crates/fln-unsafe-abi/src/lib.rs | e2e fixture invariant | this scenario | safe fallback path | result never enters a checked declaration\n' >> "$LEDGERED/ci/UNSAFE_LEDGER.txt"

set +e
"$GUARD" --root "$LEDGERED" --robot > "$ART_DIR/ledgered.ndjson"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit ledger_recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"ledgered.ndjson\""
  note "FAIL: ledgered allow site still refused"
  exit 1
fi
emit ledger_recovery passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"ledgered.ndjson\""

# ---- step 7: unsafe-boundary public export must fail closed (D3 law b) -----------------
EXPORTED="$SCRATCH_ROOT/exported"
note "seeding an unsafe-boundary public export in retained scratch copy: $EXPORTED"
copy_fixture "$EXPORTED"
printf '\npub fn seeded_public_export<T>() -> T { panic!("not executed") }\n' >> "$EXPORTED/crates/fln-unsafe-abi/src/lib.rs"

set +e
"$GUARD" --root "$EXPORTED" --robot > "$ART_DIR/seeded-export.ndjson"
rc=$?
set -e
if [ "$rc" -ne 1 ] || ! grep -q 'FLN-STRUCT-022' "$ART_DIR/seeded-export.ndjson"; then
  emit seeded_export failed "\"expected_exit\":1,\"actual_exit\":$rc,\"expected_code\":\"FLN-STRUCT-022\",\"artifact\":\"seeded-export.ndjson\""
  note "FAIL: unsafe-boundary public export was not refused"
  exit 1
fi
emit seeded_export passed "\"expected_exit\":1,\"actual_exit\":$rc,\"detected\":\"FLN-STRUCT-022\",\"artifact\":\"seeded-export.ndjson\""

# ---- step 8: recovery — crate-restricted visibility does not cross the boundary --------
RESTRICTED="$SCRATCH_ROOT/restricted"
note "recovery: reconstructing a crate-restricted boundary API at $RESTRICTED"
copy_fixture "$RESTRICTED"
printf '\npub(crate) fn seeded_crate_local_api() {}\n' >> "$RESTRICTED/crates/fln-unsafe-abi/src/lib.rs"

set +e
"$GUARD" --root "$RESTRICTED" --robot > "$ART_DIR/restricted.ndjson"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit export_recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"restricted.ndjson\""
  note "FAIL: crate-restricted recovery fixture still has findings"
  exit 1
fi
emit export_recovery passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"restricted.ndjson\""

emit run_end passed "\"verdict\":\"pass\",\"artifacts_dir\":\"target/e2e/$RUN_ID\",\"fixture_root\":\"$SCRATCH_ROOT\",\"cleanup_status\":\"retained_by_policy\""
note "PASS — artifacts in $ART_DIR; retained fixtures in $SCRATCH_ROOT"
