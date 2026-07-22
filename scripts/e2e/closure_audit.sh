#!/usr/bin/env bash
# closure_audit.sh — shared E2E scenario for the dependency-closure audit
# (bead franken_lean-xwf: G0-10, Rule D1).
#
# Real-path, no-mock: builds the real structure-guard binary, audits the real workspace
# closure (Cargo.lock ⇄ CLOSURE_ALLOWLIST ⇄ SUITE.lock ⇄ rust-toolchain.toml, expected
# PASS), then a scratch copy with a seeded unlisted registry package (expected FAIL with
# FLN-STRUCT-018), then an independent clean fixture (recovery, expected PASS).
# Human logs on stderr; schema-versioned NDJSON under target/e2e/. Fixtures retained.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="closure-audit-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"
BUILD_TARGET="$ART_DIR/cargo-target"

BEAD="franken_lean-xwf"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"closure_audit","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[closure_audit] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- step 1: build the real binary ----------------------------------------------------
note "building structure-guard (real binary, no mocks)"
( cd "$ROOT" && CARGO_TARGET_DIR="$BUILD_TARGET" cargo build -p structure-guard --quiet )
GUARD="$BUILD_TARGET/debug/structure-guard"
[ -x "$GUARD" ] || { emit build failed "\"detail\":\"binary missing at $GUARD\""; exit 1; }
emit build passed "\"artifact\":\"target/e2e/$RUN_ID/cargo-target/debug/structure-guard\""

copy_workspace() { # copy_workspace <dest>
  mkdir -p "$1"
  cp -r "$ROOT/ci" "$1/ci"
  cp -r "$ROOT/crates" "$1/crates"
  cp -r "$ROOT/tools" "$1/tools"
  cp "$ROOT/Cargo.toml" "$ROOT/Cargo.lock" "$ROOT/SUITE.lock" \
    "$ROOT/rust-toolchain.toml" "$1/"
}

# ---- step 2: the real closure must be clean --------------------------------------------
note "auditing the real workspace closure"
set +e
"$GUARD" --root "$ROOT" --robot > "$ART_DIR/real.ndjson"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit real_closure failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"real.ndjson\""
  note "FAIL: real workspace closure has findings (see $ART_DIR/real.ndjson)"
  exit 1
fi
grep -q '"verdict":"pass"' "$ART_DIR/real.ndjson"
emit real_closure passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"real.ndjson\""

# ---- step 3: seeded unlisted registry package must fail --------------------------------
SCRATCH_ROOT="$ART_DIR/fixtures"
SEEDED="$SCRATCH_ROOT/seeded"
note "seeding an unlisted registry package in retained scratch copy: $SEEDED"
copy_workspace "$SEEDED"
printf '\n[[package]]\nname = "serde"\nversion = "1.0.219"\nsource = "registry+https://github.com/rust-lang/crates.io-index"\nchecksum = "5f0e2c6ed6606019b4e29e69dbaba95b11854410e5347d525002456dbbb786b6"\n' >> "$SEEDED/Cargo.lock"

set +e
"$GUARD" --root "$SEEDED" --robot > "$ART_DIR/seeded.ndjson"
rc=$?
set -e
if [ "$rc" -ne 1 ] || ! grep -q 'FLN-STRUCT-018' "$ART_DIR/seeded.ndjson"; then
  emit seeded_registry_package failed "\"expected_exit\":1,\"actual_exit\":$rc,\"expected_code\":\"FLN-STRUCT-018\",\"artifact\":\"seeded.ndjson\""
  note "FAIL: seeded registry package was not detected"
  exit 1
fi
emit seeded_registry_package passed "\"expected_exit\":1,\"actual_exit\":$rc,\"detected\":\"FLN-STRUCT-018\",\"artifact\":\"seeded.ndjson\""

# ---- step 4: recovery — an independent clean fixture goes green ------------------------
RECOVERED="$SCRATCH_ROOT/recovered"
note "recovery: reconstructing an independent clean fixture at $RECOVERED"
copy_workspace "$RECOVERED"
set +e
"$GUARD" --root "$RECOVERED" --robot > "$ART_DIR/recovered.ndjson"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"recovered.ndjson\""
  note "FAIL: clean reconstruction still has findings"
  exit 1
fi
emit recovery passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"recovered.ndjson\""

emit run_end passed "\"verdict\":\"pass\",\"artifacts_dir\":\"target/e2e/$RUN_ID\",\"fixture_root\":\"$SCRATCH_ROOT\",\"cleanup_status\":\"retained_by_policy\""
note "PASS — artifacts in $ART_DIR; retained fixtures in $SCRATCH_ROOT"
