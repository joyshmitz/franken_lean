#!/usr/bin/env bash
# env_snapshots.sh — shared E2E scenario for the Grimoire environment (bead fln-amv).
#
# Real-path, no-mock: runs the real fln-env suite (persistent-map model tests,
# snapshot isolation, logical-root determinism across thread counts), then seeds a
# REAL bug class into an overlay workspace — add_decl silently dropping extension
# state — and proves the suite KILLS the mutant (a surviving mutant is a failed
# scenario), then recovery on the pristine overlay. NDJSON under target/e2e/.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="env-snapshots-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"

BEAD="fln-amv"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"env_snapshots","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[env_snapshots] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- step 1: the real suite ------------------------------------------------------------
note "running the fln-env suite (pmap model, isolation, root determinism)"
set +e
( cd "$ROOT" && CARGO_TARGET_DIR=target_local cargo test -q -p fln-env ) \
  > "$ART_DIR/suite.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit suite failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"suite.log\""
  note "FAIL: fln-env suite failed (see $ART_DIR/suite.log)"
  exit 1
fi
emit suite passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"suite.log\""

# ---- step 2: seeded mutant must be killed ----------------------------------------------
OVERLAY="$ART_DIR/overlay"
mkdir -p "$OVERLAY"
for crate in fln-core fln-hash fln-env; do
  cp -r "$ROOT/crates/$crate" "$OVERLAY/$crate"
done
cat > "$OVERLAY/Cargo.toml" <<'EOF'
[workspace]
resolver = "3"
members = ["fln-core", "fln-hash", "fln-env"]
EOF
cp "$ROOT/rust-toolchain.toml" "$OVERLAY/rust-toolchain.toml"
# The mutant: add_decl silently discards extension state (a real bug class the
# snapshot/root tests exist to kill).
sed -i 's/extensions: self.extensions.clone(),/extensions: crate::pmap::PMap::new(),/' \
  "$OVERLAY/fln-env/src/environment.rs"
if ! grep -q "PMap::new()," "$OVERLAY/fln-env/src/environment.rs"; then
  emit seeded_mutant failed "\"detail\":\"mutation seed was a no-op\""
  note "FAIL: mutation seed did not apply"
  exit 1
fi
set +e
( cd "$OVERLAY" && CARGO_TARGET_DIR="$OVERLAY/target" cargo test -q -p fln-env ) \
  > "$ART_DIR/mutant.log" 2>&1
rc=$?
set -e
if [ "$rc" -eq 0 ]; then
  emit seeded_mutant failed "\"expected_exit\":\"nonzero\",\"actual_exit\":0,\"artifact\":\"mutant.log\""
  note "FAIL: the extension-dropping mutant SURVIVED the suite"
  exit 1
fi
emit seeded_mutant passed "\"expected_exit\":\"nonzero\",\"actual_exit\":$rc,\"detected\":\"extension-state-dropping mutant killed\",\"artifact\":\"mutant.log\""

# ---- step 3: recovery — pristine overlay passes ----------------------------------------
sed -i 's/extensions: crate::pmap::PMap::new(),/extensions: self.extensions.clone(),/' \
  "$OVERLAY/fln-env/src/environment.rs"
set +e
( cd "$OVERLAY" && CARGO_TARGET_DIR="$OVERLAY/target" cargo test -q -p fln-env ) \
  > "$ART_DIR/recovered.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"recovered.log\""
  note "FAIL: pristine overlay no longer passes"
  exit 1
fi
emit recovery passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"recovered.log\""

emit run_end passed "\"verdict\":\"pass\",\"artifacts_dir\":\"target/e2e/$RUN_ID\",\"cleanup_status\":\"retained_by_policy\""
note "PASS — artifacts in $ART_DIR"
