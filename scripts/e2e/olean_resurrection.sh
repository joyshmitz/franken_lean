#!/usr/bin/env bash
# olean_resurrection.sh — shared E2E scenario for the G0-1 ABI-resurrection
# spike (bead franken_lean-y24, plan §22.1-1).
#
# Real-path, no-mock: REAL .olean artifacts produced by the pinned Reference
# are walked by the prototype region reader with full object-graph integrity
# checking — the checked-in C3 fixtures always, and when the pinned toolchain
# is installed, the ENTIRE stdlib library (2400+ modules). Then a REAL
# corruption class is seeded — a flipped byte inside a copied olean's data
# region — and the reader must fail typed, never panic and never accept;
# recovery re-walks the pristine copy green. NDJSON under target/e2e/;
# artifacts retained.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RUN_ID="olean-resurrection-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="$ROOT/target/e2e/$RUN_ID"
LOG="$ART_DIR/run.ndjson"
mkdir -p "$ART_DIR"

BEAD="franken_lean-y24"
SCHEMA="fln-e2e/1"
HOST="$(uname -sr)"
start_ns=$(date +%s%N)

emit() { # emit <step_id> <status> <detail-json-fragment>
  local now_ns
  now_ns=$(date +%s%N)
  printf '{"schema":"%s","run_id":"%s","bead":"%s","scenario":"olean_resurrection","step":"%s","status":"%s","elapsed_ms":%d,"host":"%s",%s}\n' \
    "$SCHEMA" "$RUN_ID" "$BEAD" "$1" "$2" $(( (now_ns - start_ns) / 1000000 )) "$HOST" "$3" >> "$LOG"
}

note() { echo "[olean_resurrection] $*" >&2; }

emit run_start started "\"cwd\":\"$ROOT\",\"argv\":\"$0\""

# ---- lane 1: fixture provenance — C3 corpus matches its manifest -----------------------
note "verifying C3 fixture corpus against MANIFEST.txt"
C3="$ROOT/tribunal/fixtures/c3"
fail=0
while read -r sha bytes _src file; do
  case "$sha" in \#*|schema|"") continue ;; esac
  actual_sha="$(sha256sum "$C3/$file" | cut -d' ' -f1)"
  actual_bytes="$(stat -c%s "$C3/$file")"
  if [ "$actual_sha" != "$sha" ] || [ "$actual_bytes" != "$bytes" ]; then
    note "FIXTURE DRIFT: $file (sha $actual_sha vs $sha, bytes $actual_bytes vs $bytes)"
    fail=1
  fi
done < "$C3/MANIFEST.txt"
if [ "$fail" -ne 0 ]; then
  emit fixtures failed "\"reason\":\"manifest_mismatch\""
  exit 1
fi
emit fixtures passed "\"count\":3,\"manifest\":\"tribunal/fixtures/c3/MANIFEST.txt\""

# ---- lane 2: the reader suite ----------------------------------------------------------
note "running the fln-olean suite (region reader + format contract)"
set +e
( cd "$ROOT" && CARGO_TARGET_DIR=target_local cargo test -q -p fln-olean ) \
  > "$ART_DIR/suite.log" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit suite failed "\"expected_exit\":0,\"actual_exit\":$rc,\"artifact\":\"suite.log\""
  note "FAIL: fln-olean suite failed (see $ART_DIR/suite.log)"
  exit 1
fi
emit suite passed "\"expected_exit\":0,\"actual_exit\":0,\"artifact\":\"suite.log\""

# ---- build the walker driver -----------------------------------------------------------
note "building walk_olean driver"
( cd "$ROOT" && CARGO_TARGET_DIR=target_local cargo build -q --locked -p fln-olean --example walk_olean ) \
  > "$ART_DIR/build.log" 2>&1
WALKER="$ROOT/target_local/debug/examples/walk_olean"

# ---- lane 3: resurrect the C3 fixtures -------------------------------------------------
set +e
"$WALKER" "$C3"/*.olean > "$ART_DIR/fixture_walk.tsv" 2>>"$ART_DIR/fixture_walk.err"
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit fixture_walk failed "\"actual_exit\":$rc,\"artifact\":\"fixture_walk.tsv\""
  note "FAIL: fixture walk reported faults"
  exit 1
fi
emit fixture_walk passed "\"files\":3,\"artifact\":\"fixture_walk.tsv\""

# ---- lane 4: resurrect the ENTIRE pinned toolchain library -----------------------------
PIN_TAG="$(sed -E 's/.*tag=([^ ]+).*/\1/' <<<"$(grep -E '^reference ' "$ROOT/SUITE.lock")")"
LIB="$HOME/.elan/toolchains/leanprover--lean4---$PIN_TAG/lib/lean"
if [ -d "$LIB" ]; then
  note "resurrecting the full pinned stdlib library from $LIB"
  set +e
  find "$LIB" -name '*.olean' | sort | xargs "$WALKER" > "$ART_DIR/library_walk.tsv" 2>>"$ART_DIR/library_walk.err"
  rc=$?
  set -e
  total="$(wc -l < "$ART_DIR/library_walk.tsv")"
  ok="$(grep -c $'\tok$' "$ART_DIR/library_walk.tsv" || true)"
  objects="$(awk -F'\t' '$8=="ok"{s+=$3} END{print s}' "$ART_DIR/library_walk.tsv")"
  consts="$(awk -F'\t' '$8=="ok"{s+=$5} END{print s}' "$ART_DIR/library_walk.tsv")"
  if [ "$rc" -ne 0 ] || [ "$total" -ne "$ok" ] || [ "$total" -lt 2000 ]; then
    emit library_walk failed "\"files\":$total,\"ok\":$ok,\"actual_exit\":$rc,\"artifact\":\"library_walk.tsv\""
    note "FAIL: library resurrection incomplete ($ok/$total clean)"
    exit 1
  fi
  emit library_walk passed "\"files\":$total,\"ok\":$ok,\"objects\":$objects,\"constants\":$consts,\"artifact\":\"library_walk.tsv\""
  note "library resurrection: $total files, $objects objects, $consts constants, zero faults"
else
  # Typed, honest skip: no pinned toolchain on this host.
  emit library_walk skipped "\"reason\":\"reference_toolchain_absent\",\"limitation\":\"L0: full-library lane unverified on this host\""
  note "SKIP: pinned toolchain library not installed (typed limitation)"
fi

# ---- lane 5: seeded corruption — flipped byte must be killed, never accepted -----------
note "seeding corruption: single byte flipped in a copied region"
CORRUPT="$ART_DIR/corrupt.olean"
cp "$C3/Init.SizeOfLemmas.olean" "$CORRUPT"
python3 - "$CORRUPT" <<'EOF'
import sys
path = sys.argv[1]
data = bytearray(open(path, "rb").read())
# Flip a bit in the middle of the data region (past the 88-byte header),
# 8-byte-slot-aligned so it lands in object payload, kept deterministic.
pos = 88 + ((len(data) - 88) // 2 // 8) * 8
data[pos] ^= 0x10
open(path, "wb").write(data)
EOF
set +e
"$WALKER" "$CORRUPT" > "$ART_DIR/corrupt_walk.tsv" 2>>"$ART_DIR/corrupt_walk.err"
rc=$?
set -e
if [ "$rc" -eq 0 ]; then
  emit corruption failed "\"actual_exit\":0,\"expected\":\"nonzero\",\"artifact\":\"corrupt_walk.tsv\""
  note "FAIL: corrupted olean walked clean — integrity checking is not real"
  exit 1
fi
if grep -q "panicked" "$ART_DIR/corrupt_walk.err"; then
  emit corruption failed "\"reason\":\"panic\",\"artifact\":\"corrupt_walk.err\""
  note "FAIL: reader panicked on corrupted input (FL-INV-07 violation)"
  exit 1
fi
emit corruption passed "\"actual_exit\":$rc,\"typed_error\":true,\"artifact\":\"corrupt_walk.tsv\""
note "corruption killed: typed error, no panic"

# ---- lane 6: recovery — pristine fixture still walks clean -----------------------------
set +e
"$WALKER" "$C3/Init.SizeOfLemmas.olean" > "$ART_DIR/recovery_walk.tsv" 2>&1
rc=$?
set -e
if [ "$rc" -ne 0 ]; then
  emit recovery failed "\"actual_exit\":$rc,\"artifact\":\"recovery_walk.tsv\""
  note "FAIL: recovery walk not green"
  exit 1
fi
emit recovery passed "\"actual_exit\":0,\"artifact\":\"recovery_walk.tsv\""

emit run_end passed "\"cleanup_status\":\"retained_by_policy\",\"artifact_dir\":\"target/e2e/$RUN_ID\""
note "PASS: all lanes green (artifacts in target/e2e/$RUN_ID)"
