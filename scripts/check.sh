#!/usr/bin/env bash
# scripts/check.sh — THE quality gate (bead franken_lean-rur; AGENTS.md "Mandatory
# Checks After Substantive Changes").
#
# Runs, in order, stopping on the first failure:
#   1. fmt              cargo fmt --check
#   2. check            cargo check --all-targets
#   3. clippy           cargo clippy --all-targets -- -D warnings
#   4. test             cargo test
#   5. structure-guard  cargo run -q -p structure-guard -- --root <repo> --robot
#   6. vendor-tree      exact staged Reference tree equals the SUITE.lock pin
#   7. ubs              ubs <changed files>          (skipped+logged if ubs absent
#                                                     or no changed rust/toml files)
#
# This script IS the CI test step — workflows call it and never duplicate the
# commands inline (AGENTS.md). Gates add obligations and never retire them: new
# permanent stages append here.
#
# Logging: human summary on stderr; schema-versioned NDJSON (fln.check/1) written to
# $FLN_CHECK_LOG (default target/check/<run-id>/run.ndjson) with per-stage argv,
# exit status, duration, and stdout/stderr artifact captures beside it (256 KiB cap
# each — bounded log volume). Stderr is never swallowed: on failure the captured
# tail is replayed to the console.
#
# Self-test (planted failures, bead acceptance): `scripts/check.sh --self-test`
# re-invokes this script once per stage with FLN_CHECK_PLANT=<stage>, which replaces
# that stage's command with a guaranteed failure; each run must exit 1 and name the
# planted stage in both streams. Exit 0 iff every planted failure was detected
# correctly.
#
# Exit codes: 0 all stages green; 1 a stage failed (named); 2 setup failure.

set -u

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO" || exit 2
SCHEMA="fln.check/1"
BEAD="franken_lean-rur"
RUN_ID="check-$(date -u +%Y%m%dT%H%M%SZ)-$$"
ART_DIR="${FLN_CHECK_ART_DIR:-$REPO/target/check/$RUN_ID}"
NDJSON="${FLN_CHECK_LOG:-$ART_DIR/run.ndjson}"
mkdir -p "$ART_DIR" "$(dirname "$NDJSON")" || exit 2
CAP_BYTES=262144
PLANT="${FLN_CHECK_PLANT:-}"

jesc() { printf '%s' "$1" | python3 -c 'import json,sys; print(json.dumps(sys.stdin.read())[1:-1], end="")'; }
emit() { printf '%s\n' "$1" >> "$NDJSON"; }
now_ms() { date +%s%3N; }

emit "{\"schema\":\"$SCHEMA\",\"event\":\"run_start\",\"run_id\":\"$RUN_ID\",\"bead\":\"$BEAD\",\"cwd\":\"$(jesc "$REPO")\",\"host\":\"$(jesc "$(uname -srm)")\",\"rustc\":\"$(jesc "$(rustc --version 2>/dev/null || echo unknown)")\",\"planted\":\"$(jesc "$PLANT")\",\"ts_utc\":\"$(date -u -Is)\"}"

run_stage() { # run_stage <name> <cmd...>
  local name="$1"; shift
  local out="$ART_DIR/$name.out" err="$ART_DIR/$name.err"
  local t0 t1 dur rc
  local -a argv=("$@")
  if [ "$PLANT" = "$name" ]; then
    argv=(false) # planted failure: the stage command is replaced wholesale
  fi
  echo "[check] stage=$name: ${argv[*]}" >&2
  t0=$(now_ms)
  "${argv[@]}" > >(head -c "$CAP_BYTES" > "$out") 2> >(head -c "$CAP_BYTES" > "$err")
  rc=$?
  wait
  t1=$(now_ms); dur=$((t1 - t0))
  emit "{\"schema\":\"$SCHEMA\",\"event\":\"stage\",\"run_id\":\"$RUN_ID\",\"stage\":\"$name\",\"argv\":\"$(jesc "${argv[*]}")\",\"planted\":$([ "$PLANT" = "$name" ] && echo true || echo false),\"exit\":$rc,\"duration_ms\":$dur,\"stdout_artifact\":\"$name.out\",\"stderr_artifact\":\"$name.err\"}"
  if [ "$rc" -ne 0 ]; then
    echo "[check] FAIL stage=$name exit=$rc (${dur}ms)" >&2
    echo "[check] --- captured stderr tail ($name) ---" >&2
    tail -n 40 "$err" >&2
    emit "{\"schema\":\"$SCHEMA\",\"event\":\"run_end\",\"run_id\":\"$RUN_ID\",\"verdict\":\"fail\",\"failed_stage\":\"$name\",\"artifacts_dir\":\"$(jesc "$ART_DIR")\"}"
    exit 1
  fi
  echo "[check] ok   stage=$name (${dur}ms)" >&2
}

skip_stage() { # skip_stage <name> <reason>  — a typed, logged, honest skip
  emit "{\"schema\":\"$SCHEMA\",\"event\":\"stage\",\"run_id\":\"$RUN_ID\",\"stage\":\"$1\",\"skipped\":true,\"reason\":\"$(jesc "$2")\"}"
  echo "[check] skip stage=$1: $2" >&2
}

self_test() {
  local failures=0
  for stage in fmt check clippy test structure-guard vendor-tree; do
    echo "[check:self-test] planting failure in stage=$stage" >&2
    local st_log="$ART_DIR/selftest-$stage.ndjson"
    FLN_CHECK_PLANT="$stage" FLN_CHECK_LOG="$st_log" \
      FLN_CHECK_ART_DIR="$ART_DIR/selftest-$stage" bash "${BASH_SOURCE[0]}" \
      > "$ART_DIR/selftest-$stage.console.out" 2> "$ART_DIR/selftest-$stage.console.err"
    local rc=$?
    local named=false
    grep -q "FAIL stage=$stage" "$ART_DIR/selftest-$stage.console.err" \
      && grep -q "\"failed_stage\":\"$stage\"" "$st_log" && named=true
    if [ "$rc" -eq 1 ] && [ "$named" = "true" ]; then
      echo "[check:self-test] ok — stage=$stage failed with exit 1 and was named" >&2
    else
      echo "[check:self-test] FAIL — stage=$stage: exit=$rc named=$named" >&2
      failures=$((failures + 1))
    fi
    emit "{\"schema\":\"$SCHEMA\",\"event\":\"self_test\",\"run_id\":\"$RUN_ID\",\"stage\":\"$stage\",\"planted_exit\":$rc,\"stage_named\":$named,\"ok\":$([ "$rc" -eq 1 ] && [ "$named" = "true" ] && echo true || echo false)}"
  done
  emit "{\"schema\":\"$SCHEMA\",\"event\":\"run_end\",\"run_id\":\"$RUN_ID\",\"verdict\":\"$([ "$failures" -eq 0 ] && echo pass || echo fail)\",\"mode\":\"self_test\",\"artifacts_dir\":\"$(jesc "$ART_DIR")\"}"
  echo "[check:self-test] $([ "$failures" -eq 0 ] && echo PASS || echo FAIL) — artifacts: $ART_DIR" >&2
  exit "$([ "$failures" -eq 0 ] && echo 0 || echo 1)"
}

case "${1:-}" in
  --self-test) self_test ;;
  --help|-h)
    sed -n '2,30p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'
    exit 0
    ;;
  "") ;;
  *) echo "unknown argument: $1 (see --help)" >&2; exit 2 ;;
esac

# --locked: CI builds ONLY from the committed lock (SUITE.lock ceremony, D1, G0-10);
# a drifted Cargo.lock fails the stage instead of being silently rewritten.
run_stage fmt cargo fmt --check
run_stage check cargo check --locked --all-targets
run_stage clippy cargo clippy --locked --all-targets -- -D warnings
run_stage test cargo test --locked
run_stage structure-guard cargo run -q --locked -p structure-guard -- --root "$REPO" --robot
run_stage vendor-tree bash scripts/verify_vendor_tree.sh

# UBS scans project-authored changed + untracked Rust/TOML. The byte-identical Reference
# snapshot is governed by vendor-tree identity instead; its intentionally malformed
# upstream fixtures are data, not FrankenLean-authored code.
if command -v ubs >/dev/null 2>&1; then
  mapfile -d '' -t UBS_FILES < <(
    { git diff --name-only -z HEAD 2>/dev/null; git ls-files --others --exclude-standard -z; } \
      | sort -zu \
      | while IFS= read -r -d '' f; do
          case "$f" in
            vendor/*) continue ;;
            *.rs|*.toml) [ -f "$f" ] && printf '%s\0' "$f" ;;
          esac
        done
  )
  if [ "${#UBS_FILES[@]}" -gt 0 ]; then
    run_stage ubs ubs "${UBS_FILES[@]}"
  else
    skip_stage ubs "no changed project-authored .rs/.toml files (vendor data excluded)"
  fi
else
  skip_stage ubs "ubs binary not on PATH"
fi

emit "{\"schema\":\"$SCHEMA\",\"event\":\"run_end\",\"run_id\":\"$RUN_ID\",\"verdict\":\"pass\",\"artifacts_dir\":\"$(jesc "$ART_DIR")\"}"
echo "[check] PASS — all stages green. Artifacts: $ART_DIR" >&2
exit 0
