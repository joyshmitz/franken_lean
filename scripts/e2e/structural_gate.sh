#!/usr/bin/env bash
# SUPERSEDED — consolidated into scripts/e2e/structure_gate.sh (bead fln-8mj).
#
# Two agents independently wrote this scenario; the canonical script is
# structure_gate.sh (real-workspace copies as fixtures, layering + unsafe-ledger
# negative/recovery legs, NDJSON artifacts). This delegating stub is retained only
# because file deletion requires express permission (AGENTS.md Rule 1) — once that
# permission is given, delete this file.
exec "$(dirname "$0")/structure_gate.sh" "$@"
