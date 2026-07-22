#!/usr/bin/env bash
# Verify that the staged Reference snapshot is the exact Git tree pinned by SUITE.lock.
# This is a CI/development integrity check; vendored Reference code is never built or run.

set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

REFERENCE_LINE="$(awk '$1 == "reference" { print; exit }' SUITE.lock)"
read -r DIRECTIVE REPOSITORY TAG_FIELD COMMIT_FIELD TREE_FIELD EXTRA <<< "$REFERENCE_LINE"
if [ "$DIRECTIVE" != "reference" ] || [ -n "${EXTRA:-}" ]; then
  echo "vendor-tree: malformed or missing SUITE.lock reference row" >&2
  exit 1
fi

TAG="${TAG_FIELD#tag=}"
COMMIT="${COMMIT_FIELD#commit=}"
EXPECTED_TREE="${TREE_FIELD#tree=}"
if [ "$TAG_FIELD" = "$TAG" ] || [ "$COMMIT_FIELD" = "$COMMIT" ] \
  || [ "$TREE_FIELD" = "$EXPECTED_TREE" ]; then
  echo "vendor-tree: reference row needs tag=, commit=, and tree= fields" >&2
  exit 1
fi

for required in vendor/lean4-src/LICENSE vendor/lean4-src/LICENSES vendor/NOTICE; do
  if [ ! -f "$required" ]; then
    echo "vendor-tree: required attribution file missing: $required" >&2
    exit 1
  fi
done
if [ -e vendor/lean4-src/.git ]; then
  echo "vendor-tree: nested Git metadata is forbidden" >&2
  exit 1
fi

# `git write-tree` reads the caller's index without changing it. The vendor import must be
# force-added so upstream's own .gitignore cannot silently omit fixture data.
INDEX_ROOT="$(git write-tree)"
if ! ACTUAL_TREE="$(git rev-parse "$INDEX_ROOT:vendor/lean4-src" 2>/dev/null)"; then
  echo "vendor-tree: vendor/lean4-src is not completely staged" >&2
  exit 1
fi
if [ "$ACTUAL_TREE" != "$EXPECTED_TREE" ]; then
  echo "vendor-tree: staged tree mismatch: expected=$EXPECTED_TREE actual=$ACTUAL_TREE" >&2
  exit 1
fi

if ! git diff --quiet --no-ext-diff -- vendor/lean4-src; then
  echo "vendor-tree: working tree differs from the staged Reference snapshot" >&2
  exit 1
fi
UNTRACKED="$(git ls-files --others -- vendor/lean4-src | sed -n '1p')"
if [ -n "$UNTRACKED" ]; then
  echo "vendor-tree: unstaged Reference path remains: $UNTRACKED" >&2
  exit 1
fi

printf 'vendor-tree: PASS repository=%s tag=%s commit=%s tree=%s\n' \
  "$REPOSITORY" "$TAG" "$COMMIT" "$ACTUAL_TREE"
