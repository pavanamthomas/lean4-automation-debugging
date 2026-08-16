#!/usr/bin/env bash
# Reject unfinished-proof tokens and custom axioms in project Lean sources.
# Scans repository `.lean` files and ignores `.lake/` (toolchain and mathlib).
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

fail=0

if find . -name '*.lean' -not -path './.lake/*' -print0 \
  | xargs -0 grep -n -E -w 'sorry|admit' --; then
  echo "FAIL: found sorry or admit in project Lean sources" >&2
  fail=1
else
  echo "PASS: no sorry or admit in project Lean sources"
fi

if find . -name '*.lean' -not -path './.lake/*' -print0 \
  | xargs -0 grep -n -E '^[[:space:]]*axiom[[:space:]]' --; then
  echo "FAIL: found custom axiom declaration in project Lean sources" >&2
  fail=1
else
  echo "PASS: no custom axiom declarations in project Lean sources"
fi

exit "$fail"
