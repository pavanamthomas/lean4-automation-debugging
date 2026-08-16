#!/usr/bin/env bash
# Targeted then full Lake build, plus the unfinished-proof / axiom check.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

export PATH="${HOME}/.elan/bin:${PATH}"

echo "==> Lean version"
lean --version
echo "==> Toolchain pin"
cat lean-toolchain

echo "==> Reject unfinished proofs and custom axioms"
bash scripts/check_no_sorry.sh

echo "==> Targeted module builds"
lake build AutomationDebugging.GoalMechanics
lake build AutomationDebugging.Rewriting
lake build AutomationDebugging.Simplification
lake build AutomationDebugging.ArithmeticAutomation
lake build AutomationDebugging.Search
lake build AutomationDebugging.Coercions
lake build AutomationDebugging.Typeclasses
lake build AutomationDebugging.InductionFailures
lake build AutomationDebugging.PerformanceTraps
lake build AutomationDebugging.ReviewerCases

echo "==> Full lake build"
lake build

echo "==> All checks passed"
