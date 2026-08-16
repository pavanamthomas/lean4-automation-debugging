# Lean 4 automation debugging

This repository is a Lake project that records how failed Lean 4 proofs
are diagnosed and repaired. Each case starts from a defective attempt,
classifies the failure, chooses the smallest repair that preserves the
intended mathematics, and checks that the repaired declaration compiles
against pinned Lean 4 and mathlib.

It is a working library, not a list of disconnected tactic snippets.

## 1. Purpose

Given a failing goal or a defective proof attempt, the work is:

1. identify *why* it fails,
2. classify the failure,
3. apply the smallest semantics-preserving repair,
4. compile the repaired declaration,
5. record the engineering trade-off (named lemma vs `simp` vs `ring`
   vs `aesop`/`grind`).

Broken candidates are kept as comments (or otherwise isolated) so they
do not enter executable declarations.

## 2. Proof failure versus semantic failure

A **proof failure** is a true statement whose candidate proof does not
close: type mismatch, rewrite match failure, missing instance, wrong
tactic class, missing local hypothesis that the statement already has,
and so on.

A **semantic failure** is a statement that is false, weaker than the
intent, quantified in the wrong order, or proved only after changing
the domain. Closing a different goal is not a repair.

Compilation is necessary and not sufficient. Every repaired case is
checked against:

- Did the repair preserve the original theorem meaning?
- Did it add an unjustified assumption?
- Did it weaken the conclusion?
- Did it alter domain or type?
- Did it change quantifier order?
- Did it become vacuous?
- Did automation prove the intended theorem rather than a neighbour?

## 3. Debugging workflow

The cases follow this procedure:

1. Read the exact target.
2. Read the local context.
3. Identify types (including coercions).
4. Check domain (`ℕ` vs `ℤ` vs `ℝ`) and coercions.
5. Test `exact` / `apply` candidates.
6. Inspect the expected lemma with `#check` (and `#print` when the
   definition matters).
7. Use `exact?`, `apply?`, `simp?` as *search*, then delete them from
   the reviewed proof.
8. Reduce automation: replace a kitchen-sink tactic with a named lemma
   or a problem-class tactic (`ring`, `omega`, `linarith`).
9. Introduce intermediate `have` statements when the gap is semantic.
10. Separate a false statement from a failed search.
11. Compile the module (`lake build AutomationDebugging.<Module>`).
12. Run a full `lake build`.

Several cases spell these steps out in the module comments
(for example C12, C29, C35, C36, C49, C50).

## 4. Automation and tool coverage

| Class | Tools shown |
| --- | --- |
| Goal closing | `exact`, `assumption`, `apply`, `refine`, `constructor`, `intro`, `rcases`/`obtain`, `cases`, `contradiction` |
| Rewriting | `rw`, `←` direction, multi-`rw`, local vs `at *`, `calc`, `congrArg`, `funext`/`ext` |
| Simplification | `simp`, `simp only`, `simp at`, `simp_all` (discussed), `simpa` (rejected when unnecessary) |
| Arithmetic | `norm_num`, `ring`, `ring_nf`, `linarith`, `nlinarith`, `omega` |
| Search | `#check`, `#print`, `exact?` / `apply?` / `simp?` as diagnostics |
| General automation | `aesop`, `grind` compared with explicit proofs, not used to inflate tactic variety |

## 5. Exact environment

These pins are the versions this repository was built with:

| Pin | Value |
| --- | --- |
| Lean toolchain | `leanprover/lean4:v4.33.0` |
| Lean version string | `4.33.0` (commit `d8b18978322de05a8f3dba51ef03cf5461676c17`) |
| mathlib input revision | `v4.33.0` |
| mathlib git revision | `db584cd6d46c92f209a44c0f1c829460d327499d` |

Files that lock this:

- `lean-toolchain`
- `lakefile.toml` (`rev = "v4.33.0"`)
- `lake-manifest.json` (generated, committed)

mathlib cache: after `lake update`, `lake exe cache get` is run by
mathlib's post-update hook. This repository was initialized that way
and did not recompile mathlib from source.

## 6. Repository organization

```
AutomationDebugging.lean                 -- library root imports
AutomationDebugging/
  GoalMechanics.lean                     -- C01–C08
  Rewriting.lean                         -- C09–C16
  Simplification.lean                    -- C17–C22
  ArithmeticAutomation.lean              -- C23–C30
  Search.lean                            -- C31–C35
  Coercions.lean                         -- C36–C39
  Typeclasses.lean                       -- C40–C42
  InductionFailures.lean                 -- C43–C46
  PerformanceTraps.lean                  -- C47–C48
  ReviewerCases.lean                     -- C49–C54
CASE_INDEX.md
FAILURE_TAXONOMY.md
AUDIT_CHECKLIST.md
scripts/build_and_check.sh
scripts/check_no_sorry.sh
.github/workflows/ci.yml
```

See `CASE_INDEX.md` for the case table and `FAILURE_TAXONOMY.md` for
the failure-class table.

## 7. How to build

Requires [elan](https://github.com/leanprover/elan).

```bash
elan --version   # 2.0.0 or newer
lake update      # fetches mathlib at the pinned revision; runs cache get
lake exe cache get   # if cache was skipped
lake build
```

Targeted module build during development:

```bash
lake build AutomationDebugging.Rewriting
```

## 8. How to run checks

```bash
bash scripts/check_no_sorry.sh    # no `sorry`, `admit`, or `axiom` in project .lean files
bash scripts/build_and_check.sh   # the above, then targeted builds, then lake build
```

CI (`.github/workflows/ci.yml`) runs the same rejection script and
`leanprover/lean-action@v1` with `build: true`, mathlib cache enabled,
and nanoda left off.

## 9. Limitations

- Search tactics (`exact?`, `apply?`, `simp?`) are documented from
  `#check` of the lemmas they are expected to find. They are not left
  in reviewed proofs, because they re-run library search on every
  build.
- `#check` and `#print` emit info traces during `lake build`. That is
  intentional documentation, not a failed build.
- `aesop` and `grind` appear as comparisons, not as a claim that they
  are the right default for every goal.
- Deprecated mathlib aliases still compile with warnings. C32 records
  the current name rather than using the alias.
- This is not a substitute for the mathlib docs or the Lean reference
  manual. Lemma names are those of mathlib `v4.33.0`.
- CI status on GitHub is independent of a local `lake build`. A local
  green build does not imply that the remote workflow has run.

## 10. Reproducibility

A rebuild on another machine should use the committed `lean-toolchain`
and `lake-manifest.json`, not `master` of mathlib. `lake update`
without a pin would move mathlib and is not the documented workflow
for reproducing this snapshot.
