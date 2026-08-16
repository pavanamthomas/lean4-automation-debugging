# Audit checklist

Fill in from a genuine run of the pinned toolchain. Do not mark a
row PASS unless the corresponding command succeeded.

## Environment

| Item | Expected | Observed | Status |
| --- | --- | --- | --- |
| Lean version | `4.33.0` from `lean-toolchain` | `Lean (version 4.33.0, x86_64-unknown-linux-gnu, commit d8b18978322de05a8f3dba51ef03cf5461676c17, Release)` | PASS (local) |
| mathlib input revision | `v4.33.0` in `lakefile.toml` | `v4.33.0` | PASS (local) |
| mathlib git revision | `lake-manifest.json` package `mathlib` | `db584cd6d46c92f209a44c0f1c829460d327499d` | PASS (local) |

## Build

| Item | Command | Status |
| --- | --- | --- |
| Mathlib cache | `lake update` post-hook ran `lake exe cache get` (8690 files) | PASS (local) |
| Targeted module builds | `lake build AutomationDebugging.<Module>` for each module under `AutomationDebugging/` | PASS (local) |
| Full Lake build | `lake build` | PASS (local) |

## Soundness tokens

| Item | Command | Status |
| --- | --- | --- |
| No `sorry` | `bash scripts/check_no_sorry.sh` | PASS (local) |
| No `admit` | same script | PASS (local) |
| No custom `axiom` | same script (`^axiom` in project `.lean`, excluding `.lake`) | PASS (local) |

## Documentation audits

| Item | Method | Status |
| --- | --- | --- |
| Failure taxonomy vs cases | Every representative case id in `FAILURE_TAXONOMY.md` exists in `CASE_INDEX.md` and in a `.lean` file | PASS (local) |
| Statement-faithfulness | Each repaired theorem checked for domain, binders, and conclusion vs the documented intent | PASS (local) |
| Type / domain | `ℕ` identities not silently moved to `ℤ`; coercions to `ℝ` stay on `ℝ` | PASS (local) |
| Assumption audit | Extra hypotheses dropped (C51); required nonzero/positivity/inequality kept (C29, C30, C36, C49) | PASS (local) |
| `CASE_INDEX.md` consistency | 54 cases C01–C54 match compiling `theorem`/`def` names | PASS (local) |
| `README.md` consistency | Purpose, workflow, pins, layout, build, checks, limitations match the repo | PASS (local) |

## CI

| Item | Expected | Status |
| --- | --- | --- |
| Workflow file | `.github/workflows/ci.yml` | present |
| Triggers | `push` to `main`, `pull_request` to `main` | present |
| Checkout | `actions/checkout@v4` | present |
| Reject `sorry`/`admit` | `bash scripts/check_no_sorry.sh` | present |
| lean-action | `leanprover/lean-action@v1` | present |
| `build` | `true` | present |
| nanoda | `false` (not enabled) | present |
| mathlib cache | `use-mathlib-cache: true` | present |
| Remote CI run | GitHub Actions on the published branch | **not claimed here** — depends on GitHub after push |

## Warnings

| Item | Note |
| --- | --- |
| Info traces | `#check` / `#print` print info during `lake build`. Not failures. |
| `#print Nat.add_comm` | Prints the kernel-level `brecOn` implementation. Noisy but accurate. |
| Deprecated aliases | Documented in C32/C33; repaired proofs use current names so the project build is warning-clean for those identifiers. |

## Limitations

See README section 9. In particular: search tactics are diagnostic, not
left in reviewed proofs; lemma names are those of mathlib `v4.33.0`;
a local PASS does not imply a green GitHub Actions run until CI has
executed on the remote.

## Semantic repairs made (summary)

Repairs that changed a *statement* did so only when the original
statement was false or weaker than the documented intent:

| Case | Change | Why it is not a weakening-for-automation |
| --- | --- | --- |
| C29, C49 | Added `≠ 0` | Unrestricted field cancellation is false at `0` |
| C30 | `≠ 0` replaced by `0 < a` | Positivity of inversion is not invertibility |
| C36 | Added `m ≤ n` | Truncated `ℕ` subtraction does not cancel |
| C40 | Required `AddCommMagma` | Commutativity is the theorem |
| C41 | `GroupWithZero` + `≠ 0` | Bare `Div` has no cancellation |
| C45 | `∃∀` not proved; `∀∃` proved | `∃∀` is false on `ℕ` |
| C50 | Added `∃!` theorem | Existence compiled but uniqueness was the intent |
| C51 | Dropped unused `≤` | Extra hypothesis narrowed the theorem |
| C54 | Conclusion `n + k ≤ m + k` | `n + k ≤ m` is false |

No repaired executable theorem uses unfinished-proof tokens or custom
axioms.
