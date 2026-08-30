# ADR-0621: An artifact citation is a caller, so a cited gate stays in `scripts/`

Status: accepted
Date: 2026-08-30
Index-summary: A committed artifact naming its gate is a caller of a different kind; 125 cited scripts were archived where `parents[1]` makes them unrunnable, so a cited gate must live in `scripts/` at the path the artifact spells

Lane: `archive-provenance`

## Context

Commit `98d17aeef` moved 346 `check-*` scripts from `scripts/` into
`scripts/archive/`. Its criterion was **"no live caller in `scripts/check.sh`
or the justfile"**, and on that criterion it was correct: most of those scripts
really were called by nothing.

The criterion was incomplete in a way the census could not see. Artifacts under
`artifacts/` name the gate that reviewed them. A plan names the gate expected to
run; a result and a sealed capsule name the gate that reviewed them, then. Those
are callers of a different kind.

Measured on `main` before this change:

| citations of `check-*` scripts by files under `artifacts/` | count |
| --- | --- |
| distinct script names cited | 212 |
| resolving into `scripts/` | 87 |
| **resolving only into `scripts/archive/`** | **125** |
| resolving nowhere | 0 |

Nothing was deleted — files were moved — but 111 of those citation pairs spell
an explicit `scripts/check-X.py`, so 111 committed artifacts carried a path that
was simply false. Zero artifacts spell `scripts/archive/`.

### Archiving made the scripts non-runnable, not merely unlisted

The two failures that surfaced (`check-autogenesis-modeq-family.py` and
`check-autogenesis-bounded-induction-family.py`, both via
`validate-autogenesis-operations.py`'s `reviewed_gate_mentions` check) were not
genuine check failures. Every archived script resolves the repo root as

```python
ROOT = pathlib.Path(__file__).resolve().parents[1]
```

which is the repo root from `scripts/` and is **`scripts/` itself** from
`scripts/archive/`. Running one from its new home:

```
No such file or directory:
  .../scripts/artifacts/autogenesis/mathlib-nat-fib-iterate-recurrence-result-v1.json
```

**345 of 345** archived Python files carry that idiom. (Positive control: 256
live scripts carry it too, where it is correct.) So the sweep did not park 346
scripts somewhere tidy — it made every one of them unable to run.

Only two of the 125 ever surfaced, because only some artifact classes are
validated for script existence at all. The other 123 were latent, including
three sealed-capsule receipts that nobody could re-check.

### A second class of caller, also invisible to the census

Capsule checkers invoke sibling checkers by path
(`RESULT_CHECKER = ROOT / "scripts/check-...-construction-result.py"`). Five
such references from four files dangled into the archive. Positive control on
that scan: 175 sibling references that resolve correctly.

## Decision

**A script named by a committed artifact lives in `scripts/`, at the path the
artifact spells.** Archiving is a location change and must not cost
verifiability; a receipt nobody can re-check is close to a receipt that says
nothing.

Concretely:

1. **129 scripts restored** to `scripts/` — 125 cited directly by an artifact,
   4 more by transitive closure through sibling invocation. **217 stay
   archived**: cited by nothing, called by nothing. The cleanup is preserved,
   now on a criterion that is true.
2. **Nothing was rewritten.** Restoring to `scripts/` makes `parents[1]` correct
   again *and* makes the artifacts' own spelling true, so neither the 345
   scripts nor the 111 artifacts needed editing. The alternative — rewriting 111
   committed artifacts to point at the archive — would have edited history to
   match a cleanup rather than the other way round.
3. **`scripts/check-artifact-gate-provenance.py`** gates the class, registered
   in both `scripts/check.sh` and the justfile.

## The gate asserts resolvability, not exit 0

This is the part worth arguing, because the obvious stronger gate is wrong.

Running all 129 restored scripts: **103 pass, 26 fail, 0 timeout**. The failures
split by artifact class, and the split is the finding:

| class | passing |
| --- | --- |
| capsule | 16 / 16 |
| result | 31 / 33 |
| plan | 52 / 76 |

A result or capsule checker re-verifies a **frozen** artifact and should pass
forever. A plan checker asserts preconditions about the **live tree** — "target
is still open", "helper identity unchanged" — and goes stale by design once the
work it planned lands. A stale plan gate is the flywheel turning, not a defect.

So requiring exit 0 would red the gate on 24 correctly-stale plans, and a gate
that fires on healthy progress is a gate someone disables. Resolvability is the
property that holds for every class, and it is the one that was actually broken.

(The 2 failing result checkers are unrelated to location: one needs an
out-of-tree `/data0` scratch pack, one reports genuine drift —
`implementation identity changed`.)

## Guards

| guard | refuses |
| --- | --- |
| `escape` | a citation resolving outside the repo |
| `dangling` | a cited script in neither `scripts/` nor `scripts/archive/` |
| `archived` | a cited script that exists only in the archive |
| `path-mismatch` | a citation spelling a directory that is not where the file is |
| `sibling` | a live script invoking a sibling gate that is only archived |
| `vacuity` | a scan matching far fewer citations than the tree holds |

Two of these nearly went in wrong, and both mistakes generalize.

**`escape` must not simply ban `..`.** The first draft did, and redded four real
artifacts (`artifacts/claims/{offdiag-schur,rado,vdw}/SEMANTICS.md`,
`artifacts/episodes/README.md`) whose relative markdown links resolve perfectly
well. Two conventions are in use and both are correct in context: a JSON
artifact writes `scripts/check-X.py` meaning repo-root-relative, a markdown one
writes `../../../scripts/check-X.py` meaning file-relative. The gate resolves
under both and accepts a citation if the file sits at either reading.

**The two vacuity floors are tested one at a time**, with the other lowered out
of the way. Both fire on an empty tree, so a single empty-tree test would let
either be deleted while staying green — the "guard nobody can remove" shape this
repository keeps rediscovering.

Mutation controls: `python3 scripts/tests/mutation_controls.py
artifact-gate-provenance`, baseline 11 tests. All seven guards **killed exactly
one test each**, and each the test named for it. No survivors, no unmeasured
mutations.

## Consequences

- `check-autogenesis-modeq-family.py` and
  `check-autogenesis-bounded-induction-family.py` go from exit 1 to
  `..._OK`, exit 0.
- Three sealed-capsule receipts that could not be re-checked by anybody now
  re-check and pass: `nat-fib-dvd`, `nat-fib-gcd`, `int-fib-natcast`.
- `scripts/` regains 129 files. It costs no gate time: `check.sh` runs an
  explicit step list, not a `scripts/check-*` glob, so a restored script adds a
  step only when somebody registers it.
- A future archiving sweep must use "no live caller **and** no artifact
  citation". Running the gate is how you find out; it fails naming the artifact
  and the script.
- **Not decided here:** whether the 217 still-archived scripts should have their
  `parents[1]` made location-independent. They are cited by nothing and called
  by nothing, so nothing claims they run, and restoring one to `scripts/`
  self-heals the idiom. If the archive ever grows a caller of its own, this
  needs revisiting.

## Alternatives rejected

- **Restore all 346.** Undoes a real cleanup and does not stop the recurrence.
- **Rewrite the 111 artifact citations to `scripts/archive/...`.** Edits
  committed history to match a sweep, and leaves the scripts still unable to run
  from there — the citation would resolve while the receipt stayed uncheckable.
- **Make all 345 archived scripts location-independent.** A 345-file mechanical
  rewrite of files nothing calls, when restoring the 129 that *are* called fixes
  the same problem with zero content edits.
- **Have the gate run each cited script and require exit 0.** Reds on 24
  correctly-stale plan gates; see above.
