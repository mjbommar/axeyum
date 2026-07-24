# SMT-COMP credited full-cell admission fixture

Status: process-free admission and admitted-wave execution implemented on the
SMT topic; no live F2 acceptance, F3 cell, or F4 result

Date: 2026-07-23

Plan: [credited full-population execution plan](smtcomp-credited-full-population-plan-2026-07-23.md)

## Result

The F2 preparation contract deliberately ends with
`launch_authorized=false`. The new `full_admission.py` boundary therefore
requires a distinct acceptance record before any F3 cell may execute. The
acceptance binds the exact preparation completion, selection, and prepared
source commit. A live admission requires the canonical acceptance file to be
committed byte-for-byte on a clean `HEAD == origin/main`, and proves that the
prepared source revision is an ancestor of that acceptance commit.

Admission is sequential. Axeyum requires no prior result; cvc5 requires the
exact safe Axeyum completion; Bitwuzla requires exact safe Axeyum and cvc5
completions in solver order. Known-status contradictions or cross-solver
disagreements already make those completions unsafe and therefore stop the
next admission.

The admitted-wave entry point replays the admission, derives the run, plan,
schedule, cell, and immutable checkpoint prefix from the preparation tree, and
then invokes the existing one-wave supervisor. A completed checkpoint is
installed atomically before the outcome returns. Callers do not supply those
execution identities independently.

Durable replay reads the acceptance from the recorded Git object, so a later
mainline advance does not invalidate an already issued admission. Creation is
stricter: it can happen only at the current clean integrated revision.

## Fixture evidence

The focused gates cover:

- 40-character Git object identity versus 64-character content digests;
- acceptance field, seal, and prepared-source ancestry rejection;
- exact byte identity at the canonical integrated acceptance path;
- durable acceptance replay after `origin/main` advances;
- rejection of preparation, composition, plan, and schedule drift;
- rejection when a solver skips its exact safe prior-result prefix;
- replay after permitted current-cell execution evidence appears; and
- admitted identity derivation plus automatic immutable checkpoint
  publication.

The complete `./scripts/check-smtcomp-resume.sh` lane gate passes 139 tests with
one expected live-host skip. Documentation links pass. Foundational resources
validate 137 concepts and 174 packs, including the consumer smoke gate.

The repository-wide gate is not green for separately owned bytes. `cargo fmt
--all --check` reports only bench/CAS formatting drift. `just parity-docs`
currently stops at the integrated quotient-package contract because
`crates/axeyum-lean-import/src/lib.rs` lacks its expected marker; the previously
observed `resume_fs.py` historical/current pin is downstream of that failure.
This SMT increment does not edit either owner surface.

## Claim boundary

This result creates neither the live acceptance manifest nor a preparation
root. It performs no Git mutation outside the topic worktree, host probe,
sentinel run, NAS mutation, systemd action, solver launch, or result claim. The
integration owner must first green-gate and land these bytes. A later reviewed
F2 run must then publish its empty preparation, and a separate mainline commit
must accept that exact completion before F3 admission can exist.
