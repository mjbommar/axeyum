# Notes: 384-l0-s1-statement-identity

Detail moved out of [`../status/384-l0-s1-statement-identity.md`](../status/384-l0-s1-statement-identity.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**A structural bind needing no pin.** A `render_lean` statement opens
`theorem <name> :` and that name must equal `kernel_theorem`. 1,158 of 1,188
satisfy it, 0 violate it. A hash says "changed"; this says "changed into a
rendering of a different declaration".

```
before: settled=2120|pinned=144|drifted=0                                PASS
after:  settled=2120|pinned=2120|unpinned=0|identity_bound=1294
        |header_exempt=30|drifted=0|floor_unpinned=0|floor_identity=1294 PASS
```

## S1's exit, executed on every merge

`scripts/check-statement-identity-mutations.py`, ~2s, no cargo. Records which
gate rejected each row, because "something failed" is not evidence that the
right thing failed.

```
control|clean-tree|statement=0|mirror=0
1 swapped binders     F-creal-ivt-approx   REJECTED by=statement-pin
2 changed constant    F-creal-ivt-approx   REJECTED by=statement-pin
3 altered relation    F-creal-ivt-approx   REJECTED by=statement-pin
4 source drift        totient-dvd-of-dvd   REJECTED by=statement-pin+mirror-fidelity
5 our own rendering   both totient mirrors REJECTED by=statement-pin+mirror-fidelity
PASS|5/5 rejected|tree restored
```

Rows 1–3 rest on the statement pin **alone**, which is the measurable S1 delta —
before this lane, `F:creal-ivt-approx` was unpinned and all three were accepted.
Mutation 5 replays the two real damaged forms from `e79804fdd` rather than an
invented one.

## Priority population (coordinator-flagged, verified here)

`exact_statement` **0 / 20** across the IVT/EVT rows, none in the pin manifest,
against a ledger-wide control of 142/2117. Now **20/20 pinned, 14/20
identity-bound** — the six `cas-*` rows name no `kernel_theorem`.
`CReal.ivt_approx` and both ADR-0603 row-2 impossibility results are fully
bound, against their corrected prose. They needed no special machinery: full
coverage reaches them by construction, and `CReal.ivt_approx` is the subject of
exit mutations 1–3.

## Mutation kill sets — 19 guards, 19 killed exactly one, 0 survived

`settled-fact-statement-identity` (13 new) and `settled-fact-statements` (6
pre-existing, one anchor re-pointed after the refactor).

Three needed a second pass, and each failure is the same defect in miniature — a
control that passes for a reason other than the guard it names:

- **repointing** and **identity floor** each SURVIVED their first run, masked by
  a neighbouring guard firing on the same fixture. Fixed by isolating: the
  repointing fixture is `cas-term` (header check inert) and carries a second
  stable fact so `identity_bound` does not also fall; the identity fixture
  licenses the repoint with an amendment, leaving the lost binding as the only
  complaint. An amended repoint IS still a lost binding, so that is the right
  semantics as well as the isolating one.
- **the amendment digest check** survived because its two `or` clauses were only
  ever exercised together. Added a fixture with the `from` digest wrong and the
  `to` digest right.

## Non-negotiables, verified

- No fact's `epistemic_status`, `proof_route`, `axiom_footprint`, evidence or
  statement text was edited. A pin asserts only that a claim will not change
  silently; it asserts nothing about whether the claim is right.
- No `formal.statement` was found misdescribing its theorem — but note this lane
  performed **no semantic audit**, only integrity binding. That is S3's job, and
  reading this coverage as review coverage would be exactly wrong.
- `check-autogenesis-holdout-isolation.py`:
  `held_out=116|files_scanned=1109|settled=0|references=0|verdict=PASS`
- `check-mirror-statement-fidelity.py`:
  `facts=2270|mirrors=514|hash_verified=502|unpinned=12|violations=0|verdict=PASS`
- Registered in BOTH `scripts/check.sh` and the justfile;
  `check-aggregate-scope.sh` still reports 64 recorded divergences.

## Two gates this lane turned red, and what it did about them

Measured against a snapshot of `main`, not assumed: main fails **65**
`check-fast.sh` steps, this branch **29**, and exactly one step was ever new
here. (The 37 main-only failures are main having advanced past this branch's
merge base, not this lane fixing anything.)

- **`adr-remote-collisions`.** `gen-adr-index.py --check-remote` found ADR-0752
  claimed by both this checkout and `origin/main`, for different decisions —
  the sibling semantic-controls lane had it. This lane picked 0752 *to avoid* a
  collision on 0747 and collided anyway, because it checked the local tree and
  the local tree does not know about origin. **Use `--check-remote`, not `ls`.**
  Renumbered to 0763; now `collisions=0|next_free=0764`, flagged ADVISORY
  because there is no `FETCH_HEAD` and the remote data is of unknown age.
- **`safety-matrix`.** S0's census pinned
  `F:nat-sumrange-add.exact_statement == False` so the column could not silently
  start saying yes to everything. Pinning every settled fact made that
  unsatisfiable — no census row can be the False side at 100% coverage — so the
  census would have stayed red for a reason that is good news.

  **S0's owner should review the repair.** Flipping the row to `True` alone
  would have deleted the column's negative polarity, so the polarity moved
  instead: `UNPINNABLE_PROBE` asserts `statement_pinned_ids()` does not contain
  an id that is in no manifest and no ledger, catching the predicate's real
  failure mode (reading the wrong field, or returning everything). Verified by
  mutation — `poisoned -> FIRED`, `healthy -> silent`. It is a **smaller claim**
  than a census-row negative; if a stronger one is wanted it belongs in
  `gen-safety-matrix.py`, which is S0's file, not this lane's.

`exact_statement` moved **142 / 2117 → 2118 / 2118 (100.0%)**: the thinnest
column in the matrix is now the only complete one.

Unrelated hygiene note, not this lane's to fix: `check-fast.sh`'s
`gate-step-timeout` step leaves five untracked `tmp*/` directories in the
worktree after every run.

## For the next lane

- **Landing a settled fact now requires `--write` and committing the manifest.**
  One command. The failure message names it.
- **The manifest is machine-written** (~14,900 lines). `--write` is the only
  supported writer; hand-editing the floor is caught by the slack check.
- **S2 (circularity) inherits a usable hook**: `kernel_theorem` is now pinned per
  fact, so the authored declaration identity S2 must compare against observed
  dependencies is already bound and cannot drift underneath it.
- **The 30 headerless `lean4` statements are the remaining structural gap** in
  this column. Each carries a bare type with no `theorem <name> :` header, so
  nothing ties it to the declaration it claims beyond `kernel_theorem` itself.
  Bounded by `max_header_exempt` so it cannot grow; reducing it is ordinary work.
