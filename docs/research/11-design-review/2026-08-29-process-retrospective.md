# Process retrospective, 2026-08-29 — what to add, remove, change

A design review of *how the work gets done*, not a summary of what happened.
Every number below was re-measured in this lane's own worktree after
`git merge --no-edit main`; where a query could have been empty for the wrong
reason it is paired with a positive control, and the control is stated.

**Three of the brief's premises did not survive checking.** They are corrected
first, because two of them would have sent work at problems that are already
solved.

---

## Part 0 — Corrections to the brief

### 0.1 The `nat_prelude_tests.rs` pin counter is already gone

The brief proposes deleting it and asks whether an environment-derived check
covers what it caught. Both halves are already done:

* `nat_prelude_tests.rs` contains **no** `[T; N]` inventory pin and no
  `assert_eq!(names.len(), N)`. `theorem_names` returns a plain `Vec` with 557
  entries. (The one `[u32; 11]` in the file is a Fibonacci value table.)
* `every_nat_declaration_is_checked_and_axiom_free` already derives coverage
  from `k.environment()`, filtered to `Nat.`, and fails naming anything
  unlisted. The other direction is covered too:
  `every_promised_name_is_admitted_with_the_expected_kind` panics on a listed
  name absent from the environment.

Positive control for the "no pin" claim: the same query
(`assert_eq!(… .len(), <2+ digits>)`) returns **10 hits** elsewhere in
`crates/axeyum-lean-kernel/src` — `rat_prelude_tests.rs:231`,
`creal_model_tests.rs:56`, `inductive_tests.rs:2420`, and others — so the
pattern works and `nat_prelude_tests.rs` genuinely has none.

**What has NOT been transplanted is the fix that mattered.** `creal` was
sharded into `creal/inventory/*.rs` so two `creal` lanes stop editing one file.
`nat_prelude` never got that, and it is now the busier prelude:

| file | commits in window | size |
| --- | --- | --- |
| `nat_prelude/nat_prelude_tests.rs` | **100** | 15,835 lines |
| `nat_prelude.rs` | **100** | 4,788 lines |
| `PLAN.md` | 98 | 1.6 MB, generated |
| `int_prelude/int_prelude_tests.rs` | 22 | |
| `creal.rs` | 20 | 16,253 lines |
| `creal/creal_tests.rs` | 16 | 11,109 lines |

Note `nat_prelude.rs` — **667 `NameId` fields, 395 `declare_*` calls** — tied at
100 commits and not named in the brief. It is the same fused
registry/struct/order/dispatch shape the 2026-08-27 architecture review
diagnosed in `creal.rs` (441 fields, 364 calls). Sharding `creal_tests.rs`
without sharding `creal.rs` halved that prelude's contention; `nat_prelude` has
had neither half.

### 0.2 The aggregate gate has no automatic caller — that is why 16 steps rotted

This is the sharpest finding in the review and it reframes the brief's "I ran
the gate for the first time in a while."

* `scripts/check.sh` declares **379** steps (`AXEYUM_CHECK_LIST=1`).
* **Neither `hooks/pre-push` nor `.github/workflows/ci.yml` invokes it.**
  `ci.yml` mentions `check.sh` twice, both inside comments. Positive control:
  both files DO name `scripts/check-kernel-suites.sh` and
  `scripts/check-lean-golden-pins.sh`, so the query is not simply broken.
* `hooks/pre-push` runs ~10 cargo/script steps directly. It does not run
  `validate-facts.py`, the 387 python controls, or `check-control-registration.sh`.

So the aggregate gate's only caller is a human typing it. And the specific
consequence is exact and circular:

```
scripts/check-local-ci-freshness.sh
  -> newest applicable record is 265h old, 3974 commits behind HEAD
  -> FAIL: exceeds the 48h budget
```

`check-local-ci-freshness.sh` is *the gate whose entire job is to notice the
battery has gone stale*, and its only caller is the gate that had gone stale.
That is almost certainly the brief's "one had been red 11 days" (265 h = 11.0
days). The detector was correct, present, controlled, and unreachable.

**And it is cost that keeps it unreachable, not discipline.** Sampling every
5th non-cargo step (71 of 355) took **549 s**, of which **15 steps accounted for
528 s** — the other 56 averaged ~0.4 s. Extrapolated, the non-cargo half alone
is ~45 minutes, before the 24 cargo steps. Telling lanes "don't run the gate, I
re-verify" was forced by arithmetic. The remedy has to be architectural, not
exhortative.

### 0.3 Where the brief was right, and by more than it said

* **Carrier-hardcoded dev helpers**: confirmed and already documented in
  `CLAUDE.md` (`NatOps::congr`, `IntDev::irefl`, `congr_bool_to_nat`). `fn congr`
  is defined in **12 separate files across 4 modules** (`nat_prelude` 5,
  `string_prelude` 5, `characterization` 1, `prelude` 1) — each a private
  re-derivation of the same idea at its own carrier.
* **Same module basename in two preludes**: not one case. `nat_prelude/` and
  `int_prelude/` share **10** basenames — `algebra crt defs division euler
  fibonacci gcd ops order parity`. Across the whole kernel **58** basenames
  appear in 2+ directories; excluding the deliberate `creal`/`creal/inventory`
  pairing, `ops` lives in 4 preludes and `defs` in 3.
* **Status-doc numbering already collides**: 211 numbered docs, and 9 numbers
  are reused — `141` **four** times, `135` and `138` three times each. Silently.

---

## Part 1 — What to add

### R1 (highest value). Give the aggregate gate an automatic caller it can afford

**Problem.** §0.2. A 45–90 minute gate with no automatic caller rots, and the
rot is invisible because the staleness detector is inside the rotted gate.

**Change, in two parts.**

1. *Built in this lane*: `scripts/check-fast.sh` — reuses the existing
   `AXEYUM_CHECK_LIST=1` enumeration contract (no edit to `check.sh`'s step
   machinery), runs every declared step under a per-step cap, and reports three
   outcomes: `ok` / `FAILED` / **`DEFERRED`**. Registered with controls in both
   `scripts/check.sh` and the justfile; `check-control-registration.sh` goes
   25 → 26 controls, 0 orphans.

   The load-bearing design constraint: **a deferred step must never read as a
   passing step.** That is the checker-that-cannot-fail defect wearing a
   performance optimization's clothes. So `NOT-A-FULL-GATE` is on every exit
   path, DEFERRED has its own counter, and an empty step list exits **2** rather
   than printing a green summary of nothing.

   *Controls and the false-positive case*, as the brief requires of anything
   proposed as a gate. Five guards, each mutation-verified in this worktree to
   kill **exactly one** control:

   | guard deleted | control that dies |
   | --- | --- |
   | the `n_declared < 1` vacuity exit | empty step list exits 2 |
   | `failed → exit 1` | a nonzero step fails the gate |
   | the 124/137 branch (fold DEFERRED into `ok`) | over-budget step is DEFERRED |
   | `NOT-A-FULL-GATE` in the summary | all-green run carries the marker |
   | the `*cargo*` case arm | cargo step never executed |

   False-positive control: a healthy mixed run (2 passes, 1 deferral, 0
   failures) must exit 0 — and it survives all five mutants, which is what
   distinguishes it from a sixth guard. The cargo control asserts
   **non-execution** through a side-effect marker file, because asserting on the
   counter alone passes even if the step ran.

2. *Not built here, needs your call*: wire tier-0 into `hooks/pre-push` **after**
   the currently-red steps are green. Wiring a red gate into the hook today
   would block every sibling lane's push, which is why this lane did not do it.

**Cost.** The script is 140 lines and exists. Wiring it is one line in
`hooks/pre-push` plus whatever the currently-red steps cost to fix.

**How you'd know it worked.** `check-local-ci-freshness` never again reports a
record older than its own 48 h budget. Concretely: the *maximum age at which a
red gate is discovered* drops from 265 h to under 24 h. That number is readable
from the freshness gate itself, so it cannot be inflated.

### R2. `.gitattributes` for the generated files — there is none

**Problem.** `PLAN.md` is **1.6 MB**, fully generated, gated by
`gen-plan.py --check`, and touched by 98 commits in the window. The repository
has **no `.gitattributes` and no configured merge driver** (`git config
--get-regexp 'merge\.'` → empty). So every concurrent lane hand-resolves
conflicts in a file whose correct resolution is always "run the generator".

**Change.** `.gitattributes`:

```
PLAN.md            merge=axeyum-generated
docs/research/09-decisions/README.md merge=axeyum-generated
```

plus a `merge.axeyum-generated.driver` that takes `%A`, ignores `%B`, and runs
the generator — registered in whatever host-setup script already exists, since a
merge driver is uniform across lanes and therefore safe as repo-local config
(unlike `git config axeyum.agent`, which was per-lane and broke for that reason).

**Cost.** One file, one config line, one small driver script.

**How you'd know.** Count merge commits whose message or reflog records a
`PLAN.md` conflict, before and after. Should go to zero. Secondary signal: the
generator's own `--check` still gates correctness, so a wrong driver cannot ship
a stale PLAN.md silently.

### R3. A contention gate — mechanize the sharding decision instead of learning it from conflicts

**Problem.** The repository's most expensive recurring lesson is "per-lane state
in per-lane paths", and it is learned each time by *paying for the collision
first*: `PLAN.md`, the ADR index, `creal_tests.rs`, and now `nat_prelude.rs` /
`nat_prelude_tests.rs` at 100 commits each. Nothing in `scripts/` measures
contention — verified by name search over all 505 `check-*` scripts, positive
control `check-aggregate-scope.sh` (found).

**Change.** `scripts/check-shared-append-points.py`: for each tracked file,
count **distinct `Agent:` trailers** committing to it over a trailing window.
Fail when a file crosses a threshold and is not listed in
`scripts/shared-append-points.tsv` with a written plan — the same
register-and-reason shape as `scripts/control-optout.tsv`, and with the same
**ceiling** on the exclusion count, so the list cannot quietly grow into the
floor-nobody-chose anti-pattern the python-orphan ratchet already died of.

*Controls*: positive — `nat_prelude_tests.rs` (100 commits, many lanes) must be
flagged. **False-positive case** — a generated file (`PLAN.md`) has high
contention by construction and must be excludable with a reason, not by lowering
the threshold; a suite without that case would let the exclusion mechanism be
deleted while staying green. Mutation: drop the distinct-lane counting and count
raw commits instead, and exactly the "one lane's 40 commits is not contention"
control dies.

**Cost.** ~150 lines plus a seeded TSV.

**How you'd know.** It should fire *before* the next hand-resolved conflict in a
new file, not after. Track: number of files that reached >20 distinct lanes
without an entry in the TSV. Target zero.

### R4. Extend `check-absence-claims.py` from declarations to numbers

**Problem.** The brief's own list of coordinator errors is three instances of
one thing: *a number in prose that no longer derives from the tree* (a stale
prebuilt binary's number; a survey grep that read "12 sites, 1 covered" when the
truth was 72 and 0; a generalization from N=1). `check-absence-claims.py`
(ADR-0611) already solved the *declaration* case with an expiring marker. The
numeric case is unguarded.

**Change.** Same grammar, one more marker:

```
<!-- measured: 379 | AXEYUM_CHECK_LIST=1 scripts/check.sh | wc -l -->
```

The gate re-runs the command and fails when the number moved, naming the file
and line. Restrict allowed commands to an allowlisted prefix set (`grep -c`,
`wc -l`, `git log … | wc -l`, a named script) so the gate is not an arbitrary
executor.

*Controls*: positive — a marker whose number is stale must fail, naming the file
and both numbers. **False-positive case** — a marker inside a fenced code block
illustrating the syntax (as in this very document) must NOT be executed;
otherwise the gate red-lines its own documentation. Mutation: remove the fenced-
block skip and exactly that control dies.

**Cost.** ~200 lines; the marker parser can be lifted wholesale from
`check-absence-claims.py`.

**How you'd know.** The count of quantified claims in `CLAUDE.md` and
`docs/research/11-design-review/` that carry a marker, versus those that do not.
It should start small and grow; a claim without a marker is one nobody has to
re-derive, and that is exactly the class that goes stale.

---

## Part 2 — What to remove or simplify

### R5. Retire the one-shot capsule checkers. There are 352 of them.

**Measured.** Of 503 `scripts/check-*.{sh,py}`:

| classification | count |
| --- | --- |
| referenced by a gate, script, CI workflow, or hook | 150 |
| referenced only by a fact-ledger `checker_command` | 1 |
| referenced only by a doc | 75 |
| **referenced nowhere at all** | **277** |

Widening "nowhere" to also exclude doc-only mentions gives **352**. Positive
control: `check-aggregate-scope.sh` is correctly classified as referenced.
Negative control: a fabricated name (`check-zzz-nonexistent.sh`) appears in no
corpus, so the containment test discriminates.

**The dates are the finding.** The last-commit histogram of the 352:

```
2026-07-20   1      2026-08-20  10      2026-08-26  2
2026-08-15   1      2026-08-21 180      2026-08-28  2
2026-08-19   2      2026-08-22 154
```

**334 of 352 were written on two days** — the autogenesis capsule era — and
essentially nothing since. They are archaeology.

**And 93 of them have a control in `scripts/tests/` that runs on EVERY
aggregate-gate run**, via the derived catch-all in `run-python-controls.py`. So
the gate spends time controlling scripts nobody runs. 248 of the 352 have no
control at all.

**Change.** Move the 352 to `scripts/archive/` (git history preserves them
regardless), and move the 93 orphan-subject controls with them. Then add the
symmetric half of `check-control-registration.sh`: that gate asserts every
*control* has a caller; nothing asserts a *subject* does. A new
`check-*.py` that no gate, fact, or script names should be red, or explicitly
marked one-shot.

**The judgement call, stated so you can overrule it.** A capsule audit
legitimately runs once. Registering all 352 in `check.sh` would be absurd. The
cost they impose is not gate time — it is **retrieval**: `scripts/` holds 797 `.sh`/`.py` files,
503 of them `check-*`, and 70% of those are dead. Retrieval is the binding
constraint on marginal cost per theorem by this repository's own cost model, and
`scripts/` is one of the namespaces lanes search.

**Cost.** One `git mv` batch, one gate.

**How you'd know.** `ls scripts/check-* | wc -l` drops from 503 to ~150. Then
the number that matters: the fraction of `check-*` scripts with a live caller
goes from 30% to ~100% and stays there.

### R6. Do NOT reintroduce a pin counter anywhere, and finish removing the last 10

`creal_tests.rs` deleted its pin and the reasoning in `CLAUDE.md` is right: the
pin answered "is this list internally consistent", never "is it complete", and
the environment-derived assertion answers the question that matters. That
reasoning applies verbatim to the 10 surviving `assert_eq!(…len(), N)` pins
(`rat_prelude_tests.rs` ×3, `creal_model_tests.rs` ×2, `inductive_tests.rs` ×3,
`creal_tests.rs:2563`, `arith_model_tests.rs`).

**But those 10 are cheap and low-traffic — the pin is not the problem.** The
`nat_prelude` situation proves it: the pin is already gone and the file still
took 100 commits, because the *shared append point* survived the pin's deletion.
Deleting a pin without sharding the list is half a fix. Do the sharding
(§R7) and let the remaining pins be.

### R7. Shard `nat_prelude` the way `creal` was sharded — including the dispatcher

**Problem.** §0.1. Two files at 100 commits each, 15,835 and 4,788 lines, edited
by ~12 lanes concurrently. This is exactly the pre-sharding `creal` state.

**Change.** Two moves, and the second is the one `creal` did *not* get:

1. `nat_prelude/inventory/<module>.rs`, one `Vec` per `nat_prelude/` source
   module, registered from `nat_prelude/inventory.rs`. Mirrors
   `creal/inventory/` exactly, including the no-pin rule and the
   "no declaration claimed by two shards" assertion that only a sharded shape
   can have.
2. **Split `nat_prelude.rs`'s 667-field struct and 395 linear `declare_*`
   calls** the same way. The 2026-08-27 architecture review names this fusion as
   the cause of recurring phase-order bugs and helper duplication in `creal.rs`;
   `nat_prelude.rs` has more of both and has never been touched.

**Cost.** Real — this is a multi-lane refactor and it must be done when the
preludes are quiet, or it will itself be the biggest conflict of the day.

**How you'd know.** Distinct lanes per file per day (the R3 metric) for
`nat_prelude.rs` drops below the threshold. Secondary: the count of
"recount the pin from a panic message" events goes to zero — the brief reports
that as happening at every merge.

---

## Part 3 — Briefing and dispatch

### The preamble is not earning its length, and the data says which parts do

269 status docs, 26,360 words of them, median 596 words. Scanning all 269 for
the practices the standing preamble teaches:

| practice | status docs mentioning it | mechanized? |
| --- | --- | --- |
| mutation testing | **125 (46%)** | yes — `mutation_controls.py` + `check-control-registration.sh` |
| ran a cargo gate | 97 (36%) | partly — `hooks/pre-push` |
| "already exists" / step 0 | 69 (25%) | no |
| negative control | 49 (18%) | partly — per-gate convention |
| reported a check as not run | 53 (19%) | no |
| pin / recount | 31 (11%) | yes — `recount-pinned-inventory.py` |
| **`shape_search`** | **13 (4.8%)** | **no** |
| stall / waiting | 8 (3%) | no |
| simulate in Python first | 6 (2%) | no |
| `debug_probe` | 3 (1%) | no |

**Compliance tracks mechanization, not emphasis.** Mutation testing is at 46%
because there is a harness and a gate that notices. `shape_search` is at 4.8%
despite retrieval being named, in this repository's own cost model, as the
binding constraint on marginal cost per theorem — because nothing but prose
points at it.

Three consequences for how you brief:

**R8. Move retrieval out of the lane and into the brief.** `shape_search` costs
13–21 s and the lane must remember to run it, know which of two spellings to
use, and know it must be freshly built. The dispatcher already has the fact's
`formal.statement`. Build `scripts/brief-step0.py <fact-id>`: run `shape_search`
against the statement's conclusion and hypothesis heads, plus
`ls crates/axeyum-lean-kernel/src/*/<topic>.rs` for the duplicate-basename trap
(§0.3 — 10 shared basenames between nat and int alone), and emit a
**"candidates already in the environment"** block to paste into the brief.

Compliance then goes to 100% by construction, because the lane does nothing.
Cost: a wrapper, ~100 lines. Signal it worked: the 25% of status docs reporting
"already exists" should *rise* first (lanes finding things earlier) and then the
re-derivation tally — 13+ recorded instances and climbing — should stop growing.

**R9. Cut the preamble to the parts a lane can act on in its first five tool
calls, and move the rest behind a pointer.** The 2,000-word preamble competes
with the task for attention, and the 4.8% figure is what losing that competition
looks like. Keep: lane identity, worktree isolation, the early-commit rule,
"a check that did not finish is 'did not run'", and the specific bounded
commands. Move to a linked page: the incident histories, the multi-carrier
helper taxonomy, the shell traps. `CLAUDE.md` already holds all of it and lanes
read it.

The evidence that the *long* parts are not read: the stall retrospectives in
`CLAUDE.md` document eleven stalls, five of them by lanes whose brief contained
the prohibition **in bold**, one of which enumerated the forbidden mechanisms
and was defeated by a mechanism not on the list. The eleventh entry reaches the
right conclusion — *stop trying to prevent the stall and make it cheap* — and
that conclusion generalizes past stalls to the whole preamble.

**R10. Number status docs per-lane, not sequentially.** 9 collisions already,
`141` four times. `docs/plan/status/<lane>.md` (the named ones) never collide;
the numbered ones do, for the reason this repository has documented five times.
Rename to `<date>-<lane>.md`. Cost: a `git mv` and a `gen-plan.py` glob change.
Signal: collisions go to zero, which is checkable in one `uniq -d`.

Also worth noting rather than acting on: only **52 of 269** status docs are
referenced from `PLAN.md` — and the most recent ones are not among them
(`docs/plan/status/299-…` appears zero times; positive control: 49 other
numbered docs do appear). The other 217 (~21,000 words) are write-only. That
may be correct — they are per-lane retrospectives and the archive has value —
but it should be a decision, not an accident, and it is a large fraction of what
every lane spends its last tokens on.

---

## Part 4 — The measurement question

`CLAUDE.md` says the metric is the trusted base and results nobody wrote by
hand — not output volume. That is the right choice and the trusted-base half is
in good shape: it is read from `Kernel::axiom_footprint`, the environment-derived
inventories fail on absence, and every prelude but `axreal` measures 0.

**The queue half has drifted, and the sibling's "mirrors closed is blind to
local facts" finding is the small end of it.** Measured over all 2,114 facts:

| | count |
| --- | --- |
| `proved` | 1,945 |
| `open` | **160** |
| `refuted` / `computed` / `conjectured` | 9 |
| of the 160 open, `ml430` mirrors | **155** |
| of the 160 open, **not** mirrors | **5** |

Three of those 5 are `F:godel-first-incompleteness`,
`F:continuum-hypothesis-independent`, `F:fol-validity-undecidable` — open by
mathematical necessity, not by queue position.

So: **the non-mirror open frontier is two facts.** The ledger is a record of
what has been proved, and the only thing feeding its queue is mirror import.
That is not a crisis — mirrors are a legitimate target — but it means "open
facts remaining" measures import rate, not capability, and a metric that reads
as a frontier is measuring a backlog.

**And the ledger has no vocabulary for "we looked and decided not to."** Of the
160 open facts, exactly **3** record a blocker anywhere in their notes, and all
3 are the undecidability results. Zero record a decline. Declines *do* exist —
`artifacts/autogenesis/` carries `-decline.py` records and decline JSON — but
they connect to no fact, so a lane that correctly determines a mirror is
unclosable (the `multichoose` case in `CLAUDE.md`, the `Int.gcd_eq_gcd_ab`
existential-vs-computable case in the 2026-08-28 frontier review) produces work
that is invisible to every fact-level count. It reads identically to a lane that
did nothing.

**R-M (the measurement recommendation).** Add a `disposition` axis to the fact
schema, orthogonal to `epistemic_status`, with values:

* `queued` — nobody has looked
* `declined` + `superseded_by: [F:…]` + a reason — we looked, it is not the
  proposition we can honestly close, and here is what we landed instead
* `undecidable-in-principle` — Gödel, CH, FOL validity
* `blocked_on: [F:…]` — a real prerequisite

`validate-facts.py` already enforces semantic rules in both directions and is
the natural place for it: a `declined` fact must name a `superseded_by` that
exists and is `proved`; a `superseded_by` target must not itself be `open`.
Then "open frontier" means queued-and-attemptable, the decline census the ledger
already produces becomes a *positive* output rather than a status quo, and the
mirror-closure counter can report closed / graded-family / declined / queued
instead of a single number that reads as failure for three different reasons.

Cost: a schema field, ~40 lines of validator, and a backfill pass over the 155
open mirrors that were touched by a lane and left open.

How you'd know: the count of open facts that have been *looked at* and carry no
record of it goes from (unknown, and unknowable today) to zero.

---

## Appendix: things checked that turned out fine

Stated because "I checked and it was fine" is worth as much as a finding, and
this document would otherwise imply everything is broken.

* **Control registration is healthy and derived, not remembered.**
  `check-control-registration.sh` → `controls=26 orphans=0 py_controls=387
  py_orphans=0 py_optout=18 py_optout_ceiling=18`. The python half runs every
  `scripts/tests/test_*.py` no caller names, so a new control runs the moment it
  is committed. This is the mechanism §R5 asks to be mirrored on the subject
  side, and it works.
* **`validate-facts.py` and `gen-plan.py --check` are green**, and the fact
  validator reports 3,313 evidence rows re-derived by 2+ independent checkers.
* **`check-absence-claims.py` (ADR-0611) is the right shape** and should be the
  template for §R4 rather than a new mechanism.

## Appendix: gates found red while measuring, not fixed here

In the 1-in-5 sample, 9 steps exited nonzero and 6 hit this lane's 60 s cap
(neither pass nor fail — the DEFERRED distinction §R1 exists for). Extrapolating
the failures gives ~45 across the full gate, against the brief's 16 — the
difference is not reconciled here, and some of the 9 may be environment-specific
to a fresh lane worktree. Three that are definitely real and definitely not
environment:

1. `scripts/check-local-ci-freshness.sh` — 265 h stale (§0.2).
2. `scripts/check-mobility-census.py` — **126 violations, every one of the form
   "`F:…` is proved in the ledger; the census is over OPEN facts".** This is a
   second instance of the brief's "broken by design" gate: a census pinned to a
   snapshot of the open frontier goes red the moment anything is proved. **A gate
   whose failure is caused by success.** Worth naming as a class —
   *never pin a gate to a snapshot of a moving frontier; derive the frontier at
   run time.*
3. `scripts/check-aggregate-scope.sh` — 11 unrecorded divergences between
   `check.sh` and `just check`, including one that is a bare `./` prefix
   mismatch on the same script (`./scripts/check-test-attribute-integrity.py`
   vs `scripts/check-test-attribute-integrity.py`) and 8 `uv run` steps from the
   python layer. Verified that the step added by this lane is **not** among them.
