# Notes: 315-attestation-ceiling

Detail moved out of [`../status/315-attestation-ceiling.md`](../status/315-attestation-ceiling.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**On the statement: yes, and better-evidenced.** Measured, because
`nursery-v1.json` carries **no `surface_validation` key at all** -- the record
is in its source catalog, `mathlib-nat-int-fact-catalog-v1.json`:

```
method           declare every formal.statement as an axiom after import Mathlib;
                 no theorem value or proof is read
observed_result  accepted-214-proof-free-axiom-types
expected_sha256  a4f51828c0b70709aeef3429400d8fac90f80d5d3164bd8259b1b5fd1fd5995d
external_file    /nas3/.../mathlib-v4.30.0-nat-int-nursery-surface-v1.lean
```

That file is still on disk and still intact:

| check | result |
| --- | --- |
| `sha256sum` | `a4f51828...` -- **matches** `expected_sha256` |
| `/usr/bin/grep -c '^axiom '` | **214**, one per evaluation entry |
| `/usr/bin/grep -c 'negative_control\|DoesNotExist'` | **0** |

`attest-nursery-surface.py` runs that method verbatim. **And v1's run has no
negative control**, so `accepted-214` cannot distinguish "Lean accepted 214"
from "the harness could not see errors" -- which is not hypothetical: lane 305's
first run of the new harness reported a clean 4 of 4 because its regex demanded
a bare `error:` while Lean 4.30 emits `error(lean.unknownIdentifier):`, and only
the negative control caught it. The extension's attestation is per row, with a
control that must be REJECTED or the run fails. So it carries strictly more
evidence than the cohort the ceiling is sized against.

## What still differs -- and it is the ROW, not the statement

`nursery-v1.json`'s `policy`:

```
split_component_authority          declared-dependency-weak-component
split_leakage                      no-declared-component-may-cross-evaluation-partitions
minimum_declared_dependency_depth  2
```

v1 entries' `source_group` values are hashed components
(`mathlib-v4.30.0-b064fa21f15a772b`, ...). The extension's are Mathlib module
paths (`Init.Data.Nat.Mod`, `Mathlib.Data.Nat.Totient`, ...), and no
dependency-component analysis was run. **Two theorems in different modules can
sit in one dependency component**, so a held-out row here can be entailed by a
train row here and nothing in this manifest sees it.

That is the brief's question answered: *same grade of statement, not the same
grade of row.* It decides the shape of the change -- promote on the attestation
axis, state the component gap in its own right, and pin it with a control that
runs against a **fully attested** cohort so it cannot be laundered later.

**The old limitations text was stale in a second way too.** It said "depends_on
is empty"; 96 of 200 extension facts now carry edges (and 125 of v1's 214).
Those are ledger-owned and accrued after the fact -- ADR-0615 item 3 makes
`depends_on` mutable -- never the preregistration-time analysis the sentence was
about. The replacement says so.

## The decision: ADR-0616

**Three changes; raising a number is still not one of them.**

1. **R3 compares by attestation.** `attested_cohort` = v1's 214 + the
   extension's accepted rows; `unattested_cohort` = every extension row without
   an accepted round trip. `EXTENSION_CEILING` is **deleted** rather than
   re-pointed -- a constant that no longer names what it bounds is the next
   lane's wrong assumption.
2. **`not_elaborable` counts as UNATTESTED.** Lean refused those strings, so
   they are worse than unchecked and must never buy headroom. All three rows the
   brief names stay counted against.
3. **`limitations` is derived from the run.** Same reason the grade itself was
   made derived one ADR earlier: a literal cannot degrade, and a file asserting
   both a 197-row `attested` list and "these carry the quotation grade" is worse
   than one asserting only the weaker claim.

Plus one guard the change makes necessary: **an ingested attestation record must
name the pinned Mathlib commit.** Recording `mathlib_commit` was descriptive;
now that an accepted row buys headroom, a run against another commit would grade
statements against a library they were not quoted from.

Alternatives rejected in the ADR, with reasons: raising to 400 (a dial, not a
rule -- exactly what ADR-0615 refused); comparing against `V1_EVALUATION_ENTRIES`
alone (tighter at 214, but reintroduces a frozen literal that tracks nothing);
requiring every row attested before a draw (unimplementable -- a draw's own rows
are unattested at emission); counting `not_elaborable` as attested.

## Is the new bound loose enough to be no bound?

**Headroom 14 -> 408, and it is not a removal.** A draw's rows land in
`unattested` by construction (`surface_validation` puts any id no run covered
there), so the guard still binds on a draw and is still cleared only by running
Lean against the pinned Mathlib -- the cadence ADR-0615 asked for, at 4 seconds
a run. It is also not what gates a draw: draw 4 measured held-out-safe **family**
supply as essentially exhausted and had to combine four below-floor modules for
two held-out slots. R5 and R9 bind; the row ceiling binding at 200 was an
artifact of counting the wrong thing.

Recorded in the ADR's *Consequences* as the thing to watch: if row count ever
becomes binding again rather than held-out adjacency, the rule may need a
cadence term as well as a ratio.

## Checks (all foreground, each run bare -- never after a pipe)

| check | result |
| --- | --- |
| `gen-autogenesis-nursery-refill.py --check` | exit 0, `entries=200\|combined=414\|attested=411\|unattested=3` |
| `check-dispatchable-frontier.py` | exit 0, DISPATCHABLE 8 |
| `check-mirror-statement-fidelity.py` | exit 0, `violations=0`, **PASS** |
| `validate-facts.py` | exit 0 |
| `check-control-registration.sh` | exit 0, `controls=27\|orphans=0\|py_orphans=0`, `py_named` 194 -> **195** |
| `scripts/tests/test_gen_autogenesis_nursery_refill.py` | **30/30** (was 22) |
| `scripts/tests/test-dispatchable-frontier.sh` | exit 0 |
| `mutation_controls.py nursery-refill-ceiling` | **7/7 killed**, 5 by exactly one |
| `mutation_controls.py --check-anchors` | `suites=36\|anchors=414\|stale=0` |
| `gen-adr-index.py` / `--check` | `rows=610`, green |
| `gen-plan.py --check` | exit 0 |
| `bash -n scripts/check.sh` | exit 0 |
| `check-autogenesis-holdout-isolation.py` | **FAIL, and PRE-EXISTING -- see below** |
| workspace cargo gate | **not run** -- no `crates/` file touched |

**The mutation run corrected me once, and it is the useful part.** The mutant
that reverts the promotion -- `attested_cohort` returning v1's 214 alone --
**SURVIVED** the first attempt. My promotion case was 215 rows with 1 attested:
214 unattested against 215 attested, which passes *and also passes* with the
extension's attested rows dropped (214 vs 214). The test asserted the rule as I
imagined it, not as it differs from the old one. Resized against the arithmetic
(218 rows / 2 attested for the promotion, 219 / 2 / 1 for the refused-row case),
each mutant is now killed by its own case. A second mutant was also too narrow:
it replaced only the first line of a multi-line implicit concatenation, leaving
the phrase the assertion looked for intact.

Two mutants kill two tests each, and in both the second is
`test_the_committed_manifest_does_not_contradict_its_own_grade`, which asserts
the committed `limitations` equals the recomputed one. That is a byte-equality
reproduction check and dies under any `limitations` mutation by construction --
a broad detector by design, with the specific behaviour pinned by its own case
each time.

Mutation ran through `scripts/tests/mutation_controls.py`, which `copytree`s to
a scratch root and `py_compile`s each target; no tracked source was mutated and
no hand loop was used.

## Found and NOT repaired here

**`check-autogenesis-holdout-isolation.py` is RED on `main`, and the brief said
it must stay PASS.** It was already red when I merged. Verified rather than
argued: a detached worktree at `main` produces byte-identical output.

```
AUTOGENESIS_HOLDOUT_ISOLATION|held_out=127|files_scanned=1105|settled=10|references=0|verdict=FAIL
    (my branch, and identical at main)
```

Ten held-out rows are `proved`: four `natural-divisibility` `dvd` rows, two
`natural-logarithm` `log`, two `clog`, `log_le_self`, `log_of_lt`. They were
flipped by **`92a61164e` "facts: close 21 already-proved ml430 mirrors found via
brief-step0"**, on `main` and not this lane's. My two commits touch **zero** fact
files (`git diff --name-only main...HEAD` is four files: the manifest, two
scripts, this document), and `held_out` and `references` are unchanged.

**Not repaired here, deliberately.** The repair is an ADR-0542 amendment with a
recorded breach in `mathlib-nursery-split-policy-v1.json` -- a decision about
which populations are still blind, owed to whoever owns partition repairs.
Making it as a side effect of a ceiling change would bury it. This is the same
`natural-divisibility` debt ADR-0615 already recorded as owed, now larger by six
`natural-logarithm` rows, and **127 is now an overstatement of blind breadth by
up to ten rows**.

## Registered

`gen-autogenesis-nursery-refill.py --check` and its suite are now steps in
**both** `scripts/check.sh` (`autogenesis-nursery-refill-tests`,
`autogenesis-nursery-refill`) and the `justfile`'s `autogenesis-nursery` recipe.
ADR-0615 recorded this as owed once the `F:ml430-nat-totient-eq-zero-3be161d6`
statement drift was resolved; it is, and it is green. ADR-0616 makes it
load-bearing rather than merely reproducible: R3 now reads `surface_validation`,
so a hand-edit there changes what the ceiling permits and this is what
re-derives it.

The mutation suite `nursery-refill-ceiling` needed no new registration -- it
extends `mutation_controls.py`, already wired into both gates and covered by
`--check-anchors`.

## Next

1. **The held-out amendment, now ten rows across two families.** Until it lands,
   `held_out=127` overstates blind breadth and the gate is red for everyone.
2. **Attest before dispatching against any new draw**, not after. Draw 4 found
   two unclosable `integer-absolute-value` rows only because it attested; a draw
   that skips it preregisters rows that cannot be closed as stated, and now also
   forfeits the headroom the run would have bought.
3. **No screen exists for the coercion-notation failure class** (a statement
   needing Mathlib's enclosing `variable` block). Unlike the glyph case it is
   not a regex, and it is now the only remaining route by which a row enters at
   full ceiling cost and can never be closed.
