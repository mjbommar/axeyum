# ADR-1455: The nursery split-exemption mechanism gets the two guards its own safety argument always assumed

Status: accepted
Date: 2026-09-01
Index-summary: Re-scopes the two nursery-v1 split exemptions a `depends_on`
repair voided, and enforces the two properties ADR-0850 argued for but never
checked -- no exemption may name a held-out row, and a recorded exemption that
matches no live crossing component fails the gate

## Context

Four gates were red on `main` at `b558d9b5a`. This ADR covers the two that are
the same defect: `scripts/check-autogenesis-nursery.py` (exit 1) and
`scripts/tests/test_check_autogenesis_nursery.py` (exit 1, the same violation
through the module's live-manifest test).

Re-measured in this lane rather than relayed. Two declared-dependency
components crossed evaluation partitions unexempted:

    component=eebbcd53cea2… partitions=['development', 'train']       2 members
    component=f888609d9f17… partitions=['development','longitudinal','train'] 11 members

### The edges are right, and the `--fix` runs did widen the leak

`check-fact-depends-derived.py` derives `depends_on` from
`Kernel::theorem_dependencies` -- the proof term, not prose -- so an edge it
adds is a real dependency. Both new crossings come from edges of that kind:

* `F:ml430-nat-factorial-dvd-ascfactorial` -> `F:ml430-nat-ascfactorial-zero`
  is `factorial_dvd_ascFactorial`'s use of `Nat.ascFactorial_zero`. The ledger
  carries **two** facts for that theorem (the native `F:nat-asc-factorial-zero`,
  already declared at the 2026-08-18 freeze, and this `ml430` mirror, which was
  not), so the derived rule demands both edges.
* `F:ml430-nat-descfactorial-one` -> `F:nat-mul-one` is `descfactorial_one`'s
  use of `Nat.mul_one`.

Reconstructing the component structure at three refs (the nursery entries and
each ref's own fact ledger, read through `git show`) measures the widening
exactly:

| ref | intra-nursery edges | crossing components |
| --- | --- | --- |
| `237c1abdd^` (before the 1,054-edge repair) | 81 | 1 |
| `366f11a91^` (after it, before the 196-edge repair) | 108 | 3 |
| `b558d9b5a` (HEAD) | 113 | 4 |

So yes: the `--fix` runs widened it, twice. `237c1abdd` (2026-08-29) took it
from 1 to 3 and ADR-0850 adjudicated those three. `366f11a91` (2026-08-31) --
which set `formal.kernel_theorem` on 28 facts and thereby unlocked
`check-fact-depends-derived.py --fix` for them, adding 196 edges across 54
facts -- added **five** intra-nursery edges, two of which created the reds
above: one new 2-member component, and one member added to an
already-exempted 10-member component.

### What that means for the remedy

Of the three honest options -- the edges are wrong, the partition assignment is
wrong, or the check is over-strict -- **none applies**. The edges are
proof-derived and removing either would make `check-fact-depends-derived.py`
red. The partitions are a preregistered frozen split, and ADR-0850 already
rejected moving rows for exactly this class (no held-out involvement, nothing
"spent" for an ADR-0542 amendment to record, and no principled correct
partition to move to). And the check is not over-strict: it did precisely what
ADR-0850 designed it to do -- the enlarged component's digest stopped matching
its exemption, so the gate went red on an unreviewed component.

This is the mechanism's designed use, and the ADR-0850 text says so: *"If any
of these three components later grows … the exemption stops matching
automatically and the gate reports the ENLARGED crossing in full,
unexempted."* The required action is a re-review, which is this document.

### Independent verification, and where it DIFFERS from ADR-0850

Checked directly against `artifacts/facts/*.json`,
`artifacts/autogenesis/nursery-v1.json` and
`artifacts/autogenesis/operations.json` (29 operations), for the 13 facts in
the two uncovered components:

* **Zero held-out members.** Both components' partition sets are subsets of
  `{train, development, longitudinal}`.
* **All 13 `epistemic_status: proved`,** by ordinary hand development.
* **Autogenesis operations DO reference two of them**, which is where the
  evidence departs from ADR-0850's "0 of 29 operations reference any of the
  18". `F:ml430-nat-ascfactorial-zero` and `F:ml430-nat-descfactorial-one` are
  named by `authoritative-mathlib-bounded-induction-factorial-family-v1` (and
  the first also by `authoritative-mathlib-statement-reflexivity-v1`).

  That operation is **train-only** over the nursery -- all four fact ids it
  names are `train` -- and neither component's development member
  (`F:ml430-nat-factorial-dvd-ascfactorial`, `F:ml430-nat-mod-lcm`) is named by
  any operation at all. So nothing has spent a development row; a train row
  being used by a producer is what train is for. The claim is weaker than
  ADR-0850's and it is the one the evidence supports, so it is the one the
  exemption reasons state.

Measured incidentally and worth recording rather than fixing here: two
operations (`authoritative-mathlib-modeq-family-v1`,
`authoritative-mathlib-nat-modeq-congruence-family-v1`) name fact ids in
**both** train and development, and no gate measures that. Neither touches
held-out. This is the same open question ADR-0850 flagged for a decision above
a single lane's level -- whether train/development need their own
spent-by-ordinary-development tracking analogous to ADR-0542's held-out one --
now with a second, independent instance.

### The two guards that were never written

Diagnosing the above surfaced two properties that **every producer respects and
no checker tested**. This is the failure class CLAUDE.md describes as the one
mutation testing structurally cannot find: a guard that was never written has
nothing to delete, so a suite in which every existing guard is killed by
exactly one test says nothing about it.

1. **`validate_exemptions` accepted an exemption naming a `held-out` row.**
   ADR-0850's entire safety argument is "no held-out member"; every recorded
   reason asserts it; `rescope-nursery-exemption.py` exits 2 rather than write
   one. The gate itself would have accepted a hand-written exemption
   suppressing a train/held-out crossing, with a plausible reason string, and
   gone green. The existing test suite did not merely miss this -- two of its
   exemption tests *demonstrated* it, exempting a `train`/`held-out` pair to
   show the mechanism works.

2. **A recorded exemption matching no live crossing component was a `--json`
   field, not a failure.** `component_split_exemptions_unused` was computed and
   reported and never affected exit status. So when the factorial component
   grew from 10 to 11, the operator saw "component crosses evaluation
   partitions" and *nothing at all* about the reviewed decision that had just
   been voided -- which is the single piece of information that distinguishes a
   re-review from a new finding. The same had happened on the cross-population
   side, where the committed exemption pins 258 members against a live 274.

### A third defect, found while fixing the second

`scripts/rescope-nursery-exemption.py` is the tool that re-scopes the
cross-population exemption, and it had **no tests**. Its parser was one regex
over the gate's combined stdout+stderr:

    rows = re.findall(r"^\s+(F:[^\s]+)\s+->\s+(\S+)", text, re.M)

The gate validates nursery-v1 **first** and raises before the cross-population
report runs, so with v1 red that regex returns V1 fact ids. Measured
2026-09-01 against the live tree: it returned the **13 members of the two V1
components**, which `main()` would have written over the 258-member
cross-population exemption -- destroying the membership list and the reason
recording why that crossing was judged benign. It is fail-closed afterwards
(the digest matches nothing), and it prints a confident
`RESCOPE|258 -> 13 members` and exits 0 on the way there. The same regex also
unions two reported components into one list, inventing a component that
exists nowhere.

## Decision

Four changes, none of which relaxes anything.

1. **Re-scope the two crossings** in `artifacts/autogenesis/nursery-v1.json`.
   The stale 10-member factorial exemption is replaced by the live 11-member
   one, with a reason that names the growth, the edge that caused it, and the
   superseded digest; a new 2-member entry covers the ascFactorial crossing.
   Both carry the partition census and the operations finding above. No
   partition is moved, no `depends_on` edge is touched, no
   `epistemic_status` changes.

2. **`validate_exemptions` refuses any exemption naming a `held-out` row**, on
   both the v1 and cross-population paths, before any other per-entry check.
   Held-out blindness, once spent, cannot be un-spent; a crossing reaching the
   blind population is a finding and, if it needs repair, an ADR-0542
   amendment -- never a suppression.

3. **A recorded exemption matching no live crossing component fails the gate**,
   rendered by a new `describe_stale_exemptions` that names the voided
   entry, its membership, its date and its authority. A grown component now
   reports both the enlarged crossing and the void adjudication in one
   message. `component_split_exemptions_unused` remains in the JSON report.

4. **`rescope-nursery-exemption.py` attributes members per component** and
   refuses -- exit 2, distinct from success -- when it cannot attribute the
   gate's output to exactly one cross-population component. A `Refused`
   exception carries that through `main()`, because signalling refusal by
   returning an empty member list would have hit `if not members: return 0`
   and exited 0.

### Controls

Every guard is mutation-verified through `scripts/tests/mutation_controls.py`,
which copies to a scratch tree (a hand-rolled loop would report the previous
mutant's result: equal-size mutants written inside one second share a bytecode
cache entry). Two new suites, both registered in `check.sh` and the `justfile`:

    nursery-split-exemption-guards: baseline green, 10 tests
      held-out row refused, both report paths     killed 2
      v1 exemption matching no live crossing      killed 2
      cross-population ditto                      killed 1

    nursery-rescope-parser: baseline green, 8 tests
      members attributed only to a cross-population component   killed 1
      two components refused rather than unioned                killed 1

The rescope guards are deliberately measured on **disjoint** cases: counting
components cannot catch a v1 error reporting exactly one component, and the
header check cannot catch two genuine cross-population components, so each
mutation kills its own test and leaves the other's alive.

Every negative case is paired with a positive control on the same code path --
an exemption over train/development that must still be accepted, a population
that must still pass once the stale entry is dropped, a clean gate run that
must still parse as "nothing to re-scope". Without those, a guard that refused
everything would satisfy the negative cases alone.

Note the two existing exemption tests that were retargeted from `held-out` to
`development`. Their purpose is "an exemption suppresses exactly the named
component", which is preserved; the held-out case they used as a vehicle is now
covered by a test asserting it is **refused**, which is strictly more coverage
than before. This is a deliberate semantic change, not a test relaxed because
it fired.

The guard controls live in a new `test_nursery_exemption_guards.py` rather than
beside their siblings for a mechanical reason: `mutation_controls.py` refuses a
suite whose baseline is not green, and `test_check_autogenesis_nursery.py`'s
`LiveManifestTests` reads the committed `nursery-v2-extension.json`, which is
red for the reason below. Registering the fuller module would have printed
`BASELINE IS NOT GREEN` and measured nothing.

## What is deliberately left red

`check-autogenesis-nursery.py` still exits 1 after this change, and it is
honest that it does. Its **cross-population** half -- the v1-union-v2 report --
is red because that union's 274-member component outgrew the 258-member
exemption recorded in `artifacts/autogenesis/nursery-v2-extension.json`, a file
a concurrent lane owns and is actively editing to author a nursery draw. This
red is pre-existing at `b558d9b5a` (that commit is itself the manifest
regeneration that grew the component), was masked by the v1 failure raising
first, and is now the only thing left.

Re-scoping it here would be worse than useless: the concurrent draw changes the
component again, so any re-scope now is stale on arrival, and editing that file
concurrently is the shared-append-point hazard this repository has recorded a
dozen incidents for. The fix is one command by that file's owner, **after** the
draw lands:

    python3 scripts/rescope-nursery-exemption.py

which is now safe to run -- before change 4 above it would have overwritten
that exemption with nursery-v1 fact ids.

Verified in this lane: with v1 green, that command correctly reports
`RESCOPE|258 -> 274 members|census={'development': 314, 'train': 230,
'longitudinal': 4}|held_out=0` and the union's three crossing components carry
zero held-out members. The write was reverted; this lane commits no change to
that file.

## Alternatives

- **Remove the `ml430`-mirror edges** so the components never form. Rejected:
  the edges are proof-derived, `check-fact-depends-derived.py` would go red,
  and suppressing a real dependency to satisfy a partition gate is the
  inversion this whole mechanism exists to prevent.
- **Move the minority-partition rows** (an ADR-0542 amendment). Rejected for
  ADR-0850's reasons, which still hold: no held-out member, no spend to record,
  and no principled target partition -- the crossing exists because one real
  component spans a boundary drawn before the dependency was known.
- **Bump the exemption to 11 members in place, without a new record.**
  Rejected: the growth is the finding. An amendment that leaves no trace of
  what the previous adjudication covered turns a self-invalidating mechanism
  into a rubber stamp, which is the failure mode this ADR is otherwise fixing.
- **Leave the stale-exemption check as a JSON control.** Rejected: it had been
  a JSON control through two separate stalings, and in neither case did anyone
  notice. A signal nobody reads is not a signal.
- **Also re-scope the v2 exemption here** to make the gate green in one commit.
  Rejected: see above -- immediately stale, and a concurrent write to a file
  another lane owns.

## Consequences

- The v1 half of `check-autogenesis-nursery.py` is green, with all four
  crossings named, reviewed, and reported in full.
- An exemption can no longer cover a held-out row, on any path, by any route.
- A voided adjudication now fails loudly and names itself, instead of being a
  field in output nobody prints.
- `rescope-nursery-exemption.py` has tests, and cannot silently overwrite one
  population's exemption with another population's fact ids.
- The gate stays red until the v2 cross-population exemption is re-scoped by
  its owner. That is one command and it is now safe.
- The train/development spend question is open, with a second instance
  recorded. Unchanged by this ADR.
