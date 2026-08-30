# Notes: 292-nursery-refill-two

Detail moved out of [`../status/292-nursery-refill-two.md`](../status/292-nursery-refill-two.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Working the cycle: with `N` new families, indices `0..N-1 mod 3` land on
`held-out` at positions `0, 3, 6, ...`. Two held-out families need indices `0`
and `3` both to exist, i.e. **`N >= 4` families minimum** -- and `4 * 10 = 40`
rows is the smallest input that can pass R3+R5+R4 together (4 families:
held-out, development, train, held-out -- 20 held-out, 10 development, 10
train, so R4's "something dispatchable" and R5's "2 new held-out families" are
both satisfied at the same time for the first time).

**40 rows is the floor for a rule-compliant refill through the existing
generator. The ceiling headroom is 6.** A "refill" that adds fewer rows than
the generator's own leakage/breadth rules require is not a refill in the
sense those rules define -- it would either violate R5 (no held-out breadth
restored) or, if it tried to add a single non-held-out family alone, would not
even reach `PER_FAMILY = 10` without ALSO adding whatever partition the cycle
assigns next, which for a lone new family is `held-out` (index 0) again.

**Conclusion: no meaningful draw is possible within the current 300-entry
ceiling using the existing family-based methodology.** This lane did not
preregister anything. Preregistering 6 rows to make a counter move would
either violate R5 (if all 6 are non-held-out, added by hand-editing the
generator's own refusal, which is exactly the kind of unilateral rule-bending
CLAUDE.md and this brief forbid) or spend the ceiling on partial held-out
families that test nothing new.

### What should change (a decision for the humans/coordinators, not this lane)

- **Raise `EVALUATION_CEILING`.** The generator's own minimum viable refill
  is 40 rows, so a ceiling raise needs to clear at least `214 + 80 + 40 = 334`
  to make a third refill possible later too; something like 400-450 gives
  two more refills of this shape before the question recurs. This is a
  recorded-decision change (the ceiling exists on purpose, per the brief), not
  a lane's unilateral edit -- flagging it here for whoever owns that call.
- **Alternatively, loosen `PER_FAMILY`** for a family whose candidate pool is
  naturally small, or allow a refill to extend an EXISTING dispatchable-eligible
  family (`natural-totient`, `natural-division`, ...) rather than only adding
  brand-new families -- this sidesteps R5's "2 NEW held-out families" rule
  (extending an existing train/development family adds no held-out obligation)
  and could fit inside 6 rows. That is also a rule change, not something this
  lane did unilaterally.
- **Shrink `PER_FAMILY` from 10** for future refills once each family's
  candidate pool and the review cost of extra work per proof shape are
  weighed -- a call for whoever set 10 in the first place, not a hyperparameter
  to flip mid-lane to hit a target count.

## Already-proved screening -- built, since "if cheap, build it" outranked a
## draw the ceiling does not allow

The sibling lcm/gcd lane found 5 of 10 rows in its family already proved
under the identical statement before doing any new work -- a coincidental
pre-existing declaration (`Nat.lcm_comm` etc. existed in `nat_prelude/lcm.rs`
for reasons unrelated to the `ml430` mirroring effort). `--statable`
(`check-dispatchable-frontier.py`) answers "can this be STATED here"; nothing
in the tree answered the narrower, cheaper "does a declaration with this
EXACT Mathlib-style name already exist", which is what actually produces free
closures.

**New: `scripts/check-autogenesis-already-proved.py`.** For a set of fact ids
(default: the current dispatchable set, read via
`check-dispatchable-frontier.py --json`), it extracts each fact's pinned
Mathlib `source_name` from its title (`"Mathlib v4.30 source proposition
<Name>"`, confirmed against both v1 and v2 facts) and checks it against
`kernel-environment-snapshot-v1.json`'s declaration names. A name match is
**necessary, not sufficient** for "already proved" -- the tool says so on
every line of output -- and it **refuses held-out fact ids even when named
explicitly**, since publishing a per-fact already-proved verdict for a
blind-evaluation row spends the thing held-out isolation exists to protect.

No fresh kernel build was needed or attempted: this worktree has no cached
`target/`, `axeyum-lean-kernel` is 334K lines with no incremental cache
available, and this repository's own guidance is to prefer measurement over a
cold build when a cheaper proxy exists. The existing environment snapshot
(committed 17:22 today, at `94b3e61`) is used as-is, with its staleness
reported on every invocation: **a name match is trustworthy (existence is
monotonic); a non-match is a lower bound on remaining work, not a proof that
none exists**, since names declared by the sibling lcm/gcd/totient lanes
after the snapshot was built would not show up.

### Result on the current dispatchable queue

```
python3 scripts/check-autogenesis-already-proved.py
screened: 11
already NAME-MATCHED in the kernel environment: 0 (0.0%)
```

**None of the 11 currently dispatchable rows are free** by this proxy --
genuine proof work remains for the whole queue, unlike the lcm/gcd family.
(Cross-checked as a positive control against a KNOWN already-proved fact,
`F:ml430-int-add-modeq-left-ee732b5b`, which is 216-entry-v1/closed and whose
source name `Int.add_modEq_left` does appear in the snapshot -- confirming the
tool actually detects a real match rather than defaulting to zero.)

### Tests

`scripts/tests/test_check_autogenesis_already_proved.py` (auto-discovered by
`scripts/run-python-controls.py`, no manual `check.sh`/justfile registration
needed -- confirmed via `scripts/check-control-registration.sh`,
`py_controls=385|py_orphans=0` after adding it): 8 unit tests -- source-name
extraction (3), a positive control (real match reported), a negative control
(real non-match not reported), a mixed batch, the held-out refusal, and a
false-positive control that the refusal does not fire on a non-held-out row.

Mutation-verified in a scratch copy (`/tmp/.../scratchpad/mutcopy{,2}`, never
the tracked source): inverting the match condition is killed by exactly the
positive- and negative-control tests; disabling the held-out refusal is
killed by exactly the refusal test. Both mutants left every other test green.

## Checks run (foreground)

| check | result |
| --- | --- |
| `python3 scripts/check-dispatchable-frontier.py` | exit 0, DISPATCHABLE 11 |
| `python3 scripts/check-autogenesis-holdout-isolation.py` (before AND after -- no manifest touched, so identical) | `held_out=67\|references=0\|PASS` both times |
| `python3 scripts/check-autogenesis-already-proved.py` | exit 0, 11 screened, 0 matched |
| `python3 -m unittest scripts.tests.test_check_autogenesis_already_proved` | 8/8 pass |
| mutation verification (2 mutants, scratch copy) | each killed by exactly the expected test(s) |
| `bash scripts/tests/test-dispatchable-frontier.sh` | 25/25 pass (untouched; confirms this lane's new file did not disturb it) |
| `scripts/check-control-registration.sh` | exit 0, `controls=25\|orphans=0`, `py_controls=385\|py_orphans=0` |
| `python3 scripts/validate-facts.py` | exit 0, 2034 facts, 0 errors |
| `python3 scripts/check-fact-depends-derived.py` | **exit 1, PRE-EXISTING on `main`** -- 8 `DEPENDS_DERIVED_ERROR` lines, all in the `natural-lcm`/`natural-gcd` family the sibling `nat-lcm-gcd` lane landed (missing `depends_on` edges for `Nat.zero_le`, `Nat.lcm_dvd`, `Nat.gcd_mul_lcm`, `Nat.dvd_lcm_left`, `Nat.dvd_lcm_right`). Confirmed not caused here: `git status --porcelain` shows only the two new scripts this lane added, no touch to `artifacts/facts/`. Not repaired here -- out of this lane's scope (`artifacts/facts/` beyond preregistration) and belongs to whoever owns that family's ledger entries. |
| `python3 scripts/gen-plan.py --check` | regenerated after this lane's status doc landed; green after |
| workspace cargo gate | **not run** -- no `crates/` file touched, and no cached `target/` exists in this worktree to make a cold build cheap |

## What this lane did NOT do

- **Did not preregister any new nursery rows.** The ceiling math above shows
  the smallest rule-compliant refill is 40 rows against 6 rows of headroom;
  preregistering anyway would have meant either hand-editing the generator's
  own R5 refusal or spending the ceiling on a partial held-out family that
  restores no blind breadth. Both are exactly the "make a counter go up"
  failure the brief warned against.
- **Did not rebuild the kernel-environment snapshot.** It is a known,
  reported limitation of the already-proved screen (see above) rather than an
  omission -- refreshing it is a `shape_search --include-constructed` run plus
  `gen-autogenesis-nursery-refill.py --snapshot-from`, and is worth doing
  before the NEXT refill lands, not for this one (which added no candidates
  the snapshot needs to cover).
- **Did not touch `check-dispatchable-frontier.py`, the nursery manifests, or
  `artifacts/facts/`.** Confirmed by `git status --porcelain`: only the two
  new `scripts/` files this lane added.

## Next

Whoever owns the ceiling decision should read "What should change" above and
pick one of the three options (raise `EVALUATION_CEILING`, allow extending an
existing family instead of only adding new ones, or shrink `PER_FAMILY`).
Until that lands, the dispatchable queue (currently 11, 9 of them
`natural-totient`) is the only source of new work, and
`check-autogenesis-already-proved.py` is available to any lane picking up a
fresh batch to check for free closures before starting proof work.
