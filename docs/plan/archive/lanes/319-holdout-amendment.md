# Lane: holdout-amendment -- repair a spent blind-evaluation population

<!-- plan-section: lane-status -->

**Lane block (`DONE -- holdout-isolation green at held_out=96, two ADR-0542
amendments recorded, R10 binds the ledger to the v2 manifest, brief-step0
refuses a held-out target, holdout-amendment, 2026-08-30`).**

## Headline

`check-autogenesis-holdout-isolation.py` was `held_out=127|settled=10|FAIL` on
`main` and is now `held_out=96|settled=0|references=0|PASS`. No fact was
reopened; all ten are genuinely proved. The guard gap that produced the
incident is closed in three places, and the amendment is now machine-enforced
rather than recorded in a file nothing read.

Commits: `81c1aef5a`, `6f4b1e62b`, `137451362`, `1093e02f9`, `876ba7c47`,
plus the ADR commit below. **Not pushed.**

## 1. The dating -- the brief's reading held for 4 rows and not for 6

Declaration dates are the first commit introducing each
`<leaf>: kernel.name_str(nat, "<leaf>")` registration under `crates/`.

| fact | kernel theorem | declared | manifest | preregistered | blind then? |
| --- | --- | --- | --- | --- | --- |
| `F:ml430-nat-log-zero-left-9ec8541e` | `Nat.log_zero_left` | 2026-08-28 `3707c6040` | v1 | 2026-08-18 `2d65f19d8` | YES |
| `F:ml430-nat-log-zero-right-8ea186db` | `Nat.log_zero_right` | 2026-08-28 `3707c6040` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-log-of-lt-89eaf42e` | `Nat.log_of_lt` | 2026-08-28 `1dd090dff` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-log-le-self-da387172` | `Nat.log_le_self` | 2026-08-28 `722d9c204` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-clog-zero-left-1c61a5bf` | `Nat.clog_zero_left` | 2026-08-28 `2ccf6322c` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-clog-zero-right-d42d47b1` | `Nat.clog_zero_right` | 2026-08-28 `2ccf6322c` | v1 | 2026-08-18 | YES |
| `F:ml430-nat-dvd-add-0c5bcc91` | `Nat.dvd_add` | 2026-08-13 `46b47f869` | v2-ext | 2026-08-29 `94b3e61ee` | **NO** |
| `F:ml430-nat-dvd-mul-right-a87a83c4` | `Nat.dvd_mul` | 2026-08-13 `46b47f869` | v2-ext | 2026-08-29 | **NO** |
| `F:ml430-nat-dvd-add-iff-right-bf79c0cd` | `Nat.dvd_add_iff_right` | 2026-08-14 `eccaf84ac` | v2-ext | 2026-08-29 | **NO** |
| `F:ml430-nat-dvd-antisymm-507f9026` | `Nat.dvd_antisymm` | 2026-08-24 `7de26df70` | v2-ext | 2026-08-29 | **NO** |

**Did anything leak? Not because of the sweep, and the two families differ.**

* **`natural-logarithm` was genuinely blind and was genuinely spent.**
  Preregistered 2026-08-18 when no `Nat.log`/`Nat.clog` existed at all;
  contaminated 2026-08-28 by ordinary `nat_prelude/log.rs` + `clog.rs` work
  unrelated to the mirror programme. This is the `natural-binomial` shape
  ADR-0542 already records, **not** the accounting artifact the brief expected.
* **`natural-divisibility` was never blind.** Preregistered 2026-08-29 naming
  theorems admitted 5 to 16 days earlier.
* **The sweep `92a61164e` caused neither.** Every declaration predates it. It
  recorded a spend rather than making one, so the brief's conclusion about the
  sweep is right and its premise about the dating is half wrong.

**Correction to the "4 of 10" figure ADR-0615 recorded.** The true count of
`natural-divisibility` rows that were not blind is **at least 5**, and the
extra one is the general finding: `F:ml430-nat-dvd-mul-right` is satisfied by a
declaration we named `Nat.dvd_mul`. **R9 is a NAME screen and is structurally
blind to a proposition already proved under a different name.** Only the
type-comparing ranker saw it. The name screen also *over*-counts: `Nat.dvd_mod_iff`
name-matches but our type is `succ x1` where Mathlib's is `n`, so the row is
still genuinely open.

## 2. The amendments

Two ADR-0542 rows in `artifacts/autogenesis/mathlib-nursery-split-policy-v1.json`,
with **different `reason` strings** because the causes differ. Whole-family, per
`partition_unit`; nothing deleted, no fact reopened. `PARTITION_COUNTS` in
`create-autogenesis-mathlib-nursery-split.py` moves to
`{train 78, development 120, held-out 16}`, with the arithmetic recorded inline
as the audit trail (76 at preregistration, -19 gcd, -20 binomial, -21 logarithm).

## 3. The honest blind-population number: **96**, and it is an UPPER bound

Screened every held-out row two ways against the 2,289-declaration snapshot,
both controls passing (`Nat.add` present, `Bogus.zzz` absent):

| manifest | family | N | name-match | type-exact | settled |
| --- | --- | --- | --- | --- | --- |
| v1 | natural-square-root | 16 | 0 | 0 | 0 |
| v2-ext | integer-absolute-value | 10 | 0 | 0 | 0 |
| v2-ext | integer-division | 10 | 0 | 0 | 0 |
| v2-ext | integer-division-boundary-cases | 10 | 0 | 0 | 0 |
| v2-ext | integer-division-inequalities | 10 | 0 | 0 | 0 |
| v2-ext | integer-natcast | 10 | 0 | 0 | 0 |
| v2-ext | natural-induction-and-divisibility | 10 | 0 | 0 | 0 |
| v2-ext | natural-parity | 10 | 0 | 0 | 0 |
| v2-ext | range-induction | 10 | 0 | 0 | 0 |
| | **remaining held-out** | **96** | **0** | **0** | **0** |

*(Before the amendment the same screen gave `natural-logarithm` 21/10/6/6 and
`natural-divisibility` 10/4/7/4 — the seven being four genuine plus the three
exact-constant candidates that sweep manually rejected. Contamination was
confined to exactly these two families.)*

**How to verify it.** Two commands, and the second is the one that matters:

```
python3 scripts/check-autogenesis-holdout-isolation.py
  -> AUTOGENESIS_HOLDOUT_ISOLATION|held_out=96|settled=0|references=0|verdict=PASS
```

then re-run the per-family screen: import `brief-step0.py`'s own `rank` and
`control_probe` (never a reimplementation), assert the probe passes, and for
every held-out row compare its title's Mathlib name against the snapshot's
declaration names AND rank its `formal.statement` against the rendered types.
Any nonzero cell is a family owing an amendment. The reusable form of this is
`scripts/check-autogenesis-already-proved.py` for the name half and
`brief-step0.py` for the type half — deliberately not merged, see §5.

**Three caveats, and the number is honest only with them:**

1. **96 is an upper bound.** The snapshot is STALE by five named leaves
   (`add_pos_right`, `coprime_mul_of_coprime`, `totient_coprime_totient_iff`,
   two `Check.*`), none in these families' namespaces. A stale snapshot can
   produce a false ABSENT, never a false PRESENT, so contamination can only be
   understated.
2. **Neither screen measures "hard".** A row provable in one line from existing
   machinery matches neither. 96 counts rows *not already proved*, which is
   weaker than *blind and unattempted*.
3. **The v2 rows carry an unquantified erosion that is NOT in the 96.**
   `nursery-v2-extension.json`'s own `limitations` say no dependency-component
   analysis was run for it, so a v2 held-out row can share a component with a
   dispatchable one and nothing in that manifest sees it. 80 of the 96 are v2.

**Both owed amendments are now made.** ADR-0615's `natural-divisibility` debt
and the six `natural-logarithm` rows 315 recorded are discharged together; they
are not the same kind of debt and the ledger now says so per row.

## 4. `brief-step0.py`: refuse by SECTION, not by silence

**The call, and why it is not the sibling's.** `check-autogenesis-already-proved.py`
refuses a held-out id outright. Copying that here would be wrong: this tool's
consumer is the **dispatcher**, and "this target is held-out, do not dispatch
it" is the most valuable sentence it can produce. A tool that goes silent on
exactly the target where the dispatcher most needs an answer sends them to a
less careful method — which is how the sweep happened.

So the BLOCK is reported **first and loudly** (it was section 4, printed after
section 1's already-proved verdict — the warning arriving after the leak), the
run exits **5**, and sections 1–3 are **withheld**: naming the declaration whose
rendered type matches a blind proposition IS the proof route, and so is a shape
near miss, and so is "read these modules".

Fail-closed: an unreadable partition or an empty held-out population refuses
rather than reports. **No override flag** — an escape hatch a lane can pass
leaves no record; an amendment leaves a breach.

Verified both directions: `F:ml430-nat-sqrt-le-self` (still held-out) → exit 5,
no sections; `F:ml430-nat-dvd-mod-iff` (amended family) → exit 0, full report.

## 5. Should the two tools be one? **No — merge the guard, not the matchers**

They look like duplicate implementations of "is this already proved" and are
not. Each is blind where the other sees:

* the **name** screen misses a proposition proved under a different name
  (`Nat.dvd_mul` for `Nat.dvd_mul_right`) — measured in §1;
* the **constant-multiset** screen misses argument order — 4 false positives in
  25 exact-constant candidates, three of them in this same family.

Their costs differ too (a dictionary lookup over the dispatchable set versus
ranking every open statement against every rendered type). Collapsing them
deletes a real check.

What *was* duplicated is the **guard**, which is exactly what differed. So the
sibling gained the fail-closed empty-population check it never had — its
refusal is `set(fact_ids) & held`, unreachable when `held` is empty — and both
tools now refuse rather than report when blindness cannot be established.

**Left open:** three readers of the two manifests remain (this tool, the
frontier module, the isolation gate). They agree today and none was the cause;
consolidating them is a reasonable next task, not this one.

## 6. R10 -- the amendment now binds the v2 manifest

The larger gap. v1 is regenerated from the ledger so a v1 amendment is
enforced; the v2 extension had **no link to the ledger at all**.
`frozen_partitions` froze `family_partitions`, so the manifest was its own
authority — a hand edit that moved a family and recomputed `extension_sha256`
regenerated perfectly clean. A digest catches a careless edit, never a
deliberate one.

`nursery-v2-extension.json` now carries `preregistered_family_partitions`;
`frozen_partitions` freezes that, and **R10** requires every difference from
`family_partitions` to be a recorded ADR-0542 amendment with matching
`from`/`to`, and refuses an amended family recycled into held-out. R8 keeps only
"a preregistered family keeps existing".

**Two drafts of R10 were vacuous and are recorded in the source as measured dead
ends** — comparing the two *computed* assignments makes both the no-amendment
and destination branches unreachable, since the ledger is applied last and they
then agree by construction. Likewise re-aiming R8 at `preregistered_assignment()`
compares a function against the dict it derives from. R10 reads the two dicts
the **manifest** records, which is what makes every branch reachable.

## 7. Controls

Every guard mutated in a `copytree`'d scratch root, `__pycache__` cleared
between iterations, never a tracked source.

`nursery-refill-amendment` (new suite in `mutation_controls.py`), baseline 37
green — **7 mutants, each killed by exactly 1 test**:
no-amendment move, wrong `from`, wrong `to`, recycled-into-held-out, missing
preregistered freeze, missing ledger, family amended twice.

`test-brief-step0.sh`, baseline 14 green, **no mutant survived**:

| guard deleted | controls that die |
| --- | --- |
| `is_held_out` → `return False` | GUARD 5, 5b |
| the `module is None` raise | GUARD 5d only |
| the empty-population raise | GUARD 5e only |
| the `if refused: return 5` branch | GUARD 5, 5d, 5e |

Reported as measured rather than rounded to "exactly one". Row 1 kills two
because refusing and withholding are one branch; row 4 kills three because the
exit status is one guard with three independent witnesses — and rows 2 and 3
each kill only their own case, which is what proves the fail-closed guards are
not rejecting through the held-out test. GUARD 5c (an amended row is answered in
full) dies under **none** of the four: without it, a tool that refused every
target would satisfy the other four and be useless.

`test_check_autogenesis_already_proved.py`: the new empty-population guard
mutated to `if not held and False:` kills exactly
`test_a_population_with_no_held_out_rows_is_refused`, with a positive control
that one held-out row is enough.

**Fixture rot found and fixed:** GUARD 5's fixture was a `natural-logarithm`
row, which this lane's own amendment made dispatchable. A control whose fixture
drifts out of the population it tests stops discriminating silently; the fixture
is now `natural-square-root`.

## 8. Gates run (foreground)

```
check-autogenesis-holdout-isolation.py  -> held_out=96|settled=0|references=0|PASS  (exit 0)
check-dispatchable-frontier.py          -> OK, dispatchable set non-empty          (exit 0)
gen-autogenesis-nursery-refill.py --check -> OK, development=70 held-out=80 train=50 (exit 0)
create-autogenesis-mathlib-nursery-split.py --check -> development=120 held-out=16 train=78|amendments=4
check-mirror-statement-fidelity.py      -> facts=2155 mirrors=414 violations=0 PASS (exit 0)
validate-facts.py                       -> 0 errors                                (exit 0)
check-control-registration.sh           -> see below
gen-plan.py --check                     -> see below
mutation_controls.py nursery-refill-amendment / nursery-refill-ceiling -> all killed
mutation_controls.py --check-anchors    -> suites=37 anchors=421 stale=0
test-brief-step0.sh                     -> pass=14 fail=0
unittest test_gen_autogenesis_nursery_refill -> 37 OK
unittest test_check_autogenesis_already_proved -> 10 OK
```

The aggregate gate was **not** run, per the brief. Exit statuses were read from
the bare command, never from a pipeline's last stage.

## 9. What this lane did not do

- No `crates/` change (three sibling lanes are in the preludes).
- No push.
- No fact reopened and no `epistemic_status` touched.
- Did not consolidate the three manifest readers (§5).
- Did not investigate the 12 `unpinned` mirrors the fidelity gate reports;
  pre-existing and unrelated.
