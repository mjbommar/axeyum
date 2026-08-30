# Notes: 309-nursery-draw-four

Detail moved out of [`../status/309-nursery-draw-four.md`](../status/309-nursery-draw-four.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Deliberately NOT added to `gen-autogenesis-nursery-refill.py`'s
`select()`.** That function re-derives every family's candidate pool on
EVERY run, including already-frozen families (only the PARTITION is frozen
by `frozen_partitions()`, not which candidates fill a family's 10 slots). A
blanket glyph filter there would retroactively remove the known-bad row from
`natural-induction-and-divisibility`'s pool, shift which candidate occupies
each of that family's 10 slots, and rewrite an already-preregistered,
already-dispatched-against family -- exactly the hazard `frozen_partitions()`
exists to prevent for partitions, arriving through a different door. Scoping
the screen to `--statable` keeps it a pre-registration gate for NEW draws
without touching old ones; confirmed `--statable` against the real 160-row
(then 200-row) extension still exits 0 both before and after.

Three new controls in `scripts/tests/test-dispatchable-frontier.sh` (S6a
fires on a fresh glyphed candidate, S6b is the false-positive control for
lookalike punctuation/identifiers -- `...` and `sorryLike` -- S6c proves the
exemption is scoped to its one `fact_id` and not general). Mutation-verified
in a `cp -r`'d scratch copy, `__pycache__` cleared between iterations, never
in the tracked worktree:

| mutation | cases killed |
| --- | --- |
| delete the glyph regex (`(?!)`, never matches) | S6a, S6c |
| drop the `\b` word boundary (`sorry` as substring) | **S6b only** |
| widen exemption to `fact_id is not None` | S6a, S6c |
| widen exemption to `fact_id is not None` (targeted retest) | **S6c only** |

Registered nowhere new -- it extends the existing suite, already wired into
`scripts/check.sh` and `justfile`.

## Family selection

Re-measured: **14** modules now carry >= 10 fully screened, unused
candidates (down from draw 3's 18). **Twelve are draw 3's own exclusion
list** (`*.Gcd`, `*.ModEq`, `*.Prime.*`, `*.Factorial.*`, `*.Choose.*`,
`*.Bitwise.*`), unchanged: each still sits over the same mathematics as a v1
family that is development or train, so a held-out assignment there is still
the natural-division violation.

That leaves exactly **two** modules with no existing-family adjacency at
all -- and this draw is the first where *neither* is usable for held-out:

- `Init.Prelude` (35 candidates, Nat order/comparison bridging) -- **30 of
  35 already declared** in this kernel's own prelude (R9-contaminated),
  confirmed the same shape as draw 3's basic-arithmetic finding.
- `Mathlib.Data.Int.Order.Basic` (13, sign-based Int multiplication
  inequalities) -- adjacent to the already-partitioned `integer-order`
  (`Init.Data.Int.Order`, development, v1).

Both are fine for development/train (neither hazard applies to a
non-blind partition) but neither may land held-out. So the two held-out
slots needed supply from BELOW the 10-candidate floor, combined the way
draw 3 combined two Int modules for `integer-division-boundary-cases`:

- **`range-induction`** (16 = 8+8): `Init.Data.Range.Polymorphic.{Int,Nat}Lemmas`
  -- bounded interval-induction principles (rcc/rco/roc/roo x left/right)
  over both fragments. No existing family covers interval induction; the
  nearest name (`natural-induction-and-divisibility`, draw 2, held-out) is a
  different argument (divisibility-flavoured induction, module
  `Mathlib.Data.Nat.Init`) -- blind beside blind is fine per that draw's own
  precedent, and this isn't even the same shape.
- **`integer-absolute-value`** (13 = 3+7+2+1):
  `Mathlib.Data.Int.Order.Lemmas` + `Mathlib.Data.Int.Lemmas` +
  `Mathlib.Algebra.Order.Group.Unbundled.Int` + `Init.Data.Dyadic.Basic` --
  every candidate an `Int.natAbs` identity. No existing family names natAbs.

Both checked (not assumed) 0/13 and 0/16 IN-ENV (R9-clean) and 0 glyphed
(S6). Per the "prefer machinery the kernel already has" guidance: `natAbs`
identities lean on sign case-splits `nat_prelude`/`int_prelude` already
support, and the range-induction family is a direct generalization of
ordinary `Nat`/`Int` induction, which is foundational.

**Primary-module ordering is chosen, not incidental.** The module-path
cycle (held-out, development, train, repeating, restarting at held-out for
the new family set) is mechanical, so the family SET is picked so the two
held-out-safe families land at cycle positions 0 and 3 (mod 3 = held-out)
and the other two land at 1 and 2:

```
Init.Data.Range.Polymorphic.IntLemmas  (range-induction)            held-out
Init.Prelude                           (natural-order-bridging)     development
Mathlib.Data.Int.Order.Basic           (integer-order-inequalities) train
Mathlib.Data.Int.Order.Lemmas          (integer-absolute-value)     held-out
```

Verified by running `assign_partitions()`, not assumed. No target outcome
was consulted; the SET and the primary-module choice within each tuple are
this lane's judgement, the assignment is still the mechanical rule.

## Already-proved fraction

```
python3 scripts/check-autogenesis-already-proved.py
screened: 28 (the DISPATCHABLE set, not all 40 new rows -- held-out rows
              are never screened for this)
already NAME-MATCHED: 10 (35.7%)
  Int.add_assoc (draw 1 carryover),
  Nat.ble_eq_true_of_le, Nat.ble_self_eq_true, Nat.ble_succ_eq_true,
  Nat.eq_of_beq_eq_true, Nat.le_antisymm, Nat.le_of_ble_eq_true,
  Nat.le_of_lt_succ, Nat.le_of_succ_le_succ, Nat.le_refl
```

All 9 new matches are in `natural-order-bridging` (9 of its 10 dispatchable
rows -- one, `Nat.add_pos_right`, is not name-matched). Consistent with the
R9-contamination measurement above: this family was picked knowing it would
be free by name, the same "contamination in a non-held-out partition is a
feature, not a defect" reasoning draw 3 used for its basic-arithmetic
families.

## Attestation on s5 -- 2 new NOT-elaborable rows

Per `docs/contributor-guide/lean-surface-attestation.md`, ran the real-Lean
attestation on the full 200-row manifest rather than leaving this draw at
quotation grade:

```
python3 scripts/attest-nursery-surface.py \
  --manifest artifacts/autogenesis/nursery-v2-extension.json \
  --json-out <tmp>
  host             s5, Mathlib c5ea0035, Lean 4.30.0
  elapsed          3.9s
  negative control REJECTED (good)
  elaborated       197 of 200
```

Three rows fail. One is the already-known `F:ml430-nat-le-induction-2f088ac3`
(`⋯`). **Two are new, and neither carries a glyph** -- confirmed by re-running
`--statable`, which reports 0 glyphed both before and after:

```
F:ml430-int-natabs-coe-sub-coe-le-of-le-d2800d86  (Int.natAbs_coe_sub_coe_le_of_le)
F:ml430-int-natabs-coe-sub-coe-lt-of-lt-e0566dd0  (Int.natAbs_coe_sub_coe_lt_of_lt)
  lean: invalid coercion notation, expected type is not known
```

This is a **different failure mode** than the elided-proof glyph: the
statement `∀ {a b n : ℕ}, a ≤ n → b ≤ n → (↑a - ↑b).natAbs ≤ n` needs
surrounding declarative context (Mathlib's enclosing `variable` block, which
fixes the coercion target) that statement-only extraction does not carry, so
declaring the bare string as an isolated `axiom` leaves Lean unable to infer
what `↑a - ↑b` coerces to before it reaches `.natAbs`. S6 correctly does not
and should not catch this -- it is not a glyph.

Recorded via `--ingest-surface-attestation` + `--sync-surface-notes`, per
ADR-0615 (never rewrite or delete a preregistered `formal.statement`; both
rows are held-out, so ADR-0542 also forbids deletion). This shrinks
`integer-absolute-value`'s closable population to 8 of 10 -- the same shape
as the `natural-induction-and-divisibility` finding from the previous lane.
40 fact notes rewritten from the generated template; 82 pre-existing
hand-edited notes (from earlier draws' closed mirrors) correctly left alone.

**No screen exists yet for this failure class** (coercion notation needing
lost declarative context). Unlike the glyph case, this is not amenable to a
cheap regex on the pretty-printed string -- it would need either the
extractor to carry more surrounding context, or a pre-preregistration
elaboration pass (i.e. attest BEFORE preregistering, not after). Flagging
for whoever next revisits the extraction pipeline.

## Checks (all foreground, bare -- never through a pipe before reading `$?`)

| check | result |
| --- | --- |
| `check-autogenesis-holdout-isolation.py` **BEFORE** | `held_out=107\|PASS` |
| `check-autogenesis-holdout-isolation.py` **AFTER** | `held_out=127\|PASS` |
| `check-dispatchable-frontier.py` | exit 0, **DISPATCHABLE 28** (was 8) |
| `check-dispatchable-frontier.py --screen` (200 entries) | exit 0, 0 blocked |
| `check-dispatchable-frontier.py --statable` (200 entries) | exit 0, 0/0/0 |
| `check-autogenesis-already-proved.py` | exit 0, 28 screened, 10 matched (35.7%) |
| `gen-autogenesis-nursery-refill.py --check` | exit 0, `entries=200` |
| `validate-facts.py` | exit 0, 2154 facts, 0 errors (181 open) |
| `check-fact-depends-derived.py` | exit 0, `missing_edges=0` |
| `check-mirror-statement-fidelity.py` | exit 0, `violations=0`, PASS |
| `create-autogenesis-chain-catalog.py --check` | **exit 1, PRE-EXISTING** -- see below |
| `scripts/tests/test-dispatchable-frontier.sh` | 28/28 (25 pre-existing + 3 new S6) |
| `gen-plan.py --check` | exit 0 |
| `gen-autogenesis-nursery-refill.py --check` after attestation ingest | exit 0, byte-stable |

**`create-autogenesis-chain-catalog.py --check` fails, and it is NOT this
draw.** It reports `proof-derived edge F:ml430-int-add-comm-c5722728 ->
F:int-characterization-categorical-at-int is absent from depends_on`.
Confirmed via `git stash` (bare command, exit code read directly, not
through a pipe -- the banned `echo "exit=$?"` after `tail` idiom would have
reported this as passing): the same failure reproduces byte-for-byte with
every change in this lane's two commits stashed out. It was introduced by
the sibling nat-mul-order merge (`Int.add_comm` closing) that landed via
`git merge --no-edit main` at the start of this lane, before any draw-4 work.
Not repaired here -- `crates/` is out of scope for this lane, and this is a
`depends_on` ledger gap in another lane's closed fact, not a nursery
manifest issue.

## Next

Dispatchable is 28. Quoted cohort is 200 of 214 -- **14 rows of headroom**
remain, likely too little for a fifth 40-row draw without either raising the
per-family floor's efficiency or re-attesting a larger v1-equivalent
population. Genuinely novel held-out-safe supply is now essentially
exhausted at the 10-candidate-module granularity: every module with >= 10
screened candidates is either draw 3's excluded list or already consumed by
draws 1-4. The next held-out family, if one is needed before v1 grows, will
need the same below-floor multi-module combination technique used here and
in draw 3 -- or a fresh module survey once more mirrors close and free up
adjacency room.

The coercion-notation attestation failure (not a glyph, not caught by S6) is
a new, distinct finding for whoever next touches the extraction pipeline or
adds a second screen.
