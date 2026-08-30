# Notes: 310-already-proved-sweep

Detail moved out of [`../status/310-already-proved-sweep.md`](../status/310-already-proved-sweep.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

| fact | why it's not a match |
| --- | --- |
| `F:ml430-int-le-elim-efa70bfa` | Statement is a `Nat.le_intro`-style CPS elimination principle (`a <= b -> forall P, (forall n : Nat, a + n = b -> P) -> P`). No declaration of that shape exists; the ranker's top pick is `Nat.le_intro` itself, which is the direct 3-hypothesis witness form, not the CPS eliminator. Same three constants (`add`, `eq`, `le`), completely different arity and structure. |
| `F:ml430-nat-dvd-add-iff-left-332cbe04` | Needs `k \| n -> (k \| m <-> k \| (m + n))` with hypothesis on `n`. The only candidate, `Nat.dvd_add_iff_right`, is `x0∣x1 -> (x0∣x2 <-> x0∣(x1+x2))`; assigning `x1 = n` to match the hypothesis forces the conclusion to `k∣(n+m)`, not `k∣(m+n)`. `Nat.add` argument order, not commuted in the type. `Nat.dvd_add_iff_left` does not exist (checked directly against the snapshot). |
| `F:ml430-nat-dvd-mul-left-a1a8a4b8` | Needs `a ∣ b*a` (unconditional). Only candidate is `Nat.dvd_mul : x0 ∣ (x0*x1)`, i.e. `a ∣ a*b` -- multiplication order swapped, and unlike the case above there also isn't a hypothesis to make room for a different variable assignment. |
| `F:ml430-nat-dvd-mul-left-of-dvd-200e20a4` | Needs `a∣b -> forall c, a ∣ c*b`. Only candidate is `Nat.dvd_mul_right_of_dvd : x0∣x1 -> x0∣(x1*x2)`, i.e. `a∣b -> a∣(b*c)` -- same swapped order. |

All 4 stay `open`, `formal` untouched, no evidence attached.

## 3. The 21 genuine closures

Six of the 21 needed the ranker's **second**-ranked candidate, not its top
pick, because of exactly the order-collision caveat the tool prints on every
verdict -- the tie-break is alphabetical-by-name at equal score, and the
alphabetically-first name was sometimes the WRONG direction/variant:

| fact | correct name (not the tool's naive top pick) | top pick was |
| --- | --- | --- |
| `F:ml430-nat-clog-zero-right-d42d47b1` | `Nat.clog_zero_right` | `Nat.clog_zero_left` (wrong side) |
| `F:ml430-nat-eq-of-beq-eq-true-6ec35ee4` | `Nat.eq_of_beq_eq_true` | `Nat.beq_eq_true_of_eq` (opposite direction) |
| `F:ml430-nat-le-of-ble-eq-true-646f4e10` | `Nat.le_of_ble_eq_true` | `Nat.ble_eq_true_of_le` (opposite direction) |
| `F:ml430-nat-log-zero-right-8ea186db` | `Nat.log_zero_right` | `Nat.log_zero_left` (wrong side) |

Every one of the 21 was verified by:

1. Reading the rendered type off the fresh snapshot (not source text, not the
   tool's naive top row) and comparing it to `formal.statement` by hand,
   substituting variables explicitly rather than trusting the constant count.
2. Running the exact `checker_command` that ended up in the fact (all 42 = 21
   facts x 2 evidence rows), and separately confirming each type-match
   checker returns count 0 against a fabricated declaration name.
3. Confirming `axiom_footprint == []` via a `theorem_axiom_footprint` binary
   **built fresh in this worktree** (not the shared checkout's copy, though
   the shared copy agreed on every name checked -- see the stale-binary
   entries in `CLAUDE.md`'s Gotchas for why that distinction matters).

The 21: `Int.add_assoc`, `Int.mul_eq_zero`, `Nat.ble_eq_true_of_le`,
`Nat.ble_self_eq_true`, `Nat.ble_succ_eq_true`, `Nat.clog_zero_left`,
`Nat.clog_zero_right`, `Nat.dvd_add`, `Nat.dvd_add_iff_right`,
`Nat.dvd_antisymm`, `Nat.dvd_mul` (via `F:ml430-nat-dvd-mul-right-a87a83c4`
only -- see the false positives above for its `-left` siblings),
`Nat.eq_of_beq_eq_true`, `Nat.le_antisymm`, `Nat.le_of_ble_eq_true`,
`Nat.le_of_lt_succ`, `Nat.le_of_succ_le_succ`, `Nat.le_refl`,
`Nat.log_le_self`, `Nat.log_of_lt`, `Nat.log_zero_left`, `Nat.log_zero_right`.

Each fact was flipped to `epistemic_status: proved`, `proof_route:
kernel-lean`, `axiom_footprint: []`, `formal.kernel_theorem` /
`formal.kernel_statement` pinned (the rendered type, in the field
`check-mirror-statement-fidelity.py` exists for -- `formal.statement`, the
mirrored Mathlib proposition, was never touched, confirmed PASS below), two
evidence rows (exact-type-match, whole-prelude axiom-freedom), and a `notes`
sentence saying plainly this was established by an earlier lane's prelude
work for reasons unrelated to this mirror programme, not proved here.

## 4. Second-order gate effects

- **`check-fact-depends-derived.py --fix`** added `depends_on` edges to 19
  other facts (e.g. `F:nat-pow-sq-aux-eq-pow`, `F:nat-restrict-injective`,
  `F:rat-nat-gauss`) whose kernel proofs already used these theorems directly
  but had nothing in the ledger to name until now. Also updated the
  pre-existing `F:nat-dvd-antisymm` generated fact's `depends_on` (unrelated
  to this lane's edits, picked up by the same `--fix` pass).
- **`gen-autogenesis-nursery-refill.py`** was stale (`--check` failed on
  `mathlib-statable-vocabulary-v1.json`); regenerated. Not attributable to
  this lane's edits specifically -- it was stale before this run started.
- **`create-autogenesis-chain-catalog.py --check` is still red, and now for a
  bigger reason than the pre-existing one this brief named.** Pinning
  `formal.kernel_theorem` on `F:ml430-int-add-assoc-749cb0ff` (required by
  this task) shifts the catalog's theorem-ownership tie-break away from the
  older, unpinned `F:int-add-assoc` fact (the script explicitly prefers a
  pinned name over one resolved through checker-command regex fallback), the
  same way the pre-existing `F:ml430-int-add-comm-c5722728` pin already had.
  Measured by importing the script's own functions and collecting every
  missing edge instead of stopping at the first: **100 missing proof-derived
  edges**, 40 newly attributable to `add_assoc`, 60 pre-existing for
  `add_comm` (confirmed pre-existing: the task brief already named the
  `add_comm` case as red from an earlier merge, before this lane touched
  anything). Added 2 of the 100 by hand for
  `F:int-characterization-categorical-at-int` as a spot check that the fix
  shape works; did **not** chase the remaining ~98 -- that is systemic
  rework across facts this lane has no context on, the script has no `--fix`,
  and `--fix` was checked not to exist (only `--check`/`--json`/`--output`/
  `--verify`). Left red. This is a real, measured finding for whoever owns
  the chain-catalog script next: **every future mirror-flip that pins
  `formal.kernel_theorem` for a widely-used theorem will surface more of
  this**, because the tie-break rule and the mirror-flip convention
  (ADR-0603) are in tension whenever both an old generated fact and a new
  mirror name the same kernel theorem.

## 5. Gates run

```
python3 scripts/validate-facts.py                    -> 0 errors, 2154 facts
python3 scripts/check-mirror-statement-fidelity.py    -> PASS, 0 violations, 402 hash-verified
python3 scripts/check-fact-depends-derived.py --fix   -> fixed, then 0 missing edges
python3 scripts/create-autogenesis-chain-catalog.py --check
                                                       -> RED (see #4), pre-existing category, not fully fixed
python3 scripts/gen-autogenesis-nursery-refill.py --check
                                                       -> regenerated once, then clean
python3 scripts/gen-plan.py --check                   -> clean, no PLAN.md changes needed
```

The aggregate gate (`just check` / `./scripts/check.sh`) was **not** run, per
the brief.

## 6. What this lane did not do

- No `crates/` or `scripts/` change (a sibling lane owns the nat prelude; the
  archived `check-autogenesis-already-proved.py` was run from a scratch copy
  with a patched `ROOT`, never edited in place).
- No push.
- Did not attempt to fully resolve the `create-autogenesis-chain-catalog.py`
  cascade (see #4) -- flagged for the next lane that touches it.
- The 7 facts scoring 0.75-0.999 in the re-run were not investigated; they
  are near-misses by the tool's own definition, not candidates for closure.
