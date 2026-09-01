# Screening `Mathlib.Data.Nat.Log` for a nursery draw

Lane `screen-nat-log-family`, 2026-09-01. Screening only — no theorems
declared, no draw authored, no generator run. This document is the
deliverable.

## Verdict

**Drawable: YES**, with one correction to the input the coordinator was
working from, and no construction needed.

- The dispatchable-frontier tool's headline `37` survivors for
  `Mathlib.Data.Nat.Log` is **inflated by 20** — those 20 statements are
  already `proved` facts in `artifacts/facts/`, closed by direct flip
  (`already-proved-sweep`, 2026-08-18/29), not by any nursery draw. The
  genuinely open, unclaimed candidate pool is **17**, still comfortably above
  the `PER_FAMILY = 10` floor. See "The 37 is wrong" below — this is a
  measured tooling gap, not a guess.
- All 17 open candidates are ordinary extensional facts about `log`/`clog`
  *values* (equalities, inequalities, `iff`s). None reference Mathlib's
  private `log.go`/`clog.go` internals. **Zero are divergence-blocked, zero
  are not-statable-here.** All 17 are `FLIPPABLE`.
- **No construction needs to be declared.** `Nat.log`, `Nat.logAux`,
  `Nat.clog`, `Nat.clogAux`, and `Nat.log2` all already exist in
  `crates/axeyum-lean-kernel/src/nat_prelude/{log,clog,log2}.rs`, fully
  proved axiom-free. This is unlike the `Nat.dist`/`Nat.nth` situation
  (ADR-0653) — there is nothing to unblock.
- R9 (candidate's Mathlib name already declared in our kernel) is clean for
  all 17, verified by direct name-registry inspection, not just by absence
  from the fact catalog — see "R9 checked directly" below.
- **R11 (adjacency) did not run** — it operates on `FAMILY_MODULES` as
  currently defined in `gen-autogenesis-nursery-refill.py`, and adding a
  hypothetical family to check it is authoring the draw, which this lane was
  told not to do. The draw author must run the real `select()` + `guard()`
  (R1–R11) before finalizing. Reported here as **did not run**.

## Method

Every number below is from a command actually run in this worktree, not
inferred.

```
$ python3 scripts/propose-nursery-refill.py --remeasure
wrote artifacts/autogenesis/refill-headroom-v1.json: 2260 survivor(s), 3 ready family(ies)
READY FAMILIES     3 (module(s) with >= 10 unused survivors, not already owned)
      37  Mathlib.Data.Nat.Log
      18  Mathlib.Data.Nat.Bitwise
      15  Mathlib.NumberTheory.FactorisationProperties
```

```
$ python3 scripts/propose-nursery-refill.py --names Mathlib.Data.Nat.Log
  [... 37 names + rendered types ...]
37 screened unused candidate(s) in Mathlib.Data.Nat.Log (PER_FAMILY is 10)
```

Cross-checked every one of those 37 names against
`artifacts/autogenesis/mathlib-nat-int-fact-catalog-v1.json` (the file the
*real* generator's `select()` uses for its `already-catalogued` screen —
`catalogued = {row["source_name"] for row in catalog["facts"] if row["kind"]
== "external-source"}`, `gen-autogenesis-nursery-refill.py:2284-2286`) and
independently against `artifacts/facts/*.json`'s `formal.kernel_theorem`
field. Both agree: **20 of the 37 already have a `proved` fact.**

Mathlib source read directly at the pinned commit:

```
$ M=/data0/axeyum/lean-import-toolchain/mathlib4
$ git -C "$M" rev-parse HEAD
c5ea00351c28e24afc9f0f84379aa41082b1188f
$ cat "$M/Mathlib/Data/Nat/Log.lean"      # full 512 lines read
```

Our source read directly, not from a doc summary:
`crates/axeyum-lean-kernel/src/nat_prelude/log.rs` (632 lines, full),
`clog.rs` (304 lines, full), `log2.rs` (106 lines, full), and
`log_clog_order.rs` (2328 lines; grepped for declared names, spot-read the
`log_aux_mono`/`log_aux_le_fuel` region).

## The 37 is wrong: `propose-nursery-refill.py --names` under-screens

`propose-nursery-refill.py`'s `used_source_names()` reads only
`nursery-v1.json` and `nursery-v2-extension.json`'s `entries[].source_name`
— i.e. only names that have gone through an actual **nursery draw**. It does
not consult the fact ledger at all. So a proposition that was closed by
**direct flip** (found already proved in the kernel, matched
character-by-character against `formal.statement`, and had its status
flipped — the honest, no-new-proof-work route this repository's own
`CLAUDE.md` documents for `Nat.descFactorial_of_lt`) is invisible to this
screen and reappears as an "unused candidate" forever.

That happened to exactly 20 of the 37 `Nat.log`/`Nat.clog` propositions, all
closed on 2026-08-18 or 2026-08-29 by the `already-proved-sweep` lane (see
each fact's own `provenance.established_by`, e.g.
`artifacts/facts/F-ml430-nat-log-zero-right-8ea186db.json`). The real
generator does **not** have this gap — its own `select()` filters against
`mathlib-nat-int-fact-catalog-v1.json`'s `external-source` rows, which is
dated today and does contain all 20 — so a real draw run through
`gen-autogenesis-nursery-refill.py` would not re-draw them. Only the
*advisory* `--names` tool used for screening is stale relative to the fact
ledger. This is a real, measured gap and future screening passes over
`propose-nursery-refill.py --names` output should cross-check against the
fact catalog before trusting the count, exactly as this lane did.

| already closed (20, moot for a fresh draw) | | |
|---|---|---|
| `Nat.log_zero_right` | `Nat.log_zero_left` | `Nat.log_one_left` |
| `Nat.log_one_right` | `Nat.log_of_lt` | `Nat.log_le_self` |
| `Nat.log_lt_self` | `Nat.log_mono_right` | `Nat.log_monotone` |
| `Nat.log_antitone_left` | `Nat.log_le_clog` | `Nat.log2_eq_log_two` |
| `Nat.clog_zero_right` | `Nat.clog_zero_left` | `Nat.clog_one_left` |
| `Nat.clog_one_right` | `Nat.clog_pos` | `Nat.clog_mono_right` |
| `Nat.clog_monotone` | `Nat.clog_antitone_left` | |

Verified directly against the kernel's own name registry too (not just the
fact catalog): every one of these 20 names matches a `p.<field>` already
declared in `log.rs`, `clog.rs`, `log2.rs`, or `log_clog_order.rs`; none of
the 17 open ones do.

## The central finding: our doc comments mischaracterize Mathlib's *current* `log`/`clog`

`log.rs`, `clog.rs`, and `log2.rs` each carry a module doc that describes
Mathlib's `Nat.log`/`Nat.clog` as naive **well-founded recursion** on `n / b`:

```rust
// crates/axeyum-lean-kernel/src/nat_prelude/log.rs:1-14
//! Mathlib v4.30 defines
//!
//! ```text
//! def Nat.log (b : ℕ) : ℕ → ℕ
//!   | n => if h : 1 < b ∧ b ≤ n then log b (n / b) + 1 else 0
//! ```
//!
//! which is *not* structural: the recursive call is at `n / b`, and `n / b` is
//! not a constructor predecessor of `n`. Mathlib discharges that with
//! well-founded recursion, which in a Lean-style kernel drags in `WellFounded`
//! and (through the equation compiler) `Quot.sound`/`propext` — fatal to this
//! project's axiom-freedom metric.
```

Reading the actual pinned Mathlib source (`Mathlib/Data/Nat/Log.lean`,
commit `c5ea0035…`), this is **not what `Nat.log` is defined as**. Mathlib's
own module docstring says so explicitly:

```lean
-- Mathlib/Data/Nat/Log.lean, module docstring
We define both functions using recursion on `b`.
In order to compute, e.g., `Nat.log b n`, we compute `e = Nat.log (b * b) n` first,
then figure out whether the answer is `2 * e` or `2 * e + 1`.
The actual implementations use fuel recursion so that `(by decide : Nat.log 2 20 = 4)` works.
```

and the real `def`:

```lean
def log (b n : ℕ) : ℕ :=
  if b ≤ 1 then 0 else (go b n).2 where
  go : ℕ → ℕ → ℕ × ℕ
  | _, 0 => (n, 0)
  | b, fuel + 1 =>
    if n < b then (n, 0)
    else
      let (q, e) := go (b * b) fuel
      if q < b then (q, 2 * e) else (q / b, 2 * e + 1)
```

This is **fuel recursion**, structural on the second argument (`fuel`),
exactly the technique our own `log.rs` uses (Nat.rec on a fuel argument,
motive constant in the value) — just a *different algorithm*: Mathlib halves
the number of recursion steps by **squaring the base** each round
(`go (b*b) fuel`) and folding two bits of the answer out of one step, where
ours **divides the value by the base** each round
(`logAux b f (n/b)`), one bit per step. `Nat.log_of_one_lt_of_le` — the
naive equation our doc quotes as if it were the definition — is in the
*actual* source a genuine **proved theorem** (`by apply eq_of_forall_gt_iff
...`, going through `log_lt_iff_lt_pow`), not Mathlib's recursion equation
either. `Nat.clog` is the same shape, confirmed by reading `clog.rs`'s
identical (and identically stale) doc claim against the same file.

**This is not a new blocker and it does not change any verdict below** —
both constructions were already fuel-recursive in spirit, so the "well-founded
recursion drags in axioms" concern the doc raises was never actually the
risk on Mathlib's side either. But it is worth fixing in the three doc
comments (`log.rs`, `clog.rs`, `log2.rs` all repeat it) as a follow-up,
since a reader trusting them would misjudge the shape of the divergence.
This screening lane did not touch those files — doc edits belong to a lane
not mid-screen, to avoid any file-sharing collision with `nat-size-squarefree`
or other lanes working nearby in `nat_prelude/`.

The one thing this *does* explain: why `log_of_one_lt_of_le` and its
siblings (`log_mul_base`, `log_div_mul_self`) are still open on **our** side
despite the constructions matching in spirit. Our `log b n := logAux b n n`
uses fuel `n`; `log b (n/b) := logAux b (n/b) (n/b)` uses fuel `n/b`.
Unfolding one step of `logAux b n n` lands at `logAux b (n-1) (n/b)` —
different fuel (`n-1`, not `n/b`) applied to the same value `n/b`. Proving
they agree needs a fuel-irrelevance argument, not a `refl`. This is ordinary
follow-on proof work of the kind `log_aux_mono` (`∀ b f g n m, f≤g → n≤m →
logAux b f n ≤ logAux b g m`), `log_aux_le_fuel`, and
`log_aux_antitone_base` (all already declared in `log_clog_order.rs`) exist
to support — not a construction gap.

## Per-statement verdicts (all 37)

Method: read each statement's rendered type from
`propose-nursery-refill.py --names`, checked which constants/functions it
mentions, and confirmed (a) whether the constant is only `Nat.log`/`Nat.clog`
applied extensionally (never Mathlib's private `log.go`/`clog.go`), and
(b) whether an analogous statement is provable from machinery already in
`log.rs`/`clog.rs`/`log_clog_order.rs`/`log2.rs`, or from ordinary
induction over `logAux`/`clogAux`. None of the 37 mention Mathlib's internal
`go` pair-accumulator (the nursery's own `not-statable-here`/hygiene screen
would have removed anything referencing a private name; confirmed by
inspection that none of the 37 do).

**All 37 are FLIPPABLE.** Zero DIVERGENCE-BLOCKED, zero NOT-STATABLE-HERE.
This is the boring, good outcome: unlike `multichoose`/`fastFib`/`binaryRec`,
neither `log` nor `clog` has a Mathlib definition that is a *theorem* about a
structurally different function — both sides define the same extensional
floor/ceiling log, by two different fuel-recursive algorithms, and every one
of the 37 statements only talks about the functions' *values*.

- **20 already flipped and proved** (table above). Not available to a fresh
  draw; not blockers.
- **17 open, all FLIPPABLE, none needing a new construction:**

  | # | name | drawn in first-10? | statement |
  |---|---|---|---|
  | 1 | `Nat.clog_anti_left` | yes | `1 < c → c ≤ b → clog b n ≤ clog c n` |
  | 2 | `Nat.clog_eq_one` | yes | `2 ≤ n → n ≤ b → clog b n = 1` |
  | 3 | `Nat.clog_mono` | yes | `1 < c → c ≤ b → m ≤ n → clog b m ≤ clog c n` |
  | 4 | `Nat.clog_of_left_le_one` | yes | `b ≤ 1 → ∀ n, clog b n = 0` |
  | 5 | `Nat.clog_of_right_le_one` | yes | `n ≤ 1 → ∀ b, clog b n = 0` |
  | 6 | `Nat.log_anti_left` | yes | `1 < c → c ≤ b → log b n ≤ log c n` |
  | 7 | `Nat.log_div_mul_self` | yes | `log b (n/b*b) = log b n` |
  | 8 | `Nat.log_eq_one_iff` | yes | `log b n = 1 ↔ n < b*b ∧ 1 < b ∧ b ≤ n` |
  | 9 | `Nat.log_eq_one_iff'` | yes | `log b n = 1 ↔ b ≤ n ∧ n < b*b` |
  | 10 | `Nat.log_eq_zero_iff` | yes | `log b n = 0 ↔ n < b ∨ b ≤ 1` |
  | 11 | `Nat.log_mono` | no (11th) | `1 < c → c ≤ b → m ≤ n → log b m ≤ log c n` |
  | 12 | `Nat.log_mul_base` | no | `1 < b → n ≠ 0 → log b (n*b) = log b n + 1` |
  | 13 | `Nat.log_of_left_le_one` | no | `b ≤ 1 → ∀ n, log b n = 0` |
  | 14 | `Nat.log_of_one_lt_of_le` | no | `1 < b → b ≤ n → log b n = log b (n/b) + 1` |
  | 15 | `Nat.log_pos` | no | `1 < b → b ≤ n → 0 < log b n` |
  | 16 | `Nat.log_pos_iff` | no | `0 < log b n ↔ b ≤ n ∧ 1 < b` |
  | 17 | `Nat.log_two_bit` | no | `n ≠ 0 → log 2 (bit b n) = log 2 n + 1` |

  "Drawn in first-10" is what `select()` would actually take:
  `gen-autogenesis-nursery-refill.py`'s `select()` iterates
  `sorted(inventory)` and takes `pool[:PER_FAMILY]` — alphabetical, not
  difficulty-ordered. `Nat.log_of_one_lt_of_le` (the recursion-relationship
  theorem this brief singled out) is **not** in the first 10 under this
  ordering; it is #14. If the draw author wants it in-scope for this family's
  first ten, that requires a deliberate override of the generator's plain
  alphabetical slice, which this lane is not authorized to make.

  Rows 1–5 and rows 11 (base-monotonicity, `clog_eq_one`) rest on
  `log_aux_mono`/`log_aux_antitone_base`/`clog_aux_mono`/
  `clog_aux_antitone_base`, all already proved in `log_clog_order.rs` —
  likely cheap corollaries, since the `AntitoneOn`-wrapped forms
  (`log_antitone_left`, `clog_antitone_left`) are already proved from the
  same lemmas. Rows 7, 12, 14 (the `n*b`/`n/b`/fuel-relationship family) are
  the genuinely new proof work, per "The central finding" above. Rows 8–10,
  15–16 are ordinary `iff` repackagings of already-proved boundary facts
  (`log_of_lt`, `log_zero_left`, etc.) plus their contrapositives.

## R9 checked directly

R9 (`gen-autogenesis-nursery-refill.py:1538`, "a candidate whose Mathlib name
already has a declaration here may [not go to held-out]") compares a
candidate's Mathlib name against the **kernel's own name registry**, not
against the fact catalog. Checked directly by grepping every declared
`p.<field>` in `log.rs`, `clog.rs`, `log2.rs`, `log_clog_order.rs`: none of
the 17 open names (nor, in particular, none of the first-10 that a draw
would actually take) match a declared name. R9-clean.

## What this lane did NOT do (by design)

- Did not run `gen-autogenesis-nursery-refill.py` or author
  `FAMILY_MODULES`/`FAMILY_ROUTES` in the tracked file — see the draft block
  below instead.
- Did not run R11 (`scripts/check-holdout-adjacency.py`'s `screen_family`)
  against a hypothetical `natural-logarithm` family, because doing so
  requires adding the family to the generator first, which is authoring the
  draw. **Marked "did not run."**
- Did not declare any theorem, definition, or evidence file. No file under
  `crates/` or `artifacts/facts/` was touched.
- Did not fix the stale Mathlib-recursion doc claim in `log.rs`/`clog.rs`/
  `log2.rs`, to avoid any collision with lanes actively working in
  `nat_prelude/`.

## Draft authoring material (NOT applied — for the draw author)

A family name in this repository's kebab-case convention, paired with the
`kernel-induction` + `recursive-function-reconstruction` route pair used for
the other fuel/structural-recursion families (`natural-fibonacci-basic`,
`natural-stirling-numbers`, `natural-nth-root`):

```python
# scripts/gen-autogenesis-nursery-refill.py, FAMILY_MODULES (add):
    "natural-logarithm": ("Mathlib.Data.Nat.Log",),

# FAMILY_ROUTES (add):
    "natural-logarithm": ("kernel-induction", "recursive-function-reconstruction"),
```

Partition is assigned mechanically by `assign_partitions()`'s
`PARTITION_CYCLE` cycle over `sorted(FAMILY_MODULES)` — not chosen here.
The draw author must:

1. Re-run `create-autogenesis-mathlib-fact-catalog.py` (or confirm today's
   `mathlib-nat-int-fact-catalog-v1.json` is still current) so `select()`'s
   `catalogued` screen picks up the 20 already-flipped names.
2. Add a **second** new family — this module alone does not clear the
   "needs 2 new families" floor computation this session measured.
3. Run the real `select()` + `guard()` (R1–R11) and read what it actually
   drew — this document's "first 10" table is a prediction from reading
   `select()`'s sort/slice logic, not a run of it.
