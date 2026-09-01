# Screening `Mathlib.Data.Nat.Log` for a nursery draw

Lane `screen-nat-log-family`, 2026-09-01. Screening only — no theorems
declared, no draw authored, no generator run (the two tooling fixes below
touch only `propose-nursery-refill.py` and `gen-autogenesis-nursery-refill.py`'s
`HELD_OUT_CONSTRUCTIONS` constant, never `FAMILY_MODULES`/`FAMILY_ROUTES`).
This document is the deliverable.

**UPDATE, same day, same lane.** The coordinator independently verified
this document's two findings, then surfaced a THIRD, structurally identical
gap: `propose-nursery-refill.py` also never applied the generator's
`HELD_OUT_CONSTRUCTIONS` screen, which — until this update — still excluded
`Nat.log`/`Nat.clog`/`Nat.log2` and would have made `select()` refuse nearly
every `Mathlib.Data.Nat.Log` candidate had a draw actually added the family.
Both gaps are now fixed in the screening tool. `Nat.log`/`Nat.clog` are
removed from `HELD_OUT_CONSTRUCTIONS`; `Nat.log2` and `Nat.sqrt` BOTH stay
-- `Nat.log2` for a reason discovered only by measuring `select()` itself,
not by the topic argument that justified dropping the other two (see "The
`HELD_OUT_CONSTRUCTIONS` decision" below) -- and both are now guarded by a
mutation-tested control. Every number in this document has been re-measured
against the fixed tool. See "Corrected re-measurement" near the end for the
authoritative numbers — the verdict below is the corrected one, not the
original.

## Verdict

**Drawable: YES**, conditional on the `HELD_OUT_CONSTRUCTIONS` decision this
update makes (see below), verified with two corrections to the tooling the
coordinator's original brief was working from, and no construction needed.

- The dispatchable-frontier tool's headline `37` survivors for
  `Mathlib.Data.Nat.Log` was **inflated by 20** — those 20 statements are
  already `proved` facts in `artifacts/facts/`, closed by direct flip
  (`already-proved-sweep`, 2026-08-18/29), not by any nursery draw. The
  genuinely open, unclaimed candidate pool is **17**, still comfortably above
  the `PER_FAMILY = 10` floor. See "The 37 is wrong" below — this was a
  measured tooling gap, not a guess, and it is now fixed at the source
  (`used_source_names()`/`catalogued_source_names()` in
  `scripts/propose-nursery-refill.py`).
- **Second, independent gap (found by the coordinator, verified here):** the
  same tool never applied the generator's `HELD_OUT_CONSTRUCTIONS` screen —
  `select()` refuses ANY candidate mentioning a construction in that set,
  regardless of which family it would land in, and every `Nat.log`/`Nat.clog`
  candidate mentions one of `Nat.log`/`Nat.clog`/`Nat.log2` as a type
  constant. So the family would have read as ready here and yielded **zero**
  candidates the moment a draw actually added it to `FAMILY_MODULES` — a
  loud `RefillError`, not silent, but only once someone tried. Fixed by (a)
  mirroring the screen into the proposer (`held_out_constructions()`) and (b)
  the substantive decision this update makes: dropping `Nat.log`/`Nat.clog`
  from the generator's `HELD_OUT_CONSTRUCTIONS`, verified sound because
  `natural-logarithm` no longer has any `held-out` row (see "The
  HELD_OUT_CONSTRUCTIONS decision" below). `Nat.log2` and `Nat.sqrt` BOTH
  stay -- `Nat.log2` for an UNRELATED reason found only by measuring
  `select()`'s actual output, not the topic argument that justified the
  other two.
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
- **`Mathlib.Data.Nat.Log` alone still cannot clear the frontier floor**,
  independent of its survivor count. `dispatchable_yield(n)` restarts the
  `held-out/development/train` partition cycle at index 0 for every draw's
  new families, so a draw of exactly 1 new family always sends `ceil(1/3) =
  1` of it (i.e. all of it) to held-out and yields **0** dispatchable rows,
  whatever the family's candidate count is. A draw needs a second new family
  regardless; see "Floor arithmetic" below for the exact numbers this
  session.

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

- Did not run `gen-autogenesis-nursery-refill.py` to produce a draw, and did
  not touch `FAMILY_MODULES`/`FAMILY_ROUTES` — see the draft block below
  instead. The one edit made to the generator (`HELD_OUT_CONSTRUCTIONS`,
  three lines) is a screening-tooling fix authorized explicitly by the
  coordinator, not a draw.
- Did not run R11 (`scripts/check-holdout-adjacency.py`'s `screen_family`)
  against a hypothetical `natural-logarithm` family, because doing so
  requires adding the family to the generator first, which is authoring the
  draw. **Marked "did not run."**
- Did not declare any theorem, definition, or evidence file. No file under
  `crates/` or `artifacts/facts/` was touched.
- Did not fix the stale Mathlib-recursion doc claim in `log.rs`/`clog.rs`/
  `log2.rs`, to avoid any collision with lanes actively working in
  `nat_prelude/`. Unaffected by the later update — that touched only
  `scripts/propose-nursery-refill.py`, `scripts/gen-autogenesis-nursery-refill.py`,
  and their test suites.

## The second blind spot: `HELD_OUT_CONSTRUCTIONS` was never applied here

`gen-autogenesis-nursery-refill.py:158` (before this update) carried:

```python
HELD_OUT_CONSTRUCTIONS = {"Nat.log", "Nat.clog", "Nat.log2", "Nat.sqrt"}
```

applied in `select()` as `if constants & HELD_OUT_CONSTRUCTIONS: continue`
(reason `held-out-construction`) — a candidate whose TYPE mentions any of
these constants is refused, for ANY family, not just one covering their own
module. The comment directly above it already said, in as many words:

> "Note the consequence for anyone reading `propose-nursery-refill.py`'s
> output: the PROPOSER does not apply this screen and the GENERATOR does, so
> `Mathlib.Data.Nat.Log` and `Mathlib.Data.Nat.Sqrt` appear in the proposer's
> 'ready families' and yield ZERO candidates here."

Confirmed by reading `select()`'s control flow directly: it iterates
`sorted(inventory)`, resolves `family = module_family.get(record["module"])`,
and `continue`s immediately if the module has no family yet
(`module_family.get(record["module"])` is `None` for both `Mathlib.Data.Nat.Log`
and `Mathlib.Data.Nat.Sqrt` today -- neither is a value in `FAMILY_MODULES`).
So the `constants & HELD_OUT_CONSTRUCTIONS` line is never
even reached for their candidates — so the exclusion bites only the moment
someone actually adds the module to `FAMILY_MODULES`, at which point `select()`
raises `RefillError(f"family {family!r} yields {len(pool)} screened
candidates, fewer than the {PER_FAMILY} the refill takes")` once nearly every
candidate is screened out. Loud, but only after the fact — the proposer's
count gave no warning in advance.

`propose-nursery-refill.py`'s `remeasure()`/`show_names()` never read
`HELD_OUT_CONSTRUCTIONS` at all before this update, so this was a second,
independent way the same tool overstated headroom, on top of the fact-ledger
gap. Fixed the same way as the first: `held_out_constructions()` reads the
set out of the generator's own source by regex (mirroring the existing
`read_pins()` pattern), and both `remeasure()`'s per-record loop and
`show_names()` now apply it in the same relative order `select()` does
(after the not-statable-here check, before the elided-proof-glyph check).

## The `HELD_OUT_CONSTRUCTIONS` decision -- made in two measured steps, and the first one was wrong

**Step A: what does a blind family's TOPIC need?** Verified directly against
`nursery-v1.json`'s `entries[].partition` field (not taken from the
generator's comment or from the coordinator's message):

```python
>>> # every natural-logarithm row:
{'development'}
>>> # every natural-square-root row:
{'held-out'}
>>> # every v1 family with ANY held-out row, scanned across all of them:
['natural-square-root']
```

`natural-logarithm` was moved entirely to `development` (ADR-0542,
2026-08-30 — ordinary hand proof work in `nat_prelude/log.rs`/`clog.rs` spent
the blind family before this session), and `natural-square-root` is
independently confirmed the **only** family in `nursery-v1.json` with any
`held-out` row — the last surviving v1 blind family. This step's own reading
was: drop all three of `Nat.log`/`Nat.clog`/`Nat.log2`, keep only `Nat.sqrt`.
**That reading was landed, then reverted for `Nat.log2` — see Step B.**

**Step B: does `select()` agree the drop is safe, rather than merely
plausible by topic?** Wrote a read-only diagnostic that calls the real
`select()` (never the generator's write path) with the original
four-constant set and with candidate reduced sets, and diffs the resulting
`(family, source_name)` pairs directly:

```
drop {"Nat.log","Nat.clog"} only, keep {"Nat.log2","Nat.sqrt"}: ZERO diff
drop "Nat.log2" alone: NOT zero --
    + natural-elementary-bounds: Nat.log2_two
    - natural-elementary-bounds: Nat.not_exists_sq
```

`natural-elementary-bounds` is an ALREADY-DRAWN family with **every one of
its 10 `nursery-v2-extension.json` rows partition `held-out`**, and it has
nothing to do with `Nat.log`/`Nat.clog`/`Nat.log2` by topic. Dropping
`Nat.log2` admits `Nat.log2_two` (which mentions `Nat.log2` as a type
constant) past every other screen, and it sorts alphabetically ahead of
`Nat.not_exists_sq` in that family's `pool[:PER_FAMILY]` slice — displacing
a member of an unrelated BLIND family. This is precisely the retroactive
alteration ADR-0542's amendment discipline exists to prevent, and it would
have shipped through an ordinary `select()` regeneration with no amendment
review at all, because `select()` re-derives the whole manifest deterministically
on every run and nothing marks an already-drawn member as protected from a
later constant edit.

**Landed:** `HELD_OUT_CONSTRUCTIONS = {"Nat.log2", "Nat.sqrt"}` — only
`Nat.log`/`Nat.clog` dropped. Re-confirmed zero-diff against the original
four-constant set over all 460 currently-drawn rows after landing, and
`gen-autogenesis-nursery-refill.py --check` passes clean (the one prior
"stale" report, from the intermediate `{"Nat.sqrt"}`-only state, was purely
the extension file's own `screens.held_out_constructions` provenance array
plus its derived hash — verified via diff to carry ZERO `entries` change —
and was resolved by running the generator once, without `--check`, to bring
that provenance field current with the corrected final source).

The comment's own numbers ("34 candidates", "17 drawable of 19 reported")
predate both this session's measurement and the fact-catalog fix, and are
**not** carried forward — see "Corrected re-measurement" below for the
numbers actually measured against the fixed tool. `Mathlib.Data.Nat.Log`'s
count is unaffected by the `Nat.log2` correction either way: none of its 17
open candidates mention `Nat.log2` as a constant, confirmed by re-measuring
after landing the final two-constant set (still 17).

## The control: `Nat.sqrt` AND `Nat.log2` must never be dropped

Per the coordinator's explicit request that this control matters more than
the removal itself: it guards the repository's last remaining v1 blind
family (`Nat.sqrt`) and, after Step B, an unrelated already-drawn blind
family's exact membership (`Nat.log2`) — both previously enforced by
nothing but a comment.

`scripts/tests/test_propose_nursery_refill.py`'s `HeldOutConstructionsTests`
asserts `held_out_constructions() == {"Nat.log2", "Nat.sqrt"}`, plus
separately that `Nat.log`/`Nat.clog` are absent (protection against an
accidental re-add in the other direction). Registered in
`scripts/tests/mutation_controls.py` as suite `nursery-refill-headroom-screen`,
with a mutation that changes the generator's `HELD_OUT_CONSTRUCTIONS =
{"Nat.log2", "Nat.sqrt"}` to `{"Nat.evil"}` — i.e. exactly the shape of an
accidental drop of either. Run through the real harness (not a hand-rolled
loop, which `__pycache__` staleness would make unreliable per this
repository's own recorded incident — cleared caches and re-ran to confirm,
then re-ran a second time through `mutation_controls.py` itself for the
authoritative verdict):

```
$ python3 scripts/tests/mutation_controls.py nursery-refill-headroom-screen
nursery-refill-headroom-screen: baseline green, 7 tests (python3 -m unittest scripts.tests.test_propose_nursery_refill)
  a fact-catalog name (drawn or flipped directly) is not headroom killed 1: test_a_proved_fact_never_drawn_through_the_nursery_is_excluded
  Nat.sqrt and Nat.log2 must stay in HELD_OUT_CONSTRUCTIONS ... killed 3: test_mirrors_the_generators_set, test_nat_log2_is_present, test_nat_sqrt_is_present
```

Exit 0 — both mutations are `killed N`, never `SURVIVED`/`DID NOT
BUILD`/`DID NOT RUN`. **The control genuinely fails without the fix**,
confirmed by both a hand run (before wiring into the harness, cache cleared
between mutations) and the harness's own authoritative classification.
Restored to the clean, fixed state immediately after each check; `git diff`
confirms no mutation was left in the tree.

## Corrected re-measurement, both fixes applied

```
$ python3 scripts/propose-nursery-refill.py --remeasure
wrote artifacts/autogenesis/refill-headroom-v1.json: 2060 survivor(s), 2 ready family(ies)
pinned inventory   9729 records, 4285e551680abf3b…
screened out       7669
      5173  not-statable-here
      1699  hygienic-or-generated
       662  already-drawn
       125  divergence-registry
        10  held-out-construction
survivors          2060 across 87 module(s)
READY FAMILIES     2 (module(s) with >= 10 unused survivors, not already owned)
      17  Mathlib.Data.Nat.Log
      15  Mathlib.NumberTheory.FactorisationProperties
AT MOST -- a draw of all 2 hygiene-clean families would add at most 10 dispatchable row(s) (held-out takes ceil(n/3), not a third)
the frontier floor is 10, so a draw needs 2 new family(ies)
```

The three original candidates, corrected:

| module | original (stale tool) | corrected | why it moved |
|---|---|---|---|
| `Mathlib.Data.Nat.Log` | 37 | **17** | 20 already-catalogued (fact-ledger fix); `held-out-construction` no longer applies to it post-decision |
| `Mathlib.Data.Nat.Bitwise` | 18 | **dropped from the ready list entirely** (< 10; exact count not surfaced by this tool, which only reports modules ≥ `PER_FAMILY`) | almost certainly the fact-ledger fix — a sibling lane (`nat-size-squarefree`) is actively landing `Nat.size`/`Nat.bit` declarations and flipping bitwise mirrors directly, exactly the shape the fact-ledger gap missed |
| `Mathlib.NumberTheory.FactorisationProperties` | 15 | **15** | unaffected by either fix — no overlap with the fact catalog's new exclusions or with `Nat.sqrt` |

**Floor arithmetic, worked out rather than asserted:**

`dispatchable_yield(n) = PER_FAMILY * (n - ceil(n / PARTITION_CYCLE_LEN))`,
`PER_FAMILY = 10`, `PARTITION_CYCLE_LEN = 3` (all re-read from source, not
copied):

| new families (n) | held-out = ceil(n/3) | dispatchable = 10·(n − held-out) | clears floor of 10? |
|---|---|---|---|
| 1 | 1 | 0 | no |
| 2 | 1 | 10 | **yes, exactly** |

**So `Mathlib.Data.Nat.Log` alone — at 17, or at the original stale 37 —
never clears the frontier floor.** This is not a consequence of either
correction; it was already true before this session touched anything, and
the tool's own message said so both before and after ("a draw needs 2 new
family(ies)"). What the corrections change is which SECOND family is
available: with the ready-family list now `{Log: 17, FactorisationProperties:
15}` (Bitwise having dropped out), a draw of exactly these two — both
individually ≥ `PER_FAMILY` — is the only pairing this measurement currently
supports, and it clears the floor exactly (10, not more). Whether
`FactorisationProperties` itself screens clean under R9/R11 is unmeasured
here — out of this lane's scope, and per the tool's own disclaimer, "the
real screen rejects most of them."

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

**Both blockers this document originally left for the draw author are now
resolved, not merely documented:** `mathlib-nat-int-fact-catalog-v1.json`
already carries the 20 already-flipped names (confirmed current, used
directly by this session's `--remeasure`), and `HELD_OUT_CONSTRUCTIONS` no
longer excludes `Nat.log`/`Nat.clog` (see "The
`HELD_OUT_CONSTRUCTIONS` decision" above) — so adding `natural-logarithm` as
drafted above would no longer hit the `RefillError` it would have hit this
morning. The remaining steps:

1. Add a **second** new family — this module alone does not clear the
   "needs 2 new families" floor computation this session measured (see
   "Floor arithmetic" above). Per the corrected re-measurement, the only
   other family currently reporting ≥ `PER_FAMILY` survivors is
   `Mathlib.NumberTheory.FactorisationProperties` (15) —
   `Mathlib.Data.Nat.Bitwise` dropped out of the ready list under the fixed
   screen. Neither has been screened for R9/R11 by this lane.
2. Run the real `select()` + `guard()` (R1–R11) and read what it actually
   drew — this document's "first 10" table is a prediction from reading
   `select()`'s sort/slice logic, not a run of it.
