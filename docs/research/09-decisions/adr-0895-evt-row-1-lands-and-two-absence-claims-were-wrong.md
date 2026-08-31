# ADR-0895: EVT row 1 lands, and two absence claims were wrong

Status: accepted
Date: 2026-08-30
Index-summary: `CReal.evt_approx_max` lands as pure composition of two
already-admitted theorems (`CReal.supOn_ub`, `CReal.supOn_approx_lub`), and
the "EVT has no row 1" claim in ADR-0692 and
`08-ivt-and-evt-measured-against-mathlib.md` is corrected: it was already
false at the moment either document was written, because both searched for
`CReal.supOn_upper_bound` — a name that never existed — instead of the
shipped `CReal.supOn_ub`.
Index-status: accepted

- **Lane:** `evt-row1-land-and-register`
- **Corrects:** ADR-0692's "Re-derivation against the current kernel"
  section and `08-ivt-and-evt-measured-against-mathlib.md` §2 ("Row 1 —
  there is none").
- **Does not touch:** ADR-0675's decision to cite IVT rather than EVT for
  the headline dominance claim, which is unaffected — see "What this does
  NOT change" below.

## What was claimed, and what was true

ADR-0692's kernel re-derivation, run in that lane's own worktree, printed:

```
CReal.supOn                    -> found  creal/complex/cpoint  definition  axioms=0
CReal.evt_approx_max           -> ABSENT (no declaration of that name)
CReal.supOn_upper_bound        -> ABSENT (no declaration of that name)
```

and `08-…`'s §2 independently ran the same probe and reported the same
absence, plus a name list that included `CReal.supOn` itself as absent (that
document was written before ADR-0691 landed `supOn`; ADR-0692 is the later,
corrected re-check).

**The upper-bound law was never absent under its own name.** It shipped as
`CReal.supOn_ub`, in `crates/axeyum-lean-kernel/src/creal/sup_laws.rs`,
already wired into the `STEPS` dispatch table in `creal.rs` before this ADR's
lane began. `CReal.supOn_approx_lub` — the least-upper-bound half — likewise
already existed in the same file. Both are `Theorem`s with an empty
`axiom_footprint`, confirmed by rebuilding `kernel_declaration_projection`
fresh in this lane's own worktree (a stale prebuilt binary reports a false
absence, per this repository's own standing warning):

```
$ cargo run -q --release -p axeyum-lean-kernel --example kernel_declaration_projection \
    -- --require-declaration CReal.supOn_ub --require-kind theorem
found	creal	theorem	CReal.supOn_ub	0

$ cargo run -q --release -p axeyum-lean-kernel --example kernel_declaration_projection \
    -- --require-declaration CReal.supOn_approx_lub --require-kind theorem
found	creal	theorem	CReal.supOn_approx_lub	0

$ cargo run -q --release -p axeyum-lean-kernel --example kernel_declaration_projection \
    -- --require-declaration CReal.supOn_upper_bound
error: no declaration named `CReal.supOn_upper_bound` in any prelude
```

The third line is the whole defect in one command: `supOn_upper_bound` is a
**guessed** name, and it has never existed. `08-…`'s own probe script
(`scratch-probe.sh`, committed alongside its draft) searched for
`CReal.supOn_upper_bound` among nine candidate names, all reported absent —
correctly, since none of the nine is the name the theorem actually shipped
under. **An absence probe that searches for a guessed name proves nothing
about whether the THING exists, only about whether that SPELLING exists.**
ADR-0692 repeated the same probe rather than searching by shape
(`shape_search --concl CReal.le --hyp CReal.UniformlyContinuousOn`, which
would have surfaced `supOn_ub` from its conclusion head and hypothesis list
without needing to guess the name at all).

**Zero facts in the ledger named either law**, independent of the naming
question — `grep -rl "sup_on\|supOn" artifacts/facts/` before this lane
returned nothing. So even a referee who knew the correct name could not have
found the theorem in the one place this repository asks them to look. That
half of the defect is bookkeeping, not naming, and this ADR's lane fixes both.

## What lands

1. **`CReal.evt_approx_max`** (`crates/axeyum-lean-kernel/src/creal/evt_row1.rs`),
   composing `supOn_approx_lub` (the witness `x`) and `supOn_ub` (bounding
   every `F y`) through `CReal.le_trans` — no new supremum machinery. Rendered
   type and axiom footprint, read from the kernel:

   ```
   theorem CReal.evt_approx_max :
     ((x0 : ((x0 : CReal) -> CReal)) -> ((x1 : CReal) -> ((x2 : CReal) ->
     ((x3 : CReal.le x1 x2) -> ((x4 : CReal.UniformlyContinuousOn x0 x1 x2) ->
     ((x5 : AxNat) -> Exists.{1} CReal (fun (x6 : CReal) =>
       And (CReal.le x1 x6) (And (CReal.le x6 x2)
         (((x7 : CReal) -> ((x8 : CReal.le x1 x7) -> ((x9 : CReal.le x7 x2) ->
           CReal.le (x0 x7)
             (CReal.add (x0 x6)
               (CReal.ofRat (Rat.natDivSucc (AxNat.succ AxNat.zero) x5)))))))))))))))
   ```

   Read from a fresh `--release` build of `kernel_declaration_projection` in
   this lane's own worktree (unfiltered emit mode, filtered to the `creal`
   row by hand). `axiom_footprint = []`, confirmed both by
   `nat_axiom_inventory --include-constructed --require-axiom-free creal`
   (`creal: axiom=0 opaque=0 quotient=0 total_trusted=0`) and by
   `kernel_declaration_projection --require-declaration CReal.evt_approx_max
   --require-kind theorem`, which prints `found creal theorem
   CReal.evt_approx_max 0`.

2. **Four facts registered**: `F:creal-supon`, `F:creal-supon-ub`,
   `F:creal-supon-approx-lub`, `F:creal-evt-approx-max`. Before this lane,
   zero facts named any `CReal.supOn` law (`grep -rl "sup_on\|supOn"
   artifacts/facts/` returned nothing).

3. **Corrections** to ADR-0692 (a dated correction note, its own decision
   left standing) and to `08-ivt-and-evt-measured-against-mathlib.md` §2 (the
   "Row 1 — there is none" heading and body, replaced with the current state
   and this ADR's citation).

## What this does NOT change

- **EVT still does not conclude an attained maximum**, and this theorem does
  not narrow `CReal.evt_attained_max_decides_sign` at all: `evt_approx_max`'s
  witness `x` moves with `n` and is never claimed to converge to a limit. Row
  2's impossibility result and row 1's approximate positive result are both
  true and both stay exactly as strong as before.
- **`F` must still be assumed `UniformlyContinuousOn [a,b]` with an explicit
  modulus carried as `Sort 1` data** — the same restriction `ivt_approx` and
  every rung of `creal/supremum.rs` carries. Nothing here reaches a weaker
  hypothesis.
- **The two-axis dominance test's EVT verdict does not flip to "dominates".**
  ADR-0692's test asks whether a comparison can be RUN at all against
  Mathlib's `IsCompact.exists_isMaxOn` (a positive ATTAINED maximum).
  `evt_approx_max` is now a genuine positive statement on our side — the row
  ADR-0692 said was needed for the comparison to even start — but it is an
  approximate maximum against Mathlib's exact one, so the honest read is
  still that **trusted base and computational content are now COMPARABLE
  for the first time**, not that we dominate: Mathlib's exact form has no
  computable content at all (classical choice over a compactness argument),
  while ours computes a witness to any requested accuracy — which is the
  same constructive-vs-classical trade `ivt_approx` already makes, just
  newly available to state for EVT. Whether that trade counts as dominance
  or as a still-narrower positive result is a judgment call for whoever
  next revisits `08-…`'s axis tables; this ADR does not make it, because
  making it well needs the Mathlib-side text re-read with the same care
  ADR-0692 gave IVT's, which is out of this lane's scope.

## Evidence and re-verification

- `crates/axeyum-lean-kernel/src/creal/evt_row1.rs` — the new declaration.
- `crates/axeyum-lean-kernel/src/creal/inventory/evt_row1.rs` — its inventory
  shard, checked by `creal_tests::every_creal_declaration_is_checked_and_axiom_free`
  against `kernel.environment()` directly (not against a hand list).
- `cargo test -p axeyum-lean-kernel --lib creal::` — 201 passed; 0 failed;
  946 filtered out; finished in 406.29 s (full sweep, run twice: the first
  run caught one pinned-order regression, fixed in a follow-up commit; the
  second run, after the fix, is the clean one quoted here).
- `python3 scripts/check-autogenesis-holdout-isolation.py` before and after
  this lane's changes: both runs printed
  `AUTOGENESIS_HOLDOUT_ISOLATION|held_out=136|files_scanned=1110|settled=0|references=0|verdict=PASS`
  — identical, since this lane never touches `artifacts/autogenesis/`.
- `python3 scripts/validate-facts.py`: 2322 facts, 0 errors, after the four
  new facts landed.
- `python3 scripts/check-settled-fact-statements.py`: `PASS` after `--write`
  pinned the four new facts (plus four unrelated already-settled facts from
  other lanes that were unpinned; additive only, no existing pin's digest
  changed).

## Negative control

`evt_approx_max`'s conclusion is `le (F y) (add (F x) eps)`. The version with
the slack term `eps` removed — an EXACT bound, `le (F y) (F x)` for every `y`
— is refused by the kernel: that would require the sampled witness to
literally attain the maximum, which is exactly what
`CReal.evt_attained_max_decides_sign` proves is unavailable. This is a small,
targeted control (one term dropped from the conclusion, not a whole subterm
transposed), so the rejection is a genuine `TypeMismatch`/proof-search
failure rather than the unbounded-failing-defeq pathology CLAUDE.md warns
about for large transposed controls. See
`crates/axeyum-lean-kernel/src/creal/evt_row1.rs`'s
`evt_approx_max_needs_the_slack_term` for the executed check: it rebuilds
both the shipped (slack) type and the exact variant from the same pieces,
asserts they are not `def_eq` (non-vacuity), then asserts the kernel accepts
the shipped proof term at the slack type and rejects it at the exact one.
Run and confirmed green in this lane's worktree: `1 passed; 0 failed;
finished in 116.28s`.
