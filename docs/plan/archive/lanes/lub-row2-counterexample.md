# Lane: lub-row2-counterexample — the least-upper-bound boundary, proved

<!-- plan-section: lane-status -->

Status: LANDED — LUB's ADR-0603 row 2 is a kernel-checked theorem, axiom-free.

Outcome 1 of the three the brief listed: **a proved implication from a stated
LUB principle to an omniscience principle**. The principle is *unrestricted
excluded middle*, not the analytic LLPO the two sibling rows reach.

## What was there before

`docs/curriculum/graded-statement-families.md` §2 recorded LUB's row 2 as
**pure absence** — "the unavailability is asserted, not proved" — the one
clean absence in that note, and the load-bearing one, since row 2 is the axis
ADR-0603's dominance argument rests on. An asserted unavailability cannot
fail, so it is not evidence.

## What the two existing row-2 results look like

Both are first-order implications taking the CLASSICAL CONCLUSION at a
specific family as a hypothesis and deriving a decision principle, both with
their family's hypothesis-class membership proved rather than asserted:

- `CReal.evt_attained_max_decides_sign` (`creal/extreme_value.rs`), family
  `CReal.evtLinear v := fun t => mul t v`, plus
  `evtLinear_uniformly_continuous`.
- `CReal.ivt_exact_root_decides_sign` (`creal/ivt_boundary.rs`), family
  `CReal.ivtPlateau`, plus its three hypothesis lemmas.

Both land on `∀ v, Or (le v zero) (le zero v)` — **analytic LLPO**, i.e. the
`lt_total` `creal/cotransitivity.rs` says is neither assumed nor provable.
Both carry an "Honest scope" section: the classical conclusion is proved at
least as strong as a principle this kernel lacks, not proved false.

## What landed

`crates/axeyum-lean-kernel/src/creal/lub_boundary.rs` — four declarations, all
**first-attempt kernel accepts**, all footprint **0** (read from
`kernel_declaration_projection`, not from prose):

| declaration | type (`render_lean` column, verbatim) | kind |
|---|---|---|
| `CReal.lubSet` | `(x0 : Prop) -> ((x1 : CReal) -> Prop)` | definition |
| `CReal.lubSet_inhabited` | `(x0 : Prop) -> CReal.lubSet x0 CReal.zero` | theorem |
| `CReal.lubSet_bounded` | `(x0 : Prop) -> ((x1 : CReal) -> ((x2 : CReal.lubSet x0 x1) -> CReal.le x1 CReal.one))` | theorem |
| `CReal.lub_decides_em` | `(x0 : Prop) -> ((x1 : CReal) -> ((x2 : ((x2 : CReal) -> ((x3 : CReal.lubSet x0 x2) -> CReal.le x2 x1))) -> ((x3 : ((x3 : CReal) -> ((x4 : CReal.lt x3 x1) -> Exists.{1} CReal (fun (x5 : CReal) => And (CReal.lubSet x0 x5) (CReal.lt x3 x5))))) -> Or x0 (Not x0))))` | theorem |

`CReal.lubSet A := fun x => Or (le x zero) (And A (le x one))` — the set
`(−∞, 0] ∪ ((−∞, 1] if A)`. Spivak's P13 quantifies over an ARBITRARY
inhabited bounded-above set, so a set carved out by an arbitrary `Prop` is
faithful to the classical statement rather than a strawman.

Why the conclusion is stronger than the siblings': `Or A (Not A)` for an
arbitrary `Prop` is unrestricted excluded middle. This kernel has only
`Decidable.em` (which takes a `Decidable` instance) and the four conditional
bridges that take unrestricted `em` as a HYPOTHESIS. LLPO is consistent with
BISH; `em` is not.

Why Bishop's supremum and not the classical one: the classical leastness
clause yields only `¬¬A` here, and `¬¬A → A` is itself the principle at issue,
so the reduction through it would be circular. The approximation property is
also exactly the clause `CReal.supOn_approx_lub` proves for the located case,
so row 2 refutes precisely the generalisation row 1 stops short of.

## Verification

- `creal_prelude_builds` — passes. Cost measured by toggling the build step in
  this worktree: **120.6 s** stubbed out against **130.5 s / 134.0 s** live
  (two runs), so ~+11 s / 9%. Not a multiple.
- `creal::lub_boundary_tests` — **4 passed**, in a new file rather than in
  `creal_tests.rs` (the append point every concurrent `creal` lane collides
  on). The one that matters is the ADR-0603 Amendment 2 non-vacuity control:
  at `A := True` BOTH supremum hypotheses are discharged and `Kernel::infer`
  accepts the instance, conclusion pinned verbatim against an independently
  built `Or True (Not True)`.
- `cargo test -p axeyum-lean-kernel --lib creal::` — **206 passed, 0
  failed**, 411.31 s. The first attempt was 205/1: the recorded build order
  in `creal_tests::steps_table_matches_recorded_extraction` is a pin a new
  `BuildStep` is invisible to until it is listed, and that one test was the
  only failure.
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean
  for this lane's files. Twelve errors remain on this base, all in
  `nat_prelude` (`add_factorial_le.rs` 2, `gauss_lemma.rs` 2,
  `nat_prelude_tests.rs` 8); this lane touched no `nat_prelude` file, so they
  are reported rather than fixed.
- `kernel_declaration_projection --require-declaration` discriminates:
  verified by asking for `CReal.lubSet_nonexistent_control`, which exits 1.
- `python3 scripts/validate-facts.py` — 2365 facts, 0 errors.
- `python3 scripts/check-settled-fact-statements.py` — PASS.
- `python3 scripts/check-autogenesis-holdout-isolation.py` — PASS before and
  after, `held_out=146 settled=0 references=0` both times. Nothing under
  `artifacts/autogenesis/` was touched.

## One thing worth carrying forward

The superseded §2 assessment looked for "a bounded, inhabited, **located** set
with no computable least upper bound". Locatedness is the wrong target — it is
exactly the data that makes `supOn` work. Dropping it is what made the
reduction four declarations long, using no primitive that was not already
present.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `a6ccca023` | `creal/lub_boundary.rs`: `CReal.lubSet`, `lubSet_inhabited`, `lubSet_bounded`, `lub_decides_em` — ADR-0603 row 2 for the least upper bound property |
| 2026-08-31 | `29c593d2a` | `creal/lub_boundary_tests.rs`: non-vacuity discharge at `A := True`, negative control, statement pin, footprint check |
| 2026-08-31 | `96c5ea9b8` | ADR-1010; `graded-statement-families.md` §2 corrected with the superseded absence quoted in place; `spivak.md` ch. 8 row; `F:creal-lub-decides-em` and its statement pin |
| 2026-08-31 | `6ff707144` | record `lub_boundary` in the pinned build order — full `creal::` sweep 206 passed, 0 failed |
