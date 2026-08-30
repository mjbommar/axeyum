# Lane 360 — `CReal.supOn` (EVT row 1)

<!-- plan-section: lane-status -->

## Status

**`CReal.supOn` LANDED**, derived and axiom-free, with
`CReal.supSeq_converges_supOn` tying it to the mesh maxima it is built from.
Thirteen declarations, four rungs. Twelve were first-attempt kernel accepts;
the thirteenth failed once on a `pi_fv`/`arrow` binder. Decision recorded in
[ADR-0691](../../research/09-decisions/adr-0691-supon-lands-evt-gets-a-row-one-but-not-yet-the-lub-laws.md).

This answers [ADR-0675](../../research/09-decisions/adr-0675-evt-is-a-refutation-with-no-row-one-behind-it.md)'s
finding that EVT had a row-2 impossibility result with nothing constructive
behind it. **It does not yet restore per-statement dominance** — see "What is
still open" below, which is the part to read before quoting this lane.

### Landed

In `crates/axeyum-lean-kernel/src/creal/supremum.rs`:

| rung | declarations |
| --- | --- |
| 6c | `CReal.meshLevelCount_ge_of_size` |
| 6d | `CReal.meshMax_le_add_of_modulus` |
| 6e | `CReal.supLevel`, `CReal.supLevel_mono`, `CReal.supSeq`, `CReal.supSeq_mono`, `CReal.supSeq_le_add` |
| 6f | `CReal.le_meshLevelCount`, `CReal.supSeq_abs_diff_le`, `CReal.supSeq_cauchy` |
| 7 | `CReal.supOn`, `CReal.supSeq_converges_supOn` |

Plus one extraction in `creal/ivt.rs`: `CReal.scaledCauchy_of_abs_diff_le`,
the raw `(K+2, per-pair)` pair that `cauchy_of_abs_diff_le` already built and
then immediately hid inside an `Exists`. `regular_of_scaled_cauchy` needs it as
DATA and kernel fact 2 means a `Cauchy f` witness can never give it back.

### Verification

- `creal_prelude_builds`: **110.4 s before, 114.0 s after** — flat. (An
  intermediate 143.8 s reading was contention, load 9.3 with a sibling lane's
  `rustc` at 436% CPU; it did not reproduce.)
- Full `creal::` sweep: **199 passed, 0 failed.** This includes
  `every_creal_declaration_is_checked_and_axiom_free`, which enumerates
  `kernel.environment()` rather than a hand list — so it is what confirms all
  thirteen are derived and axiom-free, and it is what caught them being absent
  from the inventory shards.
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: clean.
  `rustfmt --check` on every touched file: clean.
- Not run: the workspace gate, `check.sh`, and `prelude_theorem_inventory`.
  The coordinator re-verifies. Note that the theorem inventory would not have
  answered the question anyway — `supOn` is a `Definition`, and that tool lists
  theorems only.

## What is still open — read this before claiming EVT dominance

`supOn` is **a value with a convergence law, not yet a characterized
supremum.** Every machine-checked statement about it currently says only that
it is the limit of the mesh maxima. Two declarations separate that from EVT:

Detail moved to [`../notes/360-creal-supon.md`](../notes/360-creal-supon.md).

