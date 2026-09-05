# Lane: metric-products — the product of two metric spaces (W2-10)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, metric-products, 2026-09-05).** W2-10's
product-metric half is landed, in a NEW file
(`crates/axeyum-lean-kernel/src/metric_prod.rs`, registered from the crate
root beside `metric.rs`, per the brief's isolation constraint — `metric.rs`
itself was never touched): `Metric.prod` (the max metric on
`Sigma.{0,0} M.carrier (fun _ => N.carrier)`), both projections proved
uniformly continuous, the `->` direction of "continuous into the product
iff continuous in both components", completeness transfer, and
`Metric.cpoint` related to `Metric.prod Metric.creal Metric.creal` as a
carrier (setoid) equivalence — NOT an isometry, since the two distances
are genuinely different formulas (Euclidean vs max). See
[ADR-1639](../../research/09-decisions/adr-1639-the-product-metric-is-the-max-metric-and-its-triangle-inequality-is-one-max_le.md).

Twelve names (`MetricProdNames::all()`), all `Kernel::axiom_footprint`
empty, confirmed by `cargo test --release -p axeyum-lean-kernel --lib --
metric_prod --test-threads=4` (the confirmed-correct final run, after the
clippy fix below): **7 passed; 0 failed**, `finished in 99.78s`.

1. `Metric.prod : Metric -> Metric -> Metric` — the 12-field record,
   `dist (x,y) := CReal.max (M.dist (fst x)(fst y)) (N.dist (snd x)(snd y))`.
2. `Metric.prod_fst` / `Metric.prod_snd` — the two projections.
3. `Metric.prod_fst_uniformly_continuous` / `..._snd_...` — 1-Lipschitz,
   identity modulus.
4. `Metric.prod_fst_continuous_of_continuous` / `..._snd_...` — the `->`
   direction of the continuity-into-the-product iff.
5. `Metric.prod_complete : Complete M -> Complete N -> Complete (prod M N)`.
6. `Metric.cpoint_of_prod` / `Metric.prod_of_cpoint` — the carrier maps
   between `CPoint` and `(Metric.prod Metric.creal Metric.creal).carrier`.
7. `Metric.prod_of_cpoint_of_prod` (round trip one, definitional) and
   `Metric.cpoint_of_prod_of_cpoint` (round trip two, via `CPoint.rec`).

**What did NOT land**, sized:

- Compactness transfer (`CompactOn`, the net-cover route in
  `metric/compactness.rs`, ~2000 lines) — the brief marked this
  conditional on 1–3 landing, and those three (a 12-field record, two
  continuity theorems each proved for both projections, a four-deep-nested
  `Exists.rec` completeness proof) consumed the round's whole budget.
- The `<-` direction of "continuous into the product iff continuous in
  both components" — needs `CReal.max_le` to COMBINE two component
  moduli into one, the same shape `Metric.prod_complete` needed once, but
  nested one level deeper (inside a modulus-producing existential rather
  than at a theorem's top level).
- An isometry (or bi-Lipschitz bound) between `Metric.cpoint`'s Euclidean
  distance and `Metric.prod Metric.creal Metric.creal`'s max distance —
  only the CARRIER equivalence is proved. Would need `CReal.sqrt`
  monotonicity against both `max(|dx|,|dy|)` and `|dx|+|dy|` bounds; not
  derived this round.

**Two real defects, found by running the suite, not by inspection** (both
would have compiled fine — Rust sees only `ExprId`s, the type errors are
inside the kernel's own checker):

1. `Metric.ContinuousAtWith`'s modulus `k` is `Nat -> Nat` (it supplies the
   DENOMINATOR argument `k n`), unlike `Metric.CauchyAt`/`TendsToAt`'s
   plain-`Nat` numerator `K` — I conflated the two "modulus" shapes.
   `declare_continuous_comp` existentially quantified over plain `Nat`;
   fixed to `Nat -> Nat` in both the extraction and the re-packaging
   (commit `7068500cf`).
2. The N-side modulus-combination rewrite (`K2+K1 = K1+K2`, via
   `Nat.add_comm`, needed to line the N-projection's own bound up with the
   SAME combined modulus the M-side already used) built its `Eq.rec`
   motive with `CReal.le` where it needed `Rat.le` — both sides are still
   `Rat.natDivSucc` values at that point, before `CReal.ofRat_le` lifts
   them (commit `02384e4c4`).

**Mutation table** — both RUN (not predicted), each applied/tested/restored
one at a time in the shared worktree, `git diff` verified empty after each
restoration:

| mutant | mechanism | run command | result |
|---|---|---|---|
| wrong component in the triangle inequality | `build_dist_triangle`'s `t2a` (bounds `M`'s distance via `le_max_left`) changed to `le_max_right` | `cargo test -p axeyum-lean-kernel -j 4 --lib -- metric_prod:: --test-threads=4` | **KILLED: 7 of 7 `metric_prod::` tests failed.** Kernel `TypeMismatch` named the swapped selector directly (`Sigma.fst` expected, `Sigma.snd` got), `finished in 703.73s` |
| completeness forgetting to combine the two moduli | `declare_prod_complete`'s `kc := d.add(k1, k2)` changed to `kc := k1` (drops the N-projection's own rate) | `cargo test --release -p axeyum-lean-kernel --lib -- metric_prod --test-threads=4` | **KILLED: 7 of 7 `metric_prod::` tests failed.** Kernel `TypeMismatch` named a `Rat.natDivSucc` term whose numerator no longer matched the established bound, `finished in 189.10s` |

**Gates run, with nonzero test counts / exit status**:

- `cargo check -p axeyum-lean-kernel -j 4` — exit 0 (clean compile, ~6–37s
  depending on cache state).
- `rustfmt --edition 2024 crates/axeyum-lean-kernel/src/metric_prod.rs` —
  applied (per-file, not workspace `cargo fmt`).
- `cargo test -p axeyum-lean-kernel -j 4 --lib -- metric_prod:: --test-threads=4`
  (baseline, first post-fix, DEBUG profile — before the coordinator's
  correction to prefer `--release`) — **7 passed; 0 failed**, `finished
  in 424.28s`.
- `cargo test --release -p axeyum-lean-kernel --lib -- metric_prod --test-threads=4`
  (mutant 2 run) — 7 of 7 failed as designed, `finished in 189.10s`,
  restored and reconfirmed clean.
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — found
  one real lint (`vec_init_then_push` in `declare_prod`'s 12-field
  construction), fixed (`vec![...]` in place of `Vec::with_capacity` +
  twelve `.push`es, same left-to-right evaluation order, which matters
  here since each builder mints fresh fvars from `d` in sequence) — exit 0
  clean on the rerun.
- `cargo fmt --all --check` — exit 0, clean.
- `cargo test --release -p axeyum-lean-kernel --lib -- metric_prod --test-threads=4`
  (FINAL confirming run, after the clippy fix) — **7 passed; 0 failed**,
  `finished in 99.78s` — the number to trust; release is ~4.25x faster
  than the debug baseline above on this suite, matching the coordinator's
  "debug is up to 32x slower on proof terms" guidance in direction if not
  magnitude (this suite's cost is dominated by the shared-kernel
  `OnceLock` build-once-clone-seven-times pattern, not purely proof-term
  checking).
- `python3 scripts/validate-facts.py` — `2856 facts, 0 errors` (new fact
  included: `F:metric-product-completeness-transfer`).
- `python3 scripts/check-settled-fact-statements.py --write` then bare —
  `SETTLED_FACT_STATEMENTS|PASS`.
- `python3 scripts/gen-py-prelude-fields.py` — exit 0, no diff (Metric/
  `metric_prod` are not part of that mirror).
- `python3 scripts/gen-adr-index.py` — exit 0, `rows=841`;
  `duplicate_numbers=0166,0167` reported but PRE-EXISTING (old-style
  numbers from an unrelated pair of ADRs, not touched by this lane).
- `python3 scripts/gen-plan.py` / `--check` — exit 0.
- `scripts/check-merge-hygiene.sh` — first run FAILED (two stale generated
  artifacts: `frontier-shape-census-v1.json`, `production-provenance-ledger.md`,
  both stale because of the new fact); regenerated both
  (`scripts/frontier-shape-census.py`, `scripts/gen-production-provenance-ledger.py`)
  and reran — `MERGE_HYGIENE|...|PASS`.
- **Did NOT run**: `just check` / `./scripts/check.sh` (the full aggregate
  gate) — out of scope for a single-file addition and would cost another
  long queue wait on this host; the next lane merging this, or a
  pre-push run, should still run it before `main` moves.

Also added: `crates/axeyum-lean-kernel/examples/metric_prod_theorem_inventory.rs`
(the same shape as `nat_theorem_inventory`/`kernel_declaration_projection`,
for a prelude the latter does not build) and
`artifacts/facts/F-metric-product-completeness-transfer.json`.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `a0619473d` | scaffold Metric.prod (max metric, 12-field record + projections + continuity + completeness + cpoint relation); compiles clean, kernel acceptance not yet run |
| 2026-09-05 | `7068500cf` | fix: move metric_prod_tests under metric_prod/; fix Metric.ContinuousAtWith's modulus (Nat -> Nat, not Nat) |
| 2026-09-05 | `02384e4c4` | fix: N-side modulus-combination rewrite motive needs Rat.le, not CReal.le |
