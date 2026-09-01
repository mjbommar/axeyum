# Lane: ivt-evt-dominance-recheck — third re-verification of the dominance doc

<!-- plan-section: lane-status -->

Status: LANDED — ADR-1485 written, dominance document updated in place
(new preamble note, §8.1 re-ranking, §9.1 addendum, pointer at the stale
`cas-certificate=56` passage). Re-verifying
[`09-the-dominance-claim-verified-across-three-domains.md`](../../formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md)
against a tree newer than its 2026-09-01 `dominance-doc-reverify` pass
(base `f7adaf7c3`). Confirmed ADR-1435 (sturm/IVT bridge repair) and ADR-1460
(mvt/extremum audit) both post-date that base — `git merge-base --is-ancestor
f7adaf7c3 <adr-commit>` true for both.

## Measurement base

Worktree started already at `origin/main` HEAD `7e2f859dc`; no merge needed
(`git status` clean, `git rev-parse HEAD` == `git rev-parse origin/main`).

## First-pass measurements (this commit)

`kernel_declaration_projection --include-constructed`, built fresh in this
worktree (release): `rows=14539`, `distinct_names=2851` (up from the doc's
`rows=14297 distinct_names=2820` — one day of ordinary growth). All 30
`axiom`-kind rows still confirmed `prelude=axreal` only (`awk` over column 2
distinct on axiom rows -> single value `axreal`).

IVT/EVT declarations re-checked directly in this dump, all footprint 0,
unchanged from the doc: `CReal.ivt_approx`, `CReal.ivt_exact_root_decides_sign`,
`CReal.evt_approx_max`, `CReal.evt_attained_max_decides_sign`,
`CReal.lub_decides_em`, `CReal.lt_cotrans`, `CReal.apart_cotrans` all FOUND.
`CReal.le_total`, `CReal.lt_total` both still ABSENT (0 hits each) — the
positive-control-paired negative the doc's §4.1 depends on still holds.

`cargo test -p axeyum-cas --lib real_algebraic::` (ADR-1435's bridge): **24
passed, 0 failed** — includes the three new adversarial fixtures
(`verify_rejects_a_root_forged_exactly_at_the_open_upper_bound`,
`verify_accepts_a_loose_but_genuinely_open_upper_bound`,
`verify_accepts_a_root_bracket_touching_the_open_lower_bound_exactly`).

`cargo test -p axeyum-cas --lib mvt::`: **19 passed, 0 failed** (matches
ADR-1460's count exactly, including both endpoint-witness fixtures).

`cargo test -p axeyum-cas --lib extremum::`: **24 passed, 1 ignored, 0
failed** (matches ADR-1460's count exactly).

`cargo test -p axeyum-cas --lib exact_positivity_tests::` (the `ln(x^2)`
f64-sign-test fix, ADR-1410): **3 passed, 0 failed** —
`certified_equality_does_not_rest_on_a_floating_point_sign` passes; source
confirms `is_certainly_positive` replaced the `evalf(...) > 0.0` guard at
`lib.rs:2217`.

`python3 scripts/validate-facts.py`: exit 0, **2576 facts, 0 errors**,
`routes: cas-certificate=60(kernel-reconstructed=14,cas-internal=46)` —
matches the brief's "48 -> 60 facts" and the audit's "round two" closing all
five remaining unnamed modules (`gf2_search`/`gf2_shard`, `gosper`,
`groebner_cert`, `lib`). **This is not yet reflected in the dominance
document's §7.4/§8/§9, which still read `cas-certificate=54/56` and do not
mention the round-two closure, ADR-1435, or ADR-1460** — this is the specific
staleness this lane's edit fixes.

## Done

- Confirmed 5 of ADR-1400's 11 distinction-incompleteness findings fixed
  (`gosper.rs`, `gf2_shard.rs`, telescoping's pointwise floor, `normalforms.rs`,
  `sturm.rs`) plus a separately-found and fixed wrong `Certified` (the
  `ln(x^2)` f64 sign test). `ratint.rs` retired (mischaracterized, not fixed).
  Weakest open finding re-ranked to `geometry_certify.rs`'s minimality gap.
- Wrote [ADR-1485](../research/09-decisions/adr-1485-ivt-evt-dominance-recheck-re-ranks-the-distinction-gap-again.md).
- Updated the dominance document in place (new preamble note, §8.1, §9.1,
  a pointer at the stale `cas-certificate=54/56` passage).
- `python3 scripts/gen-adr-index.py` (0 new duplicates) and
  `scripts/check-merge-hygiene.sh` (PASS) both re-run after the edits.

## Not done / did not run

- §5.1's deeper gate census (`semantic_falsification`, `mutation_control`,
  `circularity`, `independent_replay`, `check-trust-closure.py`) was not
  re-run — same scope limit ADR-1425 recorded, now further stale.
- No full aggregate gate (`just check`/`check.sh`) was run — this lane
  touched no Rust source, only docs and the three targeted `axeyum-cas --lib`
  suites named above, each confirmed with a nonzero passing count.
