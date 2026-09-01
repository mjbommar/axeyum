# Lane: ivt-evt-dominance-recheck — third re-verification of the dominance doc

<!-- plan-section: lane-status -->

Status: IN PROGRESS — re-verifying
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

## What is still to do

- Write the dominance document's update: §7.4/§8 re-ranked with the sturm.rs
  fix and the zero-remaining-module-gap; §2.2/§3 given a one-line pointer to
  ADR-1435/1460 confirming the IVT/EVT rows are unaffected in substance.
- Write ADR-1485 recording the re-ranking.
- Report which of ADR-1400's eleven findings remain open (checked against
  ADR-1410's "not repaired" list: `series.rs` truncation order and
  `prove_derivative`'s half-angle fallback are explicitly still open; the
  geometry_certify.rs/geometry_check.rs minimality gap and
  `gf2_extension.rs`'s `ExtensionTraceHankelMinor` and the "decided
  negatives have no certificate type" finding were not mentioned as
  repaired in any commit found by `git log --grep`).
