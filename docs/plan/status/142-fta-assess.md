# Lane: fta-assess — refresh graded-statement-families.md, assess FTA row 3

<!-- plan-section: lane-status -->

**Done (`DONE`, fta-assess, 2026-08-27).** Two tasks, both measurement/doc,
nothing under `crates/` touched:

1. **Refreshed `docs/curriculum/graded-statement-families.md`'s MVT row 3**,
   stale within hours of being written: `polynomial_mvt`/
   `verify_mvt_certificate` (`crates/axeyum-cas/src/mvt.rs`) landed the same
   day the row still read "reachable, not built." Re-ran the suite fresh
   (`cargo test -p axeyum-cas --lib mvt::` — 18 passed, 0 failed) rather than
   trusting the landing lane's own report, updated row 3, the MVT verdict,
   and the "what this changes" pointer. Re-confirmed EVT row 2 is still
   "in progress" per `extremum.rs`'s own module doc (a separate lane is
   building that refutation in `creal/extreme_value.rs`; not yet landed at
   merge time, outcome not guessed). Mirrored the correction into
   `spivak.md` row 11. `cargo test -p axeyum-cas --lib extremum::`
   re-confirmed 20 passed, 1 ignored (unchanged from the note's own claim).

2. **Assessed FTA row 3 and row 2's very applicability** (assessment only,
   per brief — did not build root isolation, FTA, or any kernel
   declaration). Findings, all independently re-verified this session
   (fresh `--release` build of `kernel_declaration_projection`, positive AND
   negative controls of the same declaration kind, not inherited from the
   prior `graded-families` lane's report):
   - `CReal.sqrt`/`Complex.abs`/`Complex.abs_add_le`/`Complex.polyMul`(+its
     two correctness theorems)/`Complex.factorQuotient` all confirmed
     `found`; `Complex.exp`/`arg`/`fundamentalTheoremOfAlgebra` all
     confirmed absent.
     <!-- absent: Complex.exp, Complex.arg, Complex.fundamentalTheoremOfAlgebra -->
     So the earlier lane's "sqrt/abs no longer gate"
     correction holds up under independent re-check.
   - Complex root isolation genuinely does not exist: the naive keyword grep
     "matches" `extremum.rs` only via a false positive
     (`complex**ity**...isolat**ion**`, one sentence), confirmed by reading
     the line. The real evidence is `solve()`'s own match arm in
     `crates/axeyum-cas/src/lib.rs`, which drops any irreducible
     cubic-or-higher factor entirely (`_ => {}`) — no Cardano/Ferrari
     radical solver exists anywhere in the crate. Corrected
     `graded-statement-families.md`'s own row-3 parenthetical
     ("radical-form quadratics/cubics" was inaccurate — only quadratics get
     radical form; cubics-and-up get real-only Sturm isolation via
     `real_algebraic.rs`, never radical, never complex).
   - **Sized the cheapest sound route**: a Rational Univariate Representation
     (RUR) over the real/imaginary bivariate decomposition of `p(x+iy)`,
     built from `groebner_basis` (`groebner.rs`, lex order available),
     `sturm.rs`/`real_algebraic.rs` real root isolation, but needing new
     work for all of: bivariate real/imaginary decomposition, a bivariate
     (not univariate) resultant/elimination step (the existing `resultant()`
     only takes two univariate rational polynomials), primitive-element
     genericity, RUR extraction, and a certificate shape for a *derived*
     algebraic number rather than `real_algebraic.rs`'s single-witness
     `AlgebraicReal`. Confirmed no `primitive element`/`rational
     univariate`/`RUR` machinery exists anywhere in the crate. Sized as
     comparable to building `sturm.rs` + `real_algebraic.rs` again plus a
     new certificate — multi-file, not a same-day assembly the way MVT row 3
     was.
   - **The interesting finding**: FTA likely does not need row 2 at all.
     IVT/EVT/MVT/LUB's row 2 all refute the SAME failure mode — an
     undecidable comparison over an unbounded/open search. FTA's classical
     proof is a compactness argument over a bounded, closed disk, which
     Bishop-style analysis is documented to handle constructively (infimum
     of a uniformly continuous function over a compact set, no attained-max
     search needed). If the row-1 approximate construction goes through
     cleanly, FTA is a **three-row theorem (1, 3, 4)**, not a four-row
     family missing a row — a finding about ADR-0603's row-count assumption,
     not a gap in this theorem. Stated as not-fully-certain in the doc
     (nobody has attempted row 1 yet to rule out a hidden undecidable step).
   - Full reasoning and citations: `docs/curriculum/graded-statement-families.md`
     §4's new "Re-assessment, 2026-08-27" block.

Gates run this session (measurement only, all fresh): `scripts/
cargo-serialized.sh build --release -p axeyum-lean-kernel --example
prelude_theorem_inventory --example kernel_declaration_projection` (45s,
clean); `cargo test -p axeyum-cas --lib mvt::` (18 passed); `cargo test -p
axeyum-cas --lib extremum::` (20 passed, 1 ignored); `./scripts/check-links.sh`
(one pre-existing broken link, unrelated to files touched here, unchanged by
this lane). No fact registered, no `crates/`/`artifacts/`/`scripts/` file
touched.

<!-- plan-section: landed-changes -->

| 2026-08-27 | `DONE` | `graded-statement-families.md` MVT row 3 refreshed to landed; FTA row 3/row-2-applicability independently re-assessed with fresh positive/negative controls, a sized cheapest-route estimate (RUR), and a finding that FTA may be a three-row theorem with no row 2; `spivak.md` row 11 corrected to match. |
