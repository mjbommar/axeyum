# ADR-1485: re-checking IVT/EVT dominance finds five of ADR-1400's eleven findings fixed, and the weakest point moves to `geometry_certify.rs`

Date: 2026-09-01
Status: Accepted
Lane: `ivt-evt-dominance-recheck`

Index-summary: A third re-verification pass of
[09-the-dominance-claim-verified-across-three-domains.md](../../formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md),
scoped to the IVT/EVT rows the document cites, against a tree newer than the
2026-09-01 `dominance-doc-reverify` pass (ADR-1425). Confirms `sturm.rs`'s
half-open-interval defect — the specific finding ADR-1425 flagged as sitting
"directly under [the document's] IVT row" — is fixed (ADR-1435, three new
adversarial fixtures, 24/24 `real_algebraic::` tests) and that `mvt.rs`/
`extremum.rs`, sharing the same consuming idiom, were independently audited
clean for a structural reason (ADR-1460, 19/19 and 24/24-plus-1-ignored,
matching exactly). A wrong `Certified` was also found and fixed in the same
window: `equal(ln(x^2), 2*ln(x))` returned `true` at negative `x` because a
positivity check inside canonicalization was an `f64` sign test
(`sqrt(2)*sqrt(2)` hid a cancelled zero); replaced with an exact structural
predicate. Together with the two other ADR-1410 repairs, five of ADR-1400's
original eleven distinction-incomplete-certificate findings are now fixed —
every finding ranked at or above `sturm.rs`. The weakest point moves to
`geometry_certify.rs`/`geometry_check.rs`'s minimality gap (originally ranked
#6, confirmed still open by reading current source), not to a new finding.
Separately, `cas-certificate` is **60**, not the 54/56 the dominance document
still quotes in §7.4/§9 — a same-day follow-up lane closed the remaining
five-module naming gap the document tracked as "ten modules, possibly seven."
Neither the IVT nor the EVT row-1 kernel claims (§2.2, §3) moved: both were
already conceded `cas-internal` for row 3 (§6), so the sturm.rs defect never
touched the trust anchor the row-1 dominance argument actually leans on.
Index-status: Accepted

## Context

The dominance document has now been re-verified three times in one day:
`three-domain-dominance-verification` (2026-08-31, original), the
`dominance-doc-reverify` lane (2026-09-01, ADR-1425), and this lane, dispatched
specifically because two more ADRs landed after `dominance-doc-reverify`'s
measurement base (`f7adaf7c3`) that bear directly on the document's IVT/EVT
sections: ADR-1435 (the `sturm.rs` fix ADR-1425 recommended as the top
priority) and ADR-1460 (an audit of the two files ADR-1435 left unaudited).
`git merge-base --is-ancestor f7adaf7c3 <adr-1435-commit>` and the same for
ADR-1460 both confirm true — this lane's tree is genuinely newer than what
ADR-1425 measured.

## What was checked, and how

Every number below was re-run directly in this worktree (`kernel_declaration_
projection` built fresh, release; the three `axeyum-cas` test suites named
below; `validate-facts.py`), not inherited from an ADR or from the dominance
document.

1. **The IVT row's kernel claim (§2.2) is unaffected and unchanged.**
   `kernel_declaration_projection --include-constructed`: `CReal.ivt_approx`,
   `CReal.ivt_exact_root_decides_sign`, `CReal.evt_approx_max`,
   `CReal.evt_attained_max_decides_sign`, `CReal.lub_decides_em` all still
   FOUND, theorem, footprint 0 — `rows=14539 distinct_names=2851`, up from the
   document's `14297`/`2820` (ordinary growth). `CReal.le_total`/
   `CReal.lt_total` still ABSENT, with `CReal.lt_cotrans`/`CReal.apart_cotrans`
   FOUND as the positive control in the same dump. All 30 `axiom`-kind rows
   still confined to `prelude=axreal`.

2. **The row-3 CAS bridge the IVT citation names had a real defect, now
   fixed and adversarially tested.** ADR-1400 finding #5 (`sturm.rs`'s
   half-open `(lower, upper]` convention living only in prose, consumed on
   trust by `real_algebraic::verify_ivt_certificate`) is repaired (ADR-1435):
   an explicit re-derivation was added, and a forged certificate (root
   exactly at the claimed open upper bound) is confirmed in an isolated
   snapshot to be wrongly *accepted* with both the old incidental guard and
   the new guard removed, and correctly rejected with only the new guard
   restored — the standard this repository's CLAUDE.md sets for a guard to
   count as load-bearing rather than a restatement. Re-run in this worktree:
   `cargo test -p axeyum-cas --lib real_algebraic::` → **24 passed, 0
   failed**, including the three new fixtures.

   ADR-1435 itself notes the checker *as committed before the fix* was
   already sound — the defect was that its soundness rested on an incidental
   guard with no test isolating the dependency, not that a wrong verdict ever
   shipped. That is a different severity than the f64 finding below, where a
   wrong verdict genuinely did.

3. **`mvt.rs`/`extremum.rs`, sharing the same `count_real_roots_in ==
   Some(1)` idiom, are clean — for a structural reason, not luck (ADR-1460).**
   Neither file compares its own half-open isolation bracket against the
   caller's `a`/`b`; the boundary decision routes through
   `RealAlgebraic::compare_rational`, an exact bignum comparison with no
   half-open-vs-open shape to exploit. `mvt.rs` has one explicit strict-
   interiority guard (step 5), now confirmed load-bearing for *both* bounds
   (a mirrored right-bound fixture was added and verified in a snapshot to
   fail without the guard). `extremum.rs` targets a closed `[a, b]` where an
   endpoint is a legitimate answer, so the open-interval question is a
   completeness question about `critical_points`, not a soundness one about
   the reported extremum, and is guarded by two independently-sufficient
   mechanisms verified in all four combinations. Re-run: `cargo test -p
   axeyum-cas --lib mvt::` → **19 passed**; `cargo test -p axeyum-cas --lib
   extremum::` → **24 passed, 1 ignored** — both matching ADR-1460's own
   counts exactly.

4. **A wrong `Certified` was found and fixed, found incidentally while
   verifying an unrelated item.** `expand_log_over_primes`'s positivity gate
   was `evalf(e, &[]).is_some_and(|v| v > 0.0)`, inside `equal`'s
   canonicalization path. `sqrt(2)*sqrt(2)` evaluates to
   `2.0000000000000004` and is never collapsed by `simplify_radicals`, so a
   fixture `x = (sqrt(2)*sqrt(2) - 2) - 1/10^16` (exact value `-10^-16`)
   evaluated positive under `f64` and `equal(ln(x^2), 2*ln(x))` returned
   `Certified { equal: true }` — false for negative `x`, since the left side
   is a real number and the right side is not. Replaced with
   `is_certainly_positive`, an exact structural predicate that declines
   rather than guesses (costing completeness, not soundness). Re-run:
   `cargo test -p axeyum-cas --lib exact_positivity_tests::` → **3 passed**,
   including `certified_equality_does_not_rest_on_a_floating_point_sign`.

5. **`cas-certificate` is 60, not the 54/56 the dominance document's §7.4/§9
   still report.** `python3 scripts/validate-facts.py`, this worktree:
   `routes: cas-certificate=60(kernel-reconstructed=14,cas-internal=46)`. A
   same-day follow-up lane (`cas-facts-round-two`, documented in the audit
   document's own "Round two" section) re-derived which of the ten
   previously-named modules genuinely had no naming fact by checking what
   each fact's `checker_command` actually imports and exercises, rather than
   string-matching a module's basename against fact prose. The real gap
   **before** that lane's additions was five modules, not seven or ten
   (`gf2_search`, `gf2_shard`, `gosper`, `groebner_cert`, `lib`); four new
   facts closed all five (`gf2_search`/`gf2_shard` share one, since the
   `gf2_shard` re-derivation calls `gf2_search` directly). **The ten-module
   gap this document's §7 and §8 both still quote is now genuinely zero.**

## Decision

**Re-rank ADR-1400's eleven distinction-incompleteness findings again.** Five
are now fixed — every finding originally ranked at or above `sturm.rs`
(`gosper.rs`, `gf2_shard.rs`, telescoping's pointwise floor, `normalforms.rs`,
and `sturm.rs` itself) — plus the separately-found f64 sign-test bug. One more
(`ratint.rs`) is retired rather than fixed: ADR-1410 found its "dead code"
framing was itself wrong (no `#[expect(dead_code)]` exists anywhere in the
crate, and the shipped path is independently certified downstream by
`prove_derivative`), so it drops out of the ranking as a mischaracterized
non-issue.

**The current weakest point in the CAS certificate audit is
`geometry_certify.rs`/`geometry_check.rs`'s minimality gap** (originally
ranked #6), confirmed still open by reading `geometry_check.rs`'s negative-
control loop directly: it confirms a forged witness satisfies every
hypothesis and the named saturation condition and breaks some conclusion, but
never confirms every *other* named condition stays non-degenerate at that
witness — so a single witness breaking two conditions at once can be filed as
evidence for either, and `DegenerateWitness` has no field to record which.
Minimality itself (the producer's smallest-subset-first claim) is pinned only
by an out-of-tree test, not checked by the certificate at all. This sits
under the CAS-certificate route the dominance document already counts —
seventeen of the sixty `cas-certificate` facts are geometry facts (§7.4).

Ranked after it, confirmed still open by reading current source: `series.rs`'s
discarded truncation order; `lib.rs`'s `prove_derivative` half-angle fallback
(explicitly marked "did not run" in ADR-1410, distinct from the f64 finding it
sits beside); `gf2_extension.rs`'s `ExtensionTraceHankelMinor`, which still
carries no field for the trace sequence its determinant was computed from;
and the decided-negative outcomes with no certificate type at all
(`AnsatzOutcome::NotInDegree`, `groebner::ideal_contains == Some(false)`,
`ProofOutcome::NotInSaturatedIdeal`).

**Neither IVT's nor EVT's row-1 dominance claim changed, and neither was ever
at risk from the sturm.rs defect.** The dominance document's own §6 already
concedes row 3 for the analysis families is `cas-internal` — "not under the
trust anchor the dominance argument leans on." The sturm.rs bug lived entirely
inside that conceded, already-scoped-out cell; `CReal.ivt_approx`'s footprint-0
kernel claim (row 1, §2.2) is a separate theorem checked directly by the
kernel and does not consume `real_algebraic::verify_ivt_certificate` at all.
The practical effect of the fix is a strengthened row-3 cell in §4.1's IVT
family table, not a repaired row-1 claim — worth stating precisely, since
conflating the two would be a new overclaim in the opposite direction from the
one this ADR corrects.

## Consequences

- The dominance document (`09-the-dominance-claim-verified-across-three-
  domains.md`) is updated in place: a new preamble note, §8.1 (the re-ranking
  above, with its own measurements), a pointer at the `cas-certificate=56`
  passage noting it is 60 as of this lane, and a §9.1 addendum. §8's original
  ranking and §7.4/§9's `54`/`56` figures are left in place as history, per
  this document's own established practice of correcting in place rather than
  deleting.
- A lane picking up CAS certificate-repair work next should read this ADR's
  ranked list, not ADR-1400's or ADR-1425's — both are now stale on this
  specific point, in the direction of overstating how much remains at the top
  of the list.
- §5.1's deeper gate census (`semantic_falsification`, `mutation_control`,
  `circularity`, `independent_replay`) was **not** re-verified by this lane
  either — same scope limit ADR-1425 recorded, now roughly two days stale
  rather than one.
