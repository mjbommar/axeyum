# Certifying a reduction is a soundness-bug finder — two caught (2026-07-08)

Status: **methodology finding.** While extending the `Fpa2Bv` (FP→BV, ADR-0023)
trusted-reduction ledger with a per-query **certified sub-case** (tasks #69–#73), the
act of *adversarially certifying* each operator surfaced **two genuine wrong-verdict
soundness bugs** that the existing gate — thousands of unit tests, the committed
corpora, and the five Z3-differential fuzzes — had not. This note records the pattern,
because it argues for treating "add a certificate" as a first-class soundness technique,
not just an assurance add-on.

## The sub-case being built

The global `TrustId::Fpa2Bv::is_certified()` stays `false` (not every FP query is
certifiable), but a per-run [`TrustStep::certified`] flag reports a certified sub-case: a
`Fpa2Bv` `unsat` whose FP operators are **all** *faithful by construction* carries
`certified: true`. The allow-list grew to 16 non-arithmetic ops: `fp.neg`/`fp.abs`, the
five category predicates, `fp.isNegative`/`fp.isPositive`, the five comparisons, and
`fp.min`/`fp.max`. Each addition required a **rigorous faithfulness argument at every
constructible width** — and that requirement is what did the finding.

## Why certification finds what fuzzing and corpora miss

A differential fuzz or a corpus asks: *does axeyum agree with Z3 on the inputs I
generated?* A certificate asks the strictly stronger question: *is the reduction faithful
on **every** input and **every** width?* Answering the second forces you to enumerate the
circuit's regimes and its parametric assumptions — and the soundness bugs lived exactly
in the regimes the generators never sampled:

1. **`u128` sign-mask overflow on FP formats wider than 128 bits** (caught assessing the
   comparison certification). The generic FP circuits build a sign mask as
   `1u128 << (width - 1)`; for a format wider than 128 bits (a legal, if exotic,
   `(_ FloatingPoint eb sb)` with `eb + sb > 128`) that shift overflows — a panic in
   debug, a *silently-wrong mask → corrupt circuit → possibly-wrong verdict* in release,
   and (since `fp.neg`/`fp.abs` were already certified) a wrong `certified: true`. No
   corpus and no fuzz used a >128-bit FP sort. Fixed at the root: `FloatFormat::check`
   rejects `width > 128` → a graceful `unknown`, never a panic/wrong verdict/false
   certificate.

2. **Internal-fresh-symbol aliasing** (caught assessing the `fp.min`/`fp.max`
   certification). The unspecified opposite-sign-zero result of `fp.min`/`fp.max` uses a
   *fresh sign bit*, minted as a named symbol interned by name in the **user-shared**
   namespace. A crafted script `(declare-fun axeyum_fp.min.signzero.0.1 () (_ BitVec 1))`
   (`.`/`!` are legal SMT-LIB symbol chars) could **alias** that bit, pin the unspecified
   sign, and force a wrong `unsat` — and the same class sat under ~40 other reduction
   helpers (`!div_`, `!euf_atom_`, `!dt_*`, …). No fuzz declares a reserved-looking helper
   name. Fixed with an arena **internal-symbol namespace** (`declare_internal` /
   `find_internal_symbol`, disjoint from user `declare` / `find_symbol`): the same name
   string resolves to two distinct `SymbolId`s, so a user declaration can never alias an
   internal helper. All ~40 minting sites were migrated; the quantifier round-trip
   (`!q.…` symbols, deliberately on the user path with a `find_symbol` uniqueness loop)
   was left untouched and stays green.

## The takeaway

- **Certification is adversarial by nature and complements sampling.** The certificate's
  universal claim ("faithful at all inputs/widths") is a *proof obligation*; discharging
  it honestly forces the edge cases — exotic widths, reserved namespaces, unspecified-
  result placeholders — that fuzzers (which sample) and corpora (which are "normal"
  inputs) structurally under-cover. Both bugs were wrong-verdict-class and both predated
  the certification work (the aliasing one was reachable *uncertified* on the solve path).
- **Conservative certification is the discipline that made this productive.** Every
  candidate op was assessed with a "certify only if the argument is airtight, else report
  the gap" rule (delegated to worktree-isolated reviewers). Two candidates returned
  DO-NOT-CERTIFY with a precise gap → each gap was a real bug → fix the bug → the op
  becomes certifiable. A "certify optimistically" posture would have shipped both false
  certificates instead.
- **Recommendation.** When extending any trusted-reduction ledger (the `Fpa2Bv`,
  `IntBlast`, `Ackermann`, `ArrayElim`, `XorGaussian` sub-cases), budget the review as
  bug-finding, not paperwork: enumerate the reduction's regimes and its width/namespace
  assumptions, and treat any "can't fully justify" as a probable latent defect.

## Backlinks

- Tasks #69/#70/#70a/#70c (the 16-op sub-case), #71 (min/max assessment → the aliasing
  find), #72/#73 (the arena internal-symbol firewall), and the width-guard fix.
- Ledger discipline: `crates/axeyum-solver/src/trust.rs` `is_certified` doc.
- The still-open deep arc: `Fpa2Bv` **arithmetic** (rounding) needs the by-construction
  rounding-circuit-generator proof for genuine global `is_certified()→true` (#70 part B).
