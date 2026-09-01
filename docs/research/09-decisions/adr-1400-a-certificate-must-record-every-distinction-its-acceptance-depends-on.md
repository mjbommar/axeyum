# ADR-1400: a certificate must record every distinction its acceptance depends on — or re-derive it

Date: 2026-09-01
Status: Accepted
Lane: `cas-ledger-audit`

Index-summary: An audit of all 55 `axeyum-cas` modules against the fact ledger. Both headline numbers in the deficiency it answers are wrong in opposite directions: the `40 of 53` certificate-carrying modules is an unmasked grep counting doc-comment prose (masked: **27 of 55**, and a second differently-shaped query gives 23), while `19` CAS facts counts a FILENAME convention against a real route count of **48** — so nine telescoping facts existed for a subsystem reported as having none. Joined per module, the actual gap is **13 modules with a certificate surface and no naming fact**, not 34. Verdicts: 9 reconstruct today (every one PARTIAL — the kernel re-checks a strictly weaker claim, residues named), 8 could reconstruct with a named missing piece, the rest `cas-internal` with a reason. The decision this ADR records is the rule the audit's eleven findings share: **a certificate must carry every distinction its own acceptance depends on, either as a recorded field or by having the checker RE-DERIVE it — and re-derivation is strictly stronger, because a field can be forged.** Two in-tree models are named (`check_cas_ideal_certificate` rebuilds `lower`/`real_strict` rather than reading them; the SOS format expresses strictness as a numeric margin with a committed zero-margin control) against eleven violations, the sharpest being `gosper.rs`'s three acceptance modes recorded nowhere and `gf2_shard.rs` accepting an exhaustion theorem by incrementing a counter. Six facts landed, each with a checker verified to fail in both directions; the route goes 48 → 54.
Index-status: Accepted

## Context

[The CAS certifies far more than the ledger
records](../11-design-review/2026-09-01-the-cas-certifies-far-more-than-the-ledger-records.md)
logged a deficiency: 40 of 53 `axeyum-cas` modules carry a certificate surface
and 19 facts record any of it. This lane was dispatched to audit every module,
record what reconstructs, and label the rest.

The full audit — per-module verdicts, every one citing a file and a function
that was read — is
[2026-09-01-cas-certificate-reconstruction-audit.md](../11-design-review/2026-09-01-cas-certificate-reconstruction-audit.md).
This ADR records the two decisions that came out of it.

### First: the deficiency's numbers were wrong in opposite directions

Both are the same class of error this repository keeps making — a string query
answering a narrower question than the one asked — and it is worth having both
directions on record, because the two errors nearly cancelled and the cancelling
made the gap look about twice its real size.

**The numerator counted prose.** `certificate|Certificate|fn verify|fn check_`
unmasked over `src/*.rs` gives 41 of 55. This crate's doc comments discuss
certificates at length in modules that emit none — `series.rs:11-13` and
`orthopoly.rs:16-18` both say outright that they are compute operations with no
certificate attached, and both match the pattern. Masking Rust comments and
string literals gives **27 of 55**; a second, declaration-shaped query
(`struct`/`enum` named `*Certificate`/`*Cert`/`*Witness`, or
`fn verify_*`/`check_*`/`certify_*`/`validate_*`) gives 23. Two shapes agreeing
is the check one grep does not have.

**The denominator counted a filename convention.**
`ls artifacts/facts/ | grep -c '^F-cas-'` gives 19 and is a correct answer about
filenames. The ledger's own notion is `proof_route`, and
`scripts/validate-facts.py` prints it: `cas-certificate=48`. The 29 missed are
named for their mathematics — nine telescoping facts, seventeen geometry, four
GF(2). That falsifies the deficiency's specific claim that Zeilberger creative
telescoping has "no ledger fact at all": `telescoping.rs` and
`telescoping_check.rs` are each named by nine settled facts.

Joining both sides per module gives the number that answers the question:
**13 certificate-carrying modules with no naming fact**, all named in the audit.

### Second: the eleven findings share one shape

The audit read every certificate-carrying module for the failure
`nra_monomial_bound_cert` shipped — a producer distinguishing `M < k` from
`M ≤ k` with a certificate storing only `k`, so the checker could not tell them
apart and would have accepted a forged refutation of a satisfiable query. Eleven
instances, ranked in the audit. The four sharpest:

- **`gosper.rs:153`** has three acceptance modes. Modes A and B return after the
  full exact zero-test certified `S(k+1) − S(k) ≡ term`. Mode C (`:194`) returns
  *because that test did not certify it*, on the smaller reduced identity alone
  — and `certifies_telescoping:371` returns `false` both for `Unknown` and for a
  positively decided **disagreement**, which `:194` does not separate. The three
  returns are indistinguishable `CasExpr` values.
- **`gf2_shard.rs:245`** accepts `ShardStatus::Exhausted` — "every sparse
  candidate at this degree was reducible", a genuine negative theorem — with the
  entire body `summary.exhausted += 1`. The default `axeyum-gf2-check-shard`
  invocation exits 0 on a fabricated exhaustion claim; `--require-all-found` is
  opt-in.
- **Telescoping**: `confirm_telescoping:571-583` detects the certificate
  denominator vanishing at a sampled integer point, **skips the pointwise check
  there**, and still returns `Verified`. The count is in `CheckReport` and
  `telescoping_json::write_options:218` does not serialize it, and there is no
  floor on `pointwise_samples` at all. A certificate whose pointwise layer ran
  **zero** times and one confirmed at all 75 grid points produce byte-identical
  files and the identical verdict.
- **`normalforms.rs:399`,`:423`** verify `U·A·V = D` and `det = ±1` and nothing
  about the normal form: `(I, A)` passes as a Hermite form, and the
  invariant-factor divisibility chain — the entire point of Smith — is asserted
  nowhere outside a unit test.

And two places where the distinction *is* carried, which is what makes the rule
below statable rather than merely aspirational.

## Decision

**A certificate must carry every distinction its own acceptance depends on. It
may do so in either of two ways, and they are not equally good.**

1. **Re-derivation (preferred).** The checker recomputes the distinguishing
   quantity from data the certificate cannot choose, and compares. This is
   strictly stronger than recording, because a recorded field can be forged and
   a re-derivation cannot.

   In-tree models: `check_cas_ideal_certificate`
   (`axeyum-solver/src/cas_certificate.rs:559-580`) rebuilds `lower` and
   `real_strict` from the hypothesis itself rather than reading them, so the
   producer's `Candidate { floor, real_strict }` distinction survives without
   ever being stored. `gf2::check_irreducible_certificate:1806` recomputes the
   prime divisors of the degree and requires **exact vector equality** with the
   supplied list, so a certificate that *drops* an obligation is rejected rather
   than silently under-checked. `gf2_artifact::validate:203-211` recomputes the
   half-degree bound as `degree / 2` rather than reading the serialized
   `tail_degree_bound`, with the parsed artifact re-rendered and byte-compared.

2. **Recording, with a committed control.** Where re-derivation is impossible —
   the quantity is a free choice of the producer — the distinction becomes a
   field, and a negative-control fixture must exist that differs *only* in that
   field and is rejected.

   In-tree model: the SOS format has no strictness flag, because a sum-of-squares
   identity gives `≥ 0` and never `> 0`. Where strictness is needed the barrier
   certificate carries a numeric **margin** (`B ≤ −1`, `B ≥ 1`, not `B < 0`,
   `B > 0`), so a zero-margin certificate is a different *file*, and
   `artifacts/instances/sos/negative-controls/barrier-zero-margin.json` is the
   committed control. The Lyapunov certificate does the same with separate
   `lower`/`upper`/`decay` fields and four boundary controls.

**A distinction carried by neither route is a defect, and the certificate is
`cas-internal` until it is fixed** — regardless of whether a kernel bridge could
in principle exist for it. A certificate the kernel could re-check but that
cannot state which of three modes produced it is not ready to be reconstructed;
it is ready to be repaired.

**Corollary for the ledger.** A `cas-certificate` fact whose evidence rests on a
distinction the certificate cannot express must say so in `axiom_footprint`,
naming the distinction. Two of the six facts this lane landed do exactly that:
`F:cas-ratint-horowitz-x-over-x-minus-one-squared` discloses that
`verify_horowitz`/`verify_log_terms` are `#[expect(dead_code)]` and are not on
the shipped integration path, and `F:cas-smith-normal-form-two-six-twelve`
discloses that the producer's self-check would accept `(I, A)` as a Hermite
normal form.

**And the audit rule for finding these, which mutation testing cannot supply.**
Mutation testing measures the guards you *have*; a guard never written has
nothing to delete. Nine guards in `nra_monomial_bound_cert` were each killed by
exactly one test and the module was still unsound. The technique that works:
**for every case the PRODUCER distinguishes, write an adversarial fixture over an
instance where every other guard passes. If the certificate cannot express the
distinction, that impossibility is the finding.** `ratint.rs`'s two fixtures —
`wrong_degree_b_is_vacuous_without_the_properness_guard:734` and
`non_dividing_d2_slips_past_without_the_divisibility_guard:810` — are the model,
and each independently establishes its mutant is *genuinely wrong* (the second
evaluates both sides at `x = 3`) before asserting rejection.

## Consequences

- The audit's `COULD RECONSTRUCT` column now has a second axis. Several of those
  eight modules need a certificate repair *before* a kernel bridge would be
  worth building — reconstructing a certificate that has already lost a
  distinction reconstructs the loss. `boolean_circuit.rs` and `gf2_tensor.rs`
  are the two that need no repair: both replay exhaustively and both name a
  counterexample (`BooleanCircuitCheck::Failed { input, expected, observed }`,
  `Gf2TensorCheck::Failed { coordinate, expected, observed }`).
- **`series.rs` gets a concrete, cheap fix and it is already written twenty files
  away.** `series(expr, var, order)` takes the truncation order as an input and
  returns a bare `CasExpr` recording neither the order nor that a remainder was
  discarded, while `TaylorCertificate` (`taylor.rs:186`) has `n` as a field and
  claims nothing beyond order `n`. The crate's own doc examples
  (`series.rs:191`, `:328`) match `Certified { equal: true }` on the equality of
  two order-3 truncations while the surrounding text reads as an identity.
- This ADR does **not** add a gate. Every one of the eleven findings is a
  property of a Rust type's field set, and no mechanical check over the ledger
  can see them. Adding a checker that could not detect any of the eleven would
  be exactly the defect this repository cares most about — a checker that cannot
  fail — arriving through the door marked "we should gate this". The audit
  document is the artifact; the rule above is what a reviewer applies.
- Recorded here rather than left implicit, because it is the second time in one
  session a headline number came from prose rather than from the crate: **a
  survey grep over this crate must mask comments, or run a second query of a
  different shape and check the totals agree, or state its number as
  "grep-estimated, unmasked" so the next reader knows what it is worth.**

## Alternatives considered

**Add 34 facts and close the gap by volume.** Rejected, and the deficiency
document already argued against it. Recording a certificate that has lost a
distinction records the loss with the ledger's authority behind it. Six facts
whose checkers were each verified to fail in both directions are worth more than
thirty that are not — and the audit's real output is the eleven findings, which
no number of facts would have produced.

**Require every CAS certificate to reach the kernel.** Rejected as
ADR-0601 already does: `cas-internal` with a reason is a complete result. Several
of the modules here are `cas-internal` for reasons no amount of work removes —
the seven-module GF(2) cluster would need a whole new prelude, not a translator,
and `lib.rs::integrate`'s witness is a polynomial over *atomized* transcendental
heads that the kernel has no notion of.

**Gate on "every certificate struct has a `mode` field."** Rejected as
cargo-culting the fix rather than the rule. Five of the eleven findings are
better fixed by re-derivation, which adds no field at all, and `cas_poly.rs`
shows a certificate that stores *neither* of the two things its producer
distinguishes and is correct because the checker rebuilds both.
