# Lane: drat-evidence-route — route the `unsat` evidence path off the quadratic forward DRAT checker

<!-- plan-section: lane-status -->

**Your lane's block (`landed`, drat-evidence-route, 2026-08-28).**

**The question.** Why did the evidence/certificate path call `check_drat` — the
forward reference checker, superlinear in proof length — when
`check_drat_backward` and `elaborate_drat_to_lrat_backward` (ADR-0382, ~66x)
had existed since 2026-08-12? Was there a deliberate reason?

**The answer: no. It is precedence, not a decision.** ADR-0382 was written to be
additive ("`check_drat` must not change, because it is the reference; the new
checker must be additive") and its item 9 explicitly deferred re-basing the LRAT
elaborator as "an obvious follow-on ... deliberately not in this slice". The
follow-on was never taken. `git log -L` dates the accepting call sites in
`evidence.rs` and `proof.rs` to **2026-06-13**, two months before the fast engine
existed. No ADR, comment or test pins them. The backward engine is meanwhile used
throughout the campaign tooling, `cube.rs`, `weighted.rs` and half a dozen
examples — everywhere except the certificate route.

**Why the naive fix was still wrong.** Swapping in `check_drat_backward` at the
accepting sites is exactly what ADR-0382 refused, and for a good reason: it moves
the trusted base from a few dozen readable lines to ~2,700 lines of watched
literals and clause arenas. Speed bought with assurance is not a trade this
repository makes.

**What landed instead (ADR-0613): the fast engine became a producer.**
`certify_unsat_via_lrat` runs `elaborate_drat_to_lrat_backward` as an
**untrusted** emitter of antecedent hints, then has `check_lrat` — small,
search-free, linear — verify those hints against the formula directly. A
`Certified` is discharged by `check_lrat` alone, so a bug anywhere in the
backward engine yields a decline, never a wrong `unsat`. The trusted base does
not grow; it **shrinks**, from a checker that searches for a refutation to one
that is handed it. `check_drat_backward` appears only in *rejecting* position
(the DRAT conjunct in `UnsatProof::recheck`), where it can reject and never
accept. The forward reference is untouched and remains the accepting authority
whenever the LRAT route declines (a RAT lemma, or a checking budget too small for
a stage that cannot be interrupted).

**Measured, `smtcomp_cli --evidence --progress`, release, contended host:**

Detail moved to [`../notes/187-drat-evidence-route.md`](../notes/187-drat-evidence-route.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | drat-evidence-route | `certify_unsat_via_lrat`: the backward engine emits LRAT hints (untrusted), `check_lrat` verifies them (trusted, search-free) — fp8 evidence 25m46s -> 5.0 s and fp16 never-finished -> 125 s, with no move of the trusted base (ADR-0613) |
