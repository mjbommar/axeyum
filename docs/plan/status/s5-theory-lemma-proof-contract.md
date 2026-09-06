# Lane: s5-theory-lemma-proof-contract — S5 proof contract under theory lemmas (docs/plan/smt-parity-plan-2026-09-05.md row S5)

<!-- plan-section: lane-status -->

**Done (`s5-theory-lemma-proof-contract`, 2026-09-06).** The contract S7 is
gated on is decided and enforced. No solver behaviour changed.

[ADR-1704](../../research/09-decisions/adr-1704-cdclt-unsat-is-two-streams-a-boolean-refutation-over-cnf-plus-enumerated-theory-lemmas.md)
adopts the slice-2 memo's option (2), two streams. A CDCL(T) `unsat` artifact
carries the CNF, the enumerated theory lemmas (each with its theory and its
theory-level explanation — a Farkas combination, a negative cycle, a congruence
chain), and a Boolean DRAT/LRAT stream over the CNF **extended by those lemmas
as additional input clauses**. `check_drat` and `check_lrat` are unchanged: the
contract is a statement about which formula they are handed, so the trusted base
does not grow by a line. Per-lemma discharge is by the theory checkers that
already exist. The lemma count is a subtraction on the artifact
(`extended.len() - cnf.len()`), never a producer-asserted field, and
`theory_lemmas_unchecked` prints beside `certified`/`checked`. A refutation
modulo N ≥ 1 lemmas is graded at a **new** `TrustId::SatRefutationModuloTheory`;
reusing `SatRefutation` would relabel a strictly weaker statement at the stronger
level, which is one of the two things the ADR forbids S7 from doing (the other:
no unlabelled theory lemma in the RUP stream). Options (1) and (3) are rejected
with reasons; Alethe/Carcara is noted as the eventual portable single-artifact
form if (1) is ever wanted.

Read from the code, not from prose. **Have a checkable per-lemma form:** LRA
(`FarkasCertificate::verify`, `crates/axeyum-solver/src/lra.rs:498` — pure
exact-rational, no search); DL, which already builds *and verifies* a
unit-multiplier Farkas object for every conflict and then **drops** it
(`dl_online.rs:1159`, `:1516`) because `TheoryExplanation` has no slot for it;
EUF, which has `ProofStep` congruence chains plus an independent re-checker
`check_congruence` (`crates/axeyum-egraph/src/lib.rs:206`, `:1311`) that the
online CDCL(T) path never calls. **Do not:** strings (`string_theory.rs:1063`
returns a bare `CheckResult::Unsat`); NIA/NRA, whose SOS/Handelman certificates
are whole-query refutations rather than per-lemma objects. So the structural gap
is one trait slot, not new proof theory — which is why S7 gains a checked
Boolean half on day one, moving every theory route from `Evidence::Unsat(None)`
with empty `trusted_steps` to `checked modulo N`.

The boundary is pinned by
`crates/axeyum-cnf/tests/theory_lemma_proof_contract.rs` (11 tests, no
production change): a three-variable difference-logic skeleton that is
**satisfiable** propositionally, plus the negative-cycle lemma. `check_drat`
and `check_lrat` reject the lemma as a derived step (neither RUP nor RAT; no
hint chain exists) and accept the identical refutation once the lemma is an
input clause. Mutation-checked on a `lane-snapshot.sh` copy, each restored and
the baseline re-confirmed at 11/11, all three runs collecting 11 tests:
disabling `is_rat`'s resolvent-RUP requirement killed **2**; accepting an LRAT
addition whose hint chain never conflicts killed **1**; deleting the lemma from
the extended input CNF killed **3**. Vacuity controls in the suite show a
genuinely RUP addition and a genuinely hinted LRAT addition over the *same*
skeleton are accepted, so the rejections are about the lemma and not about the
checkers refusing everything.

**Next for whoever takes S7:** the only structural prerequisite is a discharge
slot on `TheoryExplanation` (`crates/axeyum-solver/src/euf_egraph.rs:164`,
with `assert` at `:80` and `final_check` at `:181`). DL's already-computed
certificate is the cheapest first discharge to wire, and EUF's `check_congruence`
the second.

<!-- plan-section: landed-changes -->

| 2026-09-06 | 54a7591c3 | Pin the CDCL(T) theory-lemma proof contract at the checker boundary (11 tests, no production change) |
| 2026-09-06 | e97db1bf4 | ADR-1704: a CDCL(T) unsat is two streams, and the theory lemmas are enumerated and counted |
| 2026-09-06 | 99f19e32a | Point `docs/internals/cnf-and-sat.md`'s UNSAT-assurance text and parity-plan §3 at ADR-1704 |
