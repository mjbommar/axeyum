# Family: the certificate chain

**This family has no board row, and that is the point.** The parity board
counts decisions. This counts whether a decision arrives with something a
checker can verify. A division can reach parity while its certificates stay
empty, and nothing on the board would show it.

## The chain, and where it is whole

| Stage | Produces a checkable artifact? | Note |
|---|---|---|
| Preprocessing / rewriting | **half** | corrected 2026-09-06 — see below |
| Bit-blasting to CNF | yes | replay maps are retained by hard rule |
| Propositional search | **yes** | DRAT by construction, checked by our own DRAT and LRAT checkers |
| Theory reasoning (CDCL(T)) | **partly** | corrected 2026-09-07 — five routes emit, the front door attaches, and the number is readable from a sweep |
| Model lifting (`sat`) | yes | every `sat` replays against the original term |

## The open hole: preprocessing — narrower and sharper than this page said

**Corrected 2026-09-06 (ADR-1721).** This page used to say preprocessing
produces no checkable artifact. Measured, that is wrong, and the true shape is
more useful: four of the trust ledger's 14 ids are preprocessing steps
(`ArrayElim`, `Ackermann`, `IntBlast`, `DatatypeElim`), and
`ArrayElimUnsatCertificate::recheck` and `AckermannUnsatCertificate::recheck`
are real, re-checkable artifacts for the eager-elimination `unsat` sub-case.

What is open is **which half they check**. A preprocessing step's obligation is
decided by what it does to the model set: a **replacement** owes a denotation
equality, a **relaxation** owes nothing in the `unsat` direction, a
**strengthening** owes a per-constraint discharge. Both certificates genuinely
discharge the *strengthening* half — the appended Ackermann congruence set is
re-derived from an independent implementation of the schema. Both **re-derive**
the *replacement* half by re-running the same producer, which `trust.rs:89-95`
already names in its own words: that "proves *determinism* but not
*faithfulness* — a stably-wrong circuit … survives re-derivation", against a
real shipped wrong-`unsat` (`af6c8bf`). That is why all four ids are
`is_certified() == false`.

Two things really are absent. `RewriteTestRoute::ProofObligation` has **one**
occurrence in the whole workspace — its own declaration — so the replacement
obligation has no producer anywhere. And the crate's one runtime semantic check,
the ADR-0408 denotation guard, is on by default and *refuses* a rewrite it
cannot justify — but it samples 4 assignments over Bool/BV only (so it is
structurally blind to the array-sorted terms read-over-write rewrites), its
verdict is read by `axeyum-bench` and nothing else, and its refusal is swallowed
at `auto.rs:1744` as an ordinary decline, indistinguishable from a timeout.

**The literature does not hand us a solution.** The published form of our own
two-stream contract states that it does not cover preprocessing. And the one
mature production system in this space needs a dedicated rewrite-rule language
and a proof-granularity flag to manage it, which says a from-scratch producer
loses coverage on rewrite steps before anywhere else. Design the manifest for
that rather than discovering it.

## The theory half: five routes emit, and the number is now readable

ADR-1704 adopted the two-stream design — a propositional refutation checked
over the CNF extended by the enumerated theory lemmas, with the lemma count
read off the artifact and a distinct trust level for a refutation modulo N
lemmas. The boundary is pinned by tests.

**Corrected 2026-09-07.** This section used to say no route emits it. Five now
run the proof-producing core: `dl_online` (S7b), plus `euf_egraph`,
`lra_theory`, `lia_theory` and `string_theory`. `produce_evidence` attaches the
step on its bare-`unsat` arms, and `smtcomp_cli --evidence` prints
`trusted=<n>[:<label>[+],…]` so the ledger can be counted across a division
instead of asserted per query from a test.

Measured the same day, first 40 files of each committed parity list, 8 s
budget, release binary, `taskset -c 0-7`, zero verdicts contradicting
`declared`:

| division | `unsat` | carrying a trust step | of those, ADR-1704 |
|---|---:|---:|---:|
| QF_IDL | 3 | **3** | **2** (`sat-refutation-modulo-theory`; the third is a lemma-free `sat-refutation`, certified) |
| QF_LIA | 4 | 4 | 0 — pre-existing `farkas+`, newly VISIBLE rather than newly produced |
| QF_UF | 16 | 1 | 0 |
| QF_LRA | 0 | 0 | 0 — nothing decided at this budget; not a certificate statement |

**QF_UF is the standing gap and the next slice.** Fifteen of its sixteen
refutations arrive as `unsat-bool-euf-online`, whose evidence producer attaches
no trusted step at all, so moving `euf_egraph` onto the proof-producing core
does not surface: those refutations never reach the arm that reads the artifact
channel. Moving a route is necessary and is not sufficient — every producer
that can answer `unsat` ahead of the fallback needs its own attach.

Three routes are still on `CdclT`: `uflra_online` and `uflia_online` (both read
`CdclT::theory_propagations()`, which on the native core lives behind
`TheorySolveOptions::collect_layer_stats`) and `ufbv_online` (the one client of
the unported incremental protocol).

Per-lemma checkability, read from the code rather than from prose: linear real
arithmetic has an exact-rational Farkas verifier; difference logic already
*builds and verifies* a Farkas object per conflict and then discards it because
the explanation type has no slot for it; the e-graph has congruence chains plus
an independent re-checker the online path never calls. Strings and the
nonlinear theories have whole-query refutations rather than per-lemma objects.
**The structural gap is one trait slot, not new proof theory.**

## Prior art — now cited (2026-09-06)

ADR-1704 carries a Prior art section citing eDRAT (Hitarth, Codel, Lachnitt,
Dutertre, FMCAD 2024). The two-stream shape is **convergence, not adoption**:
ours was derived from `ArithDpllRefutation`/`LraDpllRefutation` one level up in
this tree. Five differences are recorded there. The load-bearing one is **RAT**:
eDRAT restricts its propositional checker to RUP additions and rejects RAT,
while ADR-1704 hands the unchanged `check_drat`, which accepts both. That is
safe as ADR-1704 is decided — the extended formula is fixed before checking and
every lemma is discharged or counted — but it stops being safe under eDRAT's
core-pruning optimization, so that pairing is now a recorded constraint.
`check_lrat` already rejects RAT, so the LRAT arm agrees with them by accident.

## What the cost of all this actually is

Measured externally in 2026, not speculated: a kernel-checked bit-vector
pipeline pays a **median 6.9%** for the kernel check itself and runs a **median
8.7x** slower overall than the uncertified reference. **Trusted checking is
cheap; proof-producing search is what costs.** A slice that makes checking
faster is working in the cheap half.

## Format decisions

The legacy checker format is settled as dead — its repository has not been
pushed since September 2023 and its signature set omits bit-vectors, arrays and
datatypes entirely. The live choices are the native format of the current
reference checker and Alethe for interoperability, the latter carrying a
maintenance cost because its specification describes itself as evolving.

## Open defects in this family, found 2026-09-06 and not yet fixed

Both were found by the math-department's reconstruct lane while it changed how
the sum-of-squares attestation renders, and both are in `axeyum-solver`. **They
are reported here as that lane measured them; this coordinator confirmed the
shape in the source but has NOT re-run either.** Treat the sizes as claims until
someone does.

1. **A producer's doc comment promises more than the producer delivers.**
   `evidence::produce_nra_sos_evidence` stores the Lean module with no content
   gate, under a doc comment describing a kernel-checked proof. For a fallback
   query that description is false. A doc comment is not a gate, and a producer
   that stores whatever it is handed cannot be relied on by a consumer reading
   the comment. Fix is a content gate, or a comment that says what actually
   happens.

2. **Two fixtures are named for coverage they do not provide.**
   `tests/evidence.rs::qf_nra_sos_certificate_wrapper_carries_lean_module` and
   `tests/lean_crosscheck.rs::qf_nra_sos_certificate_audit_rows_check_in_real_lean`
   are named for the wrapper path but measured to take the honest route. The
   first asserts only that a Lean module exists and carries no `sorryAx`; if the
   wrapper path broke, it would still pass. **A test whose name claims a case it
   does not exercise is worse than no test**, because it makes the case look
   covered. Fix is either a fixture that actually reaches the wrapper, or names
   that match what runs — and the durable form ties the two together by
   asserting the rendered module name, so the name cannot drift from the route
   again.

Related context: the attestation now renders as `axeyum_attested_refutation`
when its axiom footprint is non-empty, derived from the footprint rather than
chosen, so an honest reconstruction's bytes are unchanged. That change is what
made the misnaming visible.

## Next actions

1. ~~Cite the prior art in ADR-1704 and record the comparison.~~ Done
   2026-09-06.
2. ~~S7 — emit the two-stream artifact from one theory route.~~ Done: five
   routes emit and the front door attaches (2026-09-07, and see the section
   above for the measured per-division numbers).
3. ~~Fill one preprocessing obligation end to end.~~ Done 2026-09-06
   (ADR-1721 §7). **Not canonicalization** — §6 measures why: `RuleApplication`
   carries `before`/`after` but no position or order, so a checker can verify
   every step and still not verify that they compose to the output. What landed
   is an independent faithfulness witness for read-over-write
   (`witness_read_over_write`), in the shape of
   `crates/axeyum-fp/tests/fpa2bv_faithfulness.rs`. Before it,
   `ArrayElimUnsatCertificate::recheck` returned `Ok(true)` over a wrong `unsat`
   from a mutated read-over-write; after, `Ok(false)`. It is sampled, so
   `TrustId::ArrayElim` stays uncertified — evidence, not proof.
4. ~~The same witness for `eliminate_functions`.~~ Done 2026-09-07
   (`witness_function_abstraction`, wired into
   `AckermannUnsatCertificate::recheck` as step 2). **A straight port of the
   array witness did NOT catch the defect it exists for**, and the finding
   changed the design: with `eliminate_functions` mutated so every application
   of one function shares one fresh symbol, the satisfiable
   `f(a) = 1 ∧ f(b) = 2` becomes a wrong `unsat` and `recheck` still returned
   `Ok(true)` — because the two sides are compared as BOOLEANS, and
   `f(b) = 2` and `f(a) = 2` are both simply `false` at almost every sample.
   Agreement on `false` is not agreement. The witness therefore carries a
   second, STRUCTURAL count (`unnamed_applications`): every `Op::Apply` subterm
   of the originals must have an entry in the abstraction's own application
   table at that sample's argument values, which a merged or dropped
   application cannot satisfy. With it, `recheck` returns `Ok(false)`.
   **Read this before porting the witness anywhere else** — the array
   witness's success on its own mutation was partly luck about which defect
   happened to move a Boolean. Sampled, so `TrustId::Ackermann` stays
   uncertified.
5. **Attach the trust step in `check_bool_euf_online_evidence`.** Fifteen of
   sixteen QF_UF refutations carry no step for this reason alone.
6. `eliminate_int_divmod` — landed 2026-09-06; its `MAX_CONGRUENCE_GROUPS = 48`
   soundness-mode change is still not reported to the caller.
7. Retain the ADR-0408 denotation guard's verdict past the pass, and stop
   `auto.rs:1744` swallowing its refusal as an ordinary decline.

## Owning documents

- [ADR-1704](../../../research/09-decisions/adr-1704-cdclt-unsat-is-two-streams-a-boolean-refutation-over-cnf-plus-enumerated-theory-lemmas.md)
  — the theory half, plus the eDRAT prior-art comparison
- [ADR-1721](../../../research/09-decisions/adr-1721-a-preprocessing-step-owes-one-of-three-obligations-chosen-by-the-direction-it-can-break.md)
  — the preprocessing half: three obligations, chosen by the direction a step
  can break; a re-derivation is not a discharge
- [The survey](../../../research/02-ecosystems/competition-landscape-2026-09/README.md), sections 1.3-1.5
- [Evidence and checker discipline](../../../contributor-guide/evidence-and-checker-discipline.md)
