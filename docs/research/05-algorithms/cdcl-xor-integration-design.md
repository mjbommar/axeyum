# CDCL(XOR) integration — design (slice 6 of the multiplier-wall path)

Status: **design note (resolves the proof/trust crux before implementation).**
The static-preprocessing slices of path 2 are measured-exhausted on the curated
multiplier wall (see
[multiplier-sat-wall-and-algebraic-paths.md](multiplier-sat-wall-and-algebraic-paths.md));
the remaining lever is **in-search Gaussian** — XOR reasoning interleaved with the
CDCL trail. The algorithmic foundation exists and is brute-force-validated:
`axeyum-cnf::gf2` (GF(2) Gaussian), `xor_extract` (sound gate recovery), and
`xor_search::xor_implications` (XOR propagation under a partial assignment →
implied literals + conflicts with reasons). This note designs how that primitive
plugs into a CDCL loop, and **answers the open question that gates implementation:
the soundness/proof story**, because XOR reasoning is *not* resolution and so does
not fit the existing DRAT proof core for free.

## The integration shape (CryptoMiniSat-style, the references are in-tree)

References: `references/cryptominisat/src/gaussian.cpp`, `gausswatched.h`,
`packedmatrix.h`, `packedrow.{h,cpp}`, `matrixfinder.cpp`, `xorfinder.cpp`.

The standard structure, mapped onto axeyum's pieces:

1. **Setup (once per solve).** Run `extract_xors` on the CNF to recover the XOR
   gate system; this is the matrix CMS's `matrixfinder` builds. Variables shared
   between the XOR system and the clause database are the coupling.
2. **Propagation fixpoint (per decision level).** After clause unit propagation
   reaches a fixpoint, call the XOR engine with the current trail:
   `xor_implications(constraints, num_vars, trail_assignment)`.
   - `Implied{lits}` → enqueue each forced literal on the trail with its XOR
     *reason* as the antecedent (the analogue of a propagating clause). Re-run
     clause UP; iterate clause-UP ⇄ XOR-prop until neither enqueues anything.
   - `Conflict{reason}` → a conflict at the current level; hand the reason to
     conflict analysis exactly like a conflicting clause.
   The primitive recomputes from the trail today (a fresh `Gf2System` per call);
   the *efficient* form is the incremental watched-row matrix (`gausswatched.h`),
   a later optimization — correctness first, with the recompute primitive.
3. **Conflict analysis (1-UIP).** The existing `proof_sat` analyzer resolves the
   conflict clause against trail antecedents to a 1-UIP learned clause. XOR
   reasons are clauses (the negation of the reason assignment ∨ the implied
   literal), so they slot into the same resolution *as clauses* — **but whether
   those reason clauses are themselves justified is the crux below.**
4. **Backtrack.** The XOR primitive is stateless w.r.t. the trail (it reads the
   assignment slice), so backtracking is just truncating the trail; the
   incremental-matrix version will instead undo row operations (`gausswatched`).

## The crux: XOR reasoning is not resolution, so the DRAT proof breaks

`solve_with_drat_proof` returns `ProofSolveOutcome::Unsat(Vec<DratStep>)` and the
whole project promise is **trusted small checking**: every `unsat` is either
independently checked (DRAT/LRAT/Alethe) or an explicit, ledgered trust hole
(Hard Rules; ADR-0007 demoted rustsat-batsat's UNSAT to a trust hole until a proof
route existed).

An XOR-derived reason clause `(¬a ∨ ¬b ∨ … ∨ ℓ)` (from a Gaussian-implied literal)
is a logical consequence of the XOR gates, hence of the original clauses — but it
is **generally not RUP** (reverse-unit-propagation derivable) from the clause
database. That is the entire reason XOR/Gaussian *beats* CDCL: it derives facts
resolution cannot cheaply reach. So emitting those reason clauses as `DratStep::Add`
produces an **invalid DRAT proof** — `check_drat` would (correctly) reject it, and
silently emitting it anyway would be a soundness lie.

There is no cheap fix inside DRAT. The honest options:

- **(A) Search-only + ledgered trust (recommended first cut).** Run XOR reasoning
  as untrusted *search acceleration* and **do not** emit a DRAT proof when an XOR
  reason participated in the refutation. Instead record a new trust-ledger entry
  `TrustId::XorGaussian` on that `unsat`, exactly as ADR-0007 did for batsat. The
  assurance backing the hole is the brute-force-validated soundness of
  `xor_implications` (conflict-soundness + implication-soundness over all
  completions). This is bounded, honest, and demotable. Precedent: `SatRefutation`,
  `LraDpll`, `Ackermann` are all current ledgered holes.
- **(B) DRAT with extended XOR steps.** A DRAT/DPR variant that can justify XOR
  reasoning (e.g. PR/SR clauses, or recording the Gaussian row operations). Heavy,
  and the in-tree `check_drat` does not implement it (RUP+RAT only). Out of scope.
- **(C) Algebraic / PAC certificate (the real demotion path).** This *is* path 3:
  model the XOR steps as polynomial (Nullstellensatz/PAC) derivations and check
  them with an algebraic checker. The XOR fragment is the easy sub-case of the
  full algebraic engine, so an XOR-only PAC emitter is a natural intermediate that
  later subsumes into path 3. This is how `TrustId::XorGaussian` gets demoted from
  a hole to a checked route — the same arc BitBlast/Tseitin/SatRefutation took from
  trusted to Alethe-checked.

**Decision:** ship (A) first — search-only XOR acceleration with a `XorGaussian`
trust-ledger entry and **no** false DRAT — then pursue (C) as the demotion. This
keeps the Hard Rule intact (`unknown`/ledgered-trust, never a wrong `unsat`) and
matches the project's established "trust then demote" pattern. A new ADR records
the trust hole (mirroring ADR-0007), and `trust.rs` + the golden trust-ledger
gain the `XorGaussian` id (the 6th hole).

## Where SAT (not UNSAT) gets a free pass

For **`sat`** results there is no proof obligation — the model replays against the
original terms (the existing soundness gate). So XOR acceleration on satisfiable
instances is *already* fully sound with zero trust cost: the found assignment is
checked by evaluation regardless of how the search reached it. The trust hole is
**only** for XOR-assisted `unsat`.

## Bounded first implementation slice (next, fresh context)

A self-contained **XOR-aware DPLL** in `axeyum-cnf` that decides a `CnfFormula`
plus its `extract_xors` system:

- Trail + clause watched-literal UP (a small DPLL; or reuse the `proof_sat`
  propagation scaffolding) interleaved with `xor_implications` to a fixpoint.
- 1-UIP-free first: chronological backtracking is enough for a correctness-first
  decider (no learned clauses yet → no proof-clause question for the first slice;
  it returns `Sat(model)` / `Unsat` only).
- **Differential test** against `solve_with_rustsat_batsat` on random CNFs,
  weighted toward XOR-rich instances (planted gates): same SAT/UNSAT verdict on
  every jointly-decided formula; every `Sat` model satisfies the formula. This is
  the soundness gate before any trust-ledger wiring.
- Then: wire into the solver dispatch as an *optional* accelerator on the
  bit-blasted path, `unsat` carrying the `XorGaussian` ledger entry; measure the
  curated multiplier slice (`DISAGREE=0` invariant) — the first chance to crack
  `mulhs*`/`stp_samples`/`calypto` that the preprocessing slices provably cannot.

Learned clauses + 1-UIP (and with them the proof-clause question and the
incremental watched-row matrix) come after the correctness-first decider proves
the integration is sound and the measurement shows it helps.

## Bottom line

The XOR engine is built and validated; the only thing that gated *integration*
was the proof story, and it is now decided: **XOR-assisted `unsat` is a bounded,
ledgered trust hole (`XorGaussian`), not a false DRAT proof, demotable later via an
algebraic/PAC certificate (path 3).** `sat` is already free. The next code slice
is a correctness-first XOR-aware DPLL, differential-tested, then measured on the
curated multiplier wall — the first technique in the stack that *can* reach those
instances.
