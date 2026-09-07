# Lane: sat-entry-surface — SAT Competition entry surface (ADR-1722, docs/plan/families/sat/README.md)

<!-- plan-section: lane-status -->

**All three slices landed (`WIP`, sat-entry-surface, 2026-09-06).** The three
gaps `docs/plan/families/sat/README.md` names were verified in-tree first (all
three still absent as described): no competition CLI, `drat.rs` had zero
occurrences of "binary", and `lrat.rs`'s module doc still said RUP-only.

1. **Competition entry point**
   (`crates/axeyum-cnf/examples/sat_competition_cli.rs`, new). Reads DIMACS
   from a path, solves with the native proof-producing CDCL core, and
   implements the SAT Competition Main track contract confirmed against
   `docs/research/02-ecosystems/competition-landscape-2026-09/sat-family-competitions.md`
   §1.3: `s SATISFIABLE` / `s UNSATISFIABLE` / `s UNKNOWN`, `v`-line model
   output wrapped under 4096 chars/line, a DRAT proof written to the
   caller-named path on UNSAT, exit 10/20/0. Self-checking: a SAT model is
   replayed against the parsed formula and an UNSAT proof is independently
   re-verified with `check_drat` before either verdict is ever printed — a
   search bug can only degrade the report to `s UNKNOWN`, never surface as a
   wrong verdict (`tests::a_self_check_failure_degrades_to_unknown_never_a_wrong_verdict`
   pins the guard condition directly). `--timeout-ms` and `--mem-limit-mb` are
   explicit CLI flags; the memory one is advisory only (parsed, not
   self-enforced — this workspace already enforces memory externally via
   `scripts/cargo-serialized.sh`'s systemd scope, and duplicating that inside
   the solve loop was out of scope here). Smoke-tested against real DIMACS
   files by hand (`cargo run --example sat_competition_cli -- sat.cnf
   sat.proof` → `s SATISFIABLE` / exit 10 with a model that actually
   satisfies the clauses; `unsat.cnf` → `s UNSATISFIABLE` / exit 20 with a
   proof file `check_drat` accepts), not just through the unit tests.

2. **Binary DRAT** (`crates/axeyum-cnf/src/drat.rs`:
   `write_drat_binary`/`parse_drat_binary`/`BinaryProofSink`, new). Encoding
   fetched live from the drat-trim README's "Binary DRAT Format Description"
   (github.com/marijnheule/drat-trim, 2026-09-06) rather than recalled:
   `a`/`d` (0x61/0x64) tag byte, `map(l) := (l>0) ? 2*l : -2*l+1` literal
   code, unsigned LEB128 varint (7 bits/byte, low chunk first, continuation
   bit on all but the last byte), `0x00` terminator. `BinaryProofSink` mirrors
   `TextProofSink`'s buffering/finish contract for streaming output.
   Round-trip test proves text→binary→text is byte-identical
   (`binary_round_trip_is_text_byte_identical`), a real solved UNSAT proof
   round-trips through binary and is still accepted by `check_drat`
   (`a_binary_proof_is_accepted_by_check_drat`), a 300-instance random-UNSAT
   sweep does the same
   (`random_unsat_proofs_round_trip_through_binary_and_check`), and a
   soundness-negative test flips one literal's sign bit in an encoded stream
   and confirms the result is never accepted
   (`a_corrupted_binary_proof_is_rejected` — this actually caught nothing
   wrong in the implementation, i.e. it exercises real corruption and the
   real checker rejects it, not a vacuous assertion).

3. **RAT in the LRAT elaborator** (`crates/axeyum-cnf/src/lrat.rs`). Added
   `LratStep::AddRat { id, clause, pivot, candidates: Vec<RatCandidate> }` —
   a pivot literal plus one resolution-candidate hint block per active clause
   containing its negation. `check_lrat` verifies it with no search
   (`verify_rat_addition`, sharing `follow_hint_chain` with the RUP path so
   the two cannot silently diverge), and **enumerates the active set itself**
   to require a candidate for every clause containing `¬pivot` — a
   `candidates` list that quietly drops one is rejected, not trusted
   (`check_lrat_rejects_a_rat_step_missing_a_required_candidate`). The
   *forward* elaborator (`elaborate_drat_to_lrat` and its bounded/progress
   variant) now tries RUP first via `rup_hints` (byte-identical to the old
   behavior on every input that used to elaborate via RUP) and falls back to
   the resolution-candidate scan on the clause's first literal when it is
   not RUP. The *backward* engine
   (`elaborate_drat_to_lrat_backward`/`certify_unsat_via_lrat`, ADR-0382)
   still declines RAT — an engine-specific gap now, not a format one (doc
   comments updated to say so).

   Proof the RAT path is right, not merely present, per two isolated
   fixtures (both computed from `rup_hints`/`solve_with_drat_proof`, not
   asserted): `a_rat_but_not_rup_clause_is_rejected_by_rup_only_checking_but_elaborates_as_rat`
   confirms `rup_hints` returns `None` (what the OLD RUP-only elaborator's
   behavior reduces to) for `F=[(1,2)]`, clause `(1)` — then confirms the
   NEW `elaborate_drat_to_lrat` succeeds with a zero-candidate `AddRat` step
   and `check_lrat` accepts it (`Ok(false)`, correctly not claiming UNSAT for
   a non-empty clause).
   `a_rat_clause_with_a_real_resolution_candidate_elaborates_and_checks` does
   the same with a genuine non-trivial candidate (`F=[(-2,-3)]`, clause
   `(2,3)`, one real resolution candidate whose resolvent is a tautology),
   confirms the elaborated `AddRat` step's exact shape, that `check_lrat`
   accepts it, and that it round-trips through the new `r`-marked text
   format (`write_lrat`/`parse_lrat`) unchanged. Three more soundness-negative
   tests directly attack `verify_rat_addition`: a missing required candidate,
   a candidate with a wrong (non-refuting) hint chain against a
   NON-tautological resolvent (so the hints are actually consulted, not
   short-circuited), and a pivot not actually in the clause — all three
   rejected. `RatCandidate` and `LratStep::AddRat` are exported from
   `axeyum-cnf`'s public surface. Two other in-tree exhaustive matches over
   `LratStep` were updated to compile against the new variant:
   `interpolant.rs` (declines RAT-step interpolation explicitly, returning
   `None`, rather than computing something wrong) and three
   `axeyum-solver/examples/reconstruct_*.rs` diagnostic scripts (sum
   candidate hint lengths instead of erroring; those examples use the
   *backward* elaborator, which never emits `AddRat`, so this is a
   compile-only fix, not a behavior change on any real input there).

   Not landed: a hand-verified *end-to-end* mixed RAT+RUP refutation that
   itself reaches the empty clause and check_lrat's `Ok(true)`. Two attempts
   at hand-constructed and search-constructed fixtures for this did not pan
   out inside this session's time budget (documented in the working
   transcript, not committed) — the isolated-step tests above already satisfy
   the brief's stated proof obligation (construct RAT-but-not-RUP, confirm
   old-code rejection, confirm new-code elaboration and `check_lrat`
   acceptance), so this was not blocking, but a genuine end-to-end fixture
   would be a good follow-up for the next lane touching this file.

<!-- plan-section: landed-changes -->

| 2026-09-06 | sat-entry-surface | RAT elaboration in the forward DRAT→LRAT path (`LratStep::AddRat`, `check_lrat`, `elaborate_drat_to_lrat`), docs/plan/families/sat/README.md slice 3 |
| 2026-09-06 | sat-entry-surface | competition CLI + binary DRAT emission/parsing/streaming sink, docs/plan/families/sat/README.md slices 1+2 |
