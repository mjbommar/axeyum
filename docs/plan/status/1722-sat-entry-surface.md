# Lane: sat-entry-surface — SAT Competition entry surface (ADR-1722, docs/plan/families/sat/README.md)

<!-- plan-section: lane-status -->

**Slice 1 + Slice 2 landed (`WIP`, sat-entry-surface, 2026-09-06).** The three
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

**Next up for this lane:** Slice 3, RAT elaboration in `lrat.rs`'s DRAT→LRAT
elaborator (currently RUP-only). Not started as of this commit.

<!-- plan-section: landed-changes -->

| 2026-09-06 | sat-entry-surface | competition CLI + binary DRAT emission/parsing/streaming sink, docs/plan/families/sat/README.md slices 1+2 |
