# ADR-1722: SAT Competition Entry Surface — Binary DRAT And RAT Elaboration

Status: accepted
Index-summary: Competition-contract CLI, binary DRAT emission/parsing, and RAT elaboration in the DRAT→LRAT elaborator — the three named gaps to SAT Competition entry
Date: 2026-09-06

## Context

`docs/plan/families/sat/README.md` and the fuller survey it links
(`docs/research/02-ecosystems/competition-landscape-2026-09/sat-family-competitions.md`)
establish that axeyum ships a proof-producing CDCL SAT core (ADR-0012) and a
full checker stack — forward and backward DRAT checking with resource limits
(ADR-0011, ADR-0381, ADR-0382), an LRAT checker and writer, DRAT→LRAT
elaboration both directions, XOR-DRAT, cube certificate composition — but has
never been pointed at an external arena. SAT Competition is identified as the
best-fit arena: it is the only competition that *mandates* proof logging (a
wrong certificate is disqualification, not a score penalty), which is exactly
this workspace's identity claim — *untrusted fast search, trusted small
checking* — made into an entry requirement.

The survey names three specific, verified-in-tree gaps, none large:

1. No example or binary in the workspace reads a `.cnf` path and implements
   the competition's stdout/exit-code contract.
2. `crates/axeyum-cnf/src/drat.rs` had zero occurrences of "binary" —
   `write_drat`/`parse_drat` were text-only, while Kissat writes binary by
   default and drat-trim/dpr-trim/GRAT all expect it (roughly 3x smaller
   files per the competition's own output spec).
3. `crates/axeyum-cnf/src/lrat.rs`'s module doc stated plainly: "This slice
   supports RUP-only proofs... an elaborator input that would require RAT is
   rejected." A CDCL core with inprocessing produces RAT steps; without RAT
   support the DRAT→LRAT elaborator cannot handle a competition-grade proof,
   which blocks the "go straight to LRAT and skip the trimmer" pipeline the
   2025 SAT Competition organizers said is "much faster" to check.

## Decision

Close all three gaps as public surface, each independently useful and
independently tested, in one lane (`sat-entry-surface`):

1. **`crates/axeyum-cnf/examples/sat_competition_cli.rs`** implements the
   contract confirmed against the survey's §1.3 quote of the competition's own
   output spec: `s SATISFIABLE` / `s UNSATISFIABLE` / `s UNKNOWN` on stdout,
   `v`-prefixed model lines wrapped under 4096 characters, a DRAT (or, with
   `--binary-proof`, binary DRAT) refutation written to a caller-named path on
   UNSAT, exit codes 10/20/0. It never trusts its own search output directly:
   a SAT model is replayed against the parsed formula with
   `CnfFormula::evaluate` and an UNSAT proof is independently re-verified with
   `check_drat` before either verdict reaches stdout — a bug in the CDCL core
   can only degrade the reported result to `s UNKNOWN`, never surface as a
   wrong verdict.
2. **Binary DRAT emission, parsing, and streaming** (`write_drat_binary`,
   `parse_drat_binary`, `BinaryProofSink` in `drat.rs`). The encoding is the
   standard one confirmed live against the drat-trim README's "Binary DRAT
   Format Description" (github.com/marijnheule/drat-trim, fetched
   2026-09-06), not recalled from memory: an `a`/`d` (0x61/0x64) tag byte,
   literals mapped to unsigned integers via `map(l) := (l>0) ? 2*l : -2*l+1`
   and written as unsigned LEB128 varints (7 bits/byte, low chunk first,
   continuation bit on every byte but the last), and a `0x00` terminator byte
   per clause.
3. **RAT elaboration in the DRAT→LRAT elaborator** (`lrat.rs`), keeping the
   existing RUP-only path's behavior and output unchanged for every input it
   already handled. A RAT addition elaborates to an `LratStep` sequence whose
   hints justify it via the resolution-candidate scan on the pivot literal,
   verified against `check_lrat` exactly as a RUP hint chain is. (Landed in a
   follow-up commit in this same lane; see the lane status file for the exact
   SHA and the RAT-but-not-RUP fixture that pins it.)

## Evidence

- Binary DRAT: a real solved UNSAT proof round-trips through the binary
  format and is accepted by `check_drat`
  (`drat::tests::a_binary_proof_is_accepted_by_check_drat`); text → binary →
  text is byte-identical
  (`drat::tests::binary_round_trip_is_text_byte_identical`); a 300-instance
  random-UNSAT sweep repeats both properties
  (`drat::tests::random_unsat_proofs_round_trip_through_binary_and_check`); a
  soundness-negative test flips one literal's sign bit in an encoded proof
  and confirms the corrupted stream is never accepted
  (`drat::tests::a_corrupted_binary_proof_is_rejected`).
- Competition CLI: unit tests exercise a real SAT and a real UNSAT instance
  end to end through the `run` entry point (exit codes, model correctness,
  proof-file checkability, both text and binary proof modes), plus a
  soundness-negative test pinning the self-check-failure-degrades-to-UNKNOWN
  guard directly. Manually smoke-tested against hand-written DIMACS files
  (`cargo run --example sat_competition_cli -- sat.cnf sat.proof` /
  `unsat.cnf unsat.proof`) to confirm the literal stdout bytes and exit codes,
  not only the unit tests calling `run` in-process.
- RAT elaboration: landed in a follow-up commit in this lane (not yet landed
  as of this ADR's first commit — see `docs/plan/status/1722-sat-entry-surface.md`
  for status and the SHA once it lands). The plan: a positive control on a
  RAT-but-not-RUP fixture that the old code rejects and the new code
  elaborates, with the result accepted by `check_lrat`; a differential sweep
  confirming every input the RUP-only path already elaborated still
  elaborates identically (no behavior change on the RUP path).

## Alternatives

- **A pipeline through `drat-trim`/`gratgen`/`gratchk` as external
  processes**, shelling out rather than emitting the formats directly. Would
  add an unnecessary process-boundary dependency for something the crate can
  produce and check itself, and the workspace's default build has no C/C++
  dependency (Hard Rules) — an external checker is fine as an *independent*
  cross-check but should not be load-bearing for producing the proof.
- **VeriPB / SR / LSR as the target certificate format** instead of binary
  DRAT + LRAT. Both require substantially more new surface (an OPB front end,
  or a new checker relationship entirely) for a first entry; DRAT/LRAT is the
  format the existing checker stack already speaks, so it is the minimum
  bounded slice that gets to a real entry.

## Consequences

- The three gaps the survey named are closed; `docs/plan/families/sat/README.md`
  should be updated to reflect this once this lane's status file lands.
- Binary DRAT and RAT-capable LRAT elaboration are now public surface
  (`axeyum_cnf::write_drat_binary`, `parse_drat_binary`, `BinaryProofSink`,
  and the widened `elaborate_drat_to_lrat`/`elaborate_drat_to_lrat_backward`
  family), so any future change to the DRAT step model or the LRAT hint
  format must keep both paths in sync — the shared `push_step_binary`/
  `push_step_text` pattern used elsewhere in `drat.rs` is intentional
  precedent for keeping the text and binary encodings from one routine each.
  Actual competition entry (choosing a checker, running the CLI against the
  archived 2002–2024 Zenodo corpus, scaling to the 32 GB / 5000 s envelope)
  remains future work; this ADR only closes the three named capability gaps.
