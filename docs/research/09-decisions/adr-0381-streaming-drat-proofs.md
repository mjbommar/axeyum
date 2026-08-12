# ADR-0381: Streaming DRAT proof emission and checking

- Status: proposed
- Date: 2026-08-12
- Deciders: (pending review)

## Context

The proof-producing CDCL core (`crates/axeyum-cnf/src/proof_sat.rs`,
ADR-0012) accumulated its entire DRAT proof in RAM as a `Vec<DratStep>`
for the whole search, and returned it in `ProofSolveOutcome::Unsat`. Every
learned clause and every `reduce_db` deletion appended a heap-allocated
`Vec<CnfLit>` that was never released before the verdict. The trusted
checker `check_drat` (ADR-0011) likewise took `&[DratStep]`, so the whole
proof had to exist as a value before it could be verified.

That is fine at query scale and fails at search scale. Two measurements
from the Rado campaign
([`docs/plan/claim-ledger-and-rado-frontier-2026-08-12.md`](../../plan/claim-ledger-and-rado-frontier-2026-08-12.md),
"Product findings from the axeyum-only recomputation"):

1. **Item 4 — emission.** On `F_226` (35,858 clauses) the single-run
   driver was **OOM-killed at 27.6 GiB RSS after ~2.5 h**, with the proof
   vector as the dominant consumer. The kissat oracle solved the same
   instance streaming a 2.4 GB proof to disk with flat memory. Until the
   core can stream, search-scale single-run proofs need either a
   large-memory host or the cube decomposition (whose workers free each
   per-cube proof after checking).
2. **Item 5 — checking.** `check_drat` is forward-checking and does not
   scale in *time* to search-sized proofs (a 1.2M-step proof runs for
   tens of minutes). Its *memory* profile, however, is already bounded by
   the active clause set, not by the proof: the only reason it needed the
   whole proof in RAM was its `&[DratStep]` signature. The time problem is
   a separate, still-open question (backward/core-first checking, or
   decomposition); this ADR does not address it.

So the emission side needed a design change and the consumption side
needed only an honest signature.

Constraints this has to respect: determinism is a public API promise;
`solve_with_drat_proof`, `_within` and `_with_limits` are consumed
elsewhere in the workspace and must not change signature or behavior; no
`dyn` dispatch in the search loop; no C/C++ dependency; `unsafe_code`
denied.

## Decision

Introduce a **proof sink** as the emission boundary, and a **step
iterator** as the consumption boundary, in `axeyum-cnf`. Additive: no
existing signature changes.

1. **`trait DratSink`** — `add_clause(&mut self, &[CnfLit])` and
   `delete_clause(&mut self, &[CnfLit])`, each returning
   `Result<(), ProofSinkError>`. A sink is *pure output*: no field of the
   search and no branch of it reads the sink back, so the trajectory is
   identical for every implementation. Failure is **reported, never
   panicked**.
2. **`ProofSinkError`** — a small value type carrying an
   `std::io::ErrorKind` plus a message, with `From<std::io::Error>`. It is
   `Clone + PartialEq + Eq` because it is carried inside solver outcomes,
   which are; `std::io::Error` is neither.
3. **Two sinks.** `VecProofSink` collects `Vec<DratStep>` — exactly
   today's behavior, and infallible. `TextProofSink<W: io::Write>` writes
   the standard textual DRAT format straight to a caller-chosen writer,
   with its own `BufWriter`, so the core's proof footprint is a fixed
   buffer whatever the search costs.
4. **One formatting routine.** `write_drat` and `TextProofSink` share a
   private `push_step_text`, so a streamed proof is byte-identical to the
   serialization of the equivalent `Vec` proof *by construction*, not by
   two implementations agreeing. (A test pins it anyway.)
5. **The core is generic over its sink** — `Cdcl<'sink, S: DratSink>` with
   `sink: &'sink mut S`. `S` is monomorphized, so emission is a direct
   call in the search loop. The existing entry points keep their exact
   signatures and delegate through a `VecProofSink`.
6. **New entry point**
   `solve_with_drat_proof_streaming(formula, deadline, max_conflicts,
   sink) -> StreamingProofOutcome`, where `StreamingProofOutcome` mirrors
   `ProofSolveOutcome` except that `Unsat` carries nothing (the proof went
   to the sink) and a `SinkFailed(ProofSinkError)` variant reports a sink
   that refused a step.
7. **A refused step yields no verdict.** `SinkFailed` is *undecided*, in
   the same class as `Interrupted` and `ResourceOut`. A refutation whose
   proof could not be recorded is not a checked `unsat`, and the steps the
   sink did accept are a prefix, not a refutation. The impossible
   `SinkFailed` branch on the infallible `VecProofSink` path maps to
   `Interrupted` rather than panicking — an unreachable branch must not be
   able to produce a wrong verdict *or* abort a caller.
8. **`check_drat_streaming(formula, impl Iterator<Item = Result<DratStep,
   DratError>>)`** verifies a proof one step at a time, with memory
   bounded by the active clause database. `check_drat` becomes a thin
   caller of it over a slice, so there is exactly one checking algorithm.
   A producer error (a truncated or unreadable stream) aborts the check:
   an unreadable proof is never treated as a verified one.
9. **`DratTextReader<R: io::BufRead>`** yields those steps from textual
   DRAT, one line at a time, sharing `parse_drat`'s line parsing (extracted
   as a private helper; `parse_drat`'s signature is unchanged). It fuses at
   the first failure so a checker cannot spin on a failing reader. Read
   failures are reported as `DratError::Parse` — `DratError` is public and
   matched exhaustively elsewhere in the workspace, so widening it for I/O
   was not worth a breaking change.

## Consequences

- A search-scale refutation can now be produced with flat memory:
  `TextProofSink` over a file gives the reference-solver behavior the
  campaign's item 4 asked for. The 27.6 GiB failure mode is a
  configuration choice, not a property of the core. Measured on
  pigeonhole fixtures (release build, this repo): PHP(8) emits 6,153 steps
  / 99,797 literals, so the `Vec` route holds ~596 KB of proof
  simultaneously; PHP(9) emits 48,271 steps / 1,043,100 literals, ~5.7 MB
  — **9.6× for one extra pigeon**, which is the growth curve that ends at
  27.6 GiB on a real instance. The streaming route's proof footprint on
  both is the fixed 64 KiB buffer (310,711 B and 3,184,660 B written).
- `check_drat_streaming` + `DratTextReader` verify a proof that never
  exists in RAM as a value. This removes the *memory* limit on checking;
  the *time* limit (item 5) is untouched and remains the reason
  cube-and-conquer decomposition is the practical route at this scale.
- The `Vec` path is unchanged for every existing consumer, and now goes
  through the same code as the streaming path, so the two cannot drift.
  It also drops one clone per learned clause (the old code cloned the
  learned clause into the proof vector).
- `Cdcl` is generic, which costs one monomorphization per sink type used
  in a build. That is the price of no `dyn` in BCP's caller.
- The sink boundary is where a future LRAT/Alethe streaming writer, a
  compressor, or a proof-splitting router would attach, without touching
  the search.

## Alternatives considered

- **A compact in-RAM proof arena** — store all steps in one flat
  `Vec<CnfLit>` with `(offset, len, is_delete)` headers, mirroring the
  clause arena the core already uses. This would cut the per-step
  allocation overhead substantially (probably several-fold on the measured
  instance) and is **compatible with this design** — it is exactly what a
  future `ArenaProofSink` would be. It was not chosen *as the answer*
  because it only moves the constant: the proof still grows without bound
  with the search, so a hard enough instance still dies. Streaming solves
  the unbounded case; the arena remains an attractive addition for callers
  who do want the proof in memory.
- **Return an iterator/generator of steps from the solver** — inverts
  control, forcing the search to be resumable mid-conflict. Enormous
  complexity for the same effect a sink achieves with a function call.
- **`&mut dyn DratSink`** — one code copy instead of one per sink, at the
  cost of an indirect call on every learned clause. Rejected: the emission
  point sits in the conflict path, and this project has an explicit
  ID/arena/monomorphization style.
- **Always write text, and parse it back when a `Vec` is wanted** —
  removes the sink trait but makes the common small-query path pay
  formatting and parsing, and makes proof identity depend on a round trip.
- **Deleting steps from the in-RAM proof when `reduce_db` deletes the
  clause** — unsound as a memory strategy: a DRAT proof's earlier
  additions are still needed to justify later steps, and the deletion
  lines themselves must be *in* the proof for a checker to replay it.
