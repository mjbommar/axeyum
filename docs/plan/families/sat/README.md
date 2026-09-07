# Family: propositional SAT

**State:** we compete here at the library level. The three named entry-surface
gaps closed 2026-09-06 (ADR-1722, lane `sat-entry-surface`); actual entry
(picking a checker, running against the archived corpus, scaling to the
competition's resource envelope) remains future work.

## What we already ship

Verified in-tree on 2026-09-06: forward and backward DRAT checking (text and
now binary), streaming variants with resource limits and progress reporting,
an LRAT checker and writer supporting both RUP and RAT additions, DRAT-to-LRAT
elaboration both forward (RUP+RAT) and backward (RUP core lemmas; RAT core
lemmas still declined, ADR-0382 — an engine-specific gap, not a format one,
see ADR-1722), XOR-DRAT, and cube certificate composition. The native CDCL
core emits DRAT by construction. A competition-contract CLI
(`crates/axeyum-cnf/examples/sat_competition_cli.rs`) reads a `.cnf` path and
implements the SAT Competition Main track's stdout/exit-code contract with a
self-check on every verdict (a SAT model is replayed, an UNSAT proof is
independently re-checked before either is ever printed).

## What was missing, and closed 2026-09-06 (ADR-1722)

Three items, each verified in the tree rather than assumed, before this lane's
work landed:

1. **No competition entry point.** Closed:
   `crates/axeyum-cnf/examples/sat_competition_cli.rs`.
2. **Binary DRAT was absent.** Closed: `write_drat_binary`/
   `parse_drat_binary`/`BinaryProofSink` in `crates/axeyum-cnf/src/drat.rs`,
   encoding confirmed live against the drat-trim README rather than recalled.
3. **The LRAT elaborator was RUP-only.** Closed for the *forward* elaborator
   (`elaborate_drat_to_lrat`): `LratStep::AddRat` carries a pivot literal and
   one resolution-candidate hint block per active clause containing its
   negation, verified by `check_lrat` with no search — same trust story as
   the RUP path. The *backward*, core-first elaborator
   (`elaborate_drat_to_lrat_backward`/`certify_unsat_via_lrat`, ADR-0382)
   still declines a RAT core lemma; that engine's own chain recovery was not
   extended in this slice.

No new format was strictly required to enter: the standard checkers consume
DRAT directly.

## Why it matters more than a ranking

**SAT is the only competition that mandates proof logging.** A wrong
certificate is a disqualification rather than a score penalty. It is therefore
the one external venue where our identity — untrusted fast search, trusted
small checking — is the entry requirement rather than a claim about ourselves.

## Where our engine actually stands

On identical CNF the native core needs about the same number of conflicts as
Kissat and processes them roughly 1.5x slower. On the 113-file p4dfa slice at
20 s: Kissat 11, CaDiCaL 10, native 6. That ratio, not the competition
placing, is the number S8 moves.

## Open experiment worth running

No authoritative published figure exists for the cost of DRAT proof logging in
CaDiCaL or Kissat. We are positioned to measure it, and it is publishable.

## Owning documents

- [The survey](../../../research/02-ecosystems/competition-landscape-2026-09/sat-family-competitions.md)
- ADR-1703 (the native core is the engine; the former adapter is a yardstick)
- ADR-1722 (competition CLI, binary DRAT, RAT elaboration in the forward
  DRAT→LRAT path)
