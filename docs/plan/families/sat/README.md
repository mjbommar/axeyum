# Family: propositional SAT

**State:** we compete here at the library level and have never entered the
competition. The gap is smaller than it was assumed to be.

## What we already ship

Verified in-tree on 2026-09-06: forward and backward DRAT checking, streaming
variants with resource limits and progress reporting, an LRAT checker and
writer, DRAT-to-LRAT elaboration both forward and backward, XOR-DRAT, and cube
certificate composition. The native CDCL core emits DRAT by construction.

## What is missing, specifically

Three items, each verified in the tree rather than assumed:

1. **No competition entry point.** No example takes a `.cnf` path and
   implements the competition's stdout and proof-file contract.
2. **Binary DRAT is absent.** `crates/axeyum-cnf/src/drat.rs` contains zero
   occurrences of "binary". The competition's own output specification puts
   binary proofs at roughly three times smaller.
3. **The LRAT elaborator is RUP-only.** Its module documentation states that
   an input requiring RAT is rejected — and RAT additions are what inprocessing
   produces.

None is large, and no new format is strictly required to enter: the standard
checkers consume DRAT directly.

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
