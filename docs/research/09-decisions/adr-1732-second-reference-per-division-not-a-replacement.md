# ADR-1732: A named second reference solver per division, never a replacement

Status: accepted
Date: 2026-09-07

## Context

`bench-results/PARITY.md` measures axeyum against **cvc5** in every division on
the board. cvc5 is a legitimate, serious entrant everywhere it is used as a
reference — but it is not the SMT-COMP 2026 division leader everywhere. Computed
directly from `results-sq-2026.json.gz` (see
[`docs/research/02-ecosystems/competition-landscape-2026-09/reference-solvers-and-proof-formats.md`](../02-ecosystems/competition-landscape-2026-09/reference-solvers-and-proof-formats.md)
§1.2):

| Logic | Leader | 2nd | Where cvc5 sits |
|---|---|---|---|
| QF_LRA | OpenSMT (502) | Yices2 (484, 3rd) | not in top 3 |
| QF_LIA | QiuQi (1262) | OpenSMT (1229) | not in top 3 |
| QF_UF | OpenSMT / Yices2 / cvc5 all 1104/1104 | — | tied for 1st |
| QF_RDL | Yices2 (216) | cvc5 (210) | 2nd |
| QF_UFLIA | SMTInterpol (291) | Yices2 (289) | not in top 2 |
| QF_UFLRA | Yices2 (507) | SMTInterpol (506) | 3rd (506, tied) |

No existing `PARITY.md` entry is false — each one names cvc5 as `reference` and
its measured version. But reading "axeyum is at N% parity" as "axeyum is close
to the frontier" is wrong on five of these six rows: the frontier is a
different, stronger solver, and the stated gap against cvc5 understates the
real distance to the division's actual winner.

`scripts/parity-run.sh`'s own header names the failure mode this ADR has to
avoid: *"retargeting mid-report from the division winner to an easier peer"*.
Adding a second reference has to make that harder to do by accident, not
easier — a script that let a caller point `PARITY_REFERENCE_OPTS`-style at an
arbitrary binary path would be exactly that knob with a new name.

## Decision

1. **A second reference is additive, never a substitute.** cvc5 stays the
   default reference for every division exactly as configured today. Nothing
   about an unset `PARITY_SECOND_REF` changes.
2. **The mapping from (division, name) to binary is a hardcoded table inside
   `scripts/parity-run.sh`, not a caller-supplied path.** `PARITY_SECOND_REF`
   selects a *name* (`yices2`, `smtinterpol`); the script alone decides which
   binary that resolves to and refuses the combination outright for any
   division not listed in the table above. This is the concrete mechanism
   that keeps "retargeting to an easier peer" out of reach: a caller cannot
   point the second-reference slot at a weaker solver by picking a flag value,
   because the only values that resolve to anything are the ones this ADR's
   table names, and each entry is a solver that is documented, from the same
   §1.2 computation, to be at or above cvc5 in that division.
3. **Every ledger entry states which reference it used, unambiguously.**
   `scripts/parity-run.sh` stamps a second-reference entry's title with
   `SECOND REFERENCE (<name>)` (parallel to the existing `EVIDENCE MODE`
   stamp) and adds an explicit note that the entry is not a like-for-like
   replacement of the division's default cvc5-referenced entry — it is a
   separate, named measurement against a separate, named solver. The per-file
   sidecar path is likewise suffixed (`<division>--<name>.tsv`) so a
   second-reference sweep can never overwrite the default sweep's per-file
   detail.
4. **Divisions where the true leader (or a solver ahead of cvc5) could not be
   obtained keep their existing cvc5-only entries and say nothing new.** No
   ledger entry is edited or removed; PLAN.md's append-only rule for
   `PARITY.md` is unchanged.

Scope for this ADR, per the solvers actually pinned (see
[`docs/plan/status/second-reference.md`](../../plan/status/second-reference.md)
for provenance): `yices2` for QF_LRA (2nd, ahead of cvc5), QF_UF (tied 1st),
QF_RDL (1st); `smtinterpol` for QF_UFLIA (1st). QF_LIA (QiuQi/OpenSMT) and
QF_UFLRA (not currently on the board) are not covered — neither leader nor
runner-up solver was obtainable within this task's effort budget, and
QF_UFLRA has no committed benchmark list yet.

## Evidence

- The 24s-budget, per-division computation in §1.2 of the reference-solver
  survey, reproducible from the SMT-COMP 2026 raw result dump without running
  any solver.
- `yices-2.7.0-x86_64-pc-linux-gnu-static-gmp.tar.gz` from the SRI-CSL
  `yices2` GitHub release, sha256 verified against the digest GitHub's own
  Releases API reports for the asset.
- SMTInterpol built from `ultimate-pa/smtinterpol` commit
  `1f55c1b9bfc724468b18e0e1868e4606e0285fb9` (`ant smtinterpol.jar`); no
  GitHub Releases exist for this project (confirmed: only two ancient tags,
  `2.1` and `2.5`), so a pinned source commit plus a deterministic build is
  the closest available equivalent to a numbered release, and both are
  recorded.

## Alternatives

- **Replace cvc5 as the reference wherever a stronger solver exists.**
  Rejected: it would silently invalidate every historical `PARITY.md` entry's
  comparability (a ratio computed against a different denominator solver is
  not the same number), and the append-only ledger rule exists precisely so a
  number never quietly changes meaning underneath its own history.
- **A free-form `PARITY_REFERENCE_BIN=<path>` override.** Rejected: this is
  the retargeting knob the script's header already warns about, just moved
  one layer up — anyone could point it at a weak binary and call the result a
  "second reference". The named table is the guard.
- **Skip QF_LIA and QF_UFLRA silently.** Rejected as a decision worth hiding;
  recorded here and in the status doc instead, so a later lane does not
  re-attempt Yices2 on QF_LIA believing it would show a leader-level result —
  per §1.2 it is not the leader or runner-up there.

## Consequences

- Easier: a reader of `PARITY.md` can now see, for four divisions, both "how
  far behind the reference we actually use in the default protocol" and "how
  far behind the division's true SMT-COMP 2026 frontier" — on the same
  benchmark list, same machine class, same budget.
- Harder: the parity ledger now carries two solver identities per some
  divisions; any future tooling that reads `PARITY.md` programmatically must
  key off the entry title (`SECOND REFERENCE (…)` vs. plain), not just the
  division name.
- Revisit if OpenSMT (QF_LIA, QF_LRA leader) or QiuQi (QF_LIA leader,
  non-public) ever become obtainable on this fleet — the table in this ADR is
  the place to extend, and the QF_LIA row above records why it is not yet
  populated.
