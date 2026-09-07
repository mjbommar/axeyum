# Family: Boolean optimization and counting

MaxSAT, model counting, QBF and pseudo-Boolean. **State: not entered, and no
input format is implemented.**

| Arena | Format | Present in tree? | Proof logging in that arena |
|---|---|---|---|
| MaxSAT | WCNF | **no** (zero occurrences workspace-wide) | none required |
| Model counting | CNF + counting semantics | no | none required |
| QBF | QDIMACS / QCIR | **no**, despite 37 quantifier modules | none required; no verified checker exists in any proof assistant |
| Pseudo-Boolean | OPB | **no** | optional certified tracks, VeriPB |

## The strategic reading

**Proof logging is mandatory in exactly one competition, and it is not one of
these.** All four have mature certification research and organizers who have
said in print that they want it; none requires it. Pseudo-Boolean went from
zero certified entrants before mid-2024 to six in 2025, which is the shape of
an arena about to tip.

That makes this family a **standing opportunity rather than a current
target**: entering one of these with certificates by default would be
distinctive in a way that entering SAT (where certificates are table stakes)
would not.

## Practical notes

- The reference pseudo-Boolean checker is now Rust and permissively licensed,
  but requires a newer compiler than our floor of 1.88.
- The strongest QBF solver of two recent years is also Rust.
- One evaluation in this family was cancelled in 2025, so "the competition"
  is not a reliable annual fixture across all four.

## Owning document

[The survey](../../../research/02-ecosystems/competition-landscape-2026-09/sat-family-competitions.md)
