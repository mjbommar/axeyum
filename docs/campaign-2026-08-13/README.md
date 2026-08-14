# Campaign evidence — 2026-08-13/14

The primary record behind the three roadmap strands. **Every number in
[`refactor-2026-08/`](../refactor-2026-08/README.md),
[`mathematics-2026-08/`](../mathematics-2026-08/README.md) and
[`formalized-math-2026-08/`](../formalized-math-2026-08/README.md) traces to a
file here.**

Eleven agents plus a coordinator ran for roughly twenty-four hours against open
mathematics and the stack that produces it. These are their working records,
copied verbatim from the shared workspace at
`/nas3/data/axeyum/frontier-2026-08-13/`.

## Why this is in the repository

The plans cite measurements. A measurement whose evidence lives only on a NAS
is a claim, not a measurement — the same defect the claim ledger exists to
prevent. This is 0.8 MB of prose; the ~265 MB of CNFs, DRAT proofs, cover
ledgers and logs it refers to stays on the NAS and is regenerable.

## What each lane produced

| lane | subject |
|---|---|
| `coordinator` | the campaign diary, cross-lane findings, and the action lists that became the strands |
| `agent-a-offdiag-schur` | 32 cells of `S(3;s,t,u)`, 16 new values; the wrong-`unsat` symmetry trap |
| `agent-b-rado741` | `R_4(5(x-y)=4z) = 741` closed; adaptive tree covers; the branch-point finding |
| `agent-c-rado-akb2` | the `a^k` law refuted at k=5; `R_4(5,2) = 625`; the 6.6× checking blow-up |
| `agent-d-lean-bridge` | Lean's own kernel accepting an axeyum development; the printer defects |
| `agent-e-vdw` | van der Waerden; the per-colour extension carrying to a second family in 78 lines |
| `agent-f-rewrite-preconditions` | preconditions enforced where rewrites apply; 57 rules, not 5 |
| `agent-g-drat-memory` | proof-checking memory 8× → 1.5×; three campaign numbers corrected |
| `agent-h-proof-reconstruction` | reconstruction frontier 53k → 4.57 M hints; the `cargo fmt` blind spot |
| `agent-i-cas-bridge` | the CAS ideal-refuter; six of seven guards found removable under a strong mutation |
| `agent-j-misconceptions` | 148 misconceptions censused; a negative-control suite whose guard caught its author |
| `agent-k-lemma-splitting` | hypothesis minimisation; the k=3 blocker re-diagnosed |

Each lane carries up to four files: `DIARY.md` (append-only, in order, including
what broke), `FEEDBACK.md` (roadmap items cited by file and line), `RESULT.md`
(the standing table of what was established) and `FRAGMENTATION.md` (what the
integration bought, and where it did not help).

## How to read them

The diaries are the valuable part, and they are written to be read in order —
several of the campaign's best findings only make sense as a sequence, because
an earlier belief turned out to be wrong. Notable examples, all recorded rather
than tidied away:

- a "defensive guard" documented in two places and **never implemented**;
- `which lean` returning nothing, read as a fact about the machine;
- two declaration counts that were ~10× low because the declarations are built
  by a helper rather than a struct literal;
- a control suite where **six of seven guards were removable with every test
  still green**, found by its own author after publishing the flattering number;
- a lower bound written as a known value — twice, in opposite directions, by
  different parties, twelve hours apart.

The corrections are kept beside the errors deliberately. A record that shows
only conclusions cannot be audited.
