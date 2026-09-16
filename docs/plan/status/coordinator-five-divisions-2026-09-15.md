# coordinator-solver — the five worst divisions, traced end to end against the references

<!-- plan-section: lane-status -->

Status: **in progress**. Five Opus trace lanes are merged and pushed; four
build lanes followed, two merged, one shipped ON, two closing out. The frame
is the 16-division board (200 files each) and the Tier 1 ledger sweep on
`db31113fa`; the references are z3 4.13.3 and cvc5 1.3.4 on the same lists.
Bitwuzla does neither arithmetic nor quantifiers and is not a reference here.

## The traces (all `proposed`, all merged)

| division | ours / best ref | ADR | what the trace found, against the table's row |
|---|---|---|---|
| QF_NRA | 117 / 187 | 2110 | two gaps: **45 of 70 decided by z3's CAD engine, 44 in < 1 s** (we enumerate every cell; z3 builds one per conflict); 22 are an atom-capacity bucket CAD does not help |
| QF_LRA | 107 / 166 | 2111 | the 40 "aborts" were a dense tableau (1.62 G cells for 147 K nonzeros); sparse now, 0 of 40 decide; 33 of 93 nobody decides at 24 s; theory propagation 19 per 836,531 decisions |
| QF_NIA | 84 / 144 | 2112 | the clause estimate counts a circuit z3 never builds, and it does not matter: z3's blast arm decides 1 of 116; z3 wins by a redundant lemma portfolio (no class load-bearing on ≥ 15) |
| UFLIA | 86 / 144 | 2113 | we find the instances (98.2 % of z3's terms already in our ground set) and discard them: `rej_nocontext` is 100 % of 2.1 M rejections; UFLIA has zero e-matching fixpoints |
| AUFDTLIRA | 119 / 176 | 2114 | "mbqi datatype declines" misattributed on 16 of 17; MBQI's loop never ran on 132 of 134 (prenex shape guard); z3 refutes 44 of 55 cores with both quantifier engines off |

Two blanks filled: z3 on the Tier 1 lists gets UFNIA 94 (ours 54) and AUFLIRA 197 (ours 178).

## The builds

| lane | ADR | result | ships |
|---|---|---|---|
| NRA-SINGLE-CELL | 2121 | one-cell-per-conflict CAD; full arm +6/0 on QF_NRA; sat-only arm **+4 / 0 stable losses / 0 flips**, every gain an exactly-replayed model | **`single-cell-sat` ON — QF_NRA 117 → 121** |
| LRA-PROPAGATION | 2122 | implied-bound propagation into the SAT core; sized at 24.5 % of tracked decisions, 0 on the median file; A/B 0 gains, 1 stable loss, +35 % time | OFF |
| QUANT-ACTIVATION | 2120 | nested universals activate by assignment; `rej_nocontext` 33,090 → 0 at scale; 1,200-row A/B −1 (1 stable gain, 1 stable loss); 53-core census running to name the next block | OFF |
| NIA-GROEBNER-GATE | — | the 8/8/8 admission ladder decides **0 of 116 at every level up to unbounded** | nothing |

## What the day says

Capability gaps that trace to one named mechanism moved (QF_NRA); the ones
that trace to "the reference does many things redundantly" (QF_NIA) or "the
mechanism is right and the corpus does not pay" (UFLIA's activation, QF_LRA's
propagation) did not. Every non-shipping lever has an A/B and a reason; every
ADR corrects at least one inherited number, including the briefs' own.

## Corrections worth keeping

- Four lanes were killed mid-work by an account spend limit; all resumed from
  disk with nothing lost. A lane's worktree and its /nas3 sweeps outlive the
  agent.
- Three push batteries died 17 s in with no step named; the hook now has an
  ERR trap and a named `step_seconds` failure.
- A finished lane's A/B shards kept running on cores I had given to the next
  lane; check the hosts, not the lane's claim, before assigning cores.
- Two lanes' first controls were vacuous (a population that could not decide;
  a column computed at the outermost node of a `let` tree); both caught by the
  lanes themselves and kept, labelled.
