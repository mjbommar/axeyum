# coordinator-solver — the five worst divisions, traced end to end against the references

<!-- plan-section: lane-status -->

Status: **in progress, round three**. Five trace lanes, then two rounds of
build lanes (nine), all merged; two levers shipped ON (QF_NRA 117 → 122);
the rest ship OFF with a measured reason and a named next increment. The frame
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

## Round two (2026-09-16)

| lane | ADR | result | ships |
|---|---|---|---|
| NRA-CELL-EXACT | 2126 | exact delineability (Sturm on the cell's algebraic endpoints); `Projection` split into four causes; a Boolean clause loop lands OFF | **`unsat` half ON — QF_NRA 121 → 122**, 0 losses on pinned and held-out |
| DT-FIELD-EXPANSION | 2128 | nested field expansion: pinned **+4/0** over 600, held-out AUFDTLIRA **+1/−2** (both stable), UFDTLIRA +2/0; 0 flips over 1,000 rows | OFF — the held-out draw is the only reason |
| QUANT-GROUND-INCREMENTAL | 2124 | the cold re-solve is a seven-round schedule difference selected by `online_clauses.is_none()`; incremental session: cores +1/0, divisions −4 (1 gain / 5 stable losses) | OFF; next: let the session host arithmetic |
| LRA-WARM-BASIS | 2125 | warm basis across cubes: 40,916 from-scratch tableaux → 0, −9.2 % time, +1/−2 stable; the admission screen still counted dense cells | OFF; next: a builds-per-file screen |
| QUANT-PREPROCESS | 2127 | our skolemizer already fires on 90 of 90; z3's macro finder is net −1 on our 525 undecided (its authors disabled it for the same reason) | OFF |
| DT-GROUND-PROBE | — | ADR-2114's "ground" was z3's preprocessing: stripped files are 83 of 83 sat | correction |

Two of six were a real gain on the pinned lists; the held-out draw refused one
of them. Every non-shipping lever names what to build next.

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
