# coordinator-solver — the five worst divisions, traced end to end against the references

<!-- plan-section: lane-status -->

Status: **paused at the user's request, 2026-09-16 afternoon; rounds one to four closed, round five wound down after sizing**. Five trace lanes, four rounds of build lanes and probes (nineteen lanes), all merged; two levers shipped ON (QF_NRA 117 → 122, ADR-2121/2126); one more lever is +4 stable on the pinned list with its held-out draw unfinished (ADR-2134, OFF); every other lever ships OFF with an A/B and a named next increment. `origin/main` is `b548367ff`; local main carries the day's landings and the push runs after the final fuzz pass. The frame is the 16-division board (200 files each) and the Tier 1 ledger sweep on `db31113fa`; the references are z3 4.13.3 and cvc5 1.3.4 on the same lists (UFLIA's "144" is the z3∪cvc5 union; cvc5 alone is 142). Bitwuzla does neither arithmetic nor quantifiers and is not a reference here.

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

## Round three (2026-09-16)

| lane | ADR | result | ships |
|---|---|---|---|
| QUANT-SESSION-ARITH | 2130 | the session hosts the arithmetic theory; 366 atoms move into it; cores 15 → 17, 1 stable gain (the same file every lever moves) | OFF |
| QUANT-INSTANCE-PROBE | — | handed z3's own proof instances, our ground ladder refutes 6 of 7 reconstructable cores in ~107 ms; 46 % of z3's instances are nested instantiations | the block is **instance reach**, not ground refutation |
| QUANT-INSTANCE-SELECT | 2133 | the briefed selection lever already ships and acts on 0.3 % of rejections; a generation ladder reaches its check on 31 of 53 cores and refutes at none | OFF; the refutation is absent from our set, not buried |
| LRA-WARM-SCREEN | 2132 | builds-per-file screen: strictly better than the arm it screens (1/1 vs 1/2), admitted set predicted 51 of 51; the held-out loss is the shape the lever wins on, so the axis is wrong; −9.2 % is ¾ skipped linearization; fill-in grows the warm tableau 21× | OFF |
| NRA-CLAUSE-LOOP | 2131 | certified `unsat` for the Boolean loop; A/B on 800 files (QF_NRA, QF_NIA, QF_LRA control, QF_NRA held-out): 0 stable gains, 0 stable losses, 0 flips, the one mover was ambient (NEITHER-DECIDES at 3×/arm); 10 of 16 admissible files reach the theory and are refused by the single-cell frontier (algebraic sample worth 5); the shipped checker had two false-reject bugs, fixed; the treatment arm was confounded with the sat half and is rebased | OFF; merged `931e9d173` |
| NRA-CLAUSE-LOOP (follow-up) | 2131 | the clause-loop z3 fuzz asserted the withholding ADR-2131 removed and went red on main for the eight fuzzes the lane had not run; it now adjudicates every certified `unsat` against z3 and re-reads the certificate: 1,500 instances, 373 decided (5 `unsat`), 373 agreements, 0 disagreements; one generated refutation was refused by the loop's own checker and dropped | merged `fd5d64e70` |

Four lanes on the quantified divisions each removed a real block and moved
one core; the probe then showed why: the six instances z3's proof uses are
not among the ~1,473 we admit. QUANT-REACH-DIFF is classifying, per core,
where each of z3's instances is lost (never matched / matched-rejected /
nested) — that histogram is the next build's brief.

## Round four (2026-09-16, in flight)

| lane | ADR | question | state |
|---|---|---|---|
| NRA-ALGEBRAIC-WITNESS | 2134 | the algebraic sample the clause-loop census pointed at | built OFF: an algebraic FINAL coordinate gated on exact replay; pinned QF_NRA 124 → 128, 4 STABLE-GAIN / 0 loss / 0 unstable at 3×/arm, QF_NIA and QF_LRA controls flat, 0 flips; **held-out draw stopped at 23 of 200 when the round closed**, so the criterion is unmet and the lever stays OFF (~60 min to finish); the census predicted 1 of the 4 movers (a first-wins decline slot makes a cause census non-predictive); **`RealAlgebraic::sign_at` read two endpoint samples as an enclosure and returned a wrong sign** — fixed with an exact Sturm count, no shipped wrong verdict found; merged `20e835755` |
| NIA-ORDER-LEMMAS | 2136 | z3's order/monotonicity lemma portfolio, the only QF_NIA mechanism the trace left untried | QF_NRA control clean 124/124; QF_NIA pinned sweep complete on disk; lane killed by the account limit mid-analysis and resumed; report pending |
| LRA-ATOM-SCREEN | — | the atom-count admission screen ADR-2111 left unrun, now that the tableau is sparse | measured, does not ship: QF_LRA decided 106 at 1x/2x/4x/16x/off while admitted rose 130 → 200; 16x and off add 6 and 8 allocator aborts (7.4 GiB, 24/24 stable); QF_UFLRA and QF_RDL null, QF_LIA and QF_IDL never reach the offline loop; 28 of the 32 target rows stop at "model did not replay" in the online engine's model reconstruction, which is the next QF_LRA increment; merged `5d827fe02` |
| QUANT-REACH-DIFF | — | per core, where each of z3's proof instances is lost | done: 1,025 unique bodies over 53 UFLIA cores — ADMITTED 11, MATCHED-REJECTED 169, NEVER-MATCHED 369, NESTED 476 (46 %, reproducing the probe's 46 %); nested universals are matched and their tuples computed, then dropped as inactive at `qinst_egraph.rs:7294` because nothing records that the universal is currently entailed; ADR-2120's activation-by-assignment (built, OFF) recovers 102 of the 169 rejected; three worked examples at `file:line`; merged `8441384c0` |

Round three closed with NRA-CLAUSE-LOOP's merge; every round-three lever
has an A/B and a written reason, and the one that measured a non-null
(QF_NRA 117 → 122, ADR-2121/2126) shipped.

## Round five (2026-09-16, in flight)

| lane | ADR | question | host |
|---|---|---|---|
| QUANT-COMPOSE | — (2138 unspent) | the four OFF quantifier levers composed | stopped after sizing at the user's pause: the levers share no read site (composition is a data-flow claim); the three ADRs' OFF arms read 15/15/16 on the same 53 cores, so a sweep needs a threshold above ±1; z3 and cvc5 activate a universal inside an instantiated body by asserting the instance back into the SAT layer (`qi_queue.cpp:288`, `smt_context.cpp:1482`; cvc5 `theory_quantifiers.cpp:173`), while ours forces `PositiveContext` to `None` for the whole subtree on entering a `forall` body (`qinst_egraph.rs:1948`) before any lever level is consulted, so ADR-2120 never reaches a universal nested inside another binder — a reading, not a fixture; `AXEYUM_MACRO_INLINE` has no registry row; 13 of 71 citations were wrong on first check and two exit-status checkers now hold them at BAD=0; merged `e6392a554` |
| LRA-MODEL-REPLAY | — (2139 unspent) | the 28 QF_LRA files stopping at "online CDCL(T) LRA model did not replay" (`lra_theory.rs:493`) | scoped down at the user's pause to the per-file census of which construct is outside the incremental engine; lane killed by the account limit while launching the s7 census and resumed; report pending |

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
- The five "silent 17-second" push deaths were my own `ulimit -v` in the
  launching shell: a hard limit the hook's `mem-run.sh` could not raise.
  Found by the xtrace the hook now writes; the wrapper keeps an inherited
  limit and says so (`b548367ff`).
- A 7-day prune of `target/*/build` gutted `z3-sys`'s download cache and left
  its directory, so the `--all-features` lint failed on a "cached" archive
  with no library. Prune whole `build/<crate>-<hash>` dirs, not files.
- Lane worktrees have no `references/` clones (gitignored); one lane could
  not verify its z3 citations and said so. Briefs give the absolute path.
- Two lanes' first controls were vacuous (a population that could not decide;
  a column computed at the outermost node of a `let` tree); both caught by the
  lanes themselves and kept, labelled.
