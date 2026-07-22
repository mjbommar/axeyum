# Selected-evidence Lean reconstruction prototype — 2026-07-21

Status: **bounded diagnostic result; no production API change authorized**

The generated [proof-gap matrix](generated/proof-gap-matrix.md) identifies eight
UNSAT outcomes with certified, independently checked, trust-free evidence but
no query-only Lean reconstruction. Five are quantified-BV certificate families;
three are QF_NIA Alethe proofs.

The ordinary audit calls `prove_unsat_to_lean_module(arena, assertions)`. That
facade classifies the query and re-runs certificate search. The bounded
`probe_selected_evidence_lean` diagnostic instead consumes the exact certificate
already selected by `produce_evidence` and calls its existing reconstructor. It
changes no solver, evidence, or reconstruction API.

## Frozen diagnostic protocol

- release profile, one process at a time;
- `SolverConfig` timeout 10 seconds and resource limit 100,000, matching the
  dominance rows;
- 30-second outer wall bound per file after the first combined run showed one
  row could hide later results;
- `AXEYUM_LEAN_RECON_TRACE=1` phase markers for the three remaining
  quantified-BV rows;
- after the first traced `bug802` run exposed a 6.79 GiB working set, a hard
  4 GiB `scripts/mem-run.sh` cap on every subsequent cost probe;
- no parallel Cargo/process execution; and
- success requires the in-tree reconstructor to return a module containing
  `theorem axeyum_refutation`.

Representative command:

```text
AXEYUM_LEAN_RECON_TRACE=1 MEM_LIMIT_GB=4 \
  /usr/bin/time -v scripts/mem-run.sh timeout 30s \
  target/release/examples/probe_selected_evidence_lean <file.smt2>
```

## Results

| Selected evidence | Exact row | Result under outer bound | Observed artifact/stage |
|---|---|---|---|
| closed universal counterexample | `quantified/BV/bitwuzla-regress-clean/solver__quant__regsmtparselet.smt2` | reconstructed | 15,174-byte Lean module |
| paired existential transfer | `quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__nested9_true-unreach-call.i_575.smt2` | reconstructed | 18,551,050-byte Lean module |
| BV alternation counterexample | `quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__bug802.smt2` | memory boundary in scoped kernel closure | certificate 5 ms; source 301 ms; 8,524-command tail 538 ms; no `kernel-closed`; uncapped trace reached 6,791,716 KiB RSS at 30 s, then a 4 GiB-capped rerun failed a 12,582,912-byte allocation at 18.03 s |
| BV alternation counterexample | `quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__small-pipeline-fixpoint-3.smt2` | outer timeout after kernel closure | certificate 2 ms; source 472 ms; 13,824-command tail 481 ms; `kernel-closed` at 7.744 s; no module spool by 30 s; 591,300 KiB peak RSS |
| conjunctive universal instance | `quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__cond-var-elim-binary.smt2` | outer timeout in tail reconstruction | certificate/residual below 1 ms; two source assumptions by 612 ms; 15,705-command tail emitted by 2.607 s; no `tail-reconstructed` by 30 s; 536,472 KiB peak RSS |
| generic Alethe | `non-incremental/QF_NIA/cvc5-regress-clean/cli__regress0__arith__div.01.smt2` | reconstructed through existing EUF consumer | 15 commands; 8,082-byte module; 9,204 KiB peak RSS |
| generic Alethe | `non-incremental/QF_NIA/cvc5-regress-clean/cli__regress1__arith__div.08.smt2` | reconstructed through existing EUF consumer | 6 commands; 2,916-byte module; 9,456 KiB peak RSS |
| generic Alethe | `non-incremental/QF_NIA/cvc5-regress-clean/cli__regress1__minimal_unsat_core.smt2` | reconstructed through existing EUF consumer | 15 commands; 8,082-byte module; 9,108 KiB peak RSS |

The first combined run was stopped after the first successful row and a silent
second-row interval; it is not an additional measurement. The first traced
`bug802` run had only the 30-second wall bound and exposed an unacceptable
6.79 GiB working set. It was not repeated. The 4 GiB-capped rerun and both other
remaining rows stayed inside the hard memory cap, and no kernel OOM event was
recorded. Timing is host-local diagnostic evidence, not a performance baseline.

## Interpretation

The five quantified-BV gaps are not five missing Lean theorem families:

- two already close by feeding the selected certificate to shipped
  reconstructors;
- `bug802` enters the selected alternation reconstructor and builds its tail,
  then exceeds 4 GiB during scoped kernel inference/closure;
- `small-pipeline-fixpoint-3` completes kernel closure in 7.744 seconds and
  stays below 600 MiB, then spends the rest of the bound before module spooling;
  and
- `cond-var-elim-binary` emits a 15,705-command residual by 2.607 seconds but
  does not finish CPS tail reconstruction inside 30 seconds.

The 18.5 MB successful module and the large command tails make proof size,
sharing, spooling, and render/check cost first-class concerns. More importantly,
the traces reject one generic “optimize Lean export” fix: the three rows stop in
three different mechanisms—scoped kernel closure, post-closure compact
sharing/spooling, and CPS tail reconstruction. Re-running search from the query
obscures these distinctions. None is evidence of a missing theorem family.

The three QF_NIA rows close in the prototype without an arithmetic theorem or
an arithmetic reconstructor. Their selected proof objects contain only EUF and
resolution rules:

- `div.01` and `minimal_unsat_core`: 15 commands each — two
  `eq_congruent`, two `eq_reflexive`, two `eq_transitive`, and five
  `resolution` steps;
- `div.08`: six commands — one `eq_congruent`, one `eq_reflexive`, and two
  `resolution` steps.

Each reconstructs in about 0.10 seconds wall time on this host with less than
9.5 MiB peak RSS. The source formulas are QF_NIA, but their selected proof is a
value-independent congruence contradiction over total division terms. The
query-only facade classifies from source syntax, chooses `la_generic`, and
rejects the non-conjunctive LRA shape; selected-evidence dispatch instead sends
the already checked proof to the existing EUF consumer. This is a measured
classification/plumbing defect, not missing nonlinear or linear arithmetic
proof theory.

## Roadmap consequence

Keep the reconstruction lane separate from ADR-0341's bare-evidence telemetry:

1. retain the diagnostic selected-evidence facade as the reproducible prototype;
2. define a production evidence-aware dispatch contract that preserves the
   selected certificate instead of classifying and re-searching from source
   syntax;
3. profile `bug802` inside scoped-free-variable inference/closure without
   raising the 4 GiB cap; profile compact share planning/writer traversal for
   `small-pipeline-fixpoint-3`; and profile the command/premise topology of
   `reconstruct_bitwise_cps_tail` for `cond-var-elim-binary`;
4. require module emission before spending an official-Lean run on a cost row;
   and
5. choose whether the production boundary belongs on `Evidence`, an
   evidence-aware Lean facade, or a versioned export artifact only after those
   measurements identify its required resource/reporting contract.

Five of the exact eight rows now reconstruct from their selected evidence using
existing consumers; three remain bounded quantified-BV cost cases. The generated
dominance denominator does not change from a diagnostic alone: no row is
credited until production dispatch consumes the selected evidence and the
produced module passes the required official-Lean tier.
