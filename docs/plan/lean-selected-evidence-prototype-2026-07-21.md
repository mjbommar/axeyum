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
- no parallel Cargo/process execution; and
- success requires the in-tree reconstructor to return a module containing
  `theorem axeyum_refutation`.

Representative command:

```text
timeout 30s cargo run --release -q -p axeyum-bench \
  --example probe_selected_evidence_lean -- <file.smt2>
```

## Results

| Selected evidence | Exact row | Result under outer bound | Observed artifact/stage |
|---|---|---|---|
| closed universal counterexample | `quantified/BV/bitwuzla-regress-clean/solver__quant__regsmtparselet.smt2` | reconstructed | 15,174-byte Lean module |
| paired existential transfer | `quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__nested9_true-unreach-call.i_575.smt2` | reconstructed | 18,551,050-byte Lean module |
| BV alternation counterexample | `quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__bug802.smt2` | outer timeout | source stage 299 ms; 8,524-command tail reconstructed in 566 ms; no rendered module by 30 s |
| BV alternation counterexample | `quantified/BV/cvc5-regress-clean/cli__regress1__quantifiers__small-pipeline-fixpoint-3.smt2` | outer timeout | source stage 485 ms; 13,824-command tail 537 ms; reconstruction stage 7.72 s; no rendered module by 30 s |
| conjunctive universal instance | `quantified/BV/cvc5-regress-clean/cli__regress0__quantifiers__cond-var-elim-binary.smt2` | outer timeout | no completed stage/result emitted before 30 s |
| generic Alethe | `non-incremental/QF_NIA/cvc5-regress-clean/cli__regress0__arith__div.01.smt2` | reconstructed through existing EUF consumer | 15 commands; 8,082-byte module; 9,204 KiB peak RSS |
| generic Alethe | `non-incremental/QF_NIA/cvc5-regress-clean/cli__regress1__arith__div.08.smt2` | reconstructed through existing EUF consumer | 6 commands; 2,916-byte module; 9,456 KiB peak RSS |
| generic Alethe | `non-incremental/QF_NIA/cvc5-regress-clean/cli__regress1__minimal_unsat_core.smt2` | reconstructed through existing EUF consumer | 15 commands; 8,082-byte module; 9,108 KiB peak RSS |

The first combined run was stopped after the first successful row and a silent
second-row interval; it is not an additional measurement. The per-row runs
above are the bounded result. Timing is host-local diagnostic evidence, not a
performance baseline.

## Interpretation

The five quantified-BV gaps are not five missing Lean theorem families:

- two already close by feeding the selected certificate to shipped
  reconstructors;
- two more enter the selected alternation reconstructor and build large proof
  tails, then miss the outer bound during later reconstruction/rendering; and
- one remains a bounded cost/phase diagnostic rather than an expressiveness
  result.

The 18.5 MB successful module and the two large command tails make proof size,
sharing, spooling, and render/check cost first-class concerns. Re-running search
from the query obscures this distinction. The next quantified-BV prototype
should record phase time, peak RSS, kernel term count, rendered bytes, and
external-Lean result while consuming the selected certificate. It should not
add a new theorem family.

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
3. measure the remaining three quantified-BV cost rows with bounded phase/RSS/
   kernel-term/module/external-Lean telemetry; and
4. choose whether that production boundary belongs on `Evidence`, an
   evidence-aware Lean facade, or a versioned export artifact only after those
   measurements identify its required resource/reporting contract.

Five of the exact eight rows now reconstruct from their selected evidence using
existing consumers; three remain bounded quantified-BV cost cases. The generated
dominance denominator does not change from a diagnostic alone: no row is
credited until production dispatch consumes the selected evidence and the
produced module passes the required official-Lean tier.
