# CFAA V0 Expected Results

Machine-readable form: [`expected.json`](expected.json). The validator replays
every witness through the rule model, the decision table, and an independent
reading of the statute, and requires them to agree.

## Witnesses

| Witness | Facts (others false or 0) | Outputs |
|---|---|---|
| `penalty_overlap_c2b_c2c_witness` | (a)(2), prior conviction, commercial gain | (c)(2)(B) and (c)(2)(C) apply; maximum 10 years |
| `value_threshold_mismatch_witness` | (a)(2), value $5,000, loss $5,000 | factor (I) holds; (c)(2)(B)(iii) does not |
| `civil_gate_excludes_factor_vi_witness` | (a)(5)(A), 10 computers damaged, damage suffered | factor (VI) holds; maximum 10 years; no civil action |
| `buggy_implementation_counterexample_witness` | (a)(2), value $5,000 | model 1 year; buggy table 5 years |
| `first_a2_no_aggravator` | (a)(2), value $5,000 | maximum 1 year under (c)(2)(A) |
| `first_a5A_ten_computers` | (a)(5)(A), 10 computers damaged, damage suffered | maximum 10 years under (c)(4)(B); no civil action |
| `first_a5C_large_loss` | (a)(5)(C), loss $1,000,000, damage suffered | maximum 1 year under (c)(4)(G); civil action limited to economic damages |
| `a5A_death` | (a)(5)(A), prior conviction, death | life under (c)(4)(F), which displaces (c)(4)(C) |

## Check results

Four `unsat` checks carry certified `unsat-arith-dpll` refutations; four `sat`
checks carry replayed models. Solver models are free to differ from the
recorded witnesses (for example, any offense satisfies the threshold-mismatch
obligation); the recorded witnesses are the readable instances, checked
separately by the validator.

## Region-complete sweep

The modeled comparisons use only the constants 5,000 (dollars) and 10
(computers). The sample takes {4999, 5000, 5001} for both dollar amounts,
{9, 10, 11} for the count, all 1,024 combinations of the ten non-offense Boolean
facts, and all eight offenses: 221,184 rows, each decided identically by all
three readings.
