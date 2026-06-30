# Checks

| Check | Result | Evidence | Trust Boundary |
|---|---|---|---|
| `non_negative_benefit` | `unsat` | Bool/QF_LIA fixture with checked Axeyum evidence | The formula asks for `benefit < 0` under the rule definition. |
| `cap_respected` | `unsat` | Bool/QF_LIA fixture with checked Axeyum evidence | The formula asks for `benefit > 30` under bounded household-size rules. |
| `threshold_cliff` | `sat` | Witness replay | Concrete rows show the benefit at and one unit above the new threshold. |
| `phaseout_monotonicity` | `unsat` | Bool/QF_LIA fixture with checked Axeyum evidence | Fixed household size and threshold inside the active linear phase-out slice; the validator replays the full piecewise finite sample. |
| `temporal_transition` | `sat` | Witness replay | Same facts can produce different benefit only across the effective-date threshold change. |
| `implementation_equivalence` | `unsat` | Bool/QF_LIA fixture with checked Axeyum evidence | The formal rule formula and bounded executable interpretation are asserted to disagree on the active linear phase-out slice. |

The checked SMT-LIB fixtures live in [smt2/](smt2/). The regression tests are in
[`rules_as_code_examples.rs`](../../../../crates/axeyum-solver/tests/rules_as_code_examples.rs).

Run:

```sh
python3 scripts/validate-rules-as-code.py
cargo test -p axeyum-solver --test rules_as_code_examples
```
