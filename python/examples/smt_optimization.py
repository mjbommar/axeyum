"""Exact optimization results with per-objective feasibility replay.

Run with a freshly built Axeyum extension. Gold-answer credit additionally needs
an independently checked, source-bound refutation of every better value.
"""
from axeyum import smt


SCRIPT = """(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= x 0) (<= x 10) (>= y 0) (<= y 3)))
(assert (<= (+ x y) 10))
(maximize x)
(maximize y)
(check-sat)
"""


def main() -> None:
    checked = 0
    for mode, expected in [("lex", [10, 0]), ("box", [10, 3])]:
        result = smt.optimize(SCRIPT, mode=mode, timeout_ms=2000)
        if not result.complete:
            raise RuntimeError(f"{mode}: optimization did not complete")
        if [row.value for row in result.objectives] != expected:
            raise AssertionError(f"{mode}: unexpected objective values")
        for index, row in enumerate(result.objectives):
            if row.replay() is not True:
                raise AssertionError(f"{mode} objective {index}: missing or invalid witness")
            checked += 1
            print(f"{mode}[{index}]: {row.direction} {row.value}; "
                  f"model={row.model}; replay=True; gold={row.gold_eligible}")
    if checked != 4:
        raise AssertionError("expected four actual model replays")


if __name__ == "__main__":
    main()
