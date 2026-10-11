"""Export/replay local CAS certificates; run with a freshly built extension.

python python/examples/cas_step_trace.py --output /path/to/new/example-directory
The JSON includes every step's local witness and complete surrounding expression.
Checked CAS evidence and kernel admission are separate milestones.
"""
from __future__ import annotations
import argparse
import json
from fractions import Fraction
from pathlib import Path
from axeyum import cas


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    x = cas.Expr.var("x")
    source = (x + Fraction(1, 2) + Fraction(1, 3)) * (-(-(x + Fraction(1, 7))))
    produced = cas.normalize_trace(source)
    if produced.status != "produced" or produced.trace is None:
        raise RuntimeError(f"{produced.status}: {produced.detail}")
    trace = produced.trace
    exported = trace.to_json()
    checked = cas.replay_trace(exported, source, trace.result)
    if checked.status != "checked":
        raise RuntimeError(f"{checked.status}: {checked.detail}")
    print(f"{source} -> {trace.result}; {trace.step_count} checked steps")
    payload = json.loads(exported)
    for step in payload["steps"]:
        print(f"  step {step['id']}: {step['rule']}, location={step['location']}")
    corrupt = json.loads(exported)
    corrupt["steps"][0]["context"] = "unproved"
    rejected = cas.replay_trace(json.dumps(corrupt), source, trace.result)
    if rejected.status != "rejected":
        raise RuntimeError("corrupted context was not rejected")
    print(f"corrupted context: {rejected.status} at step {rejected.failing_step}")
    if args.output:
        args.output.mkdir(parents=True, exist_ok=True)
        (args.output / "trace.json").write_text(exported)
        (args.output / "statement.json").write_text(
            json.dumps({"input": payload["input"], "result": payload["result"]})
        )


if __name__ == "__main__":
    main()
