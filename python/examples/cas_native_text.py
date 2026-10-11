"""Replay exact expressions exported by the native Rust text parser.

Pass --parser-binary /path/to/debug/examples/parse_text after building the Rust
example. The Python extension must include expression wire and wide traces.
"""
import argparse
import json
import subprocess
from fractions import Fraction
from pathlib import Path
from axeyum import cas


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--parser-binary", type=Path, required=True)
    args = parser.parse_args()
    source = "300000*(1/240)/(1-(1+1/240)^-360)"
    result = subprocess.run([str(args.parser_binary.resolve())], input=source + "\n",
                            text=True, capture_output=True, timeout=30)
    if result.returncode:
        raise RuntimeError(result.stderr)
    expression = cas.Expr.from_json(result.stdout.strip())
    if json.loads(expression.to_json()) != json.loads(cas.parse(source).to_json()):
        raise AssertionError("native/Python structural parsing disagrees")
    expected = 300000 * Fraction(1, 240) / (1 - Fraction(241, 240)**-360)
    if expression.eval({}) != expected:
        raise AssertionError("native parsed payment differs from Fraction reference")
    produced = cas.normalize_trace(expression, wide=True)
    if produced.status != "produced" or produced.trace is None:
        raise RuntimeError(f"{produced.status}: {produced.detail}")
    checked = cas.replay_trace(produced.trace.to_json(), expression,
                               cas.Expr.rat(expected.numerator, expected.denominator))
    if checked.status != "checked":
        raise AssertionError(f"native parsed payment replay failed: {checked.detail}")
    for text in ["x^y", "sin(x,y)", "2^2^3", "💥"]:
        invalid = subprocess.run([str(args.parser_binary.resolve())], input=text + "\n",
                                 text=True, capture_output=True, timeout=30)
        if invalid.returncode == 0 or not invalid.stderr or invalid.stdout:
            raise AssertionError(f"native parser did not refuse {text}")
    print(f"native payment: {produced.trace.step_count} replayed steps, "
          f"{len(produced.trace.to_json().encode())} bytes; 4 invalid inputs refused")


if __name__ == "__main__":
    main()
