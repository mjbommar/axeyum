#!/usr/bin/env python3
"""Validate the lint-only dependent motive build decline."""
import hashlib, json, pathlib, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-fib-dvd-eq-rec-motive-result-v20.json"
def sha256(path: pathlib.Path) -> str: return hashlib.sha256(path.read_bytes()).hexdigest()
def main() -> int:
    try:
        result = json.loads(RESULT.read_text()); impl = result["implementation"]; execution = result["execution"]
        assert result["state"] == "dependent-motive-implemented-build-declines-only-on-argument-count-lint"
        assert sha256(ROOT / result["plan"]["path"]) == result["plan"]["sha256"]
        assert sha256(ROOT / impl["path"]) == impl["sha256"]
        assert result["diagnostic"] == {"stage":"focused-clippy","class":"too_many_arguments","function":"eq_rec_transport","arguments":8,"limit":7}
        assert execution["complete_invocations"] == execution["input_stream_reads"] == execution["target_theorem_submissions"] == execution["ledger_writes"] == 0
    except (AssertionError, OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-fib-dvd-eq-rec-motive-result: FAIL: {error}", file=sys.stderr); return 1
    print("autogenesis-int-fib-dvd-eq-rec-motive-result: PASS: motive=implemented|decline=lint|inputs=0|targets=0"); return 0
if __name__ == "__main__": raise SystemExit(main())
