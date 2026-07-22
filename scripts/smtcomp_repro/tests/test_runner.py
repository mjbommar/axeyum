"""Typed-process and exact-output tests for the local SMT-COMP runner."""

from __future__ import annotations

import os
import signal
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from runner import run_solver  # noqa: E402
from scoring import Status  # noqa: E402


def _python(source: str, **kwargs):
    return run_solver(
        [sys.executable, "-c", source],
        wall_limit_s=kwargs.pop("wall_limit_s", 1.0),
        **kwargs,
    )


def test_timeout_retains_observed_verdict_and_exact_output():
    result = _python(
        "import time; print('sat', flush=True); time.sleep(60)",
        wall_limit_s=0.05,
        grace_s=0.2,
    )
    assert result.observed == Status.SAT
    assert result.reported is None  # legacy policy remains unchanged
    assert result.termination_class == "wall-timeout"
    assert result.exit_code is None
    assert result.signal == signal.SIGKILL
    assert result.resource_limit_kind == "wall"
    assert result.scoring_wall_time == 0.05
    assert result.runner_elapsed >= result.scoring_wall_time
    assert result.stdout_bytes == b"sat\n"


def test_nonzero_exit_is_typed_without_signal_or_resource_guess():
    result = _python("raise SystemExit(7)")
    assert result.termination_class == "nonzero-exit"
    assert result.exit_code == 7
    assert result.signal is None
    assert result.resource_limit_kind is None
    assert not result.mem_exceeded


def test_operator_signal_is_not_guessed_to_be_memory_exhaustion():
    result = _python("import os, signal; os.kill(os.getpid(), signal.SIGTERM)")
    assert result.termination_class == "signal"
    assert result.exit_code is None
    assert result.signal == signal.SIGTERM
    assert result.resource_limit_kind is None
    assert not result.mem_exceeded


def test_explicit_resource_evidence_controls_resource_classification():
    result = _python(
        "import os, signal; os.kill(os.getpid(), signal.SIGKILL)",
        evidenced_resource_limit_kind="memory",
    )
    assert result.termination_class == "resource-limit"
    assert result.exit_code is None
    assert result.signal == signal.SIGKILL
    assert result.resource_limit_kind == "memory"
    assert result.mem_exceeded


def test_non_utf8_output_is_retained_byte_exactly_and_still_parsed():
    result = _python("import os; os.write(1, b'\\xffsat\\n')")
    assert result.stdout_bytes == b"\xffsat\n"
    assert result.observed == Status.SAT


def _run_all():
    tests = sorted(name for name in globals() if name.startswith("test_"))
    failed = 0
    for name in tests:
        try:
            globals()[name]()
            print(f"PASS {name}")
        except Exception as exc:  # noqa: BLE001
            failed += 1
            print(f"FAIL {name}: {exc!r}")
    print(f"\n{len(tests) - failed}/{len(tests)} passed")
    return failed


if __name__ == "__main__":
    raise SystemExit(1 if _run_all() else 0)
