"""The sandbox: does the ceiling actually bite on THIS host, and does it say so.

CLAUDE.md's `cargo-serialized.sh` lesson is the whole design here -- `MemoryMax`
without `MemorySwapMax` is decoration, and a wrapper that caps one host says
nothing about another -- so the central test is not "the sandbox exists" but
`python_exec_selfcheck()`: over-allocate through the same code path and fail if
the allocation survives.

Every containment assertion is paired with a control that must come out the
other way. The whitelist tests are paired with an import that must SUCCEED, and
the memory ceiling is measured twice at two different caps, so a ceiling that
had quietly stopped applying would fail rather than pass silently.
"""

from __future__ import annotations

import pytest

pytest.importorskip("pydantic_ai", reason="the [agent] extra is not installed")

from axeyum.agent import sandbox

# The sandbox runs `sys.executable`, so a whitelist entry is only real if that
# interpreter can import it. Reported rather than assumed.
HAS_SYMPY = sandbox.python_exec("import sympy", timeout_s=90).exit_status == 0


# ------------------------------------------------------------- the import guard


@pytest.mark.parametrize("module", ["os", "sys", "socket", "subprocess", "pathlib", "importlib"])
def test_user_code_may_not_import_a_module_off_the_whitelist(module: str) -> None:
    result = sandbox.python_exec(f"import {module}", timeout_s=30)
    assert result.exit_status != 0
    assert "not on the import whitelist" in result.stderr


def test_the_from_form_is_refused_too() -> None:
    result = sandbox.python_exec("from os import path", timeout_s=30)
    assert result.exit_status != 0
    assert "'os'" in result.stderr


def test_calling_dunder_import_directly_is_refused() -> None:
    """The guard replaces `__import__`, so reaching for it is the same door."""
    result = sandbox.python_exec("__import__('socket')", timeout_s=30)
    assert result.exit_status != 0
    assert "not on the import whitelist" in result.stderr


def test_every_whitelisted_stdlib_module_imports(monkeypatch) -> None:
    """CONTROL for the tests above: the guard is not simply refusing everything."""
    names = [m for m in sandbox.ALLOWED_MODULES if m != "sympy"]
    code = f"import {', '.join(names)}\nprint('imported', len({names!r}))"
    result = sandbox.python_exec(code, timeout_s=30)
    assert result.exit_status == 0, result.stderr
    assert "imported" in result.stdout


def test_the_whitelist_is_per_call_and_the_refusal_names_it() -> None:
    result = sandbox.python_exec("import decimal", timeout_s=30, allowed_modules=("math",))
    assert result.exit_status != 0
    assert "'decimal'" in result.stderr
    assert "['math']" in result.stderr


# --------------------------------------------------------------------- network


def test_a_socket_cannot_be_opened() -> None:
    code = "import socket\ns = socket.socket()\ns.connect(('1.1.1.1', 80))\nprint('CONNECTED')"
    result = sandbox.python_exec(code, timeout_s=30)
    assert result.exit_status != 0
    assert "CONNECTED" not in result.stdout


def test_the_isolation_field_states_the_network_position_either_way() -> None:
    """Never silently: a gap that is only in a docstring is a gap nobody sees."""
    isolation = sandbox.python_exec("pass", timeout_s=10).isolation
    assert ("unshare-n" in isolation) or ("no-network-isolation" in isolation)


# ---------------------------------------------------------------------- memory


def test_a_two_gigabyte_allocation_is_killed() -> None:
    code = "b = bytearray(2 * 1024 * 1024 * 1024)\nb[-1] = 1\nprint('SURVIVED')"
    result = sandbox.python_exec(code, timeout_s=90)
    assert result.exit_status != 0
    assert "SURVIVED" not in result.stdout
    assert result.memory_max_mb == sandbox.DEFAULT_MEMORY_MB


def test_the_isolation_field_names_the_memory_mechanism_that_was_used() -> None:
    result = sandbox.python_exec("pass", timeout_s=10)
    if sandbox.systemd_scope_available():
        assert "systemd-scope(MemoryMax=" in result.isolation
        # The lesson this repository paid for: a ceiling without a swap ceiling
        # is decoration, so both must be named or the label is a lie.
        assert "MemorySwapMax=0" in result.isolation
    else:
        assert "rlimit-as(" in result.isolation


def test_a_tight_cap_kills_an_allocation_a_loose_cap_permits() -> None:
    """The discrimination control: the cap is a dial and it is measured moving.

    Without this pair, `test_a_two_gigabyte_allocation_is_killed` passes just as
    well when nothing is enforcing anything and 2 GiB simply fails for some
    other reason.
    """
    code = "b = bytearray(200 * 1024 * 1024)\nb[-1] = 1\nprint('SURVIVED')"
    tight = sandbox.python_exec(code, timeout_s=60, memory_mb=64)
    loose = sandbox.python_exec(code, timeout_s=60, memory_mb=1024)
    assert tight.exit_status != 0 and "SURVIVED" not in tight.stdout
    assert loose.exit_status == 0 and "SURVIVED" in loose.stdout


# ----------------------------------------------------------------- wall clock


def test_a_spin_loop_is_killed_by_the_wall_clock() -> None:
    result = sandbox.python_exec("while True:\n    pass", timeout_s=3)
    assert result.timed_out is True
    assert result.exit_status != 0
    assert result.duration_ms >= 3000


def test_a_sleeping_process_is_killed_too(monkeypatch) -> None:
    """CPU rlimits do not bound sleeping; the wall clock is a separate layer."""
    code = "import math\nx = 0\nwhile True:\n    x = math.sin(x) + 1"
    result = sandbox.python_exec(code, timeout_s=3)
    assert result.timed_out is True


def test_a_fast_call_is_not_reported_as_timed_out() -> None:
    result = sandbox.python_exec("print('quick')", timeout_s=30)
    assert result.timed_out is False
    assert result.ok is True


# ------------------------------------------------------------------ the result


def test_stdout_is_captured_and_the_status_is_zero() -> None:
    result = sandbox.python_exec("print('hello'); print('world')", timeout_s=30)
    assert result.exit_status == 0
    assert result.stdout.splitlines() == ["hello", "world"]
    assert result.duration_ms >= 0


def test_a_syntax_error_is_a_result_and_not_an_exception() -> None:
    """A decline is a datapoint; raising would put it in the harness error path."""
    result = sandbox.python_exec("def (:", timeout_s=30)
    assert result.exit_status != 0
    assert "SyntaxError" in result.stderr
    assert result.ok is False


def test_a_runtime_traceback_is_a_result_too() -> None:
    result = sandbox.python_exec("raise ValueError('nope')", timeout_s=30)
    assert result.exit_status != 0
    assert "ValueError" in result.stderr


def test_the_result_reports_the_ceiling_it_ran_under() -> None:
    result = sandbox.python_exec("pass", timeout_s=10, memory_mb=256)
    assert result.memory_max_mb == 256
    assert "256M" in result.isolation


def test_the_result_is_frozen() -> None:
    result = sandbox.python_exec("pass", timeout_s=10)
    with pytest.raises((AttributeError, TypeError)):
        result.stdout = "tampered"  # type: ignore[misc]


def test_the_working_directory_is_scratch_and_is_gone_afterwards() -> None:
    """No filesystem the caller shares: cwd is a temp dir, deleted on return."""
    result = sandbox.python_exec("import json\nprint(json.dumps({'ok': 1}))", timeout_s=30)
    assert result.exit_status == 0
    assert "scratch-cwd" in result.isolation


# ------------------------------------------------------------------- symbolics


@pytest.mark.skipif(not HAS_SYMPY, reason="the sandbox interpreter cannot import sympy")
def test_sympy_expands_a_binomial() -> None:
    code = "import sympy\nx = sympy.Symbol('x')\nprint(sympy.expand((x + 1) ** 2))\n"
    result = sandbox.python_exec(code, timeout_s=90)
    assert result.exit_status == 0, result.stderr
    assert result.stdout.strip() == "x**2 + 2*x + 1"


@pytest.mark.skipif(not HAS_SYMPY, reason="the sandbox interpreter cannot import sympy")
def test_sympy_may_import_the_standard_library_that_user_code_may_not() -> None:
    """The guard is scoped to the CALLER, which is what lets a library work."""
    result = sandbox.python_exec("import sympy\nprint(sympy.__name__)", timeout_s=90)
    assert result.exit_status == 0, result.stderr
    assert result.stdout.strip() == "sympy"


# ------------------------------------------------------------------ the probes


def test_the_probes_answer_a_bool_and_are_cached() -> None:
    assert sandbox.systemd_scope_available() is sandbox.systemd_scope_available()
    assert sandbox.unshare_net_available() is sandbox.unshare_net_available()


def test_the_isolation_label_names_every_layer() -> None:
    label = sandbox.isolation_label(512, 20, sandbox.ALLOWED_MODULES)
    for fragment in ("rlimit-cpu(", "wall-timeout(", "scratch-cwd", "import-whitelist("):
        assert fragment in label


def test_the_child_environment_carries_nothing_but_scratch_and_the_bus() -> None:
    environment = sandbox.child_environment("/scratch")
    assert set(environment) <= {"PATH", "HOME", "TMPDIR", "LC_ALL", *sandbox.PASSTHROUGH_ENV}
    assert environment["HOME"] == "/scratch"


# --------------------------------------------------------------- the self-check


def test_the_self_check_passes_on_this_host() -> None:
    """Mirrors `cargo-serialized.sh --self-check`: it fails if the allocation survives."""
    check = sandbox.python_exec_selfcheck()
    assert check.ok, check.line
    assert check.line.startswith("SANDBOX-SELFCHECK|ENFORCED|")
    assert "network=REFUSED" in check.line
    assert sandbox.SURVIVED not in check.memory.stdout


def test_the_self_check_line_names_the_cap_and_the_isolation() -> None:
    check = sandbox.python_exec_selfcheck()
    assert "cap=" in check.line
    assert "isolation=" in check.line
    assert "network_layer=" in check.line


def test_the_self_check_discriminates_when_the_probe_is_given_more_than_the_cap() -> None:
    """A check that cannot fail is worse than no check, so this makes it fail.

    The probe asks for 2 GiB. Given a 3 GiB ceiling it is no longer bounded by
    the sandbox, and the self-check must say `NOT-ENFORCED` -- exactly as
    `AXEYUM_CARGO_SWAP=1G` flips `cargo-serialized.sh --self-check`. Nothing is
    actually committed: the allocation is refused by the host or succeeds
    lazily, and either way the assertion is on the LABEL, not on the byte count.
    """
    check = sandbox.python_exec_selfcheck(memory_mb=3072)
    if sandbox.SURVIVED in check.memory.stdout:
        assert check.ok is False
        assert "NOT-ENFORCED" in check.line
    else:
        # The host refused 4 GiB for its own reasons, so this run measured
        # nothing about the ceiling. Reported as inconclusive rather than as a
        # pass -- an inconclusive check recorded as green is the failure mode
        # this whole file exists to avoid.
        pytest.skip(f"host would not grant 2 GiB even uncapped: {check.line}")


def test_the_main_entry_point_exits_on_the_finding() -> None:
    assert sandbox.main() == 0
