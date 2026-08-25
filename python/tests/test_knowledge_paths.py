"""Root discovery and the read-only primitives.

The rule under test is the one this repository gets wrong most often: an empty
answer must be distinguishable from an unasked question.
"""

from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path

import pytest

import axeyum
from axeyum import knowledge
from axeyum.knowledge import _paths

ROOT = _paths.repo_root()


def test_repo_root_finds_the_schema_marker() -> None:
    assert (ROOT / _paths.ROOT_MARKER).is_file()
    assert (ROOT / "scripts" / "validate-facts.py").is_file()


def test_env_override_wins(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setenv(_paths.ROOT_ENV, str(ROOT))
    assert _paths.repo_root() == ROOT


def test_env_override_pointing_at_a_non_checkout_raises(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    monkeypatch.setenv(_paths.ROOT_ENV, str(tmp_path))
    with pytest.raises(FileNotFoundError) as excinfo:
        _paths.repo_root()
    assert str(tmp_path) in str(excinfo.value)


def test_repo_root_raises_rather_than_guessing(tmp_path: Path) -> None:
    with pytest.raises(FileNotFoundError):
        _paths.repo_root(start=tmp_path)


def test_require_dir_and_require_file_name_the_path(tmp_path: Path) -> None:
    with pytest.raises(FileNotFoundError) as excinfo:
        _paths.require_dir(tmp_path / "absent")
    assert "absent" in str(excinfo.value)
    with pytest.raises(FileNotFoundError) as excinfo:
        _paths.require_file(tmp_path / "nofile.json")
    assert "nofile.json" in str(excinfo.value)


def test_run_script_carries_the_exit_status() -> None:
    run = _paths.run_script(ROOT, "validate-facts.py")
    assert run.returncode == 0, run.stderr
    assert run.stdout.strip(), "a script that printed nothing is not evidence"
    assert run.check() is run


def test_run_script_check_raises_on_failure() -> None:
    run = _paths.run_script(ROOT, "fact-frontier.py", ["--verify", "/nonexistent/frontier.json"])
    assert run.returncode != 0
    with pytest.raises(_paths.ScriptError):
        run.check()


def test_load_script_module_reads_a_constant_without_running_it() -> None:
    module = _paths.load_script_module(
        ROOT, "validate-autogenesis-operations.py", "_probe_operations"
    )
    assert len(module.EXECUTION_DRIVERS) > 0


def test_knowledge_is_reachable_from_the_package_root() -> None:
    assert axeyum.knowledge is knowledge
    assert "knowledge" in axeyum.__all__


def test_every_submodule_is_exported() -> None:
    expected = {
        "autogenesis",
        "claims",
        "concepts",
        "facts",
        "frontier",
        "generated",
        "nursery",
        "operations",
        "overlay",
    }
    assert expected <= set(knowledge.__all__)
    assert all(hasattr(knowledge, name) for name in expected)


def test_the_package_docstring_names_its_tier() -> None:
    assert "tier R" in (knowledge.__doc__ or "")


def test_nothing_under_scripts_imports_axeyum() -> None:
    """`scripts/` is standard-library-only, and this layer must not change that."""
    # Anchored on a word boundary: `axeyum_fsprims` is a script-local helper
    # module, not this package, and a prefix match would report it as a breach.
    pattern = r"^(import|from) axeyum($|[ .])"
    completed = subprocess.run(
        ["grep", "-rlE", pattern, str(ROOT / "scripts")],
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode in (0, 1), completed.stderr
    assert completed.stdout.strip() == ""
    # Positive control: the same query must find the imports in this package.
    control = subprocess.run(
        ["grep", "-rlE", pattern, str(Path(__file__).resolve().parent)],
        capture_output=True,
        text=True,
        check=False,
    )
    assert control.returncode == 0 and control.stdout.strip(), "the negative result is unproven"


def test_the_interpreter_is_the_one_the_tests_run_under() -> None:
    run = _paths.run_script(ROOT, "validate-facts.py")
    assert run.argv[0] == sys.executable
    assert os.path.isabs(run.argv[1])
