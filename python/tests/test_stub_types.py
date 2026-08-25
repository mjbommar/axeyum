"""The generated stubs carry real TYPES, and every `Any` left in them is listed.

`tools/gen_native_stub.py` proves the stubs have the right NAMES and ARITY
against the built extension. It ignores annotations on purpose. This suite is
the other half:

* the type ratchet `tools/check_stub_types.py` passes, and its allowlist has no
  entry that no longer names an `Any` site (the budget cannot be re-spent);
* `mypy.stubtest` -- the only checker here that compares the stubs to the
  RUNTIME as types -- exits 0;
* four signatures a consumer actually reads are spot-checked by name, so a
  regression that keeps the counts healthy still fails.
"""

from __future__ import annotations

import ast
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent.parent
STUB_PKG = ROOT / "python" / "axeyum" / "_native"
ALLOWLIST = STUB_PKG / "ANY_ALLOWLIST.txt"

# `typed` must stay at or above this share of all parameters. The measured
# value when the typed stubs landed was 97.4%; the floor is deliberately below
# it so an honest `Any` on a new polymorphic argument is not a gate failure,
# and far enough above the old 0.7% that a regression to introspection-shaped
# stubs cannot pass.
MIN_TYPED_PERCENT = 90.0


def _stub(module: str) -> ast.Module:
    assert module.startswith("axeyum._native")
    tail = module[len("axeyum._native") :].strip(".")
    path = (
        STUB_PKG.joinpath(*tail.split(".")) / "__init__.pyi" if tail else STUB_PKG / "__init__.pyi"
    )
    assert path.is_file(), f"missing {path}"
    return ast.parse(path.read_text(encoding="utf-8"))


def _function(module: str, *path: str) -> ast.FunctionDef:
    """Finds `path` (class names then the function name) in a stub."""
    body = _stub(module).body
    for name in path[:-1]:
        found = next(
            (n for n in body if isinstance(n, ast.ClassDef) and n.name == name),
            None,
        )
        assert found is not None, f"{module}: no class {name}"
        body = found.body
    found = next(
        (n for n in body if isinstance(n, ast.FunctionDef) and n.name == path[-1]),
        None,
    )
    assert found is not None, f"{module}: no def {'.'.join(path)}"
    return found


def _annotation(node: ast.expr | None) -> str:
    assert node is not None
    return ast.unparse(node)


def _parameter(fn: ast.FunctionDef, name: str) -> ast.arg:
    every = [*fn.args.posonlyargs, *fn.args.args, *fn.args.kwonlyargs]
    found = next((a for a in every if a.arg == name), None)
    assert found is not None, f"{fn.name} has no parameter {name}"
    return found


def test_every_stub_parses() -> None:
    files = sorted(STUB_PKG.rglob("*.pyi"))
    assert len(files) >= 10
    for path in files:
        ast.parse(path.read_text(encoding="utf-8"), filename=str(path))


def test_the_type_ratchet_passes() -> None:
    completed = subprocess.run(
        [sys.executable, str(ROOT / "tools" / "check_stub_types.py")],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
        timeout=300,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr
    line = next(l for l in completed.stdout.splitlines() if l.startswith("STUB_TYPES|params="))
    fields = dict(part.split("=", 1) for part in line.split("|")[1:])
    params, typed = int(fields["params"]), int(fields["typed"])
    assert params > 500, line
    assert 100.0 * typed / params >= MIN_TYPED_PERCENT, line
    # Every `Any` accounted for, and no stale entry left behind.
    assert int(fields["any"]) == int(fields["allowlisted"]), line


def test_every_allowlist_entry_carries_a_reason() -> None:
    """A site with no reason is a to-do wearing a gate's clothes."""
    for number, raw in enumerate(ALLOWLIST.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        site, separator, reason = line.partition("  ")
        assert separator, f"{ALLOWLIST.name}:{number}: no reason"
        assert len(reason.strip()) > 20, f"{ALLOWLIST.name}:{number}: reason is not one"
        assert "(" in site or site.endswith("-> return"), f"{ALLOWLIST.name}:{number}: {site}"


def test_the_ratchet_fails_on_an_unlisted_any(tmp_path: Path) -> None:
    """Negative control: drop one allowlist entry and the gate must go red."""
    kept = [
        line
        for line in ALLOWLIST.read_text(encoding="utf-8").splitlines()
        if not line.strip().startswith("axeyum._native.BvValue.__eq__ -> return")
    ]
    backup = tmp_path / "backup.txt"
    backup.write_text(ALLOWLIST.read_text(encoding="utf-8"), encoding="utf-8")
    try:
        ALLOWLIST.write_text("\n".join(kept) + "\n", encoding="utf-8")
        completed = subprocess.run(
            [sys.executable, str(ROOT / "tools" / "check_stub_types.py")],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
            timeout=300,
        )
        assert completed.returncode == 1, completed.stdout
        assert "not in ANY_ALLOWLIST.txt" in completed.stdout
    finally:
        ALLOWLIST.write_text(backup.read_text(encoding="utf-8"), encoding="utf-8")


def test_smt_solve_is_typed() -> None:
    fn = _function("axeyum._native.smt", "solve")
    assert _annotation(_parameter(fn, "script").annotation) == "builtins.str"
    assert _annotation(_parameter(fn, "timeout_ms").annotation) == "builtins.int"
    assert _parameter(fn, "timeout_ms") in fn.args.kwonlyargs, "timeout_ms must be keyword-only"
    assert _annotation(fn.returns) == "Outcome"


def test_outcome_replay_returns_bool() -> None:
    fn = _function("axeyum._native.smt", "Outcome", "replay")
    assert _annotation(fn.returns) == "builtins.bool"


def test_cas_factor_is_typed() -> None:
    fn = _function("axeyum._native.cas", "factor")
    assert _annotation(_parameter(fn, "expr").annotation) == "Expr"
    assert _annotation(_parameter(fn, "var").annotation) == "builtins.str"
    assert _annotation(fn.returns) == "typing.Optional[Expr]"


def test_kernel_axiom_footprint_is_typed() -> None:
    fn = _function("axeyum._native.kernel", "Kernel", "axiom_footprint")
    # `str | NameId`: the accessor takes either, and refusing a NameId from
    # another kernel is the one distinction that matters here.
    name = _annotation(_parameter(fn, "name").annotation)
    assert "builtins.str" in name and "NameId" in name, name
    assert _annotation(fn.returns) == "builtins.list[builtins.str]"


def test_rationals_come_back_as_fractions() -> None:
    """`Fraction`, not `Any`: the exactness is the whole point of the CAS."""
    fn = _function("axeyum._native.cas", "Rational", "to_fraction")
    assert _annotation(fn.returns) == "fractions.Fraction"


def test_stubtest_agrees_with_the_runtime() -> None:
    """The only checker here that compares the stubs to the built `.so` as types."""
    if shutil.which("stubtest") is None and not _mypy_present():
        pytest.skip("mypy is not installed; `uv sync --dev` provisions it")
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "mypy.stubtest",
            "axeyum._native",
            "--ignore-missing-stub",
            "--ignore-positional-only",
            "--mypy-config-file",
            "tools/stubtest-mypy.ini",
            "--allowlist",
            "tools/stubtest-allowlist.txt",
            "--concise",
        ],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
        timeout=900,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr


def _mypy_present() -> bool:
    try:
        import mypy  # noqa: F401
    except ImportError:
        return False
    return True
