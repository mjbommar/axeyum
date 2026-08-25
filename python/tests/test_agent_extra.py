"""The `[agent]` extra is declared, exact-pinned, and out of the gates' way.

This module imports nothing from the extra on purpose. Every other agent test
skips when `pydantic_ai` is absent, and a suite that is entirely skippable is a
gate that can go silently inert -- the failure this repository has hit
repeatedly. These four assertions run on the standard library and always fire.
"""

from __future__ import annotations

import pathlib
import re
import tomllib

ROOT = pathlib.Path(__file__).resolve().parents[2]
PYPROJECT = ROOT / "pyproject.toml"

EXPECTED = {
    "pydantic-ai-slim[anthropic]": "2.33.0",
    "pydantic-graph": "2.33.0",
    "pydantic-evals": "2.33.0",
    # Slice A6. `axeyum.agent.sandbox` runs `sys.executable`, so its import
    # whitelist can only name a module the extra actually installs -- a
    # whitelist entry for an absent module is a capability that exists in a
    # docstring and nowhere else.
    "sympy": "1.14.0",
}


def _extra() -> list[str]:
    document = tomllib.loads(PYPROJECT.read_text(encoding="utf-8"))
    return document["project"]["optional-dependencies"]["agent"]


def test_agent_extra_is_declared() -> None:
    assert _extra(), "pyproject declares no [agent] extra"


def test_every_agent_pin_is_exact() -> None:
    """`==`, never `>=`. 2.33.0 exists BECAUSE anthropic 1.0.0 broke unpinned
    installs on 2026-08-20; a range would let that recur silently."""
    for requirement in _extra():
        assert re.search(r"==\d+\.\d+\.\d+$", requirement), f"not exact-pinned: {requirement}"


def test_the_expected_packages_are_pinned_to_the_expected_versions() -> None:
    pins = dict(part.split("==", 1) for part in _extra())
    assert pins == EXPECTED


def test_no_script_imports_the_agent_package() -> None:
    """Every gate in `just check` runs on the standard library.

    A checker importing `pydantic` would make a fresh-machine `./scripts/check.sh`
    require a network install, and the repository would lose the property that
    its trusted checking runs anywhere. The episode artifact is how the two
    worlds meet, and it is JSON on disk.
    """
    offenders = [
        path.name
        for path in sorted((ROOT / "scripts").rglob("*.py"))
        if re.search(
            r"^\s*(?:from|import)\s+(?:axeyum\.agent|pydantic)",
            path.read_text(encoding="utf-8", errors="replace"),
            re.MULTILINE,
        )
    ]
    assert offenders == [], f"scripts/ must stay stdlib-only, but these import it: {offenders}"
