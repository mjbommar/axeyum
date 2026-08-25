#!/usr/bin/env python3
"""The TYPE ratchet for the generated `axeyum._native` stubs.

`tools/gen_native_stub.py` proves the stubs have the right NAMES and ARITY.
This proves they carry real TYPES, and that every `typing.Any` left in them is
one somebody wrote down a reason for.

Why a ratchet and not a threshold: the stubs are generated from the Rust
signatures by `cargo run -p axeyum-py --features stub-gen --bin stub_gen`, so
`Any` appears in exactly one situation -- a Rust signature that says
`Bound<'_, PyAny>`, i.e. "some Python object". Each of those is either a real
polymorphic surface (`Rational.coerce` takes an `int`, a `fractions.Fraction`
or a `Rational`) or a signature that has not been tightened yet. The two are
indistinguishable from a count, so they are distinguished by name:
`python/axeyum/_native/ANY_ALLOWLIST.txt` lists every site, with the reason,
and this gate fails on any site that is not listed **and** on any listed site
that no longer exists. The count can only go down.

Site keys look like::

    axeyum._native.cas.Rational.coerce(value)
    axeyum._native.cas.Rational.to_fraction -> return

Usage::

    uv run --no-sync python tools/check_stub_types.py
    uv run --no-sync python tools/check_stub_types.py --show

Prints ``STUB_TYPES|params=P|typed=T|any=A|allowlisted=L|return_any=R`` and
exits nonzero when `A` exceeds `L`, when a site is unlisted, when a listed site
has vanished, or when it examined **zero** stub files -- the last because a
checker pointed at an empty directory reports a clean tree, which this
repository has shipped at three other layers.
"""

from __future__ import annotations

import argparse
import ast
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
STUB_PKG = REPO_ROOT / "python" / "axeyum" / "_native"
ALLOWLIST = STUB_PKG / "ANY_ALLOWLIST.txt"

# Receivers, which carry no useful annotation and are not counted as parameters.
RECEIVERS = frozenset({"self", "cls"})

# The lowest parameter-typing rate this gate accepts, as a percentage. It is a
# floor on a generated artifact, so a drop means a Rust signature got looser.
MIN_TYPED_PERCENT = 90.0


def module_name(path: Path) -> str:
    """`python/axeyum/_native/cas/certify/sos/__init__.pyi` -> the dotted module."""
    relative = path.relative_to(REPO_ROOT / "python").with_suffix("")
    parts = list(relative.parts)
    if parts[-1] == "__init__":
        parts.pop()
    return ".".join(parts)


def mentions_any(node: ast.expr | None) -> bool:
    """Whether an annotation expression mentions `typing.Any` (or bare `Any`)."""
    if node is None:
        return False
    for sub in ast.walk(node):
        if isinstance(sub, ast.Name) and sub.id == "Any":
            return True
        if isinstance(sub, ast.Attribute) and sub.attr == "Any":
            return True
    return False


class Scan:
    """One walk over one stub file."""

    def __init__(self, module: str) -> None:
        self.module = module
        self.params = 0
        self.typed = 0
        self.sites: list[str] = []
        self.return_any = 0

    def visit(self, body: list[ast.stmt], scope: str) -> None:
        for node in body:
            if isinstance(node, ast.ClassDef):
                self.visit(node.body, f"{scope}.{node.name}" if scope else node.name)
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                self.function(node, scope)

    def function(self, node: ast.FunctionDef | ast.AsyncFunctionDef, scope: str) -> None:
        qualified = f"{self.module}.{scope}.{node.name}" if scope else f"{self.module}.{node.name}"
        arguments = node.args
        every = [
            *arguments.posonlyargs,
            *arguments.args,
            *([arguments.vararg] if arguments.vararg else []),
            *arguments.kwonlyargs,
            *([arguments.kwarg] if arguments.kwarg else []),
        ]
        for index, argument in enumerate(every):
            if index == 0 and argument.arg in RECEIVERS:
                continue
            self.params += 1
            if mentions_any(argument.annotation):
                self.sites.append(f"{qualified}({argument.arg})")
            else:
                self.typed += 1
        if mentions_any(node.returns):
            self.sites.append(f"{qualified} -> return")
            self.return_any += 1


def read_allowlist() -> dict[str, str]:
    """`{site: reason}` from the committed allowlist; comments and blanks ignored."""
    if not ALLOWLIST.is_file():
        return {}
    entries: dict[str, str] = {}
    for number, raw in enumerate(ALLOWLIST.read_text(encoding="utf-8").splitlines(), start=1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        site, separator, reason = line.partition("  ")
        if not separator or not reason.strip():
            raise SystemExit(
                f"STUB_TYPES|FAIL {ALLOWLIST.name}:{number}: every entry needs a reason, "
                "separated from the site by two spaces"
            )
        entries[site.strip()] = reason.strip()
    return entries


def main() -> int:
    parser = argparse.ArgumentParser(description="Type ratchet for the generated stubs.")
    parser.add_argument("--show", action="store_true", help="list every `Any` site and its reason")
    args = parser.parse_args()

    files = sorted(STUB_PKG.rglob("*.pyi"))
    params = typed = return_any = 0
    sites: list[str] = []
    for path in files:
        scan = Scan(module_name(path))
        scan.visit(ast.parse(path.read_text(encoding="utf-8")).body, "")
        params += scan.params
        typed += scan.typed
        return_any += scan.return_any
        sites.extend(scan.sites)

    allowed = read_allowlist()
    unlisted = sorted(site for site in sites if site not in allowed)
    stale = sorted(set(allowed) - set(sites))

    print(
        f"STUB_TYPES|params={params}|typed={typed}|any={len(sites)}"
        f"|allowlisted={len(allowed)}|return_any={return_any}"
    )

    if args.show:
        for site in sorted(sites):
            print(f"  {site}: {allowed.get(site, '** NOT ALLOWLISTED **')}")

    failed = False
    if not files:
        print(
            f"STUB_TYPES|FAIL no stub file was read from {STUB_PKG} -- a check that "
            "examined nothing is not a pass"
        )
        return 1
    if len(sites) > len(allowed):
        print(f"STUB_TYPES|FAIL {len(sites)} `Any` sites exceed the {len(allowed)} allowlisted")
        failed = True
    if unlisted:
        print("STUB_TYPES|FAIL these `Any` sites are not in ANY_ALLOWLIST.txt:")
        for site in unlisted:
            print(f"  {site}")
        failed = True
    if stale:
        # The ratchet half: an allowlisted site that no longer has `Any` was
        # tightened, and the entry has to go so the budget cannot be re-spent.
        print("STUB_TYPES|FAIL these allowlist entries no longer name an `Any` site:")
        for site in stale:
            print(f"  {site}")
        failed = True

    percent = 100.0 * typed / params if params else 0.0
    if percent < MIN_TYPED_PERCENT:
        print(
            f"STUB_TYPES|FAIL {percent:.1f}% of parameters are typed, below the "
            f"{MIN_TYPED_PERCENT:.0f}% floor"
        )
        failed = True
    else:
        print(f"STUB_TYPES|typed_percent={percent:.1f}|files={len(files)}")

    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
