#!/usr/bin/env python3
"""Every route the capability table names must exist in the code.

`docs/mathematics-2026-08/01-decide-vs-certify.md` item A: *"Re-derive the
capability table from the code rather than maintaining it by hand. A 1,908-line
hand-written table of what the system can do is the same category of artifact as
a guard that exists only in a comment. It should be generated, **or at minimum
gated against the routes it describes**."*

This is that minimum. Generating the whole table is a much larger job — the
`feature` and `evidence` fields carry reasoning, boundaries, and measured
numbers that no signature can produce. But the table also names the FUNCTION for
each capability, by convention in parentheses:

    "CERTIFIED Craig interpolation (lra_interpolant_certified): the same ..."

and that half is checkable. A row naming a route that no longer exists is the
table's cheapest lie: the capability reads as real, the name looks authoritative,
and nothing anywhere notices when the function is renamed or deleted.

Measured 2026-08-17 when this landed: 42 routes named, 0 missing. So it is a
ratchet, not a repair — it exists to keep that true through the renames this
repository does constantly.

# What counts as a route, and why the filter is not stricter

A parenthesized snake_case identifier, or a `path::qualified` one. A parenthesised
ENGLISH word is prose — "Condition 3 (vocabulary) carries no refutation" — so a
candidate with neither `_` nor `::` is skipped. Both cases were found by writing
the naive version first: it reported `(vocabulary)` and `(nia_square)` as missing
routes, and the second is a MODULE, not a function, which is why definitions of
`mod`/`struct`/`enum`/`trait`/`type`/`const` count too.

The check is deliberately name-only. It does NOT verify that the named function
implements what the row claims — no static check can — and it does not require
the route to be public. Its whole claim is that the name resolves to something in
this workspace, which is exactly the property that decays silently.
"""

from __future__ import annotations

import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
TABLE = ROOT / "crates/axeyum-solver/src/capabilities.rs"

# `(some_route)` or `(module::some_route)`, as the `feature` convention writes it.
ROUTE = re.compile(r"\(([a-z_][a-z0-9_]*(?:::[a-z_][a-z0-9_]*)*)\)")
DEFINITION = re.compile(
    r"\b(?:fn|mod|struct|enum|trait|type|const)\s+([A-Za-z_][A-Za-z0-9_]*)"
)

# Measured 2026-08-17. A floor, so an extractor that goes blind is caught rather
# than reporting a clean zero.
MIN_ROUTES = 40


def entries(text: str) -> list[dict[str, str]]:
    """Reuse the sibling checker's parser so both read the table identically."""
    import importlib.util

    spec = importlib.util.spec_from_file_location(
        "check_capability_assurance", ROOT / "scripts" / "check-capability-assurance.py"
    )
    assert spec and spec.loader
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.entries(text)


def routes_in(feature: str) -> list[str]:
    """The routes a `feature` field names, prose in parentheses excluded."""
    return [
        hit
        for hit in ROUTE.findall(feature)
        if "_" in hit or "::" in hit
    ]


def definitions() -> set[str]:
    """Every item name defined anywhere in the workspace's Rust sources."""
    files = subprocess.run(
        ["git", "ls-files", "*.rs"], cwd=ROOT, capture_output=True, text=True, check=True
    ).stdout.split()
    found: set[str] = set()
    for rel in files:
        try:
            found.update(
                DEFINITION.findall((ROOT / rel).read_text(encoding="utf-8", errors="ignore"))
            )
        except OSError:
            continue
    return found


def evaluate(
    recs: list[dict[str, str]], defined: set[str]
) -> tuple[list[str], int]:
    failures: list[str] = []
    checked = 0
    for rec in recs:
        for route in routes_in(rec.get("feature", "")):
            checked += 1
            if route.split("::")[-1] not in defined:
                failures.append(
                    f"{rec['area']}: the capability names route `{route}`, and no `fn`, `mod`, "
                    "`struct`, `enum`, `trait`, `type` or `const` of that name exists in the "
                    "workspace. Either the route was renamed and the table was not, or the "
                    "capability is described by a name that never existed"
                )
    return failures, checked


def main(argv: list[str]) -> int:
    recs = entries(TABLE.read_text(encoding="utf-8"))
    defined = definitions()
    failures, checked = evaluate(recs, defined)

    if "--list" in argv:
        for rec in recs:
            for route in routes_in(rec.get("feature", "")):
                mark = "ok " if route.split("::")[-1] in defined else "MISSING"
                print(f"  {mark} {rec['area']:<22} {route}")

    print(
        f"CAPABILITY_ROUTES|rows={len(recs)}|routes={checked}|"
        f"definitions={len(defined)}|missing={len(failures)}"
    )

    if checked < MIN_ROUTES:
        failures.append(
            f"only {checked} routes were extracted (floor {MIN_ROUTES}); the `(route)` "
            "convention or the parser has changed, and zero missing routes would mean "
            "nothing"
        )
    if len(defined) < 1000:
        failures.append(
            f"only {len(defined)} definitions indexed; the source scan is broken and every "
            "route would look missing"
        )

    for failure in failures:
        print(f"CAPABILITY_ROUTES_ERROR|{failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
