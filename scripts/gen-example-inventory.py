#!/usr/bin/env python3
"""Write the example-inventory COUNT into the two files that pin it (ADR-0539).

`docs/reference/examples.md` needs a hand-written row per example — what it is
FOR, which section it belongs in, whether it writes files. None of that is
derivable, and `check-parity-docs.py` rightly demands it.

The COUNT is different. `all N checked-in Cargo examples` is a derived integer,
and on 2026-08-21 it went stale **eight times in one working day** as concurrent
lanes added examples: 108 -> 113 -> 118 -> 119 -> 121 -> 122 -> 123 -> 124. Each
time the next lane to push found the gate red for a reason unrelated to its
change. One lane paid it five times and set the number wrong twice, because the
rule for deriving it ("count tracked files; a catalogue row is not a file")
existed only inside the gate.

So the count is generated here and the prose is not.

THE POPULATION IS IMPORTED, NOT REIMPLEMENTED. `check-parity-docs.py` decides
what counts as an example; this script asks it. Two scripts with two globs would
eventually disagree, and the disagreement would look like a stale number rather
than like a bug -- which is the whole failure mode being fixed.

Usage:
    python3 scripts/gen-example-inventory.py            # rewrite the markers
    python3 scripts/gen-example-inventory.py --check    # fail if they are stale
"""

from __future__ import annotations

import importlib.util
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

#: (path, regex with one capture group around the integer)
MARKERS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("docs/documentation-plan.md", re.compile(r"all (\d+) checked-in Cargo examples")),
    ("docs/plan/global/30-workstream-state.md", re.compile(r"all (\d+) Cargo examples")),
)


def tracked_example_count() -> int:
    """The number of Cargo examples, per `check-parity-docs.py`'s own definition."""
    spec = importlib.util.spec_from_file_location(
        "check_parity_docs", ROOT / "scripts" / "check-parity-docs.py"
    )
    if spec is None or spec.loader is None:
        raise SystemExit("cannot load check-parity-docs.py to read the population")
    module = importlib.util.module_from_spec(spec)
    sys.modules["check_parity_docs"] = module
    spec.loader.exec_module(module)
    return len(module._tracked_examples())  # noqa: SLF001 - one definition, deliberately


def main(argv: list[str]) -> int:
    check = "--check" in argv[1:]
    count = tracked_example_count()
    stale: list[str] = []
    for relative, pattern in MARKERS:
        path = ROOT / relative
        text = path.read_text(encoding="utf-8")
        found = pattern.search(text)
        if found is None:
            print(f"EXAMPLE_INVENTORY_ERROR|{relative}: no marker matching {pattern.pattern!r}")
            return 2
        if int(found.group(1)) == count:
            continue
        stale.append(f"{relative} says {found.group(1)}, tracked is {count}")
        if not check:
            path.write_text(
                pattern.sub(lambda m: m.group(0).replace(m.group(1), str(count), 1), text, count=1),
                encoding="utf-8",
            )

    print(f"EXAMPLE_INVENTORY|examples={count}|markers={len(MARKERS)}|stale={len(stale)}")
    if stale and check:
        for line in stale:
            print(f"  STALE {line}")
        print("  regenerate: python3 scripts/gen-example-inventory.py  (then gen-plan.py)")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
