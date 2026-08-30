#!/usr/bin/env python3
"""Re-derive the import strand's locally-verifiable counts from the tree.

`docs/formalized-math-2026-08/README.md` carries a status block that says what
the Lean-import path currently is. On 2026-08-16 that block was stale on nearly
every line — it still said `Nat.add_comm` could not be imported (it can: 52
declarations, `axioms=none`), that the Init/Std/Mathlib population was
UNSTARTED (two seeded censuses had been run and retained), and it undercounted
the pinned streams and test suites. None of that was wrong when written; it went
stale, silently, while the strand's own diaries moved past it.

That matters more here than a wrong number usually would. This block is what a
reader — human or agent — uses to pick the next goal, so a stale block does not
merely misinform, it **routes work at problems that are already solved**. The
strand spent its "what to do first" slot on a decline census that had already
been run twice.

So the counts a checkout can verify without network or a Lean toolchain are
verified here, and the block names them as verified. The census numbers are
NOT checked: reproducing them needs a built `lean4export`, and the README says
so explicitly rather than implying this gate covers them. A checker that
silently appeared to cover more than it does would be the same failure one level
up.
"""

from __future__ import annotations

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
README = ROOT / "docs/formalized-math-2026-08/README.md"
IMPORT_CRATE = ROOT / "crates/axeyum-lean-import"
STREAMS = ROOT / "artifacts/lean-imports"
FACTS = ROOT / "artifacts/facts"
IMPORTED_ROUTE = "imported-kernel-lean"


def measured() -> dict[str, int]:
    records = sum(
        sum(1 for _ in path.open(encoding="utf-8"))
        for path in sorted(STREAMS.glob("*.ndjson"))
    )
    facts = sum(
        1
        for path in FACTS.glob("*.json")
        if IMPORTED_ROUTE in path.read_text(encoding="utf-8")
    )
    return {
        "test suites": len(list((IMPORT_CRATE / "tests").glob("*.rs"))),
        "examples": len(list((IMPORT_CRATE / "examples").glob("*.rs"))),
        "pinned streams": len(list(STREAMS.glob("*.ndjson"))),
        "records": records,
        "facts": facts,
    }


# Each claim is (label, regex over the README, key into `measured()`). The
# patterns are anchored on the surrounding words rather than on bare integers,
# so they cannot drift onto an unrelated number elsewhere in the document.
CLAIMS: tuple[tuple[str, re.Pattern[str], str], ...] = (
    ("test suites", re.compile(r"(\d+) test suites"), "test suites"),
    ("examples", re.compile(r"(\d+) examples"), "examples"),
    ("pinned streams", re.compile(r"(\d+) pinned streams"), "pinned streams"),
    ("records", re.compile(r"([\d,]+) records"), "records"),
    (
        "imported facts",
        re.compile(r"(\d+) facts on proof_route `imported-kernel-lean`"),
        "facts",
    ),
)


def evaluate(text: str, values: dict[str, int]) -> list[str]:
    """Claims in `text` that disagree with `values`, or that stopped matching."""
    failures: list[str] = []
    for label, pattern, key in CLAIMS:
        # EVERY occurrence, not the first. `search` stops at the first hit, so a
        # claim repeated further down the document was invisible to this check.
        # Measured 2026-08-30: the README states `test suites` TWICE -- once in
        # the prose at "a fail-closed importer ... with N test suites" and again
        # in the "Verified on this host" table -- and editing the table's copy to
        # 99 left this gate exiting 0. Only the prose copy was ever gating, and
        # nothing said so. A duplicated claim is exactly the drift this check
        # exists to catch, so all of them are compared.
        matches = list(pattern.finditer(text))
        if not matches:
            failures.append(
                f"no `{label}` claim found in the status block; this check has "
                "stopped matching and is gating nothing"
            )
            continue
        for match in matches:
            claimed = int(match.group(1).replace(",", ""))
            if claimed != values[key]:
                failures.append(
                    f"{label}: README claims {claimed}, tree has {values[key]}"
                )
    return failures


def main() -> int:
    values = measured()
    failures = evaluate(README.read_text(encoding="utf-8"), values)
    print(
        "IMPORT_STATUS|"
        + "|".join(f"{key.replace(' ', '_')}={value}" for key, value in values.items())
    )
    for failure in failures:
        print(f"IMPORT_STATUS_ERROR|{failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
