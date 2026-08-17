#!/usr/bin/env python3
"""Re-derive the R3 reachability census and pin the doc's tables to it.

`docs/mathematics-2026-08/04-reachability.md` R3: *"Point [the misconception
audit] at something adversarial -- the graph's `techniques`, or the `B`
(out-of-fragment) rows, which already name the fragment each would need. Those
17 rows are a ranked feature request written by the mathematics itself."*

The 17 could not be re-derived by anyone. The 2026-08-13 audit's `census.tsv`
was never committed -- only its prose survived, in
`docs/campaign-2026-08-13/agent-j-misconceptions/RESULT.md`, which tells you to
regenerate the counts with an `awk` line over a file that does not exist. So a
headline number reached two strand documents with no artifact behind it, and
when re-derived on 2026-08-17 it did not hold: one of the 17 was a *distractor
form* counted as a corpus row, and one genuine out-of-fragment row
(`infinity-minus-infinity-is-zero`) was missing. The measured count is 16.

`artifacts/reachability/r3-census.tsv` is that artifact, and this script is the
reason it cannot rot: the ranked table in the strand document is a **generated
view** of it, and this check fails when the two disagree.

Eight independent guards, each with its own rejection path and its own control
in `scripts/tests/test_check_reachability_census.py` -- deliberately not one
shared validity check with eight callers, which is the shape this repository
found six-of-seven guards removable behind.

Coverage before zeroes: the sibling `math-education` checkout is not part of
this repository, so [`corpus_coverage`] reports SKIPPED rather than passing
when it is absent. An empty result from a tool that was never pointed at the
corpus is not evidence that the corpus agrees.
"""

from __future__ import annotations

import collections
import os
import pathlib
import re
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
CENSUS = ROOT / "artifacts/reachability/r3-census.tsv"
DOC = ROOT / "docs/mathematics-2026-08/04-reachability.md"

# The sibling content repository. Not a dependency of this repository, and not
# required for the gate -- see `corpus_coverage`.
CORPUS_ROOT = pathlib.Path(
    os.environ.get(
        "AXEYUM_MATH_EDUCATION_GRAPH",
        os.path.expanduser("~/projects/personal/math-education/graph"),
    )
)
CORPUS_DIR = {"misconception": "misconceptions", "technique": "techniques"}

CLASSES = ("A", "B", "C", "DEP")
CORPORA = ("misconception", "technique")

# A floor, so a parser that has stopped matching cannot report a green zero.
# 148 misconception files + 42 technique files on 2026-08-13, unchanged since.
MIN_ROWS = 190


def read_census(path: pathlib.Path | None = None) -> list[dict[str, str]]:
    """`[{corpus, slug, class, fragment, note}]`, comments and header dropped."""
    text = (path or CENSUS).read_text(encoding="utf-8")
    rows: list[dict[str, str]] = []
    for line in text.splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        cells = line.split("\t")
        if cells[0] == "corpus":
            continue
        cells += [""] * (5 - len(cells))
        rows.append(
            {
                "corpus": cells[0],
                "slug": cells[1],
                "class": cells[2],
                "fragment": cells[3],
                "note": cells[4],
            }
        )
    return rows


def totals(rows: list[dict[str, str]]) -> dict[str, dict[str, int]]:
    """`corpus -> {class -> count}`, every class present so a zero is visible."""
    out = {c: dict.fromkeys(CLASSES, 0) for c in CORPORA}
    for row in rows:
        if row["corpus"] in out and row["class"] in CLASSES:
            out[row["corpus"]][row["class"]] += 1
    return out


def ranking(rows: list[dict[str, str]]) -> list[tuple[str, int, int, int]]:
    """`[(fragment, rows, from_misconceptions, from_techniques)]`, ranked.

    Ranked by row count descending, then by fragment name -- a total order, so
    the generated table is byte-stable and a tie cannot silently reorder it.
    """
    by_fragment: dict[str, collections.Counter[str]] = collections.defaultdict(
        collections.Counter
    )
    for row in rows:
        if row["class"] == "B":
            by_fragment[row["fragment"]][row["corpus"]] += 1
    return sorted(
        (
            (name, sum(counts.values()), counts["misconception"], counts["technique"])
            for name, counts in by_fragment.items()
        ),
        key=lambda entry: (-entry[1], entry[0]),
    )


def doc_table(name: str, text: str | None = None) -> list[list[str]] | None:
    """The rows of the markdown table between `<!-- name:BEGIN/END -->`.

    `None` means the anchors are missing, which is distinct from an empty
    table: one is a broken document, the other is a real (and failing) claim.
    """
    text = text if text is not None else DOC.read_text(encoding="utf-8")
    block = re.search(
        rf"<!--\s*{re.escape(name)}:BEGIN.*?-->(?P<body>.*?)<!--\s*{re.escape(name)}:END\s*-->",
        text,
        re.S,
    )
    if not block:
        return None
    out: list[list[str]] = []
    for line in block["body"].splitlines():
        line = line.strip()
        if not line.startswith("|"):
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        if all(re.fullmatch(r":?-+:?", cell) for cell in cells):
            continue
        out.append(cells)
    return out[1:] if out else out


def corpus_coverage(rows: list[dict[str, str]]) -> tuple[list[str], bool]:
    """`(failures, checked)`. `checked=False` means the corpus was not present.

    Both directions: a censused slug that no longer exists, and a corpus file
    that the census never classified. The second is the one that matters --
    a census silently missing rows is exactly how the count drifted before.
    """
    if not CORPUS_ROOT.is_dir():
        return [], False
    failures: list[str] = []
    for corpus, directory in CORPUS_DIR.items():
        path = CORPUS_ROOT / directory
        if not path.is_dir():
            return [], False
        on_disk = {file.stem for file in path.glob("*.md")}
        censused = {row["slug"] for row in rows if row["corpus"] == corpus}
        for slug in sorted(censused - on_disk):
            failures.append(
                f"{corpus} `{slug}` is censused but no longer exists in the corpus"
            )
        for slug in sorted(on_disk - censused):
            failures.append(
                f"{corpus} `{slug}` exists in the corpus and is not censused -- "
                "the denominator is wrong, which is how `17` happened"
            )
    return failures, True


def evaluate(
    rows: list[dict[str, str]], doc: str | None = None
) -> tuple[list[str], dict[str, Any]]:
    """`(failures, report)`. Each guard has its own rejection path."""
    failures: list[str] = []
    doc_text = doc if doc is not None else DOC.read_text(encoding="utf-8")

    # G1 -- closed class and corpus vocabulary.
    for row in rows:
        if row["class"] not in CLASSES:
            failures.append(
                f"`{row['slug']}` has class `{row['class']}`, which is not one of "
                f"{'/'.join(CLASSES)}"
            )
        if row["corpus"] not in CORPORA:
            failures.append(
                f"`{row['slug']}` names corpus `{row['corpus']}`, which is not one "
                f"of {'/'.join(CORPORA)}"
            )

    # G2 -- `fragment` is non-empty EXACTLY for B. A B row with no fragment is
    # a decline with no feature request in it; a non-B row with one is a claim
    # that would inflate the ranking.
    for row in rows:
        if row["class"] == "B" and not row["fragment"]:
            failures.append(
                f"`{row['slug']}` is out of fragment and names no fragment it "
                "would need -- the ranking is what this census is for"
            )
        if row["class"] != "B" and row["fragment"]:
            failures.append(
                f"`{row['slug']}` is class {row['class']} and still names fragment "
                f"`{row['fragment']}`; only B rows contribute to the ranking"
            )

    # G3 -- one row per corpus entry.
    seen: collections.Counter[tuple[str, str]] = collections.Counter(
        (row["corpus"], row["slug"]) for row in rows
    )
    for (corpus, slug), count in sorted(seen.items()):
        if count > 1:
            failures.append(f"{corpus} `{slug}` is censused {count} times")

    # G4 -- the floor.
    if len(rows) < MIN_ROWS:
        failures.append(
            f"{len(rows)} census rows, floor {MIN_ROWS}; a census this small "
            "means the parser stopped matching, not that the corpus shrank"
        )

    derived_totals = totals(rows)
    derived_ranking = ranking(rows)

    # G5 -- the doc's totals table is a view of the census.
    stated = doc_table("R3-TOTALS", doc_text)
    if stated is None:
        failures.append("04-reachability.md has no `R3-TOTALS` anchored table")
    else:
        want = [
            [corpus, str(sum(derived_totals[corpus].values()))]
            + [str(derived_totals[corpus][cls]) for cls in ("A", "B", "C")]
            for corpus in CORPORA
        ]
        if stated != want:
            failures.append(
                f"the `R3-TOTALS` table in 04-reachability.md says {stated} and the "
                f"census says {want}"
            )

    # G6 -- the doc's ranking table is a view of the census, ORDER INCLUDED.
    stated_rank = doc_table("R3-RANKING", doc_text)
    if stated_rank is None:
        failures.append("04-reachability.md has no `R3-RANKING` anchored table")
    else:
        want_rank = [
            [name, str(count), str(misc), str(tech)]
            for name, count, misc, tech in derived_ranking
        ]
        if stated_rank != want_rank:
            failures.append(
                f"the `R3-RANKING` table in 04-reachability.md says {stated_rank} "
                f"and the census ranks {want_rank}"
            )

    # G7 -- the ranking must actually rank something.
    if not derived_ranking:
        failures.append(
            "no B rows carry a fragment, so the census ranks nothing; R3 exists "
            "to produce a ranked feature request"
        )

    # G8 -- coverage of the corpus, in both directions, when it is reachable.
    coverage_failures, coverage_checked = corpus_coverage(rows)
    failures.extend(coverage_failures)

    return failures, {
        "rows": len(rows),
        "totals": derived_totals,
        "ranking": derived_ranking,
        "coverage_checked": coverage_checked,
    }


def main(argv: list[str]) -> int:
    quiet = "--quiet" in argv
    rows = read_census()
    failures, report = evaluate(rows)

    if not quiet:
        for corpus in CORPORA:
            counts = report["totals"][corpus]
            print(
                f"  {corpus:14s} "
                + " ".join(f"{cls}={counts[cls]:3d}" for cls in CLASSES)
            )
        print("  ranked feature request (B rows, by fragment):")
        for name, count, misc, tech in report["ranking"]:
            print(f"    {name:30s} {count:3d}  (misconceptions {misc}, techniques {tech})")

    coverage = "checked" if report["coverage_checked"] else "SKIPPED-no-corpus"
    print(
        f"REACHABILITY_CENSUS|rows={report['rows']}|"
        f"fragments={len(report['ranking'])}|"
        f"top={report['ranking'][0][0] if report['ranking'] else 'NONE'}|"
        f"top_rows={report['ranking'][0][1] if report['ranking'] else 0}|"
        f"corpus_coverage={coverage}"
    )
    for failure in failures:
        print(f"REACHABILITY_CENSUS_ERROR|{failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
