#!/usr/bin/env python3
"""Validate the exact cross-shard population and finite-range claim."""

from __future__ import annotations

import json
import argparse
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SHARDS = ROOT / "artifacts/gf2/lemire/range-1-400/shards"
FACT = ROOT / "artifacts/facts/F-gf2-lemire-half-degree-through-400.json"
EXPECTED_STATEMENT = {
    "field_order": 2,
    "format": "axeyum-gf2-half-degree-range-statement",
    "irreducible": True,
    "max_degree": 400,
    "min_degree": 1,
    "monic": True,
    "tail_degree_bound": "floor(n/2)",
    "version": 1,
}
EXPECTED = (
    ("shard-1-80", 1, 80, "axeyum-gf2-search@6e1372073/binary=fcd47dd883b3/host=s1"),
    ("shard-81-160", 81, 160, "axeyum-gf2-search@6e1372073/host=s4"),
    ("shard-161-240", 161, 240, "axeyum-gf2-search@6e1372073/host=s5"),
    ("shard-241-320", 241, 320, "axeyum-gf2-search@6e1372073/host=s6"),
    ("shard-321-400", 321, 400, "axeyum-gf2-search@6e1372073/host=s7"),
)


def fail(message: str) -> None:
    raise SystemExit(f"GF2_RANGE|status=FAIL|error={message}")


def check(shards: Path) -> None:
    try:
        fact = json.loads(FACT.read_text(encoding="utf-8"))
        statement_json = fact["formal"]["statement"]
        statement = json.loads(statement_json)
    except (OSError, KeyError, TypeError, json.JSONDecodeError) as error:
        fail(f"{FACT}: {error}")
    if fact.get("id") != "F:gf2-lemire-half-degree-through-400":
        fail("finite-range fact identity differs")
    if fact.get("epistemic_status") != "computed":
        fail("finite-range fact must remain computed")
    if fact.get("proof_route") != "search-certificate":
        fail("finite-range fact must remain on the search-certificate route")
    if fact.get("formal", {}).get("language") != "certificate-spec":
        fail("finite-range fact formal language differs")
    canonical_statement_json = json.dumps(
        statement, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    )
    if statement_json != canonical_statement_json:
        fail("finite-range fact formal statement is not canonical")
    if statement != EXPECTED_STATEMENT:
        fail("finite-range fact formal statement differs")

    observed_names = sorted(path.name for path in shards.iterdir() if path.is_dir())
    expected_names = sorted(name for name, _, _, _ in EXPECTED)
    if observed_names != expected_names:
        fail("shard directory population differs")

    rows: list[dict[str, object]] = []
    for name, start, end, producer in EXPECTED:
        path = shards / name / "manifest.json"
        try:
            manifest = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            fail(f"{path}: {error}")
        if manifest.get("format") != "axeyum-gf2-lemire-search-shard":
            fail(f"{name}: format differs")
        if manifest.get("version") != 1:
            fail(f"{name}: version differs")
        if manifest.get("producer") != producer:
            fail(f"{name}: producer identity differs")
        if (manifest.get("start_degree"), manifest.get("end_degree")) != (start, end):
            fail(f"{name}: degree range differs")
        if manifest.get("max_tail_terms") != 4:
            fail(f"{name}: sparse policy differs")
        if manifest.get("max_candidates_per_degree") != 2_000_000:
            fail(f"{name}: candidate ceiling differs")
        rows.extend(manifest.get("rows", []))

    degrees = [row.get("degree") for row in rows]
    if degrees != list(range(1, 401)):
        fail("combined degree population is not exactly 1..400")
    if any(row.get("status") != "found" for row in rows):
        fail("not every degree has a found receipt")
    tail_zero = sum(row.get("tail_terms") == 0 for row in rows)
    trinomials = sum(row.get("tail_terms") == 2 for row in rows)
    pentanomials = sum(row.get("tail_terms") == 4 for row in rows)
    if (tail_zero, trinomials, pentanomials) != (1, 227, 172):
        fail("tail-term distribution differs")
    candidates = sum(int(row.get("candidates_tested", 0)) for row in rows)
    hardest = max(rows, key=lambda row: int(row.get("candidates_tested", 0)))
    if candidates != 38_679:
        fail("aggregate candidate count differs")
    if (hardest.get("degree"), hardest.get("candidates_tested")) != (349, 870):
        fail("hardest-degree measurement differs")
    print(
        "GF2_RANGE|status=PASS|degrees=400|found=400|trinomials=227|"
        "pentanomials=172|candidates=38679|max_candidates=870|hardest_degree=349"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--shards", type=Path, default=SHARDS)
    arguments = parser.parse_args()
    check(arguments.shards)


if __name__ == "__main__":
    main()
