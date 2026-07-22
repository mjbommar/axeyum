#!/usr/bin/env python3
"""Freeze or validate the preregistered SMT-COMP 2026 selection authority."""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import sys
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "docs/plan/smtcomp-official-selection-authority-v1.json"
SCHEMA = "axeyum-smtcomp-official-selection-authority-v1"
COMMIT = "401302678311593efcef8a79b614b33a3b853eac"
REPOSITORY = "https://github.com/SMT-COMP/smt-comp.github.io"
RAW_ROOT = f"https://raw.githubusercontent.com/SMT-COMP/smt-comp.github.io/{COMMIT}"
TREE_URL = (
    "https://api.github.com/repos/SMT-COMP/smt-comp.github.io/git/trees/"
    f"{COMMIT}?recursive=1"
)
RULES_URL = "https://smt-comp.github.io/2026/rules.pdf"
ZENODO_RECORD = 16740866
ZENODO_API = f"https://zenodo.org/api/records/{ZENODO_RECORD}"

EXPECTED = {
    "rules_sha256": "268e5c579ee9dd82bcf470f6c66f637c0656bf44f9488dd6347d1f25a2fb4974",
    "benchmark_sha256": "ba855e47e1ed88e2e6bb26272e84a20a0e8f0c320adc704b062f4c287e586a54",
    "benchmark_bytes": 3_239_841,
    "incremental_rows": 44_708,
    "non_incremental_rows": 450_472,
    "non_incremental_logics": 89,
    "new_non_incremental_rows": 3_445,
    "source_files": {
        "smtcomp/selection.py": "e4d5c9f9c8fc15ec500714f24e2c63aa439408109c9c9cc51b8243391223cdfb",
        "smtcomp/defs.py": "5c500314b6604fc763bede8de92cc4f9f913e42f771053ad737688e5f010bdc6",
        "pyproject.toml": "d3bcbdb9a058444d8720ae3c4aeefc923c0834ad105aa9e7a4091575d7083226",
        "poetry.lock": "8f57e76984579d949d2679eddab2b5cda5c63740d4ca656637390966b1791e4b",
    },
    "historical": {
        2018: (20_889_194, "f1b6353c1a20fd7856d584166ce619c8b0b901f7b4fd88057328e6b123bbb0e5"),
        2019: (11_770_723, "c3807ed94bc85a6be13bf443f334412e74984505dade028de08c63487f581e48"),
        2020: (8_755_041, "847a7335111b7018b4a32b2c1ec033c4971a056f321b3cf0c7b17bd9fce39590"),
        2021: (14_590_540, "a62a892549e069cef3b1f6df34ae343d815e2049741622e0bed2c29bb578365b"),
        2022: (11_096_210, "3794b37f84851c3f0404b3bfa3966dec1e051b4608a84ab2cd5fa2b0b96d7cfd"),
        2023: (12_636_621, "b3c0a11cf7cbf4aef8d6a93c81c8da018aadf7603b425d4a95f16efdabd1f680"),
        2024: (14_070_472, "bd2208c644b2f18520f08df49a797e2f8dbf1a829004c7eab76b4500b8cb5e99"),
    },
    "zenodo": {
        "concept_record": "15493089",
        "doi": "10.5281/zenodo.16740866",
        "version": "2025.08.04",
        "file_count": 90,
        "total_bytes": 4_890_207_406,
    },
    "submission_count": 53,
    "competitive_submission_count": 38,
    "competitive_seed_sum": 9_684_066_285,
    "submission_seed_modulo": 20_389_869,
    "nyse_seed": 2_341_289,
    "global_seed": 22_731_158,
}


class AuthorityError(ValueError):
    """The authority input or manifest violates the frozen contract."""


def canonical_json(value: Any) -> bytes:
    """Return the one canonical JSON representation used by this artifact."""
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def _fetch(url: str) -> bytes:
    request = urllib.request.Request(url, headers={"User-Agent": "axeyum-authority-freeze/1"})
    with urllib.request.urlopen(request, timeout=120) as response:
        return response.read()


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _expect(condition: bool, message: str) -> None:
    if not condition:
        raise AuthorityError(message)


def _github_entry(path: str, tree: dict[str, dict[str, Any]]) -> dict[str, Any]:
    data = _fetch(f"{RAW_ROOT}/{urllib.parse.quote(path)}")
    row = {
        "bytes": len(data),
        "git_blob": tree[path]["sha"],
        "path": path,
        "sha256": _sha256(data),
        "url": f"{RAW_ROOT}/{path}",
    }
    return {"entry": row, "data": data}


def refresh() -> dict[str, Any]:
    """Fetch the pinned immutable inputs and construct the canonical manifest."""
    tree_doc = json.loads(_fetch(TREE_URL))
    _expect(tree_doc.get("truncated") is False, "GitHub tree response is truncated")
    tree = {
        row["path"]: row
        for row in tree_doc["tree"]
        if row.get("type") == "blob"
    }

    source_paths = sorted(
        path
        for path in tree
        if (path.startswith("smtcomp/") and path.endswith(".py"))
        or path in {"README.md", "poetry.lock", "pyproject.toml"}
    )
    _expect(len(source_paths) == 29, f"expected 29 organizer source files, got {len(source_paths)}")
    source_rows = [_github_entry(path, tree)["entry"] for path in source_paths]
    source_by_path = {row["path"]: row for row in source_rows}
    for path, expected_sha in EXPECTED["source_files"].items():
        _expect(source_by_path[path]["sha256"] == expected_sha, f"source hash drift: {path}")

    benchmark_path = "data/benchmarks-2026.json.gz"
    benchmark_fetch = _github_entry(benchmark_path, tree)
    benchmark_bytes = benchmark_fetch["data"]
    benchmark_entry = benchmark_fetch["entry"]
    _expect(benchmark_entry["bytes"] == EXPECTED["benchmark_bytes"], "benchmark metadata size drift")
    _expect(benchmark_entry["sha256"] == EXPECTED["benchmark_sha256"], "benchmark metadata hash drift")
    benchmark_doc = json.loads(gzip.decompress(benchmark_bytes))
    non_incremental = benchmark_doc["non_incremental"]
    benchmark_counts = {
        "incremental_rows": len(benchmark_doc["incremental"]),
        "new_non_incremental_rows": sum(
            1
            for row in non_incremental
            if row["file"]["family"] and row["file"]["family"][0].startswith("2025")
        ),
        "non_incremental_logics": len({row["file"]["logic"] for row in non_incremental}),
        "non_incremental_rows": len(non_incremental),
    }
    for field, value in benchmark_counts.items():
        _expect(value == EXPECTED[field], f"benchmark count drift: {field}")

    historical_rows = []
    for year, (expected_bytes, expected_sha) in EXPECTED["historical"].items():
        path = f"data/results-sq-{year}.json.gz"
        fetched = _github_entry(path, tree)["entry"]
        _expect(fetched["bytes"] == expected_bytes, f"historical result size drift: {year}")
        _expect(fetched["sha256"] == expected_sha, f"historical result hash drift: {year}")
        historical_rows.append({"year": year, **fetched})

    submission_paths = sorted(
        path for path in tree if path.startswith("submissions/") and path.endswith(".json")
    )
    _expect(
        len(submission_paths) == EXPECTED["submission_count"],
        f"expected {EXPECTED['submission_count']} submissions, got {len(submission_paths)}",
    )
    submission_rows = []
    competitive_seed_sum = 0
    competitive_count = 0
    missing_competitive_seeds = 0
    for path in submission_paths:
        fetched = _github_entry(path, tree)
        document = json.loads(fetched["data"])
        competitive = document.get("competitive", True)
        seed = document.get("seed")
        if seed is not None:
            seed = int(seed)
        if competitive:
            competitive_count += 1
            if seed is None:
                missing_competitive_seeds += 1
            else:
                competitive_seed_sum += seed
        submission_rows.append(
            {
                **fetched["entry"],
                "competitive": competitive,
                "name": document["name"],
                "seed": seed,
            }
        )
    seed_modulo = competitive_seed_sum % (2**30)
    global_seed = seed_modulo + EXPECTED["nyse_seed"]
    _expect(competitive_count == EXPECTED["competitive_submission_count"], "competitive count drift")
    _expect(missing_competitive_seeds == 0, "competitive submission seed is missing")
    _expect(competitive_seed_sum == EXPECTED["competitive_seed_sum"], "competitive seed sum drift")
    _expect(seed_modulo == EXPECTED["submission_seed_modulo"], "seed modulo drift")
    _expect(global_seed == EXPECTED["global_seed"], "global seed drift")

    rules = _fetch(RULES_URL)
    _expect(_sha256(rules) == EXPECTED["rules_sha256"], "rules PDF hash drift")

    zenodo = json.loads(_fetch(ZENODO_API))
    zenodo_expected = EXPECTED["zenodo"]
    archive_rows = sorted(
        (
            {
                "bytes": row["size"],
                "md5": row["checksum"].removeprefix("md5:"),
                "name": row["key"],
                "url": row["links"]["self"],
            }
            for row in zenodo["files"]
        ),
        key=lambda row: row["name"],
    )
    _expect(str(zenodo["conceptrecid"]) == zenodo_expected["concept_record"], "Zenodo concept drift")
    _expect(zenodo["doi"] == zenodo_expected["doi"], "Zenodo DOI drift")
    _expect(zenodo["metadata"]["version"] == zenodo_expected["version"], "Zenodo version drift")
    _expect(len(archive_rows) == zenodo_expected["file_count"], "Zenodo file-count drift")
    _expect(sum(row["bytes"] for row in archive_rows) == zenodo_expected["total_bytes"], "Zenodo size drift")

    return {
        "benchmark_metadata": {**benchmark_entry, **benchmark_counts},
        "competition_year": 2026,
        "corpus_release": {
            "archives": archive_rows,
            "concept_record": int(zenodo_expected["concept_record"]),
            "doi": zenodo_expected["doi"],
            "record": ZENODO_RECORD,
            "title": zenodo["metadata"]["title"],
            "total_bytes": sum(row["bytes"] for row in archive_rows),
            "url": f"https://zenodo.org/records/{ZENODO_RECORD}",
            "version": zenodo_expected["version"],
        },
        "historical_results": historical_rows,
        "organizer": {
            "commit": COMMIT,
            "repository": REPOSITORY,
            "source_files": source_rows,
        },
        "policy": {
            "difficulty_cpu_seconds_inclusive": 1.0,
            "global_seed": global_seed,
            "large_logic_ratio": 0.1,
            "large_logic_threshold": 1000,
            "minimum_selected": 300,
            "new_family_prefix": "2025",
            "nyse_date": "2026-06-12",
            "nyse_seed": EXPECTED["nyse_seed"],
            "old_criteria": False,
            "previous_result_years": list(range(2018, 2025)),
            "ratio_selected": 0.5,
            "removed_benchmark_count": 2,
            "submission_seed_modulo": seed_modulo,
            "submission_seed_modulus": 2**30,
            "submission_seed_sum": competitive_seed_sum,
            "use_previous_results_for_status": False,
        },
        "rules": {
            "bytes": len(rules),
            "sha256": _sha256(rules),
            "url": RULES_URL,
        },
        "schema": SCHEMA,
        "submissions": submission_rows,
        "summary": {
            "archive_count": len(archive_rows),
            "competitive_submission_count": competitive_count,
            "missing_competitive_seed_count": missing_competitive_seeds,
            "organizer_source_file_count": len(source_rows),
            "submission_count": len(submission_rows),
        },
        "track": "single-query",
    }


def validate(document: dict[str, Any]) -> None:
    """Validate cross-field invariants without contacting the network."""
    _expect(document.get("schema") == SCHEMA, "wrong authority schema")
    _expect(document.get("competition_year") == 2026, "wrong competition year")
    _expect(document.get("track") == "single-query", "wrong track")
    _expect(document["rules"]["sha256"] == EXPECTED["rules_sha256"], "wrong rules hash")
    _expect(document["organizer"]["commit"] == COMMIT, "wrong organizer commit")

    sources = document["organizer"]["source_files"]
    _expect(sources == sorted(sources, key=lambda row: row["path"]), "source rows are not sorted")
    _expect(len({row["path"] for row in sources}) == len(sources), "duplicate source path")
    source_by_path = {row["path"]: row for row in sources}
    for path, sha in EXPECTED["source_files"].items():
        _expect(source_by_path[path]["sha256"] == sha, f"wrong source hash: {path}")

    metadata = document["benchmark_metadata"]
    _expect(metadata["sha256"] == EXPECTED["benchmark_sha256"], "wrong metadata hash")
    _expect(metadata["bytes"] == EXPECTED["benchmark_bytes"], "wrong metadata size")
    for field in (
        "incremental_rows",
        "new_non_incremental_rows",
        "non_incremental_logics",
        "non_incremental_rows",
    ):
        _expect(metadata[field] == EXPECTED[field], f"wrong metadata fact: {field}")

    historical = document["historical_results"]
    _expect([row["year"] for row in historical] == list(range(2018, 2025)), "wrong historical years")
    for row in historical:
        expected_bytes, expected_sha = EXPECTED["historical"][row["year"]]
        _expect(row["bytes"] == expected_bytes, f"wrong historical size: {row['year']}")
        _expect(row["sha256"] == expected_sha, f"wrong historical hash: {row['year']}")

    submissions = document["submissions"]
    _expect(submissions == sorted(submissions, key=lambda row: row["path"]), "submissions are not sorted")
    _expect(len({row["path"] for row in submissions}) == len(submissions), "duplicate submission path")
    competitive = [row for row in submissions if row["competitive"]]
    _expect(len(submissions) == EXPECTED["submission_count"], "wrong submission count")
    _expect(len(competitive) == EXPECTED["competitive_submission_count"], "wrong competitive count")
    _expect(all(row["seed"] is not None for row in competitive), "missing competitive seed")
    seed_sum = sum(row["seed"] for row in competitive)
    seed_modulo = seed_sum % (2**30)
    _expect(seed_sum == EXPECTED["competitive_seed_sum"], "wrong competitive seed sum")
    _expect(seed_modulo == EXPECTED["submission_seed_modulo"], "wrong seed modulo")
    _expect(seed_modulo + document["policy"]["nyse_seed"] == EXPECTED["global_seed"], "wrong global seed")
    _expect(document["policy"]["global_seed"] == EXPECTED["global_seed"], "stored global seed drift")

    release = document["corpus_release"]
    archives = release["archives"]
    _expect(release["record"] == ZENODO_RECORD, "wrong Zenodo record")
    _expect(release["version"] == EXPECTED["zenodo"]["version"], "wrong release version")
    _expect(archives == sorted(archives, key=lambda row: row["name"]), "archives are not sorted")
    _expect(len({row["name"] for row in archives}) == len(archives), "duplicate archive name")
    _expect(len(archives) == EXPECTED["zenodo"]["file_count"], "wrong archive count")
    _expect(sum(row["bytes"] for row in archives) == EXPECTED["zenodo"]["total_bytes"], "wrong archive size")
    _expect(release["total_bytes"] == EXPECTED["zenodo"]["total_bytes"], "stored archive size drift")


def check() -> None:
    raw = OUTPUT.read_bytes()
    document = json.loads(raw)
    validate(document)
    _expect(raw == canonical_json(document), "authority manifest is not canonical JSON")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--refresh", action="store_true", help="fetch pinned inputs and rewrite the manifest")
    parser.add_argument("--check", action="store_true", help="validate the committed manifest without network")
    args = parser.parse_args()
    if args.refresh == args.check:
        parser.error("choose exactly one of --refresh or --check")
    try:
        if args.refresh:
            document = refresh()
            validate(document)
            OUTPUT.write_bytes(canonical_json(document))
        else:
            check()
    except (AuthorityError, KeyError, TypeError, ValueError, OSError, urllib.error.URLError) as error:
        print(f"SMTCOMP_SELECTION_AUTHORITY_ERROR|{error}", file=sys.stderr)
        return 1
    document = json.loads(OUTPUT.read_bytes())
    print(
        "SMTCOMP_SELECTION_AUTHORITY|"
        f"sources={document['summary']['organizer_source_file_count']}|"
        f"submissions={document['summary']['submission_count']}|"
        f"competitive={document['summary']['competitive_submission_count']}|"
        f"archives={document['summary']['archive_count']}|"
        f"non_incremental={document['benchmark_metadata']['non_incremental_rows']}|"
        f"seed={document['policy']['global_seed']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
