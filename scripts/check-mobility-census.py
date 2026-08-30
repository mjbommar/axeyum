#!/usr/bin/env python3
"""Void a mobility census whose numbers do not survive being recomputed.

The census (`artifacts/autogenesis/mobility-census-v1.json`) says which tactic
preconditions reach which open facts, and its zero-match clusters are read as
the capability backlog. So it is exactly the shape CLAUDE.md warns about: at N
lanes the ledger IS the product, and a checker that cannot fail makes it
manufacture unfalsifiable claims at full speed.

Every rule below therefore recomputes something from a file the census does not
own, and every failure is a nonzero exit naming the finding:

1.  Shape: `schema_version`, `kind`, the required top-level keys, and the
    per-fact / per-tactic row shapes.
2.  `catalog_sha256` matches the committed tactic catalog on disk, and the
    census names every tactic the catalog declares -- no more, no fewer. A
    census pinned to a catalog nobody has is a census of nothing.
3.  `export_index_sha256` and `nursery_sha256` match their files.
4.  **No held-out fact id appears anywhere in the document**, scanned as text
    over the whole file rather than field by field, because a leaked id in a
    cluster, a tactic row or a free-text note costs the same split key.
5.  Every fact id in the census exists in `artifacts/facts/`, appears once, and
    is named by no cluster or tactic row that has no fact row of its own.

5b. **Graduation is lifecycle, and it is audited rather than assumed.** A fact
    that was `open` when the census ran and is `proved` now has GRADUATED: the
    flywheel closed it, which is the outcome this repository exists to produce.
    Counting that as a violation made the gate punish progress -- on
    2026-08-30, 126 of 152 rows had graduated and the checker emitted 126
    identical lines that buried the one finding that mattered. So graduation is
    counted and reported. It is not taken on trust: every row's status is
    re-read at the census's own pinned `git_commit`, and a row already settled
    there is population padding, because `open_facts` is the denominator of the
    census's headline ratio.

5c. **Freshness: is this still a description of the OPEN backlog?** Every
    quantity is recomputed from the ledger, the nursery and the frozen-export
    index, never read out of the census. A frozen export is the ONLY route to
    an evaluable goal (the census deliberately never parses `formal.statement`),
    so the open, non-held-out facts carrying one are the census's live subject.
    Zero of them means the census has no subject at all and regenerating cannot
    help; some of them with none evaluated means regenerate; a zero-match
    cluster whose facts are all settled is a capability backlog that names no
    capability.
6.  The counters are internally consistent: `evaluable + unevaluable` equals
    `open_facts`; `matched + unmatched + unevaluable` pairs equal
    `open_facts * tactics`; per-fact `mobility` equals `len(matched)`; every
    tactic's `matched_facts` equals the number of fact rows naming it; the
    partition table sums to the totals; the clusters partition the zero-match
    set exactly.
7.  `evaluable > 0`. A census that evaluated nothing is not a census, and this
    is the rule the generator also enforces -- stated twice on purpose, because
    the generator's copy protects the run and this one protects the artifact.
8.  The must-decline sampling block never reports `suspects` while claiming a
    clean result, and `evaluated == 0` must not be presented as a pass.

Standard library only: `scripts/` may not import `axeyum` (pyproject's `agent`
extra is an EXTRA precisely so no gate needs a network install).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
CENSUS = ROOT / "artifacts/autogenesis/mobility-census-v1.json"
CATALOG = ROOT / "artifacts/autogenesis/tactic-catalog-v1.json"
EXPORT_INDEX = ROOT / "artifacts/autogenesis/agent-frozen-export-index-v1.json"
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
FACTS = ROOT / "artifacts/facts"

SCHEMA_VERSION = 1
KIND = "axeyum-mobility-census"

TOP_LEVEL = (
    "schema_version",
    "kind",
    "generated_by",
    "git_commit",
    "catalog_path",
    "catalog_sha256",
    "ledger_sha256",
    "export_index_path",
    "export_index_sha256",
    "nursery_sha256",
    "holdout_policy",
    "semantics",
    "totals",
    "partitions",
    "export_coverage",
    "unevaluable_reasons",
    "tactics",
    "facts",
    "zero_match_clusters",
    "must_decline_sampling",
)

TOTALS = (
    "open_facts",
    "evaluable",
    "unevaluable",
    "tactics",
    "pairs",
    "matched_pairs",
    "unmatched_pairs",
    "unevaluable_pairs",
    "zero_match_facts",
    "clusters",
    "held_out_excluded",
    "held_out_evaluable",
    "written_fact_rows",
)


class CensusError(Exception):
    """The census is not a valid record of what it claims to have measured."""


def read_json(path: pathlib.Path, label: str) -> Any:
    if not path.is_file():
        raise CensusError(f"{label} is missing: {path}")
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise CensusError(f"{label} is unreadable: {error}") from error


def file_sha256(path: pathlib.Path, label: str) -> str:
    if not path.is_file():
        raise CensusError(f"{label} is missing: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def held_out_ids(nursery: dict[str, Any]) -> set[str]:
    entries = nursery.get("entries")
    if not isinstance(entries, list) or not entries:
        raise CensusError("the nursery manifest has no entries")
    ids = {
        entry["fact_id"]
        for entry in entries
        if isinstance(entry, dict)
        and entry.get("partition") == "held-out"
        and isinstance(entry.get("fact_id"), str)
    }
    if not ids:
        raise CensusError(
            "the nursery declares no held-out rows; the leakage rule below would pass "
            "vacuously and this gate exists to make it bite"
        )
    return ids


def ledger_statuses() -> dict[str, str]:
    if not FACTS.is_dir():
        raise CensusError(f"the fact ledger is missing: {FACTS}")
    out: dict[str, str] = {}
    for path in sorted(FACTS.glob("*.json")):
        document = json.loads(path.read_text(encoding="utf-8"))
        fact_id = document.get("id")
        if isinstance(fact_id, str):
            out[fact_id] = str(document.get("epistemic_status"))
    if not out:
        raise CensusError(f"{FACTS} held no facts; every id check below would pass vacuously")
    return out


def exportable_fact_ids() -> set[str]:
    """The fact ids carrying a digest-pinned frozen statement export.

    This is the census's whole subject. `docs/python-2026-08/07-mobility-census.md`
    records the deliberate choice: a goal comes from a frozen export imported
    into a real kernel, and there is no fallback that parses `formal.statement`
    Lean text, because that would make every verdict rest on a goal nobody
    pinned. So a fact with no export is `unevaluable`, always.

    Recomputed here from the index rather than read out of the census, which is
    the point -- the census's own `evaluable` count is exactly what a stale
    census gets wrong.
    """
    index = read_json(EXPORT_INDEX, "the frozen-export index")
    # The locals are named apart from `held_out_ids`'s deliberately: the two
    # fail-closed guards are line-for-line identical otherwise, and
    # `scripts/tests/mutation_controls.py` anchors a mutant on the line text.
    # A shared anchor matches in two functions and the harness reports AMBIGUOUS
    # ANCHOR -- not a result -- so both guards would go unmeasured.
    exports = index.get("entries")
    if not isinstance(exports, list) or not exports:
        raise CensusError(
            "the frozen-export index has no entries; every freshness rule below would pass "
            "vacuously and this gate exists to make them bite"
        )
    exportable = {
        export["fact_id"]
        for export in exports
        if isinstance(export, dict) and isinstance(export.get("fact_id"), str)
    }
    if not exportable:
        raise CensusError("the frozen-export index names no fact ids")
    return exportable


def fact_path_at(fact_id: str) -> str:
    """`F:foo` lives at `artifacts/facts/F-foo.json`; git wants the path, not the id."""
    return f"artifacts/facts/{fact_id.replace(':', '-')}.json"


def statuses_at_commit(commit: str, fact_ids: list[str]) -> tuple[str, dict[str, str]]:
    """Each fact's `epistemic_status` as of `commit`, in one `git cat-file --batch`.

    Three outcomes, deliberately distinct:

    * ``("ok", mapping)``  -- the audit ran; a fact absent from `mapping` had no
      fact file at that commit, which is itself a finding.
    * ``("no-git", {})``   -- this tree has no `.git` at all. `git archive`
      snapshots (`scripts/lane-snapshot.sh`) are built and gated exactly that
      way, so refusing there would break a supported workflow. The state is
      printed on the status line rather than swallowed, so a run that could not
      audit never looks like a run that audited and found nothing.
    * ``("unreachable", {})`` -- `.git` is present and the commit is not. That is
      a violation, not a skip: a census pinning a commit nobody can reach cannot
      have its population audited, and "skip when the check is inconvenient" is
      how a checker stops being able to fail.
    """
    if not (ROOT / ".git").exists():
        return ("no-git", {})
    probe = subprocess.run(
        ["git", "-C", str(ROOT), "cat-file", "-t", commit],
        capture_output=True,
        text=True,
        check=False,
    )
    if probe.returncode != 0 or probe.stdout.strip() != "commit":
        return ("unreachable", {})
    specs = "".join(f"{commit}:{fact_path_at(fact_id)}\n" for fact_id in fact_ids)
    proc = subprocess.run(
        ["git", "-C", str(ROOT), "cat-file", "--batch"],
        input=specs.encode("utf-8"),
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        return ("unreachable", {})
    out: dict[str, str] = {}
    data = proc.stdout
    cursor = 0
    while cursor < len(data):
        newline = data.find(b"\n", cursor)
        if newline < 0:
            break
        parts = data[cursor:newline].decode("utf-8", "replace").split()
        # A missing object prints "<spec> missing" and carries no body.
        if len(parts) != 3 or not parts[2].isdigit():
            cursor = newline + 1
            continue
        size = int(parts[2])
        try:
            document = json.loads(data[newline + 1 : newline + 1 + size])
        except json.JSONDecodeError:
            document = {}
        if isinstance(document.get("id"), str):
            out[document["id"]] = str(document.get("epistemic_status"))
        cursor = newline + 1 + size + 1
    return ("ok", out)


# ---------------------------------------------------------------------------
# Rules
# ---------------------------------------------------------------------------


def check_shape(census: Any) -> list[str]:
    if not isinstance(census, dict):
        raise CensusError("the census is not a JSON object")
    problems: list[str] = []
    if census.get("schema_version") != SCHEMA_VERSION:
        problems.append(f"schema_version is {census.get('schema_version')!r}, want {SCHEMA_VERSION}")
    if census.get("kind") != KIND:
        problems.append(f"kind is {census.get('kind')!r}, want {KIND!r}")
    for key in TOP_LEVEL:
        if key not in census:
            problems.append(f"missing top-level key {key!r}")
    totals = census.get("totals")
    if not isinstance(totals, dict):
        problems.append("totals is not an object")
    else:
        for key in TOTALS:
            if not isinstance(totals.get(key), int):
                problems.append(f"totals.{key} is not an integer")
    for row in census.get("facts") or []:
        if not isinstance(row, dict) or not isinstance(row.get("fact_id"), str):
            problems.append("a fact row has no fact_id")
            continue
        for key in ("partition", "evaluable", "mobility", "matched", "unmatched", "unevaluable"):
            if key not in row:
                problems.append(f"fact row {row['fact_id']} is missing {key!r}")
    for row in census.get("tactics") or []:
        if not isinstance(row, dict) or not isinstance(row.get("id"), str):
            problems.append("a tactic row has no id")
            continue
        for key in ("matched_facts", "distinct_goal_shapes_matched", "matched_fact_ids"):
            if key not in row:
                problems.append(f"tactic row {row['id']} is missing {key!r}")
    return problems


def check_pins(census: dict[str, Any]) -> list[str]:
    problems: list[str] = []
    for key, path, label in (
        ("catalog_sha256", CATALOG, "the tactic catalog"),
        ("export_index_sha256", EXPORT_INDEX, "the frozen-export index"),
        ("nursery_sha256", NURSERY, "the nursery"),
    ):
        measured = file_sha256(path, label)
        if census.get(key) != measured:
            problems.append(
                f"{key} is {census.get(key)!r} but {label} on disk hashes to {measured}"
            )
    return problems


def check_catalog_coverage(census: dict[str, Any]) -> list[str]:
    catalog = read_json(CATALOG, "the tactic catalog")
    declared = {str(tactic["id"]) for tactic in catalog.get("tactics", [])}
    if not declared:
        raise CensusError("the tactic catalog declares no tactics")
    present = {str(row.get("id")) for row in census.get("tactics") or []}
    problems: list[str] = []
    for missing in sorted(declared - present):
        problems.append(f"the catalog declares {missing} and the census never evaluated it")
    for extra in sorted(present - declared):
        problems.append(f"the census reports {extra}, which the catalog does not declare")
    totals = census.get("totals") or {}
    if totals.get("tactics") != len(declared):
        problems.append(
            f"totals.tactics is {totals.get('tactics')!r} against {len(declared)} declared tactics"
        )
    return problems


def check_no_held_out(census: dict[str, Any], held_out: set[str]) -> list[str]:
    """Text scan, not a field walk: a leaked id costs the same wherever it sits."""
    text = json.dumps(census, sort_keys=True)
    return [
        f"held-out fact id {fact_id} appears in the census; a held-out id in a published "
        f"artifact spends its whole split key"
        for fact_id in sorted(held_out)
        if fact_id in text
    ]


def check_fact_ids(census: dict[str, Any], statuses: dict[str, str]) -> list[str]:
    problems: list[str] = []
    seen: set[str] = set()
    for row in census.get("facts") or []:
        fact_id = row.get("fact_id")
        if not isinstance(fact_id, str):
            continue
        if fact_id in seen:
            problems.append(f"{fact_id} appears twice in the census")
        seen.add(fact_id)
        if fact_id not in statuses:
            problems.append(f"{fact_id} is in the census and not in artifacts/facts/")
        # A row whose fact has since settled is NOT rejected here. It has
        # graduated, and `check_population` audits that claim against the
        # census's pinned commit -- see rule 5b in the module docstring.
    for cluster in census.get("zero_match_clusters") or []:
        for fact_id in cluster.get("fact_ids") or []:
            if fact_id not in seen:
                problems.append(f"cluster names {fact_id}, which has no fact row")
    for row in census.get("tactics") or []:
        for fact_id in row.get("matched_fact_ids") or []:
            if fact_id not in seen:
                problems.append(f"{row.get('id')} names matched fact {fact_id} with no fact row")
    return problems


def check_counts(census: dict[str, Any]) -> list[str]:
    totals = census.get("totals") or {}
    problems: list[str] = []
    open_facts = totals.get("open_facts", 0)
    tactics = totals.get("tactics", 0)
    if totals.get("evaluable", 0) + totals.get("unevaluable", 0) != open_facts:
        problems.append(
            f"evaluable + unevaluable = {totals.get('evaluable')} + {totals.get('unevaluable')} "
            f"!= open_facts {open_facts}"
        )
    if totals.get("pairs") != open_facts * tactics:
        problems.append(f"pairs {totals.get('pairs')} != open_facts * tactics {open_facts*tactics}")
    pair_sum = (
        totals.get("matched_pairs", 0)
        + totals.get("unmatched_pairs", 0)
        + totals.get("unevaluable_pairs", 0)
    )
    if pair_sum != totals.get("pairs"):
        problems.append(f"matched + unmatched + unevaluable pairs = {pair_sum} != {totals.get('pairs')}")
    rows = census.get("facts") or []
    if totals.get("written_fact_rows") != len(rows):
        problems.append(
            f"totals.written_fact_rows {totals.get('written_fact_rows')} != {len(rows)} fact rows"
        )
    if totals.get("written_fact_rows", 0) + totals.get("held_out_excluded", 0) != open_facts:
        problems.append(
            "written_fact_rows + held_out_excluded != open_facts; a fact was neither written "
            "nor accounted for as held out"
        )
    matched_by_tactic: dict[str, int] = {}
    zero_match_written = 0
    for row in rows:
        matched = row.get("matched") or []
        if row.get("mobility") != len(matched):
            problems.append(
                f"{row.get('fact_id')}: mobility {row.get('mobility')} != {len(matched)} matched"
            )
        if row.get("evaluable"):
            if not matched:
                zero_match_written += 1
        elif matched:
            problems.append(
                f"{row.get('fact_id')} is unevaluable and still reports matched tactics"
            )
        overlap = set(matched) & set(row.get("unmatched") or {})
        overlap |= set(matched) & set(row.get("unevaluable") or {})
        overlap |= set(row.get("unmatched") or {}) & set(row.get("unevaluable") or {})
        if overlap:
            problems.append(
                f"{row.get('fact_id')}: {sorted(overlap)} carries two verdicts at once; the "
                f"three-valued result must not collapse"
            )
        total_verdicts = len(matched) + len(row.get("unmatched") or {}) + len(
            row.get("unevaluable") or {}
        )
        if total_verdicts != census["totals"]["tactics"]:
            problems.append(
                f"{row.get('fact_id')} carries {total_verdicts} verdicts against "
                f"{census['totals']['tactics']} tactics"
            )
        for tactic_id in matched:
            matched_by_tactic[tactic_id] = matched_by_tactic.get(tactic_id, 0) + 1
    for row in census.get("tactics") or []:
        counted = matched_by_tactic.get(str(row.get("id")), 0)
        named = len(row.get("matched_fact_ids") or [])
        if named != counted:
            problems.append(
                f"{row.get('id')} names {named} matched facts but {counted} fact rows match it"
            )
        shapes = row.get("distinct_goal_shapes_matched", 0)
        if shapes > counted:
            problems.append(
                f"{row.get('id')} reports {shapes} distinct goal shapes over {counted} matched "
                f"facts; a shape count above the fact count cannot be a count of shapes matched"
            )
        if counted and not shapes:
            problems.append(f"{row.get('id')} matched {counted} facts and reports zero shapes")
    clustered = [
        fact_id
        for cluster in census.get("zero_match_clusters") or []
        for fact_id in cluster.get("fact_ids") or []
    ]
    if len(clustered) != len(set(clustered)):
        problems.append("a fact appears in two zero-match clusters")
    if len(clustered) != zero_match_written:
        problems.append(
            f"{len(clustered)} facts are clustered against {zero_match_written} written "
            f"zero-match facts"
        )
    if totals.get("clusters") != len(census.get("zero_match_clusters") or []):
        problems.append("totals.clusters disagrees with the cluster list")
    for cluster in census.get("zero_match_clusters") or []:
        if cluster.get("size") != len(cluster.get("fact_ids") or []):
            problems.append(f"cluster {cluster.get('reasons')} size disagrees with its fact list")
        if not cluster.get("reasons"):
            problems.append("a zero-match cluster carries no reasons; it would name no capability")
    partitions = census.get("partitions") or {}
    for key in ("open", "evaluable", "unevaluable"):
        summed = sum(int(bucket.get(key, 0)) for bucket in partitions.values())
        want = totals.get({"open": "open_facts"}.get(key, key), 0)
        if summed != want:
            problems.append(f"partitions sum {key}={summed} against totals {want}")
    return problems


def check_population(
    census: dict[str, Any], statuses: dict[str, str]
) -> tuple[list[str], int, int, str]:
    """Split the rows into live and graduated, and audit the graduation.

    Returns ``(problems, live, graduated, audit_state)``. Graduation is normal
    lifecycle and never a violation; a row that was ALREADY settled when the
    census ran is, because it inflates `open_facts`.
    """
    problems: list[str] = []
    rows = [
        row["fact_id"]
        for row in census.get("facts") or []
        if isinstance(row, dict) and isinstance(row.get("fact_id"), str)
    ]
    live = sum(1 for fact_id in rows if statuses.get(fact_id) == "open")
    graduated = sum(1 for fact_id in rows if fact_id in statuses and statuses[fact_id] != "open")
    commit = census.get("git_commit")
    if not isinstance(commit, str) or not commit.strip():
        problems.append(
            "graduation-audit: the census pins no git_commit, so no row's open-at-census-time "
            "claim can be re-read and every graduated row would be taken on trust"
        )
        return (problems, live, graduated, "absent")
    state, historical = statuses_at_commit(commit, rows)
    if state == "unreachable":
        problems.append(
            f"graduation-audit: git_commit {commit} is not reachable in this checkout, so the "
            f"census's population cannot be audited"
        )
        return (problems, live, graduated, state)
    if state == "no-git":
        return (problems, live, graduated, state)
    for fact_id in rows:
        was = historical.get(fact_id)
        if was is None:
            problems.append(
                f"graduation-audit: {fact_id} had no fact file at {commit[:12]}; the census "
                f"counted a fact the ledger did not hold when it ran"
            )
        elif was != "open":
            problems.append(
                f"graduation-audit: {fact_id} was already {was} at {commit[:12]}; a census of OPEN "
                f"facts may not count it, and counting it inflates open_facts"
            )
    return (problems, live, graduated, state)


def check_freshness(
    census: dict[str, Any],
    statuses: dict[str, str],
    held_out: set[str],
    exportable: set[str],
) -> tuple[list[str], int, int]:
    """Is the census still a description of the OPEN backlog?

    Returns ``(problems, live_evaluable, live_exportable)``. Both counts are
    recomputed from the ledger, the nursery and the export index; neither is
    read out of the census.
    """
    problems: list[str] = []
    live_open = {fact_id for fact_id, status in statuses.items() if status == "open"}
    live_exportable = sorted((live_open & exportable) - held_out)
    rows = {
        row["fact_id"]
        for row in census.get("facts") or []
        if isinstance(row, dict) and isinstance(row.get("fact_id"), str)
    }
    live_evaluable = sorted(
        row["fact_id"]
        for row in census.get("facts") or []
        if isinstance(row, dict)
        and row.get("evaluable")
        and statuses.get(row.get("fact_id")) == "open"
    )
    if not live_exportable:
        problems.append(
            "freshness: no open fact carries a frozen statement export, so the census has no "
            "subject left. A frozen export is the only route to an evaluable goal, so "
            "REGENERATING WILL NOT HELP -- this clears only when a producer exports a statement "
            "for a fact that is still open"
        )
    elif not live_evaluable:
        problems.append(
            f"freshness: {len(live_exportable)} open fact(s) carry a frozen export and the census "
            f"evaluated none of them; regenerate with `just mobility-census-regen`"
        )
    for fact_id in live_exportable:
        if fact_id not in rows:
            problems.append(
                f"freshness: {fact_id} is open and carries a frozen export, and the census has no "
                f"row for it; the one kind of fact this census can measure went unmeasured"
            )
    for cluster in census.get("zero_match_clusters") or []:
        fact_ids = list(cluster.get("fact_ids") or [])
        if fact_ids and not any(statuses.get(fact_id) == "open" for fact_id in fact_ids):
            problems.append(
                f"freshness: the zero-match cluster {sorted(cluster.get('reasons') or [])} names "
                f"{len(fact_ids)} fact(s) and every one has settled; a capability backlog of "
                f"closed facts names no capability"
            )
    return (problems, len(live_evaluable), len(live_exportable))


def check_evaluable(census: dict[str, Any]) -> list[str]:
    totals = census.get("totals") or {}
    if totals.get("evaluable", 0) > 0:
        return []
    return [
        "evaluable is 0: a census that evaluated nothing is not a census. Every open fact would "
        "be reported as unevaluable and the capability backlog would be empty for the wrong reason"
    ]


def check_must_decline(census: dict[str, Any]) -> list[str]:
    block = census.get("must_decline_sampling")
    if not isinstance(block, dict):
        return ["must_decline_sampling is missing or not an object"]
    problems: list[str] = []
    for key in ("rows", "evaluated", "unevaluable", "suspects", "suspect_facts"):
        if key not in block:
            problems.append(f"must_decline_sampling is missing {key!r}")
    if problems:
        return problems
    if block["rows"] <= 0:
        problems.append("must_decline_sampling.rows is 0; the negative control has no subject")
    if block["evaluated"] + block["unevaluable"] != block["rows"]:
        problems.append("must_decline_sampling counters do not sum to rows")
    if block["suspects"] and not block["suspect_facts"]:
        problems.append(
            "must_decline_sampling names suspect tactics and no suspect facts; a SUSPECT with no "
            "goal behind it cannot be investigated"
        )
    if block["suspects"]:
        problems.append(
            f"a tactic precondition admits a must-decline statement: {sorted(block['suspects'])} "
            f"over {sorted(block['suspect_facts'])}. Those statements are FALSE by a recomputed "
            f"counterexample"
        )
    return problems




def validate(census_path: pathlib.Path) -> tuple[list[str], dict[str, Any]]:
    """Returns ``(problems, metrics)``; the metrics are recomputed, not read."""
    census = read_json(census_path, "the mobility census")
    problems = list(check_shape(census))
    if problems:
        return (problems, {})
    held_out = held_out_ids(read_json(NURSERY, "the nursery"))
    statuses = ledger_statuses()
    problems += check_pins(census)
    problems += check_catalog_coverage(census)
    problems += check_no_held_out(census, held_out)
    problems += check_fact_ids(census, statuses)
    population, live, graduated, audit = check_population(census, statuses)
    problems += population
    freshness, live_evaluable, live_exportable = check_freshness(
        census, statuses, held_out, exportable_fact_ids()
    )
    problems += freshness
    problems += check_counts(census)
    problems += check_evaluable(census)
    problems += check_must_decline(census)
    return (
        problems,
        {
            "live": live,
            "graduated": graduated,
            "audit": audit,
            "live_evaluable": live_evaluable,
            "live_exportable": live_exportable,
        },
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--census", default=str(CENSUS), help="the census file to validate")
    args = parser.parse_args(argv)
    path = pathlib.Path(args.census)
    try:
        problems, metrics = validate(path)
    except CensusError as error:
        print(f"MOBILITY_CENSUS_ERROR|{error}", file=sys.stderr)
        return 2
    census = json.loads(path.read_text(encoding="utf-8"))
    totals = census["totals"]
    # `open`/`evaluable` are what the census CLAIMED when it ran; `live_*` and
    # `graduated` are recomputed against the ledger as it stands now. Printing
    # both is the point: their gap is the staleness, and a single number would
    # hide which side of it moved.
    print(
        f"MOBILITY_CENSUS|open={totals['open_facts']}|evaluable={totals['evaluable']}"
        f"|unevaluable={totals['unevaluable']}|tactics={totals['tactics']}"
        f"|matched_pairs={totals['matched_pairs']}|zero_match_facts={totals['zero_match_facts']}"
        f"|clusters={totals['clusters']}|held_out_excluded={totals['held_out_excluded']}"
        f"|live={metrics.get('live', '?')}|graduated={metrics.get('graduated', '?')}"
        f"|live_evaluable={metrics.get('live_evaluable', '?')}"
        f"|live_exportable={metrics.get('live_exportable', '?')}"
        f"|audit={metrics.get('audit', 'not-reached')}"
        f"|violations={len(problems)}"
    )
    if problems:
        print(f"FAIL: {len(problems)} violation(s)", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1
    print("OK: the census recomputes against the catalog, the nursery and the ledger")
    return 0


if __name__ == "__main__":
    sys.exit(main())
