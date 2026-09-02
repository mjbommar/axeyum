#!/usr/bin/env python3
"""Every `depends_on` edge that crosses an evaluation partition is a violation.

WHY THIS EXISTS (ADR-1546 option 2, recorded as taken in ADR-1550).

`check-autogenesis-nursery.py` enforces
`split_leakage: no-declared-component-may-cross-evaluation-partitions` over
the WEAK COMPONENTS of the declared-dependency graph. It is right about its
subject and it is the wrong instrument for a producer, for two measured
reasons:

  1. IT RUNS IN NO PRE-PUSH GATE. `hooks/pre-push` ran
     `check-settled-fact-statements.py` and `check-holdout-closed-evaluation.py`
     and neither nursery gate, so a producer could close a fact whose
     `depends_on` fuses two evaluation partitions and push it without the
     property ever being evaluated. Both crossing edges of 2026-09-01 landed
     that way.
  2. A COMPONENT IS THE WRONG UNIT TO EXEMPT. A component grows when any
     member gains an edge, so an exemption that names a component's fact-id
     SET goes stale on the next producer commit and the only cheap repair is
     to enlarge it. Measured in ADR-1546: 228 -> 230 -> 258 -> 274 members in
     four days, against a live component of 305. A gate whose largest subject
     is waved through by an exemption enlarged to fit whenever it fails cannot
     fail on that subject, which is the failure mode CLAUDE.md names.

So this gate changes the unit. THE SUBJECT IS ONE EDGE: a `depends_on` entry
in one fact naming another fact, where the two facts sit in different
evaluation partitions. One edge is what a producer actually adds, it is
attributable to one commit by a pickaxe search, and -- unlike a component --
it never changes shape underneath the person who reviewed it. An exemption
here must therefore name ONE EDGE, a reason and a date; anything else is
refused.

WHAT IS AND IS NOT HONOURED

  * `artifacts/autogenesis/partition-edge-amendments-v1.json` -- a list whose
    every element names `from`, `to`, `reason`, `date`. Honoured per edge.
  * `cross_population_component_split_exemptions` (and
    `component_split_exemptions`) in the nursery manifests -- NOT honoured,
    and reported as `NOT-AN-AMENDMENT`. They name a fact-id SET, which is a
    count-shaped exemption for this gate's purpose: nothing in one of them
    says which edge was reviewed, so honouring it would suppress an edge
    nobody looked at. That is not a criticism of what those entries do for
    `check-autogenesis-nursery.py`, whose unit is the component; it is a
    statement that they are unparseable AS PER-EDGE AMENDMENTS.

THE RATCHET (`--baseline`)

The existing crossings are not this gate's to repair -- re-partitioning is
ADR-1546 option 1 and belongs to the draw. So `--record-baseline` freezes
today's crossing edge set into
`artifacts/autogenesis/partition-edge-baseline-v1.json` and `--baseline` fails
only on edges NOT in it. New crossings are blocked from today; the recorded
ones are repaired by the re-partition. `--record-baseline` REFUSES to record a
set that is not a subset of the committed baseline, so the ratchet can only
tighten: a lane cannot silence a new crossing by re-recording.

EXITS
  0  no violation (or, under --baseline, no violation outside the baseline)
  1  at least one violation
  2  cannot answer -- no manifests, no fact ledger, or --baseline with no
     baseline file. Deliberately distinct from 1: a gate that reports a
     disagreement when its subject was unavailable is wrong about its own
     subject.
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import pathlib
import subprocess
import sys
from typing import Any

# `AXEYUM_PARTITION_EDGES_ROOT` points the SHIPPED script at a throwaway tree
# so `scripts/tests/test_check_partition_edges.py` can drive every guard to
# failure without re-implementing it and without dirtying the real checkout.
# Same device as `AXEYUM_MERGE_HYGIENE_ROOT` and `AXEYUM_KERNEL_SUITES_ROOT`.
DEFAULT_ROOT = pathlib.Path(__file__).resolve().parents[1]

MANIFEST_GLOB = "artifacts/autogenesis/nursery*.json"
FACTS_DIR = "artifacts/facts"
BASELINE_PATH = "artifacts/autogenesis/partition-edge-baseline-v1.json"
AMENDMENTS_PATH = "artifacts/autogenesis/partition-edge-amendments-v1.json"

# Every partition an entry may declare. `longitudinal` is in here on purpose:
# ADR-1546 counted the 305-member component across development / train /
# held-out / longitudinal, and an edge from a drawn evaluation fact into the
# longitudinal regression population is the same leak wearing a different
# name.
PARTITIONS = ("longitudinal", "train", "development", "held-out")

# The exemption keys this gate refuses to read as amendments. Named, not
# pattern-matched, so the report says WHICH construct was declined.
COUNT_STYLE_EXEMPTION_KEYS = (
    "cross_population_component_split_exemptions",
    "component_split_exemptions",
)


class Unanswerable(RuntimeError):
    """The gate could not evaluate its subject. Exit 2, never 1."""


def sha256_of(value: Any) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode()).hexdigest()


def load_json(path: pathlib.Path) -> Any:
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError) as exc:
        raise Unanswerable(f"{path}: unreadable ({exc})") from exc


# --------------------------------------------------------------------------
# The subject
# --------------------------------------------------------------------------

def load_partitions(root: pathlib.Path) -> tuple[dict[str, str], list[str]]:
    """`{fact_id: partition}` over every nursery manifest, plus their paths."""
    manifests = sorted(root.glob(MANIFEST_GLOB))
    if not manifests:
        raise Unanswerable(
            f"no nursery manifest matches {MANIFEST_GLOB} under {root} -- "
            f"there is no drawn population to check, which is not the same "
            f"as a clean one")
    partition_of: dict[str, str] = {}
    declared_in: dict[str, str] = {}
    names: list[str] = []
    for path in manifests:
        rel = str(path.relative_to(root))
        names.append(rel)
        document = load_json(path)
        if not isinstance(document, dict):
            raise Unanswerable(f"{rel}: not a JSON object")
        entries = document.get("entries")
        if not isinstance(entries, list):
            raise Unanswerable(f"{rel}: entries is not a list")
        for index, entry in enumerate(entries):
            if not isinstance(entry, dict):
                raise Unanswerable(f"{rel}: entries[{index}] is not an object")
            fact_id = entry.get("fact_id")
            partition = entry.get("partition")
            if not isinstance(fact_id, str) or partition not in PARTITIONS:
                raise Unanswerable(
                    f"{rel}: entries[{index}] has no usable fact_id/partition")
            if fact_id in partition_of and partition_of[fact_id] != partition:
                raise Unanswerable(
                    f"{fact_id} is {partition_of[fact_id]} in "
                    f"{declared_in[fact_id]} and {partition} in {rel}")
            partition_of[fact_id] = partition
            declared_in[fact_id] = rel
    return partition_of, names


def load_dependencies(root: pathlib.Path) -> dict[str, tuple[list[str], str]]:
    """`{fact_id: (depends_on, path relative to root)}` over the fact ledger."""
    facts_dir = root / FACTS_DIR
    if not facts_dir.is_dir():
        raise Unanswerable(f"{FACTS_DIR} is absent under {root}")
    out: dict[str, tuple[list[str], str]] = {}
    for path in sorted(facts_dir.glob("*.json")):
        fact = load_json(path)
        if not isinstance(fact, dict):
            continue
        fact_id = fact.get("id")
        if not isinstance(fact_id, str):
            continue
        depends_on = fact.get("depends_on") or []
        if not isinstance(depends_on, list):
            raise Unanswerable(f"{path.name}: depends_on is not a list")
        out[fact_id] = ([d for d in depends_on if isinstance(d, str)],
                        str(path.relative_to(root)))
    return out


def crossing_edges(
    partition_of: dict[str, str],
    dependencies: dict[str, tuple[list[str], str]],
) -> list[dict[str, str]]:
    """Every DIRECTED `depends_on` edge whose endpoints differ in partition.

    Directed, not collapsed to an unordered pair, because the directed edge is
    what a producer writes: it is one string in one fact file, and it is what
    the pickaxe search attributes to a commit. `a depends_on b` and
    `b depends_on a` are two separate things somebody did.
    """
    edges: list[dict[str, str]] = []
    for fact_id, source_partition in sorted(partition_of.items()):
        depends_on, source_path = dependencies.get(fact_id, ([], ""))
        for dependency in depends_on:
            target_partition = partition_of.get(dependency)
            if target_partition is None or target_partition == source_partition:
                continue
            edges.append({
                "from": fact_id,
                "from_partition": source_partition,
                "to": dependency,
                "to_partition": target_partition,
                "declared_in": source_path,
            })
    edges.sort(key=lambda e: (e["from"], e["to"]))
    return edges


def edge_key(edge: dict[str, str]) -> tuple[str, str]:
    return (edge["from"], edge["to"])


# --------------------------------------------------------------------------
# Amendments -- per edge, or not at all
# --------------------------------------------------------------------------

def load_amendments(root: pathlib.Path) -> tuple[set[tuple[str, str]], list[str]]:
    """The per-edge amendments, and the complaints about anything that is not one.

    An amendment names ONE edge (`from`, `to`), a `reason` and a `date`. An
    element missing any of those is REPORTED AND NOT HONOURED rather than
    quietly skipped: a malformed amendment is a committed defect, and reading
    it as absent is how an exemption list stops being reviewable.
    """
    path = root / AMENDMENTS_PATH
    if not path.is_file():
        return set(), []
    document = load_json(path)
    complaints: list[str] = []
    amendments: set[tuple[str, str]] = set()
    raw = document.get("amendments") if isinstance(document, dict) else None
    if not isinstance(raw, list):
        return set(), [f"{AMENDMENTS_PATH}: `amendments` is not a list; "
                       f"nothing in it is honoured"]
    for index, item in enumerate(raw):
        if not isinstance(item, dict):
            complaints.append(f"{AMENDMENTS_PATH}[{index}]: not an object")
            continue
        missing = [k for k in ("from", "to", "reason", "date")
                   if not isinstance(item.get(k), str) or not item[k]]
        if missing:
            complaints.append(
                f"{AMENDMENTS_PATH}[{index}]: missing {', '.join(missing)} -- "
                f"an amendment names ONE edge, its reason and its date, so "
                f"this one is NOT honoured")
            continue
        amendments.add((item["from"], item["to"]))
    return amendments, complaints


def count_style_exemptions(root: pathlib.Path) -> list[str]:
    """Report every component/count-shaped exemption, and honour none of them.

    THIS FUNCTION SUPPRESSES NOTHING. It returns lines for the report. The
    whole point of ADR-1550 is that a fact-id SET is not a statement about any
    particular edge, so reading one as an amendment would wave through
    crossings nobody reviewed -- which is what happened to the component gate
    it complements.
    """
    lines: list[str] = []
    for path in sorted(root.glob(MANIFEST_GLOB)):
        document = load_json(path)
        if not isinstance(document, dict):
            continue
        rel = str(path.relative_to(root))
        for key in COUNT_STYLE_EXEMPTION_KEYS:
            value = document.get(key)
            if not isinstance(value, list) or not value:
                continue
            for index, item in enumerate(value):
                members = (item.get("component_fact_ids")
                           if isinstance(item, dict) else None)
                size = len(members) if isinstance(members, list) else "?"
                lines.append(
                    f"NOT-AN-AMENDMENT {rel}:{key}[{index}] names a component "
                    f"of {size} fact ids and no edge; unparseable as a "
                    f"per-edge amendment, so it suppresses nothing here")
    return lines


# --------------------------------------------------------------------------
# Attribution
# --------------------------------------------------------------------------

def introducing_commit(root: pathlib.Path, edge: dict[str, str]) -> str:
    """The commit that first put this dependency string into this fact file.

    A pickaxe search over the SOURCE fact's own file, oldest first. Tolerant
    by construction: the ownership sandbox and the control suites' throwaway
    trees are not this repository, and a gate that died because it could not
    run a version-control query would be answering a question nobody asked.

    `--diff-merges=first-parent` IS LOAD-BEARING AND WAS MEASURED. A plain
    pickaxe skips merge commits entirely, so an edge that entered the tree
    during a conflict resolution -- an evil merge -- is attributed to NOTHING.
    On the 2026-09-02 baseline that is **7 of 198** crossing edges, every one
    of them reported as `no commit adds this string` while the string is
    plainly in the committed file. The first of the seven,
    `F:ml430-int-add-comm-c5722728 -> F:ml430-nat-add-comm-56a2d614`, was
    introduced by the merge `0be9ff41b` and by no other commit in the file's
    nine-commit history (verified by walking every one of them and counting
    occurrences, not by trusting the pickaxe that had just said nothing).
    `--no-patch` is what keeps the merge diff itself out of the output.
    """
    path = edge.get("declared_in")
    if not path:
        return "unknown (no fact file)"
    try:
        done = subprocess.run(
            ["git", "log", "--diff-merges=first-parent", "--no-patch",
             f"-S{edge['to']}", "--format=%h %ad",
             "--date=short", "--reverse", "--", path],
            cwd=root, capture_output=True, text=True, timeout=60, check=False)
    except (OSError, subprocess.SubprocessError):
        return "unknown (version control unavailable)"
    if done.returncode != 0:
        return "unknown (version control query failed)"
    first = done.stdout.strip().splitlines()
    return first[0] if first else "unknown (no commit adds this string)"


# --------------------------------------------------------------------------
# The baseline
# --------------------------------------------------------------------------

def read_baseline(root: pathlib.Path) -> dict[str, Any]:
    path = root / BASELINE_PATH
    if not path.is_file():
        raise Unanswerable(
            f"{BASELINE_PATH} is absent -- --baseline cannot ratchet against a "
            f"baseline that does not exist. Record one with "
            f"--record-baseline, or run without --baseline for the full set.")
    document = load_json(path)
    if not isinstance(document, dict) or not isinstance(document.get("edges"), list):
        raise Unanswerable(f"{BASELINE_PATH}: no `edges` list")
    return document


def baseline_keys(document: dict[str, Any]) -> set[tuple[str, str]]:
    return {(e.get("from"), e.get("to")) for e in document["edges"]
            if isinstance(e, dict)}


def head_commit(root: pathlib.Path) -> str:
    try:
        done = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root,
                              capture_output=True, text=True, timeout=30,
                              check=False)
    except (OSError, subprocess.SubprocessError):
        return "unknown"
    return done.stdout.strip() or "unknown"


def ledger_digest(partition_of: dict[str, str],
                  dependencies: dict[str, tuple[list[str], str]]) -> str:
    """A digest of the drawn population's declared dependencies.

    Recorded as PROVENANCE (`this edge set was measured against this ledger
    state`), never recomputed into the committed file on a later run -- see
    `render_baseline`.
    """
    return sha256_of([[fact_id, partition_of[fact_id],
                       sorted(dependencies.get(fact_id, ([], ""))[0])]
                      for fact_id in sorted(partition_of)])


def render_baseline(root: pathlib.Path, edges: list[dict[str, str]],
                    manifests: list[str], ledger_sha: str,
                    previous: dict[str, Any] | None) -> str:
    """The committed baseline text.

    `recorded_date`, `recorded_at_commit` and `ledger_sha256` are PROVENANCE
    and are carried forward unchanged whenever the edge set is unchanged. That
    is not cosmetic: `check-generated-artifact-ownership.py`'s OWNER arm
    requires the owner to restore a perturbed copy BYTE-FOR-BYTE, and a field
    stamped with `today` or with a live digest of a ledger that other lanes
    edit hourly would make this artifact impossible to own. A date that moves
    only when the recorded finding moves is also the more honest field.
    """
    rows = [{k: e[k] for k in ("from", "from_partition", "to", "to_partition")}
            for e in edges]
    carry_over = (previous is not None
                  and baseline_keys(previous) == {edge_key(e) for e in edges})
    if carry_over:
        recorded_date = previous.get("recorded_date", "unknown")
        recorded_at_commit = previous.get("recorded_at_commit", "unknown")
        ledger_sha256 = previous.get("ledger_sha256", ledger_sha)
    else:
        recorded_date = datetime.date.today().isoformat()
        recorded_at_commit = head_commit(root)
        ledger_sha256 = ledger_sha
    document = {
        "kind": "axeyum-partition-edge-baseline",
        "authority": "docs/research/09-decisions/adr-1550-gate-the-producer-"
                     "the-crossing-edge-is-the-unit.md",
        "produced_by": "scripts/check-partition-edges.py --record-baseline",
        "rule": "This set may only SHRINK. --record-baseline refuses a set "
                "that is not a subset of the committed one, so a new crossing "
                "cannot be silenced by re-recording; it must be repaired or "
                "carry a per-edge amendment.",
        "manifests": manifests,
        "recorded_date": recorded_date,
        "recorded_at_commit": recorded_at_commit,
        "ledger_sha256": ledger_sha256,
        "edge_set_sha256": sha256_of(rows),
        "edge_count": len(rows),
        "edges": rows,
        "schema_version": 1,
    }
    return json.dumps(document, indent=2, sort_keys=True,
                      ensure_ascii=False) + "\n"


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", default=None,
                        help="check this tree instead of the checkout")
    parser.add_argument("--baseline", action="store_true",
                        help="fail only on edges absent from the recorded "
                             "baseline (the ratchet; this is the gate form)")
    parser.add_argument("--record-baseline", action="store_true",
                        help="write the current crossing edge set to "
                             + BASELINE_PATH)
    parser.add_argument("--no-blame", action="store_true",
                        help="skip the per-edge commit attribution")
    parser.add_argument("--json", action="store_true",
                        help="emit the violation set as JSON")
    parser.add_argument("--verbose", action="store_true",
                        help="list every declined component exemption even "
                             "when the run passes")
    args = parser.parse_args(argv)

    root = pathlib.Path(args.root
                        or os.environ.get("AXEYUM_PARTITION_EDGES_ROOT")
                        or DEFAULT_ROOT).resolve()

    try:
        partition_of, manifests = load_partitions(root)
        dependencies = load_dependencies(root)
        edges = crossing_edges(partition_of, dependencies)
        amendments, amendment_complaints = load_amendments(root)
        not_amendments = count_style_exemptions(root)
        previous: dict[str, Any] | None = None
        if (root / BASELINE_PATH).is_file():
            candidate = load_json(root / BASELINE_PATH)
            if isinstance(candidate, dict) and isinstance(candidate.get("edges"), list):
                previous = candidate
        baseline: set[tuple[str, str]] = set()
        if args.baseline:
            baseline = baseline_keys(read_baseline(root))
    except Unanswerable as exc:
        print(f"PARTITION-EDGES|UNANSWERABLE {exc}")
        return 2

    if args.record_baseline:
        return record(root, edges, manifests, partition_of, dependencies,
                      previous)

    amended = [e for e in edges if edge_key(e) in amendments]
    baselined = [e for e in edges if edge_key(e) not in amendments
                 and edge_key(e) in baseline]
    violations = [e for e in edges if edge_key(e) not in amendments
                  and edge_key(e) not in baseline]

    # The declined component exemptions are listed in full whenever the run
    # has something to say, and summarised as `not_amendments=N` otherwise --
    # this runs on every push and seven standing lines of "still not honoured"
    # is how a gate teaches people to stop reading it. The COUNT is always in
    # the summary, so a new exemption appearing is still visible.
    if violations or args.verbose:
        for line in not_amendments:
            print(line)
    for line in amendment_complaints:
        print(f"AMENDMENT-REJECTED {line}")

    if args.baseline:
        repaired = sorted(baseline - {edge_key(e) for e in edges})
        for source, target in repaired:
            print(f"REPAIRED {source} -> {target} no longer crosses; "
                  f"re-record the baseline to lock the gain in")

    if args.json:
        print(json.dumps({"violations": violations, "amended": amended,
                          "baselined": baselined}, indent=2, sort_keys=True))

    for edge in violations:
        blame = ("blame-skipped" if args.no_blame
                 else introducing_commit(root, edge))
        print(f"FAIL: {edge['from']} [{edge['from_partition']}] "
              f"depends_on {edge['to']} [{edge['to_partition']}] "
              f"-- introduced by {blame}")

    unamended_total = len([e for e in edges if edge_key(e) not in amendments])
    summary = (f"PARTITION-EDGES|manifests={len(manifests)}"
               f"|drawn={len(partition_of)}"
               f"|crossing={len(edges)}"
               f"|amended={len(amended)}"
               f"|baselined={len(baselined)}"
               f"|violations={len(violations)}"
               f"|not_amendments={len(not_amendments)}")
    if violations:
        print(summary + "|FAILED")
        print(f"  {len(violations)} `depends_on` edge(s) cross an evaluation "
              f"partition and are covered by no per-edge amendment.")
        print("  A crossing edge fuses two evaluation partitions: a held-out "
              "result stops being blind and a train/development split stops "
              "meaning anything. Repair the edge (drop the dependency, or "
              "route through a fact in the same partition), or record a "
              "per-edge amendment in " + AMENDMENTS_PATH + " naming the edge, "
              "a reason and a date. Enlarging a component exemption does "
              "NOTHING here -- see ADR-1550.")
        return 1
    print(summary + f"|unamended_total={unamended_total}|PASS")
    return 0


def record(root: pathlib.Path, edges: list[dict[str, str]],
           manifests: list[str], partition_of: dict[str, str],
           dependencies: dict[str, tuple[list[str], str]],
           previous: dict[str, Any] | None) -> int:
    """Write the baseline, refusing any set that is not a subset of the old one.

    THE RATCHET IS HERE, not in the reading. `--baseline` is only as strong as
    the file it reads, so if re-recording could enlarge the set, a lane that
    hit the gate could clear it in one command and the whole scheme would be
    the growing component exemption again under a new name.
    """
    keys = {edge_key(e) for e in edges}
    if previous is not None:
        grew = sorted(keys - baseline_keys(previous))
        if grew:
            print("PARTITION-EDGES|REFUSED-TO-GROW-BASELINE")
            for source, target in grew:
                print(f"  NEW {source} -> {target}")
            print(f"  {len(grew)} edge(s) are not in the committed baseline. "
                  f"The baseline may only SHRINK (ADR-1550): a new crossing "
                  f"is repaired or amended per edge, never absorbed. Nothing "
                  f"was written.")
            return 1
    text = render_baseline(root, edges, manifests,
                           ledger_digest(partition_of, dependencies), previous)
    (root / BASELINE_PATH).write_text(text)
    shrank = 0 if previous is None else len(baseline_keys(previous) - keys)
    print(f"PARTITION-EDGES|RECORDED|edges={len(edges)}|shrank_by={shrank}"
          f"|{BASELINE_PATH}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
