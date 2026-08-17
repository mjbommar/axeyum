#!/usr/bin/env python3
"""Re-derive the curriculum map's `covered` flag from evidence (math strand R1).

`curriculum_status` is a **stored** label in `docs/curriculum/curriculum.toml`,
surfaced through `artifacts/ontology/foundational-concepts.json`. Stored status
is the defect class this repository keeps finding, and here it reaches the
routing table for the whole mathematics vision: the map is what says which nodes
are done and, by omission, what to work on next. A node that asserts coverage it
cannot demonstrate does not merely overstate — it removes itself from the queue.

`docs/mathematics-2026-08/04-reachability.md` R1: *"A node keeps the label only
if it names a family that runs."* This makes that a gate rather than a review.
Two conditions, both derived from the source tree, neither from the label:

1. **It runs.** At least one of the node's example packs is pulled into a suite
   that executes — the `math_resource_*_routes.rs` families.
2. **It can fail.** At least one of those executing instances is asserted
   `unsat` or asserted to be *rejected*. A node whose every instance is a `sat`
   check has shown the route produces answers, not that it produces correct
   ones; the concrete case that motivated R1 was `divisibility-and-euclid`,
   which claimed `computable`/`covered` with zero negative-control evidence.

Condition 2 is decided by reading the ASSERTION, never the file name. A
filename heuristic run while writing this reported `propositional_logic` and
`predicate_logic` as lacking negative controls; both were false positives —
`tiny-cnf-refutation.cnf` and `forall-implies-exists.cnf` are both
`assert_unsat_resource_cnf_checks`, and the former also carries an explicit
tampered-proof rejection test. Names describe intent; assertions are evidence.

Measured 2026-08-16: 19 covered nodes, 19 with an executing pack, 19 with a
negative control. **R1 strips nothing today** — which is the answer, and is
worth holding as a number rather than as a belief.

Condition 2 therefore has no discriminating power on the current tree, and that
is a fact about the tree rather than a weakness in the check: all five
`math_resource_*_routes.rs` suites contain **zero** sat-assertion markers
(`CheckResult::Sat`, `assert_sat`, `Evidence::Model`) against 34 refutation
markers. They are refutation suites by construction, so every executing
instance is a negative control. It is stated here because a condition that
passes trivially is one step from a condition that cannot fail, and
`scripts/tests/test_check_curriculum_coverage.py` keeps that step visible: a
synthetic sat-only route IS correctly reported as lacking a negative control,
and deleting either condition kills exactly one test.

The known limitation: negativity is attributed per test function with one hop
of call transitivity, so a sat-only test that happened to call a shared
refutation helper would be miscounted. Nothing in the tree does that today
(there are no sat-only tests at all), but a future sat route added beside the
existing helpers should come with its own assertion rather than borrowing one.
"""

from __future__ import annotations

import json
import pathlib
import re
import sys
from collections import defaultdict
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
ONTOLOGY = ROOT / "artifacts/ontology/foundational-concepts.json"
SUITE_GLOB = "math_resource_*_routes.rs"

# A call whose name carries one of these decides the instance is a negative
# control: the route must REFUSE something. `reject` covers the tampered-proof
# tests, which are the strongest form — the checker is shown failing on demand.
NEGATIVE_CALL = re.compile(r"(unsat|reject|refut)", re.I)

INCLUDE = re.compile(
    r"const\s+(?P<name>[A-Z0-9_]+)\s*:\s*&str\s*=\s*include_str!\(\s*"
    r'"[^"]*?artifacts/examples/math/(?P<pack>[a-z0-9-]+)/(?P<rest>[^"]+)"',
    re.S,
)
# What counts as a negative control, decided per FUNCTION rather than per call.
#
# The suites express refusal two different ways, and any criterion that sees
# only one of them silently under-reports:
#
#   * `axeyum-cnf`'s boolean routes call helpers whose NAME carries it —
#     `assert_unsat_resource_cnf_checks`, `..._rejects_tampered_proofs`;
#   * the LRA/LIA/BV/UF routes assert on the RESULT TYPE inside a helper —
#     `matches!(&report.evidence, Evidence::UnsatFarkas(_))`.
#
# So a function is negative if its own body asserts refusal, OR if it calls a
# function already known to be negative. That transitivity is what connects a
# test naming the instance to the helper doing the asserting.
NEGATIVE_BODY = re.compile(
    r"(Unsat|Disproved|Refuted|unsatisfiable|reject|refut)", re.I
)
FUNCTION = re.compile(r"\bfn\s+(?P<name>[a-z_][a-z0-9_]*)\s*(?:<[^>]*>)?\s*\(")


def function_bodies(text: str) -> dict[str, str]:
    """`name -> body source`, braces balanced so nested blocks are kept whole."""
    bodies: dict[str, str] = {}
    for match in FUNCTION.finditer(text):
        brace = text.find("{", match.end())
        if brace < 0:
            continue
        depth = 0
        for index in range(brace, len(text)):
            if text[index] == "{":
                depth += 1
            elif text[index] == "}":
                depth -= 1
                if depth == 0:
                    bodies[match["name"]] = text[brace : index + 1]
                    break
    return bodies


def suites(root: pathlib.Path | None = None) -> list[pathlib.Path]:
    return sorted((root or ROOT.joinpath("crates")).rglob(SUITE_GLOB))


def instance_evidence(paths: list[pathlib.Path] | None = None) -> dict[str, dict[str, Any]]:
    """`pack -> {instances, negative_instances, suites}`, read from the sources.

    A const bound to a pack file is "negative" when it appears as an argument to
    a call whose function name matches [`NEGATIVE_CALL`].
    """
    evidence: dict[str, dict[str, Any]] = defaultdict(
        lambda: {"instances": set(), "negative": set(), "suites": set()}
    )
    for path in paths if paths is not None else suites():
        text = path.read_text(encoding="utf-8")
        const_to_file: dict[str, tuple[str, str]] = {}
        for match in INCLUDE.finditer(text):
            const_to_file[match["name"]] = (match["pack"], match["rest"])
            record = evidence[match["pack"]]
            record["instances"].add(match["rest"])
            record["suites"].add(path.name)

        bodies = function_bodies(text)
        negative_fns = {
            name for name, body in bodies.items() if NEGATIVE_BODY.search(body)
        }
        # One transitive step: a test that calls a negative helper is negative.
        for name, body in bodies.items():
            if name in negative_fns:
                continue
            if any(re.search(rf"\b{helper}\s*\(", body) for helper in negative_fns):
                negative_fns.add(name)

        for name in negative_fns:
            for const, (pack, rest) in const_to_file.items():
                if re.search(rf"\b{const}\b", bodies[name]):
                    evidence[pack]["negative"].add(rest)
    return evidence


def curriculum_nodes() -> list[dict[str, Any]]:
    rows = json.loads(ONTOLOGY.read_text(encoding="utf-8"))["rows"]
    return [row for row in rows if row["kind"] == "curriculum-node"]


def evaluate(
    nodes: list[dict[str, Any]], evidence: dict[str, dict[str, Any]]
) -> tuple[list[str], dict[str, int], list[tuple[str, int, int, int, int]]]:
    """`(failures, counts, rows)` for the `covered` nodes."""
    failures: list[str] = []
    counts = {"covered": 0, "running": 0, "with_negative_control": 0}
    rows: list[tuple[str, int, int, int, int]] = []
    for node in sorted(nodes, key=lambda row: row["id"]):
        if node["curriculum_status"] != "covered":
            continue
        counts["covered"] += 1
        packs = [pack["id"] for pack in (node.get("example_packs") or [])]
        executing = [pack for pack in packs if pack in evidence]
        negative = [pack for pack in executing if evidence[pack]["negative"]]
        if executing:
            counts["running"] += 1
        else:
            failures.append(
                f"{node['id']}: status `covered` but none of its {len(packs)} "
                "example pack(s) is referenced by an executing suite — the label "
                "asserts a family that does not run"
            )
        if negative:
            counts["with_negative_control"] += 1
        elif executing:
            failures.append(
                f"{node['id']}: status `covered` and it runs, but no executing "
                "instance participates in a refutation assertion — the route has "
                "been shown to answer, not to refuse"
            )
        rows.append(
            (
                node["id"],
                len(packs),
                len(executing),
                sum(len(evidence[p]["instances"]) for p in executing),
                sum(len(evidence[p]["negative"]) for p in executing),
            )
        )
    return failures, counts, rows


def main(argv: list[str]) -> int:
    quiet = "--quiet" in argv
    evidence = instance_evidence()
    if not evidence:
        print(
            "CURRICULUM_COVERAGE_ERROR|no example-pack references found in any "
            f"{SUITE_GLOB}; this check is looking at the wrong tree or has "
            "stopped parsing",
            file=sys.stderr,
        )
        return 1

    failures, counts, rows = evaluate(curriculum_nodes(), evidence)
    if not quiet:
        for node_id, packs, executing, instances, negatives in rows:
            print(
                f"  {node_id:34s} packs={packs:3d} executing={executing:3d} "
                f"instances={instances:3d} negative={negatives:3d}"
            )
    print(
        f"CURRICULUM_COVERAGE|covered={counts['covered']}|"
        f"running={counts['running']}|"
        f"with_negative_control={counts['with_negative_control']}|"
        f"suites={len(suites())}"
    )
    for failure in failures:
        print(f"CURRICULUM_COVERAGE_ERROR|{failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
