#!/usr/bin/env python3
"""Gate for the L3-D0 effort-taxonomy artifact.

Fails on absence, not just on malformed JSON. Specifically enforced (each is
an independent guard, see scripts/tests/test-effort-taxonomy.py for the
mutation-kill table):

  G1  episode count >= taxonomy.json's floor (the D0 exit criterion: at
      least 20 representative episodes).
  G2  every category any episode actually USES (primary or secondary) has a
      non-empty definition in taxonomy.json -- an undefined category is a
      hard failure, not a warning.
  G3  every episode carries the required fields, all non-empty, with kind/
      domain/basis drawn from the fixed enums.
  G4  basis <-> corroboration shape agreement: "self-report" must carry an
      empty/"none" corroboration; "corroborated" must carry a non-empty
      corroboration of a recognised type.
  G5  corroboration RE-VERIFICATION: a "commit" ref must resolve to a real
      commit in this repository's object store; an "adr" ref must have a
      matching file under docs/research/09-decisions/; a "file" ref must
      exist on disk. This is the guard that stops "corroborated" being a
      label anyone can type -- it is re-derived here, not trusted from the
      episode's own JSON.
  G6  every episode's "source" path exists on disk.
  G7  coverage: at least one "completed" AND one "declined" episode; at
      least one "mathematical" AND one "infrastructural" episode. A sample
      of only successes, or only one domain, cannot see the failure modes
      that cost the most (see the D0 brief).
  G8  no duplicate episode ids (would silently double-count in the
      distribution).
  G9  distribution.json and report.md are fresh relative to the JSON inputs
      (delegates to gen-effort-taxonomy.py --check, which imports the SAME
      compute_distribution() this file would otherwise have to reimplement).

Exit 0 only if every guard passes. Any single violation exits 1 and names
the episode/category/path responsible.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_DIR = ROOT / "artifacts" / "effort-taxonomy"
TAXONOMY_PATH = ARTIFACT_DIR / "taxonomy.json"
EPISODES_PATH = ARTIFACT_DIR / "episodes.json"

sys.path.insert(0, str(ROOT / "scripts"))
import importlib.util as _ilu

_gen_spec = _ilu.spec_from_file_location(
    "gen_effort_taxonomy", ROOT / "scripts" / "gen-effort-taxonomy.py"
)
_gen = _ilu.module_from_spec(_gen_spec)
assert _gen_spec.loader is not None
_gen_spec.loader.exec_module(_gen)

REQUIRED_FIELDS = [
    "id",
    "source",
    "lane",
    "primary_category",
    "secondary_categories",
    "kind",
    "domain",
    "basis",
    "corroboration",
    "summary",
]
VALID_KINDS = {"completed", "partial", "declined"}
VALID_DOMAINS = {"mathematical", "infrastructural"}
VALID_BASES = {"self-report", "corroborated"}
VALID_CORROBORATION_TYPES = {"none", "commit", "adr", "file"}


class Violation(list):
    """Accumulates human-readable failure strings; truthy iff non-empty."""


def guard_floor(taxonomy: dict, episodes: list[dict]) -> Violation:
    v = Violation()
    floor = taxonomy.get("floor", 0)
    if len(episodes) < floor:
        v.append(
            f"G1 FLOOR: {len(episodes)} episodes < required floor {floor} "
            "(D0's exit criterion is at least 20 representative episodes)"
        )
    return v


def guard_categories_defined(taxonomy: dict, episodes: list[dict]) -> Violation:
    v = Violation()
    defined = taxonomy.get("categories", {})
    used: set[str] = set()
    for ep in episodes:
        used.add(ep.get("primary_category", ""))
        used.update(ep.get("secondary_categories", []) or [])
    for cat in sorted(used):
        if not cat:
            continue
        definition = defined.get(cat)
        if not definition or not isinstance(definition, str) or not definition.strip():
            v.append(f"G2 UNDEFINED CATEGORY: '{cat}' used by an episode but has no definition in taxonomy.json")
    return v


def guard_required_fields(episodes: list[dict]) -> Violation:
    v = Violation()
    for i, ep in enumerate(episodes):
        eid = ep.get("id", f"<index {i}>")
        for field in REQUIRED_FIELDS:
            if field not in ep:
                v.append(f"G3 MISSING FIELD: episode '{eid}' has no '{field}'")
                continue
            val = ep[field]
            if field in ("secondary_categories",):
                if not isinstance(val, list):
                    v.append(f"G3 BAD TYPE: episode '{eid}' field '{field}' must be a list")
                continue
            if field == "corroboration":
                if not isinstance(val, dict):
                    v.append(f"G3 BAD TYPE: episode '{eid}' field '{field}' must be an object")
                continue
            if isinstance(val, str) and not val.strip():
                v.append(f"G3 EMPTY FIELD: episode '{eid}' field '{field}' is empty")
        kind = ep.get("kind")
        if kind is not None and kind not in VALID_KINDS:
            v.append(f"G3 BAD ENUM: episode '{eid}' kind='{kind}' not in {sorted(VALID_KINDS)}")
        domain = ep.get("domain")
        if domain is not None and domain not in VALID_DOMAINS:
            v.append(f"G3 BAD ENUM: episode '{eid}' domain='{domain}' not in {sorted(VALID_DOMAINS)}")
        basis = ep.get("basis")
        if basis is not None and basis not in VALID_BASES:
            v.append(f"G3 BAD ENUM: episode '{eid}' basis='{basis}' not in {sorted(VALID_BASES)}")
    return v


def guard_basis_corroboration_shape(episodes: list[dict]) -> Violation:
    v = Violation()
    for ep in episodes:
        eid = ep.get("id", "?")
        basis = ep.get("basis")
        corr = ep.get("corroboration") or {}
        ctype = corr.get("type")
        refs = corr.get("refs", [])
        if ctype is not None and ctype not in VALID_CORROBORATION_TYPES:
            v.append(f"G4 BAD CORROBORATION TYPE: episode '{eid}' type='{ctype}'")
            continue
        if basis == "self-report":
            if ctype != "none" or refs:
                v.append(
                    f"G4 SHAPE: episode '{eid}' is basis=self-report but carries a "
                    f"corroboration (type={ctype!r}, refs={refs!r}) -- self-report "
                    "episodes must not smuggle in an unverified corroboration"
                )
        elif basis == "corroborated":
            if ctype not in {"commit", "adr", "file"} or not refs:
                v.append(
                    f"G4 SHAPE: episode '{eid}' is basis=corroborated but its "
                    f"corroboration (type={ctype!r}, refs={refs!r}) is empty or "
                    "type=none"
                )
    return v


def _commit_exists(sha: str) -> bool:
    result = subprocess.run(
        ["git", "-C", str(ROOT), "cat-file", "-e", f"{sha}^{{commit}}"],
        capture_output=True,
    )
    return result.returncode == 0


def _adr_exists(number: str) -> bool:
    matches = list((ROOT / "docs" / "research" / "09-decisions").glob(f"adr-{number}-*.md"))
    return len(matches) > 0


def guard_corroboration_reverified(episodes: list[dict]) -> Violation:
    v = Violation()
    for ep in episodes:
        eid = ep.get("id", "?")
        corr = ep.get("corroboration") or {}
        ctype = corr.get("type")
        refs = corr.get("refs", []) or []
        if ctype == "commit":
            for ref in refs:
                if not _commit_exists(ref):
                    v.append(f"G5 DANGLING COMMIT: episode '{eid}' cites commit '{ref}', which does not resolve in this repo")
        elif ctype == "adr":
            for ref in refs:
                if not _adr_exists(ref):
                    v.append(f"G5 DANGLING ADR: episode '{eid}' cites ADR-{ref}, no matching file under docs/research/09-decisions/")
        elif ctype == "file":
            for ref in refs:
                if not (ROOT / ref).exists():
                    v.append(f"G5 DANGLING FILE: episode '{eid}' cites file '{ref}', which does not exist")
    return v


def guard_source_exists(episodes: list[dict]) -> Violation:
    v = Violation()
    for ep in episodes:
        eid = ep.get("id", "?")
        src = ep.get("source")
        if src and not (ROOT / src).exists():
            v.append(f"G6 DANGLING SOURCE: episode '{eid}' source '{src}' does not exist")
    return v


def guard_coverage(episodes: list[dict]) -> Violation:
    v = Violation()
    kinds = {ep.get("kind") for ep in episodes}
    domains = {ep.get("domain") for ep in episodes}
    if "completed" not in kinds:
        v.append("G7 COVERAGE: no 'completed' episode in the sample")
    if "declined" not in kinds:
        v.append("G7 COVERAGE: no 'declined' episode in the sample")
    if "mathematical" not in domains:
        v.append("G7 COVERAGE: no 'mathematical' episode in the sample")
    if "infrastructural" not in domains:
        v.append("G7 COVERAGE: no 'infrastructural' episode in the sample")
    return v


def guard_no_duplicate_ids(episodes: list[dict]) -> Violation:
    v = Violation()
    seen: dict[str, int] = {}
    for ep in episodes:
        eid = ep.get("id", "?")
        seen[eid] = seen.get(eid, 0) + 1
    for eid, count in seen.items():
        if count > 1:
            v.append(f"G8 DUPLICATE ID: '{eid}' appears {count} times")
    return v


def guard_generated_fresh(taxonomy_path: Path, episodes_path: Path) -> Violation:
    v = Violation()
    result = subprocess.run(
        [sys.executable, str(ROOT / "scripts" / "gen-effort-taxonomy.py"), "--check"],
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        v.append(
            "G9 STALE GENERATED ARTIFACT: "
            + (result.stdout.strip() or result.stderr.strip() or "gen-effort-taxonomy.py --check failed")
        )
    return v


def run_all_guards(
    taxonomy: dict,
    episodes: list[dict],
    taxonomy_path: Path = TAXONOMY_PATH,
    episodes_path: Path = EPISODES_PATH,
    skip_generated_check: bool = False,
) -> list[str]:
    violations: list[str] = []
    violations += guard_floor(taxonomy, episodes)
    violations += guard_categories_defined(taxonomy, episodes)
    violations += guard_required_fields(episodes)
    violations += guard_basis_corroboration_shape(episodes)
    violations += guard_corroboration_reverified(episodes)
    violations += guard_source_exists(episodes)
    violations += guard_coverage(episodes)
    violations += guard_no_duplicate_ids(episodes)
    if not skip_generated_check:
        violations += guard_generated_fresh(taxonomy_path, episodes_path)
    return violations


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--taxonomy", type=Path, default=TAXONOMY_PATH)
    parser.add_argument("--episodes", type=Path, default=EPISODES_PATH)
    parser.add_argument(
        "--skip-generated-check",
        action="store_true",
        help="skip G9 (used by the test harness against scratch fixtures with no matching generated pair)",
    )
    args = parser.parse_args()

    if not args.taxonomy.exists():
        print(f"CHECK_EFFORT_TAXONOMY|FAIL|reason=missing taxonomy file {args.taxonomy}")
        return 1
    if not args.episodes.exists():
        print(f"CHECK_EFFORT_TAXONOMY|FAIL|reason=missing episodes file {args.episodes}")
        return 1

    taxonomy = json.loads(args.taxonomy.read_text())
    episodes = json.loads(args.episodes.read_text())

    violations = run_all_guards(
        taxonomy,
        episodes,
        taxonomy_path=args.taxonomy,
        episodes_path=args.episodes,
        skip_generated_check=args.skip_generated_check,
    )

    if violations:
        print(f"CHECK_EFFORT_TAXONOMY|FAIL|violations={len(violations)}")
        for line in violations:
            print("  " + line)
        return 1

    print(
        f"CHECK_EFFORT_TAXONOMY|PASS|episodes={len(episodes)}|"
        f"categories={len(taxonomy.get('categories', {}))}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
