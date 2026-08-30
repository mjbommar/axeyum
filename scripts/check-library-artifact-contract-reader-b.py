#!/usr/bin/env python3
"""READER B for the L1 phase C0 library-artifact contract.

This is a SEPARATE, independently-coded implementation of the spec in
`artifacts/library-artifact/README.md` -- it shares no helper function with
`scripts/check-library-artifact-contract.py` (reader A). If the two ever
imported a common `compute_identity_digest`, they would be one reader with
two names; "two independent readers reproduce all identities" is the C0 exit
criterion precisely because agreement between genuinely separate code is
evidence the SPEC is well-defined, not evidence that one implementation
agrees with itself.

Deliberate differences from reader A, all converging on the same digests
because the spec is a total function of the recorded fields:

  * Digests are assembled with incremental `hashlib.sha256().update(...)`
    calls per field (with an explicit trailing separator byte), not a single
    `"\\x00".join(...).encode()` string built first.
  * Every record is wrapped in a `Decl` dataclass rather than kept as a raw
    dict, and the two closures are computed by depth-first recursion with a
    dict-of-frozensets memo table, not reader A's breadth-first
    worklist-with-a-list-and-a-set.
  * Class-based `Graph` adjacency construction (a dict built once, up front)
    instead of reader A's inline per-record edge lookups.

Reader B also implements the same five guards independently, for the same
reason: a mutation the two readers disagree about would mean the SPEC left
something ambiguous, which is exactly what running two readers is for.

Usage:
    python3 scripts/check-library-artifact-contract-reader-b.py
    python3 scripts/check-library-artifact-contract-reader-b.py --pack PATH --population-dir DIR
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_PACKS_DIR = REPO_ROOT / "artifacts" / "library-artifact" / "packs"
DEFAULT_POPULATION_DIR = REPO_ROOT / "artifacts" / "library-artifact" / "populations"

TRUSTED_KINDS = frozenset({"Inductive", "Constructor", "Recursor", "Axiom", "Opaque", "Quotient"})
TYPEPROJ_ALLOWED_KEYS = frozenset(
    {"name", "kind", "universes", "type", "type_digest", "direct_type_deps", "transitive_type_deps"}
)


def _digest_of_fields(*fields: str) -> str:
    """Incremental hashing with an explicit separator byte BETWEEN fields,
    rather than reader A's build-the-string-then-hash-once. Produces
    identical bytes to hashing `"\\x00".join(fields)` because SHA-256's
    `update()` is defined to be equivalent to hashing the concatenation of
    everything ever passed to it -- this is the point: a different code path
    that is REQUIRED to land on the same digest. (No separator after the
    LAST field -- that would hash a different byte string than
    `"\\x00".join(...)` does, which is exactly the kind of off-by-one two
    independently written readers exist to surface: an earlier draft of this
    function added a trailing separator and reader A/B disagreed on every
    single declaration until it was fixed.)"""
    h = hashlib.sha256()
    for i, field in enumerate(fields):
        if i > 0:
            h.update(b"\x00")
        h.update(field.encode("utf-8"))
    return "sha256:" + h.hexdigest()


def _digest_of_text(text: str) -> str:
    return "sha256:" + hashlib.sha256(text.encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class Decl:
    name: str
    kind: str
    universes: tuple
    type_text: str
    value_text: str | None
    type_digest: str
    value_digest: str | None
    identity_digest: str
    direct_type_deps: frozenset
    direct_value_deps: frozenset
    transitive_type_deps: frozenset
    transitive_value_deps: frozenset

    @staticmethod
    def from_json(d: dict) -> "Decl":
        return Decl(
            name=d["name"],
            kind=d["kind"],
            universes=tuple(d["universes"]),
            type_text=d["type"],
            value_text=d["value"],
            type_digest=d["type_digest"],
            value_digest=d["value_digest"],
            identity_digest=d["identity_digest"],
            direct_type_deps=frozenset(d["direct_type_deps"]),
            direct_value_deps=frozenset(d["direct_value_deps"]),
            transitive_type_deps=frozenset(d["transitive_type_deps"]),
            transitive_value_deps=frozenset(d["transitive_value_deps"]),
        )


class Graph:
    """Adjacency built once from the whole declaration list; closures are
    then pure recursive lookups against it. Reader A never builds a graph
    object -- it looks up edges inline per record."""

    def __init__(self, decls: list[Decl]):
        self.by_name = {d.name: d for d in decls}

    def type_neighbors(self, name: str) -> frozenset:
        d = self.by_name.get(name)
        return d.direct_type_deps if d else frozenset()

    def value_neighbors(self, name: str) -> frozenset:
        d = self.by_name.get(name)
        if d is None:
            return frozenset()
        return d.direct_type_deps | d.direct_value_deps

    def closure(self, start: frozenset, neighbors_of) -> frozenset:
        """Depth-first recursion with memoized visited set, as opposed to
        reader A's breadth-first frontier loop."""
        visited: set = set()

        def visit(n: str) -> None:
            if n in visited:
                return
            visited.add(n)
            for m in neighbors_of(n):
                visit(m)

        for s in start:
            visit(s)
        return frozenset(visited)


def recompute_identity(d: Decl) -> tuple:
    """Returns (type_digest, value_digest, identity_digest) recomputed from
    d's own fields, independent of reader A's assembly order/style."""
    type_digest = _digest_of_text(d.type_text)
    value_digest = None if d.value_text is None else _digest_of_text(d.value_text)
    identity_digest = _digest_of_fields(
        d.name,
        d.kind,
        ",".join(d.universes),
        type_digest,
        value_digest if value_digest is not None else "NONE",
        ",".join(sorted(d.direct_type_deps)),
        ",".join(sorted(d.direct_value_deps)),
    )
    return type_digest, value_digest, identity_digest


def recompute_pack_digest(decls_in_file_order: list[Decl]) -> str:
    h = hashlib.sha256()
    for i, d in enumerate(decls_in_file_order):
        if i > 0:
            h.update(b"\n")
        h.update(d.identity_digest.encode("utf-8"))
    return "sha256:" + h.hexdigest()


def load_json(path: Path) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def guard_missing(decls: list[Decl], pack: dict, population_dir: Path) -> list[str]:
    population_id = pack.get("source_population", {}).get("population_id")
    if not population_id:
        return ["reader-b: source_population.population_id required"]
    registry_path = population_dir / f"{population_id}.json"
    if not registry_path.is_file():
        return [f"reader-b: no population registry at {registry_path}"]
    registry = load_json(registry_path)
    present = frozenset(d.name for d in decls)
    absent = [r for r in registry.get("expected_roots", []) if r not in present]
    if absent:
        return [f"reader-b: population {population_id!r} missing expected root(s): {sorted(absent)}"]
    return []


def guard_duplicate(decls_in_file_order: list[Decl]) -> list[str]:
    counts: dict[str, int] = {}
    for d in decls_in_file_order:
        counts[d.name] = counts.get(d.name, 0) + 1
    repeated = sorted(n for n, c in counts.items() if c > 1)
    if repeated:
        return [f"reader-b: repeated name(s): {repeated}"]
    return []


def guard_reordered(decls_in_file_order: list[Decl], recorded_pack_digest: str) -> list[str]:
    recomputed = recompute_pack_digest(decls_in_file_order)
    if recomputed != recorded_pack_digest:
        return [f"reader-b: pack_digest disagreement: recorded={recorded_pack_digest} recomputed={recomputed}"]
    return []


def guard_truncated(decls: list[Decl], graph: Graph) -> list[str]:
    errors = []
    for d in decls:
        type_digest, value_digest, identity_digest = recompute_identity(d)
        if type_digest != d.type_digest:
            errors.append(f"reader-b: {d.name} type_digest disagreement")
        if value_digest != d.value_digest:
            errors.append(f"reader-b: {d.name} value_digest disagreement")
        if identity_digest != d.identity_digest:
            errors.append(f"reader-b: {d.name} identity_digest disagreement")
        recomputed_ttd = graph.closure(d.direct_type_deps, graph.type_neighbors)
        if recomputed_ttd != d.transitive_type_deps:
            errors.append(f"reader-b: {d.name} transitive_type_deps disagreement")
        recomputed_tvd = graph.closure(d.direct_type_deps | d.direct_value_deps, graph.value_neighbors)
        if recomputed_tvd != d.transitive_value_deps:
            errors.append(f"reader-b: {d.name} transitive_value_deps disagreement")
    return errors


def guard_value_exposed(typeproj_path: Path) -> list[str]:
    if not typeproj_path.is_file():
        return [f"reader-b: no projection at {typeproj_path}"]
    doc = load_json(typeproj_path)
    errors = []
    for rec in doc.get("declarations", []):
        extra = set(rec.keys()) - TYPEPROJ_ALLOWED_KEYS
        if extra:
            errors.append(f"reader-b: {rec.get('name', '?')} carries non-type-only key(s): {sorted(extra)}")
    return errors


def typeproj_path_for(pack_path: Path) -> Path:
    name = pack_path.name
    assert name.endswith(".pack.json")
    return pack_path.with_name(name[: -len(".pack.json")] + ".typeproj.json")


def identities_report(decls_in_file_order: list[Decl]) -> dict:
    """The per-declaration identity map reader B reproduces -- compared
    against reader A's equivalent report by
    scripts/tests/test-library-artifact-contract-mutations.py to demonstrate
    the two readers actually agree, not merely that each is self-consistent."""
    report = {}
    for d in decls_in_file_order:
        type_digest, value_digest, identity_digest = recompute_identity(d)
        report[d.name] = {
            "type_digest": type_digest,
            "value_digest": value_digest,
            "identity_digest": identity_digest,
        }
    return report


def validate_pack(pack_path: Path, population_dir: Path) -> list[str]:
    pack = load_json(pack_path)
    decls_in_file_order = [Decl.from_json(d) for d in pack["declarations"]]
    graph = Graph(decls_in_file_order)

    errors: list[str] = []
    errors += guard_missing(decls_in_file_order, pack, population_dir)
    errors += guard_duplicate(decls_in_file_order)
    errors += guard_reordered(decls_in_file_order, pack["pack_digest"])
    errors += guard_truncated(decls_in_file_order, graph)
    errors += guard_value_exposed(typeproj_path_for(pack_path))
    return [f"{pack_path}: {e}" for e in errors]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pack", type=Path, default=None)
    parser.add_argument("--population-dir", type=Path, default=DEFAULT_POPULATION_DIR)
    parser.add_argument("--print-identities", action="store_true", help="Dump the identities report as JSON and exit")
    args = parser.parse_args()

    pack_paths = [args.pack] if args.pack is not None else sorted(DEFAULT_PACKS_DIR.glob("*.pack.json"))
    if not pack_paths:
        print("reader-b: no packs found", file=sys.stderr)
        return 1

    if args.print_identities:
        pack = load_json(pack_paths[0])
        decls = [Decl.from_json(d) for d in pack["declarations"]]
        print(json.dumps(identities_report(decls), indent=2, sort_keys=True))
        return 0

    all_errors: list[str] = []
    for p in pack_paths:
        errs = validate_pack(p, args.population_dir)
        if errs:
            all_errors.extend(errs)
        else:
            print(f"reader-b: OK {p}")

    if all_errors:
        print("reader-b: FAILED", file=sys.stderr)
        for e in all_errors:
            print(f"  {e}", file=sys.stderr)
        return 1
    print(f"reader-b: {len(pack_paths)} pack(s) valid")
    return 0


if __name__ == "__main__":
    sys.exit(main())
