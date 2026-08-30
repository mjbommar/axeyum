#!/usr/bin/env python3
"""Validate `artifacts/library-artifact/packs/*.pack.json` (L1 phase C0).

This is READER A: the primary validator, wired into the aggregate gate. It
re-derives every digest and closure in a pack from that pack's own recorded
fields (never trusting a stored digest without recomputing it), and runs five
independent guards, one per mutation class the C0 exit criterion names:
MISSING, DUPLICATE, REORDERED, TRUNCATED, VALUE_EXPOSED. Each guard function
below is delimited by a `# GUARD:<NAME> begin/end` comment pair so
`scripts/tests/test-library-artifact-contract-mutations.py` can neutralize
exactly one guard at a time in a scratch copy and confirm that only the
matching mutation's test flips from fail to pass.

Structural validation is deliberately local (no `jsonschema` dependency),
matching `scripts/validate-facts.py`. `artifacts/library-artifact/schema/
library-artifact-pack.schema.json` documents the same shape for reference.

See `artifacts/library-artifact/README.md` for the full spec this file
implements: the canonical digest algorithm, the closure definitions, and the
structural type/proof separation (READER B is
`scripts/check-library-artifact-contract-reader-b.py`, coded independently --
different digest assembly, different traversal, different visited-set
representation -- and must agree with this file on every accepted pack).

Usage:
    python3 scripts/check-library-artifact-contract.py
    python3 scripts/check-library-artifact-contract.py --pack PATH --population-dir DIR
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_PACKS_DIR = REPO_ROOT / "artifacts" / "library-artifact" / "packs"
DEFAULT_POPULATION_DIR = REPO_ROOT / "artifacts" / "library-artifact" / "populations"

TRUSTED_KINDS = {"Inductive", "Constructor", "Recursor", "Axiom", "Opaque", "Quotient"}
ALL_KINDS = TRUSTED_KINDS | {"Definition", "Theorem"}

REQUIRED_PACK_KEYS = {
    "contract_version", "text_provenance",
    "lean_version", "lean_commit", "mathlib_version",
    "mathlib_commit", "normalization_version", "renderer_version",
    "source_population", "trusted_declaration_identities", "pack_digest",
    "declarations",
}
REQUIRED_DECL_KEYS = {
    "name", "kind", "universes", "type", "value", "type_digest",
    "value_digest", "identity_digest", "direct_type_deps",
    "direct_value_deps", "transitive_type_deps", "transitive_value_deps",
}
REQUIRED_TYPEPROJ_DECL_KEYS = {
    "name", "kind", "universes", "type", "type_digest",
    "direct_type_deps", "transitive_type_deps",
}


class ContractError(Exception):
    """A pack or projection violates the C0 contract."""


def sha256_hex(data: str) -> str:
    return "sha256:" + hashlib.sha256(data.encode("utf-8")).hexdigest()


def compute_type_digest(decl: dict) -> str:
    return sha256_hex(decl["type"])


def compute_value_digest(decl: dict) -> str | None:
    if decl["value"] is None:
        return None
    return sha256_hex(decl["value"])


def compute_identity_digest(decl: dict, type_digest: str, value_digest: str | None) -> str:
    identity_string = (
        decl["name"] + "\x00" + decl["kind"] + "\x00" +
        ",".join(decl["universes"]) + "\x00" +
        type_digest + "\x00" + (value_digest or "NONE") + "\x00" +
        ",".join(sorted(decl["direct_type_deps"])) + "\x00" +
        ",".join(sorted(decl["direct_value_deps"]))
    )
    return sha256_hex(identity_string)


def compute_pack_digest(declarations: list) -> str:
    chain = "\n".join(d["identity_digest"] for d in declarations)
    return sha256_hex(chain)


def compute_closure(start: set, edges: dict) -> list:
    seen = set(start)
    frontier = list(start)
    while frontier:
        nxt = []
        for n in frontier:
            for m in edges.get(n, []):
                if m not in seen:
                    seen.add(m)
                    nxt.append(m)
        frontier = nxt
    return sorted(seen)


def load_json(path: Path) -> dict:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def check_basic_shape(pack: dict, path: Path) -> list[str]:
    """Foundational, always-on structural validation. Not one of the five
    named mutation-class guards; it is never neutralized by the mutation
    harness, so it must not be the thing that actually catches any of the
    five mutations below (each mutation is constructed so the pack stays
    self-consistent everywhere except the one invariant its target guard
    checks)."""
    errors = []
    missing = REQUIRED_PACK_KEYS - pack.keys()
    if missing:
        errors.append(f"{path}: pack missing required keys: {sorted(missing)}")
        return errors
    if not isinstance(pack["declarations"], list) or not pack["declarations"]:
        errors.append(f"{path}: `declarations` must be a non-empty array")
        return errors
    for i, decl in enumerate(pack["declarations"]):
        missing_d = REQUIRED_DECL_KEYS - decl.keys()
        if missing_d:
            errors.append(f"{path}: declarations[{i}] missing keys: {sorted(missing_d)}")
            continue
        if decl["kind"] not in ALL_KINDS:
            errors.append(f"{path}: declarations[{i}] ({decl['name']}) has unknown kind {decl['kind']!r}")
        is_trusted = decl["kind"] in TRUSTED_KINDS
        has_value = decl["value"] is not None
        if is_trusted == has_value:
            errors.append(
                f"{path}: {decl['name']} kind={decl['kind']} but "
                f"value is {'present' if has_value else 'absent'} "
                f"(trusted kinds must have no value; Definition/Theorem must have one)"
            )
    sp = pack.get("source_population", {})
    for k in ("population_id", "requested_roots", "expected_declaration_count"):
        if k not in sp:
            errors.append(f"{path}: source_population missing `{k}`")
    return errors


# GUARD:MISSING begin
# `lean_commit` and `mathlib_commit` are real pins, so a pack READS as extracted
# output whatever its text actually is. C0's pack is hand-authored: the README
# says so four times and the pack said so nowhere, which is a disclosure that a
# consumer parsing JSON never sees. Naming it IN the pack makes C1's switch to
# real `lean4export` bytes an explicit edit rather than a silent upgrade.
TEXT_PROVENANCE = {
    "hand-authored": "written by this contract, NOT extracted -- shape only",
    "lean4export": "raw bytes from the pinned extractor",
}


def check_text_provenance(pack: dict, pack_path) -> list[str]:
    got = pack.get("text_provenance")
    if got not in TEXT_PROVENANCE:
        return [
            f"{pack_path}: text_provenance {got!r} is not one of "
            f"{sorted(TEXT_PROVENANCE)} -- a pack must say whether its type and "
            "value text was EXTRACTED or hand-authored, because the version pins "
            "beside it look identical either way"
        ]
    return []


def check_missing_roots(pack: dict, population_dir: Path) -> list[str]:
    """The pack's declared `source_population.population_id` selects an
    external registry file this validator loads from `population_dir` -- a
    location the pack under test does not write to and cannot edit. Every
    name in that file's `expected_roots` must be present among
    `declarations[*].name`. An attacker who deletes a root AND edits the
    pack's own `source_population.requested_roots`/`expected_declaration_count`
    to match cannot hide the deletion from this check, because it never reads
    those pack-internal fields as its source of truth."""
    errors = []
    sp = pack.get("source_population", {})
    population_id = sp.get("population_id")
    if not population_id:
        return ["source_population.population_id is required for the MISSING guard"]
    registry_path = population_dir / f"{population_id}.json"
    if not registry_path.exists():
        return [f"no population registry file for population_id={population_id!r} at {registry_path}"]
    registry = load_json(registry_path)
    expected_roots = registry.get("expected_roots", [])
    present_names = {d["name"] for d in pack["declarations"]}
    missing_roots = [r for r in expected_roots if r not in present_names]
    if missing_roots:
        errors.append(
            f"population {population_id!r}: expected root(s) missing from pack "
            f"(per {registry_path}): {sorted(missing_roots)}"
        )
    return errors
# GUARD:MISSING end


# GUARD:DUPLICATE begin
def check_no_duplicate_names(pack: dict) -> list[str]:
    """`declarations[*].name` must be pairwise distinct. A duplicate corrupts
    every dependency lookup silently (whichever copy a reader's dict-building
    loop keeps "wins"), so this must be caught before any deps are resolved,
    independent of whether the aggregate pack_digest was recomputed to hide
    the extra entry."""
    names = [d["name"] for d in pack["declarations"]]
    seen = set()
    dupes = set()
    for n in names:
        if n in seen:
            dupes.add(n)
        seen.add(n)
    if dupes:
        return [f"duplicate declaration name(s): {sorted(dupes)}"]
    return []
# GUARD:DUPLICATE end


# GUARD:REORDERED begin
def check_pack_digest(pack: dict) -> list[str]:
    """`pack_digest` is a hash CHAIN over `identity_digest` in file order
    (see README "Pack digest"). Per-record identity is order-independent
    (dependency sets are sorted before hashing), so this is the only check
    sensitive to the on-disk sequence of `declarations` -- permuting two
    untouched records changes nothing any other guard looks at, but changes
    this."""
    recomputed = compute_pack_digest(pack["declarations"])
    recorded = pack["pack_digest"]
    if recomputed != recorded:
        return [f"pack_digest mismatch: recorded={recorded} recomputed={recomputed}"]
    return []
# GUARD:REORDERED end


# GUARD:TRUNCATED begin
def check_record_digests(pack: dict) -> list[str]:
    """Recompute type_digest/value_digest/identity_digest and both transitive
    closures from each record's own fields and compare against what is
    recorded. Catches content corrupted (e.g. cut short) without its digest
    being recomputed to match -- the digest is the only thing standing
    between "the bytes we hashed" and "the bytes we shipped"."""
    errors = []
    by_name = {d["name"]: d for d in pack["declarations"]}
    type_edges = {n: d["direct_type_deps"] for n, d in by_name.items()}
    value_edges = {
        n: list(d["direct_type_deps"]) + list(d["direct_value_deps"])
        for n, d in by_name.items()
    }
    for decl in pack["declarations"]:
        name = decl["name"]
        want_type_digest = compute_type_digest(decl)
        if want_type_digest != decl["type_digest"]:
            errors.append(f"{name}: type_digest mismatch: recorded={decl['type_digest']} recomputed={want_type_digest}")
        want_value_digest = compute_value_digest(decl)
        if want_value_digest != decl["value_digest"]:
            errors.append(f"{name}: value_digest mismatch: recorded={decl['value_digest']} recomputed={want_value_digest}")
        want_identity_digest = compute_identity_digest(decl, want_type_digest, want_value_digest)
        if want_identity_digest != decl["identity_digest"]:
            errors.append(f"{name}: identity_digest mismatch: recorded={decl['identity_digest']} recomputed={want_identity_digest}")
        want_ttd = compute_closure(set(decl["direct_type_deps"]), type_edges)
        if want_ttd != decl["transitive_type_deps"]:
            errors.append(f"{name}: transitive_type_deps mismatch: recorded={decl['transitive_type_deps']} recomputed={want_ttd}")
        want_tvd = compute_closure(set(decl["direct_type_deps"]) | set(decl["direct_value_deps"]), value_edges)
        if want_tvd != decl["transitive_value_deps"]:
            errors.append(f"{name}: transitive_value_deps mismatch: recorded={decl['transitive_value_deps']} recomputed={want_tvd}")
    return errors
# GUARD:TRUNCATED end


# GUARD:VALUE_EXPOSED begin
def check_typeproj_no_value_leak(typeproj_path: Path) -> list[str]:
    """The producer-facing type-only projection must never carry a
    value-bearing key, on ANY record, of ANY kind. This is the structural
    half of the type/proof separation: a producer that reads only this file
    has no attribute path to proof data even if it wanted one."""
    if not typeproj_path.exists():
        return [f"no type-only projection file at {typeproj_path}"]
    typeproj = load_json(typeproj_path)
    errors = []
    for i, decl in enumerate(typeproj.get("declarations", [])):
        keys = set(decl.keys())
        forbidden = keys - REQUIRED_TYPEPROJ_DECL_KEYS
        if forbidden:
            errors.append(
                f"{typeproj_path}: declarations[{i}] ({decl.get('name', '?')}) "
                f"carries forbidden key(s) in a type-only projection: {sorted(forbidden)}"
            )
        missing = REQUIRED_TYPEPROJ_DECL_KEYS - keys
        if missing:
            errors.append(
                f"{typeproj_path}: declarations[{i}] ({decl.get('name', '?')}) "
                f"missing required type-only key(s): {sorted(missing)}"
            )
    return errors
# GUARD:VALUE_EXPOSED end


def project_type_only(decl: dict) -> dict:
    """Pure projection: destructures ONLY the allowed fields, so it cannot
    leak a value-bearing field even if the source dict carries one."""
    return {
        "name": decl["name"],
        "kind": decl["kind"],
        "universes": decl["universes"],
        "type": decl["type"],
        "type_digest": decl["type_digest"],
        "direct_type_deps": decl["direct_type_deps"],
        "transitive_type_deps": decl["transitive_type_deps"],
    }


def typeproj_path_for(pack_path: Path) -> Path:
    name = pack_path.name
    assert name.endswith(".pack.json"), name
    return pack_path.with_name(name[: -len(".pack.json")] + ".typeproj.json")


def validate_pack(pack_path: Path, population_dir: Path) -> list[str]:
    errors: list[str] = []
    try:
        pack = load_json(pack_path)
    except (json.JSONDecodeError, OSError) as e:
        return [f"{pack_path}: cannot load: {e}"]

    errors += check_basic_shape(pack, pack_path)
    if errors:
        # Basic shape failures make every other check meaningless (e.g. a
        # missing `declarations` key), so stop here rather than cascading.
        return errors

    errors += check_text_provenance(pack, pack_path)
    errors += [f"{pack_path}: {e}" for e in check_missing_roots(pack, population_dir)]
    errors += [f"{pack_path}: {e}" for e in check_no_duplicate_names(pack)]
    errors += [f"{pack_path}: {e}" for e in check_pack_digest(pack)]
    errors += [f"{pack_path}: {e}" for e in check_record_digests(pack)]
    errors += [f"{e}" for e in check_typeproj_no_value_leak(typeproj_path_for(pack_path))]
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pack", type=Path, default=None, help="Validate a single pack file")
    parser.add_argument("--population-dir", type=Path, default=DEFAULT_POPULATION_DIR)
    args = parser.parse_args()

    if args.pack is not None:
        pack_paths = [args.pack]
    else:
        pack_paths = sorted(DEFAULT_PACKS_DIR.glob("*.pack.json"))

    if not pack_paths:
        print("check-library-artifact-contract: no packs found -- nothing checked", file=sys.stderr)
        return 1

    all_errors: list[str] = []
    for p in pack_paths:
        errs = validate_pack(p, args.population_dir)
        if errs:
            all_errors.extend(errs)
        else:
            print(f"check-library-artifact-contract: OK {p}")

    if all_errors:
        print("check-library-artifact-contract: FAILED", file=sys.stderr)
        for e in all_errors:
            print(f"  {e}", file=sys.stderr)
        return 1

    print(f"check-library-artifact-contract: {len(pack_paths)} pack(s) valid")
    return 0


if __name__ == "__main__":
    sys.exit(main())
