#!/usr/bin/env python3
"""Shared fixture builder for the five C0 library-artifact mutation classes.

Both `test-library-artifact-contract.py` (in-process assertions) and
`test-library-artifact-contract-mutations.sh` (the guard-deletion kill table,
run in a scratch copy per CLAUDE.md's mutation-testing rule) use this module
to build the SAME six pack variants -- the untouched positive pack plus one
mutation per class -- so the fixtures used to prove "each mutation fails" and
the fixtures used to prove "deleting guard X only flips mutation X" are
identical.

Each mutation is built to be surgical: every OTHER self-referential field an
attacker could plausibly recompute (pack_digest, the pack's own internal
`source_population` counts/roots) is kept internally consistent, so the ONLY
thing left inconsistent is the one invariant the mutation's target guard
checks. Without this, e.g. appending a duplicate declaration would also
change the declaration count and could be caught by an unrelated check,
making "delete guard X, exactly test X flips" untrue by accident rather than
by design.

Writes, for each of {good, missing, duplicate, reordered, truncated,
value_exposed}, a `<name>.pack.json` and a `<name>.typeproj.json` into a
target directory, plus copies the (untouched) external population registry
directory alongside so `--population-dir` can point at a self-contained
scratch tree if desired.
"""
from __future__ import annotations

import copy
import hashlib
import json
import shutil
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
GOOD_PACK = REPO_ROOT / "artifacts" / "library-artifact" / "packs" / "nat-add-comm-v1.pack.json"
GOOD_TYPEPROJ = REPO_ROOT / "artifacts" / "library-artifact" / "packs" / "nat-add-comm-v1.typeproj.json"
POPULATION_DIR = REPO_ROOT / "artifacts" / "library-artifact" / "populations"

MUTATION_NAMES = [
    "missing", "duplicate", "reordered", "truncated", "value_exposed",
    "unstated_provenance",
]
# Which guard, in scripts/check-library-artifact-contract.py, is supposed to
# be the ONLY one that rejects each mutation.
MUTATION_TO_GUARD = {
    "missing": "MISSING",
    "duplicate": "DUPLICATE",
    "reordered": "REORDERED",
    "truncated": "TRUNCATED",
    "value_exposed": "VALUE_EXPOSED",
    "unstated_provenance": "PROVENANCE",
}


def _sha256_hex(s: str) -> str:
    return "sha256:" + hashlib.sha256(s.encode("utf-8")).hexdigest()


def _pack_digest(declarations: list) -> str:
    return _sha256_hex("\n".join(d["identity_digest"] for d in declarations))


def load_good() -> tuple[dict, dict]:
    with open(GOOD_PACK, "r", encoding="utf-8") as f:
        pack = json.load(f)
    with open(GOOD_TYPEPROJ, "r", encoding="utf-8") as f:
        typeproj = json.load(f)
    return pack, typeproj


def build_missing(pack: dict) -> dict:
    """Delete the `id` declaration -- a root named in the EXTERNAL population
    registry (artifacts/library-artifact/populations/nat-add-comm-v1.json)
    -- and, as an attacker would, tidy up every field the pack itself
    controls to hide it: drop `id` from the pack's own
    source_population.requested_roots, decrement its own
    expected_declaration_count, and recompute pack_digest over the remaining
    8 records. Only the EXTERNAL registry (untouched, still says `id` is
    expected) can still tell."""
    mutated = copy.deepcopy(pack)
    mutated["declarations"] = [d for d in mutated["declarations"] if d["name"] != "id"]
    sp = mutated["source_population"]
    sp["requested_roots"] = [r for r in sp["requested_roots"] if r != "id"]
    sp["expected_declaration_count"] = len(mutated["declarations"])
    mutated["pack_digest"] = _pack_digest(mutated["declarations"])
    return mutated


def build_duplicate(pack: dict) -> dict:
    """Append a byte-for-byte duplicate of the `Eq.refl` record. Update the
    pack's own declared count (10) and recompute pack_digest over the new
    10-entry chain, so only a name-uniqueness check -- not a count check or
    the order-sensitive pack_digest check -- can catch it."""
    mutated = copy.deepcopy(pack)
    eq_refl = next(d for d in mutated["declarations"] if d["name"] == "Eq.refl")
    mutated["declarations"] = mutated["declarations"] + [copy.deepcopy(eq_refl)]
    mutated["source_population"]["expected_declaration_count"] = len(mutated["declarations"])
    mutated["pack_digest"] = _pack_digest(mutated["declarations"])
    return mutated


def build_reordered(pack: dict) -> dict:
    """Swap the file-order positions of two untouched records (`Eq` and
    `Nat`). Every per-record digest is unaffected -- only the order-sensitive
    pack_digest chain notices, and it is deliberately NOT recomputed here,
    because that staleness IS the mutation."""
    mutated = copy.deepcopy(pack)
    decls = mutated["declarations"]
    i = next(idx for idx, d in enumerate(decls) if d["name"] == "Eq")
    j = next(idx for idx, d in enumerate(decls) if d["name"] == "Nat")
    decls[i], decls[j] = decls[j], decls[i]
    # pack_digest intentionally left as the ORIGINAL (pre-swap) value.
    return mutated


def build_truncated(pack: dict) -> dict:
    """Cut the `type` text of `Nat.add` short, leaving its recorded
    type_digest/identity_digest as they were (correct for the ORIGINAL,
    un-truncated text). Nothing about names, order, or the projection file
    changes."""
    mutated = copy.deepcopy(pack)
    for d in mutated["declarations"]:
        if d["name"] == "Nat.add":
            assert len(d["type"]) > 6
            d["type"] = d["type"][:6]
            # type_digest / identity_digest / pack_digest deliberately stale.
    return mutated



def build_unstated_provenance(pack: dict) -> dict:
    """A pack that does not say whether its text was EXTRACTED or written.

    The version pins beside it are real either way, so without this field a
    hand-authored pack is indistinguishable from `lean4export` output to
    anything that reads the JSON rather than the README.
    """
    out = copy.deepcopy(pack)
    out.pop("text_provenance", None)
    return out


def build_value_exposed(typeproj: dict) -> dict:
    """Inject a `value` key -- proof-derived data -- into one record of the
    type-only producer projection. The full pack is untouched for this
    mutation; only the projection file the mutation targets changes."""
    mutated = copy.deepcopy(typeproj)
    for d in mutated["declarations"]:
        if d["name"] == "Nat.add_comm":
            d["value"] = "fun n m => Nat.rec (Eq.refl n) (fun k ih => ih) m"  # leaked proof text
    return mutated


def write_fixtures(target_dir: Path) -> dict:
    """Writes good.pack.json/.typeproj.json plus one <mutation>.pack.json/
    .typeproj.json pair per mutation class into target_dir. Returns a dict of
    {name: (pack_path, typeproj_path)}."""
    target_dir.mkdir(parents=True, exist_ok=True)
    pack, typeproj = load_good()

    paths: dict[str, tuple[Path, Path]] = {}

    def _write(name: str, pack_doc: dict, typeproj_doc: dict) -> None:
        pp = target_dir / f"{name}.pack.json"
        tp = target_dir / f"{name}.typeproj.json"
        with open(pp, "w", encoding="utf-8") as f:
            json.dump(pack_doc, f, indent=2)
        with open(tp, "w", encoding="utf-8") as f:
            json.dump(typeproj_doc, f, indent=2)
        paths[name] = (pp, tp)

    _write("good", pack, typeproj)
    _write("missing", build_missing(pack), typeproj)
    _write("duplicate", build_duplicate(pack), typeproj)
    _write("reordered", build_reordered(pack), typeproj)
    _write("truncated", build_truncated(pack), typeproj)
    _write("value_exposed", pack, build_value_exposed(typeproj))
    _write("unstated_provenance", build_unstated_provenance(pack), typeproj)

    reg_dir = target_dir / "populations"
    if reg_dir.exists():
        shutil.rmtree(reg_dir)
    shutil.copytree(POPULATION_DIR, reg_dir)

    return paths


if __name__ == "__main__":
    import argparse
    import sys

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-fixtures", type=Path, required=True)
    args = parser.parse_args()
    written = write_fixtures(args.write_fixtures)
    for name, (pp, tp) in sorted(written.items()):
        print(f"{name}: {pp} {tp}")
    print(f"population registry copied to: {args.write_fixtures / 'populations'}")
    sys.exit(0)
