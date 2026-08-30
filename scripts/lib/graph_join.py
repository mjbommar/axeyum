"""L1 phase G2 — join the Mathlib declaration graph (ADR-0820) to Axeyum's
own state: ledger facts, kernel declarations, statement vocabulary,
destination curriculum nodes, producers, declines, and trust footprints.

Shared by `scripts/gen-graph-join.py` (writes `artifacts/graph-join/join.json`
and `dashboard.md`) and `scripts/check-graph-join.py` (the gate: recomputes
the join from the same committed inputs and requires a byte-identical
result). Nothing here calls cargo or touches the Lean toolchain -- every
input this module reads is already-committed JSON, matching
`check-declaration-graph.py`'s own "needs no Lean toolchain" posture.

# The identity rule this whole module exists to enforce

CLAUDE.md / ADR-0716: "If Mathlib's `def` is the same function, the mirror is
our statement. If our definitional BODY is Mathlib's THEOREM about a
structurally different `def`, the mirror is a different proposition." A bare
string match between a Mathlib declaration name and an Axeyum kernel
declaration name is NEVER, by itself, treated as identity anywhere in this
module. Every `fact_id` and `kernel_declaration` resolution goes through an
EXISTING, human-authored ledger fact whose own evidence already compared a
rendered kernel type against the Mathlib statement (the `F:ml430-*` mirror
family) -- this module reuses that prior work, it does not re-derive
identity from names.

Two things follow, both checked structurally, not by convention:

  - `resolve_fact_ids` matches on a fact's `title` field, which is prose
    ("Mathlib v4.30 source proposition X"), never on the fact's `id` slug
    (an id like `F:ml430-nat-add-comm-56a2d614` embeds a hash suffix
    specifically so it CANNOT be reverse-derived from a bare name).
  - `name_coincidence_candidates` computes, as an explicit DIAGNOSTIC, which
    unresolved declaration names merely happen to share a string with some
    OTHER fact's extracted kernel subject somewhere else in the ledger, and
    labels every one of them unresolved with a reason saying so. This is the
    demonstration that name similarity was considered and rejected as a
    basis, not silently avoided by never looking.
"""

from __future__ import annotations

import glob
import importlib.util
import json
import pathlib
import re
from dataclasses import dataclass, field
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[2]
DECL_GRAPH_DIR = ROOT / "artifacts/declaration-graph/graph"
DECL_POP_DIR = ROOT / "artifacts/declaration-graph/populations"
FACTS_DIR = ROOT / "artifacts/facts"
TRUST_CLOSURE_DIR = ROOT / "artifacts/trust-closure"
AUTOGENESIS_DIR = ROOT / "artifacts/autogenesis"
ONTOLOGY_DIR = ROOT / "artifacts/ontology"

DEFAULT_POPULATION_ID = "mathlib-group-defs-v1"

MIRROR_TITLE_TEMPLATE = "Mathlib v4.30 source proposition {name}"

SETTLED = {"proved", "computed"}
KERNEL_ROUTES = {"kernel-lean"}

# CLAUDE.md's own measured, exhaustive account of this kernel's trusted
# inductive surface: "The complete inductive list is True/False/And/Or/Iff/
# Eq/Exists/Acc/Bool/Nat/Decidable + Nat.le + Nat.Fin + Char (plus
# Nat.Pair, added by that lane)." Only the TOP-LEVEL roots are usable here
# (a declaration-graph name's root is everything before its first `.`), so
# `Nat.le`, `Nat.Fin` and `Nat.Pair` collapse into the `Nat` root and are not
# listed separately below -- a Mathlib root of `Fin` (Lean/Mathlib's own
# standalone `Fin n` type, NOT `Nat.Fin`) is DELIBERATELY absent: it is a
# different construction from ours and an exact-root match must not paper
# over that, which is the same "no name similarity creates an identity"
# discipline applied one level down, to vocabulary rather than propositions.
KERNEL_CARRIER_ROOTS: frozenset[str] = frozenset(
    {"True", "False", "And", "Or", "Iff", "Eq", "Exists", "Acc", "Bool", "Nat", "Decidable", "Char"}
)


def load_json(path: pathlib.Path) -> Any:
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


def load_population(population_id: str, population_dir: pathlib.Path = DECL_POP_DIR) -> dict:
    return load_json(population_dir / f"{population_id}.json")


def load_rows(population_id: str, graph_dir: pathlib.Path = DECL_GRAPH_DIR) -> dict:
    return load_json(graph_dir / f"{population_id}.rows.json")


def declaration_names(rows: dict) -> list[str]:
    return sorted(d["name"] for d in rows["declarations"])


def declaration_kind_by_name(rows: dict) -> dict[str, str]:
    return {d["name"]: d["kind"] for d in rows["declarations"]}


def load_facts(facts_dir: pathlib.Path = FACTS_DIR) -> dict[str, dict]:
    """`fact id -> fact dict`, over every committed ledger fact."""
    out: dict[str, dict] = {}
    for p in sorted(facts_dir.glob("*.json")):
        data = load_json(p)
        out[data["id"]] = data
    if not out:
        raise ValueError(f"no facts found under {facts_dir} -- empty ledger")
    return out


def title_index(facts_by_id: dict[str, dict]) -> dict[str, list[str]]:
    """`title -> [fact ids]`, so an ambiguous title is visible rather than
    silently picking the first match."""
    idx: dict[str, list[str]] = {}
    for fid, fact in facts_by_id.items():
        idx.setdefault(fact.get("title", ""), []).append(fid)
    return idx


def _load_depends_derived_module() -> Any:
    """Reuse `check-fact-depends-derived.py`'s `theorem_of` extraction --
    the same technique `check-trust-closure.py` uses for the same reason:
    re-deriving the subject-extraction regex here would leave two copies to
    drift apart."""
    path = ROOT / "scripts/check-fact-depends-derived.py"
    spec = importlib.util.spec_from_file_location("_axeyum_depends_derived_gj", path)
    if spec is None or spec.loader is None:  # pragma: no cover - import plumbing
        raise RuntimeError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@dataclass
class DimensionResult:
    population: list[str]
    resolved: dict[str, dict] = field(default_factory=dict)
    unresolved: dict[str, dict] = field(default_factory=dict)
    population_source: str = "declaration-graph"

    def to_json(self) -> dict:
        assert set(self.resolved) | set(self.unresolved) == set(self.population), (
            "accounting violated: every population member must be either resolved or "
            "unresolved, exactly once"
        )
        assert not (set(self.resolved) & set(self.unresolved)), (
            "accounting violated: a member cannot be both resolved and unresolved"
        )
        return {
            "population_source": self.population_source,
            "population_count": len(self.population),
            "resolved_count": len(self.resolved),
            "unresolved_count": len(self.unresolved),
            "resolved": dict(sorted(self.resolved.items())),
            "unresolved": dict(sorted(self.unresolved.items())),
        }


def resolve_fact_ids(names: list[str], facts_by_id: dict[str, dict]) -> DimensionResult:
    """Dimension 1: Mathlib declaration name -> ledger fact id.

    Basis: an EXACT match on the fact's `title` field against the mirror
    template. Never the fact's `id` (a hash-suffixed slug, unrelated to the
    declaration name by construction) and never a fuzzy/substring match.
    """
    idx = title_index(facts_by_id)
    result = DimensionResult(population=names, population_source="declaration-graph")
    for name in names:
        key = MIRROR_TITLE_TEMPLATE.format(name=name)
        matches = idx.get(key, [])
        if len(matches) == 1:
            result.resolved[name] = {
                "fact_id": matches[0],
                "basis": "ml430-mirror-title-exact",
            }
        elif len(matches) == 0:
            result.unresolved[name] = {"reason": "no-mirror-fact"}
        else:
            result.unresolved[name] = {
                "reason": "ambiguous-mirror-title",
                "candidates": sorted(matches),
            }
    return result


def resolve_kernel_declarations(
    fact_ids: DimensionResult, facts_by_id: dict[str, dict], depends_derived: Any
) -> DimensionResult:
    """Dimension 2: ledger fact (from dimension 1) -> kernel declaration name.

    Population is dimension 1's RESOLVED set, stated explicitly rather than
    the full 446-declaration population, because this dimension cannot even
    be asked about a name with no fact behind it.
    """
    names = sorted(fact_ids.resolved)
    result = DimensionResult(population=names, population_source="fact_ids.resolved")
    for name in names:
        fid = fact_ids.resolved[name]["fact_id"]
        fact = facts_by_id[fid]
        status = fact.get("epistemic_status")
        route = fact.get("proof_route")
        if status not in SETTLED:
            result.unresolved[name] = {"fact_id": fid, "reason": f"fact-not-settled:{status}"}
            continue
        if route not in KERNEL_ROUTES:
            result.unresolved[name] = {"fact_id": fid, "reason": f"non-kernel-route:{route}"}
            continue
        subject = depends_derived.theorem_of(fact)
        if subject is None:
            result.unresolved[name] = {"fact_id": fid, "reason": "no-kernel-subject-extracted"}
            continue
        explicit = "kernel_theorem" in (fact.get("formal") or {})
        result.resolved[name] = {
            "fact_id": fid,
            "kernel_theorem": subject,
            "basis": "kernel_theorem-field-explicit" if explicit else "checker-command-regex-fallback",
        }
    return result


def global_kernel_subject_index(facts_by_id: dict[str, dict], depends_derived: Any) -> dict[str, list[str]]:
    """`kernel subject name -> [fact ids]`, over EVERY settled kernel-lean
    fact in the whole ledger (not just the ones this join already resolved).
    Used only by `name_coincidence_candidates` -- a diagnostic, never a
    resolution path."""
    idx: dict[str, list[str]] = {}
    for fid, fact in facts_by_id.items():
        if fact.get("epistemic_status") not in SETTLED:
            continue
        if fact.get("proof_route") not in KERNEL_ROUTES:
            continue
        subject = depends_derived.theorem_of(fact)
        if subject:
            idx.setdefault(subject, []).append(fid)
    return idx


def name_coincidence_candidates(
    all_names: list[str],
    fact_id_resolved_names: set[str],
    facts_by_id: dict[str, dict],
    depends_derived: Any,
) -> dict[str, dict]:
    """Declaration names with NO mirror fact (dimension 1 unresolved) whose
    bare string nonetheless equals some OTHER fact's extracted kernel
    subject elsewhere in the ledger.

    Every entry here stays unresolved. This function exists to make the
    prevention visible: it shows the coincidences were found and rejected as
    a basis for identity, not that nobody looked.
    """
    subject_idx = global_kernel_subject_index(facts_by_id, depends_derived)
    out: dict[str, dict] = {}
    for name in all_names:
        if name in fact_id_resolved_names:
            continue
        hits = subject_idx.get(name)
        if hits:
            out[name] = {
                "coincident_fact_ids": sorted(hits),
                "note": (
                    "name coincides with an existing kernel declaration named in an "
                    "UNRELATED fact's evidence; no mirror fact links this Mathlib "
                    "declaration to that fact, so NO identity is asserted here"
                ),
            }
    return out


def resolve_vocabulary(names: list[str]) -> DimensionResult:
    """Dimension 3: does Axeyum's kernel have a carrier/type-former by this
    declaration's own top-level name at all?

    This is deliberately coarser than dimension 2 (propositional identity):
    it asks only whether the ROOT symbol (the part of the name before the
    first `.`) exact-matches one of the kernel's own enumerated inductive
    types (`KERNEL_CARRIER_ROOTS`, sourced from CLAUDE.md's measured
    account). It says nothing about whether any particular theorem about
    that carrier is proved -- only whether the vocabulary to STATE something
    about it exists.
    """
    result = DimensionResult(population=names, population_source="declaration-graph")
    for name in names:
        root = name.split(".", 1)[0]
        if root in KERNEL_CARRIER_ROOTS:
            result.resolved[name] = {"root": root, "basis": "kernel-inductive-type-name-exact-match"}
        else:
            reason = "root-not-in-kernel-inductive-type-list"
            note = None
            if root == "Fin":
                note = (
                    "Mathlib's standalone Fin n is a different construction from "
                    "Axeyum's Nat.Fin; deliberately NOT matched"
                )
            entry = {"root": root, "reason": reason}
            if note:
                entry["note"] = note
            result.unresolved[name] = entry
    return result


def load_foundational_concepts(ontology_dir: pathlib.Path = ONTOLOGY_DIR) -> list[dict]:
    data = load_json(ontology_dir / "foundational-concepts.json")
    return data.get("rows", [])


def resolve_destination(population_id: str, concept_rows: list[dict]) -> DimensionResult:
    """Dimension 4: declaration-graph POPULATION (not per-declaration -- the
    curriculum ledger has no per-declaration granularity) -> a curriculum
    destination node.

    Basis: the population id and its requested-root modules both name
    `Mathlib.Algebra.Group.Defs`; the candidate curriculum row is found by
    requiring `curriculum_family == "Algebra"` AND the word "group" in its
    own `curriculum_node`/`title`, read from the row's own content (its
    summary literally says "Closure/associativity/identity/inverse"), not
    inferred from the population name alone.
    """
    result = DimensionResult(population=[population_id], population_source="declaration-graph-populations")
    candidates = [
        r
        for r in concept_rows
        if r.get("curriculum_family") == "Algebra"
        and "group" in ((r.get("curriculum_node") or "") + " " + (r.get("title") or "")).lower()
    ]
    if "group" not in population_id.lower():
        result.unresolved[population_id] = {"reason": "population-id-does-not-name-a-group-destination"}
    elif len(candidates) == 1:
        row = candidates[0]
        proof_routes = row.get("proof_routes") or []
        lean_status = proof_routes[0].get("lean_status") if proof_routes else None
        result.resolved[population_id] = {
            "destination_id": row["id"],
            "curriculum_node": row.get("curriculum_node"),
            "curriculum_status": row.get("curriculum_status"),
            "lean_status": lean_status,
            "basis": "population-id-and-module-name-match-curriculum-row-content",
        }
    elif len(candidates) == 0:
        result.unresolved[population_id] = {"reason": "no-matching-curriculum-row"}
    else:
        result.unresolved[population_id] = {
            "reason": "ambiguous-curriculum-row",
            "candidates": sorted(r["id"] for r in candidates),
        }
    return result


def load_decline_records(autogenesis_dir: pathlib.Path = AUTOGENESIS_DIR) -> list[tuple[str, str]]:
    """`[(path, fact_id), ...]` for every `*decline*.json` carrying a
    `fact_id` field."""
    out: list[tuple[str, str]] = []
    for p in sorted(glob.glob(str(autogenesis_dir / "*decline*.json"))):
        data = load_json(pathlib.Path(p))
        fid = data.get("fact_id")
        if fid:
            out.append((str(pathlib.Path(p).relative_to(ROOT)), fid))
    return out


def load_operations(autogenesis_dir: pathlib.Path = AUTOGENESIS_DIR) -> list[dict]:
    path = autogenesis_dir / "operations.json"
    if not path.exists():
        return []
    return load_json(path).get("operations", [])


def resolve_producers(fact_ids: list[str], operations: list[dict]) -> DimensionResult:
    """Dimension 5: ledger fact id (from dimension 1's resolved set) ->
    registered producer operation(s), via `applicability.fact_ids` -- the
    same field `scripts/gen-production-provenance-ledger.py` reads, never a
    label a fact carries about itself."""
    result = DimensionResult(population=fact_ids, population_source="fact_ids.resolved")
    fid_to_ops: dict[str, list[str]] = {}
    for op in operations:
        for fid in op.get("applicability", {}).get("fact_ids", []):
            fid_to_ops.setdefault(fid, []).append(op["id"])
    for fid in fact_ids:
        ops = fid_to_ops.get(fid)
        if ops:
            result.resolved[fid] = {"operation_ids": sorted(ops)}
        else:
            result.unresolved[fid] = {"reason": "no-registered-operation-names-this-fact"}
    return result


def resolve_declines(fact_ids: list[str], decline_records: list[tuple[str, str]]) -> DimensionResult:
    """Dimension 6: ledger fact id -> a recorded decline (a producer that
    was TRIED and refused, e.g. `import-blocked-trusted-declaration`)."""
    result = DimensionResult(population=fact_ids, population_source="fact_ids.resolved")
    fid_to_paths: dict[str, list[str]] = {}
    for path, fid in decline_records:
        fid_to_paths.setdefault(fid, []).append(path)
    for fid in fact_ids:
        paths = fid_to_paths.get(fid)
        if paths:
            result.resolved[fid] = {"decline_paths": sorted(paths)}
        else:
            result.unresolved[fid] = {"reason": "no-recorded-decline-names-this-fact"}
    return result


def load_identity_map_names(trust_closure_dir: pathlib.Path = TRUST_CLOSURE_DIR) -> set[str]:
    """Kernel theorem names appearing in ANY S2 identity class
    (`artifacts/trust-closure/identity-map.tsv`) -- reused verbatim, never
    recomputed, per the task's instruction not to build a second
    duplicate-detection mechanism."""
    path = trust_closure_dir / "identity-map.tsv"
    names: set[str] = set()
    if not path.exists():
        return names
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        for member in parts[1].split(","):
            member = member.strip()
            if member:
                names.add(member)
    return names


def resolve_trust_footprints(
    kernel_decls: DimensionResult, facts_by_id: dict[str, dict], identity_names: set[str]
) -> DimensionResult:
    """Dimension 7: kernel declaration (from dimension 2) -> trust
    footprint, read directly from the fact's own committed `axiom_footprint`
    field (never re-derived by calling the kernel), plus whether that
    theorem participates in an S2 duplicate-identity class.
    """
    names = sorted(kernel_decls.resolved)
    result = DimensionResult(population=names, population_source="kernel_declarations.resolved")
    for name in names:
        entry = kernel_decls.resolved[name]
        fid = entry["fact_id"]
        fact = facts_by_id[fid]
        footprint = fact.get("axiom_footprint")
        if footprint is None:
            result.unresolved[name] = {"fact_id": fid, "reason": "fact-carries-no-axiom_footprint"}
            continue
        result.resolved[name] = {
            "fact_id": fid,
            "kernel_theorem": entry["kernel_theorem"],
            "axiom_footprint": sorted(footprint),
            "in_identity_class": entry["kernel_theorem"] in identity_names,
        }
    return result


def compute_join(population_id: str = DEFAULT_POPULATION_ID) -> dict:
    """The whole G2 join, over every committed input. Deterministic: no
    timestamps, no host-dependent data, so two runs on the same tree produce
    byte-identical JSON (the property `check-graph-join.py` enforces)."""
    population = load_population(population_id)
    rows = load_rows(population_id)
    names = declaration_names(rows)
    if not names:
        raise ValueError(f"declaration graph population {population_id!r} is EMPTY")

    facts_by_id = load_facts()
    depends_derived = _load_depends_derived_module()

    fact_ids = resolve_fact_ids(names, facts_by_id)
    kernel_decls = resolve_kernel_declarations(fact_ids, facts_by_id, depends_derived)
    vocabulary = resolve_vocabulary(names)
    concept_rows = load_foundational_concepts()
    destination = resolve_destination(population_id, concept_rows)

    resolved_fact_id_list = sorted(v["fact_id"] for v in fact_ids.resolved.values())
    operations = load_operations()
    producers = resolve_producers(resolved_fact_id_list, operations)
    decline_records = load_decline_records()
    declines = resolve_declines(resolved_fact_id_list, decline_records)

    identity_names = load_identity_map_names()
    trust = resolve_trust_footprints(kernel_decls, facts_by_id, identity_names)

    coincidences = name_coincidence_candidates(
        names, set(fact_ids.resolved), facts_by_id, depends_derived
    )

    return {
        "schema_version": 1,
        "kind": "axeyum-graph-join",
        "generated_by": "scripts/gen-graph-join.py",
        "population_id": population_id,
        "population_authority": f"artifacts/declaration-graph/populations/{population_id}.json",
        "expected_roots": sorted(population.get("expected_roots", [])),
        "declaration_population_count": len(names),
        "dimensions": {
            "fact_ids": fact_ids.to_json(),
            "kernel_declarations": kernel_decls.to_json(),
            "statement_vocabulary": vocabulary.to_json(),
            "destination_nodes": destination.to_json(),
            "producers": producers.to_json(),
            "declines": declines.to_json(),
            "trust_footprints": trust.to_json(),
        },
        "name_coincidence_candidates": dict(sorted(coincidences.items())),
        "notes": {
            "bounded": (
                f"This join covers exactly the {len(names)} declarations of population "
                f"{population_id!r} (7 real roots, ADR-0820); it says nothing about "
                "Mathlib declarations outside this bounded extraction."
            ),
            "adr_0790_limit_inherited": (
                "fact_ids/kernel_declarations resolution depends transitively on the "
                "ml430 mirror facts' own evidence, not on check-proposition-duplication.py "
                "(ADR-0790) directly -- this join does not call that script. Where this "
                "join DOES reuse ADR-0790/S2 machinery (trust_footprints.in_identity_class, "
                "via artifacts/trust-closure/identity-map.tsv) it inherits that "
                "computation's own stated limit verbatim: identity classes are found only "
                "by BYTE-IDENTICAL Kernel::render_lean canonical types, so a duplicate "
                "proposition rendered even slightly differently (e.g. a reordered "
                "hypothesis) would not be detected by that layer, and this join does not "
                "attempt to detect it either."
            ),
            "no_name_similarity_creates_identity": (
                "fact_ids and kernel_declarations are resolved ONLY through an existing "
                "ledger fact's own title/evidence (see module docstring); "
                "name_coincidence_candidates records every case where a bare string match "
                "existed and was NOT treated as identity, so the prevention is visible "
                "rather than assumed."
            ),
        },
    }
