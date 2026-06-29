#!/usr/bin/env python3
"""Generate the seed Foundational Concept Atlas from the math curriculum.

The committed JSON is intentionally generated from two sources of truth:
the formal math curriculum DAG and the field/resource mapping in the buildout
plan. Keep this script deterministic so diffs show semantic changes only.
"""

from __future__ import annotations

import json
import re
import tomllib
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
CURRICULUM = ROOT / "docs" / "curriculum" / "curriculum.toml"
MATH_FIELDS = ROOT / "docs" / "foundational-resources" / "MATH-FIELDS.md"
OUT = ROOT / "artifacts" / "ontology" / "foundational-concepts.json"

AREA_DIR = {
    (0, "foundations"): "docs/curriculum/00-foundations",
    (1, "number-systems"): "docs/curriculum/01-number-systems",
    (2, "structures"): "docs/curriculum/02-structures",
    (3, "destinations"): "docs/curriculum/03-destinations",
}

CURRICULUM_MAP = {
    "propositional-logic": {
        "field_ids": ["logic_and_proof"],
        "pack": "logic-basics-v0",
        "slice": "SAT/UNSAT Boolean formulas, truth tables, and CNF refutations.",
        "proof": "SAT model replay and CNF refutation evidence.",
    },
    "predicate-logic": {
        "field_ids": ["logic_and_proof", "set_theory_and_foundations"],
        "pack": "finite-predicate-v0",
        "slice": "Finite-domain quantifier expansion and counterexamples.",
        "proof": "Finite expansion replay with proof gap for general first-order logic.",
    },
    "proof-methods": {
        "field_ids": ["logic_and_proof"],
        "pack": "proof-methods-refutation-v0",
        "slice": "Negate-and-decide examples; proof by contradiction as UNSAT.",
        "proof": "Finite CNF enumeration now; LRAT/DRAT proof-object graduation remains.",
        "extra_packs": [
            (
                "proof-methods-patterns-v0",
                "Finite direct proof, contrapositive, proof-by-cases, contradiction, and invalid-converse checks.",
            ),
        ],
    },
    "induction": {
        "field_ids": ["logic_and_proof", "number_theory"],
        "pack": "induction-obligations-v0",
        "slice": "Bounded base/step obligations; general induction remains Lean-horizon.",
        "proof": "Bounded obligation replay now; induction schema requires Lean.",
        "extra_packs": [
            (
                "induction-patterns-v0",
                "Finite weak induction, strong induction, loop-invariant replay, and bad-step counterexamples.",
            ),
        ],
    },
    "sets": {
        "field_ids": ["set_theory_and_foundations"],
        "pack": "finite-sets-v0",
        "slice": "Membership, subset, union/intersection, and finite identities.",
        "proof": "Finite enumeration replay and SAT evidence for refutations.",
    },
    "relations-and-functions": {
        "field_ids": ["set_theory_and_foundations", "discrete_math"],
        "pack": "relations-functions-v0",
        "slice": "Finite relation properties, injective/surjective checks, and EUF slices.",
        "proof": "Finite replay plus EUF/Alethe route for equality-heavy examples.",
        "extra_packs": [
            (
                "equivalence-classes-v0",
                "Finite equivalence classes, quotient-map fibers, partition round trips, and explicit QF_UF/Alethe proof gaps.",
            ),
        ],
    },
    "cardinality": {
        "field_ids": ["set_theory_and_foundations", "discrete_math"],
        "pack": "finite-cardinality-v0",
        "slice": "Finite bijections/counting; infinite cardinality is proof-horizon.",
        "proof": "Finite witness replay now; infinite cardinality requires Lean.",
        "extra_packs": [
            (
                "cardinality-principles-v0",
                "Finite inclusion-exclusion, disjoint unions, double counting, powersets, and infinite-cardinality Lean horizon.",
            ),
        ],
    },
    "naturals": {
        "field_ids": ["number_theory", "discrete_math"],
        "pack": "natural-arithmetic-v0",
        "slice": "Bounded Peano arithmetic and LIA/BV arithmetic identities.",
        "proof": "LIA/BV replay and certificate routes for bounded obligations.",
    },
    "integers": {
        "field_ids": ["number_theory"],
        "pack": "integer-lia-v0",
        "slice": "Linear integer equations/inequalities and witnesses.",
        "proof": "LIA witness replay and future Diophantine/Farkas-style evidence.",
    },
    "rationals": {
        "field_ids": ["real_analysis", "linear_algebra"],
        "pack": "rationals-lra-v0",
        "slice": "Exact rational order/field facts, density, trichotomy, and Farkas links.",
        "proof": "Exact rational LRA with Farkas certificates where available.",
    },
    "reals": {
        "field_ids": ["real_analysis", "optimization_and_convexity"],
        "pack": "reals-rcf-shadow-v0",
        "slice": "Algebraic real constraints through LRA/NRA; completeness remains horizon.",
        "proof": "LRA/NRA replay and future SOS/RCF certificates.",
    },
    "complex": {
        "field_ids": ["complex_analysis", "linear_algebra"],
        "pack": "complex-algebraic-v0",
        "slice": "Complex arithmetic as real-pair algebraic constraints.",
        "proof": "Real-pair algebra replay; analytic complex analysis requires Lean.",
    },
    "divisibility-and-euclid": {
        "field_ids": ["number_theory"],
        "pack": "gcd-bezout-v0",
        "slice": "GCD, Bezout witness replay, and divisibility checks.",
        "proof": "Compute-and-check replay of gcd and Bezout witnesses.",
    },
    "modular-arithmetic": {
        "field_ids": ["number_theory", "abstract_algebra"],
        "pack": "modular-arithmetic-v0",
        "slice": "Congruences, inverses, CRT, and fixed-modulus enumeration.",
        "proof": "BV/LIA replay and finite exhaustive checks.",
    },
    "groups": {
        "field_ids": ["abstract_algebra"],
        "pack": "finite-groups-v0",
        "slice": "Cayley-table closure, identity, inverse, and associativity checks.",
        "proof": "Finite table replay; general group theory is Lean-horizon.",
    },
    "rings": {
        "field_ids": ["abstract_algebra"],
        "pack": "finite-rings-v0",
        "slice": "Two-operation table checks and distributivity.",
        "proof": "Finite table replay; structure theory is Lean-horizon.",
    },
    "fields": {
        "field_ids": ["abstract_algebra", "number_theory"],
        "pack": "finite-fields-v0",
        "slice": "Field axioms over small prime fields and composite-modulus counterexamples.",
        "proof": "Finite table replay and BV enumeration.",
    },
    "polynomials": {
        "field_ids": ["abstract_algebra", "real_analysis", "complex_analysis"],
        "pack": "polynomial-identities-v0",
        "slice": "Fixed-degree identities, factor theorem, and root witness replay.",
        "proof": "Fixed-degree algebra replay; broad polynomial theory remains partial.",
    },
    "sequences-and-limits": {
        "field_ids": ["real_analysis", "topology"],
        "pack": "sequence-limit-shadow-v0",
        "slice": "Bounded epsilon/N templates and algebraic sequence checks.",
        "proof": "Bounded arithmetic replay; general limits require Lean.",
    },
    "counting": {
        "field_ids": ["discrete_math", "probability_theory"],
        "pack": "counting-v0",
        "slice": "Permutations, combinations, and pigeonhole finite instances.",
        "proof": "Finite enumeration, SAT refutation, and LRAT gap tracking.",
    },
    "number-theory": {
        "field_ids": ["number_theory"],
        "pack": "number-theory-v0",
        "slice": "CRT, quadratic residues, sum of squares, and bounded Diophantine checks.",
        "proof": "BV/LIA replay plus future bounded arithmetic proof recipes.",
    },
    "linear-algebra": {
        "field_ids": ["linear_algebra", "numerical_analysis", "optimization_and_convexity"],
        "pack": "linear-algebra-rational-v0",
        "slice": "Fixed rational matrices, LU replay, inverse checks, and inconsistent systems.",
        "proof": "Exact replay plus Farkas certificates for infeasible LRA systems.",
    },
    "calculus": {
        "field_ids": ["real_analysis", "differential_equations_and_dynamical_systems", "numerical_analysis"],
        "pack": "calculus-algebraic-shadow-v0",
        "slice": "Polynomial derivative identities and algebraic inequalities.",
        "proof": "Algebraic LRA/NRA replay; epsilon-delta and integration require Lean.",
        "extra_packs": [
            (
                "calculus-riemann-sum-v0",
                "Finite rational Riemann sums, midpoint/trapezoid replay, antiderivative endpoints, and FTC Lean horizon.",
            ),
        ],
    },
}

FIELD_PACKS = {
    "logic_and_proof": ("proof-methods-refutation-v0", "Negation-as-query, finite CNF checks, and proof-object lessons."),
    "set_theory_and_foundations": ("finite-sets-v0", "Finite set, relation, function, and cardinality checks."),
    "discrete_math": ("counting-v0", "Finite counting and combinatorial witness checks."),
    "graph_theory": ("graph-coloring-v0", "SAT colorings, non-colorability, reachability, search cost counters, matching, cuts, and d-separation."),
    "number_theory": ("modular-arithmetic-v0", "Congruences, CRT, residues, finite fields, and bounded Diophantine examples."),
    "linear_algebra": ("linear-algebra-rational-v0", "Fixed exact matrices, LU replay, rank, inverse, and infeasibility."),
    "abstract_algebra": ("finite-fields-v0", "Finite groups, rings, fields, homomorphism tables, and Cayley-table validation."),
    "real_analysis": ("real-analysis-rational-v0", "Rational interval/ball checks, bounded epsilon-delta samples, algebraic shadows, and proof horizons."),
    "complex_analysis": ("complex-algebraic-v0", "Complex arithmetic as real-pair algebra before analytic proof horizons."),
    "topology": ("finite-topology-v0", "Finite topologies, metric balls, closure, and interior checks."),
    "measure_theory": ("finite-measure-v0", "Finite sigma-algebras, finite measures, random variables, conditional expectations, finite kernels, martingales, hitting times, concentration checks, product tables, and exact probability foundations."),
    "probability_theory": ("finite-probability-v0", "Finite mass tables, random variables, conditional expectation, kernels, martingales, hitting times, concentration/tail bounds, conditioning, Bayes rule, product measures, and exact discrete distributions."),
    "statistics": ("descriptive-statistics-v0", "Mean/variance identities, random variables, conditional expectation, finite kernel, hitting-time, martingale, and concentration checks, contingency tables, exact tests, and Simpson witnesses."),
    "optimization_and_convexity": [
        ("linear-optimization-v0", "LP feasibility, threshold cliffs, and Farkas-style certificates."),
        ("convexity-rational-v0", "Finite midpoint convexity, second differences, affine threshold monotonicity, and bad midpoint-convexity rejection."),
    ],
    "numerical_analysis": ("numerical-linear-algebra-v0", "LU replay, interval bounds, fixed-step error recurrences, and rational shadows."),
    "differential_equations_and_dynamical_systems": ("bounded-dynamics-v0", "Recurrence systems, discretized dynamics, invariant checks, Markov transitions, and finite hitting times."),
    "geometry": ("coordinate-geometry-v0", "Incidence, distance, midpoint, collinearity, and rigid finite configurations."),
    "functional_analysis_and_operator_theory": ("finite-operator-v0", "Finite-dimensional norms, operator matrices, Chebyshev polynomial slices, and finite Chebyshev-system grids."),
}

FIELD_DECIDABILITY = {
    "complex_analysis": "proof-horizon",
    "topology": "proof-horizon",
    "measure_theory": "proof-horizon",
    "functional_analysis_and_operator_theory": "proof-horizon",
    "statistics": "numerical",
    "numerical_analysis": "numerical",
}


def snake(value: str) -> str:
    return value.replace("-", "_")


def curriculum_row_id(node_id: str) -> str:
    return f"curriculum_{snake(node_id)}"


def field_row_id(field_id: str) -> str:
    return f"field_{field_id}"


def load_curriculum() -> list[dict[str, Any]]:
    with CURRICULUM.open("rb") as handle:
        data = tomllib.load(handle)
    return data["node"]


def load_math_fields() -> dict[str, dict[str, str]]:
    fields: dict[str, dict[str, str]] = {}
    in_table = False
    for line in MATH_FIELDS.read_text(encoding="utf-8").splitlines():
        if line == "## Field Set":
            in_table = True
            continue
        if line == "## Priority Bands":
            break
        if not in_table or not line.startswith("| `"):
            continue
        parts = [part.strip() for part in line.strip().strip("|").split("|")]
        if len(parts) != 5:
            continue
        field_id = parts[0].strip("`")
        fields[field_id] = {
            "title": parts[1],
            "curriculum_role": parts[2],
            "first_slice": parts[3],
            "proof_horizon": parts[4],
        }
    return fields


def curriculum_doc_path(node: dict[str, Any]) -> str:
    key = (node["layer"], node["area"])
    folder = AREA_DIR[key]
    return f"{folder}/{node['id']}.md"


def concept_decidability(node_decidability: str) -> str:
    if node_decidability == "undecidable":
        return "proof-horizon"
    return node_decidability


def pack_status(pack_id: str) -> str:
    path = ROOT / "artifacts" / "examples" / "math" / pack_id / "metadata.json"
    return "validated" if path.exists() else "planned"


def pack(pack_id: str, notes: str) -> dict[str, str]:
    return {
        "id": pack_id,
        "status": pack_status(pack_id),
        "path": f"artifacts/examples/math/{pack_id}",
        "notes": notes,
    }


def field_pack_specs(field_id: str) -> list[tuple[str, str]]:
    value = FIELD_PACKS[field_id]
    if isinstance(value, tuple):
        return [value]
    return value


def curriculum_pack_specs(mapping: dict[str, Any]) -> list[tuple[str, str]]:
    return [(mapping["pack"], mapping["slice"])] + mapping.get("extra_packs", [])


def proof_route(name: str, status: str, checker: str, lean_status: str, notes: str) -> dict[str, Any]:
    return {
        "name": name,
        "status": status,
        "checker": checker,
        "lean_status": lean_status,
        "sources": [
            "docs/proof-cookbook/README.md",
            "docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md",
        ],
        "notes": notes,
    }


def make_curriculum_row(node: dict[str, Any], node_by_id: dict[str, dict[str, Any]]) -> dict[str, Any]:
    mapping = CURRICULUM_MAP[node["id"]]
    pack_specs = curriculum_pack_specs(mapping)
    row_id = curriculum_row_id(node["id"])
    decidability = concept_decidability(node["decidability"])
    lean_required = node["status"] == "lean-horizon" or decidability == "proof-horizon"
    status = "proof-horizon" if lean_required else "seeded"
    route_status = "lean-horizon" if lean_required else "planned"
    lean_status = "required" if lean_required else "planned"
    doc_path = curriculum_doc_path(node)
    is_pack_validated = any(pack_status(pack_id) == "validated" for pack_id, _ in pack_specs)
    if is_pack_validated:
        gaps = [
            "Validated example pack exists; solver/proof integration still needs promotion where noted.",
            "Generated dashboards now report pack status and replay/proof rows; keep lessons linked to the validated pack.",
        ]
    else:
        gaps = [
            "Dedicated foundational example pack is not yet validated.",
            "Generated dashboards keep this pack planned until a validating example pack lands.",
        ]
    if node["status"] == "covered" and node["family"]:
        gaps.append(
            f"Existing curriculum family {node['family']} still needs migration into example-pack metadata."
        )
    if lean_required:
        gaps.append("General theorem content requires Lean reconstruction or another proof-assistant route.")

    return {
        "id": row_id,
        "kind": "curriculum-node",
        "title": node["title"],
        "domain": "mathematics",
        "field_ids": mapping["field_ids"],
        "curriculum_node": node["id"],
        "curriculum_layer": node["layer"],
        "curriculum_area": node["area"],
        "curriculum_status": node["status"],
        "curriculum_family": node["family"],
        "resource_status": status,
        "summary": node["summary"],
        "prerequisites": [curriculum_row_id(item) for item in node["prerequisites"]],
        "unlocks": [curriculum_row_id(item) for item in node["unlocks"] if item in node_by_id],
        "decidability": decidability,
        "axeyum_fragments": [node["axeyum_theory"]],
        "example_packs": [pack(pack_id, pack_notes) for pack_id, pack_notes in pack_specs],
        "proof_routes": [
            proof_route(
                mapping["proof"],
                route_status,
                "planned foundational example-pack validator",
                lean_status,
                mapping["slice"],
            )
        ],
        "source_refs": [
            "docs/curriculum/curriculum.toml",
            doc_path,
            "docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md",
        ],
        "open_gaps": gaps,
        "graduation": {
            "status": "planned",
            "criteria": [
                (
                    "Create and validate planned curriculum example packs, starting with "
                    f"artifacts/examples/math/{mapping['pack']}."
                    if len(pack_specs) > 1
                    else f"Create and validate artifacts/examples/math/{mapping['pack']}."
                ),
                "Replay SAT witnesses against the original mathematical claim.",
                "Name checked evidence for each UNSAT claim or keep the proof gap explicit.",
            ],
        },
    }


def make_field_row(field_id: str, field: dict[str, str], curriculum_rows: list[dict[str, Any]]) -> dict[str, Any]:
    pack_specs = field_pack_specs(field_id)
    primary_pack_id = pack_specs[0][0]
    has_multiple_packs = len(pack_specs) > 1
    unlocks = sorted(row["id"] for row in curriculum_rows if field_id in row["field_ids"])
    decidability = FIELD_DECIDABILITY.get(field_id, "bounded")
    route_status = "lean-horizon" if decidability == "proof-horizon" else "planned"
    lean_status = "required" if decidability == "proof-horizon" else "planned"
    validated_count = sum(1 for pack_id, _ in pack_specs if pack_status(pack_id) == "validated")
    if validated_count:
        pack_gap = (
            "Field-level example pack coverage has begun; broader field concept coverage remains incomplete."
            if has_multiple_packs
            else "Field-level example pack exists; broader field concept coverage remains incomplete."
        )
        gaps = [
            pack_gap,
            "Field status still needs repeated slices and proof/evidence coverage before graduation.",
        ]
    else:
        gaps = [
            "Field row is seeded, but field-level example-pack coverage is not validated yet.",
            "Generated dashboards keep this field at seeded/planned coverage until its first pack lands.",
        ]
    if decidability == "proof-horizon":
        gaps.append("Most general field theorems require Lean/mathlib-scale proof reconstruction.")
    return {
        "id": field_row_id(field_id),
        "kind": "field",
        "title": field["title"],
        "domain": "mathematics",
        "field_ids": [field_id],
        "curriculum_node": None,
        "curriculum_layer": None,
        "curriculum_area": None,
        "curriculum_status": "extension",
        "curriculum_family": "",
        "resource_status": "seeded",
        "summary": f"{field['curriculum_role']}. First Axeyum slice: {field['first_slice']}",
        "prerequisites": [],
        "unlocks": unlocks,
        "decidability": decidability,
        "axeyum_fragments": [field["first_slice"]],
        "example_packs": [pack(pack_id, pack_notes) for pack_id, pack_notes in pack_specs],
        "proof_routes": [
            proof_route(
                field["proof_horizon"],
                route_status,
                "planned foundational example-pack validator",
                lean_status,
                "Field-level proof route is a planning row until a concrete example pack validates.",
            )
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md",
        ],
        "open_gaps": gaps,
        "graduation": {
            "status": "planned",
            "criteria": [
                (
                    "Create and validate planned field example packs, starting with "
                    f"artifacts/examples/math/{primary_pack_id}."
                    if has_multiple_packs
                    else f"Create and validate artifacts/examples/math/{primary_pack_id}."
                ),
                "Add at least one concept row or curriculum row that exercises the field.",
                "Generate field-dashboard coverage from committed metadata.",
            ],
        },
    }


def main() -> int:
    nodes = load_curriculum()
    node_by_id = {node["id"]: node for node in nodes}
    fields = load_math_fields()
    curriculum_rows = [make_curriculum_row(node, node_by_id) for node in nodes]
    field_rows = [make_field_row(field_id, fields[field_id], curriculum_rows) for field_id in sorted(fields)]
    atlas = {
        "schema_version": 1,
        "generated_from": [
            "docs/curriculum/curriculum.toml",
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md",
        ],
        "rows": curriculum_rows + field_rows,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    with OUT.open("w", encoding="utf-8") as handle:
        json.dump(atlas, handle, indent=2, sort_keys=False)
        handle.write("\n")
    print(f"generated {len(atlas['rows'])} foundational concept rows")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
