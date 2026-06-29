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
EXAMPLE_ROOT = ROOT / "artifacts" / "examples" / "math"
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
        "extra_packs": [
            (
                "finite-order-lattices-v0",
                "Finite partial orders, lattice meet/join tables, distributivity, monotone maps, and fixed-point replay.",
            ),
        ],
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
            (
                "function-composition-v0",
                "Finite function composition, image/preimage, inverse tables, associativity, and function-law Lean horizon.",
            ),
            (
                "finite-monoids-v0",
                "Finite monoids as closed function-composition tables, with unit and idempotent replay.",
            ),
            (
                "finite-permutation-groups-v0",
                "Finite permutation groups as bijective function-composition tables, with cycle/sign replay and natural actions.",
            ),
            (
                "finite-group-actions-v0",
                "Finite group actions as function tables, orbit/stabilizer replay, and Burnside counting.",
            ),
            (
                "finite-order-lattices-v0",
                "Finite partial orders, meet/join lattice tables, monotone maps, fixed points, and bad-order counterexamples.",
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
            (
                "finite-order-lattices-v0",
                "Finite Boolean lattice over a two-element powerset, meet/join replay, and monotone fixed points.",
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
        "extra_packs": [
            (
                "polynomial-factorization-rational-v0",
                "Exact rational polynomial division, GCD, square-free decomposition, and irreducibility replay.",
            ),
        ],
    },
    "reals": {
        "field_ids": ["real_analysis", "optimization_and_convexity"],
        "pack": "reals-rcf-shadow-v0",
        "slice": "Algebraic real constraints through LRA/NRA; completeness remains horizon.",
        "proof": "LRA/NRA replay and future SOS/RCF certificates.",
        "extra_packs": [
            (
                "multivariable-calculus-rational-v0",
                "Exact rational gradients, directional derivatives, Jacobian chain-rule replay, and Hessian minors.",
            ),
        ],
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
        "extra_packs": [
            (
                "finite-ideals-v0",
                "Finite ideals in modular rings, principal ideal closure, quotient rings, and ring-homomorphism kernels.",
            ),
        ],
    },
    "groups": {
        "field_ids": ["abstract_algebra"],
        "pack": "finite-groups-v0",
        "slice": "Cayley-table closure, identity, inverse, and associativity checks.",
        "proof": "Finite table replay; general group theory is Lean-horizon.",
        "extra_packs": [
            (
                "finite-algebra-homomorphisms-v0",
                "Finite group homomorphism tables, kernel/image replay, quotient maps, and first-isomorphism shadows.",
            ),
            (
                "finite-monoids-v0",
                "Finite monoid tables, transformation composition replay, units, idempotents, and bad-table rejection.",
            ),
            (
                "finite-permutation-groups-v0",
                "Finite permutation groups, S3 composition replay, cycle/sign checks, and natural action orbit-stabilizer replay.",
            ),
            (
                "finite-group-actions-v0",
                "Finite group actions, orbit/stabilizer replay, and Burnside counting over table actions.",
            ),
            (
                "finite-vector-spaces-v0",
                "Finite vector-space tables, subspaces, spans, linear maps, kernels, images, and rank-nullity replay.",
            ),
            (
                "finite-dual-spaces-v0",
                "Finite dual-space covectors, dual-basis pairings, annihilators, transpose maps, and bad-covector rejection.",
            ),
            (
                "finite-modules-v0",
                "Finite module tables over rings, submodules, generated submodules, homomorphisms, kernels, images, and quotient modules.",
            ),
            (
                "finite-tensor-products-v0",
                "Finite tensor-product basis replay, bilinear maps, universal-factorization shadows, and Kronecker products.",
            ),
        ],
    },
    "rings": {
        "field_ids": ["abstract_algebra"],
        "pack": "finite-rings-v0",
        "slice": "Two-operation table checks and distributivity.",
        "proof": "Finite table replay; structure theory is Lean-horizon.",
        "extra_packs": [
            (
                "finite-algebra-homomorphisms-v0",
                "Finite ring homomorphism tables and quotient-map replay.",
            ),
            (
                "finite-modules-v0",
                "Finite module tables over Z/4Z, submodule span replay, homomorphisms, kernels, images, and quotient modules.",
            ),
            (
                "finite-ideals-v0",
                "Finite ideals in Z/6Z, principal ideal generation, quotient rings, and ring-homomorphism kernel/image replay.",
            ),
        ],
    },
    "fields": {
        "field_ids": ["abstract_algebra", "number_theory"],
        "pack": "finite-fields-v0",
        "slice": "Field axioms over small prime fields and composite-modulus counterexamples.",
        "proof": "Finite table replay and BV enumeration.",
        "extra_packs": [
            (
                "finite-vector-spaces-v0",
                "Finite vector-space tables over F2, subspaces, spans, and linear maps.",
            ),
            (
                "finite-dual-spaces-v0",
                "Finite dual spaces over F2, covector linearity, dual bases, annihilators, and transpose maps.",
            ),
            (
                "finite-tensor-products-v0",
                "Finite vector-space tensor products over F2, bilinear maps, and Kronecker-product replay.",
            ),
            (
                "polynomial-factorization-rational-v0",
                "Exact rational polynomial factorization, Euclidean GCD, and square-free replay over Q[x].",
            ),
        ],
    },
    "polynomials": {
        "field_ids": ["abstract_algebra", "real_analysis", "complex_analysis"],
        "pack": "polynomial-identities-v0",
        "slice": "Fixed-degree identities, factor theorem, and root witness replay.",
        "proof": "Fixed-degree algebra replay; broad polynomial theory remains partial.",
        "extra_packs": [
            (
                "polynomial-factorization-rational-v0",
                "Exact rational factor products, polynomial division, Euclidean GCD, square-free decomposition, and irreducible-quadratic rejection.",
            ),
            (
                "generating-functions-v0",
                "Finite coefficient extraction, Cauchy products, and recurrence/generating-function prefixes.",
            ),
        ],
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
        "extra_packs": [
            (
                "finite-permutation-groups-v0",
                "Finite permutations, cycle types, parity/sign replay, and natural action orbit-stabilizer counts.",
            ),
            (
                "finite-group-actions-v0",
                "Burnside fixed-point average and orbit counting for a finite group action.",
            ),
        ],
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
        "extra_packs": [
            (
                "finite-vector-spaces-v0",
                "Finite vector spaces over F2, subspaces, spans, linear maps, kernels, images, and rank-nullity replay.",
            ),
            (
                "finite-dual-spaces-v0",
                "Finite dual spaces over F2, dual-basis pairings, annihilators, transpose maps, and covector counterexamples.",
            ),
            (
                "inner-product-spaces-rational-v0",
                "Exact rational Gram matrices, Cauchy-Schwarz replay, orthogonal projections, and Gram-Schmidt checks.",
            ),
            (
                "finite-modules-v0",
                "Finite Z/4Z-module replay, submodules, homomorphisms, kernels, images, and quotient modules.",
            ),
            (
                "finite-tensor-products-v0",
                "Finite tensor-product basis replay, bilinear maps, universal-factorization shadows, and Kronecker products.",
            ),
            (
                "multivariable-calculus-rational-v0",
                "Exact Jacobian and Hessian matrix replay for fixed polynomial calculus rows.",
            ),
        ],
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
            (
                "multivariable-calculus-rational-v0",
                "Exact rational gradient, directional derivative, Jacobian chain-rule, and Hessian-minor replay.",
            ),
        ],
    },
}

FIELD_PACKS = {
    "logic_and_proof": ("proof-methods-refutation-v0", "Negation-as-query, finite CNF checks, finite order counterexamples, and proof-object lessons."),
    "set_theory_and_foundations": ("finite-sets-v0", "Finite set, relation, function, monoid/function-composition, permutation-group, group-action, order, lattice, and cardinality checks."),
    "discrete_math": ("counting-v0", "Finite counting, finite permutations, finite transformation monoids, group-action orbits, order/lattice, and combinatorial witness checks."),
    "graph_theory": ("graph-coloring-v0", "SAT colorings, non-colorability, reachability, search cost counters, matching, cuts, and d-separation."),
    "number_theory": ("modular-arithmetic-v0", "Congruences, CRT, residues, finite fields, finite ideals in modular rings, and bounded Diophantine examples."),
    "linear_algebra": ("linear-algebra-rational-v0", "Fixed exact matrices, finite vector spaces and modules, dual spaces, inner products, tensor products, LU replay, rank, inverse, Jacobians, Hessians, projections, and infeasibility."),
    "abstract_algebra": ("finite-fields-v0", "Finite groups, permutation groups, monoids, group actions, rings, fields, ideals, modules, dual spaces, tensor products, homomorphism tables, polynomial factorization slices, and Cayley-table validation."),
    "real_analysis": ("real-analysis-rational-v0", "Rational interval/ball checks, bounded epsilon-delta samples, algebraic factorization and multivariable-calculus shadows, and proof horizons."),
    "complex_analysis": ("complex-algebraic-v0", "Complex arithmetic and polynomial factorization shadows as real/rational algebra before analytic proof horizons."),
    "topology": ("finite-topology-v0", "Finite topologies, metric balls, closure/interior, continuous maps, and finite simplicial-homology checks."),
    "measure_theory": ("finite-measure-v0", "Finite sigma-algebras, finite measures, random variables, conditional expectations, finite kernels, martingales, hitting times, concentration checks, product tables, and exact probability foundations."),
    "probability_theory": ("finite-probability-v0", "Finite mass tables, random variables, conditional expectation, kernels, martingales, hitting times, concentration/tail bounds, conditioning, Bayes rule, product measures, and exact discrete distributions."),
    "statistics": ("descriptive-statistics-v0", "Mean/variance identities, random variables, conditional expectation, finite kernel, hitting-time, martingale, and concentration checks, contingency tables, exact tests, and Simpson witnesses."),
    "optimization_and_convexity": [
        ("linear-optimization-v0", "LP feasibility, threshold cliffs, and Farkas-style certificates."),
        ("convexity-rational-v0", "Finite midpoint convexity, second differences, affine threshold monotonicity, and bad midpoint-convexity rejection."),
        ("multivariable-calculus-rational-v0", "Exact gradients, directional derivatives, Hessian minors, and local convexity shadows."),
        ("inner-product-spaces-rational-v0", "Exact rational projections, Gram matrices, and orthogonal residual checks."),
    ],
    "numerical_analysis": ("numerical-linear-algebra-v0", "LU replay, interval bounds, inner-product projections, fixed-step error recurrences, Jacobian/Hessian replay, and rational shadows."),
    "differential_equations_and_dynamical_systems": ("bounded-dynamics-v0", "Recurrence systems, discretized dynamics, invariant checks, Markov transitions, and finite hitting times."),
    "geometry": ("coordinate-geometry-v0", "Incidence, distance, midpoint, collinearity, and rigid finite configurations."),
    "functional_analysis_and_operator_theory": ("finite-operator-v0", "Finite-dimensional norms, inner products, dual spaces, operator matrices, Chebyshev polynomial slices, and finite Chebyshev-system grids."),
}

FIELD_DECIDABILITY = {
    "complex_analysis": "proof-horizon",
    "topology": "proof-horizon",
    "measure_theory": "proof-horizon",
    "functional_analysis_and_operator_theory": "proof-horizon",
    "statistics": "numerical",
    "numerical_analysis": "numerical",
}

BRIDGE_CONCEPTS = [
    {
        "id": "bridge_finite_model_replay",
        "title": "Finite Model Replay",
        "field_ids": ["logic_and_proof"],
        "resource_status": "validated",
        "summary": (
            "A concrete finite witness or finite table is accepted only after "
            "the original mathematical claim is recomputed from the committed "
            "data, independent of solver search."
        ),
        "prerequisites": [
            "curriculum_propositional_logic",
            "curriculum_sets",
            "curriculum_naturals",
        ],
        "unlocks": [
            "bridge_counterexample_proof",
            "bridge_bounded_theorem_shadow",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite enumeration",
            "model replay",
            "Bool / SAT",
            "exact rational arithmetic",
        ],
        "example_packs": [
            (
                "logic-basics-v0",
                "Truth-table and Boolean assignment replay for tiny SAT/UNSAT claims.",
            ),
            (
                "finite-sets-v0",
                "Finite membership, subset, union, intersection, and identity replay.",
            ),
            (
                "finite-probability-v0",
                "Finite probability-table normalization, conditioning, and Bayes-rule replay.",
            ),
            (
                "linear-algebra-rational-v0",
                "Exact rational matrix witnesses replayed against the source linear-algebra claim.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite-model replay",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py",
                "lean_status": "not-required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
                ],
                "notes": (
                    "The validator recomputes the finite claim directly from "
                    "the committed model or table; no solver verdict is trusted "
                    "as evidence by itself."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md",
        ],
        "open_gaps": [
            "Finite replay proves only the stated finite instance, not the corresponding infinite or schematic theorem.",
            "Rows that involve solver lowering still need route-specific certificates when the replay target is unsat.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Every replay row names the exact finite universe, table, witness, or assignment it checks.",
                "The pack validator rejects corrupted witness data.",
                "Learner pages state the boundary between finite replay and any broader theorem.",
            ],
        },
    },
    {
        "id": "bridge_counterexample_proof",
        "title": "Counterexample Proof",
        "field_ids": ["logic_and_proof"],
        "resource_status": "validated",
        "summary": (
            "A false universal or malformed object is refuted by a concrete "
            "counterexample, checked finite replay, or a small independently "
            "checked UNSAT certificate for the negated finite obligation."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "curriculum_proof_methods",
        ],
        "unlocks": [
            "bridge_bounded_theorem_shadow",
            "curriculum_predicate_logic",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "Bool / SAT",
            "CNF / DRAT / LRAT",
            "QF_LRA / Farkas",
            "finite countermodel replay",
        ],
        "example_packs": [
            (
                "proof-methods-patterns-v0",
                "Direct proof, contrapositive, cases, contradiction, invalid-converse, and counterexample rows.",
            ),
            (
                "graph-coloring-v0",
                "Triangle non-2-colorability as exhaustive replay, CNF/LRAT, and QF_BV/DRAT evidence.",
            ),
            (
                "rationals-lra-v0",
                "Exact rational order counterexamples and Farkas-backed infeasible order claims.",
            ),
            (
                "finite-sets-v0",
                "Malformed finite set identities rejected by replay and CNF proof routes.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite counterexample plus certificate when unsat",
                "status": "checked",
                "checker": "example-pack validator plus route-specific DRAT/LRAT or Farkas regression",
                "lean_status": "planned",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                ],
                "notes": (
                    "A counterexample row is checked at the finite source claim; "
                    "certificate-backed rows additionally check the generated "
                    "CNF or rational infeasibility proof object."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
        ],
        "open_gaps": [
            "For certificate-backed counterexamples, the encoder from mathematical object to solver artifact remains a named trust step unless separately reconstructed.",
            "General proof-method soundness remains a Lean horizon rather than a consequence of finite examples.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "The row identifies whether evidence is a model witness, finite countermodel, DRAT/LRAT proof, Farkas proof, or another checked route.",
                "Tampering with the finite witness or proof artifact is rejected by the associated validator or regression.",
                "The learner page explains why a single counterexample refutes the stated universal claim.",
            ],
        },
    },
    {
        "id": "bridge_bounded_theorem_shadow",
        "title": "Bounded Theorem Shadow",
        "field_ids": ["logic_and_proof"],
        "resource_status": "validated",
        "summary": (
            "A broad theorem is represented by one or more finite, bounded, "
            "or exact-rational instances that are useful for learning and "
            "solver regression but do not prove the general theorem."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "curriculum_reals",
            "curriculum_sequences_and_limits",
        ],
        "unlocks": [
            "bridge_lean_horizon",
            "curriculum_calculus",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "QF_LRA",
            "QF_NRA shadow",
            "finite probability",
            "finite transition systems",
            "bounded epsilon-delta templates",
        ],
        "example_packs": [
            (
                "sequence-limit-shadow-v0",
                "Finite prefix and bounded epsilon-N checks for convergence-shaped claims.",
            ),
            (
                "real-analysis-rational-v0",
                "Exact rational ball, delta, and neighborhood checks for analysis shadows.",
            ),
            (
                "metric-continuity-v0",
                "Finite metric continuity examples with an explicit general-continuity horizon.",
            ),
            (
                "finite-concentration-v0",
                "Finite probability-tail inequalities checked over exact atom tables.",
            ),
        ],
        "proof_routes": [
            {
                "name": "bounded finite shadow with explicit theorem gap",
                "status": "replay-only",
                "checker": "scripts/validate-foundational-example-pack.py",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                ],
                "notes": (
                    "Exact finite shadows are checked as examples or regressions; "
                    "the unbounded theorem remains open until a Lean route lands."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
        ],
        "open_gaps": [
            "Finite bounded checks must not be advertised as completeness, compactness, convergence, or asymptotic proofs.",
            "Each shadow needs an explicit path to Lean or an explicit statement that it remains only a finite educational artifact.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "The resource states the finite bounds or exact rational instance being checked.",
                "The expected result distinguishes checked finite rows from the general theorem horizon.",
                "The learner page links the bounded row to the missing theorem-level proof route.",
            ],
        },
    },
    {
        "id": "bridge_lean_horizon",
        "title": "Lean Horizon",
        "field_ids": ["logic_and_proof"],
        "resource_status": "proof-horizon",
        "summary": (
            "An unbounded, schematic, analytic, or structure-theoretic theorem "
            "is tracked as a proof-assistant target until a kernel-checked Lean "
            "module replaces the finite shadow."
        ),
        "prerequisites": [
            "bridge_bounded_theorem_shadow",
            "curriculum_proof_methods",
            "curriculum_induction",
        ],
        "unlocks": [],
        "decidability": "proof-horizon",
        "axeyum_fragments": [
            "Lean reconstruction",
            "proof object checking",
            "general theorem statements",
            "axiom audit",
        ],
        "example_packs": [
            (
                "induction-patterns-v0",
                "Bounded induction patterns with the full induction schema kept as Lean horizon.",
            ),
            (
                "real-analysis-rational-v0",
                "Finite rational real-analysis checks with general real-analysis theorem horizons.",
            ),
            (
                "finite-topology-v0",
                "Finite topology examples with compactness, connectedness, and continuity horizons.",
            ),
            (
                "finite-chebyshev-systems-v0",
                "Finite Chebyshev-system grids with general functional-analysis theory left to Lean.",
            ),
        ],
        "proof_routes": [
            {
                "name": "Lean kernel reconstruction",
                "status": "lean-horizon",
                "checker": "planned Lean command with no sorry and axiom audit",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md",
                ],
                "notes": (
                    "Finite shadows remain useful examples, but this bridge "
                    "graduates only when a checked Lean artifact covers the "
                    "general statement without sorry."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/plan/track-3-proof-lean/P3.7-lean-reconstruction.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
        ],
        "open_gaps": [
            "The Lean tactic backend is not built for most horizon families.",
            "No finite example pack can graduate this bridge without a kernel-checked theorem artifact.",
        ],
        "graduation": {
            "status": "proof-horizon",
            "criteria": [
                "A Lean module checks with no sorry or sorryAx dependency.",
                "The resource records the theorem statement, imports, and axiom audit.",
                "The corresponding finite shadow remains linked as an example rather than the proof.",
            ],
        },
    },
]

EXAMPLE_FAMILIES = [
    {
        "id": "family_finite_algebra_alethe",
        "title": "Finite Algebra Alethe Congruence Family",
        "field_ids": ["abstract_algebra"],
        "resource_status": "validated",
        "summary": (
            "Recurring finite algebra and finite function-table conflicts that "
            "reduce to small EUF congruence, functionality, closure, or "
            "preservation obligations and recheck as zero-trust Alethe evidence."
        ),
        "prerequisites": [
            "bridge_counterexample_proof",
            "curriculum_relations_and_functions",
            "curriculum_groups",
            "curriculum_rings",
            "curriculum_fields",
            "curriculum_linear_algebra",
        ],
        "unlocks": ["field_abstract_algebra"],
        "decidability": "decidable",
        "axeyum_fragments": [
            "QF_UF",
            "EUF congruence",
            "Alethe proof checking",
            "finite table replay",
        ],
        "example_packs": [
            (
                "equivalence-classes-v0",
                "Quotient-map congruence conflict over a finite equivalence relation.",
            ),
            (
                "relations-functions-v0",
                "Function single-valuedness conflict over finite relation data.",
            ),
            (
                "finite-groups-v0",
                "Binary-operation congruence conflict for a finite operation symbol.",
            ),
            (
                "function-composition-v0",
                "Composition application consistency conflict for finite functions.",
            ),
            (
                "finite-algebra-homomorphisms-v0",
                "Homomorphism-preservation congruence conflict for finite algebra maps.",
            ),
            (
                "finite-monoids-v0",
                "Associativity failure captured as a fixed EUF equality conflict.",
            ),
            (
                "finite-order-lattices-v0",
                "Antisymmetry failure captured as a fixed equality conflict.",
            ),
            (
                "finite-permutation-groups-v0",
                "Duplicate-image non-bijection captured as an injectivity conflict.",
            ),
            (
                "finite-vector-spaces-v0",
                "Subspace addition-closure failure captured as a membership conflict.",
            ),
            (
                "finite-dual-spaces-v0",
                "Covector additivity failure captured as a finite function conflict.",
            ),
            (
                "finite-modules-v0",
                "Submodule scalar-closure failure captured as a membership conflict.",
            ),
            (
                "finite-ideals-v0",
                "Ideal additive-closure failure captured as a membership conflict.",
            ),
            (
                "finite-tensor-products-v0",
                "Bilinear left-additivity failure captured as a finite map conflict.",
            ),
        ],
        "proof_routes": [
            {
                "name": "QF_UF/Alethe congruence family",
                "status": "checked",
                "checker": "cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "Each referenced pack keeps finite table replay separate "
                    "from the EUF proof artifact; the regression parses the "
                    "SMT-LIB row, emits an UnsatAletheProof, and rechecks it "
                    "through Evidence::check."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "The family certifies small EUF conflicts, not full finite algebra structure theorems.",
            "New finite algebra packs should join this family only after they have a source-linked SMT-LIB artifact and a checked math_resource_uf_routes regression.",
            "Lean reconstruction remains partial at the family level until every recurring EUF shape has a kernel-checked route.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Every family pack row links a concrete SMT-LIB artifact and proof regression.",
                "cargo test -p axeyum-solver --test math_resource_uf_routes passes.",
                "Learner pages keep finite table replay separate from the checked Alethe certificate.",
            ],
        },
    },
]


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


def load_example_pack_metadata() -> dict[str, dict[str, Any]]:
    packs: dict[str, dict[str, Any]] = {}
    for metadata_path in sorted(EXAMPLE_ROOT.glob("*/metadata.json")):
        with metadata_path.open("r", encoding="utf-8") as handle:
            metadata = json.load(handle)
        if metadata.get("claim_status") == "template":
            continue
        packs[metadata["id"]] = metadata
    return packs


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


def field_pack_specs(field_id: str, pack_metadata: dict[str, dict[str, Any]]) -> list[tuple[str, str]]:
    value = FIELD_PACKS[field_id]
    if isinstance(value, tuple):
        specs = [value]
    else:
        specs = list(value)
    seen = {pack_id for pack_id, _ in specs}
    discovered = [
        (pack_id, metadata)
        for pack_id, metadata in pack_metadata.items()
        if field_id in metadata.get("field_ids", [])
    ]
    for pack_id, metadata in sorted(discovered):
        if pack_id in seen:
            continue
        specs.append((pack_id, metadata["title"]))
        seen.add(pack_id)
    return specs


def curriculum_pack_specs(mapping: dict[str, Any]) -> list[tuple[str, str]]:
    return [(mapping["pack"], mapping["slice"])] + mapping.get("extra_packs", [])


def proof_route(
    name: str,
    status: str,
    checker: str,
    lean_status: str,
    notes: str,
    *,
    sources: list[str] | None = None,
) -> dict[str, Any]:
    return {
        "name": name,
        "status": status,
        "checker": checker,
        "lean_status": lean_status,
        "sources": sources
        or [
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


def make_field_row(
    field_id: str,
    field: dict[str, str],
    curriculum_rows: list[dict[str, Any]],
    pack_metadata: dict[str, dict[str, Any]],
) -> dict[str, Any]:
    pack_specs = field_pack_specs(field_id, pack_metadata)
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


def make_bridge_row(spec: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": spec["id"],
        "kind": "bridge-concept",
        "title": spec["title"],
        "domain": "mathematics",
        "field_ids": spec["field_ids"],
        "curriculum_node": None,
        "curriculum_layer": None,
        "curriculum_area": None,
        "curriculum_status": "extension",
        "curriculum_family": "",
        "resource_status": spec["resource_status"],
        "summary": spec["summary"],
        "prerequisites": spec["prerequisites"],
        "unlocks": spec["unlocks"],
        "decidability": spec["decidability"],
        "axeyum_fragments": spec["axeyum_fragments"],
        "example_packs": [pack(pack_id, pack_notes) for pack_id, pack_notes in spec["example_packs"]],
        "proof_routes": spec["proof_routes"],
        "source_refs": spec["source_refs"],
        "open_gaps": spec["open_gaps"],
        "graduation": spec["graduation"],
    }


def make_example_family_row(spec: dict[str, Any]) -> dict[str, Any]:
    return {
        "id": spec["id"],
        "kind": "example-family",
        "title": spec["title"],
        "domain": "mathematics",
        "field_ids": spec["field_ids"],
        "curriculum_node": None,
        "curriculum_layer": None,
        "curriculum_area": None,
        "curriculum_status": "extension",
        "curriculum_family": "",
        "resource_status": spec["resource_status"],
        "summary": spec["summary"],
        "prerequisites": spec["prerequisites"],
        "unlocks": spec["unlocks"],
        "decidability": spec["decidability"],
        "axeyum_fragments": spec["axeyum_fragments"],
        "example_packs": [pack(pack_id, pack_notes) for pack_id, pack_notes in spec["example_packs"]],
        "proof_routes": spec["proof_routes"],
        "source_refs": spec["source_refs"],
        "open_gaps": spec["open_gaps"],
        "graduation": spec["graduation"],
    }


def main() -> int:
    nodes = load_curriculum()
    node_by_id = {node["id"]: node for node in nodes}
    fields = load_math_fields()
    pack_metadata = load_example_pack_metadata()
    curriculum_rows = [make_curriculum_row(node, node_by_id) for node in nodes]
    bridge_rows = [make_bridge_row(spec) for spec in BRIDGE_CONCEPTS]
    example_family_rows = [make_example_family_row(spec) for spec in EXAMPLE_FAMILIES]
    field_rows = [
        make_field_row(field_id, fields[field_id], curriculum_rows, pack_metadata)
        for field_id in sorted(fields)
    ]
    atlas = {
        "schema_version": 1,
        "generated_from": [
            "docs/curriculum/curriculum.toml",
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md",
            "artifacts/examples/math",
        ],
        "rows": curriculum_rows + bridge_rows + example_family_rows + field_rows,
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    with OUT.open("w", encoding="utf-8") as handle:
        json.dump(atlas, handle, indent=2, sort_keys=False)
        handle.write("\n")
    print(f"generated {len(atlas['rows'])} foundational concept rows")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
