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
                "Finite partial orders, lattice meet/join tables, distributivity, monotone maps, fixed-point replay, and bad top-element CNF evidence.",
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
                "Finite partial orders, meet/join lattice tables, monotone maps, fixed points, bad-order counterexamples, and bad top-element CNF evidence.",
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
                "Finite Boolean lattice over a two-element powerset, meet/join replay, monotone fixed points, and bad top-element CNF evidence.",
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
                "finite-root-finding-v0",
                "Finite bisection/Newton root-finding replay and checked bad-step plus bad-width rejections.",
            ),
            (
                "finite-separation-v0",
                "Finite convex-hull and separating-hyperplane replay with checked bad convex-combination and bad-separator rejections.",
            ),
            (
                "finite-kkt-v0",
                "Finite constrained-quadratic KKT replay with checked bad-stationarity rejection.",
            ),
            (
                "finite-active-set-qp-v0",
                "Finite active-set quadratic-program replay with checked bad-free-gradient rejection.",
            ),
            (
                "finite-sdp-v0",
                "Finite two-by-two SDP primal/dual replay with checked bad-objective and bad duality-gap rejections.",
            ),
            (
                "finite-gradient-descent-v0",
                "Finite exact gradient-descent step replay with checked bad-decrease, bad step-coordinate, and bad descent-bound rejections.",
            ),
            (
                "finite-line-search-v0",
                "Finite exact Armijo line-search replay with checked bad-acceptance, bad descent-direction, and bad accepted-candidate rejections.",
            ),
            (
                "finite-wolfe-line-search-v0",
                "Finite exact Wolfe line-search replay with checked bad-minimizer and bad-curvature rejections.",
            ),
            (
                "finite-projected-gradient-v0",
                "Finite exact projected-gradient interval projection with checked bad-projection rejection.",
            ),
            (
                "finite-proximal-gradient-v0",
                "Finite exact L1 proximal-gradient soft-threshold/composite-decrease replay with checked bad-proximal-point, bad composite-decrease, and bad-box rejection.",
            ),
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
            (
                "finite-root-finding-v0",
                "Finite polynomial evaluation, bisection brackets, Newton steps, and bad-step plus bad-width rejections.",
            ),
        ],
    },
    "sequences-and-limits": {
        "field_ids": ["real_analysis", "topology"],
        "pack": "sequence-limit-shadow-v0",
        "slice": "Bounded epsilon/N templates, algebraic sequence checks, and checked bad-tail bounds.",
        "proof": "Bounded arithmetic replay; general limits require Lean.",
        "extra_packs": [
            (
                "bounded-monotone-sequence-v0",
                "Finite monotone-prefix, supremum, tail-gap, replay-only bad source rows, and separate checked qf-lra proof rows.",
            ),
            (
                "finite-recurrence-prefix-v0",
                "Finite recurrence-prefix, affine recurrence, companion-matrix, bad value, and bad affine-step checks.",
            ),
        ],
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
            (
                "finite-recurrence-prefix-v0",
                "Finite recurrence prefixes, companion-matrix replay, and checked affine-step refutations for enumerative sequences.",
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
        "slice": "Fixed rational matrices, LU replay, nullspace replay, inverse checks, and inconsistent systems.",
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
            (
                "finite-recurrence-prefix-v0",
                "Finite recurrence prefixes, companion-matrix state replay, and checked affine-step refutations.",
            ),
            (
                "finite-root-finding-v0",
                "Exact rational root-finding iterations with bad Newton-step and bisection-width rejections.",
            ),
            (
                "finite-separation-v0",
                "Exact convex-hull, dot-product, and separating-hyperplane replay.",
            ),
            (
                "finite-kkt-v0",
                "Exact constrained-quadratic stationarity and complementary-slackness replay.",
            ),
            (
                "finite-active-set-qp-v0",
                "Exact active-face QP replay with inactive-constraint slack and bad-free-gradient rejection.",
            ),
            (
                "finite-sdp-v0",
                "Exact two-by-two PSD, trace, objective, slack, and dual-gap replay.",
            ),
            (
                "finite-gradient-descent-v0",
                "Exact quadratic gradient, step update, objective decrease, descent-bound replay, and checked bad step-coordinate/decrease rows.",
            ),
            (
                "finite-line-search-v0",
                "Exact Armijo trial rejection, descent-direction replay, backtracked-step acceptance, and bad-acceptance plus bad accepted-candidate rejection.",
            ),
            (
                "finite-wolfe-line-search-v0",
                "Exact Wolfe line-minimizer, sufficient-decrease, and curvature replay with bad-minimizer and bad-curvature rejections.",
            ),
            (
                "finite-projected-gradient-v0",
                "Exact interval projection after a gradient step and bad-projection rejection.",
            ),
            (
                "finite-proximal-gradient-v0",
                "Exact L1 soft-threshold/composite-decrease proximal-gradient replay and bad proximal-gradient rows.",
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
            (
                "finite-root-finding-v0",
                "Finite bisection/Newton root-finding replay, bad-width checks, and convergence-theorem horizon rows.",
            ),
            (
                "finite-kkt-v0",
                "Finite KKT stationarity and complementary-slackness replay for a constrained quadratic.",
            ),
            (
                "finite-active-set-qp-v0",
                "Finite active-set QP replay with active-face and inactive-constraint checks.",
            ),
            (
                "finite-gradient-descent-v0",
                "Finite exact gradient-descent step replay with checked bad step-coordinate/decrease rows and convergence-theorem horizon rows.",
            ),
            (
                "finite-line-search-v0",
                "Finite exact Armijo rejection/acceptance replay, descent-direction replay, accepted-candidate replay, and convergence-theorem horizon rows.",
            ),
            (
                "finite-wolfe-line-search-v0",
                "Finite exact Wolfe minimizer, sufficient-decrease/curvature replay, bad-minimizer, and convergence-theorem horizon rows.",
            ),
            (
                "finite-projected-gradient-v0",
                "Finite exact projected-gradient interval replay and convergence-theorem horizon rows.",
            ),
            (
                "finite-proximal-gradient-v0",
                "Finite exact proximal-gradient L1 soft-threshold replay and convergence-theorem horizon rows.",
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
    "measure_theory": ("finite-measure-v0", "Finite sigma-algebras, finite measures, monotonicity/subadditivity, random variables, conditional expectations, finite kernels, martingales, hitting times, concentration checks, product tables, and exact probability foundations."),
    "probability_theory": ("finite-probability-v0", "Finite mass tables, random variables, conditional expectation, kernels, martingales, hitting times, concentration/tail bounds, conditioning, independence, Bayes rule, product measures, and exact discrete distributions."),
    "statistics": ("descriptive-statistics-v0", "Mean/variance identities, random variables, conditional expectation, finite kernel, hitting-time, martingale, and concentration checks, contingency tables, exact tests, and Simpson witnesses."),
    "optimization_and_convexity": [
        ("linear-optimization-v0", "LP feasibility, threshold cliffs, and Farkas-style certificates."),
        ("convexity-rational-v0", "Finite midpoint convexity, second differences, affine threshold monotonicity, and checked bad midpoint-convexity plus affine-threshold rejection."),
        ("multivariable-calculus-rational-v0", "Exact gradients, directional derivatives, Hessian minors, and local convexity shadows."),
        ("inner-product-spaces-rational-v0", "Exact rational projections, Gram matrices, and orthogonal residual checks."),
        ("finite-separation-v0", "Finite convex-hull and hyperplane-separation replay with checked bad convex-combination and bad-separator rejections."),
        ("finite-kkt-v0", "Finite KKT stationarity, complementary slackness, and bad-stationarity rejection."),
        ("finite-active-set-qp-v0", "Finite active-set QP replay with checked bad-free-gradient rejection."),
        ("finite-sdp-v0", "Finite SDP primal/dual slack replay with checked bad-objective and bad duality-gap rejections."),
        ("finite-gradient-descent-v0", "Finite gradient-descent step replay with checked bad-decrease, bad step-coordinate, and bad descent-bound rejections."),
        ("finite-line-search-v0", "Finite Armijo line-search replay with checked bad-acceptance, bad descent-direction, and bad accepted-candidate rejections."),
        ("finite-wolfe-line-search-v0", "Finite Wolfe line-search replay with checked bad-minimizer and bad-curvature rejections."),
        ("finite-projected-gradient-v0", "Finite projected-gradient interval replay with checked bad-projection rejection."),
        ("finite-proximal-gradient-v0", "Finite proximal-gradient L1 soft-threshold/composite-decrease replay with checked bad proximal-gradient rows."),
    ],
    "numerical_analysis": ("numerical-linear-algebra-v0", "LU replay, interval bounds, inner-product projections, fixed-step error recurrences, Jacobian/Hessian replay, finite root-finding, active-set QP, gradient-step, Armijo/Wolfe line-search, projected-gradient, and proximal-gradient rational shadows."),
    "differential_equations_and_dynamical_systems": ("bounded-dynamics-v0", "Recurrence systems, discretized dynamics, threshold reachability, invariant checks, Markov transitions, and finite hitting times."),
    "geometry": [
        (
            "coordinate-geometry-v0",
            "Incidence, line equations, distance tables, midpoint, collinearity, and rigid finite configurations.",
        ),
        (
            "finite-circle-geometry-v0",
            "Finite circle point, tangent-line, chord-midpoint, and bad-radius replay over exact rational coordinates.",
        ),
        (
            "finite-inversion-geometry-v0",
            "Finite unit-circle inversion image, inverse-distance product, collinearity, and bad inverse-coordinate replay.",
        ),
        (
            "finite-cyclic-geometry-v0",
            "Finite cyclic quadrilateral, diagonal-intersection, opposite-angle, and bad-intersection replay.",
        ),
    ],
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
                "Finite probability-table normalization, conditioning, independence, and Bayes-rule replay.",
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
        "id": "bridge_refutation_query",
        "title": "Refutation As Query",
        "field_ids": ["logic_and_proof", "discrete_math"],
        "resource_status": "validated",
        "summary": (
            "A proof-by-refutation row turns a finite claim into a solver "
            "query by asserting the hypotheses, negating the target, and "
            "checking that the resulting finite obligation has a checked "
            "UNSAT certificate or a replayed countermodel."
        ),
        "prerequisites": [
            "bridge_counterexample_proof",
            "curriculum_propositional_logic",
            "curriculum_proof_methods",
        ],
        "unlocks": [
            "bridge_finite_proof_pattern",
            "bridge_finite_quantifier_expansion",
            "curriculum_counting",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "Bool / SAT",
            "CNF / DRAT / LRAT",
            "finite refutation",
            "proof object anatomy",
        ],
        "example_packs": [
            (
                "proof-methods-refutation-v0",
                "Pigeonhole-style proof by refutation with source-linked CNF and checked DRAT/LRAT evidence.",
            ),
            (
                "proof-methods-patterns-v0",
                "Contradiction and invalid-proof rows that separate countermodel replay from refutation evidence.",
            ),
            (
                "logic-basics-v0",
                "Tiny Boolean contradictions and tautology-by-negation rows with checked CNF evidence.",
            ),
            (
                "counting-v0",
                "Finite pigeonhole refutation rows that reuse the same CNF/LRAT trust story.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite refutation query plus Boolean CNF/LRAT certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-cnf --test math_resource_boolean_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/learn/math/proof-methods-refutation-end-to-end.md",
                    "docs/learn/math/proof-object-anatomy-end-to-end.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                ],
                "notes": (
                    "The solver search and CNF encoding are not trusted as "
                    "proof by themselves; the small checked object is the "
                    "DRAT/LRAT certificate for the finite refutation."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/learn/math/proof-methods-refutation-end-to-end.md",
            "docs/learn/math/proof-object-anatomy-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
        ],
        "open_gaps": [
            "A finite refutation proves only the encoded finite obligation unless the mathematical reduction is separately reconstructed.",
            "Natural-deduction proof methods and arbitrary quantified refutations remain Lean-horizon work.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the hypotheses, negated target, finite universe, and source-level encoding route.",
                "The validator links the row to the source artifact or replayed countermodel.",
                "Certificate-backed rows reject corrupted or truncated proof objects in route-specific tests.",
            ],
        },
    },
    {
        "id": "bridge_finite_proof_pattern",
        "title": "Finite Proof Pattern Replay",
        "field_ids": ["logic_and_proof", "set_theory_and_foundations"],
        "resource_status": "validated",
        "summary": (
            "A finite proof-pattern row checks direct proof, contrapositive, "
            "proof by cases, contradiction, and invalid-converse shapes over "
            "a fixed finite Boolean or set model, while keeping general proof "
            "calculus soundness in the Lean horizon."
        ),
        "prerequisites": [
            "bridge_refutation_query",
            "bridge_counterexample_proof",
            "curriculum_proof_methods",
        ],
        "unlocks": [
            "bridge_bounded_induction_obligation",
            "bridge_lean_horizon",
            "curriculum_sets",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "Bool / SAT",
            "truth-table enumeration",
            "finite set replay",
            "CNF / DRAT / LRAT",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "proof-methods-patterns-v0",
                "Finite direct, contrapositive, cases, contradiction, and invalid-converse proof-pattern rows.",
            ),
            (
                "finite-sets-v0",
                "Finite set identities and counterexample rows that reuse direct and refutation patterns.",
            ),
            (
                "logic-basics-v0",
                "Boolean implication and contradiction rows that provide the smallest proof-pattern surface.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite truth-table/set replay plus Boolean certificate when unsat",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-cnf --test math_resource_boolean_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/proof-methods-patterns-end-to-end.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                ],
                "notes": (
                    "Finite patterns are replayed as concrete examples; a "
                    "general proof calculus or tactic soundness story is not "
                    "claimed until Lean reconstruction covers the shape."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/proof-methods-patterns-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
        ],
        "open_gaps": [
            "Finite proof-pattern rows do not prove natural-deduction completeness or tactic soundness.",
            "Rows with quantified hypotheses need the finite-quantifier-expansion bridge or a Lean route.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows name the proof pattern, finite carrier or truth table, and exact expected result.",
                "The validator recomputes the finite case split, implication, or counterexample directly.",
                "Learner pages separate proof-pattern examples from theorem-level proof automation.",
            ],
        },
    },
    {
        "id": "bridge_finite_quantifier_expansion",
        "title": "Finite Quantifier Expansion",
        "field_ids": ["logic_and_proof", "set_theory_and_foundations", "discrete_math"],
        "resource_status": "validated",
        "summary": (
            "A finite quantifier-expansion row replaces universal and "
            "existential statements over a committed finite domain with the "
            "corresponding finite conjunctions, disjunctions, relation-table "
            "lookups, and equality constraints."
        ),
        "prerequisites": [
            "bridge_refutation_query",
            "bridge_finite_model_replay",
            "curriculum_predicate_logic",
        ],
        "unlocks": [
            "bridge_quotient_map",
            "bridge_bounded_induction_obligation",
            "field_set_theory_and_foundations",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite predicate logic",
            "finite-domain quantifier expansion",
            "Bool / CNF",
            "finite relations",
            "QF_UF",
        ],
        "example_packs": [
            (
                "finite-predicate-v0",
                "Finite-domain universal/existential rows with source-linked Bool/CNF proof evidence.",
            ),
            (
                "relations-functions-v0",
                "Finite relation and function-table rows that supply predicate extensions.",
            ),
            (
                "equivalence-classes-v0",
                "Finite equivalence and quotient rows that add equality-heavy QF_UF pressure.",
            ),
            (
                "finite-cardinality-v0",
                "Finite function-quantifier rows for injection/surjection obstruction examples.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite quantifier expansion with Bool/CNF or QF_UF evidence",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py, cargo test -p axeyum-cnf --test math_resource_boolean_routes, and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/learn/math/finite-predicate-end-to-end.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The finite expansion is checked for the committed domain; "
                    "arbitrary-domain first-order validity remains a separate "
                    "Lean or solver-theory horizon."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/learn/math/finite-predicate-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite-domain expansion does not prove arbitrary-domain first-order validity, compactness, completeness, or Lowenheim-Skolem theorems.",
            "Quantifier alternation over large or symbolic domains needs a separate solver-theory and proof route.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite domain, relation/function tables, and expanded Boolean or equality obligation.",
                "The validator rejects metadata/check drift between quantified source rows and expanded checks.",
                "Learner pages explicitly distinguish finite-domain truth from first-order validity.",
            ],
        },
    },
    {
        "id": "bridge_bounded_induction_obligation",
        "title": "Bounded Induction Obligation",
        "field_ids": ["logic_and_proof", "number_theory"],
        "resource_status": "validated",
        "summary": (
            "A bounded induction-obligation row checks finite base cases, "
            "finite step obligations, invariant prefixes, and arithmetic "
            "counterexample counts, while keeping the universal induction "
            "schema as an explicit Lean horizon."
        ),
        "prerequisites": [
            "bridge_finite_quantifier_expansion",
            "bridge_finite_proof_pattern",
            "curriculum_naturals",
        ],
        "unlocks": [
            "bridge_lean_horizon",
            "curriculum_number_theory",
            "curriculum_calculus",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "bounded induction obligations",
            "finite-domain enumeration",
            "QF_LIA / arithmetic-DPLL",
            "QF_LIA / Diophantine",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "induction-obligations-v0",
                "Bounded base/step obligations and bad-step counterexample-count rows.",
            ),
            (
                "induction-patterns-v0",
                "Finite weak induction, strong induction, loop-invariant, and parity-obstruction rows.",
            ),
            (
                "natural-arithmetic-v0",
                "Bounded natural-number prefix and bad negative-domain arithmetic rows.",
            ),
            (
                "graph-search-runtime-v0",
                "Finite traversal-cost family rows that reuse bounded-prefix arithmetic checks.",
            ),
        ],
        "proof_routes": [
            {
                "name": "bounded induction replay plus QF_LIA arithmetic certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lia_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/induction-obligations-end-to-end.md",
                    "docs/learn/math/induction-patterns-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                ],
                "notes": (
                    "Finite prefixes and bad-step counts are checked as "
                    "bounded arithmetic facts; the general induction schema "
                    "needs Lean reconstruction before it can graduate."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/induction-obligations-end-to-end.md",
            "docs/learn/math/induction-patterns-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
        ],
        "open_gaps": [
            "A bounded prefix or finite step check does not prove the induction schema over all natural numbers.",
            "Universal induction, recursion principles, and proof-method automation remain Lean-horizon work.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the bound, base cases, step range, arithmetic formula, and expected finite result.",
                "The validator or route regression rejects corrupted bad-step counts or impossible parity rows.",
                "Learner pages state the boundary between finite prefixes and theorem-level induction.",
            ],
        },
    },
    {
        "id": "bridge_boolean_cnf_lrat_anatomy",
        "title": "Boolean CNF DRAT/LRAT Anatomy",
        "field_ids": ["logic_and_proof", "discrete_math", "graph_theory", "topology"],
        "resource_status": "validated",
        "summary": (
            "A Boolean proof-object row starts from a committed source CNF, "
            "lets untrusted SAT search emit DRAT/LRAT evidence, and accepts "
            "the UNSAT claim only after the small proof object checks against "
            "that source formula."
        ),
        "prerequisites": [
            "bridge_refutation_query",
            "bridge_finite_quantifier_expansion",
            "curriculum_propositional_logic",
        ],
        "unlocks": [
            "bridge_qf_bv_bitblast_anatomy",
            "curriculum_counting",
            "field_graph_theory",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "Bool / CNF",
            "SAT",
            "DRAT / LRAT",
            "proof object anatomy",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "proof-methods-refutation-v0",
                "PHP(3,2) source CNF with checked DRAT/LRAT proof objects and tamper rejection.",
            ),
            (
                "logic-basics-v0",
                "Tiny Boolean contradiction rows that exercise the smallest CNF certificate surface.",
            ),
            (
                "finite-predicate-v0",
                "Finite quantifier-expansion row backed by source-linked Bool/CNF evidence.",
            ),
            (
                "graph-coloring-v0",
                "Triangle non-2-colorability rows that separate graph encoding from CNF proof checking.",
            ),
            (
                "finite-topology-v0",
                "Finite topology missing-empty-set row with a source-linked Boolean certificate.",
            ),
        ],
        "proof_routes": [
            {
                "name": "source CNF plus checked DRAT/LRAT proof object",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-cnf --test math_resource_boolean_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/learn/math/proof-object-anatomy-end-to-end.md",
                    "docs/learn/math/proof-methods-refutation-end-to-end.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                ],
                "notes": (
                    "The CNF proof checker is the trusted object for the "
                    "Boolean formula. Any source-to-CNF encoder remains a "
                    "named trust boundary unless separately reconstructed."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/learn/math/proof-object-anatomy-end-to-end.md",
            "docs/learn/math/logic-and-proof.md",
            "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
        ],
        "open_gaps": [
            "A checked DRAT/LRAT proof certifies the concrete CNF, not an arbitrary mathematical encoding that produced the CNF.",
            "General Lean reconstruction for the full Boolean proof route is still a graduation horizon.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows link to a committed DIMACS or source CNF artifact.",
                "The focused regression emits and checks DRAT/LRAT evidence for the same artifact.",
                "A tamper test rejects a truncated or corrupted proof object.",
            ],
        },
    },
    {
        "id": "bridge_qf_lra_farkas_anatomy",
        "title": "QF_LRA Farkas Certificate Anatomy",
        "field_ids": [
            "linear_algebra",
            "optimization_and_convexity",
            "real_analysis",
            "probability_theory",
            "statistics",
            "numerical_analysis",
        ],
        "resource_status": "validated",
        "summary": (
            "An exact-rational linear infeasibility row carries a Farkas "
            "certificate: nonnegative rational multipliers combine the source "
            "inequalities into an impossible constant inequality, and the "
            "certificate is rechecked independently."
        ),
        "prerequisites": [
            "bridge_counterexample_proof",
            "curriculum_rationals",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "bridge_lp_objective_farkas",
            "bridge_residual_bound",
            "bridge_probability_mass_table",
            "bridge_eigenpair",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "QF_LRA",
            "exact rational arithmetic",
            "Farkas certificate",
            "linear infeasibility",
            "Lean partial",
        ],
        "example_packs": [
            (
                "linear-optimization-v0",
                "Objective-threshold conflict with checked UnsatFarkas evidence and multiplier tamper rejection.",
            ),
            (
                "linear-algebra-rational-v0",
                "Singular inconsistent linear-system row that reduces to exact rational infeasibility.",
            ),
            (
                "finite-probability-v0",
                "Malformed probability-table rows checked through exact rational Farkas evidence.",
            ),
            (
                "numerical-linear-algebra-v0",
                "Bad residual-bound, solution-box, and Jacobi error-bound rows whose final contradictions are exact rational linear arithmetic.",
            ),
            (
                "finite-chebyshev-systems-v0",
                "Finite determinant conflict that uses the same checked QF_LRA/Farkas route.",
            ),
        ],
        "proof_routes": [
            {
                "name": "QF_LRA exact-rational Farkas certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/learn/math/farkas-certificate-anatomy-end-to-end.md",
                    "docs/learn/math/linear-algebra-and-optimization.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                    "crates/axeyum-solver/tests/evidence.rs",
                ],
                "notes": (
                    "The arithmetic search is not trusted by itself. The "
                    "accepted proof object is the exact-rational multiplier "
                    "certificate checked against the original assertions."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/learn/math/farkas-certificate-anatomy-end-to-end.md",
            "docs/learn/math/linear-algebra-and-optimization.md",
            "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
            "crates/axeyum-solver/tests/evidence.rs",
        ],
        "open_gaps": [
            "Farkas evidence covers exact linear arithmetic; nonlinear, floating-point, and theorem-level convexity claims need separate routes.",
            "Rows that compute a linear conflict from a richer model must still replay that reduction independently.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows link to a committed SMT-LIB artifact or exact linear source constraints.",
                "The route regression emits UnsatFarkas evidence and rechecks it against the source assertions.",
                "A tamper test changes a multiplier or certificate row and the checker rejects it.",
            ],
        },
    },
    {
        "id": "bridge_exact_vs_floating_arithmetic",
        "title": "Exact Vs Floating Arithmetic",
        "field_ids": [
            "real_analysis",
            "linear_algebra",
            "numerical_analysis",
            "statistics",
            "optimization_and_convexity",
        ],
        "resource_status": "validated",
        "summary": (
            "Exact rational and integer resource rows are checked by "
            "symbolic or replayed arithmetic, not by tolerance-based "
            "floating-point computations. Floating-point roundoff, "
            "conditioning, stability, and asymptotic numerical claims stay "
            "outside the checked claim unless a separate numerical-honesty "
            "or QF_FP route is attached."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "bridge_qf_lra_farkas_anatomy",
            "curriculum_rationals",
        ],
        "unlocks": [
            "bridge_residual_bound",
            "bridge_lu_replay",
            "bridge_random_matrix_finite_moment",
            "field_numerical_analysis",
            "field_statistics",
        ],
        "decidability": "numerical",
        "axeyum_fragments": [
            "exact rational arithmetic",
            "QF_LRA",
            "Farkas certificate",
            "finite replay",
            "QF_FP / bit-vector lowering boundary",
            "numerical-honesty metadata",
        ],
        "example_packs": [
            (
                "rationals-lra-v0",
                "Exact rational order, midpoint, and infeasibility rows checked without floating-point tolerance.",
            ),
            (
                "real-analysis-rational-v0",
                "Bounded epsilon-delta and rational-neighborhood rows replayed over exact rationals.",
            ),
            (
                "numerical-linear-algebra-v0",
                "Residual and solution-box rows that are exact rational shadows of numerical linear algebra.",
            ),
            (
                "least-squares-regression-v0",
                "Normal-equation, residual, and bad RSS-improvement rows checked as exact rational linear algebra, not floating-point regression.",
            ),
            (
                "finite-root-finding-v0",
                "One-step bisection/Newton rows replayed exactly while convergence and floating-point stability remain horizon claims.",
            ),
            (
                "exact-statistical-tests-v0",
                "Finite exact-test p-value rows represented as rational sums rather than floating-point statistical approximations.",
            ),
        ],
        "proof_routes": [
            {
                "name": "exact rational replay plus numerical-honesty boundary",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and QF_LRA/Farkas route regressions where a bad exact-linear row is present",
                "lean_status": "not-required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/learn/math/numerical-linear-algebra-end-to-end.md",
                    "docs/learn/math/exact-statistical-tests-end-to-end.md",
                    "docs/foundational-resources/MATH-FIELDS.md",
                ],
                "notes": (
                    "The checked object is the exact rational row or exact "
                    "linear certificate. This route deliberately does not "
                    "certify IEEE rounding, conditioning, stability, or "
                    "statistical approximation behavior."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/learn/math/numerical-linear-algebra-end-to-end.md",
            "docs/learn/math/descriptive-statistics-regression-end-to-end.md",
            "docs/learn/math/exact-statistical-tests-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-RESOURCE-MASTER-PLAN.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
        ],
        "open_gaps": [
            "Exact rational replay does not prove floating-point roundoff, conditioning, stability, or convergence guarantees.",
            "QF_FP and numerical experiment metadata need their own trust boundary before floating-point resources can graduate.",
            "Learner pages must label exact rational shadows when a topic is normally taught numerically.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Exact arithmetic packs state whether the checked row is rational/integer replay, QF_LRA/Farkas evidence, or a numerical-honesty horizon.",
                "Consumer queries can find the exact-vs-floating boundary by field and text lookup.",
                "No resource pack uses tolerance language as proof evidence without a separate numerical-honesty schema.",
            ],
        },
    },
    {
        "id": "bridge_lp_objective_farkas",
        "title": "LP Objective Threshold Replay",
        "field_ids": ["optimization_and_convexity", "linear_algebra", "real_analysis"],
        "resource_status": "validated",
        "summary": (
            "An LP objective-threshold row checks a fixed exact-rational "
            "linear program, feasible witness replay, objective lower or "
            "upper thresholds, and infeasible threshold claims through "
            "checked QF_LRA/Farkas evidence."
        ),
        "prerequisites": [
            "bridge_qf_lra_farkas_anatomy",
            "bridge_counterexample_proof",
            "curriculum_linear_algebra",
            "curriculum_rationals",
        ],
        "unlocks": [
            "bridge_rational_convexity_shadow",
            "bridge_residual_bound",
            "family_exact_rational_farkas",
            "field_optimization_and_convexity",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "QF_LRA",
            "exact rational LP",
            "Farkas certificate",
            "finite model replay",
            "objective threshold",
        ],
        "example_packs": [
            (
                "linear-optimization-v0",
                "LP feasible-point replay, objective-threshold witness, and checked infeasible-threshold Farkas row.",
            ),
            (
                "linear-algebra-rational-v0",
                "Exact rational linear-system feasibility and infeasibility rows that supply the matrix vocabulary.",
            ),
            (
                "least-squares-regression-v0",
                "Normal-equation, bad-coefficient, and bad RSS-improvement rows that reduce fixed least-squares claims to exact linear constraints.",
            ),
            (
                "numerical-linear-algebra-v0",
                "Residual-bound and solution-box rows that reuse exact linear feasibility vocabulary.",
            ),
        ],
        "proof_routes": [
            {
                "name": "LP replay plus QF_LRA/Farkas objective-threshold certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/learn/math/linear-optimization-end-to-end.md",
                    "docs/learn/math/farkas-certificate-anatomy-end-to-end.md",
                    "docs/learn/math/linear-algebra-and-optimization.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker first replays the LP witness or "
                    "objective arithmetic; false threshold claims graduate "
                    "only when the exact linear conflict carries checked "
                    "Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/learn/math/linear-optimization-end-to-end.md",
            "docs/learn/math/farkas-certificate-anatomy-end-to-end.md",
            "docs/learn/math/linear-algebra-and-optimization.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Fixed LP threshold replay is not general linear-programming duality, strong duality, sensitivity analysis, or algorithm convergence.",
            "Primal-dual certificates, KKT sufficiency, and convex optimization theorems remain Lean-horizon until explicit kernel-checked artifacts exist.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the exact rational constraints, objective, threshold direction, and source arithmetic domain.",
                "The validator replays feasible witnesses and objective values from the source LP.",
                "Bad threshold rows carry source-linked QF_LRA/Farkas evidence before solver reuse is claimed.",
            ],
        },
    },
    {
        "id": "bridge_rational_convexity_shadow",
        "title": "Rational Convexity Gradient Shadow",
        "field_ids": [
            "optimization_and_convexity",
            "real_analysis",
            "linear_algebra",
            "numerical_analysis",
        ],
        "resource_status": "validated",
        "summary": (
            "A rational convexity-shadow row checks fixed midpoint/Jensen "
            "instances, finite second differences, affine monotonicity, exact "
            "gradient replay, Hessian-minor witnesses, finite gradient-descent, "
            "Armijo/Wolfe line-search, active-set QP, projected-gradient, and proximal-gradient steps, finite KKT "
            "stationarity/complementarity, and finite SDP primal/dual slack/gap "
            "rows over rational data while keeping "
            "general convex-analysis theorems separate."
        ),
        "prerequisites": [
            "bridge_lp_objective_farkas",
            "bridge_bounded_epsilon_delta_shadow",
            "curriculum_reals",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "bridge_inner_product_projection",
            "bridge_lean_horizon",
            "field_optimization_and_convexity",
            "field_real_analysis",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "QF_LRA",
            "NRA / polynomial constraints",
            "exact rational derivatives",
            "finite grid replay",
            "finite gradient descent replay",
            "finite line search replay",
            "finite Wolfe line search replay",
            "finite active-set QP replay",
            "finite projected gradient replay",
            "finite KKT replay",
            "finite SDP replay",
            "Farkas certificate",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "convexity-rational-v0",
                "Finite midpoint-convexity, second-difference, affine-threshold, bad midpoint-convexity, and bad affine-threshold rows.",
            ),
            (
                "multivariable-calculus-rational-v0",
                "Exact gradient, directional derivative, Jacobian, Hessian-minor, and bad-gradient rows.",
            ),
            (
                "least-squares-regression-v0",
                "Normal-equation, residual-orthogonality, RSS-improvement, and regression coefficient rows over exact rationals.",
            ),
            (
                "finite-separation-v0",
                "Finite convex-hull, supporting-face, and hyperplane-separation rows over exact rationals.",
            ),
            (
                "finite-kkt-v0",
                "Finite constrained-quadratic stationarity and complementary-slackness rows over exact rationals.",
            ),
            (
                "finite-active-set-qp-v0",
                "Finite active-face QP, inactive-constraint slack, and bad-free-gradient rows over exact rationals.",
            ),
            (
                "finite-gradient-descent-v0",
                "Finite exact quadratic gradient step, descent-bound, bad-decrease, bad step-coordinate, and bad descent-bound rows over exact rationals.",
            ),
            (
                "finite-line-search-v0",
                "Finite exact Armijo rejection/acceptance, bad-acceptance, bad descent-direction, and bad accepted-candidate rows over exact rationals.",
            ),
            (
                "finite-wolfe-line-search-v0",
                "Finite exact Wolfe minimizer, sufficient-decrease, curvature, bad-minimizer, and bad-curvature rows over exact rationals.",
            ),
            (
                "finite-projected-gradient-v0",
                "Finite exact projected-gradient interval projection and bad-projection rows over exact rationals.",
            ),
            (
                "finite-proximal-gradient-v0",
                "Finite exact L1 soft-threshold/composite-decrease proximal-gradient and bad proximal-gradient rows over exact rationals.",
            ),
            (
                "finite-sdp-v0",
                "Finite two-by-two PSD, trace, objective, slack, dual-gap, and checked bad-gap rows over exact rationals.",
            ),
            (
                "reals-rcf-shadow-v0",
                "Real-algebra shadow rows that separate bounded polynomial checks from full real-closed-field theorem coverage.",
            ),
            (
                "inner-product-spaces-rational-v0",
                "Projection, Gram matrix, and norm rows used by finite convex quadratic examples.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite convexity/gradient replay plus QF_LRA/Farkas bad-shadow certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/convexity-rational-end-to-end.md",
                    "docs/learn/math/multivariable-calculus-end-to-end.md",
                    "docs/learn/math/descriptive-statistics-regression-end-to-end.md",
                    "docs/learn/math/linear-algebra-and-optimization.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes midpoint values, grid "
                    "differences, gradients, Jacobians, Hessian minors, and "
                    "normal-equation residuals, finite gradient, Armijo/Wolfe line-search, active-set QP, projected-gradient, and proximal-gradient steps, finite KKT residuals, and "
                    "two-by-two SDP slack/objective/gap arithmetic exactly; false linearized "
                    "claims use checked Farkas evidence when promoted."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/convexity-rational-end-to-end.md",
            "docs/learn/math/multivariable-calculus-end-to-end.md",
            "docs/learn/math/descriptive-statistics-regression-end-to-end.md",
            "docs/learn/math/linear-algebra-and-optimization.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite rational convexity shadows do not prove Jensen's theorem, separation theorems, KKT sufficiency, SDP duality, or algorithm convergence.",
            "Positive-definite Hessian minors and finite midpoint checks are bounded witnesses, not general differentiable-convexity theorems unless a Lean route reconstructs the theorem.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite rational sample points, polynomial/function values, derivative data, or normal equations.",
                "The validator recomputes midpoint inequalities, second differences, gradients, Hessian minors, and residual equations exactly.",
                "General convex analysis, KKT, duality, and convergence claims are linked as Lean-horizon rows instead of counted as finite solver evidence.",
            ],
        },
    },
    {
        "id": "bridge_qf_uf_alethe_anatomy",
        "title": "QF_UF Alethe Certificate Anatomy",
        "field_ids": [
            "set_theory_and_foundations",
            "abstract_algebra",
            "linear_algebra",
            "topology",
        ],
        "resource_status": "validated",
        "summary": (
            "A QF_UF proof-object row isolates an equality or congruence "
            "conflict over finite functions, quotients, algebra maps, or "
            "preimage tables, then checks an Alethe proof rather than trusting "
            "the EUF search or an Ackermann rewrite."
        ),
        "prerequisites": [
            "bridge_finite_quantifier_expansion",
            "bridge_finite_model_replay",
            "curriculum_relations_and_functions",
        ],
        "unlocks": [
            "bridge_quotient_map",
            "bridge_homomorphism_preservation",
            "family_finite_algebra_alethe",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "QF_UF",
            "EUF congruence",
            "Alethe proof",
            "finite functions",
            "Lean partial",
        ],
        "example_packs": [
            (
                "equivalence-classes-v0",
                "Quotient-map congruence conflict with checked Alethe evidence and truncated-proof rejection.",
            ),
            (
                "relations-functions-v0",
                "Function single-valuedness and relation-table consistency rows that feed the same EUF route.",
            ),
            (
                "finite-algebra-homomorphisms-v0",
                "Homomorphism-preservation conflict over finite operation tables.",
            ),
            (
                "finite-continuous-maps-v0",
                "Preimage-membership consistency conflict over finite topological maps.",
            ),
            (
                "finite-tensor-products-v0",
                "Bilinearity and representative-consistency rows in the shared finite algebra family.",
            ),
        ],
        "proof_routes": [
            {
                "name": "QF_UF congruence conflict with checked Alethe proof",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/learn/math/alethe-certificate-anatomy-end-to-end.md",
                    "docs/learn/math/sets-relations-and-finite-structures.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                    "crates/axeyum-solver/tests/evidence.rs",
                ],
                "notes": (
                    "Finite table replay establishes the object being "
                    "discussed; the Alethe certificate separately checks the "
                    "isolated equality/congruence contradiction."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/learn/math/alethe-certificate-anatomy-end-to-end.md",
            "docs/learn/math/sets-relations-and-finite-structures.md",
            "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
            "crates/axeyum-solver/tests/evidence.rs",
        ],
        "open_gaps": [
            "The checked Alethe row proves the isolated EUF conflict, not arbitrary quotient, algebra, topology, or category-theory theorems.",
            "Rows that derive EUF constraints from finite tables must keep table replay and proof-object checking distinct.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows link to a committed QF_UF source artifact or exact equality assertions.",
                "The route regression emits Evidence::UnsatAletheProof and rechecks it independently.",
                "A tamper test removes or corrupts a proof command and the checker rejects it.",
            ],
        },
    },
    {
        "id": "bridge_qf_bv_bitblast_anatomy",
        "title": "QF_BV Bit-Blast Certificate Anatomy",
        "field_ids": ["number_theory", "abstract_algebra", "graph_theory", "discrete_math"],
        "resource_status": "validated",
        "summary": (
            "A QF_BV proof-object row keeps the fixed bit width as part of "
            "the mathematical claim, lowers the BV formula through AIG and "
            "Tseitin CNF, and accepts UNSAT only after the generated DRAT "
            "certificate rechecks."
        ),
        "prerequisites": [
            "bridge_boolean_cnf_lrat_anatomy",
            "curriculum_modular_arithmetic",
            "curriculum_fields",
        ],
        "unlocks": [
            "curriculum_number_theory",
            "curriculum_rings",
            "field_abstract_algebra",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "QF_BV",
            "bit-blast",
            "AIG",
            "Tseitin CNF",
            "DRAT",
        ],
        "example_packs": [
            (
                "finite-fields-v0",
                "Composite-modulus nonfield row with checked bit-blasted DRAT evidence and truncated-proof rejection.",
            ),
            (
                "finite-rings-v0",
                "Fixed finite ring-table contradiction where width is part of the educational claim.",
            ),
            (
                "graph-coloring-v0",
                "One-bit triangle coloring obstruction that exposes a separate BV route from source CNF.",
            ),
            (
                "number-theory-v0",
                "Quadratic nonresidue modulo 7 row checked through fixed-width bit-vector evidence.",
            ),
        ],
        "proof_routes": [
            {
                "name": "QF_BV bit-blast to CNF plus checked DRAT certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_bv_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
                    "docs/learn/math/qf-bv-bitblast-certificate-anatomy-end-to-end.md",
                    "docs/learn/math/graph-coloring-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_bv_routes.rs",
                    "crates/axeyum-solver/tests/evidence.rs",
                ],
                "notes": (
                    "The checked DRAT proof certifies the generated CNF. "
                    "The BV-to-AIG and Tseitin lowering steps remain explicit "
                    "trust steps until a Lean reconstruction covers the source shape."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
            "docs/learn/math/qf-bv-bitblast-certificate-anatomy-end-to-end.md",
            "docs/learn/math/graph-coloring-end-to-end.md",
            "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_bv_routes.rs",
            "crates/axeyum-solver/tests/evidence.rs",
        ],
        "open_gaps": [
            "QF_BV DRAT proves the generated CNF; broad bit-blast faithfulness and unbounded integer analogues remain separate proof work.",
            "Use this row only when the fixed width is mathematically meaningful, not as an incidental encoding of an unbounded theorem.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the bit width, source SMT-LIB artifact, and generated CNF/DRAT route.",
                "The route regression rechecks the DIMACS/DRAT pair and Evidence::check accepts the original obligation.",
                "A truncated or corrupted DRAT certificate is rejected by the focused tamper test.",
            ],
        },
    },
    {
        "id": "bridge_totality_conventions",
        "title": "Totality Conventions",
        "field_ids": [
            "logic_and_proof",
            "set_theory_and_foundations",
            "number_theory",
            "real_analysis",
            "numerical_analysis",
        ],
        "resource_status": "validated",
        "summary": (
            "Axeyum resources must say whether an operation is total by "
            "SMT/IR convention, guarded by an explicit side condition, or "
            "left to a frontend's trapping or undefined-behavior semantics. "
            "Division-by-zero, over-shifts, partial functions, and "
            "algorithm preconditions are educational boundaries, not hidden "
            "solver assumptions."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "bridge_qf_bv_bitblast_anatomy",
            "curriculum_naturals",
            "curriculum_rationals",
        ],
        "unlocks": [
            "curriculum_modular_arithmetic",
            "bridge_exact_vs_floating_arithmetic",
            "field_number_theory",
            "field_numerical_analysis",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "SMT-LIB total BV semantics",
            "QF_BV",
            "QF_LIA side conditions",
            "finite function-table replay",
            "frontend trapping/UB guards",
        ],
        "example_packs": [
            (
                "natural-arithmetic-v0",
                "Bounded natural-number rows whose finite domain and predecessor/negative boundaries are explicit.",
            ),
            (
                "integer-lia-v0",
                "Linear integer rows that encode impossible intervals and divisibility side conditions explicitly.",
            ),
            (
                "modular-arithmetic-v0",
                "Nonunit inverse rows that check the missing inverse through an explicit arithmetic obstruction.",
            ),
            (
                "number-theory-v0",
                "Fixed-modulus residue rows where the modulus, width, and bounded search space are part of the claim.",
            ),
            (
                "finite-fields-v0",
                "Prime-field and composite-modulus rows that separate total table replay from field-inverse side conditions.",
            ),
            (
                "relations-functions-v0",
                "Finite relation/function rows that check totality, single-valuedness, injectivity, and surjectivity from tables.",
            ),
        ],
        "proof_routes": [
            {
                "name": "total semantics plus explicit side-condition replay",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py plus QF_LIA/QF_BV route regressions for rows with arithmetic or bit-vector evidence",
                "lean_status": "partial",
                "sources": [
                    "docs/research/01-foundations/bv-semantics-and-partial-operations.md",
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/learn/math/number-systems-and-arithmetic.md",
                ],
                "notes": (
                    "The trusted-small-checking story depends on making "
                    "operation conventions explicit. Frontends that need "
                    "trapping, panic, or undefined-behavior semantics must "
                    "encode those guards as ordinary claims."
                ),
            }
        ],
        "source_refs": [
            "docs/research/01-foundations/bv-semantics-and-partial-operations.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/learn/math/number-systems-and-arithmetic.md",
            "docs/learn/math/sets-relations-and-finite-structures.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
        ],
        "open_gaps": [
            "The core total semantics do not model language-specific UB, traps, or panic behavior unless a frontend adds explicit guards.",
            "Integer/rational division examples need stated nonzero side conditions before they can be treated as field or algorithm claims.",
            "Broad Lean reconstruction for totality-sensitive bit-vector and arithmetic rewrites remains partial.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows involving division, shifts, inverses, predecessor-like operations, or partial functions state the operation convention or guard.",
                "Consumer queries can find totality convention rows by field and text lookup.",
                "Learner pages explain that `unknown` is a solver result, never a hidden operator value.",
            ],
        },
    },
    {
        "id": "bridge_gcd_divisibility_witness",
        "title": "GCD Divisibility Witness",
        "field_ids": ["number_theory", "abstract_algebra", "discrete_math"],
        "resource_status": "validated",
        "summary": (
            "A gcd/divisibility row checks the integer witness directly: "
            "recompute the gcd, Bezout identity, quotient witness, or fixed "
            "gcd non-divisibility obstruction before trusting any solver "
            "search. UNSAT rows graduate through checked QF_LIA/Diophantine "
            "evidence when the source claim is an integer linear equation."
        ),
        "prerequisites": [
            "bridge_totality_conventions",
            "bridge_counterexample_proof",
            "curriculum_integers",
            "curriculum_divisibility_and_euclid",
        ],
        "unlocks": [
            "curriculum_modular_arithmetic",
            "curriculum_number_theory",
            "family_integer_diophantine",
            "bridge_finite_torsion_homology_replay",
            "field_number_theory",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "integer gcd replay",
            "Bezout witness replay",
            "divisibility quotient replay",
            "QF_LIA / Diophantine",
            "UnsatDiophantine certificate",
            "finite modular arithmetic",
        ],
        "example_packs": [
            (
                "gcd-bezout-v0",
                "GCD/common-divisor replay, Bezout coefficient replay, quotient replay, and a checked gcd non-divisibility obstruction.",
            ),
            (
                "integer-lia-v0",
                "Fixed 2*x + 4*y = 3 infeasibility row checked by gcd non-divisibility evidence.",
            ),
            (
                "modular-arithmetic-v0",
                "Composite nonunit inverse row encoded as 2*b - 6*k = 1 and checked through the Diophantine route.",
            ),
            (
                "number-theory-v0",
                "Bounded residue, sum-of-squares, and fixed Diophantine witness rows that reuse gcd/divisibility vocabulary.",
            ),
        ],
        "proof_routes": [
            {
                "name": "gcd/divisibility replay plus QF_LIA/Diophantine certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lia_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/learn/math/number-systems-and-arithmetic.md",
                    "docs/learn/math/diophantine-certificate-anatomy-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                    "artifacts/examples/math/gcd-bezout-v0/smt2/diophantine-gcd-obstruction-conflict.smt2",
                    "artifacts/examples/math/integer-lia-v0/smt2/diophantine-gcd-obstruction-conflict.smt2",
                    "artifacts/examples/math/modular-arithmetic-v0/smt2/nonunit-inverse-diophantine-conflict.smt2",
                ],
                "notes": (
                    "The replay rows recompute the source arithmetic. The "
                    "solver-backed rows additionally parse committed SMT-LIB "
                    "artifacts and require independently checked "
                    "UnsatDiophantine evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/learn/math/number-systems-and-arithmetic.md",
            "docs/learn/math/gcd-bezout-end-to-end.md",
            "docs/learn/math/diophantine-certificate-anatomy-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
        ],
        "open_gaps": [
            "This bridge certifies fixed gcd/divisibility and linear Diophantine rows, not unique factorization, prime distribution, or general number-theory theorems.",
            "Modular, quotient-ring, or algebra packs that derive a gcd obstruction must still keep their source replay separate from the integer certificate.",
            "Lean reconstruction for the QF_LIA/Diophantine route remains partial at the family level.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the exact integers, coefficients, divisor, target, modulus, or quotient witness being checked.",
                "UNSAT rows link a committed SMT-LIB artifact and a math_resource_lia_routes regression when they claim certificate evidence.",
                "Learner pages explain gcd non-divisibility as the small checked obstruction rather than a black-box solver result.",
            ],
        },
    },
    {
        "id": "bridge_modular_crt_inverse_witness",
        "title": "Modular CRT And Inverse Witness",
        "field_ids": ["number_theory", "abstract_algebra", "discrete_math"],
        "resource_status": "validated",
        "summary": (
            "A modular-arithmetic row checks concrete residue data: CRT "
            "congruences, modular inverse witnesses, fixed residue searches, "
            "and nonunit inverse obstructions. The trusted object is the "
            "replayed congruence/inverse table or the checked "
            "QF_LIA/Diophantine gcd obstruction, not a general CRT or field "
            "theorem."
        ),
        "prerequisites": [
            "bridge_gcd_divisibility_witness",
            "bridge_totality_conventions",
            "curriculum_modular_arithmetic",
            "curriculum_divisibility_and_euclid",
        ],
        "unlocks": [
            "curriculum_fields",
            "curriculum_number_theory",
            "bridge_qf_bv_bitblast_anatomy",
            "field_abstract_algebra",
            "field_number_theory",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "finite modular arithmetic",
            "CRT witness replay",
            "modular inverse replay",
            "QF_LIA / Diophantine",
            "QF_BV fixed-width residues",
            "finite table replay",
        ],
        "example_packs": [
            (
                "modular-arithmetic-v0",
                "CRT witness replay, modular inverse replay, composite nonunit search, Fermat-style finite search, and checked nonunit Diophantine evidence.",
            ),
            (
                "number-theory-v0",
                "Bounded residue, quadratic nonresidue, and two-squares rows that reuse fixed-modulus witness vocabulary.",
            ),
            (
                "finite-fields-v0",
                "Prime-field inverse tables and composite-modulus nonfield rows that contrast units with nonunits at fixed width.",
            ),
            (
                "finite-ideals-v0",
                "Finite modular-ring ideal and quotient-ring table replay with representative congruence kept on the QF_UF/Alethe route.",
            ),
        ],
        "proof_routes": [
            {
                "name": "modular replay plus QF_LIA/Diophantine nonunit certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lia_routes modular_nonunit_inverse_emits_checked_diophantine_evidence",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
                    "docs/learn/math/modular-arithmetic-end-to-end.md",
                    "docs/learn/math/number-systems-and-arithmetic.md",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                    "artifacts/examples/math/modular-arithmetic-v0/smt2/nonunit-inverse-diophantine-conflict.smt2",
                ],
                "notes": (
                    "SAT witness rows recompute each residue equation. The "
                    "promoted UNSAT nonunit row lowers 2*b == 1 mod 6 to "
                    "2*b - 6*k = 1 and checks the gcd non-divisibility "
                    "certificate independently."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
            "docs/learn/math/modular-arithmetic-end-to-end.md",
            "docs/learn/math/number-systems-and-arithmetic.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
        ],
        "open_gaps": [
            "This bridge covers fixed modulus rows and concrete CRT/inverse witnesses, not the full Chinese remainder theorem or arbitrary ring/field structure.",
            "Composite-modulus and finite-field rows must keep unit/nonunit side conditions explicit and state any fixed bit width or finite carrier.",
            "Quotient-ring representative congruence remains a separate QF_UF/Alethe bridge; this row only points at it as adjacent modular-ring vocabulary.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the modulus, residues, inverse candidate, CRT congruences, and fixed finite search space.",
                "Nonunit UNSAT rows link the SMT-LIB artifact and focused math_resource_lia_routes regression before claiming checked evidence.",
                "Learner pages distinguish concrete witness replay from CRT, field, or quotient-ring theorem proof.",
            ],
        },
    },
    {
        "id": "bridge_finite_boolean_algebra",
        "title": "Finite Boolean Algebra",
        "field_ids": ["set_theory_and_foundations", "discrete_math", "logic_and_proof"],
        "resource_status": "validated",
        "summary": (
            "Finite Boolean-algebra rows make powerset operations explicit: "
            "membership, subset order, union, intersection, complement, "
            "meet/join tables, and small malformed identities are replayed or "
            "refuted over a finite carrier."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "curriculum_sets",
            "curriculum_cardinality",
        ],
        "unlocks": [
            "bridge_partition_relation_roundtrip",
            "bridge_finite_bijection_cardinality",
            "field_topology",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite sets",
            "finite Boolean algebra",
            "Bool / CNF",
            "finite lattices",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-sets-v0",
                "Union, intersection, subset, and malformed distributive-law rows over finite carriers.",
            ),
            (
                "finite-order-lattices-v0",
                "Powerset lattice, meet/join table replay, distributive replay, monotone-map rows, and checked bad top-element CNF evidence.",
            ),
            (
                "cardinality-principles-v0",
                "Finite powerset-cardinality row checked by explicit subset enumeration.",
            ),
            (
                "finite-topology-v0",
                "Finite topology open-set families reuse powerset and finite set-family vocabulary.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite Boolean-algebra replay plus Bool/CNF bad-identity certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-cnf --test math_resource_boolean_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/learn/math/finite-sets-end-to-end.md",
                    "docs/learn/math/finite-order-lattices-end-to-end.md",
                    "docs/learn/math/cardinality-principles-end-to-end.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                ],
                "notes": (
                    "Positive rows replay finite set operations directly. "
                    "Negative rows become solver-reuse candidates only when "
                    "the Bool/CNF source artifact and certificate are linked; "
                    "finite-order-lattices-v0 now includes a one-variable "
                    "bad top-element DRAT/LRAT row."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/learn/math/finite-sets-end-to-end.md",
            "docs/learn/math/finite-order-lattices-end-to-end.md",
            "docs/learn/math/cardinality-principles-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
        ],
        "open_gaps": [
            "These rows cover explicit finite powerset and set-family tables, not arbitrary Boolean-algebra or complete-lattice theorems.",
            "Any infinite set-theory claim must remain a theorem horizon until a proof-assistant route lands.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite carrier and encode set membership without implicit universe changes.",
                "The validator recomputes the Boolean operation or order relation from the row data.",
                "Malformed identities with solver evidence link to source Bool/CNF artifacts and checked certificates.",
                "Bad finite lattice set-family rows distinguish table replay from the checked CNF contradiction.",
            ],
        },
    },
    {
        "id": "bridge_partition_relation_roundtrip",
        "title": "Finite Partition Relation Roundtrip",
        "field_ids": ["set_theory_and_foundations", "discrete_math"],
        "resource_status": "validated",
        "summary": (
            "A finite partition can be checked as an equivalence relation, "
            "and a finite equivalence relation can be checked by reconstructing "
            "its blocks, quotient map, and relation table."
        ),
        "prerequisites": [
            "bridge_finite_boolean_algebra",
            "bridge_finite_quantifier_expansion",
            "curriculum_relations_and_functions",
        ],
        "unlocks": [
            "bridge_quotient_map",
            "bridge_qf_uf_alethe_anatomy",
            "curriculum_cardinality",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "finite partitions",
            "equivalence relations",
            "finite functions",
            "QF_UF",
            "finite replay",
        ],
        "example_packs": [
            (
                "equivalence-classes-v0",
                "Equivalence, quotient-map fiber, partition-roundtrip, bad-equivalence, and QF_UF congruence rows.",
            ),
            (
                "relations-functions-v0",
                "Relation-table and function-table rows that share finite law replay vocabulary.",
            ),
            (
                "finite-cardinality-v0",
                "Finite function and bijection rows that depend on explicit domain and codomain partitions.",
            ),
            (
                "function-composition-v0",
                "Composition and inverse-table rows that consume quotient and relation-table vocabulary.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite partition/relation replay with optional QF_UF conflict certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/learn/math/equivalence-classes-end-to-end.md",
                    "docs/learn/math/sets-relations-and-finite-structures.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The roundtrip itself is a finite checker computation. "
                    "Alethe evidence is reserved for isolated equality or "
                    "congruence conflicts extracted from the finite table."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/learn/math/equivalence-classes-end-to-end.md",
            "docs/learn/math/sets-relations-and-finite-structures.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite partition roundtrips do not prove arbitrary quotient construction theorems.",
            "Rows must keep the explicit carrier, relation table, and quotient-map table together so evidence can be replayed.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows include enough finite data to rebuild the partition from the relation and the relation from the partition.",
                "Bad rows identify the exact missing reflexive, symmetric, transitive, or quotient-consistency condition.",
                "Any QF_UF promotion links the source conflict and checked Alethe artifact separately from table replay.",
            ],
        },
    },
    {
        "id": "bridge_finite_image_preimage_inverse",
        "title": "Finite Image, Preimage, and Inverse Tables",
        "field_ids": ["set_theory_and_foundations", "discrete_math", "topology"],
        "resource_status": "validated",
        "summary": (
            "Finite function rows can replay image and preimage tables, "
            "check inverse tables for bijections, and reject claimed inverses "
            "for non-injective or non-surjective maps."
        ),
        "prerequisites": [
            "bridge_partition_relation_roundtrip",
            "bridge_finite_bijection_cardinality",
            "curriculum_relations_and_functions",
        ],
        "unlocks": [
            "bridge_continuity_preimage",
            "bridge_qf_uf_alethe_anatomy",
            "field_topology",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "finite functions",
            "image/preimage replay",
            "inverse tables",
            "QF_UF",
            "finite topology",
        ],
        "example_packs": [
            (
                "function-composition-v0",
                "Image/preimage replay, bijection inverse table, non-injective inverse rejection, and composition Alethe rows.",
            ),
            (
                "relations-functions-v0",
                "Function totality, single-valuedness, and bijection-table witness rows.",
            ),
            (
                "equivalence-classes-v0",
                "Quotient-map fiber rows that reuse preimage language.",
            ),
            (
                "finite-continuous-maps-v0",
                "Continuity-by-preimage rows over finite topological spaces.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite image/preimage/inverse replay with QF_UF conflict route",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/learn/math/function-composition-end-to-end.md",
                    "docs/learn/math/relations-functions-end-to-end.md",
                    "docs/learn/math/finite-topology-measure-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "Images, preimages, and inverse tables are recomputed from "
                    "the finite function graph. QF_UF evidence checks only the "
                    "small equality conflict attached to promoted bad rows."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/learn/math/function-composition-end-to-end.md",
            "docs/learn/math/relations-functions-end-to-end.md",
            "docs/learn/math/finite-topology-measure-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Rows cover explicit finite maps; general inverse-function, quotient, or continuity theorems require a theorem route.",
            "Topology rows must still prove that the preimage family is open in the finite topology, not only that a set table was computed.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows record domain, codomain, function graph, and claimed image, preimage, or inverse table.",
                "The validator recomputes the table and rejects non-total, multi-valued, or non-bijective claims as appropriate.",
                "Promoted conflicts link to checked QF_UF/Alethe evidence when equality reasoning is the reusable solver route.",
            ],
        },
    },
    {
        "id": "bridge_finite_bijection_cardinality",
        "title": "Finite Bijection and Cardinality",
        "field_ids": ["set_theory_and_foundations", "discrete_math", "logic_and_proof"],
        "resource_status": "validated",
        "summary": (
            "Finite cardinality rows turn injection, surjection, bijection, "
            "and pigeonhole-style obstructions into explicit finite function "
            "tables or finite Bool/CNF conflicts."
        ),
        "prerequisites": [
            "bridge_finite_quantifier_expansion",
            "bridge_boolean_cnf_lrat_anatomy",
            "curriculum_cardinality",
        ],
        "unlocks": [
            "bridge_cardinality_theorem_horizon",
            "curriculum_counting",
            "bridge_finite_image_preimage_inverse",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "finite cardinality",
            "finite functions",
            "Bool / CNF",
            "DRAT / LRAT",
            "finite replay",
        ],
        "example_packs": [
            (
                "finite-cardinality-v0",
                "Bijection, proper-subset injection, no-injection, no-surjection, and Cantor-diagonal horizon rows.",
            ),
            (
                "cardinality-principles-v0",
                "Inclusion-exclusion, disjoint union, double counting, powerset cardinality, and overlap-conflict rows.",
            ),
            (
                "relations-functions-v0",
                "Bijection-table witness row for finite function cardinality.",
            ),
            (
                "function-composition-v0",
                "Bijection inverse-table row using the same finite function vocabulary.",
            ),
            (
                "counting-v0",
                "Counting identities that reuse finite cardinality and explicit combinatorial enumeration.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite function-space replay plus Bool/CNF pigeonhole certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-cnf --test math_resource_boolean_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/learn/math/finite-cardinality-end-to-end.md",
                    "docs/learn/math/cardinality-principles-end-to-end.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                ],
                "notes": (
                    "Positive cardinality rows replay explicit maps or counts. "
                    "Negative finite obstructions graduate when the function "
                    "space is encoded with a source-linked checked certificate."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/learn/math/finite-cardinality-end-to-end.md",
            "docs/learn/math/cardinality-principles-end-to-end.md",
            "docs/learn/math/sets-relations-and-finite-structures.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
        ],
        "open_gaps": [
            "Finite bijection/cardinality rows do not prove infinite cardinal arithmetic or choice-sensitive statements.",
            "The row must state whether it is checking a concrete witness, rejecting a malformed witness, or proving a finite obstruction.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state domain size, codomain size, and the exact injection/surjection/bijection obligation.",
                "Witness rows replay the table; obstruction rows link to checked Bool/CNF evidence.",
                "Learner pages explicitly separate finite finite-domain cardinality from infinite theorem horizons.",
            ],
        },
    },
    {
        "id": "bridge_finite_counting_replay",
        "title": "Finite Counting Replay",
        "field_ids": [
            "discrete_math",
            "set_theory_and_foundations",
            "logic_and_proof",
            "probability_theory",
            "statistics",
        ],
        "resource_status": "validated",
        "summary": (
            "Finite counting rows state the universe, count expression, "
            "incidence table, coefficient, or finite function space being "
            "checked. The trusted object is exact replay of the finite count "
            "or a checked Bool/CNF or QF_LIA certificate for a malformed "
            "counting claim, not an asymptotic or unbounded combinatorics "
            "theorem."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "bridge_finite_bijection_cardinality",
            "bridge_boolean_cnf_lrat_anatomy",
            "curriculum_counting",
        ],
        "unlocks": [
            "bridge_tail_count_obstruction",
            "bridge_probability_mass_table",
            "family_boolean_cnf_lrat",
            "family_integer_diophantine",
            "field_discrete_math",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "finite counting",
            "finite enumeration",
            "finite function spaces",
            "Bool / CNF",
            "DRAT / LRAT",
            "QF_LIA / Diophantine",
            "finite replay",
        ],
        "example_packs": [
            (
                "counting-v0",
                "Permutation count, Pascal identity, finite pigeonhole enumeration, and source-linked PHP(3,2) DRAT/LRAT evidence.",
            ),
            (
                "proof-methods-refutation-v0",
                "Proof-by-refutation view of the same fixed PHP(3,2) Boolean contradiction.",
            ),
            (
                "cardinality-principles-v0",
                "Finite inclusion-exclusion, disjoint-union additivity, double counting, powerset cardinality, and overlap-additivity Diophantine evidence.",
            ),
            (
                "generating-functions-v0",
                "Fixed coefficient extraction, finite Cauchy-product replay, and checked coefficient-convolution contradiction.",
            ),
            (
                "finite-group-actions-v0",
                "Orbit-stabilizer and Burnside-style finite orbit-count replay with general group-action theorems kept as Lean horizon.",
            ),
            (
                "exact-statistical-tests-v0",
                "Exact finite binomial and hypergeometric count rows plus a checked tail-count contradiction.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite counting replay plus Bool/CNF and QF_LIA certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py plus math_resource_boolean_routes and math_resource_lia_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/learn/math/counting-pigeonhole-end-to-end.md",
                    "docs/learn/math/proof-object-anatomy-end-to-end.md",
                    "docs/learn/math/cardinality-principles-end-to-end.md",
                    "docs/learn/math/generating-functions-end-to-end.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                ],
                "notes": (
                    "Positive rows recompute finite counts, coefficients, or "
                    "orbit tables. Negative rows graduate when the source "
                    "artifact is parsed and independently checked by the "
                    "Boolean DRAT/LRAT or integer Diophantine route."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/learn/math/counting-pigeonhole-end-to-end.md",
            "docs/learn/math/graph-and-discrete-reasoning.md",
            "docs/learn/math/cardinality-principles-end-to-end.md",
            "docs/learn/math/generating-functions-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
        ],
        "open_gaps": [
            "Finite counting replay does not prove general binomial identities, recurrence schemas, asymptotic enumeration, or unbounded pigeonhole principles.",
            "Statistical count rows remain exact finite-table checks; approximations, sampling asymptotics, and floating-point implementations need separate numerical-honesty resources.",
            "General Burnside/Cauchy-Frobenius, generating-function extraction, and combinatorial theorem families remain Lean-horizon until kernel-checked proofs exist.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite carrier, count formula, table, coefficient, or function-space obligation being checked.",
                "Malformed finite-count rows link a source artifact and route regression before claiming checked evidence.",
                "Learner pages distinguish finite replay and finite proof certificates from unbounded combinatorics or asymptotic theorem claims.",
            ],
        },
    },
    {
        "id": "bridge_polynomial_coefficient_factor_replay",
        "title": "Polynomial Coefficient And Factor Replay",
        "field_ids": [
            "abstract_algebra",
            "real_analysis",
            "complex_analysis",
            "discrete_math",
            "numerical_analysis",
            "geometry",
        ],
        "resource_status": "validated",
        "summary": (
            "Polynomial replay rows fix a coefficient domain, degree bound, "
            "coefficient tuple, evaluation point, divisor, factor witness, or "
            "coefficient window. Axeyum can replay the finite arithmetic and "
            "check malformed coefficient, root, discriminant, product, or "
            "step claims through finite replay, QF_LIA/Diophantine, or "
            "QF_LRA/Farkas evidence; general polynomial theory stays in the "
            "Lean or algebraic-reasoning horizon."
        ),
        "prerequisites": [
            "curriculum_polynomials",
            "bridge_finite_model_replay",
            "bridge_finite_counting_replay",
            "bridge_bounded_family_asymptotic_boundary",
        ],
        "unlocks": [
            "bridge_characteristic_polynomial",
            "bridge_derivative_identity_shadow",
            "bridge_finite_circle_inversion_cyclic_replay",
            "bridge_complex_real_pair_transform",
            "bridge_lean_horizon",
            "field_abstract_algebra",
            "field_real_analysis",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "fixed-degree polynomials",
            "coefficient replay",
            "factor witness replay",
            "finite coefficient extraction",
            "QF_LIA / Diophantine",
            "QF_LRA / Farkas",
            "NRA / RCF shadow",
            "finite replay",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "polynomial-identities-v0",
                "Fixed-degree identities, factor theorem rows, rational-root replay, and checked false-root Diophantine evidence.",
            ),
            (
                "polynomial-factorization-rational-v0",
                "Rational polynomial division, factor products, Euclidean GCD, square-free replay, and checked discriminant obstruction.",
            ),
            (
                "generating-functions-v0",
                "Finite coefficient extraction, coefficient windows, and checked Cauchy-product convolution evidence.",
            ),
            (
                "finite-root-finding-v0",
                "Exact polynomial evaluation, bisection brackets, Newton steps, and checked bad-step plus bad-width rows.",
            ),
            (
                "calculus-algebraic-shadow-v0",
                "Fixed polynomial derivative replay and checked false-derivative row.",
            ),
            (
                "finite-circle-geometry-v0",
                "Circle-line and distance-product rows that consume fixed polynomial/rational coordinate equations.",
            ),
            (
                "finite-inversion-geometry-v0",
                "Inversion product rows over rational coordinates and fixed polynomial side conditions.",
            ),
            (
                "finite-cyclic-geometry-v0",
                "Ptolemy-style rational product rows with polynomial equality obligations.",
            ),
        ],
        "proof_routes": [
            {
                "name": "fixed polynomial replay plus QF_LIA/Diophantine and QF_LRA/Farkas certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py plus math_resource_lia_routes and math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/polynomial-identities-end-to-end.md",
                    "docs/learn/math/polynomial-factorization-end-to-end.md",
                    "docs/learn/math/generating-functions-end-to-end.md",
                    "docs/learn/math/finite-root-finding-end-to-end.md",
                    "docs/learn/math/calculus-shadows-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "Positive rows recompute coefficients, products, "
                    "remainders, GCD/factor witnesses, roots, or finite "
                    "coefficient windows. Negative rows graduate only when the "
                    "source artifact is checked by the integer Diophantine or "
                    "exact-rational Farkas route."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/polynomial-identities-end-to-end.md",
            "docs/learn/math/polynomial-factorization-end-to-end.md",
            "docs/learn/math/generating-functions-end-to-end.md",
            "docs/learn/math/finite-root-finding-end-to-end.md",
            "docs/learn/math/calculus-shadows-end-to-end.md",
            "docs/learn/math/finite-circle-geometry-end-to-end.md",
            "docs/learn/math/finite-inversion-geometry-end-to-end.md",
            "docs/learn/math/finite-cyclic-geometry-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Fixed-degree replay does not prove unique factorization, algebraic closure, arbitrary polynomial GCD correctness, or root-distribution theorems.",
            "Generating-function rows are finite coefficient windows; convergence and formal power-series theorem families remain Lean-horizon resources.",
            "Geometry and calculus rows reuse polynomial arithmetic only for fixed rational obligations, not global analytic or synthetic geometry theorems.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state coefficient domain, degree bound, coefficient tuple, evaluation point, divisor, factor witness, or coefficient window.",
                "Validators recompute evaluation, product, remainder, GCD/factor witness, derivative, or coefficient extraction before trusting a solver result.",
                "Malformed polynomial rows link source SMT-LIB artifacts and checked Diophantine or Farkas route regressions before solver reuse is claimed.",
                "General polynomial, analytic, and algebraic-closure claims stay linked to Lean-horizon or RCF/NRA resources.",
            ],
        },
    },
    {
        "id": "bridge_finite_graph_replay_obstruction",
        "title": "Finite Graph Replay And Obstruction",
        "field_ids": [
            "graph_theory",
            "discrete_math",
            "logic_and_proof",
            "probability_theory",
        ],
        "resource_status": "validated",
        "summary": (
            "Finite graph rows state the vertex set, edge relation, ordering, "
            "witness object, and bounded search space being checked. The "
            "trusted object is replay of coloring, reachability, traversal, "
            "matching, cut, or d-separation data, or a checked Boolean/CNF, "
            "QF_BV, or QF_LIA certificate for a fixed malformed graph claim."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "bridge_finite_counting_replay",
            "bridge_boolean_cnf_lrat_anatomy",
            "curriculum_sets",
            "curriculum_relations_and_functions",
        ],
        "unlocks": [
            "family_boolean_cnf_lrat",
            "bridge_qf_bv_bitblast_anatomy",
            "bridge_lean_horizon",
            "field_graph_theory",
            "field_discrete_math",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite graphs",
            "finite relation replay",
            "Bool / CNF",
            "DRAT / LRAT",
            "QF_BV fixed-width encodings",
            "QF_LIA counters",
            "finite enumeration",
        ],
        "example_packs": [
            (
                "graph-coloring-v0",
                "Finite coloring witness replay, triangle non-2-colorability Bool/CNF proof route, and one-bit QF_BV/DRAT route.",
            ),
            (
                "graph-reachability-v0",
                "BFS distance, deterministic DFS traversal, disconnected no-path CNF proof, and edge-cut separation replay.",
            ),
            (
                "graph-search-runtime-v0",
                "Finite BFS/DFS visited-count replay and checked QF_LIA arithmetic-DPLL rejection of a false DFS cost bound.",
            ),
            (
                "graph-matching-v0",
                "Finite matching replay, augmenting-path flip replay, and triangle no-perfect-matching CNF proof route.",
            ),
            (
                "graph-cut-v0",
                "Finite edge/vertex cut certificates, non-cut rejection, and bounded post-removal reachability CNF proof route.",
            ),
            (
                "graph-d-separation-v0",
                "Finite DAG d-separation path enumeration with conditioned-chain and unconditioned-collider CNF proof routes.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite graph replay plus Boolean, QF_BV, and QF_LIA certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py plus math_resource_boolean_routes, math_resource_bv_routes, and math_resource_lia_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/learn/math/graph-and-discrete-reasoning.md",
                    "docs/learn/math/graph-traversal-runtime-index.md",
                    "docs/learn/math/graph-coloring-end-to-end.md",
                    "docs/learn/math/graph-reachability-end-to-end.md",
                    "docs/learn/math/graph-search-runtime-end-to-end.md",
                    "docs/learn/math/graph-matching-end-to-end.md",
                    "docs/learn/math/graph-cut-end-to-end.md",
                    "docs/learn/math/graph-d-separation-end-to-end.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                    "crates/axeyum-solver/tests/math_resource_bv_routes.rs",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                ],
                "notes": (
                    "SAT rows replay explicit finite graph witnesses. UNSAT "
                    "rows graduate only when the source artifact is checked by "
                    "the relevant proof route; general graph theory and "
                    "asymptotic runtime remain theorem-horizon work."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/learn/math/graph-and-discrete-reasoning.md",
            "docs/learn/math/graph-traversal-runtime-index.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
            "crates/axeyum-solver/tests/math_resource_bv_routes.rs",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
        ],
        "open_gaps": [
            "Finite graph rows do not prove chromatic-number theorems, max-flow/min-cut, matching duality, graph minors, extremal graph theory, or unbounded graph-family claims.",
            "Traversal-cost rows are fixed finite counterexamples; asymptotic BFS/DFS complexity and average-case runtime remain Lean-horizon.",
            "D-separation rows are finite graph-theoretic checks and do not claim causal identification, do-calculus, or probabilistic graphical-model semantics.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state vertices, edges, direction/order conventions, witness object, and the bounded search space.",
                "Malformed graph rows link source CNF/SMT-LIB artifacts and route regressions before claiming checked evidence.",
                "Learner pages keep finite graph replay separate from graph-theorem, causal, and asymptotic-runtime claims.",
            ],
        },
    },
    {
        "id": "bridge_bounded_family_asymptotic_boundary",
        "title": "Bounded Family And Asymptotic Boundary",
        "field_ids": [
            "discrete_math",
            "graph_theory",
            "real_analysis",
            "numerical_analysis",
            "differential_equations_and_dynamical_systems",
        ],
        "resource_status": "validated",
        "summary": (
            "A bounded-family row fixes a finite graph size, recurrence "
            "prefix, coefficient window, time horizon, or iteration count and "
            "states exactly what Axeyum replays or certifies. It is the shared "
            "vocabulary for examples that are useful finite checks but not "
            "asymptotic runtime, convergence-rate, closed-form, or limiting "
            "distribution theorems."
        ),
        "prerequisites": [
            "bridge_finite_counting_replay",
            "bridge_finite_graph_replay_obstruction",
            "bridge_bounded_theorem_shadow",
            "curriculum_counting",
            "curriculum_sequences_and_limits",
        ],
        "unlocks": [
            "bridge_sequence_tail_shadow",
            "bridge_finite_dynamics_euler_replay",
            "bridge_lean_horizon",
            "field_discrete_math",
            "field_graph_theory",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite family enumeration",
            "bounded graph traversal counters",
            "finite recurrence prefixes",
            "QF_LIA counters",
            "QF_LRA exact rational recurrence checks",
            "finite replay",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "graph-search-runtime-v0",
                "Finite BFS/DFS traversal and checked bad DFS cost-bound rows, with asymptotic traversal theorems kept out of scope.",
            ),
            (
                "finite-recurrence-prefix-v0",
                "Finite Fibonacci and affine recurrence prefixes, replay-only bad source rows, and separate checked qf-lra recurrence proof rows.",
            ),
            (
                "generating-functions-v0",
                "Fixed coefficient extraction and finite Cauchy-product rows, with general generating-function identities kept as proof horizons.",
            ),
            (
                "bounded-dynamics-v0",
                "Fixed finite transition traces, threshold reachability, and invariant-bound rows.",
            ),
            (
                "finite-euler-method-v0",
                "Fixed-step explicit Euler transitions and finite error-table rows.",
            ),
            (
                "counting-v0",
                "Finite enumeration and pigeonhole rows that state the checked size rather than an asymptotic family theorem.",
            ),
        ],
        "proof_routes": [
            {
                "name": "bounded finite-family replay plus LIA/LRA certificates with Lean theorem horizon",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py plus math_resource_lia_routes and math_resource_lra_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/graph-traversal-runtime-index.md",
                    "docs/learn/math/finite-recurrence-prefix-end-to-end.md",
                    "docs/learn/math/generating-functions-end-to-end.md",
                    "docs/learn/math/bounded-dynamics-end-to-end.md",
                    "docs/learn/math/finite-euler-method-end-to-end.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes the listed family member, "
                    "prefix, count, or time step. Negative rows graduate only "
                    "when the bounded arithmetic conflict has checked LIA or "
                    "Farkas evidence; asymptotic and convergence claims remain "
                    "Lean-horizon resources."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/graph-traversal-runtime-index.md",
            "docs/learn/math/finite-recurrence-prefix-end-to-end.md",
            "docs/learn/math/generating-functions-end-to-end.md",
            "docs/learn/math/bounded-dynamics-end-to-end.md",
            "docs/learn/math/finite-euler-method-end-to-end.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "A checked finite family member does not prove an asymptotic runtime bound, recurrence closed form, convergence rate, or limiting theorem.",
            "Average-case algorithms, randomized processes, numerical stability, and convergence rates require separate benchmark, numerical-honesty, or Lean-horizon artifacts.",
            "When a bounded row becomes a solver regression, the source pack must still state the fixed size or horizon that was actually checked.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite family parameter, horizon, prefix, or iteration count.",
                "Validators recompute the listed finite member or exact arithmetic obligation before trusting any solver result.",
                "General asymptotic, closed-form, convergence, or limiting claims stay linked to Lean-horizon resources.",
            ],
        },
    },
    {
        "id": "bridge_cardinality_theorem_horizon",
        "title": "Cardinality Theorem Horizon",
        "field_ids": ["set_theory_and_foundations", "logic_and_proof", "discrete_math"],
        "resource_status": "validated",
        "summary": (
            "Finite cardinality examples can be replayed or certified today, "
            "while arbitrary infinite-cardinality theorems remain Lean-horizon "
            "items that need proof-assistant reconstruction."
        ),
        "prerequisites": [
            "bridge_finite_bijection_cardinality",
            "bridge_bounded_theorem_shadow",
            "curriculum_cardinality",
        ],
        "unlocks": [
            "bridge_lean_horizon",
            "field_set_theory_and_foundations",
        ],
        "decidability": "proof-horizon",
        "axeyum_fragments": [
            "Lean horizon",
            "finite cardinality",
            "theorem boundary",
            "proof assistant",
        ],
        "example_packs": [
            (
                "finite-cardinality-v0",
                "Cantor-diagonal horizon row adjacent to finite bijection and pigeonhole checks.",
            ),
            (
                "cardinality-principles-v0",
                "Cantor-Schroeder-Bernstein horizon row adjacent to finite cardinality-principle checks.",
            ),
            (
                "relations-functions-v0",
                "Finite function-table rows that define the checked side of the boundary.",
            ),
            (
                "finite-sets-v0",
                "Finite set rows that provide the explicit-carrier side of set-theory education.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite replay boundary plus Lean horizon metadata",
                "status": "replay-only",
                "checker": "scripts/validate-foundational-example-pack.py",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-cardinality-end-to-end.md",
                    "docs/learn/math/cardinality-principles-end-to-end.md",
                    "docs/learn/math/sets-relations-and-finite-structures.md",
                ],
                "notes": (
                    "Finite rows stay useful as executable examples and "
                    "solver regressions. Infinite-cardinality theorem claims "
                    "must be represented as Lean-horizon rows until the proof route exists."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-cardinality-end-to-end.md",
            "docs/learn/math/cardinality-principles-end-to-end.md",
            "docs/learn/math/sets-relations-and-finite-structures.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
        ],
        "open_gaps": [
            "No arbitrary infinite cardinality theorem is checked until a Lean route lands.",
            "Finite solver evidence must not be presented as a proof of Cantor, Cantor-Schroeder-Bernstein, choice, or cardinal arithmetic.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows label the finite checked artifact and the infinite theorem horizon separately.",
                "The learner page names the missing proof assistant route for each infinite-cardinality theorem.",
                "Any future promotion adds a source theorem statement and proof-checking route before changing the horizon status.",
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
                "bounded-monotone-sequence-v0",
                "Finite monotone-prefix, finite supremum, tail-gap, and separate checked qf-lra proof rows for monotone-convergence shadows.",
            ),
            (
                "finite-recurrence-prefix-v0",
                "Finite recurrence prefixes, companion-matrix replay, and checked affine-step refutations for recurrence-theory shadows.",
            ),
            (
                "finite-root-finding-v0",
                "Finite bisection/Newton replay and bad bisection-width checks for root-finding theorem shadows.",
            ),
            (
                "real-analysis-rational-v0",
                "Exact rational ball, delta, and neighborhood checks for analysis shadows.",
            ),
            (
                "metric-continuity-v0",
                "Finite metric continuity examples with checked bad-delta and bad-preimage rows plus an explicit general-continuity horizon.",
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
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
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
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
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
        "id": "bridge_metric_ball",
        "title": "Metric Ball",
        "field_ids": ["real_analysis", "topology"],
        "resource_status": "validated",
        "summary": (
            "A metric ball is represented as an exact finite distance-table "
            "query: choose a center and rational radius, then include exactly "
            "the points whose distance is strictly below the radius."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "curriculum_sets",
            "curriculum_reals",
        ],
        "unlocks": [
            "bridge_bounded_epsilon_delta_shadow",
            "bridge_continuity_preimage",
            "field_topology",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite metric spaces",
            "exact rational distance comparison",
            "LRA (exact rationals)",
            "finite topology",
        ],
        "example_packs": [
            (
                "finite-topology-v0",
                "Finite metric-ball witness checked by exact rational distance comparison.",
            ),
            (
                "real-analysis-rational-v0",
                "Nested rational neighborhoods and finite rational ball membership replay.",
            ),
            (
                "metric-continuity-v0",
                "Finite domain/output balls and checked bad open-ball preimage evidence used by bounded continuity examples.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite metric-ball replay",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py",
                "lean_status": "not-required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/learn/math/finite-topology-measure-end-to-end.md",
                    "docs/learn/math/analysis-topology-proof-horizons.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "docs/learn/math/metric-ball-epsilon-delta-index.md",
                ],
                "notes": (
                    "The finite checker recomputes the ball from the distance "
                    "table and rational radius; solver evidence is only needed "
                    "when a later negative row isolates a linear contradiction."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/learn/math/finite-topology-measure-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/learn/math/metric-ball-epsilon-delta-index.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
        ],
        "open_gaps": [
            "Finite metric-ball replay does not prove general metric-topology theorems.",
            "Rows involving arbitrary radii or quantified neighborhoods remain bounded shadows until Lean coverage exists.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Every metric-ball row records the finite carrier, distance table, center, and rational radius.",
                "The validator recomputes strict radius membership without floating-point tolerance.",
                "Learner pages distinguish finite ball replay from general metric-space topology.",
            ],
        },
    },
    {
        "id": "bridge_bounded_epsilon_delta_shadow",
        "title": "Bounded Epsilon-Delta Shadow",
        "field_ids": ["real_analysis", "topology", "logic_and_proof"],
        "resource_status": "validated",
        "summary": (
            "A continuity or limit theorem is approximated by fixed rational "
            "epsilon, delta, center, and finite sample data, with every "
            "distance and output-bound check recomputed exactly."
        ),
        "prerequisites": [
            "bridge_metric_ball",
            "bridge_bounded_theorem_shadow",
            "curriculum_sequences_and_limits",
        ],
        "unlocks": [
            "bridge_continuity_preimage",
            "bridge_lean_horizon",
            "curriculum_calculus",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "bounded epsilon-delta templates",
            "QF_LRA",
            "Farkas certificate",
            "finite rational neighborhoods",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "real-analysis-rational-v0",
                "Bounded linear epsilon-delta witness plus checked bad-delta QF_LRA/Farkas row.",
            ),
            (
                "metric-continuity-v0",
                "Finite metric continuity rows with checked bad-delta and bad-preimage strict output-bound conflicts.",
            ),
            (
                "sequence-limit-shadow-v0",
                "Bounded epsilon-N, finite Cauchy-tail, and bad reciprocal-tail checks for sequence-limit shadows.",
            ),
            (
                "bounded-monotone-sequence-v0",
                "Finite monotone-prefix plus replay-only bad upper-bound and bad tail-gap rows with separate checked qf-lra proof rows.",
            ),
        ],
        "proof_routes": [
            {
                "name": "bounded exact-rational epsilon-delta replay",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/metric-ball-epsilon-delta-index.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite/bounded rows are checked directly; bad linear "
                    "delta claims are promoted only when the final rational "
                    "inequality conflict carries rechecked Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/learn/math/metric-ball-epsilon-delta-index.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "A bounded epsilon-delta row proves only the listed finite sample and rational bounds.",
            "The fully quantified forall epsilon exists delta theorem remains a Lean horizon.",
            "Nonlinear side conditions need separate NRA/RCF or Lean treatment before graduation.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the fixed epsilon, delta, center, sample domain, and exact function table or formula.",
                "The validator rejects corrupted finite samples or bad output-bound claims.",
                "General continuity or limit theorem statements remain linked as Lean-horizon rows.",
            ],
        },
    },
    {
        "id": "bridge_rational_interval_replay",
        "title": "Rational Interval Replay",
        "field_ids": ["real_analysis", "topology", "numerical_analysis"],
        "resource_status": "validated",
        "summary": (
            "A rational interval row checks exact membership, containment, "
            "endpoint order, midpoint, and radius facts over named rational "
            "bounds, keeping completeness and arbitrary-neighborhood theorems "
            "out of the finite replay claim."
        ),
        "prerequisites": [
            "curriculum_rationals",
            "curriculum_reals",
            "bridge_metric_ball",
        ],
        "unlocks": [
            "bridge_bounded_epsilon_delta_shadow",
            "bridge_squeeze_shadow",
            "bridge_derivative_identity_shadow",
            "field_real_analysis",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "exact rational arithmetic",
            "interval containment",
            "LRA (exact rationals)",
            "finite replay",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "real-analysis-rational-v0",
                "Exact rational interval, ball, and bounded epsilon-delta rows.",
            ),
            (
                "rationals-lra-v0",
                "Rational density, trichotomy, and order/transitivity replay.",
            ),
            (
                "reals-rcf-shadow-v0",
                "Ordered-field midpoint replay and small real-algebra shadows.",
            ),
            (
                "finite-root-finding-v0",
                "Bisection interval and width rows checked over exact rational endpoints.",
            ),
        ],
        "proof_routes": [
            {
                "name": "exact rational interval replay plus QF_LRA/Farkas bad-bound certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/real-analysis-rational-end-to-end.md",
                    "docs/learn/math/finite-root-finding-end-to-end.md",
                    "docs/learn/math/metric-ball-epsilon-delta-index.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes rational endpoint and "
                    "membership facts exactly. Bad interval or width claims "
                    "graduate only when their final linear conflict has "
                    "checked Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/real-analysis-rational-end-to-end.md",
            "docs/learn/math/finite-root-finding-end-to-end.md",
            "docs/learn/math/metric-ball-epsilon-delta-index.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Rational interval replay does not prove real completeness, nested-interval theorems, or compactness.",
            "Floating-point interval arithmetic and rounding guarantees require separate numerical-honesty resources.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state exact rational endpoints, included values, and any claimed midpoint, radius, or width.",
                "The validator recomputes interval membership or endpoint arithmetic from source values.",
                "General real-interval theorems stay linked as Lean horizons.",
            ],
        },
    },
    {
        "id": "bridge_sequence_tail_shadow",
        "title": "Sequence Tail Shadow",
        "field_ids": ["real_analysis", "topology", "discrete_math"],
        "resource_status": "validated",
        "summary": (
            "A sequence-tail shadow fixes a finite prefix or tail, exact "
            "rational values, a proposed limit or recurrence rule, and one "
            "bounded inequality to replay without claiming full convergence."
        ),
        "prerequisites": [
            "curriculum_sequences_and_limits",
            "bridge_rational_interval_replay",
            "bridge_bounded_epsilon_delta_shadow",
        ],
        "unlocks": [
            "bridge_cauchy_tail_shadow",
            "bridge_squeeze_shadow",
            "bridge_lean_horizon",
            "field_real_analysis",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite sequence replay",
            "bounded epsilon-N templates",
            "LRA (exact rationals)",
            "finite recurrence prefixes",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "sequence-limit-shadow-v0",
                "Finite epsilon-tail, limit-counterexample, Cauchy-tail, and bad reciprocal-tail rows.",
            ),
            (
                "bounded-monotone-sequence-v0",
                "Finite monotone-prefix, supremum, tail-gap, and bad-bound rows.",
            ),
            (
                "finite-recurrence-prefix-v0",
                "Finite recurrence prefixes, companion-matrix replay, and bad finite-value rows.",
            ),
            (
                "generating-functions-v0",
                "Finite coefficient and recurrence/generating-function prefix rows.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite sequence-prefix replay plus QF_LRA/Farkas bad-tail certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/sequence-limit-shadow-end-to-end.md",
                    "docs/learn/math/bounded-monotone-sequence-end-to-end.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes the listed sequence values "
                    "and tail inequalities. General epsilon-N, monotone, or "
                    "recurrence convergence is a Lean horizon."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/sequence-limit-shadow-end-to-end.md",
            "docs/learn/math/bounded-monotone-sequence-end-to-end.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite sequence-tail replay is not convergence, Cauchy completeness, monotone convergence, or asymptotic analysis.",
            "Closed forms and recurrence theorem proofs require induction or Lean reconstruction beyond finite prefix data.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite index range, exact sequence formula or table, proposed bound, and claimed tail property.",
                "The validator recomputes listed values and exact inequalities.",
                "Theorem-level convergence claims remain Lean-horizon rows.",
            ],
        },
    },
    {
        "id": "bridge_cauchy_tail_shadow",
        "title": "Cauchy Tail Shadow",
        "field_ids": ["real_analysis", "topology"],
        "resource_status": "validated",
        "summary": (
            "A Cauchy-tail shadow enumerates one finite tail, computes all "
            "pairwise exact rational distances, and rejects only bounded bad "
            "threshold claims unless a general completeness proof exists."
        ),
        "prerequisites": [
            "bridge_sequence_tail_shadow",
            "bridge_bounded_epsilon_delta_shadow",
            "curriculum_reals",
        ],
        "unlocks": [
            "bridge_lean_horizon",
            "field_topology",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite pairwise distance enumeration",
            "LRA (exact rationals)",
            "QF_LRA",
            "Farkas certificate",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "sequence-limit-shadow-v0",
                "Bounded Cauchy-tail no-counterexample row and bad reciprocal-tail strict-bound rejection.",
            ),
            (
                "bounded-monotone-sequence-v0",
                "Finite tail-gap replay and separate checked qf-lra bad-tail-gap proof row.",
            ),
            (
                "real-analysis-rational-v0",
                "Bounded rational-ball and epsilon-delta rows that share exact distance comparisons.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite pairwise-tail replay plus QF_LRA/Farkas threshold certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/sequence-limit-shadow-end-to-end.md",
                    "docs/learn/math/analysis-topology-proof-horizons.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker computes the maximum pairwise tail "
                    "distance exactly; malformed threshold claims use checked "
                    "Farkas evidence, while Cauchy completeness stays in Lean."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/sequence-limit-shadow-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "A finite no-counterexample tail is not a proof that a sequence is Cauchy.",
            "Equivalence between Cauchy and convergent sequences over complete spaces remains a Lean horizon.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite tail values, epsilon, farthest pair, and exact maximum distance.",
                "The validator enumerates every pair and recomputes the max distance.",
                "General Cauchy/completeness theorems remain linked as proof-horizon resources.",
            ],
        },
    },
    {
        "id": "bridge_squeeze_shadow",
        "title": "Squeeze Shadow",
        "field_ids": ["real_analysis", "logic_and_proof"],
        "resource_status": "validated",
        "summary": (
            "A squeeze-shadow row checks one bounded side-condition diagram: "
            "lower and upper rational expressions bound a middle expression at "
            "fixed sample points, while the full squeeze theorem remains Lean-only."
        ),
        "prerequisites": [
            "bridge_rational_interval_replay",
            "bridge_sequence_tail_shadow",
            "curriculum_reals",
        ],
        "unlocks": [
            "bridge_derivative_identity_shadow",
            "bridge_integration_horizon",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "exact rational inequalities",
            "bounded polynomial side conditions",
            "LRA (exact rationals)",
            "NRA / polynomial constraints",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "real-analysis-rational-v0",
                "Finite squeeze-style polynomial side conditions and checked bad-delta row.",
            ),
            (
                "sequence-limit-shadow-v0",
                "Finite tail rows that use exact rational bounds without proving general convergence.",
            ),
            (
                "bounded-monotone-sequence-v0",
                "Finite tail-gap rows that demonstrate bounded sequence inequalities.",
            ),
        ],
        "proof_routes": [
            {
                "name": "bounded inequality replay with Lean theorem horizon",
                "status": "replay-only",
                "checker": "scripts/validate-foundational-example-pack.py",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/real-analysis-rational-end-to-end.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                ],
                "notes": (
                    "The current rows replay bounded side conditions exactly. "
                    "The general squeeze theorem needs a Lean proof route "
                    "before it can be advertised as theorem evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/real-analysis-rational-end-to-end.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
        ],
        "open_gaps": [
            "Finite squeeze side conditions do not prove the quantified squeeze theorem.",
            "Nonlinear symbolic side conditions need RCF/NRA or Lean support before broader promotion.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the lower, middle, and upper expressions or exact table values.",
                "The validator checks the finite inequality chain exactly at the listed samples.",
                "The general squeeze theorem stays a Lean-horizon dependency.",
            ],
        },
    },
    {
        "id": "bridge_derivative_identity_shadow",
        "title": "Derivative Identity Shadow",
        "field_ids": ["real_analysis", "numerical_analysis"],
        "resource_status": "validated",
        "summary": (
            "A derivative-identity shadow differentiates a fixed polynomial or "
            "rational expression symbolically, evaluates exact rational sample "
            "points, and isolates bad derivative or gradient claims as small "
            "linear contradictions when possible."
        ),
        "prerequisites": [
            "bridge_rational_interval_replay",
            "bridge_squeeze_shadow",
            "curriculum_polynomials",
        ],
        "unlocks": [
            "bridge_integration_horizon",
            "bridge_rational_convexity_shadow",
            "field_numerical_analysis",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "symbolic polynomial differentiation",
            "exact rational evaluation",
            "QF_LRA",
            "Farkas certificate",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "calculus-algebraic-shadow-v0",
                "One-variable polynomial derivative replay and checked false-derivative row.",
            ),
            (
                "multivariable-calculus-rational-v0",
                "Bivariate gradient and Hessian replay plus checked bad-gradient row.",
            ),
            (
                "finite-gradient-descent-v0",
                "Exact quadratic gradient rows used by finite descent-step checks.",
            ),
            (
                "finite-root-finding-v0",
                "Newton-step rows that reuse exact derivative evaluation.",
            ),
        ],
        "proof_routes": [
            {
                "name": "symbolic derivative replay plus QF_LRA/Farkas bad-value certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/calculus-shadows-end-to-end.md",
                    "docs/learn/math/multivariable-calculus-end-to-end.md",
                    "docs/learn/math/finite-root-finding-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The validator recomputes the derivative formula and exact "
                    "sample values. Bad finite derivative or gradient claims "
                    "use checked Farkas evidence; differentiability theorems "
                    "remain Lean horizons."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/calculus-shadows-end-to-end.md",
            "docs/learn/math/multivariable-calculus-end-to-end.md",
            "docs/learn/math/finite-root-finding-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite derivative replay does not prove differentiability from limits, product/chain rules in general, MVT, or FTC.",
            "Non-polynomial derivative rules and analytic theorem reconstruction remain Lean horizons.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the source expression, derivative expression, sample point, and exact value.",
                "The validator recomputes symbolic derivative samples exactly.",
                "General calculus theorems stay linked as Lean-horizon rows.",
            ],
        },
    },
    {
        "id": "bridge_integration_horizon",
        "title": "Integration Horizon",
        "field_ids": ["real_analysis", "measure_theory", "probability_theory", "numerical_analysis"],
        "resource_status": "validated",
        "summary": (
            "An integration-horizon row separates exact finite sums, simple "
            "function integrals, and Riemann-sum shadows from theorem-level "
            "integrability, convergence, and fundamental-theorem claims."
        ),
        "prerequisites": [
            "bridge_finite_product_integration",
            "bridge_derivative_identity_shadow",
            "curriculum_calculus",
        ],
        "unlocks": [
            "bridge_conditional_expectation",
            "bridge_lean_horizon",
            "field_measure_theory",
        ],
        "decidability": "proof-horizon",
        "axeyum_fragments": [
            "finite weighted sums",
            "Riemann-sum shadows",
            "simple-function integrals",
            "QF_LRA",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "calculus-riemann-sum-v0",
                "Fixed partition Riemann-sum replay and checked false-integral row.",
            ),
            (
                "finite-integration-v0",
                "Finite simple-function integral, indicator integral, expectation, and bad expectation rows.",
            ),
            (
                "finite-product-measure-v0",
                "Finite product table, marginal, and finite Fubini-shadow rows.",
            ),
            (
                "real-analysis-rational-v0",
                "Exact rational side conditions used as bounded analysis prerequisites.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite integral replay plus Lean-horizon theorem boundary",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/calculus-shadows-end-to-end.md",
                    "docs/learn/math/finite-integration-end-to-end.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "Finite sums and simple-function integrals are replayed "
                    "exactly and bad finite values can carry Farkas evidence. "
                    "General integrability, convergence theorems, and FTC "
                    "remain Lean-horizon dependencies."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/calculus-shadows-end-to-end.md",
            "docs/learn/math/finite-integration-end-to-end.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite Riemann sums and simple-function integrals do not prove Riemann/Lebesgue integrability or convergence theorems.",
            "FTC, dominated convergence, Fubini/Tonelli, and almost-everywhere integration remain Lean horizons.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite partition, atom table, function values, and exact sum domain.",
                "The validator recomputes each finite integral or Riemann-sum value exactly.",
                "The theorem-level integration claim is explicitly marked Lean-horizon.",
            ],
        },
    },
    {
        "id": "bridge_compactness_shadow",
        "title": "Compactness Shadow",
        "field_ids": ["topology", "set_theory_and_foundations", "real_analysis"],
        "resource_status": "validated",
        "summary": (
            "Compactness is represented by finite open-cover, subcover, "
            "minimal-subcover, and finite-intersection checks over an explicit "
            "finite topology, with general compactness theorems left to Lean."
        ),
        "prerequisites": [
            "bridge_bounded_theorem_shadow",
            "bridge_metric_ball",
            "curriculum_sets",
        ],
        "unlocks": [
            "bridge_lean_horizon",
            "field_topology",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite topology",
            "finite open covers",
            "Bool / CNF",
            "DRAT / LRAT",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-compactness-v0",
                "Finite open-cover, subcover, minimality, finite-intersection, and bad-cover rows.",
            ),
            (
                "finite-topology-v0",
                "Finite topology axioms and metric-ball replay that compactness rows build on.",
            ),
            (
                "finite-continuous-maps-v0",
                "Finite continuous-map rows that name compactness-preservation as a horizon.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite open-cover replay plus Bool/CNF bad-cover certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-cnf --test math_resource_boolean_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/metric-ball-epsilon-delta-index.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                ],
                "notes": (
                    "Finite cover and subcover rows are replayed from source "
                    "sets; the promoted bad-cover row separately checks the "
                    "isolated Boolean contradiction with DRAT/LRAT."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-compactness-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/learn/math/metric-ball-epsilon-delta-index.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
        ],
        "open_gaps": [
            "Finite open-cover replay is not Heine-Borel, arbitrary topological compactness, or general finite-intersection-property equivalence.",
            "Continuous-image compactness and compactness in metric or uniform spaces remain Lean horizons.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite universe, topology, cover family, and listed subcover or closed family.",
                "The validator recomputes cover unions, subcover coverage, and finite intersections.",
                "Bad-cover rows carry source-linked checked DRAT/LRAT evidence before solver reuse is claimed.",
            ],
        },
    },
    {
        "id": "bridge_connectedness_shadow",
        "title": "Connectedness Shadow",
        "field_ids": ["topology", "set_theory_and_foundations", "real_analysis"],
        "resource_status": "validated",
        "summary": (
            "Connectedness is represented by finite clopen-subset enumeration "
            "and open-separation replay over explicit finite topologies, with "
            "general connectedness theorems kept as Lean horizons."
        ),
        "prerequisites": [
            "bridge_bounded_theorem_shadow",
            "curriculum_sets",
            "field_topology",
        ],
        "unlocks": [
            "bridge_lean_horizon",
            "field_topology",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite topology",
            "clopen subset enumeration",
            "Bool / CNF",
            "DRAT / LRAT",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-connectedness-v0",
                "Finite connected-space, separation, clopen-subset, and bad-connectedness rows.",
            ),
            (
                "finite-topology-v0",
                "Finite topology axioms that connectedness rows depend on.",
            ),
            (
                "finite-continuous-maps-v0",
                "Finite continuous-map rows that name connectedness-preservation as a horizon.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite clopen replay plus Bool/CNF bad-connectedness certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-cnf --test math_resource_boolean_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/metric-ball-epsilon-delta-index.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                ],
                "notes": (
                    "The finite checker enumerates all subsets and recomputes "
                    "clopen/open-separation facts; the promoted negative row "
                    "also checks the isolated Boolean contradiction with DRAT/LRAT."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-connectedness-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/learn/math/metric-ball-epsilon-delta-index.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
        ],
        "open_gaps": [
            "Finite connectedness replay does not prove interval connectedness, path-connectedness implications, or connected components in arbitrary spaces.",
            "Continuous-image connectedness remains a Lean-horizon theorem until a no-sorry route exists.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite universe, topology, candidate separation, or clopen subset.",
                "The validator enumerates subsets and recomputes open, closed, clopen, and separation facts.",
                "Bad-connectedness rows carry source-linked checked DRAT/LRAT evidence before solver reuse is claimed.",
            ],
        },
    },
    {
        "id": "bridge_continuity_preimage",
        "title": "Continuity By Open Preimage",
        "field_ids": ["topology", "set_theory_and_foundations", "real_analysis"],
        "resource_status": "validated",
        "summary": (
            "Finite topological continuity is checked by recomputing the "
            "preimage of every codomain-open set through a total function table "
            "and requiring each preimage to be open in the domain topology."
        ),
        "prerequisites": [
            "bridge_metric_ball",
            "bridge_bounded_epsilon_delta_shadow",
            "curriculum_relations_and_functions",
        ],
        "unlocks": [
            "bridge_compactness_shadow",
            "bridge_connectedness_shadow",
            "bridge_lean_horizon",
            "field_topology",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite functions",
            "finite topology",
            "open-set preimage enumeration",
            "Bool / enumeration",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-continuous-maps-v0",
                "Finite continuity, open-preimage, homeomorphism, and bad-continuity rows.",
            ),
            (
                "metric-continuity-v0",
                "Metric epsilon-delta and open-ball preimage rows, including a checked bad-preimage strict-bound certificate.",
            ),
            (
                "relations-functions-v0",
                "Finite function-table totality and single-valuedness checks used by preimage replay.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite open-preimage replay",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-continuous-maps-end-to-end.md",
                    "docs/learn/math/metric-ball-epsilon-delta-index.md",
                ],
                "notes": (
                    "The validator recomputes every listed preimage from the "
                    "function table and checks openness in the domain; malformed "
                    "metric open-ball membership rows can isolate a small "
                    "QF_LRA/Farkas strict-bound contradiction, while general "
                    "continuity theorems remain Lean-horizon."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-continuous-maps-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/learn/math/metric-ball-epsilon-delta-index.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
        ],
        "open_gaps": [
            "Finite preimage replay does not prove continuous-image, homeomorphism-invariance, compactness-preservation, or connectedness-preservation theorems.",
            "Only fixed finite bad-preimage rows with source-linked artifacts are certificate-backed; arbitrary topological preservation remains proof-horizon.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state domain/codomain finite topologies and the total function table.",
                "The validator recomputes each codomain-open preimage and rejects non-open preimages.",
                "General topological continuity theorems remain linked as Lean-horizon rows.",
            ],
        },
    },
    {
        "id": "bridge_finite_topology_operator_homeomorphism",
        "title": "Finite Topology Operators And Homeomorphism Replay",
        "field_ids": ["topology", "set_theory_and_foundations", "real_analysis"],
        "resource_status": "validated",
        "summary": (
            "Finite topology rows state an explicit finite universe and "
            "open-set family, then replay interior, closure, continuity, "
            "bijectivity, and inverse-continuity checks by enumeration. The "
            "trusted object is exact finite replay plus checked Bool/CNF or "
            "QF_UF/Alethe evidence for source-level malformed rows; arbitrary "
            "homeomorphism-invariance and closure-operator theorems remain "
            "Lean-horizon."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "bridge_metric_ball",
            "bridge_continuity_preimage",
            "bridge_finite_image_preimage_inverse",
            "curriculum_sets",
            "curriculum_relations_and_functions",
        ],
        "unlocks": [
            "bridge_compactness_shadow",
            "bridge_connectedness_shadow",
            "bridge_finite_quotient_topology_replay",
            "bridge_finite_specialization_order_replay",
            "bridge_finite_boundary_operator_replay",
            "bridge_finite_chain_homology_replay",
            "bridge_finite_torsion_homology_replay",
            "bridge_finite_cohomology_replay",
            "bridge_finite_universal_coefficient_shadow",
            "bridge_finite_cup_product_replay",
            "field_topology",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite topology",
            "finite closure/interior replay",
            "finite functions",
            "homeomorphism replay",
            "Bool / CNF",
            "QF_UF / Alethe",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-topology-v0",
                "Finite topology axioms, closure/interior replay, metric-ball replay, and checked bad empty-open row.",
            ),
            (
                "finite-continuous-maps-v0",
                "Finite continuity, open-preimage replay, homeomorphism replay, checked bad-continuity row, and bad-homeomorphism rejection.",
            ),
            (
                "finite-compactness-v0",
                "Finite open-cover rows that depend on the same explicit finite topology operators.",
            ),
            (
                "finite-connectedness-v0",
                "Finite clopen and open-separation rows that depend on the same explicit finite topology operators.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite topology replay plus checked bad-row certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py, cargo test -p axeyum-cnf --test math_resource_boolean_routes, and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-topology-end-to-end.md",
                    "docs/learn/math/finite-continuous-maps-end-to-end.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes open-set axioms, "
                    "interior/closure, preimages, bijections, and inverse "
                    "continuity. Malformed topology rows use checked Bool/CNF "
                    "evidence; malformed preimage rows use checked "
                    "QF_UF/Alethe evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-topology-end-to-end.md",
            "docs/learn/math/finite-continuous-maps-end-to-end.md",
            "docs/learn/math/finite-compactness-end-to-end.md",
            "docs/learn/math/finite-connectedness-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "artifacts/examples/math/finite-topology-v0/cnf/bad-empty-open-rejected.cnf",
            "artifacts/examples/math/finite-continuous-maps-v0/smt2/bad-preimage-membership-alethe-conflict.smt2",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite closure/interior replay checks one explicit topology and subset; it does not prove Kuratowski closure axioms or arbitrary closure/interior theorem schemas.",
            "Finite homeomorphism replay checks one finite bijection with continuity in both directions; it does not prove homeomorphism invariance of compactness, connectedness, homology, or other topological invariants.",
            "Additional homeomorphism or closure-operator rows should land only when they add distinct Boolean, EUF, or Lean-reconstruction pressure.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite universe, open-set family, subset, function table, inverse table, and the specific topological property being replayed.",
                "The validator recomputes topology axioms, interior, closure, preimages, bijectivity, continuity, and inverse continuity exactly.",
                "Bad topology or preimage rows link source artifacts and route regressions before claiming checked evidence.",
                "General topology and homeomorphism-invariance theorem claims remain Lean-horizon until kernel-checked proof routes exist.",
            ],
        },
    },
    {
        "id": "bridge_finite_quotient_topology_replay",
        "title": "Finite Quotient Topology Replay",
        "field_ids": ["topology", "set_theory_and_foundations", "discrete_math"],
        "resource_status": "validated",
        "summary": (
            "Finite quotient-topology rows state an explicit source topology, "
            "surjective quotient map, quotient fibers, and quotient open-set "
            "family. The trusted object is exact finite replay of fibers, "
            "same-fiber equivalence pairs, preimage-open quotient topology, "
            "and saturated-open images, plus checked QF_UF/Alethe evidence for "
            "malformed representative and quotient-open claims."
        ),
        "prerequisites": [
            "bridge_finite_topology_operator_homeomorphism",
            "bridge_quotient_map",
            "bridge_partition_relation_roundtrip",
            "bridge_finite_image_preimage_inverse",
            "curriculum_sets",
            "curriculum_relations_and_functions",
        ],
        "unlocks": [
            "field_topology",
            "field_set_theory_and_foundations",
            "field_discrete_math",
            "bridge_finite_specialization_order_replay",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite topology",
            "finite quotient maps",
            "finite equivalence relations",
            "finite preimage replay",
            "QF_UF / Alethe",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-quotient-topology-v0",
                "Finite quotient-map fibers, quotient topology by preimage-open replay, saturated-open image replay, and checked bad representative/open Alethe rows.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite quotient-topology replay plus QF_UF/Alethe representative/open certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-quotient-topology-end-to-end.md",
                    "docs/learn/math/analysis-topology-proof-horizons.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The validator recomputes source topology axioms, "
                    "surjectivity, fibers, same-fiber equivalence pairs, "
                    "quotient-open subsets by preimage enumeration, and "
                    "saturated-open image/preimage data. The malformed "
                    "representative and quotient-open rows graduate only "
                    "because the isolated equality and open-status "
                    "contradictions have checked Alethe evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md",
            "docs/foundational-resources/MATH-CURRICULUM-RESOURCE-BUILD-SEQUENCE.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-topology-end-to-end.md",
            "docs/learn/math/finite-quotient-topology-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "artifacts/examples/math/finite-quotient-topology-v0/smt2/bad-fiber-representative-alethe-conflict.smt2",
            "artifacts/examples/math/finite-quotient-topology-v0/smt2/bad-quotient-open-alethe-conflict.smt2",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite quotient-topology replay checks one fixed finite quotient map; it does not prove the quotient topology universal property or arbitrary quotient-map continuity theorems.",
            "The bad representative and quotient-open rows isolate fixed equality and open-status contradictions, not arbitrary saturated-set, separation, compactness, connectedness, or invariance reasoning.",
            "Additional quotient-topology rows should land only when they add distinct saturation, universal-property, invariance, or proof-reconstruction pressure beyond representative consistency and open-status checks.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite source topology, quotient universe, quotient map, fibers, same-fiber relation, quotient-open family, and saturated subset data.",
                "The validator recomputes fibers, surjectivity, equivalence pairs, every quotient subset preimage, quotient-open status, and saturated-open image/preimage behavior exactly.",
                "Malformed fixed quotient-representative and quotient-open rows link source artifacts and route regressions before claiming checked Alethe evidence.",
                "Quotient-space universal properties, quotient-map theorem schemas, preservation theorems, and arbitrary quotient constructions remain Lean-horizon until kernel-checked proof routes exist.",
            ],
        },
    },
    {
        "id": "bridge_finite_specialization_order_replay",
        "title": "Finite Specialization Order Replay",
        "field_ids": ["topology", "set_theory_and_foundations", "discrete_math"],
        "resource_status": "validated",
        "summary": (
            "Finite specialization-order rows state an explicit finite "
            "topology, then replay the preorder x <= y by checking every open "
            "neighborhood of x contains y. The trusted object is exact finite "
            "set-family replay plus checked QF_UF/Alethe evidence for a false "
            "T0/antisymmetry row; arbitrary specialization-order theory "
            "remains Lean-horizon."
        ),
        "prerequisites": [
            "bridge_finite_topology_operator_homeomorphism",
            "bridge_partition_relation_roundtrip",
            "curriculum_sets",
            "curriculum_relations_and_functions",
        ],
        "unlocks": [
            "field_topology",
            "field_set_theory_and_foundations",
            "field_discrete_math",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite topology",
            "finite preorders",
            "specialization order replay",
            "QF_UF / Alethe",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-specialization-order-v0",
                "Finite specialization preorder replay, singleton-closure characterization, T0/antisymmetry replay, and checked bad-T0 Alethe row.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite specialization replay plus QF_UF/Alethe bad-T0 certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-specialization-order-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The pack validator recomputes the specialization preorder "
                    "from finite open neighborhoods and singleton closures; the "
                    "bad T0 row graduates only because the fixed mutual-"
                    "specialization equality conflict has checked Alethe evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-topology-end-to-end.md",
            "docs/learn/math/finite-specialization-order-end-to-end.md",
            "artifacts/examples/math/finite-specialization-order-v0/smt2/bad-t0-antisymmetry-alethe-conflict.smt2",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite specialization-order replay checks fixed finite topologies; it does not prove T0 quotient, sobriety, Alexandroff-space, or domain-theoretic topology theorems.",
            "The bad T0 row isolates a fixed antisymmetry equality conflict, not arbitrary separation-axiom reasoning.",
            "Additional specialization-order rows should land only when they add distinct quotient, continuity-as-monotonicity, or proof-reconstruction pressure.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite universe, open-set family, listed specialization pairs, singleton closures, and the exact T0 or preorder claim.",
                "The validator recomputes topology axioms, specialization pairs, singleton closures, preorder laws, and antisymmetry exactly.",
                "Malformed fixed rows link source artifacts and route regressions before claiming checked Alethe evidence.",
                "T0 quotients, sobriety, Alexandroff-space equivalences, and domain-theoretic topology stay Lean-horizon until kernel-checked proof routes exist.",
            ],
        },
    },
    {
        "id": "bridge_finite_boundary_operator_replay",
        "title": "Finite Boundary Operator Replay",
        "field_ids": [
            "topology",
            "set_theory_and_foundations",
            "linear_algebra",
            "abstract_algebra",
        ],
        "resource_status": "validated",
        "summary": (
            "Finite boundary-operator rows state an explicit finite simplicial "
            "complex, orientation convention, chain basis, and integer boundary "
            "coefficients. The trusted object is exact replay of oriented face "
            "coefficients, boundary-of-boundary cancellation, boundary-matrix "
            "shape, or a checked QF_LIA/Diophantine certificate for a malformed "
            "fixed boundary coefficient."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "bridge_finite_counting_replay",
            "family_integer_diophantine",
            "curriculum_sets",
            "curriculum_relations_and_functions",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "bridge_finite_chain_homology_replay",
            "bridge_finite_torsion_homology_replay",
            "bridge_finite_cohomology_replay",
            "bridge_rank_nullity",
            "field_topology",
            "field_linear_algebra",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite simplicial complexes",
            "oriented boundary operators",
            "integer boundary matrices",
            "boundary squared replay",
            "QF_LIA / Diophantine",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-simplicial-homology-v0",
                "Finite simplicial-complex closure, oriented-boundary replay, boundary^2 replay, boundary-matrix rank replay, and checked bad-boundary coefficient row.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite oriented-boundary replay plus QF_LIA/Diophantine coefficient certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lia_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-simplicial-homology-end-to-end.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                ],
                "notes": (
                    "The pack validator recomputes the alternating oriented "
                    "face sum, applies the boundary operator twice, and checks "
                    "the malformed sign row only after the source-level integer "
                    "coefficient contradiction has checked Diophantine evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-simplicial-homology-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/learn/math/matrix-computation-index.md",
            "artifacts/examples/math/finite-simplicial-homology-v0/smt2/bad-boundary-coefficient-diophantine-conflict.smt2",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
        ],
        "open_gaps": [
            "Finite boundary replay checks fixed oriented simplices and fixed matrices; it does not prove functoriality, homology invariance, exactness, or topological invariance.",
            "Boundary-matrix rank rows are exact finite computations, not a general theorem about chain complexes over arbitrary rings.",
            "Additional torsion, universal-coefficient, or chain-map rows should land only when they add distinct integer-linear, finite-field, or proof-reconstruction pressure.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite complex, orientation convention, chain basis, boundary coefficients, and the exact boundary claim being replayed.",
                "The validator recomputes oriented faces, boundary coefficients, and boundary-of-boundary cancellation exactly.",
                "Malformed fixed boundary rows link source artifacts or route regressions before claiming checked Diophantine evidence.",
                "Functoriality, invariance, exact sequences, cohomology, and other algebraic-topology theorem claims remain Lean-horizon until kernel-checked proof routes exist.",
            ],
        },
    },
    {
        "id": "bridge_finite_chain_homology_replay",
        "title": "Finite Chain Complex And Homology Replay",
        "field_ids": [
            "topology",
            "set_theory_and_foundations",
            "linear_algebra",
            "abstract_algebra",
        ],
        "resource_status": "validated",
        "summary": (
            "Finite simplicial-homology rows state an explicit finite complex, "
            "oriented simplices, integer chain coefficients, boundary maps, "
            "and finite-rank data. The trusted object is exact replay of face "
            "closure, oriented boundaries, boundary-squared-zero, Betti-rank "
            "data, or a checked QF_LIA/Diophantine certificate for a malformed "
            "fixed boundary coefficient."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "bridge_finite_boundary_operator_replay",
            "bridge_rank_nullity",
            "bridge_finite_counting_replay",
            "family_integer_diophantine",
            "curriculum_sets",
            "curriculum_relations_and_functions",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "bridge_finite_torsion_homology_replay",
            "bridge_finite_cohomology_replay",
            "bridge_finite_universal_coefficient_shadow",
            "field_topology",
            "field_linear_algebra",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite simplicial complexes",
            "finite chain complexes",
            "integer linear algebra",
            "boundary matrix replay",
            "Betti-rank replay",
            "QF_LIA / Diophantine",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-simplicial-homology-v0",
                "Finite simplicial-complex closure, oriented-boundary replay, boundary^2 replay, Betti-rank replay, and checked bad-boundary coefficient row.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite chain replay plus QF_LIA/Diophantine coefficient certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lia_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-simplicial-homology-end-to-end.md",
                    "docs/learn/math/analysis-topology-proof-horizons.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                ],
                "notes": (
                    "The pack validator recomputes finite faces, boundaries, "
                    "boundary matrices, ranks, and cycle generators first; "
                    "the malformed boundary-sign row graduates only because "
                    "the isolated integer coefficient contradiction has "
                    "checked Diophantine evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-simplicial-homology-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/learn/math/matrix-computation-index.md",
            "artifacts/examples/math/finite-simplicial-homology-v0/smt2/bad-boundary-coefficient-diophantine-conflict.smt2",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
        ],
        "open_gaps": [
            "Finite chain-complex replay does not prove homology invariance, exact sequences, homotopy equivalence, cohomology operations, or general algebraic-topology theorems.",
            "Boundary-matrix rank rows are exact finite computations, not a proof of functoriality or topological invariance.",
            "Additional rank, torsion, universal-coefficient, or chain-map rows should land only when they add distinct integer-linear, finite-field, or proof-reconstruction pressure.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite complex, orientation conventions, chain coefficients, boundary matrices, and rank or Betti witnesses.",
                "The validator recomputes face closure, oriented boundaries, boundary-of-boundary cancellation, ranks, and listed cycle generators exactly.",
                "Malformed fixed rows link source artifacts or route regressions before claiming checked Diophantine evidence.",
                "General homology and algebraic-topology theorem claims remain Lean-horizon until kernel-checked proof routes exist.",
            ],
        },
    },
    {
        "id": "bridge_finite_torsion_homology_replay",
        "title": "Finite Torsion Homology Replay",
        "field_ids": [
            "topology",
            "set_theory_and_foundations",
            "linear_algebra",
            "abstract_algebra",
        ],
        "resource_status": "validated",
        "summary": (
            "Finite torsion-homology rows state an explicit finite free "
            "abelian chain complex, ordered integer boundary matrix, Smith "
            "diagonal, and quotient-generator claim. The trusted object is "
            "exact integer replay of d^2=0, rank/torsion bookkeeping, and a "
            "checked QF_LIA/Diophantine certificate for a malformed fixed "
            "boundary membership equation."
        ),
        "prerequisites": [
            "bridge_finite_boundary_operator_replay",
            "bridge_finite_chain_homology_replay",
            "bridge_gcd_divisibility_witness",
            "bridge_rank_nullity",
            "curriculum_sets",
            "curriculum_relations_and_functions",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "bridge_finite_cohomology_replay",
            "bridge_finite_universal_coefficient_shadow",
            "field_topology",
            "field_linear_algebra",
            "field_abstract_algebra",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite chain complexes over Z",
            "integer boundary matrices",
            "Smith normal form replay",
            "gcd/divisibility replay",
            "QF_LIA / Diophantine",
            "UnsatDiophantine certificate",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-chain-complex-torsion-v0",
                "Two-term chain-complex replay with d1=[2], Smith diagonal [2], H0 torsion Z/2, and a checked bad torsion-generator Diophantine row.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite torsion replay plus QF_LIA/Diophantine boundary-membership certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lia_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-chain-complex-torsion-end-to-end.md",
                    "docs/learn/math/analysis-topology-proof-horizons.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                ],
                "notes": (
                    "The pack validator checks one finite integer chain "
                    "complex and its Smith diagonal before trusting the "
                    "torsion claim. The malformed boundary-membership row "
                    "graduates only because the isolated equation 2*k = 1 "
                    "has independently checked Diophantine evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-chain-complex-torsion-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/learn/math/matrix-computation-index.md",
            "artifacts/examples/math/finite-chain-complex-torsion-v0/smt2/bad-torsion-generator-diophantine-conflict.smt2",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
        ],
        "open_gaps": [
            "Finite torsion replay checks one fixed chain complex and one one-entry Smith diagonal; it does not implement a general Smith-normal-form solver or prove classification of finitely generated abelian groups.",
            "The bad torsion-generator row isolates a fixed divisibility obstruction, not arbitrary quotient-module or exact-sequence reasoning.",
            "Universal coefficients, Ext/Tor functor laws, chain homotopy invariance, and topological invariance remain Lean-horizon until kernel-checked proof routes exist.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the free abelian chain groups, ordered bases, integer boundary matrices, Smith diagonal, torsion factors, and quotient-generator claim.",
                "The validator recomputes boundary composition, rational rank, one-entry Smith diagonal, free-rank bookkeeping, and divisibility obstructions exactly.",
                "Malformed fixed boundary-membership rows link source artifacts and route regressions before claiming checked Diophantine evidence.",
                "General torsion homology, universal coefficient theorems, exact sequences, and invariance claims remain Lean-horizon until kernel-checked proof routes exist.",
            ],
        },
    },
    {
        "id": "bridge_finite_cohomology_replay",
        "title": "Finite Simplicial Cohomology Replay",
        "field_ids": [
            "topology",
            "set_theory_and_foundations",
            "linear_algebra",
            "abstract_algebra",
        ],
        "resource_status": "validated",
        "summary": (
            "Finite cohomology rows state an explicit finite simplicial complex, "
            "F2 cochain basis, coboundary tables, and finite-rank data. The "
            "trusted object is exact replay of coboundary values, delta-squared "
            "cancellation, F2 rank calculations, or checked QF_UF/Alethe evidence "
            "for a malformed fixed coboundary value."
        ),
        "prerequisites": [
            "bridge_finite_boundary_operator_replay",
            "bridge_finite_chain_homology_replay",
            "bridge_rank_nullity",
            "curriculum_sets",
            "curriculum_relations_and_functions",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "field_topology",
            "field_linear_algebra",
            "field_abstract_algebra",
            "bridge_finite_universal_coefficient_shadow",
            "bridge_finite_cup_product_replay",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite simplicial complexes",
            "finite cochains over F2",
            "finite cochain complexes",
            "F2 matrix rank replay",
            "QF_UF / Alethe",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-simplicial-cohomology-v0",
                "Finite F2 coboundary replay, delta-squared-zero replay, cohomology-rank replay, non-coboundary cocycle witness, and checked bad-coboundary Alethe row.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite F2 cochain replay plus QF_UF/Alethe value certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-simplicial-cohomology-end-to-end.md",
                    "docs/learn/math/analysis-topology-proof-horizons.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The pack validator recomputes coboundary values from "
                    "finite simplex faces, checks delta-squared-zero, computes "
                    "F2 matrix ranks, and accepts the malformed value row only "
                    "after the isolated equality conflict has checked Alethe "
                    "evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-simplicial-homology-end-to-end.md",
            "docs/learn/math/finite-simplicial-cohomology-end-to-end.md",
            "docs/learn/math/finite-simplicial-cup-products-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/learn/math/matrix-computation-index.md",
            "artifacts/examples/math/finite-simplicial-cohomology-v0/smt2/bad-coboundary-value-alethe-conflict.smt2",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite cohomology replay checks fixed F2 cochain tables; it does not prove cohomology functoriality, cup-product laws, universal coefficients, de Rham comparison, sheaf cohomology, Poincare duality, or topological invariance.",
            "The bad coboundary row isolates a fixed value mismatch after finite replay, not arbitrary finite-field linear algebra proof reconstruction.",
            "Additional cohomology rows should land only when they add distinct torsion/universal-coefficient, cohomology-ring, or proof-reconstruction pressure.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite complex, cochain basis, coefficient field, coboundary values, and rank or cocycle witnesses.",
                "The validator recomputes simplex closure, F2 coboundaries, delta-squared-zero, F2 ranks, and non-coboundary status exactly.",
                "Malformed fixed rows link source artifacts and route regressions before claiming checked Alethe evidence.",
                "Cohomology operations, functoriality, universal coefficients, duality, and topological invariance remain Lean-horizon until kernel-checked proof routes exist.",
            ],
        },
    },
    {
        "id": "bridge_finite_universal_coefficient_shadow",
        "title": "Finite Universal Coefficient Shadow Replay",
        "field_ids": [
            "topology",
            "set_theory_and_foundations",
            "linear_algebra",
            "abstract_algebra",
        ],
        "resource_status": "validated",
        "summary": (
            "Finite universal-coefficient shadow rows state one explicit free "
            "abelian chain complex, its dual cochain map, homology and "
            "cohomology invariants, plus the degree-one Hom/Ext bookkeeping. "
            "The trusted object is exact integer invariant replay plus checked "
            "QF_UF/Alethe evidence for a malformed fixed group-identification "
            "row; the universal coefficient theorem itself remains Lean-horizon."
        ),
        "prerequisites": [
            "bridge_finite_boundary_operator_replay",
            "bridge_finite_chain_homology_replay",
            "bridge_finite_torsion_homology_replay",
            "bridge_finite_cohomology_replay",
            "bridge_gcd_divisibility_witness",
            "bridge_quotient_map",
            "curriculum_sets",
            "curriculum_relations_and_functions",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "field_topology",
            "field_linear_algebra",
            "field_abstract_algebra",
            "bridge_finite_cup_product_replay",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite chain complexes over Z",
            "integer cochain complexes",
            "finitely generated abelian group invariants",
            "Hom/Ext shadow replay",
            "QF_UF / Alethe",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-universal-coefficient-shadow-v0",
                "Two-term chain/cochain replay with d1=[2], H0=Z/2, H1=0, H^1=Z/2, degree-one Hom/Ext shadow, and a checked bad H^1=0 Alethe row.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite Hom/Ext shadow replay plus QF_UF/Alethe group-conflict certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-universal-coefficient-shadow-end-to-end.md",
                    "docs/learn/math/analysis-topology-proof-horizons.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The pack validator recomputes delta0=d1^T, the "
                    "cochain composition, the Z/2 cohomology invariant, "
                    "Hom(0,Z)=0, and Ext(Z/2,Z)=Z/2 before accepting the "
                    "degree-one row. The malformed H^1=0 row graduates only "
                    "because the isolated equality conflict has checked "
                    "Alethe evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/foundational-resources/MATH-CURRICULUM-BUILDOUT.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-chain-complex-torsion-end-to-end.md",
            "docs/learn/math/finite-simplicial-cohomology-end-to-end.md",
            "docs/learn/math/finite-universal-coefficient-shadow-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/learn/math/matrix-computation-index.md",
            "artifacts/examples/math/finite-universal-coefficient-shadow-v0/smt2/bad-uct-h1-zero-alethe-conflict.smt2",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite universal-coefficient shadow replay checks one fixed two-term chain complex and one degree-one Hom/Ext bookkeeping row; it does not prove the universal coefficient theorem.",
            "The bad H^1=0 row isolates a fixed group-identity conflict, not arbitrary exact-sequence, naturality, Ext/Tor, quotient, or splitting reasoning.",
            "Additional universal-coefficient rows should land only when they add distinct Ext/Tor, exact-sequence, quotient-module, or proof-reconstruction pressure.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the free abelian chain groups, dual cochain groups, integer maps, homology and cohomology invariants, Hom term, Ext term, and the fixed short exact-sequence shadow.",
                "The validator recomputes delta0=d1^T, cochain composition, one-entry invariant factors, Hom(0,Z), Ext(Z/2,Z), and the listed degree-one exact-sequence labels exactly.",
                "Malformed fixed group-identification rows link source artifacts and route regressions before claiming checked Alethe evidence.",
                "Universal coefficient theorem schemas, naturality, splitting choices, Ext/Tor functor laws, and arbitrary chain-complex statements remain Lean-horizon until kernel-checked proof routes exist.",
            ],
        },
    },
    {
        "id": "bridge_finite_cup_product_replay",
        "title": "Finite Simplicial Cup Product Replay",
        "field_ids": [
            "topology",
            "set_theory_and_foundations",
            "linear_algebra",
            "abstract_algebra",
        ],
        "resource_status": "validated",
        "summary": (
            "Finite cup-product rows state an explicit ordered simplicial complex, "
            "F2 cochain basis, Alexander-Whitney split convention, and listed "
            "cup-product values. The trusted object is exact replay of F2 products, "
            "one finite coboundary Leibniz row, or checked QF_BV/DRAT evidence for "
            "a malformed fixed cup-product bit."
        ),
        "prerequisites": [
            "bridge_finite_cohomology_replay",
            "bridge_finite_boundary_operator_replay",
            "bridge_finite_chain_homology_replay",
            "curriculum_sets",
            "curriculum_relations_and_functions",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "field_topology",
            "field_linear_algebra",
            "field_abstract_algebra",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite simplicial complexes",
            "finite cochains over F2",
            "finite cup products",
            "QF_BV / DRAT",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-simplicial-cup-products-v0",
                "Finite F2 cup-product replay, finite coboundary Leibniz replay, and checked bad cup-product QF_BV/DRAT row.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite F2 cup-product replay plus QF_BV/DRAT value certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_bv_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-simplicial-cup-products-end-to-end.md",
                    "docs/learn/math/analysis-topology-proof-horizons.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "crates/axeyum-solver/tests/math_resource_bv_routes.rs",
                ],
                "notes": (
                    "The pack validator recomputes the Alexander-Whitney split "
                    "for finite ordered simplices, checks one F2 coboundary "
                    "Leibniz row, and accepts the malformed value row only after "
                    "the one-bit cup-product conflict has checked DRAT evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-simplicial-cohomology-end-to-end.md",
            "docs/learn/math/finite-simplicial-cup-products-end-to-end.md",
            "docs/learn/math/analysis-topology-proof-horizons.md",
            "docs/learn/math/matrix-computation-index.md",
            "artifacts/examples/math/finite-simplicial-cup-products-v0/smt2/bad-cup-product-bitblast-conflict.smt2",
            "crates/axeyum-solver/tests/math_resource_bv_routes.rs",
        ],
        "open_gaps": [
            "Finite cup-product replay checks fixed ordered F2 cochain tables; it does not prove associativity, graded commutativity, naturality, cohomology-ring quotienting, or topological invariance.",
            "The bad cup-product row isolates a fixed one-bit value mismatch after finite replay, not arbitrary cohomology-ring proof reconstruction.",
            "Additional cup-product rows should land only when they add distinct associativity, graded-commutativity, Steenrod-operation, or proof-reconstruction pressure.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite complex, cochain basis, coefficient field, split convention, cup-product values, and coboundary relation being replayed.",
                "The validator recomputes simplex closure, F2 cup products, coboundaries, and the listed finite Leibniz row exactly.",
                "Malformed fixed rows link source artifacts and route regressions before claiming checked QF_BV/DRAT evidence.",
                "Associativity, graded commutativity, naturality, cohomology rings, and topological invariance remain Lean-horizon until kernel-checked proof routes exist.",
            ],
        },
    },
    {
        "id": "bridge_lu_replay",
        "title": "LU Factorization Replay",
        "field_ids": ["linear_algebra", "numerical_analysis"],
        "resource_status": "validated",
        "summary": (
            "A claimed LU factorization and nullspace vector are checked by "
            "exact matrix multiplication over fixed rational matrices; "
            "malformed product-entry and nullspace-component rows now route "
            "through checked QF_LRA/Farkas evidence, while pivoting, "
            "singularity, and stability claims stay separate from the replayed "
            "equalities."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "curriculum_linear_algebra",
            "curriculum_rationals",
        ],
        "unlocks": [
            "bridge_residual_bound",
            "field_numerical_analysis",
            "field_optimization_and_convexity",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite matrices",
            "exact rational arithmetic",
            "LRA (exact rationals)",
            "matrix multiplication replay",
            "QF_LRA",
        ],
        "example_packs": [
            (
                "linear-algebra-rational-v0",
                "Exact matrix-vector solution, LU factorization, and nullspace witnesses over rational matrices.",
            ),
            (
                "numerical-linear-algebra-v0",
                "Exact residual, solution-box, and one-step iterative checks that build on matrix replay.",
            ),
            (
                "linear-optimization-v0",
                "Linear feasibility and Farkas rows that reuse exact rational matrix constraints.",
            ),
        ],
        "proof_routes": [
            {
                "name": "exact rational matrix replay",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py",
                "lean_status": "not-required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "docs/learn/math/matrix-corpus-benchmark-boundary.md",
                    "docs/learn/math/linear-system-end-to-end.md",
                    "docs/learn/math/numerical-linear-algebra-end-to-end.md",
                ],
                "notes": (
                    "The pack validator recomputes L*U, A*x, and A*v exactly "
                    "over rationals; a separate qf-lra-bad-lu-product-entry "
                    "row, the bad nullspace-component row, and bad infeasible "
                    "linear-system rows use the QF_LRA/Farkas route."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/learn/math/matrix-computation-index.md",
            "docs/learn/math/matrix-corpus-benchmark-boundary.md",
            "docs/learn/math/linear-system-end-to-end.md",
            "docs/learn/math/numerical-linear-algebra-end-to-end.md",
            "artifacts/examples/math/linear-algebra-rational-v0/smt2/bad-lu-product-entry-farkas-conflict.smt2",
            "artifacts/examples/math/linear-algebra-rational-v0/smt2/bad-nullspace-component-farkas-conflict.smt2",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
        ],
        "open_gaps": [
            "LU replay checks a fixed factorization; it does not prove existence, pivoting strategy correctness, or numerical stability.",
            "Ill-conditioned and floating-point claims need separate numerical-honesty metadata before they become solver or learner claims.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the exact matrix entries, lower/upper factors, and rational arithmetic domain.",
                "The validator recomputes L*U, and the separate qf-lra-bad-lu-product-entry row rejects the corrupted equality through checked QF_LRA/Farkas evidence.",
                "Singularity, pivoting, and stability claims remain separate proof-horizon or numerical-analysis rows.",
            ],
        },
    },
    {
        "id": "bridge_rank_nullity",
        "title": "Rank-Nullity Replay",
        "field_ids": ["linear_algebra", "abstract_algebra", "set_theory_and_foundations"],
        "resource_status": "validated",
        "summary": (
            "Rank-nullity is represented by finite carrier, kernel, image, and "
            "map-table checks where the listed dimensions or cardinalities are "
            "recomputed directly for the bounded vector space."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "curriculum_fields",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "bridge_eigenpair",
            "field_linear_algebra",
            "field_abstract_algebra",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite vector spaces",
            "finite fields",
            "finite functions",
            "QF_UF",
            "finite replay",
        ],
        "example_packs": [
            (
                "finite-vector-spaces-v0",
                "Finite F2 vector-space subspace, span, linear-map, kernel, image, and rank-nullity replay.",
            ),
            (
                "finite-dual-spaces-v0",
                "Finite covectors, annihilators, dual basis, and additivity checks.",
            ),
            (
                "finite-modules-v0",
                "Finite module submodule and scalar-action rows that reuse kernel/image vocabulary.",
            ),
            (
                "random-matrix-finite-v0",
                "Rank-mixture probabilities and a checked bad expected-rank row over a finite random-matrix distribution.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite kernel/image/cardinality replay",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "docs/learn/math/matrix-corpus-benchmark-boundary.md",
                    "docs/learn/math/linear-algebra-and-optimization.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "Positive finite rows replay kernel/image membership and "
                    "cardinality; equality-heavy bad closure rows can join "
                    "the QF_UF/Alethe regression family."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/learn/math/matrix-computation-index.md",
            "docs/learn/math/matrix-corpus-benchmark-boundary.md",
            "docs/learn/math/linear-algebra-and-optimization.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite rank-nullity replay does not prove dimension uniqueness or rank-nullity over arbitrary fields.",
            "General linear algebra theorems remain Lean-horizon until kernel/image and basis-extension proofs are reconstructed.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite field, vector-space carrier, linear map, kernel, image, and dimension or cardinality witnesses.",
                "The validator recomputes closure, linearity, kernel/image membership, and rank-nullity equality.",
                "General theorem statements remain linked to Lean-horizon rows instead of benchmark rows.",
            ],
        },
    },
    {
        "id": "bridge_residual_bound",
        "title": "Residual Bound",
        "field_ids": ["numerical_analysis", "linear_algebra", "optimization_and_convexity"],
        "resource_status": "validated",
        "summary": (
            "A residual-bound row checks exact rational residuals, norms, "
            "solution boxes, Jacobi-step error bounds, or normal-equation side "
            "conditions for a fixed matrix problem, and separates exact "
            "infeasibility from floating error analysis."
        ),
        "prerequisites": [
            "bridge_lu_replay",
            "bridge_counterexample_proof",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "field_numerical_analysis",
            "field_optimization_and_convexity",
            "bridge_random_matrix_finite_moment",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "QF_LRA",
            "Farkas certificate",
            "exact rational residuals",
            "finite matrices",
            "bounded recurrence replay",
        ],
        "example_packs": [
            (
                "numerical-linear-algebra-v0",
                "Residual-norm, solution-box, Jacobi contraction, and bad residual/solution-box/Jacobi-bound rows.",
            ),
            (
                "least-squares-regression-v0",
                "Normal-equation, residual-orthogonality, bad RSS-improvement, and bad coefficient rows.",
            ),
            (
                "inner-product-spaces-rational-v0",
                "Projection, Gram matrix, and Cauchy-Schwarz rows over exact rational vectors.",
            ),
            (
                "linear-algebra-rational-v0",
                "Inconsistent rational linear-system row that reuses the Farkas route.",
            ),
        ],
        "proof_routes": [
            {
                "name": "QF_LRA/Farkas residual infeasibility",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "docs/learn/math/matrix-corpus-benchmark-boundary.md",
                    "docs/learn/math/numerical-linear-algebra-end-to-end.md",
                    "docs/learn/math/linear-algebra-and-optimization.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "Exact residual witnesses replay directly; false bound or "
                    "coefficient claims graduate only when the final rational "
                    "linear conflict has rechecked Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/learn/math/matrix-computation-index.md",
            "docs/learn/math/matrix-corpus-benchmark-boundary.md",
            "docs/learn/math/numerical-linear-algebra-end-to-end.md",
            "docs/learn/math/linear-algebra-and-optimization.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Exact residual rows do not certify floating-point roundoff, conditioning, or asymptotic convergence rates.",
            "Nonlinear norm bounds and spectral-condition claims need separate NRA, interval, or Lean-backed routes.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the matrix, candidate vector, norm or box, and exact rational residual computation.",
                "Bad residual or coefficient rows carry source-linked QF_LRA/Farkas evidence before solver reuse is claimed.",
                "Learner pages label numerical-analysis claims as exact rational shadows unless floating-point evidence exists.",
            ],
        },
    },
    {
        "id": "bridge_eigenpair",
        "title": "Eigenpair Witness",
        "field_ids": ["linear_algebra", "functional_analysis_and_operator_theory", "numerical_analysis"],
        "resource_status": "validated",
        "summary": (
            "A finite eigenpair row checks A*v = lambda*v exactly for a fixed "
            "matrix, and may additionally replay orthogonality, Rayleigh "
            "quotient, or spectral-decomposition witnesses within the bounded "
            "matrix instance."
        ),
        "prerequisites": [
            "bridge_lu_replay",
            "bridge_residual_bound",
            "bridge_characteristic_polynomial",
        ],
        "unlocks": [
            "field_functional_analysis_and_operator_theory",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite matrices",
            "LRA (exact rationals)",
            "QF_LRA",
            "NRA shadow",
            "finite-dimensional operator replay",
        ],
        "example_packs": [
            (
                "spectral-linear-algebra-v0",
                "Eigenpair, orthogonal eigenbasis, Rayleigh quotient, spectral decomposition, and bad eigenpair rows.",
            ),
            (
                "matrix-invariants-v0",
                "Characteristic roots and Cayley-Hamilton rows connected to fixed-matrix spectral checks.",
            ),
            (
                "inner-product-spaces-rational-v0",
                "Inner-product and projection rows that support orthogonality checks.",
            ),
            (
                "finite-operator-v0",
                "Finite-operator rows that expose the later operator-theory horizon.",
            ),
        ],
        "proof_routes": [
            {
                "name": "exact finite eigenpair replay plus QF_LRA/Farkas bad-eigenpair certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "docs/learn/math/matrix-corpus-benchmark-boundary.md",
                    "docs/learn/math/spectral-linear-algebra-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes A*v and lambda*v exactly; "
                    "the promoted bad-eigenpair row checks the isolated rational "
                    "component conflict with Farkas evidence. General spectral "
                    "theorems remain Lean-horizon."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/matrix-computation-index.md",
            "docs/learn/math/matrix-corpus-benchmark-boundary.md",
            "docs/learn/math/spectral-linear-algebra-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Fixed eigenpair replay does not prove existence of eigenvalues, diagonalization, spectral theorem, or stability of numerical eigensolvers.",
            "Nonlinear characteristic-root reasoning and infinite-dimensional operator theory remain separate theorem horizons.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state A, lambda, v, field/domain, and every side condition such as nonzero vector or orthogonality.",
                "The validator recomputes A*v = lambda*v exactly and rejects corrupted component claims.",
                "General spectral theorem statements are linked as Lean-horizon rows, not as finite solver evidence.",
            ],
        },
    },
    {
        "id": "bridge_characteristic_polynomial",
        "title": "Characteristic Polynomial Replay",
        "field_ids": ["linear_algebra", "abstract_algebra", "real_analysis", "numerical_analysis"],
        "resource_status": "validated",
        "summary": (
            "A characteristic-polynomial row replays trace, determinant, fixed "
            "polynomial coefficients, listed roots, and Cayley-Hamilton-style "
            "matrix substitution for a bounded matrix instance, with bad trace "
            "and bad polynomial rows checked through QF_LRA/Farkas evidence."
        ),
        "prerequisites": [
            "bridge_lu_replay",
            "curriculum_polynomials",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "bridge_eigenpair",
            "field_linear_algebra",
            "field_abstract_algebra",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite matrices",
            "fixed-degree polynomials",
            "LRA (exact rationals)",
            "QF_LRA",
            "NRA shadow",
        ],
        "example_packs": [
            (
                "matrix-invariants-v0",
                "Trace, determinant, characteristic polynomial, roots, Cayley-Hamilton, Gershgorin, bad trace, and bad polynomial rows.",
            ),
            (
                "spectral-linear-algebra-v0",
                "Eigenpair and spectral rows that consume characteristic-polynomial vocabulary.",
            ),
            (
                "polynomial-factorization-rational-v0",
                "Fixed-degree rational polynomial division, GCD, factorization, and irreducibility replay.",
            ),
        ],
        "proof_routes": [
            {
                "name": "fixed-degree matrix invariant replay plus QF_LRA/Farkas bad-trace and bad-polynomial certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "docs/learn/math/matrix-corpus-benchmark-boundary.md",
                    "docs/learn/math/matrix-invariants-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes the listed invariant values; "
                    "the promoted bad trace and bad characteristic-polynomial "
                    "rows check isolated exact-rational conflicts with Farkas "
                    "evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/matrix-computation-index.md",
            "docs/learn/math/matrix-corpus-benchmark-boundary.md",
            "docs/learn/math/matrix-invariants-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Fixed characteristic-polynomial replay does not prove arbitrary determinant identities or general Cayley-Hamilton over all rings.",
            "Root-existence and algebraic-closure claims remain Lean/NRA/RCF horizon work depending on the statement.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state matrix entries, polynomial coefficients, evaluation point or root witness, and exact arithmetic domain.",
                "The validator recomputes trace, determinant, polynomial evaluation, and any matrix substitution claim.",
                "Bad invariant rows carry source-linked QF_LRA/Farkas evidence before solver reuse is claimed.",
            ],
        },
    },
    {
        "id": "bridge_random_matrix_finite_moment",
        "title": "Finite Random-Matrix Moment",
        "field_ids": ["probability_theory", "statistics", "linear_algebra", "numerical_analysis"],
        "resource_status": "validated",
        "summary": (
            "A finite random-matrix row enumerates an explicit matrix-valued "
            "distribution and recomputes exact expectations, moments, ranks, "
            "determinants, or Gram matrices without simulation or asymptotics."
        ),
        "prerequisites": [
            "bridge_rank_nullity",
            "bridge_residual_bound",
            "curriculum_counting",
        ],
        "unlocks": [
            "field_probability_theory",
            "field_statistics",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite enumeration",
            "finite probability tables",
            "finite matrices",
            "QF_LRA",
            "exact rational expectation",
        ],
        "example_packs": [
            (
                "random-matrix-finite-v0",
                "Finite sign-matrix moments, expected Gram matrix, rank mixture, and bad trace-moment/expected-rank rows.",
            ),
            (
                "finite-probability-v0",
                "Finite probability-table normalization, Bayes, and independence rows used by expectation replay.",
            ),
            (
                "descriptive-statistics-v0",
                "Exact finite statistic rows that share expectation and moment vocabulary.",
            ),
            (
                "finite-concentration-v0",
                "Finite tail-bound and union-bound rows that separate exact enumeration from concentration theorem horizons.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite expectation/rank replay plus QF_LRA/Farkas bad-moment and bad-rank certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "docs/learn/math/matrix-corpus-benchmark-boundary.md",
                    "docs/learn/math/random-matrix-moment-index.md",
                    "docs/learn/math/random-matrix-finite-end-to-end.md",
                    "docs/learn/math/probability-and-statistics.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker normalizes the distribution and "
                    "recomputes exact moments and ranks by enumeration; false "
                    "moment or rank claims graduate only when the exact rational conflict "
                    "has checked Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/matrix-computation-index.md",
            "docs/learn/math/matrix-corpus-benchmark-boundary.md",
            "docs/learn/math/random-matrix-moment-index.md",
            "docs/learn/math/random-matrix-finite-end-to-end.md",
            "docs/learn/math/probability-and-statistics.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite enumeration is not random matrix asymptotics, concentration, or universality.",
            "Simulation outputs must not be treated as proof unless they are converted into exact finite distributions or theorem-horizon artifacts.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the exact finite support, probabilities, matrix entries, and target statistic.",
                "The validator recomputes normalization, expectations, ranks, determinants, and moment identities exactly.",
                "Asymptotic random-matrix statements remain Lean/probability-theory horizons.",
            ],
        },
    },
    {
        "id": "bridge_finite_measure_additivity",
        "title": "Finite Measure Additivity",
        "field_ids": ["measure_theory", "probability_theory", "set_theory_and_foundations"],
        "resource_status": "validated",
        "summary": (
            "A finite measure-additivity row checks a finite universe, event "
            "algebra, exact rational atom weights, complements, monotonicity, "
            "and disjoint-union additivity before any probability, product, "
            "or integration claim is treated as solver-reusable evidence."
        ),
        "prerequisites": [
            "bridge_finite_boolean_algebra",
            "bridge_finite_model_replay",
            "curriculum_rationals",
        ],
        "unlocks": [
            "bridge_probability_mass_table",
            "bridge_finite_product_integration",
            "bridge_conditional_expectation",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite sets",
            "finite event algebras",
            "exact rational arithmetic",
            "QF_LRA",
            "Farkas certificate",
            "finite replay",
        ],
        "example_packs": [
            (
                "finite-measure-v0",
                "Finite sigma-algebra, event measure, complement, and bad complement rows.",
            ),
            (
                "finite-measure-monotonicity-v0",
                "Finite subset monotonicity, union subadditivity, and bad subset-measure/union rows.",
            ),
            (
                "finite-probability-v0",
                "Probability mass-table rows as normalized finite measures.",
            ),
            (
                "finite-random-variables-v0",
                "Finite measurable-function and pushforward rows built over finite event algebras.",
            ),
            (
                "finite-concentration-v0",
                "Finite event-mass rows used by tail-bound, union-bound, and concentration-shadow examples.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite measure replay plus QF_LRA/Farkas bad-complement and bad-monotonicity certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-measure-end-to-end.md",
                    "docs/learn/math/finite-measure-monotonicity-end-to-end.md",
                    "docs/learn/math/finite-topology-measure-end-to-end.md",
                    "docs/learn/math/probability-and-statistics.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes event membership and atom "
                    "sums exactly; false complement, monotonicity, or additivity claims are "
                    "promoted only when the exact rational contradiction has "
                    "checked QF_LRA/Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-measure-end-to-end.md",
            "docs/learn/math/finite-topology-measure-end-to-end.md",
            "docs/learn/math/probability-and-statistics.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite event-algebra replay does not prove countable additivity, completion, sigma-finiteness, or Lebesgue measure construction.",
            "Monotone convergence, dominated convergence, almost-everywhere reasoning, and Radon-Nikodym theorems remain Lean horizons.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite universe, event algebra, atom weights, and exact rational measure domain.",
                "The validator recomputes complements, disjoint unions, monotonicity, and event measures from atom tables.",
                "Bad measure rows carry source-linked QF_LRA/Farkas evidence before solver reuse is claimed.",
            ],
        },
    },
    {
        "id": "bridge_probability_mass_table",
        "title": "Finite Probability Mass Table",
        "field_ids": ["probability_theory", "measure_theory", "statistics"],
        "resource_status": "validated",
        "summary": (
            "A finite probability mass table row checks a finite sample space, "
            "exact rational atom weights, event masses, complements, "
            "normalization, conditioning, product rows, and finite "
            "distribution-distance rows without simulation or "
            "continuous-distribution assumptions."
        ),
        "prerequisites": [
            "bridge_finite_measure_additivity",
            "bridge_finite_model_replay",
            "curriculum_counting",
            "curriculum_rationals",
        ],
        "unlocks": [
            "bridge_pushforward_distribution",
            "bridge_stochastic_kernel",
            "bridge_conditional_expectation",
            "bridge_finite_product_integration",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite probability tables",
            "exact rational arithmetic",
            "QF_LRA",
            "Farkas certificate",
            "finite replay",
        ],
        "example_packs": [
            (
                "finite-probability-v0",
                "Finite mass-table normalization, conditioning, independence, Bayes-rule, and total-variation replay.",
            ),
            (
                "finite-measure-v0",
                "Finite sigma-algebra, measure additivity, and complement replay.",
            ),
            (
                "finite-measure-monotonicity-v0",
                "Finite measure monotonicity and union subadditivity replay.",
            ),
            (
                "finite-product-measure-v0",
                "Finite product-probability and marginal rows over exact rational masses.",
            ),
            (
                "finite-concentration-v0",
                "Finite event masses, union probabilities, and tail probabilities used by concentration-shadow rows.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite mass-table replay plus QF_LRA/Farkas bad-table certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/learn/math/finite-probability-end-to-end.md",
                    "docs/learn/math/finite-topology-measure-end-to-end.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes atom sums and event masses "
                    "exactly; malformed normalization, complement, Bayes, "
                    "total-variation, or product rows graduate only when the final rational "
                    "conflict carries checked Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/learn/math/finite-probability-end-to-end.md",
            "docs/learn/math/finite-topology-measure-end-to-end.md",
            "docs/learn/math/probability-and-statistics.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite mass-table replay does not prove countable additivity, continuous distributions, convergence theorems, or sampling guarantees.",
            "General measure and probability theorems remain Lean-horizon until kernel-checked reconstruction exists.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite sample space, atom masses, event sets, and exact rational arithmetic domain.",
                "The validator recomputes normalization, event mass, complement, product, conditioning, or finite distance claims from atoms.",
                "Bad mass-table rows carry source-linked QF_LRA/Farkas evidence before solver reuse is claimed.",
            ],
        },
    },
    {
        "id": "bridge_pushforward_distribution",
        "title": "Finite Pushforward Distribution",
        "field_ids": ["probability_theory", "measure_theory", "statistics", "set_theory_and_foundations"],
        "resource_status": "validated",
        "summary": (
            "A finite pushforward row checks a random-variable function table "
            "by summing the source atom masses mapped to each output value, "
            "then comparing the computed distribution with the claimed target "
            "mass table."
        ),
        "prerequisites": [
            "bridge_probability_mass_table",
            "curriculum_relations_and_functions",
            "curriculum_counting",
        ],
        "unlocks": [
            "bridge_conditional_expectation",
            "bridge_random_matrix_finite_moment",
            "field_statistics",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite functions",
            "finite probability tables",
            "exact rational sums",
            "QF_LRA",
            "finite replay",
        ],
        "example_packs": [
            (
                "finite-random-variables-v0",
                "Finite random-variable image, pushforward distribution, expectation, and bad pushforward rows.",
            ),
            (
                "finite-product-measure-v0",
                "Finite product-space rows where coordinate projections induce marginal distributions.",
            ),
            (
                "random-matrix-finite-v0",
                "Matrix-valued random variables whose statistics are pushforwards of a finite distribution.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite pushforward replay plus QF_LRA/Farkas bad-distribution certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/learn/math/finite-random-variables-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The validator recomputes each target mass as a sum over "
                    "the source atoms with that output; false target masses "
                    "use the QF_LRA/Farkas route when promoted."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/learn/math/finite-random-variables-end-to-end.md",
            "docs/learn/math/random-matrix-finite-end-to-end.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite pushforward replay does not prove measurability in general measure spaces.",
            "Continuous random variables, distributional convergence, and regular conditional laws remain theorem horizons.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the source atoms, probability table, random-variable map, target values, and claimed target masses.",
                "The validator recomputes each pushforward mass and rejects corrupted table entries.",
                "Learner pages distinguish finite pushforward sums from general measurable-map theorems.",
            ],
        },
    },
    {
        "id": "bridge_finite_dynamics_euler_replay",
        "title": "Finite Dynamics And Euler Replay",
        "field_ids": [
            "differential_equations_and_dynamical_systems",
            "numerical_analysis",
            "real_analysis",
            "linear_algebra",
        ],
        "resource_status": "validated",
        "summary": (
            "Finite dynamics rows state an initial state, transition rule, "
            "horizon, trace, invariant, threshold, Euler step, or finite error "
            "table over exact rational data. The trusted object is replay of "
            "the listed finite transition data or a checked QF_LRA/Farkas "
            "certificate for a malformed fixed trace, invariant, recurrence "
            "value, or Euler update."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "bridge_qf_lra_farkas_anatomy",
            "bridge_bounded_theorem_shadow",
            "curriculum_sequences_and_limits",
            "curriculum_calculus",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "bridge_stochastic_kernel",
            "bridge_residual_bound",
            "bridge_finite_operator_chebyshev",
            "field_differential_equations_and_dynamical_systems",
            "field_numerical_analysis",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite transition systems",
            "bounded model checking",
            "finite recurrence replay",
            "explicit Euler replay",
            "finite matrices",
            "QF_LRA",
            "Farkas certificate",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-recurrence-prefix-v0",
                "Fibonacci prefix, affine recurrence, companion-matrix prefix, replay-only bad source rows, and separate checked qf-lra proof rows.",
            ),
            (
                "bounded-dynamics-v0",
                "Bounded recurrence traces, finite invariants, threshold reachability, replay-only bad transition-step, bad threshold-step, and invariant-bound rows, plus separate checked QF_LRA/Farkas proof rows.",
            ),
            (
                "finite-euler-method-v0",
                "Exact explicit-Euler transitions, finite error tables, monotone invariant replay, and checked bad error-bound plus bad Euler-step rows.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite transition replay plus QF_LRA/Farkas certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/learn/math/finite-recurrence-prefix-end-to-end.md",
                    "docs/learn/math/bounded-dynamics-end-to-end.md",
                    "docs/learn/math/finite-euler-method-end-to-end.md",
                    "docs/learn/math/finite-dynamics-euler-end-to-end.md",
                    "docs/learn/math/analysis-dynamics-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "Positive rows recompute each finite transition, matrix "
                    "state update, invariant, threshold, or Euler step exactly. "
                    "Negative rows graduate only when the source SMT-LIB or "
                    "route regression yields rechecked Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/learn/math/finite-recurrence-prefix-end-to-end.md",
            "docs/learn/math/bounded-dynamics-end-to-end.md",
            "docs/learn/math/finite-euler-method-end-to-end.md",
            "docs/learn/math/finite-dynamics-euler-end-to-end.md",
            "docs/learn/math/analysis-dynamics-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite dynamics replay does not prove continuous-time existence, uniqueness, stability, chaos, stiffness behavior, PDE theory, or convergence-rate theorems.",
            "A bounded invariant row proves only the listed horizon unless a separate induction or Lean proof route is supplied.",
            "Euler rows are exact rational numerical shadows; floating-point implementations, adaptive methods, and asymptotic error theory stay in numerical-honesty or Lean-horizon lanes.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the transition rule, horizon, initial condition, trace, invariant/threshold, and exact rational data.",
                "The validator recomputes each finite transition, matrix state, Euler update, and finite error value.",
                "Malformed finite dynamics rows link source artifacts or route regressions before claiming checked Farkas evidence.",
            ],
        },
    },
    {
        "id": "bridge_stochastic_kernel",
        "title": "Finite Stochastic Kernel",
        "field_ids": [
            "probability_theory",
            "measure_theory",
            "statistics",
            "differential_equations_and_dynamical_systems",
            "linear_algebra",
        ],
        "resource_status": "validated",
        "summary": (
            "A finite stochastic-kernel row checks exact rational transition "
            "rows, row normalization, finite Markov-chain steps, absorption or "
            "hitting-time equations, and policy-transition tables over a fixed "
            "finite state space."
        ),
        "prerequisites": [
            "bridge_probability_mass_table",
            "bridge_residual_bound",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "bridge_conditional_expectation",
            "field_probability_theory",
            "field_differential_equations_and_dynamical_systems",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite transition systems",
            "finite probability tables",
            "finite matrices",
            "QF_LRA",
            "Farkas certificate",
        ],
        "example_packs": [
            (
                "finite-stochastic-kernels-v0",
                "Finite transition-kernel normalization, marginal, composition, bad-row, and bad-composition checks.",
            ),
            (
                "finite-markov-chain-v0",
                "Finite stochastic matrices, one-step distributions, stationarity, and bad stochastic-row/stationary checks.",
            ),
            (
                "finite-hitting-times-v0",
                "Finite first-hit survival replay, expected hitting-time equations, and bad survival/expected-time rows.",
            ),
            (
                "bounded-dynamics-v0",
                "Bounded recurrence and invariant rows that share finite transition-system vocabulary.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite transition replay plus QF_LRA/Farkas kernel-row certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/learn/math/finite-stochastic-kernels-end-to-end.md",
                    "docs/learn/math/finite-markov-chain-end-to-end.md",
                    "docs/learn/math/finite-hitting-times-end-to-end.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes row sums, transition "
                    "composition, and expected-time equations exactly; bad "
                    "row, composed-entry, or threshold claims use checked "
                    "Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/learn/math/finite-stochastic-kernels-end-to-end.md",
            "docs/learn/math/finite-markov-chain-end-to-end.md",
            "docs/learn/math/finite-hitting-times-end-to-end.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite stochastic kernels do not prove regular conditional probabilities or general Markov-process theory.",
            "Mixing, recurrence/transience over infinite state spaces, and optional stopping remain Lean/probability horizons.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite state spaces, transition matrix or kernel table, and exact rational entries.",
                "The validator recomputes row normalization, composed kernels, distributions, and finite linear equations.",
                "Bad kernel or expected-time rows carry source-linked QF_LRA/Farkas evidence before solver reuse is claimed.",
            ],
        },
    },
    {
        "id": "bridge_conditional_expectation",
        "title": "Finite Conditional Expectation",
        "field_ids": ["probability_theory", "measure_theory", "statistics", "real_analysis"],
        "resource_status": "validated",
        "summary": (
            "A finite conditional-expectation row checks a finite partition or "
            "filtration block by recomputing conditional masses, weighted "
            "averages, tower-style finite identities, and martingale table "
            "conditions over exact rational probabilities."
        ),
        "prerequisites": [
            "bridge_probability_mass_table",
            "bridge_pushforward_distribution",
            "curriculum_rationals",
        ],
        "unlocks": [
            "bridge_stochastic_kernel",
            "bridge_lean_horizon",
            "field_measure_theory",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite partitions",
            "finite probability tables",
            "exact rational expectation",
            "QF_LRA",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-conditional-expectation-v0",
                "Finite partition, conditional mean, conditional variance, and bad high-block, total-expectation, tower-property, and variance-decomposition rows.",
            ),
            (
                "finite-martingales-v0",
                "Finite filtration, martingale, submartingale, stopped-expectation, and bad conditional-expectation rows.",
            ),
            (
                "finite-integration-v0",
                "Finite simple-function integral and expectation rows that share exact weighted-sum replay.",
            ),
            (
                "finite-random-variables-v0",
                "Finite random-variable expectation and independence rows used by conditional examples.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite conditional-expectation replay plus QF_LRA/Farkas bad-expectation certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-conditional-expectation-end-to-end.md",
                    "docs/learn/math/finite-martingales-end-to-end.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes block probabilities and "
                    "weighted averages exactly; general conditional "
                    "expectation remains a Lean horizon."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-conditional-expectation-end-to-end.md",
            "docs/learn/math/finite-martingales-end-to-end.md",
            "docs/learn/math/finite-integration-end-to-end.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite conditional-expectation replay does not prove Radon-Nikodym existence, regular conditional probabilities, or stopping-time theorems.",
            "General martingale convergence and optional stopping remain Lean horizons.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite partition or filtration, atom masses, random-variable values, and claimed conditional expectations.",
                "The validator recomputes each conditional block average exactly and rejects corrupted claimed values.",
                "General measure-theoretic conditional expectation is linked as Lean-horizon, not counted as finite solver evidence.",
            ],
        },
    },
    {
        "id": "bridge_finite_product_integration",
        "title": "Finite Product Measure And Integration",
        "field_ids": ["measure_theory", "probability_theory", "statistics", "real_analysis"],
        "resource_status": "validated",
        "summary": (
            "A finite product-measure and integration row checks Cartesian "
            "product atom tables, marginals, finite Fubini-style sums, simple "
            "function integrals, and expectations over exact rational weights "
            "while keeping general Lebesgue integration as a theorem horizon."
        ),
        "prerequisites": [
            "bridge_finite_measure_additivity",
            "bridge_probability_mass_table",
            "bridge_pushforward_distribution",
            "curriculum_rationals",
        ],
        "unlocks": [
            "bridge_conditional_expectation",
            "bridge_random_matrix_finite_moment",
            "field_measure_theory",
            "field_real_analysis",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite products",
            "finite probability tables",
            "exact rational weighted sums",
            "QF_LRA",
            "Farkas certificate",
            "finite replay",
        ],
        "example_packs": [
            (
                "finite-product-measure-v0",
                "Finite product atom table, marginal, Fubini shadow, and bad product-probability rows.",
            ),
            (
                "finite-integration-v0",
                "Finite simple-function integral, indicator integral, expectation, and bad expectation rows.",
            ),
            (
                "finite-conditional-expectation-v0",
                "Partition conditional-expectation rows built from finite weighted sums.",
            ),
            (
                "finite-random-variables-v0",
                "Finite expectation and pushforward rows whose integrals are exact finite sums.",
            ),
            (
                "finite-martingales-v0",
                "Finite filtration, stopped-expectation, and martingale checks that reuse conditional weighted-sum replay.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite product/integral replay plus QF_LRA/Farkas bad-sum certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-product-measure-end-to-end.md",
                    "docs/learn/math/finite-integration-end-to-end.md",
                    "docs/learn/math/finite-conditional-expectation-end-to-end.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes product atom masses, "
                    "marginals, iterated sums, indicator integrals, and "
                    "expectations exactly; false product or integral claims "
                    "graduate only with checked QF_LRA/Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-product-measure-end-to-end.md",
            "docs/learn/math/finite-integration-end-to-end.md",
            "docs/learn/math/finite-conditional-expectation-end-to-end.md",
            "docs/learn/math/finite-random-variables-end-to-end.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite product-table replay does not prove product-measure existence for general measurable spaces.",
            "General Fubini/Tonelli, dominated convergence, Lp-space theory, stochastic-process path measures, and almost-everywhere integration remain Lean horizons.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite factor spaces, atom masses, product table, marginal target, function values, and exact rational sum domain.",
                "The validator recomputes product masses, marginals, finite iterated sums, simple integrals, and expectation values.",
                "Bad product or integration rows carry source-linked QF_LRA/Farkas evidence before solver reuse is claimed.",
            ],
        },
    },
    {
        "id": "bridge_tail_count_obstruction",
        "title": "Finite Tail Count Obstruction",
        "field_ids": ["statistics", "probability_theory", "discrete_math", "measure_theory"],
        "resource_status": "validated",
        "summary": (
            "A finite tail or count-obstruction row checks exact integer "
            "counts, binomial or contingency margins, tail-event masses, and "
            "bad threshold claims using finite enumeration plus LIA or LRA "
            "certificate routes."
        ),
        "prerequisites": [
            "bridge_probability_mass_table",
            "curriculum_counting",
            "curriculum_integers",
        ],
        "unlocks": [
            "field_statistics",
            "field_probability_theory",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite enumeration",
            "QF_LIA / Diophantine",
            "QF_LRA / Farkas",
            "exact rational tail bounds",
            "finite count tables",
        ],
        "example_packs": [
            (
                "exact-statistical-tests-v0",
                "Exact binomial tail counts, hypergeometric rows, and bad tail-count obstruction.",
            ),
            (
                "descriptive-statistics-v0",
                "Finite contingency-table counts and bad total-count rows.",
            ),
            (
                "finite-concentration-v0",
                "Finite tail-probability, union-bound, and bad concentration-bound rows.",
            ),
            (
                "counting-v0",
                "Finite counting rows and pigeonhole refutations that provide the count vocabulary.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite count replay plus QF_LIA/Diophantine or QF_LRA/Farkas bad-threshold certificates",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py, cargo test -p axeyum-solver --test math_resource_lia_routes, and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/learn/math/exact-statistical-tests-end-to-end.md",
                    "docs/learn/math/finite-concentration-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "Integer count contradictions use the Diophantine route; "
                    "exact rational probability threshold contradictions use "
                    "the Farkas route. In both cases the finite table is "
                    "replayed before the solver artifact is trusted."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/learn/math/exact-statistical-tests-end-to-end.md",
            "docs/learn/math/finite-concentration-end-to-end.md",
            "docs/learn/math/probability-and-statistics.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite exact-test and tail rows do not prove asymptotic normality, CLT, concentration inequalities, or statistical inference guarantees.",
            "Floating-point p-values, simulation, and sampling algorithms need separate numerical-honesty metadata before they become proof resources.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite population, table, trial count, event set, or threshold being counted.",
                "The validator recomputes exact integer counts or rational tail masses before checking any solver certificate.",
                "Bad count or probability-threshold rows carry the appropriate checked QF_LIA/Diophantine or QF_LRA/Farkas evidence.",
            ],
        },
    },
    {
        "id": "bridge_homomorphism_preservation",
        "title": "Finite Homomorphism Preservation",
        "field_ids": ["abstract_algebra", "set_theory_and_foundations"],
        "resource_status": "validated",
        "summary": (
            "A finite homomorphism row checks that an explicit map preserves "
            "the listed operation tables pointwise, while keeping general "
            "homomorphism and isomorphism theorems as proof-assistant targets."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "bridge_counterexample_proof",
            "curriculum_relations_and_functions",
        ],
        "unlocks": [
            "bridge_kernel_image",
            "bridge_quotient_map",
            "field_abstract_algebra",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite functions",
            "finite algebra tables",
            "QF_UF",
            "Alethe proof checking",
            "finite replay",
        ],
        "example_packs": [
            (
                "finite-algebra-homomorphisms-v0",
                "Group and ring homomorphism table replay plus checked preservation and bad-map Alethe conflicts.",
            ),
            (
                "finite-groups-v0",
                "Finite group operation replay with an operation-congruence Alethe regression.",
            ),
            (
                "finite-permutation-groups-v0",
                "Permutation composition and sign-homomorphism replay over finite tables.",
            ),
            (
                "finite-modules-v0",
                "Module endomorphism replay with additive and scalar preservation checks.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite homomorphism replay plus QF_UF/Alethe preservation and bad-map conflicts",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/learn/math/finite-algebra-homomorphisms-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The finite checker evaluates every operation-preservation "
                    "equation over the source table; the promoted Alethe rows "
                    "cover both the abstract preservation congruence conflict "
                    "and the concrete bad-map equality conflict."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/learn/math/finite-algebra-homomorphisms-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite preservation replay does not prove homomorphism theorems for arbitrary algebraic structures.",
            "Isomorphism, universal-property, and categorical statements remain Lean horizons until no-sorry reconstruction exists.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite source/codomain tables and the total map.",
                "The validator recomputes preservation for each listed operation and rejects corrupted map entries.",
            "Bad preservation rows carry source-linked QF_UF/Alethe evidence before solver reuse is claimed.",
            "Concrete malformed-map rows keep finite table replay separate from the checked equality conflict.",
            ],
        },
    },
    {
        "id": "bridge_algebra_equality_certificate_boundary",
        "title": "Algebra Equality Certificate Boundary",
        "field_ids": [
            "abstract_algebra",
        ],
        "resource_status": "validated",
        "summary": (
            "This boundary decides when a finite algebra row deserves a "
            "checked equality certificate instead of remaining ordinary table "
            "replay: the table checker must identify a concrete equality, "
            "closure, representative, preservation, identity-action, "
            "action-compatibility, or bilinearity conflict, and the "
            "QF_UF/Alethe artifact must isolate "
            "that proof shape without redoing the whole finite model."
        ),
        "prerequisites": [
            "bridge_finite_model_replay",
            "bridge_counterexample_proof",
            "bridge_homomorphism_preservation",
            "bridge_quotient_map",
        ],
        "unlocks": [
            "bridge_kernel_image",
            "bridge_ideal_closure",
            "bridge_module_action",
            "bridge_tensor_bilinearity",
            "field_abstract_algebra",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite algebra tables",
            "finite functions",
            "QF_UF",
            "EUF congruence",
            "Alethe proof checking",
            "finite replay",
        ],
        "example_packs": [
            (
                "finite-groups-v0",
                "Binary-operation congruence separated from full Cayley-table replay.",
            ),
            (
                "finite-monoids-v0",
                "A malformed associativity table replayed first, then isolated as an equality conflict.",
            ),
            (
                "finite-permutation-groups-v0",
                "Non-bijection replay promoted only for the injectivity equality conflict.",
            ),
            (
                "finite-group-actions-v0",
                "Identity-action table failure isolated as an equality conflict.",
            ),
            (
                "finite-algebra-homomorphisms-v0",
                "Homomorphism preservation and concrete bad-map conflicts kept separate from table replay.",
            ),
            (
                "finite-ideals-v0",
                "Ideal closure replay plus quotient representative congruence as distinct equality artifacts.",
            ),
            (
                "finite-vector-spaces-v0",
                "Subspace closure failure promoted only after the finite vector table identifies the bad sum.",
            ),
            (
                "finite-dual-spaces-v0",
                "Covector additivity failure isolated after function-table replay.",
            ),
            (
                "finite-modules-v0",
                "Submodule scalar-closure failure separated from module table replay.",
            ),
            (
                "finite-tensor-products-v0",
                "Bilinear left-additivity failure isolated as a finite map equality conflict.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite table replay plus scoped QF_UF/Alethe equality certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/learn/math/algebra-equality-certificate-boundary.md",
                    "docs/learn/math/algebra-and-number-theory.md",
                    "docs/foundational-resources/ALGEBRA-STRUCTURE-QUERIES.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The finite checker owns structure evaluation. The Alethe "
                    "row owns only the isolated EUF contradiction or "
                    "congruence obligation, and must link a source SMT-LIB "
                    "artifact plus a route regression before solver reuse is "
                    "claimed."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/learn/math/algebra-equality-certificate-boundary.md",
            "docs/learn/math/algebra-and-number-theory.md",
            "docs/foundational-resources/ALGEBRA-STRUCTURE-QUERIES.md",
            "docs/foundational-resources/MATH-CURRICULUM-COMPREHENSIVE-RESOURCE-PLAN.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "This boundary does not prove arbitrary group, ring, module, quotient, tensor, or isomorphism theorems.",
            "A finite algebra row should not be promoted to this concept merely because it is about algebra; it needs a distinct equality, congruence, closure, representative, preservation, identity-action, action-compatibility, or bilinearity certificate shape.",
            "Lean reconstruction remains partial until recurring finite algebra EUF shapes have kernel-checked routes.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "A candidate row first states and validates the finite algebra table, map, subset, quotient, or bilinear data.",
                "Exact replay identifies the concrete failing equality or representative-independence obligation.",
                "The QF_UF/Alethe source artifact isolates that equality conflict without hiding table enumeration in the solver.",
                "A math_resource_uf_routes regression emits and independently checks UnsatAletheProof evidence.",
                "Learner and query docs keep table replay, certificate checking, and theorem horizons visibly separate.",
            ],
        },
    },
    {
        "id": "bridge_kernel_image",
        "title": "Kernel And Image Replay",
        "field_ids": ["abstract_algebra", "linear_algebra", "set_theory_and_foundations"],
        "resource_status": "validated",
        "summary": (
            "Kernel and image rows recompute the preimage of the identity or "
            "zero element and the range of a finite map, then connect those "
            "sets to homomorphism, linear-map, module-map, and quotient rows."
        ),
        "prerequisites": [
            "bridge_homomorphism_preservation",
            "bridge_rank_nullity",
            "curriculum_groups",
        ],
        "unlocks": [
            "bridge_quotient_map",
            "bridge_module_action",
            "field_linear_algebra",
            "field_abstract_algebra",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite functions",
            "finite algebra tables",
            "finite vector spaces",
            "QF_UF",
            "finite replay",
        ],
        "example_packs": [
            (
                "finite-algebra-homomorphisms-v0",
                "Kernel and image replay for the parity homomorphism from Z/4Z to Z/2Z.",
            ),
            (
                "finite-vector-spaces-v0",
                "Linear-map kernel/image and rank-nullity replay over F2 vector spaces.",
            ),
            (
                "finite-modules-v0",
                "Module endomorphism kernel/image replay over Z/4Z.",
            ),
            (
                "finite-ideals-v0",
                "Ring-homomorphism kernel/image replay for the reduction map.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite kernel/image replay with equality-heavy Alethe conflicts",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "docs/learn/math/matrix-corpus-benchmark-boundary.md",
                    "docs/learn/math/finite-algebra-homomorphisms-end-to-end.md",
                    "docs/learn/math/finite-vector-spaces-end-to-end.md",
                    "docs/learn/math/finite-modules-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "Positive rows replay membership and map images directly; "
                    "negative closure or congruence rows use the shared "
                    "QF_UF/Alethe resource regression when promoted."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/learn/math/matrix-computation-index.md",
            "docs/learn/math/matrix-corpus-benchmark-boundary.md",
            "docs/learn/math/finite-algebra-homomorphisms-end-to-end.md",
            "docs/learn/math/finite-vector-spaces-end-to-end.md",
            "docs/learn/math/finite-modules-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite kernel/image replay does not prove the first isomorphism theorem or rank-nullity in arbitrary settings.",
            "General kernel, image, exactness, and dimension theorems remain Lean horizons.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite map, identity or zero element, listed kernel, and listed image.",
                "The validator recomputes kernel and image from the map table without relying on solver output.",
                "The learner path links finite replay to the missing theorem-level Lean route.",
            ],
        },
    },
    {
        "id": "bridge_quotient_map",
        "title": "Finite Quotient Map",
        "field_ids": ["set_theory_and_foundations", "abstract_algebra", "linear_algebra", "topology"],
        "resource_status": "validated",
        "summary": (
            "A quotient-map row checks a finite equivalence relation, coset or "
            "fiber partition, induced operation table, induced map by "
            "representatives, or quotient topology by preimage-open replay, "
            "with well-definedness and saturation kept explicit."
        ),
        "prerequisites": [
            "bridge_kernel_image",
            "bridge_homomorphism_preservation",
            "curriculum_relations_and_functions",
        ],
        "unlocks": [
            "bridge_finite_quotient_topology_replay",
            "bridge_ideal_closure",
            "bridge_module_action",
            "field_set_theory_and_foundations",
            "field_topology",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite equivalence relations",
            "finite functions",
            "finite algebra tables",
            "QF_UF",
            "Alethe proof checking",
        ],
        "example_packs": [
            (
                "equivalence-classes-v0",
                "Finite equivalence-class, quotient-map fiber, and checked quotient congruence rows.",
            ),
            (
                "finite-algebra-homomorphisms-v0",
                "Kernel quotient and induced-isomorphism replay for the parity homomorphism.",
            ),
            (
                "finite-ideals-v0",
                "Quotient-ring table replay from an ideal in Z/6Z.",
            ),
            (
                "finite-modules-v0",
                "Quotient-module addition and scalar-action replay by representatives.",
            ),
            (
                "finite-quotient-topology-v0",
                "Quotient-map fibers, representative consistency, saturated-open replay, and quotient-open preimage checks for a finite topological quotient.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite quotient replay plus QF_UF/Alethe quotient congruence",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/learn/math/equivalence-classes-end-to-end.md",
                    "docs/learn/math/finite-algebra-homomorphisms-end-to-end.md",
                    "docs/learn/math/finite-ideals-quotient-rings-end-to-end.md",
                    "docs/learn/math/finite-quotient-topology-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The validator recomputes classes, fibers, quotient "
                    "tables, induced maps, quotient-open preimages, and "
                    "saturated subsets; the quotient-map congruence and "
                    "representative-consistency artifacts exercise the "
                    "checked EUF route."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/learn/math/equivalence-classes-end-to-end.md",
            "docs/learn/math/finite-algebra-homomorphisms-end-to-end.md",
            "docs/learn/math/finite-ideals-quotient-rings-end-to-end.md",
            "docs/learn/math/finite-quotient-topology-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite quotient replay does not prove quotient construction theorems, correspondence theorems, or first isomorphism in general.",
            "Finite quotient-topology replay does not prove quotient topology universal properties or arbitrary quotient-map theorem schemas.",
            "Well-definedness must be recomputed explicitly for each finite quotient row.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the equivalence relation, classes or cosets, quotient map, and induced operation or map table.",
                "The validator recomputes partition coverage, representative-independent operations, quotient-open preimages, and saturated subsets where relevant.",
                "General quotient theory remains linked as a Lean horizon.",
            ],
        },
    },
    {
        "id": "bridge_ideal_closure",
        "title": "Finite Ideal Closure",
        "field_ids": ["abstract_algebra", "number_theory", "set_theory_and_foundations"],
        "resource_status": "validated",
        "summary": (
            "A finite ideal row checks additive subgroup closure and absorption "
            "by ring multiplication over an explicit finite ring table, then "
            "uses that ideal as the source of quotient-ring replay."
        ),
        "prerequisites": [
            "bridge_quotient_map",
            "curriculum_rings",
            "curriculum_modular_arithmetic",
        ],
        "unlocks": [
            "bridge_module_action",
            "field_abstract_algebra",
            "field_number_theory",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite rings",
            "finite ideals",
            "finite quotient rings",
            "QF_UF",
            "Alethe proof checking",
        ],
        "example_packs": [
            (
                "finite-ideals-v0",
                "Ideal closure, principal generation, ring-homomorphism kernel/image, quotient-ring replay, and bad ideal rows.",
            ),
            (
                "finite-rings-v0",
                "Finite ring table replay and fixed bad-distributivity QF_BV/DRAT evidence.",
            ),
            (
                "modular-arithmetic-v0",
                "Residue arithmetic and nonunit inverse obstructions feeding quotient-ring examples.",
            ),
            (
                "finite-algebra-homomorphisms-v0",
                "Ring homomorphism replay whose kernels are ideal-like finite sets.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite ideal replay plus QF_UF/Alethe bad-closure certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
                    "docs/learn/math/finite-ideals-quotient-rings-end-to-end.md",
                    "docs/learn/math/finite-rings-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes ideal closure and quotient "
                    "tables; bad additive-closure rows use the checked "
                    "QF_UF/Alethe route, while separate fixed ring-table "
                    "contradictions may use QF_BV/DRAT."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
            "docs/learn/math/finite-ideals-quotient-rings-end-to-end.md",
            "docs/learn/math/finite-rings-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite ideal closure does not prove ideal correspondence, localization, Noetherian/PID/UFD structure, or algebraic geometry claims.",
            "General quotient-ring theorems remain Lean horizons even when the finite quotient table validates.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite ring table, candidate ideal, generated-set witness, and quotient table when present.",
                "The validator recomputes additive closure, additive inverses, zero membership, absorption, and quotient operations.",
                "Bad closure rows carry checked QF_UF/Alethe evidence before solver reuse is claimed.",
            ],
        },
    },
    {
        "id": "bridge_module_action",
        "title": "Finite Module Action",
        "field_ids": ["abstract_algebra", "linear_algebra", "set_theory_and_foundations"],
        "resource_status": "validated",
        "summary": (
            "A finite module-action row checks an explicit scalar-action table "
            "against ring and additive-group operations, then reuses submodule, "
            "homomorphism, kernel/image, and quotient-module replay."
        ),
        "prerequisites": [
            "bridge_ideal_closure",
            "bridge_kernel_image",
            "curriculum_rings",
        ],
        "unlocks": [
            "bridge_tensor_bilinearity",
            "bridge_rank_nullity",
            "field_linear_algebra",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite modules",
            "finite rings",
            "finite functions",
            "QF_UF",
            "finite replay",
        ],
        "example_packs": [
            (
                "finite-modules-v0",
                "Finite Z/4Z module table, submodule, module homomorphism, kernel/image, quotient-module, and bad submodule rows.",
            ),
            (
                "finite-vector-spaces-v0",
                "Finite vector-space rows as field-module special cases.",
            ),
            (
                "finite-dual-spaces-v0",
                "Finite dual-space and covector rows over F2.",
            ),
            (
                "finite-tensor-products-v0",
                "Tensor rows that depend on finite module/vector-space actions.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite module replay plus QF_UF/Alethe submodule conflict",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "docs/learn/math/matrix-corpus-benchmark-boundary.md",
                    "docs/learn/math/finite-modules-end-to-end.md",
                    "docs/learn/math/finite-vector-spaces-end-to-end.md",
                    "docs/learn/math/finite-dual-spaces-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The finite checker recomputes module laws, submodule "
                    "closure, homomorphism preservation, and quotient-module "
                    "tables; the bad submodule row uses checked QF_UF/Alethe evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/learn/math/matrix-computation-index.md",
            "docs/learn/math/matrix-corpus-benchmark-boundary.md",
            "docs/learn/math/finite-modules-end-to-end.md",
            "docs/learn/math/finite-vector-spaces-end-to-end.md",
            "docs/learn/math/finite-dual-spaces-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite module-action replay does not prove general module theory, exact sequences, projective/injective modules, or homological algebra.",
            "Linear algebra over arbitrary fields and infinite-dimensional module facts remain Lean horizons.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite ring, additive carrier, scalar-action table, and any submodule or homomorphism witnesses.",
                "The validator recomputes module laws and rejects corrupted scalar-closure or homomorphism rows.",
                "The lesson distinguishes finite module replay from general module theory.",
            ],
        },
    },
    {
        "id": "bridge_tensor_bilinearity",
        "title": "Tensor Bilinearity Replay",
        "field_ids": [
            "linear_algebra",
            "abstract_algebra",
            "set_theory_and_foundations",
            "functional_analysis_and_operator_theory",
        ],
        "resource_status": "validated",
        "summary": (
            "A finite tensor row checks bilinearity and a bounded "
            "universal-property shadow over explicit finite vector-space or "
            "module tables, while general tensor theory remains a Lean horizon."
        ),
        "prerequisites": [
            "bridge_module_action",
            "bridge_homomorphism_preservation",
            "curriculum_linear_algebra",
        ],
        "unlocks": [
            "field_functional_analysis_and_operator_theory",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite vector spaces",
            "finite modules",
            "finite bilinear maps",
            "QF_UF",
            "Alethe proof checking",
        ],
        "example_packs": [
            (
                "finite-tensor-products-v0",
                "Finite tensor basis, bilinear map, factorization shadow, and bad bilinear-map rows.",
            ),
            (
                "finite-vector-spaces-v0",
                "Finite vector-space carrier, basis, and linear-map rows used by tensor examples.",
            ),
            (
                "finite-dual-spaces-v0",
                "Finite covector rows that share linear functional vocabulary.",
            ),
            (
                "finite-modules-v0",
                "Finite module action and homomorphism rows that tensor examples generalize.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite bilinear replay plus QF_UF/Alethe bad-bilinearity certificate",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_uf_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "docs/learn/math/matrix-corpus-benchmark-boundary.md",
                    "docs/learn/math/finite-tensor-products-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
                ],
                "notes": (
                    "The validator exhaustively checks finite additivity and "
                    "scalar preservation in each argument; the bad bilinear row "
                    "uses the shared QF_UF/Alethe regression."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-uf-congruence-alethe.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/matrix-computation-index.md",
            "docs/learn/math/matrix-corpus-benchmark-boundary.md",
            "docs/learn/math/finite-tensor-products-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_uf_routes.rs",
        ],
        "open_gaps": [
            "Finite tensor bilinearity replay does not prove the tensor-product universal property over arbitrary modules.",
            "Exterior powers, symmetric powers, exactness, and homological algebra remain Lean-horizon topics.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite scalar field or ring, source carriers, codomain, and bilinear table.",
                "The validator recomputes additivity and scalar preservation in each argument and any listed factorization.",
                "General tensor-product theorem claims remain linked as Lean horizons.",
            ],
        },
    },
    {
        "id": "bridge_group_action",
        "title": "Finite Group Action",
        "field_ids": ["abstract_algebra", "discrete_math", "set_theory_and_foundations"],
        "resource_status": "validated",
        "summary": (
            "A finite group-action row checks identity and compatibility of an "
            "explicit action table, then recomputes orbits, stabilizers, "
            "orbit-stabilizer counts, and finite Burnside averages."
        ),
        "prerequisites": [
            "bridge_homomorphism_preservation",
            "curriculum_groups",
            "curriculum_counting",
        ],
        "unlocks": [
            "field_abstract_algebra",
            "field_discrete_math",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite group actions",
            "finite functions",
            "finite counting",
            "QF_UF",
            "finite replay",
        ],
        "example_packs": [
            (
                "finite-group-actions-v0",
                "Action-law, orbit, stabilizer, orbit-stabilizer, Burnside, bad identity-action, bad compatibility, and horizon rows.",
            ),
            (
                "finite-permutation-groups-v0",
                "Natural permutation action, orbit/stabilizer, cycle, and sign rows.",
            ),
            (
                "finite-groups-v0",
                "Group Cayley-table rows that provide the acting group structure.",
            ),
            (
                "counting-v0",
                "Finite counting examples that share orbit-counting and enumeration vocabulary.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite action-table replay",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py",
                "lean_status": "required",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-group-actions-end-to-end.md",
                    "docs/learn/math/finite-permutation-groups-end-to-end.md",
                ],
                "notes": (
                    "The finite checker recomputes action laws, orbits, "
                    "stabilizers, and Burnside fixed-point averages. General "
                    "orbit-stabilizer, Burnside, and representation-theory "
                    "statements remain Lean-horizon."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-group-actions-end-to-end.md",
            "docs/learn/math/finite-permutation-groups-end-to-end.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
        ],
        "open_gaps": [
            "Finite action replay does not prove general orbit-stabilizer, Burnside/Cauchy-Frobenius, or representation-theory theorems.",
            "Group actions on algebraic, topological, or analytic structures need their own concept rows and proof routes.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite group table, set carrier, action table, and target orbit/stabilizer/count claim.",
                "The validator recomputes identity action, compatibility, orbits, stabilizers, and fixed-point counts.",
                "General group-action theorems remain linked as Lean horizons.",
            ],
        },
    },
    {
        "id": "bridge_coordinate_orientation_geometry",
        "title": "Coordinate And Oriented Geometry Replay",
        "field_ids": ["geometry", "linear_algebra", "real_analysis"],
        "resource_status": "validated",
        "summary": (
            "Finite coordinate-geometry rows turn incidence, line equations, "
            "rigid distance tables, midpoint, collinearity, squared-distance, "
            "affine-map, signed-area, circle-point, tangent-line, "
            "chord-midpoint, inversion-image, and cyclic-configuration "
            "claims into exact rational replay obligations with checked "
            "Farkas conflicts for malformed linearized claims."
        ),
        "prerequisites": [
            "curriculum_reals",
            "curriculum_linear_algebra",
            "bridge_qf_lra_farkas_anatomy",
            "bridge_bounded_theorem_shadow",
        ],
        "unlocks": [
            "field_geometry",
            "field_linear_algebra",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "QF_LRA",
            "finite coordinate replay",
            "signed-area determinants",
            "affine map tables",
            "finite circle-geometry replay",
            "finite inversion replay",
            "finite cyclic-configuration replay",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "coordinate-geometry-v0",
                "Midpoint, collinearity, squared-distance, and bad-distance replay over exact rational coordinates.",
            ),
            (
                "orientation-area-geometry-v0",
                "Signed double-area orientation, affine area-scaling, barycentric coordinate, and bad area/orientation rows.",
            ),
            (
                "incidence-geometry-v0",
                "Line equations, point-on-line replay, non-parallel intersections, and bad-incidence rows.",
            ),
            (
                "rigid-configuration-geometry-v0",
                "Triangle distance tables, translation isometry replay, congruent-triangle distances, and bad-rigidity rows.",
            ),
            (
                "affine-geometry-v0",
                "Affine map composition, barycentric interpolation, fixed coordinate transforms, and bad collinearity/distance-preservation rows.",
            ),
            (
                "finite-circle-geometry-v0",
                "Point-on-circle, tangent-line, chord-midpoint perpendicularity, and bad-radius rows over exact rational coordinates.",
            ),
            (
                "finite-inversion-geometry-v0",
                "Unit-circle inversion image, inverse-distance product, collinearity, and bad inverse-coordinate rows.",
            ),
            (
                "finite-cyclic-geometry-v0",
                "Cyclic quadrilateral, diagonal-intersection, opposite-angle, and bad-intersection rows.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite coordinate replay plus QF_LRA/Farkas",
                "status": "checked",
                "checker": "cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/coordinate-affine-geometry-end-to-end.md",
                    "docs/learn/math/finite-circle-geometry-end-to-end.md",
                    "docs/learn/math/finite-inversion-geometry-end-to-end.md",
                    "docs/learn/math/finite-cyclic-geometry-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The packs replay the coordinate calculation first, then "
                    "use the shared exact-rational Farkas route only for the "
                    "small contradiction exposed by that replay."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/coordinate-affine-geometry-end-to-end.md",
            "docs/learn/math/finite-circle-geometry-end-to-end.md",
            "docs/learn/math/finite-inversion-geometry-end-to-end.md",
            "docs/learn/math/finite-cyclic-geometry-end-to-end.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "The finite coordinate rows do not prove synthetic Euclidean, projective, differential, or global geometry theorems.",
            "Polynomial distance and incidence claims are replayed only when the source pack reduces them to exact finite arithmetic with an explicit proof route.",
            "General circle theorems, inversion, cyclic quadrilaterals, and power-of-a-point remain Lean-horizon until kernel-checked proof routes exist.",
            "General geometric theorem statements remain Lean-horizon until a kernel-checked route exists.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state finite point sets, exact rational coordinates, and the coordinate formula being replayed.",
                "Malformed exact-linear or linearized rows link to a checked QF_LRA/Farkas regression.",
                "Learner pages keep coordinate replay separate from synthetic or analytic geometry horizons.",
            ],
        },
    },
    {
        "id": "bridge_finite_circle_inversion_cyclic_replay",
        "title": "Finite Circle Inversion And Cyclic Replay",
        "field_ids": ["geometry", "linear_algebra", "real_analysis"],
        "resource_status": "validated",
        "summary": (
            "Finite circle, inversion, and cyclic-configuration rows state "
            "exact rational coordinates, a circle or inversion center, witness "
            "points, and the coordinate formula being checked. The trusted "
            "object is replay of point-on-circle, tangent, chord, inversion, "
            "distance-product, collinearity, or cyclic-quadrilateral data, or "
            "a checked QF_LRA/Farkas certificate for a malformed fixed claim."
        ),
        "prerequisites": [
            "bridge_coordinate_orientation_geometry",
            "bridge_qf_lra_farkas_anatomy",
            "bridge_bounded_theorem_shadow",
            "curriculum_reals",
            "curriculum_linear_algebra",
            "curriculum_polynomials",
        ],
        "unlocks": [
            "field_geometry",
            "field_real_analysis",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite coordinate replay",
            "finite polynomial geometry",
            "finite circle-geometry replay",
            "finite inversion replay",
            "finite cyclic-configuration replay",
            "QF_LRA",
            "Farkas certificate",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-circle-geometry-v0",
                "Point-on-circle, tangent-line, chord-midpoint perpendicularity, and checked bad-radius rows.",
            ),
            (
                "finite-inversion-geometry-v0",
                "Unit-circle inversion image, inverse-distance product, collinearity, and checked bad inverse-coordinate rows.",
            ),
            (
                "finite-cyclic-geometry-v0",
                "Cyclic quadrilateral replay, diagonal-intersection, opposite-angle, and checked bad-intersection rows.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite circle/inversion/cyclic replay plus QF_LRA/Farkas",
                "status": "checked",
                "checker": "scripts/validate-foundational-example-pack.py and cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/finite-circle-geometry-end-to-end.md",
                    "docs/learn/math/finite-inversion-geometry-end-to-end.md",
                    "docs/learn/math/finite-cyclic-geometry-end-to-end.md",
                    "docs/learn/math/coordinate-affine-geometry-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The packs replay the exact rational coordinate formula "
                    "first; malformed rows graduate only when the exposed "
                    "linear contradiction has rechecked Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/finite-circle-geometry-end-to-end.md",
            "docs/learn/math/finite-inversion-geometry-end-to-end.md",
            "docs/learn/math/finite-cyclic-geometry-end-to-end.md",
            "docs/learn/math/coordinate-affine-geometry-end-to-end.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite circle/inversion/cyclic replay does not prove general Euclidean circle theorems, inversion theorems, cyclic-quadrilateral theorems, power-of-a-point, or Ptolemy.",
            "Angle preservation, circle-line correspondences, and synthetic theorem statements remain Lean-horizon until kernel-checked proof routes exist.",
            "Higher-degree polynomial geometry is included only when a pack states a fixed finite coordinate obligation and a checked proof route.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the circle/inversion parameters, finite point set, exact rational coordinates, and witness relation being replayed.",
                "The validator recomputes circle membership, tangent or chord constraints, inversion coordinates, distance products, collinearity, or cyclic configuration data.",
                "Malformed fixed rows link source artifacts or route regressions before claiming checked Farkas evidence.",
            ],
        },
    },
    {
        "id": "bridge_complex_real_pair_transform",
        "title": "Complex Real-Pair Transform Replay",
        "field_ids": ["complex_analysis", "real_analysis", "linear_algebra", "abstract_algebra"],
        "resource_status": "validated",
        "summary": (
            "Complex arithmetic, conjugation, norm, root-cycle, and small "
            "rational-transform claims are represented as exact real-pair "
            "calculations, with analytic complex analysis kept as an explicit "
            "Lean horizon."
        ),
        "prerequisites": [
            "curriculum_complex",
            "curriculum_reals",
            "curriculum_polynomials",
            "bridge_qf_lra_farkas_anatomy",
            "bridge_bounded_theorem_shadow",
        ],
        "unlocks": [
            "field_complex_analysis",
            "field_real_analysis",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "real-pair algebra",
            "QF_LRA",
            "NRA over exact rational pairs",
            "finite rational-function replay",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "complex-algebraic-v0",
                "Exact complex addition, multiplication, conjugation, norm-squared, bad product-coordinate, and bad norm rows.",
            ),
            (
                "complex-plane-transforms-v0",
                "Unit-root cycle, conjugation product, Mobius-transform witness, bad conjugation-product imaginary-part, and bad unit-square real-part rows.",
            ),
            (
                "polynomial-factorization-rational-v0",
                "Fixed polynomial factorization and discriminant rows that supply the algebraic boundary vocabulary.",
            ),
        ],
        "proof_routes": [
            {
                "name": "real-pair replay plus QF_LRA/Farkas",
                "status": "checked",
                "checker": "cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/complex-algebraic-end-to-end.md",
                    "docs/learn/math/complex-plane-transforms-end-to-end.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The packs replay exact real and imaginary components from "
                    "the source complex expression, then check only the final "
                    "small rational contradiction through Farkas evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/complex-algebraic-end-to-end.md",
            "docs/learn/math/complex-plane-transforms-end-to-end.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Real-pair algebra replay does not prove holomorphicity, contour integration, residues, analytic continuation, or algebraic closure.",
            "NRA-shaped complex identities remain bounded shadows unless they reduce to a checked exact-rational route.",
            "Analytic complex-analysis theorem statements remain Lean-horizon until no-sorry Lean artifacts exist.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the exact complex expression and its real-pair expansion.",
                "Bad real-part, norm, or polynomial-boundary rows link to checked QF_LRA/Farkas regressions after replay.",
                "Learner pages keep algebraic real-pair replay separate from analytic complex-analysis horizons.",
            ],
        },
    },
    {
        "id": "bridge_inner_product_projection",
        "title": "Finite Inner-Product And Projection Replay",
        "field_ids": [
            "functional_analysis_and_operator_theory",
            "linear_algebra",
            "numerical_analysis",
            "optimization_and_convexity",
            "real_analysis",
        ],
        "resource_status": "validated",
        "summary": (
            "Finite-dimensional inner-product rows replay exact rational Gram "
            "matrices, norm squares, fixed-vector Cauchy-Schwarz checks, "
            "orthogonal projections, and Gram-Schmidt steps while keeping "
            "Hilbert-space theorems as Lean horizons."
        ),
        "prerequisites": [
            "curriculum_linear_algebra",
            "curriculum_rationals",
            "curriculum_reals",
            "bridge_residual_bound",
            "bridge_qf_lra_farkas_anatomy",
        ],
        "unlocks": [
            "field_functional_analysis_and_operator_theory",
            "field_numerical_analysis",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite-dimensional linear algebra",
            "Gram matrices",
            "orthogonal projection",
            "QF_LRA",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "inner-product-spaces-rational-v0",
                "Exact inner-product, Gram-matrix, projection, Gram-Schmidt, and bad norm rows.",
            ),
            (
                "numerical-linear-algebra-v0",
                "Residual-bound and finite matrix rows that share projection and norm vocabulary.",
            ),
            (
                "least-squares-regression-v0",
                "Normal-equation and finite regression rows that use projection-style exact linear replay.",
            ),
            (
                "finite-dual-spaces-v0",
                "Finite covector, pairing, annihilator, and transpose rows that supply dual-space vocabulary.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite inner-product replay plus QF_LRA/Farkas",
                "status": "checked",
                "checker": "cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "docs/learn/math/matrix-corpus-benchmark-boundary.md",
                    "docs/learn/math/inner-product-spaces-end-to-end.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "The finite pack recomputes each rational inner-product "
                    "quantity first; checked Farkas evidence is used only for "
                    "the small bad positivity or linear-equation conflict."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/matrix-computation-index.md",
            "docs/learn/math/matrix-corpus-benchmark-boundary.md",
            "docs/learn/math/inner-product-spaces-end-to-end.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite rational projection replay does not prove the Hilbert projection theorem, Riesz representation, Hahn-Banach, or completeness results.",
            "Rows involving floating-point orthogonality, conditioning, or numerical stability require separate numerical-honesty metadata.",
            "General inner-product, duality, and Hilbert-space theorem statements remain Lean-horizon until no-sorry Lean artifacts exist.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite vector space, basis, Gram matrix, and exact rational vectors.",
                "The validator recomputes norm squares, projections, Gram-Schmidt steps, and residuals from source data.",
                "Malformed finite positivity or projection rows link to checked QF_LRA/Farkas regressions after replay.",
            ],
        },
    },
    {
        "id": "bridge_finite_operator_chebyshev",
        "title": "Finite Operator And Chebyshev Replay",
        "field_ids": [
            "functional_analysis_and_operator_theory",
            "numerical_analysis",
            "linear_algebra",
            "real_analysis",
        ],
        "resource_status": "validated",
        "summary": (
            "Finite operator rows replay exact rational norm and matrix-action "
            "bounds, while finite Chebyshev rows replay polynomial bases, "
            "interpolation matrices, duplicate-node failures, and alternating "
            "residual witnesses."
        ),
        "prerequisites": [
            "curriculum_linear_algebra",
            "curriculum_polynomials",
            "curriculum_reals",
            "bridge_inner_product_projection",
            "bridge_qf_lra_farkas_anatomy",
        ],
        "unlocks": [
            "field_functional_analysis_and_operator_theory",
            "field_numerical_analysis",
            "bridge_lean_horizon",
        ],
        "decidability": "bounded",
        "axeyum_fragments": [
            "finite-dimensional operators",
            "Chebyshev polynomial recurrence",
            "interpolation matrices",
            "QF_LRA",
            "Lean horizon",
        ],
        "example_packs": [
            (
                "finite-operator-v0",
                "Finite-dimensional norm, operator-bound, Chebyshev recurrence, bad operator-bound, and bad Chebyshev-prefix rows.",
            ),
            (
                "finite-chebyshev-systems-v0",
                "Vandermonde unisolvence, interpolation polynomial, alternating residual, and duplicate-node rows.",
            ),
            (
                "spectral-linear-algebra-v0",
                "Fixed spectral rows that share finite-operator and eigenpair vocabulary.",
            ),
            (
                "matrix-invariants-v0",
                "Characteristic-polynomial and finite matrix-invariant rows that supply operator polynomial vocabulary.",
            ),
        ],
        "proof_routes": [
            {
                "name": "finite operator replay plus QF_LRA/Farkas",
                "status": "checked",
                "checker": "cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/finite-model-replay.md",
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/proof-cookbook/recipes/lean-horizon-template.md",
                    "docs/learn/math/matrix-computation-index.md",
                    "docs/learn/math/matrix-corpus-benchmark-boundary.md",
                    "docs/learn/math/chebyshev-operator-index.md",
                    "docs/learn/math/finite-operator-end-to-end.md",
                    "docs/learn/math/finite-chebyshev-systems-end-to-end.md",
                    "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "Finite operator and Chebyshev packs replay the exact "
                    "matrix, norm, recurrence, or interpolation calculation "
                    "before handing the resulting small rational conflict to "
                    "the shared Farkas route."
                ),
            }
        ],
        "source_refs": [
            "docs/foundational-resources/MATH-FIELDS.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "docs/proof-cookbook/recipes/finite-model-replay.md",
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/proof-cookbook/recipes/lean-horizon-template.md",
            "docs/learn/math/matrix-computation-index.md",
            "docs/learn/math/matrix-corpus-benchmark-boundary.md",
            "docs/learn/math/chebyshev-operator-index.md",
            "docs/learn/math/finite-operator-end-to-end.md",
            "docs/learn/math/finite-chebyshev-systems-end-to-end.md",
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "Finite operator replay does not prove Banach-space, Hilbert-space, compact-operator, or spectral theorem claims.",
            "Finite Chebyshev grid replay does not prove Haar, minimax, alternation, or infinite-dimensional approximation theorems.",
            "General functional-analysis theorem statements remain Lean-horizon until no-sorry Lean artifacts exist.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Rows state the finite vector space, operator matrix, norm, polynomial basis, or sample grid being replayed.",
                "The validator recomputes matrix actions, norms, recurrence values, interpolation rows, and alternating residual witnesses.",
                "Malformed finite operator, recurrence, or interpolation rows link to checked QF_LRA/Farkas regressions after replay.",
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
            "docs/learn/math/analysis-calculus-theorem-horizon-map.md",
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
    {
        "id": "family_exact_rational_farkas",
        "title": "Exact Rational Farkas Infeasibility Family",
        "field_ids": ["optimization_and_convexity"],
        "resource_status": "validated",
        "summary": (
            "Recurring exact-rational contradictions that reduce to small "
            "linear equalities or inequalities and recheck as certified "
            "QF_LRA/Farkas evidence."
        ),
        "prerequisites": [
            "bridge_counterexample_proof",
            "bridge_bounded_theorem_shadow",
            "curriculum_rationals",
            "curriculum_reals",
            "curriculum_linear_algebra",
        ],
        "unlocks": ["field_optimization_and_convexity"],
        "decidability": "decidable",
        "axeyum_fragments": [
            "QF_LRA",
            "Farkas certificate",
            "exact rational arithmetic",
            "finite model replay",
        ],
        "example_packs": [
            (
                "rationals-lra-v0",
                "Fixed trichotomy and order-transitivity contradictions over exact rationals.",
            ),
            (
                "linear-algebra-rational-v0",
                "Singular inconsistent linear system rejected by exact rational infeasibility.",
            ),
            (
                "linear-optimization-v0",
                "Objective-threshold infeasibility for a tiny linear program.",
            ),
            (
                "convexity-rational-v0",
                "Bad midpoint-convexity claim reduced to a linear inequality conflict.",
            ),
            (
                "finite-concentration-v0",
                "Bad finite tail-bound inequality rejected after exact replay.",
            ),
            (
                "finite-probability-v0",
                "Bad normalization, Bayes-posterior, and independence rows rejected by exact rational constraints.",
            ),
            (
                "finite-markov-chain-v0",
                "Malformed stochastic-row and stationary-distribution equations rejected after row-sum and transition replay.",
            ),
            (
                "finite-hitting-times-v0",
                "Bad survival-mass and expected-time equations rejected after exact finite replay.",
            ),
            (
                "least-squares-regression-v0",
                "Bad regression coefficients and bad RSS-improvement claims rejected through exact linear conflicts.",
            ),
            (
                "real-analysis-rational-v0",
                "Bad bounded linear epsilon-delta claim rejected as a rational bound conflict.",
            ),
            (
                "finite-conditional-expectation-v0",
                "Bad block-expectation table rejected after exact averaging replay.",
            ),
            (
                "finite-euler-method-v0",
                "Bad explicit-Euler step rejected after exact derivative replay.",
            ),
            (
                "orientation-area-geometry-v0",
                "False affine-area scaling and orientation claims rejected after signed-area replay.",
            ),
            (
                "numerical-linear-algebra-v0",
                "False residual, solution-box, and Jacobi error-bound claims rejected as rational inequality conflicts.",
            ),
            (
                "random-matrix-finite-v0",
                "Bad trace-square moment and expected-rank claims rejected after finite exact replay.",
            ),
            (
                "affine-geometry-v0",
                "False collinearity-determinant and distance-preservation claims rejected after affine replay.",
            ),
            (
                "inner-product-spaces-rational-v0",
                "Bad negative-norm row rejected as an exact rational order conflict.",
            ),
            (
                "spectral-linear-algebra-v0",
                "False eigenpair component rejected after matrix-vector replay.",
            ),
            (
                "matrix-invariants-v0",
                "Bad characteristic-polynomial value rejected after witness-root replay.",
            ),
        ],
        "proof_routes": [
            {
                "name": "QF_LRA/Farkas rational infeasibility family",
                "status": "checked",
                "checker": "cargo test -p axeyum-solver --test math_resource_lra_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/qf-lra-farkas.md",
                    "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
                    "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
                ],
                "notes": (
                    "Each referenced pack keeps finite replay separate from "
                    "the Farkas proof artifact; the regression constructs the "
                    "exact rational contradiction, requires Evidence::UnsatFarkas, "
                    "and independently rechecks the certified trust step."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/qf-lra-farkas.md",
            "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lra_routes.rs",
        ],
        "open_gaps": [
            "The family certifies fixed exact-rational infeasibility rows, not nonlinear analysis or optimization theorems.",
            "New rational packs should join this family only after they have a source-linked example row and a checked math_resource_lra_routes regression.",
            "Lean reconstruction remains partial at the family level until the QF_LRA/Farkas proof route is kernel-checked for every recurring shape.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Every family pack row links a concrete exact-rational artifact or source-backed regression.",
                "cargo test -p axeyum-solver --test math_resource_lra_routes passes.",
                "Learner pages keep finite replay separate from the checked Farkas certificate.",
            ],
        },
    },
    {
        "id": "family_boolean_cnf_lrat",
        "title": "Boolean CNF/LRAT Refutation Family",
        "field_ids": [
            "logic_and_proof",
            "discrete_math",
            "graph_theory",
            "set_theory_and_foundations",
            "topology",
        ],
        "resource_status": "validated",
        "summary": (
            "Recurring finite refutations that compile to small Boolean CNF "
            "artifacts and recheck through generated DRAT proofs plus "
            "elaborated LRAT certificates."
        ),
        "prerequisites": [
            "bridge_counterexample_proof",
            "bridge_refutation_query",
            "bridge_boolean_cnf_lrat_anatomy",
            "curriculum_propositional_logic",
            "curriculum_proof_methods",
            "curriculum_counting",
            "curriculum_sets",
        ],
        "unlocks": [
            "field_logic_and_proof",
            "field_graph_theory",
            "field_set_theory_and_foundations",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "Bool / SAT",
            "CNF",
            "DRAT proof checking",
            "LRAT proof checking",
            "finite refutation",
        ],
        "example_packs": [
            (
                "logic-basics-v0",
                "Tiny Boolean contradiction refutation with checked DRAT/LRAT evidence.",
            ),
            (
                "proof-methods-refutation-v0",
                "PHP(3,2) proof-by-refutation row with source-linked CNF evidence.",
            ),
            (
                "proof-methods-patterns-v0",
                "Contradiction proof pattern reduced to a small unsat CNF.",
            ),
            (
                "counting-v0",
                "Finite pigeonhole refutation reusing the same CNF proof route.",
            ),
            (
                "finite-predicate-v0",
                "Finite quantifier expansion row compiled to Boolean CNF.",
            ),
            (
                "finite-sets-v0",
                "Malformed finite set identity rejected by a source-linked CNF artifact.",
            ),
            (
                "finite-cardinality-v0",
                "No-injection finite cardinality row rechecked through CNF/LRAT.",
            ),
            (
                "finite-order-lattices-v0",
                "Bad Boolean-lattice top-element claim encoded as a one-variable CNF.",
            ),
            (
                "graph-coloring-v0",
                "Triangle non-2-colorability as a compact Boolean refutation.",
            ),
            (
                "graph-reachability-v0",
                "Disconnected no-path row encoded as bounded reachability CNF.",
            ),
            (
                "graph-matching-v0",
                "Triangle no-perfect-matching row encoded as finite matching CNF.",
            ),
            (
                "graph-cut-v0",
                "Bad one-edge cut row encoded as post-removal reachability CNF.",
            ),
            (
                "graph-d-separation-v0",
                "Conditioned chain-blocking row encoded as finite DAG path CNF.",
            ),
            (
                "finite-topology-v0",
                "Missing-empty-open topology axiom row encoded as a one-variable CNF.",
            ),
            (
                "finite-compactness-v0",
                "Bad finite open-cover row encoded as a compact Boolean refutation.",
            ),
            (
                "finite-connectedness-v0",
                "Bad connectedness claim encoded as a checked Boolean refutation.",
            ),
        ],
        "proof_routes": [
            {
                "name": "Boolean CNF/DRAT/LRAT refutation family",
                "status": "checked",
                "checker": "cargo test -p axeyum-cnf --test math_resource_boolean_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
                    "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
                    "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
                ],
                "notes": (
                    "Each referenced pack keeps the source finite object "
                    "separate from the Boolean encoding; the regression parses "
                    "the committed DIMACS artifact, emits DRAT, elaborates to "
                    "LRAT, and checks that corrupted proof hints reject."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/boolean-cnf-lrat.md",
            "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-cnf/tests/math_resource_boolean_routes.rs",
        ],
        "open_gaps": [
            "The family certifies the committed finite CNF artifacts, not arbitrary graph, topology, set, or proof-method theorems.",
            "New Boolean-resource packs should join this family only after they have a source-linked DIMACS artifact and a checked math_resource_boolean_routes regression.",
            "Lean reconstruction remains partial at the family level until the Boolean CNF/LRAT route is kernel-checked back to the original finite claim.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Every family pack row links a committed DIMACS artifact and Boolean proof-route regression.",
                "cargo test -p axeyum-cnf --test math_resource_boolean_routes passes.",
                "Learner pages keep the source finite model separate from the checked DRAT/LRAT certificate.",
            ],
        },
    },
    {
        "id": "family_integer_diophantine",
        "title": "Integer Diophantine And Count Obstruction Family",
        "field_ids": ["number_theory", "discrete_math"],
        "resource_status": "validated",
        "summary": (
            "Recurring integer equalities, count contradictions, coefficient "
            "obstructions, and bounded arithmetic claims that recheck through "
            "QF_LIA Diophantine certificates or arithmetic-DPLL evidence."
        ),
        "prerequisites": [
            "bridge_counterexample_proof",
            "bridge_bounded_induction_obligation",
            "curriculum_naturals",
            "curriculum_integers",
            "curriculum_modular_arithmetic",
            "curriculum_counting",
            "curriculum_polynomials",
        ],
        "unlocks": [
            "field_number_theory",
            "field_discrete_math",
            "curriculum_number_theory",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "QF_LIA",
            "Diophantine certificate",
            "arithmetic-DPLL proof checking",
            "integer count replay",
            "finite coefficient replay",
        ],
        "example_packs": [
            (
                "modular-arithmetic-v0",
                "Nonunit modular inverse obstruction encoded as 2*b - 6*k = 1.",
            ),
            (
                "gcd-bezout-v0",
                "Fixed Bezout obstruction where gcd(6,10) does not divide 15.",
            ),
            (
                "integer-lia-v0",
                "Fixed integer infeasibility rows, including 2*x + 4*y = 3.",
            ),
            (
                "natural-arithmetic-v0",
                "Bounded natural-domain negative-element rejection through arithmetic-DPLL.",
            ),
            (
                "induction-obligations-v0",
                "Bounded induction step-count contradiction after finite replay computes zero bad steps.",
            ),
            (
                "induction-patterns-v0",
                "Finite even-product oddness obstruction checked as an integer equality conflict.",
            ),
            (
                "cardinality-principles-v0",
                "Overlap-additivity count contradiction after finite set replay computes the true union count.",
            ),
            (
                "generating-functions-v0",
                "Bad Cauchy-product coefficient row reduced to an integer coefficient contradiction.",
            ),
            (
                "polynomial-identities-v0",
                "False rational-root row reduced to a fixed integer evaluation contradiction.",
            ),
            (
                "descriptive-statistics-v0",
                "Bad contingency-table total rejected as an integer margin/count conflict.",
            ),
            (
                "exact-statistical-tests-v0",
                "Bad finite binomial tail count rejected by an integer count certificate.",
            ),
            (
                "finite-simplicial-homology-v0",
                "Bad boundary coefficient row reduced to a signed integer coefficient conflict.",
            ),
            (
                "graph-search-runtime-v0",
                "Bad DFS cost bound rejected through a tiny arithmetic-DPLL contradiction.",
            ),
        ],
        "proof_routes": [
            {
                "name": "QF_LIA/Diophantine integer obstruction family",
                "status": "checked",
                "checker": "cargo test -p axeyum-solver --test math_resource_lia_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
                    "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
                    "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
                ],
                "notes": (
                    "Each referenced pack keeps the source finite replay or "
                    "integer computation separate from the solver proof; the "
                    "regression parses the committed SMT-LIB row and requires "
                    "either UnsatDiophantine or checked arithmetic-DPLL evidence."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/qf-lia-diophantine.md",
            "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_lia_routes.rs",
        ],
        "open_gaps": [
            "The family certifies fixed integer and count contradictions, not arbitrary number-theory, combinatorics, statistics, or homology theorems.",
            "New integer-resource packs should join this family only after they have a source-linked SMT-LIB artifact and a checked math_resource_lia_routes regression.",
            "Lean reconstruction remains partial at the family level until the QF_LIA proof routes are kernel-checked back to the original finite claim.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Every family pack row links a committed SMT-LIB artifact or source-backed QF_LIA regression.",
                "cargo test -p axeyum-solver --test math_resource_lia_routes passes.",
                "Learner pages keep finite/count replay separate from the checked integer certificate.",
            ],
        },
    },
    {
        "id": "family_fixed_width_bv_drat",
        "title": "Fixed-Width QF_BV DRAT Family",
        "field_ids": ["abstract_algebra", "number_theory", "graph_theory"],
        "resource_status": "validated",
        "summary": (
            "Recurring fixed-width finite algebra, residue, and one-bit graph "
            "encoding contradictions that lower through QF_BV bit-blasting and "
            "recheck with a generated DIMACS/DRAT certificate."
        ),
        "prerequisites": [
            "bridge_counterexample_proof",
            "bridge_qf_bv_bitblast_anatomy",
            "curriculum_fields",
            "curriculum_rings",
            "curriculum_modular_arithmetic",
            "curriculum_number_theory",
        ],
        "unlocks": [
            "field_abstract_algebra",
            "field_number_theory",
            "field_graph_theory",
        ],
        "decidability": "decidable",
        "axeyum_fragments": [
            "QF_BV",
            "bit-blast lowering",
            "DIMACS",
            "DRAT proof checking",
            "fixed-width finite encoding",
        ],
        "example_packs": [
            (
                "finite-fields-v0",
                "Composite-modulus no-inverse row where fixed-width residues are the source concept.",
            ),
            (
                "finite-rings-v0",
                "Bad finite ring-table distributivity row checked through a fixed-width BV encoding.",
            ),
            (
                "graph-coloring-v0",
                "Triangle non-2-colorability row encoded as one-bit colors and checked by DRAT.",
            ),
            (
                "number-theory-v0",
                "Modulo-7 quadratic nonresidue row checked through a fixed-width residue encoding.",
            ),
        ],
        "proof_routes": [
            {
                "name": "QF_BV bit-blast DIMACS/DRAT family",
                "status": "checked",
                "checker": "cargo test -p axeyum-solver --test math_resource_bv_routes",
                "lean_status": "partial",
                "sources": [
                    "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
                    "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
                    "crates/axeyum-solver/tests/math_resource_bv_routes.rs",
                ],
                "notes": (
                    "Each referenced pack keeps finite replay or source-level "
                    "enumeration separate from the bit-vector proof artifact; "
                    "the regression exports a DIMACS/DRAT proof, rechecks it, "
                    "and rejects a truncated DRAT certificate."
                ),
            }
        ],
        "source_refs": [
            "docs/proof-cookbook/recipes/qf-bv-bitblast.md",
            "docs/foundational-resources/PROOF-UPGRADE-FRONTIER.md",
            "docs/foundational-resources/MATH-CURRICULUM-IMPLEMENTATION-MATRIX.md",
            "crates/axeyum-solver/tests/math_resource_bv_routes.rs",
        ],
        "open_gaps": [
            "The family certifies fixed-width bit-blasted CNF refutations, not arbitrary algebra, graph, or number-theory theorems.",
            "New BV-resource packs should join this family only when bit width is part of the mathematical claim and a checked math_resource_bv_routes regression exists.",
            "The bit-blast/Tseitin lowering remains an explicit trust step until Lean reconstruction covers the original formula.",
        ],
        "graduation": {
            "status": "validated",
            "criteria": [
                "Every family pack row links a committed SMT-LIB artifact and checked QF_BV/DRAT regression.",
                "cargo test -p axeyum-solver --test math_resource_bv_routes passes.",
                "Learner pages distinguish fixed-width finite encoding from unbounded arithmetic or theorem claims.",
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
    route_status = "lean-horizon" if lean_required else "planned"
    lean_status = "required" if lean_required else "planned"
    doc_path = curriculum_doc_path(node)
    is_pack_validated = any(pack_status(pack_id) == "validated" for pack_id, _ in pack_specs)
    if lean_required:
        status = "proof-horizon"
    elif is_pack_validated:
        status = "validated"
    else:
        status = "planned"
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
