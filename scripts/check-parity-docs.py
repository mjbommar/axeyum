#!/usr/bin/env python3
"""Fail when live parity documentation contradicts committed measurements.

This is intentionally a bounded guard, not a natural-language fact checker. It
owns the claims that have already rotted repeatedly: the generated division
totals, exact dominance-audit denominators, the paired 20-second p4dfa control,
the reviewer-facing project-state summary, the checked-in Cargo-example
inventory, the consumer-application corpus totals, and the source/test-backed
categorical-engine maturity classification. It also guards the prover-track
built/planned boundary against already-resolved kernel and UF findings. New
guarded numerical claims should be added only when they have one canonical,
machine-readable artifact; the categorical markers guard the dated audit and
the live roadmap language that points to it.
"""

from __future__ import annotations

import glob
import importlib.util
import json
import re
import sys
from pathlib import Path

from parity_evidence import audit_inventory_raw, paired_decision_overlap


ROOT = Path(__file__).resolve().parent.parent
GEN_SCOREBOARD = ROOT / "scripts" / "gen-scoreboard.py"
GAP_DOC = ROOT / "docs" / "plan" / "gap-analysis-z3-lean-2026-07-21.md"
PARITY_AUDIT = ROOT / "docs" / "plan" / "parity-target-evidence-audit-2026-07-21.md"
LEAN_GATE_AUDIT = ROOT / "docs" / "plan" / "official-lean-ci-gate-audit-2026-07-21.md"
PROJECT_STATE = ROOT / "docs" / "PROJECT-STATE.md"
BENCHMARK_GUIDE = ROOT / "docs" / "user-guide" / "benchmarks.md"
USER_GUIDE_INDEX = ROOT / "docs" / "user-guide" / "README.md"
FIRST_SMTLIB_GUIDE = ROOT / "docs" / "user-guide" / "first-smtlib-query.md"
UNSAT_EVIDENCE_GUIDE = ROOT / "docs" / "user-guide" / "unsat-evidence.md"
SOLVER_CONFIG_GUIDE = ROOT / "docs" / "reference" / "solver-config.md"
PARITY_LEDGER = ROOT / "bench-results" / "PARITY.md"
EXAMPLE_CATALOG = ROOT / "docs" / "reference" / "examples.md"
DOCUMENTATION_PLAN = ROOT / "docs" / "documentation-plan.md"
CONSUMER_README = ROOT / "docs" / "consumer-track" / "README.md"
CONSUMER_SCOREBOARD = ROOT / "docs" / "consumer-track" / "SCOREBOARD.md"
LEARN_INTRO = ROOT / "docs" / "learn" / "01-what-is-automated-reasoning.md"
LEARN_THEORIES = ROOT / "docs" / "learn" / "03-smt-and-theories.md"
LEARN_OUTCOMES = ROOT / "docs" / "learn" / "05-models-unsat-and-unknown.md"
LEARN_PIPELINE = ROOT / "docs" / "learn" / "07-how-axeyum-solves-a-query.md"
TERM_IR_DOC = ROOT / "docs" / "internals" / "term-ir.md"
EVALUATOR_DOC = ROOT / "docs" / "internals" / "evaluator.md"
CNF_INTERNAL_DOC = ROOT / "docs" / "internals" / "cnf-and-sat.md"
PROOF_STACK_DOC = ROOT / "docs" / "internals" / "proof-stack.md"
LEAN_INTERNAL_DOC = ROOT / "docs" / "internals" / "lean-kernel.md"
NORTH_STAR_PLAN = ROOT / "docs" / "plan" / "00-north-star.md"
NORTH_STAR_ORIENTATION = (
    ROOT / "docs" / "research" / "00-orientation" / "north-star.md"
)
FOUNDATIONAL_DAG = (
    ROOT / "docs" / "research" / "08-planning" / "foundational-dag.md"
)
FOUNDATION_ROADMAP = ROOT / "docs" / "research" / "08-planning" / "roadmap.md"
RESEARCH_QUESTIONS = (
    ROOT / "docs" / "research" / "08-planning" / "research-questions.md"
)
PROVER_README = ROOT / "docs" / "prover-track" / "README.md"
PROVER_SYNTHESIS = ROOT / "docs" / "prover-track" / "SYNTHESIS.md"
PROVER_PLAN = ROOT / "docs" / "prover-track" / "plan" / "README.md"
PROVER_P60 = (
    ROOT / "docs" / "prover-track" / "plan" / "P6.0-kernel-trustworthiness.md"
)
LEAN_AXIOM_LEDGER = ROOT / "docs" / "plan" / "lean-axiom-ledger-v1.json"
LEAN_COMPLETE_PARITY = ROOT / "docs" / "plan" / "generated" / "lean-complete-parity.md"
LEAN_OFFICIAL_MATRIX = (
    ROOT / "docs" / "plan" / "generated" / "lean-official-construct-matrix.md"
)
LEAN_QUOTIENT_RESULT = (
    ROOT / "docs" / "plan" / "lean-quotient-package-m1-m3-result-2026-07-23.md"
)
LEAN_KERNEL_EXPR = ROOT / "crates" / "axeyum-lean-kernel" / "src" / "expr.rs"
LEAN_IMPORT_LIB = ROOT / "crates" / "axeyum-lean-import" / "src" / "lib.rs"
UF_FUNCTION_ELIM = ROOT / "crates" / "axeyum-rewrite" / "src" / "functions.rs"
CNF_LIB = ROOT / "crates" / "axeyum-cnf" / "src" / "lib.rs"
CNF_LRAT = ROOT / "crates" / "axeyum-cnf" / "src" / "lrat.rs"
CNF_README = ROOT / "crates" / "axeyum-cnf" / "README.md"
CAS_README = ROOT / "crates" / "axeyum-cas" / "README.md"
CAS_LIB = ROOT / "crates" / "axeyum-cas" / "src" / "lib.rs"
BOOLEAN_CNF_COOKBOOK = (
    ROOT / "docs" / "proof-cookbook" / "recipes" / "boolean-cnf-lrat.md"
)
LRA_COOKBOOK = ROOT / "docs" / "proof-cookbook" / "recipes" / "qf-lra-farkas.md"
IR_TERM = ROOT / "crates" / "axeyum-ir" / "src" / "term.rs"
PROOF_SAT = ROOT / "crates" / "axeyum-cnf" / "src" / "proof_sat.rs"
BV_LOWERING = ROOT / "crates" / "axeyum-bv" / "src" / "lib.rs"
SAT_BV_BACKEND = ROOT / "crates" / "axeyum-solver" / "src" / "sat_bv_backend.rs"
SOLVER_LRA = ROOT / "crates" / "axeyum-solver" / "src" / "lra.rs"
SOLVER_UFLRA_ONLINE = (
    ROOT / "crates" / "axeyum-solver" / "src" / "uflra_online.rs"
)
SOLVER_UFLIA_ONLINE = (
    ROOT / "crates" / "axeyum-solver" / "src" / "uflia_online.rs"
)
SOLVER_BACKEND = ROOT / "crates" / "axeyum-solver" / "src" / "backend.rs"
SUPPORT_MATRIX_LEDGER = (
    ROOT / "crates" / "axeyum-solver" / "src" / "support_matrix.rs"
)
CAPABILITY_LEDGER = ROOT / "crates" / "axeyum-solver" / "src" / "capabilities.rs"
SMTLIB_FRONT_DOOR = ROOT / "crates" / "axeyum-solver" / "src" / "smtlib.rs"
SMTLIB_PARSE = ROOT / "crates" / "axeyum-smtlib" / "src" / "parse.rs"
GENERATED_SUPPORT_MATRIX = (
    ROOT / "docs" / "research" / "08-planning" / "support-matrix.md"
)
GENERATED_CAPABILITY_MATRIX = (
    ROOT / "docs" / "research" / "08-planning" / "capability-matrix.md"
)
LIMITATIONS = ROOT / "docs" / "user-guide" / "limitations.md"
P27_INDEX = ROOT / "docs" / "plan" / "track-2-theories" / "P2.7-strings.md"
P27_CURRENT = (
    ROOT
    / "docs"
    / "plan"
    / "track-2-theories"
    / "P2.7-strings"
    / "00-current-state.md"
)
IR_SORT = ROOT / "crates" / "axeyum-ir" / "src" / "sort.rs"
IR_VALUE = ROOT / "crates" / "axeyum-ir" / "src" / "value.rs"
IR_EVAL = ROOT / "crates" / "axeyum-ir" / "src" / "eval.rs"
WORD_STRINGS = ROOT / "crates" / "axeyum-strings" / "src" / "lib.rs"
QUOTIENT_ADR = (
    ROOT
    / "docs"
    / "research"
    / "09-decisions"
    / "adr-0365-preregister-lean-quotient-package.md"
)
CATEGORICAL_AUDIT = (
    ROOT / "docs" / "plan" / "categorical-engine-depth-audit-2026-07-21.md"
)
CI_WORKFLOW = ROOT / ".github" / "workflows" / "ci.yml"
LEAN_INSTALLER = ROOT / "scripts" / "install-pinned-lean.sh"
LEAN_CROSSCHECK_SOURCE = ROOT / "crates" / "axeyum-solver" / "tests" / "lean_crosscheck.rs"
AXEYUM_P4DFA = (
    ROOT
    / "bench-results"
    / "baselines"
    / "qf-bv-p4dfa-axeyum-vs-z3-20s-authoritative.json"
)
Z3_P4DFA = (
    ROOT
    / "bench-results"
    / "baselines"
    / "qf-bv-p4dfa-z3-standalone-20s.json"
)
SMTCOMP_INVENTORY = (
    ROOT / "bench-results" / "smtcomp-repro-20260721" / "inventory.json"
)
SMTCOMP_INVENTORY_RAW = (
    ROOT / "bench-results" / "smtcomp-repro-20260721" / "inventory_raw.json"
)
SMTCOMP_README = ROOT / "bench-results" / "smtcomp-repro-20260721" / "README.md"
SMTCOMP_QFBV = (
    ROOT / "bench-results" / "smtcomp-repro-20260721" / "head_to_head_qfbv.json"
)
SMTCOMP_PROVENANCE = (
    ROOT / "bench-results" / "smtcomp-repro-20260721" / "provenance.json"
)
MEASUREMENT_PROVENANCE = (
    ROOT / "docs" / "plan" / "generated" / "measurement-provenance-matrix.json"
)
PROOF_COOKBOOK_DOCS = tuple(
    sorted((ROOT / "docs" / "proof-cookbook").rglob("*.md"))
)
LEARN_DOCS = tuple(sorted((ROOT / "docs" / "learn").rglob("*.md")))
CURRENT_SOLVER_COMMAND_DOCS = tuple(
    sorted(
        PROOF_COOKBOOK_DOCS
        + LEARN_DOCS
        + tuple((ROOT / "docs" / "contributor-guide").rglob("*.md"))
        + tuple((ROOT / "docs" / "foundational-resources").rglob("*.md"))
        + tuple((ROOT / "docs" / "rules-as-code").rglob("*.md"))
        + tuple((ROOT / "docs" / "rules-as-code").rglob("*.json"))
    )
)
DOCUMENTED_TEST_SOURCES = {
    suite: ROOT / "crates" / "axeyum-solver" / "tests" / f"{suite}.rs"
    for suite in (
        "abv_differential_fuzz",
        "bv_differential_fuzz",
        "evidence",
        "int_inequality_lean_reconstruct",
        "lean_crosscheck",
        "math_resource_bv_routes",
        "math_resource_lia_routes",
        "math_resource_lra_routes",
        "math_resource_uf_routes",
        "progress_frontier",
        "rules_as_code_examples",
    )
}

LIVE_DOCS = (
    ROOT / "README.md",
    ROOT / "PLAN.md",
    ROOT / "STATUS.md",
    ROOT / "bench-results" / "SCOREBOARD.md",
    ROOT / "docs" / "README.md",
    PROJECT_STATE,
    USER_GUIDE_INDEX,
    ROOT / "docs" / "plan" / "README.md",
    ROOT / "docs" / "user-guide" / "benchmarks.md",
    FIRST_SMTLIB_GUIDE,
    ROOT / "docs" / "user-guide" / "limitations.md",
    SOLVER_CONFIG_GUIDE,
    GAP_DOC,
    PARITY_AUDIT,
    LEAN_GATE_AUDIT,
    SMTCOMP_README,
    CATEGORICAL_AUDIT,
    ROOT / "docs" / "plan" / "01-dependency-dag.md",
    ROOT / "docs" / "plan" / "track-3-proof-lean" / "P3.8-interpolation.md",
    ROOT / "docs" / "plan" / "track-4-usecases-frontend" / "README.md",
    ROOT / "docs" / "plan" / "track-4-usecases-frontend" / "P4.6-chc-horn.md",
    ROOT / "docs" / "plan" / "track-4-usecases-frontend" / "P4.7-synthesis.md",
    ROOT / "docs" / "research" / "08-planning" / "roadmap.md",
)

PUBLIC_CLAIM_DOCS = (
    ROOT / "README.md",
    ROOT / "docs" / "README.md",
    PROJECT_STATE,
    LEARN_INTRO,
    LEARN_THEORIES,
    LEARN_OUTCOMES,
    LEARN_PIPELINE,
    TERM_IR_DOC,
    EVALUATOR_DOC,
    CNF_INTERNAL_DOC,
    PROOF_STACK_DOC,
    LEAN_INTERNAL_DOC,
    CNF_README,
    BOOLEAN_CNF_COOKBOOK,
    LRA_COOKBOOK,
    NORTH_STAR_PLAN,
    NORTH_STAR_ORIENTATION,
    FOUNDATIONAL_DAG,
    FOUNDATION_ROADMAP,
    RESEARCH_QUESTIONS,
    ROOT / "docs" / "user-guide" / "benchmarks.md",
    ROOT / "docs" / "user-guide" / "limitations.md",
    SMTCOMP_README,
)

STALE_PATTERNS = (
    re.compile(r"Z3 (?:still )?decides all 113", re.IGNORECASE),
    re.compile(r"Z3\s+113/113", re.IGNORECASE),
    re.compile(r"p4dfa 113, parity, both hard-capped", re.IGNORECASE),
    re.compile(r"~15/35 rows"),
    re.compile(r"\b19/35 decide-strong\b"),
    re.compile(r"\b23 fragments\b"),
    re.compile(r"\b~73%\b"),
    re.compile(r"new categorical engines", re.IGNORECASE),
    re.compile(r"biggest categorical gap", re.IGNORECASE),
    re.compile(r"categorically-missing", re.IGNORECASE),
    re.compile(r"T3\.8\.5 façade — DONE"),
    re.compile(r"8[–-]8\s*@20s,\s*11[–-]11\s*@60s", re.IGNORECASE),
    re.compile(r"parity is \*budget-robust\*", re.IGNORECASE),
    re.compile(r"\|\s*20 s\s*\|\s*8 / 113\s*\|\s*9 / 113\s*\|", re.IGNORECASE),
)

PUBLIC_STALE_PATTERNS = (
    re.compile(r"every\s+`unsat`\s+carries", re.IGNORECASE),
    re.compile(r"It is sound \(`unknown`, never a wrong", re.IGNORECASE),
    re.compile(r"axeyum is \*\*never wrong\*\*", re.IGNORECASE),
    re.compile(r"82\s*/\s*228\*\* decided-correct", re.IGNORECASE),
    re.compile(r"\bnever wrong\b", re.IGNORECASE),
    re.compile(r"never a crash", re.IGNORECASE),
    re.compile(r"wrong search can.?t produce a wrong\s+`unsat`", re.IGNORECASE),
    re.compile(
        r"proof-producing core enabled it also emits a DRAT proof",
        re.IGNORECASE,
    ),
    re.compile(r"Re-derive small BV UNSAT results", re.IGNORECASE),
    re.compile(r"integer and rational values are exact,", re.IGNORECASE),
    re.compile(r"custom CDCL direction", re.IGNORECASE),
    re.compile(r"elaborate DRAT to LRAT and check LRAT", re.IGNORECASE),
    re.compile(r"unsat\s*[→-]+\s*checkable certificate", re.IGNORECASE),
    re.compile(r"A Boolean\s+`unsat`\s+claim is accepted only", re.IGNORECASE),
    re.compile(
        r"Nested and mutual inductives, recursors, quotient-related declarations,"
        r" and other features are admitted only",
        re.IGNORECASE,
    ),
    re.compile(
        r"a supported\s+`unsat`\s+route should carry independently checkable evidence",
        re.IGNORECASE,
    ),
)

PROVER_STALE_PATTERNS = (
    re.compile(r"Status:\s*designed,\s*not built", re.IGNORECASE),
    re.compile(r"positivity (?:is|remains).*vacu", re.IGNORECASE),
    re.compile(r"`Lit::Nat` is `u128`"),
    re.compile(r"!fn_app_0.*blocks every", re.IGNORECASE),
    re.compile(r"entry ADR.*owed before P6\.1", re.IGNORECASE),
)

NORTH_STAR_STALE_PATTERNS = (
    re.compile(r"destination 2 is NEAR-PARITY", re.IGNORECASE),
    re.compile(r"Binder\(later\)", re.IGNORECASE),
    re.compile(r"where Z3 decides nearly all", re.IGNORECASE),
    re.compile(r"never a wrong `unsat`", re.IGNORECASE),
)

FOUNDATIONAL_DAG_STALE_PATTERNS = (
    re.compile(r"Status:\s*draft", re.IGNORECASE),
    re.compile(r"Current Foundation:\s*Bool", re.IGNORECASE),
    re.compile(r"remaining Phase 5 gate", re.IGNORECASE),
    re.compile(r"Before Phase 6 implementation starts", re.IGNORECASE),
)

FOUNDATION_ROADMAP_STALE_PATTERNS = (
    re.compile(r"next T6\.0\.3/TL2\.15 seed", re.IGNORECASE),
    re.compile(r"quotient semantic seams remain uncredited", re.IGNORECASE),
)

RESEARCH_QUESTION_STALE_PATTERNS = (
    re.compile(r"Status:\s*draft", re.IGNORECASE),
    re.compile(r"- \[ \] How are symbolic shifts encoded\?"),
    re.compile(r"- \[ \] Should unsat proof checking be required", re.IGNORECASE),
    re.compile(
        r"Making it the \*required\* high-assurance mode.*remaining step",
        re.DOTALL,
    ),
)

P27_STALE_PATTERNS = (
    re.compile(r"Status:\s*planning", re.IGNORECASE),
    re.compile(r"SMT-LIB packed front-door cap 24", re.IGNORECASE),
    re.compile(r"there is no first-class sequence/string sort in the IR", re.IGNORECASE),
    re.compile(r"UNSAT carries a DRAT proof", re.IGNORECASE),
    re.compile(r"str\.len\s+unsat can be\s+`?unknown`?.*BV\+LIA", re.IGNORECASE),
    re.compile(r"DISAGREE=0 over 371 instances", re.IGNORECASE),
    re.compile(r"We decide the \*\*bounded\*\* SMT-LIB string fragment exactly"),
)

PROVER_LIVE_DOCS = (
    ROOT / "README.md",
    PROVER_README,
    PROVER_SYNTHESIS,
    ROOT / "docs" / "prover-track" / "design" / "00-thesis.md",
    ROOT / "docs" / "prover-track" / "design" / "03-architecture.md",
    PROVER_PLAN,
    PROVER_P60,
)


def load_scoreboard_module():
    spec = importlib.util.spec_from_file_location("axeyum_gen_scoreboard", GEN_SCOREBOARD)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot import {GEN_SCOREBOARD}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def decided(summary: dict) -> int:
    return int(summary.get("sat", 0)) + int(summary.get("unsat", 0))


def latest_parity_rows() -> dict[str, tuple[str, str, str, str]]:
    """Return the last append-only parity row for each logic.

    The ledger intentionally retains older and lower results. Public status must
    therefore copy the last row for a division, not the most flattering row.
    """

    text = PARITY_LEDGER.read_text(encoding="utf-8")
    rows: dict[str, tuple[str, str, str, str]] = {}
    sections = re.finditer(
        r"^## (?P<logic>[A-Z0-9_]+) — [^\n]+\n(?P<body>.*?)(?=^## |\Z)",
        text,
        re.MULTILINE | re.DOTALL,
    )
    for section in sections:
        body = section.group("body")

        def field(pattern: str) -> str:
            match = re.search(pattern, body, re.MULTILINE)
            if match is None:
                raise RuntimeError(
                    f"{PARITY_LEDGER.relative_to(ROOT)}: malformed "
                    f"{section.group('logic')} section; missing {pattern!r}"
                )
            return match.group("value").strip(" `*")

        rows[section.group("logic")] = (
            field(r"^\| axeyum solved \| (?P<value>[^|]+) \|$"),
            field(r"^\| reference solved \| (?P<value>[^|]+) \|$"),
            field(r"^\| \*\*ratio \(axeyum / reference\)\*\* \| (?P<value>[^|]+) \|$"),
            field(r"^\| \*\*disagreements\*\* \| (?P<value>[^|]+) \|$"),
        )
    return rows


def consumer_snapshot() -> dict[str, dict[str, int] | int]:
    """Reconcile the public consumer totals from the three committed corpora."""

    property_data = load_json(
        ROOT / "docs" / "consumer-track" / "property" / "corpus.json"
    )
    property_summary = property_data["summary"]
    evm_data = load_json(ROOT / "docs" / "consumer-track" / "evm" / "corpus.json")
    verify_data = load_json(
        ROOT / "docs" / "consumer-track" / "verify" / "corpus.json"
    )
    verify_outcomes: dict[str, int] = {}
    for case in verify_data["cases"]:
        outcome = case["outcome"]
        verify_outcomes[outcome] = verify_outcomes.get(outcome, 0) + 1

    apps = {
        "property": {
            "cases": int(property_summary["cases"]),
            "bugs": int(property_summary["disproved"]),
            "safe": int(property_summary["proved"]),
            "unknown": int(property_summary["unknown"]),
            "disagree": int(property_summary["disagree"]),
        },
        "evm": {
            "cases": int(evm_data["total"]),
            "bugs": int(evm_data["bug_found"]),
            "safe": int(evm_data["safe_proved"]),
            "unknown": int(evm_data["unknown"]),
            "disagree": int(evm_data["disagree"]),
        },
        "verify": {
            "cases": int(verify_data["total"]),
            "bugs": verify_outcomes.get("bug-found", 0),
            "safe": verify_outcomes.get("verified", 0),
            "unknown": verify_outcomes.get("unknown", 0),
            "disagree": int(verify_data["disagree"]),
        },
    }
    if apps["property"]["cases"] != len(property_data["cases"]):
        raise RuntimeError("property consumer total does not match its case inventory")
    if apps["evm"]["cases"] != len(evm_data["cases"]):
        raise RuntimeError("EVM consumer total does not match its case inventory")
    if apps["verify"]["cases"] != sum(verify_outcomes.values()):
        raise RuntimeError("verify consumer total does not match its case inventory")
    for name, app in apps.items():
        classified = app["bugs"] + app["safe"] + app["unknown"] + app["disagree"]
        if app["cases"] != classified:
            raise RuntimeError(
                f"{name} consumer outcomes classify {classified} of {app['cases']} cases"
            )

    totals = {
        field: sum(app[field] for app in apps.values())
        for field in ("cases", "bugs", "safe", "unknown", "disagree")
    }
    return {**apps, **totals}


def measured_snapshot() -> dict[str, int]:
    scoreboard = load_scoreboard_module()
    rows = scoreboard.load_division_baselines() + scoreboard.load_synthetic_baselines()

    audits = []
    for path in sorted(glob.glob(str(ROOT / "bench-results" / "dominance" / "*.json"))):
        audit = load_json(Path(path))
        if audit.get("complete_audit"):
            audits.append(audit)

    axeyum = load_json(AXEYUM_P4DFA)
    z3 = load_json(Z3_P4DFA)
    inventory = load_json(SMTCOMP_INVENTORY)
    inventory_raw = load_json(SMTCOMP_INVENTORY_RAW)
    qfbv = load_json(SMTCOMP_QFBV)
    provenance = load_json(SMTCOMP_PROVENANCE)
    measurement = load_json(MEASUREMENT_PROVENANCE)
    measurement_score = measurement["summary"]["regression_scoreboard"]
    measurement_public = measurement["summary"]["public_inventory"]
    measurement_overlap = measurement["summary"]["cross_regime"]
    for artifact in (axeyum, z3):
        config = artifact["config"]
        summary = artifact["summary"]
        if config["timeout_ms"] != 20_000 or summary["files"] != 113:
            raise RuntimeError("p4dfa control is no longer the registered 113-file/20-second cell")
    if axeyum["config"]["corpus_hash"] != z3["config"]["corpus_hash"]:
        raise RuntimeError("p4dfa Axeyum/Z3 controls do not bind the same corpus hash")
    qfbv_division = qfbv["divisions"]["QF_BV"]
    qfbv_solvers = qfbv_division["solvers"]
    inventory_audit = audit_inventory_raw(inventory_raw, solver="axeyum")
    p4dfa_overlap = paired_decision_overlap(axeyum, z3)
    aggregate = inventory["aggregate"]
    expected_legacy = {
        "total": inventory_audit["total"],
        "decided_correct": inventory_audit["legacy_decided_correct"],
        "declined": inventory_audit["declines"],
        "no_answer": inventory_audit["no_answers"],
        "WRONG": inventory_audit["known_status_disagreements"],
    }
    for key, value in expected_legacy.items():
        if aggregate.get(key) != value:
            raise RuntimeError(
                f"public inventory aggregate {key}={aggregate.get(key)!r} "
                f"does not reconcile with raw audit {value}"
            )

    baseline_unsat_instances = [
        instance
        for audit in audits
        for instance in audit["instances"]
        if instance.get("baseline_outcome") == "unsat"
    ]

    dominant_unsat = sum(
        instance.get("audit_outcome") == "unsat"
        and instance.get("evidence_certified") is True
        and instance.get("evidence_checked") is True
        and instance.get("lean_checked") is True
        and not instance.get("trust_holes")
        for instance in baseline_unsat_instances
    )
    uncertified_unsat = sum(
        instance.get("audit_outcome") == "unsat"
        and instance.get("evidence_certified") is not True
        for instance in baseline_unsat_instances
    )
    lean_reconstruction_gap = sum(
        instance.get("audit_outcome") == "unsat"
        and instance.get("evidence_certified") is True
        and instance.get("evidence_checked") is True
        and instance.get("lean_checked") is not True
        and not instance.get("trust_holes")
        for instance in baseline_unsat_instances
    )
    proof_production_errors = sum(
        instance.get("audit_outcome") != "unsat"
        for instance in baseline_unsat_instances
    )

    scoreboard_ids = []
    scoreboard_aggregate_only = 0
    for row in rows:
        baseline = load_json(ROOT / row["file"])
        instances = baseline.get("instances", [])
        if not instances:
            scoreboard_aggregate_only += row["files"]
            continue
        for instance in instances:
            path = instance["file"]
            if "non-incremental/" in path:
                path = path.split("non-incremental/", 1)[1]
            elif "quantified/" in path:
                path = "quantified/" + path.split("quantified/", 1)[1]
            scoreboard_ids.append(path)

    return {
        "rows": len(rows),
        "logics": len({row["logic"] for row in rows}),
        "files": sum(row["files"] for row in rows),
        "decided": sum(row["decided"] for row in rows),
        "compared": sum(row["compared"] for row in rows),
        "disagree": sum(row["disagree"] for row in rows),
        "decide_strong_rows": sum(row["decide_pct"] >= 80.0 for row in rows),
        "complete_audits": len(audits),
        "fully_dominant_rows": sum(
            audit["summary"].get("dominant_pct_audited") == 100.0
            for audit in audits
        ),
        "dominant_decisions": sum(
            audit["summary"]["dominant_candidates"] for audit in audits
        ),
        "audited_decisions": sum(
            audit["summary"]["audited_decided"] for audit in audits
        ),
        "lean_checked_unsat": sum(
            audit["summary"]["lean_checked_unsat"] for audit in audits
        ),
        "certified_unsat": sum(
            instance.get("evidence_certified") is True
            for instance in baseline_unsat_instances
        ),
        "audit_reported_checked_unsat": sum(
            instance.get("evidence_checked") is True
            for instance in baseline_unsat_instances
        ),
        "independently_checked_unsat": sum(
            instance.get("evidence_certified") is True
            and instance.get("evidence_checked") is True
            for instance in baseline_unsat_instances
        ),
        # The historical summary field counts baseline UNSAT decisions, including
        # proof-production failures. Keep both denominators explicit so a failed
        # evidence audit cannot be described as an audited UNSAT result.
        "baseline_unsat": sum(
            audit["summary"]["audited_unsat"] for audit in audits
        ),
        "audit_reproduced_unsat": sum(
            instance.get("audit_outcome") == "unsat"
            for audit in audits
            for instance in audit["instances"]
        ),
        "dominant_unsat": dominant_unsat,
        "uncertified_unsat": uncertified_unsat,
        "lean_reconstruction_gap": lean_reconstruction_gap,
        "proof_production_errors": proof_production_errors,
        "p4dfa_files_20s": int(axeyum["summary"]["files"]),
        "p4dfa_axeyum_20s": decided(axeyum["summary"]),
        "p4dfa_z3_20s": decided(z3["summary"]),
        "p4dfa_both_decided_20s": p4dfa_overlap["both_decided"],
        "p4dfa_axeyum_only_20s": p4dfa_overlap["left_only_decided"],
        "p4dfa_z3_only_20s": p4dfa_overlap["right_only_decided"],
        "p4dfa_both_disagree_20s": p4dfa_overlap["both_decided_disagreements"],
        "public_inventory_files": inventory["aggregate"]["total"],
        "public_inventory_decided": inventory["aggregate"]["decided_correct"],
        "public_inventory_known_status": inventory_audit["known_status_benchmarks"],
        "public_inventory_unknown_status": inventory_audit["unknown_status_benchmarks"],
        "public_inventory_known_agree": inventory_audit["known_status_agreements"],
        "public_inventory_unadjudicated_decisions": inventory_audit[
            "unadjudicated_decisions"
        ],
        "public_inventory_declined": inventory["aggregate"]["declined"],
        "public_inventory_wrong": inventory["aggregate"]["WRONG"],
        "public_inventory_no_answer": inventory["aggregate"]["no_answer"],
        "qfbv_head_to_head_files": qfbv_division["n_benchmarks"],
        "qfbv_head_to_head_axeyum": qfbv_solvers["axeyum"]["par2"]["n"],
        "qfbv_head_to_head_cvc5": qfbv_solvers["cvc5"]["par2"]["n"],
        "qfbv_head_to_head_bitwuzla": qfbv_solvers["bitwuzla"]["par2"]["n"],
        "scoreboard_file_occurrences": len(scoreboard_ids),
        "scoreboard_unique_ids": len(set(scoreboard_ids)),
        "scoreboard_repeated_occurrences": len(scoreboard_ids)
        - len(set(scoreboard_ids)),
        "scoreboard_aggregate_only": scoreboard_aggregate_only,
        "public_source_families": provenance["summary"]["source_families"],
        "public_unique_sha256": provenance["summary"]["unique_content_sha256"],
        "public_exact_duplicate_groups": provenance["summary"]["exact_duplicate_groups"],
        "scoreboard_unique_sha256": measurement_score["unique_content_sha256"],
        "scoreboard_exact_duplicate_groups": measurement_score["exact_duplicate_groups"],
        "scoreboard_exact_duplicate_excess": measurement_score["exact_duplicate_excess"],
        "cross_regime_unique_overlap": measurement_overlap["unique_content_overlap"],
        "neutral_measurement_rows": measurement_score["neutral_oracle_rows"]
        + measurement_public["neutral_oracle_rows"],
    }


def main() -> int:
    snapshot = measured_snapshot()
    consumers = consumer_snapshot()
    parity_rows = latest_parity_rows()
    failures: list[str] = []

    for path in LIVE_DOCS:
        text = path.read_text(encoding="utf-8")
        for pattern in STALE_PATTERNS:
            if match := pattern.search(text):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(f"{path.relative_to(ROOT)}:{line}: stale parity claim: {match.group(0)!r}")

    for path in PUBLIC_CLAIM_DOCS:
        text = path.read_text(encoding="utf-8")
        for pattern in PUBLIC_STALE_PATTERNS:
            if match := pattern.search(text):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(
                    f"{path.relative_to(ROOT)}:{line}: stale public claim: {match.group(0)!r}"
                )

    for path in PROVER_LIVE_DOCS:
        text = path.read_text(encoding="utf-8")
        for pattern in PROVER_STALE_PATTERNS:
            if match := pattern.search(text):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(
                    f"{path.relative_to(ROOT)}:{line}: stale prover claim: "
                    f"{match.group(0)!r}"
                )

    for path in (NORTH_STAR_PLAN, NORTH_STAR_ORIENTATION):
        text = path.read_text(encoding="utf-8")
        for pattern in NORTH_STAR_STALE_PATTERNS:
            if match := pattern.search(text):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(
                    f"{path.relative_to(ROOT)}:{line}: stale north-star claim: "
                    f"{match.group(0)!r}"
                )

    foundational_dag_text = FOUNDATIONAL_DAG.read_text(encoding="utf-8")
    for pattern in FOUNDATIONAL_DAG_STALE_PATTERNS:
        if match := pattern.search(foundational_dag_text):
            line = foundational_dag_text.count("\n", 0, match.start()) + 1
            failures.append(
                f"{FOUNDATIONAL_DAG.relative_to(ROOT)}:{line}: stale foundation "
                f"phase claim: {match.group(0)!r}"
            )

    foundation_roadmap_text = FOUNDATION_ROADMAP.read_text(encoding="utf-8")
    for pattern in FOUNDATION_ROADMAP_STALE_PATTERNS:
        if match := pattern.search(foundation_roadmap_text):
            line = foundation_roadmap_text.count("\n", 0, match.start()) + 1
            failures.append(
                f"{FOUNDATION_ROADMAP.relative_to(ROOT)}:{line}: stale roadmap "
                f"claim: {match.group(0)!r}"
            )

    research_questions_text = RESEARCH_QUESTIONS.read_text(encoding="utf-8")
    for pattern in RESEARCH_QUESTION_STALE_PATTERNS:
        if match := pattern.search(research_questions_text):
            line = research_questions_text.count("\n", 0, match.start()) + 1
            failures.append(
                f"{RESEARCH_QUESTIONS.relative_to(ROOT)}:{line}: stale research "
                f"question status: {match.group(0)!r}"
            )

    kernel_expr_text = LEAN_KERNEL_EXPR.read_text(encoding="utf-8")
    if "pub struct NatLit(BigUint);" not in kernel_expr_text:
        failures.append(
            f"{LEAN_KERNEL_EXPR.relative_to(ROOT)}: expected arbitrary-precision NatLit"
        )

    function_elim_text = UF_FUNCTION_ELIM.read_text(encoding="utf-8")
    for marker in (
        'format!("!fn_app_{}", source.index())',
        "repeated_elimination_uses_disjoint_fresh_symbols",
    ):
        if marker in function_elim_text:
            continue
        failures.append(
            f"{UF_FUNCTION_ELIM.relative_to(ROOT)}: missing UF identity marker {marker!r}"
        )

    lean_complete_text = LEAN_COMPLETE_PARITY.read_text(encoding="utf-8")
    if not re.search(
        r"^\| `A5` \| goals, tactics, automation \| .* \| `not_started` \|",
        lean_complete_text,
        re.MULTILINE,
    ):
        failures.append(
            f"{LEAN_COMPLETE_PARITY.relative_to(ROOT)}: A5 must remain explicitly "
            "not_started until native goal/tactic evidence lands"
        )

    axiom_ledger = load_json(LEAN_AXIOM_LEDGER)
    axiom_entries = axiom_ledger["entries"]
    axiom_total = len(axiom_entries)
    if axiom_total != int(axiom_ledger["expected_counts"]["total"]):
        failures.append(
            f"{LEAN_AXIOM_LEDGER.relative_to(ROOT)}: entry count does not match "
            "expected total"
        )
    axiom_classes = {
        name: sum(entry["classification"] == name for entry in axiom_entries)
        for name in (
            "derivable-theorem",
            "external-assumption",
            "primitive-interface",
        )
    }

    prover_readme_text = " ".join(PROVER_README.read_text(encoding="utf-8").split())
    for marker in (
        "no `axeyum-goal` crate exists",
        "Full Lean 4.30 parity is also explicitly unestablished",
        "`NatLit(BigUint)`",
        "`c223ed8d4`",
        f"{axiom_total}-row generated ledger",
        f"{axiom_classes['derivable-theorem']} derivable-theorem, "
        f"{axiom_classes['external-assumption']} external-assumption, and "
        f"{axiom_classes['primitive-interface']} primitive-interface",
    ):
        if marker not in prover_readme_text:
            failures.append(
                f"{PROVER_README.relative_to(ROOT)}: missing prover boundary marker "
                f"{marker!r}"
            )

    prover_count_markers = (
        (
            PROVER_SYNTHESIS,
            f"ledger classes {axiom_classes['derivable-theorem']} derivable, "
            f"{axiom_classes['external-assumption']} external, "
            f"{axiom_classes['primitive-interface']} primitive",
        ),
        (
            PROVER_PLAN,
            f"generated ledger assigns {axiom_classes['derivable-theorem']} derivable, "
            f"{axiom_classes['external-assumption']} external, and "
            f"{axiom_classes['primitive-interface']} primitive rows",
        ),
        (
            PROVER_P60,
            f"snapshot assigns {axiom_classes['derivable-theorem']} "
            "`derivable-theorem`, "
            f"{axiom_classes['external-assumption']} `external-assumption`, and "
            f"{axiom_classes['primitive-interface']} `primitive-interface` rows",
        ),
    )
    for path, marker in prover_count_markers:
        text = " ".join(path.read_text(encoding="utf-8").split())
        if f"{axiom_total}" not in text or marker not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: missing current axiom-ledger marker "
                f"{marker!r}"
            )

    prover_p60_text = PROVER_P60.read_text(encoding="utf-8")
    for task in ("T6.0.2", "T6.0.4"):
        if not re.search(
            rf"^\| {re.escape(task)} \| \*\*DONE", prover_p60_text, re.MULTILINE
        ):
            failures.append(
                f"{PROVER_P60.relative_to(ROOT)}: {task} must remain marked DONE"
            )

    root_readme_text = (ROOT / "README.md").read_text(encoding="utf-8")
    if "native interactive goal/tactic layer is not built yet" not in root_readme_text:
        failures.append("README.md: missing native goal/tactic status boundary")

    summary_text = (ROOT / "docs" / "SUMMARY.md").read_text(encoding="utf-8")
    if "(prover-track/README.md)" not in summary_text:
        failures.append("docs/SUMMARY.md: prover-track front door is not indexed")

    cnf_lib_text = CNF_LIB.read_text(encoding="utf-8")
    for marker in (
        "pub enum SatProofStatus",
        "SatProofStatus::Unchecked",
    ):
        if marker not in cnf_lib_text:
            failures.append(
                f"{CNF_LIB.relative_to(ROOT)}: missing proof-status marker {marker!r}"
            )

    beginner_markers = (
        (LEARN_INTRO, "Malformed input and operational failures remain separate errors"),
        (LEARN_OUTCOMES, "default BatSat-backed clausal route reports raw UNSAT"),
        (LEARN_OUTCOMES, "[trust ledger](../reference/trust-ledger.md)"),
        (LEARN_PIPELINE, "The UNSAT arrows are alternatives"),
        (LEARN_PIPELINE, "proof status as `Unchecked`"),
        (LEARN_PIPELINE, "[QF_BV proof exporter](../user-guide/unsat-evidence.md)"),
    )
    for path, marker in beginner_markers:
        text = " ".join(path.read_text(encoding="utf-8").split())
        if marker not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: missing beginner assurance marker "
                f"{marker!r}"
            )

    smtlib_proof_markers = (
        (SOLVER_BACKEND, "checks its proof inline in the same"),
        (SOLVER_BACKEND, "Lack of a checked proof"),
        (SAT_BV_BACKEND, "downgrade to `unknown`"),
        (FIRST_SMTLIB_GUIDE, "does not return or write the proof artifact"),
        (FIRST_SMTLIB_GUIDE, "[QF_BV proof exporter](unsat-evidence.md)"),
        (UNSAT_EVIDENCE_GUIDE, "This export API is distinct from"),
        (UNSAT_EVIDENCE_GUIDE, "fails closed to `Unknown`"),
        (SOLVER_CONFIG_GUIDE, "native core is the primary SAT search"),
        (SOLVER_CONFIG_GUIDE, "compatibility fallback"),
        (SOLVER_CONFIG_GUIDE, "does not return or write the proof artifact"),
    )
    for path, marker in smtlib_proof_markers:
        text = " ".join(path.read_text(encoding="utf-8").split())
        if marker not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: missing SMT-LIB proof boundary marker "
                f"{marker!r}"
            )

    propositional_proof_markers = (
        (CNF_LRAT, "This slice supports **RUP-only** proofs"),
        (CNF_LRAT, "RAT additions"),
        (CNF_INTERNAL_DOC, "in-tree proof-producing CDCL core"),
        (CNF_INTERNAL_DOC, "RUP-only"),
        (PROOF_STACK_DOC, "RUP-only"),
        (CNF_README, "RUP-only"),
        (USER_GUIDE_INDEX, "unsat → route-specific assurance"),
        (USER_GUIDE_INDEX, "not implied by every `unsat` verdict"),
        (
            BOOLEAN_CNF_COOKBOOK,
            "default proofless BatSat result remains lower assurance",
        ),
        (BOOLEAN_CNF_COOKBOOK, "DRAT addition that requires RAT is rejected"),
    )
    for path, marker in propositional_proof_markers:
        text = " ".join(path.read_text(encoding="utf-8").split())
        if marker not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: missing propositional proof boundary "
                f"marker {marker!r}"
            )

    lean_boundary_markers = (
        (LEAN_IMPORT_LIB, 'pub const FORMAT_VERSION: &str = "3.1.0";'),
        (LEAN_OFFICIAL_MATRIX, "official accepted: 6; official rejected: 1"),
        (LEAN_OFFICIAL_MATRIX, "dual-admitted-computation-checked`=4"),
        (
            LEAN_QUOTIENT_RESULT,
            "M1--M3 complete; M4 differential and final acceptance remain open",
        ),
        (
            LEAN_INTERNAL_DOC,
            "recursive-indexed, reflexive-higher-order, mutual, nested-inductive",
        ),
        (LEAN_INTERNAL_DOC, "offline TL2.10 M1--M3 slice"),
        (LEAN_INTERNAL_DOC, "Native syntax/macros, elaboration"),
    )
    for path, marker in lean_boundary_markers:
        text = " ".join(path.read_text(encoding="utf-8").split())
        if marker not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: missing Lean compatibility boundary "
                f"marker {marker!r}"
            )

    lra_range_markers = (
        (SOLVER_LRA, "current `i128`-backed rational range"),
        (SOLVER_LRA, "Overflow during collection, elimination"),
        (LRA_COOKBOOK, "`i128`-backed numerator/denominator range"),
        (LRA_COOKBOOK, "returns `unknown` rather than wrapping"),
        (LRA_COOKBOOK, "filtering Cargo by the builder name would run zero tests"),
        (
            LEARN_THEORIES,
            "every `unsat` must state its route-specific assurance boundary",
        ),
        (LEARN_THEORIES, "not implied by every definitive verdict"),
    )
    for path, marker in lra_range_markers:
        text = " ".join(path.read_text(encoding="utf-8").split())
        if marker not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: missing LRA range/assurance boundary "
                f"marker {marker!r}"
            )

    combination_markers = (
        (CAPABILITY_LEDGER, "Combined theory propagation and"),
        (CAPABILITY_LEDGER, "EAGER FALLBACK"),
        (SUPPORT_MATRIX_LEDGER, "online-first model-based equality sharing"),
        (SOLVER_UFLRA_ONLINE, "crate::combined_theory::CombinedIncremental"),
        (SOLVER_UFLRA_ONLINE, "older enumerative Boolean search remains"),
        (SOLVER_UFLIA_ONLINE, "crate::combined_theory_lia::CombinedIncrementalLia"),
        (SOLVER_UFLIA_ONLINE, "older enumerative Boolean search remains"),
        (LEARN_THEORIES, 'does not expose a universal "plug any two theories together"'),
        (LEARN_THEORIES, "does not imply arbitrary Nelson–Oppen completeness"),
        (ROOT / "README.md", "fallback after an online `unknown`"),
    )
    for path, marker in combination_markers:
        text = " ".join(path.read_text(encoding="utf-8").split())
        if marker not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: missing theory-combination boundary "
                f"marker {marker!r}"
            )

    cas_assurance_markers = (
        (CAS_LIB, "pub enum ZeroTest"),
        (CAS_LIB, "pub struct CertifiedIntegral"),
        (CAS_README, "This assurance is CAS-local"),
        (CAS_README, "not `axeyum_solver::Evidence`"),
        (CAS_README, "current checked `i128` range"),
        (ROOT / "README.md", "Their IRs, certificate formats, and exact trust boundaries are"),
        (ROOT / "README.md", "re-validate supported evidence artifacts"),
    )
    for path, marker in cas_assurance_markers:
        text = " ".join(path.read_text(encoding="utf-8").split())
        if marker not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: missing CAS assurance boundary marker "
                f"{marker!r}"
            )

    for path in CURRENT_SOLVER_COMMAND_DOCS:
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), start=1
        ):
            if (
                "cargo test -p axeyum-solver" in line
                and not any(
                    profile in line
                    for profile in (
                        "--features full",
                        "--features z3",
                        "--features z3-static",
                    )
                )
            ):
                failures.append(
                    f"{path.relative_to(ROOT)}:{line_number}: solver documentation test "
                    "command must enable `--features full`"
                )

    documented_test_names: dict[str, tuple[str, ...]] = {}
    for suite, source in DOCUMENTED_TEST_SOURCES.items():
        text = source.read_text(encoding="utf-8")
        names = tuple(
            re.findall(
                r"(?m)^\s*#\[test\]\n(?:\s*#\[[^\n]+\]\n)*\s*fn\s+(\w+)",
                text,
            )
        )
        if not names:
            failures.append(
                f"{source.relative_to(ROOT)}: no documentation-facing tests discovered"
            )
        documented_test_names[suite] = names

    documented_command = re.compile(
        r"cargo test -p axeyum-solver\b.*?--test\s+([\w-]+)(?:\s+(\w+))?"
    )
    for path in CURRENT_SOLVER_COMMAND_DOCS:
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), start=1
        ):
            match = documented_command.search(line)
            if match is None:
                continue
            suite, test_filter = match.groups()
            if suite not in documented_test_names:
                failures.append(
                    f"{path.relative_to(ROOT)}:{line_number}: documented "
                    f"test suite {suite!r} has no guarded source"
                )
            elif test_filter is not None and not any(
                test_filter in name for name in documented_test_names[suite]
            ):
                failures.append(
                    f"{path.relative_to(ROOT)}:{line_number}: documentation test filter "
                    f"{test_filter!r} matches no test in {suite}.rs"
                )

    for path in (
        LRA_COOKBOOK,
        ROOT / "docs" / "proof-cookbook" / "recipes" / "qf-uf-congruence-alethe.md",
    ):
        text = path.read_text(encoding="utf-8")
        if "--test lean_crosscheck lean_crosscheck_representative" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: Lean command must invoke the registered "
                "representative test harness"
            )

    ir_range_markers = (
        (IR_SORT, "Nested arrays and nested sequences remain deferred"),
        (IR_VALUE, "exact within the `i128`"),
        (IR_EVAL, "Integers are exact within the i128 reference range"),
        (LEARN_THEORIES, "not an arbitrary-precision implementation claim"),
        (TERM_IR_DOC, "exact within the current `i128` reference range"),
        (EVALUATOR_DOC, "rational numerator/denominator components are `i128`-based"),
        (LIMITATIONS, "Concrete integer/rational reference evaluation is range-bounded"),
    )
    for path, marker in ir_range_markers:
        text = " ".join(path.read_text(encoding="utf-8").split())
        if marker not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: missing concrete arithmetic range marker "
                f"{marker!r}"
            )

    ir_term_text = IR_TERM.read_text(encoding="utf-8")
    for marker in ("Forall(SymbolId)", "Exists(SymbolId)"):
        if marker not in ir_term_text:
            failures.append(
                f"{IR_TERM.relative_to(ROOT)}: missing quantifier marker {marker!r}"
            )

    p4dfa_neither = (
        snapshot["p4dfa_files_20s"]
        - snapshot["p4dfa_both_decided_20s"]
        - snapshot["p4dfa_axeyum_only_20s"]
        - snapshot["p4dfa_z3_only_20s"]
    )
    north_star_markers = (
        (NORTH_STAR_ORIENTATION, "status ledger or a schedule"),
        (
            NORTH_STAR_ORIENTATION,
            "Selected competitive cells do not establish broad product parity",
        ),
        (NORTH_STAR_ORIENTATION, "`Op::Forall(SymbolId)`"),
        (
            NORTH_STAR_ORIENTATION,
            f"the other {p4dfa_neither} are not decided by either",
        ),
        (NORTH_STAR_PLAN, "the target identity"),
        (NORTH_STAR_PLAN, "assurance gaps rather than pretending"),
        (
            NORTH_STAR_PLAN,
            "missing evidence is never relabeled as a certified `unsat`",
        ),
    )
    for path, marker in north_star_markers:
        text = " ".join(path.read_text(encoding="utf-8").split())
        if marker not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: missing north-star boundary marker "
                f"{marker!r}"
            )

    proof_sat_text = PROOF_SAT.read_text(encoding="utf-8")
    if "pub fn solve_with_drat_proof" not in proof_sat_text:
        failures.append(
            f"{PROOF_SAT.relative_to(ROOT)}: proof-producing SAT entry point missing"
        )

    foundational_dag_markers = (
        "maintained architectural contract",
        "execution phase or a complete implementation inventory",
        "Foundation invariant: Bool And Scalar BV",
        "Phase 6 landed entry contract: Custom SAT Core",
        "custom proof-producing CDCL core and in-tree DRAT checker now exist",
        "selected quantifier routes have landed at differing depth",
    )
    normalized_foundational_dag = " ".join(foundational_dag_text.split())
    for marker in foundational_dag_markers:
        if marker not in normalized_foundational_dag:
            failures.append(
                f"{FOUNDATIONAL_DAG.relative_to(ROOT)}: missing foundation marker "
                f"{marker!r}"
            )

    quotient_adr_text = QUOTIENT_ADR.read_text(encoding="utf-8")
    for marker in (
        "Status: proposed",
        "M4 differential and final acceptance remain open",
    ):
        if marker not in quotient_adr_text:
            failures.append(
                f"{QUOTIENT_ADR.relative_to(ROOT)}: missing quotient marker {marker!r}"
            )

    normalized_foundation_roadmap = " ".join(foundation_roadmap_text.split())
    for marker in (
        "first T6.0.3 four-seam seed is retained",
        "twice-identical 576-row quotient package",
        "ADR-0365",
        "final acceptance remain open",
        "not final TL2.10 acceptance",
    ):
        if marker not in normalized_foundation_roadmap:
            failures.append(
                f"{FOUNDATION_ROADMAP.relative_to(ROOT)}: missing roadmap marker "
                f"{marker!r}"
            )

    bv_lowering_text = BV_LOWERING.read_text(encoding="utf-8")
    for marker in ("fn lower_shift_op", "fn shift_ops_match_ground_evaluator"):
        if marker not in bv_lowering_text:
            failures.append(
                f"{BV_LOWERING.relative_to(ROOT)}: missing shift marker {marker!r}"
            )

    sat_bv_backend_text = SAT_BV_BACKEND.read_text(encoding="utf-8")
    for marker in (
        "config.native_cdcl || config.prove_unsat",
        "SatProofStatus::Checked",
        "downgrade to `Unknown`",
    ):
        if marker not in sat_bv_backend_text:
            failures.append(
                f"{SAT_BV_BACKEND.relative_to(ROOT)}: missing assurance marker "
                f"{marker!r}"
            )

    normalized_research_questions = " ".join(research_questions_text.split())
    for marker in (
        "maintained question register",
        "This register is not an execution queue",
        "- [x] How are symbolic shifts encoded?",
        "staged barrel-shift network",
        "- [x] Should unsat proof checking be required in high-assurance mode?",
        "records `SatProofStatus::Checked`",
        "default BatSat adapter remains lower-assurance `Unchecked`",
        "not an equality-saturation rewrite optimizer",
        "subset promised by a first release remains an explicit release decision",
    ):
        if marker not in normalized_research_questions:
            failures.append(
                f"{RESEARCH_QUESTIONS.relative_to(ROOT)}: missing question marker "
                f"{marker!r}"
            )

    string_source_markers = (
        (SMTLIB_PARSE, "const STRING_MAX_LEN: u32 = 12;"),
        (SMTLIB_PARSE, "pub(crate) const STRING_BOUND_CAP: u32 = 512;"),
        (SMTLIB_FRONT_DOOR, "const DEFAULT_STRING_BOUND: u32 = 12;"),
        (SMTLIB_FRONT_DOOR, "const STRING_BOUND_LADDER: [u32; 3] = [24, 32, 48];"),
        (SUPPORT_MATRIX_LEDGER, "solver: SolverStatus::SoundIncomplete"),
        (SUPPORT_MATRIX_LEDGER, "12-byte packed-BV"),
        (CAPABILITY_LEDGER, "declared strings default to 12 bytes"),
    )
    source_texts: dict[Path, str] = {}
    for path, marker in string_source_markers:
        text = source_texts.setdefault(path, path.read_text(encoding="utf-8"))
        if marker not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: missing bounded-string source marker "
                f"{marker!r}"
            )

    string_doc_markers = (
        (
            GENERATED_SUPPORT_MATRIX,
            "| strings (bounded) | accepted (bounded) | lowered (no IR sort) | "
            "sound, incomplete (unknown-safe) | none |",
        ),
        (GENERATED_SUPPORT_MATRIX, "12-byte packed-BV window"),
        (GENERATED_CAPABILITY_MATRIX, "24/32/48-byte retries"),
        (LIMITATIONS, "declared strings start at 12 bytes"),
        (LIMITATIONS, "some `str.to_int`/`str.from_int`"),
    )
    doc_texts: dict[Path, str] = {}
    for path, marker in string_doc_markers:
        text = doc_texts.setdefault(path, path.read_text(encoding="utf-8"))
        normalized = " ".join(text.split())
        if marker not in normalized:
            failures.append(
                f"{path.relative_to(ROOT)}: missing bounded-string documentation "
                f"marker {marker!r}"
            )

    p27_texts = {
        P27_INDEX: P27_INDEX.read_text(encoding="utf-8"),
        P27_CURRENT: P27_CURRENT.read_text(encoding="utf-8"),
    }
    for path, text in p27_texts.items():
        for pattern in P27_STALE_PATTERNS:
            if match := pattern.search(text):
                line = text.count("\n", 0, match.start()) + 1
                failures.append(
                    f"{path.relative_to(ROOT)}:{line}: stale P2.7 string status: "
                    f"{match.group(0)!r}"
                )

    for path, marker in (
        (IR_SORT, "Seq(ArraySortKey)"),
        (IR_TERM, "SeqLen"),
        (WORD_STRINGS, "solve_word_equations"),
        (WORD_STRINGS, "refute_word_equations"),
    ):
        if marker not in path.read_text(encoding="utf-8"):
            failures.append(
                f"{path.relative_to(ROOT)}: missing P2.7 implementation marker {marker!r}"
            )

    normalized_p27 = {
        path: " ".join(text.split()) for path, text in p27_texts.items()
    }
    for path, marker in (
        (P27_INDEX, "Status: implementation in progress"),
        (P27_INDEX, "The current implementation is a portfolio"),
        (P27_INDEX, "A — first-class IR + length combination"),
        (P27_INDEX, "E — models + automata"),
        (P27_CURRENT, "Status: maintained implementation snapshot"),
        (P27_CURRENT, "sound, incomplete (unknown-safe)"),
        (P27_CURRENT, "Default declared SMT-LIB string window | 12 bytes"),
        (P27_CURRENT, "Front-door retry ladder | 24, 32, then 48 bytes"),
        (P27_CURRENT, "Packed result/window hard cap | 512 bytes"),
        (P27_CURRENT, "Selected checked subroutes do not upgrade the entire fragment"),
    ):
        if marker not in normalized_p27[path]:
            failures.append(
                f"{path.relative_to(ROOT)}: missing P2.7 documentation marker {marker!r}"
            )

    required_gap_markers = (
        f"{snapshot['decided']} / {snapshot['files']}",
        f"{snapshot['compared']} oracle-compared",
        f"{snapshot['decide_strong_rows']} / {snapshot['rows']} rows",
        f"{snapshot['fully_dominant_rows']} / {snapshot['complete_audits']} audited rows",
        f"{snapshot['dominant_decisions']} / {snapshot['audited_decisions']} decisions",
        f"{snapshot['baseline_unsat']} baseline `unsat` decisions",
        f"{snapshot['audit_reproduced_unsat']} evidence-audit `unsat` outcomes",
        f"{snapshot['certified_unsat']} certified outcomes",
        f"{snapshot['independently_checked_unsat']} independently checked outcomes",
        f"{snapshot['audit_reported_checked_unsat'] - snapshot['independently_checked_unsat']} vacuous `bare-unsat` check results",
        f"{snapshot['lean_checked_unsat']} Lean-checked outcomes",
        f"{snapshot['p4dfa_axeyum_20s']} / {snapshot['p4dfa_files_20s']}",
        f"{snapshot['p4dfa_z3_20s']} / {snapshot['p4dfa_files_20s']}",
        f"{snapshot['p4dfa_both_decided_20s']} jointly decided",
        f"{snapshot['p4dfa_axeyum_only_20s']} Axeyum-only",
        f"{snapshot['p4dfa_z3_only_20s']} Z3-only",
        f"{snapshot['public_inventory_decided']} / {snapshot['public_inventory_files']}",
        f"{snapshot['public_inventory_known_agree']} known-status agreements",
        f"{snapshot['public_inventory_unadjudicated_decisions']} unadjudicated decisions",
        f"{snapshot['public_inventory_wrong']} wrong verdicts",
        f"{snapshot['qfbv_head_to_head_axeyum']} / {snapshot['qfbv_head_to_head_files']}",
        f"{snapshot['scoreboard_file_occurrences']} file-backed occurrences",
        f"{snapshot['scoreboard_unique_ids']} unique normalized benchmark paths",
        f"{snapshot['scoreboard_repeated_occurrences']} repeated occurrences",
        f"{snapshot['scoreboard_aggregate_only']} aggregate-only synthetic cases",
        f"{snapshot['public_source_families']} source families",
        f"{snapshot['public_exact_duplicate_groups']} exact byte-duplicate groups",
        f"{snapshot['scoreboard_unique_sha256']} unique byte contents",
        f"{snapshot['scoreboard_exact_duplicate_groups']} exact-alias groups",
        f"{snapshot['cross_regime_unique_overlap']} contents overlap",
        f"{snapshot['neutral_measurement_rows']} neutral-oracle rows",
    )
    gap_text = GAP_DOC.read_text(encoding="utf-8")
    for marker in required_gap_markers:
        if marker not in gap_text:
            failures.append(f"{GAP_DOC.relative_to(ROOT)}: missing measured marker {marker!r}")

    parity_audit_text = PARITY_AUDIT.read_text(encoding="utf-8")
    for marker in (
        f"{snapshot['public_inventory_known_agree']} known-status agreements",
        f"{snapshot['public_inventory_unadjudicated_decisions']} unadjudicated decisions",
        f"{snapshot['p4dfa_both_decided_20s']} jointly decided",
        f"{snapshot['p4dfa_axeyum_only_20s']} Axeyum-only",
        f"{snapshot['p4dfa_z3_only_20s']} Z3-only",
        "general solving-power distance to Z3 is not measured",
        "71/71 accepted",
        "70/70 accepted",
    ):
        if marker not in parity_audit_text:
            failures.append(
                f"{PARITY_AUDIT.relative_to(ROOT)}: missing evidence-audit marker {marker!r}"
            )

    lean_source = LEAN_CROSSCHECK_SOURCE.read_text(encoding="utf-8")
    family_block = re.search(
        r"const FAMILY_BUILDERS: &\[FamilyBuilder\] = &\[(.*?)\n\];",
        lean_source,
        re.DOTALL,
    )
    if family_block is None:
        failures.append("cannot locate Lean FAMILY_BUILDERS registry")
        lean_family_count = 0
    else:
        lean_family_count = len(
            re.findall(r"^\s+[a-z][a-z0-9_]+,\s*$", family_block.group(1), re.MULTILINE)
        )

    lean_gate_text = LEAN_GATE_AUDIT.read_text(encoding="utf-8")
    for marker in (
        "modules=71|checked=67|budget_skipped=0|failed=4",
        "families=71|modules=71|checked=71|budget_skipped=0|failed=0",
        f"families={lean_family_count}|modules={lean_family_count}|"
        f"checked={lean_family_count}|budget_skipped=0|failed=0",
        "budget_skipped=0|failed=0",
        "MISSING_LEAN_FAIL_CLOSED",
        "first corrected remote attempt",
        "no remote source-acceptance",
    ):
        if marker not in lean_gate_text:
            failures.append(
                f"{LEAN_GATE_AUDIT.relative_to(ROOT)}: missing Lean-gate marker {marker!r}"
            )

    lean_installer_text = LEAN_INSTALLER.read_text(encoding="utf-8")
    for marker in (
        "ELAN_TOOLCHAIN=",
        'elan" which lean',
        "lean_bin=",
        "resolved Lean executable",
    ):
        if marker not in lean_installer_text:
            failures.append(
                f"{LEAN_INSTALLER.relative_to(ROOT)}: missing executable-identity marker {marker!r}"
            )

    workflow_text = CI_WORKFLOW.read_text(encoding="utf-8")
    for marker in (
        "ELAN_TOOLCHAIN=",
        'elan" which lean',
        "AXEYUM_LEAN_BIN=$lean_bin",
        'cd "$RUNNER_TEMP"',
    ):
        if marker not in workflow_text:
            failures.append(
                f"{CI_WORKFLOW.relative_to(ROOT)}: missing executable-identity marker {marker!r}"
            )
    if "AXEYUM_LEAN_BIN=$lean_root/elan-home/bin/lean" in workflow_text:
        failures.append(
            f"{CI_WORKFLOW.relative_to(ROOT)}: AXEYUM_LEAN_BIN must not name the elan shim"
        )

    project_state_markers = (
        f"{snapshot['decided']} / {snapshot['files']}",
        f"{snapshot['compared']} oracle-compared",
        f"{snapshot['disagree']} recorded disagreements",
        f"{snapshot['decide_strong_rows']} / {snapshot['rows']}",
        f"{snapshot['fully_dominant_rows']} / {snapshot['complete_audits']}",
        f"{snapshot['scoreboard_file_occurrences']} occurrences",
        f"{snapshot['scoreboard_unique_ids']} unique normalized paths",
        f"{snapshot['scoreboard_unique_sha256']} unique byte contents",
        f"{snapshot['scoreboard_exact_duplicate_groups']} exact-alias groups",
        f"{snapshot['scoreboard_exact_duplicate_excess']} additional path",
        f"{snapshot['cross_regime_unique_overlap']} exact contents",
        f"{snapshot['public_inventory_decided']} / {snapshot['public_inventory_files']}",
        f"{snapshot['public_inventory_known_agree']} known-status agreements",
        f"{snapshot['public_inventory_unadjudicated_decisions']} unadjudicated decisions",
        f"{snapshot['public_inventory_declined']} explicit declines",
        f"{snapshot['public_inventory_no_answer']} no-answer outcomes",
        f"{snapshot['public_inventory_wrong']} wrong verdicts",
        f"{snapshot['dominant_unsat']} / {snapshot['baseline_unsat']}",
        f"{snapshot['uncertified_unsat']} uncertified",
        f"{snapshot['lean_reconstruction_gap']} certified",
        f"{snapshot['proof_production_errors']} proof-production errors",
        f"{snapshot['p4dfa_axeyum_20s']} / {snapshot['p4dfa_files_20s']}",
        f"{snapshot['qfbv_head_to_head_axeyum']} / {snapshot['qfbv_head_to_head_files']}",
        "zero interactive textual-session rows",
        "cannot be retroactively classified",
        "fully competition-faithful",
        f"{lean_family_count}/{lean_family_count} accepted",
    )
    project_state_text = PROJECT_STATE.read_text(encoding="utf-8")
    for marker in project_state_markers:
        if marker not in project_state_text:
            failures.append(
                f"{PROJECT_STATE.relative_to(ROOT)}: missing measured marker {marker!r}"
            )

    for logic in ("QF_NIA", "QF_UFLIA", "QF_IDL", "QF_LRA", "QF_RDL"):
        if logic not in parity_rows:
            failures.append(
                f"{PARITY_LEDGER.relative_to(ROOT)}: missing required {logic} row"
            )
            continue
        axeyum, reference, ratio, disagreements = parity_rows[logic]
        expected = f"| {logic} | {axeyum} | {reference} | {ratio} | {disagreements} |"
        actual = re.findall(
            rf"^\| {re.escape(logic)} \| [^\n]+$", project_state_text, re.MULTILINE
        )
        if actual != [expected]:
            failures.append(
                f"{PROJECT_STATE.relative_to(ROOT)}: latest {logic} parity row "
                f"must be {expected!r}, got {actual!r}"
            )

    example_paths = sorted(ROOT.glob("crates/*/examples/*.rs"))
    example_catalog_text = EXAMPLE_CATALOG.read_text(encoding="utf-8")
    for path in example_paths:
        marker = f"](../../{path.relative_to(ROOT)})"
        if marker not in example_catalog_text:
            failures.append(
                f"{EXAMPLE_CATALOG.relative_to(ROOT)}: missing Cargo example "
                f"{path.relative_to(ROOT)}"
            )
    example_count = len(example_paths)
    documentation_plan_text = DOCUMENTATION_PLAN.read_text(encoding="utf-8")
    if f"all {example_count} checked-in Cargo examples" not in documentation_plan_text:
        failures.append(
            f"{DOCUMENTATION_PLAN.relative_to(ROOT)}: missing current "
            f"{example_count}-example inventory marker"
        )
    plan_text = (ROOT / "PLAN.md").read_text(encoding="utf-8")
    if f"all {example_count} Cargo examples" not in plan_text:
        failures.append(
            f"PLAN.md: missing current {example_count}-example inventory marker"
        )

    consumer_text = " ".join(CONSUMER_README.read_text(encoding="utf-8").split())
    consumer_markers = (
        f"{consumers['property']['cases']} cases: {consumers['property']['safe']} proved, "
        f"{consumers['property']['bugs']} disproved, {consumers['property']['unknown']} unknown",
        f"{consumers['evm']['cases']} cases: {consumers['evm']['bugs']} bugs, "
        f"{consumers['evm']['safe']} safe, {consumers['evm']['unknown']} unknown",
        f"{consumers['verify']['cases']} cases: {consumers['verify']['bugs']} bugs, "
        f"{consumers['verify']['safe']} verified, {consumers['verify']['unknown']} unknown",
        f"**{consumers['cases']} cases, {consumers['bugs']} bugs/disproofs, "
        f"{consumers['safe']} safe/proved results, {consumers['unknown']} unknown, "
        f"and {consumers['disagree']} disagreements**",
    )
    for marker in consumer_markers:
        if marker not in consumer_text:
            failures.append(
                f"{CONSUMER_README.relative_to(ROOT)}: missing current consumer marker "
                f"{marker!r}"
            )

    consumer_scoreboard_text = CONSUMER_SCOREBOARD.read_text(encoding="utf-8")
    consumer_total_row = (
        f"| **Total** | — | **{consumers['cases']}** | **{consumers['bugs']}** | "
        f"**{consumers['safe']}** | **{consumers['unknown']}** | "
        f"**{consumers['disagree']}** | — | — |"
    )
    if consumer_total_row not in consumer_scoreboard_text:
        failures.append(
            f"{CONSUMER_SCOREBOARD.relative_to(ROOT)}: aggregate row must be "
            f"{consumer_total_row!r}"
        )
    for path in (ROOT / "README.md", DOCUMENTATION_PLAN, ROOT / "PLAN.md"):
        marker = f"{consumers['cases']}-case aggregate"
        if marker not in path.read_text(encoding="utf-8"):
            failures.append(
                f"{path.relative_to(ROOT)}: missing current consumer marker {marker!r}"
            )

    benchmark_text = BENCHMARK_GUIDE.read_text(encoding="utf-8")
    for marker in (
        f"{snapshot['scoreboard_file_occurrences']} file occurrences",
        f"{snapshot['scoreboard_unique_ids']} normalized paths",
        f"{snapshot['scoreboard_unique_sha256']} exact byte contents",
        f"{snapshot['cross_regime_unique_overlap']} contents occur",
        f"{snapshot['public_inventory_known_agree']} known-status agreements",
        f"{snapshot['public_inventory_unadjudicated_decisions']} unadjudicated decisions",
        "43.4% of the public inventory",
        "do not average them",
        "cannot be retrospectively reclassified",
        "without a new v2 run",
        "`CARGO_BUILD_JOBS=1`",
    ):
        if marker not in benchmark_text:
            failures.append(
                f"{BENCHMARK_GUIDE.relative_to(ROOT)}: missing measured marker {marker!r}"
            )

    categorical_text = CATEGORICAL_AUDIT.read_text(encoding="utf-8")
    for marker in (
        "125 / 125 passed",
        "94 tests",
        "Horn 22",
        "abduction nine",
        "General SyGuS",
        "No SMT-LIB `get-interpolant`",
        "No SMT-LIB `declare-rel`/`rule`/`query`",
        "No SMT-LIB `get-abduct`",
    ):
        if marker not in categorical_text:
            failures.append(
                f"{CATEGORICAL_AUDIT.relative_to(ROOT)}: missing categorical marker {marker!r}"
            )

    ci_text = CI_WORKFLOW.read_text(encoding="utf-8")
    lean_attestation = (
        "LEAN_CROSSCHECK|label=representative|"
        f"families={lean_family_count}|modules={lean_family_count}|"
        f"checked={lean_family_count}|budget_skipped=0|failed=0"
    )
    for marker in (
        "AXEYUM_LEAN_BUDGET_SECS: 0",
        "AXEYUM_LEAN_JOBS: 2",
        "--test lean_crosscheck",
        "lean_crosscheck_representative -- --nocapture --exact",
        "./scripts/install-pinned-lean.sh",
        lean_attestation,
    ):
        if marker not in ci_text:
            failures.append(
                f"{CI_WORKFLOW.relative_to(ROOT)}: missing representative Lean gate {marker!r}"
            )
    if "leanprover/lean-action" in ci_text:
        failures.append(
            f"{CI_WORKFLOW.relative_to(ROOT)}: non-Lake Axeyum job must not use lean-action"
        )

    installer_text = LEAN_INSTALLER.read_text(encoding="utf-8")
    for marker in (
        "elan_version=v4.2.3",
        "df0b2b3a439961ffcbb3985214365ffe40f49bc871df04dff268c7d8e21ca8b2",
        "sha256sum --check --status",
        'toolchain=$(tr -d \'[:space:]\' < "$repo_root/lean-toolchain")',
    ):
        if marker not in installer_text:
            failures.append(
                f"{LEAN_INSTALLER.relative_to(ROOT)}: missing pinned installer marker {marker!r}"
            )

    line = "|".join(f"{key}={value}" for key, value in snapshot.items())
    line += (
        f"|consumer_cases={consumers['cases']}"
        f"|consumer_bugs={consumers['bugs']}"
        f"|consumer_safe={consumers['safe']}"
        f"|consumer_unknown={consumers['unknown']}"
        f"|consumer_disagree={consumers['disagree']}"
        "|prover_goal_axis=not_started"
        "|prover_nat=arbitrary_precision"
        "|prover_uf_identity=source_term"
        f"|prover_axioms={axiom_total}"
        f"|prover_axioms_derivable={axiom_classes['derivable-theorem']}"
        f"|prover_axioms_external={axiom_classes['external-assumption']}"
        f"|prover_axioms_primitive={axiom_classes['primitive-interface']}"
        "|beginner_unsat_assurance=route_specific"
        "|north_star_status=aspirational"
        "|north_star_binders=first_order_present"
        "|foundation_phases=landed"
        "|foundation_custom_cdcl=proof_producing"
        "|foundation_quotient=offline_m1_m3"
        "|research_symbolic_shifts=resolved"
        "|research_high_assurance_unsat=resolved"
        "|theory_combination=online_cdclt_with_guarded_fallback"
        "|cas_assurance=local_route_specific"
        "|strings_status=sound_incomplete"
        "|strings_default_bound=12"
        "|strings_ladder_max=48"
        "|strings_packed_cap=512"
        "|p27_status=partial_portfolio"
    )
    print(f"PARITY_DOCS|{line}")
    if failures:
        for failure in failures:
            print(f"ERROR: {failure}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
