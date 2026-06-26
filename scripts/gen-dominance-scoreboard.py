#!/usr/bin/env python3
"""Generate bench-results/DOMINANCE.md from measured baselines plus proof routes.

This is the conservative companion to bench-results/SCOREBOARD.md.  The
scoreboard answers "how much does axeyum decide vs Z3?"  This report answers
"where is axeyum close to the four-constraint Pareto-dominance claim?"

The true headline metric from PLAN.md is per-instance:

    decided within budget
    + DISAGREE = 0
    + every unsat has a re-checked, trust-hole-free Lean certificate
    + pure-Rust / deterministic / unsafe-free

The division baseline JSONs do not record per-instance Lean certificate
coverage, so rows without a committed audit remain readiness entries.  Rows with
complete `cargo run -p axeyum-bench --example audit_dominance` artifacts under
bench-results/dominance/ report exact audited dominance coverage.

Usage:
    python3 scripts/gen-dominance-scoreboard.py

Reads:
    bench-results/baselines/*solver-vs-z3*.json
    bench-results/baselines/qf-nra-synthetic-graduated-vs-z3.json
    bench-results/baselines/qf-nia-synthetic-graduated-vs-z3.json
    bench-results/dominance/*.json
    scripts/gen-scoreboard.py

Writes:
    bench-results/DOMINANCE.md
"""

from __future__ import annotations

import importlib.util
import glob
import json
import os
from collections import Counter
from dataclasses import dataclass

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT_PATH = os.path.join(REPO_ROOT, "bench-results", "DOMINANCE.md")
GEN_SCOREBOARD = os.path.join(REPO_ROOT, "scripts", "gen-scoreboard.py")
AUDITS_DIR = os.path.join(REPO_ROOT, "bench-results", "dominance")


def load_scoreboard_module():
    spec = importlib.util.spec_from_file_location("axeyum_gen_scoreboard", GEN_SCOREBOARD)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {GEN_SCOREBOARD}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rel(path: str) -> str:
    return os.path.relpath(path, REPO_ROOT).replace(os.sep, "/")


def load_audits() -> dict[str, dict]:
    """Load committed per-instance dominance audits by baseline path."""
    audits: dict[str, dict] = {}
    for path in sorted(glob.glob(os.path.join(AUDITS_DIR, "*.json"))):
        with open(path, encoding="utf-8") as fh:
            data = json.load(fh)
        baseline = data.get("baseline")
        if not isinstance(baseline, str):
            continue
        data["_file"] = rel(path)
        audits[baseline] = data
    return audits


@dataclass(frozen=True)
class ProofRoute:
    lane: str
    status: str
    next_action: str
    lean_candidate: bool = True


PROOF_ROUTES: dict[str, ProofRoute] = {
    "BV": ProofRoute(
        "guarded quantifier / finite BV Lean slices",
        "partial",
        "audit quantified-BV rows with per-instance Lean reconstruction",
    ),
    "LIA": ProofRoute(
        "finite guarded-Int quantifier Alethe plus arithmetic checker",
        "partial",
        "separate guarded finite-Int unsats from unsupported infinite-domain cases",
    ),
    "QF_ABV": ProofRoute(
        "array ROW / select-congruence Alethe plus narrow Lean cross-checks",
        "partial",
        "classify array unsats by ROW/congruence vs general ArrayElim",
    ),
    "QF_ALIA": ProofRoute(
        "checked Int-array ROW/readback refuters plus scalar-array replay",
        "partial",
        "move solve frontier to AUFLIA scalar search depth",
    ),
    "QF_AUFBV": ProofRoute(
        "array+UF/BV certificates exist for narrow ROW/congruence subcases",
        "partial",
        "split direct ROW/congruence wins from general array elimination",
    ),
    "QF_AUFLIA": ProofRoute(
        "Int-array ROW/congruence route is emerging",
        "partial",
        "finish decide frontier before spending cert budget beyond narrow refuters",
    ),
    "QF_AX": ProofRoute(
        "declared-sort array ROW/extensionality models plus narrow unsat certificates",
        "partial",
        "broaden beyond this small cvc5 slice with neutral QF_AX arrays",
    ),
    "QF_BV": ProofRoute(
        "Lean-kernel bitwise/comparison subfragment; DRAT/Alethe beyond that",
        "partial",
        "add per-instance BV operator classifier; close mul/rem/shift Lean gap",
    ),
    "QF_BVFP": ProofRoute(
        "BV side has certificates; FP lowering is not Lean-kernel certified",
        "partial",
        "separate pure-BV certs from FP-to-BV trust-hole cases",
        False,
    ),
    "QF_DT": ProofRoute(
        "datatype field axioms and acyclicity are real-Lean validated",
        "partial",
        "witness the general DatatypeElim dispatch end to end",
    ),
    "QF_FF": ProofRoute(
        "finite-field lowering certifies through checked finite/BV routes",
        "partial",
        "broaden finite-field audits beyond the cvc5 slice and grow algebraic certificates",
        False,
    ),
    "QF_FP": ProofRoute(
        "small FP8_E5M2 faithfulness witnessed; large FP is not Lean-certified",
        "partial",
        "keep FP as measured-competitive, not Lean-dominant, until Fpa2Bv certs grow",
        False,
    ),
    "QF_LIA": ProofRoute(
        "Diophantine and integer-interval Lean fragments",
        "partial",
        "audit unsats by Diophantine/IntInequality/general LIA route",
    ),
    "QF_LRA": ProofRoute(
        "Farkas and disjunctive-LRA Lean reconstruction",
        "strong-partial",
        "run per-instance Lean reconstruction over the committed LRA slice",
    ),
    "QF_NIA": ProofRoute(
        "bounded int-blast has DRAT witness; Lean only for narrow integer fragments",
        "partial",
        "separate Diophantine/interval unsats from bit-blasted bounded boxes",
    ),
    "QF_NRA": ProofRoute(
        "degree-2 SOS to Lean only",
        "partial",
        "measure SOS-covered unsats separately from general nonlinear search",
    ),
    "QF_S": ProofRoute(
        "bounded string lowering has no broad Lean-kernel route",
        "none",
        "decider/front-end work first; proof lane later",
        False,
    ),
    "QF_SEQ": ProofRoute(
        "bounded sequence lowering has no broad Lean-kernel route",
        "none",
        "decider/front-end work first; proof lane later",
        False,
    ),
    "QF_SLIA": ProofRoute(
        "bounded string/LIA lowering has no broad Lean-kernel route",
        "none",
        "migrate strings to solver StrTerm API before proof investment",
        False,
    ),
    "QF_UF": ProofRoute(
        "EUF congruence Lean reconstruction",
        "strong-partial",
        "remeasure after first-class uninterpreted sorts, then run Lean audit",
    ),
    "QF_UFBV": ProofRoute(
        "EUF/BV congruence Lean reconstruction plus BV subfragment limits",
        "strong-partial",
        "audit whether measured unsats avoid BV mul/rem/shift holes",
    ),
    "QF_UFFF": ProofRoute(
        "UF+finite-field lowering certifies through checked local BV+UF routes",
        "partial",
        "broaden UFFF audits beyond the cvc5 finite-field+UF slice",
        False,
    ),
    "QF_UFLIA": ProofRoute(
        "UFLIA interpolation/reconstruction covers narrow integer fragments",
        "partial",
        "audit UFLIA unsats by integer-fragment route and UF congruence shape",
    ),
    "UF": ProofRoute(
        "quantified UF over infinite domains has no dominance route yet",
        "none",
        "decider/model-finding work first",
        False,
    ),
}


def fmt_pct(value: float) -> str:
    return f"{value:.0f}%"


def fmt_par2(value) -> str:
    if value is None:
        return "-"
    return f"{value:.3f}"


def decide_band(row: dict) -> str:
    pct = row["decide_pct"]
    if pct >= 80.0:
        return "strong"
    if pct >= 40.0:
        return "mid"
    return "weak"


def dominance_action(row: dict, route: ProofRoute) -> str:
    if row["disagree"] != 0:
        return "soundness first"
    band = decide_band(row)
    if route.status == "none":
        return "proof route missing"
    if not route.lean_candidate:
        return "build Lean route"
    if band == "strong" and route.status in {"strong-partial", "partial"}:
        return "audit now"
    if band == "mid" and route.status == "strong-partial":
        return "remeasure then audit"
    if band == "mid":
        return "grow decide + classify certs"
    return "decider first"


def exact_dominance_action(row: dict, audit: dict | None, route: ProofRoute) -> str:
    if not audit_is_complete(row, audit):
        return dominance_action(row, route)
    summary = audit.get("summary", {})
    if summary.get("audit_errors", 0):
        return "fix audit errors"
    if summary.get("timeouts", 0):
        return "fix audit timeouts"
    audited_unsat = summary.get("audited_unsat", 0)
    lean_unsat = summary.get("lean_checked_unsat", 0)
    if audited_unsat > lean_unsat:
        return "close Lean unsat gaps"
    dominant = summary.get("dominant_candidates", 0)
    audited = summary.get("audited_decided", row["decided"])
    if audited > dominant:
        return "certify remaining decided instances"
    return "dominant on audited row"


def audit_for(row: dict, audits: dict[str, dict]) -> dict | None:
    return audits.get(row["file"])


def audit_is_complete(row: dict, audit: dict | None) -> bool:
    if not audit or not audit.get("complete_audit"):
        return False
    summary = audit.get("summary", {})
    return summary.get("audited_decided") == row["decided"]


def fmt_audit_status(row: dict, audit: dict | None) -> str:
    if audit_is_complete(row, audit):
        return "complete"
    if audit:
        summary = audit.get("summary", {})
        audited = summary.get("audited_decided", 0)
        total = summary.get("baseline_decided", row["decided"])
        return f"partial {audited}/{total}"
    return "not run"


def fmt_dominant_pct(row: dict, audit: dict | None) -> str:
    if not audit:
        return "-"
    summary = audit.get("summary", {})
    audited = summary.get("audited_decided", 0)
    dominant = summary.get("dominant_candidates", 0)
    pct = summary.get("dominant_pct_audited")
    if pct is None:
        return "-"
    suffix = "" if audit_is_complete(row, audit) else " audited"
    return f"{pct:.0f}% ({dominant}/{audited}){suffix}"


def fmt_lean_unsat(audit: dict | None) -> str:
    if not audit:
        return "-"
    summary = audit.get("summary", {})
    checked = summary.get("lean_checked_unsat", 0)
    unsat = summary.get("audited_unsat", 0)
    pct = summary.get("lean_unsat_pct", 0.0)
    return f"{pct:.0f}% ({checked}/{unsat})"


def fmt_audit_gaps(audit: dict | None) -> str:
    if not audit:
        return "-"
    summary = audit.get("summary", {})
    gaps = []
    for key, label in (
        ("audit_errors", "errors"),
        ("baseline_mismatches", "mismatches"),
        ("timeouts", "timeouts"),
    ):
        value = summary.get(key, 0)
        if value:
            gaps.append(f"{label} {value}")
    unsat = summary.get("audited_unsat", 0)
    lean_checked = summary.get("lean_checked_unsat", 0)
    if unsat and lean_checked < unsat:
        gaps.append(f"Lean unsat {lean_checked}/{unsat}")
    evidence_checked = summary.get("evidence_checked", 0)
    audited = summary.get("audited_decided", 0)
    evidence_certified = summary.get("evidence_certified", 0)
    if audited and evidence_certified < audited:
        gaps.append(f"evidence certified {evidence_certified}/{audited}")
    if audited and evidence_checked < audited:
        gaps.append(f"evidence checked {evidence_checked}/{audited}")
    trust_holes = sorted(
        {
            hole
            for instance in audit.get("instances", [])
            for hole in instance.get("trust_holes", [])
        }
    )
    if trust_holes:
        gaps.append("trust holes " + ", ".join(trust_holes))
    timeout_phases = Counter(
        instance.get("timeout_phase", instance.get("audit_phase", "unknown"))
        for instance in audit.get("instances", [])
        if instance.get("audit_outcome") == "timeout"
    )
    if timeout_phases:
        phase_summary = ", ".join(
            f"{phase} {count}" for phase, count in sorted(timeout_phases.items())
        )
        gaps.append("timeout phases " + phase_summary)
    return ", ".join(gaps) if gaps else "none"


def build_markdown(rows: list[dict], audits: dict[str, dict]) -> str:
    rows = sorted(rows, key=lambda r: (r["logic"], -r["decide_pct"], r["slice"]))
    strong_rows = [r for r in rows if decide_band(r) == "strong"]
    complete_audits = [r for r in rows if audit_is_complete(r, audit_for(r, audits))]
    audit_now = [
        r
        for r in rows
        if dominance_action(r, PROOF_ROUTES.get(r["logic"], PROOF_ROUTES["UF"]))
        == "audit now"
    ]
    remaining_audit_now = [
        r for r in audit_now if not audit_is_complete(r, audit_for(r, audits))
    ]
    sound = sum(1 for r in rows if r["disagree"] == 0)
    compared = sum(r["compared"] for r in rows)
    total_files = sum(r["files"] for r in rows)
    total_decided = sum(r["decided"] for r in rows)

    lines: list[str] = []
    lines.append("# Pareto Dominance Readiness")
    lines.append("")
    lines.append(
        "> **Auto-generated. Do not edit by hand.** Regenerate with "
        "`python3 scripts/gen-dominance-scoreboard.py`."
    )
    lines.append("")
    lines.append(
        "This is the conservative companion to `bench-results/SCOREBOARD.md`. "
        "It does not replace the decide-rate scoreboard; it adds the proof-route "
        "axis needed by PLAN.md's four-constraint Pareto-dominance metric."
    )
    lines.append("")
    lines.append("## What This Measures")
    lines.append("")
    lines.append(
        "A row is Pareto-dominant only when it satisfies all four constraints: "
        "decided within budget, DISAGREE = 0, every `unsat` has a re-checked "
        "trust-hole-free Lean certificate, and the route is pure-Rust, "
        "deterministic, and unsafe-free."
    )
    lines.append("")
    lines.append(
        "The current benchmark JSONs record decide-rate, disagreement, and PAR-2, "
        "but they do **not** yet record per-instance Lean certificate coverage. "
        "Rows with a complete committed audit under `bench-results/dominance/` "
        "report exact audited `dominant%(D)`; rows without one remain readiness "
        "queue entries."
    )
    lines.append("")
    lines.append("## Headline")
    lines.append("")
    lines.append(
        f"- {len(rows)} measured division rows, {total_files} files, "
        f"{total_decided} decided, {compared} oracle-compared."
    )
    lines.append(
        f"- {sound}/{len(rows)} rows have DISAGREE = 0; any nonzero row must "
        "preempt dominance work."
    )
    lines.append(
        f"- {len(strong_rows)} rows are decide-strong (Decide% >= 80). "
        f"{len(audit_now)} have a current Lean route worth auditing now; the "
        "others need proof-route work before dominance measurement is meaningful."
    )
    lines.append(
        f"- Complete committed dominance audits with exact audited "
        f"`dominant%(D)`: {len(complete_audits)}. Remaining rows are readiness "
        "or partial-audit entries."
    )
    lines.append("")

    lines.append("## Audit Harness")
    lines.append("")
    lines.append(
        "The per-instance evidence/Lean audit entry point now exists:"
    )
    lines.append("")
    lines.append("```text")
    lines.append(
        "cargo run --release -p axeyum-bench --example audit_dominance -- "
        "<baseline.json> [timeout_ms] [limit] [out.json]"
    )
    lines.append("```")
    lines.append("")
    lines.append(
        "It re-runs baseline-decided instances through `produce_evidence`, "
        "re-checks the evidence, attempts `prove_unsat_to_lean_module` for "
        "`unsat`, and emits `evidence_certified`, `evidence_checked`, "
        "`lean_fragment`, `lean_checked`, `trust_holes`, and "
        "`dominant_candidate`. Local smoke runs already exposed both a positive "
        "`QfUfBv` Lean-certified unsat and real gaps where baseline-decided "
        "instances still lack transferable evidence."
    )
    lines.append("")

    lines.append("## Exact Audit Results")
    lines.append("")
    if complete_audits:
        lines.append(
            "Complete audit rows have one audit record for every baseline-decided "
            "instance in the row. `Dominant%` is exact for the audited row under "
            "the current evidence/Lean routes."
        )
        lines.append("")
        lines.append(
            "| Division | Slice | Decided | Dominant% | Lean unsat | Gaps | Artifact |"
        )
        lines.append("| --- | --- | ---: | ---: | ---: | --- | --- |")
        for row in complete_audits:
            audit = audit_for(row, audits)
            lines.append(
                "| {logic} | `{slice}` | {decided} | {dominant} | {lean} | {gaps} | `{artifact}` |".format(
                    logic=row["logic"],
                    slice=row["slice"],
                    decided=row["decided"],
                    dominant=fmt_dominant_pct(row, audit),
                    lean=fmt_lean_unsat(audit),
                    gaps=fmt_audit_gaps(audit),
                    artifact=audit["_file"],
                )
            )
    else:
        lines.append("No committed complete audit artifacts have been ingested yet.")
    lines.append("")

    lines.append("## First Audit Queue")
    lines.append("")
    lines.append(
        "These rows are the best immediate candidates: they are already "
        "decide-strong and have a non-empty Lean reconstruction route. The task is "
        "to measure how many decided unsats in the row actually fall inside that "
        "route."
    )
    lines.append("")
    lines.append(
        "| Division | Slice | Files | Decide% | DISAGREE | PAR-2 (s) | Lean route | Audit task |"
    )
    lines.append("| --- | --- | ---: | ---: | ---: | ---: | --- | --- |")
    for row in remaining_audit_now:
        route = PROOF_ROUTES[row["logic"]]
        lines.append(
            "| {logic} | `{slice}` | {files} | {pct} | {disagree} | {par2} | {lane} | {next} |".format(
                logic=row["logic"],
                slice=row["slice"],
                files=row["files"],
                pct=fmt_pct(row["decide_pct"]),
                disagree=row["disagree"],
                par2=fmt_par2(row.get("par2")),
                lane=route.lane,
                next=route.next_action,
            )
        )
    if not remaining_audit_now:
        lines.append("| - | - | 0 | - | - | - | - | - |")
    lines.append("")

    lines.append("## All Rows")
    lines.append("")
    lines.append(
        "`Dominance action` is intentionally conservative: it is an audit label, "
        "not a certification claim."
    )
    lines.append("")
    lines.append(
        "| Division | Slice | Files | Decided | Decide% | Band | DISAGREE | Audit | Dominant% | Lean unsat | Dominance action | Next action |"
    )
    lines.append(
        "| --- | --- | ---: | ---: | ---: | --- | ---: | --- | ---: | ---: | --- | --- |"
    )
    for row in rows:
        route = PROOF_ROUTES.get(
            row["logic"], ProofRoute("unknown", "none", "add route classification")
        )
        audit = audit_for(row, audits)
        lines.append(
            "| {logic} | `{slice}` | {files} | {decided} | {pct} | {band} | {disagree} | {audit} | {dominant} | {lean} | {action} | {next} |".format(
                logic=row["logic"],
                slice=row["slice"],
                files=row["files"],
                decided=row["decided"],
                pct=fmt_pct(row["decide_pct"]),
                band=decide_band(row),
                disagree=row["disagree"],
                audit=fmt_audit_status(row, audit),
                dominant=fmt_dominant_pct(row, audit),
                lean=fmt_lean_unsat(audit),
                action=exact_dominance_action(row, audit, route),
                next=route.next_action,
            )
        )
    lines.append("")

    lines.append("## Certification Route Legend")
    lines.append("")
    lines.append(
        "- `strong-partial`: a real Lean reconstruction route exists for an "
        "important subfragment, and the measured row is plausibly close enough "
        "to audit immediately."
    )
    lines.append(
        "- `partial`: some proof/checking route exists, but the measured row must "
        "be split by operator/reduction shape before a dominance percentage can "
        "be claimed."
    )
    lines.append(
        "- `none`: no broad Lean-kernel route exists for the measured row; push "
        "decider/front-end work or build a proof route first."
    )
    lines.append("")

    lines.append("## Next Generator Step")
    lines.append("")
    if remaining_audit_now:
        lines.append(
            "Run and commit more `bench-results/dominance/*.json` audit artifacts for "
            "the remaining `audit now` rows. Each complete artifact automatically "
            "promotes its row from readiness status to exact audited `dominant%(D)`."
        )
    else:
        lines.append(
            "The first `audit now` queue is clear. The next dominance movement comes "
            "from reducing the concrete proof/evidence gaps reported above, then "
            "regenerating the affected exact audit artifacts."
        )
    lines.append("")

    lines.append("## Provenance")
    lines.append("")
    lines.append(
        f"Generated by [`scripts/gen-dominance-scoreboard.py`](../{rel(__file__)}) "
        "from the same committed baseline JSONs consumed by "
        "[`scripts/gen-scoreboard.py`](../scripts/gen-scoreboard.py), committed "
        "`bench-results/dominance/*.json` audit artifacts, and the conservative "
        "proof-route map embedded in the generator."
    )
    lines.append("")
    return "\n".join(lines)


def main() -> None:
    scoreboard = load_scoreboard_module()
    rows = scoreboard.load_division_baselines() + scoreboard.load_synthetic_baselines()
    audits = load_audits()
    markdown = build_markdown(rows, audits)
    with open(OUT_PATH, "w", encoding="utf-8") as fh:
        fh.write(markdown)


if __name__ == "__main__":
    main()
