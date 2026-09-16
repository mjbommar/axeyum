#!/usr/bin/env python3
"""QUANT-REACH-DIFF -- classify each z3-used instance on ADR-2113's 53 UFLIA
cores against OUR admitted/rejected/never-matched ground set.

QUANT-INSTANCE-PROBE showed our ground checker refutes 6 of 7 cores when
handed z3's OWN instances as plain ground assertions -- the block is not
ground refutation. ADR-2133 showed a generation ladder over OUR accumulated
ground set reaches its check on 31 of 53 cores and refutes at NONE -- the
refutation is absent from our ground set at every generation, not buried in
it. This script names, per z3 instance, WHERE it is lost:

  ADMITTED         identical body (modulo commutative-arg order and Skolem
                    collapse) is in our own admitted (gen>=1) ground set.
  MATCHED-REJECTED  not admitted, but every one of z3's substitution
                    arguments IS a term in our ground set (any generation) --
                    so e-matching could have formed the tuple -- and the
                    run's rejection census shows a nonzero typed reason.
  NEVER-MATCHED     not admitted, arguments present, but no rejection
                    evidence attributes a formed-and-dropped tuple to it --
                    the trigger did not fire on this substitution.
  NESTED            z3's own instance body still carries an unresolved outer
                    bound variable (a nested instantiation, `BOUND_VAR` in
                    z3-proof-instances.py) -- kept as its own class, never
                    merged into NEVER-MATCHED, per z3-proof-instances.py's own
                    `not_ground` list.

# Method and its honest limits

z3's proof rewrites terms internally (z3-proof-instances.py's own docstring:
the recovered body is "z3's own internally-rewritten form", not surface
syntax) and our engine rewrites/simplifies too, so a body-level STRING
comparison after normalization is a sound necessary check for ADMITTED
(identical strings ARE the same term) but not a complete one for the
negative (a semantically-identical, syntactically-different term reads as
"not admitted" here). This is the same limitation
QUANT-INSTANCE-PROBE's Count 1 named from the opposite side (7 of 53 cores'
z3 proofs reconstruct into a COMPLETE ground-only file; the rest do not,
"the gap is not random"). Treat every ADMITTED count here as a lower bound
and every MATCHED-REJECTED/NEVER-MATCHED count as correspondingly an upper
bound on the true ADMITTED count -- exactly the direction QUANT-INSTANCE-PROBE
recorded for its own PRESENT/ABSENT ground-membership check (ADR-2120 7d).

The MATCHED-REJECTED vs NEVER-MATCHED split for the 53-core histogram is
CORE-LEVEL, not per-quantifier: our instrumentation (`AXEYUM_QPROBE` +
`AXEYUM_QPROBE_CENSUS`) prints per-universal, per-round AGGREGATE counters
(`joined`, `admitted`, thirteen `rej_*` fields) -- never a per-substitution-
tuple log, because no such log exists in the shipped binary and this lane
writes no Rust. So: if the run's rejection census shows ANY nonzero `rej_*`
evidence at all (the census ran and something was rejected) and the
candidate's arguments are all present, it is counted MATCHED-REJECTED with
the core's DOMINANT rejection reason (summed over all universals) named as
"the reason" -- an attribution at the core level, not the exact tuple. The
three worked examples in the README go one level deeper: they attribute to
a SPECIFIC quantifier by re-deriving z3's and our own trigger choice.

# Skolem-collapse and canonicalization

`canon()` recursively: (a) rewrites any atom matching our internal Skolem
naming (`!qsk_N`, `!qskf_N`, `!qu_N`, `!q.?x_N` -- `quant_skolemize.rs:64-65`)
to the literal token `SKOLEM`, discarding the numeric identity (a real loss
of distinguishing power between two DIFFERENT Skolem constants in one term --
documented, not hidden: it can only ever turn a real ADMITTED mismatch into a
false one, never the reverse, because collapsing two different symbols to one
can only make two terms look MORE alike); (b) sorts the argument lists of
commutative operators (`+`, `*`, `=`, `distinct`, `and`, `or`) by their own
rendered text, so operand order (which neither z3 nor our own renderer
promises to agree on) does not cause a spurious mismatch.
"""

from __future__ import annotations

import collections
import importlib.util
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Optional

ROOT = Path(__file__).resolve().parents[2]
Z3PI_PATH = ROOT / "scripts" / "z3-proof-instances.py"


def _load_z3pi():
    spec = importlib.util.spec_from_file_location("z3_proof_instances", Z3PI_PATH)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


Z3PI = _load_z3pi()

SKOLEM_RE = re.compile(r"^!(qsk|qskf|qu|q\.\?x_)[A-Za-z0-9_.]*$")
COMMUTATIVE = {"+", "*", "=", "distinct", "and", "or"}
GROUND_ROW_RE = re.compile(r"^GROUND\s+(\d+)\s+gen=(\d+)\s+(.*)$")
UNIVERSAL_RE = re.compile(
    r"QPROBE\s+universal\[(\d+)\] vars=(\d+) patterns=(\d+) joined=(\d+) "
    r"starved_joins=(\d+) admitted=(\d+) (.*)$"
)
REJ_RE = re.compile(r"(rej_\w+)=(\d+)")
REJ_FIELDS = [
    "rej_handoff",
    "rej_poscap",
    "rej_nocontext",
    "rej_expired",
    "rej_subst",
    "rej_true",
    "rej_unreleased",
    "rej_flood",
    "rej_ceiling",
    "rej_check",
    "rej_seen",
    "rej_dupother",
    "rej_true_newterm",
]


def parse_term(text: str):
    """Parses ONE s-expression term (not a whole file) using z3pi's
    tokenizer/parser -- both already handle `|...|` quoting and `;` comments,
    and `parse()` returns the first complete top-level form, which is exactly
    one term here."""
    return Z3PI.parse(Z3PI.tokenize(text))


def canon(node):
    """Recursive canonical form: Skolem collapse + commutative-arg sort. See
    module docstring for the documented, one-directional loss of precision."""
    if isinstance(node, str):
        return "SKOLEM" if SKOLEM_RE.match(node) else node
    canon_children = [canon(x) for x in node]
    if canon_children and isinstance(canon_children[0], str) and canon_children[0] in COMMUTATIVE:
        head, args = canon_children[0], canon_children[1:]
        args = sorted(args, key=Z3PI.render)
        return [head] + args
    return canon_children


def canon_render(text: str) -> str:
    try:
        return Z3PI.render(canon(parse_term(text)))
    except Exception:
        # A term this tool's own small parser cannot round-trip (should not
        # happen on well-formed SMT-LIB output) is compared as raw text
        # rather than silently dropped -- it will simply never match, which
        # is the safe direction (see module docstring on lower/upper bounds).
        return text.strip()


# ---------------------------------------------------------------------------
# z3 side: re-run z3 with proofs, recover ground instance bodies + not_ground
# (nested) bodies + the raw (params, body) application pairs.
# ---------------------------------------------------------------------------


def z3_extract(core_path: Path, budget_s: int, taskset_cpus: Optional[str]) -> dict:
    """Runs z3 with `:produce-proofs`, returns z3pi's own `extract()` result
    (raw_count/bodies/not_ground/unmatched) PLUS the raw (params, body)
    application list this script needs for argument-presence checks --
    z3pi's public `extract()` keeps only the deduped bodies, so the params
    are recovered here by calling the same private machinery it uses
    (`find_quant_inst_applications`/`expand`/`instance_body`), not by
    duplicating its parsing rules."""
    query = core_path.read_text(encoding="utf-8", errors="replace")
    query = "(set-option :produce-proofs true)\n" + query + "\n(get-proof)\n"
    cmd = ["z3", f"-T:{budget_s}", "-smt2", "/dev/stdin"]
    if taskset_cpus:
        cmd = ["taskset", "-c", taskset_cpus] + cmd
    try:
        proc = subprocess.run(
            cmd, input=query, capture_output=True, text=True, timeout=budget_s + 20
        )
    except subprocess.TimeoutExpired:
        return {"verdict": "TIMEOUT", "applications": [], "extract": None}
    out = proc.stdout
    verdict = None
    for line in out.splitlines():
        line = line.strip()
        if line in ("sat", "unsat", "unknown", "timeout"):
            verdict = line
            break
    if verdict != "unsat":
        return {"verdict": verdict or "NOVERDICT", "applications": [], "extract": None}

    result = Z3PI.extract(out)

    start = out.find("(proof")
    if start < 0:
        start = out.find("(let ")
    applications: list = []
    if start >= 0:
        tokens = Z3PI.tokenize(out[start:])
        tree = Z3PI.parse(tokens)
        env: dict = {}
        Z3PI.collect_lets(tree, env)
        for params, formula in Z3PI.find_quant_inst_applications(tree):
            expanded_params = [Z3PI.render(Z3PI.expand(p, env)) for p in params]
            conclusion = Z3PI.expand(formula, env)
            body = Z3PI.instance_body(conclusion)
            if body is None:
                continue
            rendered = Z3PI.render(body)
            nested = bool(Z3PI.BOUND_VAR.search(rendered))
            applications.append(
                {"params": expanded_params, "body": rendered, "nested": nested}
            )

    return {"verdict": verdict, "applications": applications, "extract": result}


# ---------------------------------------------------------------------------
# our side: parse an AXEYUM_QGROUNDDUMP file + AXEYUM_QPROBE stderr trace.
# ---------------------------------------------------------------------------


def parse_last_ground_block(dump_text: str) -> list:
    """Returns `(index, gen, term_text)` rows from the LAST `GROUNDDUMP
    begin .. end` block only -- the final accumulated set, never an earlier
    give-up snapshot (same discipline as
    quant-instance-probe's `qip-dump-admitted.sh`)."""
    lines = dump_text.splitlines()
    last_begin = None
    for i, line in enumerate(lines):
        if line.startswith("GROUNDDUMP begin"):
            last_begin = i
    if last_begin is None:
        return []
    rows = []
    for line in lines[last_begin:]:
        m = GROUND_ROW_RE.match(line)
        if m:
            rows.append((int(m.group(1)), int(m.group(2)), m.group(3)))
        elif line.startswith("GROUNDDUMP end"):
            break
    return rows


def parse_universal_census(stderr_text: str) -> dict:
    """Returns `{index: {vars, patterns, joined, admitted, rej: {field:
    count}}}`, taking the LAST printed occurrence of each universal index --
    the counters are cumulative-at-print-time (`admitted_per_universal` is
    recomputed fresh from `matcher.ground_derivations` every round), so the
    last occurrence in the trace is the final state."""
    out: dict = {}
    for m in UNIVERSAL_RE.finditer(stderr_text):
        index = int(m.group(1))
        rej = {name: int(val) for name, val in REJ_RE.findall(m.group(7))}
        out[index] = {
            "vars": int(m.group(2)),
            "patterns": int(m.group(3)),
            "joined": int(m.group(4)),
            "starved_joins": int(m.group(5)),
            "admitted": int(m.group(6)),
            "rej": rej,
        }
    return out


def dominant_reason(rej: dict) -> tuple:
    """`(field, count)` for the largest nonzero `rej_*` field, or `(None, 0)`
    if every field is zero (the census did not run, or nothing was
    rejected)."""
    best = None
    best_n = 0
    for field in REJ_FIELDS:
        n = rej.get(field, 0)
        if n > best_n:
            best = field
            best_n = n
    return best, best_n


# ---------------------------------------------------------------------------
# classification
# ---------------------------------------------------------------------------

CLASS_ADMITTED = "ADMITTED"
CLASS_MATCHED_REJECTED = "MATCHED-REJECTED"
CLASS_NEVER_MATCHED = "NEVER-MATCHED"
CLASS_NESTED = "NESTED"


def classify_core(
    z3_applications: list,
    z3_not_ground: list,
    our_ground_rows: list,
    census: dict,
) -> list:
    """Pure classification function -- no I/O, no subprocess -- so it can be
    unit-tested directly on synthetic fixtures (see
    `scripts/tests/test_quant_reach_diff_classify.py`).

    `z3_applications`: list of `{params, body, nested}` (nested ones are
    passed through for completeness but should already be filtered by the
    caller into `z3_not_ground` -- kept as a defensive re-check here).
    `our_ground_rows`: `(index, gen, term_text)` from the LAST dump block.
    `census`: `parse_universal_census()` output.

    Returns one row per UNIQUE z3 ground ('not nested') ground ('not
    nested') body: `{body, params, class, reason, detail}`.
    """
    our_ground_any = {canon_render(t) for _, _, t in our_ground_rows}
    our_ground_admitted = {canon_render(t) for _, g, t in our_ground_rows if g >= 1}

    # Core-level dominant rejection reason: summed over every universal's
    # `rej_*` fields. Documented in the module docstring as a core-level,
    # not per-tuple, attribution.
    summed_rej: collections.Counter = collections.Counter()
    any_census = False
    for u in census.values():
        for field, n in u["rej"].items():
            summed_rej[field] += n
            if n > 0:
                any_census = True
    core_reason, core_reason_n = dominant_reason(summed_rej)

    # not_ground bodies as a set, for the "is the missing term itself a
    # nested-instance product" check below.
    not_ground_set = set(z3_not_ground)

    seen_bodies: set = set()
    rows: list = []
    for app in z3_applications:
        body = app["body"]
        if body in seen_bodies:
            continue
        seen_bodies.add(body)
        if app["nested"] or Z3PI.BOUND_VAR.search(body):
            rows.append(
                {
                    "body": body,
                    "params": app["params"],
                    "class": CLASS_NESTED,
                    "reason": "unresolved-outer-bound-var",
                    "detail": "",
                }
            )
            continue

        norm_body = canon_render(body)
        if norm_body in our_ground_admitted:
            rows.append(
                {
                    "body": body,
                    "params": app["params"],
                    "class": CLASS_ADMITTED,
                    "reason": "",
                    "detail": "",
                }
            )
            continue

        params_present = [
            (p, canon_render(p) in our_ground_any) for p in app["params"]
        ]
        all_present = all(present for _, present in params_present)

        if all_present and any_census and core_reason is not None:
            rows.append(
                {
                    "body": body,
                    "params": app["params"],
                    "class": CLASS_MATCHED_REJECTED,
                    "reason": core_reason,
                    "detail": f"core-dominant-rej={core_reason} n={core_reason_n}",
                }
            )
            continue

        if all_present:
            rows.append(
                {
                    "body": body,
                    "params": app["params"],
                    "class": CLASS_NEVER_MATCHED,
                    "reason": "trigger-did-not-fire",
                    "detail": "args present, no rejection evidence in run",
                }
            )
            continue

        missing = [p for p, present in params_present if not present]
        nested_product = any(
            any(m in ng for ng in not_ground_set) for m in missing
        )
        rows.append(
            {
                "body": body,
                "params": app["params"],
                "class": CLASS_NEVER_MATCHED,
                "reason": "missing-term",
                "detail": f"missing={missing!r} nested_product={nested_product}",
            }
        )

    for body in z3_not_ground:
        norm_body = canon_render(body)
        if norm_body in {r["body"] for r in rows}:
            continue
        rows.append(
            {
                "body": body,
                "params": [],
                "class": CLASS_NESTED,
                "reason": "unresolved-outer-bound-var",
                "detail": "",
            }
        )

    return rows


def main(argv: list) -> int:
    if len(argv) < 5:
        sys.stderr.write(
            "classify.py <core.smt2> <ours.dump> <ours.stderr> <out.tsv> "
            "[budget_s] [taskset_cpus]\n"
        )
        return 2
    core_path = Path(argv[1])
    dump_path = Path(argv[2])
    stderr_path = Path(argv[3])
    out_path = Path(argv[4])
    budget_s = int(argv[5]) if len(argv) > 5 else 24
    taskset_cpus = argv[6] if len(argv) > 6 else None

    z3_result = z3_extract(core_path, budget_s, taskset_cpus)
    if z3_result["verdict"] != "unsat" or z3_result["extract"] is None:
        out_path.write_text(f"NOVERDICT\t{z3_result['verdict']}\n")
        print(f"SKIP {core_path.name}: z3 verdict={z3_result['verdict']}")
        return 0

    dump_text = dump_path.read_text(encoding="utf-8", errors="replace") if dump_path.exists() else ""
    stderr_text = stderr_path.read_text(encoding="utf-8", errors="replace") if stderr_path.exists() else ""
    ground_rows = parse_last_ground_block(dump_text)
    census = parse_universal_census(stderr_text)

    rows = classify_core(
        z3_result["applications"], z3_result["extract"]["not_ground"], ground_rows, census
    )

    counts = collections.Counter(r["class"] for r in rows)
    with out_path.open("w", encoding="utf-8") as f:
        f.write("class\treason\tdetail\tbody\tparams\n")
        for r in rows:
            f.write(
                f"{r['class']}\t{r['reason']}\t{r['detail']}\t{r['body']}\t"
                f"{json.dumps(r['params'])}\n"
            )
    print(
        f"OK {core_path.name} z3_apps={len(rows)} "
        + " ".join(f"{k}={v}" for k, v in sorted(counts.items()))
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
