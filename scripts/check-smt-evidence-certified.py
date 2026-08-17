#!/usr/bin/env python3
"""Require that every settled SMT-route fact rests on a CERTIFIED refutation.

CLAUDE.md's standing warning is that "a checker that cannot fail is worse than
no checker", and the audited instance was 40 of 162 runs exiting 0 on completion
alone. This is the same disease one level in, and it survived that audit because
the exit status *does* depend on a finding — just not on the finding that
matters.

Every SMT-route fact in the ledger attaches evidence shaped like:

    test "$(... smtcomp_cli -- --evidence <instance>.smt2 | tail -1)" = unsat

That tests the **verdict**. It does not test whether the refutation was
*certified*, and the harness reports those separately. Measured 2026-08-17:

    17 of 17 settled smt-term-level / smt-clausal instances -> certified=1
        14 kind=unsat-term-level
         2 kind=unsat-drat
         1 kind=unsat-bool-simplification

So the invariant holds today — by practice, not by enforcement. Nothing stops
the eighteenth from being uncertified, and the evidence command would not
notice. Demonstrated on `artifacts/facts/smt2/neg-barber-no-such-barber.smt2`,
a genuinely unsatisfiable instance the solver refutes but cannot certify: the
command shape above **exits 0** on it, reporting `kind=unsat-uncertified
certified=0`.

That file is therefore this check's negative control, and it is a real one
rather than a synthetic fixture — see `probe()` below.

Reported, never inferred: certification is read from the harness's own
`; evidence` line per instance. An instance that prints no such line is a
failure, not a pass, because "could not tell" must never read as "certified".
"""

from __future__ import annotations

import json
import os
import pathlib
import re
import subprocess
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"

SETTLED = {"proved", "computed"}
SMT_ROUTES = {"smt-term-level", "smt-clausal"}
INSTANCE_RE = re.compile(r"artifacts/facts/smt2/[\w.\-]+\.smt2")
EVIDENCE_RE = re.compile(r"^;\s*evidence\s+kind=(\S+)\s+certified=(\S+)", re.M)

# A floor, so an extractor that stops finding instances cannot report a healthy
# zero -- 0 uncertified of 0 is a perfect score. Measured 17 on 2026-08-17.
MIN_INSTANCES = 15

# The negative control: genuinely unsat, NOT certified. See probe().
#
# It is the instance behind `F:barber-no-such-barber`, which stays `open`
# precisely because an uncertified unsat is not evidence under this schema. That
# makes it a real control rather than a synthetic one, and it is NOT swept as a
# settled instance -- the fact is open, so `instances()` does not select it.
PROBE = "artifacts/facts/smt2/neg-barber-no-such-barber.smt2"


_CLI: list[str] | None = None


def cli() -> list[str]:
    """The evidence harness, built once rather than per instance, in RELEASE.

    `cargo run` per instance would pay cargo's startup on all ~18 of them for no
    benefit, so it is built once here. Release is not a preference: measured
    2026-08-17, a debug binary spends **233 seconds** on this sweep and 232 of
    them are the two DRAT-certified fp16 instances (the other 16 are ~0s), which
    is DRAT checking in an unoptimised build. Release brings the same sweep to
    **16 seconds** warm. The fp16 facts' own evidence commands already say
    `cargo run --release`, so this also matches what the ledger claims was run
    rather than checking those instances a slower way.

    `AXEYUM_SMTCOMP_CLI` overrides for a caller that already has a binary.
    """
    global _CLI
    if _CLI is not None:
        return _CLI
    override = os.environ.get("AXEYUM_SMTCOMP_CLI")
    if override:
        _CLI = [override]
        return _CLI
    subprocess.run(
        ["cargo", "build", "--release", "-q", "-p", "axeyum-bench", "--example", "smtcomp_cli"],
        cwd=ROOT,
        check=True,
    )
    target = pathlib.Path(os.environ.get("CARGO_TARGET_DIR") or (ROOT / "target"))
    binary = target / "release/examples/smtcomp_cli"
    _CLI = (
        [str(binary)]
        if binary.exists()
        else [
            "cargo", "run", "--release", "-q",
            "-p", "axeyum-bench", "--example", "smtcomp_cli", "--",
        ]
    )
    return _CLI


def run(instance: str) -> dict[str, Any]:
    """Verdict and certification for one instance, as the harness reports them."""
    proc = subprocess.run(
        [*cli(), "--evidence", instance],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=900,
    )
    lines = [ln for ln in proc.stdout.splitlines() if ln.strip()]
    verdict = lines[-1].strip() if lines else ""
    match = EVIDENCE_RE.search(proc.stdout)
    return {
        "path": instance,
        "verdict": verdict,
        # None -- not 0 -- when the line is absent, so "could not tell" is
        # distinguishable from "told us it was uncertified".
        "kind": match.group(1) if match else None,
        "certified": match.group(2) if match else None,
    }


def instances() -> list[tuple[str, str]]:
    """(fact id, instance path) for every settled SMT-route fact."""
    out: list[tuple[str, str]] = []
    seen: set[str] = set()
    for path in sorted(FACTS.glob("*.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        if data.get("epistemic_status") not in SETTLED:
            continue
        if data.get("proof_route") not in SMT_ROUTES:
            continue
        for item in data.get("evidence") or []:
            for found in INSTANCE_RE.findall(item.get("checker_command", "")):
                if found not in seen:
                    seen.add(found)
                    out.append((data["id"], found))
    return out


def evaluate(rows: list[dict[str, Any]], probe: dict[str, Any] | None) -> list[str]:
    """Failures. Each guard here is driven independently by the unit tests."""
    failures: list[str] = []

    if len(rows) < MIN_INSTANCES:
        failures.append(
            f"only {len(rows)} settled SMT-route instances found (floor "
            f"{MIN_INSTANCES}); the extractor is looking at the wrong tree or has "
            "stopped matching, and 0 uncertified of 0 would read as health"
        )
        return failures

    for row in rows:
        if row["verdict"] != "unsat":
            failures.append(
                f"{row['path']}: verdict {row['verdict']!r}, expected unsat -- a "
                "settled fact's instance must still be refuted"
            )
        if row["certified"] is None:
            failures.append(
                f"{row['path']}: the harness printed no `; evidence` line, so "
                "certification could not be read. That is a failure, not a pass: "
                "'could not tell' must never be recorded as 'certified'"
            )
        elif row["certified"] != "1":
            failures.append(
                f"{row['path']}: kind={row['kind']} certified={row['certified']} -- "
                "this fact is settled on an UNCERTIFIED refutation. The verdict is "
                "probably right, but the ledger's claim is that unsat carries a "
                "checkable object, and this one does not"
            )

    failures.extend(probe_failures(probe))
    return failures


def probe_failures(probe: dict[str, Any] | None) -> list[str]:
    """The negative control, and the one guard whose failure is good news.

    A check that only ever confirms `certified=1` cannot show it would notice
    `certified=0`. `neg-barber.smt2` is the discriminating case: really
    unsatisfiable, so a verdict-only checker passes it, and really uncertified,
    so this one must be able to see the difference.
    """
    if probe is None:
        return [
            f"the negative control {PROBE} is missing, so this check has no "
            "evidence it can distinguish a certified refutation from an "
            "uncertified one -- restore it before trusting a green run"
        ]
    if probe["verdict"] != "unsat":
        return [
            f"{PROBE}: verdict {probe['verdict']!r}, expected unsat. The control "
            "only discriminates while it is genuinely refuted; if the solver has "
            "stopped deciding it, this check is no longer calibrated"
        ]
    if probe["certified"] == "1":
        return [
            f"{PROBE} now reports kind={probe['kind']} certified=1. This is GOOD "
            "NEWS and an action, not a defect: the barber sentence has become "
            "certifiable, so F:barber-no-such-barber can be closed on the SMT "
            "route with certified evidence. Do that, then repoint this control at "
            "another uncertified instance -- it must not be left pointing at a "
            "case that no longer discriminates"
        ]
    return []


def main(argv: list[str]) -> int:
    found = instances()
    rows = [run(path) | {"fact": fact} for fact, path in found]
    probe = run(PROBE) if (ROOT / PROBE).exists() else None

    if "--quiet" not in argv:
        for row in rows:
            print(f"  {row['certified']} {row['kind']:<28} {row['path']}")
        if probe:
            print(f"  control: certified={probe['certified']} kind={probe['kind']}")

    certified = sum(1 for r in rows if r["certified"] == "1")
    failures = evaluate(rows, probe)
    print(f"SMT_EVIDENCE|instances={len(rows)}|certified={certified}")
    for failure in failures:
        print(f"SMT_EVIDENCE_ERROR|{failure}", file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
