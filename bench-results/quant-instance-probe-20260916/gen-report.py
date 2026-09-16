#!/usr/bin/env python3
"""Join every stage of the QUANT-INSTANCE-PROBE pipeline into one table:

    gen-report.py <probe_dir> <ledger_dir> [--out FILE]

Reads (relative to <probe_dir>):
  extract/extract-summary.tsv      z3 proof extraction, per core
  ground/build-summary.tsv         z3-instance ground-only file build + z3 check
  dumpadmit/dump-summary.tsv       our own admitted-instance dump, per core
  admitground/build-summary.tsv    admitted-instance ground-only file build

Reads from <ledger_dir>/quant-instance-probe.tsv (the ADR-2102 outcome
ledger) for arms `z3-instances` and `admitted-instances`, via
`outcome_ledger.py`/`route_trace_reader.py` -- never by re-parsing captured
stdout with a grep, which is exactly the mistake `route_trace_reader.py`'s
own docstring catalogs three ADRs' worth of.

Prints a markdown table to stdout (or --out) and the two headline counts on
stderr.
"""

from __future__ import annotations

import csv
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve()
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

_spec = importlib.util.spec_from_file_location(
    "outcome_ledger", ROOT / "scripts" / "outcome_ledger.py"
)
assert _spec is not None and _spec.loader is not None
ol = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(ol)


def read_tsv(path: Path) -> dict[str, dict]:
    if not path.exists():
        return {}
    out = {}
    with open(path, encoding="utf-8") as fh:
        for row in csv.DictReader(fh, delimiter="\t"):
            out[row["core"]] = row
    return out


def ledger_rows(ledger_dir: Path, sweep_id: str, arm: str) -> dict[str, "ol.LedgerRow"]:
    try:
        rows, _flagged = ol.load(sweep_id, ledger_dir=str(ledger_dir), allow_branch=True)
    except ol.LedgerError as exc:
        print(f"LEDGER-LOAD-FAILED: {exc}", file=sys.stderr)
        return {}
    out = {}
    for r in rows:
        if r.arm != arm:
            continue
        # corpus_path is "<core>.ground.smt2"
        core = r.corpus_path
        if core.endswith(".ground.smt2"):
            core = core[: -len(".ground.smt2")]
        out[core] = r
    return out


def main(argv: list) -> int:
    if len(argv) < 3:
        sys.stderr.write(__doc__ or "")
        return 2
    probe_dir = Path(argv[1])
    ledger_dir = Path(argv[2])
    out_path = None
    if "--out" in argv:
        out_path = Path(argv[argv.index("--out") + 1])

    extract = read_tsv(probe_dir / "extract" / "extract-summary.tsv")
    build_z3 = read_tsv(probe_dir / "ground" / "build-summary.tsv")
    dumpadmit = read_tsv(probe_dir / "dumpadmit" / "dump-summary.tsv")
    build_admit = read_tsv(probe_dir / "admitground" / "build-summary.tsv")

    ledger_z3 = ledger_rows(ledger_dir, "quant-instance-probe", "z3-instances")
    ledger_admit = ledger_rows(ledger_dir, "quant-instance-probe", "admitted-instances")

    cores = sorted(extract.keys())

    lines = []
    lines.append(
        "| core | z3 raw/uniq/unmatch | ground-only build | z3-ground | ours(z3-inst) v/decided_by/ms | admitted rows | ours(admitted) v/decided_by/ms |"
    )
    lines.append("|---|---:|---|---|---|---:|---|")

    n_z3_complete = 0
    n_ours_z3_correct = 0
    n_admit_unsat = 0
    n_admit_decided = 0

    for c in cores:
        e = extract.get(c, {})
        bz = build_z3.get(c, {})
        da = dumpadmit.get(c, {})
        ba = build_admit.get(c, {})
        lz = ledger_z3.get(c)
        la = ledger_admit.get(c)

        z3g = bz.get("z3_ground_verdict", "NA")
        if z3g == "unsat":
            n_z3_complete += 1

        def fmt(row):
            if row is None:
                return "NA"
            return f"{row.verdict}/{row.decided_by}/{row.elapsed_ms}ms"

        if z3g == "unsat" and lz is not None and lz.verdict == "unsat":
            n_ours_z3_correct += 1

        if la is not None:
            n_admit_decided += 1
            if la.verdict == "unsat":
                n_admit_unsat += 1

        lines.append(
            "| {c} | {raw}/{uniq}/{unm} | {bz} | {z3g} | {lz} | {admrows} | {la} |".format(
                c=c[:56],
                raw=e.get("raw_count", "NA"),
                uniq=e.get("unique_bodies", "NA"),
                unm=e.get("unmatched", "NA"),
                bz=bz.get("build_rc", "NA"),
                z3g=z3g,
                lz=fmt(lz),
                admrows=da.get("admitted_rows", "NA"),
                la=fmt(la),
            )
        )

    table = "\n".join(lines)
    if out_path:
        out_path.write_text(table + "\n", encoding="utf-8")
    else:
        print(table)

    print(f"HEADLINE z3-ground-only complete (z3-confirmed unsat): {n_z3_complete} of {len(cores)}", file=sys.stderr)
    print(f"HEADLINE ours refutes z3's own minimal instance set: {n_ours_z3_correct} of {n_z3_complete}", file=sys.stderr)
    print(f"HEADLINE ours on OUR OWN admitted instance set: {n_admit_unsat} unsat of {n_admit_decided} decided ({len(cores)} attempted)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
