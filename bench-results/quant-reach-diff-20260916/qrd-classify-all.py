#!/usr/bin/env python3
"""QUANT-REACH-DIFF: drives `classify.py`'s functions across all 53 ADR-2113
cores, using the already-run `qrd-run-ours.sh` output (our side) and a fresh
z3 `:produce-proofs` run per core (z3 side, cheap -- median 108 ms per
ADR-2113/core-census.sh's own reference).

    qrd-classify-all.py <cores.list> <ours_outdir> <diff_outdir> <pin> [budget_s]

Writes one `<diff_outdir>/diff/<core>.tsv` per core (classify.py's own
per-row format) plus `<diff_outdir>/histogram.tsv` (per-core class counts,
denominator = unique non-nested z3 ground bodies + nested bodies) and
`<diff_outdir>/histogram-summary.tsv` (pooled over all 53).
"""

from __future__ import annotations

import collections
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("qrd_classify", HERE / "classify.py")
assert SPEC is not None and SPEC.loader is not None
classify = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = classify
SPEC.loader.exec_module(classify)


def main(argv: list) -> int:
    if len(argv) < 5:
        sys.stderr.write(
            "qrd-classify-all.py <cores.list> <ours_outdir> <diff_outdir> <pin> [budget_s]\n"
        )
        return 2
    cores_list = Path(argv[1])
    ours_dir = Path(argv[2])
    diff_dir = Path(argv[3])
    pin = argv[4]
    budget_s = int(argv[5]) if len(argv) > 5 else 30
    (diff_dir / "diff").mkdir(parents=True, exist_ok=True)

    per_core_counts: dict = {}
    pooled: collections.Counter = collections.Counter()
    reason_pooled: collections.Counter = collections.Counter()
    z3_denominators: dict = {}

    lines = [l.strip() for l in cores_list.read_text().splitlines() if l.strip()]
    for i, path_str in enumerate(lines, 1):
        core_path = Path(path_str)
        b = core_path.name
        print(f"CLASSIFY {i}/{len(lines)} {b}", file=sys.stderr)

        z3_result = classify.z3_extract(core_path, budget_s, pin)
        if z3_result["verdict"] != "unsat" or z3_result["extract"] is None:
            per_core_counts[b] = {"NOVERDICT": 1}
            print(f"  SKIP verdict={z3_result['verdict']}", file=sys.stderr)
            continue

        dump_path = ours_dir / "dump" / f"{b}.ground"
        stderr_path = ours_dir / "raw" / f"{b}.err"
        dump_text = dump_path.read_text(encoding="utf-8", errors="replace") if dump_path.exists() else ""
        stderr_text = stderr_path.read_text(encoding="utf-8", errors="replace") if stderr_path.exists() else ""
        ground_rows = classify.parse_last_ground_block(dump_text)
        census = classify.parse_universal_census(stderr_text)
        no_dump = len(ground_rows) == 0

        rows = classify.classify_core(
            z3_result["applications"], z3_result["extract"]["not_ground"], ground_rows, census
        )

        counts = collections.Counter(r["class"] for r in rows)
        per_core_counts[b] = dict(counts)
        per_core_counts[b]["_no_dump"] = no_dump
        per_core_counts[b]["_z3_raw"] = z3_result["extract"]["raw_count"]
        per_core_counts[b]["_z3_uniq"] = len(z3_result["extract"]["bodies"])
        per_core_counts[b]["_z3_not_ground"] = len(z3_result["extract"]["not_ground"])
        pooled.update(counts)
        z3_denominators[b] = len(rows)

        for r in rows:
            if r["reason"]:
                reason_pooled[(r["class"], r["reason"])] += 1

        with (diff_dir / "diff" / f"{b}.tsv").open("w", encoding="utf-8") as f:
            f.write("class\treason\tdetail\tbody\tparams\n")
            for r in rows:
                import json as _json

                f.write(
                    f"{r['class']}\t{r['reason']}\t{r['detail']}\t{r['body']}\t"
                    f"{_json.dumps(r['params'])}\n"
                )
        print(f"  {' '.join(f'{k}={v}' for k, v in sorted(counts.items()))}", file=sys.stderr)

    classes = [
        classify.CLASS_ADMITTED,
        classify.CLASS_MATCHED_REJECTED,
        classify.CLASS_NEVER_MATCHED,
        classify.CLASS_NESTED,
    ]
    with (diff_dir / "histogram.tsv").open("w", encoding="utf-8") as f:
        f.write("core\tz3_raw\tz3_uniq\tno_dump\t" + "\t".join(classes) + "\ttotal\n")
        for b, counts in per_core_counts.items():
            if "NOVERDICT" in counts:
                f.write(f"{b}\tNA\tNA\tNA\t" + "\t".join(["NA"] * len(classes)) + "\tNOVERDICT\n")
                continue
            total = sum(counts.get(c, 0) for c in classes)
            f.write(
                f"{b}\t{counts.get('_z3_raw', 0)}\t{counts.get('_z3_uniq', 0)}\t"
                f"{counts.get('_no_dump', False)}\t"
                + "\t".join(str(counts.get(c, 0)) for c in classes)
                + f"\t{total}\n"
            )

    with (diff_dir / "histogram-summary.tsv").open("w", encoding="utf-8") as f:
        f.write("class\tcount\n")
        for c in classes:
            f.write(f"{c}\t{pooled.get(c, 0)}\n")
        f.write(f"TOTAL\t{sum(pooled.get(c, 0) for c in classes)}\n")

    with (diff_dir / "reason-summary.tsv").open("w", encoding="utf-8") as f:
        f.write("class\treason\tcount\n")
        for (cls, reason), n in sorted(reason_pooled.items(), key=lambda kv: -kv[1]):
            f.write(f"{cls}\t{reason}\t{n}\n")

    print("CLASSIFY-ALL-DONE", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
