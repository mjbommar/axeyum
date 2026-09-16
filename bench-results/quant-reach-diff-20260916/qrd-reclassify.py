#!/usr/bin/env python3
"""QUANT-REACH-DIFF: re-run classification from ALREADY-COLLECTED data.

The first full run put every non-admitted/non-nested z3 instance in
NEVER-MATCHED/missing-term across all 53 cores (0 MATCHED-REJECTED, 0
trigger-did-not-fire) -- the signature of a BROKEN argument-presence check,
not a real finding (CLAUDE.md: "ask what it would print if it were broken").
The bug: presence was checked against TOP-LEVEL `GROUND` rows only, but
`AXEYUM_QGROUNDDUMP` records asserted FORMULAS, not every e-graph leaf, so a
bare declared symbol like `this` almost never appears as its OWN row even
though it is trivially present as a leaf of a larger term. Fixed in
`classify.py` (`flatten_subterms`): presence is now checked against every
SUBTERM of every dumped row, not row equality.

Re-running the z3 extraction (`z3_extract`, ~30 s budget x 53 cores) and the
solver sweep (`qrd-run-ours.sh`, ~15 min) is NOT needed to apply the fix: the
already-written `diff/<core>.tsv` files already carry every application's
`(class, reason, detail, body, params)` from the FIRST run, which itself
carried the complete `(params, body, nested)` triple per application (nested
rows too, via `app["nested"]`/the not_ground pass -- both produce
class=NESTED and both are already present as rows). So this script
reconstructs each core's `z3_applications` list directly from its existing
`diff/<core>.tsv` (one row per unique body, already deduped) and re-runs
ONLY `classify_core` against the unchanged, already-on-disk
`runs-ours/dump/*.ground` + `runs-ours/raw/*.err`.

    qrd-reclassify.py <cores.list> <ours_outdir> <diff_outdir>
"""

from __future__ import annotations

import collections
import importlib.util
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location("qrd_classify", HERE / "classify.py")
assert SPEC is not None and SPEC.loader is not None
classify = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = classify
SPEC.loader.exec_module(classify)


def load_prior_diff(path: Path) -> tuple[list, list]:
    """Reconstructs `(applications, not_ground)` from a first-run diff TSV.
    Every row already carries body+params; NESTED rows become
    applications with `nested=True` (equivalent to the original run, which
    reached NESTED via either the application's own flag or the separate
    not_ground pass -- both produced identical rows)."""
    applications = []
    if not path.exists():
        return applications, []
    lines = path.read_text(encoding="utf-8").splitlines()
    for line in lines[1:]:
        if not line.strip():
            continue
        parts = line.split("\t", 4)
        if len(parts) < 5:
            continue
        cls, _reason, _detail, body, params_json = parts
        try:
            params = json.loads(params_json)
        except Exception:
            params = []
        applications.append(
            {"params": params, "body": body, "nested": cls == classify.CLASS_NESTED}
        )
    return applications, []


def main(argv: list) -> int:
    if len(argv) < 4:
        sys.stderr.write("qrd-reclassify.py <cores.list> <ours_outdir> <diff_outdir>\n")
        return 2
    cores_list = Path(argv[1])
    ours_dir = Path(argv[2])
    diff_dir = Path(argv[3])
    (diff_dir / "diff").mkdir(parents=True, exist_ok=True)

    per_core_counts: dict = {}
    pooled: collections.Counter = collections.Counter()
    reason_pooled: collections.Counter = collections.Counter()

    lines = [l.strip() for l in cores_list.read_text().splitlines() if l.strip()]
    for i, path_str in enumerate(lines, 1):
        core_path = Path(path_str)
        b = core_path.name
        prior_tsv = diff_dir / "diff" / f"{b}.tsv"
        applications, not_ground = load_prior_diff(prior_tsv)
        if not applications and not prior_tsv.exists():
            per_core_counts[b] = {"NOVERDICT": 1}
            print(f"SKIP {i}/{len(lines)} {b} (no prior diff)", file=sys.stderr)
            continue

        dump_path = ours_dir / "dump" / f"{b}.ground"
        stderr_path = ours_dir / "raw" / f"{b}.err"
        dump_text = dump_path.read_text(encoding="utf-8", errors="replace") if dump_path.exists() else ""
        stderr_text = stderr_path.read_text(encoding="utf-8", errors="replace") if stderr_path.exists() else ""
        ground_rows = classify.parse_last_ground_block(dump_text)
        census = classify.parse_universal_census(stderr_text)
        no_dump = len(ground_rows) == 0

        rows = classify.classify_core(applications, not_ground, ground_rows, census)

        counts = collections.Counter(r["class"] for r in rows)
        per_core_counts[b] = dict(counts)
        per_core_counts[b]["_no_dump"] = no_dump
        per_core_counts[b]["_z3_uniq"] = len(applications)
        pooled.update(counts)

        for r in rows:
            if r["reason"]:
                reason_pooled[(r["class"], r["reason"])] += 1

        with (diff_dir / "diff" / f"{b}.tsv").open("w", encoding="utf-8") as f:
            f.write("class\treason\tdetail\tbody\tparams\n")
            for r in rows:
                f.write(
                    f"{r['class']}\t{r['reason']}\t{r['detail']}\t{r['body']}\t"
                    f"{json.dumps(r['params'])}\n"
                )
        print(
            f"RECLASSIFY {i}/{len(lines)} {b} "
            + " ".join(f"{k}={v}" for k, v in sorted(counts.items())),
            file=sys.stderr,
        )

    classes = [
        classify.CLASS_ADMITTED,
        classify.CLASS_MATCHED_REJECTED,
        classify.CLASS_NEVER_MATCHED,
        classify.CLASS_NESTED,
    ]
    with (diff_dir / "histogram.tsv").open("w", encoding="utf-8") as f:
        f.write("core\tz3_uniq\tno_dump\t" + "\t".join(classes) + "\ttotal\n")
        for b, counts in per_core_counts.items():
            if "NOVERDICT" in counts:
                f.write(f"{b}\tNA\tNA\t" + "\t".join(["NA"] * len(classes)) + "\tNOVERDICT\n")
                continue
            total = sum(counts.get(c, 0) for c in classes)
            f.write(
                f"{b}\t{counts.get('_z3_uniq', 0)}\t{counts.get('_no_dump', False)}\t"
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

    print("RECLASSIFY-ALL-DONE", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
