#!/usr/bin/env python3
"""Rebuild bench-results/quant-instance-probe-20260916/dumpadmit/dump-summary.tsv
from the untouched inst/*.lastblock files (the actual dump captures, unaffected
by the bug this repairs). The original writer used
`grep -c PATTERN file || echo 0`, and `grep -c` EXITS 1 (not 0) when the count
is zero even though it still PRINTS "0" -- so on a file with no GROUND lines
that line printed "0" from grep AND "0" from the `|| echo 0` fallback, splitting
one logical TSV row across two physical lines. `wc -l` (always exit 0) does not
have this problem, which is why `admitted` in the same script was never
affected -- only `rows`.

    qip-repair-dump-summary.py <cores.list> <dumpdir>

Overwrites <dumpdir>/dump-summary.tsv with a corrected version, preserving the
core/verdict/run_rc columns already correct in `dumpadmit/*.out` and only
recomputing `dump_rows`/`admitted_rows` from the lastblock files directly.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path

GROUND_RE = re.compile(r"^GROUND\s+\d+\s+gen=(\d+)\s")


def main(argv: list) -> int:
    if len(argv) != 3:
        sys.stderr.write(__doc__ or "")
        return 2
    cores_list, dumpdir = Path(argv[1]), Path(argv[2])
    cores = [l.strip() for l in cores_list.read_text().splitlines() if l.strip()]

    out = ["core\trun_rc\tverdict\tdump_rows\tadmitted_rows"]
    for p in cores:
        b = Path(p).name
        out_file = dumpdir / "dump" / f"{b}.out"
        lastblock = dumpdir / "inst" / f"{b}.lastblock"
        verdict = "NOVERDICT"
        if out_file.exists():
            for line in out_file.read_text(encoding="utf-8", errors="replace").splitlines():
                if line in ("sat", "unsat", "unknown"):
                    verdict = line
                    break
        rows = 0
        admitted = 0
        if lastblock.exists():
            text = lastblock.read_text(encoding="utf-8", errors="replace")
            for line in text.splitlines():
                m = GROUND_RE.match(line)
                if m:
                    rows += 1
                    if int(m.group(1)) >= 1:
                        admitted += 1
        out.append(f"{b}\t0\t{verdict}\t{rows}\t{admitted}")

    (dumpdir / "dump-summary.tsv").write_text("\n".join(out) + "\n", encoding="utf-8")
    print(f"repaired {len(cores)} rows")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
