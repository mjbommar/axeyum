"""Reduce a census TSV's `qtrace` column to ONE stage's segments, in place.

`census-run.sh` records the whole `AXEYUM_QTRACE` trail per file. That trail is
what let this lane attribute the census's largest family to a named rung, and on
these divisions it is also almost all of the artifact's bytes: one `AUFLIA` file
emits a rung trail over 128 KiB long, and the three full-200 census files come
to 5.8 MB against 448-716 KB for the comparable committed boards.

So the committed full-200 files keep only the stage the published numbers are
derived from. `route-hit-rate.py` reads exactly two things out of this column --
whether `<stage>@` occurs at all, and that stage's own exit notes -- and both
survive verbatim. The per-file route attribution in the README does not come
from here at all; it comes from the dedicated `decided_by` / `bound_by` /
`bound_ms` / `total_ms` columns, which are untouched.

What is lost is the other stages' segments. Re-run `census-run.sh` to get them
back; this is a projection of a measurement, not the measurement.

Usage: python3 compact-qtrace.py <stage> <census.tsv> [<census.tsv> ...]
"""

import pathlib
import sys


def keep_stage(cell: str, stage: str) -> str:
    if cell in ("na", ""):
        return cell
    kept = [seg for seg in cell.split(";") if seg.startswith(f"{stage}@")]
    dropped = len(cell.split(";")) - len(kept)
    if dropped:
        kept.append(f"(+{dropped} segments of other stages dropped)")
    return ";".join(kept) if kept else "na"


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print("usage: compact-qtrace.py <stage> <census.tsv> ...", file=sys.stderr)
        return 2
    stage = argv[1]
    for path in argv[2:]:
        p = pathlib.Path(path)
        text = p.read_text()
        lines = text.rstrip("\n").split("\n")
        head = lines[0].split("\t")
        if "qtrace" not in head:
            print(f"ABORT: {p} has no qtrace column")
            return 3
        i = head.index("qtrace")
        out = [lines[0]]
        hits = 0
        for ln in lines[1:]:
            f = ln.split("\t")
            if len(f) > i:
                f[i] = keep_stage(f[i], stage)
                if f"{stage}@" in f[i]:
                    hits += 1
            out.append("\t".join(f))
        new = "\n".join(out) + "\n"
        p.write_text(new)
        print(f"COMPACT-OK {p.name}: {len(text)} -> {len(new)} bytes"
              f" ({len(new) / len(text):.1%}), {len(out) - 1} rows,"
              f" `{stage}@` still present on {hits}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
