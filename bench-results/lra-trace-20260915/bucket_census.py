#!/usr/bin/env python3
"""Bucket the `QF_LRA` undecided rows by TERMINAL TYPED REASON, over four channels.

# Why four channels and not the give-up string

[ADR-2045] measured that a census built on the `; give-up kind=… detail=…` line
alone loses its own largest bucket outright: the rows that die in an allocation
print **nothing** on stdout -- no verdict, no give-up line, no route trail --
and announce themselves only as `rc=134` plus one line on stderr.  Counting the
give-up strings would therefore have reported the population as smaller than it
is and the surviving buckets as larger shares of it than they are.

So every row is classified from whichever channel actually answered, and the
channel is recorded in its own column (`channel`) rather than inferred:

    trail    the route trail's binding attempt carried a typed decline
    giveup   no trail, but the CLI printed a give-up line
    abort    rc=134 and stderr names an allocation failure
    killed   rc=124 (the outer `timeout` fired past the solver's own deadline)
    silent   none of the above -- reported as its own bucket, never folded in

# Why the trail and not the prose

`scripts/route_trace_reader.py` is the repository's ONE reader for the trail
JSON (ADR-2101), and this module uses it as a library rather than re-parsing.
Three separate ADRs record what re-parsing the prose costs.

# What the row carries besides the bucket

The two probes `trace-census.sh` arms print to stderr and are read here:
`AXEYUM_LRADENSEPROBE` (the offline dense route's shape at four points) and
`AXEYUM_LRAMODELPROBE` (WHICH of the five ways online model reconstruction
failed).  The `; theory-layer` counter line is parsed for the online engine's
own numbers.  Those columns are `n/a` when the row never reached that engine --
never `0`, because a counter the engine did not keep must not read as a
measured zero.

Usage:  bucket_census.py <captures-dir>... --census <census.tsv>... [--shapes <shapes.tsv>]
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))

import route_trace_reader as rtr  # noqa: E402

ALLOC_RE = re.compile(r"memory allocation of (\d+) bytes failed|out of memory|Cannot allocate")
PANIC_RE = re.compile(r"thread '[^']*' panicked at ([^\n]*)")
MODELPROBE_RE = re.compile(r"; LRAMODELPROBE site=(\S+)")
DENSEPROBE_RE = re.compile(r"; LRADENSEPROBE (\S+) (.*)")
GIVEUP_RE = re.compile(r"^; give-up kind=(\S+) detail=(.*)$", re.M)
LAYER_RE = re.compile(r"^; theory-layer (.*)$", re.M)
ROUTE_RE = re.compile(r"^; (?:partial )?route .*?bound_by=(\S+)", re.M)

# The counters worth carrying per row.  Deliberately a short list: a 40-column
# table nobody reads is not a measurement, and everything omitted is still in
# the capture beside it.
LAYER_KEYS = [
    "decisions",
    "theory_conflicts",
    "theory_propagations",
    "bound_scan_calls",
    "bound_scan_atoms",
    "simplex_pivots",
    "simplex_rows",
    "simplex_columns",
    "final_check_core_literals",
    "theory_propagate_ms",
    "theory_final_check_ms",
    "boolean_propagate_ms",
    "fill_nnz_sum",
    "fill_samples",
]

COLUMNS = [
    "file",
    "rc",
    "verdict",
    "channel",
    "bucket",
    "detail",
    "bound_by",
    "modelprobe",
    "alloc_bytes",
    *LAYER_KEYS,
]


def parse_layer(text: str) -> dict[str, str]:
    m = LAYER_RE.search(text)
    if not m:
        return {}
    out: dict[str, str] = {}
    for tok in m.group(1).split():
        if "=" in tok:
            k, v = tok.split("=", 1)
            out[k] = v
    return out


def classify(out_text: str, err_text: str, rc: str) -> tuple[str, str, str]:
    """Return `(channel, bucket, detail)`.

    Order matters and is the point: the abort test comes FIRST, because an
    aborting row can still have printed a trail line for an earlier route and
    classifying it by that line would attribute the death to the wrong engine.
    """
    alloc = ALLOC_RE.search(err_text)
    panic = PANIC_RE.search(err_text)
    if rc == "134" or alloc or panic:
        if alloc:
            return ("abort", "alloc-failure", alloc.group(0))
        if panic:
            return ("abort", "panic", panic.group(1)[:120])
        return ("abort", "abort-no-message", "")
    if rc == "124":
        return ("killed", "outer-timeout", "outer `timeout` fired past the solver deadline")

    # The trail's own binding attempt, read through the ONE reader.
    for line in out_text.splitlines():
        if "route-trail" not in line:
            continue
        try:
            trail = rtr.parse_trail_line(line)
        except rtr.RouteTraceError:
            break
        bound = trail.bound_by
        if bound:
            # The bucket is the TYPED pair the producer emitted (`reason` plus
            # ADR-2104's `name`, or `kind` on an `incomplete`), never the prose
            # `detail`.  ADR-2045 measured one `detail` string standing for six
            # program points and four different kinds of event; bucketing on it
            # is how that census reported "ran out of time" for an `i128`
            # overflow.  The prose still travels, in its own column.
            for a in trail.attempts:
                if a.route == bound and a.declined:
                    typed = a.name or a.kind or "unnamed"
                    return (
                        "trail",
                        f"{a.reason or 'unknown'}/{typed}",
                        a.detail or "",
                    )
            return ("trail", "bound-no-decline", bound)
        break

    g = GIVEUP_RE.search(out_text)
    if g:
        return ("giveup", f"give-up/{g.group(1)}", g.group(2)[:160])
    return ("silent", "no-channel-answered", "")


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=(__doc__ or "").splitlines()[0])
    ap.add_argument("captures", nargs="+", help="captures-* directories")
    ap.add_argument("--census", nargs="+", required=True, help="census.*.tsv files")
    ap.add_argument("--out", help="write the per-row TSV here (default: stdout)")
    ap.add_argument("--summary", action="store_true", help="also print the bucket table")
    args = ap.parse_args(argv[1:])

    rows: list[dict[str, str]] = []
    for c in args.census:
        lines = Path(c).read_text().splitlines()
        head = lines[0].split("\t")
        for ln in lines[1:]:
            if ln:
                rows.append(dict(zip(head, ln.split("\t"), strict=True)))

    dirs = [Path(d) for d in args.captures]
    out_rows: list[list[str]] = []
    unresolved = 0
    for r in rows:
        slug = r["file"].replace("/", "_")
        out_text = err_text = ""
        found = False
        for d in dirs:
            o, e = d / f"{slug}.out", d / f"{slug}.err"
            if o.exists():
                out_text = o.read_text(errors="replace")
                err_text = e.read_text(errors="replace") if e.exists() else ""
                found = True
                break
        if not found:
            unresolved += 1
            sys.stderr.write(f"NO CAPTURE\t{r['file']}\n")
            continue
        channel, bucket, detail = classify(out_text, err_text, r["rc"])
        layer = parse_layer(out_text)
        probes = MODELPROBE_RE.findall(err_text)
        bm = ROUTE_RE.search(out_text)
        alloc = ALLOC_RE.search(err_text)
        row = {
            "file": r["file"],
            "rc": r["rc"],
            "verdict": r["verdict"],
            "channel": channel,
            "bucket": bucket,
            "detail": detail.replace("\t", " ")[:200],
            "bound_by": bm.group(1) if bm else "n/a",
            "modelprobe": "|".join(dict.fromkeys(probes)) if probes else "n/a",
            "alloc_bytes": alloc.group(1) if (alloc and alloc.group(1)) else "n/a",
        }
        # `n/a`, never `0`: the online engine did not run on an aborting row and
        # a zero here would read as "it ran and did nothing".
        for k in LAYER_KEYS:
            row[k] = layer.get(k, "n/a")
        out_rows.append([row[c] for c in COLUMNS])

    sink = open(args.out, "w") if args.out else sys.stdout
    try:
        print("\t".join(COLUMNS), file=sink)
        for row in out_rows:
            print("\t".join(row), file=sink)
    finally:
        if args.out:
            sink.close()

    if args.summary:
        buckets: dict[tuple[str, str], int] = {}
        for row in out_rows:
            key = (row[3], row[4])
            buckets[key] = buckets.get(key, 0) + 1
        print(f"\nrows classified: {len(out_rows)}   no capture: {unresolved}", file=sys.stderr)
        print(f"{'channel':<10}{'bucket':<46}{'n':>5}", file=sys.stderr)
        print("-" * 61, file=sys.stderr)
        for (ch, bk), n in sorted(buckets.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"{ch:<10}{bk:<46}{n:>5}", file=sys.stderr)
    return 1 if unresolved else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
