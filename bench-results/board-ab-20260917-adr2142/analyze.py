#!/usr/bin/env python3
"""Analyse the ADR-2142 board A/B exactly as the 09-15 board did, plus wall time.

Derived from bench-results/route-ownership-20260915/ab-summarize.py (same
nine-column row format: file, A, A_ms, A_rc, B, B_ms, B_rc, first, status).
Each channel is reported separately:

- verdict: decided A/B, net, gains, losses, sat<->unsat FLIPS (a flip is a
  finding to report first: the ADR claims byte-identical trajectories);
- exit status: rows where the two arms' exit statuses differ;
- soundness: every decided verdict of BOTH arms against the file's declared
  `:status`, comparable denominator published beside the disagreement count;
- wall time on both-decided rows: sum and median per arm, and the count of
  rows where B's wall < 0.5 x A's (the fix mattered) vs within noise
  (|log ratio| <= log 1.25) vs B slower than 2x A;
- malformed rows: counted and listed, never scored as unchanged.

Usage: analyze.py [--board-tsv out.tsv] [--movers out.txt] <shard.tsv>...
Rows may hold absolute corpus paths; the corpus prefix is stripped.
"""

import argparse
import math
import statistics
import sys
from collections import defaultdict

DECIDED = {"sat", "unsat"}
CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental/"
DIVS = (
    "QF_ABV QF_BV QF_DT QF_FP QF_IDL QF_LIA QF_LRA QF_NIA "
    "QF_NRA QF_RDL QF_S QF_SLIA QF_UF QF_UFLIA QF_UFLRA UF"
).split()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--board-tsv")
    ap.add_argument("--movers")
    ap.add_argument("tsv", nargs="+")
    args = ap.parse_args()

    rows = defaultdict(list)
    malformed = []
    total_rows = 0
    for path in args.tsv:
        for line in open(path):
            cells = line.rstrip("\n").split("\t")
            if cells[0] == "file":
                continue
            if len(cells) != 9:
                malformed.append((path, line.rstrip("\n")[:120]))
                continue
            cells[0] = cells[0].removeprefix(CORPUS)
            rows[cells[0].split("/", 1)[0]].append(cells)
            total_rows += 1

    hdr = (
        f"{'division':<9} {'rows':>4} {'A':>4} {'B':>4} {'net':>4} {'gain':>4} "
        f"{'LOSS':>4} {'FLIP':>4} {'rc!=':>4} {'cmpA':>4} {'DISA':>4} {'cmpB':>4} "
        f"{'DISB':>4} {'both':>4} {'A_sum_s':>8} {'B_sum_s':>8} {'A_med':>6} "
        f"{'B_med':>6} {'B<.5A':>5} {'noise':>5} {'B>2A':>4}"
    )
    print(hdr)
    board = []
    tot = defaultdict(int)
    tot_ms = defaultdict(float)
    gain_rows, loss_rows, flip_rows, rc_rows, dis_rows, fast_rows = [], [], [], [], [], []
    for div in DIVS + sorted(set(rows) - set(DIVS)):
        if div not in rows:
            continue
        a_dec = b_dec = gain = loss = flip = rc_diff = 0
        cmp_a = dis_a = cmp_b = dis_b = 0
        a_ms, b_ms = [], []
        fast = noise = slow = 0
        for path, a, a_ms_s, a_rc, b, b_ms_s, b_rc, _first, status in rows[div]:
            a_dec += a in DECIDED
            b_dec += b in DECIDED
            if a not in DECIDED and b in DECIDED:
                gain += 1
                gain_rows.append((path, a, b, a_ms_s, b_ms_s))
            if a in DECIDED and b not in DECIDED:
                loss += 1
                loss_rows.append((path, a, b, a_ms_s, b_ms_s))
            if a in DECIDED and b in DECIDED and a != b:
                flip += 1
                flip_rows.append((path, a, b))
            if a_rc != b_rc:
                rc_diff += 1
                rc_rows.append((path, a_rc, b_rc, a, b))
            if status in DECIDED and a in DECIDED:
                cmp_a += 1
                if status != a:
                    dis_a += 1
                    dis_rows.append((path, "A", status, a))
            if status in DECIDED and b in DECIDED:
                cmp_b += 1
                if status != b:
                    dis_b += 1
                    dis_rows.append((path, "B", status, b))
            if a in DECIDED and b in DECIDED:
                am, bm = int(a_ms_s), int(b_ms_s)
                a_ms.append(am)
                b_ms.append(bm)
                if bm < 0.5 * am:
                    fast += 1
                    fast_rows.append((path, a, am, bm))
                elif am > 0 and abs(math.log(max(bm, 1) / max(am, 1))) <= math.log(1.25):
                    noise += 1
                elif bm > 2 * am:
                    slow += 1
        n = len(rows[div])
        both = len(a_ms)
        a_sum = sum(a_ms) / 1000
        b_sum = sum(b_ms) / 1000
        a_med = statistics.median(a_ms) if a_ms else 0
        b_med = statistics.median(b_ms) if b_ms else 0
        print(
            f"{div:<9} {n:>4} {a_dec:>4} {b_dec:>4} {b_dec - a_dec:>+4} {gain:>4} "
            f"{loss:>4} {flip:>4} {rc_diff:>4} {cmp_a:>4} {dis_a:>4} {cmp_b:>4} "
            f"{dis_b:>4} {both:>4} {a_sum:>8.1f} {b_sum:>8.1f} {a_med:>6.0f} "
            f"{b_med:>6.0f} {fast:>5} {noise:>5} {slow:>4}"
        )
        board.append(
            (div, n, a_dec, b_dec, b_dec - a_dec, gain, loss, flip, rc_diff,
             cmp_a, dis_a, cmp_b, dis_b, both, f"{a_sum:.1f}", f"{b_sum:.1f}",
             f"{a_med:.0f}", f"{b_med:.0f}", fast, noise, slow)
        )
        for key, val in (
            ("rows", n), ("a", a_dec), ("b", b_dec), ("gain", gain), ("loss", loss),
            ("flip", flip), ("rc", rc_diff), ("cmp_a", cmp_a), ("dis_a", dis_a),
            ("cmp_b", cmp_b), ("dis_b", dis_b), ("both", both), ("fast", fast),
            ("noise", noise), ("slow", slow),
        ):
            tot[key] += val
        tot_ms["a"] += sum(a_ms)
        tot_ms["b"] += sum(b_ms)
    print(
        f"{'TOTAL':<9} {tot['rows']:>4} {tot['a']:>4} {tot['b']:>4} "
        f"{tot['b'] - tot['a']:>+4} {tot['gain']:>4} {tot['loss']:>4} {tot['flip']:>4} "
        f"{tot['rc']:>4} {tot['cmp_a']:>4} {tot['dis_a']:>4} {tot['cmp_b']:>4} "
        f"{tot['dis_b']:>4} {tot['both']:>4} {tot_ms['a'] / 1000:>8.1f} "
        f"{tot_ms['b'] / 1000:>8.1f} {'':>6} {'':>6} {tot['fast']:>5} {tot['noise']:>5} "
        f"{tot['slow']:>4}"
    )
    print(f"\nrows scored: {total_rows} of 3200 expected")
    print(f"malformed rows (excluded, not scored as unchanged): {len(malformed)}")
    for m in malformed:
        print(f"  {m}")
    print(f"\nFLIPS (sat<->unsat, must be 0): {len(flip_rows)}")
    for r in flip_rows:
        print(f"  {r}")
    print(
        f"\n:status DISAGREEMENTS (must be 0): {len(dis_rows)} over "
        f"{tot['cmp_a']} A + {tot['cmp_b']} B = {tot['cmp_a'] + tot['cmp_b']} comparisons"
    )
    for r in dis_rows:
        print(f"  {r}")
    print(f"\nGAINS (A undecided, B decided): {len(gain_rows)}")
    for r in gain_rows:
        print(f"  {r}")
    print(f"\nLOSSES (A decided, B undecided): {len(loss_rows)}")
    for r in loss_rows:
        print(f"  {r}")
    print(f"\nEXIT STATUS differs: {len(rc_rows)}")
    for r in rc_rows:
        print(f"  {r}")
    print(f"\nB wall < 0.5 x A wall on both-decided rows: {len(fast_rows)}")
    for r in sorted(fast_rows, key=lambda r: r[2] - r[3], reverse=True)[:40]:
        print(f"  {r}")

    if args.board_tsv:
        with open(args.board_tsv, "w") as fh:
            fh.write(
                "division\trows\tA_decided\tB_decided\tnet\tgains\tlosses\tflips\t"
                "rc_differs\tcmp_A\tdisagree_A\tcmp_B\tdisagree_B\tboth_decided\t"
                "A_wall_sum_s\tB_wall_sum_s\tA_wall_median_ms\tB_wall_median_ms\t"
                "B_under_half_A\twithin_noise\tB_over_2x_A\n"
            )
            for r in board:
                fh.write("\t".join(str(x) for x in r) + "\n")
            fh.write(
                "\t".join(str(x) for x in (
                    "TOTAL", tot["rows"], tot["a"], tot["b"], tot["b"] - tot["a"],
                    tot["gain"], tot["loss"], tot["flip"], tot["rc"], tot["cmp_a"],
                    tot["dis_a"], tot["cmp_b"], tot["dis_b"], tot["both"],
                    f"{tot_ms['a'] / 1000:.1f}", f"{tot_ms['b'] / 1000:.1f}", "", "",
                    tot["fast"], tot["noise"], tot["slow"],
                )) + "\n"
            )
    if args.movers:
        with open(args.movers, "w") as fh:
            for r in gain_rows + loss_rows + flip_rows:
                fh.write(CORPUS + r[0] + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
