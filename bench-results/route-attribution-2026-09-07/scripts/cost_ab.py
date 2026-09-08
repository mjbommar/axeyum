#!/usr/bin/env python3
"""Scores the `cost_ab.sh` A/B: does route attribution cost anything when OFF?

Reads the alternating-arm TSV and reports, per file, the median wall time on
each arm across repetitions, then the paired difference. Median rather than mean
because a single scheduling hiccup on one repetition should not decide the
answer.

# Guards (each exits 1, none merely warns)

  * **Verdict agreement.** If the two arms disagree on any file's verdict the
    comparison is meaningless and no timing number is reported at all. This is
    also a second, independent check of the invariance property the Rust suite
    pins -- from the shipped binary rather than the library.
  * **Coverage.** Both arms must have run every file the same number of times.
    A missing arm silently halves a population and biases the median.
  * **Discrimination.** The instrument must be able to SEE a real regression, or
    "no measurable cost" is a statement about the instrument. `--self-check`
    injects a synthetic 5% slowdown into the `new` arm and requires the verdict
    to flip to REGRESSION; if it does not, the harness cannot detect the thing
    it is being used to rule out.

Run:
  cost_ab.py ab.tsv
  cost_ab.py ab.tsv --self-check
"""
import statistics
import sys
from collections import defaultdict

# A paired median shift above this is reported as a regression. 3% is well
# inside process-startup and scheduling noise on this box for sub-second runs,
# and far below anything that would matter to a parity baseline.
REGRESSION_THRESHOLD = 0.03


def load(path):
    rows = []
    with open(path, encoding="utf-8") as f:
        header = f.readline().rstrip("\n").split("\t")
        for line in f:
            line = line.rstrip("\n")
            if not line:
                continue
            parts = line.split("\t")
            if len(parts) != len(header):
                continue
            rows.append(dict(zip(header, parts)))
    return rows


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    self_check = "--self-check" in sys.argv
    if not args:
        print("usage: cost_ab.py ab.tsv [--self-check]", file=sys.stderr)
        return 2

    rows = load(args[0])
    if not rows:
        print("no rows -- refusing to report a timing result over an empty "
              "population", file=sys.stderr)
        return 1

    times = defaultdict(lambda: defaultdict(list))
    verdicts = defaultdict(lambda: defaultdict(set))
    for r in rows:
        ms = int(r["wall_ms"])
        if self_check and r["arm"] == "new":
            ms = int(ms * 1.05)  # injected 5% regression
        times[r["file"]][r["arm"]].append(ms)
        verdicts[r["file"]][r["arm"]].add(r["verdict"])

    # GUARD: verdict agreement between the arms.
    disagree = []
    for f, byarm in verdicts.items():
        if "base" in byarm and "new" in byarm and byarm["base"] != byarm["new"]:
            disagree.append(f"{f}: base={sorted(byarm['base'])} new={sorted(byarm['new'])}")
    if disagree:
        print(f"VERDICT DISAGREEMENT on {len(disagree)} file(s) -- the timing "
              f"comparison is void:", file=sys.stderr)
        for d in disagree[:20]:
            print(f"  {d}", file=sys.stderr)
        return 1

    # GUARD: equal coverage.
    uneven = [f for f, byarm in times.items()
              if len(byarm.get("base", [])) != len(byarm.get("new", []))
              or not byarm.get("base")]
    if uneven:
        print(f"UNEVEN COVERAGE on {len(uneven)} file(s); a missing arm biases "
              f"the median", file=sys.stderr)
        return 1

    per_file = []
    for f, byarm in sorted(times.items()):
        b = statistics.median(byarm["base"])
        n = statistics.median(byarm["new"])
        per_file.append((f, b, n))

    total_base = sum(b for _, b, _ in per_file)
    total_new = sum(n for _, _, n in per_file)
    ratio = total_new / total_base if total_base else float("nan")
    # Paired per-file relative deltas: robust to one huge file dominating the
    # totals, which a bare ratio is not.
    deltas = [(n - b) / b for _, b, n in per_file if b > 0]
    median_delta = statistics.median(deltas) if deltas else float("nan")

    print(f"files            {len(per_file)}")
    print(f"reps per arm     {len(times[per_file[0][0]]['base'])}")
    print(f"total base ms    {total_base}")
    print(f"total new  ms    {total_new}")
    print(f"total ratio      {ratio:.4f}")
    print(f"median per-file  {median_delta:+.4%}")
    regressed = median_delta > REGRESSION_THRESHOLD
    verdict = "REGRESSION" if regressed else "no measurable cost"
    print(f"verdict          {verdict} (threshold {REGRESSION_THRESHOLD:.0%})")

    if self_check:
        # GUARD: the instrument must be able to see a real regression.
        if not regressed:
            print("\nSELF-CHECK FAILED: a synthetic 5% slowdown did not "
                  "register as a regression, so this harness cannot detect the "
                  "cost it is being used to rule out.", file=sys.stderr)
            return 1
        print("\nself-check ok: an injected 5% slowdown IS detected, so a "
              "clean result from the real run is a measurement rather than an "
              "insensitive instrument.")
        return 0

    return 1 if regressed else 0


if __name__ == "__main__":
    sys.exit(main())
