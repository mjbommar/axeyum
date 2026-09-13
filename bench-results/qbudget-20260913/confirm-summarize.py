"""Classify the re-checked rows, from `confirm-moved.sh`'s RAW columns.

`confirm-moved.sh` measures; this classifies. They are separate because the
first version of this lane put the classification inside the measuring script
and it got the classification WRONG in the most expensive direction: it compared
a consistently-`unknown` arm against a declared `:status unsat` and printed
**CONTRADICTED** -- the word a soundness board is scanned for -- on two rows
where the arm had simply not decided. `unknown` is a first-class result and is
never a contradiction. The bug was visible only because the raw per-run columns
were in the artifact beside the verdict; had the script printed only its
conclusion, the wrong word would have been the whole record.

The outcomes, and only the first four are about the ARM's verdict:

  GAIN          base `unknown` on all three runs, arm decided on all three
  LOSS          base decided on all three runs, arm `unknown` on all three
  UNSTABLE      either arm disagreed with itself across its three runs -- the
                ~1-1.5 % of files that flip on ambient load at a 24 s budget.
                NOT counted as a gain or a loss in either direction.
  UNCHANGED     both arms agreed with each other
  CONTRADICTED  the arm decided `sat` where something independent says `unsat`,
                or the reverse. A soundness event; it sets the exit status.

and, orthogonally, ADR-1957's denominator:

  NO OPINION    nothing -- not `:status`, not z3, not cvc5, at 24 s or at
                600 s -- can speak to a verdict we produced. Printed beside
                every zero-disagreement claim, because a zero with no
                opportunity to fire is vacuous.

Usage: python3 confirm-summarize.py <confirm.tsv> [<confirm.tsv> ...]
"""

import csv
import pathlib
import sys

DECIDED = ("sat", "unsat")


def runs(cell: str) -> list[str]:
    return [x for x in cell.split(",") if x]


def stable(cell: str) -> str | None:
    """The verdict all three runs agree on, or `None` if they do not."""
    rs = runs(cell)
    return rs[0] if rs and len(set(rs)) == 1 else None


def main(argv: list[str]) -> int:
    if len(argv) < 2:
        print("usage: confirm-summarize.py <confirm.tsv> ...", file=sys.stderr)
        return 2
    totals: dict[str, int] = {}
    no_opinion = 0
    contradictions = []
    rows_seen = 0
    for path in argv[1:]:
        p = pathlib.Path(path)
        if not p.exists():
            print(f"{path}: DID NOT RUN")
            return 1
        print(f"== {p.name}")
        for r in csv.DictReader(open(p), delimiter="\t"):
            rows_seen += 1
            b, a = stable(r["base_x3"]), stable(r["arm_x3"])
            others = [
                r[k] for k in ("status", "z3_24", "cvc5_24", "z3_600", "cvc5_600")
                if r.get(k) in DECIDED
            ]
            if not others:
                no_opinion += 1
            verdict = "UNSTABLE"
            if b is not None and a is not None:
                if a in DECIDED and any(o != a for o in others):
                    verdict = "CONTRADICTED"
                    contradictions.append((p.name, r["file"], a, others))
                elif b == a:
                    verdict = "UNCHANGED"
                elif a in DECIDED and b not in DECIDED:
                    verdict = "GAIN"
                elif b in DECIDED and a not in DECIDED:
                    verdict = "LOSS"
                else:
                    verdict = "CONTRADICTED"
                    contradictions.append((p.name, r["file"], a, others))
            totals[verdict] = totals.get(verdict, 0) + 1
            checks = " ".join(
                f"{k.replace('_24', '').replace('_600', '@600')}={r[k]}"
                for k in ("status", "z3_24", "cvc5_24", "z3_600", "cvc5_600")
                if r.get(k) not in (None, "none", "skipped")
            )
            print(f"   {verdict:12s} base=[{r['base_x3']}] arm=[{r['arm_x3']}]")
            print(f"                {checks or 'NO INDEPENDENT CHECK AT ANY BUDGET'}")
            print(f"                {r['file'].split('non-incremental/')[-1]}")
    print()
    print(f"rows re-checked: {rows_seen}   " + "   ".join(
        f"{k} {v}" for k, v in sorted(totals.items())))
    tail = "  <-- VACUOUS for those rows" if no_opinion else ""
    print(f"NO INDEPENDENT CHECK AT ANY BUDGET (ADR-1957): {no_opinion} of {rows_seen}{tail}")
    if contradictions:
        for name, f, a, others in contradictions:
            print(f"!! CONTRADICTION in {name}: arm={a} others={others} {f}")
        return 4
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
