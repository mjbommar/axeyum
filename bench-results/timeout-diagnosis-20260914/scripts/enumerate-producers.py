#!/usr/bin/env python3
"""Count, on ANY tree, the program points that can end in `lra.rs`'s single
give-up sentence.

Three methods, run against the same file, because the first two under-report and
saying so is the point:

  A. NAME SCAN  -- every `Decision::TimedOut` construction. This is what
     ADR-2045 did, and at the `Decision` level it is CORRECT: there are six.
     It stops at the enum boundary, so it cannot see a producer that reaches
     the variant through a different type.

  B. FUNNEL SCAN -- the cause-erasing returns BELOW those six: every bail point
     in `collect_constraints`, `solve`, `eliminate` and `simplex_fallback` whose
     value is a bare `None` / unit variant that the caller then has to guess a
     cause for. Each one can end in the same sentence.

  C. COMPILER -- not run here. Method C is the refactor itself: give each
     chokepoint a typed cause and the type checker enumerates every site it can
     no longer infer. It is the only method that cannot under-report, and its
     answer is what B is checked against.

Usage: enumerate-producers.py <path/to/lra.rs>
"""

import re
import sys
import pathlib

# Function name -> the bail patterns that erase a cause inside it. A pattern is
# counted once per OCCURRENCE, not once per kind: `a?` and `b?` on one line are
# two program points that a reader cannot tell apart from the caller.
FUNNELS = {
    "collect_constraints": [r"return Ok\(None\);"],
    "solve": [r"return Feasibility::TimedOut;", r"=> return Feasibility::TimedOut,"],
    "eliminate": [r"return None;", r"\?"],
    "simplex_fallback": [r"return Ok\(None\);", r"^\s*_ => Ok\(None\),", r"Ok\(None\)$"],
}


def function_body(src, name):
    """The text of `fn <name>(` up to the next line starting with `}` at col 0."""
    m = re.search(rf"^fn {re.escape(name)}\(", src, re.M)
    if not m:
        return None
    rest = src[m.start():]
    end = rest.index("\n}\n")
    return rest[: end + 2]


def main(path):
    src = pathlib.Path(path).read_text(encoding="utf-8")
    print(f"tree: {path}")

    # --- A ---------------------------------------------------------------
    name_scan = re.findall(r"return Ok\(Decision::TimedOut\);|Ok\(Decision::TimedOut\)\n", src)
    decide = function_body(src, "decide_within")
    a = 0 if decide is None else len(re.findall(r"Decision::TimedOut", decide))
    after = function_body(src, "simplex_after_elimination")
    a_after = 0 if after is None else len(re.findall(r"Decision::TimedOut", after))
    print(f"A. name scan: Decision::TimedOut constructions")
    print(f"     decide_within            {a}")
    print(f"     simplex_after_elimination {a_after}")
    print(f"     (whole file, any form)   {len(name_scan)}")

    # --- B ---------------------------------------------------------------
    total = 0
    print("B. funnel scan: cause-erasing bail points BELOW those constructions")
    for fn, pats in FUNNELS.items():
        body = function_body(src, fn)
        if body is None:
            print(f"     {fn:22} NOT FOUND -- the scan never reached its subject")
            continue
        count = 0
        for line in body.splitlines():
            stripped = line.strip()
            if stripped.startswith("//") or stripped.startswith("///"):
                continue
            for pat in pats:
                count += len(re.findall(pat, line))
        print(f"     {fn:22} {count}")
        total += count
    print(f"     funnel total             {total}")
    print(f"  TOTAL program points reaching one sentence: {a + a_after + total}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
