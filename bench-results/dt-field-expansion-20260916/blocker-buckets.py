#!/usr/bin/env python3
"""DT-FIELD-EXPANSION -- bucket a `--trace` sweep's UNDECIDED rows by the code
site their give-up sentence names, and join that with `expansion-reach.py`.

    blocker-buckets.py <sizing.shard*.tsv ...> --reach <reach-*.tsv ...>

The two questions this answers, which no committed census answers together:

  1. OF THE FILES WE DO NOT DECIDE, how many terminate at each site?
  2. OF THOSE, how many does ADR-2128's lever reach AT ALL -- i.e. how many
     have a datatype the nested expansion can convert, and no cyclic or
     `W1`-refused datatype blocking the same file?

The sentences are matched on SUBSTRINGS of the give-up detail rather than on a
bucket LABEL, because ADR-2020's census reported one cause where the raw details
held four, and this lane's own reading of DT-GROUND-PROBE's largest bucket was
wrong about which sort was refused.  An unmatched sentence is reported as
`OTHER` with its text, never dropped -- a classifier that silently absorbs what
it does not recognise reports a stable number that is stably wrong.
"""

import os
import sys
from collections import Counter, defaultdict

# (bucket, needle). ORDER MATTERS: the first match wins, and the datatype
# sentences are listed before the generic ones because `relabel_with_datatype_
# refusal` puts the datatype rung's sentence in FRONT of a lower rung's refusal.
SITES = [
    ("dt:field-sort-W1", "a datatype field sort with no expansion variable"),
    ("dt:exactness-arg", "congruence over a datatype argument whose expansion is not exact"),
    ("dt:exactness-result", "whose RESULT datatype's expansion is not exact"),
    ("dt:result-mentions-dt", "whose RESULT sort MENTIONS a datatype"),
    ("dt:ctor-arg-datatype", "constructor argument in a congruence antecedent is itself"),
    ("dt:non-variable-term", "over a non-variable datatype term"),
    ("dt:ack-pair-bound", "Ackermann"),
    ("dt:nested-child-bound", "nested datatype field expansion needs more child slots"),
    ("array:non-bv", "outside the current Bool/Int lazy array route"),
    ("bv:datatype-sorted-term", "that the pure-Rust BV backend cannot bit-blast"),
    ("quant:mbqi-unsupported", "mbqi declined an unsupported fragment"),
    # THE RELAXATION'S OWN INCOMPLETENESS, and it belongs with the exactness
    # arms rather than in `OTHER`: `project_and_replay` threw away a `sat`
    # candidate because the traversed-field children were free and the projected
    # value does not satisfy the original assertions. Exactness is what would
    # stop the children being free.
    ("dt:relaxation-incomplete", "the traversed-field relaxation is incomplete here"),
    ("dt:model-lacks-field", "datatype expansion model lacks a field value"),
    ("quant:watchdog", "watchdog fired before the worker thread returned"),
    ("quant:time-budget", "quantified solve time budget exhausted"),
    ("quant:ematching", "e-matching"),
    ("quant:instantiation-sat", "instantiation is satisfiable"),
    ("quant:mbqi-rounds", "MBQI did not converge"),
    ("backend:sort-mismatch", "operands must share a sort"),
]


def bucket(detail):
    for name, needle in SITES:
        if needle in detail:
            return name
    return None


def main():
    argv = sys.argv[1:]
    if "--reach" not in argv:
        sys.stderr.write(__doc__)
        return 2
    cut = argv.index("--reach")
    sweeps, reaches = argv[:cut], argv[cut + 1:]
    if not sweeps or not reaches:
        sys.stderr.write(__doc__)
        return 2

    # basename -> (any_cyclic, any_w1, any_convert)
    reach = {}
    for path in reaches:
        with open(path) as fh:
            next(fh, None)
            for line in fh:
                f = line.rstrip("\n").split("\t")
                if len(f) < 9:
                    continue
                b = os.path.basename(f[0])
                cy, w1, cv = reach.get(b, (0, 0, 0))
                reach[b] = (cy + int(f[3]), w1 + int(f[6]), cv + int(f[8]))

    rows = 0
    verdicts = Counter()
    buckets = Counter()
    clean = Counter()
    unknown_sentences = defaultdict(int)
    no_reach = 0
    for path in sweeps:
        with open(path) as fh:
            next(fh, None)
            for line in fh:
                f = line.rstrip("\n").split("\t")
                if len(f) < 10:
                    continue
                rows += 1
                name, verdict, detail = f[0], f[1], f[9]
                verdicts[verdict] += 1
                if verdict in ("sat", "unsat"):
                    continue
                b = bucket(detail)
                if b is None:
                    b = "OTHER"
                    unknown_sentences[detail[:160]] += 1
                buckets[b] += 1
                got = reach.get(name)
                if got is None:
                    no_reach += 1
                    continue
                cy, w1, cv = got
                if cv > 0 and cy == 0 and w1 == 0:
                    clean[b] += 1

    print("rows=%d" % rows)
    print("verdicts: %s" % dict(verdicts))
    if no_reach:
        print("WARNING: %d undecided rows had NO reach row -- the join is "
              "incomplete and every CLEAN count below is a LOWER bound" % no_reach)
    print()
    print("%-26s %6s %6s" % ("terminal site", "n", "CLEAN"))
    for b, n in buckets.most_common():
        print("%-26s %6d %6d" % (b, n, clean.get(b, 0)))
    if unknown_sentences:
        print()
        print("UNMATCHED give-up sentences (reported, never dropped):")
        for text, n in sorted(unknown_sentences.items(), key=lambda x: -x[1]):
            print("  %4d  %s" % (n, text))
    if not rows:
        sys.stderr.write("NO ROWS READ\n")
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
