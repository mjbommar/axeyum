#!/usr/bin/env python3
"""DT-ARRAY-ELEMENT sizing: how many undecided rows are blocked by the
`register_datatype` W1 refusal on an ARRAY sort, split by element-datatype vs
uninterpreted domain/range, per division with denominators.

Reuses ADR-2128's `blocker-buckets.py` SITES table verbatim (substring match on
the raw give-up detail, first match wins, unmatched reported as OTHER) so the
two censuses are comparable.
"""
import csv, os, sys, collections

csv.field_size_limit(200_000_000)
SEP = "\\p"

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
    return "OTHER: " + detail[:100]


def base(p):
    return os.path.basename(p)


def load_reach(path):
    """basename -> dict(n_dt, w1_sorts Counter, any_w1)"""
    out = collections.defaultdict(lambda: {"n": 0, "w1": collections.Counter()})
    with open(path, newline="") as fh:
        for row in csv.DictReader(fh, delimiter="\t"):
            b = base(row["file"])
            # the probe's stripped copies carry a `.core.smt2` / `.smt2` suffix
            for suf in (".core.smt2",):
                if b.endswith(suf):
                    b = b[: -len(suf)] + ".smt2"
            e = out[b]
            e["n"] += 1
            if row["today_w1"] == "1":
                e["w1"][row["w1_sort"]] += 1
    return out


def classify_w1_sort(s):
    """Split the refused sort: array-with-datatype-element vs array whose
    domain/range mentions an uninterpreted sort vs anything else."""
    if s.startswith("('Array'"):
        if "('D'," in s:
            return "array-datatype-element"
        if "('U'," in s or "Uninterpreted" in s:
            return "array-uninterpreted-component"
        return "array-other"
    return "non-array: " + s


def main():
    ledger, reach_path, label = sys.argv[1], sys.argv[2], sys.argv[3]
    reach = load_reach(reach_path) if reach_path != "-" else {}
    with open(ledger, newline="") as fh:
        rows = list(csv.DictReader(fh, delimiter="\t"))
    unk = [r for r in rows if r["verdict"] == "unknown"]
    print(f"### {label}: {len(rows)} rows, {len(rows)-len(unk)} decided, {len(unk)} undecided")

    # terminal-site histogram
    def terminal(r):
        d = [x for x in (r.get("decline_details") or "").split(SEP) if x.strip()]
        return d[-1] if d else "(no typed detail)"

    def anywhere(r):
        return [x for x in (r.get("decline_details") or "").split(SEP) if x.strip()]

    term = collections.Counter(bucket(terminal(r)) for r in unk)
    print("  terminal site (undecided rows):")
    for k, n in term.most_common():
        print(f"    {n:4d}  {k}")

    W1 = "a datatype field sort with no expansion variable"
    n_term_w1 = sum(1 for r in unk if W1 in terminal(r))
    n_any_w1 = sum(1 for r in unk if any(W1 in d for d in anywhere(r)))
    print(f"  undecided rows whose TERMINAL detail is the W1 refusal: {n_term_w1} / {len(unk)}")
    print(f"  undecided rows where the W1 refusal appears ANYWHERE in the trail: {n_any_w1} / {len(unk)}")

    if reach:
        joined = [r for r in unk if base(r["corpus_path"]) in reach]
        print(f"  reach join: {len(joined)} / {len(unk)} undecided rows have a reach row")
        has_w1 = [r for r in joined if reach[base(r["corpus_path"])]["w1"]]
        print(f"  undecided rows whose FILE declares >=1 W1-refused datatype: {len(has_w1)} / {len(unk)}")
        sorts = collections.Counter()
        for r in has_w1:
            for s, n in reach[base(r["corpus_path"])]["w1"].items():
                sorts[classify_w1_sort(s)] += n
        print("  refused-sort split (datatype instances, over those rows' files):")
        for k, n in sorts.most_common():
            print(f"    {n:5d}  {k}")
        t2 = collections.Counter(bucket(terminal(r)) for r in has_w1)
        print("  terminal site of the W1-carrying undecided rows:")
        for k, n in t2.most_common():
            print(f"    {n:4d}  {k}")
    print()


main()
