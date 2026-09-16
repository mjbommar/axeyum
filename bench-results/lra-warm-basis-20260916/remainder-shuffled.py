#!/usr/bin/env python3
"""Build the SHUFFLED remainder of an A/B list, given the rows already run.

# Why, and why it was not done up front

The A/B lists are in path order, and `QF_LRA/` path order is family-clustered:
the head is `2017-Heizmann-UltimateInvariantSynthesis/` and `LassoRanker/`, which
ADR-2125's own sizing measured as among the heaviest users of the route under
test. A sweep at 24 s per arm on two pinned core pairs measured out at about
2.5 minutes per row, so 200 rows per shard does not finish, and a partial then
has to be reported.

**A prefix of a path-ordered list cannot show an effect that is not uniform over
path order**, and here the non-uniformity is not hypothetical — it is the shape
the sizing found. Reporting the prefix as "n of 200 so far" would publish a
number biased TOWARD the treatment population, i.e. toward this lane's own
lever. That is the opposite of a conservative partial.

So the run is stopped, the rows already done are kept, and the REMAINDER is
shuffled. The union reported is then "the first k by path order, plus a seeded
uniform sample of the other 200-k", which is a statement the data supports and
which the ADR makes explicitly rather than rounding to "n of 200".

The set is never changed: this only reorders what is left, and the digest check
below proves the remainder is exactly `full - done`.

The seed is a constant in this source, not a flag, so the order cannot be
re-rolled quietly after a result. Changing it is a diff.

Usage: remainder-shuffled.py <full-list> <done.tsv> <out-list>
"""

import hashlib
import random
import sys

SEED = 20260916


def digest(rows):
    return hashlib.sha256("\n".join(sorted(rows)).encode()).hexdigest()[:16]


def main(full_path, done_path, out_path):
    full = [r for r in open(full_path).read().splitlines() if r.strip()]
    done_lines = open(done_path).read().splitlines()
    done = {l.split("\t")[0] for l in done_lines[1:] if l.strip()}

    unknown = done - set(full)
    if unknown:
        sys.exit(
            f"ABORT: {len(unknown)} row(s) in {done_path} are not in {full_path}; "
            "the two do not describe the same population"
        )

    remainder = [r for r in full if r not in done]
    if len(remainder) + len(done) != len(full):
        sys.exit("ABORT: done + remainder != full; the split is not a partition")

    rng = random.Random(f"{SEED}:{out_path}")
    shuffled = list(remainder)
    rng.shuffle(shuffled)
    if digest(shuffled) != digest(remainder):
        sys.exit("ABORT: the shuffle changed the SET, not just the order")

    with open(out_path, "w") as handle:
        handle.write("".join(f"{r}\n" for r in shuffled))
    print(
        f"{out_path}: full {len(full)}  done {len(done)}  remainder {len(shuffled)}  "
        f"remainder digest {digest(shuffled)} (order-independent)"
    )


if __name__ == "__main__":
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2], sys.argv[3])
