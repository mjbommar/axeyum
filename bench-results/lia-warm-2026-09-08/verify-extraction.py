#!/usr/bin/env python3
"""Check that inlining `decide_int_constraints` back into `lia_simplex_capped`
reproduces main's function token for token.

The extraction is the soundness-critical half of the `lra.rs` resolution: if it
changed anything about the sequence — the tightening, the Gomory-first
dispatch, the counter calls, the node budget — a wrong verdict is a possible
outcome, and neither a test nor a review of the diff would obviously say so
because the diff is a whole function moving.

So this reconstructs main's body mechanically and compares. Whitespace and the
call/return plumbing that HAS to differ (the `let outcome =` binding, the
`constraints` borrow) are normalised; nothing else is.
"""
import re
import subprocess
import sys

root = sys.argv[1]


def fn_body(src, name):
    """The text of `fn <name>(` through its closing brace at column 0."""
    i = src.index(f"\nfn {name}(")
    depth = 0
    started = False
    for j in range(i, len(src)):
        if src[j] == "{":
            depth += 1
            started = True
        elif src[j] == "}":
            depth -= 1
            if started and depth == 0:
                return src[i : j + 1]
    raise SystemExit(f"no closing brace for {name}")


main_src = subprocess.run(
    ["git", "-C", root, "show", "origin/main:crates/axeyum-solver/src/lra.rs"],
    capture_output=True,
    text=True,
    check=True,
).stdout
mine_src = open(f"{root}/crates/axeyum-solver/src/lra.rs").read()

main_capped = fn_body(main_src, "lia_simplex_capped")
mine_capped = fn_body(mine_src, "lia_simplex_capped")
mine_decide = fn_body(mine_src, "decide_int_constraints")

# Inline: take my decide body (minus signature and outer braces) and splice it
# back where the call is, restoring the `let outcome = ... ;` binding main had.
decide_inner = mine_decide[mine_decide.index("{") + 1 : mine_decide.rindex("}")]
decide_inner = decide_inner.replace(
    "if let Some(decided) = lia_gomory_cuts(constraints, nvars, deadline) {",
    "let outcome = if let Some(decided) = lia_gomory_cuts(&constraints, nvars, deadline) {",
).replace(
    "lia_branch_and_bound(constraints, nvars, &mut budget, deadline)",
    "lia_branch_and_bound(&mut constraints, nvars, &mut budget, deadline)",
)
# The block tail becomes the `};` of the binding.
decide_inner = decide_inner.rstrip()
assert decide_inner.endswith("}"), decide_inner[-60:]
decide_inner = decide_inner + ";"

reconstructed = mine_capped.replace(
    "    let outcome = decide_int_constraints(&mut constraints, nvars, node_cap, deadline);",
    decide_inner,
)


def norm(text):
    """Collapse whitespace; comments are kept because a changed comment beside
    unchanged arithmetic is exactly the drift worth seeing."""
    return re.sub(r"\s+", " ", text).strip()


a, b = norm(main_capped), norm(reconstructed)
if a == b:
    print("IDENTICAL: inlining the extraction reproduces main's lia_simplex_capped")
    sys.exit(0)

print("DIFFERS. First divergence:")
for k in range(min(len(a), len(b))):
    if a[k] != b[k]:
        print(f"  at char {k}")
        print(f"  main: ...{a[max(0, k - 120) : k + 200]}")
        print(f"  mine: ...{b[max(0, k - 120) : k + 200]}")
        break
else:
    print(f"  one is a prefix of the other: main {len(a)} chars, mine {len(b)}")
    print(f"  main tail: {a[min(len(a), len(b)) :][:300]}")
    print(f"  mine tail: {b[min(len(a), len(b)) :][:300]}")
sys.exit(1)
