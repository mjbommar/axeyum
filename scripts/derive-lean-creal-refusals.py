#!/usr/bin/env python3
"""Turn pinned Lean's error output on the generated `creal` carrier into the
committed refusal measurement the library generator reads.

WHY THIS EXISTS. `crates/axeyum-lean-kernel/examples/render_creal_library.rs`
renders every declaration the Axeyum kernel admitted into Lean source. Lean has
two checkers and they disagree (ADR-0517): its *kernel* accepts these terms --
the replay census (ADR-1661) hands it the same proofs over the `lean4export`
wire and grades them accepted by name -- while its *elaborator*, which is what
reads `.lean` source, will not unfold a definition far enough to see a
definitional equality the term needs, and refuses.

Those refusals are EXCLUSIONS with a stated reason, never `sorry` and never an
axiom (ADR-1675). This script derives the list from Lean's own output rather
than from anybody's memory, so re-running it is how the list is re-measured.

WHAT IT DOES NOT DO. It does not decide *why* Lean refused; it copies Lean's
first error line verbatim. And it does not compute the cascade -- a declaration
that merely mentions a refused one fails with `unknown constant`, which is the
same finding said twice. The generator computes that closure from the kernel,
which is the authority on dependencies, and this script drops those rows.

USAGE
    lean --root <pkg> -D maxErrors=1000000 -D maxHeartbeats=1000000 \\
         -D linter.defProp=false -D autoImplicit=false \\
         <pkg>/Axeyum/Creal/Carrier.lean > all-errors.log 2>&1
    python3 scripts/derive-lean-creal-refusals.py \\
        --log all-errors.log --carrier <pkg>/Axeyum/Creal/Carrier.lean \\
        --toolchain "$(cat lean-toolchain)" \\
        --out artifacts/measurements/lean-creal-elaborator-refusals-2026-09-05.json

`maxErrors` must be raised: Lean's default of 100 stops part-way through the
file, and a partial list would publish a package that does not build.
"""

from __future__ import annotations

import argparse
import json
import re
import sys

# A top-level command opening a declaration. `unsafe axiom` (the three
# compiler-internal constants the module banner declares) is deliberately not
# here: those are Lean's own, not part of the development.
HEAD = re.compile(r"^(?:def|theorem|opaque|axiom|inductive) ([^ \n]+)")
# Two shapes reach this script and both must parse: `lean` writes
# `<path>:<line>:<col>: error: <msg>` (and `error(lean.unknownIdentifier):` for
# a named error class), while `lake` prefixes the whole line with `error: `.
# A regex written against one of them silently matches nothing in the other,
# and "no refusals" is exactly what a broken read looks like -- which is why
# `--expect-errors` exists below.
ERROR = re.compile(
    r"Carrier\.lean:(\d+):(\d+): (?:error|warning)(?:\([^)]*\))?: (.*)$"
)

# Errors that are a consequence of an earlier refusal, not a finding of their
# own. The generator recomputes this closure from the kernel's dependency
# graph, which is complete; matching on the message is only how the rows are
# dropped here.
CASCADE = re.compile(r"^\(kernel\) unknown constant|^[Uu]nknown constant|^[Uu]nknown identifier")

# Not about any declaration.
NOT_A_DECLARATION = re.compile(r"maximum number of errors|build failed")


def declaration_heads(carrier_path: str) -> list[tuple[int, str]]:
    """(1-based line number, rendered name) for every top-level command."""
    heads: list[tuple[int, str]] = []
    with open(carrier_path, encoding="utf-8") as handle:
        for index, line in enumerate(handle, start=1):
            match = HEAD.match(line)
            if match:
                heads.append((index, match.group(1).split(".{")[0]))
    if not heads:
        sys.exit(
            f"derive-lean-creal-refusals: {carrier_path} has no declaration heads at column "
            "zero. That is a broken read of the carrier, not a carrier with no declarations."
        )
    return heads


def owner_of(heads: list[tuple[int, str]], line: int) -> str | None:
    """The declaration whose command contains `line`: the last head at or above it."""
    lo, hi, found = 0, len(heads) - 1, None
    while lo <= hi:
        mid = (lo + hi) // 2
        if heads[mid][0] <= line:
            found = heads[mid][1]
            lo = mid + 1
        else:
            hi = mid - 1
    return found


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--log", required=True, help="Lean's stdout+stderr over the carrier")
    parser.add_argument("--carrier", required=True, help="the generated Carrier.lean")
    parser.add_argument("--toolchain", required=True, help="the pin the log was produced under")
    parser.add_argument("--out", required=True)
    parser.add_argument(
        "--expect-errors",
        type=int,
        default=1,
        help=(
            "minimum number of Lean error lines this run must PARSE. A regex written for one "
            "of Lean's two output shapes matches nothing in the other, and 'no refusals' is "
            "exactly what that broken read looks like -- indistinguishable from a clean build. "
            "Set it to a number the log is known to contain."
        ),
    )
    args = parser.parse_args()

    heads = declaration_heads(args.carrier)

    refusals: dict[str, str] = {}
    cascades = 0
    unattributed = 0
    seen = 0
    with open(args.log, encoding="utf-8", errors="replace") as handle:
        for raw in handle:
            match = ERROR.search(raw.rstrip("\n"))
            if not match:
                continue
            if ": warning" in raw[: match.start(3)]:
                continue
            seen += 1
            message = match.group(3).strip()
            if NOT_A_DECLARATION.search(message):
                continue
            if CASCADE.match(message):
                cascades += 1
                continue
            owner = owner_of(heads, int(match.group(1)))
            if owner is None:
                unattributed += 1
                continue
            refusals.setdefault(owner, message)

    if seen < args.expect_errors:
        sys.exit(
            f"derive-lean-creal-refusals: parsed {seen} error line(s) from {args.log}, expected "
            f"at least {args.expect_errors}. Either the log is from a clean run (in which case "
            "there is nothing to derive and the refusal list should be empty by construction, "
            "not by a failed parse) or the error-line shape has moved."
        )

    if unattributed:
        sys.exit(
            f"derive-lean-creal-refusals: {unattributed} error(s) fell before the first "
            "declaration head. The carrier and the log do not match; re-run Lean over THIS "
            "carrier."
        )

    document = {
        "measured": "2026-09-05",
        "toolchain": args.toolchain.strip(),
        "carrier": "creal",
        "note": (
            "Declarations pinned Lean's ELABORATOR refuses from `.lean` source. Lean's KERNEL "
            "accepts the same terms over the `lean4export` wire (ADR-1661); the disagreement is "
            "ADR-0517's, between Lean's two checkers, and is a property of the route rather than "
            "of the mathematics. Derived by scripts/derive-lean-creal-refusals.py from Lean's own "
            "output; the cascade (every declaration that merely mentions one of these, which Lean "
            "reports as `unknown constant`) is NOT listed here -- the generator recomputes it from "
            "the kernel's dependency graph."
        ),
        "direct_refusals": len(refusals),
        "cascade_errors_dropped": cascades,
        "refusals": [
            {"name": name, "lean_error": refusals[name]} for name in sorted(refusals)
        ],
    }
    with open(args.out, "w", encoding="utf-8") as handle:
        json.dump(document, handle, indent=2, ensure_ascii=False)
        handle.write("\n")
    print(
        f"derive-lean-creal-refusals: {len(refusals)} direct refusals, "
        f"{cascades} cascade errors dropped -> {args.out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
