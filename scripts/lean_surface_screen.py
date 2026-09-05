#!/usr/bin/env python3
"""Screen a Lean surface statement for the two constructs that do not re-parse.

A `formal.statement` on an `F:ml430-*` mirror is a byte-identical quotation of
the pinned extractor's PRETTY-PRINTED type. A pretty-printed type is not
guaranteed to elaborate again: printing runs inside the module's context and
reading does not. Two classes of that failure are measured
(ADR-1662; `artifacts/measurements/statement-import-blocker-census-2026-09-05.json`)
and both are detectable from the statement text alone, on any host, with no Lean:

`elided-proof-glyph`
    The printer replaced a proof term with `⋯`, an inaccessible name with `✝`,
    or a truncated subterm with `…`. Read back, the glyph is a hole Lean cannot
    fill, and no amount of context makes it one.

`variable-block-dropped`
    Statement-only extraction takes the type out of the module that declared it,
    and Mathlib's enclosing `variable` block goes with it. What is left can have
    no type to elaborate against. Two signatures:

    * `coerced-projection` -- dot notation on a parenthesized group in which
      EVERY top-level operand is `↑`-coerced, e.g. `(↑a - ↑b).natAbs`. Nothing
      inside the group fixes the coercion's target, so Lean reports
      `invalid coercion notation, expected type is not known`.
    * `unascribed-lambda-projection` -- field notation on a lambda binder with
      no type ascription, e.g. `fun a => a.choose b`. Lean reports
      `Invalid field notation: Type of a is not known`.

    The "every top-level operand is coerced" condition is what makes this a
    screen rather than a `↑` grep: 54 of the 756 pinned mirror statements carry
    a coercion arrow and 51 of them elaborate fine, because a sibling operand of
    known type fixes the target.

**A screened row is FLAGGED, never dropped and never rewritten.** ADR-0615
forbids editing a preregistered `formal.statement`, and a row silently removed
from a draw is a partition change nobody recorded. The finding is a label plus
the exact text that produced it.

Library use:

    from lean_surface_screen import screen_statement
    findings = screen_statement(statement)     # [] means clean

Command line:

    python3 scripts/lean_surface_screen.py --statement '<lean text>'
    python3 scripts/lean_surface_screen.py --jsonl rows.jsonl
    python3 scripts/lean_surface_screen.py --facts

Exit status depends on the FINDING, not on the run completing: 0 when nothing
was flagged, 1 when something was, 2 when the input could not be read.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from dataclasses import dataclass

ROOT = pathlib.Path(__file__).resolve().parent.parent

#: Pretty-printer glyphs that cannot be read back. `⋯` U+22EF elides a proof
#: term, `✝` U+271D marks an inaccessible hygienic name, `…` U+2026 marks a
#: truncated subterm. Kept identical to `check-dispatchable-frontier.py`'s S6
#: set so the two tools never disagree about what a glyph is.
GLYPH_RE = re.compile(r"[⋯✝…]")

#: `fun <binders> =>` where no binder carries a `:` ascription.
UNASCRIBED_LAMBDA = re.compile(r"\bfun\s+((?:[A-Za-z_][A-Za-z0-9_'!?]*\s*)+)=>")

_IDENT_START = re.compile(r"[A-Za-z_]")
_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'!?.]*")


@dataclass(frozen=True)
class Finding:
    """One screen hit: its class, its signature, and the text that produced it."""

    screen_class: str
    signature: str
    evidence: str

    def as_dict(self) -> dict[str, str]:
        return {
            "class": self.screen_class,
            "signature": self.signature,
            "evidence": self.evidence,
        }


def _matching_open(text: str, close_index: int) -> int | None:
    """Index of the `(` matching the `)` at `close_index`, or None."""
    depth = 0
    for index in range(close_index, -1, -1):
        char = text[index]
        if char == ")":
            depth += 1
        elif char == "(":
            depth -= 1
            if depth == 0:
                return index
    return None


def _group_is_all_coerced(inner: str) -> bool:
    """Does every top-level operand of `inner` carry a `↑`?

    Returns False when the group has no coerced operand at all (there is nothing
    to be undetermined) and False as soon as one BARE operand is found, because
    a single operand of known type fixes the whole group. Numerals are neither:
    they are polymorphic and fix nothing.
    """
    coerced = 0
    index = 0
    length = len(inner)
    while index < length:
        char = inner[index]
        if char == "↑":
            coerced += 1
            index += 1
            # Consume the coerced atom, whether an identifier or a group.
            while index < length and inner[index].isspace():
                index += 1
            if index < length and inner[index] == "(":
                depth = 0
                while index < length:
                    if inner[index] == "(":
                        depth += 1
                    elif inner[index] == ")":
                        depth -= 1
                        if depth == 0:
                            index += 1
                            break
                    index += 1
            else:
                match = _IDENT.match(inner, index)
                index = match.end() if match else index + 1
            continue
        if char == "(":
            # A bare parenthesized group: whatever is inside is not coerced at
            # this level, so it can fix the type. Treat it as a bare operand.
            return False
        if _IDENT_START.match(char):
            return False
        index += 1
    return coerced > 0


def _coerced_projection_findings(statement: str) -> list[Finding]:
    findings = []
    for match in re.finditer(r"\)\s*\.[A-Za-z_]", statement):
        close_index = match.start()
        open_index = _matching_open(statement, close_index)
        if open_index is None:
            continue
        inner = statement[open_index + 1 : close_index]
        if _group_is_all_coerced(inner):
            findings.append(
                Finding(
                    "variable-block-dropped",
                    "coerced-projection",
                    statement[open_index : match.end()],
                )
            )
    return findings


def _unascribed_lambda_findings(statement: str) -> list[Finding]:
    findings = []
    for match in UNASCRIBED_LAMBDA.finditer(statement):
        binders = match.group(1).split()
        body = statement[match.end() :]
        for binder in binders:
            if re.search(rf"\b{re.escape(binder)}\.[A-Za-z_]", body):
                findings.append(
                    Finding(
                        "variable-block-dropped",
                        "unascribed-lambda-projection",
                        f"fun {' '.join(binders)} => … {binder}.…",
                    )
                )
                break
    return findings


def screen_statement(statement: str) -> list[Finding]:
    """Every screen finding for one surface statement, in a stable order.

    An empty list is the clean verdict. A statement is never modified.
    """
    collapsed = " ".join(statement.split())
    findings: list[Finding] = []
    for glyph in sorted(set(GLYPH_RE.findall(collapsed))):
        findings.append(Finding("elided-proof-glyph", "printer-glyph", glyph))
    findings.extend(_coerced_projection_findings(collapsed))
    findings.extend(_unascribed_lambda_findings(collapsed))
    return findings


# --------------------------------------------------------------------------
# Command line
# --------------------------------------------------------------------------


def _screen_rows(rows: list[tuple[str, str]]) -> int:
    flagged = 0
    for key, statement in rows:
        findings = screen_statement(statement)
        if not findings:
            continue
        flagged += 1
        for finding in findings:
            print(f"SCREEN|{key}|{finding.screen_class}|{finding.signature}|{finding.evidence}")
    print(f"SURFACE_SCREEN|rows={len(rows)}|flagged={flagged}")
    return 1 if flagged else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--statement", help="screen one statement given on the command line")
    group.add_argument(
        "--jsonl",
        type=pathlib.Path,
        help="screen a JSONL population carrying `fact_id` and `statement`",
    )
    group.add_argument(
        "--facts",
        action="store_true",
        help="screen every `F:ml430-*` fact's `formal.statement` in the ledger",
    )
    args = parser.parse_args()

    if args.statement is not None:
        return _screen_rows([("<argv>", args.statement)])
    if args.jsonl is not None:
        if not args.jsonl.exists():
            print(f"no such file: {args.jsonl}", file=sys.stderr)
            return 2
        rows = []
        for line in args.jsonl.read_text(encoding="utf-8").splitlines():
            if not line.strip():
                continue
            record = json.loads(line)
            rows.append((record["fact_id"], record["statement"]))
        if not rows:
            print(f"{args.jsonl} carries no rows", file=sys.stderr)
            return 2
        return _screen_rows(rows)

    facts = sorted((ROOT / "artifacts" / "facts").glob("F-ml430-*.json"))
    if not facts:
        print("no ml430 mirrors found", file=sys.stderr)
        return 2
    rows = []
    for path in facts:
        document = json.loads(path.read_text(encoding="utf-8"))
        statement = (document.get("formal") or {}).get("statement")
        if isinstance(statement, str):
            rows.append((document["id"], statement))
    return _screen_rows(rows)


if __name__ == "__main__":
    raise SystemExit(main())
