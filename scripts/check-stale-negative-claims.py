#!/usr/bin/env python3
"""Catch a doc comment claiming a kernel symbol is unproved when it is not.

Three incidents on 2026-08-22 shared one shape: a module doc's "what is *not*
here" section named a theorem as missing, while a `declare_<that name>`
function sat later in the same file (or the same module), landed and called
from the build sequence. One of the three shipped in three separate agent
briefs before anyone read the code that contradicted it. A fourth, matching
instance was found by hand in `int_prelude/gcd.rs` (2026-08-23): a comment
claiming `mul_neg` was "not declared as a public theorem" sitting in the same
`int_prelude` module as `sub::declare_mul_neg`, landed earlier in the build
sequence.

This script mechanizes the narrowest, most literal slice of that defect: a
comma/`and`-joined list of backtick-quoted bare identifiers immediately
followed by a present-tense negation ("is/are/was/were not proved/built/
declared/available", "is missing", "does not exist", or "not declared as a
public [theorem]") — where at least one named identifier matches a
`fn declare_<name>` defined anywhere in the same Rust module (a top-level
`foo.rs` plus its `foo/` directory, exactly Rust's own module boundary).

WHAT THIS DELIBERATELY DOES NOT CATCH, and why:

  * A claim phrased as a section HEADING ("## What is NOT here yet, and why")
    with the negation implied by the surrounding paragraph rather than stated
    as an adjacent predicate (incident 1's `modeq.rs` original wording was
    this shape). Matching on the heading requires deciding whether the
    paragraph's ARGUMENT still holds, not whether a name appears near a
    negation word — that is exactly the "surrounding prose" this repository's
    other tooling has already been burned by trusting. A heading-based trigger
    was tried and rejected: `rat_prelude/lattice.rs`'s "## What is deliberately
    not here" section is TRUE today and uses the identical heading.
  * A wrong HYPOTHESIS in a field doc (incident 2, `crt_unique`'s stale
    `0 < m*n`) — that is not a "not proved" claim at all, it is a wrong
    statement of one that IS proved, and needs comparing the doc's claimed
    type against the declaration's actual type, not a text pattern.
  * A dotted reference (`Rat.inv`, `Int.mul_neg`) practically never matches,
    even within the right module — `creal/inverse.rs` correctly says
    `Rat.inv`'s negative branch is unproved while `creal`'s own `declare_inv`
    (for `CReal.inv`, a different symbol) sits in the same module. The
    normalizer never strips a namespace prefix, so `Rat.inv` normalizes to
    `ratinv`, not `inv`, and does not collide with `declare_inv`'s `inv`. No
    namespace resolution is attempted; this is a side effect of comparing
    whole strings, not a claim of correctness for every dotted name.

So: this gate is a low-recall, aimed-for-high-precision net over the crispest
sub-shape of the defect, not a general "audit this doc" tool. See
`docs/refactor-2026-08/` (or ask the lane that wrote this) for the full
manual audit; this script exists to keep the crispest instance of it from
coming back unnoticed, not to replace rereading the code.
"""

from __future__ import annotations

import argparse
import os
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
DEFAULT_SRC = ROOT / "crates" / "axeyum-lean-kernel" / "src"

# A "test file" is excluded outright; the mixed-content case (a `mod tests {`
# block inside an otherwise-real file) is handled by truncation in
# `_strip_test_module`.
_TEST_FILE_RE = re.compile(r"(^|_)tests?\.rs$")

_DECLARE_FN_RE = re.compile(
    r"^\s*(?:pub(?:\([^)]*\))?\s+)?fn\s+declare_([A-Za-z0-9_]+)\s*\(",
    re.MULTILINE,
)

_COMMENT_LINE_RE = re.compile(r"^(\s*)(//!|///|//)(.*)$")

_BARE_NAME_INNER = r"[A-Za-z][A-Za-z0-9_.]*"
_BARE_NAME = rf"`{_BARE_NAME_INNER}`"
_NAME_LIST = rf"(?:{_BARE_NAME}(?:,\s+|\s+and\s+))*{_BARE_NAME}"
# The single source of truth for a backtick-quoted name -- used both to
# recognize a claim (`_CLAIM_RE`, via `_BARE_NAME`/`_NAME_LIST` above) and to
# EXTRACT the names out of a matched list below. Two independent copies of
# this pattern would let one drift from the other.
#
# Dotted names (`Rat.inv`) are deliberately let through here rather than
# filtered out: `_normalize` below does NOT strip a namespace prefix, so a
# dotted reference's normalized form keeps the whole string (`ratinv`, not
# `inv`) and essentially never equals a bare `declare_<suffix>`'s normalized
# name. That is what actually stops `creal/inverse.rs`'s correct claim about
# `Rat.inv` from colliding with `creal`'s own (unrelated) `declare_inv` for
# `CReal.inv` in the same module -- see `DottedNamesIgnored` in the test
# suite, which mutation-tests `_normalize` (not this regex) for exactly that.
_EXTRACT_NAME_RE = re.compile(rf"`({_BARE_NAME_INNER})`")
_TRIGGER = (
    r"(?:is|are|was|were)\s+not\s+(?:proved|built|declared|available)\b"
    r"|not\s+yet\s+(?:proved|built|declared)\b"
    r"|not\s+declared\s+as\s+(?:a\s+|an\s+)?public\b"
    r"|is\s+missing\b"
    r"|does\s+not\s+exist\b"
)
_CLAIM_RE = re.compile(rf"({_NAME_LIST})\.?\s+(?:{_TRIGGER})", re.IGNORECASE)

# Self-correcting language: a block documenting its OWN history ("an earlier
# pass left X unproved; it is declared below now") is not the defect this gate
# hunts. Matches must be resolvable against the CURRENT construction, so a
# block that already resolves itself is left alone rather than flagged and
# immediately explained away.
_SELF_CORRECTING_RE = re.compile(
    r"declared by\b"
    r"|is declared\b"
    r"|are declared\b"
    r"|now (?:proved|built|declared)\b"
    r"|an earlier (?:pass|version|draft)\b"
    r"|no longer\b"
    r"|used to say\b"
    r"|has since been\b"
    r"|see \[`declare_",
    re.IGNORECASE,
)

_MOD_TESTS_RE = re.compile(r"^\s*mod\s+tests\s*[{;]", re.MULTILINE)


def _strip_test_module(text: str) -> str:
    """Cut a file's content at its own `mod tests { ... }` (or `mod tests;`).

    Individual `#[cfg(test)]` functions elsewhere in a real file are left
    alone -- only the conventional trailing test module is truncated, which is
    the shape used throughout this crate (verified against
    `lean_export.rs`/`lean_pp.rs`/`quotient.rs`, all of which put `mod tests`
    at the end of the file after a `#[cfg(test)]` line).
    """
    m = _MOD_TESTS_RE.search(text)
    return text[: m.start()] if m else text


def module_key(path: pathlib.Path, src_root: pathlib.Path) -> str:
    """Group a file by Rust's own module boundary: `foo.rs` and `foo/*.rs`
    share a key, matching the crate's actual `mod foo { ... }` structure --
    the same boundary `sub::declare_mul_neg` and `gcd.rs`'s stale claim about
    `mul_neg` sit on either side of.
    """
    rel = path.relative_to(src_root)
    parts = rel.parts
    if len(parts) == 1:
        return parts[0][:-3] if parts[0].endswith(".rs") else parts[0]
    return parts[0]


def _normalize(name: str) -> str:
    return re.sub(r"[^a-z0-9]", "", name.lower())


def collect_declared(files: list[pathlib.Path]) -> dict[str, list[tuple[str, pathlib.Path]]]:
    """normalized declare_<name> suffix -> [(raw name, file), ...] for one module."""
    out: dict[str, list[tuple[str, pathlib.Path]]] = {}
    for f in files:
        text = _strip_test_module(f.read_text(encoding="utf-8"))
        for m in _DECLARE_FN_RE.finditer(text):
            raw = m.group(1)
            out.setdefault(_normalize(raw), []).append((raw, f))
    return out


def extract_comment_blocks(path: pathlib.Path, text: str) -> list[tuple[int, int, str]]:
    """[(start_line, end_line, joined_text)] for maximal runs of `//`/`///`/`//!`
    lines. Line numbers are 1-based and inclusive.
    """
    lines = text.split("\n")
    blocks: list[tuple[int, int, str]] = []
    cur_start: int | None = None
    cur_parts: list[str] = []
    for i, line in enumerate(lines, start=1):
        m = _COMMENT_LINE_RE.match(line)
        if m:
            body = m.group(3)
            if body.startswith(" "):
                body = body[1:]
            if cur_start is None:
                cur_start = i
            cur_parts.append(body)
        else:
            if cur_start is not None:
                blocks.append((cur_start, i - 1, " ".join(cur_parts)))
                cur_start = None
                cur_parts = []
    if cur_start is not None:
        blocks.append((cur_start, len(lines), " ".join(cur_parts)))
    return blocks


class Finding:
    def __init__(
        self,
        file: pathlib.Path,
        line_start: int,
        line_end: int,
        matched_text: str,
        bad_names: list[str],
        declare_hits: list[tuple[str, pathlib.Path]],
    ) -> None:
        self.file = file
        self.line_start = line_start
        self.line_end = line_end
        self.matched_text = matched_text
        self.bad_names = bad_names
        self.declare_hits = declare_hits

    def render(self) -> str:
        rel = os.path.relpath(self.file)
        decl_desc = ", ".join(
            f"{name} <- declare_{raw} ({os.path.relpath(d)})"
            for name, (raw, d) in zip(self.bad_names, self.declare_hits)
        )
        return (
            f"STALE_NEGATIVE_CLAIM|{rel}:{self.line_start}-{self.line_end}|"
            f'claim="{self.matched_text.strip()}"|contradicted_by={decl_desc}'
        )


def scan_module(files: list[pathlib.Path], declared: dict[str, list[tuple[str, pathlib.Path]]]) -> list[Finding]:
    findings: list[Finding] = []
    for f in files:
        text = _strip_test_module(f.read_text(encoding="utf-8"))
        for start, end, block_text in extract_comment_blocks(f, text):
            # Self-correction is checked over the WHOLE block, not a window
            # around the match: the corrective sentence ("... see
            # [`declare_mul_neg`] in `sub.rs`") routinely sits in the next
            # sentence of the same paragraph, well past a narrow lookahead,
            # and a block documenting its own history is exactly the case
            # this guard exists to leave alone.
            block_is_self_correcting = bool(_SELF_CORRECTING_RE.search(block_text))
            for claim_match in _CLAIM_RE.finditer(block_text):
                if block_is_self_correcting:
                    continue
                name_list = claim_match.group(1)
                names = _EXTRACT_NAME_RE.findall(name_list)
                bad_names = []
                declare_hits = []
                for name in names:
                    norm = _normalize(name)
                    if norm in declared:
                        bad_names.append(name)
                        declare_hits.append(declared[norm][0])
                if bad_names:
                    findings.append(
                        Finding(
                            f,
                            start,
                            end,
                            claim_match.group(0),
                            bad_names,
                            declare_hits,
                        )
                    )
    return findings


def run(src_root: pathlib.Path) -> list[Finding]:
    all_files = sorted(p for p in src_root.rglob("*.rs") if not _TEST_FILE_RE.search(p.name))
    modules: dict[str, list[pathlib.Path]] = {}
    for f in all_files:
        modules.setdefault(module_key(f, src_root), []).append(f)

    findings: list[Finding] = []
    for _key, files in sorted(modules.items()):
        declared = collect_declared(files)
        findings.extend(scan_module(files, declared))
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root",
        type=pathlib.Path,
        default=DEFAULT_SRC,
        help="source directory to scan (default: crates/axeyum-lean-kernel/src)",
    )
    args = parser.parse_args()

    src_root = args.root.resolve()
    if not src_root.is_dir():
        print(f"STALE_NEGATIVE_CLAIM_ERROR|no such directory: {src_root}", file=sys.stderr)
        return 2

    findings = run(src_root)
    if not findings:
        print(f"STALE_NEGATIVE_CLAIMS|ok|root={src_root}")
        return 0

    for finding in findings:
        print(finding.render())
    print(
        f"STALE_NEGATIVE_CLAIMS|FAILED|{len(findings)} claim(s) contradicted by a "
        "declare_ function in the same module. Fix the doc comment (never the "
        "proof) or, if the claim is genuinely about a different symbol, "
        "rephrase so it does not read as a list-then-negation."
    )
    return 1


if __name__ == "__main__":
    sys.exit(main())
