#!/usr/bin/env python3
"""Strip every `assert` whose body contains a `forall`/`exists` binder.

    strip-quantified-assertions.py [--examples] <in.smt2> <out.smt2>

DT-GROUND-PROBE (ADR-2114 follow-on). ADR-2114 measured that z3 refutes 44 of
55 `AUFDTLIRA` reference-minimal cores and 39 of 79 undecided originals with
BOTH quantifier engines off (`smt.ematching=false smt.mbqi=false`): the
quantified assertions in those files are inert and the GROUND part alone is
unsat. This tool produces that ground part, so our own quantifier-free ladder
can be measured against it directly, without the quantifier rungs (MBQI /
e-matching) ever entering the question.

Every top-level form is preserved BYTE-VERBATIM -- original whitespace,
comments and formatting included -- except a top-level `(assert ...)` whose
body contains a `(forall ...)` / `(exists ...)` form at any depth, which is
dropped whole. Nothing else is reformatted, reordered or reparsed into a
different textual shape: this tool only decides, per top-level form, KEEP or
DROP, and slices the original bytes accordingly. That is a stronger
preservation guarantee than `bench-results/dt-quant-trace-20260915/repro/
degroundify.py`, which re-serializes every form through its own writer
(collapsing original whitespace); this script exists because the next lane
needs to diff the stripped file against the original.

Tokenizing and parsing are both ITERATIVE, never recursive: this corpus nests
`let` hundreds deep with shared bodies, and CLAUDE.md records a recursive
`let`-expander reaching 63.4 GB and taking a host down on these same files.
Nothing here substitutes or expands a `let` binding; it is walked in place
like every other list, which is enough to detect a quantifier reachable from
it and costs nothing beyond the size of the file itself.

`forall`/`exists` are SMT-LIB reserved words (SMT-LIB-LIB 2.6 sec 3.1): no
`let`/`declare-fun`/binder name can legally BE one, quoted or not, so a
genuinely HIDDEN binder -- one only reachable by resolving a bound name that
happens to shadow the keyword -- is not a shape valid SMT-LIB can produce.
The detector here is still structural rather than a token/substring scan (it
requires `forall`/`exists` to be the operator position of a list, i.e. an
actual binder FORM, not merely a token that appears somewhere), so a quoted
symbol `|forall|` used as ordinary data is never mistaken for one -- the
tokenizer keeps a quoted symbol's pipes as part of one token, which can never
equal the bare string `forall`.

`(set-logic ...)` is left UNCHANGED. `crates/axeyum-smtlib/src/parse.rs`
records `script.logic` but nothing in `axeyum-solver`'s dispatcher
(`crates/axeyum-solver/src/auto.rs`) or `smtcomp_cli` branches on it --
dispatch is by the CONSTRUCTS a query actually contains, not by the declared
logic string -- so a stripped `AUFDTLIRA` file with no quantifier left in it
is accepted exactly as read, unrewritten. This is the documented fallback
("if it accepts the original logic with no quantifiers present, leave it"),
exercised rather than assumed: see `scripts/tests/
test_strip_quantified_assertions.py`'s `set-logic is left untouched` case.

Exit status depends on the finding: an unparseable file, or a split that
drops every assertion (nothing left to check) or drops none (nothing was
stripped, so the run measures the original file under another name), is
reported on stderr and this exits non-zero. A tool that cannot fail here is
worse than no tool (CLAUDE.md, evidence-and-checker discipline).
"""

from __future__ import annotations

import sys
from typing import List, Sequence, Tuple


class Sym(str):
    """A symbol, distinguished from a plain `str` only by type -- kept for
    parity with `dtshape.py`'s convention (this script does not itself need
    the distinction beyond tokenizing a quoted symbol as one whole token)."""

    __slots__ = ()


def tokenize_with_pos(text: str) -> List[Tuple[str, int, int]]:
    """Iterative tokenizer returning `(token, start, end)` triples, `end`
    exclusive. Comments and whitespace are consumed and produce no token --
    callers that need them back read the gaps between token spans out of
    `text` directly, which is what `strip_file` does."""
    out: List[Tuple[str, int, int]] = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == ";":
            j = text.find("\n", i)
            i = n if j < 0 else j + 1
        elif c in " \t\r\n":
            i += 1
        elif c in "()":
            out.append((c, i, i + 1))
            i += 1
        elif c == "|":
            j = text.find("|", i + 1)
            if j < 0:
                raise ValueError("unterminated |quoted| symbol")
            out.append((Sym(text[i : j + 1]), i, j + 1))
            i = j + 1
        elif c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            out.append((Sym(text[i : j + 1]), i, j + 1))
            i = j + 1
        else:
            j = i
            while j < n and text[j] not in " \t\r\n()|;\"":
                j += 1
            out.append((Sym(text[i:j]), i, j))
            i = j
    return out


def parse_tokens(tokens: Sequence[str]) -> list:
    """Nested-list s-expression tree from a bare (position-free) token
    sequence. Iterative, matching `dtshape.py`'s `parse`: these bodies nest
    hundreds deep and a recursive descent dies on Python's recursion limit
    before it dies on the input."""
    stack: List[list] = []
    forms: list = []
    for t in tokens:
        if t == "(":
            stack.append([])
        elif t == ")":
            if not stack:
                raise ValueError("unbalanced )")
            done = stack.pop()
            if stack:
                stack[-1].append(done)
            else:
                forms.append(done)
        else:
            if stack:
                stack[-1].append(t)
            else:
                forms.append(t)
    if stack:
        raise ValueError("unbalanced ( at end of form")
    return forms


def has_quant_binder(node) -> bool:
    """True iff `node` contains a `(forall ...)` / `(exists ...)` FORM at any
    depth, including inside a `let`'s bound VALUE -- this walks every list
    unconditionally rather than special-casing `let`, so a quantifier nested
    inside a binding's value is found the same as one in the body."""
    stack = [node]
    while stack:
        n = stack.pop()
        if isinstance(n, list):
            if n and not isinstance(n[0], list) and str(n[0]) in ("forall", "exists"):
                return True
            stack.extend(n)
    return False


class StripResult:
    def __init__(
        self,
        text: str,
        kept: int,
        dropped: int,
        kept_spans: List[Tuple[int, int]],
        dropped_spans: List[Tuple[int, int]],
    ) -> None:
        self.text = text
        self.kept = kept
        self.dropped = dropped
        self.kept_spans = kept_spans
        self.dropped_spans = dropped_spans


def strip_file(text: str) -> StripResult:
    """Split `text` into top-level forms and drop every `assert` whose body
    contains a quantifier binder. Returns the rewritten text plus counts and
    the ORIGINAL-file byte spans of one representative kept/dropped assert
    each, so a caller can show its positive control without re-scanning."""
    tokens = tokenize_with_pos(text)
    depth = 0
    start = None
    form_tokens: List[str] = []
    spans: List[Tuple[int, int, List[str]]] = []
    for tok, s, e in tokens:
        if tok == "(":
            if depth == 0:
                start = s
                form_tokens = []
            depth += 1
            form_tokens.append(tok)
        elif tok == ")":
            depth -= 1
            if depth < 0:
                raise ValueError("unbalanced ) in input")
            form_tokens.append(tok)
            if depth == 0:
                assert start is not None
                spans.append((start, e, form_tokens))
                start = None
                form_tokens = []
        else:
            if depth == 0:
                # A bare top-level atom is not valid SMT-LIB, but keep it
                # verbatim as its own one-token span rather than raising on
                # it -- this tool's job is stripping quantified asserts, not
                # validating the rest of the grammar.
                spans.append((s, e, [tok]))
            else:
                form_tokens.append(tok)
    if depth != 0:
        raise ValueError("unbalanced ( at end of file")

    out: List[str] = []
    cursor = 0
    kept = 0
    dropped = 0
    kept_spans: List[Tuple[int, int]] = []
    dropped_spans: List[Tuple[int, int]] = []
    for fstart, fend, ftoks in spans:
        out.append(text[cursor:fstart])
        body = parse_tokens(ftoks)
        form = body[0] if body else None
        is_assert = (
            isinstance(form, list)
            and form
            and not isinstance(form[0], list)
            and str(form[0]) == "assert"
        )
        drop = is_assert and len(form) >= 2 and has_quant_binder(form[1])
        if drop:
            dropped += 1
            dropped_spans.append((fstart, fend))
        else:
            if is_assert:
                kept += 1
                kept_spans.append((fstart, fend))
            out.append(text[fstart:fend])
        cursor = fend
    out.append(text[cursor:])
    return StripResult("".join(out), kept, dropped, kept_spans, dropped_spans)


def _truncate(s: str, n: int = 200) -> str:
    s = " ".join(s.split())
    return s if len(s) <= n else s[: n - 3] + "..."


def main(argv: Sequence[str]) -> int:
    args = list(argv[1:])
    show_examples = "--examples" in args
    args = [a for a in args if a != "--examples"]
    if len(args) != 2:
        sys.stderr.write(__doc__ or "")
        return 2
    src, dst = args
    try:
        with open(src, "r", encoding="utf-8", errors="replace") as fh:
            text = fh.read()
    except OSError as exc:
        sys.stderr.write(f"strip-quantified-assertions: cannot read {src}: {exc}\n")
        return 2

    try:
        result = strip_file(text)
    except ValueError as exc:
        sys.stderr.write(f"PARSE-FAIL {src}: {exc}\n")
        return 3

    with open(dst, "w", encoding="utf-8") as fh:
        fh.write(result.text)

    total = result.kept + result.dropped
    print(
        f"asserts_total={total} asserts_kept={result.kept} "
        f"asserts_dropped={result.dropped}"
    )

    if show_examples:
        if result.dropped_spans:
            s, e = result.dropped_spans[0]
            print(f"REMOVED (dropped, has a quantifier): {_truncate(text[s:e])}")
        else:
            print("REMOVED: (none -- no assert contained a quantifier binder)")
        if result.kept_spans:
            s, e = result.kept_spans[0]
            print(f"KEPT    (ground, no quantifier):     {_truncate(text[s:e])}")
        else:
            print("KEPT: (none -- every assert was dropped)")

    # A checker/tool that cannot fail is worse than none: a degenerate split
    # -- nothing dropped (nothing was stripped) or nothing kept (nothing left
    # to check) -- is reported and this exits non-zero rather than writing a
    # file that silently measures the wrong thing.
    if result.dropped == 0:
        sys.stderr.write(
            f"DEGENERATE: {src} has no quantified assert -- output is the "
            "original file under a new name\n"
        )
        return 4
    if result.kept == 0 and total > 0:
        sys.stderr.write(
            f"DEGENERATE: {src} -- every assert was quantified, nothing "
            "ground remains\n"
        )
        return 4
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
