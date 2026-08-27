#!/usr/bin/env python3
"""Fail when a test reaches a deep-recursion prelude/model build without an
`on_a_deep_stack` guard anywhere on its local call path.

# The failure this exists to convert

`artifacts/kernel-stack-envelope.tsv` (ADR-0584) measured that `creal` needs
**exactly** the default 2 MiB `#[test]` thread stack in a debug build -- there
was never any margin, so every new declaration spends into a deficit. Three
modules crossed that line reactively in one session (`creal_tests.rs`,
`creal_model_tests.rs`, `prelude_cache_tests.rs`), each fixed only after it
SIGABRTed a debug test run. `crate::on_a_deep_stack` (`src/stack.rs`) is the
one shared fix; this script is the guard that a NEW `#[test]` calling one of
the deep-build functions cannot land unprotected and repeat the pattern a
fourth time.

# Method

For each `#[test] fn NAME`, walk the LOCAL (same-file) call graph reachable
from its body. A function body that textually contains `on_a_deep_stack` is
treated as protected -- everything nested inside it (a closure argument, or a
`_body` function it names) runs on the spawned deep-stack thread, so the walk
does not need to look inside it. A body that calls one of the TARGET
functions before any `on_a_deep_stack` is reached is a violation.

This is a static, same-file, textual analysis -- not a borrow-checker-grade
call graph. It deliberately does not chase calls across `crate::`/module
paths beyond matching the target function's own name, and a test that reaches
a target only through a function defined in ANOTHER file will not be
analysed. Given every real call site so far sits in the same file as its
`#[test]`, this is the cheap check that catches the actual regression shape;
it is not a substitute for `scripts/check-kernel-stack-envelope.sh`, which
independently re-measures the stack requirement itself.

Exit status is the answer: 0 means every `#[test]` reaching a target function
does so through a body containing `on_a_deep_stack`; 1 names the ones that
do not.
"""

from __future__ import annotations

import os
import re
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
# Overridable so `scripts/tests/test-deep-stack-call-sites.sh` can point this
# at a scratch copy carrying a deliberately unwrapped call site, without
# mutating a tracked file that every other lane compiles from.
SEARCH_ROOT = Path(
    os.environ.get(
        "AXEYUM_DEEP_STACK_SEARCH_ROOT",
        str(REPO_ROOT / "crates" / "axeyum-lean-kernel" / "src"),
    )
)

# Every function whose build cost is deep enough to need a protected stack --
# see artifacts/kernel-stack-envelope.tsv. `build_creal_prelude_uncached` is
# included because `prelude_cache_tests.rs` calls it directly, bypassing the
# process-wide template that would otherwise make the build free.
TARGET_FNS = frozenset(
    {
        "build_creal_prelude",
        "build_creal_prelude_uncached",
        "build_complex_prelude",
        "build_cpoint_prelude",
        "build_creal_model_of_arith",
    }
)

FN_DEF_RE = re.compile(r"\bfn\s+([A-Za-z_][A-Za-z0-9_]*)\s*(?:<[^>]*>)?\s*\(")
TEST_ATTR_RE = re.compile(r"#\[test\]")
CALL_RE = re.compile(r"\b([A-Za-z_][A-Za-z0-9_]*)\s*\(")


def find_matching_brace(text: str, open_idx: int) -> int:
    """Index of the `{` at `open_idx`'s matching `}`, by naive char counting.

    Rust source can carry unbalanced braces inside string/char literals or
    comments; this codebase's function bodies do not lean on that, and a
    false imbalance would show up immediately as a `RuntimeError` here rather
    than a silent wrong answer.
    """
    depth = 0
    i = open_idx
    n = len(text)
    while i < n:
        c = text[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise RuntimeError(f"unbalanced braces starting at byte {open_idx}")


def extract_functions(text: str) -> dict[str, str]:
    """Map every `fn NAME(...) { ... }` in `text` to its body (braces incl.).

    Last definition of a name wins on a collision, which cannot happen for a
    correctly-compiling file (item names are unique per scope) closely enough
    for this analysis -- we only need SOME body to walk, not a fully scoped
    resolver.
    """
    functions: dict[str, str] = {}
    for m in FN_DEF_RE.finditer(text):
        name = m.group(1)
        brace_start = text.find("{", m.end() - 1)
        if brace_start == -1:
            continue
        # A `fn foo(...);` trait/decl signature with no body -- skip.
        semicolon = text.find(";", m.end() - 1)
        if semicolon != -1 and (brace_start == -1 or semicolon < brace_start):
            continue
        try:
            close = find_matching_brace(text, brace_start)
        except RuntimeError:
            continue
        functions[name] = text[brace_start : close + 1]
    return functions


def find_test_roots(text: str) -> list[str]:
    """Every function name immediately introduced by a `#[test]` attribute."""
    roots = []
    for m in TEST_ATTR_RE.finditer(text):
        # Skip forward over any other attributes (`#[should_panic(...)]`, …)
        # to the next `fn NAME`.
        fn_match = FN_DEF_RE.search(text, m.end())
        if fn_match is None:
            continue
        # Reject if a `fn` from some unrelated, much later item was matched
        # because of a stray attribute soup; bound the search window.
        if fn_match.start() - m.end() > 2000:
            continue
        roots.append(fn_match.group(1))
    return roots


def reaches_target_unprotected(
    name: str,
    functions: dict[str, str],
    visited: set[str],
) -> str | None:
    """Return the target fn name reached unprotected from `name`, or None."""
    if name in visited:
        return None
    visited.add(name)
    body = functions.get(name)
    if body is None:
        return None
    if "on_a_deep_stack" in body:
        return None
    for call_m in CALL_RE.finditer(body):
        callee = call_m.group(1)
        if callee == name:
            continue
        if callee in TARGET_FNS:
            return callee
        if callee in functions:
            found = reaches_target_unprotected(callee, functions, visited)
            if found is not None:
                return found
    return None


def check_file(path: Path) -> list[tuple[str, str]]:
    """[(test_fn_name, target_fn_name), ...] violations in `path`."""
    text = path.read_text(encoding="utf-8")
    if "on_a_deep_stack" not in text and not any(t in text for t in TARGET_FNS):
        return []
    functions = extract_functions(text)
    violations = []
    for root in find_test_roots(text):
        found = reaches_target_unprotected(root, functions, set())
        if found is not None:
            violations.append((root, found))
    return violations


def main() -> int:
    if not SEARCH_ROOT.is_dir():
        print(f"check-deep-stack-call-sites: no such directory {SEARCH_ROOT}", file=sys.stderr)
        return 2

    total_violations = 0
    files_scanned = 0
    for path in sorted(SEARCH_ROOT.rglob("*.rs")):
        files_scanned += 1
        violations = check_file(path)
        for test_name, target_name in violations:
            total_violations += 1
            try:
                rel = path.relative_to(REPO_ROOT)
            except ValueError:
                rel = path
            print(
                f"UNPROTECTED: {rel}: #[test] fn {test_name}() reaches "
                f"{target_name}() without an on_a_deep_stack guard on the path"
            )

    if files_scanned == 0:
        print("check-deep-stack-call-sites: scanned zero files -- refusing to pass vacuously", file=sys.stderr)
        return 2

    if total_violations:
        print(
            f"check-deep-stack-call-sites: {total_violations} unprotected deep-stack "
            f"call site(s) across {files_scanned} files scanned",
            file=sys.stderr,
        )
        return 1

    print(f"check-deep-stack-call-sites: OK ({files_scanned} files scanned, 0 unprotected sites)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
