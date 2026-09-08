#!/usr/bin/env python3
"""Extract module-level numeric constants from Rust sources.

Shared by two consumers that must agree:

* `scripts/check-config-registry-staleness.py`, which asks git whether a
  registered justification predates the code it protects;
* `axeyum-solver`'s `config_registry` coverage test, which requires every
  constant this finds in a governed file to be either registered or exempted.

Both read the SOURCE, never a transcribed list, because a registry whose facts
were typed by hand records the maintainer's memory rather than the tree. The one
number this file is allowed to be wrong about is which constants are
*governing*; that judgement stays in the registry, where it is reviewable.

`#[cfg(test)]` modules are skipped by brace-depth tracking rather than by a
regex over the whole file: a `#[cfg(test)] mod tests` at the end of a 9,000-line
file otherwise swallows nothing, while a nested one swallows too much.
"""

from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

# `const NAME: <numeric type> = <literal>;`, module level or inside an impl.
CONST_RE = re.compile(
    r"^\s*(?:pub(?:\([^)]*\))?\s+)?const\s+"
    r"(?P<name>[A-Z][A-Z0-9_]*)\s*:\s*"
    r"(?P<ty>usize|u8|u16|u32|u64|u128|i8|i16|i32|i64|i128|f32|f64|Duration|std::time::Duration)\s*="
    r"(?P<value>[^;]*);",
    re.MULTILINE,
)

CFG_TEST_RE = re.compile(r"^\s*#\[cfg\(test\)\]\s*$")


@dataclass(frozen=True)
class Const:
    name: str
    path: str
    line: int
    ty: str
    value: str


def _cfg_test_line_spans(lines: list[str]) -> list[tuple[int, int]]:
    """Half-open [start, end) line spans of every `#[cfg(test)]` item.

    Tracked by brace depth from the item's opening brace, so a nested module or
    a test function inside a real module is bounded correctly. A `#[cfg(test)]`
    on a `use` or a `const` (no brace before the next `;`) spans that item only.
    """
    spans: list[tuple[int, int]] = []
    i = 0
    while i < len(lines):
        if not CFG_TEST_RE.match(lines[i]):
            i += 1
            continue
        start = i
        # Walk to the item's first `{` or `;`, whichever comes first.
        j = i + 1
        depth = 0
        opened = False
        while j < len(lines):
            for ch in lines[j]:
                if ch == "{":
                    depth += 1
                    opened = True
                elif ch == "}":
                    depth -= 1
            if opened and depth <= 0:
                break
            if not opened and ";" in lines[j]:
                break
            j += 1
        spans.append((start, min(j + 1, len(lines))))
        i = j + 1
    return spans


def scan_file(path: Path, repo_root: Path) -> list[Const]:
    text = path.read_text(encoding="utf-8", errors="replace")
    lines = text.splitlines()
    skip = _cfg_test_line_spans(lines)

    def in_test(line_no: int) -> bool:
        return any(a <= line_no < b for a, b in skip)

    found: list[Const] = []
    for m in CONST_RE.finditer(text):
        line_no = text.count("\n", 0, m.start())
        if in_test(line_no):
            continue
        rel = path.relative_to(repo_root).as_posix()
        value = " ".join(m.group("value").split())
        found.append(Const(m.group("name"), rel, line_no + 1, m.group("ty"), value))
    return found


def main(argv: list[str]) -> int:
    repo_root = Path(__file__).resolve().parent.parent
    if len(argv) < 2:
        print("usage: config_registry_scan.py <file.rs> [file.rs ...]", file=sys.stderr)
        return 2
    total = 0
    for arg in argv[1:]:
        p = Path(arg)
        if not p.is_absolute():
            p = repo_root / p
        for c in scan_file(p, repo_root):
            print(f"{c.path}:{c.line}\t{c.name}\t{c.ty}\t{c.value}")
            total += 1
    print(f"# {total} constant(s)", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
