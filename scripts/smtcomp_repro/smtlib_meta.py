"""Extract the competition-relevant metadata from an SMT-LIB 2 benchmark:
the declared logic and the `(set-info :status ...)` ground truth.

Per the rules the scrambler strips `set-info`, but the *original* library file
carries `:status`, which is the expected status used for scoring (§7.1.2) and
for benchmark selection (§6). We read it from the on-disk benchmark.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Optional

from scoring import Status

_STATUS_RE = re.compile(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)")
_LOGIC_RE = re.compile(r"\(\s*set-logic\s+([A-Za-z0-9_+\-]+)\s*\)")
# Count top-level (assert (! ... :named f)) occurrences for the Unsat-Core N.
_NAMED_RE = re.compile(r":named\b")


@dataclass(frozen=True)
class BenchmarkMeta:
    path: str
    logic: Optional[str]
    status: Optional[Status]  # None == unknown/absent
    num_named: int


def _read(path: str) -> str:
    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        return fh.read()


def parse_status(text: str) -> Optional[Status]:
    m = _STATUS_RE.search(text)
    if not m:
        return None
    v = m.group(1)
    if v == "sat":
        return Status.SAT
    if v == "unsat":
        return Status.UNSAT
    return None  # 'unknown' -> None (treated as unknown status by scoring)


def parse_logic(text: str) -> Optional[str]:
    m = _LOGIC_RE.search(text)
    return m.group(1) if m else None


def read_meta(path: str) -> BenchmarkMeta:
    text = _read(path)
    return BenchmarkMeta(
        path=path,
        logic=parse_logic(text),
        status=parse_status(text),
        num_named=len(_NAMED_RE.findall(text)),
    )
