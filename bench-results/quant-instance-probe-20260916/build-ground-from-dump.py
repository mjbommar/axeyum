#!/usr/bin/env python3
"""QUANT-INSTANCE-PROBE step 4 (second arm): build the ground-only file from
OUR OWN admitted quantifier instances, instead of z3's.

    build-ground-from-dump.py <core.smt2> <dump.lastblock> <out.smt2>

`<dump.lastblock>` is the final `GROUNDDUMP begin .. end` block from
`AXEYUM_QGROUNDDUMP` (`qip-dump-admitted.sh` already isolates the LAST block
and nothing else). Each `GROUND {index} gen={g} {term}` row with `g >= 1` is
one of OUR OWN admitted quantifier instances (`qinst_egraph.rs`'s own
comment: "a source subterm (generation 0)" vs "one an admitted instance
introduced"); `g == 0` rows are the original ground assertions already in the
core file and are skipped here to avoid asserting them twice.

Same construction as `build-ground-only.py` otherwise: strip every quantified
`assert` from the original core, append the admitted-instance terms as
`(assert ...)`, and set the logic to `QF_UFLIA`. This is deliberately NOT
checked against z3 for completeness the way the z3-instance arm is -- this
arm's own question is whether OUR ground checker can refute OUR OWN admitted
set, not whether that set is a complete UFLIA refutation by some external
standard.
"""

from __future__ import annotations

import importlib.util
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
STRIP_SCRIPT = ROOT / "scripts" / "strip-quantified-assertions.py"
_spec = importlib.util.spec_from_file_location("strip_quantified_assertions", STRIP_SCRIPT)
assert _spec is not None and _spec.loader is not None
strip_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(strip_mod)

SET_LOGIC_RE = re.compile(r"\(set-logic\s+[A-Za-z_][A-Za-z0-9_]*\s*\)")
CHECK_SAT_RE = re.compile(r"\(check-sat\)")
GROUND_ROW_RE = re.compile(r"^GROUND\s+(\d+)\s+gen=(\d+)\s+(.*)$")


def admitted_terms(dump_text: str) -> list[str]:
    """Ordered, deduped list of gen>=1 term strings from one dump block."""
    seen: set[str] = set()
    out: list[str] = []
    for line in dump_text.splitlines():
        m = GROUND_ROW_RE.match(line)
        if not m:
            continue
        gen = int(m.group(2))
        if gen < 1:
            continue
        term = m.group(3).strip()
        if term and term not in seen:
            seen.add(term)
            out.append(term)
    return out


def build(original_text: str, dump_text: str) -> tuple[str, dict]:
    result = strip_mod.strip_file(original_text)
    terms = admitted_terms(dump_text)

    text = result.text
    if SET_LOGIC_RE.search(text):
        text = SET_LOGIC_RE.sub("(set-logic QF_UFLIA)", text, count=1)
    else:
        text = "(set-logic QF_UFLIA)\n" + text

    assert_block = "".join(f"(assert {t})\n" for t in terms)
    if CHECK_SAT_RE.search(text):
        text = CHECK_SAT_RE.sub(assert_block + "(check-sat)", text, count=1)
    else:
        text = text + assert_block + "(check-sat)\n"

    stats = {
        "quant_asserts_stripped": result.dropped,
        "ground_asserts_kept": result.kept,
        "admitted_instances_added": len(terms),
    }
    return text, stats


def main(argv: list) -> int:
    if len(argv) != 4:
        sys.stderr.write(__doc__ or "")
        return 2
    core_path, dump_path, out_path = argv[1], argv[2], argv[3]

    original = Path(core_path).read_text(encoding="utf-8", errors="replace")
    dump_text = Path(dump_path).read_text(encoding="utf-8", errors="replace")

    try:
        text, stats = build(original, dump_text)
    except ValueError as exc:
        sys.stderr.write(f"PARSE-FAIL {core_path}: {exc}\n")
        return 3

    if stats["quant_asserts_stripped"] == 0:
        sys.stderr.write(f"DEGENERATE {core_path}: no quantified assert to strip\n")
        return 3
    if stats["admitted_instances_added"] == 0:
        sys.stderr.write(
            f"DEGENERATE {core_path}: zero admitted (gen>=1) instances in the dump\n"
        )
        return 4

    Path(out_path).write_text(text, encoding="utf-8")
    print(
        "quant_stripped={quant_asserts_stripped} ground_kept={ground_asserts_kept} "
        "admitted_instances_added={admitted_instances_added}".format(**stats)
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
