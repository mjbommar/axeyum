"""Tests for benchmark selection (selection.py) — SMT-COMP 2026 §6."""

from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from selection import division_cap, family_of, select_division  # noqa: E402


def test_division_cap_formula():
    # §6 case 4a-4d
    assert division_cap(300) == 300
    assert division_cap(250) == 250
    assert division_cap(600) == 300
    assert division_cap(450) == 300
    assert division_cap(1000) == 500
    assert division_cap(800) == 400
    assert division_cap(2000) == 500 + 100  # 500 + (1000)/10
    assert division_cap(11000) == 500 + 1000


def test_family_of():
    assert family_of("/c/QF_BV/brummayer/x.smt2", "/c") == "QF_BV/brummayer"


def test_no_cap_when_under_limit():
    benches = [f"/c/QF_BV/fam{i%3}/b{i}.smt2" for i in range(50)]
    res = select_division(benches, "/c", seed=1)
    assert len(res.selected) == 50  # n <= 300 -> all
    assert res.cap == 50


def test_cap_and_family_coverage_deterministic():
    # 1200 benchmarks across 40 families -> cap = 500 + (1200-1000)/10 = 520.
    benches = [f"/c/QF_BV/fam{i%40:02d}/b{i:04d}.smt2" for i in range(1200)]
    res1 = select_division(benches, "/c", seed=42)
    res2 = select_division(benches, "/c", seed=42)
    assert res1.cap == 520
    assert len(res1.selected) == 520
    # every family represented (new-family guarantee) since 40 << 520
    fams = {family_of(b, "/c") for b in res1.selected}
    assert len(fams) == 40
    # deterministic under a fixed seed
    assert res1.selected == res2.selected
    # a different seed changes the fill (not necessarily the family reps)
    res3 = select_division(benches, "/c", seed=7)
    assert res3.selected != res1.selected


def test_easy_filter_removes():
    benches = [f"/c/QF_BV/fam/b{i}.smt2" for i in range(10)]
    res = select_division(benches, "/c", seed=1, is_easy=lambda b: b.endswith("b0.smt2"))
    assert all(not b.endswith("b0.smt2") for b in res.selected)
    assert len(res.selected) == 9


def _run_all():
    g = globals()
    tests = sorted(k for k in g if k.startswith("test_"))
    failed = 0
    for name in tests:
        try:
            g[name]()
            print(f"PASS {name}")
        except Exception as exc:  # noqa: BLE001
            failed += 1
            print(f"FAIL {name}: {exc!r}")
    print(f"\n{len(tests) - failed}/{len(tests)} passed")
    return failed


if __name__ == "__main__":
    sys.exit(1 if _run_all() else 0)
