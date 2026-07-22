#!/usr/bin/env python3
"""Regenerate the SMT-COMP reproduction charts from the committed JSON.

Reads (same directory):
  inventory.json          -- axeyum complete inventory over the 228 NAS files
  head_to_head_qfbv.json  -- axeyum vs cvc5 vs bitwuzla, QF_BV, 24-benchmark slice
Writes:
  inventory_decide_by_logic.png
  head_to_head_qfbv.png

Deterministic (no network, fixed order). Run:  python3 chart.py
"""
from __future__ import annotations

import json
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
INK = "#1b2733"
GRID = "#d9e0e6"
GOOD = "#2f8f5b"   # green
MID = "#c9a227"    # amber
WEAK = "#c0563b"   # red
BAR = "#3b6ea5"    # blue


def _band(pct: float) -> str:
    return GOOD if pct >= 80 else (MID if pct >= 40 else WEAK)


def inventory_chart() -> None:
    inv = json.load(open(os.path.join(HERE, "inventory.json")))
    rows = []
    for logic, c in inv["per_logic"].items():
        N = c.get("total", 0)
        correct = c.get("decided_correct", 0)
        rows.append((logic, N, correct, 100.0 * correct / N if N else 0.0))
    # sort by decide% desc, then N desc
    rows.sort(key=lambda r: (-r[3], -r[1]))
    logics = [r[0] for r in rows]
    pcts = [r[3] for r in rows]
    Ns = [r[1] for r in rows]
    corrects = [r[2] for r in rows]

    fig, ax = plt.subplots(figsize=(9, 8))
    y = range(len(logics))
    ax.barh(list(y), pcts, color=[_band(p) for p in pcts], height=0.72,
            edgecolor="white", linewidth=0.6, zorder=3)
    for i, (p, n, cor) in enumerate(zip(pcts, Ns, corrects)):
        ax.text(min(p + 1.5, 101), i, f"{p:.0f}%  ({cor}/{n})",
                va="center", ha="left", fontsize=8.5, color=INK, zorder=4)
    ax.set_yticks(list(y))
    ax.set_yticklabels(logics, fontsize=9, color=INK)
    ax.invert_yaxis()
    ax.set_xlim(0, 118)
    ax.set_xlabel("decide rate  (sat/unsat correctly returned, % of division)",
                  fontsize=9.5, color=INK)
    agg = inv["aggregate"]
    N = agg["total"]
    ax.set_title(
        f"axeyum complete inventory — {N} SMT-LIB benchmarks, per logic\n"
        f"{agg['decided_correct']} decided ({100*agg['decided_correct']/N:.0f}%),  "
        f"{agg['declined']} declined (honest unknown),  "
        f"{agg['WRONG']} WRONG",
        fontsize=11, color=INK, loc="left", pad=12)
    ax.axvline(80, color=GOOD, lw=0.8, ls=":", alpha=0.6, zorder=1)
    ax.axvline(40, color=MID, lw=0.8, ls=":", alpha=0.6, zorder=1)
    ax.grid(axis="x", color=GRID, lw=0.8, zorder=0)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    ax.text(0.995, -0.075,
            "0 wrong answers across all 228 — soundness holds.  "
            "s4 (16c/110GB), 120s/problem ceiling, 2026-07-21.",
            transform=ax.transAxes, ha="right", va="top", fontsize=7.5,
            color="#5a6b78")
    fig.tight_layout()
    out = os.path.join(HERE, "inventory_decide_by_logic.png")
    fig.savefig(out, dpi=150, bbox_inches="tight")
    print("wrote", out)


def head_to_head_chart() -> None:
    rep = json.load(open(os.path.join(HERE, "head_to_head_qfbv.json")))
    div = rep["divisions"]["QF_BV"]
    N = div["n_benchmarks"]
    solvers = div["ranking_par2"]  # already PAR-2 ordered
    solved = [div["solvers"][s]["parallel"]["n"] for s in solvers]
    par2 = [div["solvers"][s]["par2"]["wall"] for s in solvers]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(10, 4.2))
    palette = ["#2f8f5b", "#3b6ea5", "#7d5ba6"]
    c = palette[: len(solvers)]

    ax1.bar(solvers, solved, color=c, width=0.6, zorder=3, edgecolor="white")
    for i, v in enumerate(solved):
        ax1.text(i, v + 0.3, str(v), ha="center", fontsize=10, color=INK)
    ax1.set_ylim(0, N + 3)
    ax1.axhline(N, color="#5a6b78", lw=0.8, ls="--")
    ax1.text(len(solvers) - 0.5, N + 0.3, f"all {N}", ha="right", fontsize=8,
             color="#5a6b78")
    ax1.set_ylabel(f"benchmarks solved (of {N})", fontsize=9.5, color=INK)
    ax1.set_title("solved — all sound (0 wrong)", fontsize=10.5, color=INK)

    ax2.bar(solvers, par2, color=c, width=0.6, zorder=3, edgecolor="white")
    for i, v in enumerate(par2):
        ax2.text(i, v + max(par2) * 0.01, f"{v:.0f}", ha="center", fontsize=10,
                 color=INK)
    ax2.set_ylabel("PAR-2 wall time (s) — lower is faster", fontsize=9.5,
                   color=INK)
    ax2.set_title("speed (PAR-2, T=10s)", fontsize=10.5, color=INK)

    for ax in (ax1, ax2):
        ax.grid(axis="y", color=GRID, lw=0.8, zorder=0)
        for s in ("top", "right"):
            ax.spines[s].set_visible(False)
    fig.suptitle(
        "QF_BV head-to-head (24-benchmark SMT-LIB slice) — axeyum vs cvc5 vs bitwuzla",
        fontsize=11.5, color=INK, x=0.02, ha="left")
    fig.tight_layout(rect=(0, 0, 1, 0.96))
    out = os.path.join(HERE, "head_to_head_qfbv.png")
    fig.savefig(out, dpi=150, bbox_inches="tight")
    print("wrote", out)


if __name__ == "__main__":
    inventory_chart()
    head_to_head_chart()
