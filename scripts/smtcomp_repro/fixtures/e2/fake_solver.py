#!/usr/bin/env python3
"""Deterministic tiny solver used only by the E2 cgroup integration gate."""

from __future__ import annotations

import os
import sys
import time
from pathlib import Path


benchmark = Path(sys.argv[1])
marker = sys.argv[2] if len(sys.argv) > 2 else os.environ.get("AXEYUM_SMTCOMP_E2_SOLVER_MARKER")
if marker:
    Path(marker).write_text(f"{os.getpid()}\n", encoding="ascii")
text = benchmark.read_text(encoding="utf-8")
if "EXPECT_UNSAT" in text:
    print("unsat", flush=True)
else:
    print("sat", flush=True)
if "SLEEP_AFTER_VERDICT" in text:
    time.sleep(60)
else:
    time.sleep(0.05)
