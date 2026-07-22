#!/usr/bin/env python3
"""Deterministic six-case solver for the E3 multi-host loss/retry gate."""

from __future__ import annotations

import os
import sys
import time
from pathlib import Path


benchmark = Path(sys.argv[1])
if len(sys.argv) > 2:
    marker_root = Path(sys.argv[2])
    marker_root.mkdir(parents=True, exist_ok=True)
    marker = marker_root / f"{benchmark.name}.marker"
    marker.write_text(f"{os.getpid()}\n", encoding="ascii")
text = benchmark.read_text(encoding="utf-8")
print("unsat" if "EXPECT_UNSAT" in text else "sat", flush=True)
time.sleep(5 if "SLEEP_AFTER_VERDICT" in text else 0.05)
