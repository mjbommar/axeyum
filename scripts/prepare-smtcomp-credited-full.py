#!/usr/bin/env python3
"""No-launch entry point for credited SMT-COMP full preparation."""

from __future__ import annotations

import sys
from pathlib import Path

SMTCOMP = Path(__file__).resolve().parent / "smtcomp_repro"
sys.path.insert(0, str(SMTCOMP))

from full_capture import main  # noqa: E402


if __name__ == "__main__":
    raise SystemExit(main())
