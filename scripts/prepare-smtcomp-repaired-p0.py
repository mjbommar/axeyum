#!/usr/bin/env python3
"""Preparation-only entry point for the preregistered repaired P0."""

from __future__ import annotations

import sys
from pathlib import Path

SMTCOMP = Path(__file__).resolve().parent / "smtcomp_repro"
sys.path.insert(0, str(SMTCOMP))

from p0_prepare import main  # noqa: E402


if __name__ == "__main__":
    raise SystemExit(main())
