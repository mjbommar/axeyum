#!/usr/bin/env python3
"""Child process used only by the ADR-0344 filesystem kill fixtures."""

from __future__ import annotations

import argparse
import json
import os
import signal
from pathlib import Path

from resume_fs import atomic_install_json


def durable_marker(path: Path, phase: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o444)
    try:
        os.write(fd, (phase + "\n").encode("utf-8"))
        os.fsync(fd)
    finally:
        os.close(fd)
    directory = os.open(path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(directory)
    finally:
        os.close(directory)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--filename", required=True)
    parser.add_argument("--payload", type=Path, required=True)
    parser.add_argument("--stop-phase", required=True)
    parser.add_argument("--marker", type=Path, required=True)
    args = parser.parse_args()
    value = json.loads(args.payload.read_text(encoding="utf-8"))

    def stop(phase: str) -> None:
        if phase == args.stop_phase:
            durable_marker(args.marker, phase)
            signal.pause()

    atomic_install_json(args.directory, args.filename, value, phase_hook=stop)
    raise RuntimeError(f"stop phase was not observed: {args.stop_phase}")


if __name__ == "__main__":
    raise SystemExit(main())
