#!/usr/bin/env python3
"""Synthetic child modes for the preregistered TL0.7.2 process controls.

This file is not a Lean, CTest, exporter, or Axeyum workload.  Its exact bytes
are part of the cooperative evidence tuple used by the process adapter.
"""

from __future__ import annotations

import errno
import mmap
import os
import resource
import signal
import subprocess
import sys
import time


def _require_argument_count(expected: int) -> None:
    if len(sys.argv) != expected:
        raise SystemExit(64)


def _linger() -> None:
    signal.signal(signal.SIGTERM, signal.SIG_IGN)
    while True:
        time.sleep(60)


def main() -> int:
    if len(sys.argv) < 2:
        return 64
    mode = sys.argv[1]
    if mode == "exit-zero":
        _require_argument_count(2)
        sys.stdout.buffer.write(b"AXEYUM_TL0_7_2_EXIT_ZERO_STDOUT_V1\n")
        sys.stderr.buffer.write(b"AXEYUM_TL0_7_2_EXIT_ZERO_STDERR_V1\n")
        return 0
    if mode == "exit-seven":
        _require_argument_count(2)
        sys.stderr.buffer.write(b"AXEYUM_TL0_7_2_EXIT_SEVEN_V1\n")
        return 7
    if mode == "self-sigterm":
        _require_argument_count(2)
        sys.stderr.buffer.write(b"AXEYUM_TL0_7_2_SELF_SIGTERM_V1\n")
        sys.stderr.buffer.flush()
        os.kill(os.getpid(), signal.SIGTERM)
        return 70
    if mode == "linger-child":
        _require_argument_count(2)
        _linger()
    if mode == "timeout-tree":
        _require_argument_count(2)
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        child = subprocess.Popen(
            [os.path.realpath(sys.executable), os.path.realpath(__file__), "linger-child"],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            close_fds=True,
        )
        sys.stderr.write(f"AXEYUM_TL0_7_2_DESCENDANT_PID_V1={child.pid}\n")
        sys.stderr.flush()
        _linger()
    if mode == "memory-limit":
        _require_argument_count(5)
        expected_limit = int(sys.argv[2])
        mapping_bytes = int(sys.argv[3])
        marker = sys.argv[4]
        actual_soft, actual_hard = resource.getrlimit(resource.RLIMIT_AS)
        if (actual_soft, actual_hard) != (expected_limit, expected_limit):
            sys.stderr.write(
                "AXEYUM_TL0_7_2_MEMORY_CONTROL_INVALID_V1|"
                f"soft={actual_soft}|hard={actual_hard}\n"
            )
            return 88
        try:
            mapping = mmap.mmap(
                -1,
                mapping_bytes,
                flags=mmap.MAP_PRIVATE | mmap.MAP_ANONYMOUS,
                prot=mmap.PROT_READ | mmap.PROT_WRITE,
            )
        except MemoryError:
            sys.stderr.write(marker + "\n")
            return 86
        except OSError as exc:
            if exc.errno == errno.ENOMEM:
                sys.stderr.write(marker + "\n")
                return 86
            sys.stderr.write(
                "AXEYUM_TL0_7_2_MEMORY_CONTROL_OSERROR_V1|"
                f"errno={exc.errno}\n"
            )
            return 89
        else:
            mapping.close()
            sys.stderr.write("AXEYUM_TL0_7_2_MEMORY_MAPPING_UNEXPECTEDLY_SUCCEEDED_V1\n")
            return 87
    return 64


if __name__ == "__main__":
    raise SystemExit(main())
