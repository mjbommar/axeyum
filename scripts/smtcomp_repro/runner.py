"""Resource-limited solver execution — a self-contained replica of the SMT-COMP
execution service (§5), faithful for a single-process solver.

The competition runs each (solver, benchmark) pair under BenchExec on a
dedicated node: a wall-clock limit `T`, a CPU limit `m*T` across `m` cores, and
a memory limit (~30 GB), measuring actual wall-clock time `aw` and CPU time `ac`
(§7.1). This module reproduces that measurement without BenchExec so it runs on
any of the s0..s7 nodes:

  * wall time  — monotonic clock delta around the process;
  * CPU time   — ru_utime + ru_stime from os.wait4 (a Rust solver is one
                 process, so this aggregates all its threads' CPU exactly);
  * mem limit  — RLIMIT_AS in a preexec hook (best-effort);
  * wall limit — a watchdog that kills the whole process group on timeout.

For maximal fidelity on a real competition rehearsal, a BenchExec `runexec`
backend can be swapped in (see `use_benchexec`); the default needs no deps.

The solver's stdout is parsed for the last sat/unsat/unknown token — the
non-incremental tracks emit exactly one verdict (§5, one `check-sat`).
"""

from __future__ import annotations

import os
import re
import resource
import signal
import subprocess
import time
from dataclasses import dataclass
from typing import Optional

from scoring import Status

_VERDICT_RE = re.compile(r"\b(unsat|sat|unknown)\b")


@dataclass(frozen=True)
class RunResult:
    """Raw measured outcome of one execution."""

    reported: Optional[Status]  # parsed verdict (None == no verdict emitted)
    wall_time: float  # aw, seconds
    cpu_time: float  # ac, seconds
    exit_code: Optional[int]
    timed_out: bool
    mem_exceeded: bool
    stdout: str
    stderr: str


def parse_verdict(stdout: str) -> Optional[Status]:
    """Return the LAST sat/unsat/unknown token in stdout, or None.

    'unsat' is matched before 'sat' by the alternation order so the substring in
    'unsat' is never misread as 'sat'."""
    last: Optional[Status] = None
    for m in _VERDICT_RE.finditer(stdout):
        tok = m.group(1)
        last = {"sat": Status.SAT, "unsat": Status.UNSAT, "unknown": Status.UNKNOWN}[tok]
    return last


def _preexec(mem_limit_bytes: Optional[int]):
    def hook() -> None:
        os.setpgrp()  # own process group so we can kill the whole tree
        if mem_limit_bytes is not None:
            try:
                resource.setrlimit(
                    resource.RLIMIT_AS, (mem_limit_bytes, mem_limit_bytes)
                )
            except (ValueError, OSError):
                pass

    return hook


def run_solver(
    cmd: list[str],
    *,
    wall_limit_s: float,
    mem_limit_bytes: Optional[int] = None,
    grace_s: float = 2.0,
) -> RunResult:
    """Execute `cmd`, enforcing wall/mem limits, measuring wall+CPU (§5, §7.1)."""
    start = time.monotonic()
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        preexec_fn=_preexec(mem_limit_bytes),
    )
    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=wall_limit_s)
    except subprocess.TimeoutExpired:
        timed_out = True
        # Kill the whole process group, then reap.
        try:
            os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            stdout, stderr = proc.communicate(timeout=grace_s)
        except subprocess.TimeoutExpired:
            proc.kill()
            stdout, stderr = proc.communicate()
    wall = time.monotonic() - start

    # CPU time of the child from rusage (utime+stime). Popen already reaped via
    # communicate(); fall back to 0 if unavailable.
    try:
        usage = resource.getrusage(resource.RUSAGE_CHILDREN)
        # RUSAGE_CHILDREN accumulates across all reaped children of THIS process,
        # so we snapshot deltas per-call in run_many; for a single call the
        # aggregate equals this child's usage when run in isolation.
        cpu = usage.ru_utime + usage.ru_stime
    except (ValueError, OSError):
        cpu = 0.0

    exit_code = proc.returncode
    mem_exceeded = exit_code is not None and exit_code < 0 and not timed_out
    reported = None if timed_out else parse_verdict(stdout or "")
    return RunResult(
        reported=reported,
        wall_time=wall,
        cpu_time=cpu,
        exit_code=exit_code,
        timed_out=timed_out,
        mem_exceeded=mem_exceeded,
        stdout=stdout or "",
        stderr=stderr or "",
    )


class CpuMeter:
    """Per-execution CPU accounting via RUSAGE_CHILDREN deltas.

    RUSAGE_CHILDREN is cumulative over the process lifetime, so to attribute CPU
    to a single run we take the difference of the cumulative counter around it.
    Use this when running many solvers in one Python process."""

    def snapshot(self) -> float:
        u = resource.getrusage(resource.RUSAGE_CHILDREN)
        return u.ru_utime + u.ru_stime


def run_solver_metered(
    cmd: list[str],
    *,
    wall_limit_s: float,
    mem_limit_bytes: Optional[int] = None,
    grace_s: float = 2.0,
) -> RunResult:
    """Like run_solver but attributes CPU via a cumulative-rusage delta so it is
    correct when called repeatedly in one process."""
    meter = CpuMeter()
    before = meter.snapshot()
    r = run_solver(
        cmd,
        wall_limit_s=wall_limit_s,
        mem_limit_bytes=mem_limit_bytes,
        grace_s=grace_s,
    )
    after = meter.snapshot()
    cpu = max(0.0, after - before)
    return RunResult(
        reported=r.reported,
        wall_time=r.wall_time,
        cpu_time=cpu,
        exit_code=r.exit_code,
        timed_out=r.timed_out,
        mem_exceeded=r.mem_exceeded,
        stdout=r.stdout,
        stderr=r.stderr,
    )
