"""Resource-limited solver execution — a bounded local approximation of the
SMT-COMP execution service (§5) for a single-process solver.

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

For higher fidelity on a real competition rehearsal, a BenchExec `runexec`
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
import threading
import time
from dataclasses import dataclass
from typing import Optional

from scoring import Status

_VERDICT_RE = re.compile(r"\b(unsat|sat|unknown)\b")


class _PeakRssSampler:
    """Best-effort Linux VmHWM sampler for a single-process solver."""

    def __init__(self, pid: int, interval_s: float = 0.01):
        self._status = f"/proc/{pid}/status"
        self._interval_s = interval_s
        self._stop = threading.Event()
        self._peak_bytes = 0
        self._thread = threading.Thread(target=self._run, daemon=True)

    def start(self) -> None:
        self._thread.start()

    def stop(self) -> int:
        self._sample()
        self._stop.set()
        self._thread.join(timeout=1.0)
        return self._peak_bytes

    def _sample(self) -> None:
        try:
            with open(self._status, encoding="ascii") as handle:
                values = {
                    key.rstrip(":"): value
                    for key, value, *_unit in (
                        line.split() for line in handle if line.startswith(("VmHWM:", "VmRSS:"))
                    )
                }
        except (OSError, ValueError):
            return
        value = values.get("VmHWM") or values.get("VmRSS")
        if value is not None:
            self._peak_bytes = max(self._peak_bytes, int(value) * 1024)

    def _run(self) -> None:
        while not self._stop.is_set():
            self._sample()
            self._stop.wait(self._interval_s)


@dataclass(frozen=True)
class RunResult:
    """Raw measured outcome of one execution."""

    # ``reported`` preserves the legacy runner policy, which suppresses a
    # timeout-observed response.  Resumable v2 records use ``observed`` and
    # apply their separately registered verdict-admission policy instead.
    reported: Optional[Status]
    observed: Optional[Status]
    wall_time: float  # legacy elapsed wall time, seconds
    scoring_wall_time: float  # aw, clamped to the registered wall limit
    runner_elapsed: float  # includes watchdog kill/reap overhead
    cpu_time: float  # ac, seconds
    exit_code: Optional[int]
    signal: Optional[int]
    termination_class: str
    resource_limit_kind: Optional[str]
    timed_out: bool
    mem_exceeded: bool
    peak_rss_bytes: int
    stdout: str
    stderr: str
    stdout_bytes: bytes
    stderr_bytes: bytes


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
    evidenced_resource_limit_kind: Optional[str] = None,
    env: Optional[dict[str, str]] = None,
) -> RunResult:
    """Execute `cmd`, enforcing wall/mem limits, measuring wall+CPU (§5, §7.1)."""
    if evidenced_resource_limit_kind not in {None, "cpu", "memory"}:
        raise ValueError("resource-limit evidence must be 'cpu', 'memory', or None")
    start = time.monotonic()
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        preexec_fn=_preexec(mem_limit_bytes),
        env=env,
    )
    rss_sampler = _PeakRssSampler(proc.pid)
    rss_sampler.start()
    timed_out = False
    try:
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
    finally:
        peak_rss_bytes = rss_sampler.stop()
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

    captured_stdout = stdout or b""
    captured_stderr = stderr or b""
    decoded_stdout = captured_stdout.decode("utf-8", errors="replace")
    decoded_stderr = captured_stderr.decode("utf-8", errors="replace")
    observed = parse_verdict(decoded_stdout)

    return_code = proc.returncode
    if timed_out:
        termination_class = "wall-timeout"
        exit_code = None
        terminating_signal = signal.SIGKILL
        resource_limit_kind = "wall"
    elif evidenced_resource_limit_kind is not None:
        if return_code == 0:
            raise ValueError("resource-limit evidence is incompatible with exit 0")
        termination_class = "resource-limit"
        exit_code = None
        terminating_signal = -return_code if return_code is not None and return_code < 0 else None
        resource_limit_kind = evidenced_resource_limit_kind
    elif return_code == 0:
        termination_class = "completed"
        exit_code = 0
        terminating_signal = None
        resource_limit_kind = None
    elif return_code is not None and return_code < 0:
        termination_class = "signal"
        exit_code = None
        terminating_signal = -return_code
        resource_limit_kind = None
    else:
        termination_class = "nonzero-exit"
        exit_code = return_code
        terminating_signal = None
        resource_limit_kind = None

    reported = None if timed_out else observed
    return RunResult(
        reported=reported,
        observed=observed,
        wall_time=wall,
        scoring_wall_time=min(wall, wall_limit_s),
        runner_elapsed=wall,
        cpu_time=cpu,
        exit_code=exit_code,
        signal=terminating_signal,
        termination_class=termination_class,
        resource_limit_kind=resource_limit_kind,
        timed_out=timed_out,
        mem_exceeded=resource_limit_kind == "memory",
        peak_rss_bytes=peak_rss_bytes,
        stdout=decoded_stdout,
        stderr=decoded_stderr,
        stdout_bytes=captured_stdout,
        stderr_bytes=captured_stderr,
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
    evidenced_resource_limit_kind: Optional[str] = None,
    env: Optional[dict[str, str]] = None,
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
        evidenced_resource_limit_kind=evidenced_resource_limit_kind,
        env=env,
    )
    after = meter.snapshot()
    cpu = max(0.0, after - before)
    return RunResult(
        reported=r.reported,
        observed=r.observed,
        wall_time=r.wall_time,
        scoring_wall_time=r.scoring_wall_time,
        runner_elapsed=r.runner_elapsed,
        cpu_time=cpu,
        exit_code=r.exit_code,
        signal=r.signal,
        termination_class=r.termination_class,
        resource_limit_kind=r.resource_limit_kind,
        timed_out=r.timed_out,
        mem_exceeded=r.mem_exceeded,
        peak_rss_bytes=r.peak_rss_bytes,
        stdout=r.stdout,
        stderr=r.stderr,
        stdout_bytes=r.stdout_bytes,
        stderr_bytes=r.stderr_bytes,
    )
