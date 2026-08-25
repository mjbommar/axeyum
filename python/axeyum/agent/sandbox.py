"""`python_exec`: run untrusted code where a runaway cannot take the host down.

Slice A6 of [`docs/python-2026-08/03-agentic-layer.md`], and the mechanism is
lifted verbatim from a lesson this repository paid for. CLAUDE.md's
`cargo-serialized.sh` section: a kernel OOM killed a live agent session because
one test reached 125 GB, and `MemoryMax` **without** `MemorySwapMax` is
decoration -- measured there, `MemoryMax=64M` is genuinely applied, a 400 MB
allocation still succeeds, and the cgroup simply swaps on a box whose swap is
already full. Adding `MemorySwapMax=0` turns the same allocation into status
137 from the cgroup's own OOM killer, host untouched. So both properties are
set here, always, together.

Four layers, and :attr:`ExecResult.isolation` names exactly which ones were in
force -- never silently:

1. **memory** -- a `systemd-run --user --scope` carrying `MemoryMax` *and*
   `MemorySwapMax=0` when `systemd-run` is available and actually works (it is
   PROBED, not assumed: user-scope delegation differs per host), otherwise
   `RLIMIT_AS` in the child. The fallback is weaker -- it bounds address space,
   not resident pages -- and the `isolation` string says so.
2. **CPU** -- `RLIMIT_CPU` in the child in both modes, plus a hard wall-clock
   timeout enforced by killing the process GROUP. The rlimit bounds CPU, the
   wall clock bounds sleeping, and neither bounds the other.
3. **network** -- `unshare -n` when it works. On a host with unprivileged user
   namespaces unavailable it does not, and the `isolation` string then says
   `no-network-isolation`, because a gap that is documented in a docstring and
   absent from the result is a gap nobody will see.
4. **imports** -- a preamble that replaces `builtins.__import__` with a
   whitelist. The rule is scoped to the CALLER: an import is refused only when
   the immediate calling frame is user code (`__main__`), which is exactly the
   threat -- user code reaching for `os`. Library code imports freely, because
   every alternative was measured and failed. A depth counter lets sympy's
   lazy `sympy.core.relational` through the wrong door (it is imported long
   after the top-level `import sympy` returned, at depth 0). Testing the
   caller's *package* against the whitelist fails on `_io`, which the import
   machinery pulls in from a frozen bootstrap frame that belongs to no
   whitelisted package.

   This is a guard-rail and NOT a security boundary, and the difference matters.
   `os` is already in `sys.modules` before any user code runs, and code that
   `exec`s with a forged `__name__` defeats the frame test. It stops user code
   from *reaching for* `os`, `socket` or `subprocess` directly. The boundary is
   layers 1 to 3.

:func:`python_exec_selfcheck` is the ratchet on all of this, and it mirrors
`cargo-serialized.sh --self-check`: it over-allocates through the same code path
and **fails if the allocation survives**. A memory ceiling that has never been
shown to bite is a ceiling nobody has measured.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from functools import lru_cache

#: Everything user code may `import` directly. Symbolic scratch work and nothing
#: that reaches the host: no `os`, no `sys`, no `subprocess`, no `socket`, no
#: `pathlib`, no `importlib`.
ALLOWED_MODULES: tuple[str, ...] = (
    "sympy",
    "fractions",
    "math",
    "itertools",
    "json",
    "re",
    "decimal",
)

#: Default memory ceiling for one call, in MiB. Overridable per call and, for
#: the self-check's discrimination control, by `AXEYUM_SANDBOX_MEM_MB`.
DEFAULT_MEMORY_MB = 512

#: Default wall-clock ceiling for one call, in seconds.
DEFAULT_TIMEOUT_S = 20

#: How much CPU time the child may burn, as a margin over the wall budget. A
#: `while True` burns CPU and is caught by either; a `time.sleep` burns none and
#: is caught only by the wall clock.
CPU_MARGIN_S = 5

#: Ceiling on captured stdout/stderr, so a print loop cannot fill a transcript.
MAX_OUTPUT_BYTES = 256 * 1024

#: Environment variables passed through to the child, and the only ones.
#:
#: `XDG_RUNTIME_DIR` and `DBUS_SESSION_BUS_ADDRESS` are here because
#: `systemd-run --user` cannot reach the user manager without them; they are
#: passed only so the ceiling can be applied at all. Nothing else from the
#: caller's environment crosses -- no `AXEYUM_*`, no credentials, no `PYTHON*`
#: (which `-I` would ignore anyway).
PASSTHROUGH_ENV: tuple[str, ...] = ("XDG_RUNTIME_DIR", "DBUS_SESSION_BUS_ADDRESS")


def child_environment(scratch: str) -> dict[str, str]:
    """The child's whole environment: a scratch HOME/TMPDIR and the bus handles."""
    environment = {
        "PATH": "/usr/bin:/bin",
        "HOME": scratch,
        "TMPDIR": scratch,
        "LC_ALL": "C",
    }
    for name in PASSTHROUGH_ENV:
        value = os.environ.get(name)
        if value:
            environment[name] = value
    return environment


_ISO_SCOPE = "systemd-scope"
_ISO_RLIMIT = "rlimit-as"


class SandboxError(RuntimeError):
    """The sandbox could not be constructed. Never downgraded to "ran unconfined"."""


@dataclass(frozen=True, slots=True)
class ExecResult:
    """What one sandboxed run did, and what was actually containing it.

    `isolation` is a required part of the result rather than a log line: a
    caller that cannot tell a cgroup-enforced run from an `RLIMIT_AS` fallback
    cannot tell what its own measurement means.
    """

    stdout: str
    stderr: str
    exit_status: int
    duration_ms: int
    memory_max_mb: int
    isolation: str
    timed_out: bool = False

    @property
    def ok(self) -> bool:
        return self.exit_status == 0 and not self.timed_out


# ------------------------------------------------------------------ the probes


@lru_cache(maxsize=1)
def systemd_scope_available() -> bool:
    """Whether a `--user --scope` carrying BOTH memory properties actually runs.

    Probed, not assumed. `shutil.which("systemd-run")` answers a different
    question -- cgroup delegation to the user manager differs per host, and
    CLAUDE.md's own rule is to run the wrapper's `--self-check` per host because
    "a wrapper that caps s4 says nothing about s5".
    """
    if shutil.which("systemd-run") is None:
        return False
    try:
        completed = subprocess.run(
            [
                "systemd-run",
                "--user",
                "--scope",
                "-q",
                "-p",
                "MemoryMax=64M",
                "-p",
                "MemorySwapMax=0",
                "--",
                "/bin/true",
            ],
            capture_output=True,
            # The SAME environment the real call gets, and this is not a detail:
            # `systemd-run --user` needs `XDG_RUNTIME_DIR` and
            # `DBUS_SESSION_BUS_ADDRESS` to reach the user manager. Probing with
            # the caller's full environment and then running with a stripped one
            # is the "an empty result from a tool that was never pointed at your
            # subject" trap -- measured here: the probe said True and every real
            # call died with "Failed to connect to user scope bus".
            env=child_environment("/tmp"),
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return completed.returncode == 0


@lru_cache(maxsize=1)
def unshare_net_available() -> bool:
    """Whether `unshare -n` works unprivileged here. Usually it does not."""
    if shutil.which("unshare") is None:
        return False
    try:
        completed = subprocess.run(
            ["unshare", "-n", "--", "/bin/true"],
            capture_output=True,
            timeout=30,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return completed.returncode == 0


def isolation_label(memory_mb: int, timeout_s: int, allowed: tuple[str, ...]) -> str:
    """The `isolation` string: every layer, and every layer that is MISSING."""
    if systemd_scope_available():
        memory = f"{_ISO_SCOPE}(MemoryMax={memory_mb}M,MemorySwapMax=0)"
    else:
        memory = f"{_ISO_RLIMIT}({memory_mb}M; bounds address space, not resident pages)"
    if unshare_net_available():
        network = "unshare-n"
    else:
        network = "no-network-isolation(unshare-n unavailable; import guard only)"
    return "+".join(
        (
            memory,
            f"rlimit-cpu({timeout_s + CPU_MARGIN_S}s)",
            f"wall-timeout({timeout_s}s,killpg)",
            network,
            "scratch-cwd",
            f"import-whitelist({','.join(allowed)})",
        )
    )


# ----------------------------------------------------------------- the preamble


_GUARD = """
import builtins as _b, resource as _r, sys as _s
_ALLOWED = frozenset({allowed!r})
if {set_as!r}:
    _r.setrlimit(_r.RLIMIT_AS, ({as_bytes!r}, {as_bytes!r}))
_r.setrlimit(_r.RLIMIT_CPU, ({cpu!r}, {cpu!r}))
_real = _b.__import__
def _guarded(name, globals=None, locals=None, fromlist=(), level=0):
    root = name.partition(".")[0]
    if root not in _ALLOWED:
        try:
            caller = _s._getframe(1).f_globals.get("__name__") or ""
        except ValueError:
            caller = "__main__"
        if caller == "__main__":
            raise ImportError(
                "axeyum-sandbox: %r is not on the import whitelist %s"
                % (root, sorted(_ALLOWED))
            )
    return _real(name, globals, locals, fromlist, level)
_b.__import__ = _guarded
_g = {{"__name__": "__main__", "__builtins__": _b}}
exec(compile({code!r}, "<axeyum-sandbox>", "exec"), _g)
"""


def _script(code: str, *, allowed: tuple[str, ...], memory_mb: int, timeout_s: int) -> str:
    """The child's whole program: rlimits, the import guard, then the user code.

    `RLIMIT_AS` is set here only when the cgroup is NOT doing the job -- setting
    both would make a cgroup-enforced run report a `MemoryError` from the rlimit
    instead of the SIGKILL the cgroup would have delivered, and the two are
    different findings.
    """
    return _GUARD.format(
        allowed=list(allowed),
        set_as=not systemd_scope_available(),
        as_bytes=memory_mb * 1024 * 1024,
        cpu=timeout_s + CPU_MARGIN_S,
        code=code,
    )


def _argv(script: str, memory_mb: int) -> list[str]:
    """`systemd-run` scope, then `unshare -n`, then the interpreter. Each optional."""
    argv: list[str] = []
    if systemd_scope_available():
        argv += [
            "systemd-run",
            "--user",
            "--scope",
            "-q",
            "-p",
            f"MemoryMax={memory_mb}M",
            "-p",
            "MemorySwapMax=0",
            "--",
        ]
    if unshare_net_available():
        argv += ["unshare", "-n", "--"]
    # `-I` is isolated mode: no user site directory, no `PYTHON*` environment,
    # no implicit `sys.path[0]`. The sandbox's cwd must not be importable.
    argv += [sys.executable, "-I", "-c", script]
    return argv


def python_exec(
    code: str,
    timeout_s: int = DEFAULT_TIMEOUT_S,
    *,
    memory_mb: int | None = None,
    allowed_modules: tuple[str, ...] = ALLOWED_MODULES,
) -> ExecResult:
    """Run `code` in a bounded subprocess and report what bounded it.

    Never raises for a failure IN the code: a traceback, an `ImportError` from
    the whitelist, a cgroup SIGKILL and a wall-clock kill all come back as an
    :class:`ExecResult` with a nonzero `exit_status`, because a decline is a
    datapoint and an exception here would put it in the harness's error path.

    Args:
        code: The Python source to run. It is compiled in the child, so a syntax
            error is the child's nonzero exit rather than this process's.
        timeout_s: Wall-clock ceiling. The process GROUP is killed on expiry --
            killing the leader alone leaves a `systemd-run` scope's payload
            behind, which is the "background task reported as exited" shape.
        memory_mb: Ceiling in MiB; `AXEYUM_SANDBOX_MEM_MB` overrides the default
            and exists so the self-check has a discrimination control.
        allowed_modules: The import whitelist for this call.

    Raises:
        SandboxError: the scratch directory could not be made. Running without
            one would put the child's cwd in the caller's tree.
    """
    if memory_mb is None:
        memory_mb = int(os.environ.get("AXEYUM_SANDBOX_MEM_MB", DEFAULT_MEMORY_MB))
    timeout_s = max(1, int(timeout_s))
    isolation = isolation_label(memory_mb, timeout_s, allowed_modules)
    try:
        scratch = tempfile.mkdtemp(prefix="axeyum-sandbox-")
    except OSError as error:
        raise SandboxError(f"no scratch directory for the sandbox: {error}") from error
    script = _script(code, allowed=allowed_modules, memory_mb=memory_mb, timeout_s=timeout_s)
    environment = child_environment(scratch)
    started = time.monotonic()
    timed_out = False
    try:
        # Fixed argv, no shell: `code` is passed as a compiled string to a
        # `-c` program, never interpolated into a command line.
        process = subprocess.Popen(
            _argv(script, memory_mb),
            cwd=scratch,
            env=environment,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            start_new_session=True,
        )
        try:
            out, err = process.communicate(timeout=timeout_s)
        except subprocess.TimeoutExpired:
            timed_out = True
            _killpg(process)
            out, err = process.communicate(timeout=30)
        status = process.returncode
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
    return ExecResult(
        stdout=_decode(out),
        stderr=_decode(err),
        # A wall-clock kill lands as a signal, so `returncode` is negative and
        # already nonzero. It is reported as measured rather than normalized:
        # -9 (we killed it) and 137 (the cgroup killed it) are different facts.
        exit_status=int(status if status is not None else -1),
        duration_ms=max(0, int((time.monotonic() - started) * 1000)),
        memory_max_mb=memory_mb,
        isolation=isolation,
        timed_out=timed_out,
    )


def _killpg(process: subprocess.Popen) -> None:
    try:
        os.killpg(os.getpgid(process.pid), 9)
    except (OSError, ProcessLookupError):
        process.kill()


def _decode(payload: bytes | None) -> str:
    if not payload:
        return ""
    return payload[:MAX_OUTPUT_BYTES].decode("utf-8", "replace")


# ---------------------------------------------------------------- the self-check


@dataclass(frozen=True, slots=True)
class SelfCheck:
    """The result of proving the sandbox actually bites on THIS host."""

    ok: bool
    line: str
    memory: ExecResult
    network: ExecResult


#: Printed by the memory probe if nothing stopped it. Its presence in stdout is
#: the failure, exactly as `NOT-ENFORCED|status=0|out=SURVIVED` is for
#: `cargo-serialized.sh --self-check`.
SURVIVED = "SURVIVED"

_MEMORY_PROBE = (
    f"b = bytearray(2 * 1024 * 1024 * 1024)\nb[0] = 1\nb[-1] = 1\nprint({SURVIVED!r}, len(b))\n"
)

_NETWORK_PROBE = (
    "import socket\n"
    "s = socket.socket()\n"
    "s.settimeout(3)\n"
    "s.connect(('1.1.1.1', 80))\n"
    "print('CONNECTED')\n"
)


def python_exec_selfcheck(memory_mb: int | None = None) -> SelfCheck:
    """Prove the ceiling bites and the socket does not open, on THIS host.

    Two probes, and both must FAIL for the sandbox to pass:

    * **memory** -- allocate 2 GiB and touch both ends. Under the cgroup this is
      SIGKILLed (status 137) long before 4 GiB is committed; under the
      `RLIMIT_AS` fallback it is a `MemoryError` (status 1). If it prints
      `SURVIVED`, the ceiling is decoration and this returns `ok=False` --
      mirroring `cargo-serialized.sh --self-check`, which fails on
      `NOT-ENFORCED|status=0|out=SURVIVED`.
    * **network** -- open a socket to a routable address. Refused by the import
      whitelist, and additionally by the network namespace where one is
      available; the line says WHICH, because "no route" and "no socket module"
      are different guarantees.

    It discriminates: `AXEYUM_SANDBOX_MEM_MB=3072 python_exec_selfcheck()` gives
    the probe more headroom than it asks for and the memory half must then
    report `NOT-ENFORCED`. A check that cannot fail is worse than no check.
    """
    memory = python_exec(_MEMORY_PROBE, timeout_s=120, memory_mb=memory_mb)
    network = python_exec(_NETWORK_PROBE, timeout_s=30, memory_mb=memory_mb)
    survived = SURVIVED in memory.stdout or memory.exit_status == 0
    connected = "CONNECTED" in network.stdout or network.exit_status == 0
    layer = "netns+import-guard" if unshare_net_available() else "import-guard-only"
    line = (
        f"SANDBOX-SELFCHECK|"
        f"{'ENFORCED' if not survived else 'NOT-ENFORCED'}|"
        f"memory_status={memory.exit_status}|"
        f"memory_out={(memory.stdout.strip().splitlines() or [''])[0][:60]}|"
        f"network={'REFUSED' if not connected else 'CONNECTED'}|"
        f"network_status={network.exit_status}|"
        f"network_layer={layer}|"
        f"cap={memory.memory_max_mb}M|"
        f"isolation={memory.isolation}"
    )
    return SelfCheck(ok=not survived and not connected, line=line, memory=memory, network=network)


def main() -> int:
    """`python -m axeyum.agent.sandbox` -- print the self-check line, exit on it."""
    check = python_exec_selfcheck()
    print(check.line)
    return 0 if check.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())


__all__ = [
    "ALLOWED_MODULES",
    "CPU_MARGIN_S",
    "DEFAULT_MEMORY_MB",
    "DEFAULT_TIMEOUT_S",
    "MAX_OUTPUT_BYTES",
    "PASSTHROUGH_ENV",
    "SURVIVED",
    "ExecResult",
    "SandboxError",
    "SelfCheck",
    "child_environment",
    "isolation_label",
    "main",
    "python_exec",
    "python_exec_selfcheck",
    "systemd_scope_available",
    "unshare_net_available",
]
