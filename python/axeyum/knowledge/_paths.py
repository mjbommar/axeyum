"""Repository discovery and the read-only primitives every accessor shares.

Two rules are enforced here rather than in each submodule, because they are the
two this repository has repeatedly got wrong:

* **Nothing found is not the same as not looked at.** :func:`require_dir` and
  :func:`require_file` raise :class:`FileNotFoundError` naming the path, so an
  empty collection returned by an accessor always means "the directory was read
  and held nothing", never "the directory was never opened".
* **A subprocess-backed answer carries its exit status.** :func:`run_script`
  refuses to hand back stdout from a command that failed, because an empty or
  partial answer from a broken tool is indistinguishable from a strong negative
  result.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

# The marker used to identify the repository root. It is a committed schema, so
# it exists in every checkout and in every `git archive` snapshot.
ROOT_MARKER = Path("artifacts") / "ontology" / "fact.schema.json"

#: Environment variable that overrides root discovery (used by the tests to
#: point an accessor at a fixture tree).
ROOT_ENV = "AXEYUM_REPO_ROOT"

#: Default wall-clock ceiling for a helper script, in seconds. Explicit, because
#: an unbounded subprocess in a library is a hang with no owner.
DEFAULT_TIMEOUT_S = 300.0


class ScriptError(RuntimeError):
    """A canonical validator or generator script did not complete successfully."""

    def __init__(self, argv: list[str], returncode: int, stdout: str, stderr: str) -> None:
        super().__init__(
            f"{' '.join(argv)} exited {returncode}\n"
            f"--- stdout ---\n{stdout}\n--- stderr ---\n{stderr}"
        )
        self.argv = list(argv)
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


@dataclass(frozen=True, slots=True)
class ScriptRun:
    """The complete result of running a repository script.

    ``returncode`` is part of the value on purpose: a caller that wants to treat
    a nonzero exit as data (a validator reporting violations) must be able to,
    and a caller that wants an exception calls :meth:`check`.
    """

    argv: tuple[str, ...]
    returncode: int
    stdout: str
    stderr: str

    def check(self) -> ScriptRun:
        """Return self when the script exited 0; raise :class:`ScriptError` otherwise."""
        if self.returncode != 0:
            raise ScriptError(list(self.argv), self.returncode, self.stdout, self.stderr)
        return self


def repo_root(start: Path | str | None = None) -> Path:
    """Locate the Axeyum checkout root.

    ``AXEYUM_REPO_ROOT`` wins when set. Otherwise walk up from this file until a
    directory containing ``artifacts/ontology/fact.schema.json`` is found.

    Raises:
        FileNotFoundError: naming what was searched, never returning a guess.
    """
    override = os.environ.get(ROOT_ENV)
    if override:
        candidate = Path(override).expanduser().resolve()
        if not (candidate / ROOT_MARKER).is_file():
            raise FileNotFoundError(
                f"{ROOT_ENV}={override} does not look like an Axeyum checkout: "
                f"{candidate / ROOT_MARKER} is missing"
            )
        return candidate

    here = Path(start).resolve() if start is not None else Path(__file__).resolve()
    for directory in (here, *here.parents):
        if (directory / ROOT_MARKER).is_file():
            return directory
    raise FileNotFoundError(
        f"no Axeyum checkout above {here}: nothing containing {ROOT_MARKER} "
        f"(set {ROOT_ENV} to point at one)"
    )


def resolve_root(root: Path | str | None = None) -> Path:
    """Normalize an optional caller-supplied root to an absolute, verified path."""
    if root is None:
        return repo_root()
    candidate = Path(root).expanduser().resolve()
    if not (candidate / ROOT_MARKER).is_file():
        raise FileNotFoundError(
            f"{candidate} is not an Axeyum checkout: {candidate / ROOT_MARKER} is missing"
        )
    return candidate


def require_file(path: Path) -> Path:
    """Return ``path`` when it is a file; raise :class:`FileNotFoundError` naming it."""
    if not path.is_file():
        raise FileNotFoundError(f"expected a file at {path}")
    return path


def require_dir(path: Path) -> Path:
    """Return ``path`` when it is a directory; raise :class:`FileNotFoundError` naming it."""
    if not path.is_dir():
        raise FileNotFoundError(f"expected a directory at {path}")
    return path


def read_json(path: Path) -> Any:
    """Read one JSON document, raising :class:`FileNotFoundError` when absent."""
    require_file(path)
    return json.loads(path.read_text(encoding="utf-8"))


def run_script(
    root: Path,
    script: str,
    args: list[str] | tuple[str, ...] = (),
    *,
    timeout_s: float = DEFAULT_TIMEOUT_S,
) -> ScriptRun:
    """Run ``scripts/<script>`` under the current interpreter and capture everything.

    ``scripts/`` is standard-library-only by policy and must never import this
    package, so the two worlds exchange JSON over a pipe, exactly as the
    producer/checker pairs in this repository already do.
    """
    path = require_file(root / "scripts" / script)
    argv = [sys.executable, str(path), *[str(a) for a in args]]
    # Fixed interpreter, repository-local script; no shell, no user-supplied binary.
    completed = subprocess.run(
        argv,
        capture_output=True,
        text=True,
        timeout=timeout_s,
        cwd=str(root),
        check=False,
    )
    return ScriptRun(
        argv=tuple(argv),
        returncode=completed.returncode,
        stdout=completed.stdout,
        stderr=completed.stderr,
    )


def load_script_module(root: Path, script: str, module_name: str) -> Any:
    """Import a repository script as a module to read its constants.

    Used where a constant is the contract (``EXECUTION_DRIVERS``): copying the
    list into Python would create a second source of truth that can drift
    silently, which is the failure this whole layer is written to avoid. Every
    such script guards its entry point with ``if __name__ == "__main__"``, so
    executing the module runs no work.
    """
    import importlib.util

    path = require_file(root / "scripts" / script)
    spec = importlib.util.spec_from_file_location(module_name, path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {path} as a module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


__all__ = [
    "DEFAULT_TIMEOUT_S",
    "ROOT_ENV",
    "ROOT_MARKER",
    "ScriptError",
    "ScriptRun",
    "load_script_module",
    "read_json",
    "repo_root",
    "require_dir",
    "require_file",
    "resolve_root",
    "run_script",
]
