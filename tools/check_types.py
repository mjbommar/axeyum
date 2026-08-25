"""The type-checker gate for the Python package.

Runs Astral's `ty` over `python/axeyum/` -- the code this repository writes --
and refuses an increase in the diagnostic count.

Why a budget instead of zero: five diagnostics remain, and none of them is
fixable in `python/axeyum/**.py`.

  * `AbstractAgent.run` is a pydantic-ai overload set that our call does not
    match under `ty`'s reading. It runs correctly (the agent suites cover it).
  * THREE inside the GENERATED stub `python/axeyum/_native/producers/*.pyi*`.
    `StatementImport` has a member named `kernel`, and the stub imports the
    sibling module as `from axeyum._native import kernel`; inside a class body
    the member shadows the import, so `goal(self) -> kernel.ExprId` resolves
    `kernel` to the method. `pyo3-stub-gen` 0.23 always qualifies a cross-module
    type as `<last module component>.<Type>` (`TypeInfo::locally_defined`,
    `ImportKind::Module`) and offers no alias, so this cannot be fixed from the
    annotations; the fixes available are to rename the accessor (a public API
    change) or to re-export the three kernel handle types into `producers`.
    Neither belongs in a typing slice. Recorded rather than hidden.

  The four that USED to be here are gone: `axeyum._native.cas.certify` and
  `axeyum._native.kernel.identity` now resolve, because the stubs are a PACKAGE
  with one directory per PyO3 submodule; and `Declined.reason` is declared by
  `crate::stub_info::stub_exception!`.

Each is recorded here rather than silenced with an ignore comment, because an
ignore comment is invisible in a count and a budget is not.

The gate is shown to BITE on every run: a file with a deliberate type error is
checked through the same code path, and the gate fails if `ty` reports nothing
for it. A type checker pointed at the wrong path exits 0 with an empty report,
which is indistinguishable from a clean tree -- this repository has shipped that
mistake at three other layers.
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
TARGET = "python/axeyum"

# The number of `ty` diagnostics in TARGET that are not ours to fix. Lower it
# whenever the real number drops; never raise it without naming the diagnostic
# above and saying why it cannot be fixed here.
BUDGET = 4


def ty_binary() -> str:
    """The `ty` executable, from PATH or from this interpreter's environment."""
    found = shutil.which("ty")
    if found:
        return found
    candidate = Path(sys.executable).parent / "ty"
    if candidate.is_file():
        return str(candidate)
    raise SystemExit("TYPES|FAIL `ty` is not installed -- run `uv sync --dev`")


def run_ty(binary: str, target: str) -> tuple[int, str]:
    """Runs `ty check target` and returns (diagnostic count, raw output)."""
    completed = subprocess.run(
        [binary, "check", target, "--output-format", "concise"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    output = completed.stdout + completed.stderr
    count = sum(1 for line in output.splitlines() if "error[" in line or "warning[" in line)
    return count, output


def control_fires(binary: str) -> int:
    """Checks a deliberately ill-typed file; returns how many diagnostics it got.

    Zero means the gate is not looking at anything, whatever the real target
    reported.
    """
    with tempfile.TemporaryDirectory(prefix="axeyum-ty-control-") as directory:
        probe = Path(directory) / "control.py"
        probe.write_text("value: int = 'not an int'\n", encoding="utf-8")
        count, _ = run_ty(binary, str(probe))
        return count


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--show",
        action="store_true",
        help="print the diagnostics as well as the count",
    )
    args = parser.parse_args()

    binary = ty_binary()
    control = control_fires(binary)
    count, output = run_ty(binary, TARGET)
    if args.show:
        print(output.rstrip())

    print(f"TYPES|target={TARGET}|diagnostics={count}|budget={BUDGET}|control={control}")

    if control == 0:
        print(
            "TYPES|FAIL the positive control produced no diagnostics -- `ty` is not "
            "analysing anything, so the count above means nothing"
        )
        return 1
    if count > BUDGET:
        print(f"TYPES|FAIL {count} diagnostics exceed the budget of {BUDGET}")
        if not args.show:
            print(output.rstrip())
        return 1
    if count < BUDGET:
        print(
            f"TYPES|IMPROVED {count} < {BUDGET}: lower BUDGET in tools/check_types.py "
            "so the gain is held"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
