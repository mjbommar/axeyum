#!/usr/bin/env python3
"""cindergraph → Axeyum → sanitizer replay, over a directory of C samples.

For every function cindergraph can parse in every ``*.c`` under ``--samples``:

1. :mod:`lift` turns the AST into one QF_BV query per (path, sink).
2. ``axeyum.smt.solve`` (the native Python bindings) answers each query; a
   ``sat`` carries a model. ``--cli`` switches to shelling out to the
   ``axeyum_cli`` example binary instead, for a checkout that has not built
   the extension.
3. The model becomes a C ``main`` that calls the function with exactly those
   arguments; it is compiled with AddressSanitizer and UBSan and run. The
   sanitizer's first report line is the evidence — a witness that does not
   reproduce is reported as such, never as a finding.

``unsat`` on every obligation of a function is "no witness within the model",
and the README says what the model is. A refused function is listed with its
reason. Exit status is 1 if any witness fails to replay, or any sample's
expected verdict (from the ``// expect:`` lines) is not met; that is what makes
the run a check rather than a demo.

    python3 check.py --samples samples --out /tmp/cdefects
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lift import CType, Lifted, Query, lift_source  # noqa: E402

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
DEFAULT_CLI = REPO / "target" / "release" / "examples" / "axeyum_cli"
CLI_BUILD_LINE = "cargo build --release -p axeyum-bench --example axeyum_cli --features full"
COMMON = ["-fno-sanitize-recover=all", "-fno-omit-frame-pointer", "-O0", "-g", "-w"]
# The sanitizer that can observe each finding kind — and only that one, so the
# replay's report is evidence for THIS finding rather than for whichever
# undefined behaviour happens first on the path.
SANITIZER_FOR = {
    "buffer": "-fsanitize=address",
    "buffer-read": "-fsanitize=address",
    "index-negative": "-fsanitize=address",
    "index-high": "-fsanitize=address",
    "divide": "-fsanitize=undefined",
    "shift": "-fsanitize=undefined",
    "signed-overflow": "-fsanitize=undefined",
    "narrowing": "-fsanitize=implicit-conversion",  # clang only
}
_VALUE_RE = re.compile(r"\((\w+)\s+(#b[01]+|#x[0-9a-fA-F]+|\(_ bv(\d+) \d+\))\)")
_LINE_RE = re.compile(r":(\d+):\d+: runtime error")
_FRAME_RE = re.compile(r"#\d+ .*?/samples/[^:\s]+:(\d+)")
BOUNDS = (1, 16, 256, 4096)  # smallest witness first: it is the one a reader can check by hand


class Backend:
    """Decides one SMT-LIB script and returns ``(verdict, {name: unsigned int})``."""

    def run(self, smtlib: str, timeout_ms: int) -> tuple[str, dict[str, int]]:
        raise NotImplementedError


class NativeBackend(Backend):
    """Calls straight into the compiled extension: no subprocess, no text parsing.

    ``axeyum.smt.solve`` already returns the satisfying assignment as
    ``{declared name: value}`` (``Outcome.model``), replay-checked in Rust
    before it crosses the language boundary — the same values the ``(get-value
    ...)`` command at the end of every lifted query would have asked for, so
    the query need not even carry that command for this backend to read them.
    """

    def __init__(self) -> None:
        from axeyum import smt as _smt

        self._solve = _smt.solve

    def run(self, smtlib: str, timeout_ms: int) -> tuple[str, dict[str, int]]:
        outcome = self._solve(smtlib, timeout_ms=timeout_ms)
        values = (
            {name: int(value) for name, value in outcome.model.items()}
            if outcome.status == "sat"
            else {}
        )
        return outcome.status, values


class CliBackend(Backend):
    """Explicit ``--cli`` fallback: shells out to the ``axeyum_cli`` example binary."""

    def __init__(self, cli: Path) -> None:
        self.cli = cli

    def run(self, smtlib: str, timeout_ms: int) -> tuple[str, dict[str, int]]:
        proc = subprocess.run(
            [str(self.cli), "-", "--timeout-ms", str(timeout_ms)],
            input=smtlib,
            text=True,
            capture_output=True,
            timeout=timeout_ms / 1000 + 30,
        )
        lines = [line for line in proc.stdout.splitlines() if line.strip()]
        verdict = lines[0].strip() if lines else "no-output"
        values: dict[str, int] = {}
        if verdict == "sat" and len(lines) > 1:
            for name, lit, dec in _VALUE_RE.findall(lines[1]):
                values[name] = (
                    int(dec)
                    if dec
                    else int(lit[2:], 2)
                    if lit.startswith("#b")
                    else int(lit[2:], 16)
                )
        return verdict, values


def bounded(query: Query, bound: int) -> str:
    """The same query with every scalar parameter held to magnitude ``bound``."""
    extra = []
    for p, t in query.params:
        if bound >= 1 << (t.width - 1):
            continue
        if t.signed:
            extra.append(f"(assert (bvsle {p} (_ bv{bound} {t.width})))")
            extra.append(f"(assert (bvsge {p} (bvneg (_ bv{bound} {t.width}))))")
        else:
            extra.append(f"(assert (bvule {p} (_ bv{bound} {t.width})))")
    return query.smtlib.replace("(check-sat)", "\n".join(extra) + "\n(check-sat)", 1)


def solve(backend: Backend, query: Query, timeout_ms: int) -> tuple[str, dict[str, int]]:
    """Verdict and model; a ``sat`` is re-solved under growing bounds and the smallest witness wins."""
    verdict, values = backend.run(query.smtlib, timeout_ms)
    if verdict != "sat":
        return verdict, values
    for bound in BOUNDS:
        small_verdict, small_values = backend.run(bounded(query, bound), timeout_ms)
        if small_verdict == "sat":
            return verdict, small_values
    return verdict, values


def c_literal(value: int, t: CType) -> str:
    if t.signed and value >= 1 << (t.width - 1):
        value -= 1 << t.width
    suffix = "" if t.width <= 32 else "L"
    if not t.signed:
        suffix = "u" + suffix
    if t.signed and value == -(1 << (t.width - 1)):
        return f"(-{-(value + 1)}{suffix} - 1)"  # INT_MIN without an overflowing literal
    return f"{value}{suffix}"


def harness(sample: Path, lifted: Lifted, values: dict[str, int]) -> str:
    args = []
    setup = []
    for p in lifted.params:
        if p in lifted.pointer_params:
            cap = lifted.capacities[p]
            n = (
                int(cap[len("(_ bv") :].split()[0])
                if cap.startswith("(_ bv")
                else values.get(cap, 0)
            )
            size = max(n, 1)
            setup.append(f"    unsigned char *{p} = malloc({size}); memset({p}, 0, {size});")
            args.append(f"(void *){p}")
        else:
            t = dict(lifted.scalar_params)[p]
            args.append(c_literal(values.get(p, 0), t))
    return (
        f'#include "{sample.resolve()}"\n#include <stdlib.h>\n#include <string.h>\n'
        f"int main(void) {{\n"
        + "\n".join(setup)
        + f"\n    volatile long r = (long){lifted.function}({', '.join(args)});\n    (void)r;\n    return 0;\n}}\n"
    )


def replay(cc: str, source: Path, out: Path, kind: str, line: int) -> tuple[bool, str]:
    """Compile with the one sanitizer that observes ``kind``; True only if it fires at ``line``."""
    exe = out.with_suffix("")
    san = SANITIZER_FOR[kind]
    if san == "-fsanitize=implicit-conversion" and "clang" not in cc:
        return False, "narrowing needs clang's -fsanitize=implicit-conversion"
    comp = subprocess.run(
        [cc, san, *COMMON, str(source), "-o", str(exe)], capture_output=True, text=True
    )
    if comp.returncode != 0:
        return False, "compile failed: " + comp.stderr.strip().splitlines()[-1][:160]
    run = subprocess.run([str(exe)], capture_output=True, text=True, timeout=60)
    err = run.stderr
    for report in err.splitlines():
        if "ERROR: AddressSanitizer" in report or "runtime error" in report:
            report = re.sub(r"^==\d+==", "", report).strip()
            report = re.sub(r" on address 0x[0-9a-f]+ at pc .*$", "", report)
            report = re.sub(r"^.*?/samples/", "", report)
            m = _LINE_RE.search(report)
            where = int(m.group(1)) if m else None
            if where is None:
                # An ASan report names the line in its first user-code stack frame.
                frames = [int(f) for f in _FRAME_RE.findall(err)]
                where = frames[0] if frames else None
            if where is not None and where != line:
                return (
                    False,
                    f"sanitizer fired at line {where}, not the finding's line {line}: {report[:120]}",
                )
            return True, f"{report[:150]} (line {where})" if where is not None else report[:160]
    return False, f"exit {run.returncode}, no sanitizer report"


def expectations(src: str) -> dict[str, str]:
    """``// expect: <function> <finding|clean|refused>`` lines, if the sample carries them."""
    return {
        m.group(1): m.group(2)
        for m in re.finditer(r"//\s*expect:\s*(\w+)\s+(finding|clean|refused)", src)
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples", type=Path, default=HERE / "samples")
    ap.add_argument("--out", type=Path, default=Path("/tmp/cindergraph-defects"))
    ap.add_argument(
        "--cli",
        action="store_true",
        help="shell out to the axeyum_cli example binary instead of the native "
        "axeyum.smt bindings; fallback for a checkout that has not built the extension "
        "(uv run --no-sync maturin develop)",
    )
    ap.add_argument(
        "--cli-path",
        type=Path,
        default=DEFAULT_CLI,
        help="axeyum_cli binary path, only used with --cli",
    )
    ap.add_argument("--cc", default="clang" if shutil.which("clang") else "cc")
    ap.add_argument("--timeout-ms", type=int, default=10000)
    args = ap.parse_args()
    backend: Backend
    if args.cli:
        if not args.cli_path.exists():
            print(
                f"axeyum_cli not found at {args.cli_path}; build it: {CLI_BUILD_LINE}",
                file=sys.stderr,
            )
            return 2
        backend = CliBackend(args.cli_path)
    else:
        try:
            backend = NativeBackend()
        except ImportError:
            print(
                "axeyum native module not importable; build it with "
                "'uv run --no-sync maturin develop', or pass --cli to shell out to "
                f"axeyum_cli instead (build it: {CLI_BUILD_LINE})",
                file=sys.stderr,
            )
            return 2
    args.out.mkdir(parents=True, exist_ok=True)
    rows: list[tuple[str, ...]] = []
    failures = 0
    for sample in sorted(args.samples.glob("*.c")):
        src = sample.read_text()
        expect = expectations(src)
        for item in lift_source(src):
            if isinstance(item, tuple):
                name, why = item
                rows.append((sample.name, name, "refused", "-", "-", str(why)))
                if expect.get(name, "refused") != "refused":
                    failures += 1
                continue
            lifted: Lifted = item
            witnesses = 0
            seen: set[tuple[int, str]] = set()
            findings: list[tuple[str, ...]] = []
            for k, q in enumerate(lifted.queries):
                ob = q.obligation
                verdict, values = solve(backend, q, args.timeout_ms)
                (args.out / f"{sample.stem}.{lifted.function}.{k}.smt2").write_text(q.smtlib)
                if ob.kind == "dead-branch":
                    # The query asks "is this edge reachable"; unsat means dead.
                    if verdict == "unsat" and (ob.line, ob.note) not in seen:
                        seen.add((ob.line, ob.note))
                        findings.append(
                            (
                                sample.name,
                                lifted.function,
                                "dead-branch",
                                f"line {ob.line}",
                                f"`{ob.text}` {ob.note} is infeasible",
                                "proved unreachable (no replay: nothing executes)",
                            )
                        )
                        witnesses += 1
                    continue
                if verdict != "sat":
                    continue
                key = (ob.line, ob.kind)
                if key in seen or (ob.kind == "buffer-read" and (ob.line, "buffer") in seen):
                    continue  # one row per construct; the write side of a call outranks its read side
                seen.add(key)
                witnesses += 1
                hsrc = args.out / f"{sample.stem}.{lifted.function}.{k}.main.c"
                hsrc.write_text(harness(sample, lifted, values))
                ok, report = replay(args.cc, hsrc, hsrc.with_suffix(".bin"), ob.kind, ob.line)
                inputs = ", ".join(
                    f"{p}={c_literal(values.get(p, 0), t)}" for p, t in lifted.scalar_params
                )
                caps = ", ".join(
                    f"cap({p})={values.get(lifted.capacities[p], lifted.capacities[p])}"
                    for p in lifted.pointer_params
                    if not lifted.capacities[p].startswith("(_ bv")
                )
                findings.append(
                    (
                        sample.name,
                        lifted.function,
                        ob.kind,
                        f"line {ob.line}",
                        f"`{ob.text}` with {inputs}{'; ' + caps if caps else ''}",
                        ("REPLAYED: " if ok else "DID NOT REPLAY: ") + report,
                    )
                )
                if not ok:
                    failures += 1
            if findings:
                rows.extend(findings)
            else:
                rows.append(
                    (
                        sample.name,
                        lifted.function,
                        "clean",
                        "-",
                        f"{len(lifted.queries)} obligations over {lifted.paths} paths, all unsat",
                        "no witness within the model",
                    )
                )
            want = expect.get(lifted.function)
            if want == "finding" and witnesses == 0 or want == "clean" and witnesses > 0:
                failures += 1
                rows.append(
                    (
                        sample.name,
                        lifted.function,
                        "EXPECTATION-FAILED",
                        "-",
                        f"expected {want}",
                        "",
                    )
                )
    print("| sample | function | finding | where | witness | replay |")
    print("|---|---|---|---|---|---|")
    for r in rows:
        print("| " + " | ".join(str(c).replace("|", "\\|") for c in r) + " |")
    (args.out / "results.tsv").write_text("\n".join("\t".join(r) for r in rows) + "\n")
    print(
        f"\n{len(rows)} rows, {failures} failure(s); queries and harnesses in {args.out}",
        file=sys.stderr,
    )
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
