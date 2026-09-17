#!/usr/bin/env python3
"""cindergraph → Axeyum → sanitizer replay, over a directory of C samples.

For every function cindergraph can parse in every ``*.c`` under ``--samples``:

1. :mod:`lift` turns the AST into one QF_BV query per (path, sink), unrolling
   loops to ``--unroll`` iterations (a file's ``// axeyum: unroll = N`` wins).
2. ``axeyum.smt.solve`` (the native Python bindings) answers each query; a
   ``sat`` carries a model. ``--cli`` switches to shelling out to the
   ``axeyum_cli`` example binary instead, for a checkout that has not built
   the extension.
3. The model becomes a C ``main`` that calls the function with exactly those
   arguments; it is compiled with the one sanitizer that observes the finding's
   kind and run. The sanitizer's first report line is the evidence — a witness
   that does not reproduce is reported as such, never as a finding.

``unsat`` on every obligation of a function is "no witness within the model",
and the README says what the model is. A function with a loop whose bound is
not met within the unrolling is ``bounded``, never ``clean``. A refused
function is listed with its reason, and the refusal reasons are histogrammed at
the end: on inputs nobody wrote to be lifted, that histogram is what says what
to build next. Exit status is 1 if any witness fails to replay, or any sample's
expected verdict (from the ``// expect:`` lines) is not met, or the replay
control (the first replayed harness judged at the line after its finding) is
not refused; that is what makes the run a check rather than a demo.

The first line of stdout says what the run parsed C with —
``cindergraph|version=…|commit=…|pinned=…|match=yes`` — and the last two are
machine-readable: ``CINDERGRAPH_DEFECTS_REPLAY_CONTROL|…`` and
``CINDERGRAPH_DEFECTS_RUN|rows=…|…|failures=…``.
``scripts/check-cindergraph-defects.sh`` is the gate that runs this and then
re-derives the verdict from ``results.tsv`` rather than from this exit status.

    python3 check.py --samples samples --out /tmp/cdefects
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
import tomllib
from collections import Counter
from importlib import metadata
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lift import DEFAULT_UNROLL, CType, Lifted, Query, lift_source

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
DEFAULT_CLI = REPO / "target" / "release" / "examples" / "axeyum_cli"
CLI_BUILD_LINE = "cargo build --release -p axeyum-bench --example axeyum_cli --features full"
COMMON = [
    "-fno-sanitize-recover=all",
    "-fno-omit-frame-pointer",
    "-O0",
    "-g",
    "-w",
    # Real inputs (decompiler output, fixtures without prototypes) call
    # functions they never declare; that is an error in clang >= 16 and would
    # otherwise make every such file "not compilable" before the sink is reached.
    "-Wno-error=implicit-function-declaration",
    "-Wno-error=int-conversion",
]
# Headers the harness includes BEFORE the sample, so a fixture that uses
# `int32_t` or `size_t` without including anything still compiles.
STD_HEADERS = "#include <stddef.h>\n#include <stdint.h>\n#include <stdlib.h>\n#include <string.h>\n"
# The sanitizer that can observe each finding kind — and only that one, so the
# replay's report is evidence for THIS finding rather than for whichever
# undefined behaviour happens first on the path. `uninitialized` is resolved at
# run time (MemorySanitizer, else valgrind, else no oracle: see `uninit_oracle`).
SANITIZER_FOR = {
    "buffer": "-fsanitize=address",
    "buffer-read": "-fsanitize=address",
    "index-negative": "-fsanitize=address",
    "index-high": "-fsanitize=address",
    "use-after-free": "-fsanitize=address",
    "divide": "-fsanitize=undefined",
    "shift": "-fsanitize=undefined",
    "signed-overflow": "-fsanitize=undefined",
    "narrowing": "-fsanitize=implicit-conversion",  # clang only
    "alloc-size-wrap": "-fsanitize=unsigned-integer-overflow",  # clang only
    "uninitialized": "-fsanitize=memory",  # clang only, and not on every target
}
CLANG_ONLY = {
    "-fsanitize=implicit-conversion",
    "-fsanitize=unsigned-integer-overflow",
    "-fsanitize=memory",
}
NO_ORACLE = "no runtime oracle available"
_VALUE_RE = re.compile(r"\((\w+)\s+(#b[01]+|#x[0-9a-fA-F]+|\(_ bv(\d+) \d+\))\)")
_LINE_RE = re.compile(r":(\d+):\d+: runtime error")
_REPORT_MARKS = ("ERROR: AddressSanitizer", "WARNING: MemorySanitizer", "runtime error")
# What the sanitizer's report must say for it to be evidence for THIS kind. A
# report of another kind at the same line (`x << n` aborting before `32 - n`
# on one line) is not a replay of the finding, whatever the line number says.
REPORT_FOR = {
    "buffer": ("AddressSanitizer",),
    "buffer-read": ("AddressSanitizer",),
    "index-negative": ("AddressSanitizer",),
    "index-high": ("AddressSanitizer",),
    "use-after-free": ("heap-use-after-free", "double-free", "attempting free"),
    "divide": ("division by zero", "division of"),
    "shift": ("shift exponent", "left shift of"),
    "signed-overflow": ("signed integer overflow", "negation of"),
    "narrowing": ("implicit conversion",),
    "alloc-size-wrap": ("unsigned integer overflow",),
    "uninitialized": ("use-of-uninitialized-value", "uninitialised value"),
}
BOUNDS = (1, 16, 256, 4096)  # smallest witness first: it is the one a reader can check by hand
PYPROJECT = REPO / "pyproject.toml"
_PIN_RE = re.compile(r"^cindergraph\s*@\s*git\+\S+@([0-9a-f]{7,40})$")
# The two lines the gate (`scripts/check-cindergraph-defects.sh`) reads. `RUN`
# carries this driver's own counts so a second reading of `results.tsv` can be
# checked against them; `REPLAY_CONTROL` says whether the replay check refused
# a deliberately wrong line on THIS run.
RUN_LINE = "CINDERGRAPH_DEFECTS_RUN"
CONTROL_LINE = "CINDERGRAPH_DEFECTS_REPLAY_CONTROL"


def pinned_cindergraph() -> str:
    """The commit ``pyproject.toml``'s dev group pins cindergraph to, or ``unknown``."""
    try:
        groups = tomllib.loads(PYPROJECT.read_text()).get("dependency-groups", {})
    except (OSError, tomllib.TOMLDecodeError):
        return "unknown"
    for entry in groups.get("dev", []):
        m = _PIN_RE.match(str(entry).strip())
        if m:
            return m.group(1)
    return "unknown"


def cindergraph_provenance() -> tuple[str, str, str]:
    """``(version, installed commit, pinned commit)``: what this run parsed C with.

    The installed commit comes from the distribution's PEP 610
    ``direct_url.json`` (a git install records ``vcs_info.commit_id``); the
    pinned one from the ``cindergraph @ git+...@<sha>`` entry in
    ``pyproject.toml``'s dev group. Either is ``unknown`` when absent — a wheel
    from an index has no commit, a checkout with the pin removed has nothing to
    compare against — and the gate treats ``unknown`` as a mismatch, never as a
    match.
    """
    try:
        import cindergraph as _cg
    except ImportError:
        return "not-installed", "unknown", pinned_cindergraph()
    version = str(getattr(_cg, "__version__", "unversioned"))
    installed = "unknown"
    try:
        raw = metadata.distribution("cindergraph").read_text("direct_url.json")
        if raw:
            installed = str(json.loads(raw).get("vcs_info", {}).get("commit_id", "unknown"))
    except metadata.PackageNotFoundError:
        pass
    return version, installed, pinned_cindergraph()


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
            check=False,
        )
        lines = [line for line in proc.stdout.splitlines() if line.strip()]
        verdict = lines[0].strip() if lines else "no-output"
        values: dict[str, int] = {}
        if verdict == "sat" and len(lines) > 1:
            for name, lit, dec in _VALUE_RE.findall(lines[1]):
                # `#b…` and `#x…` are Python's own `0b…`/`0x…` spellings with the
                # sigil swapped; base 0 reads the prefix itself.
                values[name] = int(dec) if dec else int("0" + lit[1:], 0)
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


def resolve(term: str, values: dict[str, int]) -> int:
    """A capacity or length term's value: a ``(_ bvN 64)`` literal or a model name."""
    if term.startswith("(_ bv"):
        return int(term[len("(_ bv") :].split()[0])
    return values.get(term, 0)


def harness(sample: Path, lifted: Lifted, values: dict[str, int]) -> str:
    args = []
    setup = []
    for p in lifted.params:
        if p in lifted.pointer_params:
            # A pointer with no annotation and no modelled use (or it would have
            # been refused) gets a small zeroed block: the model never read it.
            n = resolve(lifted.capacities[p], values) if p in lifted.capacities else 64
            size = max(n, 1)
            setup.append(f"    unsigned char *{p} = malloc({size}); memset({p}, 0, {size});")
            if p in lifted.strlens:
                # The annotated string: `strlen` bytes of 'a', then the NUL.
                length = resolve(lifted.strlens[p], values)
                setup.append(f"    memset({p}, 'a', {length}); {p}[{length}] = 0;")
            args.append(f"(void *){p}")
        else:
            t = dict(lifted.scalar_params)[p]
            args.append(c_literal(values.get(p, 0), t))
    return (
        f'{STD_HEADERS}#include "{sample.resolve()}"\n'
        f"int main(void) {{\n"
        + "\n".join(setup)
        + f"\n    volatile long r = (long){lifted.function}({', '.join(args)});\n    (void)r;\n    return 0;\n}}\n"
    )


_UNINIT_ORACLE: dict[str, str | None] = {}


def uninit_oracle(cc: str) -> str | None:
    """How an uninitialised read is observed here: MSan, valgrind, or nothing.

    ``-fsanitize=memory`` exists only in clang and only on some targets, so it
    is probed by compiling and running a program rather than assumed from the
    compiler's name; valgrind is the fallback; with neither, the finding is
    reported as ``no runtime oracle available`` and counted apart from the
    replayed ones — never as a replay.
    """
    if cc in _UNINIT_ORACLE:
        return _UNINIT_ORACLE[cc]
    oracle: str | None = None
    with tempfile.TemporaryDirectory(prefix="axeyum-msan-probe-") as tmp:
        probe = Path(tmp) / "probe.c"
        probe.write_text("int main(void) { return 0; }\n")
        exe = Path(tmp) / "probe"
        comp = subprocess.run(
            [cc, "-fsanitize=memory", "-O0", str(probe), "-o", str(exe)],
            capture_output=True,
            text=True,
            check=False,
        )
        if comp.returncode == 0:
            run = subprocess.run(
                [str(exe)], capture_output=True, text=True, timeout=60, check=False
            )
            if run.returncode == 0:
                oracle = "-fsanitize=memory"
    if oracle is None and shutil.which("valgrind"):
        oracle = "valgrind"
    _UNINIT_ORACLE[cc] = oracle
    return oracle


def sanitizer_report(err: str, sample_name: str, kind: str, line: int) -> tuple[bool, str]:
    """The first sanitizer report in ``err``; True only if it is ``kind``'s report at ``line``."""
    frame_re = re.compile(r"#\d+ .*?" + re.escape(sample_name) + r":(\d+)")
    for report in err.splitlines():
        if any(mark in report for mark in _REPORT_MARKS):
            report = re.sub(r"^==\d+==", "", report).strip()
            report = re.sub(r" on address 0x[0-9a-f]+ at pc .*$", "", report)
            report = re.sub(r"^.*?/(?=" + re.escape(sample_name) + ")", "", report)
            m = _LINE_RE.search(report)
            where = int(m.group(1)) if m else None
            if where is None:
                # An ASan/MSan report names the line in its first user-code stack frame.
                frames = [int(f) for f in frame_re.findall(err)]
                where = frames[0] if frames else None
            if where is not None and where != line:
                return (
                    False,
                    f"sanitizer fired at line {where}, not the finding's line {line}: {report[:120]}",
                )
            if not any(mark in report for mark in REPORT_FOR[kind]):
                return (
                    False,
                    f"sanitizer fired for a different defect at line {where}, not {kind}: {report[:120]}",
                )
            return True, f"{report[:150]} (line {where})" if where is not None else report[:160]
    return False, ""


def valgrind_report(err: str, sample_name: str, line: int) -> tuple[bool, str]:
    frame_re = re.compile(r"\(" + re.escape(sample_name) + r":(\d+)\)")
    for report in err.splitlines():
        if "uninitialised value" in report:
            report = re.sub(r"^==\d+==\s*", "", report).strip()
            frames = [int(f) for f in frame_re.findall(err)]
            where = frames[0] if frames else None
            if where is not None and where != line:
                return False, f"valgrind fired at line {where}, not the finding's line {line}"
            return True, f"valgrind: {report[:120]} (line {where})"
    return False, ""


def replay(
    cc: str, source: Path, out: Path, kind: str, line: int, sample_name: str
) -> tuple[bool | None, str]:
    """Compile with the one sanitizer that observes ``kind``; True only if it fires at ``line``.

    ``None`` means no oracle exists on this host for this kind: the finding
    is neither replayed nor refuted, and the driver counts it separately.
    """
    exe = out.with_suffix("")
    san = SANITIZER_FOR[kind]
    if san == "-fsanitize=memory":
        oracle = uninit_oracle(cc)
        if oracle is None:
            return None, f"{NO_ORACLE}: neither -fsanitize=memory nor valgrind"
        san = oracle
    if san in CLANG_ONLY and "clang" not in cc:
        return None, f"{NO_ORACLE}: {kind} needs clang's {san}"
    flags = [] if san == "valgrind" else [san]
    comp = subprocess.run(
        [cc, *flags, *COMMON, str(source), "-o", str(exe)],
        capture_output=True,
        text=True,
        check=False,
    )
    if comp.returncode != 0:
        last = comp.stderr.strip().splitlines()[-1][:160]
        # Whose fault: the input's, or the harness's? A sample that does not
        # compile on its own (decompiler pseudo-types, missing prototypes) has
        # no runtime oracle; a sample that does, wrapped in a main that does
        # not, is a harness bug and a failed replay.
        alone = subprocess.run(
            [cc, "-fsyntax-only", *COMMON, "-x", "c", "-"],
            input=source.read_text().split("\nint main(void)", 1)[0],
            capture_output=True,
            text=True,
            check=False,
        )
        if alone.returncode != 0:
            return None, f"{NO_ORACLE}: the input does not compile as C ({last})"
        undefined = re.findall(r"undefined reference to `([^']+)'", comp.stderr)
        if undefined:
            # It compiles but calls functions nothing defines (decompiler
            # pseudo-calls, other translation units): no program to run.
            return None, f"{NO_ORACLE}: the input calls undefined {sorted(set(undefined))}"
        return False, f"harness compile failed: {last}"
    if san == "valgrind":
        run = subprocess.run(
            ["valgrind", "-q", "--error-exitcode=99", str(exe)],
            capture_output=True,
            text=True,
            timeout=300,
            check=False,
        )
        ok, report = valgrind_report(run.stderr, sample_name, line)
    else:
        run = subprocess.run([str(exe)], capture_output=True, text=True, timeout=60, check=False)
        ok, report = sanitizer_report(run.stderr, sample_name, kind, line)
    if report:
        return ok, report
    return False, f"exit {run.returncode}, no sanitizer report"


def expectations(src: str) -> dict[str, str]:
    """``// expect: <function> <finding|clean|refused|bounded>`` lines, if the sample carries them."""
    return {
        m.group(1): m.group(2)
        for m in re.finditer(r"//\s*expect:\s*(\w+)\s+(finding|clean|refused|bounded)", src)
    }


def normalize_reason(why: str) -> str:
    """A refusal reason with its identifiers blanked, so a histogram groups by construct."""
    why = re.sub(r"^line \d+: ", "", why)
    why = re.sub(r"'[^']*'", "'…'", why)
    why = re.sub(r"\d+", "N", why)
    return why


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
    ap.add_argument(
        "--unroll",
        type=int,
        default=DEFAULT_UNROLL,
        help="loop unrolling bound (a file's `// axeyum: unroll = N` overrides it)",
    )
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
    version, installed, pinned = cindergraph_provenance()
    # The first line of a run says what it ran against: the parser's version,
    # the commit it was installed from, and the commit `pyproject.toml` pins.
    # Nothing here refuses a mismatch -- this is an example that should run
    # against a local cindergraph checkout too -- but the gate does.
    print(
        f"cindergraph|version={version}|commit={installed}|pinned={pinned}"
        f"|match={'yes' if installed != 'unknown' and installed == pinned else 'no'}"
    )
    args.out.mkdir(parents=True, exist_ok=True)
    rows: list[tuple[str, ...]] = []
    # The first replayed witness's harness, kept for the control after the sweep.
    control: tuple[Path, str, int, str] | None = None
    failures = 0
    replayed = 0
    unoracled = 0
    refusals: Counter[str] = Counter()
    for sample in sorted(args.samples.rglob("*.c")):
        src = sample.read_text(errors="replace")
        expect = expectations(src)
        try:
            items = lift_source(src, unroll=args.unroll)
        except RuntimeError as e:
            # cindergraph could not parse the file: every function in it is unreached.
            rows.append((sample.name, "-", "parse-error", "-", "-", str(e)[:200]))
            refusals[normalize_reason(str(e)[:80])] += 1
            continue
        for item in items:
            if isinstance(item, tuple):
                name, why = item
                rows.append((sample.name, name, "refused", "-", "-", str(why)))
                refusals[normalize_reason(why.why)] += 1
                if expect.get(name, "refused") != "refused":
                    failures += 1
                continue
            lifted: Lifted = item
            witnesses = 0
            seen: set[tuple[int, str]] = set()
            findings: list[tuple[str, ...]] = []
            # A dead branch is one whose edge is infeasible on EVERY path that
            # reaches it — inside an unrolled loop that is every iteration, so
            # verdicts are gathered per (line, edge) and judged after the sweep.
            edges: dict[tuple[int, str, str], list[str]] = {}
            bound_hit: dict[tuple[int, str], bool] = {}
            tag = f"; unrolled to {lifted.unrolled}" if lifted.unrolled else ""
            for k, q in enumerate(lifted.queries):
                ob = q.obligation
                verdict, values = solve(backend, q, args.timeout_ms)
                (args.out / f"{sample.stem}.{lifted.function}.{k}.smt2").write_text(q.smtlib)
                if ob.kind == "dead-branch":
                    # The query asks "is this edge reachable"; unsat means dead.
                    edges.setdefault((ob.line, ob.text, ob.note), []).append(verdict)
                    continue
                if ob.kind == "loop-bound":
                    # The query asks "does some input still loop after K iterations".
                    bound_hit[(ob.line, ob.text)] = (
                        bound_hit.get((ob.line, ob.text), False) or verdict != "unsat"
                    )
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
                ok, report = replay(
                    args.cc, hsrc, hsrc.with_suffix(".bin"), ob.kind, ob.line, sample.name
                )
                inputs = ", ".join(
                    f"{p}={c_literal(values.get(p, 0), t)}" for p, t in lifted.scalar_params
                )
                caps = ", ".join(
                    f"cap({p})={resolve(lifted.capacities[p], values)}"
                    for p in lifted.pointer_params
                    if p in lifted.capacities and not lifted.capacities[p].startswith("(_ bv")
                )
                status = (
                    "REPLAYED: "
                    if ok
                    else "NO RUNTIME ORACLE: "
                    if ok is None
                    else "DID NOT REPLAY: "
                )
                findings.append(
                    (
                        sample.name,
                        lifted.function,
                        ob.kind,
                        f"line {ob.line}",
                        f"`{ob.text}` with {inputs}{'; ' + caps if caps else ''}{tag}",
                        status + report,
                    )
                )
                if ok:
                    replayed += 1
                    if control is None:
                        control = (hsrc, ob.kind, ob.line, sample.name)
                elif ok is None:
                    unoracled += 1
                else:
                    failures += 1
            for (line, text, note), verdicts in edges.items():
                if all(v == "unsat" for v in verdicts):
                    findings.append(
                        (
                            sample.name,
                            lifted.function,
                            "dead-branch",
                            f"line {line}",
                            f"`{text}` {note} is infeasible{tag}",
                            "proved unreachable (no replay: nothing executes)",
                        )
                    )
                    witnesses += 1
            bounded_loops = [key for key, hit in bound_hit.items() if hit]
            for line, text in bounded_loops:
                findings.append(
                    (
                        sample.name,
                        lifted.function,
                        "bounded",
                        f"line {line}",
                        f"`{text}` can still hold after {lifted.unrolled} iterations",
                        f"bounded: no witness within {lifted.unrolled} iterations",
                    )
                )
            if findings:
                rows.extend(findings)
            else:
                rows.append(
                    (
                        sample.name,
                        lifted.function,
                        "clean",
                        "-",
                        f"{len(lifted.queries)} obligations over {lifted.paths} paths, all unsat{tag}",
                        "no witness within the model",
                    )
                )
            want = expect.get(lifted.function)
            met = {
                None: True,
                "finding": witnesses > 0,
                "clean": witnesses == 0 and not bounded_loops,
                "bounded": witnesses == 0 and bool(bounded_loops),
                "refused": False,
            }[want]
            if not met:
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
    # The control on the replay check itself: the same harness, judged against
    # the line AFTER its finding, must come back refused. A `replay()` that
    # always says yes, or one that stopped reading the line out of the report,
    # passes every row above and fails exactly here. Without a replayed
    # witness there is nothing to control, and that is printed as NOT-RUN, not
    # as a pass; the gate requires `refused`.
    if control is not None:
        hsrc, kind, line, sample_name = control
        accepted, why = replay(
            args.cc, hsrc, hsrc.with_suffix(".ctl.bin"), kind, line + 1, sample_name
        )
        verdict = "refused" if accepted is False else "ACCEPTED" if accepted else "NO-ORACLE"
        if accepted is not False:
            failures += 1
        print(
            f"{CONTROL_LINE}|witness={sample_name}:{line}|judged_at={line + 1}|{verdict}|{why[:100]}"
        )
    else:
        print(f"{CONTROL_LINE}|witness=none|judged_at=-|NOT-RUN|no replayed witness to control")
    print("| sample | function | finding | where | witness | replay |")
    print("|---|---|---|---|---|---|")
    for r in rows:
        print("| " + " | ".join(str(c).replace("|", "\\|") for c in r) + " |")
    (args.out / "results.tsv").write_text("\n".join("\t".join(r) for r in rows) + "\n")
    kinds = Counter(r[2] for r in rows)
    print(
        f"{RUN_LINE}|rows={len(rows)}|replayed={replayed}|dead={kinds.get('dead-branch', 0)}"
        f"|clean={kinds.get('clean', 0)}|bounded={kinds.get('bounded', 0)}"
        f"|no_oracle={unoracled}|refused={kinds.get('refused', 0)}|failures={failures}"
    )
    print(
        f"\n{len(rows)} rows ({', '.join(f'{k} {n}' for k, n in sorted(kinds.items()))}); "
        f"{replayed} replayed, {unoracled} without a runtime oracle, {failures} failure(s); "
        f"queries and harnesses in {args.out}",
        file=sys.stderr,
    )
    if refusals:
        print("\nrefusal reasons (first blocking construct per function):", file=sys.stderr)
        for reason, n in refusals.most_common():
            print(f"  {n:4d}  {reason}", file=sys.stderr)
        (args.out / "refusals.tsv").write_text(
            "".join(f"{n}\t{reason}\n" for reason, n in refusals.most_common())
        )
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
