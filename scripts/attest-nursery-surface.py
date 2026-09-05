#!/usr/bin/env python3
"""Re-elaborate nursery `formal.statement` rows as proof-free axioms against a real Mathlib.

This is the SAME method `create-autogenesis-mathlib-fact-catalog.py` records in
`surface_validation.method` for nursery-v1: declare every statement as an `axiom`
after `import Mathlib`, reading no theorem value and no proof. Acceptance is
syntax/type evidence about the STATEMENT, never proof evidence about the claim.

Why this script exists
----------------------
A pretty-printed type is not guaranteed to re-parse. A manifest row whose
`statement` was quoted byte-identically from an extractor's `type` field is
bound to its source by a checksum, but nothing has confirmed Lean will accept
the string back. Only an elaboration run can, and that needs a BUILT Mathlib at
the pinned commit, which most hosts here do not have.

HOST REQUIREMENT
----------------
A Mathlib checkout at the pinned commit WITH `.lake/build` populated. As of
2026-08-29 that is **s5** only:

    ~/lean-import-scale/mathlib4        c5ea00351c28e24afc9f0f84379aa41082b1188f
    ~/lean-import-scale/mathlib4/.lake/build   6.2 GB
    ~/.elan/toolchains/leanprover--lean4---v4.30.0

`scripts/provision-lean-import-toolchain.sh` provisions a checkout on other
hosts but does NOT build Mathlib, so it is not sufficient for this script.

`command -v lean` RETURNS NOTHING ON A HOST THAT HAS LEAN -- elan does not put
toolchains on PATH. Never conclude a host cannot do this from an empty
`command -v`; use `scripts/check-lean-gate.sh --print-toolchain`, or the
`--toolchain` default below.

Usage
-----
    # full run against s5 (default), all rows
    python3 scripts/attest-nursery-surface.py --manifest artifacts/autogenesis/nursery-v2-extension.json

    # a bounded subset when you need an answer fast
    python3 scripts/attest-nursery-surface.py --limit 20

    # emit the module without running anything
    python3 scripts/attest-nursery-surface.py --emit-only --out /tmp/surface.lean

Exit status
-----------
0  every row elaborated
1  at least one row did not elaborate (the rows and their errors are printed)
2  the host could not run Lean at all (setup failure, distinct from a row failure)

The status depends on WHAT THE RUN FOUND, not on the run completing.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import shlex
import subprocess
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from lean_surface_screen import Finding, screen_statement  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
DEFAULT_MANIFEST = ROOT / "artifacts/autogenesis/nursery-v2-extension.json"
DEFAULT_HOST = "s5"
DEFAULT_MATHLIB = "~/lean-import-scale/mathlib4"
DEFAULT_TOOLCHAIN = "~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean"
DEFAULT_LAKE = "~/.elan/bin/lake"

# A statement Lean must reject. Without it a run that elaborates nothing at all
# -- a stub `lean`, an empty module, a swallowed error stream -- looks identical
# to a clean pass. The harness fails if this is ever accepted.
NEGATIVE_CONTROL = "∀ (n : ℕ), Nat.axeyumThisSymbolDoesNotExist n = n"


class AttestError(RuntimeError):
    pass


def load_rows(manifest: pathlib.Path) -> list[dict]:
    data = json.loads(manifest.read_text())
    entries = data.get("entries")
    if not isinstance(entries, list) or not entries:
        raise AttestError(f"{manifest} has no `entries` list")
    rows = []
    for entry in entries:
        for field in ("fact_id", "statement", "source_name"):
            if field not in entry:
                raise AttestError(f"entry missing `{field}`: {entry.get('fact_id', '?')}")
        rows.append(entry)
    return rows


def screen_rows(rows: list[dict]) -> list[tuple[str, list[Finding]]]:
    """Every manifest row the surface screen flags, with its findings.

    Rows are returned, not removed: the caller still elaborates them. This
    exists so a flagged row is NAMED before a 3.6-second remote round trip on
    the one host with a built Mathlib tells you the same thing as an opaque
    Lean diagnostic.
    """
    flagged = []
    for row in rows:
        findings = screen_statement(row["statement"])
        if findings:
            flagged.append((row["fact_id"], findings))
    return flagged


def axiom_name(index: int, fact_id: str) -> str:
    """A Lean-legal identifier that still names its row.

    Fact ids carry `:` and `-`, neither of which is a legal Lean identifier
    character, so the id is sanitized and the index keeps names unique even if
    two ids sanitize to the same string.
    """
    slug = re.sub(r"[^0-9A-Za-z]+", "_", fact_id).strip("_")
    return f"axeyum_surface_{index:04d}_{slug}"


def render_module(rows: list[dict], *, with_negative_control: bool = True) -> tuple[str, dict[int, dict]]:
    """Return the Lean module text and a map from 1-based LINE NUMBER to row.

    Every axiom occupies exactly one line so a Lean diagnostic of the form
    `file:LINE:COL: error:` maps back to a row without any guessing. Statements
    containing newlines are collapsed to a single line; Lean's grammar is
    whitespace-insensitive here, and this keeps the mapping total.
    """
    lines: list[str] = []
    lines.append("-- GENERATED by scripts/attest-nursery-surface.py. Do not edit.")
    lines.append("-- Proof-free surface attestation: every statement is declared as an axiom.")
    lines.append("-- No theorem value and no proof is read. Acceptance is syntax/type evidence.")
    lines.append("import Mathlib")
    lines.append("set_option linter.all false")
    line_map: dict[int, dict] = {}

    if with_negative_control:
        lines.append(f"axiom axeyum_negative_control : {NEGATIVE_CONTROL}")
        line_map[len(lines)] = {"fact_id": "<negative-control>", "negative_control": True}

    for index, row in enumerate(rows):
        statement = " ".join(row["statement"].split())
        lines.append(f"axiom {axiom_name(index, row['fact_id'])} : {statement}")
        line_map[len(lines)] = row
    return "\n".join(lines) + "\n", line_map


# Lean 4.30 tags diagnostics: `error(lean.unknownIdentifier): Unknown constant ...`.
# A regex demanding a bare `error:` matches NOTHING, so every row reports as
# elaborated and the run looks like a clean pass. That is exactly what happened
# on the first real run here, and only NEGATIVE_CONTROL distinguished it from a
# genuine 160/160. The tag group is therefore optional, and the negative control
# is not optional.
DIAGNOSTIC = re.compile(
    r"^(?P<file>[^\s:]+):(?P<line>\d+):(?P<col>\d+):\s*(?P<sev>error|warning)(?:\([^)]*\))?:\s*(?P<msg>.*)$"
)


def parse_diagnostics(output: str) -> dict[int, list[str]]:
    """Group Lean diagnostics by source line. Continuation lines attach to the last one."""
    by_line: dict[int, list[str]] = {}
    current: list[str] | None = None
    for raw in output.splitlines():
        match = DIAGNOSTIC.match(raw)
        if match:
            if match.group("sev") != "error":
                current = None
                continue
            current = by_line.setdefault(int(match.group("line")), [])
            current.append(f"{match.group('col')}: {match.group('msg')}")
        elif raw.startswith("AXEYUM_"):
            # Our own remote-script sentinels. Without this they attach to the
            # last diagnostic as continuation lines and end up quoted inside the
            # manifest as if Lean had said them.
            current = None
        elif current is not None and raw.strip():
            current.append(f"    {raw.rstrip()}")
    return by_line


def run_remote(host: str, script: str, *, timeout: int) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["ssh", "-o", "BatchMode=yes", host, "bash", "-s"],
        input=script,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def build_remote_script(module: str, *, mathlib: str, lake: str, toolchain: str, remote_path: str) -> str:
    """A remote script that writes the module and elaborates it.

    The heredoc terminator is quoted so nothing in the module is expanded by the
    remote shell -- these statements are full of `$`-free but backtick-adjacent
    unicode, and an expanding heredoc would silently rewrite them.
    """
    return "\n".join(
        [
            "set -u",
            f"cd {mathlib} || {{ echo 'AXEYUM_SETUP_FAIL: no mathlib checkout'; exit 90; }}",
            f"cat > {shlex.quote(remote_path)} <<'AXEYUM_MODULE_EOF'",
            module.rstrip("\n"),
            "AXEYUM_MODULE_EOF",
            f"test -x {toolchain} || {{ echo 'AXEYUM_SETUP_FAIL: no lean toolchain'; exit 91; }}",
            "test -d .lake/build || { echo 'AXEYUM_SETUP_FAIL: mathlib is not built'; exit 92; }",
            "echo AXEYUM_COMMIT=$(git rev-parse HEAD)",
            f"echo AXEYUM_LEAN_VERSION=$({toolchain} --version | head -1)",
            "echo AXEYUM_LEAN_BEGIN",
            f"{lake} env {toolchain} {shlex.quote(remote_path)}",
            "status=$?",
            "echo AXEYUM_LEAN_END",
            "echo AXEYUM_LEAN_EXIT=$status",
            "exit $status",
        ]
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--manifest", type=pathlib.Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--host", default=DEFAULT_HOST, help="ssh host with a BUILT Mathlib (default: s5)")
    parser.add_argument("--mathlib", default=DEFAULT_MATHLIB)
    parser.add_argument("--lake", default=DEFAULT_LAKE)
    parser.add_argument("--toolchain", default=DEFAULT_TOOLCHAIN)
    parser.add_argument("--limit", type=int, default=0, help="attest only the first N rows (a SUBSET; say so when reporting)")
    parser.add_argument(
        "--only",
        action="append",
        default=[],
        metavar="FACT_ID",
        help="attest ONLY these fact ids -- isolates a suspected row from its neighbours",
    )
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        metavar="FACT_ID",
        help="drop these fact ids. Use after a failure to confirm the remaining rows pass on "
        "their own: a PARSE error can desync Lean's parser and swallow following lines, which "
        "would report them as elaborated when they were never read.",
    )
    parser.add_argument("--emit-only", action="store_true", help="write the module and exit without running Lean")
    parser.add_argument(
        "--screen-only",
        action="store_true",
        help="run only the extraction-time surface screen (no Lean, no ssh, any host); "
        "exits 1 when a row is flagged",
    )
    parser.add_argument("--out", type=pathlib.Path, help="also write the generated module here")
    parser.add_argument("--json-out", type=pathlib.Path, help="write a machine-readable result record here")
    parser.add_argument("--timeout", type=int, default=3600)
    parser.add_argument("--no-negative-control", action="store_true", help="diagnostic only; a run without it proves less")
    args = parser.parse_args()

    rows = load_rows(args.manifest)
    total_rows = len(rows)

    known = {row["fact_id"] for row in rows}
    for fact_id in list(args.only) + list(args.exclude):
        if fact_id not in known:
            raise AttestError(f"--only/--exclude names {fact_id}, which is not in {args.manifest}")
    if args.only:
        rows = [row for row in rows if row["fact_id"] in set(args.only)]
    if args.exclude:
        rows = [row for row in rows if row["fact_id"] not in set(args.exclude)]
    if args.limit:
        rows = rows[: args.limit]
    if not rows:
        raise AttestError("selection left no rows to attest")
    subset = len(rows) < total_rows

    module, line_map = render_module(rows, with_negative_control=not args.no_negative_control)
    module_sha = hashlib.sha256(module.encode()).hexdigest()

    if args.out:
        args.out.write_text(module)
        print(f"module written: {args.out}")
    print(f"manifest         {args.manifest}")
    print(f"rows attested    {len(rows)} of {total_rows}{'  (SUBSET)' if subset else ''}")
    print(f"module sha256    {module_sha}")

    # The extraction-time screen (ADR-1662). It runs BEFORE Lean and needs no
    # Lean: both classes it detects are visible in the statement text, so a host
    # without a built Mathlib -- every host but one -- can learn what this run
    # would fail on. A flagged row is still sent to Lean and never modified;
    # ADR-0615 forbids editing a preregistered `formal.statement`, and a row
    # dropped from a run is a coverage change nobody recorded.
    screened = screen_rows(rows)
    print(f"surface screen   {len(screened)} of {len(rows)} rows flagged")
    for fact_id, findings in screened:
        for finding in findings:
            print(f"  SCREEN  {fact_id}  {finding.screen_class}/{finding.signature}  {finding.evidence}")

    if args.screen_only:
        # Exit status depends on the FINDING: a clean screen is 0, a flagged
        # row is 1. Without that this mode would pass on every input and be
        # worse than not having run it.
        print(
            "VERDICT: SCREEN ONLY -- no Lean was run, so nothing here is an "
            "attestation; this reports only what the screen can see."
        )
        return 1 if screened else 0

    if args.emit_only:
        return 0

    remote_path = f"/tmp/axeyum-surface-{module_sha[:16]}.lean"
    script = build_remote_script(
        module, mathlib=args.mathlib, lake=args.lake, toolchain=args.toolchain, remote_path=remote_path
    )

    started = time.time()
    try:
        proc = run_remote(args.host, script, timeout=args.timeout)
    except subprocess.TimeoutExpired:
        print(f"SETUP/RUN FAILURE: no result within {args.timeout}s on {args.host}", file=sys.stderr)
        return 2
    elapsed = time.time() - started

    combined = proc.stdout + proc.stderr
    if "AXEYUM_SETUP_FAIL" in combined or proc.returncode in (90, 91, 92, 255):
        print(f"SETUP FAILURE on {args.host} (exit {proc.returncode}):", file=sys.stderr)
        print(combined.strip(), file=sys.stderr)
        return 2

    commit = next((l.split("=", 1)[1] for l in combined.splitlines() if l.startswith("AXEYUM_COMMIT=")), "?")
    lean_version = next(
        (l.split("=", 1)[1] for l in combined.splitlines() if l.startswith("AXEYUM_LEAN_VERSION=")), "?"
    )
    print(f"host             {args.host}")
    print(f"mathlib commit   {commit}")
    print(f"lean             {lean_version}")
    print(f"elapsed          {elapsed:.1f}s")

    by_line = parse_diagnostics(combined)

    negative_line = next((ln for ln, row in line_map.items() if row.get("negative_control")), None)
    negative_ok = True
    if negative_line is not None:
        negative_ok = negative_line in by_line
        verdict = "REJECTED (good)" if negative_ok else "ACCEPTED -- THE HARNESS IS NOT DISCRIMINATING"
        print(f"negative control {verdict}")

    failures: list[tuple[dict, list[str]]] = []
    for line, row in sorted(line_map.items()):
        if row.get("negative_control"):
            continue
        if line in by_line:
            failures.append((row, by_line[line]))

    unattributed = sorted(ln for ln in by_line if ln not in line_map)

    passed = len(rows) - len(failures)
    print(f"elaborated       {passed} of {len(rows)}")
    print(f"failed           {len(failures)}")
    if unattributed:
        print(f"unattributed errors on lines {unattributed} -- the line map did not cover these")

    for row, messages in failures:
        print()
        print(f"FAILED  {row['fact_id']}")
        print(f"  source_name  {row.get('source_name')}")
        print(f"  family       {row.get('family')}  partition={row.get('partition')}")
        print(f"  statement    {row['statement']}")
        for message in messages:
            print(f"  lean         {message}")

    if args.json_out:
        args.json_out.write_text(
            json.dumps(
                {
                    "kind": "axeyum-nursery-surface-attestation",
                    "manifest": str(args.manifest.relative_to(ROOT)) if args.manifest.is_absolute() else str(args.manifest),
                    "host": args.host,
                    "mathlib_commit": commit,
                    "lean_version": lean_version,
                    "module_sha256": module_sha,
                    # Which rows this run actually READ. A consumer must not
                    # infer coverage from a count: a later draw grows the
                    # manifest, and a row this run never saw has to be
                    # distinguishable from one it saw and accepted.
                    "attested_fact_ids": sorted(row["fact_id"] for row in rows),
                    "rows_attested": len(rows),
                    "rows_in_manifest": total_rows,
                    "subset": subset,
                    "elaborated": passed,
                    "failed": len(failures),
                    "negative_control_rejected": negative_ok,
                    "elapsed_seconds": round(elapsed, 1),
                    "failures": [
                        {"fact_id": r["fact_id"], "source_name": r.get("source_name"), "statement": r["statement"], "lean": m}
                        for r, m in failures
                    ],
                },
                indent=2,
                ensure_ascii=False,
                sort_keys=True,
            )
            + "\n"
        )
        print(f"json written     {args.json_out}")

    if not negative_ok:
        print("VERDICT: NOT ATTESTED -- the negative control was accepted, so nothing here is evidence.")
        return 1
    if failures or unattributed:
        print("VERDICT: NOT ATTESTED -- see the failing rows above.")
        return 1
    scope = f"{len(rows)} of {total_rows} rows" if subset else f"all {len(rows)} rows"
    if negative_line is None:
        # A run with no row that MUST fail cannot distinguish "everything
        # elaborated" from "the harness saw nothing". That is not a quibble
        # here: it is exactly what happened on this script's first real run,
        # when the diagnostic regex missed Lean 4.30's tagged `error(...)`. So
        # the verdict says so rather than reading as an attestation.
        print(f"VERDICT: NOT AN ATTESTATION -- {scope} produced no diagnostics, "
              f"but the negative control was disabled, so this run cannot "
              f"distinguish that from a harness that sees nothing.")
        return 1
    print(f"VERDICT: ATTESTED -- {scope} elaborate as proof-free axioms against Mathlib {commit[:12]}.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except AttestError as exc:
        print(f"error: {exc}", file=sys.stderr)
        sys.exit(2)
