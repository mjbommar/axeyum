#!/usr/bin/env python3
"""Run every `F:ml430-*` mirror statement through the statement-only import route.

This is the measurement behind *Next Ten item 5* in
`docs/math-department/14-lean-lang.md`: for each mirror, does its
`formal.statement` cross into this kernel as a goal, and if not, what TYPED
reason stopped it?

The route is the real one, not a proxy. Each statement becomes the value of a
transparent `def <goal> : Prop` after `import Mathlib`, exactly as ADR-0604 §2's
worked example does; official Lean elaborates it, official `lean4export` emits
the definition's own declaration closure, and
`axeyum_lean_import::import_statement_ndjson` admits or declines the stream. No
proof value is ever read and nothing is proved -- this measures whether a
STATEMENT is expressible here.

Two hosts, because they must be. A built Mathlib is 6 GB of oleans and lives on
one fleet host (`--host`, default `s5`); the importer is this checkout. So the
Lean half runs over ssh and the streams come back as a tarball.

Phases (`--phase`, default `all`):

    elaborate  emit one module holding every selected statement, elaborate it,
               and attribute each diagnostic to its row by LINE NUMBER
    export     rebuild the module from the rows that elaborated, compile it to
               an olean, and export one stream per target
    import     run the streams through `import_statement_ndjson`
    classify   fold the three phases into one typed verdict per row
    publish    write the census artifact and its markdown summary

Every phase writes its result under `--work`, so a later phase can be re-run
without repeating an earlier one.

Exit status is 0 when the census completed, 1 when a phase produced no usable
result, and 2 when the remote host could not run Lean at all. A DECLINE is never
a nonzero exit -- the declines are the finding.
"""

from __future__ import annotations

import argparse
import collections
import json
import pathlib
import re
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parent.parent

DEFAULT_HOST = "s5"
DEFAULT_MATHLIB = "~/lean-import-scale/mathlib4"
DEFAULT_LEAN4EXPORT = "~/lean-import-scale/lean4export"
DEFAULT_LEAN = "~/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean"
DEFAULT_LAKE = "~/.elan/bin/lake"

# A statement Lean must reject. Without it, a run in which NOTHING elaborated --
# a stub `lean`, an empty module, a swallowed error stream -- is indistinguishable
# from a clean pass. Same control, and same reason, as
# `scripts/attest-nursery-surface.py`.
NEGATIVE_CONTROL = "∀ (n : ℕ), Nat.axeyumThisSymbolDoesNotExist n = n"

# Lean 4.30 tags diagnostics `error(lean.unknownIdentifier):`, so a regex
# demanding a bare `error:` matches nothing and every row reports as elaborated.
# The tag group is optional here for exactly that reason.
DIAGNOSTIC = re.compile(
    r"^(?P<file>[^\s:]+):(?P<line>\d+):(?P<col>\d+):\s*"
    r"(?P<sev>error|warning)(?:\([^)]*\))?:\s*(?P<msg>.*)$"
)


def goal_name(index: int) -> str:
    return f"axeyumCensusGoal{index:04d}"


# --------------------------------------------------------------------------
# Elaboration-side classes
# --------------------------------------------------------------------------

# Ordered most specific first; the last entry matches anything, so a row is
# never left unclassified. The first three are the classes
# `scripts/lean_surface_screen.py` screens for at extraction time.
#
# `coercion-variable-block` and `field-notation-variable-block` have the SAME
# root cause -- statement-only extraction drops Mathlib's enclosing `variable`
# block, so `↑a` and `a.choose` have no type to elaborate against -- but they are
# counted separately because Lean's diagnostic differs and a reader must be able
# to match a class back to the message it came from.
ELABORATION_CLASSES: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("coercion-variable-block", re.compile(r"invalid coercion notation", re.IGNORECASE)),
    (
        "field-notation-variable-block",
        re.compile(r"[Ii]nvalid field notation.*is not known", re.DOTALL),
    ),
    (
        "elided-proof-glyph",
        re.compile(r"[⋯✝]|don't know how to synthesize placeholder", re.IGNORECASE),
    ),
    ("unknown-identifier", re.compile(r"[Uu]nknown (constant|identifier)")),
    ("ambiguous-notation", re.compile(r"ambiguous", re.IGNORECASE)),
    (
        "instance-or-typeclass",
        re.compile(r"failed to synthesize|typeclass instance", re.IGNORECASE),
    ),
    ("parse-error", re.compile(r"unexpected (token|character)|expected", re.IGNORECASE)),
    ("elaboration-other", re.compile(r".", re.DOTALL)),
)


def elaboration_class(messages: list[str]) -> str:
    joined = "\n".join(messages)
    for name, pattern in ELABORATION_CLASSES:
        if pattern.search(joined):
            return name
    return "elaboration-other"


# --------------------------------------------------------------------------
# Remote plumbing
# --------------------------------------------------------------------------


def run_remote(host: str, script: str, *, timeout: int) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["ssh", "-o", "BatchMode=yes", host, "bash", "-s"],
        input=script,
        capture_output=True,
        text=True,
        timeout=timeout,
    )


def render_module(rows: list[dict], *, with_negative_control: bool) -> tuple[str, dict[int, dict]]:
    """The Lean module, and a map from 1-based LINE NUMBER to the row on it.

    Every goal occupies exactly one line, so a `file:LINE:COL: error:` maps back
    to its row with no guessing. Statements are whitespace-collapsed to keep that
    mapping total; Lean's grammar is whitespace-insensitive here.
    """
    lines = [
        "-- GENERATED by scripts/run-statement-import-blocker-census.py. Do not edit.",
        "-- Statement-only census: every mirror statement is the VALUE of a",
        "-- transparent `def _ : Prop`. No theorem value and no proof is read.",
        "import Mathlib",
        "set_option linter.all false",
    ]
    line_map: dict[int, dict] = {}
    if with_negative_control:
        lines.append(f"def axeyumCensusNegativeControl : Prop := {NEGATIVE_CONTROL}")
        line_map[len(lines)] = {"fact_id": "<negative-control>", "negative_control": True}
    for row in rows:
        statement = " ".join(row["statement"].split())
        lines.append(f"def {row['goal']} : Prop := {statement}")
        line_map[len(lines)] = row
    return "\n".join(lines) + "\n", line_map


def parse_diagnostics(output: str) -> dict[int, list[str]]:
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
            current = None
        elif current is not None and raw.strip():
            current.append(raw.strip())
    return by_line


def remote_prelude(args, module_name: str) -> list[str]:
    """Shell variable assignments for every remote path.

    Paths are emitted as `$HOME`-relative ASSIGNMENTS rather than interpolated
    into each command, because a `~` inside a quoted word is not expanded by the
    remote shell: `cat > '~/mathlib4/M.lean'` silently creates nothing and the
    elaboration then reports a missing file, not a Lean verdict. Measured here on
    the first pilot run.
    """

    def expand(path: str) -> str:
        return path.replace("~/", "$HOME/", 1) if path.startswith("~/") else path

    return [
        "set -u",
        f'ML="{expand(args.mathlib)}"',
        f'EX="{expand(args.lean4export)}"',
        f'LEAN="{expand(args.lean)}"',
        f'LAKE="{expand(args.lake)}"',
        f'MOD="{module_name}"',
        f'WORK="{expand(args.remote_work)}"',
        'cd "$ML" || { echo "AXEYUM_SETUP_FAIL: no mathlib checkout"; exit 90; }',
        'test -d .lake/build || { echo "AXEYUM_SETUP_FAIL: mathlib is not built"; exit 92; }',
        'test -x "$LEAN" || { echo "AXEYUM_SETUP_FAIL: no lean toolchain"; exit 91; }',
    ]


def elaborate_script(module: str, *, args, module_name: str) -> str:
    """Write the module INSIDE the Mathlib root and elaborate it.

    Inside the root because `lean` refuses an input file outside the lakefile's
    root directory; the file is removed again whatever happens. The heredoc
    terminator is quoted so the remote shell expands nothing -- these statements
    are full of unicode and backtick-adjacent text.
    """
    return "\n".join(
        [
            *remote_prelude(args, module_name),
            'cat > "$ML/$MOD.lean" <<\'AXEYUM_MODULE_EOF\'',
            module.rstrip("\n"),
            "AXEYUM_MODULE_EOF",
            "echo AXEYUM_COMMIT=$(git rev-parse HEAD)",
            'echo AXEYUM_LEAN_VERSION=$("$LEAN" --version | head -1)',
            "echo AXEYUM_LEAN_BEGIN",
            '"$LAKE" env "$LEAN" "$ML/$MOD.lean"',
            "status=$?",
            "echo AXEYUM_LEAN_END",
            "echo AXEYUM_LEAN_EXIT=$status",
            'rm -f "$ML/$MOD.lean"',
            "exit $status",
        ]
    )


def export_script(module: str, goals: list[str], *, args, module_name: str) -> str:
    return "\n".join(
        [
            *remote_prelude(args, module_name),
            'rm -rf "$WORK"; mkdir -p "$WORK/streams" || exit 90',
            'OLEAN="$ML/.lake/build/lib/lean/$MOD.olean"',
            'cat > "$ML/$MOD.lean" <<\'AXEYUM_MODULE_EOF\'',
            module.rstrip("\n"),
            "AXEYUM_MODULE_EOF",
            'cat > "$WORK/goals.txt" <<\'AXEYUM_GOALS_EOF\'',
            "\n".join(goals),
            "AXEYUM_GOALS_EOF",
            "echo AXEYUM_OLEAN_BEGIN",
            '"$LAKE" env "$LEAN" -o "$OLEAN" "$ML/$MOD.lean"',
            "olean_status=$?",
            "echo AXEYUM_OLEAN_EXIT=$olean_status",
            "if [ $olean_status -ne 0 ]; then",
            '  rm -f "$ML/$MOD.lean" "$OLEAN"',
            "  exit $olean_status",
            "fi",
            "echo AXEYUM_EXPORT_BEGIN",
            "while read -r goal; do",
            '  [ -n "$goal" ] || continue',
            f"  timeout -s KILL {args.export_timeout}"
            ' "$LAKE" env "$EX/.lake/build/bin/lean4export" Mathlib "$MOD"'
            ' -- "$goal" > "$WORK/streams/$goal.ndjson" 2> "$WORK/streams/$goal.err"',
            "  rc=$?",
            '  lines=$(wc -l < "$WORK/streams/$goal.ndjson")',
            '  echo "AXEYUM_EXPORT|$goal|$rc|$lines"',
            'done < "$WORK/goals.txt"',
            "echo AXEYUM_EXPORT_END",
            'rm -f "$ML/$MOD.lean" "$OLEAN"',
            'cd "$WORK" && tar czf streams.tar.gz streams',
            'echo AXEYUM_TARBALL="$WORK/streams.tar.gz"',
            'du -sh "$WORK/streams.tar.gz"',
        ]
    )


# --------------------------------------------------------------------------
# Phases
# --------------------------------------------------------------------------


def load_rows(path: pathlib.Path, statuses: set[str]) -> list[dict]:
    rows = []
    for index, line in enumerate(path.read_text(encoding="utf-8").splitlines()):
        if not line.strip():
            continue
        row = json.loads(line)
        if row["epistemic_status"] not in statuses:
            continue
        rows.append(row)
    if not rows:
        raise SystemExit(f"{path} yielded no rows for statuses {sorted(statuses)}")
    for index, row in enumerate(rows):
        row["goal"] = goal_name(index)
    return rows


def phase_elaborate(args, rows: list[dict], work: pathlib.Path) -> dict:
    module, line_map = render_module(rows, with_negative_control=True)
    (work / "module.lean").write_text(module, encoding="utf-8")
    script = elaborate_script(module, args=args, module_name=args.module_name)
    started = time.time()
    completed = run_remote(args.host, script, timeout=args.timeout)
    elapsed = time.time() - started
    output = completed.stdout + completed.stderr
    (work / "elaborate.log").write_text(output, encoding="utf-8")
    if "AXEYUM_SETUP_FAIL" in output:
        print(output[-2000:], file=sys.stderr)
        raise SystemExit(2)
    diagnostics = parse_diagnostics(output)

    control_lines = [line for line, row in line_map.items() if row.get("negative_control")]
    if len(control_lines) != 1:
        raise SystemExit("the module must carry exactly one negative control")
    if control_lines[0] not in diagnostics:
        raise SystemExit(
            "the negative control ELABORATED. Lean accepted a statement naming a "
            "constant that does not exist, so this run proves nothing about the "
            "rows that 'passed'."
        )

    result = {
        "elapsed_s": round(elapsed, 2),
        "module_lines": module.count("\n"),
        "rows": {},
        "negative_control": "rejected",
    }
    for line, row in line_map.items():
        if row.get("negative_control"):
            continue
        messages = diagnostics.get(line, [])
        result["rows"][row["fact_id"]] = {
            "goal": row["goal"],
            "elaborated": not messages,
            "class": None if not messages else elaboration_class(messages),
            "messages": messages[:4],
        }
    (work / "elaborate.json").write_text(json.dumps(result, indent=2), encoding="utf-8")
    failures = [k for k, v in result["rows"].items() if not v["elaborated"]]
    print(
        f"ELABORATE|rows={len(result['rows'])}|elaborated={len(result['rows']) - len(failures)}"
        f"|failed={len(failures)}|negative_control=rejected|elapsed={elapsed:.1f}s"
    )
    return result


def phase_export(args, rows: list[dict], work: pathlib.Path) -> dict:
    elaborated = json.loads((work / "elaborate.json").read_text(encoding="utf-8"))
    clean = [row for row in rows if elaborated["rows"][row["fact_id"]]["elaborated"]]
    if not clean:
        raise SystemExit("no row elaborated; nothing to export")
    module, _ = render_module(clean, with_negative_control=False)
    (work / "module-clean.lean").write_text(module, encoding="utf-8")
    script = export_script(
        module, [row["goal"] for row in clean], args=args, module_name=args.module_name
    )
    started = time.time()
    completed = run_remote(args.host, script, timeout=args.timeout)
    elapsed = time.time() - started
    output = completed.stdout + completed.stderr
    (work / "export.log").write_text(output, encoding="utf-8")
    if "AXEYUM_SETUP_FAIL" in output:
        print(output[-2000:], file=sys.stderr)
        raise SystemExit(2)

    per_goal = {}
    for line in output.splitlines():
        if not line.startswith("AXEYUM_EXPORT|"):
            continue
        _, goal, rc, lines = line.split("|")
        per_goal[goal] = {"rc": int(rc), "stream_lines": int(lines)}
    if not per_goal:
        print(output[-2000:], file=sys.stderr)
        raise SystemExit("the export phase reported no per-goal result")

    tarball = None
    for line in output.splitlines():
        if line.startswith("AXEYUM_TARBALL="):
            tarball = line.split("=", 1)[1].strip()
    if tarball is None:
        raise SystemExit("the export phase produced no tarball")
    local_tar = work / "streams.tar.gz"
    fetch = subprocess.run(
        ["scp", "-o", "BatchMode=yes", f"{args.host}:{tarball}", str(local_tar)],
        capture_output=True,
        text=True,
    )
    if fetch.returncode != 0:
        raise SystemExit(f"scp failed: {fetch.stderr}")
    streams = work / "streams"
    if streams.exists():
        subprocess.run(["rm", "-rf", str(streams)], check=True)
    subprocess.run(["tar", "xzf", str(local_tar), "-C", str(work)], check=True)

    result = {"elapsed_s": round(elapsed, 2), "goals": per_goal}
    (work / "export.json").write_text(json.dumps(result, indent=2), encoding="utf-8")
    failed = sum(1 for value in per_goal.values() if value["rc"] != 0 or value["stream_lines"] < 2)
    print(
        f"EXPORT|goals={len(per_goal)}|exported={len(per_goal) - failed}|failed={failed}"
        f"|elapsed={elapsed:.1f}s"
    )
    return result


def phase_import(args, rows: list[dict], work: pathlib.Path) -> dict:
    export = json.loads((work / "export.json").read_text(encoding="utf-8"))
    streams = work / "streams"
    manifest_lines = []
    for row in rows:
        goal = row["goal"]
        info = export["goals"].get(goal)
        if info is None:
            continue
        stream = streams / f"{goal}.ndjson"
        manifest_lines.append(f"{row['fact_id']}\t{goal}\t{stream}")
    if not manifest_lines:
        raise SystemExit("no stream to import")
    manifest = work / "import-manifest.tsv"
    manifest.write_text("\n".join(manifest_lines) + "\n", encoding="utf-8")

    build = subprocess.run(
        [
            str(ROOT / "scripts/cargo-serialized.sh"),
            "build",
            "--release",
            "-p",
            "axeyum-lean-import",
            "--example",
            "statement_import_census",
        ],
        cwd=str(ROOT),
        capture_output=True,
        text=True,
    )
    if build.returncode != 0:
        print(build.stdout[-3000:] + build.stderr[-3000:], file=sys.stderr)
        raise SystemExit("could not build statement_import_census")
    binary = ROOT / "target/release/examples/statement_import_census"
    if not binary.exists():
        raise SystemExit(f"{binary} was not produced")
    started = time.time()
    completed = subprocess.run(
        [str(binary), str(manifest)], capture_output=True, text=True, cwd=str(ROOT)
    )
    elapsed = time.time() - started
    (work / "import.log").write_text(completed.stderr, encoding="utf-8")
    if completed.returncode != 0:
        print(completed.stderr[-3000:], file=sys.stderr)
        raise SystemExit("the import census could not run")
    result = {"elapsed_s": round(elapsed, 2), "rows": {}}
    for line in completed.stdout.splitlines():
        if not line.strip():
            continue
        record = json.loads(line)
        result["rows"][record["row"]] = record
    (work / "import.json").write_text(json.dumps(result, indent=2), encoding="utf-8")
    admitted = sum(1 for v in result["rows"].values() if v["outcome"] == "admitted")
    print(
        f"IMPORT|rows={len(result['rows'])}|admitted={admitted}"
        f"|declined={len(result['rows']) - admitted}|elapsed={elapsed:.1f}s"
    )
    return result


def phase_classify(args, rows: list[dict], work: pathlib.Path) -> dict:
    elaborate = json.loads((work / "elaborate.json").read_text(encoding="utf-8"))
    export = json.loads((work / "export.json").read_text(encoding="utf-8"))
    imported = json.loads((work / "import.json").read_text(encoding="utf-8"))

    classified = []
    for row in rows:
        fact_id = row["fact_id"]
        goal = row["goal"]
        elab = elaborate["rows"][fact_id]
        if not elab["elaborated"]:
            record = {
                "stage": "elaboration",
                "class": elab["class"],
                "detail": (elab["messages"] or [""])[0],
            }
        else:
            info = export["goals"].get(goal, {})
            if info.get("rc", 1) != 0 or info.get("stream_lines", 0) < 2:
                record = {
                    "stage": "export",
                    "class": (
                        "export-timeout-or-resource"
                        if info.get("rc", 1) != 0
                        else "export-empty-stream"
                    ),
                    "detail": f"rc={info.get('rc')} lines={info.get('stream_lines')}",
                }
            else:
                run = imported["rows"].get(fact_id)
                if run is None:
                    record = {"stage": "import", "class": "did-not-run", "detail": ""}
                elif run["outcome"] == "admitted":
                    record = {
                        "stage": "admitted",
                        "class": "admitted",
                        "detail": "",
                        "admitted_declarations": run.get("admitted_declarations"),
                        "declaration_records": run.get("declaration_records"),
                        # Which admission feature carried this row, straight
                        # from the importer's own report -- so "the count went
                        # up" never has to stand in for "the feature fired".
                        # Absent on a run whose importer predates ADR-1667.
                        "substituted_theorems": run.get("substituted_theorems", []),
                        "native_quotient_package": run.get(
                            "native_quotient_package", []
                        ),
                    }
                else:
                    record = {
                        "stage": "import",
                        "class": run["class"],
                        "detail": run.get("display", ""),
                    }
        classified.append(
            {
                "fact_id": fact_id,
                "held_out": row["held_out"],
                "fragment": row["fragment"],
                "row_kind": row["row_kind"],
                "epistemic_status": row["epistemic_status"],
                **record,
            }
        )
    (work / "classified.json").write_text(json.dumps(classified, indent=2), encoding="utf-8")
    counts = collections.Counter(entry["class"] for entry in classified)
    for name, count in counts.most_common():
        print(f"CLASS|{name}|{count}")
    return {"classified": classified}


def _counts(entries: list[dict], key) -> dict[str, int]:
    return dict(sorted(collections.Counter(key(e) for e in entries).items()))


def _delta(baseline_path: pathlib.Path, document: dict) -> dict:
    """Per-class and per-blocking-name movement against an earlier census.

    Derived from the two ARTIFACTS, never from a literal, so a number that did
    not move shows as 0 rather than as silence, and a class or declaration that
    appears in only one of the two runs still gets a row (with the missing side
    read as 0). The population is compared explicitly: a delta across two
    different populations is not a delta, so this records both row counts and
    the caller must reject the comparison if they differ.
    """
    baseline = json.loads(baseline_path.read_text(encoding="utf-8"))

    def class_counts(doc: dict) -> dict[str, int]:
        return {name: bucket["count"] for name, bucket in doc["classes"].items()}

    def blocker_counts(doc: dict) -> dict[str, int]:
        return dict(doc["first_trusted_declaration_in_closure"]["by_declaration"])

    classes_before = class_counts(baseline)
    classes_after = class_counts(document)
    names_before = blocker_counts(baseline)
    names_after = blocker_counts(document)

    def rows(before: dict[str, int], after: dict[str, int]) -> dict[str, dict[str, int]]:
        return {
            key: {
                "before": before.get(key, 0),
                "after": after.get(key, 0),
                "delta": after.get(key, 0) - before.get(key, 0),
            }
            for key in sorted(set(before) | set(after))
        }

    return {
        "baseline": str(baseline_path.relative_to(ROOT))
        if baseline_path.is_relative_to(ROOT)
        else str(baseline_path),
        "baseline_date": baseline.get("date"),
        "baseline_axeyum_commit": baseline.get("provenance", {}).get("axeyum_commit"),
        "population_rows": {
            "before": baseline["population"]["rows"],
            "after": document["population"]["rows"],
            "comparable": baseline["population"]["rows"] == document["population"]["rows"],
        },
        "admitted": {
            "before": baseline["outcome"]["admitted"],
            "after": document["outcome"]["admitted"],
            "delta": document["outcome"]["admitted"] - baseline["outcome"]["admitted"],
        },
        "by_class": rows(classes_before, classes_after),
        "by_first_blocking_declaration": rows(names_before, names_after),
    }


def phase_publish(args, rows: list[dict], work: pathlib.Path) -> dict:
    """Write the census artifact and its markdown summary.

    HELD-OUT DISCIPLINE. `scripts/check-autogenesis-holdout-isolation.py` forbids
    a new artifact from naming a held-out fact id, and held-out membership here
    comes from the nursery manifests via `check-dispatchable-frontier.py`, never
    from a hand list. So a held-out row contributes to every COUNT and appears in
    no id list, and the number omitted is itself recorded -- an omission nobody
    can see is indistinguishable from a row that was never measured.
    """
    classified = json.loads((work / "classified.json").read_text(encoding="utf-8"))
    elaborate = json.loads((work / "elaborate.json").read_text(encoding="utf-8"))
    export = json.loads((work / "export.json").read_text(encoding="utf-8"))
    imported = json.loads((work / "import.json").read_text(encoding="utf-8"))
    log = (work / "elaborate.log").read_text(encoding="utf-8")

    def header(prefix: str) -> str:
        for line in log.splitlines():
            if line.startswith(prefix):
                return line.split("=", 1)[1].strip()
        return "?"

    by_class: dict[str, dict] = {}
    for entry in classified:
        bucket = by_class.setdefault(
            entry["class"],
            {
                "stage": entry["stage"],
                "count": 0,
                "by_fragment": collections.Counter(),
                "by_status": collections.Counter(),
                "held_out": 0,
                "fact_ids": [],
                "example_detail": entry["detail"][:200] if entry["detail"] else "",
            },
        )
        bucket["count"] += 1
        bucket["by_fragment"][entry["fragment"]] += 1
        bucket["by_status"][entry["epistemic_status"]] += 1
        if entry["held_out"]:
            bucket["held_out"] += 1
        else:
            bucket["fact_ids"].append(entry["fact_id"])
    for bucket in by_class.values():
        bucket["by_fragment"] = dict(sorted(bucket["by_fragment"].items()))
        bucket["by_status"] = dict(sorted(bucket["by_status"].items()))
        bucket["fact_ids"] = sorted(bucket["fact_ids"])
        bucket["held_out_ids_omitted"] = bucket["held_out"]

    # The screen is run over THIS census's own population, not over the ledger,
    # so the two sides of the agreement table share a denominator. Comparing a
    # whole-ledger screen against a subset run reports a disagreement that is
    # only a difference of population.
    sys.path.insert(0, str(ROOT / "scripts"))
    from lean_surface_screen import screen_statement

    screen_flagged = sorted(
        row["fact_id"] for row in rows if screen_statement(row["statement"])
    )

    # The largest class is only actionable if it says WHICH declaration stopped
    # each row. `import_statement_ndjson` reports the first trusted declaration
    # it meets, so this is a distribution over first blockers, not over all of
    # them -- stated here rather than implied, because the two are different
    # numbers and only one was measured.
    blocking = collections.Counter()
    blocking_kind = collections.Counter()
    for record in imported["rows"].values():
        match = re.search(
            r'trusted declaration "([^"]+)" \((\w+)\)', record.get("display", "")
        )
        if match:
            blocking[match.group(1)] += 1
            blocking_kind[match.group(2)] += 1
    elaboration_blockers = {
        entry["fact_id"] for entry in classified if entry["stage"] == "elaboration"
    }

    document = {
        "schema_version": 1,
        "kind": "axeyum-statement-import-blocker-census",
        "date": args.date,
        "question": (
            "For every pinned Mathlib v4.30 mirror in the ledger, does its "
            "`formal.statement` cross into this kernel as a goal through the "
            "statement-only import route, and if not, what typed reason stopped it?"
        ),
        "method": (
            "Each statement becomes the value of a transparent `def _ : Prop` after "
            "`import Mathlib`; official Lean 4.30.0 elaborates it; official "
            "lean4export emits that definition's own declaration closure; "
            "axeyum_lean_import::import_statement_ndjson admits or declines the "
            "stream. No proof value is read and nothing is proved. Reproduce with "
            "scripts/run-statement-import-blocker-census.py."
        ),
        "provenance": {
            "axeyum_commit": args.commit,
            "mathlib_commit": header("AXEYUM_COMMIT"),
            "lean": header("AXEYUM_LEAN_VERSION"),
            "lean4export_commit": args.lean4export_commit,
            "elaboration_host": args.host,
            "import_host": "this checkout",
            "negative_control": elaborate["negative_control"],
            "elapsed_seconds": {
                "elaborate": elaborate["elapsed_s"],
                "export": export["elapsed_s"],
                "import": imported["elapsed_s"],
            },
        },
        "population": {
            "rows": len(classified),
            "open": sum(1 for e in classified if e["epistemic_status"] == "open"),
            "proved": sum(1 for e in classified if e["epistemic_status"] == "proved"),
            "held_out": sum(1 for e in classified if e["held_out"]),
            "by_fragment": _counts(classified, lambda e: e["fragment"]),
            "by_row_kind": _counts(classified, lambda e: e["row_kind"]),
            "holdout_authority": "scripts/check-dispatchable-frontier.py --json",
        },
        "outcome": {
            "admitted": sum(1 for e in classified if e["class"] == "admitted"),
            "blocked": sum(1 for e in classified if e["class"] != "admitted"),
            "by_stage": _counts(classified, lambda e: e["stage"]),
        },
        "classes": {
            name: bucket for name, bucket in sorted(by_class.items(), key=lambda kv: -kv[1]["count"])
        },
        "open_mirrors_only": {
            "rows": sum(1 for e in classified if e["epistemic_status"] == "open"),
            "by_class": _counts(
                [e for e in classified if e["epistemic_status"] == "open"],
                lambda e: e["class"],
            ),
        },
        "proved_mirrors_control": {
            "why": (
                "The 499 proved mirrors are the positive control population: they "
                "were already established here, so a blocker on one is a property "
                "of the ROUTE and never of the proposition's difficulty."
            ),
            "rows": sum(1 for e in classified if e["epistemic_status"] == "proved"),
            "by_class": _counts(
                [e for e in classified if e["epistemic_status"] == "proved"],
                lambda e: e["class"],
            ),
        },
        "first_trusted_declaration_in_closure": {
            "why": (
                "The statement's own definition closure reaches a proof-bearing "
                "declaration, so the proof-isolation gate refuses the stream. This "
                "is the FIRST such declaration per stream, not all of them."
            ),
            "by_kind": dict(sorted(blocking_kind.items())),
            "by_declaration": dict(sorted(blocking.items(), key=lambda kv: (-kv[1], kv[0]))),
            "distinct_declarations": len(blocking),
        },
        "admission_features": {
            "why": (
                "For each admitted row the importer reports which reconstructed "
                "theorems it substituted and whether it admitted the kernel's own "
                "quotient package (ADR-1667). Counted here so an admission is "
                "attributable to a feature rather than inferred from a total "
                "going up. COUNTS ONLY -- no ids, because the population is "
                "partly held out."
            ),
            "rows_naming_a_substitution": sum(
                1 for e in classified if e.get("substituted_theorems")
            ),
            "rows_naming_the_quotient_package": sum(
                1 for e in classified if e.get("native_quotient_package")
            ),
            "by_substituted_theorem": dict(
                sorted(
                    collections.Counter(
                        name
                        for e in classified
                        for name in e.get("substituted_theorems", [])
                    ).items(),
                    key=lambda kv: (-kv[1], kv[0]),
                )
            ),
        },
        "screen_agreement": {
            "screen": "scripts/lean_surface_screen.py",
            "flagged_by_screen": len(screen_flagged),
            "rejected_by_lean_at_elaboration": len(elaboration_blockers),
            "flagged_and_rejected": len(set(screen_flagged) & elaboration_blockers),
            "flagged_but_elaborated": len(set(screen_flagged) - elaboration_blockers),
            "rejected_but_unflagged": len(elaboration_blockers - set(screen_flagged)),
            "population": len(rows),
            "note": (
                "Both sets are derived over the SAME population -- the screen from "
                "each row's statement text, Lean from this run. Neither is a literal."
            ),
        },
    }
    if args.baseline:
        document["delta_against_baseline"] = _delta(args.baseline, document)

    out_json = (
        ROOT
        / "artifacts/measurements"
        / f"statement-import-blocker-census-{args.date}{args.out_suffix}.json"
    )
    out_json.write_text(
        json.dumps(document, indent=2, ensure_ascii=False, sort_keys=False) + "\n",
        encoding="utf-8",
    )

    lines = [
        f"# Statement-import blocker census, {args.date}",
        "",
        "GENERATED by `scripts/run-statement-import-blocker-census.py --phase publish`.",
        f"Do not edit; the numbers live in `{out_json.name}`.",
        "",
        f"Population: {document['population']['rows']} `F:ml430-*` mirrors "
        f"({document['population']['open']} open, {document['population']['proved']} proved); "
        f"{document['population']['held_out']} held out, so their ids appear in no list below.",
        "",
        f"Route: `def _ : Prop` after `import Mathlib` -> `lean4export` -> "
        f"`import_statement_ndjson`. Mathlib `{document['provenance']['mathlib_commit'][:12]}`, "
        f"{document['provenance']['lean']}.",
        "",
        f"**{document['outcome']['admitted']} of {document['population']['rows']} statements cross "
        f"into the kernel as a goal.** The rest, by class:",
        "",
        "| class | stage | rows | open | proved | Nat | Int | held out |",
        "|---|---|---:|---:|---:|---:|---:|---:|",
    ]
    for name, bucket in document["classes"].items():
        lines.append(
            f"| `{name}` | {bucket['stage']} | {bucket['count']} | "
            f"{bucket['by_status'].get('open', 0)} | {bucket['by_status'].get('proved', 0)} | "
            f"{bucket['by_fragment'].get('Nat', 0)} | {bucket['by_fragment'].get('Int', 0)} | "
            f"{bucket['held_out']} |"
        )
    if "delta_against_baseline" in document:
        delta = document["delta_against_baseline"]
        lines += [
            "",
            "## Delta against "
            f"`{delta['baseline']}` ({delta['baseline_date']}, axeyum "
            f"`{(delta['baseline_axeyum_commit'] or '')[:9]}`)",
            "",
            f"Population {delta['population_rows']['before']} -> "
            f"{delta['population_rows']['after']}, comparable: "
            f"**{delta['population_rows']['comparable']}**. Admitted "
            f"{delta['admitted']['before']} -> {delta['admitted']['after']} "
            f"(**{delta['admitted']['delta']:+d}**).",
            "",
            "| class | before | after | delta |",
            "|---|---:|---:|---:|",
        ]
        for name, row in delta["by_class"].items():
            lines.append(
                f"| `{name}` | {row['before']} | {row['after']} | {row['delta']:+d} |"
            )
        lines += [
            "",
            "The blocker distribution is over FIRST-reported blockers, so a name "
            "falling to zero means the rows that reported it now report whatever "
            "was behind it -- never that they were admitted. Read this table "
            "beside the admitted delta above.",
            "",
            "| first blocking declaration | before | after | delta |",
            "|---|---:|---:|---:|",
        ]
        for name, row in delta["by_first_blocking_declaration"].items():
            lines.append(
                f"| `{name}` | {row['before']} | {row['after']} | {row['delta']:+d} |"
            )

    features = document["admission_features"]
    lines += [
        "",
        "## Which admission feature carried an admitted row",
        "",
        f"{features['rows_naming_a_substitution']} admitted rows named at least "
        "one reconstructed substitution; "
        f"{features['rows_naming_the_quotient_package']} named the kernel's own "
        "quotient package. Counts only -- the population is partly held out.",
        "",
    ]

    agreement = document["screen_agreement"]
    lines += [
        "",
        "## The screen",
        "",
        f"`{agreement['screen']}` flags {agreement['flagged_by_screen']} of the "
        f"{document['population']['rows']} statements; Lean rejects "
        f"{agreement['rejected_by_lean_at_elaboration']} at elaboration. "
        f"Agreement {agreement['flagged_and_rejected']}, "
        f"{agreement['flagged_but_elaborated']} flagged-but-elaborated, "
        f"{agreement['rejected_but_unflagged']} rejected-but-unflagged.",
        "",
    ]
    out_md = out_json.with_suffix(".md")
    out_md.write_text("\n".join(lines), encoding="utf-8")
    print(f"PUBLISH|json={out_json.relative_to(ROOT)}|md={out_md.relative_to(ROOT)}")
    return document


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows", type=pathlib.Path, required=True)
    parser.add_argument("--work", type=pathlib.Path, required=True)
    parser.add_argument(
        "--phase",
        default="all",
        choices=["all", "elaborate", "export", "import", "classify", "publish"],
    )
    parser.add_argument("--date", default="2026-09-05")
    parser.add_argument(
        "--out-suffix",
        default="",
        help=(
            "appended to the published artifact's basename, so a re-run can sit "
            "BESIDE the run it is compared against instead of overwriting it "
            "(e.g. --out-suffix -after-c4). Does not change the `date` field."
        ),
    )
    parser.add_argument(
        "--baseline",
        type=pathlib.Path,
        default=None,
        help=(
            "an earlier census artifact to diff against; adds a "
            "`delta_against_baseline` block with per-class and per-blocking-name "
            "before/after/delta rows, derived from both artifacts."
        ),
    )
    parser.add_argument("--commit", default="", help="the axeyum commit this census was measured at")
    parser.add_argument(
        "--lean4export-commit", default="a3e35a584f59b390667db7269cd37fca8575e4bf"
    )
    parser.add_argument("--status", default="open,proved")
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--host", default=DEFAULT_HOST)
    parser.add_argument("--mathlib", default=DEFAULT_MATHLIB)
    parser.add_argument("--lean4export", default=DEFAULT_LEAN4EXPORT)
    parser.add_argument("--lean", default=DEFAULT_LEAN)
    parser.add_argument("--lake", default=DEFAULT_LAKE)
    parser.add_argument("--module-name", default="AxeyumStatementCensusRun")
    parser.add_argument("--remote-work", default="~/axeyum-statement-census-run")
    parser.add_argument("--timeout", type=int, default=14400)
    parser.add_argument("--export-timeout", type=int, default=300)
    args = parser.parse_args()

    args.work.mkdir(parents=True, exist_ok=True)
    rows = load_rows(args.rows, set(args.status.split(",")))
    if args.limit:
        rows = rows[: args.limit]
    (args.work / "rows.json").write_text(json.dumps(rows, indent=2), encoding="utf-8")
    print(f"SELECTED|rows={len(rows)}|statuses={args.status}")

    order = ["elaborate", "export", "import", "classify", "publish"]
    phases = order if args.phase == "all" else [args.phase]
    for phase in phases:
        {
            "elaborate": phase_elaborate,
            "export": phase_export,
            "import": phase_import,
            "classify": phase_classify,
            "publish": phase_publish,
        }[phase](args, rows, args.work)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
