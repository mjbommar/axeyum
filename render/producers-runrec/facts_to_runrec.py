#!/usr/bin/env python3
"""Run fact-ledger evidence checkers for real, and record what happened.

WHY THIS EXISTS. `13-facts-diary.md` item 2 states the structural gap between
the fact ledger and the render strand exactly right: a Doc-IR `claim` needs at
least one `EvidenceRef`, an `EvidenceRef` points at a RUN RECORD, and a run
record carries `provenance.exit_status` -- the one field the whole fail-closed
law flows through. A fact-ledger evidence row carries `check_status: checked`
(an assertion that somebody checked it, once, somewhere) and a command a reader
*could* run. It carries no exit status. Synthesising one would forge exactly the
field that makes the rest of the pipeline honest, so `facts_to_docir.py`
correctly emits no claims at all.

The only sound way to close that gap is to RUN the commands. This script does
that: it reads the ledger rows, executes each `checker_command` verbatim, and
writes one `RunRecord` per executed command with the MEASURED exit status.

THREE RULES IT KEEPS, and why each one is a rule.

1. VERBATIM. The command string from the ledger is handed to `bash -c`
   unmodified, with the repository root as cwd. Nothing is reinterpreted,
   normalised, or "fixed". A command that no longer runs is a ledger finding,
   and rewriting it here would hide the finding and record a green run for a
   command nobody can reproduce.

2. ONE RECORD PER EXECUTION, NEVER ONE PER CITATION. Seventeen of the arith
   pilot's facts cite the SAME axiom-freedom command. That is one check
   supporting seventeen facts, not seventeen checks. Emitting seventeen records
   from one execution would manufacture independence that does not exist -- the
   same discipline `fact.schema.json` applies to its `checkers` list. So rows
   are grouped by exact command text, the group runs once, and the record's
   `claims` list carries one entry per citing row. `runrec-index.json` maps
   (fact id, evidence row id) -> (record path, record id, claim key) so a
   consumer can still resolve per row.

3. THE EXIT STATUS IS MEASURED, AND SO IS THIS SCRIPT'S. A red run is recorded
   faithfully and reported loudly; it is a finding, not an embarrassment. This
   script's own exit status depends on the finding and not on completion:

     0  every planned command ran, every record validated, no red run
     1  at least one red run, or a record that failed validation, or a row
        that could not be run at all (unless the corresponding --allow-* flag
        is given)
     2  usage, or nothing to do (an empty run is not a passing run)

   `--allow-red` and `--allow-skips` downgrade the first two to warnings for
   the workflow where recording the reds *is* the deliverable. Records are
   written either way: writing them is the job.

WHAT `inputs` PINS, AND WHAT IT DOES NOT. `Provenance.inputs` lists the files
the command NAMES -- the example source or script that implements the checker,
and the artifact the row points at -- each with a SHA-256 that assembly
re-hashes on every render (fail-closed law rule 4). It does NOT pin the
transitive closure: the rest of the crate behind a `cargo run --example`, or
the other 100 claims a ledger-sweeping checker reads. Those are named in
`notes` instead of silently omitted. A content-addressed checker-closure digest
is the right answer and is recorded as a P1 item in `18-runrec-diary.md`; what
is NOT acceptable is an input list that looks complete and is not.

USAGE

    python3 render/producers-runrec/facts_to_runrec.py --survey
    python3 render/producers-runrec/facts_to_runrec.py

    # a different fact set
    python3 render/producers-runrec/facts_to_runrec.py \
        --facts-from render/examples-input/facts/facts-pilot.doc.json

    # the checker-sensitivity control (separate, see --negative-control)
    python3 render/producers-runrec/facts_to_runrec.py --negative-control
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import re
import subprocess
import sys
import time

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
DEFAULT_OUT = os.path.join(REPO_ROOT, "render", "examples-input", "runrec")
DEFAULT_FACTS_DOC = os.path.join(
    REPO_ROOT, "render", "examples-input", "facts", "facts-pilot-arith.doc.json"
)
# The two headline Rado facts. Their evidence was weighed before running (see
# `--survey`): every command is under a minute on this host, so they are in.
EXTRA_FACTS = ["F:rado-r4-a5-b3", "F:rado-r4-a5-b4"]

FACTS_DIR = os.path.join(REPO_ROOT, "artifacts", "facts")
SCHEMA = os.path.join(REPO_ROOT, "artifacts", "ontology", "docir.schema.json")
VALIDATOR = os.path.join(REPO_ROOT, "scripts", "validate-docir.py")

# Statuses this producer is willing to declare for a green run, by ledger
# evidence kind. NOTHING here is stronger than what the command actually
# establishes, and the interesting case is `kernel-term`: see `claim_status`.
KIND_STATUS = {
    "kernel-term": "checked",
    "exhaustive-enumeration": "checked",
    "instance-pin": "checked",
    "claim-ref": "evidence",
    "witness-replay": "evidence",
    "unsat-certificate": "evidence",
    "cube-cover": "evidence",
    "cube-tree-cover": "evidence",
    "published-value-replication": "evidence",
    "bound-citation": "evidence",
}

CARGO_EXAMPLE = re.compile(r"-p\s+(?P<crate>[A-Za-z0-9_-]+)\s+--example\s+(?P<ex>[A-Za-z0-9_-]+)")
PATHLIKE = re.compile(r"[A-Za-z0-9_][A-Za-z0-9_./+-]*/[A-Za-z0-9_./+-]+")


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def slug(text: str) -> str:
    """Lowercase `[a-z0-9-]`, the id grammar both `F:` and `R:` use."""
    out = re.sub(r"[^a-z0-9]+", "-", text.lower()).strip("-")
    out = re.sub(r"-+", "-", out)
    return out


def git_epoch() -> dict:
    """Epoch as DATA, from the current commit. Never the wall clock."""
    env = os.environ.get("SOURCE_DATE_EPOCH")
    out = subprocess.run(
        ["git", "-C", REPO_ROOT, "log", "-1", "--format=%ct %H"],
        capture_output=True,
        text=True,
        check=False,
    )
    if out.returncode == 0 and out.stdout.strip():
        ct, sha = out.stdout.split()
        return {"unix": int(ct), "source": "commit", "commit": sha}
    if env:
        return {"unix": int(env), "source": "source-date-epoch"}
    sys.exit("error: no epoch available (no git commit, no SOURCE_DATE_EPOCH); refusing to guess")


def fact_path(fact_id: str) -> str:
    return os.path.join(FACTS_DIR, fact_id.replace(":", "-", 1) + ".json")


def load_fact(fact_id: str) -> dict:
    with open(fact_path(fact_id), "r", encoding="utf-8") as fh:
        return json.load(fh)


def fact_ids_from_doc(path: str) -> list[str]:
    with open(path, "r", encoding="utf-8") as fh:
        blob = fh.read()
    return sorted(set(re.findall(r"F:[a-z0-9]+(?:-[a-z0-9]+)*", blob)))


def declared_inputs(command: str, artifact: str | None) -> list[dict]:
    """Files the command NAMES, each with a digest. Mechanical, never guessed."""
    found: dict[str, str] = {}

    m = CARGO_EXAMPLE.search(command)
    if m:
        rel = os.path.join("crates", m.group("crate"), "examples", m.group("ex") + ".rs")
        if os.path.isfile(os.path.join(REPO_ROOT, rel)):
            found[rel] = "checker"

    for tok in PATHLIKE.findall(command):
        rel = tok.strip("\"'`),;")
        if rel.startswith("/"):
            continue  # absolute scratch paths are outputs, not pinned inputs
        full = os.path.join(REPO_ROOT, rel)
        if os.path.isfile(full):
            role = "checker" if rel.startswith("scripts/") else "artifact"
            found.setdefault(rel, role)

    if artifact and not artifact.startswith("sha256:"):
        full = os.path.join(REPO_ROOT, artifact)
        if os.path.isfile(full):
            found[artifact] = "artifact"

    return [
        {"path": rel, "sha256": sha256_file(os.path.join(REPO_ROOT, rel)), "role": role}
        for rel, role in sorted(found.items())
    ]


def unpinned_note(command: str) -> str:
    """Name what `inputs` does NOT cover, rather than let it look complete."""
    parts = []
    m = CARGO_EXAMPLE.search(command)
    if m:
        parts.append(
            "`inputs` pins the example source, not the rest of `%s` that it links; "
            "a change inside the crate would not trip the render's input-hash guard."
            % m.group("crate")
        )
    if "validate-claims.py" in command or "check-claim-certificates.py" in command:
        parts.append(
            "This checker SWEEPS the whole claim ledger (104 `claim.json` files under "
            "`artifacts/claims/`), so its verdict depends on far more bytes than the row's "
            "own artifact; pinning all of them would make every unrelated ledger edit break "
            "every render, so only the row's artifact and the script are pinned."
        )
    return " ".join(parts)


def exact_type_pinned(command: str) -> bool:
    """True when the kernel-term row pins the theorem's TYPE, not just its name.

    `grep -qE '^Nat.add_comm[[:space:]]'` passes for ANY theorem of that name --
    restate the proposition and the check still goes green. `grep -qxF '<name>
    <arity> <canonical type>'` pins the admitted type. The difference is the
    whole strength of the row, so the record says which one ran.
    """
    return "-qxF" in command or "-qF" in command


def claim_status(kind: str, command: str) -> tuple[str, str | None]:
    base = KIND_STATUS.get(kind, "evidence")
    if kind == "kernel-term":
        if exact_type_pinned(command):
            return (
                "proved",
                "The checker pins the theorem's canonical type as the kernel prints it, "
                "so a restatement of the proposition would fail this row.",
            )
        return (
            "checked",
            "NAME-ONLY CHECK. The checker matches the theorem's NAME in the kernel "
            "inventory and does not look at its type, so a theorem restated under the "
            "same name would still pass. Deliberately capped at `checked`: this run "
            "establishes that the kernel admits a theorem called this, not that it "
            "admits this proposition.",
        )
    return (base, None)


def canonical_json(obj) -> str:
    return json.dumps(obj, sort_keys=True, indent=2, ensure_ascii=True) + "\n"


def collect_rows(fact_ids: list[str]) -> list[dict]:
    rows = []
    for fid in fact_ids:
        fact = load_fact(fid)
        for ev in fact.get("evidence", []):
            rows.append(
                {
                    "fact_id": fid,
                    "fact_title": fact.get("title", ""),
                    "epistemic": fact.get("epistemic_status"),
                    "row_id": ev.get("id", ""),
                    "kind": ev.get("kind", ""),
                    "check_status": ev.get("check_status"),
                    "checkers": ev.get("checkers") or [],
                    "supports": ev.get("supports"),
                    "artifact": ev.get("artifact"),
                    "command": ev.get("checker_command"),
                }
            )
    return rows


def classify(row: dict) -> tuple[str, str]:
    cmd = row["command"]
    if not cmd:
        return ("not-runnable", "no `checker_command` in the ledger row")
    art = row["artifact"]
    if art:
        if art.startswith("sha256:"):
            return ("runnable", "artifact is a bare content digest, not a file")
        full = os.path.join(REPO_ROOT, art)
        if not os.path.exists(full):
            return ("not-runnable", "declared artifact `%s` is not in the tree" % art)
    m = CARGO_EXAMPLE.search(cmd)
    if m:
        rel = os.path.join("crates", m.group("crate"), "examples", m.group("ex") + ".rs")
        if not os.path.isfile(os.path.join(REPO_ROOT, rel)):
            return ("not-runnable", "checker example `%s` is missing from the tree" % rel)
    m2 = re.search(r"(scripts/[A-Za-z0-9_.-]+\.py)", cmd)
    if m2 and not os.path.isfile(os.path.join(REPO_ROOT, m2.group(1))):
        return ("not-runnable", "checker script `%s` is missing from the tree" % m2.group(1))
    return ("runnable", "")


def run_command(command: str, timeout: int) -> dict:
    t0 = time.monotonic()
    try:
        proc = subprocess.run(
            ["bash", "-c", command],
            cwd=REPO_ROOT,
            capture_output=True,
            timeout=timeout,
        )
        dt = time.monotonic() - t0
        return {
            "timed_out": False,
            "exit_status": proc.returncode,
            "duration_ms": int(dt * 1000),
            "stdout": proc.stdout,
            "stderr": proc.stderr,
        }
    except subprocess.TimeoutExpired:
        dt = time.monotonic() - t0
        return {
            "timed_out": True,
            "exit_status": None,
            "duration_ms": int(dt * 1000),
            "stdout": b"",
            "stderr": b"",
        }


def build_record(group: list[dict], result: dict, epoch: dict, role: str) -> dict:
    command = group[0]["command"]
    first = group[0]
    if len(group) == 1:
        rid = "R:" + slug(first["fact_id"].split(":", 1)[1] + "-" + first["row_id"])
    else:
        # A shared record must NOT be named after whichever citing row sorts
        # first: it covers all of them, and naming it for one is both misleading
        # and unstable under a change of fact set. Name it for the checker plus
        # a digest of the command, which is what the group actually is.
        m0 = CARGO_EXAMPLE.search(command)
        if m0:
            what = m0.group("ex")
        else:
            s0 = re.search(r"scripts/([A-Za-z0-9_.-]+)\.py", command)
            what = s0.group(1) if s0 else "command"
        rid = "R:shared-%s-%s" % (
            slug(what),
            hashlib.sha256(command.encode("utf-8")).hexdigest()[:8],
        )

    inputs = declared_inputs(command, first["artifact"])
    m = CARGO_EXAMPLE.search(command)
    if m:
        generator = "crates/%s/examples/%s.rs (via `cargo run --example`), invoked by render/producers-runrec/facts_to_runrec.py" % (
            m.group("crate"),
            m.group("ex"),
        )
    else:
        script = re.search(r"(scripts/[A-Za-z0-9_.-]+\.py)", command)
        generator = "%s, invoked by render/producers-runrec/facts_to_runrec.py" % (
            script.group(1) if script else "bash -c (ledger checker_command)"
        )

    exit_status = result["exit_status"]
    green = exit_status == 0
    outcome = "established" if green else "inconclusive"

    claims = []
    for row in group:
        status, note = claim_status(row["kind"], command)
        if not green:
            # A red run establishes nothing. The claim entry still exists so a
            # consumer can find it by row, but it says so.
            status = "open"
            note = (
                "The run exited %s, so this row establishes nothing. %s"
                % (exit_status, note or "")
            ).strip()
        key = slug(row["fact_id"].split(":", 1)[1] + "-" + row["row_id"])
        claim = {
            "key": key,
            "status": status,
            "statement": (
                "Fact-ledger evidence row `%s` of `%s` (kind `%s`) was replayed by running "
                "its recorded `checker_command`; the command exited %s."
                % (row["row_id"], row["fact_id"], row["kind"], exit_status)
            ),
            "supports": {"kind": "fact", "id": row["fact_id"]},
        }
        if note:
            claim["note"] = note
        claims.append(claim)

    stdout = result["stdout"]
    stderr = result["stderr"]
    stats = {
        "rows_covered": len(group),
        "stdout_bytes": len(stdout),
        "stdout_sha256": hashlib.sha256(stdout).hexdigest(),
        "stderr_bytes": len(stderr),
        "stderr_sha256": hashlib.sha256(stderr).hexdigest(),
        "wall_seconds": round(result["duration_ms"] / 1000.0, 3),
        "exact_type_pinned": exact_type_pinned(command),
    }

    cited = ", ".join("%s/%s" % (r["fact_id"], r["row_id"]) for r in group)
    notes = [
        "Produced by replaying fact-ledger evidence rows, not by re-deriving the "
        "mathematics. The command is the ledger's `checker_command` verbatim; this "
        "record asserts only that it was run, from the repository root, and exited "
        "with the status recorded here.",
        "Cited by: %s." % cited,
    ]
    up = unpinned_note(command)
    if up:
        notes.append("NOT PINNED: " + up)
    if len(group) > 1:
        notes.append(
            "ONE EXECUTION, %d CITATIONS. These rows share one command byte for byte, so "
            "they are one check supporting %d facts, not %d independent checks."
            % (len(group), len(group), len(group))
        )

    summary = "%s: `%s` exited %s in %.1fs, replaying %d fact-ledger evidence row(s)." % (
        "GREEN" if green else "RED",
        command if len(command) <= 90 else command[:87] + "...",
        exit_status,
        result["duration_ms"] / 1000.0,
        len(group),
    )

    record = {
        "schema_version": 1,
        "id": rid,
        "role": role,
        "outcome": outcome,
        "provenance": {
            "generator": generator,
            "command": command,
            "inputs": inputs,
            "exit_status": exit_status,
            "epoch": epoch,
            "duration_ms": result["duration_ms"],
        },
        "summary": summary,
        "claims": claims,
        "stats": stats,
        "replay": {
            "line": command,
            "cwd": ".",
            "expected_exit_status": 0,
            "expected_seconds": max(1, int(math.ceil(result["duration_ms"] / 1000.0))),
        },
        "notes": " ".join(notes),
    }
    return record


def emit(record: dict, out_dir: str) -> str:
    name = record["id"].replace(":", "-", 1) + ".json"
    path = os.path.join(out_dir, name)
    with open(path, "w", encoding="ascii") as fh:
        fh.write(canonical_json(record))
    return path


def validate(paths: list[str]) -> tuple[int, str]:
    if not os.path.isfile(VALIDATOR):
        return (2, "scripts/validate-docir.py is not in the tree")
    proc = subprocess.run(
        [sys.executable, VALIDATOR, "--kind", "run-record"] + paths,
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )
    return (proc.returncode, (proc.stdout + proc.stderr).strip())


# --------------------------------------------------------------------------
# The checker-sensitivity control.
#
# A `negative-control` record is a recording of a deliberately broken run, kept
# to show what the checker does with it. This one is unusual and is labelled as
# such: it shows that a name-only kernel-term row does NOT catch a restated
# theorem. The run exits 0 -- which is the whole point -- so its `outcome` is
# `refuted`: what it refutes is the checker's sensitivity, not the mathematics.
# `scripts/validate-docir.py` rejects a control that exited 0 and still claims
# `outcome: established`, which is exactly the shape being avoided here.
# --------------------------------------------------------------------------
CONTROL_CMD = (
    "cargo run -q -p axeyum-lean-kernel --example nat_theorem_inventory -- add_comm 2>/dev/null "
    "| sed 's/Eq[.]{1} AxNat (AxNat[.]add x0 x1) (AxNat[.]add x1 x0)/AxNat.le x0 x1/' "
    "| grep -qE '^Nat[.]add_comm[[:space:]]'"
)


def build_control(epoch: dict, timeout: int) -> tuple[dict, dict]:
    result = run_command(CONTROL_CMD, timeout)
    exit_status = result["exit_status"]
    caught = exit_status != 0
    record = {
        "schema_version": 1,
        "id": "R:control-nat-add-comm-name-only-blind",
        "role": "negative-control",
        "outcome": "established" if caught else "refuted",
        "provenance": {
            "generator": "render/producers-runrec/facts_to_runrec.py --negative-control",
            "command": CONTROL_CMD,
            "inputs": declared_inputs(CONTROL_CMD, None),
            "exit_status": exit_status,
            "epoch": epoch,
            "duration_ms": result["duration_ms"],
        },
        "summary": (
            "MUTATED INPUT, DELIBERATE: the theorem's printed type is rewritten to a "
            "different proposition before the row's grep sees it, and the grep of "
            "`F:nat-add-comm`'s `kernel-add-comm` row %s (exit %s)."
            % ("CAUGHT it" if caught else "STILL PASSED", exit_status)
        ),
        "claims": [
            {
                "key": "name-only-row-is-blind-to-the-type",
                "status": "evidence" if not caught else "open",
                "statement": (
                    "`F:nat-add-comm`'s `kernel-add-comm` checker command matches only the "
                    "theorem NAME in the kernel inventory: with the printed type replaced by "
                    "`AxNat.le x0 x1` -- a different proposition -- the same grep exits %s."
                    % exit_status
                ),
                "note": (
                    "Evidence about the CHECKER, never about the mathematics. Nat.add_comm is "
                    "genuinely admitted by the kernel; what this control measures is that the "
                    "ledger row would not notice if it were not."
                ),
            }
        ],
        "stats": {
            "checker_caught_the_mutation": caught,
            "wall_seconds": round(result["duration_ms"] / 1000.0, 3),
        },
        "replay": {
            "line": CONTROL_CMD,
            "cwd": ".",
            "expected_exit_status": exit_status if exit_status is not None else 0,
            "expected_seconds": max(1, int(math.ceil(result["duration_ms"] / 1000.0))),
        },
        "notes": (
            "NOT A DEFECT REPORT AND NOT SUPPORT FOR ANY FACT. Assembly refuses to cite a "
            "`negative-control` record under any role but `negative-control`, so this file "
            "cannot be quoted as evidence for F:nat-add-comm. It exists because "
            "'13 of 17 kernel-term rows check the name and not the type' is a claim that "
            "should be measured rather than asserted in a diary."
        ),
    }
    return record, result


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--facts-from", default=DEFAULT_FACTS_DOC, help="Doc-IR document to read F: ids from")
    ap.add_argument("--fact", action="append", default=[], help="extra fact id (repeatable)")
    ap.add_argument("--no-extra-facts", action="store_true", help="omit the built-in Rado headline facts")
    ap.add_argument("--out-dir", default=DEFAULT_OUT)
    ap.add_argument("--timeout", type=int, default=120, help="per-command wall-clock seconds")
    ap.add_argument("--survey", action="store_true", help="classify and print; run nothing")
    ap.add_argument("--negative-control", action="store_true", help="also run the checker-sensitivity control")
    ap.add_argument("--allow-red", action="store_true")
    ap.add_argument("--allow-skips", action="store_true")
    args = ap.parse_args()

    fact_ids = fact_ids_from_doc(args.facts_from)
    if not args.no_extra_facts:
        fact_ids += [f for f in EXTRA_FACTS if f not in fact_ids]
    fact_ids += [f for f in args.fact if f not in fact_ids]
    missing = [f for f in fact_ids if not os.path.isfile(fact_path(f))]
    if missing:
        sys.exit("error: fact(s) not in the ledger: %s" % ", ".join(missing))
    if not fact_ids:
        print("nothing to do: no fact ids", file=sys.stderr)
        return 2

    rows = collect_rows(fact_ids)
    if not rows:
        print("nothing to do: those facts carry no evidence rows", file=sys.stderr)
        return 2

    for row in rows:
        row["class"], row["why"] = classify(row)

    runnable = [r for r in rows if r["class"] == "runnable"]
    skipped = [r for r in rows if r["class"] != "runnable"]

    print("=== classification: %d facts, %d evidence rows ===" % (len(fact_ids), len(rows)))
    print("%-34s %-32s %-26s %-12s %s" % ("fact", "row", "kind", "class", "why/command"))
    for r in rows:
        cmd = r["command"] or ""
        print(
            "%-34s %-32s %-26s %-12s %s"
            % (
                r["fact_id"][:34],
                r["row_id"][:32],
                r["kind"][:26],
                r["class"],
                r["why"] if r["why"] else (cmd[:70] + ("..." if len(cmd) > 70 else "")),
            )
        )
    print("runnable=%d not-runnable=%d" % (len(runnable), len(skipped)))

    # Group by exact command text.
    groups: dict[str, list[dict]] = {}
    for r in runnable:
        groups.setdefault(r["command"], []).append(r)
    order = sorted(groups, key=lambda c: (groups[c][0]["fact_id"], groups[c][0]["row_id"]))
    print("distinct commands to execute: %d (from %d rows)" % (len(order), len(runnable)))

    if args.survey:
        return 0

    os.makedirs(args.out_dir, exist_ok=True)
    epoch = git_epoch()
    written, index, reds, timeouts = [], [], [], []

    for cmd in order:
        group = sorted(groups[cmd], key=lambda r: (r["fact_id"], r["row_id"]))
        result = run_command(cmd, args.timeout)
        if result["timed_out"]:
            timeouts.append((cmd, group))
            print("TIMEOUT (>%ds), skipped, nothing recorded: %s" % (args.timeout, cmd[:100]))
            continue
        record = build_record(group, result, epoch, "production")
        path = emit(record, args.out_dir)
        written.append(path)
        if result["exit_status"] != 0:
            reds.append(record["id"])
        print(
            "%-4s exit=%-3s %6.2fs  %s  <- %s"
            % (
                "RED" if result["exit_status"] else "ok",
                result["exit_status"],
                result["duration_ms"] / 1000.0,
                os.path.relpath(path, REPO_ROOT),
                ", ".join("%s/%s" % (r["fact_id"], r["row_id"]) for r in group),
            )
        )
        for row, claim in zip(group, record["claims"]):
            index.append(
                {
                    "fact_id": row["fact_id"],
                    "evidence_row": row["row_id"],
                    "evidence_kind": row["kind"],
                    "run_record": os.path.relpath(path, args.out_dir),
                    "record_id": record["id"],
                    "claim_key": claim["key"],
                    "claim_status": claim["status"],
                    "exit_status": record["provenance"]["exit_status"],
                }
            )

    if args.negative_control:
        record, result = build_control(epoch, args.timeout)
        if result["timed_out"]:
            print("TIMEOUT on the negative control; nothing recorded")
        else:
            path = emit(record, args.out_dir)
            written.append(path)
            print(
                "ctrl exit=%-3s %6.2fs  %s  (checker caught the mutation: %s)"
                % (
                    result["exit_status"],
                    result["duration_ms"] / 1000.0,
                    os.path.relpath(path, REPO_ROOT),
                    record["stats"]["checker_caught_the_mutation"],
                )
            )

    idx_path = os.path.join(args.out_dir, "runrec-index.json")
    with open(idx_path, "w", encoding="ascii") as fh:
        fh.write(
            canonical_json(
                {
                    "schema_version": 1,
                    "kind": "runrec-index",
                    "note": (
                        "NOT a Doc-IR document and NOT a run record: a lookup table from "
                        "(fact id, evidence row) to the run record that replayed that row. "
                        "Do not pass it to scripts/validate-docir.py. Several rows may share "
                        "one record when they share one command; that is one check, not many."
                    ),
                    "epoch": epoch,
                    "entries": sorted(
                        index, key=lambda e: (e["fact_id"], e["evidence_row"])
                    ),
                    "not_runnable": sorted(
                        (
                            {
                                "fact_id": r["fact_id"],
                                "evidence_row": r["row_id"],
                                "evidence_kind": r["kind"],
                                "reason": r["why"],
                            }
                            for r in skipped
                        ),
                        key=lambda e: (e["fact_id"], e["evidence_row"]),
                    ),
                }
            )
        )

    rc_val, out_val = validate(sorted(written))
    print("--- validate-docir.py --kind run-record: exit %d ---" % rc_val)
    if out_val:
        print(out_val)

    print("=== summary ===")
    print("evidence rows          : %d" % len(rows))
    print("rows runnable          : %d" % len(runnable))
    print("commands executed      : %d" % (len(order) - len(timeouts)))
    print("records written        : %d" % len(written))
    print("green runs             : %d" % (len(order) - len(timeouts) - len(reds)))
    print("RED runs               : %d %s" % (len(reds), reds if reds else ""))
    print("timed out (>%ds)       : %d" % (args.timeout, len(timeouts)))
    print("rows not runnable      : %d" % len(skipped))
    for r in skipped:
        print("    %s / %s -- %s" % (r["fact_id"], r["row_id"], r["why"]))

    bad = 0
    if rc_val != 0:
        print("FAIL: at least one emitted record does not validate")
        bad = 1
    if reds and not args.allow_red:
        print("FAIL: %d red run(s); pass --allow-red to record them without failing" % len(reds))
        bad = 1
    if (skipped or timeouts) and not args.allow_skips:
        print(
            "FAIL: %d row(s) could not be run; pass --allow-skips to accept"
            % (len(skipped) + sum(len(g) for _, g in timeouts))
        )
        bad = 1
    if not written:
        print("FAIL: nothing was written (an empty run is not a passing run)")
        return 2
    return bad


if __name__ == "__main__":
    sys.exit(main())
