#!/usr/bin/env python3
"""Validate Doc-IR documents and run records, independently of the Rust model.

Mirrors `scripts/validate-facts.py`: the schema in
`artifacts/ontology/docir.schema.json` is one implementation of the format and
`render/src/ir.rs` is another, and neither is allowed to be the only one. This
script is the third party that makes a disagreement between them visible.

WHAT IT CHECKS. Structure against the JSON Schema (using `jsonschema` when it is
importable, and a hand-rolled subset when it is not -- see `--require-jsonschema`
if you need the strong form), plus the semantic rules a schema cannot express:

  * block ids are unique within a document (they are anchor targets);
  * every claim carries at least one evidence reference;
  * a literal table has exactly one cell per column in every row;
  * a run record's claim keys are unique;
  * a run record that did NOT complete (`exit_status != 0`) does not also say
    it established something (`outcome: established`) -- a run cannot both fail
    and have found what it was looking for, and that combination is how a
    checker that cannot fail looks from the outside;
  * every figure has an `alt`;
  * the file is ASCII (repository-wide rule).

EXIT STATUS DEPENDS ON THE FINDING, not on completion:
  0  every file checked, no errors -- AND at least one file was checked
  1  at least one error
  2  usage, or nothing was checked (an empty check is not a passing check)

`--canonicalize` prints the canonical form of one file -- sorted keys, two-space
indent, ASCII, one trailing newline -- which is byte-for-byte what
`axeyum_render::canonical_json` produces. That equality is the round-trip test.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

DEFAULT_SCHEMA = "artifacts/ontology/docir.schema.json"

BLOCK_TYPES = {
    "prose",
    "claim",
    "statement",
    "steps",
    "table",
    "certificate",
    "figure",
    "include",
}
VERBOSITY = {"essential", "detail", "archive"}
STATUSES = {"proved", "checked", "evidence", "advisory", "refuted", "open"}
OUTCOMES = {"established", "refuted", "inconclusive"}


class Findings:
    def __init__(self) -> None:
        self.errors: list[str] = []
        self.warnings: list[str] = []
        self.checks = 0

    def error(self, where: str, msg: str) -> None:
        self.errors.append(f"{where}: {msg}")

    def warn(self, where: str, msg: str) -> None:
        self.warnings.append(f"{where}: {msg}")


def canonical(obj) -> str:
    return json.dumps(obj, indent=2, sort_keys=True, ensure_ascii=True) + "\n"


def detect_kind(obj) -> str:
    if isinstance(obj, dict) and "blocks" in obj and "meta" in obj:
        return "document"
    if isinstance(obj, dict) and "provenance" in obj and "summary" in obj:
        return "run-record"
    return "unknown"


def schema_validate(obj, kind: str, schema: dict, where: str, f: Findings, strict: bool) -> None:
    """Structural validation. Uses `jsonschema` when available."""
    try:
        import jsonschema
    except ImportError:
        if strict:
            f.error(where, "jsonschema is not importable and --require-jsonschema was given")
            return
        f.warn(where, "jsonschema not importable; structural checks are the hand-rolled subset")
        hand_rolled(obj, kind, where, f)
        return

    if kind == "run-record":
        sub = dict(schema)
        sub["$ref"] = "#/$defs/RunRecord"
        for key in ("type", "required", "properties", "additionalProperties"):
            sub.pop(key, None)
        validator = jsonschema.Draft202012Validator(sub)
    else:
        validator = jsonschema.Draft202012Validator(schema)

    for err in sorted(validator.iter_errors(obj), key=lambda e: list(e.path)):
        path = "/".join(str(p) for p in err.path) or "<root>"
        f.error(where, f"schema: at {path}: {err.message}")
    f.checks += 1


def hand_rolled(obj, kind: str, where: str, f: Findings) -> None:
    """The subset worth having when `jsonschema` is missing.

    Deliberately narrow and deliberately honest about being narrow: it checks
    the discriminators and required keys that everything downstream indexes on,
    and it does not pretend to be the schema.
    """
    if not isinstance(obj, dict):
        f.error(where, "top level is not an object")
        return
    if obj.get("schema_version") != 1:
        f.error(where, f"schema_version is {obj.get('schema_version')!r}, expected 1")
    if kind == "document":
        for key in ("meta", "blocks"):
            if key not in obj:
                f.error(where, f"missing required key {key!r}")
        meta = obj.get("meta", {})
        for key in ("doc_id", "title", "epoch"):
            if key not in meta:
                f.error(where, f"meta: missing required key {key!r}")
        for i, block in enumerate(obj.get("blocks", [])):
            at = f"blocks[{i}]"
            for key in ("id", "tag", "kind"):
                if key not in block:
                    f.error(where, f"{at}: missing required key {key!r}")
            if block.get("tag") not in VERBOSITY:
                f.error(where, f"{at}: tag {block.get('tag')!r} is not one of {sorted(VERBOSITY)}")
            if block.get("kind", {}).get("type") not in BLOCK_TYPES:
                f.error(
                    where,
                    f"{at}: kind.type {block.get('kind', {}).get('type')!r} is not a block kind",
                )
    else:
        for key in ("id", "provenance", "summary"):
            if key not in obj:
                f.error(where, f"missing required key {key!r}")
        prov = obj.get("provenance", {})
        for key in ("generator", "command", "inputs", "exit_status", "epoch"):
            if key not in prov:
                f.error(where, f"provenance: missing required key {key!r}")
    f.checks += 1


def check_evidence_roles(kind: dict, at: str, doc_dir, where: str, f: Findings) -> None:
    """The negative-control pairing, checked independently of the Rust resolver.

    A record whose `role` is `negative-control` records a deliberately broken
    run. Citing it as support would put a mutant's red run behind a claim, so
    the reference must declare `role: negative-control` -- and, in the other
    direction, that role must not be pointed at a production run, or the page
    tells its reader that a green run was expected to fail.

    Unresolvable paths are NOT an error here: the Rust assembler owns the
    dangling-reference rule and reports it with the manifest's search paths.
    This check only speaks about records it can actually read.
    """
    for j, ev in enumerate(kind.get("evidence") or []):
        rel = ev.get("run_record")
        if not isinstance(rel, str) or doc_dir is None:
            continue
        rec_path = (doc_dir / rel)
        if not rec_path.is_file():
            continue
        try:
            rec = json.loads(rec_path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        declared = ev.get("role", "primary")
        actual = rec.get("role", "production")
        if actual == "negative-control" and declared != "negative-control":
            f.error(
                where,
                f"{at}: evidence[{j}] cites `{rec.get('id')}`, a NEGATIVE CONTROL, "
                f"as `{declared}` -- i.e. as support. A deliberately broken run never "
                "supports a claim (fail-closed law rule 2)",
            )
        if actual != "negative-control" and declared == "negative-control":
            f.error(
                where,
                f"{at}: evidence[{j}] declares `role: negative-control` over "
                f"`{rec.get('id')}`, which is a production run",
            )


def check_document(doc: dict, where: str, f: Findings, doc_dir=None) -> None:
    seen: dict[str, int] = {}
    for i, block in enumerate(doc.get("blocks", [])):
        at = f"blocks[{i}] `{block.get('id')}`"
        bid = block.get("id")
        if bid in seen:
            f.error(where, f"{at}: duplicate block id (also blocks[{seen[bid]}])")
        elif isinstance(bid, str):
            seen[bid] = i

        kind = block.get("kind", {})
        ktype = kind.get("type")

        if ktype == "claim":
            if not kind.get("evidence"):
                f.error(
                    where,
                    f"{at}: claim `{kind.get('label')}` carries no evidence "
                    "(fail-closed law rule 1)",
                )
            if kind.get("status") not in STATUSES:
                f.error(where, f"{at}: status {kind.get('status')!r} is not a badge vocabulary term")
            check_evidence_roles(kind, at, doc_dir, where, f)

        if ktype == "table":
            if "from_run" not in kind:
                cols = kind.get("columns") or []
                for r, row in enumerate(kind.get("rows") or []):
                    if len(row) != len(cols):
                        f.error(
                            where,
                            f"{at}: row {r} has {len(row)} cells but {len(cols)} columns",
                        )
                if not kind.get("source"):
                    f.error(where, f"{at}: literal table with no `source` provenance")

        if ktype == "certificate":
            # The same rule the Rust resolver enforces, stated independently:
            # a box that says "nothing recorded a run" while naming the run it
            # recorded makes two contradictory statements, and a reader cannot
            # tell which one the page means.
            if kind.get("no_exit_reason") and kind.get("evidence"):
                f.error(
                    where,
                    f"{at}: certificate states `no_exit_reason` "
                    f"({kind['no_exit_reason']!r}) and yet cites "
                    f"{len(kind['evidence'])} run record(s). Either an execution was "
                    "recorded or it was not",
                )
            # And the other half, which the Rust side reports as an EMITTER
            # diagnostic rather than a refusal: silence about whether anything
            # ran at all. Reported here as a warning, because a certificate is
            # allowed to be an invitation to the reader -- it just has to say
            # so.
            if not kind.get("no_exit_reason") and not kind.get("evidence"):
                f.warn(
                    where,
                    f"{at}: certificate carries neither `evidence` nor "
                    "`no_exit_reason`; the rendered box will imply a run that "
                    "nothing records",
                )

        if ktype == "figure" and not kind.get("alt"):
            f.error(where, f"{at}: figure has no `alt` text")

        if ktype == "statement" and "ref" not in kind:
            f.error(where, f"{at}: statement block with no `ref`")

    if doc.get("meta", {}).get("epoch", {}).get("source") == "fixed":
        f.warn(where, "meta.epoch.source is `fixed`: honest for a fixture, not for a publication")
    f.checks += 1


def check_run_record(rec: dict, where: str, f: Findings) -> None:
    prov = rec.get("provenance", {})
    exit_status = prov.get("exit_status")
    outcome = rec.get("outcome", "established")

    if outcome not in OUTCOMES:
        f.error(where, f"outcome {outcome!r} is not one of {sorted(OUTCOMES)}")
    if isinstance(exit_status, int) and exit_status != 0 and outcome == "established":
        f.error(
            where,
            f"exit_status is {exit_status} but outcome is `established`: a run that did not "
            "complete cannot also have found what it was looking for",
        )

    keys: dict[str, int] = {}
    for i, claim in enumerate(rec.get("claims", [])):
        key = claim.get("key")
        if key in keys:
            f.error(where, f"claims[{i}]: duplicate claim key {key!r} (also claims[{keys[key]}])")
        elif isinstance(key, str):
            keys[key] = i
        if claim.get("status") not in STATUSES:
            f.error(where, f"claims[{i}]: status {claim.get('status')!r} is not a badge term")

    if rec.get("role") == "negative-control" and exit_status == 0 and outcome == "established":
        f.error(
            where,
            "this record declares `role: negative-control` -- a run of a deliberately "
            "broken variant -- but it exited 0 and reports `established`. A negative "
            "control that did not fail is not a control: either the mutation is inert "
            "or the checker cannot see it",
        )

    for name, table in (rec.get("tables") or {}).items():
        ncols = len(table.get("columns", []))
        for r, row in enumerate(table.get("rows", [])):
            if len(row) != ncols:
                f.error(where, f"tables[{name}]: row {r} has {len(row)} cells but {ncols} columns")

    for i, inp in enumerate(prov.get("inputs", [])):
        digest = inp.get("sha256", "")
        if len(digest) != 64 or any(c not in "0123456789abcdef" for c in digest):
            f.error(where, f"provenance.inputs[{i}]: {digest!r} is not a lowercase hex SHA-256")
    f.checks += 1


def check_ascii(raw: bytes, where: str, f: Findings) -> None:
    try:
        raw.decode("ascii")
    except UnicodeDecodeError as e:
        f.error(where, f"non-ASCII byte at offset {e.start} (repository-wide rule)")
    f.checks += 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="*", help="Doc-IR documents and/or run records")
    ap.add_argument("--kind", choices=["auto", "document", "run-record"], default="auto")
    ap.add_argument("--schema", default=None)
    ap.add_argument("--canonicalize", action="store_true", help="print canonical JSON of one file")
    ap.add_argument("--require-jsonschema", action="store_true")
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()

    if not args.paths:
        print("validate-docir: no files given; an empty check is not a passing check", file=sys.stderr)
        return 2

    if args.canonicalize:
        if len(args.paths) != 1:
            print("validate-docir: --canonicalize takes exactly one file", file=sys.stderr)
            return 2
        sys.stdout.write(canonical(json.loads(Path(args.paths[0]).read_text())))
        return 0

    root = Path(__file__).resolve().parents[1]
    schema_path = Path(args.schema) if args.schema else root / DEFAULT_SCHEMA
    schema = json.loads(schema_path.read_text())

    f = Findings()
    files = 0
    for p in args.paths:
        path = Path(p)
        where = str(path)
        try:
            raw = path.read_bytes()
        except OSError as e:
            f.error(where, f"cannot read: {e}")
            continue
        check_ascii(raw, where, f)
        try:
            obj = json.loads(raw)
        except json.JSONDecodeError as e:
            f.error(where, f"not JSON: {e}")
            continue

        kind = args.kind if args.kind != "auto" else detect_kind(obj)
        if kind == "unknown":
            f.error(where, "cannot tell whether this is a document or a run record")
            continue

        schema_validate(obj, kind, schema, where, f, args.require_jsonschema)
        if kind == "document":
            check_document(obj, where, f, path.resolve().parent)
        else:
            check_run_record(obj, where, f)
        files += 1

    for w in f.warnings:
        print(f"WARN  {w}", file=sys.stderr)
    for e in f.errors:
        print(f"ERROR {e}", file=sys.stderr)

    if files == 0:
        print("validate-docir: 0 files checked -- refusing to report success", file=sys.stderr)
        return 2
    if not args.quiet:
        print(
            f"validate-docir: {files} file(s), {f.checks} check group(s), "
            f"{len(f.errors)} error(s), {len(f.warnings)} warning(s)"
        )
    return 1 if f.errors else 0


if __name__ == "__main__":
    sys.exit(main())
