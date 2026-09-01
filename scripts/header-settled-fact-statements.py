#!/usr/bin/env python3
"""Give a settled fact's `formal.statement` the `theorem <name> :` header that
makes it checkable against the declaration the fact claims.

WHY THIS EXISTS
---------------

`scripts/check-settled-fact-statements.py` carries a structural bind: a `lean4`
statement rendered by `Kernel::render_lean` opens `theorem <name> :`, and that
name must be the fact's `formal.kernel_theorem`. It is the sharpest statement
check in the ledger, because it catches a statement replaced by a *different*
declaration's rendering — something no content hash can describe.

A statement with no header is exempt from that bind, and the exemption is
counted (`coverage_floor.max_header_exempt`) so a new one cannot appear quietly.
But the count only sees a fact once it NAMES a declaration. On 2026-08-31 the
`resolve-kernel-subjects` lane annotated 28 facts with the
`formal.kernel_theorem` they had been missing; twelve of those carried headerless
statements, which had always been headerless and had never been counted. The
allowance went 67 -> 79 and the L0 gate reddened. Nothing regressed — the ledger
got more honest, and the honest fix is to give the statements their header, not
to raise the ceiling.

WHAT THIS DOES, AND THE PRECONDITION THAT MAKES IT SAFE
------------------------------------------------------

A settled `lean4` fact naming `formal.kernel_theorem = N` whose
`formal.statement` is **byte-for-byte** the kernel's own `canonical_type` for
`N` is rewritten to `<keyword> N : <statement>`. That is a PURE PREFIX: the
proposition is untouched, and the byte-identity against the kernel's rendering
is what proves it. The keyword follows the declaration's kind
(`theorem`/`def`/`inductive`/`axiom`/`opaque`), matching the convention already
in the ledger (1,620 `theorem` headers and 21 `def` ones as of this writing).

Anything else is REFUSED and reported, never guessed:

* **ABSENT** — the name is in no prelude's environment. These are the
  proof-isolated `ml430` imports, checked through an ephemeral
  `Kernel::add_declaration` that is discarded per fact and never merged. There
  is no persistent declaration to render, so there is no honest header to write.
* **DIVERGENT** — the declaration exists but the statement is not its rendering.
  Replacing the text would be a content change; that is an editorial act needing
  its own amendment, and this tool will not make it look mechanical.
* **AMBIGUOUS** — one name renders to two different types across preludes.
* **UNKNOWN-KIND** — a declaration kind with no header keyword.

`--apply` also appends one amendment row per rewritten fact to
`artifacts/ontology/settled-fact-statement-pins.json`. It must:
`check-settled-fact-statements.py` refuses to re-pin a changed statement without
one, deliberately, so that running `--write` after a drift cannot launder it.
The amendment records both digests and says the change was a prefix.

THE TRAP THIS AVOIDS (ADR-1275)
-------------------------------

Running `check-settled-fact-statements.py --write` BEFORE the statements carry
their header pins the headerless form, which then reads as unamended drift. So
the order is: dump the declaration's true rendered type from the kernel, set the
statement, THEN pin.

USAGE
-----

    cargo run -q --release -p axeyum-lean-kernel \\
      --example kernel_declaration_projection > /tmp/projection.tsv
    python3 scripts/header-settled-fact-statements.py --projection /tmp/projection.tsv --check
    python3 scripts/header-settled-fact-statements.py --projection /tmp/projection.tsv --apply
    python3 scripts/check-settled-fact-statements.py --write

`--release` on the projection is MANDATORY: in debug it builds `creal`/`complex`/
`cpoint` deep enough to overflow the thread stack, which looks like a broken tool.

EXIT STATUS
-----------

`--check` exits **1** when at least one fixable fact is still headerless — the
status depends on the finding, not on the run completing. It exits **0** when
none is, even if refusals remain: a refusal is not something `--apply` can fix.
Bad input (missing projection, unreadable manifest) exits **2**.

Controls: `scripts/tests/test_header_settled_fact_statements.py`, registered in
`scripts/tests/mutation_controls.py` under `header-settled-fact-statements`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
SETTLED = {"proved", "computed"}

# Must stay in step with `check-settled-fact-statements.py`'s own HEADER.
HEADER = re.compile(r"^\s*(theorem|def|axiom|opaque|abbrev|inductive)\s+(\S+)\s*:")

# Declaration kind (as `kernel_declaration_projection` spells it) -> the Lean
# keyword a rendered header opens with. A kind absent from this map is refused
# rather than defaulted: `theorem` is not a safe default for a definition.
KEYWORD = {
    "theorem": "theorem",
    "definition": "def",
    "inductive": "inductive",
    "axiom": "axiom",
    "opaque": "opaque",
}

REASON = (
    "HEADER ONLY -- a pure prefix, not a content change. `formal.statement` was "
    "byte-for-byte the kernel's own `canonical_type` for {name} "
    "(`Kernel::render_lean(declaration.ty())`, read from "
    "`kernel_declaration_projection --release`), and is now that same string "
    "behind `{keyword} {name} : `. The proposition is untouched; what changes is "
    "that `check-settled-fact-statements.py`'s structural bind can now check the "
    "statement against the declaration this fact claims, instead of exempting it. "
    "The fact became visible to that check only when `366f11a91` supplied its "
    "`formal.kernel_theorem`; it was headerless before and after, and no ceiling "
    "was raised to accommodate it."
)


class HeaderError(Exception):
    pass


def digest(statement: object) -> str:
    return hashlib.sha256(str(statement).encode()).hexdigest()


def read_projection(path: pathlib.Path) -> dict[str, set[tuple[str, str]]]:
    """name -> {(kind, canonical_type)}, from the projection's TSV rows."""
    if not path.is_file():
        raise HeaderError(f"no projection at {path} — run kernel_declaration_projection --release")
    decls: dict[str, set[tuple[str, str]]] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        parts = line.split("\t")
        if len(parts) < 8:
            continue
        _label, kind, name, _fp, _dt, _dd, _th, canonical = parts[:8]
        decls.setdefault(name, set()).add((kind, canonical))
    if not decls:
        raise HeaderError(f"projection {path} carried no declarations — the tool has no subject")
    return decls


def classify(
    facts_dir: pathlib.Path, decls: dict[str, set[tuple[str, str]]]
) -> tuple[list[dict], list[tuple[str, str, str]]]:
    """Return (fixable, refused). Pure, so `--check` and `--apply` agree."""
    fixable: list[dict] = []
    refused: list[tuple[str, str, str]] = []
    for path in sorted(facts_dir.glob("*.json")):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise HeaderError(f"unreadable fact {path.name}: {exc}") from exc
        if data.get("epistemic_status") not in SETTLED:
            continue
        formal = data.get("formal") or {}
        statement = formal.get("statement")
        name = formal.get("kernel_theorem")
        if formal.get("language") != "lean4" or not name or not isinstance(statement, str):
            continue
        if HEADER.match(statement):
            continue

        found = decls.get(name)
        if not found:
            refused.append((data["id"], name, "ABSENT"))
            continue
        canonicals = {canonical for _kind, canonical in found}
        if len(canonicals) > 1:
            refused.append((data["id"], name, "AMBIGUOUS"))
            continue
        if statement not in canonicals:
            refused.append((data["id"], name, "DIVERGENT"))
            continue
        kinds = {kind for kind, _canonical in found}
        keywords = {KEYWORD[kind] for kind in kinds if kind in KEYWORD}
        if len(keywords) != 1:
            refused.append((data["id"], name, "UNKNOWN-KIND"))
            continue
        keyword = keywords.pop()
        fixable.append(
            {
                "fact_id": data["id"],
                "path": path,
                "name": name,
                "keyword": keyword,
                "old": statement,
                "new": f"{keyword} {name} : {statement}",
            }
        )
    return fixable, refused


def apply(fixable: list[dict], pins_path: pathlib.Path, date: str) -> None:
    if not pins_path.is_file():
        raise HeaderError(f"missing pins manifest: {pins_path}")
    try:
        manifest = json.loads(pins_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise HeaderError(f"unreadable pins manifest: {exc}") from exc

    amendments = list(manifest.get("amendments") or [])
    already = {row.get("fact_id") for row in amendments if isinstance(row, dict)}

    for row in fixable:
        data = json.loads(row["path"].read_text(encoding="utf-8"))
        data["formal"]["statement"] = row["new"]
        row["path"].write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
        if row["fact_id"] in already:
            continue
        amendments.append(
            {
                "fact_id": row["fact_id"],
                "date": date,
                "from_sha256": digest(row["old"]),
                "to_sha256": digest(row["new"]),
                "reason": REASON.format(name=row["name"], keyword=row["keyword"]),
                "recorded_by": "statement-headers",
            }
        )

    manifest["amendments"] = amendments
    pins_path.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")


def run(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="header settled fact statements")
    parser.add_argument("--projection", required=True, type=pathlib.Path)
    parser.add_argument("--facts", type=pathlib.Path, default=ROOT / "artifacts/facts")
    parser.add_argument(
        "--pins",
        type=pathlib.Path,
        default=ROOT / "artifacts/ontology/settled-fact-statement-pins.json",
    )
    parser.add_argument("--date", default="2026-08-31")
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args(argv)

    if args.check and args.apply:
        raise HeaderError("--check and --apply are mutually exclusive")
    if not args.check and not args.apply:
        args.check = True

    decls = read_projection(args.projection)
    fixable, refused = classify(args.facts, decls)

    for fact_id, name, why in refused:
        print(f"HEADER_STATEMENTS|REFUSED|{why}|{fact_id}|{name}", file=sys.stderr)

    if args.apply:
        apply(fixable, args.pins, args.date)
        print(
            f"HEADER_STATEMENTS|applied={len(fixable)}|refused={len(refused)}|"
            f"declarations={len(decls)}"
        )
        return 0

    for row in fixable:
        print(f"HEADER_STATEMENTS|FIXABLE|{row['fact_id']}|{row['keyword']} {row['name']}")
    print(
        f"HEADER_STATEMENTS|fixable={len(fixable)}|refused={len(refused)}|"
        f"declarations={len(decls)}"
    )
    if fixable:
        print(
            f"HEADER_STATEMENTS|FAIL|{len(fixable)} settled lean4 fact(s) name a declaration "
            "whose rendered type they already carry verbatim, and could be headed but are not",
            file=sys.stderr,
        )
        return 1
    print("HEADER_STATEMENTS|PASS")
    return 0


def main() -> int:
    try:
        return run()
    except HeaderError as exc:
        print(f"HEADER_STATEMENTS|ERROR|{exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
