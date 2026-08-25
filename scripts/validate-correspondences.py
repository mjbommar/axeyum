#!/usr/bin/env python3
"""Validate `artifacts/correspondences/*.json`: claims that two facts are the same idea.

A correspondence is NOT a proof dependency, and keeping the two apart is most of
this gate's job. `depends_on` says one proof used the other; a correspondence says
the two statements are the same mathematical content whether or not either proof
ever mentions the other. Cassini's identity and the multiplicativity of a 2x2
determinant are one theorem, and no `depends_on` edge will ever connect them
because Cassini's proof is an induction that never mentions a determinant. So the
rule is exclusive in both directions: a correspondence whose endpoints the fact
ledger already connects -- directly or transitively -- is REFUSED, with the
message naming `depends_on` as the field that belongs there instead.

The rest of the rules exist because the sibling `math-education` corpus already
ran the experiment of requiring a prose reason and nothing else. Measured there:
1,263 `bridges_to` edges, 100% carrying a reason, median 190 characters -- and
`volume.md` still shipped a bridge to `C:pi` whose reason text was entirely about
density. It validated cleanly because both fields were well-formed. Prose is not
evidence, so every rule below is about something a machine can recompute:

  * VACUITY. An empty correspondence directory, or an empty fact ledger, is an
    error. A gate whose subject has vanished prints the same "no violations" as
    one that works.
  * Endpoints resolve, are distinct, and are SETTLED (`proved` / `computed`).
    Two things cannot be the same idea when one of them is not established.
  * The endpoints' formal statements must DIFFER. A correspondence between two
    identical statements is a duplicate fact, and belongs in a dedup pass.
  * `carrier-transport` is checked STRUCTURALLY, not taken on trust: the two
    facts must be in different fragments, and erasing the carrier from both
    formal statements must leave the same string. `Nat.fib n = 0 <-> n = 0` and
    `Int.fib n = 0 <-> n = 0` both erase to `<C>.fib n = 0 <-> n = 0`; an
    unrelated pair does not, and is rejected. A fragment with no entry in
    CARRIERS fails closed rather than skipping the check -- a carrier the map
    does not know is an unmeasured claim, not a passing one.
  * `independent-formalization` requires DIFFERENT proof routes. Its whole
    content is that two machines reached the same theorem separately; two facts
    on the same route are one formalization recorded twice.
  * The two status axes are the ledger's, applied to the edge. `derivation_status`
    is what WE established about the correspondence, `external_status` what
    mathematics knows -- and each is BACKED, not toned:
      - `asserted` <-> `via` is empty. Exactly, both ways.
      - `route-recorded` requires `via` non-empty with every non-null `ref`
        resolving to a fact or to a declaration the kernel projection has
        actually observed. A route naming an object that does not exist is the
        failure this array exists to make impossible.
      - a `specialization` additionally requires at least ONE non-blank `ref`
        among its steps, whatever its derivation_status. `route-recorded`
        permits null refs generally and should -- a step may be an algebraic
        rearrangement with nothing to cite -- but a specialisation is by
        definition an instantiation OF something, and a route of prose with
        every reference null names no general theorem at all.
      - `mechanized-here` additionally forbids a null `ref` and requires
        evidence carrying a checker command.
      - evidence at all requires `mechanized-here`, mirroring the fact ledger's
        rule that an `open` fact must carry an EMPTY evidence array.
      - `external_status: novel-here` requires `mechanized-here`. Claiming the
        connection is new to mathematics while nothing here derives it is the
        one combination that is pure tone.

Exit status depends on what was found: 1 for any violation, 1 for a vacuous
population, 0 only with a non-empty population and no violations. The
`CORRESPONDENCES|...` line reports per-kind counts including the ZEROES, so a
vocabulary term nobody ever instantiated is visible rather than merely declared.

Standard library only: `scripts/` may not import `axeyum`.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
CORRESPONDENCES = ROOT / "artifacts" / "correspondences"
FACTS = ROOT / "artifacts" / "facts"
SCHEMA = ROOT / "artifacts" / "ontology" / "theorem-correspondence.schema.json"
KERNEL_PROJECTION = ROOT / "artifacts" / "autogenesis" / "kernel-dependency-projection-v1.json"

ID_RE = re.compile(r"^X:[a-z0-9]+(?:-[a-z0-9]+)*$")
FACT_ID_RE = re.compile(r"^F:[a-z0-9]+(?:-[a-z0-9]+)*$")
DATE_RE = re.compile(r"^[0-9]{4}-[0-9]{2}-[0-9]{2}$")

KINDS = ("carrier-transport", "independent-formalization", "specialization")
DERIVATION_STATUSES = ("asserted", "route-recorded", "mechanized-here")
EXTERNAL_STATUSES = ("classical", "folklore", "novel-here", "unclassified")
SETTLED = ("proved", "computed")

REQUIRED_KEYS = (
    "schema_version", "kind", "id", "title", "correspondence_kind", "endpoints",
    "claim", "transport", "derivation_status", "external_status", "via",
    "evidence", "provenance",
)
OPTIONAL_KEYS = ("notes",)

# Every spelling of a carrier that can appear in a formal statement, per
# `formal.fragment`. Erasing these is what makes `carrier-transport` checkable.
# Aliases are erased longest-first so `CReal` is never matched as `C` + `Real`,
# and so `AxNat` is erased before `Nat` can match its tail.
#
# `AxNat` IS THE KERNEL'S OWN SPELLING OF THE CONSTRUCTED NATURALS, and it
# belongs under `Nat` -- the `Ax` is *axeyum*, added by `lean_pp` so the
# rendered name does not shadow Lean's `Nat`. It is NOT an axiomatisation.
# `AxReal` is the opposite case and a genuinely different carrier: the
# axiomatised ordered field, 30 assumed laws, and it is a fragment of its
# own. Without `AxNat` here the word-boundary erasure could never fire on a
# statement written in kernel spelling (the `x` blocks `(?<![A-Za-z])Nat`),
# so every such transport failed closed and the gate silently steered
# authors toward prose-ℕ -- a checker shaping its own input.
CARRIERS: dict[str, tuple[str, ...]] = {
    "Nat": ("AxNat", "Nat", "ℕ"),
    "Int": ("Int", "ℤ"),
    "Rat": ("Rat", "ℚ"),
    "CReal": ("CReal", "ℝ"),
    "AxReal": ("AxReal",),
    "Complex": ("Complex", "ℂ"),
    "CPoint": ("CPoint",),
    "Bool": ("Bool",),
    "List": ("List",),
}
CARRIER_PLACEHOLDER = "⟨C⟩"

MIN_CLAIM = 120
MIN_TRANSPORT = 60


class CorrespondenceError(Exception):
    """A structural failure that makes every rule below vacuous."""


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise CorrespondenceError(f"{path}: cannot read JSON: {exc}") from exc


def load_facts() -> dict[str, dict[str, Any]]:
    """The ledger, keyed by fact id. An empty ledger is an error, not a pass."""
    facts: dict[str, dict[str, Any]] = {}
    for path in sorted(FACTS.glob("*.json")):
        document = load_json(path)
        if isinstance(document, dict) and isinstance(document.get("id"), str):
            facts[document["id"]] = document
    if not facts:
        raise CorrespondenceError(
            f"{FACTS} held no facts; every endpoint, status and dependency check "
            "below would pass vacuously"
        )
    return facts


def load_kernel_declarations() -> set[str]:
    """Declaration ids the kernel projection has actually observed.

    Missing or empty is NOT fatal here: a `via` step may legitimately reference
    only facts, and the projection is a generated snapshot that a lane refreshes
    with a cargo run. What is fatal is a `kernel:` reference that the snapshot
    does not contain -- see `resolve_reference`.
    """
    if not KERNEL_PROJECTION.is_file():
        return set()
    document = load_json(KERNEL_PROJECTION)
    rows = (document or {}).get("declarations", [])
    return {row["id"] for row in rows if isinstance(row, dict) and isinstance(row.get("id"), str)}


def dependency_closure(facts: dict[str, dict[str, Any]]) -> dict[str, set[str]]:
    """Transitive `depends_on` reachability, both directions collapsed later.

    Direct edges are not enough. If A depends on B and B on C, then A's proof
    reaches C, and a "correspondence" between A and C is still a statement about
    the proof order rather than about the mathematics.
    """
    direct = {
        fact_id: {d for d in (document.get("depends_on") or []) if isinstance(d, str)}
        for fact_id, document in facts.items()
    }
    closure: dict[str, set[str]] = {}
    for fact_id in direct:
        seen: set[str] = set()
        stack = list(direct[fact_id])
        while stack:
            nxt = stack.pop()
            if nxt in seen:
                continue
            seen.add(nxt)
            stack.extend(direct.get(nxt, ()))
        closure[fact_id] = seen
    return closure


def erase_carrier(statement: str, fragment: str) -> str:
    """Replace every spelling of `fragment`'s carrier with a placeholder.

    Word-boundaried on ASCII letters so `Int` does not match inside `Integer`;
    the unicode aliases are single glyphs and need no boundary.
    """
    out = statement
    for alias in sorted(CARRIERS[fragment], key=len, reverse=True):
        if alias.isascii():
            out = re.sub(rf"(?<![A-Za-z]){re.escape(alias)}(?![A-Za-z])", CARRIER_PLACEHOLDER, out)
        else:
            out = out.replace(alias, CARRIER_PLACEHOLDER)
    return out


def resolve_reference(ref: str, facts: dict[str, dict[str, Any]], declarations: set[str]) -> str | None:
    """Return a violation message when a `via` reference names nothing real."""
    if ref.startswith("kernel:"):
        name = ref[len("kernel:"):]
        if name in declarations:
            return None
        return (
            f"via ref {ref!r} names no declaration the kernel projection has observed. "
            "The projection is a snapshot; if the theorem is newer than it, refresh it "
            "with `python3 scripts/gen-autogenesis-kernel-dependency-projection.py` "
            "rather than asserting the name here"
        )
    if FACT_ID_RE.fullmatch(ref):
        if ref in facts:
            return None
        return f"via ref {ref!r} is not a fact in the ledger"
    return f"via ref {ref!r} is neither an F: fact id nor a kernel:<Name> reference"


def check_structure(document: Any, name: str, problems: list[str]) -> bool:
    """Shape and enum membership. Returns False when the semantic rules cannot run."""
    if not isinstance(document, dict):
        problems.append(f"{name}: root is not an object")
        return False
    unknown = set(document) - set(REQUIRED_KEYS) - set(OPTIONAL_KEYS)
    if unknown:
        problems.append(f"{name}: unknown key(s) {sorted(unknown)}")
    missing = [key for key in REQUIRED_KEYS if key not in document]
    if missing:
        problems.append(f"{name}: missing required key(s) {missing}")
        return False
    if document["schema_version"] != 1:
        problems.append(f"{name}: schema_version must be 1")
    if document["kind"] != "axeyum-theorem-correspondence":
        problems.append(f"{name}: kind must be axeyum-theorem-correspondence")
    if not isinstance(document["id"], str) or not ID_RE.fullmatch(document["id"]):
        problems.append(f"{name}: id must match {ID_RE.pattern}")
        return False
    if document["correspondence_kind"] not in KINDS:
        problems.append(f"{name}: correspondence_kind must be one of {list(KINDS)}")
        return False
    if document["derivation_status"] not in DERIVATION_STATUSES:
        problems.append(f"{name}: derivation_status must be one of {list(DERIVATION_STATUSES)}")
        return False
    if document["external_status"] not in EXTERNAL_STATUSES:
        problems.append(f"{name}: external_status must be one of {list(EXTERNAL_STATUSES)}")
        return False
    endpoints = document["endpoints"]
    if not isinstance(endpoints, list) or len(endpoints) != 2:
        problems.append(f"{name}: endpoints must be exactly two fact ids")
        return False
    if not all(isinstance(e, str) and FACT_ID_RE.fullmatch(e) for e in endpoints):
        problems.append(f"{name}: every endpoint must match {FACT_ID_RE.pattern}")
        return False
    if not isinstance(document["via"], list) or not isinstance(document["evidence"], list):
        problems.append(f"{name}: via and evidence must be arrays")
        return False
    provenance = document["provenance"]
    if not isinstance(provenance, dict) or not DATE_RE.fullmatch(str(provenance.get("date", ""))):
        problems.append(f"{name}: provenance.date must be YYYY-MM-DD")
    if not provenance.get("sources"):
        problems.append(f"{name}: provenance.sources must name at least one file")
    return True


def check_prose(document: dict[str, Any], name: str, problems: list[str]) -> None:
    """Floors set from measured practice, not from a round number.

    math-education's SHACL floor of 10 characters never fired against a corpus
    whose shortest real reason was 75. A floor below the shortest honest value
    is decoration.
    """
    if len(document["claim"].strip()) < MIN_CLAIM:
        problems.append(f"{name}: claim is shorter than {MIN_CLAIM} characters")
    if len(document["transport"].strip()) < MIN_TRANSPORT:
        problems.append(
            f"{name}: transport is shorter than {MIN_TRANSPORT} characters. Name the map "
            "that identifies the two statements, not the fact that one exists"
        )
    if document["claim"].strip() == document["transport"].strip():
        problems.append(
            f"{name}: claim and transport are the same text. WHAT is shared and HOW the "
            "two are identified are different questions"
        )


def check_endpoints(
    document: dict[str, Any],
    name: str,
    facts: dict[str, dict[str, Any]],
    closure: dict[str, set[str]],
    problems: list[str],
) -> tuple[dict[str, Any], dict[str, Any]] | None:
    left_id, right_id = document["endpoints"]
    if left_id == right_id:
        problems.append(f"{name}: the two endpoints are the same fact")
        return None
    missing = [e for e in (left_id, right_id) if e not in facts]
    if missing:
        problems.append(f"{name}: endpoint(s) {missing} are not facts in the ledger")
        return None
    left, right = facts[left_id], facts[right_id]
    for fact in (left, right):
        if fact.get("epistemic_status") not in SETTLED:
            problems.append(
                f"{name}: endpoint {fact['id']} is {fact.get('epistemic_status')!r}; two results "
                f"cannot be shown to be the same idea until both are settled ({list(SETTLED)})"
            )
    if right_id in closure.get(left_id, ()) or left_id in closure.get(right_id, ()):
        problems.append(
            f"{name}: the fact ledger already connects {left_id} and {right_id} through "
            "`depends_on`. That edge says one proof used the other, which is a statement "
            "about proof order; a correspondence is for the case where no such edge exists "
            "and never will. Use `depends_on`"
        )
    if left.get("formal", {}).get("statement") == right.get("formal", {}).get("statement"):
        problems.append(
            f"{name}: the two endpoints have identical formal statements. That is a duplicate "
            "fact, not a correspondence"
        )
    return left, right


def check_kind_rules(
    document: dict[str, Any],
    name: str,
    left: dict[str, Any],
    right: dict[str, Any],
    problems: list[str],
) -> None:
    kind = document["correspondence_kind"]
    left_fragment = left.get("formal", {}).get("fragment")
    right_fragment = right.get("formal", {}).get("fragment")
    if kind == "carrier-transport":
        if left_fragment == right_fragment:
            problems.append(
                f"{name}: carrier-transport endpoints are both in fragment {left_fragment!r}. "
                "One carrier is not a transport"
            )
            return
        unknown = [f for f in (left_fragment, right_fragment) if f not in CARRIERS]
        if unknown:
            problems.append(
                f"{name}: fragment(s) {unknown} have no carrier spelling in CARRIERS, so the "
                "structural check cannot run. Add them rather than letting the claim through "
                "unmeasured"
            )
            return
        left_erased = erase_carrier(left["formal"]["statement"], str(left_fragment))
        right_erased = erase_carrier(right["formal"]["statement"], str(right_fragment))
        if left_erased != right_erased:
            problems.append(
                f"{name}: erasing the carrier leaves two different statements, so these are not "
                f"one law over two carriers.\n    {left['id']} -> {left_erased!r}\n"
                f"    {right['id']} -> {right_erased!r}"
            )
    elif kind == "independent-formalization":
        if left.get("proof_route") == right.get("proof_route"):
            problems.append(
                f"{name}: independent-formalization endpoints are both on proof route "
                f"{left.get('proof_route')!r}. The content of this kind is that two DIFFERENT "
                "routes reached the same theorem"
            )
    elif kind == "specialization":
        if document["derivation_status"] == "asserted":
            problems.append(
                f"{name}: a specialization must record the instantiation route in `via`. Saying one "
                "theorem is a case of another, with no step named, is the claim without the argument"
            )
        elif not any(
            isinstance(step, dict) and isinstance(step.get("ref"), str) and step["ref"].strip()
            for step in document["via"]
        ):
            # A `via` of prose steps with every `ref` null passes the rule above
            # -- it is non-empty -- and names no theorem at all. That is the
            # same claim-without-the-argument the rule exists to refuse, one
            # level down, and it is what an author writes when they know the
            # specialisation is true and have not looked up the general form.
            # `route-recorded` permits null refs generally, and should: a step
            # may legitimately be an algebraic rearrangement with nothing to
            # cite. But a SPECIALISATION is by definition an instantiation OF
            # something, so at least one step has to say of what.
            problems.append(
                f"{name}: a specialization records {len(document['via'])} via step(s) and not one "
                "of them names a `ref`. The general theorem being instantiated must be named -- a "
                "route of prose with every reference null is the claim without the argument again"
            )


def check_backing(
    document: dict[str, Any],
    name: str,
    facts: dict[str, dict[str, Any]],
    declarations: set[str],
    problems: list[str],
) -> None:
    """The two status axes, each required to be backed rather than toned."""
    derivation = document["derivation_status"]
    via = document["via"]
    evidence = document["evidence"]

    if (derivation == "asserted") != (not via):
        problems.append(
            f"{name}: derivation_status is {derivation!r} with {len(via)} via step(s). "
            "`asserted` means exactly that no route is written down, so it holds precisely "
            "when `via` is empty"
        )
    for index, step in enumerate(via):
        if not isinstance(step, dict) or "ref" not in step or "step" not in step:
            problems.append(f"{name}: via[{index}] must be an object with `step` and `ref`")
            continue
        ref = step["ref"]
        if ref is None:
            continue
        if not isinstance(ref, str):
            problems.append(f"{name}: via[{index}].ref must be a string or null")
            continue
        message = resolve_reference(ref, facts, declarations)
        if message is not None:
            problems.append(f"{name}: {message}")

    if derivation == "mechanized-here":
        if any(isinstance(s, dict) and s.get("ref") is None for s in via):
            problems.append(
                f"{name}: derivation_status is `mechanized-here` while a via step has a null "
                "ref. A route with a missing step is not mechanized; it is `route-recorded`"
            )
        if not evidence:
            problems.append(
                f"{name}: derivation_status is `mechanized-here` with no evidence. The claim "
                "that a machine established this must name the command that re-derives it"
            )
        for index, row in enumerate(evidence):
            if not isinstance(row, dict) or not str(row.get("checker_command", "")).strip():
                problems.append(f"{name}: evidence[{index}] has no checker_command")
    elif evidence:
        problems.append(
            f"{name}: derivation_status is {derivation!r} but evidence is non-empty. Evidence is "
            "what makes a correspondence `mechanized-here`; carrying it under a weaker status "
            "is the contradiction the fact ledger already refuses for an `open` fact"
        )

    if document["external_status"] == "novel-here" and derivation != "mechanized-here":
        problems.append(
            f"{name}: external_status is `novel-here` while derivation_status is {derivation!r}. "
            "Claiming the connection is new to mathematics, with nothing here deriving it, is "
            "the one combination that is pure tone"
        )


def validate(directory: Path = CORRESPONDENCES) -> tuple[list[str], dict[str, Any]]:
    facts = load_facts()
    declarations = load_kernel_declarations()
    closure = dependency_closure(facts)

    paths = sorted(directory.glob("*.json"))
    if not paths:
        raise CorrespondenceError(
            f"{directory} holds no correspondence; every rule in this gate would pass "
            "vacuously, and a data model with no instance is a wish"
        )

    problems: list[str] = []
    seen_ids: dict[str, str] = {}
    seen_pairs: dict[frozenset[str], str] = {}
    kinds = dict.fromkeys(KINDS, 0)
    derivations = dict.fromkeys(DERIVATION_STATUSES, 0)
    externals = dict.fromkeys(EXTERNAL_STATUSES, 0)

    for path in paths:
        name = path.name
        document = load_json(path)
        if not check_structure(document, name, problems):
            continue
        identifier = document["id"]
        expected = identifier.replace("X:", "X-", 1) + ".json"
        if name != expected:
            problems.append(f"{name}: id {identifier!r} implies filename {expected!r}")
        if identifier in seen_ids:
            problems.append(f"{name}: duplicate id {identifier!r}, already used by {seen_ids[identifier]}")
        seen_ids[identifier] = name

        kinds[document["correspondence_kind"]] += 1
        derivations[document["derivation_status"]] += 1
        externals[document["external_status"]] += 1

        check_prose(document, name, problems)
        check_backing(document, name, facts, declarations, problems)
        pair = frozenset(document["endpoints"])
        if len(pair) == 2 and pair in seen_pairs:
            problems.append(
                f"{name}: a correspondence for this endpoint pair already exists in "
                f"{seen_pairs[pair]}; one adjudication per pair"
            )
        seen_pairs[pair] = name
        resolved = check_endpoints(document, name, facts, closure, problems)
        if resolved is None:
            continue
        check_kind_rules(document, name, resolved[0], resolved[1], problems)

    summary = {
        "correspondences": len(paths),
        "facts": len(facts),
        "declarations": len(declarations),
        "kinds": kinds,
        "derivations": derivations,
        "externals": externals,
    }
    return problems, summary


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "directory", nargs="?", type=Path, default=CORRESPONDENCES,
        help="the correspondence directory to validate",
    )
    args = parser.parse_args(argv)
    try:
        problems, summary = validate(args.directory)
    except CorrespondenceError as error:
        print(f"CORRESPONDENCES_ERROR|{error}", file=sys.stderr)
        return 1

    kinds = ",".join(f"{k}:{v}" for k, v in summary["kinds"].items())
    derivations = ",".join(f"{k}:{v}" for k, v in summary["derivations"].items())
    externals = ",".join(f"{k}:{v}" for k, v in summary["externals"].items())
    print(
        f"CORRESPONDENCES|checked={summary['correspondences']}|facts={summary['facts']}"
        f"|kernel_declarations={summary['declarations']}|kinds={kinds}"
        f"|derivation={derivations}|external={externals}"
        f"|violations={len(problems)}"
    )
    if problems:
        print(f"FAIL: {len(problems)} violation(s)", file=sys.stderr)
        for problem in problems:
            print(f"  {problem}", file=sys.stderr)
        return 1
    print(
        "OK: every correspondence resolves, is settled on both ends, is NOT a `depends_on` "
        "edge in disguise, and carries the backing its two status axes claim"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
