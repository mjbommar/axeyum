#!/usr/bin/env python3
"""Validate the claim ledger under artifacts/claims/.

Structural: every claim.json validates against claim.schema.json (a local,
dependency-free structural checker — same stance as
validate-smt-fragment-atlas.py: no jsonschema dependency).

Referential:
  * id equals directory name
  * evidence artifact paths exist and their sha256 matches when declared
  * axeyum_refs.fragments subset of artifacts/ontology/smt-fragments.json ids
  * axeyum_refs.curriculum_nodes subset of docs/curriculum/curriculum.toml ids
  * epistemic discipline:
      - computed  => at least one evidence row with check_status == checked
      - conjectured/open => frontier present; no 'checked' row may claim to
        settle the full statement (supports must state a bound/partial)
      - bound-citation rows must be check_status == not-checked
  * concept_refs marked resolved require provenance.graph_pin, and when the
    math-education checkout is available at ../math-education, the target id
    must exist there (pending refs are fine and are reported, not failed —
    the resolution policy is: pending is honest, false-resolved is a lie).

Exit nonzero on any error. --quiet suppresses the per-claim OK lines.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIMS = ROOT / "artifacts" / "claims"
SCHEMA = ROOT / "artifacts" / "ontology" / "claim.schema.json"
FRAGMENTS = ROOT / "artifacts" / "ontology" / "smt-fragments.json"
CURRICULUM = ROOT / "docs" / "curriculum" / "curriculum.toml"
MATH_ED = ROOT.parent / "math-education"

EPISTEMIC = {"axiom", "proved", "computed", "empirical", "conjectured", "open"}
LANGUAGES = {"cnf-family", "smtlib2", "axeyum-term", "prose-only"}
RELATIONS = {"instance-of", "exercises", "refutes", "frontier-of", "uses-technique"}
EVIDENCE_KINDS = {"witness-replay", "unsat-certificate", "cube-cover",
                  "exhaustive-enumeration", "published-value-replication",
                  "bound-citation"}
CHECK_STATUS = {"checked", "replay-only", "not-checked"}
ID_RE = re.compile(r"^[a-z0-9][a-z0-9-]*$")
SHA_RE = re.compile(r"^[0-9a-f]{64}$")
PIN_RE = re.compile(r"^[0-9a-f]{40}$")
DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")
GRAPH_REF_RE = re.compile(r"^(C|M|TQ|TH|TM):[a-z0-9][a-z0-9./-]*(@[a-z]+)?$")

CLAIM_REQUIRED = {"schema_version", "id", "title", "statement", "epistemic_status",
                  "formal", "concept_refs", "axeyum_refs", "provenance", "evidence"}
CLAIM_OPTIONAL = {"frontier", "supersedes", "notes"}
EVIDENCE_REQUIRED = {"id", "kind", "supports", "check_status", "checker_command"}
EVIDENCE_OPTIONAL = {"artifact", "artifact_sha256", "artifact_format", "notes",
                     "parameters", "regeneration"}
TOOLCHAIN_REQUIRED = {"axeyum_commit", "rustc_version"}
TOOLCHAIN_OPTIONAL = {"target", "dirty"}

# ------------------------------------------------- artifact format contract
#
# Findings register B8: 34 ledger claims shipped UNSAT certificates in BINARY
# DRAT -- kissat's default output -- while axeyum's own `parse_drat` reads TEXT
# DRAT. Every declared hash matched, every path existed, and this validator was
# green; the certificates were nevertheless UNREADABLE BY THE SYSTEM THAT SHIPS
# THEM. A stored proof is evidence only if the checker in our trust base can
# parse it, so the dialect is part of the validated contract, and it is read
# out of the artifact's own BYTES -- never taken from the record's say-so.
#
# The vocabulary deliberately names only formats this ledger actually stores.
# An unrecognized artifact fails closed as `unknown` rather than being waved
# through: a format gate that cannot classify a file has not checked it.
ARTIFACT_FORMATS = {
    "drat-text",          # textual DRAT, the dialect axeyum's parse_drat reads
    "drat-text-gzip",     # ... under a gzip envelope (self-identifying, undone
                          #     by the checker harness before parsing)
    "drat-binary",        # binary DRAT (kissat's default) -- NOT readable here
    "drat-binary-gzip",
    "dimacs-cnf",         # the deciding instance itself, not a proof
    "colouring-text",     # a witness colouring, one colour per integer
    "tsv-ledger",         # a per-cube certification ledger
}

# The formats axeyum's own in-tree checker can consume (`parse_drat` ->
# `check_drat_backward`, ADR-0381). A `checked` unsat-certificate row MUST
# store one of these: anything else is a certificate no shipped checker can
# read, which is exactly the B8 defect.
CHECKER_READABLE_FORMATS = {"drat-text", "drat-text-gzip"}

GZIP_MAGIC = b"\x1f\x8b"
# Refuse to sniff an unreasonably large payload rather than exhausting RAM in
# a structural gate; such an artifact must carry a `regeneration` recipe.
MAX_SNIFF_BYTES = 1 << 30
# Bytes that may appear in any text artifact. A DRAT proof body needs far
# fewer, but comment lines carry free text; what matters for the binary/text
# discrimination is that NUL and the 0x80..0xff range never appear in a text
# file and appear immediately in a binary DRAT one.
TEXT_SAFE_BYTES = bytes(range(0x20, 0x7F)) + b"\t\n\r"
DRAT_LINE_RE = re.compile(r"^(d\s+)?(-?\d+\s+)*0$")


def fail(errors: list[str], msg: str) -> None:
    errors.append(msg)


def read_payload(path: Path) -> tuple[bytes, str, str | None]:
    """Return (payload, envelope, error).

    `envelope` is "-gzip" when the file is gzip-wrapped and "" otherwise; the
    payload is what a checker would actually parse. Decompression is capped:
    an artifact too large to sniff is reported, never silently skipped.
    """
    raw = path.read_bytes()
    if raw[:2] != GZIP_MAGIC:
        if len(raw) > MAX_SNIFF_BYTES:
            return b"", "", f"artifact is {len(raw)} bytes, past the sniff cap"
        return raw, "", None
    import zlib
    dec = zlib.decompressobj(zlib.MAX_WBITS | 16)
    out = dec.decompress(raw, MAX_SNIFF_BYTES + 1)
    if len(out) > MAX_SNIFF_BYTES:
        return b"", "-gzip", (f"gzip payload exceeds the {MAX_SNIFF_BYTES}-byte "
                              f"sniff cap")
    return out, "-gzip", None


def classify_payload(payload: bytes) -> tuple[str, bool]:
    """Classify decompressed artifact bytes; return (format, ends_in_empty_clause).

    Deliberately structural: what the bytes ARE, independent of the file's
    name, the claim's declaration, or the tool that wrote it. `parse_drat`'s
    grammar is re-implemented here rather than imported so this gate is a
    second reading of the dialect, not an echo of the first.
    """
    if not payload:
        return "unknown", False
    if payload.translate(None, TEXT_SAFE_BYTES):
        # Not a text file. Binary DRAT frames every step as 'a'/'d' + varbyte
        # literals + a NUL terminator, so it announces itself in byte 0.
        if payload[:1] in (b"a", b"d") and b"\x00" in payload:
            return "drat-binary", False
        return "unknown", False

    text = payload.decode("ascii")
    lines = [ln.strip() for ln in text.splitlines()]
    body = [ln for ln in lines if ln and not ln.startswith("c")]
    if not body:
        return "unknown", False
    if body[0].startswith("p cnf"):
        return "dimacs-cnf", False
    ends_empty = body[-1] == "0"
    if "\t" in text:
        return "tsv-ledger", False
    sample = body[:500] + body[-2:]
    if all(DRAT_LINE_RE.match(ln) for ln in sample):
        return "drat-text", ends_empty
    tokens = text.split()
    if tokens and all(t.isdigit() and t != "0" for t in tokens):
        return "colouring-text", False
    return "unknown", False


def detect_artifact_format(path: Path) -> tuple[str, bool, str | None]:
    """(detected format, ends_in_empty_clause, error) for one artifact file."""
    payload, envelope, err = read_payload(path)
    if err is not None:
        return "unknown", False, err
    fmt, ends_empty = classify_payload(payload)
    if fmt == "unknown":
        return "unknown", False, None
    return fmt + envelope if envelope else fmt, ends_empty, None


def check_artifact_format(errors: list[str], path: Path, ev: dict,
                          artifact: Path | None) -> None:
    """Enforce the format contract for one evidence row (findings register B8).

    Three rules, in order of what they catch:
      1. a declared format must be one we know and must MATCH the bytes;
      2. an unsat-certificate row that stores an artifact must declare one --
         silence is how a binary proof passed for a text one;
      3. a `checked` unsat-certificate must store a format axeyum's own
         checker can read, and its proof must end in the empty clause. A
         certificate our checker cannot parse is not checked evidence, whoever
         else verified it.
    """
    eid = ev.get("id", "")
    kind = ev.get("kind")
    declared = ev.get("artifact_format")
    if declared is not None and artifact is None:
        fail(errors, f"{path}: evidence '{eid}' declares artifact_format but "
                     f"names no artifact")
        return
    if declared is not None and declared not in ARTIFACT_FORMATS:
        fail(errors, f"{path}: evidence '{eid}' has unknown artifact_format "
                     f"'{declared}'")
        return
    if artifact is None or not artifact.exists():
        return
    if kind == "unsat-certificate" and declared is None:
        fail(errors, f"{path}: evidence '{eid}' stores a certificate but "
                     f"declares no artifact_format; the dialect of a stored "
                     f"proof is part of the contract (findings register B8)")
        return
    if declared is None:
        return
    detected, ends_empty, err = detect_artifact_format(artifact)
    if err is not None:
        fail(errors, f"{path}: evidence '{eid}' artifact cannot be sniffed: {err}")
        return
    if detected != declared:
        fail(errors, f"{path}: evidence '{eid}' declares artifact_format "
                     f"'{declared}' but the stored bytes are '{detected}'")
        return
    if kind == "unsat-certificate" and ev.get("check_status") == "checked":
        if declared not in CHECKER_READABLE_FORMATS:
            fail(errors, f"{path}: evidence '{eid}' is a 'checked' certificate "
                         f"stored as '{declared}', which axeyum's own checker "
                         f"cannot read (parse_drat reads text DRAT); a proof "
                         f"the shipped checker cannot parse is not checked "
                         f"evidence (findings register B8)")
        elif not ends_empty:
            fail(errors, f"{path}: evidence '{eid}' is a 'checked' certificate "
                         f"whose proof does not end in the empty clause, so it "
                         f"does not derive a contradiction")


def load_fragment_ids() -> set[str]:
    data = json.loads(FRAGMENTS.read_text())
    return {row["id"] for row in data["rows"]}


def load_curriculum_ids() -> set[str]:
    ids = set()
    for line in CURRICULUM.read_text().splitlines():
        m = re.match(r'^id = "([a-z0-9-]+)"$', line.strip())
        if m:
            ids.add(m.group(1))
    return ids


def load_math_ed_ids() -> set[str] | None:
    """Best-effort id census of the sibling math-education graph."""
    if not (MATH_ED / "graph").is_dir():
        return None
    ids: set[str] = set()
    id_re = re.compile(r"^id:\s*'?([A-Z]{1,4}:[a-z0-9./-]+)'?\s*$")
    for sub in ("concepts", "misconceptions", "techniques", "threads", "themes"):
        d = MATH_ED / "graph" / sub
        if not d.is_dir():
            continue
        for f in d.glob("*.md"):
            for line in f.read_text(encoding="utf-8").splitlines()[:6]:
                m = id_re.match(line.strip())
                if m:
                    ids.add(m.group(1))
                    break
    return ids


def encounter_base(ref: str) -> str:
    return ref.split("@", 1)[0]


def validate_claim(path: Path, fragment_ids: set[str], curriculum_ids: set[str],
                   math_ed_ids: set[str] | None, quiet: bool) -> list[str]:
    errors: list[str] = []
    pendings: list[str] = []
    try:
        c = json.loads(path.read_text())
    except json.JSONDecodeError as e:
        return [f"{path}: unparseable JSON: {e}"]

    keys = set(c)
    for k in CLAIM_REQUIRED - keys:
        fail(errors, f"{path}: missing required field '{k}'")
    for k in keys - CLAIM_REQUIRED - CLAIM_OPTIONAL:
        fail(errors, f"{path}: unknown field '{k}'")
    if errors:
        return errors

    if not isinstance(c["schema_version"], int) or c["schema_version"] < 1:
        fail(errors, f"{path}: bad schema_version")
    if not ID_RE.match(c["id"]):
        fail(errors, f"{path}: malformed id '{c['id']}'")
    if c["id"] != path.parent.name:
        fail(errors, f"{path}: id '{c['id']}' != directory '{path.parent.name}'")
    if len(c.get("statement", "")) < 10:
        fail(errors, f"{path}: statement too short to be a claim")
    if c["epistemic_status"] not in EPISTEMIC:
        fail(errors, f"{path}: bad epistemic_status '{c['epistemic_status']}'")

    fm = c["formal"]
    for k in {"language", "family", "parameters"} - set(fm):
        fail(errors, f"{path}: formal missing '{k}'")
    if fm.get("language") not in LANGUAGES:
        fail(errors, f"{path}: bad formal.language")
    gen = fm.get("generator")
    if gen and not (ROOT / gen).exists():
        fail(errors, f"{path}: formal.generator '{gen}' does not exist")
    sem = fm.get("semantics_note")
    if sem and not (ROOT / sem).exists():
        fail(errors, f"{path}: formal.semantics_note '{sem}' does not exist")

    prov = c["provenance"]
    for k in {"conjectured_by", "searched_by", "checked_by", "date"} - set(prov):
        fail(errors, f"{path}: provenance missing '{k}'")
    if "date" in prov and not DATE_RE.match(prov["date"]):
        fail(errors, f"{path}: bad provenance.date")
    pin = prov.get("graph_pin")
    if pin is not None and not PIN_RE.match(pin):
        fail(errors, f"{path}: graph_pin is not a 40-hex commit")

    tc = prov.get("toolchain")
    if tc is not None:
        for k in TOOLCHAIN_REQUIRED - set(tc):
            fail(errors, f"{path}: toolchain missing '{k}'")
        for k in set(tc) - TOOLCHAIN_REQUIRED - TOOLCHAIN_OPTIONAL:
            fail(errors, f"{path}: toolchain unknown field '{k}'")
        commit = tc.get("axeyum_commit")
        if commit is not None and not PIN_RE.match(commit):
            fail(errors, f"{path}: axeyum_commit is not a 40-hex commit")

    # concept refs and the resolution policy
    for ref in c["concept_refs"]:
        unknown = set(ref) - {"graph", "ref", "relation", "resolved", "note"}
        if unknown:
            fail(errors, f"{path}: concept_ref unknown keys {sorted(unknown)}")
        if ref.get("graph") != "math-education":
            fail(errors, f"{path}: concept_ref.graph must be 'math-education'")
        r = ref.get("ref", "")
        if not GRAPH_REF_RE.match(r):
            fail(errors, f"{path}: malformed graph ref '{r}'")
        if ref.get("relation") not in RELATIONS:
            fail(errors, f"{path}: bad concept_ref.relation")
        if ref.get("resolved"):
            if pin is None:
                fail(errors, f"{path}: ref '{r}' resolved but no graph_pin recorded")
            if math_ed_ids is not None and encounter_base(r) not in math_ed_ids:
                fail(errors, f"{path}: ref '{r}' marked resolved but absent "
                             f"from ../math-education graph")
        else:
            pendings.append(r)

    ax = c["axeyum_refs"]
    for frag in ax.get("fragments", []):
        if frag not in fragment_ids:
            fail(errors, f"{path}: unknown fragment '{frag}'")
    for node in ax.get("curriculum_nodes", []):
        if node not in curriculum_ids:
            fail(errors, f"{path}: unknown curriculum node '{node}'")

    # evidence rows and epistemic discipline
    seen_ids: set[str] = set()
    has_checked = False
    for ev in c["evidence"]:
        for k in EVIDENCE_REQUIRED - set(ev):
            fail(errors, f"{path}: evidence missing '{k}'")
        for k in set(ev) - EVIDENCE_REQUIRED - EVIDENCE_OPTIONAL:
            fail(errors, f"{path}: evidence unknown field '{k}'")
        eid = ev.get("id", "")
        if eid in seen_ids:
            fail(errors, f"{path}: duplicate evidence id '{eid}'")
        seen_ids.add(eid)
        if ev.get("kind") not in EVIDENCE_KINDS:
            fail(errors, f"{path}: bad evidence.kind")
        if ev.get("check_status") not in CHECK_STATUS:
            fail(errors, f"{path}: bad evidence.check_status")
        if ev.get("kind") == "bound-citation" and ev.get("check_status") != "not-checked":
            fail(errors, f"{path}: bound-citation '{eid}' must be not-checked "
                         f"(a citation is not a machine check)")
        if ev.get("check_status") == "checked":
            has_checked = True
            if ev.get("checker_command", "none") == "none":
                fail(errors, f"{path}: checked evidence '{eid}' has no checker_command")
        regen = ev.get("regeneration")
        if regen is not None:
            for k in {"command", "produces_sha256"} - set(regen):
                fail(errors, f"{path}: regeneration on '{eid}' missing '{k}'")
            for k in set(regen) - {"command", "produces_sha256", "bytes",
                                   "approx_wall_seconds", "note"}:
                fail(errors, f"{path}: regeneration on '{eid}' unknown field '{k}'")
            sha = regen.get("produces_sha256")
            if sha is not None and not SHA_RE.match(sha):
                fail(errors, f"{path}: regeneration on '{eid}' has a malformed "
                             f"produces_sha256")
            if prov.get("toolchain") is None:
                fail(errors, f"{path}: evidence '{eid}' is regenerable but no "
                             f"provenance.toolchain is pinned; a recipe without "
                             f"a pinned toolchain is not reproducible")

        art = ev.get("artifact")
        if art is None and regen is None and ev.get("check_status") == "checked":
            fail(errors, f"{path}: evidence '{eid}' is 'checked' but names "
                         f"neither an artifact nor a regeneration recipe")
        check_artifact_format(errors, path, ev, (ROOT / art) if art else None)
        if art is not None:
            p = ROOT / art
            if not p.exists():
                fail(errors, f"{path}: evidence artifact '{art}' does not exist")
            elif "artifact_sha256" in ev:
                if not SHA_RE.match(ev["artifact_sha256"]):
                    fail(errors, f"{path}: bad artifact_sha256 for '{eid}'")
                else:
                    actual = hashlib.sha256(p.read_bytes()).hexdigest()
                    if actual != ev["artifact_sha256"]:
                        fail(errors, f"{path}: sha256 mismatch for '{art}': "
                                     f"declared {ev['artifact_sha256'][:12]}…, "
                                     f"actual {actual[:12]}…")

    status = c["epistemic_status"]
    if status == "computed" and not has_checked:
        fail(errors, f"{path}: epistemic_status 'computed' requires at least one "
                     f"evidence row with check_status 'checked'")
    if status in {"conjectured", "open"}:
        if "frontier" not in c:
            fail(errors, f"{path}: '{status}' claim requires a frontier record")
        else:
            fr = c["frontier"]
            for k in {"known", "would_settle"} - set(fr):
                fail(errors, f"{path}: frontier missing '{k}'")
            for k in set(fr) - {"known", "would_settle", "attack_notes"}:
                fail(errors, f"{path}: frontier unknown field '{k}'")
    if status not in {"conjectured", "open"} and "frontier" in c:
        fail(errors, f"{path}: frontier is only for conjectured/open claims")

    if not errors and not quiet:
        pend = f" ({len(pendings)} pending refs)" if pendings else ""
        print(f"OK   {c['id']}: {status}, {len(c['evidence'])} evidence rows{pend}")
    return errors


def main() -> int:
    global CLAIMS
    quiet = "--quiet" in sys.argv
    args = sys.argv[1:]
    if "--root" in args:
        CLAIMS = Path(args[args.index("--root") + 1])
    if not CLAIMS.is_dir():
        print("no artifacts/claims/ directory; nothing to validate")
        return 0
    if not SCHEMA.exists():
        print("missing claim.schema.json", file=sys.stderr)
        return 1
    fragment_ids = load_fragment_ids()
    curriculum_ids = load_curriculum_ids()
    math_ed_ids = load_math_ed_ids()
    if math_ed_ids is None and not quiet:
        print("note: ../math-education not present; resolved refs checked "
              "structurally only")

    claim_files = sorted(CLAIMS.glob("**/claim.json"))
    if not claim_files:
        print("no claims found under artifacts/claims/**/claim.json",
              file=sys.stderr)
        return 1

    all_errors: list[str] = []
    ids: set[str] = set()
    for path in claim_files:
        errs = validate_claim(path, fragment_ids, curriculum_ids, math_ed_ids,
                              quiet)
        all_errors.extend(errs)
        try:
            cid = json.loads(path.read_text()).get("id")
            if cid in ids:
                all_errors.append(f"duplicate claim id '{cid}'")
            ids.add(cid)
        except json.JSONDecodeError:
            pass

    for e in all_errors:
        print(f"ERROR {e}", file=sys.stderr)
    print(f"\n{len(claim_files)} claims, {len(all_errors)} errors")
    return 1 if all_errors else 0


if __name__ == "__main__":
    sys.exit(main())
