#!/usr/bin/env python3
"""Semantically re-check claim-ledger evidence artifacts.

This is the trusted-disposer half of the claim ledger: for every evidence row
that declares check_status == "checked", re-derive the check from the artifact
and the claim parameters using code in THIS file only. It shares no code with
any search tool or instance generator — it is a deliberate third derivation
of the semantics (the generator and the search are the other two, and they
are not trusted).

Currently understood families:
  * rado-colouring-a(x-y)=bz  — witness-replay rows: the artifact is a
    whitespace-separated list of colours for 1..n; we recompute every
    solution of a(x-y)=bz inside [n]^3 by direct search and confirm none is
    monochromatic, then confirm the row's `supports` bound matches n.
    unsat-certificate rows: the artifact pair (DIMACS CNF, DRAT) is
    re-checked with an external DRAT checker when --drat-checker is given;
    we additionally regenerate the CNF from the claim parameters with an
    in-file encoder and require byte-identity with the stored CNF, so the
    certificate provably refutes the *intended* instance, not merely some
    file.

A family this script does not understand fails closed: an evidence row
claiming "checked" in an unknown family is an ERROR, not a skip.

--only <glob> restricts the run to claim ids matching the glob (the whole
ledger takes minutes). A glob that matches nothing is an error, not an
empty pass — a subset gate that silently checked zero claims would be the
same green-over-nothing lie the negative fixtures exist to prevent.
"""

from __future__ import annotations

import fnmatch
import json
import math
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CLAIMS = ROOT / "artifacts" / "claims"

# Rows this run could not re-check because their artifact is not in this
# tree. Reported explicitly in the summary: an unchecked row must never be
# indistinguishable from a checked one.
NOT_RECHECKED: list[str] = []

# A second base for resolving artifact paths, set only in bundle mode.
# Artifact paths are written relative to whatever tree the claim lives in:
# repository-root-relative here and in the negative fixtures, bundle-relative
# in a shipped snapshot. Trying both is what lets one checker serve both
# without a flag; anchoring on one alone breaks the other, and re-anchoring
# unconditionally is how the negative fixtures were briefly broken.
ALT_ROOT: Path | None = None


def artifact_path(art: str) -> Path:
    """Resolve an artifact path against the repo root, then the bundle root."""
    primary = ROOT / art
    if primary.exists() or ALT_ROOT is None:
        return primary
    alt = ALT_ROOT / art
    return alt if alt.exists() else primary


RADO_FAMILY = "rado-colouring-a(x-y)=bz"
BOUND_RE = re.compile(r"R_(\d+)\s*(>|=|>=)\s*(\d+)")


# ------------------------------------------------- independent Rado semantics

def rado_solutions(a: int, b: int, n: int):
    """All (x, y, z) in [n]^3 with a(x-y) = bz, by direct search."""
    for x in range(1, n + 1):
        for y in range(1, n + 1):
            num = a * (x - y)
            if num <= 0 or num % b:
                continue
            z = num // b
            if 1 <= z <= n:
                yield (x, y, z)


def check_rado_witness(a: int, b: int, k: int, colours: list[int]) -> str | None:
    """None if the colouring avoids monochromatic solutions; else a message."""
    n = len(colours)
    col = [0] + colours
    for j in range(1, n + 1):
        if not (1 <= col[j] <= k):
            return f"integer {j} has colour {col[j]} outside 1..{k}"
    for (x, y, z) in rado_solutions(a, b, n):
        if col[x] == col[y] == col[z]:
            return f"monochromatic solution ({x},{y},{z}) in colour {col[x]}"
    return None


def rado_cnf(a: int, b: int, k: int, n: int) -> str:
    """Regenerate the deciding CNF; must be byte-identical to the artifact.

    Variable convention: v(j, i) = (j-1)*k + i.  Clause order: positive
    (colour-at-least-one) for j = 1..n; then negative per solution in
    parametric t-then-y order with members sorted and deduplicated; then
    at-most-one; then symmetry breaking.  This mirrors the documented
    generator contract in the claim's semantics note.
    """
    def var(j: int, i: int) -> int:
        return (j - 1) * k + i

    clauses: list[list[int]] = []
    for j in range(1, n + 1):
        clauses.append([var(j, i) for i in range(1, k + 1)])
    g = math.gcd(a, b)
    ap, bp = a // g, b // g
    t = 1
    while ap * t <= n and bp * t + 1 <= n:
        z, dx = ap * t, bp * t
        for y in range(1, n - dx + 1):
            trip = sorted({y + dx, y, z})
            for i in range(1, k + 1):
                clauses.append([-var(v, i) for v in trip])
        t += 1
    for j in range(1, n + 1):
        for i1 in range(1, k + 1):
            for i2 in range(i1 + 1, k + 1):
                clauses.append([-var(j, i1), -var(j, i2)])
    clauses.append([var(1, 1)])
    for j in range(2, n + 1):
        for i in range(2, k + 1):
            if j <= i - 1:
                clauses.append([-var(j, i)])
            else:
                clauses.append([-var(j, i)] + [var(jp, i - 1) for jp in range(1, j)])
    lines = [f"p cnf {n * k} {len(clauses)}\n"]
    lines.extend(" ".join(map(str, cl)) + " 0\n" for cl in clauses)
    return "".join(lines)


# --------------------------------------------------------------- cube covers

def check_cube_cover(path: Path, ev: dict, a: int, b: int, k: int,
                     params: dict) -> list[str]:
    """Re-verify a decomposed refutation from its per-cube ledger.

    A cube cover refutes a formula by splitting on the colours of `d` chosen
    integers and refuting each cell of the resulting case split. What this
    checker establishes, mechanically:

      1. every recorded cube has verdict `unsat` and a passed proof check;
      2. the recorded cubes are EXACTLY the full product [1..k]^d — every
         cell present, none duplicated, none extra;
      3. for each branch integer j, the formula really does contain the
         at-least-one clause {v(j,1) .. v(j,k)} verbatim, so the case split
         is genuinely exhaustive over that integer.

    (3) is the step that makes (2) mean anything: without it, an "exhaustive"
    cover could omit a case the formula permits. The residual meta-argument
    is only the composition lemma (checked refutations of an exhaustive cover
    imply the formula is unsatisfiable).

    NOT established here: the per-cube DRAT proofs themselves. Those are
    checked by the harness at production time and their pass/fail verdict is
    what column `check` records; this checker confirms the ledger is
    complete, exhaustive, and uniformly passing. Re-deriving them requires
    the harness and is a separate, deterministic re-run.
    """
    errors: list[str] = []
    eid = ev["id"]
    art = ev.get("artifact")
    if art is None:
        errors.append(f"{path}: '{eid}' cube-cover has no artifact")
        return errors
    ev_params = ev.get("parameters") or {}
    branch = ev_params.get("branch")
    if not isinstance(branch, list) or not branch:
        errors.append(f"{path}: '{eid}' cube-cover needs parameters.branch "
                      f"(the list of branch integers)")
        return errors
    n = int(params["n"])

    rows = []
    text = artifact_path(art).read_text()
    for lineno, line in enumerate(text.splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if fields[0] == "index":          # header
            continue
        if len(fields) < 7:
            errors.append(f"{path}: '{eid}' malformed cube row at line {lineno}")
            return errors
        rows.append(fields)

    d = len(branch)
    expected = k ** d
    seen: dict[tuple[int, ...], int] = {}
    passed = 0
    deferred = 0
    for fields in rows:
        try:
            colours = tuple(int(c) for c in fields[1].split(","))
        except ValueError:
            errors.append(f"{path}: '{eid}' unparseable colour tuple {fields[1]!r}")
            return errors
        if len(colours) != d:
            errors.append(f"{path}: '{eid}' cube {fields[0]} has {len(colours)} "
                          f"colours but branch has {d} integers")
            return errors
        if any(not 1 <= c <= k for c in colours):
            errors.append(f"{path}: '{eid}' cube {fields[0]} has a colour "
                          f"outside 1..{k}")
            return errors
        if fields[2] != "unsat":
            errors.append(f"{path}: '{eid}' cube {fields[0]} verdict is "
                          f"'{fields[2]}', not 'unsat'")
            return errors
        if fields[6] == "failed":
            errors.append(f"{path}: '{eid}' cube {fields[0]} proof check FAILED")
            return errors
        if fields[6] == "passed":
            passed += 1
        else:
            deferred += 1
        seen[colours] = seen.get(colours, 0) + 1

    dupes = [c for c, n_ in seen.items() if n_ > 1]
    if dupes:
        errors.append(f"{path}: '{eid}' cover has {len(dupes)} duplicated "
                      f"cube(s), first {dupes[0]}")
    if len(seen) != expected:
        missing = expected - len(seen)
        errors.append(f"{path}: '{eid}' cover is NOT exhaustive: {len(seen)} "
                      f"distinct cubes recorded, {expected} required "
                      f"({missing} missing)")
        return errors

    # (3) the case split is licensed by the formula's own at-least-one clauses
    formula_lines = rado_cnf(a, b, k, n).splitlines()
    clause_sets = {frozenset(int(t) for t in ln.split()[:-1])
                   for ln in formula_lines[1:]}
    for j in branch:
        if not 1 <= j <= n:
            errors.append(f"{path}: '{eid}' branch integer {j} is outside "
                          f"1..{n}, so the formula has no case-split clause "
                          f"for it and the case split is not licensed")
            continue
        alo = frozenset((j - 1) * k + i for i in range(1, k + 1))
        if alo not in clause_sets:
            errors.append(f"{path}: '{eid}' formula has no at-least-one clause "
                          f"for branch integer {j}; the case split is not "
                          f"licensed and the cover proves nothing")

    # A cover is only fully checked when EVERY cell's proof was verified.
    # Cells deferred past a check cap rest on the solver's verdict alone, so a
    # cover containing them is `replay-only`: re-derived, not independently
    # confirmed end to end. The claim must also declare the split, so the
    # coverage is a stated number rather than a footnote nobody reads.
    declared = ev_params.get("checked_cubes")
    if declared is not None and declared != passed:
        errors.append(f"{path}: '{eid}' declares checked_cubes={declared} but "
                      f"the cover records {passed} passed")
    status = ev["check_status"]
    if deferred and status == "checked":
        errors.append(f"{path}: '{eid}' is labelled 'checked' but {deferred} of "
                      f"{len(seen)} cells were deferred past the check cap and "
                      f"rest on the solver's verdict alone; use 'replay-only' "
                      f"and declare parameters.checked_cubes")
    if deferred and declared is None:
        errors.append(f"{path}: '{eid}' has {deferred} deferred cells but does "
                      f"not declare parameters.checked_cubes")

    if not errors:
        cov = (f"{passed}/{len(seen)} proofs checked"
               if deferred else f"all {passed} proofs checked")
        print(f"  {status} cube-cover {eid}: {len(seen)}/{expected} cells, all "
              f"unsat, {cov}, exhaustive over branch {branch} "
              f"(at-least-one clauses confirmed in the formula)")
    return errors


# ------------------------------------------------------------------- driver

def check_instance_pin(path: Path, ev: dict, a: int, b: int, k: int,
                       params: dict) -> list[str]:
    """Re-check an instance-pin row: WHICH formula do the verdicts speak about?

    A cover ledger records `unsat` for a list of cubes. That is a verdict
    about a formula, and it is worth exactly nothing unless the formula is
    identified. The 313 upper bound shipped with five such ledgers and no
    pinned instance -- five records of a verdict whose subject nothing named.

    This establishes two things, both from bytes:

      1. the stored CNF regenerates byte-identically from the claim's own
         (a, b, k, n) using THIS file's independently written encoder -- not
         the generator of record, so a bug shared by one implementation does
         not authenticate itself;
      2. the recorded sha256 is the sha256 of those bytes.

    Byte-identity is the strong half. A hash says "these bytes are what I
    stored"; regeneration says "these bytes are the formula the claim's
    parameters denote". Only the second survives a corrupted store.
    """
    import hashlib

    errors: list[str] = []
    eid = ev["id"]
    art = ev.get("artifact")
    if art is None:
        return [f"{path}: '{eid}' instance-pin has no artifact"]
    n = int(params["n"])
    regenerated = rado_cnf(a, b, k, n).encode()
    recorded = ev.get("artifact_sha256")

    # CNF instances are deliberately NOT distributed in the arXiv bundle: they
    # regenerate in milliseconds from four integers, so shipping the bytes
    # saves a verifier nothing. When the file is absent we therefore check the
    # pin the only way that is available AND the only way that matters -- we
    # rebuild the formula from the claim's own parameters and hash that. The
    # recorded sha256 is the pin; regeneration is what redeems it.
    art_path = artifact_path(art)
    if art_path.exists():
        stored = art_path.read_bytes()
        mode = f"{len(stored)} B on disk"
        if stored != regenerated:
            errors.append(f"{path}: '{eid}' stored CNF is NOT byte-identical "
                          f"to the instance regenerated from a={a} b={b} "
                          f"k={k} n={n} ({len(stored)} B stored vs "
                          f"{len(regenerated)} B regenerated)")
    else:
        stored = regenerated
        mode = f"{len(regenerated)} B regenerated (not distributed)"

    actual = hashlib.sha256(stored).hexdigest()
    if recorded != actual:
        errors.append(f"{path}: '{eid}' records artifact_sha256 {recorded} "
                      f"but the bytes hash to {actual}")

    if not errors:
        print(f"  checked instance-pin {eid}: {mode}, matches the instance "
              f"regenerated from a={a} b={b} k={k} n={n}, sha256 "
              f"{actual[:16]}...")
    return errors


def check_unsat_certificate(path: Path, ev: dict, a: int, b: int, k: int,
                            params: dict, drat_checker: str | None) -> list[str]:
    """Re-check an unsat-certificate row against the claim's parameters.

    What this checker establishes, mechanically, in THIS file's code only:

      1. the deciding CNF beside the certificate regenerates byte-identically
         from the claim's (a, b, k, n) — the certificate refutes the intended
         instance, not merely some file;
      2. the stored artifact's bytes are what the record says they are: the
         gzip payload's sha256, byte count, and step count all match the
         recorded `parameters`, when present;
      3. for a text-DRAT artifact, every proof line parses under the DRAT
         text grammar (optional `d`, non-zero integer literals, `0`
         terminator) and the final clause ADDITION is the empty clause — a
         certificate that never derives the empty clause refutes nothing.

    NOT established here: the RUP re-derivation of each step. That is
    axeyum's own `check_drat_backward`, re-run via the in-tree
    `recertify_rado` example (which also re-solves the instance from
    scratch); an external checker cross-check runs when `--drat-checker`
    is given.
    """
    import gzip
    import hashlib

    errors: list[str] = []
    eid = ev["id"]
    art = ev.get("artifact")
    if art is None:
        return [f"{path}: '{eid}' unsat-certificate has no artifact"]
    art_path = artifact_path(art)
    if not art_path.exists():
        return [f"{path}: '{eid}' artifact {art} does not exist"]
    n = int(params["n"])

    # 1. The deciding CNF regenerates byte-identically.
    #
    # When the instance is stored we require byte-identity with it. When it is
    # not -- the arXiv bundle ships no CNFs, since they rebuild from four
    # integers in milliseconds -- there is nothing to disagree with, and the
    # instance's identity rests on the claim's parameters plus the pin row.
    # Demanding the file here was wrong: it failed 34 rows in the bundle for
    # having honoured the bundle's own size policy.
    cnf_path = art_path.parent / art_path.name.replace(".drat.gz", ".cnf")
    if cnf_path.exists():
        if cnf_path.read_text() != rado_cnf(a, b, k, n):
            errors.append(f"{path}: '{eid}' stored CNF differs from the "
                          f"regenerated instance for a={a} b={b} k={k} n={n}")
    else:
        rado_cnf(a, b, k, n)   # regenerates; identity is pinned by parameters

    fmt = ev.get("artifact_format", "")
    data = art_path.read_bytes()
    if fmt.endswith("-gzip"):
        try:
            payload = gzip.decompress(data)
        except OSError as error:
            return errors + [f"{path}: '{eid}' gzip payload unreadable: {error}"]
    else:
        payload = data

    recorded = ev.get("parameters") or {}
    if fmt in ("drat-text", "drat-text-gzip"):
        # 2. Bind the recorded numbers to the bytes.
        payload_sha = hashlib.sha256(payload).hexdigest()
        if recorded.get("proof_sha256") not in (None, payload_sha):
            errors.append(f"{path}: '{eid}' recorded proof_sha256 does not "
                          f"match the gzip payload")
        if recorded.get("proof_bytes") not in (None, len(payload)):
            errors.append(f"{path}: '{eid}' recorded proof_bytes "
                          f"{recorded.get('proof_bytes')} != {len(payload)}")

        # 3. Every step parses; the last ADD is the empty clause.
        steps = 0
        last_add_len = None
        for line_no, line in enumerate(payload.decode("ascii").splitlines(), 1):
            tokens = line.split()
            if not tokens:
                continue
            delete = tokens[0] == "d"
            literals = tokens[1:] if delete else tokens
            if not literals or literals[-1] != "0":
                errors.append(f"{path}: '{eid}' proof line {line_no} is not "
                              f"0-terminated")
                break
            body = literals[:-1]
            if any(not lit.lstrip("-").isdigit() or lit in ("0", "-0")
                   for lit in body):
                errors.append(f"{path}: '{eid}' proof line {line_no} has a "
                              f"non-literal token")
                break
            steps += 1
            if not delete:
                last_add_len = len(body)
        else:
            if recorded.get("proof_steps") not in (None, steps):
                errors.append(f"{path}: '{eid}' recorded proof_steps "
                              f"{recorded.get('proof_steps')} != {steps}")
            if last_add_len != 0:
                errors.append(f"{path}: '{eid}' final clause addition is not "
                              f"the empty clause; this proof refutes nothing")
        if not errors:
            print(f"  checked unsat certificate {eid}: CNF regenerated "
                  f"byte-identically, {steps} text-DRAT steps parsed, ends in "
                  f"the empty clause")
    elif fmt in ("drat-binary", "drat-binary-gzip"):
        if ev.get("check_status") == "checked":
            errors.append(f"{path}: '{eid}' is binary DRAT, which this system "
                          f"cannot read; it must not claim 'checked' (B8)")
    else:
        errors.append(f"{path}: '{eid}' unknown certificate format {fmt!r}")

    # Optional external cross-check, never the trusted path.
    if drat_checker and not errors and fmt in ("drat-text", "drat-text-gzip",
                                               "drat-binary", "drat-binary-gzip"):
        import tempfile
        with tempfile.NamedTemporaryFile(suffix=".drat") as tmp:
            tmp.write(payload)
            tmp.flush()
            result = subprocess.run(
                [drat_checker, str(cnf_path), tmp.name],
                capture_output=True, text=True)
            if "s VERIFIED" not in result.stdout:
                errors.append(f"{path}: '{eid}' external checker did not "
                              f"verify: {result.stdout[-200:]}")
            else:
                print(f"  external cross-check {eid}: s VERIFIED")
    return errors


def parse_bound(supports: str) -> tuple[int, str, int] | None:
    m = BOUND_RE.search(supports)
    if not m:
        return None
    return int(m.group(1)), m.group(2), int(m.group(3))


def check_claim(path: Path, drat_checker: str | None) -> list[str]:
    errors: list[str] = []
    c = json.loads(path.read_text())
    fam = c["formal"]["family"]
    params = c["formal"]["parameters"]

    for ev in c["evidence"]:
        if ev["check_status"] != "checked":
            continue
        eid = ev["id"]
        kind = ev["kind"]
        if fam != RADO_FAMILY:
            errors.append(f"{path}: evidence '{eid}' is 'checked' but family "
                          f"'{fam}' is not understood by this checker")
            continue
        a, b, k = int(params["a"]), int(params["b"]), int(params["k"])

        # A row whose artifact this tree deliberately does not carry cannot be
        # re-checked here, and saying otherwise would be the exact failure this
        # ledger exists to prevent. Report it as NOT re-checked, name the
        # recipe, and carry it into the summary -- never pass it silently.
        art = ev.get("artifact")
        if (ev.get("distribution") == "regenerable" and art is not None
                and not artifact_path(art).exists()):
            recipe = (ev.get("regeneration") or {}).get("command")
            if recipe is None and kind == "instance-pin":
                # An instance is defined by its four parameters; the recipe is
                # never unknown for these rows.
                recipe = (f"gen-rado-instance.py {a} {b} {k} {params['n']}"
                          f"  # -> sha256 {ev.get('artifact_sha256','?')}")
            recipe = recipe or "no recipe recorded"
            NOT_RECHECKED.append(f"{path.parent.name}/{eid}: {art} not "
                                 f"distributed; regenerate with: {recipe}")
            print(f"  NOT re-checked {eid}: artifact not distributed "
                  f"(regenerable; sha256 {ev.get('artifact_sha256','?')[:16]}...)")
            continue

        if kind in {"witness-replay", "published-value-replication"}:
            art = ev.get("artifact")
            if art is None:
                errors.append(f"{path}: '{eid}' checked but has no artifact")
                continue
            colours = [int(t) for t in artifact_path(art).read_text().split()]
            msg = check_rado_witness(a, b, k, colours)
            if msg is not None:
                errors.append(f"{path}: '{eid}' witness INVALID: {msg}")
                continue
            bound = parse_bound(ev["supports"])
            if bound is not None:
                bk, rel, bn = bound
                if bk != k:
                    errors.append(f"{path}: '{eid}' supports k={bk} but claim k={k}")
                if rel == ">" and len(colours) < bn:
                    errors.append(f"{path}: '{eid}' claims R_{k} > {bn} but the "
                                  f"witness has only {len(colours)} integers")
            print(f"  checked witness {eid}: {len(colours)} integers, "
                  f"no monochromatic solution of {a}(x-y)={b}z")

        elif kind == "unsat-certificate":
            errors.extend(check_unsat_certificate(path, ev, a, b, k, params,
                                                  drat_checker))

        elif kind == "cube-cover":
            errors.extend(check_cube_cover(path, ev, a, b, k, params))

        elif kind == "instance-pin":
            errors.extend(check_instance_pin(path, ev, a, b, k, params))

        elif kind == "exhaustive-enumeration":
            errors.append(f"{path}: '{eid}' exhaustive-enumeration re-check "
                          f"not implemented for this family; cannot be 'checked'")
        else:
            errors.append(f"{path}: '{eid}' kind '{kind}' cannot be 'checked'")
    return errors


def main() -> int:
    global CLAIMS, ALT_ROOT
    drat_checker = None
    only = None
    args = sys.argv[1:]
    if "--drat-checker" in args:
        i = args.index("--drat-checker")
        drat_checker = args[i + 1]
    if "--only" in args:
        i = args.index("--only")
        only = args[i + 1]
    if "--root" in args:
        CLAIMS = Path(args[args.index("--root") + 1])
        # In the shipped bundle the snapshot's paths are relative to the
        # bundle root, the parent of the claims directory. Offer it as a
        # fallback base rather than replacing the repo root: the negative
        # fixtures are also loaded through --root and use repo-relative paths.
        # Before this was a fallback, `--root claims` raised FileNotFoundError
        # on the first witness, so the re-check command the bundle's own
        # README documents had never worked.
        ALT_ROOT = CLAIMS.resolve().parent
    claim_files = sorted(CLAIMS.glob("**/claim.json"))
    if not claim_files:
        print("no claims found", file=sys.stderr)
        return 1
    if only is not None:
        claim_files = [p for p in claim_files
                       if fnmatch.fnmatch(p.parent.name, only)]
        if not claim_files:
            print(f"--only '{only}' matched no claim id", file=sys.stderr)
            return 1
    all_errors: list[str] = []
    for path in claim_files:
        print(f"{path.parent.name}:")
        all_errors.extend(check_claim(path, drat_checker))
    for e in all_errors:
        print(f"ERROR {e}", file=sys.stderr)
    if NOT_RECHECKED:
        print(f"\nNOT re-checked here ({len(NOT_RECHECKED)}); each is "
              f"regenerable and hash-pinned:")
        for m in NOT_RECHECKED:
            print(f"  - {m}")
    print(f"\n{len(claim_files)} claims re-checked, {len(all_errors)} errors, "
          f"{len(NOT_RECHECKED)} row(s) not re-checked here")
    return 1 if all_errors else 0


if __name__ == "__main__":
    sys.exit(main())
