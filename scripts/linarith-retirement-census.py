#!/usr/bin/env python3
"""Census of `nat_prelude`/`int_prelude` theorems retirable to `crate::linarith`.

WHY THIS EXISTS. ADR-1576 measured 4,737 order-lemma call sites
(`nat_prelude` 1,546, `int_prelude` 378 — this script's own count differs
slightly, see below — `rat_prelude` 601, `creal` 2,212) and retired the first
fifteen by hand-picking them. This is the instrument that should have found
them: it scans every `<dev>.theorem(name, arity, &|d, v| { ... })` /
`<dev>.int_theorem(...)` call site in `nat_prelude/` and `int_prelude/`
(excluding `*_tests.rs`) and flags one as a CANDIDATE when its hand-written
proof body cites *only* lemma names already in `crate::linarith`'s documented
vocabulary — resolving one level of local helper-function delegation (a
theorem that calls `some_core(d, ...)` inlines that helper's own citations
too, recursively, since several of the fifteen historical retirements did
exactly this).

THIS IS A CENSUS, NOT A RETIREMENT PROOF. A flagged candidate is a theorem
whose GOAL SHAPE plausibly falls inside the linear fragment because its
existing hand proof only reaches for order/add primitives — `linarith`
reasons about the goal directly, not by replaying the hand proof's lemma
choice, so a flagged candidate can still fail to retire (a hypothesis shape
`collect` cannot parse, a certificate the search bound cannot reach) and an
UNFLAGGED theorem can occasionally still retire (linarith finds a route the
hand proof never took). Retirement is verified by compiling and running the
suite, never by this census alone.

THE ALLOWED-LEMMA VOCABULARY is not only the "lemma -> role" table in
`linarith/nat.rs`'s and `linarith/int.rs`'s module docs (the lemmas the
EMITTER cites). It also includes a small number of PRIMITIVE order
constructors — `Nat.le.step`, `Nat.le_succ_succ`, `Nat.le_of_succ_le_succ`
for the ℕ side — that the ten historical `nat_prelude` retirements cited in
their HAND proofs even though the emitter reaches the same conclusions a
different way. Each addition is verified against those ten (`--positive-
control`, and every run): fetched from `f7cbb3ee3^` (the commit immediately
before `refactor(nat_prelude): retire ten hand-written order proofs`) and
`5b45a40c0^` (immediately before `feat(linarith): the integer fragment, and
five more retired proofs`), so the "positive control" is not asserted, it is
RE-DERIVED from the real pre-retirement source on every run — see
`positive_control` in the emitted JSON. If it ever stops finding all fifteen,
the vocabulary or the resolver regressed.

WHAT COUNTS AS "ONLY order/add lemmas": every `p.<name>` / `p.nat.<name>`
citation in the theorem's closure body, PLUS every citation reachable through
one level of local helper-function calls (`some_core(d, ...)`) resolved
against a whole-directory `fn name -> body` table, must be in the allowed
set — OR be the name of one of the fifteen ALREADY-RETIRED theorems (citing
an already-retired lemma costs nothing extra: its proof is generated, not
hand-written). A body mentioning any of a short list of complexity markers
(`exists_elim`, `case_split`, `cases_`, `WellFounded`, `.fix(`, `induction`)
anywhere in its own text or a resolved helper's is disqualified outright,
whatever its citations.

Exit 0 always (a census, not a gate) except `--check`, which exits 1 when the
committed artifact is stale — the file is registered with
`scripts/check-generated-artifact-ownership.py`.

Usage:
    python3 scripts/linarith-retirement-census.py              # write the artifact
    python3 scripts/linarith-retirement-census.py --check       # fail if stale
    python3 scripts/linarith-retirement-census.py --top 20      # print top N by lines
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
NAT_DIR = ROOT / "crates" / "axeyum-lean-kernel" / "src" / "nat_prelude"
INT_DIR = ROOT / "crates" / "axeyum-lean-kernel" / "src" / "int_prelude"
LINARITH_NAT_SRC = ROOT / "crates" / "axeyum-lean-kernel" / "src" / "linarith" / "nat.rs"
LINARITH_INT_SRC = ROOT / "crates" / "axeyum-lean-kernel" / "src" / "linarith" / "int.rs"
ARTIFACT = ROOT / "artifacts" / "refactor" / "linarith-retirement-census.json"
SCHEMA_VERSION = 1
PRODUCED_BY = "scripts/linarith-retirement-census.py"

NAT_PRE_RETIREMENT_COMMIT = "f7cbb3ee3^"
NAT_RETIREMENT_COMMIT = "f7cbb3ee3"
INT_PRE_RETIREMENT_COMMIT = "5b45a40c0^"
INT_RETIREMENT_COMMIT = "5b45a40c0"

# The ten/five names ADR-1576 records as the FIRST retirement batch -- fixed,
# not updated by later retirements. Used only as the positive control's
# expected set (re-derived from the real pre-retirement source at the two
# commits below on every run, never asserted). The "citing an already-retired
# name costs nothing extra" allowance a *candidate* gets uses the CURRENT
# `already_retired` set instead (computed from source, in `classify`'s
# caller), so it grows as later lanes retire more -- deriving that from a
# literal here would go stale the moment this lane's own five retirements
# landed.
ADR1576_RETIRED_NAT = (
    "le_refl_thm", "le_succ", "succ_le_succ", "le_of_lt_succ",
    "lt_succ_self", "lt_succ_of_le", "lt_add_one", "le_succ_of_le",
    "zero_lt_succ", "le_of_lt_add_one",
)
ADR1576_RETIRED_INT = (
    "add_left_comm", "add_neg_cancel_left", "add_neg_cancel_right",
    "add_le_add_three", "add_le_of_le_sub_left",
)

# The emitter's own documented vocabulary (`linarith/nat.rs`'s "lemma | role"
# table), plus `le_step`/`le_of_succ_le_succ` -- primitives none of the
# ten retirements' hand proofs avoided, confirmed empirically below.
ALLOWED_NAT = frozenset({
    "le_refl", "le_trans", "le_add_right", "add_le_add_left",
    "add_le_add_right", "le_of_add_le_add_right", "le_succ_succ",
    "lt_irrefl", "le_antisymm", "add_comm", "add_right_comm", "add_assoc",
    "mul_comm",
    # Primitive order constructors the emitter does not cite but the
    # historical hand proofs did; see the module docstring above.
    "le_step", "le_of_succ_le_succ",
})

# `linarith/int.rs`'s documented vocabulary, plus `le_succ_of_lt`, `mul_one`,
# `mul_zero`, `left_distrib` -- the ℤ strictness bridge and the literal-mul
# unroll this same lane landed (both new prelude/emitter surface, not present
# when ADR-1576 wrote its own table).
ALLOWED_INT = frozenset({
    "le_refl", "le_trans", "add_le_add", "add_le_add_left",
    "add_le_add_right", "add_le_add_iff_right", "le_of_nat_add",
    "lt_of_nat_add", "lt_of_lt_of_le", "le_of_lt", "lt_irrefl",
    "le_antisymm", "add_comm", "add_assoc", "add_zero", "add_neg",
    "logic.iff_mp", "iff_mp",
    "le_succ_of_lt", "mul_one", "mul_zero", "left_distrib", "mul_comm",
    "nat.zero_le", "nat.le_succ_succ", "lt_elim",
})

DISQUALIFYING_MARKERS = (
    "exists_elim", "case_split", "cases_", "with_hypotheses", "by_borrow",
    "WellFounded", ".fix(", ".induct(", "induction", "gcd", "factorial",
    "choose(", "prime", "dvd", "sqrt", "pow(", "_rec(", ".rec(", "Exists",
)

_STRING = re.compile(r'"(?:\\.|[^"\\])*"')
_CHAR = re.compile(r"'(?:\\.|[^'\\])'")
_LINE_COMMENT = re.compile(r"//[^\n]*")
_BLOCK_COMMENT = re.compile(r"/\*.*?\*/", re.DOTALL)


def mask(text: str) -> str:
    """`text` with comments and string/char literal content blanked (same
    length, newlines preserved), so brace matching ignores braces inside
    either."""
    def blank(m: re.Match) -> str:
        return "".join(c if c == "\n" else " " for c in m.group(0))

    out = _BLOCK_COMMENT.sub(blank, text)
    out = _LINE_COMMENT.sub(blank, out)
    out = _STRING.sub(blank, out)
    out = _CHAR.sub(blank, out)
    return out


def match_brace(masked: str, open_at: int) -> int | None:
    """Offset just past the `}` matching the `{` at `open_at`, or None."""
    depth = 0
    for i in range(open_at, len(masked)):
        c = masked[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i + 1
    return None


_THEOREM_CALL = re.compile(
    r"\b(?P<recv>[a-zA-Z_][a-zA-Z0-9_]*)\.(?P<method>theorem|int_theorem)\(\s*"
    r"p\.(?P<name>[a-zA-Z_][a-zA-Z0-9_]*)\s*,\s*(?P<arity>[0-9]+|[a-zA-Z_][a-zA-Z0-9_.]*)\s*,\s*&\|"
)
_RETIRED_CALL = re.compile(
    r"linarith::declare\([^,]+,\s*&?p\s*,\s*p\.(?P<name>[a-zA-Z_][a-zA-Z0-9_]*)"
)
_FN_DEF = re.compile(
    r"\bfn\s+(?P<name>[a-zA-Z_][a-zA-Z0-9_]*)\s*(?:<[^>]*>)?\s*\("
)
# Two spellings reach the same prelude fields: an aliased `let p = d.int();`
# (or `.prelude()`) local, and a direct inline `d.int().name` /
# `d.prelude().name` with no alias at all -- `int_prelude/sub_nat_nat.rs`
# uses the second form throughout, and missing it made every one of its
# theorems look like it cited nothing (silently "uncovered-free").
_CITATION = re.compile(
    r"\b(?:p|np)\.((?:[a-zA-Z_][a-zA-Z0-9_]*\.)*[a-zA-Z_][a-zA-Z0-9_]*)"
    r"|\bd\.(?:int|prelude|nat_prelude)\(\)\.((?:[a-zA-Z_][a-zA-Z0-9_]*\.)*[a-zA-Z_][a-zA-Z0-9_]*)"
)
_STRUCT_ONLY = frozenset({"nat", "logic", "int"})
_HELPER_CALL = re.compile(r"\b([a-z_][a-zA-Z0-9_]*)\(\s*d\b")


def find_fn_bodies(raw: str, masked: str) -> dict[str, list[str]]:
    """Every `fn NAME(...) { ... }` in this file, keyed by name."""
    out: dict[str, list[str]] = {}
    for m in _FN_DEF.finditer(masked):
        brace = masked.find("{", m.end() - 1)
        if brace < 0:
            continue
        # No body between the signature and the next `fn`/EOF (a trait
        # signature with no default) -- only accept a `{` that starts
        # within a short run of the parameter list's close.
        close_paren = masked.rfind(")", m.end() - 1, brace + 1)
        if close_paren < 0:
            continue
        end = match_brace(masked, brace)
        if end is None:
            continue
        body = raw[brace:end]
        out.setdefault(m.group("name"), []).append(body)
    return out


def citations_of(body: str) -> set[str]:
    cites = set()
    for m in _CITATION.finditer(body):
        name = m.group(1) or m.group(2)
        if name in _STRUCT_ONLY:
            continue
        cites.add(name)
    return cites


def resolve_citations(
    body: str, symtab: dict[str, list[str]], depth: int = 4
) -> tuple[set[str], bool, set[str]]:
    """Direct + one/two-level-resolved helper citations, whether a
    disqualifying marker appears anywhere reached, and the helper names
    actually resolved (for reporting)."""
    cites = set(citations_of(body))
    disqualified = any(marker in body for marker in DISQUALIFYING_MARKERS)
    resolved: set[str] = set()
    visited: set[str] = set()
    frontier = [n for n in _HELPER_CALL.findall(body) if n != "d"]
    d = depth
    while frontier and d > 0:
        d -= 1
        nxt: list[str] = []
        for name in frontier:
            if name in visited:
                continue
            visited.add(name)
            bodies = symtab.get(name)
            if not bodies:
                continue
            resolved.add(name)
            for hb in bodies:
                cites |= citations_of(hb)
                if any(marker in hb for marker in DISQUALIFYING_MARKERS):
                    disqualified = True
                nxt.extend(n for n in _HELPER_CALL.findall(hb) if n != "d")
        frontier = nxt
    return cites, disqualified, resolved


def scan_dir(directory: pathlib.Path) -> tuple[list[dict], list[str], dict[str, list[str]]]:
    """(theorem call sites, already-retired names, whole-dir fn symbol table)."""
    sites: list[dict] = []
    retired: list[str] = []
    symtab: dict[str, list[str]] = {}
    files = sorted(p for p in directory.glob("*.rs") if not p.name.endswith("_tests.rs"))
    parsed: dict[pathlib.Path, tuple[str, str]] = {}
    for path in files:
        raw = path.read_text(encoding="utf-8", errors="replace")
        masked = mask(raw)
        parsed[path] = (raw, masked)
        for name, bodies in find_fn_bodies(raw, masked).items():
            symtab.setdefault(name, []).extend(bodies)
        for m in _RETIRED_CALL.finditer(masked):
            retired.append(m.group("name"))
    for path in files:
        raw, masked = parsed[path]
        rel = str(path.relative_to(ROOT))
        for m in _THEOREM_CALL.finditer(masked):
            brace = masked.find("{", m.end() - 1)
            if brace < 0:
                continue
            end = match_brace(masked, brace)
            if end is None:
                continue
            body = raw[brace:end]
            line_count = body.count("\n") + 1
            sites.append({
                "file": rel,
                "name": m.group("name"),
                "arity": m.group("arity"),
                "body": body,
                "line_count": line_count,
            })
    return sites, sorted(set(retired)), symtab


def linarith_foundational(*sources: pathlib.Path) -> frozenset[str]:
    """Every `p.<name>` the emitter's OWN source cites, in either carrier.

    A theorem the emitter itself depends on cannot be retired to the emitter
    -- `Int.add_le_add_left` is cited inside `emit_le`, which runs on every
    single ℤ proof the search produces, this lane's own `Int.le_succ_of_lt`
    is cited inside `collect`'s strictness weakening, and so on. Retiring
    either would make the emitter's search for its OWN theorem's proof
    reference a name the kernel has not declared yet -- caught at
    `add_declaration` time (`UnknownConst`), not silently wrong, but it is
    not a real target and does not belong in the candidate list. Derived from
    the emitter's own source on every run, not hand-maintained, so it cannot
    go stale the way a literal list would.
    """
    names: set[str] = set()
    for src in sources:
        if not src.exists():
            continue
        text = src.read_text(encoding="utf-8", errors="replace")
        for name in citations_of(text):
            names.add(name.rsplit(".", 1)[-1])
    return frozenset(names)


def classify(sites: list[dict], symtab: dict[str, list[str]], allowed: frozenset[str],
             known_retired: tuple[str, ...],
             foundational: frozenset[str] = frozenset()) -> tuple[list[dict], list[dict]]:
    candidates, declined = [], []
    for site in sites:
        cites, disqualified, resolved = resolve_citations(site["body"], symtab)
        # A citation to an already-retired name costs nothing extra.
        uncovered = {c for c in cites if c not in allowed and c not in known_retired}
        entry = {
            "name": site["name"],
            "file": site["file"],
            "arity": site["arity"],
            "line_count": site["line_count"],
            "citations": sorted(cites),
            "resolved_helpers": sorted(resolved),
        }
        bare_refl = not cites and (
            "d.refl(" in site["body"] or "d.irefl(" in site["body"]
        )
        if site["name"] in foundational:
            entry["reason"] = "the emitter itself depends on this lemma (circular)"
            declined.append(entry)
        elif bare_refl:
            # Zero lemma citations, proved by pure defeq. Vacuously "cites
            # only allowed lemmas" -- and almost always a CUSTOM recursive
            # function's own defining equation (`stirlingFirst`, `fib`, ...)
            # reducing on constructor-shaped arguments, which the parser
            # treats as an opaque atom rather than something `add`/`succ`
            # related -- not something the search can reach. Excluded rather
            # than flagged; a genuinely trivial additive refl (rare) is a
            # false negative here, not a false positive.
            entry["reason"] = "no lemma citations (bare defeq/refl proof)"
            declined.append(entry)
        elif disqualified or uncovered:
            entry["reason"] = (
                "disqualifying marker" if disqualified
                else f"uncovered citation(s): {sorted(uncovered)}"
            )
            declined.append(entry)
        else:
            candidates.append(entry)
    candidates.sort(key=lambda e: (-e["line_count"], e["name"]))
    declined.sort(key=lambda e: (-e["line_count"], e["name"]))
    return candidates, declined


def git_show(rev: str, path: str) -> str | None:
    try:
        out = subprocess.run(
            ["git", "show", f"{rev}:{path}"],
            cwd=ROOT, capture_output=True, text=True, check=True,
        )
    except subprocess.CalledProcessError:
        return None
    return out.stdout


def positive_control() -> dict:
    """Re-derive the fifteen historical retirements from the real
    pre-retirement source at the two commits, rather than asserting they
    would be found."""
    result: dict = {}
    for label, rev, rel_files, expected, allowed, known in (
        ("nat", NAT_PRE_RETIREMENT_COMMIT,
         ["crates/axeyum-lean-kernel/src/nat_prelude/order_extra.rs",
          "crates/axeyum-lean-kernel/src/nat_prelude/order_more.rs"],
         ADR1576_RETIRED_NAT, ALLOWED_NAT, ADR1576_RETIRED_NAT),
        ("int", INT_PRE_RETIREMENT_COMMIT,
         ["crates/axeyum-lean-kernel/src/int_prelude/add_basics.rs",
          "crates/axeyum-lean-kernel/src/int_prelude/algebra.rs",
          "crates/axeyum-lean-kernel/src/int_prelude/order_add.rs"],
         ADR1576_RETIRED_INT, ALLOWED_INT, ADR1576_RETIRED_INT),
    ):
        symtab: dict[str, list[str]] = {}
        parsed = {}
        for rel in rel_files:
            text = git_show(rev, rel)
            if text is None:
                result[label] = {"error": f"could not fetch {rel}@{rev}"}
                break
            masked = mask(text)
            parsed[rel] = (text, masked)
            for name, bodies in find_fn_bodies(text, masked).items():
                symtab.setdefault(name, []).extend(bodies)
        else:
            sites = []
            for rel, (text, masked) in parsed.items():
                for m in _THEOREM_CALL.finditer(masked):
                    brace = masked.find("{", m.end() - 1)
                    if brace < 0:
                        continue
                    end = match_brace(masked, brace)
                    if end is None:
                        continue
                    if m.group("name") not in expected:
                        continue
                    body = text[brace:end]
                    sites.append({
                        "file": rel, "name": m.group("name"),
                        "arity": m.group("arity"), "body": body,
                        "line_count": body.count("\n") + 1,
                    })
            candidates, declined = classify(sites, symtab, allowed, known)
            flagged = sorted(e["name"] for e in candidates)
            found_names = {s["name"] for s in sites}
            result[label] = {
                "commit": rev,
                "expected_names": sorted(expected),
                "found_call_sites": sorted(found_names),
                "flagged": flagged,
                "declined": [
                    {"name": e["name"], "reason": e["reason"]} for e in declined
                ],
                "all_found_and_flagged": (
                    found_names == set(expected)
                    and set(flagged) == set(expected)
                ),
            }
    return result


def build() -> dict:
    nat_sites, nat_retired, nat_symtab = scan_dir(NAT_DIR)
    int_sites, int_retired, int_symtab = scan_dir(INT_DIR)
    nat_foundational = linarith_foundational(LINARITH_NAT_SRC)
    int_foundational = linarith_foundational(LINARITH_INT_SRC)
    # The "citing an already-retired name costs nothing extra" allowance uses
    # every retirement DETECTED IN THE CURRENT SOURCE, not the fixed
    # ADR-1576 batch -- it must grow as later lanes retire more.
    nat_candidates, nat_declined = classify(
        nat_sites, nat_symtab, ALLOWED_NAT, tuple(nat_retired), nat_foundational
    )
    int_candidates, int_declined = classify(
        int_sites, int_symtab, ALLOWED_INT, tuple(int_retired), int_foundational
    )

    decline_reasons: dict[str, int] = {}
    for e in nat_declined + int_declined:
        key = e["reason"].split(":")[0]
        decline_reasons[key] = decline_reasons.get(key, 0) + 1

    for group in (nat_candidates, nat_declined, int_candidates, int_declined):
        for e in group:
            e.pop("body", None)

    return {
        "schema_version": SCHEMA_VERSION,
        "kind": "linarith-retirement-census",
        "produced_by": PRODUCED_BY,
        "authority": (
            "<dev>.theorem/<dev>.int_theorem call sites in nat_prelude/ and "
            "int_prelude/ (excluding *_tests.rs); a candidate's every direct "
            "or one-level-resolved-helper `p.<lemma>` citation must lie in "
            "the documented linarith emitter vocabulary plus the primitive "
            "order constructors the historical retirements needed"
        ),
        "allowed_lemmas": {
            "nat": sorted(ALLOWED_NAT),
            "int": sorted(ALLOWED_INT),
        },
        "positive_control": positive_control(),
        "already_retired": {
            "note": (
                "`known` is the ORIGINAL fifteen (ADR-1576's own batch), used "
                "as the positive control's fixed expected set -- it is not "
                "updated by later retirements, so `match: false` after a new "
                "retirement lands is expected, not a regression. "
                "`detected_in_source` is every `linarith::declare(...)` call "
                "site this run actually finds, current as of this run."
            ),
            "nat": {
                "known": sorted(ADR1576_RETIRED_NAT),
                "detected_in_source": nat_retired,
                "match": sorted(ADR1576_RETIRED_NAT) == nat_retired,
            },
            "int": {
                "known": sorted(ADR1576_RETIRED_INT),
                "detected_in_source": int_retired,
                "match": sorted(ADR1576_RETIRED_INT) == int_retired,
            },
        },
        "population": {
            "nat_theorem_call_sites": len(nat_sites),
            "nat_candidates": len(nat_candidates),
            "nat_declined": len(nat_declined),
            "int_theorem_call_sites": len(int_sites),
            "int_candidates": len(int_candidates),
            "int_declined": len(int_declined),
        },
        "decline_histogram": dict(sorted(decline_reasons.items(), key=lambda kv: -kv[1])),
        "candidates": {"nat": nat_candidates, "int": int_candidates},
        "declined": {"nat": nat_declined, "int": int_declined},
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                     help="fail if the committed artifact is stale; never writes")
    ap.add_argument("--top", type=int, default=0,
                     help="print the top N candidates by line count per carrier")
    args = ap.parse_args(argv)

    data = build()
    rendered = json.dumps(data, indent=2, sort_keys=True) + "\n"

    if args.check:
        if not ARTIFACT.exists() or ARTIFACT.read_text(encoding="utf-8") != rendered:
            print(f"LINARITH_RETIREMENT_CENSUS stale: {ARTIFACT} does not match "
                  "a fresh run -- regenerate with "
                  "`python3 scripts/linarith-retirement-census.py`", file=sys.stderr)
            return 1
        print(f"LINARITH_RETIREMENT_CENSUS ok|{ARTIFACT} matches")
        return 0

    ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
    ARTIFACT.write_text(rendered, encoding="utf-8")

    pc = data["positive_control"]
    pc_ok = all(v.get("all_found_and_flagged") for v in pc.values())
    print(
        "LINARITH_RETIREMENT_CENSUS|"
        f"nat_sites={data['population']['nat_theorem_call_sites']}|"
        f"nat_candidates={data['population']['nat_candidates']}|"
        f"int_sites={data['population']['int_theorem_call_sites']}|"
        f"int_candidates={data['population']['int_candidates']}|"
        f"positive_control_ok={pc_ok}"
    )
    if args.top:
        for carrier in ("nat", "int"):
            print(f"-- top {args.top} {carrier} candidates by line count --")
            for e in data["candidates"][carrier][: args.top]:
                print(f"  {e['line_count']:4d}  {e['name']}  ({e['file']})")
    if not pc_ok:
        print("WARNING: positive control did not find/flag all fifteen "
              "historical retirements -- see positive_control in the "
              "artifact", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
