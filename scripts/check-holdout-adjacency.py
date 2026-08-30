#!/usr/bin/env python3
"""ADR-0653's adjacency rule, as code instead of prose.

The rule is one sentence:

  > a family may be held out only if its mathematics is not already published
  > by an existing development/train family.

Until this script, nothing enforced it. `guard()` in
`gen-autogenesis-nursery-refill.py` carries ten rules and **R9 is a NAME
screen**: it refuses a held-out candidate whose Mathlib declaration name is
already in the kernel environment. Measured 2026-08-30 (ADR-0762) and
reproduced independently here, a draw putting `Init.Data.Nat.Bitwise.Lemmas`
and `Mathlib.Data.Nat.GCD.Basic` into **held-out** -- beside `natural-bitwise`
and `natural-gcd`, both *development*, both worked by lanes that week --
returns

    GUARD PASSED -- 340 entries, 120 held-out rows, 12 held-out families

with the three-family control refusing at R5 in the same run. The machinery is
live; it has no adjacency rule to fire.

WHAT THIS COVERS, AND WHAT IT DOES NOT
--------------------------------------
Three contamination shapes have actually occurred, and they are different
problems. Claiming one screen covers all three would be worse than shipping a
partial screen with the gap named, so:

  shape 1  TOPICAL OVERLAP -- the held-out family's subject matter is already
           a development/train family's subject matter (`natural-binomial`,
           ADR-0542; and the bitwise/gcd draw above).
           **COVERED**, by two independent signals:
             * `topic`      -- the module topic segments coincide.
             * `vocabulary` -- the drawn statements are about constants a
                               development/train family publishes.
           They are complementary, not redundant, and each catches cases the
           other misses; the measured separation is in `--measure`.

  shape 2  A DIFFERENTLY-NAMED THEOREM -- our development proves the same
           proposition under another name, so R9's exact-name comparison sees
           nothing (`natural-parity`: the theorem landed five hours before
           preregistration and R9 reported a clean 0/10).
           **PARTIALLY COVERED**, by the `environment` signal, which is draw
           8's hand-run "screen 2 namespace sweep" mechanised: it asks whether
           the kernel environment declares ANYTHING about the candidate's
           subject operators, not whether it declares this theorem. It is a
           subject-level screen, so it cannot see a same-subject family whose
           operators we have not declared at all, and it says nothing about
           whether a particular row is provable here.

  shape 3  A DEFINITION THAT DECIDES ROWS BY REDUCTION -- declaring the
           construction settles closed rows the instant `add_declaration`
           returns (`fermat-numbers`, ADR-0695: three rows spent by the
           definition, not by a test).
           **NOT COVERED.** That is `scripts/check-holdout-closed-evaluation.py`'s
           job, and it has its own recorded blindness: `is_closed_evaluation`
           requires a binder-free statement, so `∀ (a : ℕ), Nat.nthRoot 0 a = 1`
           -- refl the moment the construction lands -- is invisible to it
           (383-nursery-draw-8.md). Nothing here narrows that gap.

RELATION TO THE OTHER TWO HOLDOUT CHECKERS
------------------------------------------
`check-autogenesis-holdout-isolation.py` asks whether a preregistered held-out
row has been settled or referenced. `check-autogenesis-holdout-contamination.py`
asks whether the kernel already proves one, by building the kernel and
comparing rendered types; it is advisory and post-hoc by design. Both look at
rows that are ALREADY preregistered. This one runs BEFORE preregistration and
is a hard guard rule, because after preregistration the only lawful repair is
an ADR-0542 amendment ledger -- which is a spend, not a fix.

USAGE
-----
    scripts/check-holdout-adjacency.py            # gate the committed manifests
    scripts/check-holdout-adjacency.py --measure  # the calibration table
    scripts/check-holdout-adjacency.py --self-test

`guard()` imports `screen_family` from here, so a draw cannot pass without it.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import re
import sys
from collections import Counter, defaultdict
from typing import Any, Iterable, NamedTuple

ROOT = pathlib.Path(__file__).resolve().parents[1]
AUTOGEN = ROOT / "artifacts/autogenesis"
NURSERY_V1 = AUTOGEN / "nursery-v1.json"
EXTENSION = AUTOGEN / "nursery-v2-extension.json"
FACTS = ROOT / "artifacts/facts"

# --- the three tunables, and why each is where it is ------------------------
#
# Every one of these is calibrated in `--measure` against BOTH directions: the
# authored draws on `main`, which must pass, and the known contaminations,
# which must fail. A screen with no accepting case cannot tell "correct" from
# "refuses everything", and three consecutive declined draws is what makes that
# the live risk rather than a theoretical one.

# A constant is PLUMBING if it is characteristic of more than this many of the
# nursery's families. Derived from the nursery, NOT from Mathlib frequency:
# measured 2026-08-30, an inventory-frequency rule at 2% classifies `Nat.Prime`
# (390 rows) and `Nat.Coprime` (241) as ambient -- the exact subjects
# `natural-primes` and `natural-coprimality` own -- because importance and
# frequency are the same thing in a mathematical library. Family-frequency does
# not have that failure: `Nat.Prime` is characteristic of 3 families, `Eq` of
# 29, `Nat` of 31.
AMBIENT_FAMILIES = 6

# A constant is CHARACTERISTIC of a family when it appears in at least this
# fraction of the family's rows (and at least twice). Below this a constant is
# incidental to the family rather than its subject.
SUBJECT_FRACTION = 0.30

# The `vocabulary` signal refuses at this many adjacent rows out of the ten a
# draw takes. Draw 7 deliberately permitted 2 of 10 `fermat-numbers` rows to
# mention `Nat.Prime` as shared vocabulary and that draw is authored; draw 8
# rejected `Squarefree` by judgement at 8 of 10. The threshold has to sit
# strictly between those, and the measured margin is reported by `--measure`.
VOCABULARY_MAX_ROWS = 5

# Module path segments that name a namespace root, a carrier or a file-naming
# convention rather than a topic. `Nat`/`Int` are here deliberately: they are
# the carrier, so treating them as topics would make every Nat module adjacent
# to every other one and the screen would refuse everything.
MODULE_ROOTS = frozenset({"Init", "Mathlib", "Batteries", "Std", "Lean", "Core"})
MODULE_GENERIC = frozenset({
    "Data", "Basic", "Lemmas", "Defs", "Init", "Bootstrap", "Aux", "LemmasAux",
    "Prelude", "Core", "Simp", "Tactic", "Util", "Classes", "Instances",
    "Nat", "Int", "Algebra", "Group", "Ring", "Order", "NumberTheory",
    "Analysis", "SpecialFunctions", "Polymorphic", "Basic2",
})

# SYNTAX IS NOT MATHEMATICS. An elaborated Lean type names the operation
# through its typeclass plumbing -- `n &&& m` arrives as `HAnd.hAnd` +
# `instHAndOfAndOp` + `Nat.instAndOp`, and `a % b` as `HMod.hMod` +
# `Nat.instMod` -- and a frequency rule cannot separate those from a subject,
# because `natural-modulus` really is characteristic in `Nat.instMod`.
# Measured 2026-08-30 without this filter: 40 of 42 families come out adjacent
# to something and the screen refuses every draw, which is indistinguishable
# from a broken flywheel. With it, the surviving published subjects are exactly
# the mathematics -- `Nat.gcd`, `Nat.Prime`, `Nat.Coprime`, `Even`, `Odd`,
# `Nat.choose`, `Nat.factorial`, `Nat.totient`, `Nat.fib`, `Nat.log`,
# `Nat.ModEq`, `Nat.lcm`, `Nat.testBit`, `Nat.fermatNumber`, ... -- and nothing
# else. The classification is structural and stated, not a tuned threshold:
# typeclass instances, heterogeneous-operator classes, logical formers,
# coercions, structure projections, and the carriers' own constructors.
SYNTAX_PATTERNS = (
    re.compile(r"^inst"),                      # instHMod, instOfNatNat, instLENat
    re.compile(r"\.inst"),                     # Nat.instMod, Int.instSemiring
    re.compile(r"^H[A-Z][A-Za-z]*\."),         # HAdd.hAdd, HMod.hMod, HAnd.hAnd
    re.compile(r"\.to[A-Z]"),                  # Monoid.toPow, structure projection
    re.compile(r"\.cast$"),                    # Nat.cast, Int.cast -- coercion
    re.compile(r"^(LE|LT|GE|GT|Neg|Add|Mul|Sub|Div|Mod|Pow|Dvd|OfNat|Min|Max|"
               r"AndOp|OrOp|Xor|Complement|ShiftLeft|ShiftRight|Membership|"
               r"Coe|CoeTail|NatCast|IntCast|Insert|Singleton)\."),
)
SYNTAX_NAMES = frozenset({
    "Eq", "Iff", "And", "Or", "Not", "Ne", "Exists", "True", "False",
    "Nat", "Int", "Bool", "Prop", "Sort", "Type", "Unit", "Decidable",
    "Bool.true", "Bool.false", "Nat.succ", "Nat.zero", "Int.ofNat",
    "Int.negSucc", "List", "Array", "Option", "Prod", "Subtype", "Set",
    "Finset", "DFunLike.coe",
})


def is_syntax(constant: str) -> bool:
    """True when a constant names plumbing rather than a piece of mathematics."""
    if constant in SYNTAX_NAMES:
        return True
    return any(p.search(constant) for p in SYNTAX_PATTERNS)


# Word stems that carry no subject information when sweeping the kernel
# environment for a candidate's operators.
STEM_STOPWORDS = frozenset({
    "nat", "int", "inst", "of", "to", "eq", "le", "lt", "ne", "and", "or",
    "not", "iff", "add", "mul", "sub", "div", "mod", "neg", "pow", "op",
    "ofnat", "hmul", "hadd", "hsub", "hdiv", "hmod", "hpow", "hand", "hor",
    "hxor", "dvd", "exists", "prop", "type", "sort", "bool", "true", "false",
    "self", "left", "right", "zero", "one", "two", "succ", "pred", "cast",
})

# An adjacency the project has looked at and accepted, with the numbers it was
# accepted at. This is the "required disclosure" half of the rule: a family may
# appear here only with an ADR, and the row must MATCH the live measurement, so
# a stale acceptance goes red instead of standing forever. Topic overlap is not
# waivable -- only the vocabulary count is, and only up to a stated number.
ADJACENCY_ACCEPTED: dict[str, dict[str, Any]] = {}


class RefusalError(Exception):
    """The adjacency rule refuses a family. Raised, never returned."""


class Row(NamedTuple):
    name: str
    module: str
    constants: frozenset


class Finding(NamedTuple):
    family: str
    verdict: str                 # "clean" | "refused"
    topic_hits: tuple            # ((segment, other_family), ...)
    vocabulary_rows: int
    vocabulary_hits: tuple       # ((constant, other_family), ...)
    environment_hits: tuple      # ((stem, example_declaration, count), ...)
    reasons: tuple


# --------------------------------------------------------------------------
# loading
# --------------------------------------------------------------------------
def load_refill_module():
    """Import the refill generator by path; it is a script, not a package."""
    spec = importlib.util.spec_from_file_location(
        "_refill_for_adjacency", ROOT / "scripts/gen-autogenesis-nursery-refill.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


_WHAT = re.compile(r"`([^`]+)`")
_MUTATION = re.compile(r"mutation of ([A-Za-z0-9_.']+)")


def _source_name_from_fact(fact: dict[str, Any]) -> str | None:
    """The Mathlib declaration a v1 nursery fact was transcribed from.

    v1 entries carry no `source_name` -- their `source_group` is an opaque
    catalog hash -- so the ledger is the only place the Mathlib name survives.
    A mutation names its parent in `provenance.source` instead.
    """
    prov = fact.get("provenance", {})
    for pa in prov.get("prior_art", []) or []:
        m = _WHAT.search(pa.get("what", ""))
        if m:
            return m.group(1)
    m = _MUTATION.search(prov.get("source", "") or "")
    return m.group(1) if m else None


def resolve_families(refill) -> tuple[dict[str, list[Row]], dict[str, str], dict[str, int]]:
    """Every nursery family, its rows joined to the pinned Mathlib inventory.

    Returns (rows by family, partition by family, coverage counters). Both
    manifests are required and each must contribute, for the reason
    `check-autogenesis-holdout-contamination.py` records at length: a detector
    reading one of two populations reports the same "clean" as one that works.
    """
    inventory = refill.read_inventory()
    inv = {
        name: Row(name, rec["module"],
                  frozenset(refill.CONST_RE.findall(rec["type_repr"])))
        for name, rec in inventory.items()
    }
    facts = {}
    for path in FACTS.glob("*.json"):
        try:
            data = json.loads(path.read_text())
        except json.JSONDecodeError:
            continue
        if isinstance(data, dict) and "id" in data:
            facts[data["id"]] = data

    v1 = json.loads(NURSERY_V1.read_text())
    ext = json.loads(EXTENSION.read_text())
    rows: dict[str, list[Row]] = defaultdict(list)
    partition: dict[str, str] = {}
    counts = Counter()

    for entry in v1["entries"]:
        if entry["partition"] == "longitudinal":
            continue
        partition[entry["family"]] = entry["partition"]
        counts["v1"] += 1
        fact = facts.get(entry["fact_id"])
        name = _source_name_from_fact(fact) if fact else None
        row = inv.get(name)
        if row is None:
            counts["unresolved"] += 1
            continue
        rows[entry["family"]].append(row)
    for entry in ext["entries"]:
        partition[entry["family"]] = entry["partition"]
        counts["extension"] += 1
        rows[entry["family"]].append(
            Row(entry["source_name"], entry["module"], frozenset(entry["constants"])))

    if not counts["v1"] or not counts["extension"]:
        raise SystemExit(
            "check-holdout-adjacency: a manifest contributed zero rows "
            f"(v1={counts['v1']} extension={counts['extension']}); refusing to "
            "report a clean screen over a population it did not read")
    return dict(rows), partition, dict(counts)


# --------------------------------------------------------------------------
# the three signals
# --------------------------------------------------------------------------
def topics(module: str) -> frozenset:
    """The topic segments of a module path, carrier and convention removed."""
    return frozenset(
        seg for seg in module.split(".")
        if seg not in MODULE_ROOTS and seg not in MODULE_GENERIC
    )


def characteristic(rows: Iterable[Row], fraction: float = SUBJECT_FRACTION) -> set:
    rows = list(rows)
    if not rows:
        return set()
    counts: Counter = Counter()
    for row in rows:
        counts.update(row.constants)
    floor = max(2, fraction * len(rows))
    return {c for c, k in counts.items() if k >= floor}


def plumbing(by_family: dict[str, list[Row]],
             ambient_families: int = AMBIENT_FAMILIES) -> set:
    """Constants characteristic of too many families to be anyone's subject."""
    seen: Counter = Counter()
    for rows in by_family.values():
        seen.update(characteristic(rows))
    return {c for c, k in seen.items() if k > ambient_families}


def subject_constants(rows: Iterable[Row], plumb: set) -> set:
    return {c for c in characteristic(rows) - plumb if not is_syntax(c)}


def _stems(constant: str) -> set:
    """Word stems of a constant name, for the environment sweep."""
    tail = constant.split(".")[-1]
    words = re.findall(r"[A-Z]+(?![a-z])|[A-Z][a-z]*|[a-z]+|\d+", tail)
    out = {w.lower() for w in words if len(w) > 2}
    out.add(tail.lower())
    return {w for w in out if w not in STEM_STOPWORDS and len(w) > 2}


def environment_sweep(subjects: Iterable[str], env: Iterable[str],
                      limit: int = 4) -> tuple:
    """Declarations in OUR kernel about the candidate's subject operators.

    This is shape 2's screen. It answers "does our development work on this
    mathematics", which is a strictly weaker and strictly more findable
    question than "does our development prove this theorem" -- the question R9
    asks and gets a clean answer to even when a differently-named proof exists.
    """
    env = list(env)
    lowered = [(name, name.lower()) for name in env]
    hits = []
    for constant in sorted(set(subjects)):
        for stem in sorted(_stems(constant)):
            matched = [name for name, low in lowered if stem in low]
            if matched:
                hits.append((stem, matched[0], len(matched)))
    hits.sort(key=lambda h: -h[2])
    return tuple(hits[:limit])


def screen_family(family: str, rows: list[Row],
                  published_rows: dict[str, list[Row]],
                  published_partition: dict[str, str],
                  env: Iterable[str] | None = None,
                  vocabulary_max_rows: int = VOCABULARY_MAX_ROWS) -> Finding:
    """ADR-0653's rule applied to ONE candidate held-out family.

    `published_rows` must NOT contain `family` itself: a family is trivially
    adjacent to its own mathematics, and a screen that scores a family against
    itself refuses every draw, which is the failure mode this whole exercise
    exists to avoid.
    """
    if family in published_rows:
        raise ValueError(
            f"screen_family: {family!r} is in published_rows; a family scored "
            "against itself is always adjacent and the screen becomes vacuous")

    plumb = plumbing({**published_rows, family: rows})
    my_topics = frozenset().union(*(topics(r.module) for r in rows)) if rows else frozenset()
    my_subjects = subject_constants(rows, plumb)

    topic_hits: list = []
    vocabulary_owner: dict[str, str] = {}
    for other, other_rows in sorted(published_rows.items()):
        if published_partition.get(other) not in ("development", "train"):
            continue
        other_topics = frozenset().union(*(topics(r.module) for r in other_rows)) \
            if other_rows else frozenset()
        for seg in sorted(my_topics & other_topics):
            topic_hits.append((seg, other))
        for c in sorted(subject_constants(other_rows, plumb)):
            vocabulary_owner.setdefault(c, other)

    hit_rows = 0
    hit_constants: Counter = Counter()
    for row in rows:
        shared = row.constants & set(vocabulary_owner)
        if shared:
            hit_rows += 1
            hit_constants.update(shared)
    vocabulary_hits = tuple(
        (c, vocabulary_owner[c]) for c, _ in hit_constants.most_common(6))

    env_hits = environment_sweep(my_subjects, env or ())

    reasons = []
    if topic_hits:
        shown = ", ".join(f"{seg} (published by {fam})" for seg, fam in topic_hits[:4])
        reasons.append(
            f"topic: its module topic segments are already a development/train "
            f"family's -- {shown}")
    accepted = ADJACENCY_ACCEPTED.get(family)
    allowance = vocabulary_max_rows
    if accepted is not None:
        allowance = max(allowance, int(accepted.get("vocabulary_rows", 0)))
    if hit_rows > allowance:
        shown = ", ".join(f"{c} ({fam})" for c, fam in vocabulary_hits[:4])
        reasons.append(
            f"vocabulary: {hit_rows} of {len(rows)} rows are about constants a "
            f"development/train family publishes (allowance {allowance}) -- {shown}")
    if accepted is not None and accepted.get("vocabulary_rows") not in (None, hit_rows):
        reasons.append(
            f"disclosure: ADJACENCY_ACCEPTED[{family!r}] records "
            f"vocabulary_rows={accepted['vocabulary_rows']} but the live "
            f"measurement is {hit_rows}; the acceptance no longer describes "
            "this draw")

    return Finding(
        family=family,
        verdict="refused" if reasons else "clean",
        topic_hits=tuple(topic_hits),
        vocabulary_rows=hit_rows,
        vocabulary_hits=vocabulary_hits,
        environment_hits=env_hits,
        reasons=tuple(reasons),
    )


def screen_draw(new_families: dict[str, list[Row]],
                new_partition: dict[str, str],
                existing_rows: dict[str, list[Row]],
                existing_partition: dict[str, str],
                env: Iterable[str] | None = None,
                vocabulary_max_rows: int = VOCABULARY_MAX_ROWS) -> list[Finding]:
    """Every NEW held-out family of a draw, screened against what is published.

    Same-draw development/train families are included in the published set: a
    draw that publishes a subject in one partition and holds the same subject
    out in another is exactly the leak, and the same-draw case is not special.
    """
    published = dict(existing_rows)
    partition = dict(existing_partition)
    for fam, rows in new_families.items():
        if new_partition.get(fam) in ("development", "train"):
            published[fam] = rows
            partition[fam] = new_partition[fam]
    out = []
    for fam in sorted(new_families):
        if new_partition.get(fam) != "held-out":
            continue
        out.append(screen_family(fam, new_families[fam], published, partition,
                                 env=env,
                                 vocabulary_max_rows=vocabulary_max_rows))
    return out


def assert_draw_lawful(new_families: dict[str, list[Row]],
                       new_partition: dict[str, str],
                       existing_rows: dict[str, list[Row]],
                       existing_partition: dict[str, str],
                       env: Iterable[str] | None = None) -> list[Finding]:
    findings = screen_draw(new_families, new_partition, existing_rows,
                           existing_partition, env=env)
    refused = [f for f in findings if f.verdict == "refused"]
    if refused:
        detail = "; ".join(f"{f.family}: {' | '.join(f.reasons)}" for f in refused)
        raise RefusalError(
            f"R11 {len(refused)} new held-out family/families publish "
            f"mathematics a development/train family already publishes "
            f"(ADR-0653): {detail}")
    return findings


# --------------------------------------------------------------------------
# entry points
# --------------------------------------------------------------------------
def _draw_membership(refill) -> dict[str, int]:
    """Which draw introduced each family, read from FAMILY_MODULES' own order."""
    text = (ROOT / "scripts/gen-autogenesis-nursery-refill.py").read_text()
    block = text.split("FAMILY_MODULES: dict[str, tuple[str, ...]] = {", 1)[1]
    block = block.split("\nFAMILY_ROUTES", 1)[0]
    draw = 1
    out: dict[str, int] = {}
    for line in block.splitlines():
        m = re.search(r"---\s*draw (\d+)", line)
        if m:
            draw = int(m.group(1))
            continue
        m = re.match(r'\s{4}"([a-z0-9-]+)":', line)
        if m:
            out[m.group(1)] = draw
    return out


def _context():
    refill = load_refill_module()
    rows, partition, counts = resolve_families(refill)
    env = set(refill.load_json(refill.ENV_SNAPSHOT)["declarations"])
    return refill, rows, partition, counts, env


def cmd_check(args) -> int:
    """Gate the COMMITTED manifests: every held-out family, screened."""
    refill, rows, partition, counts, env = _context()
    membership = _draw_membership(refill)
    held = sorted(f for f, p in partition.items() if p == "held-out")
    if not held:
        print("check-holdout-adjacency: zero held-out families; refusing to "
              "report a clean screen over an empty population")
        return 1
    bad = 0
    print(f"population  v1={counts['v1']} extension={counts['extension']} "
          f"unresolved={counts.get('unresolved', 0)} families={len(partition)} "
          f"held_out_families={len(held)}")
    for fam in held:
        others = {f: r for f, r in rows.items() if f != fam}
        # A family is screened against what was published by the time it was
        # drawn -- later draws cannot retroactively contaminate it, and reading
        # them in would refuse the whole standing population.
        mine = membership.get(fam, 0)
        others = {f: r for f, r in others.items() if membership.get(f, 0) <= mine}
        finding = screen_family(fam, rows[fam], others, partition, env=env)
        mark = "REFUSED" if finding.verdict == "refused" else "clean  "
        print(f"  {mark} draw{mine:<2d} {fam:36s} topic={len(finding.topic_hits):2d} "
              f"vocab={finding.vocabulary_rows}/{len(rows[fam])}")
        for reason in finding.reasons:
            print(f"          {reason}")
        bad += finding.verdict == "refused"
    print(f"check-holdout-adjacency: {len(held)} held-out families, {bad} refused")
    return 1 if bad else 0


def cmd_measure(args) -> int:
    """The calibration table: authored draws AND known contaminations."""
    refill, rows, partition, counts, env = _context()
    membership = _draw_membership(refill)
    plumb = plumbing(rows)
    print(f"families={len(rows)} rows={sum(len(r) for r in rows.values())} "
          f"unresolved={counts.get('unresolved', 0)} plumbing={len(plumb)} "
          f"(AMBIENT_FAMILIES={AMBIENT_FAMILIES})")
    print(f"plumbing: {sorted(plumb)}")
    print()
    print(f"{'draw':>4s} {'family':36s} {'part':12s} {'n':>3s} {'topic':>5s} "
          f"{'vocab':>7s}  verdict")
    for fam in sorted(rows, key=lambda f: (membership.get(f, 0), f)):
        mine = membership.get(fam, 0)
        others = {f: r for f, r in rows.items()
                  if f != fam and membership.get(f, 0) <= mine}
        finding = screen_family(fam, rows[fam], others, partition, env=env)
        print(f"{mine:4d} {fam:36s} {partition[fam]:12s} {len(rows[fam]):3d} "
              f"{len(finding.topic_hits):5d} {finding.vocabulary_rows:3d}/"
              f"{len(rows[fam]):<3d}  {finding.verdict}"
              + ("   <- HELD-OUT" if partition[fam] == "held-out" else ""))
    return 0


def _self_test_cases():
    """Fixtures that exercise each guard independently. Mutation-checked."""
    def R(name, module, *consts):
        return Row(name, module, frozenset(consts))

    dev = {
        "pub-gcd": [R(f"Nat.gcd_x{i}", "Mathlib.Data.Nat.GCD.Lemmas",
                      "Nat.gcd", "Eq") for i in range(10)],
    }
    part = {"pub-gcd": "development"}
    # `plumbing` is DERIVED from the nursery, not stoplisted, so a fixture with
    # one family classifies `Eq` as that family's subject and every candidate
    # comes out adjacent. Seven filler families put `Eq` over AMBIENT_FAMILIES,
    # which is what the real 42-family nursery does. Without them the suite
    # tests a degenerate corpus and cannot distinguish the guards.
    for i in range(AMBIENT_FAMILIES + 1):
        fam = f"filler-{i}"
        dev[fam] = [R(f"Filler{i}.t{j}", f"Mathlib.Data.Filler{i}.Basic",
                      f"Filler{i}.op", "Eq") for j in range(10)]
        part[fam] = "development"

    # 1. topic overlap alone (no shared constants at all)
    topical = [R(f"Nat.gcdAlt{i}", "Mathlib.Data.Nat.GCD.Basic", "Nat.zzz", "Eq")
               for i in range(10)]
    # 2. vocabulary overlap alone (different topic, shared subject constant)
    vocab = [R(f"Nat.sf{i}", "Mathlib.Data.Nat.Squarefree", "Nat.gcd", "Eq")
             for i in range(10)]
    # 3. clean: different topic, different constants
    clean = [R(f"Nat.nthRoot{i}", "Mathlib.Analysis.Pow.NthRootLemmas",
               "Nat.nthRoot", "Eq") for i in range(10)]
    # 4. under the vocabulary allowance -- must stay clean
    under = [R(f"Nat.mix{i}", "Mathlib.Data.Nat.Squarefree",
               *(("Nat.gcd", "Eq") if i < VOCABULARY_MAX_ROWS else ("Nat.zzz", "Eq")))
             for i in range(10)]
    return dev, part, {
        "topic": (topical, "refused", "topic"),
        "vocabulary": (vocab, "refused", "vocabulary"),
        "clean": (clean, "clean", None),
        "under-allowance": (under, "clean", None),
    }


def cmd_self_test(args) -> int:
    dev, part, cases = _self_test_cases()
    failures = []
    for label, (rows, want, want_reason) in sorted(cases.items()):
        got = screen_family(f"cand-{label}", rows, dev, part, env=())
        ok = got.verdict == want
        if ok and want_reason:
            ok = any(r.startswith(want_reason) for r in got.reasons)
        print(f"  {'ok  ' if ok else 'FAIL'} {label:16s} verdict={got.verdict} "
              f"topic={len(got.topic_hits)} vocab={got.vocabulary_rows}/{len(rows)} "
              f"reasons={[r.split(':')[0] for r in got.reasons]}")
        if not ok:
            failures.append(label)

    # self-scoring must be refused outright, not silently accepted
    try:
        screen_family("pub-gcd", dev["pub-gcd"], dev, part, env=())
    except ValueError:
        print("  ok   self-scoring   refused with ValueError")
    else:
        print("  FAIL self-scoring   a family scored against itself was accepted")
        failures.append("self-scoring")

    # the environment sweep must have a positive control, or an empty answer
    # from it is indistinguishable from a misaimed query
    hits = environment_sweep({"Nat.gcd"}, ["Nat.gcd", "Nat.gcd_comm", "Nat.add"])
    miss = environment_sweep({"Nat.zzzUnheardOf"}, ["Nat.gcd", "Nat.add"])
    if hits and not miss:
        print(f"  ok   env-sweep      positive={hits[0]} negative={miss}")
    else:
        print(f"  FAIL env-sweep      positive={hits} negative={miss}")
        failures.append("env-sweep")

    print(f"self-test: {len(cases) + 2 - len(failures)} passed, "
          f"{len(failures)} failed {failures}")
    return 1 if failures else 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--measure", action="store_true",
                    help="print the calibration table over every family")
    ap.add_argument("--self-test", action="store_true",
                    help="run the fixture suite (no repository data)")
    args = ap.parse_args(argv)
    if args.self_test:
        return cmd_self_test(args)
    if args.measure:
        return cmd_measure(args)
    return cmd_check(args)


if __name__ == "__main__":
    sys.exit(main())
