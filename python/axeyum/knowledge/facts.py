"""The fact ledger: ``artifacts/facts/*.json``, typed and validator-mirroring.

A fact is the only resource in this repository that carries a formal statement
**and** a status, which is why the self-extension loop consumes it. The two
status axes are deliberate: :attr:`Fact.epistemic_status` is what *we*
established, :attr:`Fact.external_status` is what mathematics knows, and their
disagreement in our favour is :func:`novel` -- the output the project exists to
produce.

:meth:`Fact.validate` mirrors ``scripts/validate-facts.py`` rather than
re-deriving its rules. Same inputs, same verdicts, same message text; the tests
run both over fixture ledgers and compare the error sets exactly. The one thing
this module must never do is disagree with the gate while looking greener.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any

from ._paths import require_dir, resolve_root

# --- constants mirrored from scripts/validate-facts.py -----------------------

ID_RE = re.compile(r"^F:[a-z0-9]+(-[a-z0-9]+)*$")

REQUIRED = frozenset(
    {
        "schema_version",
        "id",
        "title",
        "statement",
        "formal",
        "epistemic_status",
        "depends_on",
        "evidence",
        "provenance",
    }
)
STATUSES = frozenset({"axiom", "proved", "computed", "empirical", "conjectured", "open", "refuted"})
EXTERNAL_STATUSES = frozenset({"proved", "refuted", "conjectured", "open", "unknown"})
#: What the wider literature has settled; asserting one means naming a source.
EXTERNAL_SETTLED = frozenset({"proved", "refuted"})
#: What WE established. Paired with an unsettled external status, this is novelty.
OURS_SETTLED = frozenset({"proved", "computed", "refuted"})
EVIDENCE_KINDS = frozenset(
    {
        "kernel-term",
        "witness-replay",
        "unsat-certificate",
        "cube-cover",
        "cube-tree-cover",
        "exhaustive-enumeration",
        "published-value-replication",
        "bound-citation",
        "instance-pin",
        "claim-ref",
    }
)
CHECK_STATUSES = frozenset({"checked", "replay-only", "not-checked"})
LANGUAGES_ALL = frozenset(
    {"smtlib2", "lean4", "lean4-surface", "axeyum-ir", "cas-term", "certificate-spec"}
)
ROUTES = frozenset(
    {
        "kernel-lean",
        "imported-kernel-lean",
        "smt-term-level",
        "smt-clausal",
        "search-certificate",
        "cas-certificate",
        "none",
    }
)
#: Only this route can deliver axiom-freedom: only there does an empty footprint
#: correspond to a measurable fact about a kernel environment.
AXIOM_FREE_CAPABLE = frozenset({"kernel-lean"})
#: Routes on which the proof term was NOT authored here.
IMPORTED_ROUTES = frozenset({"imported-kernel-lean"})
#: A status that asserts the statement was settled must be backed by something.
ESTABLISHED = frozenset({"proved", "computed", "refuted"})

_SMTCOMP_ASSERTION_RE = re.compile(r"\btest\b|\bgrep\b|\[\[?")


# --- typed rows --------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Evidence:
    """One evidence row. ``check_status`` is the discriminator that matters."""

    id: str | None
    kind: str | None
    supports: str | None
    check_status: str | None
    checkers: tuple[str, ...]
    artifact: str | None
    checker_command: str | None
    raw: dict[str, Any] = field(repr=False)

    @property
    def is_checked(self) -> bool:
        return self.check_status == "checked"

    @property
    def independently_rederived(self) -> bool:
        """Two or more named checkers re-derived this row (cross-oracle agreement)."""
        return len(self.checkers) >= 2

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> Evidence:
        checkers = raw.get("checkers", [])
        return cls(
            id=raw.get("id"),
            kind=raw.get("kind"),
            supports=raw.get("supports"),
            check_status=raw.get("check_status"),
            checkers=tuple(c for c in checkers if isinstance(c, str))
            if isinstance(checkers, list)
            else (),
            artifact=raw.get("artifact"),
            checker_command=raw.get("checker_command"),
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class Formal:
    """``formal`` is the proposition itself -- unlike a claim, whose ``formal``
    is a generator recipe."""

    language: str | None
    statement: str | None
    fragment: str | None
    free_symbols: tuple[str, ...]
    raw: dict[str, Any] = field(repr=False)

    @classmethod
    def from_raw(cls, raw: Any) -> Formal:
        if not isinstance(raw, dict):
            return cls(None, None, None, (), {})
        symbols = raw.get("free_symbols", [])
        return cls(
            language=raw.get("language"),
            statement=raw.get("statement"),
            fragment=raw.get("fragment"),
            free_symbols=tuple(symbols) if isinstance(symbols, list) else (),
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class Provenance:
    date: str | None
    established_by: str | None
    source: str | None
    prior_art: tuple[Any, ...]
    raw: dict[str, Any] = field(repr=False)

    @classmethod
    def from_raw(cls, raw: Any) -> Provenance:
        if not isinstance(raw, dict):
            return cls(None, None, None, (), {})
        prior = raw.get("prior_art", [])
        return cls(
            date=raw.get("date"),
            established_by=raw.get("established_by"),
            source=raw.get("source"),
            prior_art=tuple(prior) if isinstance(prior, list) else (prior,),
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class Fact:
    """One proposition in ``artifacts/facts/``.

    ``raw`` is kept because :meth:`validate` must see exactly what the canonical
    validator sees, including keys this dataclass does not model.
    """

    id: str
    path: Path
    title: str | None
    statement: str | None
    schema_version: Any
    epistemic_status: str | None
    external_status: str | None
    proof_route: str | None
    axiom_footprint: tuple[str, ...] | None
    depends_on: tuple[str, ...]
    evidence: tuple[Evidence, ...]
    formal: Formal
    provenance: Provenance
    concept_refs: tuple[Any, ...]
    notes: str | None
    supersedes: tuple[str, ...]
    raw: dict[str, Any] = field(repr=False)

    # -- derived views the frontier and the agent care about ------------------

    @property
    def is_settled(self) -> bool:
        """Established here, by any route (``proved``/``computed``/``refuted``)."""
        return self.epistemic_status in ESTABLISHED

    @property
    def is_open(self) -> bool:
        return self.epistemic_status == "open"

    @property
    def checked_evidence_count(self) -> int:
        return sum(1 for ev in self.evidence if ev.is_checked)

    @property
    def is_axiom_free(self) -> bool:
        """``axiom_footprint == []`` on a route where that is measurable.

        An empty footprint on any other route would read as the strongest claim
        the project makes on evidence that cannot support it, so it is not
        accepted here either.
        """
        return self.proof_route in AXIOM_FREE_CAPABLE and self.axiom_footprint == ()

    @property
    def is_imported(self) -> bool:
        """Proof term checked here, authored elsewhere. Not evidence of construction."""
        return self.proof_route in IMPORTED_ROUTES

    @property
    def is_novel(self) -> bool:
        """Established here, not settled in the literature."""
        return self.epistemic_status in OURS_SETTLED and self.external_status in {
            "open",
            "conjectured",
        }

    @property
    def is_import_backlog(self) -> bool:
        """Known to mathematics, not to us. Not a problem for the loop to solve."""
        return self.epistemic_status == "open" and self.external_status == "proved"

    def validate(self, known_ids: set[str] | frozenset[str], root: Path) -> list[str]:
        """Mirror ``validate-facts.py``'s ``validate_one`` for this fact."""
        return validate_one(self.path, self.raw, set(known_ids), root)

    @classmethod
    def from_raw(cls, path: Path, raw: dict[str, Any]) -> Fact:
        footprint = raw.get("axiom_footprint")
        depends = raw.get("depends_on", [])
        evidence = raw.get("evidence", [])
        supersedes = raw.get("supersedes", [])
        refs = raw.get("concept_refs", [])
        return cls(
            id=raw.get("id", f"<{path.name}>"),
            path=path,
            title=raw.get("title"),
            statement=raw.get("statement"),
            schema_version=raw.get("schema_version"),
            epistemic_status=raw.get("epistemic_status"),
            external_status=raw.get("external_status"),
            proof_route=raw.get("proof_route"),
            axiom_footprint=tuple(footprint) if isinstance(footprint, list) else None,
            depends_on=tuple(depends) if isinstance(depends, list) else (),
            evidence=tuple(Evidence.from_raw(ev) for ev in evidence if isinstance(ev, dict))
            if isinstance(evidence, list)
            else (),
            formal=Formal.from_raw(raw.get("formal")),
            provenance=Provenance.from_raw(raw.get("provenance")),
            concept_refs=tuple(refs) if isinstance(refs, list) else (),
            notes=raw.get("notes"),
            supersedes=tuple(supersedes) if isinstance(supersedes, list) else (),
            raw=raw,
        )


# --- the mirrored validator --------------------------------------------------


def validate_one(path: Path, fact: dict[str, Any], known_ids: set[str], root: Path) -> list[str]:
    """A line-for-line mirror of ``validate-facts.py::validate_one``.

    Kept textually identical to the script, including message wording, so a
    difference between the two is a test failure rather than a judgement call.
    """
    errors: list[str] = []
    fid = fact.get("id", f"<{path.name}>")

    missing = set(REQUIRED) - set(fact)
    if missing:
        errors.append(f"{fid}: missing required field(s): {sorted(missing)}")
        return errors

    if not ID_RE.match(fact["id"]):
        errors.append(f"{fid}: id must match ^F:[a-z0-9-]+$")

    expected_name = fact["id"].replace("F:", "F-") + ".json"
    if path.name != expected_name:
        errors.append(f"{fid}: lives in {path.name} but its id implies {expected_name}")

    status = fact["epistemic_status"]
    if status not in STATUSES:
        errors.append(f"{fid}: epistemic_status {status!r} is not one of {sorted(STATUSES)}")

    formal = fact["formal"]
    for key in ("language", "statement", "fragment"):
        if not formal.get(key):
            errors.append(f"{fid}: formal.{key} is required and must be non-empty")
    if formal.get("language") not in LANGUAGES_ALL:
        errors.append(
            f"{fid}: formal.language {formal.get('language')!r} not in {sorted(LANGUAGES_ALL)}"
        )
    if formal.get("language") == "certificate-spec":
        statement = formal.get("statement", "")
        try:
            certificate_spec = json.loads(statement)
        except json.JSONDecodeError as error:
            errors.append(f"{fid}: certificate-spec statement is not valid JSON: {error}")
        else:
            if not isinstance(certificate_spec, dict):
                errors.append(f"{fid}: certificate-spec statement must be a JSON object")
            elif statement != json.dumps(
                certificate_spec, sort_keys=True, separators=(",", ":"), ensure_ascii=False
            ):
                errors.append(f"{fid}: certificate-spec statement must use canonical JSON")
            elif (
                not isinstance(certificate_spec.get("format"), str)
                or not certificate_spec["format"].strip()
            ):
                errors.append(f"{fid}: certificate-spec requires a non-empty string format")
            elif (
                not isinstance(certificate_spec.get("version"), int)
                or isinstance(certificate_spec.get("version"), bool)
                or certificate_spec["version"] <= 0
            ):
                errors.append(f"{fid}: certificate-spec requires a positive integer version")

    for dep in fact["depends_on"]:
        if not ID_RE.match(dep):
            errors.append(f"{fid}: depends_on entry {dep!r} is not a fact id")
        elif dep not in known_ids:
            errors.append(
                f"{fid}: depends_on {dep} does not exist -- a dependency DAG "
                f"with dangling edges is not a build order"
            )

    checked = 0
    for ev in fact["evidence"]:
        for key in ("id", "kind", "supports", "check_status"):
            if key not in ev:
                errors.append(f"{fid}: evidence row missing {key!r}")
        if ev.get("kind") not in EVIDENCE_KINDS:
            errors.append(
                f"{fid}: evidence kind {ev.get('kind')!r} not in {sorted(EVIDENCE_KINDS)}"
            )
        if ev.get("check_status") not in CHECK_STATUSES:
            errors.append(f"{fid}: evidence check_status {ev.get('check_status')!r} is unknown")
        if ev.get("check_status") == "checked":
            checked += 1
        for c in ev.get("checkers", []):
            if not isinstance(c, str) or not c.strip():
                errors.append(f"{fid}: evidence.checkers entries must be non-empty names")
        # A checker is only worth its exit status: `smtcomp_cli --evidence` exits
        # 0 on ANY decided verdict, so a bare invocation proves the binary ran.
        cmd = ev.get("checker_command") or ""
        if "smtcomp_cli" in cmd and not _SMTCOMP_ASSERTION_RE.search(cmd):
            errors.append(
                f"{fid}: checker_command invokes smtcomp_cli without asserting a "
                f"verdict. It exits 0 on sat AND unsat, so as written it checks "
                f"that the binary ran. Wrap it, e.g. "
                f'test "$(... | tail -1)" = unsat'
            )
        if ev.get("kind") == "claim-ref":
            art = ev.get("artifact")
            if not art:
                errors.append(f"{fid}: claim-ref evidence must name the claim in `artifact`")
            elif not (root / art).is_file():
                errors.append(f"{fid}: claim-ref points at {art}, which does not exist")

    # --- the semantic rules ---
    if status in ESTABLISHED and checked == 0:
        errors.append(
            f"{fid}: status {status!r} asserts the statement was settled, but no "
            f"evidence row is `checked`. A status with nothing establishing it is "
            f"the defect this ledger exists to prevent."
        )

    if status == "proved" and "axiom_footprint" not in fact:
        errors.append(
            f"{fid}: status `proved` requires axiom_footprint. An EMPTY array means "
            f"axiom-free and is a stronger claim than an absent field, so absence "
            f"must not read as the strong case."
        )

    if status == "open" and fact["evidence"]:
        errors.append(
            f"{fid}: status `open` must carry an empty evidence array -- an open fact "
            f"with evidence is a contradiction, and the empty array is a statement."
        )

    route = fact.get("proof_route")
    if route is not None and route not in ROUTES:
        errors.append(f"{fid}: proof_route {route!r} is not one of {sorted(ROUTES)}")
    if status in ESTABLISHED and route is None:
        errors.append(
            f"{fid}: status {status!r} requires a proof_route. axiom_footprint is "
            f"only comparable WITHIN a route, so a settled fact that does not say "
            f"which machine settled it makes its own footprint unreadable."
        )
    if route in ROUTES and route not in AXIOM_FREE_CAPABLE and fact.get("axiom_footprint") == []:
        errors.append(
            f"{fid}: axiom_footprint [] on proof_route {route!r}. An empty footprint "
            f"asserts axiom-freedom, which only {sorted(AXIOM_FREE_CAPABLE)} can "
            f"deliver -- there it means a kernel environment admits no Axiom, Opaque "
            f"or Quotient. On any other route it names semantic assumptions that are "
            f"real and cannot be empty, so [] would read as the strongest claim the "
            f"project makes on evidence that cannot support it."
        )

    if route in IMPORTED_ROUTES and not fact["provenance"].get("prior_art"):
        errors.append(
            f"{fid}: proof_route {route!r} means the proof term was authored "
            f"elsewhere, so provenance.prior_art must name who authored it. "
            f"An import that reads as a local proof is the failure this route "
            f"exists to prevent."
        )

    external = fact.get("external_status")
    if external is not None:
        if external not in EXTERNAL_STATUSES:
            errors.append(
                f"{fid}: external_status {external!r} is not one of {sorted(EXTERNAL_STATUSES)}"
            )
        elif (
            external in EXTERNAL_SETTLED
            and status not in OURS_SETTLED
            and not fact["provenance"].get("prior_art")
        ):
            errors.append(
                f"{fid}: this fact is {status!r} to us but external_status "
                f"{external!r}, so the LITERATURE is the only thing holding it up "
                f"-- provenance.prior_art must name who settled it. (When we have "
                f"established a fact ourselves, external_status is corroborative "
                f"and needs no citation; the risk is relying on an unverified "
                f"claim about the literature, which is how this project came to "
                f"cite Zenodo self-deposits as refereed results.)"
            )

    return errors


# --- the ledger --------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class FactLedger:
    """Every fact under ``artifacts/facts/``, read once.

    An empty :attr:`facts` here always means the directory existed and held no
    ``*.json``; a missing directory raises :class:`FileNotFoundError` in
    :func:`load`.
    """

    root: Path
    directory: Path
    facts: tuple[Fact, ...]
    parse_errors: tuple[str, ...]

    def __len__(self) -> int:
        return len(self.facts)

    def __iter__(self):
        return iter(self.facts)

    @property
    def ids(self) -> frozenset[str]:
        return frozenset(f.id for f in self.facts)

    def get(self, fact_id: str) -> Fact:
        """Return one fact.

        Raises:
            KeyError: when no such fact exists. An accessor asked about a subject
                it cannot find must not answer as though it had looked and found
                nothing (principle 4).
        """
        for fact in self.facts:
            if fact.id == fact_id:
                return fact
        raise KeyError(f"no fact {fact_id!r} under {self.directory}")

    def by_status(self) -> dict[str, tuple[Fact, ...]]:
        """Group by ``epistemic_status`` -- what *we* established."""
        grouped: dict[str, list[Fact]] = {}
        for fact in self.facts:
            grouped.setdefault(fact.epistemic_status or "?", []).append(fact)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def status_counts(self) -> dict[str, int]:
        return {k: len(v) for k, v in self.by_status().items()}

    def by_external_status(self) -> dict[str, tuple[Fact, ...]]:
        """Group by ``external_status`` -- what mathematics knows. Absent is ``None``."""
        grouped: dict[str, list[Fact]] = {}
        for fact in self.facts:
            grouped.setdefault(fact.external_status or "<absent>", []).append(fact)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def novel(self) -> tuple[Fact, ...]:
        """Established here, not settled in the literature. Reported, never failed."""
        return tuple(sorted((f for f in self.facts if f.is_novel), key=lambda f: f.id))

    def import_backlog(self) -> tuple[Fact, ...]:
        """Settled elsewhere but not here."""
        return tuple(sorted((f for f in self.facts if f.is_import_backlog), key=lambda f: f.id))

    def route_counts(self) -> dict[str, int]:
        counts: dict[str, int] = {}
        for fact in self.facts:
            if fact.proof_route:
                counts[fact.proof_route] = counts.get(fact.proof_route, 0) + 1
        return dict(sorted(counts.items()))

    def axiom_free(self) -> tuple[Fact, ...]:
        """Axiom-free, counted only on the route where that is measurable."""
        return tuple(f for f in self.facts if f.is_axiom_free)

    def validate(self) -> list[str]:
        """Every error ``validate-facts.py`` would report, in the same order."""
        errors: list[str] = list(self.parse_errors)
        seen: dict[str, Fact] = {}
        for fact in self.facts:
            fid = fact.raw.get("id")
            if fid in seen:
                errors.append(f"{fid}: duplicate id, also in {seen[fid].path.name}")
            elif fid:
                seen[fid] = fact
        known = set(seen)
        for fact in self.facts:
            errors.extend(validate_one(fact.path, fact.raw, known, self.root))
        return errors

    def is_valid(self) -> bool:
        return not self.validate()


@lru_cache(maxsize=8)
def _load_cached(root_key: str) -> FactLedger:
    root = Path(root_key)
    directory = require_dir(root / "artifacts" / "facts")
    facts: list[Fact] = []
    parse_errors: list[str] = []
    for path in sorted(directory.glob("*.json")):
        try:
            raw = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            parse_errors.append(f"{path.name}: not valid JSON: {exc}")
            continue
        facts.append(Fact.from_raw(path, raw))
    return FactLedger(
        root=root,
        directory=directory,
        facts=tuple(facts),
        parse_errors=tuple(parse_errors),
    )


def load(root: Path | str | None = None, *, refresh: bool = False) -> FactLedger:
    """Read the whole ledger. Cached per root; ``refresh=True`` re-reads."""
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
    return _load_cached(str(resolved))


def get(fact_id: str, root: Path | str | None = None) -> Fact:
    """One fact by id; :class:`KeyError` when absent."""
    return load(root).get(fact_id)


def by_status(root: Path | str | None = None) -> dict[str, tuple[Fact, ...]]:
    return load(root).by_status()


def novel(root: Path | str | None = None) -> tuple[Fact, ...]:
    return load(root).novel()


def validate(root: Path | str | None = None) -> list[str]:
    return load(root).validate()


__all__ = [
    "AXIOM_FREE_CAPABLE",
    "CHECK_STATUSES",
    "ESTABLISHED",
    "EVIDENCE_KINDS",
    "EXTERNAL_SETTLED",
    "EXTERNAL_STATUSES",
    "ID_RE",
    "IMPORTED_ROUTES",
    "LANGUAGES_ALL",
    "OURS_SETTLED",
    "REQUIRED",
    "ROUTES",
    "STATUSES",
    "Evidence",
    "Fact",
    "FactLedger",
    "Formal",
    "Provenance",
    "by_status",
    "get",
    "load",
    "novel",
    "validate",
    "validate_one",
]
