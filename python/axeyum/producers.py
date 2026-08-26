"""``axeyum.producers`` (tier P) -- untrusted, bounded proof producers.

Everything here *searches*. Nothing here decides. A producer returns a candidate
proof term and the **same kernel** then re-checks it through
:meth:`axeyum.kernel.Kernel.add_declaration`; a producer that returns a wrong
term produces a kernel rejection, never an admitted theorem. That is why these
functions are reachable from Python at all -- no call here can admit a fact,
write a ledger, or change an axiom footprint.

Three rules are carried across the language boundary verbatim.

**``declined`` is a typed value.** :class:`DeclineReason` carries the producer's
own Rust enum variant as ``.kind`` and its payload as ``.detail``; it is never
flattened to a string or a bool. It is *delivered* on :class:`Declined`, an
exception, because a decline has no candidate to return and ``None`` would erase
exactly the typed reason the enum exists to preserve. Catch :class:`Declined`,
read ``.reason``, branch on ``.kind`` -- never on the message text.

**Budgets are pinned constants, never keyword defaults.** :data:`MAX_BINDERS` is
part of five settled facts' reproduction contract: every
``mathlib-bounded-induction-family-*`` manifest pins ``max_binders: 8`` and
``scripts/check-autogenesis-bounded-induction-family.py`` refuses a mismatch
*even when every ``proof_sha256`` is byte-identical*. Raising it to 12 was
reverted within the hour for that reason. There is no argument through which
Python can change it.

**Handles belong to one kernel.** Every ``ExprId``/``NameId`` here is the
``axeyum.kernel`` handle carrying its kernel's epoch, checked on every consuming
call. A goal from another kernel raises ``EpochError`` rather than silently
denoting a different term.

The producers' candidate classes are deliberately distinct types: they measure different
quantities against different budgets, and one class with ``inductions_used =
None`` would make "this producer performs no inductions" indistinguishable from
"nobody measured".
"""

from __future__ import annotations

from ._native.producers import (
    APPLICATION_MAX_BINDERS,
    APPLICATION_MAX_DEPTH,
    APPLICATION_MAX_TERMS,
    FORMAT_VERSION,
    IDENTITY_VERSION,
    MAX_BINDERS,
    MAX_INDUCTIONS,
    MODEQ_MAX_BINDERS,
    ApplicationCandidate,
    AxiomIdentity,
    Candidate,
    CircularityAudit,
    DeclarationDependency,
    DeclarationIdentity,
    Declined,
    DeclineReason,
    ImportLimits,
    ImportReport,
    ModEqCandidate,
    StatementImport,
    StatementImportError,
    audit_circularity,
    import_candidate_statement_ndjson,
    import_statement_ndjson,
    propose_bounded_application,
    propose_bounded_induction,
    propose_modeq_family,
)

__all__ = [
    "APPLICATION_MAX_BINDERS",
    "APPLICATION_MAX_DEPTH",
    "APPLICATION_MAX_TERMS",
    "FORMAT_VERSION",
    "IDENTITY_VERSION",
    "MAX_BINDERS",
    "MAX_INDUCTIONS",
    "MODEQ_MAX_BINDERS",
    "ApplicationCandidate",
    "AxiomIdentity",
    "Candidate",
    "CircularityAudit",
    "DeclarationDependency",
    "DeclarationIdentity",
    "DeclineReason",
    "Declined",
    "ImportLimits",
    "ImportReport",
    "ModEqCandidate",
    "StatementImport",
    "StatementImportError",
    "audit_circularity",
    "import_candidate_statement_ndjson",
    "import_statement_ndjson",
    "propose_bounded_application",
    "propose_bounded_induction",
    "propose_modeq_family",
]
