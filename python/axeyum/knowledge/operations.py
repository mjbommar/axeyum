"""The Autogenesis producer/checker operation registry.

The measurement that shapes this module: of 26 registered operations, 24 name
exactly one fact in ``applicability.fact_ids``. A registry where every entry
names one target is a **dispatch table, not a producer**, and it cannot fail to
"produce" -- the checker-that-cannot-fail defect moved one arrow upstream. So
:attr:`Operation.n_targets` and :attr:`Operation.is_multi_target` are derived
from ``applicability.fact_ids`` and from nothing else: never from a label an
operation carries, never from its id, never from its scope.

``EXECUTION_DRIVERS`` is read out of ``scripts/validate-autogenesis-operations.py``
at import time rather than copied. A copied allowlist is a second source of
truth that drifts silently, and the drift is invisible until an operation is
accepted here that the gate would reject.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
from typing import Any

from ._paths import load_script_module, read_json, resolve_root

REGISTRY_PATH = Path("artifacts") / "autogenesis" / "operations.json"
VALIDATOR = "validate-autogenesis-operations.py"

#: Registry scopes. ``counterfactual-fixture-only`` operations exist to exercise
#: the machinery and must never admit anything.
SCOPES = frozenset({"authoritative", "counterfactual-fixture-only"})


@lru_cache(maxsize=4)
def _validator_module(root_key: str) -> Any:
    return load_script_module(Path(root_key), VALIDATOR, "_axeyum_validate_autogenesis_operations")


def execution_drivers(root: Path | str | None = None) -> frozenset[str]:
    """The driver allowlist, read from the canonical validator (9 members today)."""
    module = _validator_module(str(resolve_root(root)))
    return frozenset(module.EXECUTION_DRIVERS)


def admission_contracts(root: Path | str | None = None) -> frozenset[tuple[str, ...]]:
    """The allowed ``(epistemic_status, proof_route, evidence_kind, footprint_policy)``
    tuples, read from the canonical validator."""
    module = _validator_module(str(resolve_root(root)))
    return frozenset(tuple(contract) for contract in module.ADMISSION_CONTRACTS)


def sealed_capsule_contracts(root: Path | str | None = None) -> dict[str, dict[str, Any]]:
    """Per-fact sealed-capsule pins, read from the canonical validator."""
    module = _validator_module(str(resolve_root(root)))
    return dict(module.SEALED_CAPSULE_CONTRACTS)


@dataclass(frozen=True, slots=True)
class Applicability:
    """What an operation claims to be able to handle."""

    fact_ids: tuple[str, ...]
    formal_languages: tuple[str, ...]
    fragments: tuple[str, ...]


@dataclass(frozen=True, slots=True)
class Stage:
    """One half of a producer/checker pair."""

    operation: str | None
    implementation: str | None
    input_kind: str | None
    output_kind: str | None

    @classmethod
    def from_raw(cls, raw: Any) -> Stage:
        if not isinstance(raw, dict):
            return cls(None, None, None, None)
        return cls(
            operation=raw.get("operation"),
            implementation=raw.get("implementation"),
            input_kind=raw.get("input_kind"),
            output_kind=raw.get("output_kind"),
        )


@dataclass(frozen=True, slots=True)
class Admission:
    """What admitting this operation's output would assert about a fact."""

    epistemic_status: str | None
    proof_route: str | None
    evidence_kind: str | None
    axiom_footprint_policy: str | None
    axiom_footprint: tuple[str, ...] | None

    @property
    def contract(self) -> tuple[str | None, str | None, str | None, str | None]:
        return (
            self.epistemic_status,
            self.proof_route,
            self.evidence_kind,
            self.axiom_footprint_policy,
        )

    @classmethod
    def from_raw(cls, raw: Any) -> Admission:
        if not isinstance(raw, dict):
            return cls(None, None, None, None, None)
        footprint = raw.get("axiom_footprint")
        return cls(
            epistemic_status=raw.get("epistemic_status"),
            proof_route=raw.get("proof_route"),
            evidence_kind=raw.get("evidence_kind"),
            axiom_footprint_policy=raw.get("axiom_footprint_policy"),
            axiom_footprint=tuple(footprint) if isinstance(footprint, list) else None,
        )


@dataclass(frozen=True, slots=True)
class Executor:
    """How the operation is actually run, when it is runnable at all."""

    driver: str | None
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    def __bool__(self) -> bool:
        return bool(self.raw)


@dataclass(frozen=True, slots=True)
class Operation:
    """One registered operation."""

    id: str
    scope: str
    applicability: Applicability
    producer: Stage
    checker: Stage
    admission: Admission
    executor: Executor
    reviewed_gate_mentions: tuple[str, ...]
    raw: dict[str, Any] = field(repr=False, default_factory=dict)

    @property
    def n_targets(self) -> int:
        """How many facts this operation claims. Derived from
        ``applicability.fact_ids`` and nothing else."""
        return len(self.applicability.fact_ids)

    @property
    def is_multi_target(self) -> bool:
        """True when the operation is a producer rather than a dispatch row.

        ``fact_ids`` is a list and nothing ever required length one; an entry of
        length one is a table row that cannot fail to produce.
        """
        return self.n_targets > 1

    @property
    def is_authoritative(self) -> bool:
        return self.scope == "authoritative"

    @property
    def is_executable(self) -> bool:
        """The operation names an executor driver."""
        return self.executor.driver is not None

    def targets(self, fact_id: str) -> bool:
        return fact_id in self.applicability.fact_ids

    @classmethod
    def from_raw(cls, raw: dict[str, Any]) -> Operation:
        applicability_raw = raw.get("applicability") or {}
        executor_raw = raw.get("executor") or {}
        return cls(
            id=raw["id"],
            scope=raw.get("scope", ""),
            applicability=Applicability(
                fact_ids=tuple(applicability_raw.get("fact_ids") or ()),
                formal_languages=tuple(applicability_raw.get("formal_languages") or ()),
                fragments=tuple(applicability_raw.get("fragments") or ()),
            ),
            producer=Stage.from_raw(raw.get("producer")),
            checker=Stage.from_raw(raw.get("checker")),
            admission=Admission.from_raw(raw.get("admission")),
            executor=Executor(driver=executor_raw.get("driver"), raw=dict(executor_raw)),
            reviewed_gate_mentions=tuple(raw.get("reviewed_gate_mentions") or ()),
            raw=raw,
        )


@dataclass(frozen=True, slots=True)
class OperationRegistry:
    """``artifacts/autogenesis/operations.json``, typed."""

    root: Path
    path: Path
    schema_version: Any
    kind: str
    operations: tuple[Operation, ...]

    def __len__(self) -> int:
        return len(self.operations)

    def __iter__(self):
        return iter(self.operations)

    def get(self, operation_id: str) -> Operation:
        """One operation; :class:`KeyError` when absent."""
        for op in self.operations:
            if op.id == operation_id:
                return op
        raise KeyError(f"no operation {operation_id!r} in {self.path}")

    def covering(self, fact_id: str) -> tuple[Operation, ...]:
        """Every operation naming this fact. Empty means the registry was read
        and nothing named it."""
        return tuple(op for op in self.operations if op.targets(fact_id))

    def covered_fact_ids(self) -> frozenset[str]:
        return frozenset(fid for op in self.operations for fid in op.applicability.fact_ids)

    def multi_target(self) -> tuple[Operation, ...]:
        """The reusable producers -- the number the programme is actually trying
        to raise."""
        return tuple(op for op in self.operations if op.is_multi_target)

    def by_scope(self) -> dict[str, tuple[Operation, ...]]:
        grouped: dict[str, list[Operation]] = {}
        for op in self.operations:
            grouped.setdefault(op.scope, []).append(op)
        return {k: tuple(v) for k, v in sorted(grouped.items())}

    def drivers_in_use(self) -> frozenset[str]:
        return frozenset(op.executor.driver for op in self.operations if op.executor.driver)

    def unknown_drivers(self) -> frozenset[str]:
        """Drivers used here that the canonical allowlist does not contain."""
        return self.drivers_in_use() - execution_drivers(self.root)


@lru_cache(maxsize=4)
def _load_cached(root_key: str) -> OperationRegistry:
    root = Path(root_key)
    path = root / REGISTRY_PATH
    document = read_json(path)
    return OperationRegistry(
        root=root,
        path=path,
        schema_version=document.get("schema_version"),
        kind=document.get("kind", ""),
        operations=tuple(Operation.from_raw(row) for row in document.get("operations", [])),
    )


def load(root: Path | str | None = None, *, refresh: bool = False) -> OperationRegistry:
    """Read the operation registry. Cached per root."""
    resolved = resolve_root(root)
    if refresh:
        _load_cached.cache_clear()
        _validator_module.cache_clear()
    return _load_cached(str(resolved))


def get(operation_id: str, root: Path | str | None = None) -> Operation:
    return load(root).get(operation_id)


__all__ = [
    "REGISTRY_PATH",
    "SCOPES",
    "VALIDATOR",
    "Admission",
    "Applicability",
    "Executor",
    "Operation",
    "OperationRegistry",
    "Stage",
    "admission_contracts",
    "execution_drivers",
    "get",
    "load",
    "sealed_capsule_contracts",
]
