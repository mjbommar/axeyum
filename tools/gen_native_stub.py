#!/usr/bin/env python3
"""The NAME and ARITY drift gate between the built extension and its stubs.

``python/axeyum/_native/**/__init__.pyi`` is now generated from the RUST
signatures by ``cargo run -p axeyum-py --features stub-gen --bin stub_gen``
(``pyo3-stub-gen``), not by introspecting the built module. That is what makes
the stubs *typed*; it also means nothing in the generator's own pipeline ever
looks at the extension that actually gets imported. Two things can therefore be
wrong at once and neither tool notices:

* a name reaches Python through a runtime call the macros cannot see --
  ``module.add("MAX_BV_WIDTH", ...)``, an ``add_submodule``, an alias -- so it
  exists in the ``.so`` and in no stub;
* a ``#[gen_stub_pyfunction(module = "...")]`` names a module the function is
  not registered in, so the stub describes a symbol that is not there.

This script is what compares the two. It walks the IMPORTED module, walks the
COMMITTED stubs, and requires that they describe the same names with the same
parameter names in the same order. **It ignores annotations entirely** --
``tools/check_stub_types.py`` is the gate for those, and keeping the two
separate means a type improvement cannot mask a name regression.

This file used to *generate* an all-``Any`` stub package by introspection.
Nothing does that any more; the previous role is gone, the drift check it
carried is not.

Three comparisons are deliberately weaker, because PyO3 controls the runtime
spelling and a Rust parameter name is not observable:

* ``__new__``/``__init__``: PyO3 leaves ``__new__`` as ``(*args, **kwargs)``
  and puts the real ``#[new]`` signature on the CLASS's
  ``__text_signature__``, so the stub's ``__init__`` is compared against that.
* Every other dunder: CPython's slot wrappers name their argument by the C
  convention (``value``, ``key``), never the Rust one, and the arguments are
  positional-only. Arity is compared; names are not.
* An alias -- a module attribute that IS the same object as another attribute
  already covered -- is reported, not required. ``ir.bv.lower_terms_py`` is a
  second binding of ``ir.bv.lower_terms``, not a second function.

Usage::

    uv run --no-sync python tools/gen_native_stub.py --check
    uv run --no-sync python tools/gen_native_stub.py            # same, verbose

Prints ``STUBS|modules=M|symbols=S|aliases=A`` and exits 1 on any drift **or**
on having compared zero symbols. The second guard is the one this repository
keeps paying for: a gate that examines nothing and exits 0 is worse than no
gate (a corpus sweep printed "running 0 tests ... ok" for 15 days).
"""

from __future__ import annotations

import argparse
import ast
import sys
import types
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
PYTHON_ROOT = REPO_ROOT / "python"

# Names on a module object that are Python's, not ours.
MODULE_DUNDERS = frozenset(
    {"__doc__", "__loader__", "__name__", "__package__", "__spec__", "__file__", "__all__"}
)

# Members every `#[pyclass]` inherits or that PyO3 stamps on; a stub that omits
# them is not drift.
IGNORED_CLASS_MEMBERS = frozenset(
    {
        "__doc__",
        "__module__",
        "__dict__",
        "__weakref__",
        "__text_signature__",
        "__getattribute__",
        "__setattr__",
        "__delattr__",
        "__init_subclass__",
        "__subclasshook__",
        "__class__",
        "__new__",
        "__init__",
    }
)


def split_signature(text: str) -> list[str]:
    """Top-level comma split of a ``__text_signature__`` body."""
    parts: list[str] = []
    depth = 0
    current: list[str] = []
    for character in text:
        if character in "([{":
            depth += 1
        elif character in ")]}":
            depth -= 1
        if character == "," and depth == 0:
            parts.append("".join(current).strip())
            current = []
        else:
            current.append(character)
    tail = "".join(current).strip()
    if tail:
        parts.append(tail)
    return parts


def runtime_parameters(signature: str | None) -> list[str] | None:
    """Parameter names from a ``__text_signature__``; None when PyO3 omitted it."""
    if signature is None:
        return None
    inner = signature.strip()
    if inner.startswith("(") and inner.endswith(")"):
        inner = inner[1:-1]
    names: list[str] = []
    for raw in split_signature(inner):
        if raw in ("/", "*") or raw.startswith("$"):
            continue
        raw = raw.lstrip("*")
        names.append(raw.split("=")[0].split(":")[0].strip())
    return names


def stub_parameters(node: ast.FunctionDef | ast.AsyncFunctionDef) -> list[str]:
    """Parameter names from a stub ``def``, receiver dropped."""
    arguments = node.args
    every = [
        *arguments.posonlyargs,
        *arguments.args,
        *([arguments.vararg] if arguments.vararg else []),
        *arguments.kwonlyargs,
        *([arguments.kwarg] if arguments.kwarg else []),
    ]
    names = [argument.arg for argument in every]
    if names and names[0] in ("self", "cls"):
        names = names[1:]
    return names


def is_dunder(name: str) -> bool:
    return name.startswith("__") and name.endswith("__")


class Drift:
    """Accumulates findings so the report names every one, not just the first."""

    def __init__(self) -> None:
        self.problems: list[str] = []
        self.symbols = 0
        self.aliases: list[str] = []
        self.artifacts: list[str] = []

    def report(self, message: str) -> None:
        self.problems.append(message)


def stub_path(module_name: str) -> Path:
    return PYTHON_ROOT / Path(*module_name.split(".")) / "__init__.pyi"


def walk_modules(module: types.ModuleType, name: str, found: dict[str, types.ModuleType]) -> None:
    found[name] = module
    for key, value in vars(module).items():
        if isinstance(value, types.ModuleType) and value.__name__.startswith("axeyum._native"):
            walk_modules(value, f"{name}.{key}", found)


def compare_callable(
    drift: Drift, where: str, runtime_object: object, node: ast.FunctionDef, *, arity_only: bool
) -> None:
    signature = getattr(runtime_object, "__text_signature__", None)
    expected = runtime_parameters(signature)
    if expected is None:
        # PyO3 omits the signature for some slots; there is nothing to compare
        # against, and inventing a comparison would be worse than none.
        return
    drift.symbols += 1
    actual = stub_parameters(node)
    if arity_only:
        if len(expected) != len(actual):
            drift.report(
                f"{where}: runtime takes {len(expected)} argument(s), stub takes {len(actual)}"
            )
        return
    if expected != actual:
        drift.report(f"{where}: runtime parameters {expected}, stub {actual}")


def check_class(drift: Drift, module_name: str, name: str, cls: type, node: ast.ClassDef) -> None:
    members = vars(cls)
    stub_members: dict[str, ast.FunctionDef] = {}
    stub_attributes: set[str] = set()
    for statement in node.body:
        if isinstance(statement, ast.FunctionDef):
            stub_members[statement.name] = statement
        elif isinstance(statement, ast.AnnAssign) and isinstance(statement.target, ast.Name):
            stub_attributes.add(statement.target.id)
        elif isinstance(statement, ast.Assign):
            # A simple `#[pyclass(eq, eq_int)]` enum's variants come out as
            # `Certified = ...`, an Assign, not an AnnAssign.
            stub_attributes |= {t.id for t in statement.targets if isinstance(t, ast.Name)}
        elif isinstance(statement, ast.ClassDef):
            stub_attributes.add(statement.name)

    # The `#[new]` signature lives on the class, not on `__new__`.
    constructor = stub_members.get("__init__") or stub_members.get("__new__")
    if constructor is not None:
        compare_callable(
            drift, f"{module_name}.{name}.__init__", cls, constructor, arity_only=False
        )

    for member_name, member in sorted(members.items()):
        if member_name in IGNORED_CLASS_MEMBERS:
            continue
        if member_name.startswith("_") and not is_dunder(member_name):
            continue
        if member_name not in stub_members and member_name not in stub_attributes:
            if is_dunder(member_name):
                # PyO3 and CPython synthesise dunders the Rust never wrote: the
                # five ordering slots on every `#[pyclass]`, `__ne__` from
                # `__eq__`, and a reflected `__rX__` for every `__X__` (one
                # `nb_*` slot serves both operand orders). The interpreter
                # resolves these through the slot, so a stub that omits one
                # loses precision and never correctness. Reported, not failed.
                drift.artifacts.append(f"{module_name}.{name}.{member_name}")
                continue
            drift.report(f"{module_name}.{name}.{member_name}: on the class, absent from the stub")
            continue
        node_member = stub_members.get(member_name)
        if node_member is None or not callable(member):
            continue
        if type(member).__name__ in ("getset_descriptor", "member_descriptor"):
            continue
        compare_callable(
            drift,
            f"{module_name}.{name}.{member_name}",
            member,
            node_member,
            arity_only=is_dunder(member_name),
        )

    for member_name in sorted(stub_members) + sorted(stub_attributes):
        if member_name in ("__init__", "__new__") or member_name in members:
            continue
        if issubclass(cls, BaseException):
            # An exception's payload is attached with `setattr` at the RAISE
            # site (`Declined.reason`, `KernelError.variant`), so it exists on
            # the instance and never on the class. It is declared in the stub
            # deliberately -- see `crate::stub_info::stub_exception!` -- and
            # `ty` reported it as an unresolved attribute until it was.
            drift.artifacts.append(f"{module_name}.{name}.{member_name} (raise-time payload)")
            continue
        if is_dunder(member_name):
            # PyO3 compiles some dunders into a type slot rather than into a
            # same-named attribute: `#[pymethods] fn __getattr__` becomes
            # `tp_getattro`, which Python surfaces as `__getattribute__`. The
            # stub names the protocol the class actually implements.
            drift.artifacts.append(f"{module_name}.{name}.{member_name} (slot-only)")
            continue
        drift.report(f"{module_name}.{name}.{member_name}: in the stub, absent from the class")


def check_module(drift: Drift, module_name: str, module: types.ModuleType) -> None:
    path = stub_path(module_name)
    if not path.is_file():
        drift.report(f"{module_name}: no stub at {path.relative_to(REPO_ROOT)}")
        return
    tree = ast.parse(path.read_text(encoding="utf-8"))
    stub_functions = {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef)}
    stub_classes = {n.name: n for n in tree.body if isinstance(n, ast.ClassDef)}
    stub_names = set(stub_functions) | set(stub_classes)
    for statement in tree.body:
        if isinstance(statement, ast.AnnAssign) and isinstance(statement.target, ast.Name):
            stub_names.add(statement.target.id)
        elif isinstance(statement, ast.Assign):
            stub_names |= {t.id for t in statement.targets if isinstance(t, ast.Name)}
        elif isinstance(statement, ast.ImportFrom):
            stub_names |= {alias.asname or alias.name for alias in statement.names}

    members = {
        key: value
        for key, value in vars(module).items()
        if not isinstance(value, types.ModuleType)
        and (not key.startswith("_") or key == "__version__")
        and key not in MODULE_DUNDERS
    }

    for key, value in sorted(members.items()):
        if key in stub_names:
            drift.symbols += 1
            continue
        twin = next(
            (
                other
                for other, obj in sorted(members.items())
                if obj is value and other in stub_names
            ),
            None,
        )
        if twin is not None:
            drift.aliases.append(f"{module_name}.{key} -> {twin}")
            continue
        drift.report(f"{module_name}.{key}: in the extension, absent from the stub")

    for name, node in sorted(stub_functions.items()):
        target = members.get(name)
        if target is None:
            drift.report(f"{module_name}.{name}: in the stub, absent from the extension")
            continue
        compare_callable(drift, f"{module_name}.{name}", target, node, arity_only=is_dunder(name))

    for name, node in sorted(stub_classes.items()):
        target = members.get(name)
        if target is None:
            drift.report(f"{module_name}.{name}: in the stub, absent from the extension")
            continue
        if isinstance(target, type):
            check_class(drift, module_name, name, target, node)


def run() -> Drift:
    import axeyum._native as native

    modules: dict[str, types.ModuleType] = {}
    walk_modules(native, "axeyum._native", modules)
    drift = Drift()
    for name, module in sorted(modules.items()):
        check_module(drift, name, module)
    drift.module_count = len(modules)  # type: ignore[attr-defined]
    return drift


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="kept for the callers that pass it; the script only ever checks",
    )
    parser.add_argument("--quiet", action="store_true", help="do not list the aliases")
    parser.add_argument(
        "--show",
        action="store_true",
        help="also list every dunder PyO3 or CPython synthesised, and every "
        "raise-time exception payload the stub declares",
    )
    args = parser.parse_args(argv)

    drift = run()
    modules = getattr(drift, "module_count", 0)
    print(
        f"STUBS|modules={modules}|symbols={drift.symbols}"
        f"|aliases={len(drift.aliases)}|synthesised_dunders={len(drift.artifacts)}"
    )

    if not args.quiet:
        for alias in drift.aliases:
            print(f"  alias: {alias}")
    if args.show:
        for artifact in drift.artifacts:
            print(f"  synthesised: {artifact}")

    failed = False
    if drift.problems:
        print("stub drift against the built extension:", file=sys.stderr)
        for problem in drift.problems:
            print(f"  {problem}", file=sys.stderr)
        print(
            "regenerate with:\n"
            "  uv run --no-sync maturin develop\n"
            "  cargo run -p axeyum-py --features stub-gen --bin stub_gen",
            file=sys.stderr,
        )
        failed = True
    if drift.symbols == 0:
        print(
            "STUBS|FAIL symbols=0 -- nothing was compared; a check that examined "
            "nothing is not a pass",
            file=sys.stderr,
        )
        failed = True
    if failed:
        print(f"STUBS|FAIL symbols={drift.symbols} problems={len(drift.problems)}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
