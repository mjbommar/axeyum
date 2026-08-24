"""The committed ``axeyum._native`` stubs must match the extension that is built.

``axeyum._native`` is a compiled PyO3 ``.so``. No type checker can read it, so
without stubs the entire Python surface is invisible.
``python/axeyum/_native/*.pyi`` supplies that surface, generated from the built
module by ``tools/gen_native_stub.py``.

A stub that drifts is worse than no stub: it makes the checker confidently
wrong about code that changed underneath it. The sibling repository this
generator is ported from paid for that twice -- a hand-written stub of its
native surface produced ~1,400 diagnostics against functions that existed, and
a five-line hand stub of ``pytest`` shadowed the real one for 417 more.

This test is what stops the replacement from going the same way. It
regenerates every stub into a temporary directory from the module that is
actually imported and compares **bytes**, so a Rust signature change cannot
land with a stale stub still describing the old one. Because the Rust surface
is under active development, this test is expected to go red whenever the
extension is rebuilt with a changed API -- that redness is the mechanism, not a
malfunction. The fix is never to edit a ``.pyi`` by hand::

    uv run --no-sync maturin develop
    uv run --no-sync python tools/gen_native_stub.py

Two of the tests below are negative controls on the generator's own ``--check``
mode: one on drift, one on a run that compared nothing. The second exists
because "the gate examined zero things and exited 0" is this repository's most
frequently repeated failure, and a drift checker with no floor has exactly that
shape.
"""

from __future__ import annotations

import importlib.util
import keyword
import sys
import types
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent.parent
GENERATOR = ROOT / "tools" / "gen_native_stub.py"
STUB_PKG = ROOT / "python" / "axeyum" / "_native"

# The extension registers these; a stub package with fewer files than this is
# not a healthy comparison, it is a comparison that mostly did not happen.
MIN_STUBS = 2


def _load_generator() -> types.ModuleType:
    spec = importlib.util.spec_from_file_location("_gen_native_stub", GENERATOR)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def gen() -> types.ModuleType:
    return _load_generator()


@pytest.fixture
def regenerated(gen: types.ModuleType, tmp_path: Path) -> dict[str, bytes]:
    """Write a full stub set into a temp dir; return ``{filename: bytes}``."""
    out = tmp_path / "_native"
    assert gen.main(["--stub-dir", str(out)]) == 0
    return {p.name: p.read_bytes() for p in sorted(out.glob("*.pyi"))}


def test_generator_and_stubs_are_present() -> None:
    """The stubs are generated output; the generator must ship with them."""
    assert GENERATOR.is_file(), f"missing {GENERATOR}"
    assert STUB_PKG.is_dir(), f"missing {STUB_PKG}"


def test_regenerated_stubs_match_the_committed_ones_byte_for_byte(
    regenerated: dict[str, bytes],
) -> None:
    """Regenerate from the imported ``.so`` and require byte equality."""
    assert len(regenerated) >= MIN_STUBS, (
        f"only {len(regenerated)} stub(s) generated; a comparison this small is "
        "not evidence that the surface is described"
    )
    stale: list[str] = []
    for name, expected in sorted(regenerated.items()):
        committed = STUB_PKG / name
        if not committed.exists():
            stale.append(f"{name}: missing from python/axeyum/_native/")
            continue
        actual = committed.read_bytes()
        if actual != expected:
            stale.append(
                f"{name}: {len(actual.splitlines())} lines committed vs "
                f"{len(expected.splitlines())} generated"
            )
    assert not stale, (
        "committed stubs are stale against the built extension:\n  "
        + "\n  ".join(stale)
        + "\n\nregenerate with:\n"
        "  uv run --no-sync maturin develop\n"
        "  uv run --no-sync python tools/gen_native_stub.py"
    )


def test_no_stub_outlives_the_submodule_it_described(
    regenerated: dict[str, bytes],
) -> None:
    """A stub for a submodule the extension no longer exports is drift too."""
    orphans = sorted(p.name for p in STUB_PKG.glob("*.pyi") if p.name not in regenerated)
    assert not orphans, "stub files describe submodules that no longer exist: " + ", ".join(orphans)


def test_public_surface_is_fully_covered(regenerated: dict[str, bytes]) -> None:
    """Every public name on the built module appears in its stub.

    Byte equality above already implies this, but this is the property that
    matters and it fails naming the missing symbol rather than a line count.
    """
    import axeyum._native as native

    def public(obj: object) -> set[str]:
        members = vars(obj)
        return {
            k
            for k, v in members.items()
            if not k.startswith("_") and not isinstance(v, types.ModuleType)
        }

    checks: list[tuple[str, str, set[str]]] = [("axeyum._native", "__init__.pyi", public(native))]
    for name, value in vars(native).items():
        if isinstance(value, types.ModuleType):
            checks.append((f"axeyum._native.{name}", f"{name}.pyi", public(value)))

    missing: list[str] = []
    for mod_name, stub_name, names in checks:
        text = regenerated.get(stub_name, b"").decode()
        for symbol in sorted(names):
            if not symbol.isidentifier() or symbol in keyword.kwlist:
                # Exported under a name Python cannot spell; the generator
                # reports these separately and cannot stub them.
                continue
            if symbol not in text:
                missing.append(f"{mod_name}.{symbol}")
    assert not missing, "stub omits public names: " + ", ".join(missing)


def test_check_mode_passes_on_the_committed_stubs(
    gen: types.ModuleType, capsys: pytest.CaptureFixture[str]
) -> None:
    """``--check`` is what the gate runs; it must agree with the test above."""
    assert gen.main(["--check"]) == 0
    out = capsys.readouterr().out
    assert "STUBS|compared=" in out, out
    compared = int(out.rsplit("STUBS|compared=", 1)[1].split()[0])
    assert compared >= MIN_STUBS, f"--check compared only {compared} stub(s)"


def test_check_mode_fails_on_drift(gen: types.ModuleType, tmp_path: Path) -> None:
    """Negative control: one edited stub must make ``--check`` exit 1.

    Without this, "the checker passes" would be evidence of nothing -- a
    checker that cannot fail is worse than no checker.
    """
    out = tmp_path / "_native"
    assert gen.main(["--stub-dir", str(out)]) == 0
    victim = out / "smt.pyi"
    victim.write_text(victim.read_text() + "def a_signature_that_is_not_in_rust() -> None: ...\n")
    assert gen.main(["--check", "--stub-dir", str(out)]) == 1


def test_check_mode_fails_when_nothing_was_compared(
    gen: types.ModuleType, tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Negative control on the inert-gate floor, independent of the drift path.

    With nothing to generate there is nothing to be stale either, so the drift
    branch is silent and only the ``compared == 0`` floor can fail the run.
    Deleting that floor kills exactly this test.
    """
    monkeypatch.setattr(gen, "_generate", lambda *a, **k: {})
    assert gen.main(["--check", "--stub-dir", str(tmp_path)]) == 1
