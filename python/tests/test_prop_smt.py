"""Hypothesis properties for ``axeyum.smt``: the replay contract, and a
differential against the ``smtcomp_cli`` binary.

Two things are checked on random ground QF_BV scripts.

**The replay contract has three states, not two.** ``replay() is True`` means the
lifted model was evaluated against the original assertions and satisfies them;
``False`` means it was evaluated and does **not** -- a soundness signal;
``ReplayUnavailable`` means there was nothing to replay. The value ``False`` and
the exception must never stand in for each other, because collapsing them is how
a checker stops being able to fail. Every generated script asserts the full
triple for whichever branch it lands in.

**The verdict is compared against a separate process.** ``smtcomp_cli`` is the
competition front end; running it as a subprocess on the same text exercises a
different entry point (argv, its own parse, its own configuration) than the
in-process binding. A disagreement is a defect in one of them, and the test
names which side said what.

The comparison count is asserted, not assumed: a differential that silently
compared nothing is the inert gate this repository keeps rediscovering.
"""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path

import pytest
from _prop_helpers import Tally
from hypothesis import given, settings
from hypothesis import strategies as st

import axeyum
from axeyum import smt

TIMEOUT_MS = 20_000
WIDTHS = [1, 2, 3, 4, 8]
BV_BINARY = ["bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvudiv", "bvurem", "bvshl"]
BV_UNARY = ["bvnot", "bvneg"]
PREDICATES = ["=", "distinct", "bvult", "bvule", "bvugt", "bvsle", "bvsgt"]


def _bv_term(draw: st.DrawFn, names: list[str], width: int, depth: int) -> str:
    """One well-sorted `width`-bit term over `names`, constants included.

    Constants are drawn from a set that always contains ``0`` -- the degenerate
    divisor for ``bvudiv``/``bvurem`` -- so the generated corpus reaches the
    underspecified operators at their underspecified argument rather than only
    at random ones.
    """
    if depth <= 0:
        return draw(
            st.one_of(
                st.sampled_from(names),
                st.one_of(
                    st.sampled_from([0, 1, (1 << width) - 1]),
                    st.integers(min_value=0, max_value=(1 << width) - 1),
                ).map(lambda value: f"(_ bv{value} {width})"),
            )
        )
    shape = draw(st.sampled_from(["leaf", "unary", "binary"]))
    if shape == "leaf":
        return _bv_term(draw, names, width, 0)
    if shape == "unary":
        op = draw(st.sampled_from(BV_UNARY))
        return f"({op} {_bv_term(draw, names, width, depth - 1)})"
    op = draw(st.sampled_from(BV_BINARY))
    left = _bv_term(draw, names, width, depth - 1)
    right = _bv_term(draw, names, width, depth - 1)
    return f"({op} {left} {right})"


def _bool_term(draw: st.DrawFn, names: list[str], width: int, depth: int) -> str:
    """One Boolean assertion over `width`-bit terms."""
    if depth > 0 and draw(st.booleans()):
        op = draw(st.sampled_from(["not", "and", "or"]))
        if op == "not":
            return f"(not {_bool_term(draw, names, width, depth - 1)})"
        left = _bool_term(draw, names, width, depth - 1)
        right = _bool_term(draw, names, width, depth - 1)
        return f"({op} {left} {right})"
    predicate = draw(st.sampled_from(PREDICATES))
    left = _bv_term(draw, names, width, 2)
    right = _bv_term(draw, names, width, 2)
    return f"({predicate} {left} {right})"


@st.composite
def qf_bv_script(draw: st.DrawFn) -> str:
    """A ground QF_BV script: 1-4 symbols of one width, 1-4 assertions."""
    width = draw(st.sampled_from(WIDTHS))
    count = draw(st.integers(min_value=1, max_value=4))
    names = [f"x{index}" for index in range(count)]
    declarations = "".join(f"(declare-fun {name} () (_ BitVec {width}))" for name in names)
    assertions = "".join(
        f"(assert {_bool_term(draw, names, width, 1)})"
        for _ in range(draw(st.integers(min_value=1, max_value=4)))
    )
    return f"(set-logic QF_BV){declarations}{assertions}(check-sat)"


def _check_replay_contract(script: str) -> str:
    """Asserts the full three-state replay contract; returns the status."""
    outcome = smt.solve(script, timeout_ms=TIMEOUT_MS)
    assert outcome.status in {"sat", "unsat", "unknown"}, (outcome.status, script)
    if outcome.status == "sat":
        assert outcome.replay_available is True, script
        # `is True`, never truthiness: `False` is the soundness signal and must
        # not be reachable through a value that merely looks like a pass.
        assert outcome.replay() is True, (script, outcome.model)
        assert outcome.replay_unavailable_reason is None, script
    else:
        assert outcome.replay_available is False, script
        assert isinstance(outcome.replay_unavailable_reason, str), script
        with pytest.raises(axeyum.ReplayUnavailable):
            outcome.replay()
    return outcome.status


def test_replay_contract_holds_on_random_scripts() -> None:
    """`sat` replays; everything else raises rather than returning `False`.

    Both branches must be reached: a generator that only produced `sat` would
    leave the `ReplayUnavailable` half of the contract untested while the test
    stayed green, so the arm counts are asserted after the run.
    """
    seen = Tally("replay contract")
    statuses: dict[str, int] = {}

    @given(script=qf_bv_script())
    @settings(max_examples=200)
    def check(script: str) -> None:
        status = _check_replay_contract(script)
        statuses[status] = statuses.get(status, 0) + 1
        seen.check()

    check()
    # Printed, not just asserted: the counts are what a reader checks to see
    # that the corpus reached both arms, and rule 4 of this strand is that
    # every gate prints a nonzero count.
    print(f"PROP|{seen} statuses={statuses}")
    seen.require(150)
    assert statuses.get("sat", 0) >= 10, statuses
    assert statuses.get("unsat", 0) >= 10, statuses


def _smtcomp_cli() -> Path | None:
    """The prebuilt competition front end, or `None` when it was not built.

    `AXEYUM_SMTCOMP_CLI` overrides; otherwise the workspace's own
    `target/release/examples/smtcomp_cli`, which `cargo build --release
    --examples` produces and the aggregate gate already builds.
    """
    override = os.environ.get("AXEYUM_SMTCOMP_CLI")
    if override:
        return Path(override) if Path(override).is_file() else None
    root = Path(__file__).resolve().parents[2]
    candidate = root / "target" / "release" / "examples" / "smtcomp_cli"
    if candidate.is_file():
        return candidate
    found = shutil.which("smtcomp_cli")
    return Path(found) if found else None


def test_differential_against_smtcomp_cli(tmp_path: Path) -> None:
    """The in-process binding and the CLI decide the same random scripts alike.

    SMT-COMP 7.1.2 makes the CLI print `unknown` for an error, so an `unknown`
    on either side is counted and skipped rather than treated as a
    disagreement -- comparing those would report ~60 phantom conflicts (the
    `explain_corpus` gotcha, one layer over).
    """
    cli = _smtcomp_cli()
    if cli is None:
        pytest.skip(
            "smtcomp_cli not built: `cargo build --release -p axeyum-solver "
            "--features full --example smtcomp_cli`, or set AXEYUM_SMTCOMP_CLI"
        )
    tally = Tally("smtcomp_cli differential")
    disagreements: list[tuple[str, str, str]] = []
    counter = [0]

    @given(script=qf_bv_script())
    @settings(max_examples=200)
    def compare(script: str) -> None:
        counter[0] += 1
        path = tmp_path / f"case{counter[0]}.smt2"
        path.write_text(script, encoding="utf-8")
        completed = subprocess.run(
            [str(cli), str(path)],
            capture_output=True,
            text=True,
            timeout=120,
            check=False,
        )
        external = completed.stdout.strip().splitlines()
        external_status = external[-1].strip() if external else "<no output>"
        internal_status = smt.solve(script, timeout_ms=TIMEOUT_MS).status
        if external_status == "unknown" or internal_status == "unknown":
            tally.decline(f"undecided: cli={external_status} binding={internal_status}")
            return
        tally.check()
        if external_status != internal_status:
            disagreements.append((script, internal_status, external_status))

    compare()
    print(f"PROP|{tally}")
    assert not disagreements, (
        f"{len(disagreements)} verdict disagreement(s); first: "
        f"binding said {disagreements[0][1]}, {cli.name} said {disagreements[0][2]} "
        f"for {disagreements[0][0]}"
    )
    # A differential that compared nothing is not a differential.
    tally.require(50)


def test_a_word_only_fallback_parse_reports_replay_unavailable() -> None:
    """A `sat` the replay route cannot re-derive must RAISE, not answer `True`.

    Regression for a defect found by this suite on 2026-08-24. `smt.solve`'s
    replay state is built by re-parsing the script, and `parse_script` retries a
    bounded-encoder decline -- here a string literal past the ADR-0029 byte
    model -- as a **word-only** parse that builds no flat assertions. The front
    door still decides the query correctly on source-level routes, but
    `check_model` was then handed an EMPTY assertion stack, returned `true`, and
    `Outcome.replay()` reported `True` for a `sat` whose model was `{}`.

    The verdict was never wrong; the certification was. A checker whose input is
    empty cannot fail, which is the failure mode this repository treats as worse
    than having no checker at all.
    """
    script = r'(set-logic QF_S)(declare-fun s () String)(assert (= s "\u{100}"))(check-sat)'
    outcome = smt.solve(script, timeout_ms=TIMEOUT_MS)

    assert outcome.status == "sat"
    assert outcome.replay_available is False
    assert "word-only" in (outcome.replay_unavailable_reason or "")
    with pytest.raises(axeyum.ReplayUnavailable):
        outcome.replay()

    # Positive control: the same shape WITHIN the byte model still replays, so
    # the guard above refuses the fallback rather than refusing strings.
    ordinary = smt.solve(
        '(set-logic QF_S)(declare-fun s () String)(assert (= s "hi"))(check-sat)',
        timeout_ms=TIMEOUT_MS,
    )
    assert ordinary.status == "sat"
    assert ordinary.replay() is True
    assert ordinary.model == {"s": "hi"}


def test_solve_and_parse_agree_on_what_they_accept() -> None:
    """`smt.parse` refuses a script `smt.solve` decides -- pinned, not endorsed.

    `parse` binds `parse_script_within`, which does NOT take the word-first
    fallback; `solve` reaches it through `parse_script`. So the two disagree on
    exactly the scripts above. This is a real inconsistency in the surface and
    it is recorded here so that closing it (either way) is a deliberate,
    visible change rather than a silent one.
    """
    script = r'(set-logic QF_S)(declare-fun s () String)(assert (= s "\u{100}"))(check-sat)'
    assert smt.solve(script, timeout_ms=TIMEOUT_MS).status == "sat"
    with pytest.raises(axeyum.SmtLibParseError, match="exceeds the bounded byte model"):
        smt.parse(script)
