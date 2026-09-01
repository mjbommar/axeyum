"""Controls for `rescope-nursery-exemption.py`'s gate-output parser.

The tool re-scopes ONE cross-population exemption to the live component, and
it learns what that component is by reading `check-autogenesis-nursery.py`'s
own error text. It had no tests at all, and the parser was a single regex over
combined stdout+stderr:

    rows = re.findall(r"^\\s+(F:[^\\s]+)\\s+->\\s+(\\S+)", text, re.M)

That is wrong in two ways, both of which silently destroy a reviewed
adjudication rather than failing:

1. The gate validates **nursery-v1 first** and raises before the
   cross-population report ever runs. Measured 2026-09-01 with the v1
   component-split red, the regex returned the 13 members of the two V1
   components -- and `main()` would have written them over the 258-member
   CROSS-POPULATION exemption it targets. Fail-closed afterwards (the digest
   no longer matches anything), but the membership list and the reason string
   recording why the crossing was judged benign are gone.

2. Two crossing components in one report are unioned into a single member
   list, inventing a component that exists nowhere.

Neither shows up as an error: the tool prints a confident
`RESCOPE|258 -> 13 members` and exits 0.

Every negative case here is paired with a POSITIVE control on the same parser,
because a parser that returned "refused" for everything would satisfy the
negative cases alone.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path
import subprocess
import unittest


SCRIPT = Path(__file__).parents[1] / "rescope-nursery-exemption.py"
SPEC = importlib.util.spec_from_file_location("rescope_nursery_exemption", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


V1_ONLY_OUTPUT = """autogenesis-nursery: 2 partition-leak violation type(s) found:

declared dependency component crosses evaluation partitions
  component=eebbcd53cea2… partitions=['development', 'train']
    F:ml430-nat-ascfactorial-zero-fd183202 -> train
    F:ml430-nat-factorial-dvd-ascfactorial-44a4e641 -> development

evaluation population shares a component with Autogenesis-1 (longitudinal=['F:nat-mul-one'])
  component=f888609d9f17… partitions=['development', 'longitudinal', 'train']
    F:ml430-nat-descfactorial-one-d4856d4a -> train
    F:ml430-nat-mod-lcm-ee6bdd41 -> development
    F:nat-mul-one -> longitudinal
"""

V1_SINGLE_COMPONENT_OUTPUT = """autogenesis-nursery: 1 partition-leak violation type(s) found:

declared dependency component crosses evaluation partitions
  component=eebbcd53cea2… partitions=['development', 'train']
    F:ml430-nat-ascfactorial-zero-fd183202 -> train
    F:ml430-nat-factorial-dvd-ascfactorial-44a4e641 -> development
"""

CROSS_POPULATION_OUTPUT = """autogenesis-nursery: 1 cross-population partition-leak violation type(s) found:

declared dependency component crosses evaluation partitions (cross-population: nursery-v1 union nursery-v2-extension)
  component=275519ee5747… partitions=['development', 'train']
    F:ml430-int-add-assoc-749cb0ff -> development [v2]
    F:ml430-int-gcd-div-5e01872f -> train [v1]
    F:ml430-nat-add-comm-56a2d614 -> train [v2]
"""

TWO_CROSS_POPULATION_COMPONENTS = """autogenesis-nursery: 1 cross-population partition-leak violation type(s) found:

declared dependency component crosses evaluation partitions (cross-population: nursery-v1 union nursery-v2-extension)
  component=aaaaaaaaaaaa… partitions=['development', 'train']
    F:a-train -> train [v1]
    F:a-dev -> development [v2]
  component=bbbbbbbbbbbb… partitions=['development', 'train']
    F:b-train -> train [v2]
    F:b-dev -> development [v2]
"""

CLEAN_OUTPUT = """AUTOGENESIS_NURSERY_OK|abc|ready=true|evaluation=214|blockers=0
AUTOGENESIS_NURSERY_CROSS_POPULATION_OK|def|v1=216|v2=460|components=348
"""


class _FakeCompleted:
    def __init__(self, text: str) -> None:
        self.stdout = text
        self.stderr = ""
        self.returncode = 1


class LiveComponentParserTests(unittest.TestCase):
    def setUp(self) -> None:
        self._real_run = subprocess.run
        self.addCleanup(setattr, subprocess, "run", self._real_run)

    def _gate_prints(self, text: str) -> None:
        subprocess.run = lambda *a, **k: _FakeCompleted(text)  # type: ignore[assignment]

    def test_a_v1_only_crossing_is_refused_not_scraped(self) -> None:
        # The destructive case. The old parser returned the five V1 fact ids
        # from this exact output and `main()` would have overwritten the
        # cross-population exemption with them.
        self._gate_prints(V1_ONLY_OUTPUT)
        with self.assertRaises(MODULE.Refused):
            MODULE.live_component()

    def test_a_v1_only_crossing_with_ONE_component_is_still_refused(self) -> None:
        # This is the case the multi-component refusal cannot cover: exactly
        # one V1 component is reported, so counting blocks does not save you
        # and only the cross-population header check does. Without it the tool
        # returns two ml430 factorial fact ids and re-scopes the v2 exemption
        # onto them.
        self._gate_prints(V1_SINGLE_COMPONENT_OUTPUT)
        with self.assertRaises(MODULE.Refused):
            MODULE.live_component()

    def test_a_single_cross_population_component_is_parsed(self) -> None:
        # POSITIVE CONTROL for the refusal above: the parser must still do its
        # job on the output it exists to read, or "refuse everything" would
        # pass every negative test in this file.
        self._gate_prints(CROSS_POPULATION_OUTPUT)
        members, census, held_out = MODULE.live_component()
        self.assertEqual(
            members,
            [
                "F:ml430-int-add-assoc-749cb0ff",
                "F:ml430-int-gcd-div-5e01872f",
                "F:ml430-nat-add-comm-56a2d614",
            ],
        )
        self.assertEqual(census, {"development": 1, "train": 2})
        self.assertEqual(held_out, [])

    def test_two_cross_population_components_are_refused_not_unioned(self) -> None:
        self._gate_prints(TWO_CROSS_POPULATION_COMPONENTS)
        with self.assertRaises(MODULE.Refused):
            MODULE.live_component()

    def test_a_clean_gate_run_reports_nothing_to_re_scope(self) -> None:
        # POSITIVE CONTROL: a green gate must be distinguishable from a
        # refusal, because `main()` returns 0 for one and 2 for the other.
        self._gate_prints(CLEAN_OUTPUT)
        members, census, held_out = MODULE.live_component()
        self.assertEqual(members, [])
        self.assertEqual(census, {})
        self.assertEqual(held_out, [])

    def test_a_held_out_member_is_surfaced_for_main_to_refuse_on(self) -> None:
        # `main()` exits 2 on a held-out member rather than re-scoping. That
        # decision is only as good as the parser reporting the partition, so
        # pin it here rather than only in the docstring.
        self._gate_prints(
            CROSS_POPULATION_OUTPUT.replace(
                "F:ml430-int-add-assoc-749cb0ff -> development [v2]",
                "F:ml430-int-add-assoc-749cb0ff -> held-out [v2]",
            )
        )
        _members, _census, held_out = MODULE.live_component()
        self.assertEqual(held_out, ["F:ml430-int-add-assoc-749cb0ff"])


class MainExitStatusTests(unittest.TestCase):
    """A refusal must not read as success.

    `main()` checks `if not members: return 0` before anything else, so an
    early version that signalled refusal by returning an empty member list
    would have exited 0 -- "nothing to re-scope" -- for a case that is a
    finding.
    """

    def setUp(self) -> None:
        self._real_run = subprocess.run
        self.addCleanup(setattr, subprocess, "run", self._real_run)

    def test_a_v1_only_crossing_exits_two(self) -> None:
        subprocess.run = lambda *a, **k: _FakeCompleted(V1_ONLY_OUTPUT)  # type: ignore[assignment]
        self.assertEqual(MODULE.main(), 2)

    def test_a_clean_gate_run_exits_zero(self) -> None:
        subprocess.run = lambda *a, **k: _FakeCompleted(CLEAN_OUTPUT)  # type: ignore[assignment]
        self.assertEqual(MODULE.main(), 0)


if __name__ == "__main__":
    unittest.main()
