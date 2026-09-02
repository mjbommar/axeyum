#!/usr/bin/env python3
"""Controls for ``scripts/frontier-shape-census.py``.

The census exists to tell a producer designer what the ready frontier looks
like, so a wrong bucket is not a cosmetic defect: it is a wrong instruction
about where to spend a lane. Two properties are worth guarding and they need
different kinds of control.

**The signature, over SYNTHETIC statements.** One case per conclusion-head
class, written here rather than drawn from the ledger, so a case survives the
fact it was modelled on being proved and flipped. Three of them exist because
the shared parser genuinely returns the wrong thing for that spelling and the
census refines it -- modular congruence, dot notation on a bound receiver, and
a kernel-rendered type whose binders are not spelled ``xN``. Each of those is a
measured miss, not a hypothetical: ``F:goldbach-strong`` reported a conclusion
head of ``h4``, which is the name of one of its own hypotheses' binders.

**The held-out exclusion, over a SYNTHETIC id.** A fixed fake id is injected
into a nursery manifest copy and into a fixture frontier, and the census must
neither bucket it nor name it anywhere in the artifact. The id is invented for
this test precisely so the control never has to name a real blind-evaluation
row -- the thing the exclusion exists to prevent.

Discovered and run by ``scripts/run-python-controls.py``; no registration step::

    python3 -m unittest scripts.tests.test_frontier_shape_census
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "frontier-shape-census.py"

# A fact id that exists in no manifest and no ledger. Named for what it is, so
# a reader grepping for it finds this file and not a real preregistered row.
SYNTHETIC_HELD_OUT = "F:synthetic-held-out-control-do-not-register"
SYNTHETIC_OPEN = "F:synthetic-open-control-do-not-register"


def load(path: pathlib.Path, alias: str):
    spec = importlib.util.spec_from_file_location(alias, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CENSUS = load(SCRIPT, "frontier_shape_census_under_test")
STEP0 = load(ROOT / "scripts" / "brief-step0.py", "brief_step0_for_census_tests")


def signature(statement: str, fact_id: str = "F:ml430-synthetic",
              fragment: str = "Nat") -> dict:
    fact = {"id": fact_id, "statement": "", "formal": {"statement": statement}}
    entry = {"fragment": fragment}
    frontier_module = load(ROOT / "scripts" / "fact-frontier.py",
                           "fact_frontier_for_census_tests")
    return CENSUS.signature_of(fact, entry, None, STEP0, frontier_module, set())


class ConclusionHeadTests(unittest.TestCase):
    """One case per class in the dispatch vocabulary, over synthetic text."""

    def test_equation(self) -> None:
        got = signature("∀ (m n k : ℕ), (m &&& n).testBit k = (m.testBit k && n.testBit k)")
        self.assertEqual(got["conclusion_head"], "Eq")
        self.assertEqual(got["hypothesis_count"], 0)
        self.assertEqual(got["bound_variable_count"], 3)
        self.assertEqual(got["carriers"], ["Nat"])

    def test_strict_and_non_strict_bounds_are_different_classes(self) -> None:
        """A strict and a non-strict bound need different lemmas at the last
        step, so folding them into one class would tell a producer designer
        that one route covers both."""
        self.assertEqual(signature("∀ (b x : ℕ), Nat.log b x < x")["conclusion_head"], "lt")
        self.assertEqual(signature("∀ (b x : ℕ), Nat.log b x ≤ x")["conclusion_head"], "le")

    def test_divisibility(self) -> None:
        got = signature("∀ (n : ℕ), 2 ∣ n * (n + 1)")
        self.assertEqual(got["conclusion_head"], "dvd")

    def test_iff(self) -> None:
        got = signature("∀ {n : ℕ}, Nat.fib n = 0 ↔ n = 0 ∨ n = 1")
        self.assertEqual(got["conclusion_head"], "Iff")

    def test_conjunction_and_disjunction(self) -> None:
        self.assertEqual(
            signature("∀ {x y : ℤ}, x.gcd y ≠ 0 → x ≠ 0 ∧ y ≠ 0")["conclusion_head"],
            "And")
        self.assertEqual(
            signature("∀ {n : ℕ}, n = 0 ∨ 0 < n")["conclusion_head"], "Or")

    def test_modular_congruence(self) -> None:
        """`≡` is in brief-step0's NOTATION table but NOT in `head_of`'s symbol
        scan, so without the census's refinement this returns the name of a
        bound variable and the whole ModEq class disappears from the report."""
        got = signature("∀ {n a b : ℕ}, b ≡ a [MOD n]")
        self.assertEqual(got["conclusion_head"], "ModEq")
        self.assertEqual(
            signature("∀ {n a b : ℤ}, b ≡ a [ZMOD n]")["conclusion_head"], "ModEq")

    def test_dot_notation_predicate_on_a_bound_receiver(self) -> None:
        """`head_of` returns the RECEIVER for `(n ^ m).Deficient`, which is the
        binder `n`. A bucket named after a variable looks exactly like a
        finding and is not one."""
        got = signature("∀ {n m : ℕ}, Nat.Prime n → (n ^ m).Deficient")
        self.assertEqual(got["conclusion_head"], "other:Deficient")
        self.assertEqual(got["hypothesis_heads"], ["other:Prime"])

    def test_a_lone_binder_name_is_unparsed_not_a_bucket(self) -> None:
        got = signature("∀ (q : ℕ), q")
        self.assertEqual(got["conclusion_head"], "unparsed")

    def test_kernel_rendered_binders_that_are_not_xN(self) -> None:
        """The dialect two native facts are written in. Measured: without the
        binder normalization `F:goldbach-strong` reports its conclusion head as
        `h4`, its own second hypothesis's binder name."""
        statement = (
            "theorem Synthetic.strong : ((n : AxNat) -> ((h4 : AxNat.le "
            "(AxNat.succ AxNat.zero) n) -> ((heven : AxNat.dvd (AxNat.succ "
            "AxNat.zero) n) -> Exists.{1} AxNat (fun (p : AxNat) => Eq.{1} "
            "AxNat p n))))")
        got = signature(statement, fact_id="F:synthetic-native")
        self.assertEqual(got["dialect"], CENSUS.DIALECT_RENDERED)
        self.assertEqual(got["conclusion_head"], "Exists")
        self.assertEqual(got["hypothesis_heads"], ["le", "dvd"])

    def test_hypothesis_heads_stay_aligned_with_their_chunks(self) -> None:
        got = signature(
            "∀ (n p : ℕ), 1 < n → Nat.Prime p → p ∣ n.fermatNumber → "
            "∃ k, p = k * 2 ^ (n + 2) + 1")
        self.assertEqual(got["hypothesis_heads"], ["lt", "other:Prime", "dvd"])
        self.assertEqual(got["hypothesis_count"], 3)

    def test_prose_and_smtlib_are_unparsed_rather_than_guessed(self) -> None:
        prose = signature("; NOT EXPRESSIBLE. The proposition quantifies over "
                          "formal systems.")
        self.assertEqual(prose["dialect"], CENSUS.DIALECT_PROSE)
        self.assertEqual(prose["conclusion_head"], "unparsed")
        smt = signature("(forall ((n Int) (a Int)) (=> (> n 2) (not (= a 0))))")
        self.assertEqual(smt["dialect"], CENSUS.DIALECT_SMTLIB)
        self.assertEqual(smt["conclusion_head"], "unparsed")

    def test_mutation_controls_are_labeled_not_silently_counted(self) -> None:
        """A mutation control is a deliberately FALSE proposition kept as a
        negative control. Counting one as a producer target overstates what
        building for its bucket would buy."""
        fact = {"id": "F:ml430-mutation-deadbeef",
                "statement": "A `polarity-reversal` of something true.",
                "formal": {"statement": "∀ (n : ℕ), n.factorial = 0"}}
        frontier_module = load(ROOT / "scripts" / "fact-frontier.py",
                               "fact_frontier_for_mutation_test")
        got = CENSUS.signature_of(fact, {"fragment": "Nat"}, None, STEP0,
                                  frontier_module, set())
        self.assertTrue(got["mutation_control"])
        self.assertEqual(got["provenance"], "ml430-mirror")

    def test_divergence_blocking_is_read_from_the_registry(self) -> None:
        """Blocked in one direction and clear in the other, over the SAME
        statement, so a blocker that matched everything would fail here."""
        dispatchable = load(ROOT / "scripts" / "check-dispatchable-frontier.py",
                            "dispatchable_frontier_for_census_tests")
        registry = [{"mathlib_constant": "Nat.testBit", "class": "codomain",
                     "surface_forms": [".testBit"]}]
        fact = {"id": "F:ml430-synthetic", "statement": "",
                "formal": {"statement": "∀ (m n k : ℕ), (m &&& n).testBit k = 0"}}
        clear = {"id": "F:ml430-synthetic", "statement": "",
                 "formal": {"statement": "∀ (n : ℕ), n.multichoose 0 = 1"}}
        frontier_module = load(ROOT / "scripts" / "fact-frontier.py",
                               "fact_frontier_for_divergence_test")
        blocked = CENSUS.signature_of(fact, {"fragment": "Nat"}, None, STEP0,
                                      frontier_module, set(), registry,
                                      dispatchable.blockers_for)
        self.assertEqual(blocked["divergence_blocked"], ["Nat.testBit"])
        unblocked = CENSUS.signature_of(clear, {"fragment": "Nat"}, None, STEP0,
                                        frontier_module, set(), registry,
                                        dispatchable.blockers_for)
        self.assertEqual(unblocked["divergence_blocked"], False)

    def test_no_registry_means_unknown_not_unblocked(self) -> None:
        got = signature("∀ (m n k : ℕ), (m &&& n).testBit k = 0")
        self.assertIsNone(got["divergence_blocked"])

    def test_unknown_environment_is_unknown_never_absent(self) -> None:
        """With no snapshot the declared flag must be None. A false ABSENT here
        would say a producer cannot state a fact it can state perfectly well --
        the stale-binary failure this repository has shipped twice."""
        got = signature("∀ (n : ℕ), n.multichoose 0 = 1")
        self.assertIsNone(got["conclusion_constants_declared"])


class BucketingTests(unittest.TestCase):

    def test_coarse_key_bands_hypothesis_counts(self) -> None:
        self.assertEqual(CENSUS.band(0), "0")
        self.assertEqual(CENSUS.band(1), "1")
        self.assertEqual(CENSUS.band(2), "2+")
        self.assertEqual(CENSUS.band(9), "2+")

    @staticmethod
    def _row(name: str, **overrides) -> dict:
        signature = {"carriers": ["Nat"], "conclusion_head": "Eq",
                     "hypothesis_count": 0, "mutation_control": False,
                     "divergence_blocked": False}
        signature.update(overrides)
        return {"fact_id": f"F:{name}", "signature": signature}

    def test_targetable_size_excludes_both_unclosable_classes(self) -> None:
        """Mutation controls AND divergence-blocked mirrors. Subtracting only
        the first is how the largest bucket in this census -- nine facts, zero
        targetable -- reads as the obvious place to point a producer."""
        buckets = CENSUS.rank_buckets(
            [self._row("a"),
             self._row("b", mutation_control=True),
             self._row("c", divergence_blocked=["Nat.testBit"])],
            CENSUS.coarse_key)
        self.assertEqual(len(buckets), 1)
        self.assertEqual(buckets[0]["size"], 3)
        self.assertEqual(buckets[0]["targetable_size"], 1)
        self.assertEqual(buckets[0]["mutation_control_count"], 1)
        self.assertEqual(buckets[0]["divergence_blocked_count"], 1)

    def test_an_unloaded_divergence_registry_is_unknown_not_clear(self) -> None:
        """`None` must NOT be read as "nothing is blocked": that would inflate
        every targetable count silently. It counts as targetable (the number is
        then an UPPER BOUND, which the report says) and
        `divergence_registry_loaded` is what tells a reader which it is."""
        buckets = CENSUS.rank_buckets(
            [self._row("a", divergence_blocked=None)], CENSUS.coarse_key)
        self.assertEqual(buckets[0]["divergence_blocked_count"], 0)
        self.assertEqual(buckets[0]["targetable_size"], 1)

    def test_buckets_rank_largest_first_and_ties_are_deterministic(self) -> None:
        rows = [
            self._row(name, carriers=[carrier], conclusion_head=head)
            for name, carrier, head in (
                ("a", "Nat", "Eq"), ("b", "Nat", "Eq"), ("c", "Int", "le"))
        ]
        first = CENSUS.rank_buckets(rows, CENSUS.coarse_key)
        second = CENSUS.rank_buckets(list(reversed(rows)), CENSUS.coarse_key)
        self.assertEqual([b["size"] for b in first], [2, 1])
        self.assertEqual(json.dumps(first), json.dumps(second))


class HeldOutExclusionTests(unittest.TestCase):
    """A synthetic held-out id must not reach any bucket or any member list."""

    def _tree(self) -> pathlib.Path:
        scratch = pathlib.Path("/data0/axeyum/scratch")
        tmp = tempfile.TemporaryDirectory(dir=scratch if scratch.is_dir() else None)
        self.addCleanup(tmp.cleanup)
        root = pathlib.Path(tmp.name) / "tree"
        (root / "scripts").mkdir(parents=True)
        (root / "artifacts" / "autogenesis").mkdir(parents=True)
        (root / "artifacts" / "facts").mkdir(parents=True)
        for name in ("frontier-shape-census.py", "brief-step0.py", "fact-frontier.py",
                     "check-autogenesis-holdout-isolation.py",
                     "validate-autogenesis-operations.py",
                     "validate-producer-contracts.py",
                     "validate-producer-contract-declines.py"):
            source = ROOT / "scripts" / name
            if source.is_file():
                (root / "scripts" / name).write_text(source.read_text())
        for name in ("nursery-v1.json", "nursery-v2-extension.json"):
            manifest = json.loads((ROOT / "artifacts/autogenesis" / name).read_text())
            manifest["entries"] = [
                {"fact_id": SYNTHETIC_HELD_OUT, "partition": "held-out"},
                {"fact_id": SYNTHETIC_OPEN, "partition": "train"},
            ]
            (root / "artifacts/autogenesis" / name).write_text(json.dumps(manifest))
        for fact_id in (SYNTHETIC_HELD_OUT, SYNTHETIC_OPEN):
            (root / "artifacts/facts" / (fact_id.removeprefix("F:") + ".json")).write_text(
                json.dumps({
                    "id": fact_id,
                    "statement": "a synthetic control proposition",
                    "epistemic_status": "open",
                    "external_status": "open",
                    "depends_on": [],
                    "formal": {"language": "lean4", "fragment": "Nat",
                               "statement": "∀ (n : ℕ), n.multichoose 0 = 1"},
                }))
        return root

    def _frontier(self, root: pathlib.Path) -> pathlib.Path:
        path = root / "frontier.json"
        path.write_text(json.dumps({
            "ledger": {"fact_count": 2, "ledger_sha256": "0" * 64},
            "frontier_sha256": "1" * 64,
            "diagnostics": {},
            "selection": {"ready_fact_ids": [SYNTHETIC_HELD_OUT, SYNTHETIC_OPEN]},
            "entries": [
                {"fact_id": SYNTHETIC_HELD_OUT, "fragment": "Nat",
                 "route_class": "proof-route-only",
                 "matched_producer_contract_ids": []},
                {"fact_id": SYNTHETIC_OPEN, "fragment": "Nat",
                 "route_class": "proof-route-only",
                 "matched_producer_contract_ids": []},
            ],
        }))
        return path

    def _run(self, root: pathlib.Path, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable, str(root / "scripts" / "frontier-shape-census.py"),
             "--frontier", str(self._frontier(root)), *args],
            cwd=root, capture_output=True, text=True, timeout=300, check=False)

    def test_a_held_out_id_is_excluded_and_never_named(self) -> None:
        root = self._tree()
        artifact = root / "artifacts/autogenesis/frontier-shape-census-v1.json"
        done = self._run(root, "--artifact", str(artifact))
        self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
        text = artifact.read_text()
        self.assertNotIn(SYNTHETIC_HELD_OUT, text)
        self.assertNotIn(SYNTHETIC_HELD_OUT, done.stdout)
        census = json.loads(text)
        self.assertEqual(census["population"]["held_out_excluded"], 1)
        self.assertEqual(census["population"]["censused_count"], 1)
        members = [fid for bucket in census["buckets"]["fine"]
                   for fid in bucket["fact_ids"]]
        self.assertEqual(members, [SYNTHETIC_OPEN])

    def test_the_exclusion_control_is_not_vacuous(self) -> None:
        """The positive half: the same run MUST carry the non-held-out sibling.
        Without this, an exclusion that dropped every fact would pass."""
        root = self._tree()
        artifact = root / "artifacts/autogenesis/frontier-shape-census-v1.json"
        self._run(root, "--artifact", str(artifact))
        self.assertIn(SYNTHETIC_OPEN, artifact.read_text())

    def test_an_empty_held_out_population_is_refused(self) -> None:
        """An exclusion that excludes nothing is not an exclusion. The
        isolation gate refuses a manifest contributing zero held-out rows and
        the census must not paper over that with an empty set."""
        root = self._tree()
        manifest_path = root / "artifacts/autogenesis/nursery-v1.json"
        manifest = json.loads(manifest_path.read_text())
        manifest["entries"] = [{"fact_id": SYNTHETIC_OPEN, "partition": "train"}]
        manifest_path.write_text(json.dumps(manifest))
        done = self._run(root, "--artifact",
                         str(root / "artifacts/autogenesis/out.json"))
        self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
        self.assertIn("UNANSWERABLE", done.stderr)


class CheckModeTests(unittest.TestCase):

    def test_unanswerable_is_exit_2_not_exit_1(self) -> None:
        """A checker reporting `disagrees` when it could not compute an answer
        is the checker-that-cannot-fail defect wearing the opposite mask."""
        done = subprocess.run(
            [sys.executable, str(SCRIPT), "--check", "--frontier", "/dev/null"],
            cwd=ROOT, capture_output=True, text=True, timeout=120, check=False)
        self.assertEqual(done.returncode, 2, done.stdout + done.stderr)
        self.assertIn("UNANSWERABLE", done.stderr)

    def test_a_perturbed_artifact_fails_the_check(self) -> None:
        committed = ROOT / "artifacts/autogenesis/frontier-shape-census-v1.json"
        if not committed.is_file():
            self.skipTest("no committed census artifact in this tree")
        census = json.loads(committed.read_text())
        census["population"]["primary_count"] += 1
        with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as handle:
            json.dump(census, handle)
            perturbed = handle.name
        self.addCleanup(lambda: pathlib.Path(perturbed).unlink(missing_ok=True))
        done = subprocess.run(
            [sys.executable, str(SCRIPT), "--check", "--artifact", perturbed],
            cwd=ROOT, capture_output=True, text=True, timeout=600, check=False)
        self.assertEqual(done.returncode, 1, done.stdout + done.stderr)
        self.assertIn("disagrees", done.stderr)


if __name__ == "__main__":
    unittest.main()
