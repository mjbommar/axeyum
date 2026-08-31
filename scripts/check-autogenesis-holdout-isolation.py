#!/usr/bin/env python3
"""The held-out partition must stay blind, and prose did not keep it that way.

`docs/autogenesis/16-mathlib-frozen-nursery-split-result.md` preregistered 214
propositions into train / development / held-out, and the programme README
promises that "every policy improvement is evaluated against immutable held-out
populations." On 2026-08-21 an authoritative operation was registered against
`F:ml430-nat-gcd-greatest-0a04214a`, a held-out fact, and it stayed unnoticed
until 2026-08-22 because **nothing checked**:
`check-autogenesis-nursery.py` validates the manifest's internal integrity and
never inspects what operations do to it, and `validate-autogenesis-operations.py`
did not mention partitions at all. The split key is `<family>:<statement-shape>`
and the declared partition unit is the whole family, so one row spent 19 of the
then-76 held-out propositions -- 25% of the partition.

This gate closes that hole from both directions:

1.  **No held-out fact may be settled in the ledger.** Establishing a held-out
    proposition by ANY route spends it; the operation registry is only one way
    in, so checking the registry alone would leave the others open.
2.  **No artifact may reference a held-out fact id**, except the files that
    define a population themselves. A generic walk is used rather than a check
    on `applicability.fact_ids`: operations already carry fact ids at three
    distinct JSON paths (`applicability.fact_ids[]`, `executor.input_fact_id`,
    `executor.premise_fact_id`), so a field-specific guard was bypassable the
    day it was written, and a schema addition would silently reopen it.

    Since slice A4 the walk covers `artifacts/episodes/` too, including the
    `*.json.snapshot` sidecars -- transcripts, proposals and transaction
    proposals. Ten agent episodes were committed on 2026-08-24 while this gate
    scanned only `artifacts/autogenesis/`; that they were clean was measured by
    hand, which is exactly the arrangement this file exists to replace.

FAIL-CLOSED. An unreadable manifest, or a held-out population that has somehow
become empty, is an error rather than a quiet pass -- a guard whose subject has
vanished reports the same "no violations" as a guard that works.

`held_out=` in this gate's output line is the FULL held-out partition as the
manifests declare it -- every row with `partition: "held-out"` in either
`nursery-v1.json` or `nursery-v2-extension.json`, unconditionally. That
deliberately includes the small number of `-mutation-`-named scratch fixtures
(outcome-blind pipeline test controls, never real evaluation subjects) that
happen to be filed under held-out to sit beside the real proposition they
mutated -- this gate's job is to protect the WHOLE declared bookkeeping
population, fixtures included, so it does not exclude them the way
`scripts/check-dispatchable-frontier.py`'s narrower `held_out` (real
ml430-mirror dispatch candidates only) does. Measured 2026-08-31: this gate's
146 vs. the frontier gate's 145 is exactly that one fixture
(`F:ml430-mutation-2086302b3a338591b3179871`), not a disagreement about the
same population -- see the frontier script's docstring for the other side.
"""

from __future__ import annotations

import json
import pathlib
import sys
from typing import Any

ROOT = pathlib.Path(__file__).resolve().parents[1]
NURSERY = ROOT / "artifacts/autogenesis/nursery-v1.json"
EXTENSION = ROOT / "artifacts/autogenesis/nursery-v2-extension.json"
FACTS = ROOT / "artifacts/facts"
ARTIFACTS = ROOT / "artifacts/autogenesis"
EPISODES = ROOT / "artifacts/episodes"

# The files that DEFINE a population necessarily name its members, and a census
# that filtered them would fail the very rule that makes it evidence.
#
# `nursery-v1.json` and `mathlib-nat-int-fact-catalog-v1.json` are the split
# manifest and the source catalog. `frontier.json.snapshot` joined them when
# this gate was extended to `artifacts/episodes/` (slice A4): it is
# `fact-frontier.py --json`, a census of the WHOLE open ledger which
# `fact-frontier.py --verify` re-derives entry for entry, so it necessarily
# enumerates every held-out id exactly as the nursery does. It is exempted BY
# NAME rather than by directory, and it is the only name under
# `artifacts/episodes/` that is: an episode document, a transcript, a proposal
# or a transaction proposal naming a held-out id is a breach, and the whole
# reason for scanning that tree.
#
# `nursery-v2-extension.json` joined them on 2026-08-29: it is the split
# manifest for the refill and necessarily names its own held-out members, for
# the same reason `nursery-v1.json` does. `mathlib-statable-vocabulary-v1.json`
# is NOT exempt and must not become so -- it enumerates only the 214 catalogued
# v1 propositions, none of which the extension holds out.
POPULATION_FILES = {
    "nursery-v1.json",
    "nursery-v2-extension.json",
    "mathlib-nat-int-fact-catalog-v1.json",
    "frontier.json.snapshot",
}
SETTLED = {"proved", "computed"}


class IsolationError(Exception):
    pass


def held_out_facts() -> set[str]:
    # BOTH manifests, and each is REQUIRED. The 2026-08-29 refill preregisters
    # 30 held-out rows in `nursery-v2-extension.json`; a gate reading only v1
    # would report PASS while leaving every one of them unprotected, which is
    # the same shape as the incident this file exists to prevent -- a blind
    # population that nothing was watching.
    held: set[str] = set()
    for path in (NURSERY, EXTENSION):
        if not path.is_file():
            raise IsolationError(f"nursery manifest is missing: {path}")
        try:
            manifest = json.loads(path.read_text())
        except json.JSONDecodeError as error:
            raise IsolationError(
                f"nursery manifest is unreadable: {path.name}: {error}") from error
        entries = manifest.get("entries")
        if not isinstance(entries, list):
            raise IsolationError(f"{path.name} has no entries")
        found = {
            entry["fact_id"]
            for entry in entries
            if isinstance(entry, dict) and entry.get("partition") == "held-out"
        }
        if not found:
            raise IsolationError(
                f"{path.name} contributes no held-out rows; without them this "
                f"gate would pass vacuously for that manifest's population")
        held |= found
    if not held:
        raise IsolationError(
            "the held-out population is empty; this gate would pass vacuously"
        )
    return held


def scan_targets() -> list[pathlib.Path]:
    """Every file this gate walks for held-out references.

    Two trees, and the episode tree is walked recursively and for two suffixes.
    `*.json.snapshot` is not decoration: an episode's transcript, its proposals
    and its transaction proposal all carry that suffix precisely so
    `check-agent-episode.py` does not read them as malformed episodes, and a
    walk that only looked at `*.json` would therefore skip every file an agent
    actually wrote its reasoning into.
    """
    # `rglob`, not `glob`, since 2026-08-30. The non-recursive form silently
    # dropped `artifacts/autogenesis/producer-contracts/` -- 2 JSON files, the
    # same class of artifact in the same tree this gate claims to cover, in a
    # subdirectory that did not exist when the glob was written. A producer
    # contract is prospective dispatch: naming a held-out fact in one is exactly
    # the breach this gate exists for.
    #
    # This is the ONLY widening taken. The 2026-08-30 session audit found held-out
    # ids outside the scan set and asked whether the scan should grow; re-derived
    # here over all 136 pre-amendment ids, **18 distinct ids** appear in `crates/`,
    # `docs/`, `scripts/` and `PLAN.md`. Widening to those trees is REFUSED, and
    # not on volume:
    #
    #   * 13 of the 18 are in `docs/plan/generated/autogenesis-baseline.json`, a
    #     premise->consequent graph whose edges come from the facts' OWN
    #     preregistered `depends_on`. It republishes population data; it adds
    #     nothing a reader of the nursery does not already have.
    #   * `nat_prelude/sqrt.rs:55` reasons in a source comment about
    #     `F:ml430-nat-sqrt-eq-79ae8eae` and says `sqrt_zero`/`sqrt_one` are its
    #     `n in {0,1}` instances. That is an incidental mention, not a spend: the
    #     row is the QUANTIFIED `forall n, sqrt (n*n) = n`, two instances of a
    #     universal do not establish it, and the comment explicitly declines the
    #     general theorem. (Were it a closed equation, `check-holdout-closed-
    #     evaluation.py` would refuse it -- a different gate, deliberately.)
    #   * The rest are bookkeeping: an attestation ceiling ADR, draw status
    #     files, a refusal-test fixture, a `not_elaborable` exemption set.
    #
    # And the decisive one: a widened scan would fire on
    # `docs/research/11-design-review/2026-08-30-session-audit.md`, the document
    # that FOUND the contamination, and on the ADR recording the repair. **A gate
    # that reds when someone writes down a discovered leak punishes disclosure**,
    # and the predictable response is an exemption list that grows until the gate
    # means nothing. The narrow scan measures "no reference in the autogenesis
    # artifacts", which is a real property; the verdict line should be read as
    # that, and not as "the held-out set is untouched by the tree".
    targets = list(ARTIFACTS.rglob("*.json"))
    if EPISODES.is_dir():
        targets += EPISODES.rglob("*.json")
        targets += EPISODES.rglob("*.json.snapshot")
    return sorted(set(targets))


def strings(value: Any, path: str) -> list[tuple[str, str]]:
    if isinstance(value, dict):
        return [x for k, v in value.items() for x in strings(v, f"{path}.{k}")]
    if isinstance(value, list):
        return [x for v in value for x in strings(v, f"{path}[]")]
    if isinstance(value, str):
        return [(value, path)]
    return []


def main() -> int:
    try:
        held = held_out_facts()
    except IsolationError as error:
        print(f"AUTOGENESIS_HOLDOUT_ISOLATION_ERROR|{error}", file=sys.stderr)
        return 1

    violations: list[str] = []

    # (1) settled held-out facts
    settled = []
    for fact_id in sorted(held):
        path = FACTS / (fact_id.replace("F:", "F-") + ".json")
        if not path.is_file():
            continue
        status = json.loads(path.read_text()).get("epistemic_status")
        if status in SETTLED:
            settled.append(f"{fact_id} is {status}")
    violations += [f"settled-held-out-fact|{item}" for item in settled]

    # (2) references from anywhere else
    scanned = 0
    for path in scan_targets():
        if path.name in POPULATION_FILES:
            continue
        try:
            raw = path.read_text()
            document = json.loads(raw)
        except (OSError, json.JSONDecodeError):
            continue
        scanned += 1
        named: set[str] = set()
        for value, where in strings(document, ""):
            if value in held:
                violations.append(f"held-out-reference|{path.name}{where}|{value}")
                named.add(value)
        # A second guard, and NOT a duplicate of the one above. That one
        # compares whole JSON values, which is right for a structured artifact
        # where a fact id is a field. An episode transcript is PROSE: a model
        # writing "I will work on F:..." puts the id in a value that is not
        # equal to it, and the exact walk returns clean. Measured 2026-08-24 --
        # the first version of the episode scan passed a transcript naming a
        # held-out fact in a sentence. `episode.assert_no_held_out` had always
        # used substring containment for exactly this reason; the two gates now
        # agree about what "names a held-out fact" means.
        for fact_id in sorted(held):
            if fact_id not in named and fact_id in raw:
                violations.append(f"held-out-reference|{path.name}|embedded-in-text|{fact_id}")

    verdict = "FAIL" if violations else "PASS"
    print(
        f"AUTOGENESIS_HOLDOUT_ISOLATION|held_out={len(held)}|"
        f"files_scanned={scanned}|settled={len(settled)}|"
        f"references={len(violations) - len(settled)}|verdict={verdict}"
    )
    for item in violations:
        print(f"  {item}", file=sys.stderr)
    if violations:
        print(
            "held-out isolation is spent by any of these; the repair is an amendment "
            "in artifacts/autogenesis/mathlib-nursery-split-policy-v1.json, not a "
            "deletion -- see docs/autogenesis/"
            "226-production-measurement-and-general-producer-plan.md",
            file=sys.stderr,
        )
    return 1 if violations else 0


if __name__ == "__main__":
    raise SystemExit(main())
