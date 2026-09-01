#!/usr/bin/env python3
"""Re-scope a cross-population component-split exemption to the live component.

ADR-0850's exemption names the EXACT closed fact-id set of a dependency
component and stops matching the moment that component changes. That property
is what makes it safe, and it is not negotiable -- it has caught two genuinely
different upstream causes already.

It also means ordinary theorem work re-triggers it. Measured 2026-08-31: the
same component went 206 -> 228 -> 230 -> 238 in one day as lanes closed facts
that connect into it through `add_comm`/`add_assoc`. Re-scoping by hand three
times invites the shortcut nobody should take -- keying the exemption on
something looser so it stops firing.

So this automates the MECHANICAL half and refuses to automate the REVIEW:

  * It re-scopes only when the live component contains ZERO held-out members.
    A held-out member is contamination, and this script exits 2 naming the rows
    rather than writing anything. That question is the entire safety property
    and a human has to see it.
  * It recomputes `extension_sha256` with the GENERATOR'S OWN `digest()`, never
    a hand-rolled hash -- a hand-rolled one that happens to differ is
    indistinguishable from tampering.
  * It records the partition census in the reason, so the next reader sees what
    was true when it was re-scoped rather than taking it on faith.

Exit 0 re-scoped (or already current), 1 usage/parse error, 2 REFUSED because a
held-out row is in the component.
"""

from __future__ import annotations

import collections
import importlib.util
import json
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
EXTENSION = ROOT / "artifacts/autogenesis/nursery-v2-extension.json"
GATE = ROOT / "scripts/check-autogenesis-nursery.py"
GENERATOR = ROOT / "scripts/gen-autogenesis-nursery-refill.py"


def load_generator_digest():
    """Reuse the generator's own digest so the two cannot disagree."""
    spec = importlib.util.spec_from_file_location("_gen", GENERATOR)
    module = importlib.util.module_from_spec(spec)
    try:
        spec.loader.exec_module(module)
    except SystemExit:
        pass
    return module.digest


class Refused(RuntimeError):
    """The gate's output cannot be attributed to exactly one cross-population component."""


def live_component() -> tuple[list[str], dict[str, int], list[str]]:
    """Members, partition census, and held-out members, read from the GATE.

    This parses the gate's output PER COMPONENT and refuses anything it cannot
    attribute to exactly one cross-population component. The first version
    scraped every `F:… -> partition` line in combined stdout+stderr with one
    regex and unioned them, which is wrong in two ways that both destroy data:

    * The gate checks nursery-v1 FIRST and raises before the cross-population
      report ever runs. Measured 2026-09-01, with the v1 component-split red,
      that regex returned the 13 members of the two V1 components -- and
      `main()` would have written them over the 258-member CROSS-POPULATION
      exemption it targets, replacing a reviewed adjudication with an unrelated
      fact set. Fail-closed afterwards (the digest would not match), but the
      record is gone and the reason string with it.
    * Two crossing components in one report are unioned into one list, which
      invents a component that does not exist.

    So: require the cross-population header, group members under their own
    `component=` line, and refuse unless exactly one component is reported.
    """
    proc = subprocess.run(
        [sys.executable, str(GATE)], capture_output=True, text=True, cwd=ROOT
    )
    text = proc.stdout + proc.stderr

    blocks: dict[str, list[tuple[str, str]]] = {}
    current: str | None = None
    in_cross_population = False
    for line in text.splitlines():
        if line.startswith("declared dependency component crosses") or line.startswith(
            "cross-population evaluation union shares"
        ):
            in_cross_population = "cross-population" in line
            current = None
            continue
        component = re.match(r"^\s+component=(\S+?)…?\s+partitions=", line)
        if component:
            current = component.group(1) if in_cross_population else None
            if current is not None:
                blocks.setdefault(current, [])
            continue
        member = re.match(r"^\s+(F:[^\s]+)\s+->\s+(\S+)", line)
        if member and current is not None:
            blocks[current].append((member.group(1), member.group(2)))

    if not blocks:
        if re.search(r"^\s+(F:[^\s]+)\s+->\s+(\S+)", text, re.M):
            print(
                "RESCOPE|REFUSED|the gate reported a crossing, but none of it is a "
                "CROSS-POPULATION component -- nursery-v1's own component-split check "
                "is red and raises first. Fix that before re-scoping the v2 exemption; "
                "re-scoping now would overwrite it with nursery-v1's fact ids.",
                file=sys.stderr,
            )
            raise Refused
        print("RESCOPE|no crossing component reported -- nothing to re-scope")
        return [], {}, []

    if len(blocks) > 1:
        print(
            f"RESCOPE|REFUSED|{len(blocks)} distinct cross-population components are "
            f"reported ({sorted(blocks)}). This script re-scopes ONE exemption and "
            "cannot tell which; unioning them would invent a component that does not "
            "exist. Re-scope by hand, or split the exemptions first.",
            file=sys.stderr,
        )
        raise Refused

    rows = next(iter(blocks.values()))
    census = collections.Counter(partition for _, partition in rows)
    held_out = sorted({fid for fid, partition in rows if partition == "held-out"})
    return sorted({fid for fid, _ in rows}), dict(census), held_out


def main() -> int:
    try:
        members, census, held_out = live_component()
    except Refused:
        return 2
    if not members:
        return 0

    if held_out:
        print(
            f"RESCOPE|REFUSED|{len(held_out)} HELD-OUT row(s) are inside the crossing "
            f"component: {held_out[:5]}. That is contamination, not routine growth -- "
            "it is a finding for a human to review, and this script will not paper "
            "over it by re-scoping.",
            file=sys.stderr,
        )
        return 2

    manifest = json.loads(EXTENSION.read_text(encoding="utf-8"))
    exemptions = manifest.get("cross_population_component_split_exemptions") or []
    if not exemptions:
        print("RESCOPE|no exemptions present", file=sys.stderr)
        return 1

    target = max(exemptions, key=lambda e: len(e.get("component_fact_ids", [])))
    before = len(target.get("component_fact_ids", []))
    if target.get("component_fact_ids") == members:
        print(f"RESCOPE|already current at {before} members")
        return 0

    target["component_fact_ids"] = members
    base = str(target.get("reason", "")).split(" RE-SCOPED")[0]
    target["reason"] = (
        f"{base} RE-SCOPED {before} -> {len(members)} members by "
        "`rescope-nursery-exemption.py`, which refuses when any member is held-out. "
        f"Partition census at re-scope: {census}. Zero held-out members, so the "
        "crossing stays benign under ADR-0542."
    )

    digest = load_generator_digest()
    body = {k: v for k, v in manifest.items() if k != "extension_sha256"}
    manifest["extension_sha256"] = digest(body)
    EXTENSION.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(
        f"RESCOPE|{before} -> {len(members)} members|census={census}|held_out=0|"
        f"digest={manifest['extension_sha256'][:16]}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
