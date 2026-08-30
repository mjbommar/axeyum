#!/usr/bin/env python3
"""An artifact that cites a gate script must be able to re-run it.

WHY THIS EXISTS
---------------
`98d17aeef` archived 346 `check-*` scripts on the criterion "no live caller in
`scripts/check.sh` or the justfile". That criterion could not see the callers
that matter most here: an artifact under `artifacts/` names the gate that
reviewed it -- a plan cites the gate expected to run, a result or a sealed
capsule cites the gate that reviewed it, then. Those are callers of a different
kind, and 125 cited scripts were swept into `scripts/archive/`, where they are
not merely unlisted but NON-RUNNABLE: every archived script resolves the repo
root as `pathlib.Path(__file__).resolve().parents[1]`, which is `scripts/`
itself once the file sits one level deeper.

Only two of the 125 ever surfaced, because only some artifact classes are
validated for script existence at all. The other 123 sat unnoticed, including
three sealed-capsule receipts that could not be re-checked by anybody.

A receipt nobody can re-check is close to a receipt that says nothing. So the
invariant is:

    a script named by a committed artifact lives in `scripts/`, at the path the
    artifact spells.

WHAT THIS DELIBERATELY DOES NOT ASSERT
--------------------------------------
It does not run the cited scripts and require exit 0. Measured over the 129
restored alongside this gate -- 103 pass, 26 fail -- the failures split by
artifact class:

    capsule   16/16 pass
    result    31/33 pass
    plan      52/76 pass

A result or capsule checker re-verifies a frozen artifact and should pass
forever. A PLAN checker asserts preconditions about the LIVE tree ("target is
still open", "helper identity unchanged") and goes stale by design once the
work it planned lands -- a stale plan gate is the flywheel turning, not a
defect. Requiring exit 0 would therefore red the gate on 24 correctly-stale
plans, and a gate that fires on healthy progress gets disabled. Resolvability
is the property that holds for every class.

GUARDS (each mutation-verified to be killed by exactly one control)
-------------------------------------------------------------------
  escape        a citation resolves outside the repo (absolute, or climbing
                past the root). A plain `../` link is NOT an escape -- markdown
                artifacts cite their gate relatively and resolve correctly.
  dangling      the cited script exists in neither `scripts/` nor the archive
  archived      the cited script exists only in `scripts/archive/`
  path-mismatch the citation spells a directory that is not where the file is
  sibling       a live script invokes a sibling gate that is only in the archive
  vacuity       the scan matched fewer citations than the tree is known to hold

Usage:
    python3 scripts/check-artifact-gate-provenance.py [--json]
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
ARTIFACTS = ROOT / "artifacts"
SCRIPTS = ROOT / "scripts"
ARCHIVE = SCRIPTS / "archive"

# A citation is a gate-script filename, optionally prefixed by the directory the
# artifact believes it lives in. The optional leading `../` and the absolute
# form are matched ONLY so the escape guard can reject them; a plain filename
# with no directory at all is the common shape and is fine.
CITATION = re.compile(
    r"(?P<prefix>/?(?:\.\./)*(?:scripts/)?(?:archive/)?)"
    r"(?P<name>check-[A-Za-z0-9._-]+\.(?:py|sh))"
)

# Vacuity floors. On the tree where this gate was written the scan found 578
# (artifact, citation) pairs and 182 sibling references. The floors
# sit well under those and far above zero, so they fail loudly if the walk stops
# reaching `artifacts/` or the regex stops matching -- the failure mode where a
# checker reports a clean tree because it looked at nothing.
MIN_ARTIFACT_CITATIONS = 300
MIN_SIBLING_REFERENCES = 100

# Scanning every artifact byte is the point, but a couple of trees under
# `artifacts/` are vendored corpora and opaque blobs where a `check-*.py`
# substring would not be a citation.
SKIP_DIRS = {"instances", "fixtures"}


def _read(path: pathlib.Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return ""


def _walk(base: pathlib.Path):
    for dirpath, dirnames, filenames in os.walk(base):
        rel = pathlib.Path(dirpath).relative_to(base)
        if rel.parts and rel.parts[0] in SKIP_DIRS:
            dirnames[:] = []
            continue
        dirnames.sort()
        for name in sorted(filenames):
            yield pathlib.Path(dirpath) / name


def scan_artifact_citations(root: pathlib.Path = ROOT):
    """Yield (artifact_relpath, raw_citation, prefix, name) for every mention."""
    for path in _walk(root / "artifacts"):
        text = _read(path)
        if "check-" not in text:
            continue
        rel = path.relative_to(root).as_posix()
        seen = set()
        for match in CITATION.finditer(text):
            raw = match.group(0)
            if raw in seen:
                continue
            seen.add(raw)
            yield rel, raw, match.group("prefix"), match.group("name")


def _resolutions(artifact_rel: str, raw: str) -> set[str]:
    """Every repo-relative path the citation could reasonably denote.

    Two conventions are in use and both are correct in their own context. A
    JSON artifact writes `scripts/check-X.py` meaning repo-root-relative; a
    markdown artifact writes `../../../scripts/check-X.py` meaning relative to
    its own directory. A citation is honest if the file sits at either reading,
    so resolve both and let the caller test membership. Anything landing
    outside the repo is dropped, which is what makes the set empty for a real
    escape.
    """
    artifact_dir = os.path.dirname(artifact_rel)
    out = set()
    for base in ("", artifact_dir):
        resolved = os.path.normpath(os.path.join(base, raw))
        if resolved.startswith(".." + os.sep) or resolved == "..":
            continue
        out.add(pathlib.PurePosixPath(resolved).as_posix())
    return out


def scan_sibling_references(root: pathlib.Path = ROOT):
    """Yield (script_relpath, name) for `scripts/check-*` inside a live script."""
    pattern = re.compile(r"scripts/(check-[A-Za-z0-9._-]+\.(?:py|sh))")
    for entry in sorted((root / "scripts").iterdir()):
        if not entry.is_file() or entry.suffix not in {".py", ".sh"}:
            continue
        for name in dict.fromkeys(pattern.findall(_read(entry))):
            if name == entry.name:
                continue
            yield entry.relative_to(root).as_posix(), name


def check(root: pathlib.Path = ROOT, floors: bool = True):
    scripts_dir = root / "scripts"
    archive_dir = scripts_dir / "archive"
    live = {p.name for p in scripts_dir.iterdir() if p.is_file()}
    archived = (
        {p.name for p in archive_dir.iterdir() if p.is_file()}
        if archive_dir.is_dir()
        else set()
    )

    failures: list[tuple[str, str]] = []
    artifact_citations = 0
    sibling_references = 0

    for rel, raw, prefix, name in scan_artifact_citations(root):
        artifact_citations += 1

        # escape -- a citation must land inside the repo. Checked first: the
        # location guards below would otherwise resolve it against the wrong
        # base. `..` on its own is NOT an escape: a markdown artifact links its
        # gate relatively (`../../../scripts/check-claim-certificates.py`) and
        # that is a correct, resolvable path.
        candidates = _resolutions(rel, raw)
        if raw.startswith("/") or not candidates:
            failures.append(
                ("escape", f"{rel} cites {raw!r}: does not resolve inside the repo")
            )
            continue

        # dangling -- names a script that is nowhere in the tree.
        if name not in live and name not in archived:
            failures.append(
                (
                    "dangling",
                    f"{rel} cites {name}, which exists in neither "
                    f"scripts/ nor scripts/archive/",
                )
            )
            continue

        # archived -- the citation IS a caller, so the cited gate may not sit in
        # the archive, where `parents[1]` resolves to `scripts/` and the script
        # cannot run at all.
        if name in archived:
            failures.append(
                (
                    "archived",
                    f"{rel} cites {name}, which is archived; a cited gate must "
                    f"live in scripts/ to be re-runnable",
                )
            )
            continue

        # path-mismatch -- the file is live, so if the artifact spelled a
        # directory at all it must be one that resolves to where the file
        # actually is, under either convention.
        if prefix.strip("/") and f"scripts/{name}" not in candidates:
            failures.append(
                (
                    "path-mismatch",
                    f"{rel} cites {raw}, which resolves to "
                    f"{sorted(candidates)}, but {name} lives in scripts/",
                )
            )

    for rel, name in scan_sibling_references(root):
        sibling_references += 1
        if name in archived and name not in live:
            failures.append(
                (
                    "sibling",
                    f"{rel} invokes scripts/{name}, which is archived and "
                    f"cannot run from there",
                )
            )

    # vacuity -- every guard above can only fire on input it was given. If the
    # walk or the regex silently stops producing citations, all of them pass and
    # the gate reports a clean tree it never looked at.
    if floors and artifact_citations < MIN_ARTIFACT_CITATIONS:
        failures.append(
            (
                "vacuity",
                f"only {artifact_citations} artifact citations scanned "
                f"(floor {MIN_ARTIFACT_CITATIONS}); the scan is not reaching artifacts/",
            )
        )
    if floors and sibling_references < MIN_SIBLING_REFERENCES:
        failures.append(
            (
                "vacuity",
                f"only {sibling_references} sibling references scanned "
                f"(floor {MIN_SIBLING_REFERENCES}); the scan is not reaching scripts/",
            )
        )

    return failures, artifact_citations, sibling_references, len(live), len(archived)


def main() -> int:
    parser = argparse.ArgumentParser(description="check artifact gate provenance")
    parser.add_argument(
        "--json", action="store_true", help="emit machine-readable output"
    )
    args = parser.parse_args()

    failures, citations, siblings, n_live, n_archived = check()

    if args.json:
        print(
            json.dumps(
                {
                    "ok": not failures,
                    "artifact_citations": citations,
                    "sibling_references": siblings,
                    "live_scripts": n_live,
                    "archived_scripts": n_archived,
                    "failures": [{"guard": g, "detail": d} for g, d in failures],
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 1 if failures else 0

    if failures:
        for guard, detail in failures:
            print(f"ARTIFACT_GATE_PROVENANCE_ERROR|{guard}|{detail}")
        by_guard: dict[str, int] = {}
        for guard, _ in failures:
            by_guard[guard] = by_guard.get(guard, 0) + 1
        summary = ",".join(f"{g}={n}" for g, n in sorted(by_guard.items()))
        print(
            f"ARTIFACT_GATE_PROVENANCE_ERROR|{len(failures)} broken gate "
            f"citations|{summary}"
        )
        return 1

    print(
        f"ARTIFACT_GATE_PROVENANCE_OK|artifact_citations={citations}"
        f"|sibling_references={siblings}|live={n_live}|archived={n_archived}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
