#!/usr/bin/env python3
"""Build and verify the accepted portable R6 local-shard result authority."""

from __future__ import annotations

import argparse
import shutil
import sys
import tempfile
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import lean_u2_official_execution as BASE  # noqa: E402
from scripts import lean_u2_official_execution_m2_r3 as R3  # noqa: E402
from scripts import lean_u2_official_execution_m2_r6 as R6  # noqa: E402


RESULT = ROOT / "docs/plan/lean-u2-official-execution-tl0.6.3-m2-r6-v1.json"
EVIDENCE_ROOT = R6.DEFAULT_EVIDENCE_ROOT
SCHEMA = "axeyum-lean-u2-official-execution-m2-r6-result-v1"
INVENTORY_DOMAIN = "r6-complete-evidence-pending-validation-v1"
INVENTORY_FILES = 152
INVENTORY_BYTES = 5_246_140
INVENTORY_SHA256 = (
    "73634b06b802b938c604aea100afd3aacf2f727f6ee8275f90566d69d1b3fdb3"
)
VALIDATION_REVISION = "4d0ad392ee514ccd990f69bb46b639accc7ad280"


class R6ResultError(ValueError):
    """The accepted R6 result authority or evidence drifted."""


def portable_inventory(root: Path) -> list[dict[str, Any]]:
    return R3.R2_DIAGNOSTIC.portable_manifest(root)


def validate_evidence_portable(root: Path = EVIDENCE_ROOT) -> dict[str, Any]:
    inventory = portable_inventory(root)
    if (
        len(inventory) != INVENTORY_FILES
        or sum(row["bytes"] for row in inventory) != INVENTORY_BYTES
        or BASE.domain_digest(INVENTORY_DOMAIN, inventory) != INVENTORY_SHA256
    ):
        raise R6ResultError("R6 accepted evidence portable identity drift")
    with tempfile.TemporaryDirectory(prefix="axeyum-r6-result-") as temporary:
        copy = Path(temporary) / "evidence"
        shutil.copytree(root, copy)
        for path in copy.rglob("*"):
            if path.is_file():
                path.chmod(0o444)
        with R6.r6_bindings():
            completion = R6.validate_complete_store(copy)
    if completion["record_sha256"] != (
        "1f0b9af8997d9cced7bbb141e979ecd169b882b3df57ae02b0cb5f34ff0f3b67"
    ):
        raise R6ResultError("R6 accepted completion identity drift")
    return {"inventory": inventory, "completion": completion}


def build_result_authority(root: Path = EVIDENCE_ROOT) -> dict[str, Any]:
    evidence = validate_evidence_portable(root)
    completion = evidence["completion"]
    terminal = BASE.load_canonical(root / "terminal.json")
    junit = BASE.load_canonical(root / "junit.json")
    post = BASE.load_canonical(root / "post.json")
    projection = BASE.load_canonical(root / "projection.json")
    expected_summary = {
        "official_cases": 64,
        "official_outcomes": 64,
        "official_passes": 64,
        "official_failures": 0,
        "unique_new_official_cases": 64,
        "local_physical_shards_completed": 1,
    }
    if (
        terminal["record_sha256"]
        != "9d060439a088800cce1e900cfdf52d6be617956d9d0b33aa70c93f2879e60d81"
        or terminal["class"] != "exited"
        or terminal["exit_code"] != 0
        or junit["record_sha256"]
        != "77054383710c134239b7b002f154118d39958df62f3ac2c3357807aa27c25c50"
        or junit["summary"]
        != {
            "official_cases": 64,
            "official_outcomes": 64,
            "official_passes": 64,
            "official_failures": 0,
        }
        or post["record_sha256"]
        != "5297007237cbc08357f0210c872db40ef5adb4667d348b3cf431d3e470e2f5a1"
        or post["conditional_artifact"]["required"] is not False
        or post["assurance"]["retained_payload_count"] != 66
        or projection["record_sha256"]
        != "a20da2c529137930adab9db5f0332b3572ead5d7876ae34faaea3fe4115688f5"
        or {
            key: projection["credits"][key]
            for key in expected_summary
        }
        != expected_summary
        or completion["credits"] != projection["credits"]
    ):
        raise R6ResultError("R6 accepted terminal/JUnit/post/projection drift")
    return BASE.seal(
        {
            "schema": SCHEMA,
            "status": "accepted-local-official-shard",
            "run_id": R6.RUN_ID,
            "attempt_id": R6.ATTEMPT_ID,
            "sequence": R6.SEQUENCE,
            "shard_id": R6.M2.SHARD_ID,
            "execution_revision": "dc5880332a2805e050021bcf3f403574d3fae237",
            "validation_revision": VALIDATION_REVISION,
            "evidence": {
                "root": str(root.relative_to(ROOT)),
                "files": INVENTORY_FILES,
                "bytes": INVENTORY_BYTES,
                "manifest_domain": INVENTORY_DOMAIN,
                "manifest_sha256": INVENTORY_SHA256,
                "terminal_sha256": terminal["record_sha256"],
                "junit_sha256": junit["record_sha256"],
                "post_sha256": post["record_sha256"],
                "projection_sha256": projection["record_sha256"],
                "completion_sha256": completion["record_sha256"],
            },
            "summary": expected_summary,
            "credits": completion["credits"],
            "claims": {
                "local_official_shard_observed": True,
                "parent_profile_complete": False,
                "official_provider_reproduced": False,
                "axeyum_native_outcomes_observed": False,
                "paired_parity_observed": False,
                "performance_claimed": False,
                "lean_complete_parity": False,
            },
            "record_sha256": "",
        },
        SCHEMA,
    )


def validate_result_authority(data: Any) -> list[str]:
    if not isinstance(data, dict) or not BASE.valid_seal(data, SCHEMA):
        return ["R6 result authority identity drift"]
    try:
        expected = build_result_authority()
    except (R3.R3Error, R6.R6Error, R6ResultError) as error:
        return [f"R6 result evidence validation failed: {error}"]
    return [] if data == expected else ["R6 result authority field drift"]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("result",))
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    try:
        expected = build_result_authority()
        if args.check:
            if not RESULT.is_file() or BASE.load_json(RESULT) != expected:
                raise R6ResultError("committed R6 result authority is stale")
        else:
            RESULT.write_bytes(BASE.canonical_bytes(expected))
        print(
            "LEAN_U2_M2_R6_RESULT|official_outcomes=64|passes=64|"
            "local_shards=1|parent=false|provider=false|axeyum=0|pairs=0|parity=0|"
            f"record={expected['record_sha256']}"
        )
    except (R3.R3Error, R6.R6Error, R6ResultError) as error:
        print(f"LEAN_U2_M2_R6_RESULT_ERROR|{error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
