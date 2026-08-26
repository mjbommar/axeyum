#!/usr/bin/env python3
"""Generate the checked Lean-arrow statement-export capability receipt.

The large NDJSON streams stay in the external reference pack.  This projection
binds their bytes to the exact fact statements and then imports every stream
through Axeyum's proof-isolation boundary.  A successful exporter process alone
is deliberately insufficient evidence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from axeyum import producers

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "artifacts/autogenesis/binomial-arrow-export-capability-v1.json"
PACK = Path("/nas3/data/axeyum/autogenesis/reference-packs/86688948e-binomial-arrow-statements-v1")
EXPECTED = {
    "F:ml430-nat-choose-eq-zero-of-lt-92ebab29": {
        "target": "Axeyum.Autogenesis.Statement.Generated.natChooseEqZeroOfLt",
        "stream_sha256": "126f7cca3feab5f58919f49f83699ded935264e59953803ec247b278f0802221",
        "measurement_stream_sha256": "37b51b79a569d67f083514b86b0ed731aa877144cdbf5ef6c3c6b6806ac1b82d",
    },
    "F:ml430-nat-choose-ne-zero-49c3d3cb": {
        "target": "Axeyum.Autogenesis.Statement.Generated.natChooseNeZero",
        "stream_sha256": "cc4cce2cc4a91144543ef81e44e1a52ac416839ef772d81ce2b27a729060d8ca",
        "measurement_stream_sha256": "e5882423a2bca8f8c2811796db3c5adb75419c06942d86f50e903badc6a3200b",
    },
    "F:ml430-nat-choose-symm-of-eq-add-9b5f9a20": {
        "target": "Axeyum.Autogenesis.Statement.Generated.natChooseSymmOfEqAdd",
        "stream_sha256": "412388246c1027be27f677b56693d52ff62646e924cdbbe0352895918cb6ea20",
        "measurement_stream_sha256": "5ce7f332fea4fcf9b26e98345248a0e5ebd8b77d3d8139af551d0c2907bb96b4",
    },
}
SOURCE_SHA256 = "d97a9f22bf9965a140e2dc5273fa8ed32a3a511db073995e939d58fc91e702e2"
MAP_SHA256 = "16fab9a5d10f076b9b92d011d14a159062a67ac9d253718a825b7886d1f9bd02"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def build(pack: Path = PACK) -> dict[str, Any]:
    source = pack / "AxeyumBinomialArrowBatchV1.lean"
    mapping_path = pack / "map.json"
    source_bytes = source.read_bytes()
    mapping_bytes = mapping_path.read_bytes()
    require(digest(source_bytes) == SOURCE_SHA256, "adapter source changed")
    require(digest(mapping_bytes) == MAP_SHA256, "fact-to-target map changed")
    mapping = json.loads(mapping_bytes)
    require(mapping == {key: row["target"] for key, row in EXPECTED.items()}, "map disagrees")

    rows = []
    for fact_id, expected in sorted(EXPECTED.items()):
        fact_path = ROOT / "artifacts/facts" / f"{fact_id.replace(':', '-', 1)}.json"
        fact = json.loads(fact_path.read_text())
        statement = fact.get("formal", {}).get("statement")
        require(
            isinstance(statement, str) and ("→" in statement or "↔" in statement),
            f"{fact_id} is no longer arrow-bearing",
        )
        filename = f"{fact_id.replace(':', '-', 1)}.ndjson"
        stream = pack / "target-only" / filename
        payload = stream.read_bytes()
        require(digest(payload) == expected["stream_sha256"], f"{fact_id} stream changed")
        measurement_stream = pack / "streams" / filename
        measurement_payload = measurement_stream.read_bytes()
        require(
            digest(measurement_payload) == expected["measurement_stream_sha256"],
            f"{fact_id} measurement stream changed",
        )
        imported = producers.import_statement_ndjson(payload, None, expected["target"])
        report = imported.report()
        target_identity = next(
            row for row in report.declaration_identities if row.name == expected["target"]
        )
        require(target_identity.kind == "definition", f"{fact_id} target is not a definition")
        require(report.axioms == [], f"{fact_id} import retained axioms")
        require(report.substituted_theorems == [], f"{fact_id} import exposed theorem proofs")
        require(report.lean_version == "4.30.0", f"{fact_id} Lean version drifted")
        require(report.exporter_version == "3.1.0", f"{fact_id} exporter version drifted")
        rows.append(
            {
                "fact_id": fact_id,
                "formal_statement_sha256": digest(statement.encode()),
                "target_definition": expected["target"],
                "target_content_sha256": target_identity.content_sha256,
                "stream": str(stream),
                "stream_bytes": len(payload),
                "stream_records": len(payload.splitlines()),
                "stream_sha256": expected["stream_sha256"],
                "measurement_stream": str(measurement_stream),
                "measurement_stream_bytes": len(measurement_payload),
                "measurement_stream_records": len(measurement_payload.splitlines()),
                "measurement_stream_sha256": expected["measurement_stream_sha256"],
                "admitted_declarations": report.admitted_declarations,
                "axioms": report.axioms,
                "substituted_theorems": report.substituted_theorems,
                "goal_rendered": imported.kernel().render_lean(imported.goal()),
                "proof_isolated_import": "accepted",
            }
        )

    return {
        "schema_version": 1,
        "kind": "axeyum-binomial-arrow-export-capability",
        "state": "three-arrow-statements-exported-and-proof-isolated",
        "claim": (
            "lean4export 3.1.0 can export implication-bearing Prop definitions; "
            "Axeyum independently imported all three without axioms or theorem proofs"
        ),
        "non_claims": [
            "the propositions are proved",
            "the current producer can prove the propositions",
            "every Lean surface statement is exportable",
        ],
        "source": {
            "external_pack": str(pack),
            "adapter_source_sha256": SOURCE_SHA256,
            "mapping_sha256": MAP_SHA256,
            "mathlib_commit": "c5ea00351c28e24afc9f0f84379aa41082b1188f",
            "lean_version": "4.30.0",
            "lean_githash": "d024af099ca4bf2c86f649261ebf59565dc8c622",
            "lean4export_commit": "a3e35a584f59b390667db7269cd37fca8575e4bf",
            "lean4export_version": "3.1.0",
            "lean4export_binary_sha256_observed_on_s5": (
                "8e763913b03762488571a93ced6ec1a4e04f7d8eebbe40bd1215ba41a6bd4449"
            ),
            "transport": "exporter stdout streamed over SSH to avoid the s5 disk quota",
        },
        "census": {
            "arrow_statements": len(rows),
            "exported": len(rows),
            "proof_isolated_imports": len(rows),
            "axioms": sum(len(row["axioms"]) for row in rows),
            "substituted_theorems": sum(len(row["substituted_theorems"]) for row in rows),
        },
        "rows": rows,
        "correction": (
            "The 2026-08-25 arrow-ceiling diagnosis conflated an output/storage failure "
            "with exporter semantics. --exportable-only remains only as a legacy replay filter."
        ),
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    rendered = json.dumps(build(), indent=2, sort_keys=True) + "\n"
    if args.check:
        if not args.output.is_file() or args.output.read_text() != rendered:
            print("BINOMIAL_ARROW_EXPORT_ERROR|artifact is stale")
            return 1
    else:
        args.output.write_text(rendered)
    data = json.loads(rendered)
    print(
        "BINOMIAL_ARROW_EXPORT|"
        f"exported={data['census']['exported']}|"
        f"proof_isolated={data['census']['proof_isolated_imports']}|"
        f"axioms={data['census']['axioms']}|theorem_proofs={data['census']['substituted_theorems']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
