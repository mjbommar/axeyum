#!/usr/bin/env python3
"""Generate read-only proposals for exact proposition reconciliation."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FACTS = ROOT / "artifacts/facts"
CENSUS = ROOT / "artifacts/autogenesis/open-ranked-proposition-census-v1.json"
INDEX = ROOT / "artifacts/autogenesis/kernel-lemma-search-index-pre-reconciliation-v1.json"
OVERLAY = ROOT / "artifacts/autogenesis/knowledge-overlay-v1.json"
TRANSACTION = ROOT / "scripts/prepare-autogenesis-fact-transaction.py"
OUTPUT = ROOT / "artifacts/autogenesis/proposition-reconciliation-proposals-v1.json"


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_module():
    spec = importlib.util.spec_from_file_location("reconciliation_transaction", TRANSACTION)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {TRANSACTION}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def fact_path(fact_id: str) -> Path:
    return FACTS / f"{fact_id.replace(':', '-')}.json"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    census = json.loads(CENSUS.read_text())
    index = json.loads(INDEX.read_text())
    overlay = json.loads(OVERLAY.read_text())
    transaction = load_module()
    lemmas = {row["kernel_declaration_id"]: row for row in index["lemmas"]}
    links = {
        (row.get("source", {}).get("id"), row.get("target", {}).get("id")): row
        for row in overlay["links"]
        if row.get("relation") == "definitionally-matches"
    }
    census_sha = file_sha256(CENSUS)
    proposals = []
    for match in census["matches"]:
        fact_id = match["fact_id"]
        theorem = match["native_theorem"]
        exact_facts = lemmas[theorem]["exact_fact_ids"]
        if len(exact_facts) != 1:
            raise RuntimeError(f"{theorem}: expected one exact native fact, got {exact_facts}")
        before = json.loads(fact_path(fact_id).read_text())
        native = json.loads(fact_path(exact_facts[0]).read_text())
        link = links.get((fact_id, theorem))
        if link is None:
            raise RuntimeError(f"missing exact overlay link: {fact_id} -> {theorem}")
        proposals.append(
            transaction.build_proposition_reconciliation_transaction(
                before_fact=before,
                native_fact=native,
                match=match,
                overlay_link=link,
                census_sha256=census_sha,
            )
        )

    artifact = {
        "schema_version": 1,
        "kind": "axeyum-proposition-reconciliation-proposals",
        "state": "prepared-read-only-no-ledger-writes",
        "source": {
            "census_sha256": census_sha,
            "kernel_lemma_index_path": str(INDEX.relative_to(ROOT)),
            "kernel_lemma_index_sha256": file_sha256(INDEX),
            "knowledge_overlay_sha256": file_sha256(OVERLAY),
            "transaction_builder_sha256": file_sha256(TRANSACTION),
        },
        "summary": {
            "proposal_count": len(proposals),
            "authoritative_ledger_writes": 0,
            "operation_count": 0,
            "autonomous_credit_count": 0,
        },
        "proposals": proposals,
        "next": "Version the pre-reconciliation evaluation artifacts, then apply these exact proposals through a crash-safe checked writer and regenerate all affected views.",
    }
    rendered = json.dumps(artifact, indent=2, sort_keys=True) + "\n"
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != rendered:
            raise SystemExit(f"stale generated artifact: {OUTPUT.relative_to(ROOT)}")
    else:
        OUTPUT.write_text(rendered)
    print(
        f"AUTOGENESIS_RECONCILIATION_PROPOSALS_OK|proposals={len(proposals)}|"
        "writes=0|operations=0|autonomous=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
