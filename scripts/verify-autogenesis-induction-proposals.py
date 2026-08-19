#!/usr/bin/env python3
"""Verify an induction proposal bundle against its exact input catalog."""

from __future__ import annotations

import argparse
import importlib.util
import json
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[1]
PROPOSER = ROOT / "scripts/autogenesis-induction-proposer.py"


class ProposalError(RuntimeError):
    """The proposal output is malformed, mutated, or stale."""


def load_proposer():
    spec = importlib.util.spec_from_file_location("autogenesis_induction_proposer", PROPOSER)
    if spec is None or spec.loader is None:
        raise ProposalError(f"cannot load {PROPOSER}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def verify(catalog: dict, bundle: dict, tsv: str) -> None:
    proposer = load_proposer()
    claimed = bundle.get("bundle_sha256")
    unsigned = dict(bundle)
    unsigned.pop("bundle_sha256", None)
    if claimed != proposer.digest(unsigned):
        raise ProposalError("bundle_sha256 does not match proposal content")
    try:
        expected = proposer.build_bundle(catalog)
    except (KeyError, TypeError, ValueError) as error:
        raise ProposalError(f"cannot derive proposals from catalog: {error}") from error
    if bundle != expected:
        raise ProposalError("proposal bundle is internally valid but not derived from the catalog")
    if tsv != proposer.render_tsv(expected):
        raise ProposalError("TSV checker projection disagrees with the verified JSON bundle")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--catalog", required=True, type=pathlib.Path)
    parser.add_argument("--bundle", required=True, type=pathlib.Path)
    parser.add_argument("--tsv", required=True, type=pathlib.Path)
    args = parser.parse_args()
    try:
        catalog = json.loads(args.catalog.read_text())
        bundle = json.loads(args.bundle.read_text())
        verify(catalog, bundle, args.tsv.read_text())
        print(
            f"AUTOGENESIS_INDUCTION_PROPOSALS_OK|phase={bundle['phase']}|"
            f"plans={len(bundle['plans'])}|bundle={bundle['bundle_sha256']}"
        )
        return 0
    except (OSError, json.JSONDecodeError, KeyError, ProposalError) as error:
        print(f"AUTOGENESIS_INDUCTION_PROPOSALS_ERROR|{error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
