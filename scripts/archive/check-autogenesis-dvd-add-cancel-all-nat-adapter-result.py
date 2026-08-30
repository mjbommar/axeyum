#!/usr/bin/env python3
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/dvd-add-cancel-all-nat-adapter-result-v1.json"

def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> None:
    result = json.loads(RESULT.read_text())
    assert result["state"] == "adapter-reconstructed-twice-empty-footprint"
    assert digest(ROOT / result["plan"]["path"]) == result["plan"]["sha256"]
    assert digest(ROOT / result["source"]["path"]) == result["source"]["sha256"]
    pack = Path(result["evidence"]["pack"])
    assert digest(pack / "manifest.json") == result["evidence"]["manifest_sha256"]
    assert digest(pack / "adapter.ndjson") == result["evidence"]["stream_sha256"]
    assert digest(pack / "audit-1.json") == result["evidence"]["audit_sha256"] == digest(pack / "audit-2.json")
    assert result["theorem"]["axiom_footprint"] == [] and result["theorem"]["fresh_reconstructions"] == 2
    assert result["authority"]["all_nat_adapter_credit"] == 1
    assert all(value == 0 for key, value in result["authority"].items() if key != "all_nat_adapter_credit")
    print("AUTOGENESIS_DVD_ADD_CANCEL_ALL_NAT_ADAPTER_RESULT_OK|runs=2|footprint=0|positive=parameter|official=0")

if __name__ == "__main__":
    main()
