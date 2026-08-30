#!/usr/bin/env python3
"""Validate the sealed exact Int.gcd_fib theorem."""

import hashlib, json, pathlib, stat, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
RESULT = ROOT / "artifacts/autogenesis/mathlib-int-gcd-fib-construction-result-v13.json"
PACK = pathlib.Path("/nas3/data/axeyum/autogenesis/reference-packs/int-gcd-fib-exact-v1")

def sha256(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def mode(path): return f"{stat.S_IMODE(path.stat().st_mode):04o}"

def main():
    try:
        result = json.loads(RESULT.read_text()); capsule = pathlib.Path(result["capsule"]["path"])
        dependencies = ["Axeyum.Autogenesis.intFibNatAbsV1", "Eq.symm", "Eq.trans", "Int.gcd_def", "Nat.fib_gcd"]
        valid = (result.get("state") == "exact-int-gcd-fib-constructed-exported-and-twice-reimported-empty-footprint"
            and sha256(ROOT / result["plan"]["path"]) == result["plan"].get("sha256")
            and sha256(ROOT / result["producer"]["path"]) == result["producer"].get("sha256")
            and result["target"].get("name") == "Int.gcd_fib" and result["target"].get("axiom_footprint") == []
            and result["target"].get("direct_theorem_dependencies") == dependencies
            and result["int_gcd_def"].get("axiom_footprint") == [] and result["int_gcd_def"].get("direct_theorem_dependencies") == []
            and sha256(capsule) == result["capsule"].get("sha256") and capsule.stat().st_size == result["capsule"].get("bytes")
            and mode(capsule) == result["capsule"].get("mode")
            and sha256(PACK / "manifest.json") == result["capsule"].get("manifest_sha256") and mode(PACK) == result["capsule"].get("directory_mode")
            and result["execution"].get("complete_invocations") == 1 and result["execution"].get("fresh_target_imports") == 2
            and result["execution"].get("retries") == 0 and result["execution"].get("ledger_writes") == 0
            and result["authority"].get("fact_status_changes") == 0 and result["authority"].get("rendered_material") == 0)
        if not valid: raise ValueError("exact Int.gcd_fib evidence changed")
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"autogenesis-int-gcd-fib-construction-result-v13: FAIL: {error}", file=sys.stderr); return 1
    print("autogenesis-int-gcd-fib-construction-result-v13: PASS: target=Int.gcd_fib|axioms=0|dependencies=5|fresh_imports=2|ledger_writes=0"); return 0

if __name__ == "__main__": raise SystemExit(main())
