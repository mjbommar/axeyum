#!/usr/bin/env python3
"""Install axeyum-native certificates into the claim ledger (B8/F6, roadmap R3).

Consumes the results of `recertify-claims.py` (one JSON line per claim,
every line `verified`) and, for each named evidence row:

  * replaces the stored artifact with the gzipped TEXT DRAT proof axeyum's
    own core produced and its own backward checker verified;
  * flips the row from `replay-only` to `checked` and declares the format;
  * records the re-derivation's falsifiable numbers (steps, hashes, times);
  * moves kissat/drat-trim out of the trusted path WITHOUT erasing that they
    were the original disposer — they stay as HISTORICAL provenance lines;
  * pins the producing toolchain (axeyum commit, rustc, target).

usage:
  scripts/apply-recertified-claims.py results.jsonl [more.jsonl ...]
"""
from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

OLD_SEARCH = "kissat 4.0.4 (rel-4.0.4)"
OLD_CHECK = "drat-trim (2026 build, references/drat-trim)"


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True,
                          text=True, check=True).stdout.strip()


def main() -> int:
    rows: dict[str, dict] = {}
    for path in sys.argv[1:]:
        for line in Path(path).read_text().splitlines():
            r = json.loads(line)
            rows[r["id"]] = r
    if not rows:
        print("no result rows given", file=sys.stderr)
        return 2
    unverified = [i for i, r in rows.items() if r.get("status") != "verified"]
    if unverified:
        print(f"refusing: unverified rows {unverified}", file=sys.stderr)
        return 1

    axeyum_commit = git("rev-parse", "HEAD")
    dirty = bool(git("status", "--porcelain",
                     "--", "crates", "Cargo.toml", "Cargo.lock"))
    rustc = subprocess.run(["rustc", "--version"], capture_output=True,
                           text=True, check=True).stdout.strip()

    touched = 0
    for cj in sorted((ROOT / "artifacts/claims/rado").glob("*/claim.json")):
        c = json.loads(cj.read_text())
        r = rows.get(c["id"])
        if r is None:
            continue
        ev = next(e for e in c["evidence"] if e["id"] == r["ev"])
        art = ROOT / ev["artifact"]
        old_sha = ev["artifact_sha256"]
        old_bytes = art.stat().st_size
        shutil.copyfile(r["gz"], art)
        assert sha256(art) == r["gz_sha256"], "copied artifact hash drift"

        p = c["formal"]["parameters"]
        ev["artifact_sha256"] = r["gz_sha256"]
        ev["artifact_format"] = "drat-text-gzip"
        ev["check_status"] = "checked"
        ev["parameters"] = {
            "producer": "axeyum solve_with_drat_proof_streaming + TextProofSink "
                        "(crates/axeyum-cnf, ADR-0381)",
            "checker": "axeyum check_drat_backward (crates/axeyum-cnf, ADR-0382)",
            "proof_steps": r["steps"],
            "proof_bytes": r["drat_bytes"],
            "proof_sha256": r["payload_sha256"],
            "solve_seconds": r["solve_s"],
            "check_seconds": r["check_s"],
        }
        ev["checker_command"] = (
            f"cargo run --release -p axeyum-search --example recertify_rado -- "
            f"{p['a']} {p['b']} {p['k']} {p['n']} {ev['artifact'].replace('.drat.gz', '.cnf')} "
            f"/tmp/{c['id']}.drat 1.0"
            f"   # regenerates the CNF (byte-compared against the stored one), re-solves "
            f"with axeyum's proof-producing core, and re-derives the proof with axeyum's "
            f"backward DRAT checker; the stored artifact is the gzip of exactly such a run")
        ev["notes"] = (
            f"RE-CERTIFIED {r.get('date', '2026-08-12')} inside axeyum's own stack: the "
            f"proof was produced by the in-tree proof-producing CDCL core streaming TEXT "
            f"DRAT to disk ({r['solve_s']:.3f} s, {r['steps']} steps), read back through "
            f"axeyum's own parse_drat, and re-derived by axeyum's own backward DRAT "
            f"checker ({r['check_s']:.3f} s). No external solver and no external checker "
            f"took part. SUPERSEDES the original kissat certificate (sha256 {old_sha}, "
            f"{old_bytes} bytes), which was BINARY DRAT: drat-trim verified it, but "
            f"axeyum's own parse_drat reads text DRAT, so the shipped system could not "
            f"read the certificate it shipped (findings register B8). The deciding CNF "
            f"beside it regenerates byte-identically from the claim's parameters.")

        prov = c["provenance"]
        prov["searched_by"] = [
            ("axeyum proof-producing CDCL core (solve_with_drat_proof_streaming, "
             f"pure Rust, ADR-0381): produced the stored certificate in "
             f"{r['solve_s']:.3f} s")
            if s == OLD_SEARCH else s for s in prov["searched_by"]]
        if not any("HISTORICAL" in s and "kissat" in s for s in prov["searched_by"]):
            prov["searched_by"].append(
                "HISTORICAL (superseded, ADR-0002 oracle role only): kissat 4.0.4 "
                "(rel-4.0.4) produced the original binary-DRAT certificate for this "
                "instance on 2026-08-12")
        prov["checked_by"] = [
            ("axeyum in-tree backward DRAT checker (check_drat_backward, ADR-0382, "
             f"pure Rust): re-derived all {r['steps']} steps of the stored "
             f"certificate in {r['check_s']:.3f} s")
            if s == OLD_CHECK else s for s in prov["checked_by"]]
        if not any("HISTORICAL" in s and "drat-trim" in s for s in prov["checked_by"]):
            prov["checked_by"].append(
                "HISTORICAL (no longer in the trusted path): drat-trim (2026 build, "
                "references/drat-trim) verified the superseded kissat binary-DRAT "
                "certificate on 2026-08-12")
        prov["toolchain"] = {
            "axeyum_commit": axeyum_commit,
            "rustc_version": rustc,
            "target": "x86_64-unknown-linux-gnu",
            "dirty": dirty,
        }

        cj.write_text(json.dumps(c, indent=2, ensure_ascii=False) + "\n")
        touched += 1
        print(f"updated {c['id']}")
    print(f"\n{touched} claim records updated")
    missing = set(rows) - {
        json.loads(cj.read_text())["id"]
        for cj in (ROOT / "artifacts/claims/rado").glob("*/claim.json")}
    if missing:
        print(f"WARNING: results for unknown claims: {sorted(missing)}",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    main()
