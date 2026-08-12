#!/usr/bin/env python3
"""Drive `recertify_rado` over ledger claims whose UNSAT certificate needs
regenerating with axeyum's own proof core (findings B8/F6, roadmap R3).

Selects every `unsat-certificate` evidence row whose artifact is a
`*.drat.gz` and whose `check_status` is not already `checked` (pass
`--all` to redo checked rows too). For each: runs the in-tree example
binary (solve + stream text DRAT + backward-check, all axeyum), gzips the
proof deterministically (mtime=0), and emits one JSON line with the
falsifiable numbers and both hashes. `apply-recertified-claims.py`
installs the results into the ledger.

The compute can be split across hosts with `--ids`/`--skip-ids`; merge the
result files by concatenation.

usage:
  scripts/recertify-claims.py --bin target/release/examples/recertify_rado \
      --proof-dir /tmp/proofs --out results.jsonl [--workers 2] \
      [--hours 0.5] [--ids id1,id2,...] [--all]
"""
from __future__ import annotations

import argparse
import concurrent.futures as cf
import gzip
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def jobs(only: set[str] | None, skip: set[str], redo_checked: bool) -> list[dict]:
    out = []
    for cj in sorted((ROOT / "artifacts" / "claims" / "rado").glob("*/claim.json")):
        c = json.loads(cj.read_text())
        if only is not None and c["id"] not in only:
            continue
        if c["id"] in skip:
            continue
        p = c["formal"]["parameters"]
        for ev in c["evidence"]:
            art = ev.get("artifact", "")
            if ev.get("kind") != "unsat-certificate" or not art.endswith(".drat.gz"):
                continue
            if ev.get("check_status") == "checked" and not redo_checked:
                continue
            base = Path(art).name[: -len(".drat.gz")]
            out.append({
                "id": c["id"], "ev": ev["id"],
                "a": p["a"], "b": p["b"], "k": p["k"], "n": p["n"],
                "cnf": str(cj.parent / (base + ".cnf")),
                "artifact": art,
            })
    # Biggest first so workers stay busy to the end.
    out.sort(key=lambda j: -(j["n"] * j["k"]))
    return out


def run(job: dict, bin_path: Path, proof_dir: Path, hours: str) -> dict:
    drat = proof_dir / f"{job['id']}.drat"
    r = subprocess.run(
        [str(bin_path), str(job["a"]), str(job["b"]), str(job["k"]), str(job["n"]),
         job["cnf"], str(drat), hours],
        capture_output=True, text=True)
    try:
        res = json.loads(r.stdout.strip().splitlines()[-1])
    except Exception:
        res = {"status": "driver-error", "stdout": r.stdout[-300:],
               "stderr": r.stderr[-300:]}
    res.update({"id": job["id"], "ev": job["ev"], "artifact": job["artifact"],
                "exit": r.returncode})
    if res.get("status") == "verified":
        # Deterministic gzip (mtime=0, no filename) so the artifact bytes are
        # reproducible from the proof bytes alone.
        gz = proof_dir / f"{job['id']}.drat.gz"
        with open(drat, "rb") as f_in, open(gz, "wb") as f_out:
            with gzip.GzipFile(fileobj=f_out, mode="wb", mtime=0) as z:
                while chunk := f_in.read(1 << 20):
                    z.write(chunk)
        res["payload_sha256"] = sha256(drat)
        res["gz_sha256"] = sha256(gz)
        res["gz"] = str(gz)
        drat.unlink()  # the gz is the artifact; the raw proof can be large
    print(f"{job['id']:<24} {res.get('status'):<12} steps={res.get('steps')} "
          f"solve={res.get('solve_s')} check={res.get('check_s')}", flush=True)
    return res


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bin", required=True, type=Path)
    ap.add_argument("--proof-dir", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--hours", default="0.5")
    ap.add_argument("--ids", help="comma-separated claim ids to run (default all)")
    ap.add_argument("--skip-ids", default="", help="comma-separated claim ids to skip")
    ap.add_argument("--all", action="store_true",
                    help="also redo rows already marked checked")
    args = ap.parse_args()

    args.proof_dir.mkdir(parents=True, exist_ok=True)
    only = set(args.ids.split(",")) if args.ids else None
    skip = set(filter(None, args.skip_ids.split(",")))
    js = jobs(only, skip, args.all)
    print(f"{len(js)} claims to re-certify", flush=True)
    results = []
    with cf.ThreadPoolExecutor(max_workers=args.workers) as ex:
        futures = [ex.submit(run, j, args.bin, args.proof_dir, args.hours) for j in js]
        for fut in futures:
            results.append(fut.result())
    args.out.write_text("".join(json.dumps(r) + "\n" for r in results))
    bad = [r for r in results if r.get("status") != "verified"]
    print(f"\n{len(results) - len(bad)} verified, {len(bad)} not verified")
    for r in bad:
        print(f"  NOT VERIFIED {r['id']}: {r.get('status')}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
