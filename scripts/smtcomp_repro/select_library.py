"""Apply SMT-COMP §6 benchmark selection across a full SMT-LIB tree.

Walks a corpus root whose immediate subdirectories are logics
(`<root>/<LOGIC>/<submitter>/.../*.smt2`), applies the §6 per-division cap +
seeded family sampling (from selection.py) to each logic independently, and
writes:
  - a combined selected file list (one path per line), and
  - a manifest JSON: per-logic pool size, cap, and selected count.

Usage:
  python3 select_library.py <corpus_root> --seed 20260721 \
      --out-list selected.txt --out-manifest selection_manifest.json
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import sys
import zlib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from selection import select_division  # noqa: E402


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("corpus_root")
    ap.add_argument("--seed", type=int, default=20260721)
    ap.add_argument("--out-list", required=True)
    ap.add_argument("--out-manifest", required=True)
    args = ap.parse_args()

    root = args.corpus_root
    logics = sorted(
        d for d in os.listdir(root) if os.path.isdir(os.path.join(root, d))
    )
    selected: list[str] = []
    manifest = {"seed": args.seed, "corpus_root": root, "logics": {}}
    for lg in logics:
        lg_dir = os.path.join(root, lg)
        files = glob.glob(os.path.join(lg_dir, "**", "*.smt2"), recursive=True)
        if not files:
            continue
        # per-logic seed (deterministic across runs) so adding/removing a logic
        # doesn't reshuffle the others
        lg_seed = args.seed + (zlib.crc32(lg.encode()) % 100000)
        res = select_division(files, root, seed=lg_seed)
        selected.extend(res.selected)
        manifest["logics"][lg] = {
            "pool": res.n_pool,
            "cap": res.cap,
            "selected": len(res.selected),
            "families": res.n_families,
        }

    selected.sort()
    with open(args.out_list, "w", encoding="utf-8") as fh:
        fh.write("\n".join(selected) + "\n")
    manifest["total_pool"] = sum(v["pool"] for v in manifest["logics"].values())
    manifest["total_selected"] = len(selected)
    with open(args.out_manifest, "w", encoding="utf-8") as fh:
        json.dump(manifest, fh, indent=2)

    print(f"logics={len(manifest['logics'])}  "
          f"pool={manifest['total_pool']}  selected={manifest['total_selected']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
