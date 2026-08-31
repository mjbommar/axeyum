# IVT/EVT audit evidence

These files support
[`08-ivt-and-evt-measured-against-mathlib.md`](../../08-ivt-and-evt-measured-against-mathlib.md).
They are retained audit evidence, not general-purpose repository-root tools.

- `probe-kernel-declarations.sh` checks named positive and negative controls in
  the built kernel environment.
- `dump-ivt-evt-facts.py` extracts the relevant fact-ledger rows.
- `kernel-declaration-inventory.tsv` is the raw kernel declaration inventory
  used by the audit.
- `ivt-evt-fact-dump.txt` is the raw output from the fact extraction script.

Run the scripts from the repository root; their paths are root-relative.
