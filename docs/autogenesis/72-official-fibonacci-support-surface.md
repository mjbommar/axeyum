# Official Fibonacci coprimality support surface

Date: 2026-08-20

## Result

All seven native theorem roots preregistered for the Fibonacci-neighbor
coprimality induction now compose together into the official r082 target:

1. `Nat.add_comm`
2. `Nat.dvd_add_iff_right`
3. `Nat.dvd_gcd`
4. `Nat.eq_one_of_dvd_one`
5. `Nat.gcd_dvd_left`
6. `Nat.gcd_dvd_right`
7. `Nat.gcd_zero_left`

The 92-declaration source closure uses exactly three explicit target-owned
leaves: `Nat.dvd_mod_iff`, `Nat.mod_lt`, and the new axiom-free
`Nat.gcd_succ`. It adds 14 theorems and four definitions, all with empty
kernel-derived footprints. Receipt
`c4cedfbc21119852cd885829601434015971582165103f2580f29ea4e677ec67`
replays exactly.

This closes the entire support layer selected before the native proof was
constructed. The next kernel submission can target the actual official
Fibonacci proposition rather than another prerequisite.

## Reproducibility

Two fresh executions produced byte-identical JSON with SHA-256
`a015fcfa54805ce5e989447cab240e33b36cbb98103f073e61f476a6fe763ff0`.
The default one-root mode remains byte-compatible with the earlier
`Nat.dvd_gcd` evidence; `--all-support` selects the complete preregistered root
set.

```sh
cargo run -q -p axeyum-lean-import \
  --example nat_gcd_succ_specialization -- \
  /path/to/nat-mod-invariant.ndjson \
  /path/to/r082.ndjson \
  /path/to/nat-gcd-bridge.ndjson \
  --all-support
```

## Immutable evidence

The sealed pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/9e83ab67a-lean430-fibonacci-support-surface-v1/manifest.json`

Its manifest SHA-256 is
`ed9f461b8f36018b91fa865e7b552bd06e3fcc438f08655ec2c3cbc2a793b16c`.
The directory is mode `0555`; all three files are mode `0444`.

## Boundary

The exact r082 proposition has not yet been admitted. Consequently there is no
semantic theorem receipt, evaluation credit, fact transition, or ledger write.
The completed support environment is authority to attempt the final target,
not evidence that it is already proved there.

## Next

Reconstruct the native induction term against the exact official
`Nat.Coprime (Nat.fib n) (Nat.fib (n + 1))` goal in this completed target.
After two identical fresh-kernel admissions, issue and replay the semantic
receipt, then attempt the crash-safe fact-ledger transition.
