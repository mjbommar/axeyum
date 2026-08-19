# Lean reconstruction prelude axiom ledger

> **Generated; do not edit by hand.** Source: [`docs/plan/lean-axiom-ledger-v1.json`](../lean-axiom-ledger-v1.json). Regenerate with `python3 scripts/gen-lean-axiom-ledger.py`; use `--check` to rebuild the isolated kernel preludes and reject name/type/count drift.

This ledger inventories declarations actually admitted as trusted after constructing each reconstruction prelude. It is not a call-site grep, and type well-formedness is not a proof that an assumption is true.

**No number below is authored.** Every count is derived from the two measurements named under [Machine-checked contract](#machine-checked-contract) and re-derived by `--check`. The previous revision hard-coded them, and when the Int development was proved down this ledger kept publishing a trusted base 33 rows larger than the one the kernel actually admits.

## Snapshot

- **30 total assumptions:** real 30.
- Axiom-free preludes, enumerated rather than inferred from absence: `complex`, `creal`, `integer`, `logic`, `nat`, `rat`, `string`. An axiom-free prelude emits no rows, so the measurement declares its own coverage; a prelude that silently stopped being built fails the gate instead of shrinking the total.
- 0 names are shared by the isolated real and integer preludes; ADR-0387's `Int.*` / `AxReal.*` namespaces make the packages composable.
- Integer trust policy: [ADR-0465](../../research/09-decisions/adr-0465-the-axiom-ledger-is-derived-not-transcribed.md) — The integer prelude admits no assumption; a checked dependency closure using it inherits nothing from this ledger.
- **35 assumptions have been retired** from the trusted surface since this ledger was first frozen; they are kept below rather than deleted, because a reduction in the trusted base is the result, not a smaller table.
- Classification: derivable-theorem 3, external-assumption 19, primitive-interface 8.
- Discharge: planned 3, retained 27.

## Trusted surface by prelude

Counts are over the whole trusted surface, not `Declaration::Axiom` alone: `Opaque` has no proof body and `Quotient` admits `Quot.sound`.

| Prelude | Axiom | Opaque | Quotient | Trusted total | Ledger rows |
|---|---|---|---|---|---|
| `complex` | 0 | 0 | 0 | 0 | 0 |
| `creal` | 0 | 0 | 0 | 0 | 0 |
| `integer` | 0 | 0 | 0 | 0 | 0 |
| `logic` | 0 | 0 | 0 | 0 | 0 |
| `nat` | 0 | 0 | 0 | 0 | 0 |
| `rat` | 0 | 0 | 0 | 0 | 0 |
| `real` | 30 | 0 | 0 | 30 | 30 |
| `string` | 0 | 0 | 0 | 0 | 0 |

## Machine-checked contract

- Row source: `cargo run --quiet -p axeyum-lean-kernel --example prelude_axiom_inventory`.
- Coverage source: `cargo run --quiet --release -p axeyum-lean-kernel --example nat_axiom_inventory -- --include-constructed` — enumerates 8 preludes and declares a per-prelude count line for each, including the axiom-free ones.
- The two are cross-checked against each other: per-prelude axiom counts, name sets, and canonical types must all agree, so a filter bug in either shows up as a disagreement rather than as a smaller number.
- Type identity: sha256 of Kernel::render_lean(declaration.ty) UTF-8 bytes.
- Any added/removed axiom, renamed declaration, or canonical type change fails validation before the generated ledger can remain current. A population change additionally requires an explicit `--accept-population-change` run.
- **Every prelude above is pinned by value, and a moved number is reported with its direction.** A *rise* is a regression — something previously proved is now assumed. A *fall* is a result this ledger has not published yet, and it is the direction a blanket axiom-free assertion structurally cannot see, because that assertion only ever becomes more true. Both fail the gate; what differs is what the operator is told to do next.
- Every row has source, semantic classification, owner, review owner, discharge state, and retained-evidence fields.
- `discharged` requires a real repository evidence path; a `derivable-theorem` may not be marked `retained`.
- Documents that cite these counts are listed in the manifest's `live_documents` and scanned: a stale count fails the gate, and so does a document that stops citing the ledger at all.

## Ledger

| Prelude | Name | Type SHA-256 | Classification | Discharge | Owner | Source |
|---|---|---|---|---|---|---|
| `real` | `AxReal` | `73d4fe359be51073c75f6c2a03507b52a55364cf0c923d65def2fa12cb438933` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.add` | `9a1095ebb7e7f3c8be0739e50fdeb8e477e65eef4654053d850e60af4945506e` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.add_assoc` | `89c85f1b696b466df15b38ca075b5a655e12aef7a1a225def814f7b4078c940a` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.add_comm` | `b57422809db16ffcc4d601a421b11fe41a90e683fae2da8a95cff9695eb11dee` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.add_le_add` | `1ecd890660212db88dd7f1a1340209521a84afba8a39bc41207908170b54ed3b` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.add_lt_add_of_le_of_lt` | `81db25978ae163c5610ea820e54f8a29c077120a66e772957c19702af4778a49` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.add_neg` | `d6410774eb71dd100d1840dda4c6cf2e1ef23fe8659634a0ee57dbeb1d0f7dff` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.add_zero` | `b696625c14e848148eac73b7015b4eebf2a1f441e9300611e8486804655088c7` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.le` | `753c8c2001b13a61dc9ecba0b4daadd145d5178cb9769b15f161e4e92386a031` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.le_of_lt` | `902a4ace4a1bcc22926db02f8fc44a630495ef6ead57ec119f3667e8412a3d94` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.le_refl` | `21ecd845e5615f2c29f0ae811192f97ae4e3dea6a2e7fc85f09d127bdc3662ab` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.le_trans` | `03c11c1fcb9de331066ec3719ec2fb8e3f364434c7eb9554bc836b1da6b78ca8` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.left_distrib` | `b50968b27155f838eb986b3471f04dcc721a66bfaf020e0c679f679f8f58033e` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.lt` | `753c8c2001b13a61dc9ecba0b4daadd145d5178cb9769b15f161e4e92386a031` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.lt_irrefl` | `3f3146b15e86a7a3a488a6f239883501102785bbe518495a0c8f0017a2560325` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.lt_of_le_of_lt` | `a0c71c2fa471224978fcfc7372df6df4cc3ac3874120c77d6a675a282e0eddb9` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.lt_of_lt_of_le` | `0ce9705a9a600ff66a412d1fca5ed8ace97ad0c3f89e7394aa544e18762ba8e8` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.lt_trans` | `9709b10a6ac19cfb0e7b6e8c2b9ee0026504b8ed990fa00474296cb13e8c6142` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.mul` | `9a1095ebb7e7f3c8be0739e50fdeb8e477e65eef4654053d850e60af4945506e` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.mul_assoc` | `7ba323e70286173ebede9d8e223a30193688eb946f9ae061f9e4eb89d4a89981` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.mul_comm` | `d15d2dd4b854b32a5f47a3c49c7e528780b1c158a9658608e50c8ef910d2828e` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.mul_le_mul_of_nonneg_left` | `1efb13a1e2c0fed9f871e5f95ff768a3eb6739d36a155cf44ced2f1ae4cc5ae3` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.mul_nonneg` | `0e3ef33f4684b720e9d95fef8286288f5d7d12af939b06f0b5cc346319fca937` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.mul_one` | `905dc270f401d094bca9dab6de51827758fd994576d177ab1d9318fccbc87b55` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.mul_zero` | `91d06a7ebaa2bd7ae862690aa81ae68f08cb742ca76cfdcd6a03586c99aefe44` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.neg` | `5fea5c580ac9ac835e3d60d9ae3b8bccfba7913ce4e5f79f7361129f2d285982` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.one` | `c5072556a63d1dca64c66cc5e93df90b6549bfd5f6eea0a1b1acfaa66fd38df9` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.sq_nonneg` | `5ceb1722fb0c114b8dc277ee24f1bac88a03fc10977ed3731b036b6476e3763d` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.zero` | `c5072556a63d1dca64c66cc5e93df90b6549bfd5f6eea0a1b1acfaa66fd38df9` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `AxReal.zero_lt_one` | `69d2008346a542c24e2442df5976cddee657de7b42f8c01c1b1ad3005ff8799b` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |

## Retired assumptions

Rows the kernel no longer admits. They are retained because the interesting fact about a trust ledger is which way it moved.

Retired by date: 2026-08-15 (33), 2026-08-16 (1), 2026-08-17 (1).

| Prelude | Name | Retired | Type SHA-256 | Note |
|---|---|---|---|---|
| `integer` | `Int` | 2026-08-15 | `73d4fe359be51073c75f6c2a03507b52a55364cf0c923d65def2fa12cb438933` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.add` | 2026-08-15 | `99eafe1ef787823aede1d24c97170433c8d770f8b3810273b569c3b5ab26da1b` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.add_assoc` | 2026-08-15 | `9405ec939ed80e568fe1929fd63482e0907a48e8b6dbb95d2c58f81cf486b26f` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.add_comm` | 2026-08-15 | `595e9a1c7bf447f9f1347f3babb46d091fc129d812c39cf7d531b903c942b953` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.add_le_add` | 2026-08-15 | `8703098c251851d0a84b8efaf8b31b091dd09ee931606c89f0b9db1427108ec5` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.add_lt_add_of_le_of_lt` | 2026-08-15 | `f4736a674bdbe79e58392817d03b945c8fea0bc3c8387fde4f99d9e480065a61` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.add_neg` | 2026-08-15 | `5f8dff2caa3f9a0c45d532af52407506e3d9de23385c760328e5094f8e6c62a7` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.add_zero` | 2026-08-15 | `8b6f4f975687dab9c145b2abe816dbb4f49e25a21fa466e9e5072f60feb0db80` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.eq_em` | 2026-08-15 | `815531ec43bb75ccb38bb94fb77863a34d9f9235fb3e78c9c07439ecfcc40d3f` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.euclidean_decomposition` | 2026-08-16 | `db11d59452e63e2bf02c37d587c101862fe902da7fbfef7d3c7b1a96ee4ab945` | Discharged: Int.euclidean_decomposition became a theorem over the proved Nat development, leaving the integer prelude with no assumption at all. Its witnesses are uniform per sign case — q = negSucc a and r = ofNat (K - succ b) on the negative branch — so no case needed a new axiom. |
| `integer` | `Int.le` | 2026-08-15 | `fb0d4590496986200c403ac1cfe3e5ad58a8be4d2fb551726c2262e1e4cc6b31` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.le_of_lt` | 2026-08-15 | `12f9daa9d0684a6f29684456cb56f90d95b89917f32299d0ba70a2cd8177a578` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.le_refl` | 2026-08-15 | `225ccf020467237aeef9c273c920eb77e1cdf2d2cfd33d16b15c2b85ff1bf963` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.le_total` | 2026-08-15 | `7964ea1ddd7637c9f5e72388b9aae51c8066791ca42dbc7febc59d71ad5de1bb` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.le_trans` | 2026-08-15 | `120977f039a28529bcb6438ae595de51bc03f3ce03b1ecfbc681080ebe466388` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.left_distrib` | 2026-08-15 | `54570226ae27575cff7284441daddeb6786e0333c9c3c8338ab3cc40d9cc08a9` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.lt` | 2026-08-15 | `fb0d4590496986200c403ac1cfe3e5ad58a8be4d2fb551726c2262e1e4cc6b31` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.lt_irrefl` | 2026-08-15 | `110efe1cc3d1f368c16f520f21ccbf93d9b72825bcf99ea0faf25a6aba5880f7` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.lt_of_le_of_lt` | 2026-08-15 | `27f076961d39a9a97f0d8889c51a89affb931e3a810fa3622bb90494ca9ff338` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.lt_of_le_of_ne` | 2026-08-15 | `128cb1d7a0bc5bb9f7d8ccd178ecf38df7f10991ed97b879a96c08acb39d219d` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.lt_of_lt_of_le` | 2026-08-15 | `99a02402ef4fa99afe3c07bca6d734c05be0f768b58c6ca6aaea4d67e5cb8291` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.lt_trans` | 2026-08-15 | `52ee835f5c5c74c3f396677055ff707e53c31adf31e6ba27064fe434da809149` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.mul` | 2026-08-15 | `99eafe1ef787823aede1d24c97170433c8d770f8b3810273b569c3b5ab26da1b` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.mul_assoc` | 2026-08-15 | `2022ec97f7bab2ae54b9c6858b8d949cdd4d17979879868c6c54ca774acc3760` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.mul_comm` | 2026-08-15 | `d4edb8ba8ef7d85b6a8dbbdb1b46303fd287538628221862750b891437507640` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.mul_le_mul_of_nonneg_left` | 2026-08-15 | `09700274d10387750ded321ce969d5d0ace4a816cc73b699d6ae5d80da294a15` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.mul_nonneg` | 2026-08-15 | `b228baf14a1e176e55bb1b2f367e88bb1f009fd7f4caf72f334111391b7c094a` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.mul_one` | 2026-08-15 | `0efaaff79fe83859a46220be902384c97524b96ffd6924f8c10c50739525382e` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.mul_zero` | 2026-08-15 | `15b2aaf49d7e1c3c445f49c50912509a6bdc2a198e53532c30dfd93e7e2b9c01` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.neg` | 2026-08-15 | `3d4ca0eca780c74b60445fd8f9d01162f0a10f34146c015ba989b441ff95c15d` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.no_int_between` | 2026-08-15 | `1fb9cd08ac2f8b8f45027c8192d7cb0a26aea3dd823b5ee2d1c1b8c2e14a6ec4` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.one` | 2026-08-15 | `0b5f608070c6ce3bc711621b8371e71901bdf196dbdf04807b513f75346b7018` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.zero` | 2026-08-15 | `0b5f608070c6ce3bc711621b8371e71901bdf196dbdf04807b513f75346b7018` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `integer` | `Int.zero_lt_one` | 2026-08-15 | `1dca56836e9ca3fa78c875df42107dfb3e82716a9a9ee5470aa2fe3e33365164` | Left the trusted surface when the integer development was proved out: the carrier became an inductive over the proved Nat development, the operations became checked definitions, and the laws became theorems with empty axiom footprints. |
| `string` | `axeyum.string.2.append` | 2026-08-17 | `5807e40ae2f7047b9c13ec27ba628bd001a37d77633c65598aec24aa94561f25` | Retired: `append` is no longer assumed. `axeyum.string.<n>.append` is now a checked `Declaration::Definition` by structural recursion over `Str.rec`, and its four free-monoid laws (`nil_append`, `cons_append`, `append_nil`, `append_assoc`) are `Declaration::Theorem`s whose proof terms the kernel re-checks on admission. The string prelude trusted surface is empty. Its `primitive-interface`/`retained` classification is overturned by ADR-0513: the carrier `Str` is a constructed inductive, so the row was a `derivable-theorem`. Checked outside this kernel too -- a real `lean` binary accepts the exported module and its `#print axioms` names no `axeyum.string.*` row. |

## Shared real/integer names

ADR-0387 requires this set to remain empty so integer and real packages can coexist without declaration aliasing:

None.

Read this weakly: it compares **ledger rows**, and the integer prelude now contributes 0 of them, so an empty intersection here is close to arithmetically forced. The aliasing hazard ADR-0387 names is over whole environments, and that is checked in the kernel, not here.

## Next classification gate

Every live row must hold exactly one of `primitive-interface`, `external-assumption`, `derivable-theorem`, or `defect`, with a discharge target, and must preserve its type digest while the assumption remains live. An axiom-reduction claim is credited only when this ledger observes the runtime population fall — which is now the same event that updates this file.
