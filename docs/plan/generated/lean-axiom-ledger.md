# Lean reconstruction prelude axiom ledger

> **Generated; do not edit by hand.** Source: [`docs/plan/lean-axiom-ledger-v1.json`](../lean-axiom-ledger-v1.json). Regenerate with `python3 scripts/gen-lean-axiom-ledger.py`; use `--check` to rebuild the isolated kernel preludes and reject name/type drift.

This ledger inventories declarations actually admitted as axioms after constructing each reconstruction prelude. It is not a call-site grep, and type well-formedness is not a proof that an assumption is true.

## Snapshot

- **65 total assumptions:** real 30, integer 34, string 1.
- The earlier 64-row call-site census missed `axeyum.string.append`, which is inserted directly as `Declaration::Axiom` rather than through `declare_axiom(...)`.
- 0 names are shared by the isolated real and integer preludes; ADR-0387's `Int.*` / `Real.*` namespaces make the packages composable.
- Integer trust policy: [ADR-0388](../../research/09-decisions/adr-0388-retain-axiomatized-int-and-use-nat-deficits-for-rado.md) retains all 34 assumptions for reconstruction, requires that count in any dependent publication claim, and keeps credited Rado rigidity on the zero-axiom Nat prefix-deficit route.
- Classification: derivable-theorem 7, external-assumption 41, primitive-interface 17.
- Discharge: planned 7, retained 58.

## Machine-checked contract

- Source command: `cargo run --quiet -p axeyum-lean-kernel --example prelude_axiom_inventory`.
- Type identity: sha256 of Kernel::render_lean(declaration.ty) UTF-8 bytes.
- Any added/removed axiom, renamed declaration, or canonical type change fails validation before the generated ledger can remain current.
- Every row has source, semantic classification, owner, review owner, discharge state, and retained-evidence fields.
- `discharged` requires a real repository evidence path; a `derivable-theorem` may not be marked `retained`.

## Ledger

| Prelude | Name | Type SHA-256 | Classification | Discharge | Owner | Source |
|---|---|---|---|---|---|---|
| `integer` | `Int` | `73d4fe359be51073c75f6c2a03507b52a55364cf0c923d65def2fa12cb438933` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add` | `99eafe1ef787823aede1d24c97170433c8d770f8b3810273b569c3b5ab26da1b` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add_assoc` | `9405ec939ed80e568fe1929fd63482e0907a48e8b6dbb95d2c58f81cf486b26f` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add_comm` | `595e9a1c7bf447f9f1347f3babb46d091fc129d812c39cf7d531b903c942b953` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add_le_add` | `8703098c251851d0a84b8efaf8b31b091dd09ee931606c89f0b9db1427108ec5` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add_lt_add_of_le_of_lt` | `f4736a674bdbe79e58392817d03b945c8fea0bc3c8387fde4f99d9e480065a61` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add_neg` | `5f8dff2caa3f9a0c45d532af52407506e3d9de23385c760328e5094f8e6c62a7` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add_zero` | `8b6f4f975687dab9c145b2abe816dbb4f49e25a21fa466e9e5072f60feb0db80` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.eq_em` | `815531ec43bb75ccb38bb94fb77863a34d9f9235fb3e78c9c07439ecfcc40d3f` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.euclidean_decomposition` | `db11d59452e63e2bf02c37d587c101862fe902da7fbfef7d3c7b1a96ee4ab945` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.le` | `fb0d4590496986200c403ac1cfe3e5ad58a8be4d2fb551726c2262e1e4cc6b31` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.le_of_lt` | `12f9daa9d0684a6f29684456cb56f90d95b89917f32299d0ba70a2cd8177a578` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.le_refl` | `225ccf020467237aeef9c273c920eb77e1cdf2d2cfd33d16b15c2b85ff1bf963` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.le_total` | `7964ea1ddd7637c9f5e72388b9aae51c8066791ca42dbc7febc59d71ad5de1bb` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.le_trans` | `120977f039a28529bcb6438ae595de51bc03f3ce03b1ecfbc681080ebe466388` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.left_distrib` | `54570226ae27575cff7284441daddeb6786e0333c9c3c8338ab3cc40d9cc08a9` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt` | `fb0d4590496986200c403ac1cfe3e5ad58a8be4d2fb551726c2262e1e4cc6b31` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt_irrefl` | `110efe1cc3d1f368c16f520f21ccbf93d9b72825bcf99ea0faf25a6aba5880f7` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt_of_le_of_lt` | `27f076961d39a9a97f0d8889c51a89affb931e3a810fa3622bb90494ca9ff338` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt_of_le_of_ne` | `128cb1d7a0bc5bb9f7d8ccd178ecf38df7f10991ed97b879a96c08acb39d219d` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt_of_lt_of_le` | `99a02402ef4fa99afe3c07bca6d734c05be0f768b58c6ca6aaea4d67e5cb8291` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt_trans` | `52ee835f5c5c74c3f396677055ff707e53c31adf31e6ba27064fe434da809149` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul` | `99eafe1ef787823aede1d24c97170433c8d770f8b3810273b569c3b5ab26da1b` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_assoc` | `2022ec97f7bab2ae54b9c6858b8d949cdd4d17979879868c6c54ca774acc3760` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_comm` | `d4edb8ba8ef7d85b6a8dbbdb1b46303fd287538628221862750b891437507640` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_le_mul_of_nonneg_left` | `09700274d10387750ded321ce969d5d0ace4a816cc73b699d6ae5d80da294a15` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_nonneg` | `b228baf14a1e176e55bb1b2f367e88bb1f009fd7f4caf72f334111391b7c094a` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_one` | `0efaaff79fe83859a46220be902384c97524b96ffd6924f8c10c50739525382e` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_zero` | `15b2aaf49d7e1c3c445f49c50912509a6bdc2a198e53532c30dfd93e7e2b9c01` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.neg` | `3d4ca0eca780c74b60445fd8f9d01162f0a10f34146c015ba989b441ff95c15d` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.no_int_between` | `1fb9cd08ac2f8b8f45027c8192d7cb0a26aea3dd823b5ee2d1c1b8c2e14a6ec4` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.one` | `0b5f608070c6ce3bc711621b8371e71901bdf196dbdf04807b513f75346b7018` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.zero` | `0b5f608070c6ce3bc711621b8371e71901bdf196dbdf04807b513f75346b7018` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.zero_lt_one` | `1dca56836e9ca3fa78c875df42107dfb3e82716a9a9ee5470aa2fe3e33365164` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `real` | `Real` | `73d4fe359be51073c75f6c2a03507b52a55364cf0c923d65def2fa12cb438933` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add` | `f2e8a9c49ce5206d637c9c5ee49f06f6a3af55513878d9f7e8e384eea3aa4f81` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_assoc` | `010706d27846e58f8806ea5c1cf86f36006509e6ba0d1fe53c30bc6a815e0375` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_comm` | `96ac1fae5e7cb3bfce50d0acf0ae06d725ab9db784437abb8dddf22ff2a63fd8` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_le_add` | `f2dba407206ae9aee1e7271b20ac080a5ed3be5cc60e819dd51f8ad39e3ba472` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_lt_add_of_le_of_lt` | `61dab1f23de81a2ee826601b5adca6d84e7b1bc845dd9b377198cfb5e32eaf18` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_neg` | `be1f382dc2e9103cd241fa8c87b5c6621ad1dbf15d5f0c282add161c1b9368ed` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_zero` | `5fdb128700136eaf8890e16fcb700b26ba436ec4b8ec30e3c4a43080f0c6209f` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.le` | `a10c86b54d3bc736182d7f41c8b61bd52ddfdc419d11ec68231f003858b4d4b6` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.le_of_lt` | `d3ecb420bd8b58b96bf42f156b23030ae7a99bb5864c9fda2374ededac593551` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.le_refl` | `f5c864085fd2bb4fb0f638d9b3cb9cb1f64379761d9accc22a9197ece7a867cd` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.le_trans` | `1a5c60023b90c8f031e31e9b1873ae601012899f2ec7337959bbea48309fa407` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.left_distrib` | `49e4bb494347a7cebb968e140694e73bbb2061fc77606cb54f0f441bd2014239` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.lt` | `a10c86b54d3bc736182d7f41c8b61bd52ddfdc419d11ec68231f003858b4d4b6` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.lt_irrefl` | `d5e994116fa2552b8f08bb81cc13787eaa9bb29d01514a14ed0964989b25b22d` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.lt_of_le_of_lt` | `8b1cf1cfc93a487470e1c27fa8e657654e3145091192e124fe86ae9f59740ffd` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.lt_of_lt_of_le` | `124f6579d3deeba5d60cf3d01dad82bd45c09712d5e9af626546ad6e68388c55` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.lt_trans` | `e8157e27eeb1a96770c6a82fe7cd3b4c91b5f2614caa6387c93826fd688de4fe` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul` | `f2e8a9c49ce5206d637c9c5ee49f06f6a3af55513878d9f7e8e384eea3aa4f81` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_assoc` | `c22be271299ef5138292168168a43fdf1bd4d4476dbead0c2919def7d79424a1` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_comm` | `3c0b942ac4b04998399a7ab1dde5ac1375448892dbfa2c064fc24b7faf646c53` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_le_mul_of_nonneg_left` | `3ff0e3315918a93418533bc852007c850f0099a2a3e239b84403975fd0b402a8` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_nonneg` | `ba9072322e8a0653a24193b48c7909982d9ea1d9cacea908434df90281b34a91` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_one` | `d8d0e9e72d701ef85b76be29d3cc5f97ee21e4846e8165b726c1cbe6a8ccb902` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_zero` | `7bebbf5bf8b0eb78d1b6d46281315452269b93e5b4f9f6afcb6a81997dd9827b` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.neg` | `9320571f977aee60b4ad45a17f33141ed397307d63889b68f6e8a90101e36656` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.one` | `e55fe37737b783cc821bb77a370950bb6a51dcf386ab6ee70d31808409ba412e` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.sq_nonneg` | `605acf4574faed32958aa25327f592fe46270080b7764c0a4d02e411ed9f2d64` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.zero` | `e55fe37737b783cc821bb77a370950bb6a51dcf386ab6ee70d31808409ba412e` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.zero_lt_one` | `b8b5fca98eaedc898bf7553c4225a08e801c5b862dbad897ab79e74897a23b5c` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `string` | `axeyum.string.2.append` | `5807e40ae2f7047b9c13ec27ba628bd001a37d77633c65598aec24aa94561f25` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/string_prelude.rs) |

## Shared real/integer names

ADR-0387 requires this set to remain empty so integer and real packages can coexist without declaration aliasing:

None.

## Next classification gate

TL3.2 must move every `unclassified` row to exactly one of `primitive-interface`, `external-assumption`, `derivable-theorem`, or `defect`, assign a discharge target, and preserve the type digest while the assumption remains live. TL3.4 cannot claim an axiom reduction until this ledger observes a checked replacement and the runtime population falls accordingly.
