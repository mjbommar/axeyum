# Lean reconstruction prelude axiom ledger

> **Generated; do not edit by hand.** Source: [`docs/plan/lean-axiom-ledger-v1.json`](../lean-axiom-ledger-v1.json). Regenerate with `python3 scripts/gen-lean-axiom-ledger.py`; use `--check` to rebuild the isolated kernel preludes and reject name/type drift.

This ledger inventories declarations actually admitted as axioms after constructing each reconstruction prelude. It is not a call-site grep, and type well-formedness is not a proof that an assumption is true.

## Snapshot

- **65 total assumptions:** real 30, integer 34, string 1.
- The earlier 64-row call-site census missed `axeyum.string.append`, which is inserted directly as `Declaration::Axiom` rather than through `declare_axiom(...)`.
- 0 names are shared by the isolated real and integer preludes; ADR-0387's `Int.*` / `Real.*` namespaces make the packages composable.
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
| `integer` | `Int.add_assoc` | `b3490544f65fe393d8a1606aeb8c290653d25b9db81da992a32c1c46b375e03d` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add_comm` | `ca66824476d768952ff943ec91cd1855bde5b79077ca17e3b637a93abac07c8c` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add_le_add` | `e682a147038310d2a4cf0fa128f9d3d85ecbf60d1b6c7a18bb7e3b921e88a180` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add_lt_add_of_le_of_lt` | `21932556551cb99a4f26eeec5ccadbae1f5b4500b83da40fd8f0bc00d855fcef` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add_neg` | `a833468aa772568d260c60a8c04f25fe391778ab608d12e1554f6827c1a3e091` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.add_zero` | `e1086481c043571fafae5a3f1cd3148a92787ba04a7003589ae3d294cc89148b` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.eq_em` | `48af5e1253501708b551575e8863cc31cfc84f55e79a36271f511e60a2ce0fb0` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.euclidean_decomposition` | `a9f583a380b8b2272c9964fc7184ed71153918cf76222a2dd3fa5b1a768b913a` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.le` | `fb0d4590496986200c403ac1cfe3e5ad58a8be4d2fb551726c2262e1e4cc6b31` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.le_of_lt` | `4019deacd910d899601a8c2fc3a79b3f93c2d78e7ac5be5c5099c48681ec67b4` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.le_refl` | `9a02a0a8dc71a548d4ef1131bb9f82e7494f56761ad5b560c99b18ae3aff4dae` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.le_total` | `7a3b7f02d2b20391f7d929711043786fbb0d64f002e29ee8162fb32d005a1d5c` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.le_trans` | `179eea807216b81de284d61d54072a13a37ad8c752489cb223f8e29f9cd7d548` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.left_distrib` | `cc7fbca01df707927a691bf62c7939515c38db58f4d185d1784fb419c1ff1f08` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt` | `fb0d4590496986200c403ac1cfe3e5ad58a8be4d2fb551726c2262e1e4cc6b31` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt_irrefl` | `b8962ef5d1ca82b228cf041d4686aa57223d9894f264274be2d40132987163f1` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt_of_le_of_lt` | `a9ef9287c468d81197d3235ce3acdff2e27ab86c9130f62da045dde159787843` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt_of_le_of_ne` | `6187bce3b97fc810532df6ae829957c87338f96435efecbdb739caad105888d6` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt_of_lt_of_le` | `0275ec8e59c261f55230482e713f1740dd3ba57571483106e808812f7f8ca8dc` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.lt_trans` | `791c51c4d397bc1404cd4548eb2ababfb1211259223e81690157a062fe64e188` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul` | `99eafe1ef787823aede1d24c97170433c8d770f8b3810273b569c3b5ab26da1b` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_assoc` | `9fd05d06480a08a787471954ea27fc53cb0458991452eec35024bcfae12c571c` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_comm` | `edc6d465b1d00c2a71150867acca53c394193d174a32d2f143c29a10e5121483` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_le_mul_of_nonneg_left` | `7ae153ab0e805e5070c4097cada2e6e283e3a523646d9592c24c1a5f8a136fe9` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_nonneg` | `df0afa471a97dd892eb33086e663f8bc2e4b0b8a8fb29d3675c61a41934d7a78` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_one` | `a810365d6e329a0b3f0cfa8fdb624079a84c6b017d908c61c2c8ed97f5a787b2` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.mul_zero` | `588995deeaf6ce64c21bf3b44de37b11ae1904b404f9988b653389e8be6fd628` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.neg` | `3d4ca0eca780c74b60445fd8f9d01162f0a10f34146c015ba989b441ff95c15d` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.no_int_between` | `7f57c506a1c4b13bf3d9df6348ec2964ff59324f2f89ff0e8aece76cfccf0929` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.one` | `0b5f608070c6ce3bc711621b8371e71901bdf196dbdf04807b513f75346b7018` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.zero` | `0b5f608070c6ce3bc711621b8371e71901bdf196dbdf04807b513f75346b7018` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `Int.zero_lt_one` | `4408487d4ee7ce3076e892de988abc4ce8607f6d50542fbfff9d2c5576ec7b9b` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `real` | `Real` | `73d4fe359be51073c75f6c2a03507b52a55364cf0c923d65def2fa12cb438933` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add` | `f2e8a9c49ce5206d637c9c5ee49f06f6a3af55513878d9f7e8e384eea3aa4f81` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_assoc` | `41a7752ca7998e0204320b9c7e0128eb96469453d5d12fd008f658bad05bf5dc` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_comm` | `21b7aa04c4d1b817044dd5d58ac6db6cff4aa6eafe10a6887f60e45d64d02520` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_le_add` | `a7de6e3901222430486d414f5d77bd86d0e74b037ec8c9ddb46b07303ac7bd38` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_lt_add_of_le_of_lt` | `8d4a911c8f406a36f05d915ba073e0350e3907ee70282a162fb7697eb79ed6f3` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_neg` | `c444b45713cbd86f6bb6407c916fe3d1727a6e55cc7128a5ce6f9377f36555a2` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.add_zero` | `035ae4fbf63e9ad089e9e7efccc9aa72ed1ad0297e2d90a34a510272f985543b` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.le` | `a10c86b54d3bc736182d7f41c8b61bd52ddfdc419d11ec68231f003858b4d4b6` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.le_of_lt` | `5620ce5dc1576633102753237836bbafbf50a9509e418efaa388161e274ce26d` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.le_refl` | `dad915fc6720f4975c18e31e48b80800696f63cb80e09acf8dd74036265dd28e` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.le_trans` | `bf7b27744fc4377f5af252e6b8764a3a3e48e1b4b213e646528a964b5d672a22` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.left_distrib` | `c601cd87134fe1852045b60b03551c8683ccf29cb1cae01b1f2f16f206684420` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.lt` | `a10c86b54d3bc736182d7f41c8b61bd52ddfdc419d11ec68231f003858b4d4b6` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.lt_irrefl` | `4a1cb3e6b7bcd8ea9e20cd082c4ede91eeeb77f0bcb4b54cd6d8503194b858ba` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.lt_of_le_of_lt` | `e98599a3458c49014f7de151b062f3edd40b2f9751a79073dd525ec3c1349de8` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.lt_of_lt_of_le` | `3f690a2b5df3639ef4075d6bf2835e3166fd32e4b76f0e2964d1798351ed0679` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.lt_trans` | `bb01600476a791d73418df37586c4eb83574a76d2d809f766d97f2dac7160fad` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul` | `f2e8a9c49ce5206d637c9c5ee49f06f6a3af55513878d9f7e8e384eea3aa4f81` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_assoc` | `03413da766a4c02cb66ae0cefce8b2b1f7d2d06c1f7f323d1ecaea4e395f594f` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_comm` | `8bf3e887a84779288e7c149ff40a55b4489c84e275d7b8f28df5a46c82a595fa` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_le_mul_of_nonneg_left` | `f7bf52359dbcd46af5a5fefeecd8f61e694bc759ff0fd5ef09016250961fcef8` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_nonneg` | `3809933d2a109e08381a3bee00914a2fa47808679f0b6d42652ef854a6bdd1c6` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_one` | `142e5b03e44c6acebe27a9e32f774e63976bfe9362ee590c7613a7c7cef0644c` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.mul_zero` | `ca429aa687d55926af3925bbce13977d4a4190aa5b42d56ddf1a980d9e5a3c44` | `derivable-theorem` | `planned` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.neg` | `9320571f977aee60b4ad45a17f33141ed397307d63889b68f6e8a90101e36656` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.one` | `e55fe37737b783cc821bb77a370950bb6a51dcf386ab6ee70d31808409ba412e` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.sq_nonneg` | `0127d470edf8737447cd44d74592d7450d582526cf89f083014e7c2e50e69a06` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.zero` | `e55fe37737b783cc821bb77a370950bb6a51dcf386ab6ee70d31808409ba412e` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `Real.zero_lt_one` | `d6aa3944b193704b0786691ce7b78c068a598ecb58cc0eb137da13a977a42f5b` | `external-assumption` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `string` | `axeyum.string.2.append` | `5807e40ae2f7047b9c13ec27ba628bd001a37d77633c65598aec24aa94561f25` | `primitive-interface` | `retained` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/string_prelude.rs) |

## Shared real/integer names

ADR-0387 requires this set to remain empty so integer and real packages can coexist without declaration aliasing:

None.

## Next classification gate

TL3.2 must move every `unclassified` row to exactly one of `primitive-interface`, `external-assumption`, `derivable-theorem`, or `defect`, assign a discharge target, and preserve the type digest while the assumption remains live. TL3.4 cannot claim an axiom reduction until this ledger observes a checked replacement and the runtime population falls accordingly.
