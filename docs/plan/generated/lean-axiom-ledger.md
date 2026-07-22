# Lean reconstruction prelude axiom ledger

> **Generated; do not edit by hand.** Source: [`docs/plan/lean-axiom-ledger-v1.json`](../lean-axiom-ledger-v1.json). Regenerate with `python3 scripts/gen-lean-axiom-ledger.py`; use `--check` to rebuild the isolated kernel preludes and reject name/type drift.

This ledger inventories declarations actually admitted as axioms after constructing each reconstruction prelude. It is not a call-site grep, and type well-formedness is not a proof that an assumption is true.

## Snapshot

- **65 total assumptions:** real 30, integer 34, string 1.
- The earlier 64-row call-site census missed `axeyum.string.append`, which is inserted directly as `Declaration::Axiom` rather than through `declare_axiom(...)`.
- 28 names are shared by the isolated real and integer preludes; they cannot coexist safely until TL3.3 namespaces them.
- Classification: unclassified 65.
- Discharge: unreviewed 65.

## Machine-checked contract

- Source command: `cargo run --quiet -p axeyum-lean-kernel --example prelude_axiom_inventory`.
- Type identity: sha256 of Kernel::render_lean(declaration.ty) UTF-8 bytes.
- Any added/removed axiom, renamed declaration, or canonical type change fails validation before the generated ledger can remain current.
- Every row has source, semantic classification, owner, review owner, discharge state, and retained-evidence fields.
- `discharged` requires a real repository evidence path; a `derivable-theorem` may not be marked `retained`.

## Ledger

| Prelude | Name | Type SHA-256 | Classification | Discharge | Owner | Source |
|---|---|---|---|---|---|---|
| `integer` | `Z` | `73d4fe359be51073c75f6c2a03507b52a55364cf0c923d65def2fa12cb438933` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `add` | `a50f6da124c00b9833ae125026f0d19f89feaaad0a8ba5e21124d2134e0e57c3` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `add_assoc` | `8c368d7f7e47251a9874e33cc1375984c727e26d8888f5ff378e789eeb637839` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `add_comm` | `1e84eb5b61c23d94cd7719c19ae4ac96acbdad700955860fdaf3268310cca17b` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `add_le_add` | `2723bf3e55fd02c689ce38d809ea951a4123ba09584f3d64f8d3a5e2004d0193` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `add_lt_add_of_le_of_lt` | `d821843b7b7e61d62b98632466639bceea182bb99ee1b1d9c978ee2e53981469` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `add_neg` | `2d75d06d7bc47721fec49fc6f94eb1969e28fdf2843f953c770c0442955351ba` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `add_zero` | `2a1a511db974782a9b8f473df93eb040721f706a2bd18b18e7524f0df85693a9` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `eq_em` | `1c3912469d09aa9c3b7d403caf5fe93b4cef1245445a1f1644a63b465c1153e8` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `euclidean_decomposition` | `aa7d684471911f39d063778b692f47787fcbb2ec2948ae1b4f3c657484bfe8ed` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `le` | `c975b1f4c08ce82c13f17d985e1d5b7c84e13cdcc138701fbd52ffc86207f93a` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `le_of_lt` | `abd4d9cec7b74beaaab89c0235f0cadcc04a99fd9fccdd12cfbf16152e1eb22b` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `le_refl` | `13bcdfe993e08bf6a0e0aef425954f1ca3c148cfc99fd1ea10238be066ce3796` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `le_total` | `26dd5135968b4dc3f33d2413571abedae8d283d9ee05d9ab3b59ba80605b0087` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `le_trans` | `b9c4a2d4c7bbe6eea1007fd0f0711656a8b4d31b0d8e09947c65e5e6a2174b32` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `left_distrib` | `e394284ba167b48a1ee8979b9d5d0b15e06bdd2e779b35103cda2f108df86d45` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `lt` | `c975b1f4c08ce82c13f17d985e1d5b7c84e13cdcc138701fbd52ffc86207f93a` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `lt_irrefl` | `f2e7456cb76d815d9dc3528a0b0b56a380ea8e13921f9b35c30166d913379f0a` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `lt_of_le_of_lt` | `1519700f0fac42140aed037ed44e290c8047bacfbb47a8b35d4300b2adb404fe` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `lt_of_le_of_ne` | `d69eaf91baa1861dd1920506a1975a3132a214044deb63bd84dfe6382ae6ccd6` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `lt_of_lt_of_le` | `def1dbf606405a68f38269ebd93607004ecf1ea94302fb9cc572f73d08894a2c` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `lt_trans` | `d727a52d24a04f1dd229363eed450e00a729bf688351d7ebba495a994129462c` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `mul` | `a50f6da124c00b9833ae125026f0d19f89feaaad0a8ba5e21124d2134e0e57c3` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `mul_assoc` | `9383b0c56aac8a6e693f10855c5628109976e7629686f229e634fbfbac98f4cd` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `mul_comm` | `7748c93e66da2e8d728a598a868ca4722559246494bb07bc4943118976f4df1e` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `mul_le_mul_of_nonneg_left` | `4dec8c6ca34d6b51296cbf9674ac59bb989500f49cc9a0b3e621c25dd34cd320` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `mul_nonneg` | `aa7898b9ec71db236ecc2db9d2f06924e4081602c627ec4684c145b6800a2332` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `mul_one` | `d2cf971dedfcefe6b355e80681f55a9f3a0e4250a33c7be5a979150ebf7222b9` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `mul_zero` | `58a50f33e9617c1456d95dc672a8211dbd813d1b770299d9bad2c3b03250c74c` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `neg` | `f22e19e706441c80e1ee90c8b36a492c6fac1cc6b6a177b3511136a49a1ac6e1` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `no_int_between` | `eeeb805b0b6588bdea4686289ae15504d595c4d72701e57d85004575add6807a` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `one` | `bbeebd879e1dff6918546dc0c179fdde505f2a21591c9a9c96e36b054ec5af83` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `zero` | `bbeebd879e1dff6918546dc0c179fdde505f2a21591c9a9c96e36b054ec5af83` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `integer` | `zero_lt_one` | `1218b67926fc23777cf1d2db606bf41bd4e0630c89f8691148c9d22bd11aba8a` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/int_prelude.rs) |
| `real` | `R` | `73d4fe359be51073c75f6c2a03507b52a55364cf0c923d65def2fa12cb438933` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `add` | `b905be4af5d877c0146616a6081b478bd8470b42f2a0e943a75031314d0be667` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `add_assoc` | `a5421d641fd315b90525fddff57c700a8b6cd02663572b44cb2856d2f7b9ce76` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `add_comm` | `f8d6c4f0f68cc255ee1300e073c7524341ab0892e44a3750591dc079ad635dc8` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `add_le_add` | `1d827d1424db29dc79e9246aa87f3c18268b204de73ff6047f4cad61f54c1025` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `add_lt_add_of_le_of_lt` | `55ee53833c4ee679cb531aeb8ab3a3a696f0f82c1ca2ab3a3adabfc470859ed7` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `add_neg` | `aa9e28295403c510bec3321b544e027e344dd4363026ceb85370296cc4418fa5` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `add_zero` | `f83bc33da02d6eaebca93bd0668a45aa1653728bbf804e980df6a26dbe51fa7d` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `le` | `99db23573d28e998b0673b420e83dd90c40f6fa9fef0935d8f64ac079a2a7291` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `le_of_lt` | `fb668045881c8840f245cd802e98d7dae889b0e2b893c87aab4eee62c8d5066b` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `le_refl` | `ac9383bcee0d386915762b7c9fd7c126022f3ea6c09cf05dbd6903bba27e01f7` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `le_trans` | `34044535bca8a6e144e25164e2223e098e0ce145d4fca4bd8a9e212e3474def7` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `left_distrib` | `17a87212242d7596441bda00219d6d73edb1a7fe90d374688d99ff48323c238a` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `lt` | `99db23573d28e998b0673b420e83dd90c40f6fa9fef0935d8f64ac079a2a7291` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `lt_irrefl` | `e9458824676ae0b8f0844fb9a01b6b282c598b35271e3c85d3fa33b8794c0c50` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `lt_of_le_of_lt` | `49c9be5d7ae861a17dbc78d978130eaa247133f97a455f75add1de866fa0ada7` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `lt_of_lt_of_le` | `365b75a8bc1b6be8b69d86e59fd4a62f7099b00d118c4300a12aa06d6c7d2c2a` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `lt_trans` | `5b5e1d7c8ad5e7941018ed9dffb2c56e1843e0bf7580b24405c24078622c89b9` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `mul` | `b905be4af5d877c0146616a6081b478bd8470b42f2a0e943a75031314d0be667` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `mul_assoc` | `d4fe37dc3e9b3885945645a801747066d0b3ac558934f4a6c9deb6943a0c1c52` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `mul_comm` | `61e63f0ea2f46ff2db167fad963e046c54d2bb594629083cf2531159e8018a4a` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `mul_le_mul_of_nonneg_left` | `1440c13f1aea94ee0fc7dcec12261f14f005254c818859e5d41ee4ffbaf65b3e` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `mul_nonneg` | `4ca7247d960862eec2f2639aec75e5039fcf14506142eaf549c338d18a1c1bcd` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `mul_one` | `03f43b5b67b54ad32ea74dfec54ebecbc15f8a6d5984b0bc156b05aba4a8ef1c` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `mul_zero` | `71ab4305a985128bab3fdf1d654a26903fdebaad0b7137b5bdd48ea72d11848c` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `neg` | `0b3d437dd8d142c7dd71a8edd5e8ea04292bfe738cd752f8a308ba47535bc472` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `one` | `8c2574892063f995fdf756bce07f46c1a5193e54cd52837ed91e32008ccf41ac` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `sq_nonneg` | `4cba49c6a1ad6337c59a4a40e120caa786d000fb458a4ec8fc54a90468c1db14` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `zero` | `8c2574892063f995fdf756bce07f46c1a5193e54cd52837ed91e32008ccf41ac` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `real` | `zero_lt_one` | `1218b67926fc23777cf1d2db606bf41bd4e0630c89f8691148c9d22bd11aba8a` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/arith_prelude.rs) |
| `string` | `axeyum.string.append` | `3073c0d7c85a8b0bc0b7d36f1d00423e44064523e360a092d81e228247d93506` | `unclassified` | `unreviewed` | `axeyum-lean-kernel` / `TL3.2` | [source](../../../crates/axeyum-lean-kernel/src/string_prelude.rs) |

## Shared real/integer names

These are separate declarations only because the preludes are built in separate kernels today. Their collision is an explicit TL3.3 blocker:

`add`, `add_assoc`, `add_comm`, `add_le_add`, `add_lt_add_of_le_of_lt`, `add_neg`, `add_zero`, `le`, `le_of_lt`, `le_refl`, `le_trans`, `left_distrib`, `lt`, `lt_irrefl`, `lt_of_le_of_lt`, `lt_of_lt_of_le`, `lt_trans`, `mul`, `mul_assoc`, `mul_comm`, `mul_le_mul_of_nonneg_left`, `mul_nonneg`, `mul_one`, `mul_zero`, `neg`, `one`, `zero`, `zero_lt_one`.

## Next classification gate

TL3.2 must move every `unclassified` row to exactly one of `primitive-interface`, `external-assumption`, `derivable-theorem`, or `defect`, assign a discharge target, and preserve the type digest while the assumption remains live. TL3.4 cannot claim an axiom reduction until this ledger observes a checked replacement and the runtime population falls accordingly.
