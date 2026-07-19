# Glaurung fixed-authority shadow calibration — 2026-07-19

ADR-0274 completed all 30 registered processes with 30/30 validator-clean v4
traces. Raw artifacts are retained at
`/nas4/data/workspace-infosec/.axeyum-fixed-authority-shadow-calibration-20260719.gvbTxZ`.

Every tier reproduces the same 4,846 ordered check identities, Z3 outcomes,
findings, and outer-work partition. The invariant identity/outcome hashes are
`89d28a2978e4d9fc1bbba78bb1413a80fffc408c0bbc4dcef51b1eb6b5e1e928`
and `f0b5580fcc6bba0accd6a91fc76a1373a60835af84c5982394ca9d6b3312fafa`.

The mechanical triplet is Z3 rlimit 100,000, Axeyum progress checks 32,768
(tier 2), and Bitwuzla termination polls 512 (tier 9). Each selected cold/warm
pair decides 4,846/4,846; all verdicts agree. Lower-tier nondecisions are typed
resource-limit, with zero wall/other/operational/fallback/deadline failures.

Campaign SHA-256 is
`0526f925aba7816e61df3598553f7bb0ed323a8b492f5d3e700add6ec193ceb7`;
analysis SHA-256 is
`7b20e363ee5558de02e5534e047c2645ffe8a65541be239754fc9fd03ad18cf6`.
No 338-function census was run. A separate zero-row ADR must freeze and jointly
reproduce the triplet before the census.
