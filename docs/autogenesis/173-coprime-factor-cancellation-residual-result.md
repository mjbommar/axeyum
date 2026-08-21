# Residual cancellation leaves one unexpected carrier

The residual source compiled, exported, and reconstructed twice identically.
`dvdAddWitnessV1` is empty-footprint and accepted. The multiplicative witness
still reaches `propext`, so the residual cancellation theorem does too.

This is narrower than V2: five of the six measured carriers are absent. The
remaining witness reports only `Eq.trans`, `Nat.mul_assoc`, and `congrArg` as
direct theorem dependencies, all previously classified clean in another
stream. The correct next step is to audit those three identities in this exact
sealed stream before revising the proof.

The manifest is
`/nas3/data/axeyum/autogenesis/reference-packs/4c81f2ce2-coprime-factor-cancellation-residual-v1/manifest.json`
with SHA-256
`700688eed6ae81148bf61d039111b8701a8f5f9d92591d9be2c6920c78548e33`.
