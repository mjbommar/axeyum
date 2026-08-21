# `Int.fib_neg_natCast` dependency audit result

Date: 2026-08-21

## Result

The exact 36-root surface splits evenly: 18 empty-footprint supports and 18
`propext`-bearing roots. Transport through negation, natural casts, powers, and
multiplication is already clean. The remaining mathematical center is parity
and `Int.fib_of_odd`; the latter depends directly on one private theorem root.

This rules out direct composition of the official negative-natural theorem but
avoids rebuilding the clean transport layer. The next increment will qualify
the private `Int.fib_of_odd` root without rendering its proof, then choose the
smallest direct recurrence replacement. No theorem or ledger credit was granted.

The immutable measurement pack is
`/nas3/data/axeyum/autogenesis/reference-packs/int-fib-neg-natcast-dependency-audit-v1/`
with manifest SHA-256
`1c722edb023be56a2ec4232c42b76a97647ee74589267993180eb3c5e424e3dc`.
