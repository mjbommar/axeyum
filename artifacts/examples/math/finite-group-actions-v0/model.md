# Model

The acting group is `C2 = {e, s}` with `s*s = e`. The finite set is the four
two-bit strings:

```text
00, 01, 10, 11
```

The action table is:

```text
e.x = x
s.00 = 00
s.11 = 11
s.01 = 10
s.10 = 01
```

The checker treats the group operation and action as finite tables. It
recomputes identity action, compatibility `g.(h.x) = (g*h).x`, orbits,
stabilizers, fixed-point counts, and the Burnside average.

For the malformed identity-action row, the finite replay identifies the failing
point. The separate `qf-uf-bad-identity-action` row links the QF_UF artifact
that checks the resulting `e.x = x` conflict with an Alethe certificate.

For the malformed compatibility row, the finite replay uses the same group and
point set but changes the `s` row so that:

```text
s.01 = 10
s.10 = 10
```

The checker recomputes:

```text
s.(s.01)   = s.10 = 10
(s*s).01   = e.01 = 01
```

so the compatibility law `s.(s.01) = (s*s).01` fails. The linked QF_UF
artifact belongs to the separate `qf-uf-bad-action-compatibility` row; it
isolates that equality conflict and checks it with an Alethe certificate.

General group actions, orbit-stabilizer, Burnside/Cauchy-Frobenius, and
representation-theoretic results over arbitrary groups remain proof-assistant
horizon material.
