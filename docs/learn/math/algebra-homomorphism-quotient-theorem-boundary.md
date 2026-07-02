# Algebra Homomorphism And Quotient Theorem Boundary

This page separates Axeyum's finite homomorphism, kernel/image, ideal, and
quotient-ring resources from general isomorphism theorems, ideal
correspondence, quotient theory, localization, Noetherian theory, and
categorical universal properties.

Primary packs:

- [finite-algebra-homomorphisms-v0](../../../artifacts/examples/math/finite-algebra-homomorphisms-v0/)
- [finite-ideals-v0](../../../artifacts/examples/math/finite-ideals-v0/)

Companion lessons and maps:

- [End To End: Finite Algebra Homomorphisms](finite-algebra-homomorphisms-end-to-end.md)
- [End To End: Finite Ideals And Quotient Rings](finite-ideals-quotient-rings-end-to-end.md)
- [Algebra And Number Theory](algebra-and-number-theory.md)
- [Algebra Equality Certificate Boundary](algebra-equality-certificate-boundary.md)
- [Theorem Horizon Queries](../../foundational-resources/THEOREM-HORIZON-QUERIES.md)

## Current Finite Resources

`finite-algebra-homomorphisms-v0` checks one concrete parity map from `Z/4Z`
to `Z/2Z`. The validator replays group homomorphism preservation, ring
homomorphism preservation, kernel/image computation, the quotient by the kernel,
and the induced map onto the image. The QF_UF/Alethe rows isolate small
homomorphism-preservation equality conflicts; they do not prove a general
isomorphism theorem.

`finite-ideals-v0` checks the even residues in `Z/6Z`. The validator replays
ideal closure, principal generation by `2`, the kernel/image of the modulo-`2`
ring homomorphism, and the quotient-ring addition/multiplication tables. The
QF_UF/Alethe rows isolate bad additive closure and quotient representative
independence; they do not prove general ideal theory.

The checked resources cover:

```text
Z/4Z -> Z/2Z parity map:       finite group/ring preservation -> replay-only finite table
kernel and image:              ker(f)={0,2}, image={0,1}     -> replay-only finite table
quotient by kernel:            two cosets and induced map     -> replay-only finite table
bad homomorphism:              g(1+1) != g(1)+g(1)           -> checked finite replay + Alethe
Z/6Z even ideal:               {0,2,4} closure replay         -> replay-only finite table
principal ideal:               (2)={0,2,4}                   -> replay-only finite table
quotient ring:                 E/O addition and product      -> replay-only finite table
bad ideal / representative:    one closure or congruence row  -> checked QF_UF/Alethe
general theorem layer:         arbitrary groups/rings/ideals  -> Lean/theorem work
```

Those rows prove bounded facts about displayed finite tables. They do not
prove first isomorphism, correspondence, universal, localization, Noetherian,
or algebraic-geometry theorems.

## Claim And Evidence Rows

| Check | Expected | Evidence Status | What It Means |
|---|---|---|---|
| `z4-to-z2-group-homomorphism` | `sat` | replay-only finite table | The displayed parity map preserves finite group addition. |
| `kernel-image-replay` | `sat` | replay-only finite table | The kernel and image are recomputed from the finite map table. |
| `quotient-first-isomorphism-replay` | `sat` | replay-only finite table | The quotient by this kernel is isomorphic to this image via the displayed induced map. |
| `z4-to-z2-ring-homomorphism` | `sat` | replay-only finite table | The parity map preserves zero, one, addition, and multiplication on the displayed rings. |
| `qf-uf-homomorphism-preservation-alethe` | `unsat` | checked QF_UF/Alethe | Congruent source elements preserve the abstract homomorphism equation. |
| `bad-group-homomorphism-rejected` | `unsat` | checked finite replay | The displayed malformed map fails on the concrete pair `1,1`. |
| `qf-uf-bad-group-homomorphism-alethe` | `unsat` | checked QF_UF/Alethe | The malformed map's fixed equality conflict is independently checked. |
| `z6-even-ideal` | `sat` | replay-only finite table | The even residues form a two-sided ideal in this finite ring. |
| `principal-ideal-span-replay` | `sat` | replay-only finite table | Multiples of `2` generate the listed ideal. |
| `mod-two-ring-hom-kernel-image` | `sat` | replay-only finite table | The modulo-`2` map has the listed kernel and image. |
| `quotient-ring-replay` | `sat` | replay-only finite table | The listed two-coset quotient ring table matches representative replay. |
| `qf-uf-quotient-ring-representative-alethe` | `unsat` | checked QF_UF/Alethe | Quotient addition is independent of choosing congruent representatives in the scoped row. |
| `bad-ideal-rejected` | `unsat` | replay-only finite table | The malformed subset `{0,2}` fails additive closure in `Z/6Z`. |
| `qf-uf-bad-ideal-additive-closure` | `unsat` | checked QF_UF/Alethe | The fixed malformed closure-membership equality is impossible. |
| `general-isomorphism-theorems-lean-horizon` | `not-run` | Lean horizon | General isomorphism theorem and structure-theory claims remain future proof work. |
| `general-ideal-theory-lean-horizon` | `not-run` | Lean horizon | General ideal and quotient-ring theory remains future proof work. |

The boundary is:

```text
untrusted fast search -> candidate map, kernel, image, ideal, cosets, quotient table
trusted small checking -> finite operation replay plus scoped QF_UF/Alethe conflicts
theorem horizon       -> isomorphism theorems, correspondence, localization, Noetherianity
```

## What Is Not Proved Yet

The current packs do not prove:

- first, second, third, or lattice isomorphism theorems for arbitrary groups,
  rings, modules, or algebras;
- normal-subgroup quotient theory beyond the displayed finite quotient;
- ideal correspondence theorems for arbitrary rings;
- prime, maximal, radical, primary, or Noetherian ideal theory;
- localization, spectra, sheaves, schemes, or algebraic geometry;
- categorical universal properties for quotient objects;
- functorial or naturality statements about kernels, images, quotients, or
  induced maps in arbitrary categories.

Those claims need theorem statements, algebraic hypotheses, and no-`sorry`
proof artifacts before they can graduate from horizon metadata to theorem
coverage.

## Query The Boundary

Find the finite rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-algebra-homomorphisms-v0 \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-ideals-v0 \
  --require-any
```

Find the checked QF_UF/Alethe rows:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-algebra-homomorphisms-v0 \
  --route Alethe \
  --proof-status checked \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-ideals-v0 \
  --route Alethe \
  --proof-status checked \
  --require-any
```

Find quotient and ideal drilldowns:

```sh
python3 scripts/query-foundational-resources.py checks \
  --pack finite-algebra-homomorphisms-v0 \
  --text quotient \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-ideals-v0 \
  --text quotient \
  --require-any

python3 scripts/query-foundational-resources.py checks \
  --pack finite-ideals-v0 \
  --text ideal \
  --require-any
```

Find the theorem horizons:

```sh
python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-algebra-homomorphisms-v0 \
  --require-any

python3 scripts/query-foundational-resources.py horizon-frontier \
  --pack finite-ideals-v0 \
  --require-any
```

## Graduation Criteria

Homomorphism and quotient resources graduate only when they add:

1. precise theorem statements for the isomorphism, correspondence, quotient,
   or ideal-theory claim;
2. explicit hypotheses, including group/ring/module kind, normality,
   two-sidedness, commutativity, unitality, exactness, or finiteness
   assumptions;
3. no-`sorry` proof artifacts for each theorem claim before display labels
   change from finite replay to theorem coverage;
4. a kernel-checked route that connects the finite examples to the theorem
   statement only where that instantiation is actually proved;
5. display labels that keep finite table replay, QF_UF/Alethe equality
   evidence, and theorem horizons separate.

Until then, the packs remain finite checked resources and compact bridges to
future algebra proof resources.

## Validate

From the repository root:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-algebra-homomorphisms-v0
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/finite-ideals-v0
python3 scripts/query-foundational-resources.py checks --pack finite-algebra-homomorphisms-v0 --route Alethe --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-ideals-v0 --route Alethe --proof-status checked --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-algebra-homomorphisms-v0 --text quotient --require-any
python3 scripts/query-foundational-resources.py checks --pack finite-ideals-v0 --text quotient --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-algebra-homomorphisms-v0 --require-any
python3 scripts/query-foundational-resources.py horizon-frontier --pack finite-ideals-v0 --require-any
```

Expected resource boundary: finite maps, kernels, images, ideals, and quotient
tables validate; scoped preservation, additive-closure, and representative
independence contradictions stay checked QF_UF/Alethe evidence; general
isomorphism and ideal-theory theorems remain explicit Lean/theorem horizons.
