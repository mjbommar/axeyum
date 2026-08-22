# The Lemire gap as an uncertainty problem

Status: research note, 2026-08-22. Two of the three correspondences below are
exact mathematics; the third is an analogy. None is a proof, and the note says
at each point what would have to be proved for the analogy to become one.

Companions: [01-target-and-toolkit.md](01-target-and-toolkit.md) (the target),
[02-mechanism-hunt.md](02-mechanism-hunt.md) (what has been tried).

## 1. Exact: Fourier uncertainty on the class group

The ray classes form the finite abelian 2-group `E_ell = (F_2[x]/x^{ell+1})^x`
of order `2^ell`; its dual is the group of Hayes characters. Write `N` for
the prime population on `E_ell` (Mangoldt mass of degree-`n` polynomials in
each class) and `S_n(chi) = N^hat(chi)` for its Fourier transform. Three
facts, all exact:

- **Position data.** The conjecture asks about one position, the identity
  class: a delta function, support `1`, with full momentum support `2^ell`.
  Donoho--Stark on `E_ell` gives `|supp f| . |supp f^hat| >= 2^ell`; the
  identity class is a maximally momentum-spread state.
- **Minimum-uncertainty states are subgroup indicators.** The functions that
  saturate the bound are indicators of subgroups (and their translates), and
  these are exactly the objects whose prime mass is known exactly by
  orthogonality: the power subgroups `2^s E_j` (the `P_{j,s}`), the cylinders
  `hK`. Everything finer than a subgroup has spread-out momentum.
- **Weil is a sup-norm in momentum space.** The Riemann hypothesis gives
  `|S_n(chi)| <= (j-1) 2^{ceil(n/2)}` for each character, a bound on each
  Fourier coefficient's *modulus* with no phase information. A function
  whose Fourier moduli are bounded can be concentrated at any position, so
  the best position bound is the average of the moduli -- the Weil-per-class
  bound, a factor `~ell` short of what is needed.

So the gap is an uncertainty relation in the literal sense: the conjecture
is a sharp position statement, the only available control is a phase-blind
sup bound in momentum, and the two are separated by exactly the factor that
the number of Frobenius eigenvalues per character supplies. Every exact
reformulation in note 02 is a unitary change of coordinates on this pair and
conserves the gap.

## 2. Exact: the Witt layers are the Clifford hierarchy

Identify `F_{2^n}` with `n` qubits (computational basis `F_2^n`) and view a
character of `E_j` as the diagonal unitary
`U_chi : |alpha> -> zeta_{2^s}^{Tr(G(alpha~))} |alpha>`,
`alpha~` the Teichmueller lift, `G` the Witt polynomial of the character.
Then, by the Galois-ring dictionary of note 01 and the carry formula of
note 02:

| Witt order `2^s` | phase function on `F_2^n` | quantum object | status of the layer |
| --- | --- | --- | --- |
| `2` | linear Boolean functions `Tr(f(alpha))`, `f` odd-degree `<= j` | Pauli-`Z` strings (Clifford level 1) | complete sums vanish or are Weil sums of `f` |
| `4` | quadratic forms (the `Z/4` trace `Tr_4(alpha~)`, the Kerdock form) | Clifford diagonal gates, `+-1, +-i` phases; stabilizer / MUB structure | Gauss sums exactly evaluable; `L`-polynomials supersingular (slopes `1/2`); Weil attained exactly (ratio `1` at `(j,s)=(2,2)` for every `n`) |
| `2^s`, `s >= 3` | Witt digit `s-1` of `Tr(alpha~^k)`: Boolean degree `2^{s-1}` (carry formula) | diagonal gates of the `s`-th level of the Clifford hierarchy (`T`-like `zeta_8`, `zeta_16`, ... phases) | no exact evaluation; generic sizes (Teichmueller-trace Gauss sums within 2% of KHC at `s=3,4`); Weil only |

Under this identification the character sum is a transition amplitude,
`S_n(chi) = 2^n <+|^{(x)n} U_chi |+>^{(x)n}` (plus the boundary term at
`alpha = 0`), i.e. an IQP-type amplitude (Bremner--Jozsa--Shepherd), and the
identity-class prime count

```text
N_ell(1) = 2^{-ell} sum_chi S_n(chi)
```

is a coherent sum of `2^ell` such amplitudes, one for every diagonal gate in
the family. The stabilizer boundary (`s <= 2`) is exactly where our data show
rigid, Weil-saturating behaviour, and the post-Clifford region (`s >= 3`) is
exactly where the cancellation the proof needs lives and where generic
amplitudes are `#P`-hard to approximate. This is a precise sense in which the
missing information is "quantum": it is the aggregate interference of
post-Clifford phases, not any individual amplitude. The `Z/4` row is the
classical Kerdock--Clifford correspondence (Hammons--Kumar--Calderbank--
Sloane--Sole 1994; Calderbank--Cameron--Kantor--Seidel 1997); the higher rows
are Carlet's `Z/2^k`-linear Kerdock codes read through the diagonal
Clifford-hierarchy classification (Cui--Gottesman--Krishna 2017).

## 3. Analogy: interference, delocalization, and what would close the gap

The open estimate (note 01, `(HWO)`, `(CYL)`) asks for a saving of a factor
`4 ell` over the incoherent bound. In amplitude language: Weil adds moduli
(intensities), the truth adds amplitudes with phases (interference, square-
root cancellation), and the conjecture needs only *partial* destructive
interference -- a `1/(4 ell)` reduction -- among the `2^{a-1}` momentum
components at the identity position. In statistical-mechanics language: the
second moment over classes is at its random (Sato--Tate) value, the mean is
exact, and the statement needed is that no single named site carries a
`1/(16 ell^2)` fraction of the energy -- a *delocalization* statement. Energy
conservation and mean-field theory cannot forbid a localized state; proving
delocalization needs ergodicity or mixing, and arithmetic has no mixing
theorem for this family at a fixed small field.

What would turn the analogy into a proof, in each language:

- **Uncertainty:** an inequality that uses the *phases* of the `S_n(chi)`,
  not their moduli -- i.e. a correlation statement between different
  `L`-functions of the family at the common frequency `n`. Orthogonality is
  the only phase-aware tool and answers only subgroup-level questions.
- **Quantum:** an interference theorem for the aggregate of post-Clifford
  diagonal amplitudes over the whole Witt layer -- a structural reason why
  the family of degree-`2^{s-1}` phase polynomials cannot conspire at one
  position -- that does not go through evaluating amplitudes (which is
  `#P`-hard generically).
- **Statistical mechanics:** a concentration or anti-concentration inequality
  for a single site in an exponentially large ensemble, without a transitive
  symmetry (only the translation involution exists).

All three are the same missing theorem. Its shape is also visible in the
data: order-`4` layers sit exactly at the incoherent bound (no phases to use),
and the higher-order layers fall below it by a factor that grows like
`2^{ell/2}/ell` (note 02, section 1), which is what one expects of
post-Clifford amplitudes with no residual stabilizer structure.

## 4. What this note does not claim

It does not claim that quantum mechanics proves anything about primes, that
the Lemire problem is `#P`-hard, or that the uncertainty principle forbids a
proof. It claims only that (i) the gap is an exact Fourier-uncertainty gap on
`E_ell`, (ii) the Witt-order filtration of the characters is the Clifford
hierarchy of diagonal gates on `n` qubits, with the data respecting the
stabilizer boundary, and (iii) the missing inequality is, in every language
we have, a statement about aggregate phases of post-Clifford amplitudes. The
value of the identification is that it says which tools are structurally
irrelevant (anything that bounds moduli) and where a proof must look
(aggregate phase structure of the Galois-ring trace digits).

## References

- D. L. Donoho, P. B. Stark, "Uncertainty principles and signal recovery,"
  SIAM J. Appl. Math. 49 (1989).
- A. R. Hammons, P. V. Kumar, A. R. Calderbank, N. J. A. Sloane, P. Sole,
  "The `Z_4`-linearity of Kerdock, Preparata, Goethals, and related codes,"
  IEEE Trans. Inform. Theory 40 (1994).
- A. R. Calderbank, P. J. Cameron, W. M. Kantor, J. J. Seidel, "`Z_4`-Kerdock
  codes, orthogonal spreads, and extremal Euclidean line-sets," Proc. LMS 75
  (1997).
- C. Carlet, "`Z_{2^k}`-linear codes," IEEE Trans. Inform. Theory 44 (1998).
- S. X. Cui, D. Gottesman, A. Krishna, "Diagonal gates in the Clifford
  hierarchy," Phys. Rev. A 95 (2017).
- M. J. Bremner, R. Jozsa, D. J. Shepherd, "Classical simulation of commuting
  quantum computations implies collapse of the polynomial hierarchy," Proc.
  R. Soc. A 467 (2011).
- N. M. Katz, "Witt vectors and a question of Keating and Rudnick," IMRN 2013.

## 5. Barrier lemma: moduli-only inputs cannot prove (REL)

Fix `ell`, `n`, `a = ell - ceil(log2 ell) - 1`, `K = ker(E_ell -> E_{a-1})`,
and let `m(g)` be the cylinder-mean population (the inverse transform of the
true Fourier coefficients of conductor `< a`, i.e. `N_{a-1}(class of g)/|K|`,
nonnegative). Put `c = m(1)/(1 - 2^{a-1-ell})` and

```text
F(g) = m(g) + c ( 2^{a-1-ell} 1_K(g) - delta_{g,1} ).
```

Then `F >= 0` (`F(1) = 0`, `F(g) = m(g) + c 2^{a-1-ell} > 0` on `K\{1}`,
`F = m` off `K`), `sum F = 2^n`, `F^hat(chi) = N^hat(chi)` for every `chi` of
conductor `< a`, `F^hat(chi) = -c` for every `chi` of conductor `>= a`, so
`|F^hat(chi)| ~ 2^{n-ell} <= (a-1) 2^{ceil(n/2)} < (cond(chi)-1)
2^{ceil(n/2)}` for all high conductors (inside Weil by a factor about `a`),
and the second moment of `F` is below that of `N` (measured ratio `0.22,
0.15, 0.12` at `(ell,n) = (12,25), (16,33), (20,41)`, construction verified
numerically with `F(1) = 0` and `min F = 0`). `F` is a legitimate function
on `E_ell` satisfying every hypothesis of the form: total mass,
nonnegativity, exact low-conductor populations, per-character Weil bounds on
the Fourier moduli, bounds on low moments. Since `F(1) = 0`, no argument that
uses only hypotheses of that form can prove `N_ell(1) > 0`, let alone
`(REL)`. Any proof must use that `N` is a Lambda-weighted prime count beyond
its Fourier moduli -- i.e. phase information across the family. This is the
rigorous content of the uncertainty reading above and the population-level
form of the `Q^k` obstruction in note 02 (shape B). It is a barrier for a
class of methods, not an independence result: the conjecture is almost
certainly true, and a phase-aware input is not blocked.

Read with the row/column/diagonal picture: "rows" (conductor fixed, degree
growing) are provable by RH and Deligne's horizontal equidistribution;
"columns" (degree fixed, `q` growing) by Katz's vertical equidistribution;
at fixed `q` everything with `j <= n/2 - log2 n` is provable by Weil and
orthogonality, and the strip `j ~ n/2` -- where the Donoho--Stark product is
saturated and the RH degree factor `j-1` enters -- contains Lemire
(`j = n/2 - 1`) and no theorem.
