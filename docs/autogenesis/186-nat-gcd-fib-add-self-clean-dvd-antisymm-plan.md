# Clean divisibility antisymmetry plan for `Nat.gcd_fib_add_self`

Date: 2026-08-21

The dependency audit reduced official `Nat.dvd_antisymm` to one contaminated
edge: `Nat.le_of_dvd`. The next operation therefore constructs exactly two
target-owned supports.

First, it duplicates Axeyum's independently kernel-checked, empty-footprint
native `Nat.le_of_dvd` proof under
`Axeyum.Autogenesis.leOfDvdCleanV1`. Its expected direct dependencies are the
three native clean multiplication/order lemmas measured from the kernel.

Second, it constructs `Axeyum.Autogenesis.dvdAntisymmCleanV1` directly in the
exact r091 kernel. It case-splits both natural numbers: zero branches use the
measured clean `Nat.eq_zero_of_zero_dvd`; successor branches use the injected
clean divisor bound and official clean `Nat.le_antisymm`. The other three
official leaves are composed from the sealed audit stream and every composition
must replay.

Two fresh invocations must be byte-identical. Across both, the ceiling is four
stream reads, four compositions, four support theorem submissions, zero target
submissions, and zero retries. No proof term, theorem type, or theorem value may
be rendered.

```sh
python3 scripts/check-autogenesis-nat-gcd-fib-add-self-clean-dvd-antisymm-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_clean_dvd_antisymm_plan
```
