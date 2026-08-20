# Exact Fibonacci semantic receipt

Date: 2026-08-20

## Result

The exact official `Nat.fib_coprime_fib_succ` candidate now has one
dependency-bound semantic theorem receipt, independently reissued from two
fresh complete target reconstructions.

The receipt SHA-256 is
`34b9aad06fc8a640c81df0951b1af37a464f2d9305c048784e4f590b83ff0d0e`.
It binds:

- frozen r082 source stream
  `6afa79d79481403d3e3273ea3eea26b4d1194762f9bd623ec019f8e821323cfd`;
- target definition `Axeyum.Autogenesis.Coverage.r082` and fact
  `F:ml430-nat-fib-coprime-fib-succ-162fc738`;
- exact goal, proof, and theorem declaration identities;
- sealed candidate observation
  `a1d92b2090392ac90e22419e6e4f6572beff1cbbd27f83d72c7dfcd566ca860a`;
- policy `nat-fib-coprime-official-receipt-v1`;
- operation `official-fibonacci-coprimality-induction-v1` and its fixed
  one-template, two-submission, one-invocation, zero-retry budget; and
- all eight preregistered direct theorem names and canonical declaration
  identities.

The complete kernel-derived axiom footprint is empty. The receipt also binds
115 transitive theorem rows as replayed diagnostics with set SHA-256
`fa08448a022db2ba1fdd4226979a86854e561888658801d295f4dba0dc3ef84e`.
Those rows do not become an expanded premise whitelist.

## Independent replay

The issuer performs two separate full constructions from the immutable input
streams:

1. compose all seven support roots over the three checked target leaves;
2. compose the axiom-free pointwise Fibonacci recurrence;
3. construct and ordinarily admit the exact official theorem;
4. issue the dependency-bound receipt from the first environment; and
5. reconstruct the second environment, reissue the complete receipt, and
   compare every field and the receipt digest.

Two complete process executions produced byte-identical 29,591-byte
observations with SHA-256
`70862ddfb6ce5e66e0320cb4f4e2bf54e4d33da31ece5b7cbe8484fc0e8a80cf`.
The previously sealed default, exact-target, and authority-audit modes remained
byte-identical after the refactor.

## Immutable evidence

The read-only receipt pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/169aab71b-exact-fibonacci-semantic-receipt-v1/manifest.json`

Its manifest SHA-256 is
`eb965a345686d349c9615199a7009730152edefdbf9c49d454bdb95e0c3b427e`.
The directory is mode `0555`; all three files are mode `0444`. The tracked
checker recomputes the receipt digest, binds historical implementation blobs
and both prerequisite packs, verifies every authority field, checks the direct
and transitive dependency inventories, and enforces zero fact/evaluation/ledger
credit. Seventeen mutation tests exercise the cumulative evidence chain.

## Reproduction

```sh
cargo run -q -p axeyum-lean-import \
  --example nat_gcd_succ_specialization -- \
  /path/to/nat-mod-invariant.ndjson \
  /path/to/r082.ndjson \
  /path/to/nat-gcd-bridge.ndjson \
  --issue-receipt \
  /path/to/fib-recurrence.ndjson \
  /path/to/exact-theorem.json

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
python3 -m unittest \
  scripts.tests.test_check_autogenesis_nat_fib_coprime_premise_plan
```

## Authority boundary and next step

The receipt is checked candidate evidence. It is not an admission event and
has not changed the fact. Evaluation credit and ledger writes remain zero.

Next, register one exact receipt-consuming operation for this fact. Its
executor must accept only this receipt pack and its frozen source/candidate
authority, then use the ordinary crash-safe prepare/apply protocol. The fact
may change only after durable intent, event replay, settled-fact replay, and
derived child-readiness checks all agree.
