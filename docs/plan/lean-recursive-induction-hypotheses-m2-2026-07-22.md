# Lean recursive induction hypotheses: M2 native-semantics result

Status: complete; M3 importer policy and first official-stream product
observation are next

Date: 2026-07-22

Parent:
[TL2.12 execution plan](lean-recursive-induction-hypotheses-tl2.12-plan-2026-07-22.md)

Decision gate:
[proposed ADR-0353](../research/09-decisions/adr-0353-preregister-lean-recursive-induction-hypotheses.md)

## 1. Result

M2 accepts the preregistered single-family native rule:

```text
u : Pi xs, I params indices
u_ih : Pi xs, motive indices (u xs)

iota argument:
fun xs => I.rec params motive minors indices (u xs)
```

One implementation covers all four corners. Empty telescopes and indices are
the historical direct case; nonempty indices give recursive-indexed fields;
nonempty telescopes give higher-order fields; both nonempty give the
`Acc`-shaped case. Constructor classification, minor generation, and rule
generation continue to use M1's shared WHNF telescope-tail representation.

This is a native kernel milestone. No M2 code changes importer metadata policy,
and neither newly frozen official computation stream was passed to the Rust
importer. M3 owns the first product observation, exact official recursor
comparison, policy widening, completion-only publication, and the two
importer-boundary mutation classes.

## 2. Native case matrix

All fourteen registered IDs execute through the public `Kernel::add_inductive`
path.

Positive rows:

- `direct-control`;
- `vector-direct-indexed`;
- `higher-order-zero-index`;
- `acc-indexed-dependent`;
- `two-binder-dependent`;
- `mixed-fields`;
- `multiple-recursive`;
- `implicit-telescope`;
- `reducible-wrapper`;
- `prop-acc`.

Every positive row checks admission, generated recursor metadata, recursor-type
inference, original-field-before-IH ordering, recursive-field ordering,
telescope depth, nested binder information, and an exact selected iota result.
The dependent two-binder row additionally checks dependent binder domains and
uses the recursive occurrence's index rather than the constructor result index.

Negative rows:

- `wrong-tail-params`;
- `family-in-domain`;
- `family-in-index`;
- `nested-foreign-head`.

Every negative row compares the typed error family and the complete environment
snapshot before and after rejection. Invalid fixed parameters, recursive
indices containing the family, negative positions, and foreign-head nesting do
not become recursive fields.

## 3. Mutation teeth

The generated grammar selects and rejects all nine native semantic mutation
classes across applicable cases:

1. `omit-duplicate-reorder-ih`;
2. `ih-before-fields`;
3. `drop-reorder-index`;
4. `constructor-index-for-recursive-index`;
5. `motive-on-unapplied-field`;
6. `nested-lambda-or-argument-order`;
7. `nested-binder-type-or-info`;
8. `neighbor-field-recursion`;
9. `wrong-motive-or-universe`.

A separate exact recursor contract rejects four forms of
`official-recursor-type-minor-rule-nfields`: a changed recursor type, changed
minor-premise type, changed rule RHS, and changed rule field count. These are
native structural mutations against an independently built expected contract;
they are not official-wire observations.

The two remaining registered mutation IDs are intentionally M3 importer work:

- `reflexive-metadata-nonauthority`;
- `late-failure-no-publication`.

M2 does not relabel those boundary checks as native evidence.

## 4. Generated recursive grammar

The fixed generator executes 768 unique public-path cases twice and compares
the complete serialized summary byte-for-byte:

```text
schema=axeyum-lean-recursive-ih-grammar-v1
seed=41585249485f4d32
cases=768
recursive-fields=0:288,1:224,2:160,3:96
profiles=0p0i:192,1p0i:192,1p1i:192,2p1i:192
sorts=type:384,prop:384
depths=0:192,1:192,2:192,3:192
index-productions=none:384,constant:320,field-dependent:64
descriptor-fnv1a64=0d245921566be735
```

The population crosses zero through five total fields, zero through three
recursive fields, telescope depths zero through three, four parameter/index
profiles, `Prop`/`Type`, explicit/implicit/strict-implicit binders, direct and
higher-order recursion, mixed fields, multiple recursive fields, and selected
reducible wrappers. Every positive case checks recursor inference and exact
iota. The production record, not the generated declaration, constructs the
expected rule and selects its applicable mutation.

## 5. TL2.11 positivity control

The mandatory 840-case population and its original descriptor digest remain
frozen. M2 reports two different facts rather than pretending the deliberate
admission widening did not occur:

```text
schema=axeyum-lean-strict-positivity-grammar-v2
seed=4158505354524943
cases=840
admission=admit:360,recursive-indexed:0,reflexive:0,non-positive:270,invalid:210
tl2.11-baseline-outcomes=admit:174,recursive-indexed:42,reflexive:144,non-positive:270,invalid:210
profiles=0p0i:240,1p0i:270,1p1i:330
sorts=prop:420,type:420
depths=0:168,1:168,2:168,3:168,4:168
tl2.11-descriptor-fnv1a64=02985687422aa0ff
```

The 186 formerly deferred positive shapes now admit by design. All 270
non-positive and 210 invalid cases retain their exact fail-closed classes. The
TL2.11 baseline outcome partition and population digest remain explicit
regression facts.

## 6. Bounded validation

All commands used one Cargo build job and the repository's 4 GiB memory
wrapper.

| Gate | Result |
|---|---:|
| kernel library suite | 182 passed |
| strict-positivity public matrix + 840-case grammar | 2 passed |
| recursive-IH matrix + mutation contract + 768-case grammar | 4 passed |
| direct-recursive importer identity control | 1 passed; 19 filtered |
| focused all-target/all-feature clippy with `-D warnings` | passed |
| focused rustdoc with `-D warnings` | passed |

The retained direct declaration identities are unchanged:

| Declaration | SHA-256 |
|---|---|
| `MiniNat.rec` | `dee04a36959066e63f15d5711a5a03de2ac91d71333c48135ef0fdc89cb0f5ef` |
| `MiniList.rec` | `1087558f366706316eefaca0abc48a4b592da2a8496e5d6bbdaa7eea5b677660` |

No full importer or workspace gate is claimed at this intermediate semantic
milestone: the frozen construct-matrix expectation deliberately still records
the pre-M2 recursive-indexed decline. M3 must make and document the first
official product observation, update that matrix from tested facts, and close
the importer gates before TL2.12 can advance.

## 7. Claim boundary and handoff

M2 establishes generated native single-family recursors for the registered
direct, indexed, higher-order, and combined shapes. It does not establish
official stream compatibility, importer policy soundness, mutual groups,
nested-inductive lowering, well-founded frontend support, or broad Lean
parity.

M3 next must:

1. prove `isReflexive` is descriptive metadata rather than permission;
2. retain typed declines for unsafe, nested, malformed, and multi-family
   boundaries;
3. import both frozen official target streams twice with completion-only
   publication;
4. compare official/generated recursor types, rules, counts, and field counts;
5. reject every importer type/rule/metadata/publication mutation; and
6. hand the still-unobserved computation streams to M4.
