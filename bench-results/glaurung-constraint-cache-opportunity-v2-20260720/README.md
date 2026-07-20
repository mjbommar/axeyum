# Canonical constraint-cache opportunity correction

This read-only artifact corrects the exact-identity mismatch exposed by the
rejected ADR-0303 timing campaign. ADR-0303 defined an exact cache key as the
sorted, duplicate-elided set of assertion identities. The v1 opportunity tool
instead keyed exact hits by the ordered textual query SHA-256 while using the
canonical set only for implication lookup.

The compatibility-preserving analyzer now has two explicit modes. Its default
`textual-query` mode reproduces v1 byte semantics; `canonical-constraint-set`
emits this v2 schema and matches the preregistered/implemented cache identity.
Six focused tests include a same-set/different-textual-query control.

Per four-driver process, canonical exact reuse is 8,001/12,902 checks (62.01%),
not 5,868/12,902 (45.48%). Implication-only reuse is correspondingly 562
(4.36%), not 2,695. The structural total is unchanged at 8,563/12,902 (66.37%)
because 2,133 occurrences move only from implication to exact. All five logical
repetitions remain classification-stable within every driver.

This is still opportunity only: no cache cost, timing, memory, or warm-state
additivity conclusion is taken from it.
