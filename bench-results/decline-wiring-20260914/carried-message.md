# The carried message, shown end to end rather than asserted

ADR-1980's named prerequisite: where a rung converts another rung's refusal, the
refusing rung's own sentence must reach whatever the ladder ends on, or a
blocker census silently starts reading a different string.

The unit test pins the shape. This is the same thing measured through the
SHIPPED give-up string, on a real file
(`UFLIA/sledgehammer/QEpres/smtlib.1120322.smt2`, HEAD binary, 24 s budget,
`AXEYUM_QPROBE_HELD_SET_REPLAY=10000` so the replay prints its `why=`).

## OFF — the shipped arm

    why=ResourceLimit|combined theories: eager Ackermann elimination would emit
    944361 congruence constraints, exceeding the deterministic admission bound
    of 64 (the O(k²) expansion and its downstream solve run unbounded; this
    needs a lazy/CEGAR route)

The query gives up naming a bound, and nothing says which rung was running when
it did. A census keyed on this string ranks the bound as the remedy. That is how
ADR-2020 got to "missing wiring".

## ON — the hoist

    why=ResourceLimit|integer bit-blast width ladder: no width is attemptable —
    the admission test that guards every rung is decided before `width` is read,
    so all 15 rungs refuse identically (each would have cloned the whole term DAG
    first). The refusing rung said: combined theories: eager Ackermann
    elimination would emit 944361 congruence constraints, exceeding the
    deterministic admission bound of 64 (the O(k²) expansion and its downstream
    solve run unbounded; this needs a lazy/CEGAR route)

Three things a census can now read that it could not before: **which rung ended**
(the width ladder), **why no other rung could have differed** (the test is
decided before `width` is read, 15 rungs identical), and **the refusing rung's
sentence verbatim** — so a census that peels to the innermost reason still
buckets this exactly where it did, and the pair count (944,361) is unchanged.

Note the same file also emits
`UF+arithmetic: lazy Ackermann abstraction build would still construct 6818682
congruence terms, exceeding the secondary bound of 2000000` in BOTH arms. That
is the over-bound dispatcher's OTHER exit (`refuse_pathological_for_lazy`),
firing on a different ground set of the same file — further evidence that these
queries reach `auto.rs:4068` and are handled there.
