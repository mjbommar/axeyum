# 256 -- nat-bitwise-comm (lane `nat-bitwise-comm`)

<!-- plan-section: lane-status -->

Status: `bitwise_comm` LANDED and closed. `lt_xor_cases` NOT attempted --
sized only (see below), per the brief's "landing bitwise_comm alone is a
good outcome."

## Task
- `F:ml430-nat-bitwise-comm-1a273bae` (`Nat.bitwise_comm`) -- primary
  target. **DONE**, flipped to `proved`.
- `F:ml430-nat-lt-xor-cases-c43a1e85` (`Nat.lt_xor_cases`) -- secondary.
  **NOT attempted.** Still `open`.

## `bitwise_comm`: what was built and why

### Did the unconditional form hold, or did it need `Le` hypotheses?

Needed `Le` hypotheses -- `lor`'s shape, not `land`'s. A Python simulation
(`bitwiseAux` re-implemented directly, not committed -- pure scratchpad)
run BEFORE any Rust was written:

```python
def bitwiseAux(f, fuel, m, n):
    if fuel == 0:
        return n if f(False, True) else 0
    if n == 0:
        return m if f(True, False) else 0
    if m == 0:
        return n if f(False, True) else 0
    return 2 * bitwiseAux(f, fuel - 1, m // 2, n // 2) + \
        (1 if f(m % 2 == 1, n % 2 == 1) else 0)
```

Result: `bitwiseAux(or, 0, 0, 1) = 1` but `bitwiseAux(or, 0, 1, 0) = 0` --
the unconditional (fuel not necessarily sufficient) form is FALSE whenever
`f false true = true` (`f = or`, `f = xor`), and true only when
`f false true = false` (`f = and`, matching `land`'s absorbing-zero row --
see CLAUDE.md's own "AND IT PROPAGATES INTO THE STATEMENT" entry, added
independently the same day and describing exactly this). With `Le m fuel`
AND `Le n fuel` (sufficient fuel for both operands), the statement held for
`and`/`or`/`xor` over 2000 random trials each, and `bitwise f m n =
bitwise f n m` (canonical fuel) held for all three over the full `0..60`
grid. So `bitwise_aux_comm_of_fuel` needed `lor`'s shape
(`Le m fuel -> Le n fuel -> ...`), generalized over `f`, plus an explicit
`hf : forall a b, f a b = f b a` hypothesis `land`/`lor` never needed
(their `f` is fixed and concrete, so commutativity is a closed fact, not a
hypothesis to thread).

### How `f`'s commutativity threads through the per-bit step (and where else it's needed)

Two sites need `hf`, not one:

Detail moved to [`../notes/256-nat-bitwise-comm.md`](../notes/256-nat-bitwise-comm.md).

