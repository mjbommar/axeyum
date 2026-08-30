# Lane: ipc-soundness — slice 4 of `F:excluded-middle-not-intuitionistic`

<!-- plan-section: lane-status -->

**IN PROGRESS.** Early commit per lane protocol: design record only, no code yet.

**Key finding from verifying slices 1-3 (do not skip this).** The brief's
requested soundness statement — `Provable ctx phi -> sat ctx v -> eval phi v = 2`
with `sat` = "every context formula evaluates to top" — is NOT the statement an
induction on the derivation can carry. `imp_intro`'s case is the obstruction:
its induction hypothesis says only *if* `eval phi v = 2` then `eval psi v = 2`,
whereas the goal needs `himp3 (eval phi v) (eval psi v) = 2`, i.e.
`eval phi v <= eval psi v` — and nothing in the hypothesis constrains the case
where `eval phi v` is the middle element 1.

The statement that DOES carry the induction is the standard algebraic one:

    ipc_soundness : Provable ctx phi -> forall v, Nat.le (ipcCtxMeet ctx v) (ipc_eval phi v)

where `ipcCtxMeet nil v = 2` and `ipcCtxMeet (cons a l) v = meet3 (eval a v) (ipcCtxMeet l v)`.
Residuation (`min(m,a) <= b  <->  m <= himp3 a b`) is what makes `imp_intro`
and `imp_elim` go through, and linearity of the chain is what makes `or_elim`
go through. Checked by hand for all eleven cases before writing any code.

`sat` is still built (brief part (a)) and bridged: `sat ctx v -> ipcCtxMeet ctx v = 2`,
so the sat-shaped corollary `Provable ctx phi -> sat ctx v -> Nat.le 2 (eval phi v)`
follows. At `ctx = nil` that is `2 <= eval phi v`, and the countermodel gives
`eval pem (const 1) = 1`, so `Not (Nat.le 2 1)` closes the fact.

<!-- plan-section: landed-changes -->

| 2026-08-30 | ipc-soundness | WIP: slice 4 design record (soundness must run on the context MEET, not on `sat`) |
