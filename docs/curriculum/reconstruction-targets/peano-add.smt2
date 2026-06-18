; Peano addition over a Nat datatype, defined by recursion on succ.
; TARGET (not a benchmark): the two universals below require INDUCTION and are
; not SMT-decidable — axeyum parses the datatype/recursion but answers `unknown`.
; The destination is a kernel-checked proof (P3.6/P3.7); see ../DEPTH.md.

(set-logic ALL)

(declare-datatype Nat ((zero) (succ (pred Nat))))

; add(zero, n) = n ; add(succ m, n) = succ (add m n)
(define-fun-rec add ((m Nat) (n Nat)) Nat
  (match m (
    (zero n)
    ((succ k) (succ (add k n))))))

; Goal 1 — right identity:  ∀ n. add(n, zero) = n   (induction on n)
(push 1)
(assert (not (forall ((n Nat)) (= (add n zero) n))))
(check-sat)   ; expected here: unknown (needs induction) — TARGET, not decided
(pop 1)

; Goal 2 — commutativity:  ∀ m n. add(m, n) = add(n, m)   (induction)
(push 1)
(assert (not (forall ((m Nat) (n Nat)) (= (add m n) (add n m)))))
(check-sat)   ; expected here: unknown (needs induction) — TARGET, not decided
(pop 1)
