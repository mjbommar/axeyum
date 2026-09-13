; EXPECT: GAP
; The other half of read-over-write: a write at a DIFFERENT outer index must not
; be visible.  `c1` alone would pass an implementation that returned the stored
; row unconditionally, so this fixture is what makes the pair discriminating.
;
; It is EXPECT: GAP rather than EXPECT: REACH because axeyum answers `unknown`
; on its surrogate today, and the reason is measured rather than guessed: the
; surrogate is
;
;   (assert (not (= i j)))
;   (assert (not (= (select (ite (= i j) r (|M..row| j)) o)
;                   (select (|M..row| j) o))))
;
; and writing the SAME query with `select` pushed through the array-sorted `ite`
; by hand gives `unsat`.  So the gap is one rewrite -- select-over-ite on an
; array-sorted `ite` whose branch is a UF-returned row -- and NOT the array
; theory.  `crates/axeyum-rewrite/src/arrays.rs` already has that rewrite; it is
; `eliminate_arrays`' own, and this query does not reach it.
;
; Sizing it was the point of the sweep's `--distribute` arm, which pushes the
; `select` through for every file.  It is worth +0 on ALIA and +0 on ABV.
(set-logic ALIA)
(declare-fun M () (Array Int (Array Int Int)))
(declare-fun r () (Array Int Int))
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun o () Int)
(assert (not (= i j)))
(assert (not (= (select (select (store M i r) j) o) (select (select M j) o))))
(check-sat)
