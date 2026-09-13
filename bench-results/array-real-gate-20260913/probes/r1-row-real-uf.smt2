; `p5-row-real` with ONE uninterpreted-function application added, so
; `Features::has_function` is set and the `if features.has_real` branch's
; `Err(Unsupported) if features.has_function` arm falls THROUGH instead of
; returning. That is the only difference from `p5`, and it is what separates
; the two gates the Real-element array population actually sits behind.
;
; The UF atom must not be a tautology: `(= (g i) (g i))` canonicalizes to
; `true` BEFORE the feature scan runs, so `has_function` stays false and the
; probe silently becomes a duplicate of `p5`.
(set-logic AUFLIRA)
(declare-fun m () (Array Int Real))
(declare-fun g (Int) Int)
(declare-fun i () Int)
(declare-fun j () Int)
(declare-fun v () Real)
(assert (> (g i) 0))
(assert (not (= (select (store m i v) j) (ite (= i j) v (select m j)))))
(check-sat)
