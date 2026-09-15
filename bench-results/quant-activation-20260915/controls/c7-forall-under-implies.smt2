; CONTROL 7 -- the DISCRIMINATING control for the whitelist column.  The
; universal sits at a POSITIVE position, but the path to it crosses a `=>` and
; a `not`, and `PositiveContext` accepts a path of `BoolAnd`/`BoolOr` steps
; ONLY.  So `context` is `None` and every matched tuple is dropped as
; `rej_nocontext` -- while c2, whose path is one `or` step, gets a context and
; is handed off.  A classifier that reported both as "split" could not tell the
; shape the engine already handles from the shape it throws away.
; qshape expects: pos_forall_split=1 split_whitelisted=0 split_refused=1
;                 widen_target=1 activation_target=1
(set-logic UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const c Bool)
(assert (not (=> (forall ((y Int)) (> (f y) y)) c)))
(assert (< (f a) a))
(check-sat)
