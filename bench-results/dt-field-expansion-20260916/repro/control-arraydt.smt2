(set-logic AUFDTLIRA)
; CONTROL for `expansion-reach.py`: the W1 shape, which the lever must NOT
; convert.
;
; `holder`'s field sort is `(Array Int inner)` -- an ARRAY OVER A DATATYPE.
; `field_sort_expands` (datatype_native.rs:1549) rejects it because
; `sort_mentions_datatype` holds, so `register_datatype` (:1511-1518) refuses
; the whole datatype.  Depth unrolling does not reach this: the field is not a
; datatype field, it is an array field, and its expansion variable would carry
; datatype content into the residual for `refuse_if_datatype_survives` to
; refuse.
;
; `expansion-reach.py` must print `today_w1 1` and `lever_converts 0` on
; `holder`.  This is the shape that is 142 of 142 of the refused sorts in the
; DT-GROUND-PROBE population, so a census that scored it convertible would be
; scoring the whole SPARK bucket wrong.
(declare-datatypes ((inner 0)) (((mk_inner (ic Int)))))
(declare-datatypes ((holder 0)) (((mk_holder (arr (Array Int inner))))))
(declare-const a holder)
(assert ((_ is mk_holder) a))
(check-sat)
