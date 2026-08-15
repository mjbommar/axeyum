; NEGATIVE CONTROL for `--verify-formal` -- this script states something FALSE.
;
; It asserts the negation of `F |= sku -> customer_id`, which is NOT a
; consequence of the order-line schema: a catalogue entry says nothing about
; who bought it. So the negation is SATISFIABLE, and `db_design_certify
; --verify-formal` must reject the file rather than report a checked formal
; statement. Without this control, `--verify-formal` would be a flag that
; exits 0 on any script the parser accepts.
;
; The model the solver finds here is exactly the counterexample relation:
; sku and unit_price true, everything else false.

(set-logic QF_UF)
(set-info :status sat)

(declare-const line_uuid Bool)
(declare-const order_id Bool)
(declare-const line_no Bool)
(declare-const sku Bool)
(declare-const qty Bool)
(declare-const unit_price Bool)
(declare-const customer_id Bool)
(declare-const customer_email Bool)
(declare-const warehouse Bool)
(declare-const region Bool)

(define-fun horn () Bool
  (and (=> line_uuid (and order_id line_no))
       (=> (and order_id line_no) (and line_uuid sku qty))
       (=> order_id (and customer_id warehouse))
       (=> customer_id customer_email)
       (=> customer_email customer_id)
       (=> sku unit_price)
       (=> warehouse region)))

(assert (not (=> horn (=> sku customer_id))))
(check-sat)
