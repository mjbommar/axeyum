; The propositional content of F:orders-fd-implication-certified, asserted in
; NEGATED form so that `unsat` is the fact.
;
; A set of functional dependencies is a Horn theory: `A B -> C D` is the clause
; `A /\ B -> C /\ D` over one Boolean per attribute. Implication `F |= X -> Y`
; is then propositional entailment, and its two directions are two shapes of
; valid formula:
;
;   * IMPLIED    -- `horn => (X => Y)` is a tautology, so no assignment can
;                   satisfy F, X and the failure of Y.
;   * NOT IMPLIED -- pin every attribute to the witness assignment and the
;                   formula `witness => (horn /\ X /\ ~y)` is a tautology too.
;                   That reads as: THIS assignment satisfies every dependency,
;                   the determinant, and the failure of the dependent -- which
;                   is exactly the two-row counterexample relation, one row all
;                   zeros and the other differing off the agreement set.
;
; Both shapes are valid, so the conjunction is valid, so its negation below is
; unsatisfiable. Schema and dependencies are
; artifacts/instances/dbdesign/orders-schema.dbd, verbatim.
;
; Checked by:
;   cargo run --release -q -p axeyum-bench --example db_design_certify -- \
;       artifacts/instances/dbdesign/orders-schema.dbd --expect-checks 11 \
;       --verify-formal artifacts/instances/dbdesign/orders-fd-claims.smt2

(set-logic QF_UF)
(set-info :status unsat)

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

; F, verbatim from the instance file.
(define-fun horn () Bool
  (and (=> line_uuid (and order_id line_no))
       (=> (and order_id line_no) (and line_uuid sku qty))
       (=> order_id (and customer_id warehouse))
       (=> customer_id customer_email)
       (=> customer_email customer_id)
       (=> sku unit_price)
       (=> warehouse region)))

; F |= order_id line_no -> region
(define-fun claim_a () Bool (=> horn (=> (and order_id line_no) region)))

; F |= line_uuid -> customer_email
(define-fun claim_b () Bool (=> horn (=> line_uuid customer_email)))

; F |/= sku -> customer_id, witnessed by the rows that agree exactly on
; {sku, unit_price}.
(define-fun witness_sku () Bool
  (and (not line_uuid) (not order_id) (not line_no) sku (not qty) unit_price
       (not customer_id) (not customer_email) (not warehouse) (not region)))
(define-fun claim_c () Bool (=> witness_sku (and horn sku (not customer_id))))

; F |/= warehouse -> order_id, witnessed by the rows that agree exactly on
; {warehouse, region}.
(define-fun witness_warehouse () Bool
  (and (not line_uuid) (not order_id) (not line_no) (not sku) (not qty)
       (not unit_price) (not customer_id) (not customer_email) warehouse region))
(define-fun claim_d () Bool (=> witness_warehouse (and horn warehouse (not order_id))))

(assert (not (and claim_a claim_b claim_c claim_d)))
(check-sat)
