(set-logic AUFLIRA)
(define-sort Row () (Array Int Real))
(declare-fun a () (Array Int Row))
(check-sat)
