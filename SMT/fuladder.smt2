
(set-logic QF_BV) 


(define-fun x () (_ BitVec 8) #b00001101)
(define-fun y () (_ BitVec 8) #b00001110)
(declare-fun z0 () (_ BitVec 8))
(declare-fun sign () (_ BitVec 1))
(declare-fun z1 () (_ BitVec 8))

; Assert the expressions
(assert (= z0 (bvadd x y)))       ; z0 = x + y
(assert (= sign ((_ extract 7 7) z0))) ; sign = most significant bit of z0
(assert (= z1 (bvand z0 #b01111111))) ; z1 = z0 & 0111 (clears the most significant bit)

