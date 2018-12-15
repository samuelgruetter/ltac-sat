; Cannot use bitvectors of parametric size :(
; https://stackoverflow.com/questions/10329721/generic-bitvector-type-of-any-length
; (declare-const w Int)
; (declare-const x (_ BitVec w))
; (declare-const y (_ BitVec w))
;
; Note: the inverse function is int2bv, and needs to be parametrized:
; (assert (not (= ((_ int2bv 32) x) ((_ int2bv 32) y))))


; So let's hard-code to 32-bit vectors:

(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))

(assert (= (bv2int x) (bv2int y)))

(assert (not (= x y)))

(check-sat)

(get-model)

(simplify (bv2int #x00000001))
(simplify (bv2int #x00000000))
(simplify (= (bv2int #x00000001) (bv2int #x00000000)))

; z3-4.4.0pre wrongly returns
; sat
; (model
;   (define-fun y () (_ BitVec 32)
;     #x00000000)
;   (define-fun x () (_ BitVec 32)
;     #x00000001)
; )
; 1
; 0
; false

; Z3 version 4.8.0 correctly answers unsat
;  8-bit    0.044s
; 16-bit    5.943s
; 17-bit   15.687s
; 18-bit   60.325s
; takes forever if using 32 bit vectors
