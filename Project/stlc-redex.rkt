#lang racket

(require redex "tut-subst.rkt")

;; Ruling out run-time errors by type checking

;; SYNTAX
(define-language STLC
  [v ::= ;; values
     x
     true
     false
     (λ (x t) e)]
  [e ::= ;; expressions
     v
     (if e then e else e)
     (e e)]
  [t ::= ;; types
     bool
     (t -> t)]
  [x ::= ;; variables
     variable-not-otherwise-mentioned]
  [E ::= ;; evaluation contexts
     hole
     (if E then e else e)
     (E e)
     (v E)]
  )

(define ex1 (term ((λ (x (bool -> bool)) x) (λ (w bool) w))))
(define re1 (term (λ (w bool) w)))

(define ex2 (term ((λ (x (bool -> bool)) (λ (y bool) x)) (λ (w bool) w))))
(define re2 (term (λ (y bool) (λ (w bool) w))))

(define ex3 (term ((λ (x (bool -> (bool -> bool))) x)
                   (λ (y bool) (λ (z bool) z)))))
(define re3 (term (λ (y bool) (λ (z bool) z))))

(define not (term (λ (x : bool) (if x then false else true))))
(define ex10 (term (not true)))
(define re10 (term false))

(define ex11 (term (not false)))
(define re11 (term (true)))

(define-metafunction STLC
  subst : x e e -> e
  [(subst x e_1 e)
   ,(subst/proc (redex-match STLC x)
                (term (x))
                (term (e_1))
                (term e))])

(define ->v
  (reduction-relation
   STLC
   #:domain e
   (--> (in-hole E (if true then e_1 else e_2))
        (in-hole E e_1)
        if-true)
   (--> (in-hole E (if false then e_1 else e_2))
        (in-hole E e_2)
        if-false)
   (--> (in-hole E ((λ (x t) e_1) v))
        (in-hole E (subset x v e_1))
        app)))

(define-extended-language STLC-typ STLC
  (G ::= ((x t) ...)))

(define-judgment-form STLC-typ
  #:contract (typed G e t)
  #:mode (typed I I O)
  [ ;; x : t \in G
   ------------------------------------------------ tvar
   (typed ((x_1 t_1) ... (x t) (x_2 t_2) ...) x t)]

  [(typed ((x t) (x_1 t_1) ...) e t_r)
   ----------------------------------------------- tlam
   (typed ((x_1 t_1) ...) (λ (x t) e) (t -> t_r))]

  [(typed G e_fun (t_arg -> t_res))
   (typed G e_arg t_arg)
   ---------------------------------- tapp
   (typed G (e_fun e_arg) t_res)]

  [
   ---------------- ttrue
   (typed G true bool)]
  [
   ---------------- tfalse
   (typed G false bool)]
  [
   (typed G e_1 bool)
   (typed G e_2 t_r)
   (typed G e_3 t_r)
   ---------------- tif
   (typed G (if e_1 then e_2 else e_3) t_r)])

;; ----------------------------------------------------------
;; (evaluate e) determines the value of e using CBN reduction

(module+ test
  (test-equal (term (evaluate ,ex1)) re1)
  (test-equal (term (evaluate ,ex2)) re2)
  (test-equal (term (evaluate ,ex3)) re3)
  (test-equal (term (evaluate ,ex10)) re10)
  (test-equal (term (evaluate ,ex11)) re11))

(define-metafunction STLC
  evaluate : e -> v or "type error!"
  [(evaluate e)
   ,(first (apply-reduction-relation* ->v (term e)))
   (side-condition (judgment-holds (typed () e t)))]
  [(evaluate e)
   "type error!"])


;; -------------------------------------------------------------------
;; PROBLEMS


(define bad (term (w (λ (x bool) x))))
(test-equal (term (evaluate ,bad)) "type error!")
(define bad1 (term (true (λ (x bool) x))))
(test-equal (term (evaluate ,bad1)) "type error!")


(define ex4 (term ((λ (x (int -> int)) ((λ (y int) (x y)) 4)) (λ (z int) z))))
(define (test4) (term (evaluate ,ex4)))
(define (trace4) (traces ->v ex4))
; (show ex4)

(define ex5 (term ((λ (x ((int -> int) -> int))
                     ((λ (y (int -> int)) (x y)) (λ (z int) z))) 42)))
(define (test5) (term (evaluate ,ex5)))
; (show ex5)

;; ----------------------------

(define (show ex)
  (traces ->v ex
          #:pred
          (lambda (e)
            (if (judgment-holds (typed () ,e t))
                "limegreen"
                "pink"))))

