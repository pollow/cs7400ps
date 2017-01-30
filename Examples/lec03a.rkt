#lang racket
(require redex)

;; design of functions on plain recursive data
;; introduce ellipses in patterns
;; where clauses to aid pattern-matching functions 

;;---------------------------------------------------
(define-language Assignments ;; DATA DEFINITION
  (stmt ::= (x = expr))
  (expr ::= 
        1
        x
        (expr + expr))
  (x    ::=
        a b c))

(define e1 (term a))
(define e2 (term (c + (a + b))))
(define e3 (term ((a + 1) + (a + b))))

;; ---------------------------------------------------------------
;; PROBLEM: determine the variables that occur in an expr 

;; vars : expr -> (x ...)
;; Produce the list of variables in the given expression
(define-metafunction Assignments
  vars : expr -> (x ...)
  [(vars 1) ()]
  [(vars x) (x)]
  [(vars (expr_1 + expr_2))
   (x_1 ... x_2 ...)
   (where (x_1 ...) (vars expr_1))
   (where (x_2 ...) (vars expr_2))])

(test-equal (term (vars 1)) (term ()))
(test-equal (term (vars ,e1)) (term (a)))
(test-equal (term (vars ,e2)) (term (c a b)))
(test-equal (term (vars ,e3)) (term (a a b)))

;; PROBLEM: determine the variables that occur in a stmt 

;; vars-stmt : stmt -> (x ...)
;; Produce set of variables in stmt
(define-metafunction Assignments
  vars-stmt : stmt -> (x ...)
  [(vars-stmt (x = expr))
   (x x_1 ...)
   (where (x_1 ...) (vars expr))])

(test-equal (term (vars-stmt (c = ,e3))) (term (c a a b)))

(test-results)