#lang racket
(require redex)

;; introduce ellipses in grammar patterns, 
;; design of functions on list-mingled data
;; where clauses to avoid cons 

;; ---------------------------------------------------------------
(define-language Assignments
  (stmt ::= 
        (x = expr)
        (block stmt ...))
  (expr ::= 1 x (expr + expr))
  (x    ::= a b c))

(define e1 (term a))
(define e2 (term (c + (a + b))))
(define e3 (term ((a + 1) + (a + b))))

(define s1 (term (b = 1)))
(define s2 (term (block ,s1 ,s1 (a = c))))

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
   (where (x_1 ...) (vars expr))]
  [(vars-stmt (block stmt ...)) 
   (vars-stmt-list stmt ...)])

(define-metafunction Assignments
  vars-stmt-list : stmt ... -> (x ...)
  [(vars-stmt-list) ()]
  [(vars-stmt-list stmt_1 stmt_2 ...)
   (x_1 ... x_2 ...)
   (where (x_1 ...) (vars-stmt stmt_1))
   (where (x_2 ...) (vars-stmt-list stmt_2 ...))])
  

(test-equal (term (vars-stmt (c = ,e3))) (term (c a a b)))
(test-equal (term (vars-stmt ,s1)) (term (b)))
(test-equal (term (vars-stmt ,s2)) (term (b b a c)))


(test-results)