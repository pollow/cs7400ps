#lang racket
(require redex)

;; extending a language for defining functions 
;; escape to Racket (for using simple functions); 
;; auxiliary functions and side-conditions 

;; ---------------------------------------------------------------
;; Note: grammar in this file uses prefix notation instead of infix
(define-language Assignments
  (stmt ::= (= x expr)) 
  (expr ::= 1 x (+ expr expr))
  (x    ::= a b c))

(define e1 (term (+ a 1)))
(define e2 (term (+ (+ a c) b)))

(define-extended-language Value Assignments
  (venv ::= ((x n) ...))
  (n ::= natural))

;; PROBLEM: determine the value of an expr, 
;; given a list of variable-number pairings 

;; val : expr venv -> natural
;; Determine value of expr given var-environment
(define-metafunction Value
  val : expr venv -> natural
  [(val 1 venv) 1]
  [(val x venv) (lookup x venv)]
  [(val (+ expr_1 expr_2) venv)
   ,(+ (term (val expr_1 venv)) (term (val expr_2 venv)))])

;; lookup : x venv -> natural 
;; extract the value paired with x in venv
(define-metafunction Value
  lookup : x venv -> natural 
  [(lookup x ((x_1 n_1) ... (x n) (x_2 n_2) ...))
   n
   (side-condition (not (member (term x) (term (x_1 ...)))))])


(test-equal (term (val 1 ())) 1)
(test-equal (term (val ,e1 ((c 3) (a 4) (a 3)))) 5) 
(test-equal (term (val ,e1 ((b 3) (a 4)))) 5)
(test-equal (term (val ,e2 ((c 1) (b 3) (a 5)))) 9)

(test-results)