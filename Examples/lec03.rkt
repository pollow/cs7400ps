#lang racket
(require redex)

;; Grammar, metafunctions, design of metafunctions 
;;------------------------------------------------


(define-language Assignments ;; DATA DEFINITION
  (stmt ::= (x = expr))
  (expr ::= 
        1
        x
        (expr + expr))
  (x    ::=
        a b c))

;(test-equal (redex-match? Assignments expr (term (a + b))) #t)
;(test-equal (redex-match? Assignments stmt (term (a = 1))) #t)

;; ---------------------------------------------------------------
;; CONSTRAINT: Assignment statements must use 'a' only on LHS 
;; 
;; PROBLEM: Design a function that checks whether a 
;; given STMT satisfies this constraint

;; a-on-lhs : stmt -> boolean
;; Does the stmt have a on the LHS?
(define-metafunction Assignments
  a-on-lhs : stmt -> boolean
  [(a-on-lhs (a = expr)) #t]
  [(a-on-lhs stmt) #f])
  

;; DATA EXAMPLES
(define s1 (term (a = 1)))
(define s2 (term (a = (a + 1))))
(define s3 (term (b = (c + a))))

(test-equal (term (a-on-lhs ,s1)) #t)
(test-equal (term (a-on-lhs ,s2)) #t)
(test-equal (term (a-on-lhs ,s3)) #f)

;; ---------------------------------------------------------------
;; PROBLEM: Is the given variable a or b? (we don't like c) 

;; SIGNATURE & PURPOSE
;; good-var : x -> boolean
;; Is the given variable a or b?
(define-metafunction Assignments 
  good-var : x -> boolean
  [(good-var c) #f]
  [(good-var x) #t])

#;(define-metafunction Assignments 
  good-var : x -> boolean
  [(good-var a) #t]
  [(good-var b) #t]
  [(good-var c) #f])
    
(test-equal (term (good-var a)) #t)
(test-equal (term (good-var b)) #t)
(test-equal (term (good-var c)) #f)


(test-results)