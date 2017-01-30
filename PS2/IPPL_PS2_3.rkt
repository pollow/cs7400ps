#lang racket
(require redex)

;;  An Expression is one of:
;;   -- Variable
;;   -- (function Variable Expression)
;;   -- (Expression Expression)
;;  A Variable is a String.
(define-language A
  (Expression ::=
              (Expression Expression)
              (function Variable Expression)
              Variable)
  (Variable ::= string))

(define a1 (term (function "y"
                           ((function "x"
                                      ("x" "y"))
                            ("x" "y")))))

(test-equal (redex-match? A Expression a1) #t)


;;  An DBExpression is one of:
;;   -- Number
;;   -- Variable
;;   -- (function Variable DBExpression)
;;   -- (DBExpression DBExpression)
;;  A Variable is a String.

(define-language DB
  (DBExpression ::=
                (DBExpression DBExpression)
                (function Variable DBExpression)
                Variable
                number)
  (Variable ::= string))

(define db1 (term (function "y"
                           ((function "x"
                                      (0 1))
                            ("x" 0)))))

(test-equal (redex-match? DB DBExpression db1) #t)
(test-equal (redex-match? DB DBExpression a1) #t)
(test-equal (redex-match? A DBExpression db1) #f)

(define-union-language S A DB)
(test-equal (redex-match? S DBExpression a1) #t)
(test-equal (redex-match? S DBExpression db1) #t)

;; ENV tracking the depth of the scope of a variable in a function.
(define-extended-language ES S
  (ENV := (Variable number)))

;; The function consumes an Expression and produces a DBExpression.
;; For each variable introduced by the first clause in an Expression,
;; db replaces it with the number of function nodes between it and the closest
;; enclosing function node that comes with the same variable. If there is no such node,
;; the variable is left unchanged in the output.
(define-metafunction ES
  db : Expression (ENV ...) ... -> DBExpression
  [(db Variable) Variable]
  [(db Variable ((Variable_1 number_1) ...
                 (Variable number)
                 (Variable_2 number_2) ...))
   number
   (side-condition (not (member (term Variable) (term (Variable_1 ...)))))]
  [(db Variable (ENV ...)) Variable]
  [(db (function Variable Expression))
   (function Variable (db Expression ((Variable 0))))]
  [(db (function Variable Expression)
       ((Variable_1 number_1) ... (Variable number) (Variable_2 number_2) ...))
   (function Variable
             (db Expression (inc ((Variable_1 number_1) ...
                                  (Variable -1)
                                  (Variable_2 number_2) ...))))
   (side-condition (not (member (term Variable) (term (Variable_1 ...)))))]
  [(db (function Variable Expression) (ENV ...))
   (function Variable (db Expression ((Variable 0) ENV_1 ...)))
   (where (ENV_1 ...) (inc (ENV ...)))]
  [(db (Expression_1 Expression_2))
   ((db Expression_1) (db Expression_2))]
  [(db (Expression_1 Expression_2) (ENV ...))
   ((db Expression_1 (ENV ...)) (db Expression_2 (ENV ...)))])

;; The function increase the number component of each ENV by 1.
;; For example, (inc ("x" 1) ("y" 2)) -> (("x" 2) ("y" 3))
(define-metafunction ES
  inc : (ENV ...) -> (ENV ...)
  [(inc ()) ()]
  [(inc ((Variable number)))
   ((Variable ,(+ (term number) 1)))]
  [(inc ((Variable number) (Variable_1 number_1) ...))
   ((Variable ,(+ (term number) 1)) ENV_1 ...)
   (where (ENV_1 ...) (inc ((Variable_1 number_1) ...)))])

(test-equal (term (inc (("x" 1) ("y"  2) ("z" 3))))
            (term (("x" 2) ("y" 3) ("z" 4))))

(test-equal (term (db ,a1)) (term ,db1))

(define a2 (term (function "y"
                           ((function "x"
                                      ((function "z"
                                                 ("x" (function "x"
                                                                ("x","y")))) "y"))
                            ("x" "y")))))

(define db2 (term (function "y"
                           ((function "x"
                                      ((function "z" (1 (function "x" (0,3)))) 1))
                            ("x" 0)))))

(define a3 (term (function "y"
                           ((function "x"
                             ((function "z" ("x"
                                             (function "y"
                                                ((function "x"
                                                  ((function "z" ("x"
                                                    (function "x" ("x","y")))) "y"))
                                                     ("x" "y"))))) "y"))
                            ("x" "y")))))

(define db3 (term (function "y"
                           ((function "x"
                             ((function "z" (1
                                             (function "y"
                                                ((function "x"
                                                  ((function "z" (1
                                                    (function "x" (0,3)))) 1))
                                                     (2 0))))) 1))
                            ("x" 0)))))

(test-equal (redex-match? DB DBExpression db2) #t)
(test-equal (redex-match? A Expression a2) #t)

(test-equal (redex-match? DB DBExpression db3) #t)
(test-equal (redex-match? A Expression a3) #t)

(test-equal (term (db ,a2)) (term ,db2))
(test-equal (term (db ,a3)) (term ,db3))