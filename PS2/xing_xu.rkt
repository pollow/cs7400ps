#lang racket
(require redex)

;; ----------------------- PROBLEM 1 -----------------------
(define-language mobile
  (m w        ; atomic sculpture (weight)
     (m m w)) ; composite
  (w number)) ; weight is a number

(define m1 (term 0))
(define m2 (term (0 1 2)))
(define m3 (term (,m1 ,m2 3)))
(define m4 (term (,m2 ,m3 4)))
(define m5 (term (,m4 ,m3 ,m4)))
(define m6 (term (,m4 ,m4 7)))

(test-equal (redex-match? mobile m m1) #t)
(test-equal (redex-match? mobile m m2) #t)
(test-equal (redex-match? mobile m m3) #t)
(test-equal (redex-match? mobile m m4) #t)
(test-equal (redex-match? mobile m m5) #f)
(test-equal (redex-match? mobile m m6) #t)

;; counts the number of atomic sculptures in a mobile
(define-metafunction mobile
  num-atomics : m -> number
  [(num-atomics w) 1]
  [(num-atomics (m_1 m_2 w)) ,(+ (term (num-atomics m_1))
                                 (term (num-atomics m_2)))])

(test-equal (term (num-atomics ,m4)) 5)
(test-equal (term (num-atomics ,m6)) 10)

;; determines the total weight of a mobile
(define-metafunction mobile
  total-weight : m -> number
  [(total-weight w) ,(term w)]
  [(total-weight (m_1 m_2 w)) ,(+  (term (total-weight m_1))
                                   (term (total-weight m_2))
                                   (term w))])

(test-equal (term (total-weight ,m4)) 13)
(test-equal (term (total-weight ,m6)) 33)

;; determines the maximal number of links from the
;; top of a mobile to one of its atomic sculptures
(define-metafunction mobile
  depth : m -> number
  [(depth w) 0]
  [(depth (m_1 m_2 w)) ,(+ (term ,(max (term (depth m_1))
                                       (term (depth m_2))))
                           1)])

(test-equal (term (depth ,m4)) 3)
(test-equal (term (depth ,m6)) 4)

;; replaces all atomic sculptures with an old weight with
;; atomic sculptures of a new weight in some mobile
(define-metafunction mobile
  replace : m number number -> m
  [(replace w number_old number_new)
   number_new
   (side-condition (= (term w) (term number_old)))]
  [(replace w number_old number_new) w]
  [(replace (m_1 m_2 w) number_old number_new)
   ((replace m_1 number_old number_new)
    (replace m_2 number_old number_new)
    w)])

(define mr1 (term 7))
(define mr2 (term (7 1 2)))
(define mr3 (term (,mr1 ,mr2 3)))
(define mr4 (term (,mr2 ,mr3 4)))

(test-equal (term (replace 1 0 7)) 1)
(test-equal (term (replace ,m2 0 7)) mr2)
(test-equal (term (replace ,m4 0 7)) mr4)
(test-equal (term (replace ,m4 9 7)) m4)


;; determines whether or not a mobile is balanced. A mobile is balanced if
;; the weight of  the mobile on one end is equal to the weight of the mobile
;; on the other end. The weight of a mobile naturally includes the beams.
(define-metafunction mobile
  balanced? : m -> boolean
  [(balanced? w) #t]
  [(balanced? (m_1 m_2 w))
   ,(=  (term (total-weight m_1))
        (term (total-weight m_2)))
   (side-condition (term (balanced? m_1)))
   (side-condition (term (balanced? m_2)))]
  [(balanced? any) #f])

(test-equal (term (balanced? ,m4)) #f)
(test-equal (term (balanced? ,m6)) #f)
(define mb1 (term (1 1 2)))
(define mb2 (term (,mb1 ,mb1 3)))
(define mb3 (term (,mb2 (4 4 3) 9)))
(test-equal (term (balanced? ,mb1)) #t)
(test-equal (term (balanced? ,mb2)) #t)
(test-equal (term (balanced? ,mb3)) #t)
;; ----------------------- PROBLEM 1 END -----------------------
;; ----------------------- PROBLEM 2 -----------------------

(define-language Graph
  (g (graph n ... e ...))
  (n (node x))
  (e (edge x x))
  (x variable-not-otherwise-mentioned))
 
(define g1 (term (graph (node a) (node b) (node c)
                        (edge b a) (edge b c))))
(define g2 (term (graph (node a) (node b)
                        (edge b a) (edge b c))))

(test-equal (redex-match? Graph g g1) #t)
(test-equal (redex-match? Graph g g2) #t)

;; determines whether or not the edges in a Graph g
;; mention only names that also name a node in g
(define-metafunction Graph
  good : g -> boolean
  [(good (graph n ...)) #t] ; for empty graph
  [(good (graph e ...)) #f]
  [(good (graph n ... (edge x_1 x_2) e ...))
   (good (graph n ... e ...))
   (side-condition (member (term (node x_1)) (term (n ...))))
   (side-condition (member (term (node x_2)) (term (n ...))))]
  [(good any) #f])

(test-equal (term (good (graph))) #t)
(test-equal (term (good (graph (node a) (node b) (edge b a)))) #t)
(test-equal (term (good (graph (node a) (node b) (edge b c)))) #f)
(test-equal (term (good ,g2)) #f)
(test-equal (term (good ,g1)) #t)

;; ----------------------- PROBLEM 2 END -----------------------

;; ----------------------- PROBLEM 3 -----------------------


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
;; enclosing function node that comes with the same variable. If there is no 
;; such node, the variable is left unchanged in the output.
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

(define a2
  (term (function "y"
                  ((function "x"
                      ((function "z"
                          ("x" (function "x"
                                  ("x","y")))) "y"))
                   ("x" "y")))))

(define db2
  (term (function "y"
           ((function "x"
               ((function "z" (1 (function "x" (0,3)))) 1))
            ("x" 0)))))

(define a3
  (term (function "y"
           ((function "x"
               ((function "z" ("x"
                   (function "y"
                      ((function "x"
                          ((function "z" ("x"
                              (function "x" ("x","y")))) "y"))
                       ("x" "y"))))) "y"))
            ("x" "y")))))

(define db3
  (term (function "y"
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
;; ----------------------- PROBLEM 3 END -----------------------