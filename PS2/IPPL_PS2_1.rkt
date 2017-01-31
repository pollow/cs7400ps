#lang racket
(require redex)

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
(test-equal (term (balanced? ,mb1)) #t)
(test-equal (term (balanced? ,mb2)) #t)