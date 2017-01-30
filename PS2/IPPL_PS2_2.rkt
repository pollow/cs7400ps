#lang racket
(require redex)

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
  [(good (graph e ...)) #f]
  [(good (graph n ...)) #t]
  [(good (graph n ... (edge x_1 x_2) e ...))
   ,(and
      (and
      (member (term (node x_1)) (term  (n ...)))
       (member (term (node x_2)) (term  (n ...))))
    (term (good (graph n ... e ...))))])

(test-equal (term (good (graph))) #t)
(test-equal (term (good (graph (node a) (node b) (edge b a)))) #t)
(test-equal (term (good (graph (node a) (node b) (edge b c)))) #f)
(test-equal (term (good ,g2)) #f)
(test-equal (term (good ,g1)) #t)
