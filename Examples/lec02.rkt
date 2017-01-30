#lang racket
(require redex)

;; Simple language of boolean expressions with disjunction

(define-language 
  bool-or
  (e ::= 
     t
     f
     (e or e))
  (C ::=             ;; general contexts C
     hole
     (C or e)
     (e or C)))

#;(define-language   ;; alternative definition, using E
  bool-or
  (e ::= 
     t
     f
     (e or e))
  (E ::=             ;; evaluation contexts E for left-to-right eval order
     hole
     (E or e)))


(define e1 (term t))
(define e2 (term (t or f)))
(define e3 (term (,e2 or f)))  ; note use of unquote
(define e4 (term ((t or f) or (f or f))))

(define C1 (term hole))
(define C2 (term (hole or f)))

(redex-match bool-or e (term (t or (f or t))))
(redex-match bool-or (e_1 or e_2) (term ((f or t) or (t or f))))

(redex-match bool-or C C2)
(redex-match bool-or (in-hole C e) (term (f or t)))

(define bool-red
  (reduction-relation
   bool-or
   (--> (in-hole C (f or e))
        (in-hole C e)
        or-false)
   (--> (in-hole C (t or e))
        (in-hole C t)
        or-true)))

#;(define bool-red     ;; alternative definition, using E
  (reduction-relation
   bool-or
   (--> (in-hole E (f or e))
        (in-hole E e)
        or-false)
   (--> (in-hole E (t or e))
        (in-hole E t)
        or-true)))

(traces bool-red e4)
; (traces bool-red (term ((f or t) or (f or (t or t)))))
; (traces bool-red (term (((f or f) or (t or t)) or (f or t))))