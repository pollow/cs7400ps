#lang racket
(require redex)

;; Language Definition for Lam
(define-language Lam
  [e ::=
     x
     (λ (x) e)
     (e e)]
  [x ::=
     variable-not-otherwise-mentioned])

;; Language Definition for LamBool
(define-language LamBool
  [e ::=
     x
     (e e)
     (λ (x) e)
     (if e then e else e)
     true
     false]
  [x ::=
     variable-not-otherwise-mentioned])


;                                                                                   
;                                                                                   
;                                                             ;                     
;   ;;;;;;                  ;                                 ;                     
;   ;    ;;                 ;                      ;                                
;   ;     ;                 ;                      ;                                
;   ;     ;   ;;;;      ;;; ;  ;     ;    ;;;    ;;;;;;     ;;;      ;;;    ; ;;;;  
;   ;    ;;   ;   ;    ;   ;;  ;     ;   ;   ;     ;          ;     ;   ;   ;;   ;; 
;   ;;;;;    ;    ;;  ;     ;  ;     ;  ;          ;          ;    ;     ;  ;     ; 
;   ;    ;   ;;;;;;;  ;     ;  ;     ;  ;          ;          ;    ;     ;  ;     ; 
;   ;     ;  ;        ;     ;  ;     ;  ;          ;          ;    ;     ;  ;     ; 
;   ;     ;  ;        ;     ;  ;     ;  ;          ;          ;    ;     ;  ;     ; 
;   ;     ;   ;        ;   ;;  ;;   ;;   ;   ;     ;          ;     ;   ;   ;     ; 
;   ;      ;   ;;;;     ;;; ;   ;;;; ;    ;;;       ;;;    ;;;;;;;   ;;;    ;     ; 
;                                                                                   
;                                                                                   
;                                                                                   
;                                                                                   

;; ------------------------------------------------------------------
;; REDUCTION : Call by Value For Lam
(define-extended-language Lam-cbv Lam
  (v x (λ (x ...) e))
  (E hole
     (v ... E e ...)))

(define ->v
  (reduction-relation
   Lam-cbv
   #:domain e
   ;; case for only one value to apply
   (--> (in-hole E ((λ (x) e_body) v))
        (in-hole E (subst-n (x v) e_body))
        subst0)))

;; ------------------------------------------------------------------
;; TESTS
(module+ test
  (test-equal
   (apply-reduction-relation* ->v (term ((λ (x) w) z)))
   (list (term w)))
  
  (test-equal 
   (apply-reduction-relation* ->v (term (((λ (x) (λ (y) x)) w) z)))
   (list (term w)))
  
  (define example (term (((λ (x) (λ (y) (x y))) (λ (z) y)) w)))

  (test-equal
   (apply-reduction-relation* ->v example)
   (list (term y)))

  
  (define omega (term ((λ (x) (x x)) (λ (x) (x x)))))
  ;(apply-reduction-relation* ->v example)
  ;(traces ->v omega)
 
  ;(define strange (term ((λ (x) x) a b)))
  ;(apply-reduction-relation* ->v strange)
)

;; ------------------------------------------------------------------
;; REDUCTION : Call by Value For LamBool

(define-extended-language LamBool-cbv LamBool
  (v x (λ (x ...) e) true false)
  (E hole
     (v ... E e ...)
     (if E then e else e)))

(define =>v
  (reduction-relation
   LamBool-cbv
   #:domain e
   (--> (in-hole E ((λ (x) e_body) v))
        (in-hole E (subst-n (x v) e_body))
        substB0)
   (--> (if true then e_1 else e_2)
        e_1
        if-true)
   (--> (if false then e_1 else e_2)
        e_2
        if-false)))

;; ------------------------------------------------------------------
;; TESTS

(module+ test
  (test-equal 
   (apply-reduction-relation* =>v (term ((λ (x) w) z)))
   (list (term w)))
  
  (test-equal 
   (apply-reduction-relation* =>v (term (((λ (x) (λ (y) x)) w) z)))
   (list (term w)))
  
  (define example_1 (term (((λ (x) (λ (y) (x y))) (λ (z) y)) w)))

  (test-equal
   (apply-reduction-relation* =>v example_1)
   (term (y)))
  
  (define omega_1 (term ((λ (x) (x x)) (λ (x) (x x)))))
  ;(apply-reduction-relation* ->v example)
  ;(traces ->v omega)
 
  ;(define strange_1 (term ((λ (x) x) a b)))
  ;(apply-reduction-relation* =>v strange_1)

  (test-equal 
   (apply-reduction-relation* =>v
                              (term (if (((λ (x) (λ (y) x)) true) x)
                                        then ((λ (x) t) z)
                                        else ((λ (x) f) z))))
   (list (term t)))

  (test-equal 
   (apply-reduction-relation* =>v (term (if true
                                            then ((λ (x) t) z)
                                            else ((λ (x) f) z))))
   (list (term t)))

  (test-equal 
   (apply-reduction-relation* =>v (term (if (((λ (x) (λ (y) x)) false) x)
                                            then ((λ (x) t) z)
                                            else ((λ (x) f) z))))
   (list (term f)))

  (test-equal 
   (apply-reduction-relation* =>v (term (if false
                                            then ((λ (x) t) z)
                                            else ((λ (x) f) z))))
   (list (term f)))
)



;                                      
;                                      
;                         ;            
;   ;     ;               ;     ;;;;   
;   ;     ;    ;                   ;   
;   ;     ;    ;                   ;   
;   ;     ;  ;;;;;;     ;;;        ;   
;   ;     ;    ;          ;        ;   
;   ;     ;    ;          ;        ;   
;   ;     ;    ;          ;        ;   
;   ;     ;    ;          ;        ;   
;   ;     ;    ;          ;        ;   
;   ;;   ;;    ;          ;        ;   
;    ;;;;;      ;;;    ;;;;;;;      ;;;
;                                      
;                                      
;                                      
;                                      


;; union language suffice to the definition of alpha equivalence
(define-union-language U LamBool Lam)

;; ------------------------------------------------------------------
;; EQUIVALENCE CLASS

(define (=alpha t1 t2)
  
  (define-extended-language Lam-sd U
    (e .... d)
    (d natural))
  
  ;; (sd e0) converts e to de Bruin (static distance) form
  (define-metafunction Lam-sd 
    sd : any -> any
    [(sd any_0) (sd/a any_0 ())])
  
  ;; (sd/a e (x ...)) converts e to static distance form 
  ;; in the context (x ...), the variables on the path 
  ;; from e0 to e 
    (define-metafunction Lam-sd 
      sd/a : any (x ...) -> any
      [(sd/a x (x_c ...)) 
       (distance x (x_c ...) 0)]
      [(sd/a (λ (x) any) (x_c ...)) 
       (λ (dummy) (sd/a any (x x_c ...)))]
      [(sd/a (any_left any_right ...) (x_c ...))
       ((sd/a any_left (x_c ...)) (sd/a any_right (x_c ...)) ...)]
      [(sd/a any (x_c ...)) 
       any])
  
  ;; (distance x env) -- at which position does x occur in env
  (define-metafunction Lam-sd 
    distance : x (x ...) natural -> e
    [(distance x () d) x]
    [(distance x (x x_c ...) d) d]
    [(distance x (x_c x_d ...) d) 
     (distance x (x_d ...) ,(+ (term d) 1))])
  
  ;; -- IN -- 
  (define sd1 (term (sd ,t1)))
  (define sd2 (term (sd ,t2)))
  (equal? sd1 sd2))
(module+ test
  (test-equal (=alpha (term (λ (x) x)) (term (λ (y) y))) #t)
  (test-equal (=alpha (term (y (λ (x) x))) (term (y (λ (y) y)))) #t))

;; ------------------------------------------------------------------
;; SUBSTITUTION

(define-metafunction U
  subst-n : (x any) ... any -> any
  [(subst-n (x_1 any_1) (x_2 any_2) ... any_3)
   (subst x_1 any_1 (subst-n (x_2 any_2) ... any_3))]
  [(subst-n any_3) 
   any_3])

;; (subst x e_1 e) replaces all occurrences of 
;; x in e with e_1 HYGIENICALLY 
(define-metafunction U
  subst : x any any -> any 
  ;; 1. x_1 bound, so don't continue in Î» body
  [(subst x_1 any_1 (λ (x_2 ... x_1 x_3 ...) any_2))
   (λ (x_2 ... x_1 x_3 ...) any_2)]
  ;; 2. general purpose capture avoiding case
  [(subst x_1 any_1 (λ (x_2 ...) any_2))
   (λ (x ...) (subst x_1 any_1 (subst-vars* (x_2 x) ... any_2)))
   (where (x ...) ,(variables-not-in (term (x_1 any_1 any_2))
                                     (term (x_2 ...))))]
  ;; 3. replace x_1 with e_1
  [(subst x_1 any_1 x_1) any_1]
  ;; 4. x_1 and x_2 are different, so don't replace
  [(subst x_1 any_1 x_2) x_2]
  ;; the last two cases cover all other expression forms
  [(subst x_1 any_1 (any_2 ...))
   ((subst x_1 any_1 any_2) ...)]
  [(subst x_1 any_1 any_2) any_2])

;; (subst-vars (x_1 e_1) ... e) replaces all occurrences of 
;; x_1, ... in e with e_1, ... UNCONDITIONALLY 
(define-metafunction U
  subst-vars* : (x any) ... any -> any 
  [(subst-vars* any) 
   any]
  [(subst-vars* (x_1 any_1) (x_2 any_2) ... any) 
   (subst-vars x_1 any_1 (subst-vars* (x_2 any_2) ... any))])

;; (subst-vars x e_1 e) replaces all occurrences of 
;; x in e with e_1 UNCONDITIONALLY 
(define-metafunction U
  subst-vars : x any any -> any 
  [(subst-vars x_1 any_1 x_1) any_1]
  [(subst-vars x_1 any_1 (any_2 ...)) ((subst-vars x_1 any_1 any_2) ...)]
  [(subst-vars x_1 any_1 any_2) any_2]
  [(subst-vars x_1 any_1 (x_2 any_2) ... any_3) 
   (subst-vars x_1 any_1 (subst-vars ((x_2 any_2) ... any_3)))])

;; ------------------------------------------------------------------
;; TESTS

(module+ test
  (test-equal (term (subst x y x)) (term y))
  
  (test-equal (term (subst x y z)) (term z))
  
  (test-equal (term (subst x y (x (y z)))) 
              (term (y (y z)))
              #:equiv =alpha)
  
  (test-equal (term (subst x y ((λ (x) x) ((λ (y1) y1) (λ (x) z)))))
              (term ((λ (z) z) ((λ (y2) y2) (λ (x) z))))
              #:equiv =alpha)  ;; note: test fails without =alpha
  
  (test-equal (term (subst x y (if0 (+ 1 x) x x)))
              (term (if0 (+ 1 y) y y))
              #:equiv =alpha)
  
  (test-equal (term (subst x (λ (z) y) (λ (y) x)))
              (term (λ (y1) (λ (z) y)))
              #:equiv =alpha)
  
  (test-equal (term (subst x 1 (λ (y) x)))
              (term (λ (y) 1))
              #:equiv =alpha)
  
  (test-equal (term (subst x y (λ (y) x)))
              (term (λ (y2) y))
              #:equiv =alpha)

  (test-equal (term (subst x (λ (y) y) (λ (z) (z2 z))))
              (term (λ (z1) (z2 z1)))
              #:equiv =alpha)
  
  (test-equal (term (subst x (λ (z) z) (λ (z) (z1 z))))
              (term (λ (z2) (z1 z2)))
              #:equiv =alpha)
  
  (test-equal (term (subst x z (λ (z) (z1 z))))
              (term (λ (z2) (z1 z2)))
              #:equiv =alpha)
  
  (test-equal (term (subst x3 5 (λ (x2) x2)))
              (term (λ (x1) x1))
              #:equiv =alpha)
  
  (test-equal (term (subst z * (λ (z x) 1)))
              (term (λ (z x) 1))
              #:equiv =alpha)
  
  (test-equal (term (subst q (λ (x) z) (λ (z x) q)))
              (term (λ (z1 x1) (λ (x) z)))
              #:equiv =alpha)
  
  (test-equal (term (subst x 1 (λ (x x) x)))
              (term (λ (x x) x))
              #:equiv =alpha)
  
  (test-results))

;                                               
;                                               
;                                               
;   ;;;;;;;                                     
;      ;                                        
;      ;                                        
;      ;       ; ;;;    ;;;;   ; ;;;;    ;;;;;  
;      ;       ;;   ;  ;    ;  ;;   ;;  ;     ; 
;      ;       ;            ;  ;     ;  ;       
;      ;       ;       ;;;;;;  ;     ;  ;;;;    
;      ;       ;      ;;    ;  ;     ;     ;;;; 
;      ;       ;      ;     ;  ;     ;        ; 
;      ;       ;      ;    ;;  ;     ;  ;     ; 
;      ;       ;       ;;;; ;  ;     ;   ;;;;;  
;                                               
;                                               
;                                               
;                                               


;; in the metafunction the language of input should
;; be distinguished from the language of output.
;; So that the metafunction will not confuse the grammar.
(define-union-language ST (s. LamBool) (t. Lam))

(define-metafunction ST
  translate : s.e -> t.e
  [(translate true) (λ (x) (λ (y) x))]
  [(translate false) (λ (x) (λ (y) y))]
  [(translate s.x) s.x]
  [(translate (λ (s.x) s.e)) (λ (s.x) (translate s.e))]
  [(translate (s.e_1 s.e_2)) ((translate s.e_1) (translate s.e_2))]
  ;; wrap the vlaue in a lambda function and apply
  ;; it to an 'id' function to evaluate the value lately
  [(translate (if s.e_1 then s.e_2 else s.e_3))
   (((((λ (b) (λ (m) (λ (n) ((b m) n) )))
    (translate s.e_1))
    (λ (s.x_1) (translate s.e_2)))
    (λ (s.x_2) (translate s.e_3))) (λ (x) x))
   (where s.x_1 ,(variable-not-in (term s.e_2) (term x)))
   (where s.x_2 ,(variable-not-in (term s.e_3) (term x)))])

(module+ test
  (test-equal (term (translate x)) (term x) #:equiv =alpha)
  (test-equal (term (translate true)) (term (λ (u) (λ (v) u))) #:equiv =alpha)
  (test-equal (term (translate false)) (term (λ (u) (λ (v) v))) #:equiv =alpha)
  (test-equal (term (translate false)) (term (λ (u) (λ (v) v))) #:equiv =alpha)
  (test-equal (term (translate (λ (x) (λ (y) z))))
              (term (λ (u) (λ (v) z))) #:equiv =alpha)
  (test-equal (term (translate (if true then (λ (x) (λ (y) z)) else false)))
              (term (((((λ (b) (λ (m) (λ (n) ((b m) n)))) (λ (x) (λ (y) x)))
                       (λ (x1) (λ (x) (λ (y) z))))
                      (λ (x) (λ (x) (λ (y) y))))
                     (λ (x) x))) #:equiv =alpha))

(define-metafunction LamBool
  CorrectnessConjecture : e -> boolean
  ;; weak divergency conjecture
  [(CorrectnessConjecture e)
   #t
   (side-condition
    (and (empty? (apply-reduction-relation* =>v
                                            (term e)))
         (empty? (apply-reduction-relation* ->v
                                            (term (translate e))))))]
  ;; strong divergency conjecture
  [(CorrectnessConjecture e)
   #t
   (side-condition
    (and (empty? (apply-reduction-relation*
                  ->v
                  (term (translate ,(car (apply-reduction-relation*
                                          =>v (term e)))))))
         (empty? (apply-reduction-relation* ->v
                                            (term (translate e))))))]
  ;; convergency conjecture
  [(CorrectnessConjecture e)
   ,(=alpha
     (car (apply-reduction-relation*
           ->v
           (term (translate ,(car (apply-reduction-relation* =>v (term e)))))))
     (car (apply-reduction-relation* ->v (term (translate e)))))])

(redex-check LamBool e (term (CorrectnessConjecture e)))
(term (CorrectnessConjecture ((λ (x) (x x)) (λ (x) (x x)))))