#lang racket

(require redex "stlc-redex.rkt" "f-redex.rkt")

(define-union-language ST (s. STLC-typ) (t. F-typ))

(define-metafunction ST
  tt : s.t -> t.t
  [(tt bool) bool]
  [(tt int) int]
  [(tt (s.t_1 -> s.t_2)) (∀ [α] (tt s.t_1) -> (((tt s.t_2) -> α) -> α))])

(define-metafunction ST
  cps : s.e s.G t.Δ t.κ -> t.e
  [(cps true ((s.x_1 s.t_1) ...) (t.α_1 ...) (t.x_1 ...))
   (λ [t.α_2] (t.x_k ((tt bool) -> t.α_2)) (t.x_k true))
   (where t.x_k ,(variable-not-in (term (s.x_1 ... t.x_1 ...)) (term k)))
   (where t.α_2 ,(variable-not-in (term (t.α_1 ...)) (term α)))]
  [(cps false ((s.x_1 s.t_1) ...) (t.α_1 ...) (t.x_1 ...))
   (λ [t.α_2] (t.x_k ((tt bool) -> t.α_2)) (t.x_k false))
   (where t.x_k ,(variable-not-in (term (s.x_1 ... t.x_1 ...)) (term k)))
   (where t.α_2 ,(variable-not-in (term (t.α_1 ...)) (term α)))]
  [(cps integer ((s.x_1 s.t_1) ...) (t.α_1 ...) (t.x_1 ...))
   (λ [t.α_2] (t.x_k ((tt int) -> t.α_2)) (t.x_k integer))
   (where t.x_k ,(variable-not-in (term (s.x_1 ... t.x_1 ...)) (term k)))
   (where t.α_2 ,(variable-not-in (term (t.α_1 ...)) (term α)))]
  [(cps s.x ((s.x_1 s.t_1) ... (s.x s.t) (s.x_2 s.t_2) ...) (t.α_1 ...) (t.x_1 ...))
   (λ [t.α_2] (t.x_k ((tt s.t) -> t.α_2)) (t.x_k s.x))
   (where t.x_k ,(variable-not-in (term (s.x s.x_1 ... t.x_1 ...)) (term k)))
   (where t.α_2 ,(variable-not-in (term (t.α_1 ...)) (term α)))
   (judgment-holds (typed ((s.x_1 s.t_1) ... (s.x s.t) (s.x_2 s.t_2) ...) s.x s.t))]
  [(cps (λ (s.x s.t) s.e) ((s.x_1 s.t_1) ...) (t.α_3 ...) (t.x_1 ...))
   (λ [t.α_1] (t.x_k ((tt (s.t -> s.t_2)) -> t.α_1))
       (t.x_k (λ [t.α_2] (s.x_new (tt s.t))
              (λ (t.x_k1 ((tt s.t_2) -> t.α_2))
                ((cps (subst s.x s.x_new s.e) ((s.x_new s.t) (s.x_1 s.t_1) ...) (t.α_1 t.α_2 t.α_3 ...) (t.x_k t.x_k1 t.x_1 ...)) [t.α_2] t.x_k1)))))
   (judgment-holds (typed ((s.x_new s.t) (s.x_1 s.t_1) ...) (subst s.x s.x_new s.e) s.t_2))
   (where t.α_1 ,(variable-not-in (term (s.e s.x_1 ... t.α_3 ...)) (term α)))
   (where t.α_2 ,(variable-not-in (term (t.α_1 s.e s.x_1 ... t.α_3 ...)) (term α)))
   #;(where t.e_1 (cps (subst s.x s.x_new s.e) ((s.x_new s.t) (s.x_1 s.t_1) ...) (t.α_1 t.α_2 t.α_3 ...) (t.x_k t.x_k1 t.x_1 ...)))
   (where t.x_k ,(variable-not-in (term (s.e s.x_1 ... t.x_1 ...)) (term k)))
   (where t.x_k1 ,(variable-not-in (term (t.x_k s.e s.x_1 ... t.x_1 ...)) (term k)))
   (where s.x_new ,(variable-not-in (term (t.x_k t.x_k1 s.e s.x_1 ... t.x_1 ...)) (term s.x)))]
  [(cps (s.e_1 s.e_2) ((s.x_1 s.t_1) ...) (t.α_2 ...) (t.x_3 ...))
   (λ [t.α_1] (t.x_k ((tt s.t_3) -> t.α_1))
       (t.e_1 [t.α_1] (λ (t.x_1 (tt (s.t_2 -> s.t_3)))
                       (t.e_2 [t.α_1] (λ (t.x_2 (tt s.t_2)) ((t.x_1 [t.α_1] t.x_2) [t.α_1] t.x_k))))))
   (where t.α_1 ,(variable-not-in (term (s.e_1 s.e_2 (s.x_1 s.t_1) ... t.α_2 ...)) (term α)))
   (where t.x_k ,(variable-not-in (term ((t.e_1 t.e_2) s.x_1 ... t.x_3 ...)) (term k)))
   (where t.x_1 ,(variable-not-in (term ((t.e_1 t.e_2) s.x_1 ... t.x_3 ...)) (term x)))
   (where t.x_2 ,(variable-not-in (term ((t.e_1 t.e_2) t.x_1 s.x_1 ... t.x_3 ...)) (term x)))
   (where t.e_1 (cps s.e_1 ((s.x_1 s.t_1) ...) (t.α_1 t.α_2 ...) (t.x_k t.x_1 t.x_2 t.x_3 ...)))
   (where t.e_2 (cps s.e_2 ((s.x_1 s.t_1) ...) (t.α_1 t.α_2 ...) (t.x_k t.x_1 t.x_2 t.x_3 ...)))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_1 (s.t_2 -> s.t_3)))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_2 s.t_2))]
  [(cps (if s.e_1 then s.e_2 else s.e_3) ((s.x_1 s.t_1) ...) (t.α_2 ...) (t.x_2 ...))
   (λ [t.α_1] (t.x_k ((tt s.t_2) -> t.α_1))
     (t.e_v [t.α_1]
      (λ (t.x_1 bool) (if t.x_1 then (t.e_v1 [t.α_1] t.x_k)
                            else (t.e_v2 [t.α_1] t.x_k)))))
   (where t.x_k ,(variable-not-in (term (s.e_1 s.e_2 s.e_3 (s.x_1 s.t_1) ... t.x_2 ...)) (term k)))
   (where t.α_1 ,(variable-not-in (term (s.e_1 s.e_2 s.e_3 (s.x_1 s.t_1) ... t.α_2 ...)) (term α)))
   (where t.x_1 ,(variable-not-in (term (s.e_1 s.e_2 s.e_3 (s.x_1 s.t_1) ... t.x_2 ...)) (term x)))
   (where t.e_v (cps s.e_1 ((s.x_1 s.t_1) ...) (t.α_1 t.α_2 ...) (t.x_k t.x_1 t.x_2 ...)))
   (where t.e_v1 (cps s.e_2 ((s.x_1 s.t_1) ...) (t.α_1 t.α_2 ...) (t.x_k t.x_1 t.x_2 ...)))
   (where t.e_v2 (cps s.e_3 ((s.x_1 s.t_1) ...) (t.α_1 t.α_2 ...) (t.x_k t.x_1 t.x_2 ...)))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_1 bool))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_2 s.t_2))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_3 s.t_2))]
  [(cps (s.e_1 \; s.e_2) ((s.x_1 s.t_1) ...) (t.α_2 ...) (t.x_2 ...))
   (λ [t.α_1] (t.x_k ((tt s.t_3) -> t.α_1))
       (t.e_1 [t.α_1] (λ (t.x_1 (tt s.t_2))
                       (t.e_2 [t.α_1] t.x_k))))
   #;(λ [t.α_1] (t.x_k ((tt s.t_3) -> t.α_1))
       (λ (t.x_1 (tt s.t_2))
                       (t.e_2 [t.α_1] t.x_k)))
   (where t.α_1 ,(variable-not-in (term (s.e_1 s.e_2 (s.x_1 s.t_1) ... t.α_2 ...)) (term α)))
   (where t.x_k ,(variable-not-in (term (t.e_1 s.x_1 ... t.x_2 ...)) (term k)))
   (where t.x_1 ,(variable-not-in (term (t.x_k t.e_2 s.x_1 ... t.x_2 ...)) (term x)))
   (where t.e_1 (cps s.e_1 ((s.x_1 s.t_1) ...) (t.α_1 t.α_2 ...) (t.x_k t.x_1 t.x_2 ...)))
   (where t.e_2 (cps s.e_2 ((s.x_1 s.t_1) ...) (t.α_1 t.α_2 ...) (t.x_k t.x_1 t.x_2 ...)))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_1 s.t_2))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_2 s.t_3))])

#;(redex-match STLC
               e
               (term (λ (f (int -> int)) (λ (g (int -> int)) ((f 0) \; ((g 0) \; 0))))))

#;(judgment-holds (typed ((f (int -> int)) (g (int -> int))) ((f 0) \; ((g 0) \; 0)) t) t)

#;(term (cps (x \; x) ((x bool))))
#;(term (cps (λ (f (int -> int)) (f 0)) ()))
#;(term (cps ((f 0) \; (g 0)) ((f (int -> int)) (g (int -> int)))))

(stepper red (term (cps (λ (f (int -> int)) (λ (g (int -> int)) ((f 0) \; ((g 0) \; 0)))) () () ())))
#;(stepper red (term (cps (λ (f (int -> int)) (λ (g (int -> int)) ((g 0) \; ((f 0) \; 0)))) () () ())))
#;(stepper red (term (cps (λ (f (int -> int)) (λ (g (int -> int)) (((f 0) \; (g 0)) \; 0))) () () ())))
#;(judgment-holds (typed () (λ (f (int -> int)) (λ (g (int -> int)) ((f 0) \; ((g 0) \; 0)))) t) t)
#;(term (cps f1 ((g1 (int -> int)) (f1 (int -> int)))))


#;(λ (α)
   (k ((∀ (α)
          (∀ (α) int -> ((int -> α) -> α)) ->
          (((∀ (α) (∀ (α) int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> α) -> α)) -> α))
   (k
    (λ (α1)
      (f1 (∀ (α) int -> ((int -> α) -> α)))
      (λ (k1 ((∀ (α) (∀ (α) int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> α1))
        (k1
            (λ (α3)
              (g1 (∀ (α) int -> ((int -> α) -> α)))
              (λ (k3 (int -> α3))
                ((f1 (α3) 0) (α3) (λ (x int) ((g1 (α3) 0) (α3) (λ (x1 int) (k3 0))))))))))))
#;(λ [β] (k (int -> β)) [] [β] (λ (h (∀ (α)
          (∀ (α) int -> ((int -> α) -> α)) ->
          (((∀ (α) (∀ (α) int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> α) -> α)))
                                (((h f1)
                                   [β] (λ (h ((∀ (α) (∀ (α) int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> β))
                                         (h g1))) [β] k)))

#;(λ [β] (k (int -> β)) [] [β] (λ (h (∀ (α)
          (∀ (α) int -> ((int -> α) -> α)) ->
          (((∀ (α) (∀ (α) int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> α) -> α)))
                                 (((h (λ [γ] (x int) (λ (k1 (int -> γ)) k 1)))
                                   [β] (λ (h ((∀ (α) (∀ (α) int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> β))
                                         (h (λ [γ] (x int) (λ (k2 (int -> γ)) k 2))))) [β] k)))


#;(λ (k (int -> α)) [] (λ (h ((int -> ((int -> α) -> α)) -> ((((int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> α) -> α)))
                                 (((h (λ (x int) (λ (k1 (int -> α)) k 1)))
                                   (λ (h (((int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> α))
                                         (h (λ (x int) (λ (k2 (int -> α)) k 2))))) k)))

#;(λ (α)
  (k ((∀ (α) (∀ (α) int -> ((int -> α) -> α)) -> (((∀ (α) (∀ (α) int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> α) -> α)) -> α))
  (k
   (λ (α1)
     (f1 (∀ (α) int -> ((int -> α) -> α)))
     (λ (k1 ((∀ (α) (∀ (α) int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> α1))
       (k1
        (λ (α3)
          (g1 (∀ (α) int -> ((int -> α) -> α)))
          (λ (k3 (int -> α8))
            ((g1 (α3) 0) (α3) (λ (x int) ((f1 (α3) 0) (α3) (λ (x1 int) (k3 0))))))))))))

#;(λ (k (((int -> ((int -> α) -> α))
        -> ((((int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> α) -> α)) -> α))
  (k
   (λ (f1 (int -> ((int -> α) -> α)))
     (λ (k1 (((int -> ((int -> α) -> α)) -> ((int -> α) -> α)) -> α))
       (k1
        (λ (g1 (int -> ((int -> α) -> α)))
          (λ (k3 (int -> α))
            ((g1 0) (λ (x int) ((f1 0) (λ (x1 int) (k3 0))))))))))))


#;(term (cps true ()))
#;(term (cps false ()))
#;(term (cps x ((x bool))))
#;(term (cps (λ (x bool) x) ()))
#;(term (cps ((λ (x bool) x) true) ()))
#;(term (cps (λ (x (bool -> bool)) (x true)) ()))
#;(term (cps (if true then false else true) ()))
#;(term (cps (λ (x bool) (if x then false else true)) ()))

#;(term (cps ((λ (x bool) (λ (y bool) x)) true) ()))

#;(term (Fevaluate (cps ((λ (x bool) (λ (y bool) x)) true) ())))
#;(term (Fevaluate (cps (λ (x bool) x) ())))
#;(term (cps (λ (x bool) x) ()))
#;(term (cps x ((x (bool -> bool)))))
#;(judgment-holds (typed () (λ (f (bool -> bool)) (λ (x bool) (f x))) (t -> t)) t)
#;(redex-let ST ([s.t (term (judgment-holds (typed () (λ (f (bool -> bool)) (λ (x bool) (f x))) t) t))]) (term (λ [α] (k (∀ [α] (tt s.t) -> α)) (k [α] x))))
#;(redex-let STLC-typ ([t_1 (term bool)]) (term (λ [α] (k (∀ [α] (tt t_1) -> α)) (k [α] x))))
#;(redex-match F
               t
               (term (∀ (α) (∀ (α) bool -> (∀ (α) (∀ (α) σ -> α) -> α)) -> α)))
#;(test-equal (judgment-holds (Ftyped () ((k (∀ (α) (∀ (α) bool -> (∀ (α) (∀ (α) σ -> α) -> α)) -> α)))
                                    (k (α) (λ (β) (x bool) (λ (γ) (g (∀ (β) σ -> β)) ((λ (α) (h (∀ (α) σ -> α)) (h (α) x)) (β) g)))) t) t) '((∀ (α) bool -> bool)))

#;(test-equal (judgment-holds (Ftyped () ((g (∀ (β) σ -> β)) (x σ))
                                    ((λ (α) (h (∀ (α) σ -> α)) (h (α) x)) (β) g) t) t) '((∀ (α) bool -> bool)))

#;(test-equal (judgment-holds (Ftyped () ((g (∀ (β) σ -> β)))
                                    ((λ (α) (h (∀ (α) σ -> α)) (h (α) x)) (β) g) t) t) '((∀ (α) bool -> bool)))
