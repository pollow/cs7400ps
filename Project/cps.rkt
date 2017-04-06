#lang racket

(require redex "stlc-redex.rkt" "f-redex.rkt")

(define-union-language ST (s. STLC-typ) (t. F-typ))

(define-metafunction ST
  tt : s.t -> t.t
  [(tt bool) bool]
  [(tt (s.t_1 -> s.t_2)) (∀ [α] (tt s.t_1) -> (((tt s.t_2) -> α) -> α))])

(define-metafunction ST
  cps : s.e s.G t.Δ -> t.e
  [(cps true s.G (t.α_0 ...))
   (λ [t.α_1] (k ((tt bool) -> t.α_1)) (k true))
   (where t.α_1 ,(variable-not-in (term (t.α_0 ...)) (term α)))]
  [(cps false s.G (t.α_0 ...))
   (λ [t.α_1] (k ((tt bool) -> t.α_1)) (k false))
   (where t.α_1 ,(variable-not-in (term (t.α_0 ...)) (term α)))]
  [(cps s.x ((s.x_1 s.t_1) ... (s.x s.t) (s.x_2 s.t_2) ...) (t.α_0 ...))
   (λ [t.α_1] (k ((tt s.t) -> t.α_1)) (k x))
   (where t.α_1 ,(variable-not-in (term (t.α_0 ...)) (term α)))
   (judgment-holds (typed ((s.x_1 s.t_1) ... (s.x s.t) (s.x_2 s.t_2) ...) s.x s.t))]
  [(cps (λ (s.x s.t) s.e) ((s.x_1 s.t_1) ...) (t.α_0 ...))
   (λ [t.α_1] (t.x_k ((tt (s.t -> s.t_2)) -> t.α_1))
       (t.x_k (λ [t.α_2] (s.x_new (tt s.t))
              (λ (t.x_k1 ((tt s.t_2) -> t.α_2))
                (t.e_1 [t.α_2] t.x_k1)))))
   (judgment-holds (typed ((s.x_new s.t) (s.x_1 s.t_1) ...) (subst s.x s.x_new s.e) s.t_2))
   (where t.α_1 ,(variable-not-in (term (t.α_0 ...)) (term α)))
   (where t.α_2 ,(variable-not-in (term (t.α_1 t.α_0 ...)) (term α)))
   (where t.e_1 (cps (subst s.x s.x_new s.e) ((s.x_new s.t) (s.x_1 s.t_1) ...) (t.α_2 t.α_1 t.α_0 ...)))
   (where t.x_k ,(variable-not-in (term (s.e s.x_1 ...)) (term k)))
   (where t.x_k1 ,(variable-not-in (term (k s.e s.x_1 ...)) (term k)))
   (where s.x_new ,(variable-not-in (term (k k_1 s.e s.x_1 ...)) (term s.x)))]
  [(cps (s.e_1 s.e_2) ((s.x_1 s.t_1) ...) (t.α_0 ...))
   (λ [t.α_1] (t.x_k ((tt s.t_3) -> t.α_1))
       (t.e_1 [t.α_1] (λ (t.x_1 (tt (s.t_2 -> s.t_3)))
                       (t.e_2 [t.α_1] (λ (t.x_2 (tt s.t_2)) ((t.x_1 [t.α_1] t.x_2) [t.α_1] t.x_k))))))
   (where t.α_1 ,(variable-not-in (term (t.α_0 ...)) (term α)))
   (where t.x_k ,(variable-not-in (term (t.e_1 t.e_2)) (term t.x_k)))
   (where t.x_1 ,(variable-not-in (term (t.e_1 t.e_2)) (term t.x_1)))
   (where t.x_2 ,(variable-not-in (term (t.e_1 t.e_2)) (term t.x_2)))
   (where t.e_1 (cps s.e_1 ((s.x_1 s.t_1) ...) (t.α_1 t.α_0 ...)))
   (where t.e_2 (cps s.e_2 ((s.x_1 s.t_1) ...) (t.α_1 t.α_0 ...)))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_1 (s.t_2 -> s.t_3)))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_2 s.t_2))]
  [(cps (if s.e_1 then s.e_2 else s.e_3) ((s.x_1 s.t_1) ...) (t.α_0 ...))
   (λ [t.α_1] (k ((tt s.t_2) -> t.α_1))
     (t.e_v [t.α_1]
      (λ (t.x_1 bool) (if t.x_1 then (t.e_v1 [t.α_1] k)
                            else (t.e_v2 [t.α_1] k)))))
   (where t.α_1 ,(variable-not-in (term (t.α_0 ...)) (term α)))
   (where t.x_1 ,(variable-not-in (term (s.e_1 s.e_2 s.e_3 (s.x_1 s.t_1) ...)) (term x)))
   (where t.e_v (cps s.e_1 ((s.x_1 s.t_1) ...) (t.α_1 t.α_0 ...)))
   (where t.e_v1 (cps s.e_2 ((s.x_1 s.t_1) ...) (t.α_1 t.α_0 ...)))
   (where t.e_v2 (cps s.e_3 ((s.x_1 s.t_1) ...) (t.α_1 t.α_0 ...)))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_1 bool))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_2 s.t_2))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_3 s.t_2))])

(term (cps true () ()))
(term (cps false () ()))
(term (cps x ((x bool)) ()))
(term (cps (λ (x bool) x) () ()))
(term (cps ((λ (x bool) x) true) () ()))
(term (cps (λ (x (bool -> bool)) (x true)) () ()))
(term (cps (if true then false else true) () ()))
(term (cps (λ (x bool) (if x then false else true)) () ()))

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
