#lang racket

(require redex "stlc-redex.rkt" "f-redex.rkt")

(define-union-language ST (s. STLC-typ) (t. F-typ))

(define-metafunction ST
  tt : any -> any
  [(tt bool) bool]
  [(tt (s.t_1 -> s.t_2)) (∀ [α] (tt s.t_1) -> (∀ [α] (∀ [α] (tt s.t_2) -> α) -> α))]
  [(tt (s.t_1 -> any)) (∀ [α] (tt s.t_1) -> (∀ [α] (∀ [α] any -> α) -> α))]
  [(tt (any -> s.t_2)) (∀ [α] any -> (∀ [α] (∀ [α] (tt s.t_2) -> α) -> α))]
  [(tt any) any])

(define-metafunction ST
  cps : s.e s.G -> t.e
  [(cps true s.G) (λ [α] (k (∀ [α] (tt bool) -> α)) (k [α] true))]
  [(cps false s.G) (λ [α] (k (∀ [α] (tt bool) -> α)) (k [α] false))]
  [(cps s.x ((s.x_1 s.t_1) ... (s.x s.t) (s.x_2 s.t_2) ...))
   (λ [α] (k (∀ [α] (tt s.t) -> α)) (k [α] x))
   (judgment-holds (typed ((s.x_1 s.t_1) ... (s.x s.t) (s.x_2 s.t_2) ...) s.x s.t))]
  [(cps (λ (s.x s.t) s.e) ((s.x_1 s.t_1) ...))
   (λ [α] (k (∀ [α] (tt (s.t -> s.t_2)) -> α))
     (k [β] (λ [β] (s.x_new (tt s.t))
              (λ [γ] (g (∀ [β] (tt s.t_2) -> β)) ((cps (subst s.x s.x_new s.e) ((s.x_new s.t) (s.x_1 s.t_1) ...)) [β] g)))))
   (judgment-holds (typed ((s.x_new s.t) (s.x_1 s.t_1) ...) (subst s.x s.x_new s.e) s.t_2))
   (where s.x_new ,(variable-not-in (term (s.e s.x_1 ...)) (term s.x)))]
  [(cps (s.e_1 s.e_2) ((s.x_1 s.t_1) ...))
   (λ [α] (k (∀ [α] (tt s.t_3) -> α))
     ((cps s.e_1 ((s.x_1 s.t_1) ...)) [α]
                  (λ [α] (f (tt (s.t_2 -> s.t_3)))
                    ((cps s.e_2 ((s.x_1 s.t_1) ...)) [α] (λ [α] (x (tt s.t_2)) ((f [α] x) [α] k))))))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_1 (s.t_2 -> s.t_3)))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_2 s.t_2))]
  [(cps (if s.e_1 then s.e_2 else s.e_3) ((s.x_1 s.t_1) ...))
   (λ [α] (k (∀ [α] (tt s.t_2) -> α))
     ((cps s.e_1 ((s.x_1 s.t_1) ...)) [α]
                  (λ [α] (x bool) (if x then ((cps s.e_2 ((s.x_1 s.t_1) ...)) [α] k) else ((cps s.e_3 ((s.x_1 s.t_1) ...)) [α] k)))))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_1 bool))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_2 s.t_2))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_3 s.t_2))])

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