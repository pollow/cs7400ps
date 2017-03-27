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
  [(cps s.x s.G)
   (λ [α] (k (∀ [α] (tt σ) -> α)) (k [α] x))]
  [(cps (λ (s.x s.t) s.e) ((s.x_1 s.t_1) ...))
   (λ [α] (k (∀ [α] (tt (s.t -> σ)) -> α))
     (k [α] (λ [β] (s.x (tt s.t))
              (λ [γ] (g (∀ [β] (tt σ) -> β)) ((cps s.e ((s.x s.t) (s.x_1 s.t_1) ...)) [β] g)))))]
  [(cps (s.e_1 s.e_2) s.G)
   (λ [α] (k (∀ [α] (tt t) -> α))
     ((cps s.e_1 s.G) [α]
                  (λ [α] (f (tt δ))
                    ((cps s.e_2 s.G) [α] (λ [α] (x (tt σ))
                                       ((f [α] x) [α] k))))))]
  [(cps (if s.e_1 then s.e_2 else s.e_3) s.G)
   (λ [α] (k (∀ [α] (tt σ) -> α))
     ((cps s.e_1 s.G) [α]
                  (λ [α] (x bool)
                    (if x then ((cps s.e_2 s.G) [α] k) else ((cps s.e_3 s.G) [α] k)))))])

#;(term (cps ((λ (x bool) (λ (y bool) x)) true) ()))
(term (cps (λ (x bool) x) ()))
(redex-match F
               t
               (term (∀ (α) (∀ (α) bool -> (∀ (α) (∀ (α) σ -> α) -> α)) -> α)))
(test-equal (judgment-holds (Ftyped () ((k (∀ (α) (∀ (α) bool -> (∀ (α) (∀ (α) σ -> α) -> α)) -> α)))
                                    (k (α) (λ (β) (x bool) (λ (γ) (g (∀ (β) σ -> β)) ((λ (α) (h (∀ (α) σ -> α)) (h (α) x)) (β) g)))) t) t) '((∀ (α) bool -> bool)))

(test-equal (judgment-holds (Ftyped () ((g (∀ (β) σ -> β)) (x σ))
                                    ((λ (α) (h (∀ (α) σ -> α)) (h (α) x)) (β) g) t) t) '((∀ (α) bool -> bool)))

(test-equal (judgment-holds (Ftyped () ((g (∀ (β) σ -> β)))
                                    ((λ (α) (h (∀ (α) σ -> α)) (h (α) x)) (β) g) t) t) '((∀ (α) bool -> bool)))