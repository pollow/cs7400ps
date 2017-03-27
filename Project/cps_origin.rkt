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
   (λ [α] (k (∀ [α] (tt σ) -> α)) (k [α] x))
   #;(where σ (getType x s.G))]
  [(cps (λ (s.x s.t) s.e) ((s.x_1 s.t_1) ...))
   (λ [α] (k (∀ [α] (tt (s.t -> σ)) -> α))
     (k [α] (λ [β] (s.x (tt s.t))
              (λ [γ] (g (∀ [β] (tt σ) -> β)) ((cps s.e ((s.x s.t) (s.x_1 s.t_1) ...)) [β] g)))))
   #;(where σ (getReturnType (getType (λ (s.x s.t) s.e) ((s.x_1 s.t_1) ...))))]
  [(cps (s.e_1 s.e_2) s.G)
   (λ [α] (k (∀ [α] (tt t) -> α))
     ((cps s.e_1 s.G) [α]
                  (λ [α] (f (tt δ))
                    ((cps s.e_2 s.G) [α] (λ [α] (x (tt σ))
                                       ((f [α] x) [α] k))))))
   #;(where σ (getType s.e_2 s.G))
   #;(where δ (getType s.e_1 s.G))
   ;; δ = σ -> t
   #;(where t (getReturnType δ))]
  [(cps (if s.e_1 then s.e_2 else s.e_3) s.G)
   (λ [α] (k (∀ [α] (tt σ) -> α))
     ((cps s.e_1 s.G) [α]
                  (λ [α] (x bool)
                    (if x then ((cps s.e_2 s.G) [α] k) else ((cps s.e_3 s.G) [α] k)))))
   #;(side-condition (judgment-holds (typed () e bool)))
   #;(where e s.e_1)
   #;(side-condition (test-equal (term (getType s.e_2 s.G)) (term (getType s.e_3 s.G))))
   #;(where σ (getType s.e_2 s.G))])

#;(define-metafunction STLC-typ
  getType : e G -> t
  [(getType true G) bool]
  [(getType false G) bool]
  [(getType x ((x_1 t_1) ... (x t) (x_2 t_2) ...)) t]
  [(getType (λ (x t) e) ((x_1 t_1) ...))
   (t -> (getType e ((x t) (x_1 t_1) ...)))]
  [(getType (e_1 e_2) G) (getReturnType (getType e_1 G))]
  [(getType (if e_1 then e_2 else e_3) G) (getType e_2 G)])

#;(define-metafunction STLC-typ
  getReturnType : t -> t
  [(getReturnType (t_1 -> t_2)) t_2])

(term (cps ((λ (x bool) (λ (y bool) x)) true) ()))
#;(term (getReturnType (getType (λ (x bool) x) ())))
#;(term (cps (λ (x bool) x) ()))
#;(term (tt (bool -> σ)))
#;(first (judgment-holds (typed () (λ (x bool) x) t) t))
#;(term (tt bool))