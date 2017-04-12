#lang racket

(require redex "stlc-redex.rkt" "f-redex.rkt")

(define-union-language ST (s. STLC-typ) (t. F-typ))

;; tt is a function which translate a given source type into target type
;; as descripted in the paper 
(define-metafunction ST
  tt : s.t -> t.t
  [(tt bool) bool]
  [(tt int) int]
  [(tt (s.t_1 -> s.t_2)) (∀ [α] (tt s.t_1) -> (((tt s.t_2) -> α) -> α))])

;;  cps is a function which translate a given typed source expression
;;  into typed target CPS expression 
;;  INPUT
;;  s.e : source expression
;;  s.G : source variable environment
;;  t.Δ : target type variable environment
;;  t.κ : target continuation variable (only for readability)
;;  OUTPUT
;;  t.e : target expression
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

  ;; a newly added rule to handle (e_1;e_2), which has not been introduced by the paper
  [(cps (s.e_1 \; s.e_2) ((s.x_1 s.t_1) ...) (t.α_2 ...) (t.x_2 ...))
   (λ [t.α_1] (t.x_k ((tt s.t_3) -> t.α_1))
       (t.e_1 [t.α_1] (λ (t.x_1 (tt s.t_2))
                       (t.e_2 [t.α_1] t.x_k))))
   (where t.α_1 ,(variable-not-in (term (s.e_1 s.e_2 (s.x_1 s.t_1) ... t.α_2 ...)) (term α)))
   (where t.x_k ,(variable-not-in (term (t.e_1 s.x_1 ... t.x_2 ...)) (term k)))
   (where t.x_1 ,(variable-not-in (term (t.x_k t.e_2 s.x_1 ... t.x_2 ...)) (term x)))
   (where t.e_1 (cps s.e_1 ((s.x_1 s.t_1) ...) (t.α_1 t.α_2 ...) (t.x_k t.x_1 t.x_2 ...)))
   (where t.e_2 (cps s.e_2 ((s.x_1 s.t_1) ...) (t.α_1 t.α_2 ...) (t.x_k t.x_1 t.x_2 ...)))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_1 s.t_2))
   (judgment-holds (typed ((s.x_1 s.t_1) ...) s.e_2 s.t_3))])


#;(stepper red (term (cps (λ (f (int -> int)) (λ (g (int -> int)) ((f 0) \; ((g 0) \; 0)))) () () ())))
#;(stepper red (term (cps (λ (f (int -> int)) (λ (g (int -> int)) ((g 0) \; ((f 0) \; 0)))) () () ())))
#;(stepper red (term (cps (λ (f (int -> int)) (λ (g (int -> int)) (((f 0) \; (g 0)) \; 0))) () () ())))
#;(judgment-holds (typed () (λ (f (int -> int)) (λ (g (int -> int)) ((f 0) \; ((g 0) \; 0)))) t) t)

(judgment-holds (Ftyped (β) () ((λ [γ] (f (int -> ((int -> γ) -> β))) (f 0)) (λ [α] (x int) (λ (k (int -> α)) (k x)))) t) t)
(judgment-holds (Ftyped (β) () (λ [α] (x int) (λ (k (int -> α)) (k x))) t) t)
(judgment-holds (Ftyped (β) () (λ [γ] (f (int -> ((int -> γ) -> β))) (f 0)) t) t)

(judgment-holds (Ftyped () () ((λ [γ] (f (int -> ((int -> γ) -> γ))) (f 0)) [α] (λ [α] (x int) (λ (k (int -> α)) (k x)))) t) t)
(judgment-holds (Ftyped () () (λ [γ] (f (int -> ((int -> γ) -> γ))) (f 0)) t) t)
(judgment-holds (Ftyped () () (λ [α] (x int) (λ (k (int -> α)) (k x))) t) t)