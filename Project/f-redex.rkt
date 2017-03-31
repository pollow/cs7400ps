#lang racket

(require redex)

(provide (all-defined-out))

(define-language F
  (e ::=
     (e [t] e)
     (e e)
     v
     (if v then e else e))
  (v ::=
     x
     true
     false
     (λ (x t) e)
     (λ [α] (x t) e))
  (t ::=
     (t -> t)
     (∀ [α] t -> t)
     α
     bool)
  (E hole)
  (x variable-not-otherwise-mentioned)
  (α variable-not-otherwise-mentioned))

(define red
  (reduction-relation
   F
   (--> (in-hole E (if true then e_1 else e_2))
        (in-hole E e_1)
        "if true")
   (--> (in-hole E (if false then e_1 else e_2))
        (in-hole E e_2)
        "if false")
   (--> (in-hole E ((λ [α] (x t_1) e) [t] v))
        (in-hole E (subst-x x v (subst-α α t e)))
        "βv")))


(define-metafunction F
  subst-x : x any any -> any
  ;; 1. x_1 bound, so don't continue in λ body
  [(subst-x x_1 any_1 (λ [α] (x_1 t_1) any_2))
   (λ [α] (x_1 t_1) any_2)]
  [(subst-x x_1 any_1 (∀ [α] (x_1 t_1) any_2))
   (∀ [α] (x_1 t_1) any_2)]
  ;; 2. general purpose capture avoiding case
  [(subst-x x_1 any_1 (λ [α] (x_2 t_2) any_2))
   (λ [α] (x_new t_2) 
     (subst-x x_1 any_1
              (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in
                  (term (x_1 any_1 any_2)) 
                  (term x_2)))]
  [(subst-x x_1 any_1 (∀ [α] (x_2 t_2) any_2))
   (∀ [α] (x_new t_2) 
     (subst-x x_1 any_1
              (subst-var x_2 x_new any_2)))
   (where x_new ,(variable-not-in
                  (term (x_1 any_1 any_2)) 
                  (term x_2)))]
  ;; 3. replace x_1 with e_1
  [(subst-x x_1 any_1 x_1) any_1]
  ;; 4. x_1 and x_2 are different, so don't replace
  [(subst-x x_1 any_1 x_2) x_2]
  ;; the last cases cover all other expressions
  [(subst-x x_1 any_1 (any_2 ...))
   ((subst-x x_1 any_1 any_2) ...)]
  [(subst-x x_1 any_1 any_2) any_2])

(define-metafunction F
  subst-var : x any any -> any
  [(subst-var x_1 any_1 x_1) any_1]
  [(subst-var x_1 any_1 (any_2 ...)) 
   ((subst-var x_1 any_1 any_2) ...)]
  [(subst-var x_1 any_1 any_2) any_2]
  [(subst-var any) any])


(define-metafunction F
  subst-α : α any any -> any
  ;; 1. α_1 bound, so don't continue in λ body
  [(subst-α α_1 any_1 (λ [α_1] (x_1 t_1) any_2))
   (λ [α_1] (x_1 t_1) any_2)]
  ;; 2. general purpose capture avoiding case
  [(subst-α α_1 any_1 (λ [α_2] (x_1 t_1) any_2))
   (λ [α_new] (x_1 t_1)
      (subst-α α_1 any_1
               (subst-var-α α_2 α_new any_2)))
   (where α_new ,(variable-not-in
                  (term (α_1 any_1 any_2)) 
                  (term α_2)))]
  [(subst-α α_1 any_1 α_1) any_1]
  [(subst-α α_1 any_1 α_2) α_2]
  [(subst-α α_1 any_1 (any_2 ...))
   ((subst-α α_1 any_1 any_2) ...)]
  [(subst-α α_1 any_1 any_2) any_2])

(define-metafunction F
  subst-var-α : α any any -> any
  [(subst-var-α α_1 any_1 α_1) any_1]
  [(subst-var-α α_1 any_1 (any_2 ...)) 
   ((subst-var-α α_1 any_1 any_2) ...)]
  [(subst-var-α α_1 any_1 any_2) any_2]
  [(subst-var-α any) any])


(define-extended-language F-typ F
  (Δ ::= (α ...))
  (Γ ::= ((x t) ...)))

(define-judgment-form F-typ
  #:contract (Ftyped Δ Γ e t)
  #:mode (Ftyped I I I O)
  [ ;; x : t \in Γ
   ------------------------------------------------ Ftvar
   (Ftyped (α ...) ((x_1 t_1) ... (x t) (x_2 t_2) ...) x t)]
  
  [(Ftyped (α α_1 ...) ((x t) (x_1 t_1) ...) e t_r)
   ----------------------------------------------- Ftlam
   (Ftyped (α_1 ...) ((x_1 t_1) ...) (λ [α] (x t) e) (∀ [α] t -> t_r))]

  [(Ftyped (α_1 ...) ((x t) (x_1 t_1) ...) e t_r)
   ----------------------------------------------- Ftlam2
   (Ftyped (α_1 ...) ((x_1 t_1) ...) (λ (x t) e) (t -> t_r))]
  
  [(Ftyped Δ Γ v_fun (∀ [α] t_arg -> t_res))
   (Ftyped Δ Γ v_arg t_2)
   (where t_2 (subst-α α t t_arg))
   (where t_3 (subst-α α t t_res))
   ------------------------------------------------ Ftapp
   (Ftyped Δ Γ (v_fun [t] v_arg) t_3)]

  [(Ftyped Δ Γ v_fun (t_arg -> t_res))
   (Ftyped Δ Γ v_arg t_arg)
   ------------------------------------------------ Ftapp2
   (Ftyped Δ Γ (v_fun v_arg) t_res)]
  
  [
   ---------------- Fttrue
   (Ftyped Δ Γ true bool)]

  [
   ---------------- Ftfalse
   (Ftyped Δ Γ false bool)]

  [
   (Ftyped Δ Γ e_1 bool)
   (Ftyped Δ Γ e_2 t_r)
   (Ftyped Δ Γ e_3 t_r)
   ------------------- Ftif
   (Ftyped Δ Γ (if e_1 then e_2 else e_3) t_r)])

(define-metafunction F
  Fevaluate : e -> any or "type error!"
  [(Fevaluate e)
   ,(first (apply-reduction-relation* red (term e)))
   (side-condition (judgment-holds (Ftyped () () e t)))]
  [(Fevaluate e)
   "type error!"])


(define fex1 (term ((λ [α] (x (∀ [α] bool -> bool)) x) [α] (λ [α] (w bool) w))))
(define fre1 (term (λ [α] (w bool) w)))

(define fex2 (term ((λ [α] (x (∀ [α] bool -> bool)) (λ [α] (y bool) x)) [α] (λ [α] (w bool) w))))
(define fre2 (term (λ [α] (y bool) (λ [α] (w bool) w))))

(define fex3 (term ((λ [α] (x (∀ [α] bool -> (∀ [α] bool -> bool))) x)
                   [α]
                   (λ [α] (y bool) (λ [α] (z bool) z)))))
(define fre3 (term (λ [α] (y bool) (λ [α] (z bool) z))))

(define fex10 (term ((λ [α] (x bool) (if x then false else true)) [α] true)))
(define fre10 (term false))

(define fex11 (term ((λ [α] (x bool) (if x then false else true)) [α] false)))
(define fre11 (term true))

(module+ test
  (test-equal (judgment-holds (Ftyped () () (λ [α] (x bool) x) t) t) '((∀ (α) bool -> bool)))
  (test-equal (judgment-holds (Ftyped () () true t) t) '(bool))
  (test-equal (judgment-holds (Ftyped () () ((λ [α] (x (∀ [α] bool -> bool)) x) [α] true) t) t) '())
  (test-equal (judgment-holds (Ftyped () () ((λ [α] (x bool) x) [α] true) t) t) '(bool))
  (test-equal (judgment-holds (Ftyped () () ((λ [α] (x (∀ [α] bool -> bool)) x) [α] (λ [α] (w bool) w)) t) t) '((∀ (α) bool -> bool)))
  (test-equal (judgment-holds (Ftyped () () (λ [α] (f (∀ [α] α -> α)) (λ [β] (x β) (f [β] x))) t) t) '((∀ (α) (∀ (α) α -> α) -> (∀ (β) β -> β)))))

(module+ test
  (test-equal (term (Fevaluate ,fex1)) fre1)
  (test-equal (term (Fevaluate ,fex2)) fre2)
  (test-equal (term (Fevaluate ,fex3)) fre3)
  (test-equal (term (Fevaluate ,fex10)) fre10)
  (test-equal (term (Fevaluate ,fex11)) fre11))
