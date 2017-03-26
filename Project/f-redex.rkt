#lang racket

(require redex)

(provide (all-defined-out))

(define-language F
  (e (v [t] v) v (if v then e else e))
  (v x true false (λ [α] (x t) e))
  (t (∀ [α] t -> t) α bool)
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
  ;; 2. general purpose capture avoiding case
  [(subst-x x_1 any_1 (λ [α] (x_2 t_2) any_2))
   (λ [α] (x_new t_2) 
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
  #:contract (typed Δ Γ e t)
  #:mode (typed I I I O)
  [ ;; x : t \in Γ
   ------------------------------------------------ Ftvar
   (typed (α ...) ((x_1 t_1) ... (x t) (x_2 t_2) ...) x t)]
  
  [(typed (α α_1 ...) ((x t) (x_1 t_1) ...) e t_r)
   ----------------------------------------------- Ftlam
   (typed (α_1 ...) ((x_1 t_1) ...) (λ [α] (x t) e) (∀ [α] t -> t_r))]

  [(typed Δ Γ v_fun (∀ [α] t_arg -> t_res))
   (typed Δ Γ v_arg t_2)
   (where t_2 (subst-α α t t_arg))
   (where t_3 (subst-α α t t_res))
   ------------------------------------------------ Ftapp
   (typed Δ Γ (v_fun [t] v_arg) t_3)]
  
  [
   ---------------- Fttrue
   (typed Δ Γ true bool)]

  [
   ---------------- Ftfalse
   (typed Δ Γ false bool)]

  [
   (typed Δ Γ e_1 bool)
   (typed Δ Γ e_2 t_r)
   (typed Δ Γ e_3 t_r)
   ------------------- Ftif
   (typed Δ Γ (if e_1 then e_2 else e_3) t_r)])

(define-metafunction F
  Fevaluate : e -> any or "type error!"
  [(Fevaluate e)
   ,(first (apply-reduction-relation* red (term e)))
   (side-condition (judgment-holds (typed () () e t)))]
  [(Fevaluate e)
   "type error!"])


(define ex1 (term ((λ [α] (x (∀ [α] bool -> bool)) x) [α] (λ [α] (w bool) w))))
(define re1 (term (λ [α] (w bool) w)))

(define ex2 (term ((λ [α] (x (∀ [α] bool -> bool)) (λ [α] (y bool) x)) [α] (λ [α] (w bool) w))))
(define re2 (term (λ [α] (y bool) (λ [α] (w bool) w))))

(define ex3 (term ((λ [α] (x (∀ [α] bool -> (∀ [α] bool -> bool))) x)
                   [α]
                   (λ [α] (y bool) (λ [α] (z bool) z)))))
(define re3 (term (λ [α] (y bool) (λ [α] (z bool) z))))

(define ex10 (term ((λ [α] (x bool) (if x then false else true)) [α] true)))
(define re10 (term false))

(define ex11 (term ((λ [α] (x bool) (if x then false else true)) [α] false)))
(define re11 (term true))

(module+ test
  (test-equal (judgment-holds (typed () () (λ [α] (x bool) x) t) t) '((∀ (α) bool -> bool)))
  (test-equal (judgment-holds (typed () () true t) t) '(bool))
  (test-equal (judgment-holds (typed () () ((λ [α] (x (∀ [α] bool -> bool)) x) [α] true) t) t) '())
  (test-equal (judgment-holds (typed () () ((λ [α] (x bool) x) [α] true) t) t) '(bool))
  (test-equal (judgment-holds (typed () () ((λ [α] (x (∀ [α] bool -> bool)) x) [α] (λ [α] (w bool) w)) t) t) '((∀ (α) bool -> bool)))
  (test-equal (judgment-holds (typed () () (λ [α] (f (∀ [α] α -> α)) (λ [β] (x β) (f [β] x))) t) t) '((∀ (α) (∀ (α) α -> α) -> (∀ (β) β -> β)))))

(module+ test
  (test-equal (term (Fevaluate ,ex1)) re1)
  (test-equal (term (Fevaluate ,ex2)) re2)
  (test-equal (term (Fevaluate ,ex3)) re3)
  (test-equal (term (Fevaluate ,ex10)) re10)
  (test-equal (term (Fevaluate ,ex11)) re11))