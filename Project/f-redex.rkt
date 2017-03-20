#lang racket

(require redex)

(provide (all-defined-out))

(define-language F
  (e (v [t] v) v (if v then e else e))
  (v x true false (λ [α] (x : t) e))
  (t (∀ [α] t -> t) α bool)
  (E hole)
  (x variable-not-otherwise-mentioned)
  (α variable-not-otherwise-mentioned))

(define red
  (reduction-relation
   F
   (--> (in-hole E (if true then e_1 else e_2))
        (in-hole E (e_1))
        "if true")
   (--> (in-hole E (if false then e_1 else e_2))
        (in-hole E (e_2))
        "if false")
   (--> (in-hole E ((λ [α] (x : t_1) e) [t] v))
        (in-hole E (subst-x x v (subst-α α t e)))
        "βv")))


(define-metafunction F
  subst-x : x any any -> any
  ;; 1. x_1 bound, so don't continue in λ body
  [(subst-x x_1 any_1 (λ [α] (x_1 : t_1) any_2))
   (λ [α] (x_1 : t_1) any_2)]
  ;; 2. general purpose capture avoiding case
  [(subst-x x_1 any_1 (λ [α] (x_2 : t_2) any_2))
   (λ [α] (x_new : t_2) 
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
  [(subst-α α_1 any_1 (λ [α_1] (x_1 : t_1) any_2))
   (λ [α_1] (x_1 : t_1) any_2)]
  ;; 2. general purpose capture avoiding case
  [(subst-α α_1 any_1 (λ [α_2] (x_1 : t_1) any_2))
   (λ [α_new] (x_1 : t_1)
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

;; e env tenv -> t or #f
;; this should be replced by type judgements
(define-metafunction F
  tc : e ((x : t) ...) (α ...) -> t or #f
  [(tc true ((x : t) ...) (α ...)) 
   bool]
  [(tc false ((x : t) ...) (α ...)) 
   bool]
  [(tc x_1 ((x_2 : t_2) ... (x_1 : t_1) (x_3 : t_3) ...) (α_1 ...))
   t_1
   (side-condition (not (member (term x_1) (term (x_2 ...)))))]
  [(tc (λ [α_1] (x_1 : t_1) e) ((x_2 : t_2) ...) (α ...))
   (∀ [α_new] t_1 -> t)
   (where α_new ,(variable-not-in (term (α ...))
                                  (term α_1)))
   (where e_new (subst-var-α α_1 α_new e))
   (where t (tc e_new ((x_1 : t_1) (x_2 : t_2) ...) (α_new α ...)))]
  [(tc (v_1 [t_1] v_2) ((x : t) ...) (α ...))
   (subst-α α_1 t_1 (∀ [α_1] t_2 -> t_3))
   (where (∀ [α_1] t_2 -> t_3) (tc v_1 ((x : t) ...) (α ...)))]
   ;;use "where (∀ [α_1] t_2)" will lead to error.

)

;; a few examples from Pierce
#;(test-equal (term (tc (λ [α] (x : α) x) () ()))
            (term (∀ [α] α -> α)))
#;(test-equal (term (tc x ((x : β)) (β)))
            (term β))
(test-equal (term (tc ((λ [α] (x : α) x) [β] true) () ()))
            (term (∀ [β] β -> β)))

#;(test-equal (term (tc (λ [β] (f : (∀ [β] β -> β)) (λ [β] (x : β) (x [β] (x [β] f)))) () ()))
            (term (∀ [β] ((β -> β) -> (β -> β)))))

#;(redex-match? F e (term (λ [β] (f : ∀ [β] β -> β) (λ [β] (x : β) (f (f x))))))

#;(redex-match? F e (term (λ [β] (f : (∀ [β] β -> β)) (λ [β] (x : β) (x [β] (x [β] f))))))