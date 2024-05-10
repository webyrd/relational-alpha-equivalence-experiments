(load "../lib/faster-minikanren/mk-vicare.scm")
(load "../lib/faster-minikanren/mk.scm")
(load "../lib/faster-minikanren/test-check.scm")

;; WEB -- 7 May, 2024

;; Experiments with implementing alpha-equivalence,
;; capture-avoiding-substitution, gensym, etc., fully relationally,
;; without using nominal unification.  Instead, use care encoding
;; along with `=/=`, `absento`, and `symbolo` constraints.  (Of
;; course, the `absento` constraint is inspired by the freshness (#)
;; constraint of nominal logic, but has a very different semantics and
;; implementation.)

;; My initial impression is that this approach is viable.  However,
;; there is one obvious and serious disadvantage: the resulting
;; relations are "eager," as opposed to the laziness of nominal
;; unification, or the laziness of `absento`, for example.  As a
;; result, a conjunction of these goals is likely to result in
;; extremely inefficient "generate-and-test" behavior.

;; I agree with Michael Ballantyne that the most promising general
;; approach to making relations lazier is to look at techniques from
;; Prolog, Curry, constraint programming, etc., such as co-routining,
;; delaying/freezing goals, narrowing and residuation, and the
;; Extended Andorra Model of evaluation.


;; Simultaneously look up symbols `x1` and `x2` in lists of symbols
;; `xs1` and `xs2`, respectively.  For this relation to succeed, `x1`
;; and `x2` must appear in `xs1` and `xs2` in the same position.  (For
;; example, if `x1` first appears in the fourth position of `xs1`,
;; `x2` must first appear in the fourth position of `xs2`, and vice
;; versa.)
(define dual-lookupo
  (lambda (x1 x2 xs1 xs2)
    (fresh (a1 a2 d1 d2)
      (symbolo x1) (symbolo x2)
      (symbolo a1) (symbolo a2) 
      (== `(,a1 . ,d1) xs1)
      (== `(,a2 . ,d2) xs2)
      (conde
        ((== x1 a1) (== x2 a2))
        ((=/= x1 a1) (=/= x2 a2)
         (dual-lookupo x1 x2 d1 d2))))))

#|
Grammar for lambda-calculus terms:

t ::= <x> where <x> is a symbol representing a variable reference |
      (lambda (<x>) <t>) where <x> is a symbol representing an identifier |
      (<t> <t>) representing an application
|#

;; `(alpha-equivo t1 t2)` succeeds if `t1` and `t2` are alpha
;; equivalent.
(define alpha-equivo
  (lambda (t1 t2)
    (alpha-equiv-auxo t1 t2 '() '())))

(define alpha-equiv-auxo
  (lambda (t1 t2 xs1 xs2)
    ;; `xs1` and `xs2` are lists of symbols representing identifiers
    ;; bound by `lambda`.  Together, the pair of `xs1` and `xs2` serve
    ;; as a mapping between variables bound in `t1` and `t2`.  If `t1`
    ;; contains a variable reference, say `z`, either:
    ;;
    ;; (1) `x` is a free variable (in which case it must not be
    ;; present in either `xs1` or `xs2`, and must occur as `z` in
    ;; `t2`); or,
    ;;
    ;; (2) `z` occurs bound in `xs1`, and the equivalent variable
    ;; bound in `xs2` must appear in `t2`.
    (conde
      ((symbolo t1) (symbolo t2)
       (conde
         ((== t1 t2)
           ;; free variable case
          (absento t1 xs1) (absento t2 xs2))
         ((dual-lookupo t1 t2 xs1 xs2))))
      ((fresh (x1 x2 e1 e2)
         (== `(lambda (,x1) ,e1) t1)
         (== `(lambda (,x2) ,e2) t2)
         (alpha-equiv-auxo e1 e2 `(,x1 . ,xs1) `(,x2 . ,xs2))))
      ((fresh (rator1 rator2 rand1 rand2)
         (== `(,rator1 ,rand1) t1)
         (== `(,rator2 ,rand2) t2)
         (alpha-equiv-auxo rator1 rator2 xs1 xs2)
         (alpha-equiv-auxo rand1 rand2 xs1 xs2))))))

;; capture-avoiding-substitution, based on the rules described in:
;;
;; https://yangdanny97.github.io/blog/2019/05/25/capture-avoiding-substitution
(define capture-avoiding-substo
  (lambda (t t-sub x t-new)
    (fresh ()
      (symbolo x)
      (conde
        ((symbolo t)
         (conde
           ((== x t) (== t-sub t-new))
           ((=/= x t) (== t t-new))))
        ((fresh (y e y^ e^ t-new^)
           ;; if `t` is a `lambda` term, alpha-rename `t` to produce a
           ;; new term that respects the two hygiene conditions for
           ;; capture-avoiding substitution.
           (symbolo y)
           (symbolo y^)
           (== `(lambda (,y) ,e) t)
           (== `(lambda (,y^) ,t-new^) t-new)
           (=/= y^ x)
           (absento y^ t-sub)
           (alpha-equivo t `(lambda (,y^) ,e^))
           (capture-avoiding-substo e^ t-sub x t-new^)))
        ((fresh (e1 e2 e1^ e2^)
           (== `(,e1 ,e2) t)
           (== `(,e1^ ,e2^) t-new)
           (capture-avoiding-substo e1 t-sub x e1^)
           (capture-avoiding-substo e2 t-sub x e2^)))))))


(test "alpha-equivo-1"
  (run 8 (t1 t2) (alpha-equivo t1 t2))
  '(((_.0
      _.0)
     (sym _.0))
    (((lambda (_.0) _.1)
      (lambda (_.2) _.1))
     (sym _.1)
     (absento (_.1 _.0) (_.1 _.2)))
    (((lambda (_.0) _.0)
      (lambda (_.1) _.1))
     (sym _.0 _.1))
    (((_.0 _.1)
      (_.0 _.1))
     (sym _.0 _.1))
    (((lambda (_.0) (lambda (_.1) _.2))
      (lambda (_.3) (lambda (_.4) _.2)))
     (sym _.2)
     (absento (_.2 _.0) (_.2 _.1) (_.2 _.3) (_.2 _.4)))
    (((lambda (_.0) (lambda (_.1) _.1))
      (lambda (_.2) (lambda (_.3) _.3)))
     (sym _.1 _.3))
    (((_.0 (lambda (_.1) _.2))
      (_.0 (lambda (_.3) _.2)))
     (sym _.0 _.2)
     (absento (_.2 _.1) (_.2 _.3)))
    (((lambda (_.0) (_.1 _.2))
      (lambda (_.3) (_.1 _.2)))
     (sym _.1 _.2)
     (absento (_.1 _.0) (_.1 _.3) (_.2 _.0) (_.2 _.3)))))

(test "capture-avoiding-substo-1"
  (run 10 (t t-sub x t-new)
    (capture-avoiding-substo t t-sub x t-new))
  '(((_.0 _.1 _.0 _.1)
     (sym _.0))
    ((_.0 _.1 _.2 _.0)
     (=/= ((_.0 _.2)))
     (sym _.0 _.2))
    (((_.0 _.0) _.1 _.0 (_.1 _.1))
     (sym _.0))
    (((lambda (_.0) _.1) _.2 _.1 (lambda (_.3) _.2))
     (=/= ((_.0 _.1)) ((_.1 _.3)))
     (sym _.0 _.1 _.3)
     (absento (_.3 _.2)))
    (((_.0 _.1) _.2 _.0 (_.2 _.1))
     (=/= ((_.0 _.1)))
     (sym _.0 _.1))
    (((lambda (_.0) _.1) _.2 _.3 (lambda (_.4) _.1))
     (=/= ((_.0 _.1)) ((_.1 _.3)) ((_.1 _.4)) ((_.3 _.4)))
     (sym _.0 _.1 _.3 _.4)
     (absento (_.4 _.2)))
    (((_.0 _.1) _.2 _.1 (_.0 _.2))
     (=/= ((_.0 _.1)))
     (sym _.0 _.1))
    (((lambda (_.0) _.0) _.1 _.2 (lambda (_.3) _.3))
     (=/= ((_.2 _.3)))
     (sym _.0 _.2 _.3)
     (absento (_.3 _.1)))
    (((_.0 _.1) _.2 _.3 (_.0 _.1))
     (=/= ((_.0 _.3)) ((_.1 _.3)))
     (sym _.0 _.1 _.3))
    (((lambda (_.0) (lambda (_.1) _.2))
      _.3
      _.2
      (lambda (_.4) (lambda (_.5) _.3)))
     (=/= ((_.0 _.2)) ((_.2 _.4)) ((_.2 _.5)))
     (sym _.0 _.2 _.4 _.5)
     (absento (_.2 _.1) (_.4 _.3) (_.5 _.3)))))
