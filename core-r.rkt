#lang racket

;; Core R
;;
;; Formal semantics of Core R from
;; "Evaluating the design of the R language: objects and functions for
;;  data analysis" (doi>10.1007/978-3-642-31057-7_6)
;;
;; Redex model 2016 by Oli Flückiger and Joseph Sackett
;;  for 7400: iPPL (Amal Ahmed)

(require redex)

;; =============================================================================
;;             Syntax

; Fig. 1 : Surface syntax
(define-language core-r
  (e ::=
     n                          ; number
     s                          ; string
     x                          ; symbol
     (x @ e)                    ; vector access: x[[e]]
     {e ...}                    ; sequence: {e; e}
     (function (f ...) e)       ; function declaration
     (x ^ (a ...))              ; invoke: c(a ...)
     (x <- e)                   ; assign
     (x <<- e)                  ; super assign
     (x @ e <- e)               ; vector element assign
     (x @ e <<- e)              ; vector element super assign
     (attr e e)                 ; attribute access
     (attr e e <- e))           ; attribute set
  (n ::= number)
  (s ::= string)
  (x ::= variable-not-otherwise-mentioned)
  (f ::=                        ; formal arg is either:
     x                          ;   symbol
     (x = e))                   ;   symbol with default value
  (P ::= (e ...))
  (N ::= ((x = e) ...))
  (a ::=                        ; function args:
     e                          ;   positional
     (x = e)))                  ;   named


;; -----------------------------------------------------------------------------

; Fig. 2 : Syntax for data objects
(define-extended-language core-r-red core-r
  (e ::=
     ....
     u                ; values
     (v ^ (a ...))    ; partially reduced functions
     )
  
  ; Types of references: iota, rho or v
  (refT ::=
        &i
        &p
        &v)
  
  ; reference to a frame
  (i ::= (&i n))
  ; reference to a promise
  (p ::= (&p n))
  ;reference to data obj
  (v ::= (&v n))
  
  ; common type for references
  (ref ::=
       i
       p
       v)
  
  (Pr ::= (pr (at ...)))   ; primitive values have attributes
  (at ::= (mv mv))         ; attribute (alpha): pair of addresses or bottom
  (mv ::=                  ; maybe address: might be missing
      v
      U)
  
  (pr ::=                 ; primitive values:
      (num n ...)          ;   number
      (str s ...)          ;   string
      (gen v ...)          ;   references
      (λ G (f ...) e)      ;   closure, G binds to declaring frame
      )
  
  ; Different types of cells on the heap
  (l ::=               ; cells on the heap:
     (i F)             ;   a Frame
     (p (e G))         ;   an unevaluated promise
     (p v)             ;   an evaluated promise
     (v Pr))           ;   a primitive value
  
  ; metavariable for any value which can be stored on the heap
  (hval ::=
        F
        (e G)
        v
        Pr)
  
  ; internal values
  (u ::=
     p
     v
     ; FIX: u needs to range over missing value. see p.11, Fig. 4, [args4]
     U)
  
  ; the heap is a list of cells
  (H ::= (l ...))
  
  ; a binding from symbol to value
  (bind :: = (x u))
  ; frame is a list of bindings
  (F ::= (bind ...))
  
  ; An environment (Gamma) is a list of frames 
  (G ::= (i ...))
  
  ; Execution stack:
  ; contains expressions and their environments to be executed.
  ; / and * solely for faster visual recognition
  (S ::= (e / G *))
  
  ; Execution contexts
  (C ::=
     hole
     (x <- C)
     (x @ C)
     (x <<- C)        ; FIX : added
     (x @ e <- C)
     (x @ C <- v)
     (v ... C e ...)
     (attr C e)
     (attr v C)
     (attr e e <- C)
     (attr C e <- v)
     (attr v C <- v))
  (R ::=
     hole
     (v ... R)))


;; =============================================================================
;;             Metafunctions from Fig. 4

;; ------------ [GetF 1-4]

; lookup a function
(define-metafunction
  core-r-red
  getfun : H G x -> v
  
  ; getF1 -> current scope has a function binding x
  ((getfun H (i i_r ...) x)
   v
   (where F (load i H))
   (where (bind_l ... (x v) bind_r ...) F)
   (where ((λ any ...) (at ...)) (load v H)))
  
  ; getF3 -> current scope has a promise binding x which is evaluated to a function
  ((getfun H (i i_r ...) x)
   v
   (where F (load i H))
   (where (bind_l ... (x p) bind_r ...) F)
   (where v (load p H))
   (where ((λ any ...) (at ...)) v))
  
  ; getF4 -> current scope has a promise binding x which is not evaluated
  ((getfun H (i i_r ...) x)
   p
   (where F (load i H))
   (where (bind_l ... (x p) bind_r ...) F)
   (where (e G_p) (load p H)))
  
  ; getF2,5 -> go to parrent scope
  ((getfun H (i i_r ...) x)
   (getfun H (i_r ...) x)))


;; ------------ [Split, Args, Args1-4]

; bind passed arguments to formal arguments
(define-metafunction
  core-r-red
  args : (f ...) (a ...) G G H -> (F G H)
  
  ((args (f ...) (a ...) G (i_1 ...) H)
   (F G_2 H_2)
   (where (P N) (split (a ...) () ()))
   (where i_fresh (fresh &i H))
   (where G_2 (i_fresh i_1 ...))
   (where (F H_1) (args2 (f ...) P N G G_2 H))
   (where H_2 (store i_fresh F H_1))))

(define-metafunction
  core-r-red
  split : (a ...) P N -> (P N)
  ; named arg first
  ((split ((x_f = e_f) a ...) P N)
   (P_1 ((x_f = e_f) (x_1 = e_1) ...))
   (where (P_1 ((x_1 = e_1) ...)) (split (a ...) P N)))
  ; positional arg first
  ((split (e_f a ...) P N)
   ((e_f e_1 ...) N_1)
   (where ((e_1 ...) N_1) (split (a ...) P N)))
  ; done
  ((split () P N)
   (P N)))

(define-metafunction
  core-r-red
  args2 : (f ...) P N G G H -> (F H)
  
  ; Formal argument is matched by a named parameter
  ((args2 (x f ...) P N G G_1 H)
   (F_1 H_2)
   (where ((x_l e_l) ... (x = e) (x_r = e_r) ...) N)
   (where (F H_1) (args2 (f ...) P ((x_l e_l) ... (x_r = e_r) ...) G G_1 H))
   (where p_fresh (fresh &p H_1))
   (where H_2 (store p_fresh (e G) H_1))
   (where F_1 (update/frame x p_fresh F)))
  
  ; Formal argument (which has ignored default value) is matched by a named parameter
  ((args2 ((x = e_def) f ...) P N G G_1 H)
   (F_1 H_2)
   (where ((x_l e_l) ... (x = e) (x_r = e_r) ...) N)
   (where (F H_1) (args2 (f ...) P ((x_l e_l) ... (x_r = e_r) ...) G G_1 H))
   (where p_fresh (fresh &p H_1))
   (where H_2 (store p_fresh (e G) H_1))
   (where F_1 (update/frame x p_fresh F)))
  
  ; Formal argument is matched by a positional arg
  ((args2 (x f ...) (e e_r ...) N G G_1 H)
   (F_1 H_2)
   (where (F H_1) (args2 (f ...) (e_r ...) N G G_1 H))
   (where p_fresh (fresh &p H_1))
   (where H_2 (store p_fresh (e G) H_1))
   (where F_1 (update/frame x p_fresh F)))
  
  ; Formal argument (with ignored default) is matched by a positional arg
  ((args2 ((x = e_def) f ...) (e e_r ...) N G G_1 H)
   (F_1 H_2)
   (where (F H_1) (args2 (f ...) (e_r ...) N G G_1 H))
   (where p_fresh (fresh &p H_1))
   (where H_2 (store p_fresh (e G) H_1))
   (where F_1 (update/frame x p_fresh F)))
  
  ; Missing arg no default
  ((args2 (x f ...) () N G G_1 H)
   (F_1 H_1)
   (where (F H_1) (args2 (f ...) () N G G_1 H))
   (where F_1 (update/frame x U F)))
  
  ; Missing arg with default expression
  ((args2 ((x = e) f ...) () N G G_1 H)
   (F_1 H_2)
   (where (F H_1) (args2 (f ...) () N G G_1 H))
   (where p_fresh (fresh &p H_1))
   (where H_2 (store p_fresh (e G_1) H_1))
   (where F_1 (update/frame x p_fresh F)))
  
  ; Base case
  ((args2 () () () G G_1 H)
   (() H))
  )


;; =============================================================================
;;             Metafunctions from Fig. 18

;; ------------ helpers

; get a fresh reference of a certain type
(define-metafunction core-r-red
  fresh : refT H -> ref
  ((fresh refT H) (fresh/acc refT H 0)))
(define-metafunction core-r-red
  fresh/acc : refT H n -> ref
  ((fresh/acc refT () n_max)
   (refT n_next)
   (where n_next ,(+ (term n_max) 1)))
  ((fresh/acc refT (((refT n_cur) any) l ...) n_max)
   (fresh/acc refT (l ...) n_next)
   (where n_next ,(if (> (term n_cur) (term n_max)) (term n_cur) (term n_max))))
  ((fresh/acc refT (((refT_other n_other) any) l ...) n_max)
   (fresh/acc refT (l ...) n_max)))

; load a value from the heap, given a reference
(define-metafunction core-r-red
  load : ref H -> hval
  ((load ref (l_l ... (ref hval) l_r ...))
   hval))

; store value on the heap
(define-metafunction core-r-red
  store : ref hval H -> H
  ((store ref hval (l_l ... (ref hval_old) l_r ...))
   (l_l ... l_r ... (ref hval)))
  ((store ref hval (l ...))
   (l ... (ref hval))))

; update binding in a given frame
(define-metafunction core-r-red
  update/frame : x u F -> F
  ((update/frame x u (bind_l ... (x u_old) bind_r ...))
   (bind_l ... (x u) bind_r ...))
  ((update/frame x u (bind ...))
   (bind ... (x u))))


;; ------------ [Copy0-2]

; produce a new heap with a copy of v
(define-metafunction
  core-r-red
  cpy : H mv -> (H mv)
  
  ; copy1
  ((cpy H U) (H U))
  
  ; copy2
  ((cpy H v)
   (H_2 v_fresh)
   ; load value
   (where (pr (at ...)) (load v H))
   ; copy its attributes
   (where (H_1 (at_2 ...)) (cpy/attr () H (at ...)))
   ; get a fresh ref
   (where v_fresh (fresh &v H))
   ; create new value with the copied attrs
   (where Pr_n (pr (at_2 ...)))
   ; store it to the new heap
   (where H_2 (store v_fresh Pr_n H_1))))

; copy0
(define-metafunction
  core-r-red
  cpy/attr : (at ...) H (at ...) -> (H (at ...))
  ((cpy/attr (at_done ...)                  H    ((mv_1 mv_2) at_r ...))
   ; accumulate copied attrs in at_done
   (cpy/attr (at_done ... (mv_n_1 mv_n_2))  H_2  (at_r ...))
   ; copy attr key
   (where (H_1 mv_1_n) (cpy H   mv_1))
   ; copy attr val
   (where (H_2 mv_2_n) (cpy H_1 mv_2)))
  ((cpy/attr (at ...) H ())
   (H (at ...))))


;; ------------ [Super1-3]

; assign function used for super assignments
(define-metafunction
  core-r-red
  assign : x v G H -> H
  
  ; super3
  ; we are at the top scope -> unconditionally assign
  ((assign x v (i) H)
   H_1
   (where F (load i H))
   (where F_1 (update/frame x v F))
   (where H_1 (store i F_1 H)))
  
  ; super1
  ; bindign exitst in current frame -> update
  ((assign x v (i i_r ...) H)
   H_1
   (where F (load i H))
   (where (bind_l ... (x u) bind_r ...) F)
   (where F_1 (update/frame x v F))
   (where H_1 (store i F_1 H)))
  
  ; super2
  ; binding does not exits -> go to the parent frame
  ((assign x v (i i_r ...) H)
   (assign x v (i_r ...) H)))

;; ------------ [Look1-2]

; lookup a variable in a certain gamma
; FIX : u not v
(define-metafunction core-r-red
  lookup : G H x -> u
  ; Look0+1
  ((lookup (i i_rest ...) H x)
   u
   (where F (load i H))
   (where (bind_l ... (x u) bind_r ...) F))
  ; Look2
  ((lookup (i i_rest ...) H x)
   (lookup (i_rest ...) H x)))


;; ------------ [(Get|SET)(N|S|G)]

; access vector v at offset n
(define-metafunction core-r-red
  get : v n H -> (v H)
  ((get v n_m H)
   (v_1 H_1)
   (where ((num n_1 ... n n_2 ...) (at ...)) (load v H))
   (side-condition (eq? (- (term n_m) 1) (length (term (n_1 ...)))))
   (where v_1 (fresh &v H))
   (where H_1 (store v_1 ((num n) ()) H))))

; assign vector at offset
(define-metafunction core-r-red
  set : v n v H -> H
  
  ; setN : override an existing value
  ((set v n_m v_1 H)
   H_1
   (where n (readn v_1 H))
   (where ((num n_l ... n_old n_r ...) (at ...)) (load v H))
   (side-condition (eq? (- (term n_m) 1) (length (term (n_l ...)))))
   (where H_1 (store v ((num n_l ... n n_r ...) (at ...)) H)))
  
  ; setNE : grow the vector by one element
  ;         (growing more than 1 element at a time is an omission in core r)
  ((set v n_m v_1 H)
   H_1
   (where n (readn v_1 H))
   (where ((num n_l ...) (at ...)) (load v H))
   (side-condition (eq? (- (term n_m) 1) (length (term (n_l ...)))))
   (where H_1 (store v ((num n_l ... n) (at ...)) H)))
  
  ; TODO: cases for str, gen and casts
  )

;; ------------ [ReadS(sic)]

; convert reference to numerical value iff ref. is a scalar number on the heap
(define-metafunction core-r-red
  ; FIX: readn not reads
  readn : v H -> n
  ((readn v H)
   n
   (where ((num n) ()) (load v H))))


;; =============================================================================
;;             Reduction relation --> Fig. 5, p. 12

; (rule names according to the paper)
; Inner reduction relation, is driven by outer ==>
; Takes expression, environment and heap
;  * steps to reduced expression and modified heap
;  * environment Gamma is not returned (i.e. is unchanged), but content of
;    frames can change on the heap.
(define ->
  (reduction-relation 
   core-r-red
   ; Domain and codomain of the reduction relation are not equal..?
   ; #:domain (e G H)
   
   (--> (n G H)
        (v H_n)
        (where (l ...) H)
        (where v (fresh &v H))
        (where Pr ((num n) ()))
        (where H_n (l ... (v Pr)))
        num)
   
   (--> (s G H)
        (v H_n)
        (where (l ...) H)
        (where v (fresh &v H))
        (where Pr ((str s) ()))
        (where H_n (store v Pr H))
        str)
   
   (--> ((function (f ...) e) G H)
        (v H_n)
        (where (l ...) H)
        (where v (fresh &v H))
        (where Pr ((λ G (f ...) e) ()))
        (where H_n (store v Pr H))
        fun)
   
   (--> (x G H)
        (u H)
        (where u (lookup G H x))
        find)
   
   (--> (p G H)    ; FIX: H' (') typo
        (v H)
        (where v (load p H))
        get-p)
   
   (--> ((x <- v) (i i_r ...) H)
        (v H_2)
        ; Copy the value to assign
        (where (H_1 v_1) (cpy H v))
        ; Get the current frame
        (where F (load i H))
        ; Update the frame
        (where F_1 (update/frame x v_1 F))
        ; Extend the heap with an extended frame
        (where H_2 (store i F_1 H_1))
        ass)
   
   (--> ((x <<- v) (i i_r ...) H)
        (v H_2)
        ; Copy the value to assign
        (where (H_1 v_1) (cpy H v))
        ; Assign starting at the parent frame
        (where H_2 (assign x v_1 (i_r ...) H_1))
        d-ass)
   
   (--> ((x @ v) G H)
        (v_2 H_1)
        (where v_1 (lookup G H x))
        (where n (readn v H))
        (where (v_2 H_1) (get v_1 n H))
        get)
   
   (--> ((x @ v <- v_1) (i i_r ...) H)
        (v_1 H_2)
        (where (H_1 v_2) (cpy H v_1))
        (where (bind_l ... (x v_3) bind_r ...) (load i H))
        (where n (readn v H_1))
        (where H_2 (set v_3 n v_2 H_1))
        set-l)
   
   (--> ((x @ v <- v_1) (i i_r ...) H)
        (v_1 H_4)
        (where (H_1 v_2) (cpy H v_1))
        (where F (load i H_1))
        ; x not in dom(F) :
        (side-condition (eq? (redex-match core-r-red (bind_l ... (x v_some) bind_r ...) (term F)) #f))
        (where v_3 (lookup (i_r ...) H_1 x))
        (where (H_2 v_4) (cpy H_1 v_3))
        (where F_1 (update/frame x v_4 F))
        (where H_3 (store i F_1 H_2))
        (where n (readn v H))
        (where H_4 (set v_4 n v_2 H_3))
        set-g)
   
   ))


;; =============================================================================
;;             Reduction relation ==> Fig. 3, p. 10

; (rule names according to the paper)
; Outer reduction relation ==>, drives the inner -->
; Deals with function invocation, forcing promises, and returning from those two

(define =>
  (reduction-relation
   core-r-red
   #:domain (S ... : H)
   
   ; Take one reduction step --> for the current expression at the top of
   ; the execution stack
   (--> (((in-hole C e)   / G *) S ... : H)
        (((in-hole C e_n) / G *) S ... : H_n)
        (where ((e_n H_n)) ,(apply-reduction-relation -> (term (e G H))))
        exp)
   
   ; Promise reference: push promise to execution stack
   (--> (            ((in-hole C p) / G *) S ... : H)
        ((e / G_1 *) ((in-hole C p) / G *) S ... : H)
        (where (e G_1) (load p H))
        force-p)
   
   ; Function lookup (1):
   ;  the binding for x is a promise, we have to force it to figure out if
   ;  it evaluates to a closure. See p. 5 for this "feature"
   (--> (          ((in-hole C (x ^ (a ...))) / G *) S ... : H)
        ((p / G *) ((in-hole C (x ^ (a ...))) / G *) S ... : H)
        (where p (getfun H G x))
        force-f)
   
   ; Function lookup (2): binding points to a closure
   (--> (((in-hole C (x ^ (a ...))) / G *) S ... : H)
        (((in-hole C (v ^ (a ...))) / G *) S ... : H)
        (where v (getfun H G x))
        get-f)
   
   ; Function invocation:
   ;  push closure onto execution stack
   (--> (            ((in-hole C (v ^ (a ...))) / G *) S ... : H)
        ((e / G_2 *) ((in-hole C (v ^ (a ...))) / G *) S ... : H_1)
        (where ((λ G_1 (f ...) e) (at ...)) (load v H))
        (where (F G_2 H_1) (args (f ...) (a ...) G G_1 H))
        inv-f)
   
   ; Return from promise:
   ;  update promise cell with value, remove promise expression from stack
   (--> (((in-hole R v) / G_1 *) ((in-hole C p) / G *) S ... : H)
        (                        ((in-hole C p) / G *) S ... : H_1)
        (where H_1 (store p v H))
        ret-p)
   
   ; Return from function
   ;  substitute function invocation with value of last statement
   ;  from method body
   (--> (((in-hole R v) / G_1 *) ((in-hole C (v_1 ^ (a ...))) / G *) S ... : H)
        (                        ((in-hole C v)               / G *) S ... : H)
        ret-f)
   
   ; FIX: sequence rule added
   (--> (((in-hole C (v_1 ... v)) / G *) : H)
        (((in-hole C v)           / G *) : H)
        seq)
   ))


; return the primitive value of the result of a computation from the heap
(define-metafunction core-r-red
  result : ((v / G *) : H) -> Pr
  ((result ((v / G *) : H))
   (load v H)))

(define (eval t)
  ; in the initial state we have two environments
  ; TODO, FIX : this deals with the fact that super assignment does not stop at the toplevel env
  (let ((init-state (term ((,t / ((&i 0) (&i -1)) *) : (((&i -1) ()) ((&i 0) ()))))))
    (let ((res (apply-reduction-relation* => init-state)))
      (term (result ,(first res))))))

(define (show t)
  (let ((init-state (term ((,t / ((&i 0) (&i -1)) *) : (((&i -1) ()) ((&i 0) ()))))))
    (traces => init-state)))

; helper to create a number vector
(define-metafunction core-r-red
  c-num : n ... -> Pr
  ((c-num n ...)
   ((num n ...) ())))


;; -----------------------------------------------------------------------------

(module+ test
  (define three (term (c-num 3)))
  
  (test-equal (eval (term (bla <- 3)))
              three)
  
  (test-equal (eval (term ((bla <- 3) bla)))
              three)
  
  (test-equal (eval (term ((bla <<- 3) bla)))
              three)
  
  (test-equal (eval (term ((loc <- 1)
                           (f <- (function () (loc <<- 3)))
                           (f ^ ())
                           loc)))
              three)
  
  (define one (term (c-num 1)))
  
  (test-equal (eval (term ((f <- (function (a) a))
                           (f ^ (1)))))
              one)
  
  (test-equal (eval (term ((a <- 1)
                           a)))
              one)
  
  (test-equal (eval (term ((a <- 1)
                           (a @ 2 <- 3)
                           a)))
              (term (c-num 1 3)))
  
  ; Core r does not support anon- functions
  ; (eval (term ((function () 1) ^ ())))
  
  (test-equal (eval (term ((a <- 1)
                           (f <- (function ()
                                           ((a @ 2 <- 3)
                                            a)))
                           (r <- (f ^ ()))
                           (b <- r)
                           (b @ 3 <- a)
                           b)))
              (term (c-num 1 3 1)))
  
  
  (define r
    (eval (term {1
                 (f <- (function (c (a = 66) (b = 2))
                                 (1
                                  (sup <- (function () (loc <<- 37)))
                                  (loc <- -1)
                                  (d <- a)
                                  (d @ 2 <- b)
                                  (d @ 3 <- c)
                                  (d @ 4 <- loc)
                                  (sup ^ ())
                                  (d @ 5 <- loc)
                                  d)))
                 (g <- (function (a) 1))
                 (f ^ ((b = (g ^ ())) 42))})))
  
  (test-equal r (term (c-num 66, 1, 42, -1, 37)))
  
  ; (show (term ((a <- 1)
  ;              (f <- (function (x) ((r <- a)
  ;                                   (r @ 2 <- x)
  ;                                   (r @ 3 <- a)
  ;                                   r)))
  ;              (f ^ ((a <- 2))))))
  )