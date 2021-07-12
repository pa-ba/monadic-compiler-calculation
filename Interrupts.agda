module Interrupts where

------------------------------------------------------------------------
-- Calculation for the interrupts language. Instead of the abridged
-- version of the language presented in the paper, we consider the
-- full language as presented by Hutton and Wright [2007].
------------------------------------------------------------------------


open import NonDeterm
open import Data.Nat
open import Data.Maybe hiding (_>>=_)
open import Data.Product 
open import Data.List


---------------------
-- Source language --
---------------------


data Expr : Set where
  Val : ℕ → Expr
  Add : Expr → Expr → Expr
  Throw : Expr
  Catch : Expr → Expr → Expr
  Seqn  : Expr → Expr → Expr
  Block : Expr → Expr
  Unblock : Expr → Expr

Value : Set
Value = Maybe ℕ

data Status : Set where
  U : Status
  B : Status


interrupt : Status → ND Value
interrupt U = return nothing
interrupt B = zero

mutual
  eval : Expr → Status → ND Value
  eval e i = eval' e i ⊕ interrupt i
  
  eval' : Expr → Status → ND Value
  eval' (Val n)   i  = return (just n)
  eval' (Add x y) i  =
     eval x i >>= getJust (return nothing) λ m →
     eval y i >>= getJust (return nothing) λ n →
     return (just (m + n))
  eval' (Seqn x y) i = 
    eval x i >>= getJust (return nothing) λ m →
    eval y i
  eval' (Catch x y) i = 
    eval x i >>= getJust (eval y i) λ n →
    return (just n)
  eval' (Block x) i = eval x B
  eval' (Unblock x) i = eval x U
  eval' Interrupt i = return nothing



---------------------
-- Target language --
---------------------


data Code : Set where
  PUSH : ℕ → Code → Code
  ADD : Code → Code
  POP : Code → Code
  THROW : Code
  RESET : Code → Code
  BLOCK : Code → Code
  UNBLOCK : Code → Code
  MARK : Code → Code → Code
  UNMARK : Code → Code
  HALT : Code

data Elem : Set where
  VAL : ℕ → Elem
  HAN : Code → Elem
  STA : Status → Elem


Stack : Set
Stack = List Elem


Conf : Set
Conf = Stack × Status

mutual
  exec : Code → Conf → ND Conf
  exec (PUSH n c) (s , i) = exec c (VAL n ∷ s , i) ⊕ inter s i
  exec (ADD c) (VAL n ∷ VAL m ∷ s , i) = exec c (VAL (m + n) ∷ s , i) ⊕ inter s i
  exec (POP c) (VAL _ ∷ s , i) = exec c (s , i) ⊕ inter s i
  exec THROW (s , i) = fail s i
  exec (RESET c) (VAL v ∷ STA i ∷ s , _) = exec c (VAL v ∷ s , i) ⊕ inter s i
  exec (BLOCK c) (s , i) = exec c (STA i ∷ s , B)
  exec (UNBLOCK c) (s , i) = exec c (STA i ∷ s , U)
  exec (UNMARK c) (VAL n ∷ HAN _ ∷ s , i) = exec c (VAL n ∷ s , i)
  exec (MARK c' c) (s , i) = exec c (HAN c' ∷ s , i) ⊕ inter s i
  exec HALT c = return c
  exec _ _ = zero

  fail : Stack → Status → ND Conf
  fail (HAN c ∷ s) i = exec c (s , i)
  fail (VAL m ∷ s) i = fail s i
  fail (STA i ∷ s) _ = fail s i
  fail _ _ = zero

  inter : Stack → Status → ND Conf
  inter s U = fail s U
  inter s B = zero


--------------
-- Compiler --
--------------


comp : Expr → Code → Code
comp (Val n) c = PUSH n c
comp (Add x y) c = comp x (comp y (ADD c))
comp (Seqn x y) c = (comp x (POP (comp y c)))
comp Throw c = THROW
comp (Block x) c = BLOCK (comp x (RESET c))
comp (Unblock x) c = UNBLOCK (comp x (RESET c))
comp (Catch x y) c = MARK (comp y c) (comp x (UNMARK c))

-----------------
-- Calculation --
-----------------


-- some lemmas that we will use during the calculation

lemma-inter : ∀ s c i →
  (interrupt i >>= getJust (fail s i) λ v →
  exec c (VAL v ∷ s , i))
  ~ inter s i
lemma-inter _ _  U = ~refl
lemma-inter _ _  B = ~refl

mutual
  pos-eval : ∀ e i → ∃[ v ] eval e i ⇓ v
  pos-eval e i = pos-plus-l ( pos-eval' e i)
  pos-eval' : ∀ e i → ∃[ v ] eval' e i ⇓ v
  pos-eval' (Val x) i = pos-ret
  pos-eval' (Add x y) i = pos-bind (eval x i) (pos-eval x i)
    λ m → pos-getJust (ret nothing) m pos-ret  λ n → pos-bind (eval y i) ( pos-eval y i)
    λ n → pos-getJust (ret nothing) n pos-ret ( λ v → pos-ret)
  pos-eval' Throw i = pos-ret
  pos-eval' (Catch x y) i = pos-bind (eval x i) ( pos-eval x i)
    λ m → pos-getJust (eval y i)  m (pos-eval y i) λ _ → pos-ret
  pos-eval' (Seqn x y) i = pos-bind (eval x i) ( pos-eval x i)
    λ m → pos-getJust (ret nothing) m  pos-ret (λ _ → pos-eval y i)
  pos-eval' (Block e) i =  pos-eval e B
  pos-eval' (Unblock e) i = pos-eval e U


fail-inter : ∀ s i → fail s i ⊕ inter s i ~ fail s i
fail-inter s U = plus-idem (fail s U)
fail-inter s B = plus-unit-r 



-- Each case of the calculation will start with the following

eval-eval' : ∀ e s c i →
     (eval e i >>= getJust (fail s i) λ v →
      exec c (VAL v ∷ s , i))
  ~ ((eval' e i >>= getJust (fail s i) λ v →
      exec c (VAL v ∷ s , i))
  ⊕ inter s i)
eval-eval' e s c i =
  (eval e i >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i))
  ~⟨⟩
  (eval' e i ⊕ interrupt i >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i))
  ~⟨⟩
  (eval' e i >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i))
  ⊕ (interrupt i >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i))
  ~⟨ plus-cong-r  (lemma-inter s c i) ⟩
  (eval' e i >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i))
  ⊕ inter s i
  ∎

-- Some of the cases will move the inter term inside as follows

distr-inter : ∀ e s c i →
 (eval' e i >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i))
  ⊕ inter s i
      ~   (eval' e i >>= getJust (fail s i) λ v →
           exec c (VAL v ∷ s , i) ⊕ inter s i)
distr-inter e s c i =
  (eval' e i >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i))
  ⊕ inter s i
  ~⟨ getJust-interchange (pos-eval' e i) ⟩
  (eval' e i >>= getJust (fail s i ⊕ inter s i) λ v →
   exec c (VAL v ∷ s , i) ⊕ inter s i)
  ~⟨ getJust-cong-default (eval' e i) (fail-inter s i) ⟩
  (eval' e i >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i) ⊕ inter s i)
  ∎


-- This is the compiler correctness property. This is where the main
-- calculation happens.

spec : ∀ e {s c i} →
     (eval e i >>= getJust (fail s i) λ v →
      exec c (VAL v ∷ s , i))
         ~ exec (comp e c) (s , i)
spec (Val n) {s} {c} {i} =
  (eval (Val n) i >>=
  getJust (fail s i) (λ v → exec c (VAL v ∷ s , i)))
  ~⟨ eval-eval' ( Val n) s c i ⟩
  (return (just n) >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i)) ⊕ inter s i
  ~⟨⟩
  exec c (VAL n ∷ s , i) ⊕ inter s i
  ~⟨⟩
  exec (PUSH n c) (s , i)
  ∎
spec (Add x y) {s} {c} {i} =
  (eval (Add x y) i >>=
  getJust (fail s i) (λ v → exec c (VAL v ∷ s , i)))
  ~⟨ eval-eval' (Add x y) s c i ⟩
  ((eval x i >>= getJust (return nothing) λ m →
    eval y i >>= getJust (return nothing) λ n →
    return (just (m + n)))
     >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i)) ⊕ inter s i
  ~⟨ distr-inter (Add x y) s c i ⟩
  ((eval x i >>= getJust (return nothing) λ m →
    eval y i >>= getJust (return nothing) λ n →
    return (just (m + n)))
     >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i) ⊕ inter s i)
  ~⟨  getJust-assoc (eval x i) ⟩
    ((eval x i >>= getJust (fail s i) (λ m →
           eval y i >>= getJust (return nothing) (λ n →
           return (just (m + n)))
      >>= getJust (fail s i) λ v →
    exec c (VAL v ∷ s , i) ⊕ inter s i)))
  ~⟨ getJust-cong (eval x i) ( λ m →  getJust-assoc (eval y i)) ⟩
    (eval x i >>= getJust (fail s i) λ m →
     eval y i >>= getJust (fail s i) λ n →
    exec c (VAL (m + n) ∷ s , i) ⊕ inter s i)
  ~⟨⟩
    (eval x i >>= getJust (fail s i) λ m →
     eval y i >>= getJust (fail (VAL m ∷ s) i) λ n →
    exec (ADD c) (VAL n ∷ VAL m ∷ s , i))
  ~⟨ getJust-cong (eval x i) ( λ m →  spec y) ⟩
    (eval x i >>= getJust (fail s i) λ m →
    exec (comp y (ADD c)) (VAL m ∷ s , i))
  ~⟨ spec x ⟩
  exec (comp x (comp y (ADD c))) (s , i)
  ∎
spec Throw {s} {c} {i} =
 (eval Throw i >>= getJust (fail s i) λ v →
  exec c (VAL v ∷ s , i))
 ~⟨ eval-eval' Throw s c i ⟩
  fail s i ⊕ inter s i
 ~⟨ fail-inter s i ⟩
  fail s i
 ~⟨⟩ 
  exec THROW (s , i)
  ∎

spec (Catch x y) {s} {c} {i} =
  (eval (Catch x y) i >>=
  getJust (fail s i) (λ v → exec c (VAL v ∷ s , i)))
  ~⟨ eval-eval' (Catch x y) s c i  ⟩
  ((eval x i >>= getJust (eval y i) λ n →
    return (just n)) >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i)) ⊕ inter s i
  ~⟨ plus-cong-l ( getJust-assoc (eval x i)) ⟩ 
  (eval x i >>= getJust
    (eval y i >>= getJust (fail s i) λ v →
     exec c (VAL v ∷ s , i))
    λ n →  exec c (VAL n ∷ s , i)) ⊕ inter s i
  ~⟨ plus-cong-l (getJust-cong-default (eval x i) (spec y)) ⟩
  (eval x i >>= getJust
    (exec (comp y c) (s , i))
    λ n →  exec c (VAL n ∷ s , i)) ⊕ inter s i
  ~⟨⟩
  (eval x i >>= getJust
    (fail (HAN (comp y c) ∷ s) i)
    λ n →  exec (UNMARK c) (VAL n ∷ HAN (comp y c) ∷ s , i)) ⊕ inter s i
  ~⟨ plus-cong-l (spec x) ⟩
  (exec (comp x (UNMARK c)) (HAN (comp y c) ∷ s , i)) ⊕ inter s i
  ~⟨⟩
  exec (MARK (comp y c) (comp x (UNMARK c))) (s , i)
  ∎
spec (Seqn x y) {s} {c} {i} =
 (eval (Seqn x y) i >>= getJust (fail s i) λ v →
  exec c (VAL v ∷ s , i))
 ~⟨ eval-eval' (Seqn x y) s c i ⟩
   ((eval x i >>= getJust (return nothing) λ m →
    eval y i) >>= getJust (fail s i) λ v →
           exec c (VAL v ∷ s , i)) ⊕ inter s i
 ~⟨ plus-cong-l (getJust-assoc (eval x i)) ⟩ 
   (eval x i >>= getJust (fail s i) λ m →
    eval y i >>= getJust (fail s i) λ v →
    exec c (VAL v ∷ s , i)) ⊕ inter s i
 ~⟨ plus-cong-l (getJust-cong (eval x i) λ m → spec y) ⟩ 
   (eval x i >>= getJust (fail s i) λ m →
    exec (comp y c) (s , i)) ⊕ inter s i
 ~⟨ getJust-interchange (pos-eval x i) ⟩ 
   (eval x i >>= getJust (fail s i ⊕ inter s i) λ m →
    exec (comp y c) (s , i) ⊕ inter s i)
 ~⟨ getJust-cong-default ( eval x i) (fail-inter s i) ⟩ 
   (eval x i >>= getJust (fail s i) λ m →
    exec (comp y c) (s , i) ⊕ inter s i)
 ~⟨⟩ 
   (eval x i >>= getJust (fail s i) λ m →
     exec (POP (comp y c)) (VAL m ∷ s , i))
 ~⟨ spec x ⟩ 
  exec (comp x (POP (comp y c))) (s , i)
  ∎

spec (Block x) {s} {c} {i} =
  (eval (Block x) i >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i))
 ~⟨ eval-eval' (Block x) s c i ⟩
  (eval x B >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i)) ⊕ inter s i
 ~⟨ distr-inter (Block x) s c i ⟩
  (eval x B >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i) ⊕ inter s i)
 ~⟨⟩
  (eval x B >>= getJust (fail (STA i ∷ s) B) λ v →
   exec (RESET c) (VAL v ∷ STA i ∷ s , B))
 ~⟨ spec x ⟩
  exec (comp x (RESET c)) (STA i ∷ s , B)
 ~⟨⟩
  exec (BLOCK (comp x (RESET c))) (s , i)
  ∎
  
spec (Unblock x) {s} {c} {i} =
  (eval (Unblock x) i >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i))
 ~⟨ eval-eval' (Unblock x) s c i ⟩
  (eval x U >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i)) ⊕ inter s i
 ~⟨ distr-inter (Unblock x) s c i ⟩
  (eval x U >>= getJust (fail s i) λ v →
   exec c (VAL v ∷ s , i) ⊕ inter s i)
 ~⟨⟩
  (eval x U >>= getJust (fail (STA i ∷ s) U) λ v →
   exec (RESET c) (VAL v ∷ STA i ∷ s , U))
 ~⟨ spec x ⟩
  exec (comp x (RESET c)) (STA i ∷ s , U)
 ~⟨⟩
  exec (UNBLOCK (comp x (RESET c))) (s , i)
  ∎




------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e HALT

specCompile : ∀ s x i →
  (eval x i >>= getJust (fail s i) λ v →
   return (VAL v ∷ s , i))
  ~
  (exec (compile x) (s , i))
specCompile s x i =  spec x {s} {HALT} {i}
