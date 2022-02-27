{-# OPTIONS --copatterns --sized-types #-}

------------------------------------------------------------------------
-- Calculation for the interrupts language extended with a degenerate
-- loop primitive to demonstrate reasoning about languages with both
-- non-termination and non-determinism.
------------------------------------------------------------------------


module InterruptsLoop where

open import PartialNonDeterm public
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
  Loop : Expr

Value : Set
Value = Maybe ℕ

data Status : Set where
  U : Status
  B : Status


interrupt : ∀ {i} → Status → PND Value i
interrupt U = return nothing
interrupt B = zero

mutual
  eval : ∀ {i} → Expr → Status → PND Value i
  eval e i = eval' e i ⊕ interrupt i
  
  eval' : ∀ {i} → Expr → Status → PND Value i
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
  eval' Throw i = return nothing
  eval' Loop i = eval∞ Loop i

  eval∞ : ∀ {i} → Expr → Status → PND Value i
  eval∞ x s = later (∞eval x s)

  ∞eval : ∀ {i} → Expr → Status → ∞PND Value i
  force (∞eval x s) = eval x s

  
---------------------
-- Target language --
---------------------


data Code : Set where
  PUSH : ℕ → Code → Code
  ADD : Code → Code
  INTER : Code → Code
  POP : Code → Code
  THROW : Code
  RESET : Code → Code
  BLOCK : Code → Code
  UNBLOCK : Code → Code
  MARK : Code → Code → Code
  UNMARK : Code → Code
  LOOP : Code
  HALT : Code


data Elem : Set where
  VAL : ℕ → Elem
  HAN : Code → Elem
  STA : Status → Elem


Stack : Set
Stack = List Elem


Conf : Set
Conf = Stack × Status

-- We use the TERMINATING pragma since Agda does not recognize that
-- `exec` is terminating. We prove that `exec` is terminating
-- separately in the `Terminating.InterruptsLoop` module.

{-# TERMINATING #-}
mutual
  exec : ∀ {i} → Code → Conf → PND Conf i
  exec (PUSH n c) (s , i) = exec c (VAL n ∷ s , i) ⊕ inter s i
  exec (ADD c) (VAL n ∷ VAL m ∷ s , i) = exec c (VAL (m + n) ∷ s , i)
  exec (INTER c) (s , i) = exec c (s , i) ⊕ inter s i
  exec (POP c) (VAL _ ∷ s , i) = exec c (s , i)
  exec THROW (s , i) = fail s i
  exec (RESET c) (VAL v ∷ STA i ∷ s , _) = exec c (VAL v ∷ s , i)
  exec (BLOCK c) (s , i) = exec c (STA i ∷ s , B) ⊕ inter s i
  exec (UNBLOCK c) (s , i) = exec c (STA i ∷ s , U) ⊕ inter s i
  exec (UNMARK c) (VAL n ∷ HAN _ ∷ s , i) = exec c (VAL n ∷ s , i)
  exec (MARK c' c) (s , i) = exec c (HAN c' ∷ s , i) ⊕ inter s i
  exec LOOP (s , i) = later(∞exec LOOP (s , i)) ⊕ inter s i
  exec HALT c = return c
  exec _ _ = zero

  ∞exec : ∀ {i} → Code → Conf → ∞PND Conf i
  force (∞exec c x) = exec c x


  fail : ∀ {i} → Stack → Status → PND Conf i
  fail (HAN c ∷ s) i = exec c (s , i)
  fail (VAL m ∷ s) i = fail s i
  fail (STA i ∷ s) _ = fail s i
  fail _ _ = zero

  inter : ∀ {i} → Stack → Status → PND Conf i
  inter s U = fail s U
  inter s B = zero


--------------
-- Compiler --
--------------


comp : Expr → Code → Code
comp (Val n) c = PUSH n c
comp (Add x y) c = INTER (comp x (comp y (ADD c)))
comp (Seqn x y) c = INTER (comp x (POP (comp y c)))
comp Throw c = THROW
comp (Block x) c = BLOCK (comp x (RESET c))
comp (Unblock x) c = UNBLOCK (comp x (RESET c))
comp (Catch x y) c = MARK (comp y c) (comp x (UNMARK c))
comp Loop c = LOOP


-----------------
-- Calculation --
-----------------

-- some lemmas that we will use during the calculation

lemma-inter : ∀ {i} s c b →
  (interrupt b >>= getJust (fail s b) λ v →
  exec c (VAL v ∷ s , b))
  ~[ i ] inter s b
lemma-inter _ _  U = ~irefl
lemma-inter _ _  B = ~irefl


fail-inter : ∀ {i} s b → (fail s b ⊕ inter s b) ~[ i ] fail s b
fail-inter s U = plus-idem (fail s U)
fail-inter s B = plus-unit-r 


-- Each case of the calculation will start with the following

eval-eval' : ∀ {i} e s c b →
     (eval e b >>= getJust (fail s b) λ v →
      exec c (VAL v ∷ s , b))
  ~[ i ] ((eval' e b >>= getJust (fail s b) λ v →
      exec c (VAL v ∷ s , b))
  ⊕ inter s b)
eval-eval' e s c b =
  (eval e b >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b))
  ~⟨⟩
  (eval' e b ⊕ interrupt b >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b))
  ~⟨⟩
  (eval' e b >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b))
  ⊕ (interrupt b >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b))
  ~⟨ plus-cong-r  (lemma-inter s c b) ⟩
  ((eval' e b >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b))
  ⊕ inter s b)
  ∎



-- This is the compiler correctness property in its i-bisimilarity
-- form. This is where the calculation happens.


spec : ∀ i e {s c b} →
     (eval e b >>= getJust (fail s b) λ v →
      exec c (VAL v ∷ s , b))
         ~[ i ] exec (comp e c) (s , b)
spec zero _ =  ~izero
spec i (Val n){s} {c} {b} =
  (eval (Val n) b >>=
  getJust (fail s b) (λ v → exec c (VAL v ∷ s , b)))
  ~⟨ eval-eval' ( Val n) s c b ⟩
  (return (just n) >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b)) ⊕ inter s b
  ~⟨⟩
  exec c (VAL n ∷ s , b) ⊕ inter s b
  ~⟨⟩
  exec (PUSH n c) (s , b)
  ∎
spec i (Add x y) {s} {c} {b} =
  (eval (Add x y) b >>=
  getJust (fail s b) (λ v → exec c (VAL v ∷ s , b)))
  ~⟨ eval-eval' (Add x y) s c b ⟩
  ((eval x b >>= getJust (return nothing) λ m →
    eval y b >>= getJust (return nothing) λ n →
    return (just (m + n)))
     >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b)) ⊕ inter s b
  ~⟨  plus-cong-l (getJust-assoc (eval x b)) ⟩
    (eval x b >>= getJust (fail s b) (λ m →
           eval y b >>= getJust (return nothing) (λ n →
           return (just (m + n)))
      >>= getJust (fail s b) λ v →
    exec c (VAL v ∷ s , b))) ⊕ inter s b
  ~⟨ plus-cong-l (getJust-cong (eval x b) ( λ m →  getJust-assoc (eval y b))) ⟩
    (eval x b >>= getJust (fail s b) λ m →
     eval y b >>= getJust (fail s b) λ n →
    exec c (VAL (m + n) ∷ s , b))  ⊕ inter s b
  ~⟨⟩
   (eval x b >>= getJust (fail s b) λ m →
     eval y b >>= getJust (fail (VAL m ∷ s) b) λ n →
    exec (ADD c) (VAL n ∷ VAL m ∷ s , b)) ⊕ inter s b
  ~⟨ plus-cong-l (getJust-cong (eval x b) ( λ m →  spec i y)) ⟩
    (eval x b >>= getJust (fail s b) λ m →
     exec (comp y (ADD c)) (VAL m ∷ s , b)) ⊕ inter s b
  ~⟨ plus-cong-l (spec i x) ⟩
    exec (comp x (comp y (ADD c))) (s , b) ⊕ inter s b
  ~⟨⟩
  exec (INTER (comp x (comp y (ADD c)))) (s , b)
  ∎
  
spec i Throw {s} {c} {b} =
 (eval Throw b >>= getJust (fail s b) λ v →
  exec c (VAL v ∷ s , b))
 ~⟨ eval-eval' Throw s c b ⟩
  fail s b ⊕ inter s b
 ~⟨ fail-inter s b ⟩
  fail s b
 ~⟨⟩ 
  exec THROW (s , b)
  ∎

spec i (Catch x y) {s} {c} {b} =
  (eval (Catch x y) b >>=
  getJust (fail s b) (λ v → exec c (VAL v ∷ s , b)))
  ~⟨ eval-eval' (Catch x y) s c b  ⟩
  ((eval x b >>= getJust (eval y b) λ n →
    return (just n)) >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b)) ⊕ inter s b
  ~⟨ plus-cong-l ( getJust-assoc (eval x b)) ⟩ 
  (eval x b >>= getJust
    (eval y b >>= getJust (fail s b) λ v →
     exec c (VAL v ∷ s , b))
    λ n →  exec c (VAL n ∷ s , b)) ⊕ inter s b
  ~⟨ plus-cong-l (getJust-cong-default (eval x b) (spec i y)) ⟩
  (eval x b >>= getJust
    (exec (comp y c) (s , b))
    λ n →  exec c (VAL n ∷ s , b)) ⊕ inter s b
  ~⟨⟩
  (eval x b >>= getJust
    (fail (HAN (comp y c) ∷ s) b)
    λ n →  exec (UNMARK c) (VAL n ∷ HAN (comp y c) ∷ s , b)) ⊕ inter s b
  ~⟨ plus-cong-l (spec i x) ⟩
  (exec (comp x (UNMARK c)) (HAN (comp y c) ∷ s , b)) ⊕ inter s b
  ~⟨⟩
  exec (MARK (comp y c) (comp x (UNMARK c))) (s , b)
  ∎
spec i (Seqn x y) {s} {c} {b} =
 (eval (Seqn x y) b >>= getJust (fail s b) λ v →
  exec c (VAL v ∷ s , b))
 ~⟨ eval-eval' (Seqn x y) s c b ⟩
   ((eval x b >>= getJust (return nothing) λ m →
    eval y b) >>= getJust (fail s b) λ v →
           exec c (VAL v ∷ s , b)) ⊕ inter s b
 ~⟨ plus-cong-l (getJust-assoc (eval x b)) ⟩ 
   (eval x b >>= getJust (fail s b) λ m →
    eval y b >>= getJust (fail s b) λ v →
    exec c (VAL v ∷ s , b)) ⊕ inter s b
 ~⟨ plus-cong-l (getJust-cong (eval x b) λ m → spec i y) ⟩ 
   (eval x b >>= getJust (fail s b) λ m →
    exec (comp y c) (s , b)) ⊕ inter s b
 ~⟨⟩ 
   (eval x b >>= getJust (fail s b) λ m →
     exec (POP (comp y c)) (VAL m ∷ s , b)) ⊕ inter s b
 ~⟨ plus-cong-l (spec i x) ⟩ 
  exec (comp x (POP (comp y c))) (s , b) ⊕ inter s b
 ~⟨⟩ 
  exec (INTER (comp x (POP (comp y c)))) (s , b)
  ∎

spec i (Block x) {s} {c} {b} =
  (eval (Block x) b >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b))
 ~⟨ eval-eval' (Block x) s c b ⟩
  (eval x B >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b)) ⊕ inter s b
 ~⟨⟩
  (eval x B >>= getJust (fail (STA b ∷ s) B) λ v →
   exec (RESET c) (VAL v ∷ STA b ∷ s , B)) ⊕ inter s b
 ~⟨ plus-cong-l (spec i x) ⟩
  exec (comp x (RESET c)) (STA b ∷ s , B) ⊕ inter s b
 ~⟨⟩
  exec (BLOCK (comp x (RESET c))) (s , b)
  ∎
  
spec i (Unblock x) {s} {c} {b} =
  (eval (Unblock x) b >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b))
 ~⟨ eval-eval' (Unblock x) s c b ⟩
  (eval x U >>= getJust (fail s b) λ v →
   exec c (VAL v ∷ s , b)) ⊕ inter s b
 ~⟨⟩
  (eval x U >>= getJust (fail (STA b ∷ s) U) λ v →
   exec (RESET c) (VAL v ∷ STA b ∷ s , U)) ⊕ inter s b
 ~⟨ plus-cong-l (spec i x) ⟩
  exec (comp x (RESET c)) (STA b ∷ s , U) ⊕ inter s b
 ~⟨⟩
  exec (UNBLOCK (comp x (RESET c))) (s , b)
  ∎


spec (suc j) Loop {s} {c} {b} = 
  (eval Loop b >>= getJust (fail s b) λ v →
      exec c (VAL v ∷ s , b))
  ~⟨ eval-eval' Loop s c b ⟩
    (eval' Loop b >>= getJust (fail s b) λ v →
      exec c (VAL v ∷ s , b)) ⊕ inter s b
  ~⟨⟩
    (later (∞eval Loop b ∞>>= getJust (fail s b) λ v →
      exec c (VAL v ∷ s , b))) ⊕ inter s b
  ~⟨ plus-cong-l (~ilater ( spec j Loop {c = c})) ⟩
    (later (∞exec (comp Loop c) (s , b))) ⊕ inter s b
  ~⟨⟩
  (exec LOOP (s , b))
  ∎



-- Here we lift the correctness property into its non-indexed form
-- (i.e. in terms of bisimilarity).

spec' : ∀ e s c b →
  (eval e b >>= getJust (fail s b) λ v →
      exec c (VAL v ∷ s , b))
  ~ exec (comp e c) (s , b)
spec' e s c b =  stepped _ _  (λ i → spec i e)



------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e HALT

specCompile : ∀ e s b →
  (eval e b >>= getJust (fail s b) λ v →
      return (VAL v ∷ s , b))
  ~ exec (compile e) (s , b)
specCompile e s =  spec' e s HALT
