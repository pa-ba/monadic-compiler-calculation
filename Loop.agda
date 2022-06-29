{-# OPTIONS --copatterns --sized-types #-}

------------------------------------------------------------------------
-- Calculation for the simple arithmetic language with a degenerate
-- loop primitive
------------------------------------------------------------------------

module Loop where

open import Partial
open import Data.Nat
open import Data.Product 
open import Data.List

---------------------
-- Source language --
---------------------

data Expr : Set where
  Val : ℕ -> Expr
  Add : Expr -> Expr -> Expr
  Loop : Expr


mutual
  eval : ∀ {i} → Expr → Partial ℕ i
  eval (Val x) = return x
  eval (Add x y) =
    do n ← eval x
       m ← eval y
       return (n + m)
  eval Loop = later (∞eval Loop)

  ∞eval : ∀ {i} → Expr → ∞Partial ℕ i
  force (∞eval x) = eval x
  
---------------------
-- Target language --
---------------------


data Code : Set where
  PUSH : ℕ -> Code -> Code
  ADD : Code -> Code
  LOOP : Code
  HALT : Code

Stack : Set
Stack = List ℕ


mutual
  exec : ∀ {i} → Code → Stack → Partial Stack i
  exec (PUSH n c) s = exec c (n ∷ s)
  exec (ADD c) (n ∷ m ∷ s) = exec c ((m + n) ∷ s)
  exec LOOP s = later (∞exec LOOP s)
  exec HALT s = return s
  exec _ _ = never

  ∞exec : ∀ {i} → Code → Stack → ∞Partial Stack i
  force (∞exec e x) = exec e x

--------------
-- Compiler --
--------------


comp : Expr → Code → Code
comp (Val n) c =  PUSH n c
comp (Add x y) c = comp x (comp y (ADD c))
comp Loop c = LOOP




-----------------
-- Calculation --
-----------------

-- This is the compiler correctness property in its indexed
-- bisimilarity form. This is where the calculation happens.


spec : ∀ i x {s c} →
  (do v ← eval x
      exec c (v ∷ s))
  ~[ i ]
  (exec (comp x c) s)
spec zero _ =  ~izero
spec i (Val x) {s} {c} =
  (eval (Val x) >>= (λ v → exec c (v ∷ s)))
  ~⟨⟩
  (exec (comp (Val x) c) s)
  ∎
spec i (Add x y) {s} {c} =
  (eval (Add x y) >>= (\ v → exec c (v ∷ s)))
  ~⟨⟩
  (do v <- (do n ← eval x
               m ← eval y
               return (n + m))
      exec c (v ∷ s))
  ~⟨  bind-assoc (eval x) ⟩
  (do n ← eval x
      v <- (do m ← eval y
               return (n + m))
      exec c (v ∷ s))
  ~⟨  bind-cong-r (eval x) (\ n -> bind-assoc (eval y)) ⟩
  (do n ← eval x
      m ← eval y
      v <- (return (n + m))
      exec c (v ∷ s))
  ~⟨⟩
  (do n ← eval x
      m ← eval y
      exec c ((n + m) ∷ s))
  ~⟨⟩
  (do n ← eval x
      m ← eval y
      exec (ADD c) (m ∷ n ∷ s))
  ~⟨  bind-cong-r (eval x) (\ n' → spec i  y)  ⟩
  (do n ← eval x
      exec (comp y (ADD c)) (n ∷ s))
  ~⟨ spec i x ⟩
    exec (comp x (comp y (ADD c))) s
  ∎
spec (suc j) Loop {s} {c} =
  (eval Loop >>= \ v → exec c (v ∷ s))
  ~⟨⟩
  (later (∞eval Loop ∞>>= \ v → exec c (v ∷ s)))
  ~⟨ ~ilater (spec j Loop {c = c}) ⟩
  later (∞exec (comp Loop c) s)
  ~⟨⟩
  exec LOOP s
  ∎


-- Here we lift the correctness property into its non-indexed form
-- (i.e. in terms of bisimilarity).

spec' : ∀ s c x →
  (do v ← eval x
      exec c (v ∷ s))
  ~
  (exec (comp x c) s)
spec' s c x =  stepped _ _  (λ n → spec n x)



------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e HALT

specCompile : ∀ s x →
  (do v ← eval x
      return (v ∷ s))
  ~
  (exec (compile x) s)
specCompile s x =  spec' s HALT x
