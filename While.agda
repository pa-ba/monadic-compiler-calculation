{-# OPTIONS --copatterns --sized-types #-}

------------------------------------------------------------------------
-- Calculation for a simple arithmetic language with a while loop
------------------------------------------------------------------------


module While where

open import Partial
open import Data.Nat
open import Agda.Builtin.Nat
open import Data.Bool
open import Data.Product 
open import Data.List


---------------------
-- Source language --
---------------------


data Expr : Set where
  Val : ℕ -> Expr
  Add : Expr -> Expr -> Expr
  While : Expr -> Expr


mutual
  eval : ∀ {i} → Expr → Partial ℕ i
  eval (Val x) = return x
  eval (Add x y) =
    do n ← eval x
       m ← eval y
       return (n + m)
  eval (While x) = do n <- eval x
                      if n == 0 then eval' (While x) else return n

  eval' : ∀ {i} →  Expr → Partial ℕ i
  eval' x = later (∞eval x)

  ∞eval : ∀ {i} → Expr → ∞Partial ℕ i
  force (∞eval x) = eval x

  
---------------------
-- Target language --
---------------------


data Code : Set where
  PUSH : ℕ -> Code -> Code
  ADD : Code -> Code
  LABEL : Code -> Code
  JMP : Code -> Code
  HALT : Code


data Elem : Set where
  VAL : ℕ → Elem
  WHILE : Code → Elem

Stack : Set
Stack = List Elem


mutual
  exec : ∀ {i} → Code → Stack → Partial Stack i
  exec (PUSH n c) s = exec c (VAL n ∷ s)
  exec (ADD c) (VAL n ∷ VAL m ∷ s) = exec c (VAL (m + n) ∷ s)
  exec (JMP c) (VAL n ∷ WHILE c' ∷ s) = if n == 0 then (exec' c' s) else exec c (VAL n ∷ s)
  exec (LABEL c) s = exec c (WHILE (LABEL c) ∷ s)
  exec HALT s = return s
  exec _ _ = never


  exec' : ∀ {i} → Code → Stack → Partial Stack i
  exec' e x = later (∞exec e x)

  ∞exec : ∀ {i} → Code → Stack → ∞Partial Stack i
  force (∞exec e x) = exec e x



--------------
-- Compiler --
--------------

comp : Expr → Code → Code
comp (Val n) c =  PUSH n c
comp (Add x y) c = comp x (comp y (ADD c))
comp (While x) c = LABEL (comp x (JMP c))



-----------------
-- Calculation --
-----------------


-- This is the compiler correctness property in its i-bisimilarity
-- form. This is where the calculation happens.

spec : ∀ i x {s c} →
  (do v ← eval x
      exec c (VAL v ∷ s))
  ~[ i ]
  (exec (comp x c) s)
spec zero _ =  ~izero
spec i (Val x) {s} {c} =
  (eval (Val x) >>= (λ v → exec c (VAL v ∷ s)))
  ~⟨⟩
  (exec (comp (Val x) c) s)
  ∎
spec i (Add x y) {s} {c} =
  (eval (Add x y) >>= (\ v → exec c (VAL v ∷ s)))
  ~⟨⟩
  (do v <- (do n ← eval x
               m ← eval y
               return (n + m))
      exec c (VAL v ∷ s))
  ~⟨  bind-assoc (eval x) ⟩
  (do n ← eval x
      v <- (do m ← eval y
               return (n + m))
      exec c (VAL v ∷ s))
  ~⟨  bind-cong-r (eval x) (\ n -> bind-assoc (eval y)) ⟩
  (do n ← eval x
      m ← eval y
      v <- (return (n + m))
      exec c (VAL v ∷ s))
  ~⟨⟩
  (do n ← eval x
      m ← eval y
      exec c (VAL (n + m) ∷ s))
  ~⟨⟩
  (do n ← eval x
      m ← eval y
      exec (ADD c) (VAL m ∷ VAL n ∷ s))
  ~⟨  bind-cong-r (eval x) (\ n' → spec i y)  ⟩
  (do n ← eval x
      exec (comp y (ADD c)) (VAL n ∷ s))
  ~⟨ spec i x ⟩
    (exec (comp x (comp y (ADD c))) s)
  ∎
spec i@(suc j) (While x) {s} {c} =
  (do v ← (do n <- eval x
              if n == 0 then eval' (While x) else return n)
      exec c (VAL v ∷ s))
  ~⟨ bind-assoc (eval x) ⟩
  (do n <- eval x
      v ← if n == 0 then eval' (While x) else return n
      exec c (VAL v ∷ s))
  ~⟨  bind-cong-r (eval x) (\ n → if-bind (n == 0)) ⟩
  (do n <- eval x
      if (n == 0)
        then ( later (∞eval (While x) ∞>>= \ v →  exec c (VAL v ∷ s)))
        else exec c (VAL n ∷ s))
  ~⟨  bind-cong-r (eval x) (\ n → if-then-cong (n == 0) (~ilater (spec j (While x)))) ⟩
  (do n <- eval x
      if (n == 0)
        then later (∞exec (comp (While x) c) s)
        else exec c (VAL n ∷ s))
  ~⟨⟩
  (do n <- eval x
      exec (JMP c) (VAL n ∷ WHILE (comp (While x) c) ∷ s))
  ~⟨ spec i x ⟩
  (exec (comp x (JMP c)) (WHILE (comp (While x) c) ∷ s))
  ~⟨⟩
  (exec (LABEL (comp x (JMP c))) s)
  ∎


-- Here we lift the correctness property into its non-indexed form
-- (i.e. in terms of bisimilarity).


spec' : ∀ s c x →
  (do v ← eval x
      exec c (VAL v ∷ s))
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
      return (VAL v ∷ s))
  ~
  (exec (compile x) s)
specCompile s x =  spec' s HALT x
