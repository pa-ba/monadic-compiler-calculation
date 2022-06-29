{-# OPTIONS --copatterns --sized-types #-}

------------------------------------------------------------------------
-- Calculation for call-by-value lambda calculus extended with
-- integers and exceptions (including exception handling).
--
-- In addition to the inclusion of exceptions, we also change the
-- semantics slightly: A type error (e.g. trying to add a number to a
-- closure) now results in an exception instead of divergence. This
-- was chosen to illustrate how the reasoning changes if we have two
-- different ways of representing failure. Divergence is still used in
-- case of an unbound variable.
--
------------------------------------------------------------------------


module LambdaException where


open import Partial public
open import Data.Nat
open import Data.Maybe hiding (_>>=_)
open import Agda.Builtin.Nat
open import Data.Bool
open import Data.Product 
open import Data.List hiding (lookup)
open import Function

---------------------
-- Source language --
---------------------


data Expr : Set where
  Val   : ℕ → Expr
  Add   : Expr → Expr → Expr
  Abs   : Expr → Expr
  App   : Expr → Expr → Expr
  Var   : ℕ → Expr
  Catch : Expr → Expr → Expr
  Throw : Expr

mutual
  data Value : Set where
    Num : ℕ → Value
    Clo : Expr → Env → Value

  Env : Set
  Env = List Value


-- The following two functions are used instead of partial pattern
-- matching. Agda supports an Idris-style pattern matching syntax
-- within the do notation, but that is useless for reasoning (see
-- https://agda.readthedocs.io/en/v2.6.2/language/lambda-abstraction.html)


lookup : ∀ {a i} → ℕ → List a → Partial a i
lookup 0 (x ∷ xs) = return x
lookup (suc i) (x ∷ xs) = lookup i xs
lookup _ _ = never


num : Maybe Value → Maybe ℕ
num (just (Num n)) = just n
num _ = nothing

getNum : ∀ {i A} → Partial A i → (ℕ → Partial A i) → Maybe Value → Partial A i
getNum = match num

clo : Maybe Value → Maybe (Expr × Env)
clo (just (Clo x e)) = just (x , e)
clo _ = nothing


getClo : ∀ {i A} → Partial A i → (Expr × Env → Partial A i) → Maybe Value → Partial A i
getClo = match clo

mutual
  eval : ∀ {i} → Expr → Env → Partial (Maybe Value) i
  eval (Val x) e = return (just (Num x))
  eval (Add x y) e =
    eval x e >>= getNum (return nothing) λ n →
    eval y e >>= getNum (return nothing) λ m →
    return (just (Num (n + m)))
  eval (Var i) e = do v ← lookup i e
                      return (just v)
  eval (Abs x)   e = return (just (Clo x e))
  eval (App x y) e = eval x e >>= getClo (return nothing) λ (x' , e') →
                     eval y e >>= getJust (return nothing) λ v →
                     later (∞eval x' (v ∷ e'))
  eval Throw _ = return nothing
  eval (Catch x y) e = eval x e >>= getJust (eval y e) λ v →
                       return (just v)

  ∞eval : ∀ {i} → Expr → Env → ∞Partial (Maybe Value) i
  force (∞eval x e) = eval x e

---------------------
-- Target language --
---------------------


data Code : Set where
  PUSH : ℕ → Code → Code
  ADD : Code → Code
  ISNUM : Code → Code
  ISCLO : Code → Code
  LOOKUP : ℕ → Code → Code
  RET : Code
  THROW : Code
  UNMARK : Code → Code
  MARK : Code → Code → Code
  APP : Code → Code
  ABS : Code → Code → Code
  HALT : Code

mutual
  data Value' : Set where
    Num' : ℕ → Value'
    Clo' : Code → Env' → Value'

  Env' : Set
  Env' = List Value'
  

data Elem : Set where
  VAL : Value' → Elem
  CLO : Code → Env' → Elem
  HAN : Code → Elem


Stack : Set
Stack = List Elem

Conf : Set
Conf = Stack × Env'

-- We use the TERMINATING pragma since Agda does not recognize that
-- `exec` is terminating. We prove that `exec` is terminating
-- separately in the `Terminating.LambdaException` module.

mutual
  {-# TERMINATING #-}
  exec : ∀ {i} → Code → Conf → Partial Conf i
  exec (PUSH n c) (s , e) = exec c (VAL (Num' n) ∷ s , e)
  exec (ADD c) (VAL (Num' n) ∷ VAL (Num' m) ∷ s , e) = exec c (VAL (Num' (m + n)) ∷ s , e)
  exec (ADD c) (VAL _ ∷ s , e) = fail s e
  exec (ISNUM c) (VAL (Num' n) ∷ s , e) = exec c (VAL (Num' n) ∷ s , e)
  exec (ISNUM c) (VAL _ ∷ s , e) = fail s  e
  exec (ISCLO c) (VAL (Clo' c' e' ) ∷ s , e) = exec c (VAL (Clo' c' e') ∷ s , e)
  exec (ISCLO c) (VAL _ ∷ s , e) = fail s  e
  exec (LOOKUP n c) (s , e) = do v <- lookup n e
                                 exec c (VAL v ∷ s , e)
  exec RET  (VAL u ∷ CLO c e' ∷ s , _) = exec c (VAL u ∷ s , e')
  exec (APP c) (VAL v ∷ VAL (Clo' c' e') ∷ s , e) = later (∞exec c' (CLO c e ∷ s , v ∷ e'))
  exec (ABS c' c) (s , e) = exec c (VAL (Clo' c' e) ∷ s , e)
  exec THROW (s , e) = fail s e
  exec (UNMARK c) (VAL v ∷ HAN c' ∷ s , e) = exec c (VAL v ∷ s , e)
  exec (MARK c' c) (s , e) = exec c (HAN c' ∷ s , e)
  exec HALT c = return c
  exec _ _ = never


  ∞exec : ∀ {i} → Code → Conf → ∞Partial Conf i
  force (∞exec c e) = exec c e

  fail : ∀ {i} → Stack → Env' → Partial Conf i
  fail (VAL _ ∷ s) e = fail s e
  fail (CLO _ e' ∷ s) e = fail s e'
  fail (HAN c ∷ s) e = exec c (s , e)
  fail _ _ = never

--------------
-- Compiler --
--------------

comp : Expr → Code → Code
comp (Val n) c =  PUSH n c
comp (Add x y) c = comp x (ISNUM (comp y (ADD c)))
comp (Var i) c = LOOKUP i c
comp (App x y) c = comp x (ISCLO (comp y (APP c)))
comp (Abs x) c = ABS (comp x RET) c
comp (Catch x y) c = (MARK (comp y c) (comp x (UNMARK c)))
comp Throw c = THROW




-----------------
-- Calculation --
-----------------


mutual
  conv : Value → Value'
  conv (Clo x' e') = Clo' (comp x' RET) (convE e')
  conv (Num n) = Num' n

  convE : Env → Env'
  convE [] = []
  convE (x ∷ xs) = conv x ∷ convE xs


-- This is the lemma that is used in the `Var` case.
lookup-conv : ∀ {i A} n e → (f : Value' → Partial A ∞) →
  (lookup n e >>= (f ∘ conv)) ~[ i ] (lookup n (convE e) >>= f)
lookup-conv zero (x ∷ e) f =  ~irefl
lookup-conv (suc n) (x ∷ e) f = lookup-conv n e f
lookup-conv (suc n) [] f =  ~itrans never-bind ( ~isymm never-bind)
lookup-conv zero [] f = ~itrans never-bind ( ~isymm never-bind)


-- This is the compiler correctness property in its indexed
-- bisimilarity form. This is where the calculation happens.


spec : ∀ i x {s c e} →
  (eval x e >>= getJust (fail s (convE e)) λ v →
   exec c (VAL (conv v) ∷ s , convE e))
  ~[ i ]
  (exec (comp x c) (s , convE e))
spec zero _ =  ~izero
spec i (Val x) {s} {c} {e}  =
  (eval (Val x) e >>= getJust (fail s (convE e)) λ v →
   exec c (VAL (conv v) ∷ s , convE e))
  ~⟨⟩
  (exec c (VAL (Num' x) ∷ s , convE e))
  ~⟨⟩
  (exec (comp (Val x) c) (s , convE e))
  ∎
spec i (Add x y) {s} {c} {e} =
    ((eval x e >>= getNum (return nothing) λ n →
      eval y e >>= getNum (return nothing) λ m →
      return (just (Num (n + m)))) >>= getJust (fail s (convE e)) λ v →
    exec c (VAL (conv v) ∷ s , convE e))
   ~⟨ match-assoc num (eval x e) ⟩
    (eval x e >>= getNum (fail s (convE e)) (λ n →
      eval y e >>= getNum (return nothing) (λ m →
      return (just (Num (n + m)))) >>= getJust (fail s (convE e)) λ v →
    exec c (VAL (conv v) ∷ s , convE e)))
   ~⟨ match-cong num (eval x e) ( λ _ → match-assoc num (eval y e)) ⟩
    (eval x e >>= getNum (fail s (convE e)) (λ n →
     eval y e >>= getNum (fail s (convE e)) (λ m →
     exec c (VAL (Num' (n + m)) ∷ s , convE e))))
   ~⟨⟩
    (eval x e >>= getNum (fail s (convE e)) (λ n →
     eval y e >>= getNum (fail s (convE e)) (λ m →
     exec (ADD c) (VAL (Num' m) ∷ VAL (Num' n) ∷ s , convE e))))
   ~⟨ match-cong num (eval x e) (
        λ n → bind-cong-r (eval y e) 
        λ {(just (Num n')) →  ~irefl ; (just (Clo _ _)) →  ~irefl ; nothing →  ~irefl}) ⟩
    (eval x e >>= getNum (fail s (convE e)) (λ n →
     eval y e >>= getJust (fail (VAL (Num' n) ∷ s) (convE e)) (λ m →
     exec (ADD c) (VAL (conv m) ∷ VAL (Num' n) ∷ s , convE e))))
   ~⟨  match-cong num (eval x e) ( λ n →  spec i y) ⟩
    (eval x e >>= getNum (fail s (convE e)) (λ n →
     exec (comp y (ADD c)) (VAL (Num' n) ∷ s , convE e)))
   ~⟨⟩
    (eval x e >>= getNum (fail s (convE e)) (λ n →
     exec (ISNUM (comp y (ADD c))) (VAL (Num' n) ∷ s , convE e)))
   ~⟨  bind-cong-r (eval x e) ( λ {nothing →  ~irefl ; (just (Clo _ _)) →  ~irefl ; (just (Num n)) →  ~irefl}) ⟩
    (eval x e >>= getJust (fail s (convE e)) (λ n →
     exec (ISNUM (comp y (ADD c))) (VAL (conv n) ∷ s , convE e)))
   ~⟨ spec i x ⟩
     (exec (comp x (ISNUM (comp y (ADD c)))) (s , convE e))
  ∎  

spec i (Var n) {s} {c} {e} =
  (eval (Var n) e >>= getJust (fail s (convE e)) λ v →
   exec c (VAL (conv v) ∷ s , convE e))
  ~⟨⟩
  ((do v ← lookup n e
       return (just v)) >>= getJust (fail s (convE e)) λ v →
   exec c (VAL (conv v) ∷ s , convE e))
  ~⟨  bind-assoc (lookup n e) ⟩
  (do v ← lookup n e
      exec c (VAL (conv v) ∷ s , convE e))
  ~⟨  lookup-conv n e _ ⟩
  (do v ← lookup n (convE e)
      exec c (VAL v ∷ s , convE e))
  ~⟨⟩
  (exec (LOOKUP n c) (s , convE e))
  ∎

spec i@(suc j) (App x y) {s} {c} {e} =
  (eval (App x y) e >>= getJust (fail s (convE e)) λ v →
   exec c (VAL (conv v) ∷ s , convE e))
  ~⟨⟩
  ((eval x e >>= getClo (return nothing) λ (x' , e') →
    eval y e >>= getJust (return nothing) λ v →
    later (∞eval x' (v ∷ e'))) >>= getJust (fail s (convE e)) λ w →
   exec c (VAL (conv w) ∷ s , convE e))
  ~⟨ match-assoc clo (eval x e) ⟩
  (eval x e >>= getClo (fail s (convE e)) (λ (x' , e') →
   eval y e >>= getJust (return nothing) (λ v →
    later (∞eval x' (v ∷ e'))) >>= getJust (fail s (convE e)) λ w →
   exec c (VAL (conv w) ∷ s , convE e)))
  ~⟨ match-cong clo (eval x e) ( λ c → match-assoc id (eval y e)) ⟩
  (eval x e >>= getClo (fail s (convE e)) λ (x' , e') →
   eval y e >>= getJust (fail s (convE e)) λ v →
    later (∞eval x' (v ∷ e')) >>= getJust (fail s (convE e)) λ w →
   exec c (VAL (conv w) ∷ s , convE e))
  ~⟨⟩
  (eval x e >>= getClo (fail s (convE e)) λ (x' , e') →
   eval y e >>= getJust (fail s (convE e)) λ v →
    later (∞eval x' (v ∷ e')) >>= getJust (fail (CLO c (convE e) ∷ s) (convE (v ∷ e'))) λ w →
    exec RET (VAL (conv w) ∷ CLO c (convE e) ∷ s , convE (v ∷ e')))
  ~⟨ match-cong clo (eval x e) ( λ (x' , e') → match-cong id (eval y e) λ v →  ~ilater ( spec j x') ) ⟩
  (eval x e >>= getClo (fail s (convE e)) λ (x' , e') →
   eval y e >>= getJust (fail s (convE e)) λ v →
   later (∞exec (comp x' RET) (CLO c (convE e) ∷ s , convE (v ∷ e'))))
  ~⟨⟩
  (eval x e >>= getClo (fail s (convE e)) λ (x' , e') →
   eval y e >>= getJust (fail (VAL (Clo' (comp x' RET) (convE e')) ∷ s) (convE e)) λ v →
   exec (APP c) (VAL (conv v) ∷ VAL (Clo' (comp x' RET) (convE e')) ∷ s , convE e))
  ~⟨  match-cong clo (eval x e) ( λ _ →  spec i y) ⟩
  (eval x e >>= getClo (fail s (convE e)) λ (x' , e') →
   exec (comp y (APP c)) (VAL (Clo' (comp x' RET) (convE e')) ∷ s , convE e))
  ~⟨⟩
  (eval x e >>= getClo (fail s (convE e)) λ (x' , e') →
   exec (ISCLO (comp y (APP c))) (VAL (Clo' (comp x' RET) (convE e')) ∷ s , convE e))
  ~⟨ bind-cong-r (eval x e) (λ { (just (Num _)) → ~irefl; (just (Clo x' e')) →  ~irefl; nothing → ~irefl })⟩
  (eval x e >>= getJust (fail s (convE e)) λ v →
   exec (ISCLO (comp y (APP c))) (VAL (conv v) ∷ s , convE e))
  ~⟨ spec i x ⟩
  (exec (comp x (ISCLO (comp y (APP c)))) (s , convE e))
  ∎


spec i (Abs x) {s} {c} {e} =
  (exec c (VAL (Clo' (comp x RET) (convE e)) ∷ s , convE e))
  ~⟨⟩ -- definition of exec (ABS c) 
  (exec (ABS (comp x RET) c) (s , convE e))
  ∎

spec i Throw {s} {c} {e} =
  (return nothing >>= getJust (fail s (convE e)) λ v →
   exec c (VAL (conv v) ∷ s , convE e))
  ~⟨⟩
  (fail s (convE e))
  ~⟨⟩
  (exec THROW (s , convE e))
  ∎

spec i (Catch x y) {s} {c} {e} =
  ((eval x e >>= getJust (eval y e) λ v →
    return (just v)) >>= getJust (fail s (convE e)) λ v →
   exec c (VAL (conv v) ∷ s , convE e))
  ~⟨  match-assoc id (eval x e) ⟩
  (eval x e >>= getJust (eval y e >>= getJust (fail s (convE e)) λ v →
                          exec c (VAL (conv v) ∷ s , convE e))
    λ v → exec c (VAL (conv v) ∷ s , convE e))
  ~⟨ match-cong-default id (eval x e) ( spec i y) ⟩
  (eval x e >>= getJust (exec (comp y c) (s , convE e))
    λ v → exec c (VAL (conv v) ∷ s , convE e))
  ~⟨⟩
  (eval x e >>= getJust (fail (HAN (comp y c) ∷ s) (convE e))
    λ v → exec c (VAL (conv v) ∷ s , convE e))
  ~⟨⟩
  (eval x e >>= getJust (fail (HAN (comp y c) ∷ s) (convE e))
    λ v → exec (UNMARK c) (VAL (conv v) ∷ HAN (comp y c) ∷ s , convE e))
  ~⟨ spec i x ⟩
  (exec (comp x (UNMARK c)) (HAN (comp y c) ∷ s , convE e))
  ~⟨⟩
  (exec (MARK (comp y c) (comp x (UNMARK c))) (s , convE e))
  ∎


-- Here we lift the correctness property into its non-indexed form
-- (i.e. in terms of bisimilarity).

spec' : ∀ s c e x →
  (eval x e >>= getJust (fail s (convE e)) λ v →
   exec c (VAL (conv v) ∷ s , convE e))
  ~
  (exec (comp x c) (s , convE e))
spec' s c e x =  stepped _ _  (λ i → spec i x)



------------------------
-- top-level compiler --
------------------------

compile : Expr → Code
compile e = comp e HALT


specCompile : ∀ s x →
  (eval x [] >>= getJust (fail s []) λ v →
   return (VAL (conv v) ∷ s , []))
  ~
  (exec (compile x) (s , []))
specCompile s x = spec' s HALT [] x
