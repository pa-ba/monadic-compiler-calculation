{-# OPTIONS --sized-types #-}

-- Here we give a separate proof that the virtual machine exec for the
-- lambda calculus is indeed well-defined.

module Terminating.LambdaException where

open import LambdaException hiding (_∎)

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Agda.Builtin.Nat
open import Data.Nat

open import Data.Product 
open import Data.List hiding (lookup)

-- Define the measure that is used to show that exec is well-founded

csize : Code → ℕ
csize (PUSH x c) =  suc (csize c)
csize (ADD c) =  suc (csize c)
csize (LOOKUP x c) = suc (csize c)
csize RET = 1
csize (APP c) = suc (csize c)
csize (ABS c c') = suc (csize c + csize c')
csize (MARK c c') = suc (csize c + csize c')
csize HALT = 1
csize THROW = 1
csize (ISNUM c) = suc (csize c)
csize (ISCLO c) = suc (csize c)
csize (UNMARK c) = suc (csize c)


ssize : Stack → ℕ
ssize [] = 0
ssize (VAL x ∷ s) =  ssize s
ssize (CLO c e ∷ s) =  csize c + ssize s
ssize (HAN c ∷ s) =  csize c + ssize s


fsize : Conf → ℕ
fsize (s , e) =  ssize s

-- We define exec' which is a variant of exec with an explicit fuel
-- argument that ensures termination. We will show that exec' is
-- equivalen to exec. The size measure defined above defines exactly
-- how much fuel we have to provide.
mutual
  exec' : ∀ {i} → ℕ → Code → Conf → Partial Conf i
  exec' 0 _ _ = never
  exec' (suc j) (PUSH n c) (s , e) = exec' j c (VAL (Num' n) ∷ s , e)
  exec' (suc j) (ADD c) (VAL (Num' n) ∷ VAL (Num' m) ∷ s , e) = exec' j c (VAL (Num' (m + n)) ∷ s , e)
  exec' (suc j) (ADD c) (VAL _ ∷ s , e) = fail' j s e
  exec' (suc j) (LOOKUP n c) (s , e) = do v <- lookup n e
                                          exec' j c (VAL v ∷ s , e)
  exec' (suc j) (ISNUM c) (VAL (Num' n) ∷ s , e) = exec' j c (VAL (Num' n) ∷ s , e)
  exec' (suc j) (ISNUM c) (VAL _ ∷ s , e) = fail' j s  e
  exec' (suc j) (ISCLO c) (VAL (Clo' c' e' ) ∷ s , e) = exec' j c (VAL (Clo' c' e') ∷ s , e)
  exec' (suc j) (ISCLO c) (VAL _ ∷ s , e) = fail' j s  e
  exec' (suc j) RET  (VAL u ∷ CLO c e' ∷ s , _) = exec' j c (VAL u ∷ s , e')
  exec' _ (APP c) (VAL v ∷ VAL (Clo' c' e') ∷ s , e) = later (∞exec' c' (CLO c e ∷ s , v ∷ e'))
  exec' (suc j) (ABS c' c) (s , e) = exec' j c (VAL (Clo' c' e) ∷ s , e)
  exec' (suc j) (UNMARK c) (VAL v ∷ HAN c' ∷ s , e) = exec' j c (VAL v ∷ s , e)
  exec' (suc j) (MARK c' c) (s , e) = exec' j c (HAN c' ∷ s , e)
  exec' (suc j) THROW (s , e) = fail' j s e
  exec' _ HALT c = return c
  exec' _ _ _ = never


  ∞exec' : ∀ {i} → Code → Conf → ∞Partial Conf i
  force (∞exec' c e) = exec' (csize c + fsize e) c e

  fail' : ∀ {i} → ℕ → Stack → Env' → Partial Conf i
  fail' j (VAL _ ∷ s) e = fail' j s e
  fail' j (CLO _ e' ∷ s) e = fail' j s e'
  fail' j (HAN c ∷ s) e = exec' j c (s , e)
  fail' _ _ _ = never


open ≤-Reasoning

-- Finally we show that exec' is equivalent to exec.

mutual
  execBisim : ∀ c e i → (j : ℕ) → (csize c + fsize e ≤ j) → exec c e ~[ i ] exec' j c e
  execBisim c e zero _ le =  ~izero
  execBisim (PUSH x c) (s , e) (suc i) _ (s≤s le) = execBisim c _ _ _  le
  execBisim (ADD c) ([] , e) (suc i) _ (s≤s le) =  ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ [] , e) (suc i) _ (s≤s le) =  ~irefl
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (Num' x₁) ∷ s , e) (suc i) (suc j) (s≤s le) =
    execBisim c ((VAL (Num' (x₁ + x)) ∷ s), e) _ j le
  execBisim (ADD c) (VAL (Num' x) ∷ VAL (Clo' x₁ x₂) ∷ s , e) (suc i) (suc j) (s≤s le) =
    failBisim s e _ j ( m+n≤o⇒n≤o (csize c) le)
  execBisim (ADD c) (VAL (Num' x) ∷ CLO x₁ x₂ ∷ s , e) (suc i) (suc j) (s≤s le) =
    failBisim (CLO x₁ x₂ ∷ s) e _ j ((m+n≤o⇒n≤o (csize c) le))
  execBisim (ADD c) (VAL (Num' x) ∷ HAN x₁ ∷ s , e) (suc i) (suc j) (s≤s le) =
    failBisim (HAN x₁ ∷ s) e _ j (m+n≤o⇒n≤o (csize c) le)
  execBisim (ADD c) (VAL (Clo' x x₁) ∷ s , e) (suc i) _ (s≤s le) = failBisim s _ _ _ (m+n≤o⇒n≤o _ le)
  execBisim (ADD c) (CLO x x₁ ∷ s , e) (suc i) _ (s≤s le) = ~irefl
  execBisim (ADD c) (HAN x ∷ s , e) (suc i) _ (s≤s le) = ~irefl
  execBisim (LOOKUP x c) (s , e) (suc i) _ (s≤s le) =  bind-cong-r (lookup x e) (λ v →  execBisim c _ _ _  le)
  execBisim RET ([] , e) (suc i) _ (s≤s le) =  ~irefl
  execBisim RET (HAN x ∷ s , e) (suc i) _ (s≤s le) = ~irefl
  execBisim RET (VAL x ∷ [] , e) (suc i) _ (s≤s le) = ~irefl
  execBisim RET (VAL x ∷ VAL x₁ ∷ s , e) (suc i) _ (s≤s le) = ~irefl
  execBisim RET (VAL x ∷ HAN x₁ ∷ s , e) (suc i) _ (s≤s le) = ~irefl
  execBisim RET (VAL x ∷ CLO c x₂ ∷ s , e) (suc i) _ (s≤s le) =  execBisim c _ _ _ le
  execBisim RET (CLO x x₁ ∷ s , e) (suc i) _ (s≤s le) = ~irefl
  execBisim (APP c) ([] , e) (suc i) _ (s≤s le) = ~irefl
  execBisim (APP c) (HAN x ∷ s , e) (suc i) _ (s≤s le) = ~irefl
  execBisim (APP c) (VAL x ∷ [] , e) (suc i) _ (s≤s le) = ~irefl
  execBisim (APP c) (VAL x ∷ VAL (Num' x₁) ∷ s , e) (suc i) _ (s≤s le) =  ~irefl
  execBisim (APP c) (VAL x ∷ VAL (Clo' c' x₂) ∷ s , e) (suc i) (suc j) (s≤s le) = ~ilater ( ∞execBisim c' _ _)
  execBisim (APP c) (VAL x ∷ CLO x₁ x₂ ∷ s , e) (suc i) _ (s≤s le) = ~irefl
  execBisim (APP c) (VAL x ∷ HAN x₁ ∷ s , e) (suc i) _ (s≤s le) = ~irefl
  execBisim (APP c) (CLO x x₁ ∷ s , e) (suc i) _ (s≤s le) = ~irefl
  execBisim (ABS c c') (s , e) (suc i) (suc j) (s≤s le) = execBisim c' _ _ j (lemma (csize c') (ssize s) (csize c) j le)
    where lemma : ∀ a b c j → c + a + b ≤ j → a + b ≤ j
          lemma a b c j le = begin
                             a + b
                             ≤⟨ m≤n+m (a + b) c ⟩
                             c + (a + b)
                             ≡˘⟨  +-assoc c a b ⟩
                             c + a + b
                             ≤⟨  le ⟩
                             j 
                             ∎
  execBisim (ISNUM c) ([] , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (ISNUM c) (VAL (Num' x₁) ∷ s , e) (suc i) (suc j) (s≤s le) = execBisim c _ _ j le
  execBisim (ISNUM c) (VAL (Clo' x₁ x₂) ∷ s , e) (suc i) (suc j) (s≤s le) = failBisim s e _ _ ( m+n≤o⇒n≤o (csize c) le)
  execBisim (ISNUM c) (CLO x₁ x₂ ∷ s , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (ISNUM c) (HAN x₁ ∷ s , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (ISCLO c) ([] , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (ISCLO c) (VAL (Num' x₁) ∷ s , e) (suc i) (suc j) (s≤s le) = failBisim s e _ _ ( m+n≤o⇒n≤o (csize c) le)
  execBisim (ISCLO c) (VAL (Clo' x₁ x₂) ∷ s , e) (suc i) (suc j) (s≤s le) = execBisim c _ _ j le
  execBisim (ISCLO c) (CLO x₁ x₂ ∷ s , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (ISCLO c) (HAN x₁ ∷ s , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (UNMARK c) ([] , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (UNMARK c) (VAL x ∷ [] , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (UNMARK c) (VAL x ∷ VAL x₁ ∷ s , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (UNMARK c) (VAL x ∷ CLO x₁ x₂ ∷ s , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (UNMARK c) (VAL x ∷ HAN x₁ ∷ s , e) (suc i) (suc j) (s≤s le) = execBisim c _ _ j (lemma {csize c} le)
    where lemma : ∀ {a} {b} {c} {n} → a + (b + c) ≤ n → a + c ≤ n
          lemma {a} {b} {c} {n} le =
            begin
            a + c
            ≤⟨ +-mono-≤ (≤-refl {a})  (m≤n+m c b)  ⟩
            a + (b + c)
            ≤⟨  le ⟩
            n
            ∎

  execBisim (UNMARK c) (CLO x x₁ ∷ s , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (UNMARK c) (HAN x ∷ s , e) (suc i) (suc j) (s≤s le) = ~irefl
  execBisim (MARK c c') (s , e) (suc i) (suc j) (s≤s le) =  execBisim c' _ _ j (lemma {csize c} le)
    where lemma : ∀ {a} {b} {c} {n} → a + b + c ≤ n → b + (a + c) ≤ n
          lemma {a} {b} {c} {n} le =
            begin
            b + (a + c)
            ≡˘⟨ +-assoc b a c  ⟩
            (b + a) + c
            ≡⟨  cong₂ _+_ (+-comm b a) refl ⟩
            a + b + c
            ≤⟨  le ⟩
            n
            ∎

  execBisim THROW (s , e) (suc i) (suc j) (s≤s le) = failBisim s e _ _  le
  execBisim HALT (s , e) (suc i) _ (s≤s le) =  ~irefl
  
  ∞execBisim : ∀ c e i → force (∞exec c e) ~[ i ] force (∞exec' c e)
  ∞execBisim c e i =  execBisim c _ _ (csize c + fsize e) ≤-refl

  failBisim : ∀ s e i → (j : ℕ) → (ssize s ≤ j) → fail s e ~[ i ] fail' j s e
  failBisim [] e i j le = ~irefl
  failBisim (VAL x ∷ s) e i j le =  failBisim s e i j le
  failBisim (CLO c e' ∷ s) e i j le =  failBisim s e' i _ (m+n≤o⇒n≤o (csize c) le)
  failBisim (HAN c ∷ s) e i j le =  execBisim c (s , e) i j le

-- This shows that exec is bisimilar to exec'

bisim : ∀ c e →  exec c e ~ exec' (csize c + fsize e) c e
bisim c e = stepped _ _  λ i → execBisim c e i (csize c + fsize e) ≤-refl
