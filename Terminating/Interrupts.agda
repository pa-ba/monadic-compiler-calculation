{-# OPTIONS --sized-types #-}

-- Here we give a separate proof that the virtual machine exec for the
-- interrupts language is indeed well-defined.

module Terminating.Interrupts where

open import Interrupts hiding (_∎)

open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Agda.Builtin.Nat
open import Data.Nat

open import Data.Product 
open import Data.List

-- Define the measure that is used to show that exec is well-founded

csize : Code → ℕ
csize (PUSH x c) =  suc (csize c)
csize (ADD c) =  suc (csize c)
csize (POP c) =  suc (csize c)
csize THROW = 1
csize (RESET c) =  suc (csize c)
csize (BLOCK c) =  suc (csize c)
csize (UNBLOCK c) =  suc (csize c)
csize (UNMARK c) = suc (csize c)
csize (MARK c c') = suc (csize c + csize c')
csize HALT = 1


ssize : Stack → ℕ
ssize [] = 0
ssize (VAL x ∷ s) =  ssize s
ssize (STA _ ∷ s) =  ssize s
ssize (HAN c ∷ s) =  csize c + ssize s



fsize : Conf → ℕ
fsize (s , e) =  ssize s



-- We define exec' which is a variant of exec with an explicit fuel
-- argument that ensures termination. We will show that exec' is
-- equivalen to exec. The size measure defined above defines exactly
-- how much fuel we have to provide.

mutual
  exec' : ℕ → Code → Conf → ND Conf
  exec' 0 _ _ = zero
  exec' (suc j) (PUSH n c) (s , i) = exec' j c (VAL n ∷ s , i) ⊕ inter' j s i
  exec' (suc j) (ADD c) (VAL n ∷ VAL m ∷ s , i) = exec' j c (VAL (m + n) ∷ s , i) ⊕ inter' j s i
  exec' (suc j) (POP c) (VAL _ ∷ s , i) = exec' j c (s , i) ⊕ inter' j s i
  exec' (suc j) THROW (s , i) = fail' j s i
  exec' (suc j) (RESET c) (VAL v ∷ STA i ∷ s , _) = exec' j c (VAL v ∷ s , i) ⊕ inter' j s i
  exec' (suc j) (BLOCK c) (s , i) = exec' j c (STA i ∷ s , B)
  exec' (suc j) (UNBLOCK c) (s , i) = exec' j c (STA i ∷ s , U)
  exec' (suc j) (UNMARK c) (VAL n ∷ HAN _ ∷ s , i) = exec' j c (VAL n ∷ s , i)
  exec' (suc j) (MARK c' c) (s , i) = exec' j c (HAN c' ∷ s , i) ⊕ inter' j s i
  exec' _ HALT c = return c
  exec' _ _ _ = zero

  fail' : ℕ → Stack → Status → ND Conf
  fail' j (HAN c ∷ s) i = exec' j c (s , i)
  fail' j (VAL m ∷ s) i = fail' j s i
  fail' j (STA i ∷ s) _ = fail' j s i
  fail' _ _ _ = zero

  inter' : ℕ → Stack → Status → ND Conf
  inter' j s U = fail' j s U
  inter' _ s B = zero


open ≤-Reasoning

-- Finally we show that exec' is equivalent to exec.

mutual
  execBisim : ∀ c e → (j : ℕ) → (csize c + fsize e ≤ j) → exec c e ~ exec' j c e
  execBisim (PUSH x c) (s , i) (suc n) (s≤s le)
    = plus-cong (execBisim c _ _ le) (interBisim s i n (m+n≤o⇒n≤o _ le))
  execBisim (ADD c) ([] , i) .(suc _) (s≤s le) = ~refl
  execBisim (ADD c) (VAL x ∷ [] , i) .(suc _) (s≤s le) = ~refl
  execBisim (ADD c) (HAN x ∷ [] , i) .(suc _) (s≤s le) = ~refl
  execBisim (ADD c) (STA x ∷ [] , i) .(suc _) (s≤s le) = ~refl
  execBisim (ADD c) (VAL x ∷ VAL x₁ ∷ s , i) .(suc _) (s≤s le)
    = plus-cong (execBisim c _ _ le) (interBisim s i _ (m+n≤o⇒n≤o _ le))
  execBisim (ADD c) (VAL x ∷ HAN x₁ ∷ s , i) .(suc _) (s≤s le) = ~refl
  execBisim (ADD c) (VAL x ∷ STA x₁ ∷ s , i) .(suc _) (s≤s le) = ~refl
  execBisim (ADD c) (HAN x ∷ y ∷ s , i) .(suc _) (s≤s le) = ~refl
  execBisim (ADD c) (STA x ∷ y ∷ s , i) .(suc _) (s≤s le) = ~refl
  execBisim (POP c) ([] , i) .(suc _) (s≤s le) = ~refl
  execBisim (POP c) (VAL x ∷ s , i) .(suc _) (s≤s le)
    = plus-cong (execBisim c _ _ le) (interBisim s i _ (m+n≤o⇒n≤o _ le))
  execBisim (POP c) (HAN x ∷ s , i) .(suc _) (s≤s le) = ~refl
  execBisim (POP c) (STA x ∷ s , i) .(suc _) (s≤s le) = ~refl
  execBisim THROW (s , i) (suc n) (s≤s le) = failBisim s i n le
  execBisim (RESET c) ([] , i) .(suc _) (s≤s le) = ~refl
  execBisim (RESET c) (VAL x ∷ [] , i) .(suc _) (s≤s le) = ~refl
  execBisim (RESET c) (VAL x ∷ VAL x₁ ∷ s , i) .(suc _) (s≤s le) = ~refl
  execBisim (RESET c) (VAL x ∷ HAN x₁ ∷ s , i) .(suc _) (s≤s le) = ~refl
  execBisim (RESET c) (VAL x ∷ STA y ∷ s , i) (suc n) (s≤s le)
    = plus-cong (execBisim c _ _ le) (interBisim s y n (m+n≤o⇒n≤o _ le))
  execBisim (RESET c) (HAN x ∷ s , i) .(suc _) (s≤s le) = ~refl
  execBisim (RESET c) (STA x ∷ s , i) .(suc _) (s≤s le) = ~refl
  execBisim (BLOCK c) (s , i) (suc n) (s≤s le) = execBisim c (STA i ∷ s , B) n le
  execBisim (UNBLOCK c) (s , i) (suc n) (s≤s le) = execBisim c (STA i ∷ s , U) n le
  execBisim (MARK c c') (s , i) (suc n) (s≤s le)
    =  plus-cong (execBisim c' _ n  ( lemma {csize c} le)) (interBisim s i n (m+n≤o⇒n≤o _ le))
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

  execBisim (UNMARK c) ([] , i) (suc n) (s≤s le) = ~refl
  execBisim (UNMARK c) (VAL x ∷ [] , i) (suc n) (s≤s le) = ~refl
  execBisim (UNMARK c) (VAL x ∷ VAL x₁ ∷ s , i) (suc n) (s≤s le) = ~refl
  execBisim (UNMARK c) (VAL x ∷ HAN x₁ ∷ s , i) (suc n) (s≤s le)
    =  execBisim c (VAL x ∷ s , i) n ( lemma {csize c} le)
    where lemma : ∀ {a} {b} {c} {n} → a + (b + c) ≤ n → a + c ≤ n
          lemma {a} {b} {c} {n} le =
            begin
            a + c
            ≤⟨ +-mono-≤ (≤-refl {a})  (m≤n+m c b)  ⟩
            a + (b + c)
            ≤⟨  le ⟩
            n
            ∎

  execBisim (UNMARK c) (VAL x ∷ STA x₁ ∷ s , i) (suc n) (s≤s le) = ~refl
  execBisim (UNMARK c) (HAN x ∷ s , i) (suc n) (s≤s le) = ~refl
  execBisim (UNMARK c) (STA x ∷ s , i) (suc n) (s≤s le) = ~refl
  execBisim HALT e .(suc _) (s≤s le) = ~refl

  interBisim : ∀ s i → (j : ℕ) → (ssize s ≤ j) → inter s i ~ inter' j s i
  interBisim s U j le = failBisim s U j le
  interBisim s B j le = ~refl
  
  failBisim : ∀ s i → (j : ℕ) → (ssize s ≤ j) → fail s i ~ fail' j s i
  failBisim [] i j le = ~refl
  failBisim (VAL x ∷ s) i j le = failBisim s i j le
  failBisim (HAN c ∷ s) i j le = execBisim c (s , i) j le
  failBisim (STA x ∷ s) i j le = failBisim s x j le
