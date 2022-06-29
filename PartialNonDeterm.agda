{-# OPTIONS --copatterns --sized-types #-}

------------------------------------------------------------------------
-- This module defines the monad that combines the partiality and the
-- non-determinism monad. In addition, it defines strong bisimilarity
-- and proves the monad laws and all reasoning priciples we need for
-- our calculation proofs.
------------------------------------------------------------------------

module PartialNonDeterm where

open import Size public

open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Bool hiding (_≤_; _<_; _≤?_)
open import Category.Monad public
open import Category.Monad.Indexed public
open import Level renaming (zero to lzero; suc to lsuc) public
open import Data.Maybe renaming (_>>=_ to _M>>=_)
open import Function
open import Relation.Nullary

mutual
  data PND (A : Set) (i : Size) : Set where
    now   : A → PND A i
    zero  : PND A i
    _⊕_   : PND A i → PND A i → PND A i
    later : ∞PND A i → PND A i

  record ∞PND (A : Set) (i : Size) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → PND A j


infixr 6 _~⟨_⟩_
infixr 6 _~⟨⟩_
infix 6 _~[_]_
infixl 7 _⊕_
infix 5 _⇓[_]_
infix 5 _⇓_
infix 5 _⇑[_]
infix 5 _⇓[_]
infix 5 _⇑
infix 5 _⇓

open ∞PND public

-- Indexed convergence to a value.
data _⇓[_]_ {A : Set} : PND A ∞ → ℕ → A → Set where
  iconv-now : ∀{i} → (x : A) → now x ⇓[ i ] x
  iconv-l : ∀{i} {p} {x} → p ⇓[ i ] x → (q : PND A ∞) → p ⊕ q ⇓[ i ] x
  iconv-r : ∀{i} {q} {x} → (p : PND A ∞) → q ⇓[ i ] x → p ⊕ q ⇓[ i ] x
  iconv-later :  ∀{i} → {v : A} → {p : ∞PND A ∞} → force p ⇓[ i ] v → later p ⇓[ suc i ] v

-- Indexed divergence
data _⇑[_] {A : Set} : PND A ∞ → ℕ → Set where
  idiv-zero : ∀ (p : PND A ∞) → p ⇑[ 0 ]
  idiv-l : ∀ {i}  {p : PND A ∞} → p ⇑[ i ] → (q : PND A ∞) → p ⊕ q ⇑[ i ]
  idiv-r : ∀ {i}  {q : PND A ∞} → (p : PND A ∞) → q ⇑[ i ] → p ⊕ q ⇑[ i ]
  idiv-suc :  ∀{i} → {p : ∞PND A ∞} → force p ⇑[ i ] → later p ⇑[ suc i ]

-- Indexed non-divergence
data _⇓[_] {A : Set} : PND A ∞ → ℕ → Set where
  iconv-now' : ∀ {i} (x : A) → now x ⇓[ i ]
  iconv-zero : ∀ {i} → zero ⇓[ i ]
  iconv-plus : ∀ {i}  {p q : PND A ∞} → p ⇓[ i ] → q ⇓[ i ] → p ⊕ q ⇓[ i ]
  iconv-later' :  ∀{i} → {p : ∞PND A ∞} → force p ⇓[ i ] → later p ⇓[ suc i ]


module Bind where
  mutual
    _>>=_ : ∀ {i A B} → PND A i → (A → PND B i) → PND B i
    now   x >>= f = f x
    (later x) >>= f = later (x ∞>>= f)
    zero >>= f = zero
    (p ⊕ q) >>= f = (p >>= f) ⊕ (q >>= f)

    _∞>>=_ :  ∀ {i A B} → ∞PND A i → (A → PND B i) → ∞PND B i
    force (x ∞>>= f) = force x >>= f

delayMonad : ∀ {i} → RawMonad {f = lzero} (λ A → PND A i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  } where open Bind


module _ {i : Size} where
  open module PartialMonad = RawMonad (delayMonad {i = i}) 
                           public renaming (_⊛_ to _<*>_)

open Bind public using (_∞>>=_)

-- (non-indexed) convergence to a value
data _⇓_ {A : Set} : PND A ∞ → A → Set where
  conv-now : (x : A) → now x ⇓ x
  conv-l : ∀ {p} {x} → p ⇓ x → (q : PND A ∞) → p ⊕ q ⇓ x
  conv-r : ∀ {q} {x} → (p : PND A ∞) → q ⇓ x → p ⊕ q ⇓ x
  conv-later :  {v : A} → {p : ∞PND A ∞} → force p ⇓ v → (later p) ⇓ v

-- (non-indexed) divergence
mutual
  data _⇑ {i : Size} {A : Set} : PND A ∞ → Set where
    div-l : ∀  {p : PND A ∞} → p ⇑ → (q : PND A ∞) → p ⊕ q ⇑
    div-r : ∀  {q : PND A ∞} → (p : PND A ∞) → q ⇑ → p ⊕ q ⇑
    div-suc :  ∀ {p : ∞PND A ∞} → p ∞⇑ → later p ⇑

  record _∞⇑ {i : Size} {A : Set} (p : ∞PND A ∞) : Set where
    coinductive
    constructor ⇑delay
    field
      ⇑force : {j : Size< i} → _⇑ {j} (force p)

open _∞⇑ public


-- (non-indexed) non-divergence
data _⇓ {i : Size} {A : Set} : PND A ∞ → Set where
  conv-now' : (x : A) → now x ⇓
  conv-zero : zero ⇓
  conv-plus : ∀  {p q : PND A ∞} → p ⇓ → q ⇓ → p ⊕ q ⇓
  conv-later' :{p : ∞PND A ∞} → force p ⇓ → (later p) ⇓


-- weak bisimilarity
record _~_  {A : Set} (p q : PND A ∞) : Set where
  constructor mk~
  field
    ~conv-l : ∀ {v} → p ⇓ v → q ⇓ v
    ~conv-r : ∀ {v} → q ⇓ v → p ⇓ v
    ~div-l : p ⇓ → q ⇓
    ~div-r : q ⇓ → p ⇓
open _~_ public

-- strong indexed bisimilarity
record _~[_]_  {A : Set} (p : PND A ∞) (i : ℕ) (q : PND A ∞) : Set where
  constructor imk~
  field
    ~iconv-l : ∀ {v} {j} → j < i → p ⇓[ j ] v → q ⇓[ j ] v
    ~iconv-r : ∀ {v} {j} → j < i → q ⇓[ j ] v → p ⇓[ j ] v
    ~idiv-l : ∀ {j} → j < i → p ⇓[ j ] → q ⇓[ j ]
    ~idiv-r : ∀ {j} → j < i → q ⇓[ j ] → p ⇓[ j ]

open _~[_]_ public

-- basic properties of _~[_]_

~izero   : ∀ {A} {a b : PND A ∞} → a ~[ 0 ] b
~izero = imk~ (λ {()}) (λ {()}) (λ {()})  λ {()}

~irefl  : ∀ {i A} {a : PND A ∞} → a ~[ i ] a
~irefl = imk~ (λ l c → c) (λ l c → c) ( λ l c → c) λ l c → c

~itrans : ∀ {i A} {a b c : PND A ∞}
  (eq : a ~[ i ] b) (eq' : b ~[ i ] c) → a ~[ i ] c
~itrans eq eq' = imk~ ( λ le c → ~iconv-l eq' le (~iconv-l eq le c))
                      ( λ le c → ~iconv-r eq le (~iconv-r eq' le c))
                      ( λ le c → ~idiv-l eq' le (~idiv-l eq le c))
                      ( λ le c → ~idiv-r eq le (~idiv-r eq' le c))

~isymm : ∀ {i A} {a b : PND A ∞}
  (eq : a ~[ i ] b) → b ~[ i ] a
~isymm eq = imk~ (~iconv-r eq) (~iconv-l eq) (~idiv-r eq) (~idiv-l eq)


iconv-cong : ∀ {A} {i}{v} {p q p' q' : PND A ∞} →
  (p ⇓[ i ] v → p' ⇓[ i ] v) → (q ⇓[ i ] v → q' ⇓[ i ] v) → p ⊕ q ⇓[ i ] v → p' ⊕ q' ⇓[ i ] v
iconv-cong f g (iconv-l c _) =  iconv-l (f c) _
iconv-cong f g (iconv-r _ c) =  iconv-r _ (g c)

idiv-cong : ∀ {A} {i} {p q p' q' : PND A ∞} →
  (p ⇓[ i ] → p' ⇓[ i ]) → (q ⇓[ i ] → q' ⇓[ i ]) → p ⊕ q ⇓[ i ] → p' ⊕ q' ⇓[ i ]
idiv-cong f g (iconv-plus c c') = iconv-plus (f c) (g c')


plus-cong : ∀ {A} {i} {p q p' q' : PND A ∞} → p ~[ i ] p' → q ~[ i ] q' → p ⊕ q ~[ i ] p' ⊕ q'
plus-cong eq eq' = imk~ ( λ le → iconv-cong (~iconv-l eq le) (~iconv-l eq' le))
                        ( λ le → iconv-cong (~iconv-r eq le) (~iconv-r eq' le))
                        ( λ le → idiv-cong (~idiv-l eq le) (~idiv-l eq' le))
                        ( λ le → idiv-cong (~idiv-r eq le) (~idiv-r eq' le))

plus-cong-r : ∀ {A} {i} {p q q' : PND A ∞} → q ~[ i ] q' → p ⊕ q ~[ i ] p ⊕ q'
plus-cong-r eq = plus-cong ~irefl eq

plus-cong-l : ∀ {A} {i} {p q p' : PND A ∞} → p ~[ i ] p' → p ⊕ q ~[ i ] p' ⊕ q
plus-cong-l eq = plus-cong  eq ~irefl

iconv-later-cong : ∀ {i} {A} {p q : ∞PND A ∞} {v : A} → (force p ⇓[ i ] v → force q ⇓[ i ] v)
  →  later p ⇓[ suc i ] v → later q ⇓[ suc i ] v
iconv-later-cong f (iconv-later c) = iconv-later (f c)

idiv-later-cong : ∀ {i} {A} {p q : ∞PND A ∞} → (force p ⇓[ i ] → force q ⇓[ i ])
  →  later p ⇓[ suc i ] → later q ⇓[ suc i ]
idiv-later-cong f (iconv-later' c) = iconv-later' (f c)




~ilater : ∀ {A} {i} {p q : ∞PND A ∞} → force p ~[ i ] force q → later p ~[ suc i ] later q
~ilater {A} {i} {p} {q} eq = imk~  (λ { {v} {suc j} (s≤s le) → iconv-later-cong (~iconv-l eq le)})
                                      (λ { {v} {suc j} (s≤s le) → iconv-later-cong (~iconv-r eq le)})
                                      (λ { {suc j} (s≤s le) → idiv-later-cong (~idiv-l eq le)})
                                      (λ { {suc j} (s≤s le) → idiv-later-cong (~idiv-r eq le)})


_~⟨_⟩_ : ∀ {A : Set} {i} (x : PND A ∞) → ∀ {y : PND A ∞} {z : PND A ∞} → x ~[ i ] y → y ~[ i ] z → x ~[ i ] z
_~⟨_⟩_ {_} x r eq =  ~itrans r eq

_~⟨⟩_ : ∀ {A : Set} {i} (x : PND A ∞) → ∀ {y : PND A ∞} → x ~[ i ] y → x ~[ i ] y
_~⟨⟩_  x eq = eq



_∎ : ∀ {A : Set} {i} (x : PND A ∞) → x ~[ i ] x
_∎  x = ~irefl


-- Proof of congruence over bind

iconv-upward : ∀ {i j A v} → {p : PND A ∞} →  i ≤ j → p ⇓[ i ] v → p ⇓[ j ] v
iconv-upward le (iconv-now v) =  iconv-now v
iconv-upward le (iconv-l c q) =  iconv-l (iconv-upward le c) q
iconv-upward le (iconv-r p c) = iconv-r p (iconv-upward le c)
iconv-upward (s≤s le) (iconv-later c) = iconv-later (iconv-upward le c)


bind-cong-conv : ∀ {i j A B} {a : PND A ∞} {f : A → PND B ∞} {v : A} {w : B}
  → (a ⇓[ i ] v) → f v ⇓[ j ] w → (a >>= f) ⇓[ i + j ] w
bind-cong-conv {i} {j} (iconv-now _) d =  iconv-upward (m≤n+m _ _) d
bind-cong-conv (iconv-l c q) d = iconv-l (bind-cong-conv c d) _
bind-cong-conv (iconv-r p c) d = iconv-r _ (bind-cong-conv c d)
bind-cong-conv (iconv-later c) d =  iconv-later (bind-cong-conv c  d)



bind-cong-conv' : ∀ {i A B} {a : PND A ∞} {f : A → PND B ∞} {w : B} 
                  → (a >>= f) ⇓[ i ] w → ∃[ v ] ∃[ i1 ] ∃[ i2 ] (i ≡ i1 + i2 × a ⇓[ i1 ] v × f v ⇓[ i2 ] w)
bind-cong-conv' {i} {a = now x} c =  x , 0 , i ,  refl , iconv-now x , c
bind-cong-conv' {a = a1 ⊕ a2} (iconv-l c .(a2 Bind.>>= _)) with bind-cong-conv' {a = a1} c
... | v' , i1 , i2 , eq , d1 , d2 =  v' , i1 , i2 , eq ,  iconv-l d1 a2 , d2
bind-cong-conv' {a = a1 ⊕ a2} (iconv-r .(a1 Bind.>>= _) c) with bind-cong-conv' {a = a2} c
... | v' , i1 , i2 , eq , d1 , d2 =  v' , i1 , i2 , eq ,  iconv-r a1 d1 , d2
bind-cong-conv' {a = later x} (iconv-later c) with bind-cong-conv' {a = force x} c
... | v' , i1 , i2 , refl , d1 , d2 = v' , suc i1 , i2 ,  refl , iconv-later d1 , d2



≤+suc : ∀ {i} i1 i2 → suc (i1 + i2) ≤ i →  i1 + suc i2 ≤ i
≤+suc i1 i2 le rewrite +-suc i1 i2 =  le

bind-cong-r : ∀ {i A B}  (a : PND A ∞)
              {k l : A → PND B ∞} (h : ∀ a → (k a) ~[ i ] (l a)) →
              (a >>= k) ~[ i ] (a >>= l)

bind-cong-r {i} {A} {B} a {k} {l} h = imk~ le1' ri1' (le2' a) (ri2' a)
  where le1' : {v : B} {j : ℕ} → j < i → (a >>= k) ⇓[ j ] v → (a >>= l) ⇓[ j ] v
        le1' le c with bind-cong-conv' {a = a} c
        ... | v' , i1 , i2 , refl , d1 , d2 = bind-cong-conv d1
                                              (~iconv-l (h v') (m+n≤o⇒n≤o _ (≤+suc i1 i2 le)) d2)
        ri1' : {v : B} {j : ℕ} → j < i → (a >>= l) ⇓[ j ] v → (a >>= k) ⇓[ j ] v
        ri1' le c with bind-cong-conv' {a = a} c
        ... | v' , i1 , i2 , refl , d1 , d2 = bind-cong-conv d1
                                              (~iconv-r (h v') (m+n≤o⇒n≤o _ (≤+suc i1 i2 le)) d2)                                              
        le2' : ∀ a → {j : ℕ} → j < i → (a >>= k) ⇓[ j ] → (a >>= l) ⇓[ j ]
        le2' (now x) le c = ~idiv-l  (h x) le c
        le2' (zero) le c = iconv-zero
        le2' (a1 ⊕ a2) le (iconv-plus c1 c2) = iconv-plus (le2' a1 le c1) (le2' a2 le c2)
        le2' (later x) (s≤s le) (iconv-later' c) = iconv-later' (le2' (force x) (≤-step le) c)
        ri2' : ∀ a → {j : ℕ} → j < i → (a >>= l) ⇓[ j ] → (a >>= k) ⇓[ j ]
        ri2' (now x) le c = ~idiv-r  (h x) le c
        ri2' (zero) le c = iconv-zero
        ri2' (a1 ⊕ a2) le (iconv-plus c1 c2) = iconv-plus (ri2' a1 le c1) (ri2' a2 le c2)
        ri2' (later x) (s≤s le) (iconv-later' c) = iconv-later' (ri2' (force x) (≤-step le) c)


----------------
-- monad laws --
----------------

bind-assoc : ∀{i A B C}(m : PND A ∞)
                 {k : A → PND B ∞}{l : B → PND C ∞} →
                 ((m >>= k) >>= l) ~[ i ] (m >>= λ a → k a >>= l)
bind-assoc (now x) =  ~irefl
bind-assoc zero =  ~irefl
bind-assoc (m ⊕ m') = plus-cong (bind-assoc  m) (bind-assoc m')
bind-assoc {zero} (later x) = ~izero
bind-assoc {suc i} (later x) = ~ilater (bind-assoc ( force x))


bind-unit-r : ∀ {A} {i} (p : PND A ∞)  → (p >>= now) ~[ i ] p
bind-unit-r (now x) =  ~irefl
bind-unit-r zero =  ~irefl
bind-unit-r (p ⊕ q) = plus-cong (bind-unit-r p) (bind-unit-r q)
bind-unit-r {i = zero} (later x) =  ~izero
bind-unit-r {i = suc i} (later x) = ~ilater (bind-unit-r (force x))

bind-unit-l : ∀ {A B} {i} {x : A} (f : A → PND B ∞)  → (now x >>= f) ~[ i ] f x
bind-unit-l p =  ~irefl


conv-stepped : ∀ {A} {i} {p : PND A ∞} {v} →  p ⇓[ i ] v → p ⇓ v
conv-stepped (iconv-now v) = conv-now v
conv-stepped (iconv-l c q) = conv-l (conv-stepped c) q
conv-stepped (iconv-r p c) = conv-r p (conv-stepped c)
conv-stepped (iconv-later c) = conv-later (conv-stepped c)


-- lemmas --

conv-plus-unit-l : ∀ {i} {A} {p : PND A ∞} {v : A} → zero ⊕ p ⇓[ i ] v → p ⇓[ i ] v
conv-plus-unit-l (iconv-r .zero c) = c

div-plus-unit-l : ∀ {i} {A} {p : PND A ∞} → zero ⊕ p ⇓[ i ] → p ⇓[ i ]
div-plus-unit-l (iconv-plus c c') = c'


conv-plus-unit-r : ∀ {i} {A} {p : PND A ∞} {v : A} → p ⊕ zero ⇓[ i ] v → p ⇓[ i ] v
conv-plus-unit-r (iconv-l c .zero) = c

div-plus-unit-r : ∀ {i} {A} {p : PND A ∞} → p ⊕ zero ⇓[ i ] → p ⇓[ i ]
div-plus-unit-r (iconv-plus c c') = c


conv-plus-assoc : ∀ {i} {A} {p q r : PND A ∞} {v : A} → p ⊕ q ⊕ r ⇓[ i ] v → p ⊕ (q ⊕ r) ⇓[ i ] v
conv-plus-assoc (iconv-l (iconv-l c _) _) = iconv-l c _
conv-plus-assoc (iconv-l (iconv-r _ c) _) = iconv-r _ (iconv-l c _)
conv-plus-assoc (iconv-r p c) =  iconv-r _ (iconv-r _ c)

conv-plus-assoc' : ∀ {i} {A} {p q r : PND A ∞} {v : A} → p ⊕ (q ⊕ r) ⇓[ i ] v → p ⊕ q ⊕ r ⇓[ i ] v
conv-plus-assoc' (iconv-l c _ ) = iconv-l (iconv-l c _) _
conv-plus-assoc' (iconv-r _ (iconv-l c _)) = iconv-l (iconv-r _ c) _
conv-plus-assoc' (iconv-r _ (iconv-r _ c)) = iconv-r _ c


div-plus-assoc : ∀ {i} {A} {p q r : PND A ∞} → p ⊕ q ⊕ r ⇓[ i ] → p ⊕ (q ⊕ r) ⇓[ i ]
div-plus-assoc (iconv-plus (iconv-plus c c₁) c') = iconv-plus c (iconv-plus c₁ c')

div-plus-assoc' : ∀ {i} {A} {p q r : PND A ∞} → p ⊕ (q ⊕ r) ⇓[ i ] → p ⊕ q ⊕ r ⇓[ i ]
div-plus-assoc' (iconv-plus c' (iconv-plus c c₁)) = iconv-plus (iconv-plus c' c) c₁

conv-plus-idem : ∀ {i} {A} {v : A} {p : PND A ∞} → p ⊕ p ⇓[ i ] v → p ⇓[ i ] v
conv-plus-idem (iconv-l c _) =  c
conv-plus-idem (iconv-r _ c) = c

conv-plus-idem' : ∀ {i} {A} {v : A} {p : PND A ∞} → p ⇓[ i ] v → p ⊕ p ⇓[ i ] v
conv-plus-idem' c = iconv-l c _


div-plus-idem : ∀ {i} {A} {p : PND A ∞} → p ⊕ p ⇓[ i ] → p ⇓[ i ]
div-plus-idem (iconv-plus c c₁) = c

div-plus-idem' : ∀ {i} {A} {p : PND A ∞} → p ⇓[ i ] → p ⊕ p ⇓[ i ]
div-plus-idem' c = iconv-plus c c 

conv-plus-comm : ∀ {i} {A} {v : A} {p q : PND A ∞} → p ⊕ q ⇓[ i ] v → q ⊕ p ⇓[ i ] v
conv-plus-comm (iconv-l c _) = iconv-r _ c
conv-plus-comm (iconv-r _ c) = iconv-l c _


div-plus-comm : ∀ {i} {A} {p q : PND A ∞} → p ⊕ q ⇓[ i ] → q ⊕ p ⇓[ i ]
div-plus-comm (iconv-plus c c₁) = iconv-plus c₁ c

--------------------------
-- non-determinism laws --
--------------------------

plus-unit-l : ∀ {i} {A} {p : PND A ∞} → zero ⊕ p ~[ i ] p
plus-unit-l = imk~ ( λ le →  conv-plus-unit-l) ( λ le c → iconv-r _ c)
                     ( λ le → div-plus-unit-l)  (λ le c → iconv-plus iconv-zero  c)


plus-unit-r : ∀ {i} {A} {p : PND A ∞} → p ⊕ zero ~[ i ] p
plus-unit-r = imk~ ( λ le →  conv-plus-unit-r) ( λ le c → iconv-l c _)
                     ( λ le → div-plus-unit-r)  (λ le c → iconv-plus c iconv-zero)

plus-assoc : ∀ {i} {A} {p q r : PND A ∞} → (p ⊕ q) ⊕ r ~[ i ] p ⊕ (q ⊕ r)
plus-assoc = imk~ ( λ le → conv-plus-assoc) ( λ le →  conv-plus-assoc')
                  ( λ le → div-plus-assoc)  ( λ le → div-plus-assoc')

plus-idem : ∀ {i} {A} (p : PND A ∞) → p ⊕ p ~[ i ] p
plus-idem p = imk~ ( λ le →  conv-plus-idem) ( λ le →  conv-plus-idem')
                   ( λ le →  div-plus-idem) ( λ le →  div-plus-idem')

plus-comm : ∀ {i} {A} {p q : PND A ∞} → p ⊕ q ~[ i ] q ⊕ p
plus-comm = imk~ (const conv-plus-comm) ( const conv-plus-comm) ( const div-plus-comm) ( const div-plus-comm)


plus-distr : ∀ {i} {A B} {p q : PND A ∞} {f : A → PND B ∞}  → ((p ⊕ q) >>= f) ~[ i ] (p >>= f) ⊕ (q >>= f)
plus-distr = ~irefl

zero-bind : ∀ {i} {A B} {f : A → PND B ∞} → (zero >>= f) ~[ i ] zero
zero-bind = ~irefl


-- The interchange law below does not hold (but it does in the
-- non-determinism monad without partiality). One can easily see why:
-- If p diverges, then the right-hand side has no converging
-- behaviour, whereas the left-hand side has all behaviours of q.

-- interchange : ∀ {i} {A B} {p : PND A ∞} {q : PND B ∞} {f : A → PND B ∞} → (∃[ v ] p ⇓[ i ] v)
--   → (p >>= f) ⊕ q ~[ i ] (p >>= λ x → f x ⊕ q)



-- lemmas --

stepped-conv : ∀ {A} {p : PND A ∞} {v} → p ⇓ v → ∃[ i ] p ⇓[ i ] v
stepped-conv (conv-now v) =  0 , iconv-now v 
stepped-conv (conv-l c q) with stepped-conv c
... | i , c' =  i , iconv-l  c'  q
stepped-conv (conv-r p c) with stepped-conv c
... | i , c' =  i , iconv-r p  c'
stepped-conv (conv-later c) with stepped-conv c
...| i , c' =  suc i , iconv-later c'

stepped1 : ∀ {A} (p q : PND A ∞) → (∀ {i} {v : A} → p ⇓[ i ] v → q ⇓[ i ] v) → {v : A} → p ⇓ v → q ⇓ v
stepped1 p q f c = conv-stepped (f (proj₂ (stepped-conv c)))


le-neg : ∀ i j → ¬ i ≤ j → j < i
le-neg zero j nle with nle z≤n
... | ()
le-neg (suc i) zero nle = s≤s z≤n
le-neg (suc i) (suc j) nle = s≤s (le-neg  i j (λ le → nle (s≤s le)))

conv-stepped' : ∀ {A} {i} {p : PND A ∞}  →  p ⇓[ i ] → p ⇓
conv-stepped' (iconv-now' x) = conv-now' x
conv-stepped' iconv-zero = conv-zero
conv-stepped' (iconv-plus x y) = conv-plus (conv-stepped' x) ( conv-stepped' y)
conv-stepped' (iconv-later' c) = conv-later' (conv-stepped'  c)

iconv-up : ∀ {A} {i j} {p : PND A ∞} → i ≤ j → p ⇓[ i ] → p ⇓[ j ]
iconv-up le (iconv-now' x) = iconv-now' x
iconv-up le iconv-zero = iconv-zero
iconv-up le (iconv-plus c c') = iconv-plus (iconv-up le c) (iconv-up le c')
iconv-up (s≤s le) (iconv-later' c) = iconv-later' (iconv-up le c)

stepped-conv' : ∀ {A} {p : PND A ∞} → p ⇓ → ∃[ i ] p ⇓[ i ]
stepped-conv' (conv-now' x) = zero , iconv-now' x
stepped-conv' conv-zero = zero , iconv-zero
stepped-conv' (conv-plus c c') with stepped-conv' c | stepped-conv' c'
... | i , d | j , d' with i ≤? j
... | no ¬p = i , iconv-plus d ( iconv-up (≤-trans ( n≤1+n _) (le-neg _ _  ¬p)) d')
... | yes p = j , iconv-plus ( iconv-up  p d) d'
stepped-conv' (conv-later' c) with stepped-conv' c
...| i , c' =  suc i ,  iconv-later' c'



stepped2 : ∀ {A} (p q : PND A ∞) → (∀ {i} → p ⇓[ i ] → q ⇓[ i ]) → p ⇓ → q ⇓
stepped2 p q f c = conv-stepped' (f ( proj₂ (stepped-conv' c)))



----------------------------------------------------
-- indexed bisimilarity implies weakbisimilairity --
----------------------------------------------------

stepped : ∀ {A} (p q : PND A ∞) →  (∀ i → p ~[ i ] q) → p ~ q
stepped p q s = mk~ (stepped1 p q λ {i} c → ~iconv-l (s ( suc i)) ≤-refl c)
                    (stepped1 q p λ {i} c → ~iconv-r (s ( suc i)) ≤-refl c)
                    (stepped2 p q λ {i} c →  ~idiv-l (s ( suc i)) (n<1+n _) c)
                    (stepped2 q p λ {i} c →  ~idiv-r (s ( suc i)) (n<1+n _) c)



-- Pattern matching


match : ∀ {A B C : Set} → (A → Maybe B) → PND C ∞ → (B → PND C ∞) → A → PND C ∞
match m d f a with m a
... | just x =  f x
... | nothing = d

getJust : ∀ {A B : Set} → PND B ∞ → (A → PND B ∞) → Maybe A → PND B ∞
getJust = match id


match-assoc : ∀ {i A B C D} (c : A → Maybe B) (m : PND A ∞) {d : PND C ∞}
               {f : B → PND C ∞}{g : C → PND D ∞} →
               ((m >>= match c d f) >>= g) ~[ i ] (m >>= match c (d >>= g) (λ x → f x >>=  g))
match-assoc {i} {A} {B} c m {d} {f} {g} =
            ~itrans (bind-assoc m) ( bind-cong-r m (λ x → cases c x ))
  where 
  cases : (c : A → Maybe B) (x : A) →
          (match c d f x >>= g) ~[ i ] (match c (d >>= g) (λ y → f y >>= g) x)
  cases c x with c x
  ... | just y  =  ~irefl
  ... | nothing =  ~irefl

getJust-assoc : ∀{i B C D} (m : PND (Maybe B) ∞) {d : PND C ∞}
               {f : B → PND C ∞}{g : C → PND D ∞} →
               ((m >>= getJust d f) >>= g) ~[ i ] (m >>= getJust (d >>= g) (λ x → f x >>= g))
getJust-assoc = match-assoc id


match-cong-default : ∀{i A B C} (c : A → Maybe B) (m : PND A ∞)
  {d : PND C ∞} {e : PND C ∞} {f : B → PND C ∞}
               (h : d ~[ i ] e) →
               (m >>= match c d f) ~[ i ] (m >>= match c e f)
match-cong-default {i} {A} c m {d} {e} {f} h =  bind-cong-r m   cases
  where cases : (a : A) → (match c d f a) ~[ i ] (match c e f a)
        cases a with c a
        ...| just x =  ~irefl
        ...| nothing = h


getJust-cong-default : ∀{i B C} (m : PND (Maybe B) ∞)
  {d : PND C ∞} {e : PND C ∞} {f : B → PND C ∞}
               (h : d ~[ i ] e) →
               (m >>= getJust d f) ~[ i ] (m >>= getJust e f)
getJust-cong-default = match-cong-default id


match-cong : ∀{i A B C} (c : A → Maybe B) (m : PND A ∞) {d : PND C ∞}
               {f : B → PND C ∞} {g : B → PND C ∞}
               (h : ∀ x → f x ~[ i ] g x) →
               (m >>= match c d f) ~[ i ] (m >>= match c d g)
match-cong {i} {A} c m {d} {f} {g} e =  bind-cong-r m  cases
  where cases : (x : A) → match c d f x ~[ i ] match c d g x
        cases x with c x
        ...| just y =  e y
        ...| nothing =  ~irefl

getJust-cong : ∀{i B C} (m : PND (Maybe B) ∞) {d : PND C ∞}
               {f : B → PND C ∞} {g : B → PND C ∞}
               (h : ∀ x → f x ~[ i ] g x) →
               (m >>= getJust d f) ~[ i ] (m >>= getJust d g)
getJust-cong = match-cong id

match-distr :  ∀{i A B C} (c : A → Maybe B)
            {p q : PND C ∞} {f : B → PND C ∞} a
            → match c p f a ⊕ q ~[ i ] match c (p ⊕ q) (λ x → f x ⊕ q) a
match-distr c a with c a
... | nothing = ~irefl
... | just x = ~irefl
