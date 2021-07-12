{-# OPTIONS --copatterns --sized-types #-}

------------------------------------------------------------------------
-- This module defines the Patiality monad and strong bisimilarity. In
-- addition it proves the monad laws and all reasoning priciples we
-- need for our calculation proofs.
------------------------------------------------------------------------

module Partial where

open import Size public

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Product
open import Data.Bool renaming (_≤_ to _≤b_;_<_ to _<b_)
open import Category.Monad public
open import Category.Monad.Indexed public
open import Level renaming (zero to lzero; suc to lsuc) public
open import Data.Maybe renaming (_>>=_ to _M>>=_)
open import Function


mutual

  data Partial (A : Set) (i : Size) : Set where
    now   : A → Partial A i
    later : ∞Partial A i → Partial A i

  record ∞Partial (A : Set) (i : Size) : Set where
    coinductive
    constructor delay
    field
      force : {j : Size< i} → Partial A j

infix 3 _~_
infix 6 _~[_]_

open ∞Partial public

-- Monad instance.

module Bind where
  mutual
    _>>=_ : ∀ {i A B} → Partial A i → (A → Partial B i) → Partial B i
    now   x >>= f = f x
    later x >>= f = later (x ∞>>= f)

    _∞>>=_ :  ∀ {i A B} → ∞Partial A i → (A → Partial B i) → ∞Partial B i
    force (x ∞>>= f) = force x >>= f

delayMonad : ∀ {i} → RawMonad {f = lzero} (λ A → Partial A i)
delayMonad {i} = record
  { return = now
  ; _>>=_  = _>>=_ {i}
  } where open Bind


module _ {i : Size} where
  open module PartialMonad = RawMonad (delayMonad {i = i}) 
                           public renaming (_⊛_ to _<*>_)

open Bind public using (_∞>>=_)

---------------------------
-- (strong) bisimilarity --
---------------------------

-- We define strong bisimilarity in the style of Danielsson. We prove
-- later that this definition is equivalent to the definition in the
-- paper (see theorem `equiv-iconv~`).

mutual
  data _~_ {i : Size} {A : Set} : (a? b? : Partial A ∞) → Set where

    ~now   : ∀ a → now a ~ now a
    ~later : ∀ {a∞ b∞} (eq : _∞~_ {i} a∞ b∞) → later a∞ ~ later b∞

  record _∞~_ {i : Size} {A : Set} (a∞ b∞ : ∞Partial A ∞) : Set where
    coinductive
    constructor ~delay
    field
      ~force : {j : Size< i} → _~_ {j} (force a∞) (force b∞)

open _∞~_ public
 


-- Reflexivity

mutual
  ~refl  : ∀ {i A} (a? : Partial A ∞) → _~_ {i} a? a?
  ~refl (now a)    = ~now a
  ~refl (later a∞) = ~later (∞~refl a∞)

  ∞~refl : ∀ {i A} (a∞ : ∞Partial A ∞) → _∞~_ {i} a∞ a∞
  ~force (∞~refl a∞) = ~refl (force a∞)


-- Transitivity

mutual
  ~trans : ∀ {i A} {a b c : Partial A ∞}
    (eq : _~_ {i} a b) (eq' : _~_ {i} b c) → _~_ {i} a c
  ~trans (~now a)    (~now .a)    = ~now a
  ~trans (~later eq) (~later eq') = ~later (∞~trans eq eq')

  ∞~trans : ∀ {i A} {a∞ b∞ c∞ : ∞Partial A ∞}
    (eq : _∞~_ {i} a∞ b∞) (eq' : _∞~_ {i} b∞ c∞) → _∞~_ {i} a∞ c∞
  ~force (∞~trans eq eq') = ~trans (~force eq) (~force eq')

-- indexed bisimilarity

mutual
  data _~[_]_ {A : Set} : (a : Partial A ∞) → (i : ℕ) → (b : Partial A ∞) → Set where
    ~izero   : ∀ {a b} → a ~[ 0 ] b
    ~inow   : ∀ i a → now a ~[ i ] now a
    ~ilater : ∀ {i a b} (eq : force a ~[ i ] force b) → later a ~[ suc i ] later b

-- indexed bisimilarity implies bisimilairity

mutual
  stepped : ∀ {A} (a b : Partial A ∞) → (∀ i → a ~[ i ] b) → a ~ b
  stepped (now x) (now y) eq with eq 1
  ... | ~inow _ _  =  ~now x
  stepped (now x) (later y) eq with eq 1
  ... | ()
  stepped (later x) (now y) eq with eq 1
  ... | ()
  stepped (later x) (later y) eq =  ~later (∞stepped x y (\ i -> stepped-later i x y (eq (suc i))))
    where stepped-later : ∀ {A} i (a b : ∞Partial A ∞) →
                         (later a  ~[ suc i ] later b) →  force a ~[ i ] force b
          stepped-later i a b (~ilater eq) =  eq
  ∞stepped : ∀ {A} (a b : ∞Partial A ∞) → (∀ i → force a ~[ i ] force b) → a ∞~ b
  ~force (∞stepped a b eq) =  stepped (force a) (force b)  eq

-- reflexivity


~irefl'  : ∀ {i A} (a : Partial A ∞) → a ~[ i ] a
~irefl' {zero} a =  ~izero
~irefl' {suc i} (now x) = ~inow (suc i) x
~irefl' {suc i} (later x) =  ~ilater (~irefl' ( force x)) 

~irefl  : ∀ {i A} {a : Partial A ∞} → a ~[ i ] a
~irefl {_} {_} {a} =  ~irefl' a


-- Transitivity


~itrans : ∀ {i A} {a b c : Partial A ∞}
  (eq : a ~[ i ] b) (eq' : b ~[ i ] c) → a ~[ i ] c
~itrans {zero} eq eq' = ~izero
~itrans {suc i} (~inow .(suc i) a) (~inow .(suc i) .a) = ~inow (suc i) a
~itrans {suc i} (~ilater eq) (~ilater eq') =  ~ilater (~itrans {i} eq eq')

-- Symmetry


~isymm : ∀ {i A} {a b : Partial A ∞}
  (eq : a ~[ i ] b) → b ~[ i ] a
~isymm {zero} eq  = ~izero
~isymm (~inow i a) =  ~inow i a
~isymm {suc i} (~ilater eq) = ~ilater (~isymm eq)



_~⟨_⟩_ : ∀ {A : Set} {i} (x : Partial A ∞) → ∀ {y : Partial A ∞} {z : Partial A ∞} → x ~[ i ] y → y ~[ i ] z → x ~[ i ] z
_~⟨_⟩_ {_} x r eq =  ~itrans r eq

_~⟨⟩_ : ∀ {A : Set} {i} (x : Partial A ∞) → ∀ {y : Partial A ∞} → x ~[ i ] y → x ~[ i ] y
_~⟨⟩_  x eq = eq



_∎ : ∀ {A : Set} {i} (x : Partial A ∞) → x ~[ i ] x
_∎  x = ~irefl

infix  3 _∎
infixr 1 _~⟨_⟩_
infixr 1 _~⟨⟩_

~idown : ∀ {i} {A} {a b : Partial A ∞} -> a ~[ suc i ] b -> a ~[ i ] b
~idown {i} (~inow .(suc _) a) = ~inow i a
~idown {zero} (~ilater eq) = ~izero
~idown {suc i} (~ilater eq) =  ~ilater ( ~idown eq)

bind-cong : ∀ {i A B}  {a b : Partial A ∞} (eq : a ~[ i ] b)
            {k l : A → Partial B ∞} (h : ∀ a → (k a) ~[ i ] (l a)) →
            (a >>= k) ~[ i ] (b >>= l)
bind-cong (~izero) g = ~izero
bind-cong (~inow _ a) g =  g a
bind-cong {suc i} (~ilater h) g =  ~ilater ( bind-cong h \ a' -> ~idown (g a'))

bind-cong-l : ∀ {i A B}  {a b : Partial A ∞} (eq : a ~[ i ] b)
            {k : A → Partial B ∞} →
            (a >>= k) ~[ i ] (b >>= k)
bind-cong-l (~izero) = ~izero
bind-cong-l (~inow a _) =  ~irefl
bind-cong-l (~ilater eq) = ~ilater ( bind-cong-l eq)


bind-cong-r : ∀ {i A B}  (a : Partial A ∞)
            {k l : A → Partial B ∞} (h : ∀ a → (k a) ~[ i ] (l a)) →
            (a >>= k) ~[ i ] (a >>= l)
bind-cong-r (now x) eq =  eq x
bind-cong-r {zero} (later x) eq =  ~izero
bind-cong-r {suc i} (later x) eq = ~ilater (bind-cong-r (force x) \ a' -> ~idown (eq a') )

bind-assoc : ∀{i A B C}(m : Partial A ∞)
                 {k : A → Partial B ∞}{l : B → Partial C ∞} →
                 ((m >>= k) >>= l) ~[ i ] (m >>= λ a → k a >>= l)
bind-assoc (now x) =  ~irefl
bind-assoc {zero} (later x) =  ~izero
bind-assoc {suc i} (later x) =  ~ilater ( bind-assoc (force x))


mutual
  never : ∀ {a i} -> Partial a i
  never = later ∞never

  ∞never : ∀ {a i} -> ∞Partial a i
  force ∞never = never




if-bind : ∀ {A B n} {x y : Partial A ∞} {f : A → Partial B ∞} b 
  → ((if b then x else y) >>= f) ~[ n ] (if b then (x >>= f) else (y >>= f))
if-bind false =  ~irefl
if-bind true = ~irefl

if-then-cong : ∀ b {A n} {x y x' : Partial A ∞} (eq : x ~[ n ] x') → (if b then x else y) ~[ n ] (if b then x' else y)
if-then-cong false eq = ~irefl
if-then-cong true eq =  eq


never-bind : ∀ {i A B} {f : A → Partial B ∞} → (never >>= f) ~[ i ] never
never-bind {0} = ~izero
never-bind {suc i} =  ~ilater never-bind

bind-never : ∀ {i A B} (m : Partial A ∞) → _~[_]_ {B} (m >>= (λ x → never)) i never
bind-never {zero} m = ~izero
bind-never {suc i} (now x) = ~irefl
bind-never {suc i} (later x) =  ~ilater ( bind-never (force x))




match : ∀ {i} {A B C : Set} → (A → Maybe B) → Partial C i → (B → Partial C i) → A → Partial C i
match m d f a with m a
... | just x =  f x
... | nothing = d

getJust : ∀ {i} {A B : Set} → Partial B i → (A → Partial B i) → Maybe A → Partial B i
getJust = match id




match-assoc : ∀{i A B C D} (c : A → Maybe B) (m : Partial A ∞) {d : Partial C ∞}
               {f : B → Partial C ∞}{g : C → Partial D ∞} →
               ((m >>= match c d f) >>= g) ~[ i ] (m >>= match c (d >>= g) (λ x → f x >>=  g))
match-assoc {i} {A} {B} c m {d} {f} {g} =
  ~itrans (bind-assoc m) ( bind-cong-r m (λ x → cases c x ))
  where 
  cases : (c : A → Maybe B) (x : A) →
          (match c d f x >>= g) ~[ i ] (match c (d >>= g) (λ y → f y >>= g) x)
  cases c x with c x
  ... | just y  =  ~irefl
  ... | nothing =  ~irefl


match-cong-default : ∀{i A B C} (c : A → Maybe B) (m : Partial A ∞)
  {d : Partial C ∞} {e : Partial C ∞} {f : B → Partial C ∞}
               (h : d ~[ i ] e) →
               (m >>= match c d f) ~[ i ] (m >>= match c e f)
match-cong-default {i} {A} c m {d} {e} {f} h =  bind-cong-r m   cases
  where cases : (a : A) → (match c d f a) ~[ i ] (match c e f a)
        cases a with c a
        ...| just x =  ~irefl
        ...| nothing = h

match-cong : ∀{i A B C} (c : A → Maybe B) (m : Partial A ∞) {d : Partial C ∞}
               {f : B → Partial C ∞} {g : B → Partial C ∞}
               (h : ∀ x → f x ~[ i ] g x) →
               (m >>= match c d f) ~[ i ] (m >>= match c d g)
match-cong {i} {A} c m {d} {f} {g} e =  bind-cong-r m  cases
  where cases : (x : A) → match c d f x ~[ i ] match c d g x
        cases x with c x
        ...| just y =  e y
        ...| nothing =  ~irefl


-- Prove that the indexed bisimilarity relation can be characterised
-- using the indexed convergence relation (defined below) as follows:
--
--   p ~[i] q  <=> (∀ j < i, v. p ⇓[j] v <=> q ⇓[j] v)
--

data _⇓[_]_ {A : Set} : Partial A ∞ → ℕ → A → Set where
  iconv-now : ∀{i} → (x : A) → now x ⇓[ i ] x
  iconv-later :  ∀{i} → {v : A} → {p : ∞Partial A ∞} → force p ⇓[ i ] v → (later p) ⇓[ suc i ] v

-- lemmas 
~iconv : ∀ {A} {i} {j} {p : Partial A ∞} {q : Partial A ∞} {v} →  (le : j < i) → p ~[ i ] q → p ⇓[ j ] v → q ⇓[ j ] v
~iconv l (~inow _ a) c = c
~iconv (s≤s (s≤s l)) (~ilater e) (iconv-later c) = iconv-later (~iconv (s≤s l) e c)


conv-inv : ∀ {A} {p : Partial A ∞} {v : A} → p ⇓[ 0 ] v → p ≡ now v
conv-inv (iconv-now _) = refl

conv-inv' : ∀ {B : Set} {A : Set} {p : ∞Partial A ∞} {v : A} → (later p) ⇓[ 0 ] v → B
conv-inv' ()

conv-down : ∀ {i} {A} {x} {y} → (∀ {j} {v : A} → j < suc i → (later x) ⇓[ j ] v → (later y) ⇓[ j ] v)
  → ({j : ℕ} {v : A} → j < i → force x ⇓[ j ] v → force y ⇓[ j ] v)
conv-down f le c with f (s≤s le) (iconv-later c)
... | iconv-later d = d


iconv~ : ∀ {A} {i} {p : Partial A ∞} {q : Partial A ∞}
  → (∀ {j}{v} →  (le : j < i) → p ⇓[ j ] v → q ⇓[ j ] v)
  → (∀ {j}{v} →  (le : j < i) → q ⇓[ j ] v → p ⇓[ j ] v)
  → p ~[ i ] q
iconv~ {i = zero} f g = ~izero
iconv~ {i = suc i} {now x} f g with conv-inv (f (s≤s z≤n) (iconv-now x))
... | refl = ~inow (suc i) x
iconv~ {i = suc i} {later x} { now y} f g = conv-inv' (g (s≤s z≤n) (iconv-now y))
iconv~ {i = suc i} {later x} {later y} f g = ~ilater (iconv~ ( conv-down f) ( conv-down g))

-- Theorem: p ~[i] q  <=> (∀ j < i, v. p ⇓[j] v <=> q ⇓[j] v)

equiv-iconv~ : ∀ {A} {i} {p : Partial A ∞} {q : Partial A ∞}
  →  p ~[ i ] q ⇔ (∀ {j}{v} → (le : j < i) → p ⇓[ j ] v ⇔  q ⇓[ j ] v)
equiv-iconv~ {A} {i} {p} {q} = mk⇔  to  from
  where from : ({j : ℕ} {v : A} → j < i → (p ⇓[ j ] v) ⇔ (q ⇓[ j ] v)) →
            p ~[ i ] q
        from eq = iconv~ ( λ le c → Equivalence.f (eq le) c)  ( λ le c → Equivalence.g (eq le) c)
        to : p ~[ i ] q → {j : ℕ} {v : A} → j < i → (p ⇓[ j ] v) ⇔ (q ⇓[ j ] v)
        to eq le = mk⇔ (~iconv le eq) (~iconv le (~isymm eq))


-- Prove that the indexed bisimilarity relation can be characterised
-- using the indexed convergence relation and the indexed divergence
-- relation (defined below) as follows:
--
--   p ~[i] q  <=> (∀ j < i, v. p ⇓[j] v => q ⇓[j] v) ∧ (∀ j ≤ i. p ⇑[j] => q ⇑[j])
--

data _⇑[_] {A : Set} : Partial A ∞ → ℕ → Set where
  idiv-zero : ∀ (p : Partial A ∞) → p ⇑[ 0 ]
  idiv-suc :  ∀{i} → {p : ∞Partial A ∞} → force p ⇑[ i ] → (later p) ⇑[ suc i ]

~idiv : ∀ {A} {i} {j} {p : Partial A ∞} {q : Partial A ∞} → (le : j ≤ i) →  p ~[ i ] q → p ⇑[ j ] → q ⇑[ j ]
~idiv z≤n ~izero d = idiv-zero _
~idiv le (~inow _ a) d = d
~idiv z≤n (~ilater e) d = idiv-zero _
~idiv (s≤s le) (~ilater e) (idiv-suc d) = idiv-suc (~idiv le e d)

idiv~ : ∀ {A} {i} {p : Partial A ∞} {q : Partial A ∞}
  → (∀ {j}{v} →  (le : j < i) → p ⇓[ j ] v → q ⇓[ j ] v)
  → (∀ {j} →  (le : j ≤ i) →  p ⇑[ j ] → q ⇑[ j ])
  → p ~[ i ] q
idiv~ {i = zero} c d = ~izero
idiv~ {i = suc i} {now x} c d  with conv-inv (c (s≤s z≤n) (iconv-now x))
... | refl = ~inow (suc i) x
idiv~ {A} {suc i} {later x} c d with d ( s≤s z≤n) (idiv-suc (idiv-zero _))
...| idiv-suc {p = p} (idiv-zero .(force p)) = ~ilater (idiv~ (conv-down c) ( down d))
  where down : ({j : ℕ} → j ≤ suc i → (later x) ⇑[ j ] → (later p) ⇑[ j ])
               → {j : ℕ} → j ≤ i → force x ⇑[ j ] → force p ⇑[ j ]
        down h l d with h (s≤s l) (idiv-suc d)
        ... | idiv-suc r = r

-- Theorem: p ~[i] q  <=> (∀ j < i, v. p ⇓[j] v => q ⇓[j] v) ∧ (∀ j ≤ i. p ⇑[j] => q ⇑[j])

equiv-idiv~ : ∀ {A} {i} {p : Partial A ∞} {q : Partial A ∞}
  → p ~[ i ] q ⇔ ((∀ {j}{v} → (j < i) → p ⇓[ j ] v →  q ⇓[ j ] v) ×
                  (∀ {j} → (j ≤ i) → p ⇑[ j ] → q ⇑[ j ]))
equiv-idiv~ {A} {i} {p} {q} =  mk⇔  to
                                    (λ (c , d) → idiv~ c  d)
  where to : p ~[ i ] q → ({j : ℕ} {v : A} → j < i → p ⇓[ j ] v → q ⇓[ j ] v)
                        × ({j : ℕ} → j ≤ i → p ⇑[ j ] → q ⇑[ j ])
        to eq =  ( λ le c → ~iconv le eq c) ,  λ le d → ~idiv le eq d
