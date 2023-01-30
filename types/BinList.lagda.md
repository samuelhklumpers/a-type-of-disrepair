```
{-# OPTIONS --cubical #-}

module BinList where

open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat as ℕ

open import Cubical.Data.Nat.Properties
open import Cubical.Data.Fin hiding (_/_)

open import Cubical.Data.Empty renaming (elim to ⊥-elim)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Everything
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Relation.Binary
open import Cubical.Relation.Nullary.Properties
open import Cubical.Relation.Nullary
open import Cubical.HITs.SetQuotients as SQ
open import Cubical.Data.Equality as Eq renaming (eqToPath to path) using ()
open import Cubical.Data.Nat.Properties
open import Cubical.Data.Sigma


private variable
  ℓ : Level
  A B : Type ℓ
  x y : A
```

Good morning, in this text, I will be spelling the construction of binary trees by the method of calculation.
For this, we first define a type of binary numbers, from which we construct the associated indices.
Then, we can use the representability of vectors and the exponent identities to calculate the type of binary trees.

Without further ado, let's define the ordinary binary numbers.
We can do this in a couple of ways, for example as lists of digits
```
data DL : Type where
  nb  : DL
  0b_ : DL → DL
  1b_ : DL → DL

infix 10 0b_ 1b_
```

We read these as little-endian naturals (i.e., least significant digit first, or from right-to-left). -- make it so it is not 
Alas, this representation turns out to be horribly redundant!
Namely, adding a 0b on the right (equivalently, having leading zeroes) does not change the value of a number.

Using our new found power (--cubical), we can resolve this in a couple of ways.
We will add the required equalities using a quotient:
```
R : DL → DL → Type
R nb     nb     = ⊤
R nb     (0b x) = R nb x
R nb     (1b _) = ⊥
R (0b x) nb     = R x nb
R (0b x) (0b y) = R x y
R (0b _) (1b _) = ⊥
R (1b _) nb     = ⊥
R (1b _) (0b _) = ⊥
R (1b x) (1b y) = R x y

Bin = DL / R
```
Remark: here R defines a binary relation on DL. In addition to relating every x : DL to itself x R x, R also relates (0b x) R nb, provided x R nb.
In particular, this let's us unfold things like (0b 0b nb) R nb step-by-step, i.e., nb R nb ⇒ (0b nb) R nb ⇒ (0b 0b nb) R nb.

This ensures that any term with leading zeros becomes equal to one with none,
and yields the equalities we would expect from non-redundant binary numbers, like:
```
example : Path Bin [ 1b 0b 0b nb ] [ 1b nb ]
example = eq/ _ _ tt
```

Clearly any "natural" number type should be isomorphic to ℕ,
so let's prove this! For this, we define some helpers:
```
module Digits where
  -- successor operation on DL,
  -- note that because DL is binary, the term grows a lot slower in the number of applications of suc than it would in ℕ!
  suc : DL → DL
  suc nb     = 1b nb
  suc (0b x) = 1b x
  suc (1b x) = 0b (suc x) -- carry the bit

  -- interpret a list of binary digits as a natural
  ⟦_⟧ : DL → ℕ
  ⟦ nb ⟧   = 0
  ⟦ 0b x ⟧ = 2 ℕ.· ⟦ x ⟧
  ⟦ 1b x ⟧ = 1 ℕ.+ 2 ℕ.· ⟦ x ⟧

  -- "⟦_⟧ is a homomorphism of natural numbers"
  ⟦⟧-suc : ∀ x → ⟦ suc x ⟧ ≡ ℕ.suc ⟦ x ⟧
  ⟦⟧-suc nb     = refl
  ⟦⟧-suc (0b x) = refl
  ⟦⟧-suc (1b x) = (cong (2 ℕ.·_) (⟦⟧-suc x)) ∙ ·-suc 2 ⟦ x ⟧

  -- going back is very easy using suc!
  fromℕ : ℕ → DL
  fromℕ ℕ.zero    = nb
  fromℕ (ℕ.suc n) = suc (fromℕ n)
```

Evidently, a natural number should satisfy fromℕ ⟦ x ⟧ ≡ x, for which the following lemma is essential, but clearly fails already at 0
```
  -- fromℕ-2· : ∀ n → fromℕ (2 ℕ.· n) ≡ 0b fromℕ n
  -- fromℕ-2· ℕ.zero    = {!nb ≡ 0b nb!}
  -- fromℕ-2· (ℕ.suc n) = {!nice try!}
```

This is precisely because nb ≡ 0b nb cannot automatically hold in DL, which is why adding it as a path to Bin _does_ make Bin a proper natural number type.
```
module Binary where
  -- some boilerplate lifting operations from DL to Bin (not sure if this is necessary or could be smoother)
  Bin-0b : Bin → Bin
  Bin-0b = setQuotUnaryOp 0b_ λ _ _ r → r

  Bin-1b : Bin → Bin
  Bin-1b = setQuotUnaryOp 1b_ λ _ _ r → r

  suc : Bin → Bin
  suc = setQuotUnaryOp Digits.suc p
    where
    -- note that non-trivial operations on quotients require us to provide (non-trivial) coherences.
    -- particularly, maps out of quotients cannot violate the relation 
    p : ∀ a a' → R a a' → R (Digits.suc a) (Digits.suc a')
    p nb     nb      r = tt
    p nb     (0b a') r = r
    p (0b a) nb      r = r
    p (0b a) (0b a') r = r
    p (1b a) (1b a') r = p a a' r
    
  ⟦_⟧ : Bin → ℕ
  ⟦_⟧ = SQ.rec isSetℕ Digits.⟦_⟧ p
    where
    p : ∀ a b → R a b → Digits.⟦ a ⟧ ≡ Digits.⟦ b ⟧
    p nb     nb     r = refl
    p nb     (0b b) r = cong (2 ℕ.·_) (p nb b r)
    p (0b a) nb     r = cong (2 ℕ.·_) (p a nb r)
    p (0b a) (0b b) r = cong (2 ℕ.·_) (p a b r)
    p (1b a) (1b b) r = cong (λ n → 1 ℕ.+ 2 ℕ.· n) (p a b r)
    
  ⟦⟧-suc : ∀ x → ⟦ suc x ⟧ ≡ ℕ.suc ⟦ x ⟧
  ⟦⟧-suc = SQ.elimProp (λ _ → isSetℕ _ _) Digits.⟦⟧-suc

  fromℕ : ℕ → Bin
  fromℕ = [_] ∘ Digits.fromℕ

  -- the lemma which fails for DL now holds in Bin, exactly by the path we inserted
  fromℕ-2· : ∀ x → fromℕ (2 ℕ.· x) ≡ Bin-0b (fromℕ x)
  fromℕ-2· ℕ.zero    = eq/ nb (0b nb) tt
  fromℕ-2· (ℕ.suc x) = 
    fromℕ (2 ℕ.· ℕ.suc x)    ≡⟨ cong fromℕ (·-suc 2 x) ⟩
    fromℕ (2 ℕ.+ 2 ℕ.· x)    ≡⟨ cong (λ k → suc (suc k)) (fromℕ-2· x) ⟩
    Bin-0b (fromℕ (ℕ.suc x)) ∎

  fromℕ-1+2· : ∀ n → fromℕ (1 ℕ.+ 2 ℕ.· n) ≡ Bin-1b (fromℕ n)
  fromℕ-1+2· ℕ.zero    = refl
  fromℕ-1+2· (ℕ.suc n) = 
    fromℕ (1 ℕ.+ 2 ℕ.· ℕ.suc n)   ≡⟨ cong (fromℕ ∘ ℕ.suc) (·-suc 2 n) ⟩
    fromℕ (ℕ.suc (2 ℕ.+ 2 ℕ.· n)) ≡⟨ cong (suc ∘ suc) (fromℕ-1+2· n) ⟩
    Bin-1b (fromℕ (ℕ.suc n))      ∎

-- the actual proof of equivalence between our binary naturals and the unary naturals
-- (no univalence, yet)
Bin≃ℕ : Bin ≃ ℕ
Bin≃ℕ = isoToEquiv (iso ⟦_⟧ fromℕ sec ret)
  module Bin≃ℕ where
    open Binary

    sec : section ⟦_⟧ fromℕ
    sec ℕ.zero    = refl
    sec (ℕ.suc x) = ⟦⟧-suc (fromℕ x) ∙ cong ℕ.suc (sec x)

    ret : retract ⟦_⟧ fromℕ
    ret = elimProp (λ _ → squash/ _ _) go
      module ret where
        go : ∀ a → fromℕ Digits.⟦ a ⟧ ≡ [ a ]
        go nb     = refl
        go (0b a) = fromℕ-2· Digits.⟦ a ⟧ ∙ cong Bin-0b (go a)
        go (1b a) = fromℕ-1+2· Digits.⟦ a ⟧ ∙ cong Bin-1b (go a)
```

Great! We can then derive the associated indices fairly directly from the inequality on DL.
```
-- note that we split on the right argument first:
-- this makes the next computation easier
_≤DL_ : DL → DL → Type
nb     ≤DL nb     = ⊤
(0b x) ≤DL nb     = x ≤DL nb
(1b _) ≤DL nb     = ⊥
nb     ≤DL (0b y) = ⊤
(0b x) ≤DL (0b y) = x ≤DL y
(1b x) ≤DL (0b y) = Digits.suc x ≤DL y -- recall suc (1b x) ≡ 0b (suc x)
nb     ≤DL (1b y) = ⊤
(0b x) ≤DL (1b y) = x ≤DL y
(1b x) ≤DL (1b y) = x ≤DL y

_<DL_ : DL → DL → Type
x <DL y = Digits.suc x ≤DL y
```

We would like to define the index type such that it satisfies
```
Index′ : DL → Type
Index′ x = Σ[ y ∈ DL ] (y <DL x)
```

However, this is a bit clumsy.
We can compute a nicer representation.
```
{- 
⊥-strict : (A → ⊥) → A ≃ ⊥
⊥-strict f = uninhabEquiv f (λ x → x)

x≤nb : ∀ x → x ≤DL nb → R x nb
x≤nb nb     p = tt
x≤nb (0b x) p = x≤nb x p

snotz-R : ∀ x → R (Digits.suc x) nb → ⊥
snotz-R x p = h x (Digits.suc x) refl p
  where
  h : ∀ x y → y ≡ Digits.suc x → R y nb → ⊥
  h nb nb p q = {!!}
  h nb (0b y) p q = {!!}
  h (0b x) nb p q = {!!}
  h (0b x) (0b y) p q = {!!}
  h (1b x) nb p q = {!!}
  h (1b x) (0b y) p q = {!!}

x≮nb : ∀ x → x <DL nb → ⊥
x≮nb x x<nb = {!x≤nb (Digits.suc x) x<nb!}
-}

-- trust me
-- Index-nb : Index′ nb ≡ ⊥
-- Index-nb = ua (⊥-strict λ { (1b y , y<x) → {!y<x!} })

-- Index-0b : ∀ x → Index′ (0b x) ≃ Index′ x × Index′ x
-- Index-0b x = {!x!}
```

Theoretically speaking anyway.
In practice, we define
```
data Index : DL → Type where
  0t0 : ∀ {x} → Index x → Index (0b x)
  0t1 : ∀ {x} → Index x → Index (0b x)
  
  1t0 : ∀ {x} → Index x → Index (1b x)
  1t1 : ∀ {x} → Index x → Index (1b x)
  1h0 : ∀ {x}           → Index (1b x)

```

-- and prove that this is a suitable index type
-- ```
-- IndexBin-nb : ∀ {x} → IndexBin x → x ≡ nb → ⊥
-- IndexBin-nb (i0b ix iy) p = IndexBin-nb ix {!cong 0b p ∙ ?!}
-- IndexBin-nb (i1b ix iy) p = {!!}
-- IndexBin-nb i1h         p = {!!}

-- re-index-Bin : ∀ x → Fin ⟦ x ⟧Bin ≃ IndexBin x
-- re-index-Bin nb     = {!!}
-- re-index-Bin (0b x) = {!!}
-- re-index-Bin (1b x) = {!!}
-- re-index-Bin (0i i) = {!!}
-- ```
