<!-- -*-agda2-mode-*- -->

<!--
```
module AffineFunctionsAsData where

open import Data.Nat using (ℕ)
import Data.Nat.Coprimality as CP
open import Data.Product
open import Data.Rational
open import Data.Rational.Properties
import Data.Rational.Properties as ℚ
open import Data.Rational.Solver
import Data.Rational as ℚ
open import Level using (0ℓ)
open import Algebra.Core

```
-->

# Denotational Design Example: affine functions as denotation

In this module I will attempt to apply the principles of _denotational
design_ to come up with a representation for affine functions as data
structures.

We take as our definition of affine functions all functions of the
form `f(x) = ax + b` where `a` and `b` are constants.

For the purposes of this note we use rational numbers, `ℚ`, as the
domain and co-domain of our affine functions. The real numbrers, `ℝ`,
would be preferable but they are harder to model. `Float` will not
suffice as the ordinary properties of arithmetic do not actually hold
on floating point numbers. e.g. it is not necessarily true that
`a * (b + c) = a * b + a * c`.


At this point we have not defined an API for whatever data structure
we end up using. We will let the denotation "suggest" the API to us.
We do this by seeing what body of mathematics surrounds the
denotation. What interesting algebraic properties does it have? What
mathematical structures is it part of?

A representation as data that immediately suggests itself is that of
ordered pairs.

```

AF : Set
AF = ℚ × ℚ
```

Now let's look at how we might add them. Let's consult the denotation.

    f(x) = ax + b
    g(x) = cx + d

then

    f(x) + g(x) = (ax + b) + (cx + d) = (a + c)x + (b + d)

```
_⊕_ : AF → AF → AF
(a , b) ⊕ (c , d) = (a + c , b + d)
```

Now let's tackle function composition. Taking the same definition of
`f(x)` and `g(x)` as before we can now look at what `f ∘ g` is:

   (f ∘ g)(x) = f(g(x)) = f(cx + d) = a(cx + d) + b = acx + ad + b = acx + (ad + b)

```
_∘_ : AF → AF → AF
(a , b) ∘ (c , d) = (a * c , a * d + b)
```

The meaning function is easy to define.

```
⟦_⟧ : AF → (ℚ → ℚ)
⟦ (a , b) ⟧ = λ x → a * x + b
```

## An API for monoids: attempt 1

Affine functions clearly form a monoid with the identity element being the function `f(x) = 0` and the binary operation of addition. Let's quickly prove that.

But first, let's define what it means to add two functions.

```
_⊹_ : Op₂ (ℚ → ℚ)
(f ⊹ g) x = f x + g x
```

We can now beging our attempt in earnest.

```
module Attempt1 where
  open import Relation.Binary.PropositionalEquality

  IsAffine : (ℚ → ℚ) → Set
  IsAffine f = ∃[ a ] ∃[ b ] ((x : ℚ) → f x ≡ a * x + b)
  ```

  Let's prove this for a basic affine function

  ```
  ℚ[_] : ℕ → ℚ
  ℚ[ x ] = mkℚ+ x 1 (CP.sym (CP.1-coprimeTo x))
  ```

  ```
  10x+3 : ℚ → ℚ
  10x+3 = λ x → (ℚ[ 10 ]) * x + ℚ[ 3 ]

  10x+3-isAffine : IsAffine 10x+3
  10x+3-isAffine = (ℚ[ 10 ] , ℚ[ 3 ] , λ _ → refl )
```

Now we can package up the affine functions as follows

```
  AffineFunction : Set
  AffineFunction = Σ (ℚ → ℚ) IsAffine

  10x+3-affine : AffineFunction
  10x+3-affine = (10x+3 , 10x+3-isAffine)
```

```
  +-isAffine : {f g : ℚ → ℚ} →  IsAffine f → IsAffine g → IsAffine (f ⊹ g)
  +-isAffine {f} {g} (a , b , p₁) (c , d , p₂) = (a + c , b + d , pf′ )
    where
      open ≡-Reasoning
      open +-*-Solver
      pf′ : (x : ℚ) → f x + g x ≡ (a + c) * x + (b + d)
      pf′ x =
          f x + g x
        ≡⟨ cong₂ _+_ (p₁ x) (p₂ x)   ⟩
         (a * x + b) + (c * x + d)
        ≡⟨ solve 5 (λ a b c d x →
             ((a :* x :+ b) :+ (c :* x :+ d)) :=
             ((a :+ c) :* x :+ (b :+ d))) refl a b c d x ⟩
          (a + c) * x + (b + d)
        ∎

  _∙_ : Op₂ AffineFunction
  (f , pᶠ) ∙ (g , pᵍ) = (f ⊹ g , +-isAffine pᶠ pᵍ)


  const-0ℚ-isAffine : IsAffine (λ _ → 0ℚ)
  const-0ℚ-isAffine = (0ℚ , 0ℚ , pf)
      where
        open +-*-Solver
        pf : (x : ℚ) → 0ℚ ≡ 0ℚ * x + 0ℚ
        pf x =
          solve 1 (λ x → con 0ℚ := (con 0ℚ :* x) :+ con 0ℚ) refl x

  ε : AffineFunction
  ε = (λ _ → 0ℚ) , const-0ℚ-isAffine


  infix 4 _≈_
  _≈_ : AffineFunction → AffineFunction → Set
  (_ , (a , b , _)) ≈ (_ , (c , d , _)) = a ≡ c × b ≡ d
      -- the proofs are unimportant
  -- this is a specification but it's not simple enough.
  -- TODO: Is this true?


  module AffineFunctionMonoid where
    open import Relation.Binary.PropositionalEquality
    open import Algebra.Definitions {A = AffineFunction} _≈_
    open import Algebra.Structures {A = AffineFunction} _≈_

    open import Relation.Binary.Bundles

    AffineFunction-setoid : Setoid 0ℓ 0ℓ
    AffineFunction-setoid = record { Carrier = AffineFunction
                  ; _≈_ = _≈_
                  ; isEquivalence =
                      record { refl = refl , refl
                             ; sym = λ (x₁≈y₁ , x₂≈y₂) →  sym x₁≈y₁ , sym x₂≈y₂
                             ; trans = λ (i₁≈j₁ , i₂≈j₂) (j₁≈k₁ , j₂≈k₂ ) →
                                         trans i₁≈j₁ j₁≈k₁ , trans i₂≈j₂ j₂≈k₂
                             }
                  }

    affineFunctionIsMonoid : IsMonoid _∙_ ε
    affineFunctionIsMonoid =
      record
        { isSemigroup = affineFunctionIsSemigroup
        ; identity = identityˡ , identityʳ
        }
      where
        open import Relation.Binary.Reasoning.Setoid AffineFunction-setoid
        ∙-cong : Congruent₂ _∙_ -- ∀ {x y u v} → x ≈ y → u ≈ v → x ∙ u ≈ y ∙ v
        ∙-cong {x@(_ , (x₁ , x₂ , _))}
               {y@(_ , (y₁ , y₂ , _))}
               {u@(_ , (u₁ , u₂ , _))}
               {v@(_ , (v₁ , v₂ , _))}
               x≈y@(x₁≈y₁ , x₂≈y₂)
               u≈v@(u₁≈v₁ , u₂≈v₂) =
          begin
            x ∙ u
          ≈⟨ cong₂ _+_ x₁≈y₁ u₁≈v₁ , cong₂ _+_ x₂≈y₂ u₂≈v₂ ⟩
            y ∙ v
          ∎

        affineFunctionIsMagma : IsMagma _∙_
        affineFunctionIsMagma =
          record { isEquivalence = Setoid.isEquivalence AffineFunction-setoid
                 ; ∙-cong = λ {x} {y} {u} {v} → ∙-cong {x} {y} {u} {v}
                 }

        assoc : ∀ f g h →  (f ∙ g) ∙ h ≈ f ∙ (g ∙ h)
        assoc f@(_ , (f₁ , f₂ , _)) g@(_ , (g₁ , g₂ , _)) h@(_ , (h₁ , h₂ , _)) =
          begin
            (f ∙ g) ∙ h
          ≈⟨ +-assoc f₁ g₁ h₁ , +-assoc f₂ g₂ h₂  ⟩
            f ∙ (g ∙ h)
          ∎

        affineFunctionIsSemigroup : IsSemigroup _∙_
        affineFunctionIsSemigroup =
          record
            { isMagma = affineFunctionIsMagma
            ; assoc = assoc
            }



        identityˡ : ∀ f → ε ∙ f ≈ f
        identityˡ f@(_ , (a , b , _)) =
          begin
            ε ∙ f
          ≈⟨ +-identityˡ a , +-identityˡ b ⟩
            f
          ∎


        identityʳ : ∀ f → f ∙ ε ≈ f
        identityʳ f@(_ , (a , b , _)) =
          begin
            f ∙ ε
          ≈⟨ +-identityʳ a , +-identityʳ b ⟩
            f
          ∎
```

## An API for monoids: attempt 2

I was quite unhappy with the definition of `_≈_` in Attempt 1 above.
In this attempt the denotation will just be `ℚ → ℚ`. The image of the
meaning function `⟦_⟧ : AF → (ℚ → ℚ)` will actually just be the affine functions.
Another way to say this is that `⟦_⟧` is not surjective.

```
module Attempt2 where

```

Our equivalence relation will just be _extensional equality_ on functions.
The monoidal operation will be `_⊹_` and we define `const0ℚ` as our identity element.


```
  const0ℚ : ℚ → ℚ
  const0ℚ = λ _ → 0ℚ

  module AffineFunctionMonoid where
    _∙_ : (ℚ → ℚ) → (ℚ → ℚ) → (ℚ → ℚ)
    _∙_ = _⊹_

    ε : (ℚ → ℚ)
    ε = const0ℚ

    open import Relation.Binary.PropositionalEquality
             using (_≡_; _≗_; _→-setoid_; module ≡-Reasoning; cong₂)
    open import Algebra.Definitions {A = ℚ → ℚ } _≗_
    open import Algebra.Structures {A = ℚ → ℚ} _≗_

    open import Relation.Binary.Bundles

    ℚ→ℚ-setoid : Setoid 0ℓ 0ℓ
    ℚ→ℚ-setoid = ℚ →-setoid ℚ

    open Setoid ⦃ … ⦄ hiding (refl; sym; trans) public
    instance
      _ = ℚ→ℚ-setoid

    isMonoid : IsMonoid _∙_ ε
    isMonoid =
        record
          { isSemigroup = isSemigroup
          ; identity    = identityˡ , identityʳ
          }
      where
        open ≡-Reasoning

        ∙-cong : {f f′ g g′ : ℚ → ℚ} → f ≈ f′ → g ≈ g′ → f ∙ g ≈ f′ ∙ g′
        ∙-cong {f} {f′} {g} {g′} f≈f′ g≈g′ x =
          begin
            (f ∙ g) x
          ≡⟨⟩
            f x + g x
          ≡⟨ cong₂ _+_ (f≈f′ x) (g≈g′ x) ⟩
            f′ x + g′ x
          ≡⟨⟩
            (f′ ∙ g′) x
          ∎

        isMagma : IsMagma _∙_
        isMagma =
          record
            { isEquivalence = isEquivalence
            ; ∙-cong = ∙-cong
            }

        assoc : ∀ f g h → (f ∙ g) ∙ h ≈ f ∙ (g ∙ h)
        assoc f g h x =
          begin
            ((f ∙ g) ∙ h) x
          ≡⟨⟩
            (f x + g x) + h x
          ≡⟨ +-assoc (f x) (g x) (h x) ⟩
            f x + (g x + h x)
          ≡⟨⟩
            (f ∙ (g ∙ h)) x
          ∎


        isSemigroup : IsSemigroup _∙_
        isSemigroup =
          record
            { isMagma = isMagma
            ; assoc   = assoc
            }

        identityˡ : ∀ f → ε ∙ f ≈ f
        identityˡ f x =
          begin
            (ε ∙ f) x
          ≡⟨⟩
            0ℚ + f x
          ≡⟨ +-identityˡ (f x) ⟩
            f x
          ∎

        identityʳ : ∀ f → f ∙ ε ≈ f
        identityʳ f x =
          begin
            (f ∙ ε) x
          ≡⟨⟩
            f x + 0ℚ
          ≡⟨ +-identityʳ (f x) ⟩
            f x
          ∎
```

Now that we have shown that the denotation is a monoid let's prove
that the representation is also a monoid.

```
  module AFIsMonoid where
    open import Relation.Binary.PropositionalEquality
    open import Algebra.Definitions {A = AF} _≡_
    open import Algebra.Structures {A = AF} _≡_

    _∙_ : AF → AF → AF
    _∙_ = _⊕_

    ε : AF
    ε = 0ℚ , 0ℚ

    isMonoid : IsMonoid _∙_ ε
    isMonoid =
        record
          { isSemigroup = isSemigroup
          ; identity    = identityˡ , identityʳ
          }
      where
        open ≡-Reasoning

        assoc : ∀ f g h → (f ∙ g) ∙ h ≡ f ∙ (g ∙ h)
        assoc f@(f₁ , f₂) g@(g₁ , g₂) h@(h₁ , h₂) =
          cong₂ _,_ (+-assoc f₁ g₁ h₁) (+-assoc f₂ g₂ h₂)

        isSemigroup : IsSemigroup _∙_
        isSemigroup =
          record
            { isMagma = isMagma _∙_
            ; assoc   = assoc
            }

        identityˡ : ∀ f → ε ∙ f ≡ f
        identityˡ f@(f₁ , f₂) = cong₂ _,_ (+-identityˡ f₁) (+-identityˡ f₂)

        identityʳ : ∀ f → f ∙ ε ≡ f
        identityʳ f@(f₁ , f₂) = cong₂ _,_ (+-identityʳ f₁) (+-identityʳ f₂)
```

```
  open import Relation.Binary.PropositionalEquality using (_≗_; module ≡-Reasoning; cong; sym)

  monoid-homo-id : ⟦ AFIsMonoid.ε ⟧ ≗ AffineFunctionMonoid.ε
  monoid-homo-id x =
    begin
      ⟦ 0ℚ , 0ℚ ⟧ x
    ≡⟨⟩
      0ℚ * x + 0ℚ
    ≡⟨ cong (λ □ → □ + 0ℚ) (*-zeroˡ x)  ⟩
      0ℚ + 0ℚ
    ≡⟨⟩
      const0ℚ x
    ∎
    where
      open ≡-Reasoning

  monoid-homo-op : ∀ f g → ⟦ f AFIsMonoid.∙ g ⟧ ≗ ⟦ f ⟧ AffineFunctionMonoid.∙ ⟦ g ⟧
  monoid-homo-op f@(f₁ , f₂) g@(g₁ , g₂) x =
    begin
      ⟦ f AFIsMonoid.∙ g ⟧ x
    ≡⟨⟩
      (f₁ + g₁) * x + (f₂ + g₂)
    ≡⟨ cong (λ □ → □ + (f₂ + g₂)) (*-distribʳ-+ x f₁ g₁) ⟩
      (f₁ * x + g₁ * x) + (f₂ + g₂)
    ≡⟨ +-assoc (f₁ * x) (g₁ * x) (f₂ + g₂) ⟩
      f₁ * x + (g₁ * x + (f₂ + g₂))
    ≡⟨ cong (λ □ → f₁ * x + □) (+-comm (g₁ * x ) (f₂ + g₂)) ⟩
      f₁ * x + ((f₂ + g₂) + g₁ * x)
    ≡⟨ cong (λ □ → f₁ * x + □) (+-assoc f₂ g₂ (g₁ * x)) ⟩
      f₁ * x + (f₂ + (g₂ + g₁ * x))
    ≡⟨ cong (λ □ → f₁ * x + (f₂ + □)) (+-comm g₂ (g₁ * x)) ⟩
      f₁ * x + (f₂ + (g₁ * x + g₂))
    ≡⟨ sym (+-assoc (f₁ * x) f₂ (g₁ * x + g₂)) ⟩
      (f₁ * x + f₂) + (g₁ * x + g₂)
    ≡⟨⟩
      (⟦ f ⟧ AffineFunctionMonoid.∙ ⟦ g ⟧) x
    ∎
    where
      open ≡-Reasoning

```



## An API for affine transformations

The Wikipedia page on _Affine Transformations_ has this to say:

> The functions `f : ℚ → ℚ , f(x) = mx + c` with `m` and `c` in `ℚ`,
> are precisely the affine transformations of the real line.
