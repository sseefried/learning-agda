<!-- -*-agda2-mode-*- -->

<!--
```
module AffineFunctionsAsData where

open import Data.Product
open import Data.Float hiding (_+_)
import Data.Float as ℝ
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





At this point we have not defined an API for whatever data structure
we end up using. We will let the denotation "suggest" the API to us.
We do this by seeing what body of mathematics surrounds the
denotation. What interesting algebraic properties does it have? What
mathematical structures is it part of?

A representation as data that immediately suggests itself is that of
ordered pairs.

```
ℝ = Float

AF : Set
AF = ℝ × ℝ
```

Now let's look at how we might add them. Let's consult the denotation.

    f(x) = ax + b
    g(x) = cx + d

then

    f(x) + g(x) = (ax + b) + (cx + d) = (a + c)x + (b + d)


```
_+_ : AF → AF → AF
(a , b) + (c , d) = (a ℝ.+ c , b ℝ.+ d)
```

Now let's tackle function composition. Taking the same definition of
`f(x)` and `g(x)` as before we can now look at what `f ∘ g` is:

   (f ∘ g)(x) = f(g(x)) = f(cx + d) = a(cx + d) + b = acx + ad + b = acx + (ad + b)

```
_∘_ : AF → AF → AF
(a , b) ∘ (c , d) = (a ℝ.* c , a ℝ.* d ℝ.+ b)
```

The meaning function is easy to define.

```
⟦_⟧ : AF → (ℝ → ℝ)
⟦ (a , b) ⟧ = λ x → a ℝ.* x ℝ.+ b
```

## An API for monoids

Affine functions clearly form a monoid with the identity element being the function `f(x) = 0` and the binary operation of addition. Let's quickly prove that.

```
open import Relation.Binary.PropositionalEquality

IsAffine : (ℝ → ℝ) → Set
IsAffine f = ∃[ a ] ∃[ b ] ∀ x → f x ≡ a ℝ.* x ℝ.+ b
```

Let's prove this for a basic affine function

```
10x+3 : ℝ → ℝ
10x+3 = λ x → (ℝ.fromℕ 10) ℝ.* x ℝ.+ (ℝ.fromℕ 3)

10x+3-isAffine : IsAffine 10x+3
10x+3-isAffine = (ℝ.fromℕ 10 , ℝ.fromℕ 3 , λ _ → refl )
```

Now we can package up the affine functions as follows

```
AffineFunction : Set
AffineFunction = Σ (ℝ → ℝ) IsAffine

10x+3-affine : AffineFunction
10x+3-affine = (10x+3 , 10x+3-isAffine)

```

```
module AffineFunctionMonoid where
  open import Relation.Binary.PropositionalEquality
  open import Algebra.Structures {A = ℝ → ℝ} _≗_


  _∙_ : Op₂ AffineFunction
  (f , pᶠ) ∙ (g , pᵍ) = ((λ x → f x ℝ.+ g x) , pf pᶠ pᵍ)
    where
      pf : IsAffine f → IsAffine g → IsAffine (λ x → f x ℝ.+ g x)
      pf (a , b , p₁) (c , d , p₂) = (a ℝ.+ c , b ℝ.+ d , pf2 )
        where
          open ≡-Reasoning
          pf2 : (x : ℝ) → f x ℝ.+ g x ≡ (a ℝ.+ c) * x ℝ.+ (b ℝ.+ d)
          pf2 x =
            begin
              f x ℝ.+ g x
            ≡⟨ cong₂ (λ □ ◯ →  □ ℝ.+ ◯) (p₁ x) (p₂ x)   ⟩
             (a * x ℝ.+ b) ℝ.+ (c * x ℝ.+ d)
            ≡⟨ {!!} ⟩
              (a ℝ.+ c) * x ℝ.+ (b ℝ.+ d)
            ∎



  ε : AffineFunction
  ε = ((λ _ → ℝ.fromℕ 0) , {!!} )

--  affineFunctionIsMonoid : IsMonoid _∙_ ε
--  affineFunctionIsMonoid  = {!!}

```


## An API for affine transformations

The Wikipedia page on _Affine Transformations_ has this to say:

> The functions `f : ℝ → ℝ , f(x) = mx + c` with `m` and `c` in `ℝ`,
> are precisely the affine transformations of the real line.
