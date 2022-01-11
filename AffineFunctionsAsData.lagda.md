<!-- -*-agda2-mode-*- -->

<!--
```
module AffineFunctionsAsData where

open import Data.Nat using (ℕ)
import Data.Nat.Coprimality as CP
open import Data.Product
open import Data.Rational
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
(a , b) ⊕ (c , d) = (a ℚ.+ c , b ℚ.+ d)
```

Now let's tackle function composition. Taking the same definition of
`f(x)` and `g(x)` as before we can now look at what `f ∘ g` is:

   (f ∘ g)(x) = f(g(x)) = f(cx + d) = a(cx + d) + b = acx + ad + b = acx + (ad + b)

```
_∘_ : AF → AF → AF
(a , b) ∘ (c , d) = (a ℚ.* c , a ℚ.* d ℚ.+ b)
```

The meaning function is easy to define.

```
⟦_⟧ : AF → (ℚ → ℚ)
⟦ (a , b) ⟧ = λ x → a ℚ.* x ℚ.+ b
```

## An API for monoids

Affine functions clearly form a monoid with the identity element being the function `f(x) = 0` and the binary operation of addition. Let's quickly prove that.

```
open import Relation.Binary.PropositionalEquality

IsAffine : (ℚ → ℚ) → Set
IsAffine f = ∃[ a ] ∃[ b ] ∀ x → f x ≡ a ℚ.* x ℚ.+ b
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
module AffineFunctionMonoid where
  open import Relation.Binary.PropositionalEquality
  open import Algebra.Structures {A = ℚ → ℚ} _≗_

  _⊹_ : Op₂ (ℚ → ℚ)
  (f ⊹ g) x = f x + g x

  _∙_ : Op₂ AffineFunction
  (f , pᶠ) ∙ (g , pᵍ) = (f ⊹ g , pf pᶠ pᵍ)
    where
      pf : IsAffine f → IsAffine g → IsAffine (λ x → f x + g x)
      pf (a , b , p₁) (c , d , p₂) = (a + c , b + d , pf2 )
        where
          open ≡-Reasoning
          pf2 : (x : ℚ) → f x + g x ≡ (a + c) * x + (b + d)
          pf2 x =
            begin
              f x + g x
            ≡⟨ cong₂ (λ □ ◯ →  □ + ◯) (p₁ x) (p₂ x)   ⟩
             (a * x + b) + (c * x + d)
            ≡⟨ {!!} ⟩
              (a + c) * x + (b + d)
            ∎



  ε : AffineFunction
  ε = ((λ _ → ℚ[ 0 ]) , {!!} )

--  affineFunctionIsMonoid : IsMonoid _∙_ ε
--  affineFunctionIsMonoid  = {!!}

```


## An API for affine transformations

The Wikipedia page on _Affine Transformations_ has this to say:

> The functions `f : ℚ → ℚ , f(x) = mx + c` with `m` and `c` in `ℚ`,
> are precisely the affine transformations of the real line.
