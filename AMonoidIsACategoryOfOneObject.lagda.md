<!-- -*-agda2-*- -->

# A monoid is a category of one object

In this module we'll formally prove that "a monoid is a category of
one object". We do this by proving the correspondence both ways.

In the forward direction we have a module `Monoid⇒Category`,
parameterised on a monoid, that provides a function `toCategory`.

In the reverse direction we have a module `Category⇒Monoid`,
parameterised on a category, that provides a function `toMonoid`

First, we'll start with the preamble.

```agda

open import Relation.Binary using (Rel; Setoid; IsEquivalence)

module AMonoidIsACategoryOfOneObject {a ℓ} {A : Set a}  where

open import Level using (0ℓ; _⊔_) renaming (suc to lsuc)
open import Data.Unit.Polymorphic using (⊤; tt)

open import Algebra.Structures {a} {ℓ}
open import Algebra.Definitions {a} {ℓ}
open import Categorical.Raw hiding (⊤)
open import Categorical.Equiv
import Categorical.Laws as Laws
open import Data.Product
```

We choose the object type in the category to be `⊤`. This means that
the single object is the value ‵tt`.

The _morphisms_ of the category will be values of type `A`, which are
the _elements_ of the monoid. This is quite an odd category. The
morphisms are normally thought of as something like a function, but in
this case they are just values of type `A`.

We define the morphism arrow as follows:

```agda
_⇨_ : ⊤ {ℓ} → ⊤ → Set a
tt ⇨ tt = A
```

Next we provide a convenient package of a `Category`, `Equivalent` and
`Laws.Category` value.  We use a dependent product to satisfy the
dependencies of the later values on the previous values.

```agda
CategoryAndLaws :  Set (a ⊔ lsuc ℓ)
CategoryAndLaws = Σ (Category {obj = ⊤} _⇨_)
                    (λ cat →  Σ (Equivalent ℓ {obj = ⊤} _⇨_)
                    (λ equiv → Laws.Category {obj = ⊤} _⇨_  ⦃ equiv ⦄ ⦃ cat ⦄))
```

Now we are able to define the `Monoid⇨Category` module.


```agda
module Monoid⇒Category {_≈_ : Rel A ℓ} {_∙_ : A → A → A} {ε : A} (is-monoid : IsMonoid _≈_ _∙_ ε) where

  open IsMonoid ⦃ … ⦄ public
  instance
        _ : IsMonoid _≈_ _∙_ ε
        _ = is-monoid

  open import Relation.Binary.Reasoning.Setoid {a} {ℓ} (setoid _≈_)

  toCategory : CategoryAndLaws
  toCategory = category , equivalent , categoryLaws
    where
      category : Category _⇨_
      category     = record { id = ε ; _∘_ = _∙_ }
      equivalent : Equivalent ℓ _⇨_
      equivalent   = record { _≈_ = _≈_ ; equiv = isEquivalence _≈_}
      categoryLaws : Laws.Category {obj = ⊤} _⇨_ ⦃ equivalent ⦄ ⦃ category ⦄
      categoryLaws = record { identityˡ = λ {_ _ x} → identityˡ _≈_ x
                            ; identityʳ = λ {_ _ x} → identityʳ _≈_ x
                            ; assoc     = λ {_ _ _ _ x y z} → assoc _≈_ z y x
                            ; ∘≈        = ∙-cong _≈_
                            }
```

And the reverse direction is done as follows.


```agda
module Category⇨Monoid ((category , equivalent , categoryLaws) : CategoryAndLaws) where
  open Laws.Category ⦃ … ⦄ public
  instance
    _ : Category _⇨_
    _ = category
    _ : Equivalent ℓ _⇨_
    _ = equivalent
    _ : Laws.Category _⇨_
    _ = categoryLaws

  toMonoid : IsMonoid _≈_ _∘_ id
  toMonoid =
    record { isSemigroup = semigroup
           ; identity    = (λ x → identityˡ) , (λ x → identityʳ)
           }
    where
      magma : IsMagma _≈_ _∘_
      magma = record { isEquivalence = equiv  ; ∙-cong = ∘≈ }

      semigroup : IsSemigroup _≈_ _∘_
      semigroup = record { isMagma = magma ; assoc = λ z y x → assoc }
```

These two modules formally prove that a monoid really is a category of
one object. Given one of these entities you can transform it into the
other.
