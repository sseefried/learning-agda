<!-- -*-agda2-*- -->

This module relies on Conal Elliott's `denotational-hardware` repo on
[GitHub](https://github.com/conal/denotational-hardware/)

A phrase you might have heard if "a monoid is a category of one
object". In this module we show two different ways of expressing the
same structure, once as a monoid, once as a category of one object.

We choose as our example the monoid of endofunctions (i.e those
functions of type `A → A` for some `A`) with the associative binary
operator being function composition and with the identity element
being the identity function.

Here is the preamble:

```
module EndoFunctionsAsAMonoid where

open import Level
open import Categorical.Raw
open import Categorical.Equiv hiding (refl)
open import Data.Unit renaming (⊤ to Unit)
import Categorical.Laws as Laws
open import Relation.Binary.PropositionalEquality
```

We define composition and identity as follows:

```
infix 5 _∘ᴬ_
_∘ᴬ_ : {A : Set} → (A → A) → (A → A) → (A → A)
_∘ᴬ_ = λ f g x → f (g x)

idᴬ : {A : Set} → A → A
idᴬ = λ x → x
```

We can then prove that this is a monoid as follows:

```
module FunctionMonoid (A : Set) where
  open import Algebra.Structures {A = A → A } _≡_
  open import Algebra.Definitions
  open import Data.Product

  fun-isMagma : IsMagma _∘ᴬ_
  fun-isMagma = record { isEquivalence = isEquivalence ; ∙-cong = cong₂ _∘ᴬ_ }

  fun-isSemigroup : IsSemigroup _∘ᴬ_
  fun-isSemigroup = record { isMagma = fun-isMagma ; assoc =  λ a b c → refl  }

  fun-isMonoid : IsMonoid _∘ᴬ_ idᴬ
  fun-isMonoid = record { isSemigroup = fun-isSemigroup ; identity = ((λ x → refl) , (λ x → refl)) }
```

But we can also express it as a category of one object. The singular object is just unit (`tt`)
but the morphisms are all the functions from `A → A`.

```
_⇨ᵒ_ : {A : Set} → Unit → Unit → Set
_⇨ᵒ_ {A} tt tt = A → A

instance
  _ : {A : Set} → Category (_⇨ᵒ_ {A})
  _ = record { id = idᴬ ; _∘_ = λ f g x → f (g x) }

  _ : {A : Set} → Equivalent 0ℓ (_⇨ᵒ_ {A})
  _ = record { _≈_ = _≡_ ; equiv = isEquivalence }

  _ : {A : Set} → Laws.Category (_⇨ᵒ_ {A})
  _ = record { identityˡ = refl ; identityʳ = refl ; assoc = refl ; ∘≈ = λ h≈k f≈g → cong₂ _∘ᴬ_ h≈k f≈g  }

```
