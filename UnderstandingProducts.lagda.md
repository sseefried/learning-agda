```
module UnderstandingProducts where

open import Level
open import Data.Bool
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Categorical.Raw
open import Categorical.Equiv hiding (refl)
open import Functions hiding (tt ; if_then_else_)
open import Data.Unit renaming (⊤ to Unit)
import Categorical.Laws as Laws
open import Relation.Binary.PropositionalEquality
open import Data.Product using (Σ; _,_) renaming (_×_ to _×′_)
open import Relation.Nullary


open Laws.Category ⦃ … ⦄ public
open Laws.Cartesian ⦃ … ⦄ public




-- https://en.wikipedia.org/wiki/Product_(category_theory)

X-is-same-as-product-X×⊤ : ∀ {obj : Set} {_⇨_ : obj → obj → Set} {X Y : obj}  ⦃ _ : Category {obj = obj}  _⇨_ ⦄ ⦃ _ : Equivalent 0ℓ _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Laws.Category _⇨_ ⦄ ⦃ _ : Laws.Cartesian _⇨_ ⦄
     → (f₁ : Y ⇨ X) → (f₂ : Y ⇨ ⊤) →
     Σ (Y ⇨ X) (λ f  → ((id ∘ f ≈ f₁) ×′ (! ∘ f ≈ f₂)))
X-is-same-as-product-X×⊤ f₁ f₂ = f₁ , identityˡ , p
  where
    open ≈-Reasoning
    p = begin
            ! ∘ f₁
           ≈⟨ ∀⊤ ⟩
            !
           ≈⟨ Categorical.Equiv.sym ∀⊤  ⟩
            f₂
        ∎


X≈X×⊤2 : ∀ {obj : Set} {_⇨_ : obj → obj → Set} {A : obj}  ⦃ _ : Category {obj = obj}  _⇨_ ⦄ ⦃ _ : Equivalent 0ℓ _⇨_ ⦄ ⦃ _ : Products obj ⦄ ⦃ _ : Cartesian _⇨_ ⦄ ⦃ _ : Laws.Category _⇨_ ⦄ ⦃ _ : Laws.Cartesian _⇨_ ⦄
   → (id ▵ ! ≈ id)
X≈X×⊤2 = {!!}
```
