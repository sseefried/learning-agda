module CartesianIsomorphism where

open import Level renaming (suc to lsuc)
open import Categorical.Raw
open import Categorical.Equiv
open import Functions (0ℓ)
open import Categorical.Laws using ()
import Categorical.Laws as L

module _ (obj : Set) (_⇨_ : obj → obj → Set) (a c d : obj)
         ⦃ _ : Category _⇨_ ⦄
         ⦃ equivl : Equivalent 0ℓ _⇨_ ⦄
         ⦃ catLaw : L.Category _⇨_ ⦄
         ⦃ _ : Products obj ⦄
         ⦃ _ : Cartesian _⇨_ ⦄
         ⦃ cartLaw : L.Cartesian _⇨_ ⦄
  where

  open import Function.Bundles
  open import Relation.Binary.Bundles
  open import Data.Product using (_,_) renaming (_×_ to _×′_)
  open import Relation.Binary.Core

  cat cat² : Setoid 0ℓ 0ℓ
  cat = record { Carrier = a ⇨ (c × d)
             ; _≈_ = _≈_
             ; isEquivalence = equiv }
  cat² = record { Carrier = (a ⇨ c) ×′ (a ⇨ d)
             ; _≈_ = λ (a⇨c₁ , a⇨d₁) (a⇨c₂ , a⇨d₂) → (a⇨c₁ ≈ a⇨c₂) ×′ (a⇨d₁ ≈ a⇨d₂)
             ; isEquivalence =
                 record
                   { refl  = refl  , refl
                   ; sym   = λ (eq₁ , eq₂) → sym eq₁ , sym eq₂
                   ; trans = λ (eq₁ , eq₂) (eq₁′ , eq₂′)  → trans eq₁ eq₁′ , trans eq₂ eq₂′
                   }
             }

  open Setoid cat  using () renaming (Carrier to A; _≈_ to _≈₁_)
  open Setoid cat² using () renaming (Carrier to B; _≈_ to _≈₂_)

  iso : Inverse cat cat²
  iso = record
        { f       = f
        ; f⁻¹     = f⁻¹
        ; cong₁   = cong₁
        ; cong₂   = cong₂
        ; inverse = inverseˡ , inverseʳ
        }
     where
       f : a ⇨ (c × d) → (a ⇨ c) ×′ (a ⇨ d)
       f = λ a⇨c×d  → exl ∘ a⇨c×d , exr ∘ a⇨c×d

       f⁻¹ : (a ⇨ c) ×′ (a ⇨ d) → a ⇨ (c × d)
       f⁻¹ = λ a⇨c,a⇨d → exl a⇨c,a⇨d ▵ exr a⇨c,a⇨d

       cong₁ : {x y : a ⇨ (c × d)} → x ≈₁ y → (f x ≈₂ f y)
       cong₁ {x} {y} x≈₁y  =
           begin
             f x
           ≡⟨⟩
             exl ∘ x , exr ∘ x
           ≈⟨ L.∘≈ʳ x≈₁y , L.∘≈ʳ x≈₁y ⟩
             exl ∘ y , exr ∘ y
           ≡⟨⟩
             f y
           ∎
         where
             open import Relation.Binary.Reasoning.Setoid cat²

       cong₂ : {x y : (a ⇨ c) ×′ (a ⇨ d)} → x ≈₂ y → (f⁻¹ x ≈₁ f⁻¹ y)
       cong₂ {x} {y} x≈₂y =
           begin
             f⁻¹ x
           ≡⟨⟩
             exl x ▵ exr x
           ≈⟨ L.▵≈ (exl x≈₂y) (exr x≈₂y) ⟩
             exl y ▵ exr y
           ≡⟨⟩
             f⁻¹ y
           ∎
         where
             open import Relation.Binary.Reasoning.Setoid cat

       inverseˡ : ∀ x → f (f⁻¹ x) ≈₂ x
       inverseˡ (a⇨c , a⇨d) =
          begin
            f (f⁻¹ (a⇨c , a⇨d))
          ≡⟨⟩
            f (a⇨c ▵ a⇨d)
          ≡⟨⟩
            (exl ∘ (a⇨c ▵ a⇨d) , exr ∘ (a⇨c ▵ a⇨d))
          ≈⟨ L.exl∘▵ , L.exr∘▵ ⟩
            (a⇨c , a⇨d)
          ∎
           where
             open import Relation.Binary.Reasoning.Setoid cat²

       inverseʳ : ∀ x → f⁻¹ (f x) ≈₁ x
       inverseʳ a⇨c×d =
           begin
             f⁻¹ (f a⇨c×d)
           ≡⟨⟩
             f⁻¹ (exl ∘ a⇨c×d , exr ∘ a⇨c×d)
           ≡⟨⟩
             (exl ∘ a⇨c×d) ▵ (exr ∘ a⇨c×d)
           ≈⟨ sym L.▵∘ ⟩
             (exl ▵ exr) ∘ a⇨c×d
           ≈⟨ L.∘≈ˡ L.exl▵exr ⟩
            id ∘ a⇨c×d
           ≈⟨ L.identityˡ ⟩
             a⇨c×d
           ∎
         where
           open ≈-Reasoning
