{-# OPTIONS --without-K --safe #-}

module MonoidLawTransfer where

open import Data.Product
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b

open import Algebra.Core using (Op₂)

record Monoid (A : Set) : Set₁ where
   infixr 29 _∙_
   field
      _∙_ : Op₂ A
      ε   : A

open Monoid ⦃ … ⦄ public

record MonoidHomomorphism (⟦_⟧ : A → B) (_≈₂_ : B → B → Set)
                          (monoidA : Monoid A) (monoidB : Monoid B) : Set where
  instance
    _ : Monoid A
    _ = monoidA
    _ : Monoid B
    _ = monoidB

  field
    ε-homo : ⟦ ε ⟧ ≈₂ ε
    homo : ∀ x y → ⟦ x ∙ y ⟧ ≈₂ ⟦ x ⟧ ∙ ⟦ y ⟧

  open import Algebra.Definitions
  open import Algebra.Structures
  open IsMonoid ⦃ … ⦄ public
  open Level
  open import Relation.Binary

  _≈₁_ : A → A → Set
  a ≈₁ b = ⟦ a ⟧ ≈₂ ⟦ b ⟧

  is-monoid-via-homomorphism : IsMonoid _≈₂_ _∙_ ε → IsMonoid _≈₁_ _∙_ ε
  is-monoid-via-homomorphism is-monoid₂ =
    record
      { isSemigroup =
          record
            { isMagma =
                record
                  { isEquivalence = record { refl = refl; sym = sym; trans = trans }
                  ; ∙-cong = ∙-congruent
                  }
            ; assoc = ∙-assoc
            }
      ; identity = ∙-identityˡ , ∙-identityʳ
      }
    where
      instance
        _ : IsMonoid _≈₂_ _∙_ ε
        _ = is-monoid₂

      open import Relation.Binary.Reasoning.Setoid (setoid)

      ∙-congruent : Congruent₂ _≈₁_ _∙_
      ∙-congruent {x} {y} {u} {v} x≈₁y u≈₁v =
        begin
          ⟦ x ∙ u ⟧
        ≈⟨ homo x u ⟩
          ⟦ x ⟧ ∙ ⟦ u ⟧
        ≈⟨ ∙-cong x≈₁y u≈₁v ⟩
          ⟦ y ⟧ ∙ ⟦ v ⟧
        ≈⟨ sym (homo y v) ⟩
          ⟦ y ∙ v ⟧
        ∎

      ∙-identityˡ : LeftIdentity _≈₁_ ε _∙_
      ∙-identityˡ x =
        begin
          ⟦ ε ∙ x ⟧
        ≈⟨ homo ε x  ⟩
          ⟦ ε ⟧ ∙ ⟦ x ⟧
        ≈⟨ ∙-congʳ ε-homo ⟩
          ε ∙ ⟦ x ⟧
        ≈⟨ identityˡ ⟦ x ⟧ ⟩
          ⟦ x ⟧
        ∎

      ∙-identityʳ : RightIdentity _≈₁_ ε _∙_
      ∙-identityʳ x =
        begin
          ⟦ x ∙ ε ⟧
        ≈⟨ homo x ε ⟩
          ⟦ x ⟧ ∙ ⟦ ε ⟧
        ≈⟨ ∙-congˡ ε-homo ⟩
          ⟦ x ⟧ ∙ ε
        ≈⟨ identityʳ ⟦ x ⟧ ⟩
          ⟦ x ⟧
        ∎

      ∙-assoc : Associative _≈₁_ _∙_
      ∙-assoc x y z =
        begin
          ⟦ (x ∙ y) ∙ z ⟧
        ≈⟨ homo (x ∙ y) z ⟩
          ⟦ x ∙ y ⟧ ∙ ⟦ z ⟧
        ≈⟨ ∙-congʳ (homo x y) ⟩
          (⟦ x ⟧ ∙ ⟦ y ⟧) ∙ ⟦ z ⟧
        ≈⟨ assoc ⟦ x ⟧ ⟦ y ⟧ ⟦ z ⟧ ⟩
          ⟦ x ⟧ ∙ (⟦ y ⟧ ∙ ⟦ z ⟧)
        ≈⟨ sym  (∙-congˡ (homo y z)) ⟩
          ⟦ x ⟧ ∙ ⟦ y ∙ z ⟧
        ≈⟨ sym (homo x (y ∙ z)) ⟩
          ⟦ x ∙ (y ∙ z) ⟧
        ∎
