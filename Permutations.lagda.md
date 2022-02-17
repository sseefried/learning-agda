# Sorting

```
module Permutations where

open import Data.Nat using (ℕ; _+_)
open import Data.Fin renaming (Fin to 𝔽) hiding (_+_)
open import Data.Fin.Properties hiding (setoid)
open import Relation.Binary.PropositionalEquality using (_≡_; _≗_)
open import Data.Sum
open import Data.Sum.Properties
open import Function
open import Function.Bundles
open import Level using (Level)

splitPermute : (m : ℕ) {n : ℕ} → (𝔽 (m + n) → 𝔽 (n + m))
splitPermute m {n} = join n m ∘ swap ∘ splitAt m

cong-[_]∘⟨_⟩∘[_] : {a : Level} {A′ A B B′ : Set a}
       → ∀ (h : B → B′) {f g : A → B}
       → f ≗ g  → (h′ : A′ → A) → h ∘ f ∘ h′ ≗ h ∘ g ∘ h′
cong-[_]∘⟨_⟩∘[_] h {f} {g} f≗g h′ = λ x → cong h (f≗g (h′ x))
  where
    open Relation.Binary.PropositionalEquality using (cong)

inverse : {m n : ℕ} → splitPermute n ∘ splitPermute m ≗ id
inverse {m} {n} =
  begin
    (splitPermute n ∘ splitPermute m)                             ≡⟨⟩
    (join m n ∘ swap ∘ splitAt n) ∘ (join n m ∘ swap ∘ splitAt m) ≡⟨⟩
    (join m n ∘ swap ∘ splitAt n ∘ join n m ∘ swap ∘ splitAt m)   ≈⟨ cong-[ join m n ∘ swap ]∘⟨ splitAt-join n m ⟩∘[ swap ∘ splitAt m ] ⟩
    (join m n ∘ swap ∘ swap ∘ splitAt m)                          ≈⟨ cong-[ join m n ]∘⟨ swap-involutive ⟩∘[ splitAt m ] ⟩
    (join m n ∘ splitAt m)                                        ≈⟨ join-splitAt m n ⟩
    id
  ∎
  where
    open import Relation.Binary.PropositionalEquality
    open import Relation.Binary.Reasoning.Setoid (𝔽 (m + n) →-setoid 𝔽 (m + n))

splitPermute↔ : (m : ℕ) {n : ℕ} → (𝔽 (m + n) ↔ 𝔽 (n + m))
splitPermute↔ m {n} = mk↔′ (splitPermute m) (splitPermute n) (inverse {n} {m}) (inverse {m} {n})
```
