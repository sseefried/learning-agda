# Sorting

```
module Permutations where

open import Data.Nat using (ℕ)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Data.Fin renaming (Fin to 𝔽)
open import Data.Fin.Properties hiding (setoid)
--open import Function.Inverse
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; module ≡-Reasoning)
open import Relation.Nullary
--open import Function.LeftInverse
--open import Function.Equality using (_⟶_)
open import Level using (0ℓ)
open import Relation.Binary.Bundles
open import Data.Product hiding (swap)
open import Data.Sum
open import Data.Sum.Properties
open import Function
open import Function.Bundles

splitPermute : (m : ℕ) {n : ℕ} → (𝔽 (m ℕ.+ n) → 𝔽 (n ℕ.+ m))
splitPermute m {n} = join n m ∘ swap ∘ splitAt m

inverse : {m n : ℕ} (x : 𝔽 (m ℕ.+ n)) → (splitPermute n ∘ splitPermute m) x ≡ x
inverse {m} {n} x =
  begin
    (splitPermute n ∘ splitPermute m) x                                ≡⟨⟩
    ((join m n ∘ swap ∘ splitAt n) ∘ (join n m ∘ swap ∘ splitAt m)) x  ≡⟨⟩
    (join m n ∘ swap ∘ (splitAt n ∘ join n m) ∘ swap ∘ splitAt m) x    ≡⟨ cong (join m n ∘ swap) (splitAt-join n m ((swap ∘ splitAt m)  x)) ⟩
    (join m n ∘ swap ∘ swap ∘ splitAt m) x                             ≡⟨ cong (join m n) (swap-involutive (splitAt m x)) ⟩
    (join m n ∘ splitAt m) x                                           ≡⟨ join-splitAt m n x ⟩
    x
  ∎
  where
    open import Relation.Binary.PropositionalEquality
    open ≡-Reasoning

splitPermute↔ : (m : ℕ) {n : ℕ} → (𝔽 (m ℕ.+ n) ↔ 𝔽 (n ℕ.+ m))
splitPermute↔ m {n} = mk↔′ (splitPermute m) (splitPermute n) (inverse {n} {m}) (inverse {m} {n})

```
