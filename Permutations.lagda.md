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

splitPermute : (m : ℕ) {n : ℕ} → (𝔽 (m + n) → 𝔽 (n + m))
splitPermute m {n} = join n m ∘ swap ∘ splitAt m

inverse : {m n : ℕ} → splitPermute n ∘ splitPermute m ≗ λ x → x
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

splitPermute↔ : (m : ℕ) {n : ℕ} → (𝔽 (m + n) ↔ 𝔽 (n + m))
splitPermute↔ m {n} = mk↔′ (splitPermute m) (splitPermute n) (inverse {n} {m}) (inverse {m} {n})
```
