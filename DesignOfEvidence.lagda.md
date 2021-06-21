<!-- -*-agda2-*- -->


# Design of Evidence data types in Agda

I was perplexed by how one would come up with evidence data types
in Agda but I recently came across a plausible way to go about
"discovering" what the evidence data type should be.

<!--
```
module DesignOfEvidence where

open import Data.Bool hiding (_≤_)
open import Data.Nat hiding (_≤ᵇ_; _≤_)
-- open import Data.Nat using (_≤?_; _≤ᵇ_)
open import Relation.Binary.PropositionalEquality
```
-->

Consider the following definite of the `_≤?_` function

```
_≤ᵇ_ : ℕ → ℕ → Bool
suc n ≤ᵇ zero  = false
zero ≤ᵇ m      = true
suc n ≤ᵇ suc m = n ≤ᵇ m
```

Now let's consider the pattern of recursion for a
"successful" invocation of `_≤ᵇ_`.

```
_ : 2 ≤ᵇ 3 ≡ true
_ = begin
      2 ≤ᵇ 3
    ≡⟨⟩
      suc (suc zero) ≤ᵇ suc (suc (suc zero))
    ≡⟨⟩ -- recursive call
      suc zero ≤ᵇ suc (suc zero)
    ≡⟨⟩ -- recursive call
      zero ≤ᵇ suc zero
    ≡⟨⟩ --base case
     true
    ∎
  where
    open ≡-Reasoning
```

Clearly, in any case where the result is `true` the
function will match on the base case (where `zero ≤ᵇ n`)
or the recursive case (where `suc n ≤ᵇ suc m`).

This points us towards the following data type

```
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {n m} → n ≤ m → suc n ≤ suc m
```

Here's a test:

```
_ : 2 ≤ 3
_ = s≤s (s≤s z≤n)
```
