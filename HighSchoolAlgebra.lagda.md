<!-- -*-agda2-*- -->

<!--
```
{-# OPTIONS --with-K #-}

module HighSchoolAlgebra where

open import Data.Rational
open import Data.Rational.Properties
```
-->

## Preamble

We're going to show how to transform `a + b ≡ c + d` into `a - c ≡ d - b`.

Here are some lemmas we're going to need

```
open import Relation.Binary.PropositionalEquality

subLHSʳ : (a b c : ℚ) → (a + b ≡ c) → (a ≡ c - b)
subLHSʳ a b c eq =
      begin
        a
      ≡⟨ sym (+-identityʳ a) ⟩
        a + 0ℚ
      ≡⟨ cong (λ □ → a + □) (sym (+-inverseʳ b))  ⟩
        a + (b - b)
      ≡⟨ sym (+-assoc a  b (- b)) ⟩
        (a + b) - b
      ≡⟨ cong (λ □ → □ - b) eq ⟩
        c - b
      ∎
    where
      open ≡-Reasoning

subRHSˡ : (a b c : ℚ) → a ≡ b + c → a - b ≡ c
subRHSˡ a b c eq =
      begin
        a - b
      ≡⟨ cong (_- b) eq ⟩
        b + c - b
      ≡⟨ cong (_- b) (+-comm b c) ⟩
        c + b - b
      ≡⟨ +-assoc c b (- b) ⟩
        c + (b - b)
      ≡⟨ cong (c +_) (+-inverseʳ b)  ⟩
        c + 0ℚ
      ≡⟨ +-identityʳ c ⟩
        c
      ∎
    where
      open ≡-Reasoning

reassoc : (a b c d : ℚ) → a ≡ b + c + d → a ≡ b + (c + d)
reassoc a b c d eq =
      begin
        a
      ≡⟨ eq ⟩
        b + c + d
      ≡⟨ +-assoc b c d ⟩
        b + (c + d)
      ∎
    where
      open ≡-Reasoning
```

## Using `Function.Reasoning`

Using this approach the equations sit on the right of `∶` syntax.

```
module _ where

  open import Function.Reasoning


  ex1 : (a b c d : ℚ) → a + b ≡ c + d → a - c ≡ d - b
  ex1 a b c d a+b≡c+d =
       a+b≡c+d             ∶ a + b ≡ c + d
    |> subLHSʳ a b (c + d) ∶ a ≡ c + d - b
    |> reassoc a c d (- b) ∶ a ≡ c + (d - b)
    |> subRHSˡ a c (d - b) ∶ a - c ≡  d - b

```
