<!-- -*-agda2-*- -->

<!--
```
module HighSchoolAlgebra where

open import Data.Rational
open import Data.Rational.Properties
```
-->

# How to do algebraic manipulations like I was taught in High School

For a while I've wanted to manipulate equations just like I was taught
in high school. For instance, given the equation `a + b ≡ c + d` I'd like to be able to
do something like

```plain
  a + b ≡ c + d
  a     ≡ c + d - b        -- subtract b from both sides
  a - c ≡ d - b            -- subtract c from both sides
```

I now know how to do this is in Agda and with some help from Matthew
Daggitt on the Agda Zulip and a private discussion with Conal Elliott.


## Preamble

Here are some lemmas we're going to need. They're simply proofs that allow us
to do things like "subtract from both sides" or "reassociate addition".

```
open import Relation.Binary.PropositionalEquality hiding (setoid)

subLHSʳ : (a b c : ℚ) → (a + b ≡ c) → (a ≡ c - b)
subLHSʳ a b c eq =
      begin
        a             ≡⟨ sym (+-identityʳ a) ⟩
        a + 0ℚ        ≡⟨ cong (λ □ → a + □) (sym (+-inverseʳ b))  ⟩
        a + (b - b)   ≡⟨ sym (+-assoc a  b (- b)) ⟩
        (a + b) - b   ≡⟨ cong (λ □ → □ - b) eq ⟩
        c - b         ∎
    where
      open ≡-Reasoning

subRHSˡ : (a b c : ℚ) → a ≡ b + c → a - b ≡ c
subRHSˡ a b c eq =
      begin
        a - b        ≡⟨ cong (_- b) eq ⟩
        b + c - b    ≡⟨ cong (_- b) (+-comm b c) ⟩
        c + b - b    ≡⟨ +-assoc c b (- b) ⟩
        c + (b - b)  ≡⟨ cong (c +_) (+-inverseʳ b)  ⟩
        c + 0ℚ       ≡⟨ +-identityʳ c ⟩
        c            ∎
    where
      open ≡-Reasoning

reassoc : (a b c d : ℚ) → a ≡ b + c + d → a ≡ b + (c + d)
reassoc a b c d eq =
      begin
        a            ≡⟨ eq ⟩
        b + c + d    ≡⟨ +-assoc b c d ⟩
        b + (c + d)  ∎
    where
      open ≡-Reasoning
```

## Using `Function.Reasoning`

I learned this technique from Matthew Daggitt on the Agda Zulip in
this
[post](https://agda.zulipchat.com/#narrow/stream/238741-general/topic/How.20to.20do.20high-school.20style.20algebraic.20reasoning.20on.20equations/near/268177299).

Using this approach one can see the algebraic equations on the right
of `∶` syntax, while the proofs which justify them appear on the left
side.

The algebraic equations, being type annotations, are actually
optional. However, they should be included for clarity's sake.

```
module _ where


  open import Function using (flip)
  open import Function.Reasoning
  open import Level

  ex1 : (a b c d : ℚ) → a + b ≡ c + d → a - c ≡ d - b
  ex1 a b c d a+b≡c+d =
       a+b≡c+d             ∶ a + b ≡ c + d
    |> subLHSʳ a b (c + d) ∶ a ≡ c + d - b
    |> reassoc a c d (- b) ∶ a ≡ c + (d - b)
    |> subRHSˡ a c (d - b) ∶ a - c ≡  d - b

  infixr 0 _∋_<|_
  _∋_<|_ : ∀ {a b : Level} {A : Set a} (B : {A} → Set b) →
            (∀ a → B {a}) → (a : A) →  B {a}
  ty ∋ f <| a = _|>_ {B = λ a → ty {a}} a f

  ex1′ : (a b c d : ℚ) → a + b ≡ c + d → a - c ≡ d - b
  ex1′ a b c d a+b≡c+d =
           a - c ≡ d - b   ∋ subRHSˡ a c (d - b)   <|
           a ≡ c + (d - b) ∋ reassoc a c d (- b)   <|
           a ≡ c + d - b   ∋ (subLHSʳ a b (c + d)) <|
           a+b≡c+d

```




## Using logical equivalence and Setoid reasoning

```
module _ where
  open import Function.Equivalence using (equivalence; ⇔-setoid; _⇔_)
  open import Level

  subLHSʳ′ : (a b c : ℚ) → (a ≡ c - b) → (a + b ≡ c)
  subLHSʳ′ a b c eq =
      begin
        a + b         ≡⟨ cong (_+ b) eq  ⟩
        (c - b) + b   ≡⟨ +-assoc c (- b) b  ⟩
        c + (- b + b) ≡⟨ cong (c +_) (+-inverseˡ b)  ⟩
        c + 0ℚ        ≡⟨ +-identityʳ c  ⟩
        c             ∎
    where
      open ≡-Reasoning

  subRHSˡ′ : (a b c : ℚ) → a - b ≡ c → a ≡ b + c
  subRHSˡ′ a b c eq =
      begin
        a         ≡⟨ {!!} ⟩
        b + c     ∎
    where
      open ≡-Reasoning

  reassoc′ : (a b c d : ℚ) → a ≡ b + (c + d) → a ≡ b + c + d
  reassoc′ a b c d eq =
      begin
        a         ≡⟨ {!!} ⟩
        b + c + d ∎
    where
      open ≡-Reasoning

  subLHSʳ⇔ : (a b c : ℚ) → (a + b ≡ c) ⇔ (a ≡ c - b)
  subLHSʳ⇔ a b c  = equivalence (subLHSʳ a b c) (subLHSʳ′ a b c)

  subRHSˡ⇔ : (a b c : ℚ) → a ≡ b + c ⇔ a - b ≡ c
  subRHSˡ⇔ a b c = equivalence (subRHSˡ a b c) (subRHSˡ′ a b c)

  reassoc⇔ : (a b c d : ℚ) → a ≡ b + c + d ⇔ a ≡ b + (c + d)
  reassoc⇔ a b c d = equivalence (reassoc a b c d) (reassoc′ a b c d)

  ex2 : (a b c d : ℚ) → a + b ≡ c + d ⇔ a - c ≡ d - b
  ex2 a b c d =
      begin
        a + b ≡ c + d       ≈⟨ subLHSʳ⇔ a b (c + d) ⟩
        a     ≡ c + d - b   ≈⟨ reassoc⇔ a c d (- b) ⟩
        a     ≡ c + (d - b) ≈⟨ subRHSˡ⇔ a c (d - b) ⟩
        a - c ≡ d - b
      ∎
    where
      open import Relation.Binary.Reasoning.Setoid (⇔-setoid 0ℓ)


```
