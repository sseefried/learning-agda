<!-- -*-agda2-*- -->
# What I learned while studying Integers defined as quotients

In mathematics there is a well known construction whereby one can
create a mathematial structure that is functionaly equivalent to the
integers, `ℤ`, by representing each integer value as a pair of natural
numbers.

I just found a really nice example of this construction in the Agda
standard library (v2.6.2) in module
`Relation.Binary.HeterogeneousEquality.Quotients`. I have copied the
contents of that module here in order to annotate it with my own
notes. I'm hoping that this process will be useful to other as well as
myself, which is why I'm publishing it here.

## Imports and preliminaries

```agda
{-# OPTIONS --with-K --safe #-}

module AnnotatedIntegerQuotients where

open import Relation.Binary.HeterogeneousEquality.Quotients
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality hiding (isEquivalence)
import Relation.Binary.PropositionalEquality as ≡
open import Data.Nat.Base
open import Data.Nat.Properties hiding (_≟_)
open import Data.Product
open import Function.Base

open ≅-Reasoning
```

`ℕ²` is defined as convenient shorthand for `ℕ × ℕ`.

```agda
ℕ² = ℕ × ℕ
```

## The representation of integers using natural numbers

The basic idea behind representing integers as natural numbers is to
regard each pair `(a , b) : ℕ²` as equivalent to the integer `-a + b`.
So for instance, `(1 , 0)` represents `-1`, but so does `(4 , 3)`. In
fact, there is an infinitude of representations for the integer `-1`,
and also for all other integers.

However, this definition, as I have informally presented it above, is
a bit fishy as it relies on a notion of integer addition and
negation. Although these noations are familar to most of us, it is
these very notions that are we are attempting to define using only the
concepts of natural numbers and addition on natural numbers.

What is interesting, however, is that we can use our knowledge of the
properties of integer arithmetic to come up with a relationship
between two equivalent representations of an integer.

Say `(x , y)` and `(x′ , y′)` both represent the same integer. If we
pretend for a moment that `x` and `y` are integers then we can say
that


    -x + y ∼ -x′ + y′

A little algebraic manipulation then gives us

    x + y′ ∼ x + x′

Now that we have removed all mention of negation (`-`) what we are
left with will serve as a _definition_ of equivalence. This is only
possible because integer addition of integers `x` and `y` is the same
as natural number addition precisely when integers `x` and `y` are
non-negative (and `x` and `y` are interpreted as natural numbers).

Equivalence is defined in just this way in the module

```agda
_∼_ : ℕ² → ℕ² → Set
(x , y) ∼ (x′ , y′) = x + y′ ≅ x′ + y

infix 10 _∼_
```

Next we want to prove the _transitivity_ property on this definition of equivalence.
The proof is below.

```agda


∼-trans : ∀ {i j k} → i ∼ j → j ∼ k → i ∼ k
∼-trans {x₁ , y₁} {x₂ , y₂} {x₃ , y₃} p q =
  ≡-to-≅ $ +-cancelˡ-≡ y₂ $ ≅-to-≡ $ begin
  y₂ + (x₁ + y₃) ≡⟨ ≡.sym (+-assoc y₂ x₁ y₃) ⟩
  y₂ + x₁ + y₃   ≡⟨ ≡.cong (_+ y₃) (+-comm y₂ x₁) ⟩
  x₁ + y₂ + y₃   ≅⟨ cong (_+ y₃) p ⟩
  x₂ + y₁ + y₃   ≡⟨ ≡.cong (_+ y₃) (+-comm x₂ y₁) ⟩
  y₁ + x₂ + y₃   ≡⟨ +-assoc y₁ x₂ y₃ ⟩
  y₁ + (x₂ + y₃) ≅⟨ cong (y₁ +_) q ⟩
  y₁ + (x₃ + y₂) ≡⟨ +-comm y₁ (x₃ + y₂) ⟩
  x₃ + y₂ + y₁   ≡⟨ ≡.cong (_+ y₁) (+-comm x₃ y₂) ⟩
  y₂ + x₃ + y₁   ≡⟨ +-assoc y₂ x₃ y₁ ⟩
  y₂ + (x₃ + y₁) ∎
```

However, I found this quite hard to understand so I'm going to go into
a little bit more detail.

The body of the `∼-trans` definition does a pattern match on `i`, `j`
and `k` leading to the following equalities. (I used the definition of
`_∼_` above to come up with these.)

    i ∼ j = x₁ + y₂ ≅ x₂ + y₁
    j ∼ k = x₂ + y₃ ≅ x₃ + y₂
    i ∼ k = x₁ + y₃ ≅ x₃ + y₁

What I would have expected was a proof that had a structure somewhat like this:

    begin
    x₁ + y₃ ≡⟨ ... ⟩
    ...
    x₃ + y₁ ∎

However, what you'll notice is the application of  `≡-to-≅ $ +-cancelˡ-≡ y₂ $ ≅-to-≡` to
a proof of the form
    y₂ + (x₁ + y₃) ≡⟨ ... ⟩
    ...
    y₂ + (x₃ + y₁) ∎

What is going on here? First, `≅-to-≡` and `≡-to-≅` convert to and
from propositional equality `≡` from heterogenous equality (`≅`). But
it is `+-cancelˡ-≡ y₂` that does the real work. Its signature is
`+-cancelˡ-≡ : LeftCancellative _≡_ _+_`. This can be further
evaluated (with the aid of hotkey `C-u C-u C-u C-c C-d` in Emacs) to
`+-cancelˡ-≡ : ∀ x {y z : ℕ} → x + y ≡ x + z → y ≡ z`.

Thus in this context, `+-cancelˡ-≡ y₂` evaluates to a function of type
`y₂ + (x₁ + y₃) ≡ y₂ + (x₃ + y₁) → x₁ + y₃ ≡ x₃ + y₁ `. That is it
takes a proof of one equivalence and gives us the equivalence that I
was originally expecting.

With that proof out of the way we can now show that `_∼_` is an
equivalence relation as follows. The definition of `_∼_` is simple
enough that `refl` and `sym` are adequate definitions for the
corresponding `IsEquivalence` fields. Agda's normalisation takes care
of the rest.

```agda


∼-isEquivalence : IsEquivalence _∼_
∼-isEquivalence = record
  { refl  = refl
  ; sym   = sym
  ; trans = λ {i} {j} {k} → ∼-trans {i} {j} {k}
  }
```

We can now define a _setoid_ using `ℕ²` as the value type and `_∼_` as
the equivalence relation.

```agda
ℕ²-∼-setoid : Setoid 0ℓ 0ℓ
ℕ²-∼-setoid = record { isEquivalence = ∼-isEquivalence }
```

## Defining integers as a quotient

Now the real magic begins. We define a module called `Integers` that
is parameterised on `quot : Quotients 0ℓ 0ℓ` which simplifies to `quot
: (S : Setoid ℕ² 0ℓ) → Quotient S`.

At this point, I'm not sure why it's parameterised but I suspect it's
a trick that allows one to defer the problem of how a record value of
type `Quotient Int` actually gets constructed.

```agda
module Integers (quot : Quotients 0ℓ 0ℓ) where
```

We then define `Int : Quotient ℕ²-∼-setoid`.

```agda
  Int : Quotient ℕ²-∼-setoid
  Int = quot _
```

I'm unclear about what `_` means on the right-hand side of a
definition, but I'm pretty sure that it is equivalent to `Int = quot
`ℕ²-∼-setoid`.

```agda
  open Quotient Int renaming (Q to ℤ)
```

We then `open` the record so that the fields and functions `Q`, `abs`,
`compat`, `compat-abs`, `lift` and `lift-conv` are visible. It is
worth exploring the definition of the `Quotient` record using `M-.`

Next, we define just what it means to add two integer representations
together. Note that I used the phrase _integer representation_. We are
not yet at the stage where we are ready to develop notation for the
actual integers themselves. Another step of abstraction is required
for that.

```agda
  _+²_ : ℕ² → ℕ² → ℕ²
  (x₁ , y₁) +² (x₂ , y₂) = x₁ + x₂ , y₁ + y₂
```

Next we try to prove the property `+²-cong` which essentially says
that if `a` and `a′` represent the same integer, and `b` and `b′`
represent the same integer then `a +² b` represents the same integer
as `a′ +² b′`.



```agda
  +²-cong : ∀{a b a′ b′} → a ∼ a′ → b ∼ b′ → a +² b ∼ a′ +² b′
  +²-cong {a₁ , b₁} {c₁ , d₁} {a₂ , b₂} {c₂ , d₂} ab∼cd₁ ab∼cd₂ = begin
    (a₁ + c₁) + (b₂ + d₂) ≡⟨ ≡.cong (_+ (b₂ + d₂)) (+-comm a₁ c₁) ⟩
    (c₁ + a₁) + (b₂ + d₂) ≡⟨ +-assoc c₁ a₁ (b₂ + d₂) ⟩
    c₁ + (a₁ + (b₂ + d₂)) ≡⟨ ≡.cong (c₁ +_) (≡.sym (+-assoc a₁ b₂ d₂)) ⟩
    c₁ + (a₁ + b₂ + d₂)   ≅⟨ cong (λ n → c₁ + (n + d₂)) ab∼cd₁ ⟩
    c₁ + (a₂ + b₁ + d₂)   ≡⟨ ≡.cong (c₁ +_) (+-assoc a₂ b₁ d₂) ⟩
    c₁ + (a₂ + (b₁ + d₂)) ≡⟨ ≡.cong (λ n → c₁ + (a₂ + n)) (+-comm b₁ d₂) ⟩
    c₁ + (a₂ + (d₂ + b₁)) ≡⟨ ≡.sym (+-assoc c₁ a₂ (d₂ + b₁)) ⟩
    (c₁ + a₂) + (d₂ + b₁) ≡⟨ ≡.cong (_+ (d₂ + b₁)) (+-comm c₁ a₂) ⟩
    (a₂ + c₁) + (d₂ + b₁) ≡⟨ +-assoc a₂ c₁ (d₂ + b₁) ⟩
    a₂ + (c₁ + (d₂ + b₁)) ≡⟨ ≡.cong (a₂ +_) (≡.sym (+-assoc c₁ d₂ b₁)) ⟩
    a₂ + (c₁ + d₂ + b₁)   ≅⟨ cong (λ n → a₂ + (n + b₁)) ab∼cd₂ ⟩
    a₂ + (c₂ + d₁ + b₁)   ≡⟨ ≡.cong (a₂ +_) (+-assoc c₂ d₁ b₁) ⟩
    a₂ + (c₂ + (d₁ + b₁)) ≡⟨ ≡.cong (λ n → a₂ + (c₂ + n)) (+-comm d₁ b₁) ⟩
    a₂ + (c₂ + (b₁ + d₁)) ≡⟨ ≡.sym (+-assoc a₂ c₂ (b₁ + d₁)) ⟩
    (a₂ + c₂) + (b₁ + d₁) ∎
```

The body of the proof was still a bit confusing to me, so let's go
into what is going on. Each of the type variables in the signature is
pattern matched upon in the definition. The following equalities hold

    a = a₁ , b₁
    b = c₁ , d₁
    a′ = a₂ , b₂
    b′ = c₂ , d₂
    a  +² b  = (a₁ , b₁) +² (c₁ , d₁)
    a′ +² b′ = (a₂ , b₂) +² (c₂ , d₂)

We are trying to prove that `a +² b ∼ a′ +² b′`. Using the definition
of `_+²_` this means we are trying to show that

   (a₁ , b₁) +² (c₁ , d₁) ∼ (a₂ , b₂) +² (c₂ , d₂)

or

   (a₁ + c₁ , b₁ + d₁) ~ (a₂ + c₂ , b₂ + d₂)

Now, using the definition of `_∼_` we find that we are trying to show

   (a₁ + c₁) + (b₂ + d₂) ≅ (a₂ + c₂) + (b₁ + d₁)

This is precisely what the body of the definition proves.


[TODO: True? ]
## Extensionality on integers???


The `module _` trick below brings the `ext` variable into scope on all
the definitions inside the module body. e.g. `_+ℤ_` does not have type
`ℤ → ℤ → ℤ` but rather `∀ {a b} {A : Set a} {B₁ B₂ : A → Set b} {f₁ :
∀ a → B₁ a} {f₂ : ∀ a → B₂ a} → (∀ a → f₁ a ≅ f₂ a) → f₁ ≅ f₂ → ℤ → ℤ
→ ℤ`

```agda
  module _ (ext : ∀ {a b} {A : Set a} {B₁ B₂ : A → Set b} {f₁ : ∀ a → B₁ a}
                  {f₂ : ∀ a → B₂ a} → (∀ a → f₁ a ≅ f₂ a) → f₁ ≅ f₂) where

    _+ℤ_ : ℤ → ℤ → ℤ
    _+ℤ_ = Properties₂.lift₂ ext Int Int (λ i j → abs (i +² j))
         $ λ {a} {b} {c} p p′ → compat-abs (+²-cong {a} {b} {c} p p′)

    zero² : ℕ²
    zero² = 0 , 0

    zeroℤ : ℤ
    zeroℤ = abs zero²

    +²-identityʳ : (i : ℕ²) → (i +² zero²) ∼ i
    +²-identityʳ (x , y) = begin
      (x + 0) + y ≡⟨ ≡.cong (_+ y) (+-identityʳ x) ⟩
      x + y       ≡⟨ ≡.cong (x +_) (≡.sym (+-identityʳ y)) ⟩
      x + (y + 0) ∎

    +ℤ-on-abs≅abs-+₂ : ∀ a b → abs a +ℤ abs b ≅ abs (a +² b)
    +ℤ-on-abs≅abs-+₂ = Properties₂.lift₂-conv ext Int Int _
                     $ λ {a} {b} {c} p p′ → compat-abs (+²-cong {a} {b} {c} p p′)

    +ℤ-identityʳ : ∀ i → i +ℤ zeroℤ ≅ i
    +ℤ-identityʳ = lift _ eq (≅-heterogeneous-irrelevantʳ _ _ ∘ compat-abs) where

      eq : ∀ a → abs a +ℤ zeroℤ ≅ abs a
      eq a = begin
        abs a +ℤ zeroℤ      ≡⟨⟩
        abs a +ℤ abs zero²  ≅⟨ +ℤ-on-abs≅abs-+₂ a zero² ⟩
        abs (a +² zero²)    ≅⟨ compat-abs (+²-identityʳ a) ⟩
        abs a               ∎

    +²-identityˡ : (i : ℕ²) → (zero² +² i) ∼ i
    +²-identityˡ i = refl

    +ℤ-identityˡ : (i : ℤ)  → zeroℤ +ℤ i ≅ i
    +ℤ-identityˡ = lift _ eq (≅-heterogeneous-irrelevantʳ _ _ ∘ compat-abs) where

      eq : ∀ a → zeroℤ +ℤ abs a ≅ abs a
      eq a = begin
        zeroℤ +ℤ abs a     ≡⟨⟩
        abs zero² +ℤ abs a ≅⟨ +ℤ-on-abs≅abs-+₂ zero² a ⟩
        abs (zero² +² a)   ≅⟨ compat-abs (+²-identityˡ a) ⟩
        abs a              ∎

    +²-assoc : (i j k : ℕ²) → (i +² j) +² k ∼ i +² (j +² k)
    +²-assoc (a , b) (c , d) (e , f) = begin
      ((a + c) + e) + (b + (d + f)) ≡⟨ ≡.cong (_+ (b + (d + f))) (+-assoc a c e) ⟩
      (a + (c + e)) + (b + (d + f)) ≡⟨ ≡.cong ((a + (c + e)) +_) (≡.sym (+-assoc b d f)) ⟩
      (a + (c + e)) + ((b + d) + f) ∎

    +ℤ-assoc : ∀ i j k → (i +ℤ j) +ℤ k ≅ i +ℤ (j +ℤ k)
    +ℤ-assoc = Properties₃.lift₃ ext Int Int Int eq compat₃ where

      eq : ∀ i j k → (abs i +ℤ abs j) +ℤ abs k ≅ abs i +ℤ (abs j +ℤ abs k)
      eq i j k = begin
        (abs i +ℤ abs j) +ℤ abs k ≅⟨ cong (_+ℤ abs k) (+ℤ-on-abs≅abs-+₂ i j) ⟩
        (abs (i +² j) +ℤ abs k)   ≅⟨ +ℤ-on-abs≅abs-+₂ (i +² j) k ⟩
        abs ((i +² j) +² k)       ≅⟨ compat-abs (+²-assoc i j k) ⟩
        abs (i +² (j +² k))       ≅⟨ sym (+ℤ-on-abs≅abs-+₂ i (j +² k)) ⟩
        (abs i +ℤ abs (j +² k))   ≅⟨ cong (abs i +ℤ_) (sym (+ℤ-on-abs≅abs-+₂ j k)) ⟩
        abs i +ℤ (abs j +ℤ abs k) ∎

      compat₃ : ∀ {a a′ b b′ c c′} → a ∼ a′ → b ∼ b′ → c ∼ c′ → eq a b c ≅ eq a′ b′ c′
      compat₃ p q r = ≅-heterogeneous-irrelevantˡ _ _
                    $ cong₂ _+ℤ_ (cong₂ _+ℤ_ (compat-abs p) (compat-abs q))
                    $ compat-abs r
```

----------------------

```agda

open import Data.Bool
open import Relation.Nullary

-- Bool is the sign bit. false = negative, true = positive
data Z : Set where
  int : Bool → ℕ → Z

infixl 5 _+Z_
_+Z_ : Z → Z → Z
(int s₀ n₀) +Z (int s₁ n₁) with s₀ ≟ s₁
... | yes _  = int s₀ (n₀ + n₁)
... | no _ = if n₀ ≤ᵇ n₁ then int s₁ (n₁ ∸ n₀) else int s₀ (n₀ ∸ n₁)

abs-Z : ℕ² → Z
abs-Z (neg , pos) = if neg ≤ᵇ pos then int true (pos ∸ neg) else int false (neg ∸ pos)

-- Z-setoid : Setoid 0ℓ 0ℓ
-- Z-setoid = record { Carrier = Z }

quot : Set → Quotient ℕ²-∼-setoid
quot s = record { Q = Z ; abs = abs-Z  ; compat-abs = {!!} ; lift = {!!} ; lift-conv = {!!}   }


compat-abs : {a a′ : ℕ²} → a ∼ a′ → abs-Z a ≅ abs-Z a′
compat-abs {x , y} {x′ , y′} eq =
  begin
    abs-Z (x , y) ≡⟨⟩
    (if x  ≤ᵇ y  then int true (y  ∸ x)  else int false (x  ∸ y)) ≅⟨ cong ((λ b → if b then  int true (y ∸ x) else int false (x  ∸ y))) (foo1 {x} {y} {x′} {y′} eq) ⟩
    (if x′ ≤ᵇ y′ then int true (y ∸ x) else int false (x ∸ y)) ≡⟨ {!!} ⟩
    (if x′ ≤ᵇ y′ then int true (y′ ∸ x′) else int false (x′ ∸ y′)) ≡⟨ {!!} ⟩
    abs-Z (x′ , y′)
  ∎

  where
    open ≅-Reasoning
    foo1 : ∀ {x y x′ y′} → x + y′ ≅ x′ + y → (x ≤ᵇ y) ≅ (x′ ≤ᵇ y′)
    foo1 eq =  ?


--    x + y′ ≅ x′ + y
--    x ∸ y  ≅ x′ - y′

--

-- open Integers quot

```
