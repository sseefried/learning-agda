<!-- -*-agda2-*- -->

```
module CannotModelAffineFunctions where


open import Data.Product
open import Data.Float
import Data.Float as ℝ
open import Relation.Binary.PropositionalEquality


ℝ : Set
ℝ = Float

IsAffine : (ℝ → ℝ) → Set
IsAffine f = ∃[ a ] ∃[ b ] ∀ x → f x ≡ a ℝ.* x ℝ.+ b
```

I can't complete the following proof since the final equation is probably not true for
`Float`s!

A perfect example of why we need exact real arithmetic.

I guess I could use Dedekind cuts or Cauchy Sequences

```
pf0 : {f g : ℝ → ℝ} → IsAffine f → IsAffine g → IsAffine (λ x → f x ℝ.+ g x)
pf0 {f} {g} (a , b , p₁) (c , d , p₂) = (a ℝ.+ c , b ℝ.+ d , pf2 )
        where
          open ≡-Reasoning
          pf2 : (x : ℝ) → f x ℝ.+ g x ≡ (a ℝ.+ c) * x ℝ.+ (b ℝ.+ d)
          pf2 x =
            begin
              f x ℝ.+ g x
            ≡⟨ cong₂ (λ □ ◯ →  □ ℝ.+ ◯) (p₁ x) (p₂ x)   ⟩
             (a * x ℝ.+ b) ℝ.+ (c * x ℝ.+ d)
            ≡⟨ {!!} ⟩
              (a ℝ.+ c) * x ℝ.+ (b ℝ.+ d)
            ∎
```
