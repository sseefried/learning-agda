# Permutations

```agda
module Permutations where

module SplitPermute1 where

  open import Data.Nat using (β; _+_)
  open import Data.Fin renaming (Fin to π½) hiding (_+_)
  open import Data.Fin.Properties hiding (setoid)
  open import Relation.Binary.PropositionalEquality using (_β‘_; _β_)
  open import Data.Sum
  open import Data.Sum.Properties
  open import Function
  open import Function.Bundles
  open import Level using (Level)

  splitPermute : (m : β) {n : β} β (π½ (m + n) β π½ (n + m))
  splitPermute m {n} = join n m β swap β splitAt m

  cong-[_]ββ¨_β©β[_] :
    {a : Level} {Aβ² A B Bβ² : Set a}
    β (h : B β Bβ²)
    β {f g : A β B}
    β f β g
    β (hβ² : Aβ² β A)
    β h β f β hβ² β h β g β hβ²
  cong-[_]ββ¨_β©β[_] h {f} {g} fβg hβ² = Ξ» x β cong h (fβg (hβ² x))
    where
      open Relation.Binary.PropositionalEquality using (cong)

  inverse : {m n : β} β splitPermute n β splitPermute m β id
  inverse {m} {n} =
    begin
      (splitPermute n β splitPermute m)                             β‘β¨β©
      (join m n β swap β splitAt n) β (join n m β swap β splitAt m) β‘β¨β©
      (join m n β swap β splitAt n β join n m β swap β splitAt m)   ββ¨ cong-[ join m n β swap ]ββ¨ splitAt-join n m β©β[ swap β splitAt m ] β©
      (join m n β swap β swap β splitAt m)                          ββ¨ cong-[ join m n ]ββ¨ swap-involutive β©β[ splitAt m ] β©
      (join m n β splitAt m)                                        ββ¨ join-splitAt m n β©
      id
    β
    where
      open import Relation.Binary.PropositionalEquality
      open import Relation.Binary.Reasoning.Setoid (π½ (m + n) β-setoid π½ (m + n))

  splitPermuteβ : (m : β) {n : β} β (π½ (m + n) β π½ (n + m))
  splitPermuteβ m {n} = mkββ² (splitPermute m) (splitPermute n) (inverse {n} {m}) (inverse {m} {n})
```

## A constructive approach

There is no need for proofs with this approach! The proofs are part of
each `Inverse` record. Conal Elliott calls this _compositional correctness_.

```agda
module SplitPermute2 where

  open import Data.Nat using (β; _+_)
  open import Data.Fin renaming (Fin to π½) hiding (_+_)
  open import Data.Fin.Properties hiding (setoid)
  open import Function.Construct.Composition hiding (inverse)
  open import Function.Construct.Symmetry using (sym-β)
  open import Function using (mkββ²; _β_)
  open import Function.Bundles using (Inverse)
  open import Data.Sum
  open import Data.Sum.Properties

  open Inverse

  swapβ : β {a b} {A : Set a} {B : Set b} β  (A β B) β (B β A)
  swapβ {a} {b} {A} {B} = mkββ² swap swap swap-involutive swap-involutive

  splitPermuteβ : (m : β) {n : β} β π½ (m + n) β π½ (n + m)
  splitPermuteβ m {n} = (+ββ {m} {n} β-β swapβ) β-β sym-β +ββ
```
