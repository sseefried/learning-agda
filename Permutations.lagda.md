# Sorting

```
module Permutations where

open import Data.Nat using (ℕ)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Data.Fin renaming (Fin to 𝔽)
open import Data.Fin.Properties hiding (setoid)
open import Function.Inverse
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; module ≡-Reasoning)
open import Relation.Nullary
open import Function.LeftInverse
open import Function.Equality using (_⟶_)
open import Level using (0ℓ)
open import Relation.Binary.Bundles
open import Data.Product

Perm : ℕ → Set
Perm n = 𝔽 n ↔ 𝔽 n

-- 𝔽(m + n) ⇔ 𝔽(m) ⊎ 𝔽(n) ⇔ 𝔽(n) ⊎ 𝔽(m) ⇔ 𝔽(n + m)
--


-- vocabulary
-- mathematical properties give you ways to prove things



-- (02) --
-- (13) --

+1-mod-n : {n : ℕ} → 𝔽 n → 𝔽 n
+1-mod-n {ℕ.suc n} m with n ℕ.≟ toℕ m
... | no m≢n  = suc (lower₁ m m≢n)
... | yes _ = zero

-1-mod-n : {n : ℕ} → 𝔽 n → 𝔽 n
-1-mod-n {ℕ.suc n} zero = fromℕ n
-1-mod-n {ℕ.suc n} (suc m) = inject₁ m


i≡j⇒j<i+1 : ∀ {i j } → i ≡ j → j ℕ.< ℕ.suc i
i≡j⇒j<i+1 {i} {j} i≡j =
  begin
    ℕ.suc j
  ≡⟨ cong ℕ.suc (≡-sym i≡j) ⟩
    ℕ.suc i
  ∎
  where
    open Relation.Binary.PropositionalEquality renaming (sym to ≡-sym)
    open ℕ.≤-Reasoning

open ≡-Reasoning

left-inverse′ : (n : ℕ) → (x : 𝔽 n) → -1-mod-n (+1-mod-n x) ≡ x
left-inverse′ ℕ.zero ()
left-inverse′ (ℕ.suc ℕ.zero) zero = refl
left-inverse′ (ℕ.suc (ℕ.suc n′)) x
            with ℕ.suc n′ ℕ.≟ toℕ x
...  | no n+1≢x with x
...               | zero = refl
...               | suc x =
    begin
      -1-mod-n (suc (lower₁ (suc x) n+1≢x))
    ≡⟨⟩
      inject₁ (lower₁ (suc x) n+1≢x)
    ≡⟨  inject₁-lower₁ (suc x) n+1≢x ⟩
      suc x
    ∎
left-inverse′ (ℕ.suc (ℕ.suc n)) x
     | yes n+1≡x =
   begin
     -1-mod-n zero
   ≡⟨⟩
     fromℕ (ℕ.suc n)
   ≡⟨ fromℕ-def (ℕ.suc n) ⟩
     fromℕ< n+1<n+2
   ≡⟨ fromℕ<-cong (ℕ.suc n) (toℕ x) n+1≡x n+1<n+2 (i≡j⇒j<i+1 n+1≡x) ⟩
      fromℕ< (i≡j⇒j<i+1 n+1≡x )
   ≡⟨ fromℕ<-toℕ x (i≡j⇒j<i+1 n+1≡x)  ⟩
     x
   ∎
   where
     n+1<n+2 : ℕ.suc n ℕ.< ℕ.suc (ℕ.suc n)
     n+1<n+2 = ℕ.s≤s (ℕ.s≤s (ℕ.≤-reflexive refl))

{- right-inverse′ : (n : ℕ) → (x : 𝔽 n) → +1-mod-n′ (-1-mod-n x) ≡ x
right-inverse′ (ℕ.suc n) zero
  with fromℕ n ≟ fromℕ n
... | yes _ =
  begin
    +1-mod-n′ (-1-mod-n zero)
  ≡⟨ {!!} ⟩
    zero
  ∎
-}


module PermGroup (n : ℕ) where
  open import Algebra.Structures {A = Perm n } _≡_
  open import Algebra.Definitions {A = Perm n } _≡_
  open import Relation.Binary.PropositionalEquality

  identity : Perm n
  identity =
      record
        { to = record { _⟨$⟩_ = λ x → x ; cong = λ z → z }
        ; from = record { _⟨$⟩_ = λ x → x ; cong = λ z → z }
        ; inverse-of =
            record
               { left-inverse-of = left-inverse
               ; right-inverse-of = right-inverse
               }
        }
    where
      open ≡-Reasoning
      left-inverse : (x : 𝔽 n) → x ≡ x
      left-inverse _ = refl

      right-inverse : (x : 𝔽 n) → x ≡ x
      right-inverse _ = refl

  sucPred : Perm n
  sucPred =
    record
      { to = to′
      ; from = from′
      ; inverse-of =
          record
            { left-inverse-of = left-inverse
            ; right-inverse-of = right-inverse
            }
      }
    where
       open ≡-Reasoning
       to-cong : ∀ {i j} → i ≡ j → +1-mod-n i ≡ +1-mod-n j
       to-cong refl = refl

       from-cong : ∀ {i j} → i ≡ j → -1-mod-n i ≡ -1-mod-n j
       from-cong refl = refl

       to′ : setoid (𝔽 n) ⟶ setoid (𝔽 n)
       to′ = record
               { _⟨$⟩_ = +1-mod-n
               ; cong = to-cong
               }

       from′ : setoid (𝔽 n) ⟶ setoid (𝔽 n)
       from′ = record
            { _⟨$⟩_ = -1-mod-n
            ; cong = from-cong
            }


       left-inverse : (x : 𝔽 n) → -1-mod-n (+1-mod-n x) ≡ x
       left-inverse x = left-inverse′ n x

       right-inverse : (x : 𝔽 n) → +1-mod-n (-1-mod-n x) ≡ x
       right-inverse = {!!}
```
