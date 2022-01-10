module ThisIsNotDenotationalDesign where

open import Data.Bool.Base
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Empty using (⊥)
open import Data.List
open import Level using (Level; 0ℓ) renaming (suc to lsuc)
open import Data.Maybe

-- Denotation is `ℕ → Maybe A`
record IStack {a : Level} {A : Set a} (Stack : Set a → Set a) : Set (lsuc a) where
  field
    empty : Stack A
    push  : A → Stack A → Stack A
    pop   : Stack A → Maybe A × Stack A

    -- Conal: this is axiomatic semantics not denotational
    ⟦_⟧   : Stack A → (ℕ → Maybe A) -- meaning function
    empty-law : ⟦ empty ⟧ ≗ (λ _ → nothing)
    push-law  : {x : A} {s : Stack A}
              → ⟦ push x s ⟧ ≗ λ n → if n ≡ᵇ 0 then just x else ⟦ s ⟧ (n ∸ 1)
    pop-law-1 : {s : Stack A} → proj₁ (pop s) ≡ ⟦ s ⟧ 0
    pop-law-2 : {s : Stack A} → ⟦ proj₂ (pop s) ⟧ ≗ λ n → ⟦ s ⟧ (n + 1)

{-

Start with denotation.


How do we come up with an interface.

What algebraic language do you like speaking?
That's my API

Question: how does stack work in C.

- Mutable stack representation can't be a representation of the immutable list denotation
  (but it could be part of it)

Lists - monoids, functors etc - the algebra would be suggested from these

Distinction:
-
-



-}

{-

- have we got all the laws?
- have we got enough?
- have we got too many?
- are two IStack instances obervationally equal?

-}


open IStack ⦃ … ⦄ public

empty′ : {a : Level} {A : Set a} → List A
empty′ = []

push′ : {a : Level} {A : Set a} → A → List A → List A
push′ = _∷_

pop′ : {a : Level} {A : Set a} → List A → Maybe A × List A
pop′ []       = nothing , []
pop′ (a ∷ as) = just a , as

_!_ : {a : Level} {A : Set a} → List A → ℕ → Maybe A
[] ! _       = nothing
(a ∷ _)  ! 0 = just a
(a ∷ as) ! n = as ! (n ∸ 1)

⟦_⟧′ : {a : Level} {A : Set a} → List A → (ℕ → Maybe A)
⟦ s ⟧′ = λ n → s ! n

empty-law′ : {a : Level} {A : Set a} → ⟦ empty′ {a} {A} ⟧′ ≗ (λ _ → nothing)
empty-law′ n =
    begin
      ⟦ empty′ ⟧′ n
    ≡⟨⟩
      nothing
    ≡⟨⟩
      (λ _ → nothing) n
    ∎
  where
    open ≡-Reasoning

push-law′ : ∀ {a : Level} {A : Set a} {x : A} {s : List A}
          → ⟦ push′ x s ⟧′ ≗ λ n → if n ≡ᵇ 0 then just x else ⟦ s ⟧′ (n ∸ 1)
push-law′ {_} {_} {x} {s} n =
  begin
    ⟦ push′ x s ⟧′ n
  ≡⟨⟩
    ⟦ x ∷ s ⟧′ n
  ≡⟨⟩
    (x ∷ s) ! n
  ≡⟨ foo n  ⟩
    (if n ≡ᵇ 0 then just x else s ! (n ∸ 1))
  ≡⟨⟩
    (if n ≡ᵇ 0 then just x else ⟦ s ⟧′ (n ∸ 1))
  ∎
  where
    open ≡-Reasoning
    foo : (λ n → (x ∷ s) ! n) ≗ (λ n → if n ≡ᵇ 0 then just x else s ! (n ∸ 1))
    foo 0 =
      begin
        (x ∷ s) ! 0
      ≡⟨⟩
        (if 0 ≡ᵇ 0 then just x else s ! (0 ∸ 1))
      ∎
    foo (suc n) =
      begin
        (x ∷ s) ! (suc n)
      ≡⟨⟩
        s ! n
      ≡⟨⟩
       (if suc n ≡ᵇ 0 then just x else s ! (suc n ∸ 1))
      ∎

pop-law-1′ : {a : Level} {A : Set a} {s : List A} → proj₁ (pop′ s) ≡ ⟦ s ⟧′ 0
pop-law-1′ {_} {_} {[]} = refl
pop-law-1′ {_} {_} {a ∷ as} = refl

pop-law-2′ : {a : Level} {A : Set a} {s : List A} → ⟦ proj₂ (pop′ s) ⟧′ ≗ λ n → ⟦ s ⟧′ (n + 1)
pop-law-2′ {_} {_} {[]} n = refl
pop-law-2′ {_} {_} {a ∷ as} n =
    begin
      ⟦ proj₂ (pop′ (a ∷ as)) ⟧′ n
    ≡⟨⟩
      ⟦ as ⟧′ n
    ≡⟨⟩
      as ! n
    ≡⟨ sym pf ⟩
      (a ∷ as) ! (n + 1)
    ≡⟨⟩
      ⟦ a ∷ as ⟧′ (n + 1)
    ∎
  where
    open ≡-Reasoning
    pf : ∀ {n} → (a ∷ as) ! (n + 1) ≡ as ! n
    pf {0} = refl
    pf {suc n} rewrite +-comm 1 n = refl


stack : {a : Level} {A : Set a} → IStack {a} {A} List
stack {a} {A} = record
          { empty     = empty′
          ; push      = push′
          ; pop       = pop′
          ; ⟦_⟧       = ⟦_⟧′
          ; empty-law = empty-law′
          ; push-law  = push-law′
          ; pop-law-1 = λ {s} → pop-law-1′ {a} {A} {s}
          ; pop-law-2 = λ {s} → pop-law-2′ {a} {A} {s}
          }
