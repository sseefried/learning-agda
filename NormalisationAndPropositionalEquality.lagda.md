<!-- -*-agda2-*- -->
# Normalisation and Propositional Equality



## Transcript of my question on the Agda Zulip

[Zulip](agda.zulipchat.com) is yet another instant messaging platform. Here's what I wrote on there. [Link](https://agda.zulipchat.com/#narrow/stream/259644-newcomers/topic/Normalising.20and.20C-c.20C-n.20in.20Emacs.20Agda.20mode)

----

Sean Seefried: I've just done the following simple proof. If I use C-c C-n in Emacs Agda it shows me that `uncurry _∧_` and
`λ x → proj₁ x ∧ proj₂ x` are already normalised but yet the proof pf below goes through. Why is this?

It was my understanding that ≡ on functions in _intensional_ and so the normal forms must be the same.


    module NormaliseExample where
    
    open import Data.Bool
    open import Data.Product
    open import Relation.Binary.PropositionalEquality
    
    pf : uncurry _∧_ ≡ λ x → proj₁ x ∧ proj₂ x
    pf = begin
        uncurry _∧_
      ≡⟨⟩
        (λ (x , y) → _∧_ x y)
      ≡⟨⟩
        (λ (x , y) → x ∧ y)
      ≡⟨⟩
        (λ x → proj₁ x ∧ proj₂ x)
      ∎
      where
        open ≡-Reasoning
    
    -- Use C-c C-n in holes below.
    ex₁ : Set
    ex₁ = {! uncurry _∧_ !}
    
    ex₂ : Set
    ex₂ = {! λ x → proj₁ x ∧ proj₂ x !}

Andrea Vezzosi: C-c C-n normalizes only with beta rules, it does not eta expand things. equality checking however does use eta, so functions are equal if they normalize to equal terms when applied to fresh variables.

Sean Seefried: @Andrea Vezzosi thanks! Is there a bit of documentation that you know of that speaks about this? A reference would be really useful to me.

Jesper Cockx: I think this is the most relevant reference for it: http://www.cse.chalmers.se/~abela/unif-sigma-long.pdf

Jesper Cockx: That's mostly about the way Agda does the conversion checking (through higher-order unification), there's of course also a lot of stuff you can find about eta-equality in general

Andrea Vezzosi: Figure 3 and 4 of https://dl.acm.org/doi/10.1145/3158111 might be more readable (expect[sic] for the De Bruijn notation).
Fig 3 gives you a declarative description of the equality relation. While Fig 4 gives you reduction. C-c C-n is iterated reduction. The equality checking algorithm, which makes use of reduction, is in figure 6.

The article does not cover unification, or record types, but might be a good place to start.

https://dl.acm.org/doi/10.1145/3158111

----

Here is the program I based my question on

```
module NormalisationAndPropositionalEquality where

open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality

pf : uncurry _∧_ ≡ λ x → proj₁ x ∧ proj₂ x
pf = begin
    uncurry _∧_
  ≡⟨⟩
    (λ (x , y) → _∧_ x y)
  ≡⟨⟩
    (λ (x , y) → x ∧ y)
  ≡⟨⟩
    (λ x → proj₁ x ∧ proj₂ x)
  ∎
  where
    open ≡-Reasoning

-- Use C-c C-n in holes below.
ex₁ : Set
ex₁ = {! uncurry _∧_ !}

ex₂ : Set
ex₂ = {! λ x → proj₁ x ∧ proj₂ x !}
```
