# In Agda you can, and sometimes need to do an `import` before a `module` declarations

It turns out that in Agda you sometimes need to do `import`s before `module` declarations.
There is nothing like this in Haskell and, in fact, its invalid syntax.

I've copied and pasted the definition of `Relation.Binary.Partial.Setoid` below
to show the idiom.

The line `open import Relation.Binary` brings the type `PartialSetoid` into scope
which is type of the `S` parameter of the module.

```
{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for reasoning with a partial setoid
------------------------------------------------------------------------

open import Relation.Binary

module ImportsBeforeModuleDeclaration -- was Relation.Binary.Partial.Setoid
  {s₁ s₂} (S : PartialSetoid s₁ s₂) where

open PartialSetoid S
import Relation.Binary.Reasoning.Base.Partial _≈_ trans as Base

------------------------------------------------------------------------
-- Re-export the contents of the base module

open Base public
  hiding (step-∼)

------------------------------------------------------------------------
-- Additional reasoning combinators

infixr 2 step-≈ step-≈˘

-- A step using an equality

step-≈ = Base.step-∼
syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

-- A step using a symmetric equality

step-≈˘ : ∀ x {y z} → y IsRelatedTo z → y ≈ x → x IsRelatedTo z
step-≈˘ x y∼z y≈x = x ≈⟨ sym y≈x ⟩ y∼z
syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z
```
