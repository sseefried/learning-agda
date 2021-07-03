<!-- -*-agda2-*- -->

# Function `subst` and patterns of recursion

```
module SubstAndPatternOfRecursion where

open import Data.Fin
open import Data.Nat as ℕ
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
```

I wanted to explain to the channel what I mean by "pattern of recursion is the same"


   inject+ : ∀ {m} n → Fin m → Fin (m ℕ.+ n)
   inject+ n zero    = zero
   inject+ n (suc i) = suc (inject+ n i)



and

_+_ : Nat → Nat → Nat
zero  + m = m
suc n + m = suc (n + m)


The pattern matches in inject+ are on the Fin m and the result in Fin
(m ℕ.+ n). For this reason the pattern matching in the invocation of m
ℕ.+ n perfectly matches that pattern matching of the Fin m value.

When we try to define inject+2 : ∀ {m} n → Fin m → Fin (n ℕ.+ m) where
we have swapped m and n in the result type then this no longer
holds. This makes it hard (perhaps impossible) to define inject+2
directly. At least I couldn't find a way.

```
inject+2 : ∀ {m} n → Fin m → Fin (n ℕ.+ m)
inject+2 {m} n i = subst Fin (+-comm m n) (inject+ n i)
```
