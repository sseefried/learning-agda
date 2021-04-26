<!-- -*-agda2-*- -->
# Using inequality proofs from `ℕ` for the `Fin` data structure

The Finite Sets data structure in module `Data.Fin` is
useful, among other things, for indexing into the vector
data structure. It represents natural numbers less than
a given natural number. e.g. The type `Fin 3` contains
three values `zero`, `suc zero` and `suc (suc zero)`
(and no more).

This post demonstrates something I learned while trying
to do inequality proofs on values of type `Fin n`.

<!--
```
open import Data.Nat using (s≤s; z≤n)
open import Data.Fin
-- open import Relation.Binary.PropositionalEquality
```
-->

Let's look at two values from `Fin 3` that represent
1 and 2 respectively.

```
fin1/3 : Fin 3
fin1/3 = suc zero

fin2/3 : Fin 3
fin2/3 = suc (suc zero)
```



