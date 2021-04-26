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
open import Data.Nat using (s≤s; z≤n; ℕ)
import Data.Nat as N
open import Data.Fin
open import Level using (0ℓ)
import Level as L
open import Relation.Binary.Core
open import Function
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

Now let's say we want to prove that `fin1/3` is less than
or equal to `fin2/3`. How do we do this? Let's first look
at the case for natural numbers, `ℕ`.

The module `Data.Nat.Base` defines the following data structure


    data _≤_ : Rel ℕ 0ℓ where
      z≤n : ∀ {n}                 → zero  ≤ n
      s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n


The constructor `z≤n` constructs a proof that `zero ≤ n`
while `s≤s`, given a proof that `m ≤ n` constructs a proof
that `suc m ≤ suc n`.

We can prove that `1 ≤ 2` as follows. (We have imported `Data.Nat`
qualified as `N`)


```
1≤2 : 1 N.≤ 2
1≤2 = s≤s z≤n
```

However, what about similar proofs on `Fin` values? It turns out
that exactly the same constructors, `s≤s` and `z≤n` are used to
construct proofs for `Fin` as for `ℕ`. This can be seen in the
proof below.

```
fin1/3≤fin2/3 : fin1/3 ≤ fin2/3
fin1/3≤fin2/3 = s≤s z≤n
```

How is this possible? Finding out why took me considerable time
and required me to correct some faulty thinking. This post
serves as a record of my discovery process.

The first thing one discovers is that `Data.Fin._≤_` is defined as

    _≤_ : ∀ {n} → Rel (Fin n) ℓ₀
    _≤_ = ℕ._≤_ on toℕ

The first thing you'll notice is that this is a function declaration,
not a data type declaration.  I had already seen this `Rel` term in
definition of the data structure `Data.Nat._≤_` as

    data _≤_ : Rel ℕ 0ℓ where

Looking into the definition of `Rel` we find that it is defined as follows in
module `

    Rel : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
    Rel A ℓ = REL A A ℓ

    REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
    REL A B ℓ = A → B → Set ℓ

In Agda there is no real distinction between the value and the type level
which can be confusing for a newcomer. And it is certainly confused this
newcomer. In attempting to normalise the terms `Rel ℕ 0ℓ` and `Rel (Fin n) ℓ₀`
I got the wrong result completely. I looked at the _type_ of `Rel` but not
at the body of the `Rel` definition.

Fortunately, you can use Agda to help you. In the following definition
put your cursor over the whole and use the `C-c C-n` hotkey.

```
normaliseRel1 : Set (L.suc 0ℓ)
normaliseRel1 = {! Rel ℕ 0ℓ !}
```

You will find that it normalises to `ℕ → ℕ → Set`.
Similarly you'll find that the following normalises to `Fin n → Fin n → Set`.

```
normaliseRel2 : {n : ℕ} → Set (L.suc 0ℓ)
normaliseRel2 {n} = {! Rel (Fin n) 0ℓ !}
```


Let's look at the definition of `Data.Fin._≤_` again.

    _≤_ : ∀ {n} → Rel (Fin n) ℓ₀
    _≤_ = ℕ._≤_ on toℕ

It could just as easily have been written:

    _≤_ : ∀ {n} → Fin n → Fin n → Set
    _≤_ = ℕ._≤_ on toℕ


Let's try using the `C-c C-n` hotkey on the body
of the definition below.

```
normaliseBody : ∀ {n} → Fin n → Fin n → Set
normaliseBody = {! N._≤_ on toℕ !}
```

We find that it normalises to

    λ x y → toℕ x N.≤ toℕ y

This explains why we can use inequality proofs on `ℕ`
when trying to prove inequalities on `Fin` values.


When one writes `fin1/3≤fin2/3 : fin1/3 ≤ fin2/3`
the type is normalised to `1 N.≤ 2` as one can see
by using the `C-c C-n` hotkey below.

```
typeOfFin1/3≤fin2/3 : Set
typeOfFin1/3≤fin2/3 = {! fin1/3 ≤ fin2/3 !}
```

This explains why a value of type `1 N.≤ 2` will
suffice as a proof for `fin1/3≤fin2/3 : fin1/3 ≤ fin2/3`.


