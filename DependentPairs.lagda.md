<!-- -*-agda2-*- -->
# Dependent Pairs


Dependent Pairs are defined as follows in module `Agda.Builtin.Sigma`

    record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
      constructor _,_
      field
        fst : A
        snd : B fst    

The second element of the pair is dependent on the type of the first.
You will recall that Finite Sets are defined as follows in `Data.Fin`

    data Fin : ℕ → Set where
      zero : {n : ℕ} → Fin (suc n)
      suc  : {n : ℕ} (i : Fin n) → Fin (suc n)

Let's do some imports first.
```
open import Data.Nat
import Data.Fin as F
open F using (Fin)
open import Agda.Builtin.Sigma
```

Now let's look at three values in `Fin 3` representing
`0`, `1` and `2` in `ℕ` respectively.

```
fin0/3 : Fin 3
fin0/3 = F.zero

fin1/3 : Fin 3
fin1/3 = F.suc F.zero

fin2/3 : Fin 3
fin2/3 = F.suc (F.suc F.zero)
```

It turns out that dependent pairs can be used to model
Finite Sets as well. I learned that [here](https://people.inf.elte.hu/divip/AgdaTutorial/Sets.Sigma.html)
(under the heading **Σ as Subset**)

An alternative definition for Finite Sets is `Fin'` below:

```
Fin' : ℕ → Set
Fin' n = Σ ℕ (λ m → m < n)
```

The first element of the pair is a natural number and the second element
is a proof that it is less than a particular natural number.

Here are some examples of values of `Fin'` which correspond to the values of
`Fin` I defined above:

```
fin'0/3 : Fin' 3
fin'0/3 = (0 , 0<3)
  where
    0<3 : 0 < 3
    0<3 = s≤s z≤n

fin'1/3 : Fin' 3
fin'1/3 = (1 , 1<3)
  where
    1<3 : 1 < 3
    1<3 = s≤s (s≤s z≤n)

fin'2/3 : Fin' 3
fin'2/3 = (2 , 2<3)
  where
    2<3 : 2 < 3
    2<3 = s≤s (s≤s (s≤s z≤n))
```

We can define a function that converts between the two representations
as follows:

```
toFin : {n : ℕ} → Fin' n → Fin n
toFin (zero , s≤s z≤n) = F.zero
toFin (suc n , s≤s p) = F.suc (toFin (n , p))
```

Finally here some applications of `toFin`. I've
left holes so that you can use Emacs shortcut keys such
as `C-c C-n` (normalise) and `C-c C-d` (type of) to
see their values.

```
toFin0/3 : Fin 3
toFin0/3 = {! toFin fin'0/3 !}

toFin1/3 : Fin 3
toFin1/3 = {! toFin fin'1/3 !}

toFin2/3 : Fin 3
toFin2/3 = {! toFin fin'2/3 !}
```
