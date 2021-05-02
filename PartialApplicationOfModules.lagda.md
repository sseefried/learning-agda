<!-- -*-agda2-*- -->
# Partial application of modules


It's all very adequately explained here: https://agda.readthedocs.io/en/v2.5.2/language/module-system.html#parameterised-modules

```
module PartialApplicationOfModules where

  open import Data.List
```

Here is a module. It has three parameters.

```
  module Folding (A : Set) (id : A) (_+_ : A → A → A) where

    open import Data.List

    fold : List A → A
    fold [] = id
    fold (x ∷ xs) = x + fold xs
```

You can just open the module without providing any values for the parameters. This will add those missing parameters as extra arguments to
every definition within the module. The type of `fold` below is `(A : Set) (id : A) (_+_ : A → A → A) → List A → A` which you can
verify for yourself using `C-c C-d`

```
  module Example1 where

    open Folding

    example : Set
    example = {! fold!}
```

If you provide parameters then `fold` will have its types specialised. The type is `List ℕ → ℕ` below

```
  module Example1a where
    open import Data.Nat

    open Folding ℕ zero _+_

    example : Set
    example = {! fold !}
```

But you can partially apply to a module! The type of `fold` below is `(id : ℕ) (_+₁_ : ℕ → ℕ → ℕ) → List ℕ → ℕ`

```
  module Example2 where
    open import Data.Nat

    open Folding ℕ

    example : Set
    example = {! fold !}

```

And `(_+₁_ : ℕ → ℕ → ℕ) → List ℕ → ℕ` below

```
  module Example3 where
    open import Data.Nat

    open Folding ℕ zero

    example : Set
    example = {! fold !}

```

Just like for functions you can only partially apply in the order
that the parameters appear in the declaration.

Now let's look at another example


```
  module Composer {A B C : Set} (f : B → C) (g : A → B) where
    open import Function

    composed : A → C
    composed = f ∘ g
```

The type of `composed` is `{A B C : Set} (f : B → C) (g : A → B) → A → C` below.

```
  module Example5 where
    open import Data.Nat
    open Composer 

    example : Set
    example = {! composed !} 

```

Because we have implicit parameters you can omit then. Plus we can apply
selectively using their name. 

In the following example `B` and `C` can be inferred (from the type of `suc`)
and only the implicit argument `{A = ℕ}` needs to be provided. applications involving
named arguments B and C can be ommited.

```
  module Example6 where
    open import Data.Nat
    open Composer {A = ℕ} suc

    example : Set
    example = {! composed !} 

```

But remember, you can omit implicit parameters but you can't reorder applications. The follow is illegal:

    open Compose {B = ℕ} {A = ℕ}
