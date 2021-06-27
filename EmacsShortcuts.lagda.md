<!-- -*-agda2-*- -->



<!--
```
module EmacsShortcuts where

open import Relation.Binary.PropositionalEquality


```
-->

# Emacs Shortcuts


## Computing normal forms

Just learned the `C-u C-u` prefix in Emacs when working with shortcuts
that work on terms or types. So useful!

I was trying to get the type of subst but with C-c C-d I was getting:

    {A.a : Level} {A : Set A.a} {ℓ : Level} → Substitutive _≡_ ℓ


It's not all that helpful if you don't know what Substitutives
definition is.

But with C-u C-u C-c C-d (the same as above but prefixed with C-u C-u)
you get:


    {A.a : Level} {A : Set A.a} {ℓ : Level} (P : A → Set ℓ) {x y : A} → x ≡ y → P x → P y


Now that's better! You can try it out in this module.
