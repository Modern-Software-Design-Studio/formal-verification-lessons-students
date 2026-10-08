---
title: '50.057 Introduction to Agda Cohort Exercise'
author:
- ISTD, SUTD
header-includes:
  - \usepackage{newunicodechar}
  - \newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
  - \newunicodechar{∀}{\ensuremath{\forall}}
  - \newunicodechar{∃}{\ensuremath{\exists}}
  - \newunicodechar{∷}{::}
  - \newunicodechar{⊎}{\ensuremath{\uplus}}
  - \newunicodechar{Σ}{\ensuremath{\Sigma}}
  - \newunicodechar{⊥}{\ensuremath{\bot}}
  - \newunicodechar{⊤}{\ensuremath{\top}}
  - \newunicodechar{→}{\ensuremath{\rightarrow}}
  - \newunicodechar{←}{\ensuremath{\leftarrow}}
  - \newunicodechar{≡}{\ensuremath{\equiv}}
  - \newunicodechar{≤}{\ensuremath{\le}}
  - \newunicodechar{⟨}{\ensuremath{\langle}}
  - \newunicodechar{⟩}{\ensuremath{\rangle}}
  - \newunicodechar{×}{\ensuremath{\times}}
  - \newunicodechar{λ}{\ensuremath{\lambda}}
  - \newunicodechar{¬}{\ensuremath{\neg}}
  - \newunicodechar{∧}{\ensuremath{\wedge}}
  - \newunicodechar{∨}{\ensuremath{\vee}}
  - \newunicodechar{₁}{\ensuremath{_1}}
  - \newunicodechar{₂}{\ensuremath{_2}}
  - \newunicodechar{⇒}{\ensuremath{\Rightarrow}}
  - \newunicodechar{≟}{=?}
  - \newunicodechar{ʸ}{\ensuremath{^{\mathrm{y}}}}
  - \newunicodechar{ⁿ}{\ensuremath{^{\mathrm{n}}}}  
---

# Introduction to Agda — Cohort Exercise

This exercise is a guided introduction to Agda. Open this file in Emacs in `agda2-mode` and work through it interactively. For each exercise, replace the `{! !}` holes with a correct Agda term and reload with `C-c C-l`.

## Emacs/Agda2-mode commands to use

| Keys | Command |
|------|---------|
| `C-c C-l` | Load / type-check the file. |
| `C-c C-r` | Refine the hole (`{! !}`). |
| `C-c C-a` | Try to solve the hole automatically. |
| `C-c C-SPC` | Give the expression in the hole. |
| `C-c C-c` | Case split on a variable in the hole. |
| `C-c C-,` | Show the goal type and context. |
| `C-c C-n` | Evaluate a selected expression. |

If you are stuck, type `C-c C-,` inside a hole to see what Agda expects.


## Part 1: Getting used to holes

Load the file with `C-c C-l`.

```agda
module IntroAgda where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no; ¬_ ; ofʸ ; ofⁿ )
open import Data.Product using (Σ; ∃; _,_; _×_; Σ-syntax; ∃-syntax )
open Σ using (proj₁ ; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using ( T ; Bool ; true ; false ; _∨_ ; _∧_ ; not )
open import Agda.Builtin.Unit using ( tt )
open import Data.Empty using (⊥ ; ⊥-elim)
```

### Exercise 1.1

Replace the hole below with a natural number. Try `C-c C-r` first, then type the numeral and press `C-c C-SPC`. Notice that `C-c C-a` may also work.

```agda
myFirstNumber : ℕ
myFirstNumber = {! !}
```

### Exercise 1.2

Define `double` by pattern matching on `n`. Place the cursor in the hole and press `C-c C-c`. Agda will ask for the variable name; type `n` and press return. Then fill in each branch.

```agda
double : ℕ → ℕ
double n = {! !}
```


## Part 2: Natural numbers and equality proofs

### Exercise 2.1

This goal reduces by computation. What is the proof that the left-hand side equals the right-hand side?

```agda
0+0 : zero + zero ≡ zero
0+0 = {! !}
```

### Exercise 2.2

Prove that zero is a left identity for addition. Split on `n`.

```agda
0+ : ∀ (n : ℕ) → zero + n ≡ n
0+ n = {! !}
```

### Exercise 2.3

Prove the successor property. This is needed for more complex lemmas.

```agda
suc+ : ∀ (m n : ℕ) → (suc m) + n ≡ suc (m + n)
suc+ m n = {! !}
```

### Exercise 2.4

Prove associativity of addition by induction on `m`. Use `0+` and `suc+`.

```agda
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc m n p = {! !}
```


## Part 3: Relations

The ordering `_≤_` on natural numbers is defined inductively:

```agda
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
```

### Exercise 3.1

Reflexivity of `_≤_`.

```agda
≤-refl : ∀ {n} → n ≤ n
≤-refl = {! !}
```

### Exercise 3.2

Transitivity of `_≤_`.

```agda
≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans m≤n n≤p = {! !}
```

### Exercise 3.3

Monotonicity of successor for `_≤_`.

```agda
≤-suc : ∀ {m n} → m ≤ n → suc m ≤ suc n
≤-suc m≤n = {! !}
```


## Part 4: Predicate logic as Agda types

The exercises in `../cohort_answer/predicate.md` can be recast as types in Agda. Each connective corresponds to a type from the standard library:

* `∧` becomes `_×_`.
* `∨` becomes `_⊎_`.
* `⇒` becomes the function arrow `→`.
* `∀` becomes the dependent function type `∀`.
* `∃` becomes `∃` (a synonym for `Σ`), and a proof is a pair `a , p`.

### Exercise 4.1 — Universal elimination

This exercise mirrors Exercise 1 of `predicate.md`. From `∀ y. ∃ z. follows(y,z)` and `∀ x y. ((∃ z. follows(y,z)) ⇒ follows(x,y))` derive `follows(ada,cara)`.

```agda
postulate
  Person : Set
  follows : Person → Person → Set
  ada cara : Person

exercise1
  : (∀ (y : Person) → ∃[ z ](follows y z))
  → (∀ (x y : Person) → (∃[ z ](follows y z)) → follows x y)
  → follows ada cara
exercise1 h1 h2 = {! !}
```

**Hint.** Apply `h2` to `ada` and `cara`. Then use `h1 cara` to obtain a witness; extract its components with pattern matching.


### Exercise 4.2 — Existential introduction

This exercise mirrors Exercise 3 of `predicate.md`. From a ground fact `p(c,d)` derive existentials.

```agda
postulate
  Object : Set
  p : Object → Object → Set
  c d : Object


exercise3a : p c d → ∃[ y ](p c y)
exercise3a pcd = {! !} 

exercise3b : p c d → ∃[ x ](p x d)
exercise3b pcd = {! !}

```

**Hint.** In Agda, a proof of `∃ A B` is written as `a , evidence`, where `a` is a witness of type `A`. For `exercise3a` we choose `d` as the witness because the premise `pcd` already proves `p c d`. For `exercise3b` we choose `c` because the same premise proves `p c d`.



## Part 5: Conjuction, Disjunction, Decidablity, Boolean and Negation

### Exercise 5.1 - Decidable equality and `with`

Complete the function below. It should return `yes refl` if `m` and `n` are equal, and `no` followed by a proof otherwise.

```agda
≟-decision : ∀ (m n : ℕ) → Dec (m ≡ n)
≟-decision m n = {! !}
```

**Hint.** Type `with m Data.Nat.≟ n ... | yes eq ... | no neq`, or call m Data.Nat.≟ n directly.


### Exercise 5.2 - Mutual recursive definition 

In Agda, if two functions call each other, we have to put their type signatures together, or put them in a mutual block

There is no need to edit the following. 

```agda
even : ℕ → Bool
odd  : ℕ → Bool

even zero    = true
even (suc n) = odd n 

odd  zero    = false   
odd  (suc n) = even n
```

### Exercise 5.3 - From Boolean to Predicate

In Agda, we can lift a boolean to a predicate by calling `T` that turns a true value into into `tt` .


There is no need to edit the following. 

```agda

Even : ℕ → Set
Even n = T (even n) -- ^ T lifts a boolean into a predicarte

Odd  : ℕ → Set 
Odd  n = T (odd n)  

```


### Exercise 5.4 - Negation is a function that returns ⊥

In Agda, error or undefined is denoted by ⊥. 

A negation ¬ P  is just a function takes the input (evidence of P) and return ⊥. 


```agda
even→¬odd : ∀ ( n : ℕ )
            → Even n
            → ¬ (Odd n)
even→¬odd zero tt = λ ()
even→¬odd (suc n) x = λ z → even→¬odd n z x

odd→¬even : ∀ ( n : ℕ )
            → Odd n
            → ¬ (Even n)
odd→¬even zero () 
odd→¬even (suc n) x = λ z → odd→¬even n z x

```

### Exercise 5.5 - Decidability

A Dec record is to capture the true or false value together with the predicate evidence.

() denotes an absurd pattern. 


The pragma {-# TERMINATING #-} is to tell Agda to trust the annotated mutual recursive functions are terminating. 


```agda 

even? : (n : ℕ)  → Dec (Even n)
even? n with even n in eq
... | true = true Relation.Nullary.because ofʸ tt
... | false = false Relation.Nullary.because ofⁿ λ ()

odd? : (n : ℕ)  → Dec (Odd n)
odd? n with odd n in eq
... | true = true Relation.Nullary.because ofʸ tt
... | false = false Relation.Nullary.because ofⁿ λ ()


{-# TERMINATING #-} 
¬even→odd : ∀ ( n : ℕ )
          → ¬ (Even n)
          → Odd n

¬odd→even : ∀ ( n : ℕ )
          → ¬ (Odd n)
          → Even n

¬even→odd zero even-zero→⊥ = ⊥-elim (even-zero→⊥ tt)
¬even→odd (suc n) even-suc-n→⊥ with odd? (suc n)
... | yes odd-suc-n = odd-suc-n
... | no  ¬odd-suc-n = ⊥-elim (even-suc-n→⊥ (¬odd→even (suc n) ¬odd-suc-n))

¬odd→even = {!!} 
```


### Exercise 5.6 - Conjunction and disjunction

In Agda, a conjuction × is a pair (_,_) , and a disjunction ⊎ is just an (enum) datatype with inj₁ (left choice) and inj₂ (right choice) 


```agda

even_or_odd : ∀ ( n : ℕ ) → (Even n) ⊎ (Odd n)
even_or_odd zero = inj₁ tt
even_or_odd (suc n) with even? (suc n)
... | yes even-suc-n = inj₁ even-suc-n
... | no ¬even-suc-n = inj₂ {!!} 


```


### Exercise 5.7 - Challenge

This exercise mirrors Exercise 8 of `predicate.md`. 

Hints: you might want to first define `sucn≡sucm→n≡m`. Then exericse8 is a recursion over `x` and `y`.

```agda
sucn≡sucm→n≡m : ∀ { n m : ℕ }
                → suc n ≡ suc m
                → n ≡ m
sucn≡sucm→n≡m = {!!} 

exercise8 : ∀ (x y : ℕ )
            → x ≡ y
            → ( (Even x) × (Even y) ) ⊎ ( (Odd x) × (Odd y) )
exercise8 = {!!} 


```
