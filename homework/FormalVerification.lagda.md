---
title: '50.057 Introduction to Formal Verification'
author:
- ISTD, SUTD
header-includes:
  - \usepackage{newunicodechar}
  - \usepackage{stmaryrd}
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
  - \newunicodechar{ʳ}{\textsuperscript{r}}
  - \newunicodechar{ℤ}{\ensuremath{\mathbb{Z}}}
  - \newunicodechar{ᵇ}{\textsuperscript{b}}
  - \newunicodechar{ⁱ}{\textsuperscript{i}}
  - \newunicodechar{ˡ}{\textsuperscript{l}}
  - \newunicodechar{≮}{\ensuremath{\nless}}
  - \newunicodechar{≥}{\ensuremath{\geq}}
  - \newunicodechar{≱}{\ensuremath{̸\not\geq}}
  - \newunicodechar{̸}{\ensuremath{\mkern-12mu/}}
  - \newunicodechar{∸}{\ensuremath{̸\mathring{-}}}
  - \newunicodechar{ʰ}{\ensuremath{^{\mathrm{h}}}}
  - \newunicodechar{Δ}{\ensuremath{\Delta}}
  - \newunicodechar{ᵢ}{\ensuremath{_{\mathrm{i}}}}
  - \newunicodechar{⟦}{\ensuremath{\llbracket}}
  - \newunicodechar{⟧}{\ensuremath{\rrbracket}}
  - \newunicodechar{ᵣ}{\ensuremath{_{\mathrm{r}}}}
  - \newunicodechar{ᵉ}{\ensuremath{^{\mathrm{e}}}}
  - \newunicodechar{⨾}{\ensuremath{\mathrel{\circ}}}
  - \newunicodechar{⊨}{\ensuremath{\vDash}}
  - \newunicodechar{∗}{\ensuremath{*}}
  
---


## Hoare Logic and Program Verification

In this cohort exercise, we use Agda as a proof assistant to "actualize" the
concepts and theories that we learned in the lecture note.


The following Agda workbook made reference from the following github repo.


```url
https://github.com/mzeuner/SimpleHoareProver/tree/main
```


```agda
module FormalVerification where


import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; map; concatMap ; _∷ʳ_ ; length ; head )


open import Data.Integer using (ℤ ; +0 ; 1ℤ ; -1ℤ ; pred ; _≤ᵇ_ ) renaming (  _≟_ to _≟ⁱ_ ; _+_ to _+ⁱ_; _*_ to _*ⁱ_; _-_ to _-ⁱ_; _≤_ to _≤ⁱ_ ; _<?_ to _<?ⁱ_ ; _<_ to _<ⁱ_ )

import Data.Integer.Properties as ℤ-Props
open ℤ-Props using (*-identityʳ ; *-identityˡ ; *-assoc ; *-comm ; ≤∧≮⇒≡ ; ≮⇒≥ ; <⇒≱ ; ≤ᵇ⇒≤ ; i<j⇒i≤pred[j] ; +-comm ; *-distribʳ-+ ; pred-suc ; ≤-antisym ; <-irrefl ; <⇒≤ ; *-zeroˡ ; +-identityˡ)

import Data.Nat as Nat
open Nat using (ℕ ; _≟_ ; zero ; suc ; _∸_ ; z≤n ; s≤s ) renaming ( _+_ to _+ℕ_ )



import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; subst )
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)



import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)


import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

import Relation.Nullary as Nullary 
open Nullary using (¬_ ) 

open import Relation.Nullary.Decidable using (Dec ; yes ; no  )
open import Data.Empty using (⊥ ; ⊥-elim)


open import Data.Unit using (⊤; tt)
open import Data.Bool using ( T ; Bool ; true ; false ; _∨_ ; _∧_  ) renaming ( not to notᵇ )


```


## Model the source language in which the program being verified

We model a tiny sub set of Rust (let's call it "micro rust") , which supports only integer arithmetics, assignment and  control flow.


### Variable and values


In the following snippet, we deine the "type-alias" of values, variables and a memory environment that maps variables to values.

For simplicity, we use natural numbers to represent variables (ids).

```agda

Val = ℤ 

Var = ℕ 

Env = List ( Var × Val ) 

```

### Program epression and operators

In the following snippet, we define the expression of micro rust, which could be

* variable
* integer constant
* the "builtin" + , -, * and ! operations. 


```agda

infix 7 _+ʰ_
infix 7 _-ʰ_
infix 7 _*ʰ_ 
infix 10 _!ʰ


{-# TERMINATING #-}
_! : ℤ → ℤ
_! n with n ≤ᵇ +0
... | true = 1ℤ
... | false = ((n -ⁱ 1ℤ) !) *ⁱ n


data Exp : Set where
  $_ : Var → Exp            -- ^ variable expression
  C_ : ℤ → Exp              -- ^ constant expression
  _+ʰ_ : Exp → Exp → Exp    -- ^ infix + expression 
  _-ʰ_ : Exp → Exp → Exp    -- ^ infix - expression
  _*ʰ_ : Exp → Exp → Exp    -- ^ infix * expression   
  _!ʰ : Exp → Exp           -- ^ factorial expression

```

### Predicate

Next we define the predicate supported in micro rust, which consist of

* equality and inequalities relations
* negation, conjunction and disjunction connectives
* the true and the false atom predicate


```agda
infix 6 _≡ʰ_
infix 6 _<ʰ_ 
infix 5 _and_
infix 5 _or_

data Pred : Set where
  _≡ʰ_ : Exp → Exp → Pred    -- ^ equality
  _<ʰ_  : Exp → Exp → Pred   -- ^ less than
  _>ʰ_  : Exp → Exp → Pred   -- ^ greater than  
  not  : Pred → Pred         -- ^ negation
  _and_ : Pred → Pred → Pred -- ^ conjunction
  _or_  : Pred → Pred → Pred -- ^ disjunction 
  True  : Pred
  False : Pred 
  


```

### Statement

Next we define the statements in micro rust, which consists of

* skip (AKA the no-op statement)
* assignment
* conditional
* while loop
* sequence statement, stmt1 ; stmt2 (note that ; we use in our Agda implementation is an infix unicode ;.

Note that we make the boolean expressions appearing in the if-else and the while are merely predicate.
In addition, we need to attach the loop invariant to while statment, which is needed in the WLP calculation later.


```agda

infix 5 _←_
infix 4 _⨾_ 


data Stmt :  Set where
  skip : Stmt 
  _←_  : Var → Exp → Stmt                     -- ^ assignment statement (it is a backashed l )
  if_then_else_ : Pred → Stmt → Stmt → Stmt   -- ^ if-then-else statement
  while : Pred              -- ^ invariant 
    → Pred                  -- ^ while cond
    → Stmt
    → Stmt                                    -- ^ while statement with invariant
  _⨾_  : Stmt → Stmt → Stmt                    -- ^ sequence statement (it is a backslashed ;)

```

### Substitution

We need substituion operation in the Hoare Rules later, which is defined as follows


```agda

infix 8 ⟦_/_⟧ᵉ_


⟦_/_⟧ᵉ_ : Exp → Var → Exp → Exp
⟦_/_⟧ᵉ_ e v ($ v') with v ≟ v' 
... | yes refl = e
... | no ¬v≡v' = $ v'
⟦_/_⟧ᵉ_ e v (C c) = C c 
⟦_/_⟧ᵉ_ e v (e₁ +ʰ e₂) =  ⟦ e / v ⟧ᵉ e₁ +ʰ ⟦ e / v ⟧ᵉ e₂
⟦_/_⟧ᵉ_ e v (e₁ -ʰ e₂) =  ⟦ e / v ⟧ᵉ e₁ -ʰ ⟦ e / v ⟧ᵉ e₂
⟦_/_⟧ᵉ_ e v (e₁ *ʰ e₂) =  ⟦ e / v ⟧ᵉ e₁ *ʰ ⟦ e / v ⟧ᵉ e₂
⟦_/_⟧ᵉ_ e v (e' !ʰ) = (⟦ e / v ⟧ᵉ e') !ʰ



infix 8 ⟦_/_⟧_ 

⟦_/_⟧_ : Exp → Var → Pred → Pred
⟦_/_⟧_ e v ( e₁ ≡ʰ e₂ ) = ( ⟦ e / v ⟧ᵉ e₁ ) ≡ʰ ( ⟦ e / v ⟧ᵉ e₂ )
⟦_/_⟧_ e v ( e₁ <ʰ e₂ ) = ( ⟦ e / v ⟧ᵉ e₁ ) <ʰ ( ⟦ e / v ⟧ᵉ e₂ )
⟦_/_⟧_ e v ( e₁ >ʰ e₂ ) = ( ⟦ e / v ⟧ᵉ e₁ ) >ʰ ( ⟦ e / v ⟧ᵉ e₂ )
⟦_/_⟧_ e v ( not p )    = not ( ⟦ e / v ⟧ p )
⟦_/_⟧_ e v ( p and q )  = ⟦ e / v ⟧ p and ⟦ e / v ⟧ q
⟦_/_⟧_ e v ( p or q )   =  ⟦ e / v ⟧ p or ⟦ e / v ⟧ q
⟦_/_⟧_ e v True         = True
⟦_/_⟧_ e v False        = False

```

### Auxiliary operation

We some additional auxiliary operations, e.g.

* `lookup` returns a value of a variable in an environment, if it is found; if it is not found, we returns a zero
  * Note: we should have signal an error or return nothing of a Maybe data type. We keep it simple so that proof can be simpler.
* `evalExp` evaluates an expression under the given environment and returns the integer value.
* `eval` evaluates a predicate under the given environment and returns the boolean value.


```agda


infix 5 _⇒_  -- implication, ( it is a backslashed => )

pattern _⇒_ p q = (not p) or q


lookup : Env → Var → Val
lookup [] x = +0
lookup ( ( x , v ) ∷ Δ ) y with x ≟ y
... | yes _ = v
... | no _  = lookup Δ y 


evalExp : Env → Exp → ℤ
evalExp Δ ($ v)      = lookup Δ v
evalExp Δ (C v)      = v
evalExp Δ (e₁ +ʰ e₂) = evalExp Δ e₁ +ⁱ evalExp Δ e₂
evalExp Δ (e₁ -ʰ e₂) = evalExp Δ e₁ -ⁱ evalExp Δ e₂
evalExp Δ (e₁ *ʰ e₂) = evalExp Δ e₁ *ⁱ evalExp Δ e₂
evalExp Δ (e !ʰ)      = (evalExp Δ e) !

isYes : ∀ {P : Set} → Dec P → Bool
isYes (yes _) = true
isYes (no _) = false

eval-≡ʰ : ℤ → ℤ → Bool
eval-≡ʰ v₁ v₂ = isYes (v₁ ≟ⁱ v₂)

eval-<ʰ : ℤ → ℤ → Bool
eval-<ʰ v₁ v₂ = isYes (v₁ <?ⁱ v₂)

eval : Env → Pred → Bool
eval Δ (e₁ ≡ʰ e₂) = eval-≡ʰ (evalExp Δ e₁) (evalExp Δ e₂)
eval Δ (e₁ <ʰ e₂) = eval-<ʰ (evalExp Δ e₁) (evalExp Δ e₂)
eval Δ (e₁ >ʰ e₂) = eval-<ʰ (evalExp Δ e₂) (evalExp Δ e₁)
eval Δ (not p )   = notᵇ (eval Δ p)
eval Δ (p and q ) = (eval Δ p) ∧ (eval Δ q)
eval Δ (p or q )  = (eval Δ p) ∨ (eval Δ q)
eval Δ True       = true
eval Δ False      = false 

```

### Auxiliary lemma


In the follow we define a type constructor do allows sub-proof.

We also define a simple lemma that shows implication is reflexive.


```agda

-- "grounding" a true predicate to be a valid Set.
⊨ : Pred → Set
⊨ p =  ∀ ( Δ : Env ) → T ( eval Δ p ) -- T is defined in data.Bool.Core, mapping boolean to Set


-- a little lemma that's used implicitly in Hoare's paper
⇒-refl : ∀ { p } → ⊨ (p ⇒ p)
⇒-refl {p} Δ with eval Δ p
... | true = tt
... | false = tt


-- common lemmas needed for proving

True⇒n≡n : ∀ { n : Var } → ⊨ ( True ⇒ ( ($ n) ≡ʰ ($ n) ))
True⇒n≡n {n} Δ with lookup Δ n
... | x with x ≟ⁱ x
...      | yes _ = tt
...      | no ¬eq = ⊥-elim (¬eq refl)

n≡ʰm⇒n+1≡ʰm+1 : ∀ { n m : Var } → ⊨ ( ( ($ n) ≡ʰ ($ m) ) ⇒ ( (($ n) +ʰ (C 1ℤ)) ≡ʰ (($ m) +ʰ (C 1ℤ)) ) )
n≡ʰm⇒n+1≡ʰm+1 {n} {m} Δ with lookup Δ n | lookup Δ m
... | v₁ | v₂ with v₁ ≟ⁱ v₂
...             | no _ = tt
...             | yes v₁≡v₂ with (v₁ +ⁱ 1ℤ) ≟ⁱ (v₂ +ⁱ 1ℤ)
...                          | yes _ = tt
...                          | no ¬eq = ⊥-elim (¬eq (cong (_+ⁱ 1ℤ) v₁≡v₂))
                                            

```


### Hoare Rules


As we learned from the lecture note, Hoare Logic is shipped with a set of inference rules, which
can be neatly defined using agda data type, one constructor per rule.


```agda


data ⟨_⟩_⟨_⟩ : Pred → Stmt → Pred → Set where 
  skipR      : { p : Pred }
             ----------------- 
             → ⟨ p ⟩ skip ⟨ p ⟩ 

  assignR    : { p : Pred }
             → { x : Var }
             → { e : Exp }
             ---------------------------------
             → ⟨ ⟦ e / x ⟧ p ⟩ ( x ← e ) ⟨ p ⟩
  
  seqR       : { p r q : Pred }
             → { s₁ s₂ : Stmt }
             → ⟨ p ⟩ s₁ ⟨ r ⟩
             → ⟨ r ⟩ s₂ ⟨ q ⟩ 
             -----------------------------------
             → ⟨ p ⟩ ( s₁ ⨾ s₂ ) ⟨ q ⟩

  ifR        : { p r q : Pred }
             → { s₁ s₂ : Stmt }
             → ⟨ p and r ⟩ s₁ ⟨ q ⟩
             → ⟨ p and (not r) ⟩ s₂ ⟨ q ⟩
             ------------------------------------
             → ⟨ p ⟩ if r then s₁ else s₂ ⟨ q ⟩ 

  whileR     : { p r inv : Pred }
             → { s : Stmt }
             → ⟨ p and r ⟩ s ⟨ p ⟩
             ------------------------------------
             → ⟨ p ⟩ while inv r s ⟨ p and (not r) ⟩


  conseqR    : { p p' q q' : Pred }
             → { s : Stmt }
             → ⊨ ( p ⇒ p' ) 
             → ⟨ p' ⟩ s ⟨ q' ⟩             
             → ⊨ ( q' ⇒ q )  
             --------------------------
             → ⟨ p ⟩ s ⟨ q ⟩ 


```



### Example - `mul`


Let's verify the annotation in `mul` function in the notes is correct. This function
computes the product of two natural numbers `n` and `m` by repeated addition, using a
`while` loop.


```rust
fn mul(n: i32, m: i32) -> i32 {
    // PRE: { n >= 0 & m >= 0 }
    let mut i = 0;
    // O1: { i = 0 & n >= i }
    let mut r = 0;
    // O2: { n >= i & r = i * m }
    while i < n {
        // P1: { n >= i & r = i * m & i < n }
        r = r + m;
        // P2: { n >= i + 1 & r = (i + 1) * m }
        i = i + 1;
        // P3: { n >= i & r = i * m }
    }
    // { i = n & r = n * m & n >= i & r = i * m }
    r
}
```

## Exercise 1 

Complete the TODOs holes in the following proof. 


```agda
module MulProof where

  n m i r : Var
  n = 0
  m = 1
  i = 2
  r = 3

  -- invariant: i is non-negative (n >= i) and r = i * m
  I : Pred
  I = (not (($ n) <ʰ ($ i))) and (($ r) ≡ʰ (($ i) *ʰ ($ m)))

  -- precondition: n and m are non-negative
  pre : Pred
  pre = (not (($ n) <ʰ (C +0))) and (not (($ m) <ʰ (C +0)))

  -- postcondition: i = n, r = n * m, and the invariant still holds
  post : Pred
  post = (($ i) ≡ʰ ($ n)) and ((($ r) ≡ʰ (($ n) *ʰ ($ m))) and I)

  prog = i ← C +0 ⨾
         ( r ← C +0 ⨾
           while I
               (($ i) <ʰ ($ n))
               ( r ← ( ($ r) +ʰ ($ m) ) ⨾
                 i ← ( ($ i) +ʰ (C 1ℤ)) ) )

  prf : ⟨ pre ⟩ prog ⟨ post ⟩
  prf = seqR step1 (seqR step2 step3)
    where

    -- proving step 1 

    O1 : Pred
    O1 = (($ i) ≡ʰ (C +0)) and (not (($ n) <ʰ ($ i)))

    step1-pre : ⊨ (pre ⇒ (((C +0) ≡ʰ (C +0)) and (not (($ n) <ʰ (C +0)))))
    step1-pre Δ with lookup Δ n | lookup Δ m
    ... | v₁' | v₂' with v₁' <?ⁱ +0
    ... | yes v₁'<0 = tt
    ... | no ¬v₁'<0 with v₂' <?ⁱ +0
    ... | yes v₂'<0 = tt
    ... | no ¬v₂'<0 = tt

    step1 : ⟨ pre ⟩ (i ← C +0) ⟨ O1 ⟩
    step1 = {!!} -- TODO:  Hints: you need to make use of conseqR and assignR and ⇒-refl with step1-pre 


    -- proving step 2
    
    -- step2-pre is showing
    --  O1 implies
    --   n >= i and 0 = i * m
    step2-pre : ⊨ (O1 ⇒ ((not (($ n) <ʰ ($ i))) and ((C +0) ≡ʰ (($ i) *ʰ ($ m)))))
    step2-pre Δ with lookup Δ i | lookup Δ n | lookup Δ m
    ... | vᵢ | v₁' | v₂' with vᵢ ≟ⁱ +0
    ... | no _ = tt
    ... | yes vᵢ≡+0 with v₁' <?ⁱ vᵢ
    ... | yes _ = tt
    ... | no ¬v₁'<vᵢ with +0 ≟ⁱ (vᵢ *ⁱ v₂')
    ... | yes _ = tt
    ... | no ¬eq = ⊥-elim (¬eq (sym (trans (cong (_*ⁱ v₂') vᵢ≡+0) (*-zeroˡ v₂'))))

    -- step2 is showing
    --  { O1 } r = 0 { I } , note that O2 is I
    step2 : ⟨ O1 ⟩ (r ← C +0) ⟨ I ⟩
    step2 = {!!} -- TODO:  Hints: you need to make use of conseqR and assignR and ⇒-refl with step2-pre


    -- proving step 3

    P1 : Pred
    P1 = (I and (($ i) <ʰ ($ n)))

    P2 : Pred
    P2 = (not (($ n) <ʰ (($ i) +ʰ (C 1ℤ)))) and (($ r) ≡ʰ ((($ i) +ʰ (C 1ℤ)) *ʰ ($ m)))

    pred+1-suc : ∀ v → pred (v +ⁱ 1ℤ) ≡ v
    pred+1-suc v = trans (cong pred (+-comm v 1ℤ)) (pred-suc v)

    i<n⇒¬n<i+1 : ∀ i n → i <ⁱ n → ¬ (n <ⁱ i +ⁱ 1ℤ)
    i<n⇒¬n<i+1 i n i<n n<i+1 = ⊥-elim (<-irrefl refl (subst (λ x → x <ⁱ n) i≡n i<n))
      where
        i≡n : i ≡ n
        i≡n = ≤-antisym (<⇒≤ i<n) (subst (λ x → n ≤ⁱ x) (pred+1-suc i) (i<j⇒i≤pred[j] n<i+1))



    -- body-r-pre is a proof showing
    --    I and i < n imply
    --    (n >= i + 1) and (r + m) = (i + 1) * m
    body-r-pre : ⊨ (P1 ⇒ ((not (($ n) <ʰ (($ i) +ʰ (C 1ℤ)))) and ((($ r) +ʰ ($ m)) ≡ʰ ((($ i) +ʰ (C 1ℤ)) *ʰ ($ m)))))
    body-r-pre Δ = helper Δ (lookup Δ i) (lookup Δ r) (lookup Δ n) (lookup Δ m) refl refl refl refl
      where
        helper : ∀ Δ vᵢ vᵣ v₁' v₂'
          → lookup Δ i ≡ vᵢ → lookup Δ r ≡ vᵣ → lookup Δ n ≡ v₁' → lookup Δ m ≡ v₂'
          → T (eval Δ (P1 ⇒ ((not (($ n) <ʰ (($ i) +ʰ (C 1ℤ)))) and ((($ r) +ʰ ($ m)) ≡ʰ ((($ i) +ʰ (C 1ℤ)) *ʰ ($ m))))))
        helper Δ vᵢ vᵣ v₁' v₂' i-eq r-eq n-eq m-eq -- relies on trichotomy of ℤ,  lookup an undefined variable yield 0
          rewrite i-eq | r-eq | n-eq | m-eq
          with v₁' <?ⁱ vᵢ | vᵣ ≟ⁱ (vᵢ *ⁱ v₂') | vᵢ <?ⁱ v₁'
        ... | yes n<i   | _     | _       = tt
        ... | no ¬n<i   | no ¬B | _       = tt
        ... | no ¬n<i   | yes B | no ¬i<n = tt
        ... | no ¬n<i   | yes B | yes i<n
          with v₁' <?ⁱ (vᵢ +ⁱ 1ℤ) | (vᵣ +ⁱ v₂') ≟ⁱ ((vᵢ +ⁱ 1ℤ) *ⁱ v₂')
        ... | yes n<i+1 | _     = ⊥-elim (i<n⇒¬n<i+1 vᵢ v₁' i<n n<i+1)
        ... | no ¬n<i+1 | yes _ = tt
        ... | no ¬n<i+1 | no ¬eq = ⊥-elim (¬eq (trans (cong (_+ⁱ v₂') B) (trans (sym (cong (λ x → (vᵢ *ⁱ v₂') +ⁱ x) (*-identityˡ v₂'))) (sym (*-distribʳ-+ v₂' vᵢ 1ℤ)))))

    -- body-r is a proof showing
    --    { P1 } r = r + m { P2 } 
    body-r : ⟨ P1 ⟩ (r ← ($ r) +ʰ ($ m)) ⟨ P2 ⟩
    body-r = {!!} -- TODO. Hints: you need to make use of conseqR and assignR and ⇒-refl with body-r-pre

    -- body-i is a proof showing
    --    { P2 } i = i + 1 { I }
    --  Note that P2 is ⟦ (i + 1) / i ⟧ I
    body-i : ⟨ P2 ⟩ (i ← ($ i) +ʰ (C 1ℤ)) ⟨ I ⟩
    body-i = {!!} -- TODO. Hint: you need to make use of assignR 

    -- body is a proof showing
    --   { P1 } r = r + m ; i = i + 1 { I }
    body : ⟨ P1 ⟩ (r ← ($ r) +ʰ ($ m) ⨾ i ← ($ i) +ʰ (C 1ℤ)) ⟨ I ⟩
    body = seqR body-r body-i

    while-proof : ⟨ I ⟩ (while I (($ i) <ʰ ($ n)) (r ← ($ r) +ʰ ($ m) ⨾ i ← ($ i) +ʰ (C 1ℤ))) ⟨ I and (not (($ i) <ʰ ($ n))) ⟩
    while-proof = whileR body



    -- step3-post is a proof showing I and i >= n imply the post-condition.
    step3-post : ⊨ ((I and (not (($ i) <ʰ ($ n)))) ⇒ post) 
    step3-post Δ = helper Δ (lookup Δ i) (lookup Δ r) (lookup Δ n) (lookup Δ m) refl refl refl refl
      where
      helper : ∀ Δ vᵢ vᵣ v₁' v₂'
        → lookup Δ i ≡ vᵢ → lookup Δ r ≡ vᵣ → lookup Δ n ≡ v₁' → lookup Δ m ≡ v₂'
        → T (eval Δ ((I and (not (($ i) <ʰ ($ n)))) ⇒ post))
      helper Δ vᵢ vᵣ v₁' v₂' i-eq r-eq n-eq m-eq -- relies on trichotomy of ℤ, lookup an undefined variable yield 0
        rewrite i-eq | r-eq | n-eq | m-eq
        with v₁' <?ⁱ vᵢ | vᵣ ≟ⁱ (vᵢ *ⁱ v₂') | vᵢ <?ⁱ v₁'
      ... | yes n<i   | _     | _       = tt
      ... | no ¬n<i   | no ¬B | _       = tt
      ... | no ¬n<i   | yes B | yes i<n = tt
      ... | no ¬n<i   | yes B | no ¬i<n
        with vᵢ ≟ⁱ v₁' | vᵣ ≟ⁱ (v₁' *ⁱ v₂')
      ... | no ¬vᵢ≡v₁' | _           = ⊥-elim (¬vᵢ≡v₁' (≤-antisym (≮⇒≥ {v₁'} {vᵢ} ¬n<i) (≮⇒≥ {vᵢ} {v₁'} ¬i<n)))
      ... | yes vᵢ≡v₁' | no ¬vᵣ≡v₁'v₂' = ⊥-elim (¬vᵣ≡v₁'v₂' (trans B (cong (_*ⁱ v₂') vᵢ≡v₁')))
      ... | yes vᵢ≡v₁' | yes _       = tt


    step3 : ⟨ I ⟩ (while I (($ i) <ʰ ($ n)) (r ← ($ r) +ʰ ($ m) ⨾ i ← ($ i) +ʰ (C 1ℤ))) ⟨ post ⟩
    step3 = conseqR (⇒-refl {I}) while-proof step3-post


```

## Weakest Liberal Precondition

The weakest liberal precondition can be defined as follows, (which is described in the notes).


```agda
wlp : Pred → Stmt → Pred
wlp q skip                    = q
wlp q (x ← e)                 = ⟦ e / x ⟧ q
wlp q (s₁ ⨾ s₂)                = wlp (wlp q s₂) s₁
wlp q (if r then s₁ else s₂ ) = (r ⇒ (wlp q s₁)) and ( (not r) ⇒ (wlp q s₂)) 
wlp q (while inv r s)         = inv and ( ((inv and r) ⇒ (wlp inv s)) and ( (inv and (not r)) ⇒ q ) )
```



## Exercise 2 - Spot the AI Slop

The following proof is generated by AI.

It is correct since it compiles. However it is smelly.

Apply your logic skills to spot the slop.

```agda
module MulWLPProof where

  open  MulProof


  infered_wlp : Pred
  infered_wlp = wlp post prog
{-
  (not (($ n) <ʰ (C +0))) and
   ((C +0) ≡ʰ ((C +0) *ʰ ($ m))) and
   (((((not (($ n) <ʰ (C +0))) and ((C +0) ≡ʰ ((C +0) *ʰ ($ m))))
      and ((C +0) <ʰ ($ n)))
     ⇒
     ((not (($ n) <ʰ ((C +0) +ʰ (C 1ℤ)))) and
      ((C +0) +ʰ ($ m) ≡ʰ (((C +0) +ʰ (C 1ℤ)) *ʰ ($ m))))
   and
   ((((not (($ n) <ʰ (C +0))) and ((C +0) ≡ʰ ((C +0) *ʰ ($ m))))
      and not ((C +0) <ʰ ($ n)))
     ⇒
     ((C +0) ≡ʰ ($ n) and
      (((C +0) ≡ʰ (($ n) *ʰ ($ m))) and
       ((not (($ n) <ʰ (C +0))) and ((C +0) ≡ʰ ((C +0) *ʰ ($ m)))))))))
  -}


  wlp-arith : ∀ v₂' → (+0 +ⁱ v₂') ≡ ((+0 +ⁱ 1ℤ) *ⁱ v₂')
  wlp-arith v₂' = trans (+-identityˡ v₂') (sym (*-identityˡ v₂'))

  v₁'<1-contradiction : ∀ v₁' → ¬ (v₁' <ⁱ +0) → +0 <ⁱ v₁' → v₁' <ⁱ 1ℤ → ⊥
  v₁'<1-contradiction v₁' ¬v₁'<0 0<v₁' v₁'<1 = ⊥-elim (<-irrefl refl (subst (λ x → +0 <ⁱ x) v₁'≡+0 0<v₁'))
    where
      pred1≡0 : pred 1ℤ ≡ +0
      pred1≡0 = refl
      v₁'≡+0 : v₁' ≡ +0
      v₁'≡+0 = ≤-antisym (subst (λ x → v₁' ≤ⁱ x) pred1≡0 (i<j⇒i≤pred[j] v₁'<1)) (≮⇒≥ {v₁'} {+0} ¬v₁'<0)


  precond⇒infered_wlp : ⊨ (pre ⇒ infered_wlp)
  precond⇒infered_wlp Δ = helper Δ (lookup Δ n) (lookup Δ m) refl refl
    where
      helper : ∀ Δ v₁' v₂' → lookup Δ n ≡ v₁' → lookup Δ m ≡ v₂'
        → T (eval Δ (pre ⇒ infered_wlp))
      helper Δ v₁' v₂' n-eq m-eq -- relies on trichotomy of ℤ
        rewrite n-eq | m-eq
        with v₁' <?ⁱ +0   | v₂' <?ⁱ +0 | +0 ≟ⁱ (+0 *ⁱ v₂') | +0 <?ⁱ v₁' | v₁' <?ⁱ (+0 +ⁱ 1ℤ) | (+0 +ⁱ v₂') ≟ⁱ ((+0 +ⁱ 1ℤ) *ⁱ v₂') | +0 ≟ⁱ v₁'  | +0 ≟ⁱ (v₁' *ⁱ v₂')
      ... | yes _         | _          | _                 | _          | _                  | _                                  | _          | _            = tt
      ... | no _          | yes _      | _                 | _          | _                  | _                                  | _          | _            = tt
      ... | no _          | no _       | no ¬0≢0v₂'        | _          | _                  | _                                  | _          | _            = ⊥-elim (¬0≢0v₂' (sym (*-zeroˡ v₂')))
      ... | no ¬v₁'<0     | no _       | yes _             | yes 0<v₁'  | yes v₁'<1          | _                                  | _          | _            = ⊥-elim (v₁'<1-contradiction v₁' ¬v₁'<0 0<v₁' v₁'<1)
      ... | no _          | no _       | yes _             | yes _      | no _               | yes _                              | _          | _            = tt
      ... | no _          | no _       | yes _             | yes _      | no _               | no ¬0+m≢1*m                        | _          | _            = ⊥-elim (¬0+m≢1*m (wlp-arith v₂'))
      ... | no _          | no _       | yes _             | no _       | _                  | _                                  | yes _      | yes _        = tt
      ... | no _          | no _       | yes _             | no _       | _                  | _                                  | yes v₁'≡+0 | no ¬0≢v₁'v₂' = ⊥-elim (¬0≢v₁'v₂' (trans (*-zeroˡ v₂') (cong (_*ⁱ v₂') v₁'≡+0)))
      ... | no ¬v₁'<0     | no _       | yes _             | no ¬0<v₁'  | _                  | _                                  | no ¬0≢v₁'  | _            = ⊥-elim (¬0≢v₁' (sym (≤∧≮⇒≡ (≮⇒≥ {+0} {v₁'} ¬0<v₁') ¬v₁'<0)))

```
