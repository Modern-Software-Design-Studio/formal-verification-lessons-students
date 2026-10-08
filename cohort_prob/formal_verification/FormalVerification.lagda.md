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
open ℤ-Props using (*-identityʳ ; *-identityˡ; *-assoc; *-comm; ≤∧≮⇒≡; ≮⇒≥; <⇒≱; ≤ᵇ⇒≤; i<j⇒i≤pred[j]; +-comm)

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


### Example - `add_one`


Let's verify the annotation in `add_one` function in the notes is correct.


```rust
fn add_one(n : i32) -> i32 {
    // { n == n }. We should've written {$n = n$} but let's keep it simple.
    let mut r = n;
    // { r == n } 
    r = r + 1;
    // { r == n + 1 }
    r
}
```


```agda
module AddOneProof where

  n r : Var 
  n = 0
  r = 1

  prog : Stmt
  prog = r ← $ n ⨾ r ← ($ r +ʰ C 1ℤ)


  prf : ⟨ ($ n) ≡ʰ ($ n) ⟩ prog ⟨ ($ r) ≡ʰ ($ n) +ʰ (C 1ℤ) ⟩ 
  prf = seqR
        (assignR {($ r) ≡ʰ ($ n)} {r} {$ n} )
        (conseqR (n≡ʰm⇒n+1≡ʰm+1 {r} {n}) 
                 (assignR {($ r) ≡ʰ ($ n) +ʰ (C 1ℤ)} {r} {$ r +ʰ C 1ℤ } )
                 (⇒-refl {($ r) ≡ʰ ($ n) +ʰ (C 1ℤ)} ) ) 


```


### Example - `fac`


Let's verify the annotation in `fac` function in the notes is correct.


```rust
fn fac(n: i32) -> i32 { 
    // PRE: { n >= 0 }
    let mut i = n;
    // O1: { i >= 0 & i = n } 
    let mut r = 1;
    // O2: { i >= 0 & i! ∗ r = n! }
    while i > 0 {
        // P1: { i > 0 & i! ∗ r = n! }           
        r = r * i;
        // P2: { i > 0 & (i-1)! ∗ r = n! }   
        i = i - 1;
        // P3: { i >= 0 & i! ∗ r = n! }
    }
    // { i = 0 & r = n! & i! ∗ r = n!}
    r
}
```

### Exercise 1 

Complete the TODOs holes in the following proof. 


```agda
module FacProof where

  n r i : Var 
  n = 0
  r = 1
  i = 2

  -- invariant: i is non-negative and i! * r = n!
  I : Pred
  I = (not (($ i) <ʰ (C +0))) and (((($ i)!ʰ) *ʰ ($ r)) ≡ʰ (($ n)!ʰ))

  -- precondition: n is non-negative (factorial is only meaningful here)
  pre : Pred
  pre = not (($ n) <ʰ (C +0))

  -- postcondition: i = 0, r = n!, and the invariant still holds
  post : Pred
  post = (($ i) ≡ʰ (C +0)) and ((($ r) ≡ʰ (($ n)!ʰ)) and I)

  prog = i ← $ n ⨾
         ( r ← C 1ℤ ⨾
           while I
               (($ i) >ʰ (C +0))
               ( r ← ( ($ r) *ʰ ($ i) ) ⨾
                 i ← ( ($ i) -ʰ (C 1ℤ)) ) )

  prf : ⟨ pre ⟩ prog ⟨ post ⟩
  prf = seqR step1 (seqR step2 step3)
    where

    -- proving step 1 

    O1 : Pred
    O1 = (($ i) ≡ʰ ($ n)) and (not (($ i) <ʰ (C +0)))
    

    step1-pre : ⊨ (pre ⇒ ((($ n) ≡ʰ ($ n)) and pre)) 
    step1-pre Δ with eval Δ pre
    ... | false = tt
    ... | true with lookup Δ n
    ...        |    x  with x ≟ⁱ x
    ...                 | yes _ = tt
    ...                 | no ¬eq = ⊥-elim (¬eq refl)

    step1 : ⟨ pre ⟩ (i ← $ n) ⟨ O1 ⟩
    step1 = {!!} -- TODO: fixme


    -- proving step 2
    
    -- step2-pre is showing
    --  O1 implies
    --   i >= 0 and i! * 1 = n!
    step2-pre : ⊨ (O1 ⇒ ((not (($ i) <ʰ (C +0))) and (((($ i)!ʰ) *ʰ (C 1ℤ)) ≡ʰ (($ n)!ʰ))))
    step2-pre Δ with lookup Δ i | lookup Δ n
    ... | vᵢ | v₂ with vᵢ ≟ⁱ v₂ in i≡n?
    ... | no ¬i≡n rewrite i≡n? = tt
    ... | yes vᵢ≡v₂ with vᵢ <?ⁱ +0 in i<0?
    ... | yes i<0 rewrite i<0? = tt
    ... | no ¬i<0 with (vᵢ ! *ⁱ 1ℤ) ≟ⁱ (v₂ !) in i!1≡n!?
    ... | yes _ rewrite i!1≡n!? = tt
    ... | no ¬eq rewrite i!1≡n!? = ⊥-elim (¬eq (trans (*-identityʳ (vᵢ !)) (cong _! vᵢ≡v₂)))


    -- step2 is showing
    --  { O1 } r = 1 { O2 } , note that O2 is I
    step2 : ⟨ O1 ⟩ (r ← C 1ℤ) ⟨ I ⟩
    step2 = {!!} -- TODO: fixme 


    -- proving step 3

    P1 : Pred
    P1 = (I and (($ i) >ʰ (C +0)))
    
    P2 : Pred
    P2 = (not ((($ i) -ʰ (C 1ℤ)) <ʰ (C +0))) and (((($ i) -ʰ (C 1ℤ))!ʰ) *ʰ ($ r) ≡ʰ (($ n)!ʰ))

    pred≡-1 : ∀ v → pred v ≡ v -ⁱ 1ℤ
    pred≡-1 v = +-comm -1ℤ v

    factorial-step : ∀ v → +0 <ⁱ v → v ! ≡ ((v -ⁱ 1ℤ) !) *ⁱ v
    factorial-step v 0<v with v ≤ᵇ +0 in eq
    ... | true = ⊥-elim (<⇒≱ 0<v (≤ᵇ⇒≤ (subst T (sym eq) tt)))
    ... | false = refl



    -- body-r-pre is a proof showing
    --    I and i > 0 imply
    --    (i - 1 >= 0) and (i - 1) * (r * i) = n!
    body-r-pre : ⊨ (P1 ⇒ ((not ((($ i) -ʰ (C 1ℤ)) <ʰ (C +0))) and (((($ i) -ʰ (C 1ℤ))!ʰ) *ʰ (($ r) *ʰ ($ i)) ≡ʰ (($ n)!ʰ))))
    body-r-pre Δ = helper Δ (lookup Δ i) (lookup Δ r) (lookup Δ n) refl refl refl
      where
        helper : ∀ Δ vᵢ vᵣ v₂
          → lookup Δ i ≡ vᵢ → lookup Δ r ≡ vᵣ → lookup Δ n ≡ v₂
          → T (eval Δ (P1 ⇒ ((not ((($ i) -ʰ (C 1ℤ)) <ʰ (C +0))) and (((($ i) -ʰ (C 1ℤ))!ʰ) *ʰ (($ r) *ʰ ($ i)) ≡ʰ (($ n)!ʰ)))))
        helper Δ vᵢ vᵣ v₂ i-eq r-eq n-eq -- relies on trichotomy of ℤ,  lookup an undefined variable yield 0
          rewrite i-eq | r-eq | n-eq
          with vᵢ <?ⁱ +0 | +0 <?ⁱ vᵢ | (vᵢ ! *ⁱ vᵣ) ≟ⁱ (v₂ !)
        ... | yes _      | _         | _                      = tt
        ... | no _       | no _      | no _                   = tt
        ... | no _       | no _      | yes _                  = tt
        ... | no _       | yes _     | no _                   = tt
        ... | no ¬i<0    | yes 0<i   | yes i!r≡n!
          with (vᵢ -ⁱ 1ℤ) <?ⁱ +0 | ((vᵢ -ⁱ 1ℤ) ! *ⁱ (vᵣ *ⁱ vᵢ)) ≟ⁱ (v₂ !)
        ... | yes i-1<0          | _ = ⊥-elim (<⇒≱ i-1<0 (subst (+0 ≤ⁱ_) (pred≡-1 vᵢ) (i<j⇒i≤pred[j] 0<i)))
        ... | no _               | yes _ = tt
        ... | no _               | no ¬eq = ⊥-elim (¬eq (trans
          (trans
            (cong (((vᵢ -ⁱ 1ℤ) !) *ⁱ_) (*-comm vᵣ vᵢ))
            (trans
              (sym (*-assoc ((vᵢ -ⁱ 1ℤ) !) vᵢ vᵣ))
              (cong (_*ⁱ vᵣ) (sym (factorial-step vᵢ 0<i)))))
          i!r≡n!))

    -- body-r is a proof showing
    --    { P1 } r = r * i { P2 } 
    body-r : ⟨ P1 ⟩ (r ← ($ r) *ʰ ($ i)) ⟨ P2 ⟩ 
    body-r = {!!} -- TODO. Hints: you need to make use of conseqR and assignR and ⇒-refl

    -- body-i is a proof showing
    --    { P2 } i = i - 1 { I }
    --  Note that P3 is I!
    body-i : ⟨ P2 ⟩ (i ← ($ i) -ʰ (C 1ℤ)) ⟨ I ⟩ 
    body-i = {!!} -- TODO. Hint: you need to make use of assignR 

    -- body is a proof showing
    --   { P1 } r = r * i ; i = i - 1 { I }
    --  Note that P3 is I!
    body : ⟨ P1 ⟩ (r ← ($ r) *ʰ ($ i) ⨾ i ← ($ i) -ʰ (C 1ℤ)) ⟨ I ⟩
    body = seqR body-r body-i

    while-proof : ⟨ I ⟩ (while I (($ i) >ʰ (C +0)) (r ← ($ r) *ʰ ($ i) ⨾ i ← ($ i) -ʰ (C 1ℤ))) ⟨ I and (not (($ i) >ʰ (C +0))) ⟩
    while-proof = whileR body



    -- step3-post is a proof showing I and i <= 0 imply the post-condition.
    step3-post : ⊨ ((I and (not (($ i) >ʰ (C +0)))) ⇒ post) 
    step3-post Δ = helper Δ (lookup Δ i) (lookup Δ r) (lookup Δ n) refl refl refl
      where
      vᵣ≡v₂! : ∀ vᵢ vᵣ v₂ → vᵢ ≡ +0 → (vᵢ ! *ⁱ vᵣ) ≡ (v₂ !) → vᵣ ≡ (v₂ !)
      vᵣ≡v₂! vᵢ vᵣ v₂ vᵢ≡0 i!r≡n! = trans (sym (*-identityˡ vᵣ)) (trans (cong (_*ⁱ vᵣ) (sym (trans (cong _! vᵢ≡0) refl))) i!r≡n!)

      helper : ∀ Δ vᵢ vᵣ v₂
        → lookup Δ i ≡ vᵢ → lookup Δ r ≡ vᵣ → lookup Δ n ≡ v₂
        → T (eval Δ ((I and (not (($ i) >ʰ (C +0)))) ⇒ post))
      helper Δ vᵢ vᵣ v₂ i-eq r-eq n-eq -- relies on trichotomy of ℤ, lookup an undefined variable yield 0
        rewrite i-eq | r-eq | n-eq
        with vᵢ <?ⁱ +0 | +0 <?ⁱ vᵢ | (vᵢ ! *ⁱ vᵣ) ≟ⁱ (v₂ !) | vᵢ ≟ⁱ +0
      ... |  yes _     | _         | _                      | _        = tt
      ... |  no _      | yes _     | no _                   | _        = tt
      ... |  no _      | yes _     | yes _                  | _        = tt
      ... |  no _      | no _      | no _                   | _        = tt
      ... |  no ¬vᵢ<0  | no ¬0ltvᵢ | yes i!r≡n!             | no ¬vᵢ≡0
        = ⊥-elim (¬vᵢ≡0 (≤∧≮⇒≡ (≮⇒≥ {+0} {vᵢ} ¬0ltvᵢ) ¬vᵢ<0))
      ... | no ¬vᵢ<0   | no ¬0ltvᵢ | yes i!r≡n!             | yes vᵢ≡0
        rewrite vᵣ≡v₂! vᵢ vᵣ v₂ vᵢ≡0 i!r≡n! | vᵢ≡0 | *-identityˡ (v₂ !)
        with v₂ ! ≟ⁱ v₂ !
      ... | yes _  = tt
      ... | no ¬eq = ⊥-elim (¬eq refl)


    step3 : ⟨ I ⟩ (while I (($ i) >ʰ (C +0)) (r ← ($ r) *ʰ ($ i) ⨾ i ← ($ i) -ʰ (C 1ℤ))) ⟨ post ⟩
    step3 = conseqR (⇒-refl {I}) while-proof step3-post



```



### Weakest Liberal Precondition

The weakest liberal precondition can be defined as follows, (which is described in the notes).


```agda
wlp : Pred → Stmt → Pred
wlp q skip                    = q
wlp q (x ← e)                 = ⟦ e / x ⟧ q
wlp q (s₁ ⨾ s₂)                = wlp (wlp q s₂) s₁
wlp q (if r then s₁ else s₂ ) = (r ⇒ (wlp q s₁)) and ( (not r) ⇒ (wlp q s₂)) 
wlp q (while inv r s)         = inv and ( ((inv and r) ⇒ (wlp inv s)) and ( (inv and (not r)) ⇒ q ) )
```


## Exercise 2:

Complete the TODO holes in the following proof.


```agda
module AddOneWLPProof where

  open  AddOneProof


  infered_wlp : Pred
  infered_wlp = wlp (($ r) ≡ʰ ($ n) +ʰ (C 1ℤ) ) prog
  

  -- evaluating AddOneWLPProof.infered_wlp with ctrl-c ctrl-n should yield 
  -- ($ 0) +ʰ (C ℤ.pos 1) ≡ʰ ($ 0) +ʰ (C ℤ.pos 1)

  ¬true≡false : ¬ (true ≡ false)
  ¬true≡false = λ ()  
  

  precond⇒infered_wlp : ⊨ ( ($ n) ≡ʰ ($ n) ⇒ infered_wlp )
  precond⇒infered_wlp Δ with eval Δ ( ($ n) ≡ʰ ($ n) ⇒ infered_wlp ) in eval-eq
  ... | true = tt
  ... | false = sub_prf
    where
      not-isYes-lookup0≡lookup0_is_false : notᵇ (isYes (lookup Δ 0 ≟ⁱ lookup Δ 0)) ≡ false
      not-isYes-lookup0≡lookup0_is_false with lookup Δ 0
      ... | x with x ≟ⁱ x
      ...      | yes _ = refl
      ...      | no ¬eq = ⊥-elim (¬eq refl)

      isYes-lookup0+1=lookup0+1_is_true : isYes (lookup Δ 0 +ⁱ ℤ.pos 1 ≟ⁱ lookup Δ 0 +ⁱ ℤ.pos 1) ≡ true
      isYes-lookup0+1=lookup0+1_is_true with lookup Δ 0
      ... | x with x +ⁱ ℤ.pos 1 ≟ⁱ x +ⁱ ℤ.pos 1
      ...      | yes _ = refl
      ...      | no ¬eq = ⊥-elim (¬eq refl)
      
      eval_is_true : notᵇ (isYes (lookup Δ 0 ≟ⁱ lookup Δ 0)) ∨ isYes (lookup Δ 0 +ⁱ ℤ.pos 1 ≟ⁱ lookup Δ 0 +ⁱ ℤ.pos 1)  ≡ true
      eval_is_true =
        begin
          notᵇ (isYes (lookup Δ 0 ≟ⁱ lookup Δ 0)) ∨ isYes (lookup Δ 0 +ⁱ ℤ.pos 1 ≟ⁱ lookup Δ 0 +ⁱ ℤ.pos 1)
        ≡⟨ cong (λ x → x ∨  isYes (lookup Δ 0 +ⁱ ℤ.pos 1 ≟ⁱ lookup Δ 0 +ⁱ ℤ.pos 1)) not-isYes-lookup0≡lookup0_is_false ⟩ 
          false ∨ isYes (lookup Δ 0 +ⁱ ℤ.pos 1 ≟ⁱ lookup Δ 0 +ⁱ ℤ.pos 1)
        ≡⟨ cong (λ x → false ∨ x) isYes-lookup0+1=lookup0+1_is_true ⟩
          true 
        ∎ 
      true≡false : true ≡ false
      true≡false = {!!} -- TODO. Hints: you need to make use of eval_is_true and eval-eq
      
      sub_prf : ⊥
      sub_prf = ¬true≡false true≡false
```

### Exercise 3

The following proof is generated by an AI model.

Spot the AI slop! (It is a correct proof, but it is smelly.)


```agda
module FacWLPProof where

  open  FacProof


  infered_wlp : Pred
  infered_wlp = wlp post prog
{-
  (not (($ 0) <ʰ (C +0)) and ($ 0) !ʰ *ʰ (C ℤ.pos 1) ≡ʰ ($ 0) !ʰ) and
   ((((not (($ 0) <ʰ (C +0)) and ($ 0) !ʰ *ʰ (C ℤ.pos 1) ≡ʰ ($ 0) !ʰ)
   and (($ 0) >ʰ (C +0)))
  ⇒
  (not (($ 0) -ʰ (C ℤ.pos 1) <ʰ (C +0)) and
   (($ 0) -ʰ (C ℤ.pos 1)) !ʰ *ʰ ((C ℤ.pos 1) *ʰ ($ 0)) ≡ʰ ($ 0) !ʰ))
 and
 (((not (($ 0) <ʰ (C +0)) and ($ 0) !ʰ *ʰ (C ℤ.pos 1) ≡ʰ ($ 0) !ʰ)
   and not (($ 0) >ʰ (C +0)))
  ⇒
  (($ 0) ≡ʰ (C +0) and
   ((C ℤ.pos 1) ≡ʰ ($ 0) !ʰ and
    (not (($ 0) <ʰ (C +0)) and ($ 0) !ʰ *ʰ (C ℤ.pos 1) ≡ʰ ($ 0) !ʰ)))))
 -}



  precond⇒infered_wlp : ⊨ ( pre ⇒ infered_wlp )
  precond⇒infered_wlp Δ = helper Δ (lookup Δ n) refl
    where
      pred≡-1 : ∀ v → pred v ≡ v -ⁱ 1ℤ
      pred≡-1 v = +-comm -1ℤ v

      factorial-step : ∀ v → +0 <ⁱ v → v ! ≡ ((v -ⁱ 1ℤ) !) *ⁱ v
      factorial-step v 0<v with v ≤ᵇ +0 in eq
      ... | true = ⊥-elim (<⇒≱ 0<v (≤ᵇ⇒≤ (subst T (sym eq) tt)))
      ... | false = refl

      helper : ∀ Δ v → lookup Δ n ≡ v → T (eval Δ (pre ⇒ infered_wlp))
      helper Δ v v-eq -- relies on trichotomy of ℤ
        rewrite v-eq
        with v <?ⁱ +0 | +0 <?ⁱ v | (v ! *ⁱ 1ℤ) ≟ⁱ (v !) | (v -ⁱ 1ℤ) <?ⁱ +0 | ((v -ⁱ 1ℤ) ! *ⁱ (1ℤ *ⁱ v)) ≟ⁱ (v !) | v ≟ⁱ +0 | 1ℤ ≟ⁱ v !
      ... | yes v<0   | _        | _                    | _                | _                                   | _       | _          = tt
      ... | no ¬v<0   | yes 0<v  | no ¬v!*1≡v!          | _                | _                                   | _       | _          = ⊥-elim ( ¬v!*1≡v! (*-identityʳ (v !)))
      ... | no ¬v<0   | yes 0<v  | yes _                | yes v-1<0        | _                                   | _       | _          = ⊥-elim (<⇒≱ v-1<0 (subst (+0 ≤ⁱ_) (pred≡-1 v) (i<j⇒i≤pred[j] 0<v)))
      ... | no ¬v<0   | yes 0<v  | yes _                | no _             | no ¬v-1!*1*v≡v!                     | _       | _          = ⊥-elim (¬v-1!*1*v≡v! (trans (cong (((v -ⁱ 1ℤ) !) *ⁱ_) (*-identityˡ v)) (sym (factorial-step v 0<v))))
      ... | no ¬v<0   | yes 0<v  | yes _                | no _             | yes _                               | _       | _          = tt
      ... | no ¬v<0   | no ¬0<v  | no ¬v!*1≡v!          | _                | _                                   | _       | _          = ⊥-elim (¬v!*1≡v! (*-identityʳ (v !)))
      ... | no ¬v<0   | no ¬0<v  | yes _                | _                | _                                   | no ¬v≡0 | _          = ⊥-elim (¬v≡0 (≤∧≮⇒≡ (≮⇒≥ {+0} {v} ¬0<v) ¬v<0))
      ... | no ¬v<0   | no ¬0<v  | yes _                | _                | _                                   | yes v≡0 | no ¬1≡v    = ⊥-elim (¬1≡v (sym (cong _! v≡0)))
      ... | no ¬v<0   | no ¬0<v  | yes _                | _                | _                                   | yes _   | yes _      = tt


```
