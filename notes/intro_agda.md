---
title: '50.057 Introduction to Agda'
author:
- ISTD, SUTD
header-includes:
  - \usepackage{newunicodechar}
  - \usepackage{amssymb}
  - \newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
  - \newunicodechar{∀}{\ensuremath{\forall}}
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
  - \newunicodechar{ʰ}{h}
  - \newunicodechar{ᵉ}{e}
  - \newunicodechar{₀}{0}
  - \newunicodechar{⨾}{;}
  - \newunicodechar{λ}{\ensuremath{\lambda}}
  - \newunicodechar{¬}{\ensuremath{\neg}}
  - \newunicodechar{ⁱ}{i}
  - \newunicodechar{ʳ}{r}
  - \newunicodechar{₁}{1}
  - \newunicodechar{₂}{2}
  - \newunicodechar{ℤ}{\ensuremath{\mathbb{Z}}}
  - \newunicodechar{Δ}{\ensuremath{\Delta}}
  - \newunicodechar{⇒}{\ensuremath{\Rightarrow}}
  - \newunicodechar{∃}{\ensuremath{\exists}}
  - \newunicodechar{∎}{\#}
  - \newunicodechar{≟}{=?}
  - \newunicodechar{⟦}{[[}
  - \newunicodechar{⟧}{]]}
  - \newunicodechar{⊨}{\ensuremath{\models}}
---

# 50.057 Introduction to Agda

## Learning Outcomes

* Explain what Agda is, and how dependent types and the Curry-Howard correspondence turn programs into proofs.
* Install Agda and set up the Emacs `agda2-mode`.
* Use the most common Emacs/Agda2-mode commands to develop Agda code interactively.
* Write basic Agda definitions: datatypes, functions by pattern matching, infix operators, modules, and imports.
* Define and reason about natural numbers, carry out proofs by induction, and define relations as inductive types.
* Map common Agda constructs to the PLFA Part 1 chapters.

This note is *not* a complete Agda course. It is a condensed tour of the Agda ideas used later in the formal verification material. For a full treatment, see Part 1 of *Programming Language Foundations in Agda* (PLFA) at <https://plfa.github.io/>: [Naturals](https://plfa.github.io/Naturals/), [Induction](https://plfa.github.io/Induction/), [Relations](https://plfa.github.io/Relations/), [Equality](https://plfa.github.io/Equality/), [Connectives](https://plfa.github.io/Connectives/), [Negation](https://plfa.github.io/Negation/), [Quantifiers](https://plfa.github.io/Quantifiers/), [Decidable](https://plfa.github.io/Decidable/), and [Lists](https://plfa.github.io/Lists/).


## What is Agda?

Agda is three things at once:

1. A **pure, dependently typed functional programming language** (in the same spirit as Haskell, but with a much richer type system).
2. A **proof assistant**, because types can express logical propositions and well-typed programs are proofs of those propositions (the *Curry-Howard correspondence*).
3. An **interactive environment** (tightly integrated with Emacs) where you write programs with *holes*, ask Agda for their types, and gradually refine the holes until the file type-checks.

Because types can depend on values, we can encode properties directly in types. For example, a function that returns the head of a non-empty list can have the type

```agda
head : ∀ {A : Set} {n : ℕ} → SList A (suc n) → A
```

where `SList A (suc n)` is the type of lists of length `suc n`. The type itself guarantees that the list is not empty, so the function never has to handle the `nil` case. This idea—*illegal states are unrepresentable*—is the main reason Agda is used for formal verification.


## Installation

There are two common ways to get Agda on macOS/Linux. Pick whichever matches your setup.

### Option 1: Homebrew (simplest)

If you use Homebrew, Agda and its standard library can be installed with

```bash
brew install agda
```

Afterwards, make sure `agda` and `agda-mode` are on your `PATH`:

```bash
agda --version
agda-mode setup
```

### Option 2: Through `cabal` (the PLFA setup)

The machine that produced these notes uses this route. First install a Haskell toolchain (`ghc` and `cabal`) using [GHCup](https://www.haskell.org/ghcup/):

```bash
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

Then install Agda:

```bash
cabal update
cabal install Agda
```

Agda needs the *standard library*. The setup used for PLFA clones the whole PLFA repository and registers the bundled standard library:

```bash
git clone https://github.com/plfa/plfa.github.io.git ~/plfa
cd ~/plfa
```

Tell Agda where the library is by creating two files:

* `~/.agda/libraries` containing

  ```
  $HOME/plfa/standard-library/standard-library.agda-lib
  $HOME/plfa/src/plfa.agda-lib
  ```

* `~/.agda/defaults` containing

  ```
  standard-library
  plfa
  ```

Verify the installation:

```bash
agda --version
```

If `agda` is not found, add `~/.cabal/bin` to your `PATH`.


## Setting up Emacs and `agda2-mode`

Most people write Agda inside Emacs. Once `agda-mode` is installed, run

```bash
agda-mode setup
```

This appends the necessary Emacs configuration (loading `agda2-mode` and the Agda input method) to your Emacs init file, usually `~/.emacs` or `~/.emacs.d/init.el`. If you use a custom Emacs distribution such as Doom or Spacemacs, consult its documentation; the key idea is to load `agda2-mode` from wherever `agda-mode` installed it.

Open a file named `HelloAgda.agda`. Emacs should switch to `Agda2` mode (check the mode line). The simplest sanity check is to load the file with `C-c C-l` (see next section).


## Emacs basics and Agda2-mode keyboard shortcuts

### Minimal Emacs survival kit

| Keys | Action |
|------|--------|
| `C-x C-f` | Open a file |
| `C-x C-s` | Save the file |
| `C-x C-c` | Quit Emacs |
| `C-g` | Cancel the current command |
| `M-x` | Run an extended command |
| `C-x b` | Switch buffer |
| `C-x o` | Move to the other window |
| `C-x 1` | Close all other windows |

`C-` means Ctrl, `M-` means Meta (usually Option/Alt or Esc).

### Agda2-mode commands

The interaction model is: you write a file containing *holes* written `{! !}`, then ask Agda to check, split cases, fill holes, etc.

| Keys | Action |
|------|--------|
| `C-c C-l` | **Load** the file. Type-checks everything and highlights errors/unsolved holes. |
| `C-c C-c` | **Case split** on the variable under the cursor inside a hole. |
| `C-c C-SPC` | **Give** the expression in the hole to Agda, if it has the right type. |
| `C-c C-r` | **Refine** the hole: Agda inserts the function skeleton and leaves new holes for the arguments. |
| `C-c C-,` | Show the **goal type and context** at the current hole. |
| `C-c C-.` | Like `C-c C-,`, but also shows the inferred type of the expression in the hole. |
| `C-c C-d` | **Deduce** the type of a selected expression. |
| `C-c C-n` | **Normalise** (fully evaluate) a selected expression. |
| `M-.` | Jump to the definition of the identifier under the cursor. |
| `M-,` | Jump back. |
| `C-c C-x C-h` | Show all Agda2-mode keybindings. |
| `C-c C-x C-d` | Toggle display of implicit arguments. |
| `C-c C-a` | Try to solve the hole automatically (`Agsy`). |
| `C-c C-x C-a` | Abort a running Agda process. |

### Unicode input

Agda source files make heavy use of Unicode. Emacs enters these through the *Agda input method*. Toggle it with `C-\`. Then type a backslash and the mnemonic name:

| Type | Becomes |
|------|---------|
| `\bN` | `ℕ` |
| `\->` or `\to` | `→` |
| `\l` | `λ` |
| `\forall` | `∀` |
| `\==` | `≡` |
| `\le` | `≤` |
| `\times` | `×` |
| `\uplus` | `⊎` |
| `\Sigma` | `Σ` |
| `\top` | `⊤` |
| `\bot` | `⊥` |
| `\langle` | `⟨` |
| `\rangle` | `⟩` |
| `\::` | `∷` |

A mnemonic like `\bN` is read “blackboard N”. If you forget a name, `C-c C-x C-h` lists the input-method bindings.

Alternatively, you can also move the cursor to a unicode character and use `C-u C-x` = (or run `M-x describe-char`) to display the detail of that unicode character. 


## First Agda definitions

### Literate files

Files with the `.lagda.md` extension are *literate Agda* files: a Markdown file where code blocks marked ` ```agda ` are checked by Agda. The surrounding text is ordinary Markdown. Non-literate files use the extension `.agda`.

Every Agda file must begin with a module declaration that matches the file name:

```agda
module HelloAgda where
```

Comments are `--` to the end of the line, or `{- ... -}` for blocks.

### Datatypes

The natural numbers are defined inductively:

```agda
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
```

`Set` is the type of small types. `zero` and `suc` are *constructors*. Values are built by repeatedly applying `suc` to `zero`: `zero`, `suc zero`, `suc (suc zero)`, etc.

This Agda declaration does exactly the same job as the following pieces of a predicate-logic specification:

* `zero` is a constant object (a 0-ary function).
* `suc` is a unary function symbol.
* The predicate $Nat(\_)$ is defined by the two axioms
  $$
  Nat(zero)
  \qquad
  \forall n.\ (Nat(n) \implies Nat(suc(n)))
  $$
* The induction principle for `ℕ` is
  $$
  \begin{array}{c}
  P(zero) \quad \forall n.\ (P(n) \implies P(suc(n))) \\
  \hline
  \forall n.\ P(n)
  \end{array}
  $$

In Agda, the `data` declaration bundles the constructors *and* the induction principle into one definition. The values `zero`, `suc zero`, `suc (suc zero)` are the *ground terms* of the datatype, just as they are the ground terms built from the function symbols in predicate logic.

Functions are defined by *pattern matching*:

```agda
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

infixl 6 _+_
```

The underscores in `_+_` are placeholders: `_+_` is an infix operator, and `m + n` is the same as `_+_ m n`. `infixl 6 _+_` declares it left-associative with precedence 6.

### Type synonyms, records, and `where`

A type synonym is just an abbreviation:

```agda
Val = ℤ
Var = ℕ
Env = List (Var × Val)
```

Local definitions are introduced with `where`:

```agda
double-plus : ℕ → ℕ
double-plus n = m + m
  where
  m = n + n
```

### Infix and mixfix operators

Agda allows operators that are not just words. For example, arithmetic operators and a factorial operator can be declared with:

```agda
infixl 6 _+_
infixl 6 _-_
infixl 7 _*_
infix  8 _!
```

and a mixfix conditional can be defined with:

```agda
if_then_else_ : Bool → Cmd → Cmd → Cmd
```

This lets us write `if b then c₁ else c₂` asssuming we have defined the `Cmd` datatype with `c₁` and `c₂` are its value terms. 


## Imports and name management

A typical Agda file opens with a collection of imports. The syntax is very flexible:

```agda
import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; map)

open import Data.Integer using (ℤ ; +0 ; 1ℤ)
  renaming (_+_ to _+ⁱ_; _*_ to _*ⁱ_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
```

* `open import M` imports `M` and immediately opens its names.
* `open M using (...)` opens only the listed names.
* `renaming (old to new)` imports a name but calls it something else (useful when several modules define `_+_`).
* `import M as Alias` imports `M` under a short alias; you refer to its names as `Alias.name`.

Implicit arguments are written in braces. For example, the equality type is parameterised over a type `A` and two values, but Agda usually infers them:

```agda
refl : ∀ {A : Set} {x : A} → x ≡ x
```

When you need to supply an implicit argument explicitly, write it in braces at a call site: `f {x = e}` or just `f {e}`.


## Proving in Agda: equality and induction

### Propositional equality

Equality in Agda is an inductive family with one constructor:

```agda
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
```

The type `x ≡ y` is the proposition that `x` and `y` are equal. The only way to prove it is `refl`, which proves `x ≡ x`. Pattern matching on a proof `x ≡ y` replaces `y` with `x`, because the only possible constructor is `refl`.

The standard library provides helpers:

```agda
cong  : ∀ {A B : Set} (f : A → B) {x y} → x ≡ y → f x ≡ f y
sym   : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
subst : ∀ {A : Set} (P : A → Set) {x y} → x ≡ y → P x → P y
```

### Induction is recursion

To prove a property for all natural numbers, define a function by recursion on the natural number. This is exactly the induction principle you know from mathematics.

#### Hand-written proof: associativity of addition

We model addition with two axioms:

$$
\begin{array}{ll}
({\tt AddZero}) & \forall n.\ add(zero, n) = n \\
({\tt AddSuc})  & \forall m n.\ add(suc(m), n) = suc(add(m, n))
\end{array}
$$

The goal is

$$
\forall m n p.\ add(add(m,n), p) = add(m, add(n,p)).
$$

We prove it by linear induction on $m$. Let

$$
\psi(m) \equiv \forall n p.\ add(add(m,n), p) = add(m, add(n,p)).
$$

The induction rule is

$$
\begin{array}{c}
\psi(zero) \\
\forall x.\ (\psi(x) \implies \psi(suc(x))) \\
\hline
\forall x.\ \psi(x)
\end{array}
$$

For the equality steps we use the following rules:

$$
\begin{array}{c}
s = t \\
\hline
C[s] = C[t]
\end{array}
\quad ({\tt EqSubst})
\qquad
\begin{array}{c}
a = b \quad b = c \\
\hline
a = c
\end{array}
\quad ({\tt EqTrans})
\qquad
\begin{array}{c}
a = b \\
\hline
suc(a) = suc(b)
\end{array}
\quad ({\tt CongSuc})
$$

$C[\cdot]$ is any context: we may replace equals by equals inside a term. We also use symmetry of equality, $a = b \Rightarrow b = a$, written `EqSym`, when convenient.

**Base case:** $\psi(zero)$. Let $n$ and $p$ be arbitrary.

$$
\begin{array}{|r|c|l|}
\hline
1. & add(zero, n) = n & {\tt Axiom\ (AddZero)} \\ \hline
2. & add(add(zero,n), p) = add(n, p) & {\tt EqSubst}: 1 \\ \hline
3. & add(zero, add(n,p)) = add(n, p) & {\tt Axiom\ (AddZero)} \\ \hline
4. & add(n, p) = add(zero, add(n,p)) & {\tt EqSym}: 3 \\ \hline
5. & add(add(zero,n), p) = add(zero, add(n,p)) & {\tt EqTrans}: 2, 4 \\ \hline
6. & \forall n p.\ add(add(zero,n), p) = add(zero, add(n,p)) & \forall{\tt Intro}: n, p \\ \hline
\end{array}
$$

**Inductive case:** $\forall m.\ (\psi(m) \implies \psi(suc(m)))$. Let $m$ be arbitrary and assume the induction hypothesis

$$
{\tt IH} \equiv \forall n p.\ add(add(m,n), p) = add(m, add(n,p)).
$$

Let $n$ and $p$ be arbitrary.

$$
\begin{array}{|r|c|l|}
\hline
1. & add(suc(m), n) = suc(add(m,n)) & {\tt Axiom\ (AddSuc)} \\ \hline
2. & add(add(suc(m),n), p) = add(suc(add(m,n)), p) & {\tt EqSubst}: 1 \\ \hline
3. & add(suc(add(m,n)), p) = suc(add(add(m,n), p)) & {\tt Axiom\ (AddSuc)} \\ \hline
4. & add(add(suc(m),n), p) = suc(add(add(m,n), p)) & {\tt EqTrans}: 2, 3 \\ \hline
5. & add(add(m,n), p) = add(m, add(n,p)) & \forall{\tt Elim}: {\tt IH} \\ \hline
6. & suc(add(add(m,n), p)) = suc(add(m, add(n,p))) & {\tt CongSuc}: 5 \\ \hline
7. & add(add(suc(m),n), p) = suc(add(m, add(n,p))) & {\tt EqTrans}: 4, 6 \\ \hline
8. & add(suc(m), add(n,p)) = suc(add(m, add(n,p))) & {\tt Axiom\ (AddSuc)} \\ \hline
9. & suc(add(m, add(n,p))) = add(suc(m), add(n,p)) & {\tt EqSym}: 8 \\ \hline
10. & add(add(suc(m),n), p) = add(suc(m), add(n,p)) & {\tt EqTrans}: 7, 9 \\ \hline
11. & \forall n p.\ add(add(suc(m),n), p) = add(suc(m), add(n,p)) & \forall{\tt Intro}: n, p \\ \hline
12. & \psi(m) \implies \psi(suc(m)) & \implies{\tt Intro}: {\tt IH}, 11 \\ \hline
13. & \forall m.\ (\psi(m) \implies \psi(suc(m))) & \forall{\tt Intro}: m \\ \hline
\end{array}
$$

By linear induction we conclude $\forall m.\ \psi(m)$, i.e.

$$
\forall m n p.\ add(add(m,n), p) = add(m, add(n,p)).
$$

#### The same proof in Agda

The hand-written induction above becomes a recursive function in Agda:

```agda
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero    n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)
```

* Base case: `(zero + n) + p` reduces to `n + p`, and `zero + (n + p)` reduces to `n + p`, so `refl` proves them equal.
* Inductive step: assuming the induction hypothesis `(m + n) + p ≡ m + (n + p)`, we apply `cong suc` to both sides because `suc` is applied on the outside.

### Equational reasoning

For longer proofs, Agda provides a readable chain notation via `≡-Reasoning`. Here is the same `+-assoc` lemma reproved in that style:

```agda
open Eq.≡-Reasoning

+-assoc' : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc' zero n p =
  begin
    (zero + n) + p
  ≡⟨ refl ⟩
    n + p
  ≡⟨ sym refl ⟩
    zero + (n + p)
  ∎
+-assoc' (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨ refl ⟩
    suc (m + n) + p
  ≡⟨ refl ⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc' m n p) ⟩
    suc (m + (n + p))
  ≡⟨ sym refl ⟩
    suc m + (n + p)
  ∎
```

Each line is chained by an equality justification. The base case needs `sym refl` at the end because `zero + (n + p)` reduces to `n + p`, so we are using the equation in the reverse direction. The inductive step applies the induction hypothesis under `cong suc` and finishes with another `sym refl`.


## Relations as inductive types

A binary relation on `ℕ` can be defined as an indexed datatype:

```agda
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
```

The two constructors are exactly the inference rules you would draw on paper:

```
           m ≤ n
  ------   ---------
  zero ≤ n  suc m ≤ suc n
```

Agda actually lets you write the line of dashes in source files; it is treated as a separator and does not affect parsing. This is why the inference-rule style reads so naturally in Agda.

Proofs about relations are again proofs by pattern matching:

```agda
≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n       _         = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)
```

This idea scales to arbitrary relations. Evaluation relations, typing relations, program-logic judgments, and ordering relations such as `≤` are all defined in the same way: as inductive families whose constructors can be read as inference rules.


## Decidable propositions and the `with` construct

Many practical proofs need to branch on a decision. The type `Dec P` says that `P` is decidable:

```agda
data Dec (P : Set) : Set where
  yes :   P → Dec P
  no  : ¬ P → Dec P
```

For example, natural numbers have decidable equality `_≟_`. A typical use is to branch on whether two values are equal:

```agda
open import Data.Bool using (Bool; true; false)

same? : ℕ → ℕ → Bool
same? m n with m ≟ n
... | yes _ = true
... | no  _ = false
```

`with m ≟ n` evaluates the decision and then pattern matches on the result. `yes _` means the values are equal (the proof is ignored with `_`); `no _` means they are not. `≟` is overloaded; if you use both natural-number and integer equality in the same file you may need to rename one of them.

When the proof inside `yes` is needed later, give it a name:

```agda
... | yes m≡n = cong suc m≡n
```

Here `m≡n` is a proof of `m ≡ n`.

Here `⊥-elim` is *ex falso quodlibet*: from a proof of the empty type `⊥` we can prove anything. It is used when a branch is impossible.

The `rewrite` keyword is a convenient shorthand for `subst`. If you have a proof `eq : x ≡ y`, then `rewrite eq` replaces `x` by `y` in the goal. The `in` form (`with ... in eq`) keeps the equation around for rewriting later.


## Connectives, negation, quantifiers

The logical connectives are just datatypes:

```agda
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where   -- no constructors
```

* `A × B` is conjunction: a pair of proofs.
* `A ⊎ B` is disjunction: either a proof of `A` or a proof of `B`, tagged.
* `⊤` is the always-true proposition, with one trivial proof `tt`.
* `⊥` is the false proposition, with no proofs.

Negation is defined as implication to falsity:

```agda
¬_ : Set → Set
¬ A = A → ⊥
```

To prove `¬ A` you assume `A` and derive a contradiction. Since `⊥` has no constructors, the only way to construct a value of type `⊥` is to exploit the assumption `A`.

### Intuitionistic logic

Agda implements **intuitionistic** logic, not classical logic. A proposition is true only when we can construct a proof of it. Because of that, some classical principles are not valid in general:

* **Law of Excluded Middle (LEM):** `P ⊎ ¬ P` is not provable for an arbitrary proposition `P`. It is only provable when `P` is *decidable* (e.g. `n ≡ m` for natural numbers).
* **Double-negation elimination:** `¬ ¬ P → P` is not provable in general. We can prove the weaker direction `P → ¬ ¬ P`, but the converse requires an explicit proof of `P`.

This may feel restrictive, but it matches the computational reading of proofs: knowing that `P` is not false does not automatically give us a witness or construction for `P`.

For example, the following type is *not* inhabited for an arbitrary `P`:

```agda
lem : ∀ {P : Set} → P ⊎ ¬ P
lem = {! !}
```

Agda will not let you fill that hole (try `C-c C-a` and watch it fail). On the other hand, the following direction is fine:

```agda
¬¬-intro : ∀ {P : Set} → P → ¬ ¬ P
¬¬-intro p np = np p
```

If you ever need LEM for a particular decidable proposition, you can use `Dec` from `Relation.Nullary` and branch on `yes p` or `no ¬p`.

Universal quantification is a dependent function type `∀`, and existential quantification is a dependent pair `Σ`:

```agda
Σ : ∀ {A : Set} (B : A → Set) → Set
Σ = Product.Σ

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ = Σ
```

To prove `∃ B` you provide a witness `a` and a proof of `B a`, written `a , p`.

### Example: even or odd

Using `_⊎_` we can state that every natural number is either even or odd.

```agda
open import Data.Nat.Properties using (even?)

EvenOrOdd : ℕ → Set
EvenOrOdd n = (T (even? n)) ⊎ (T (even? (suc n)))

even-or-odd : ∀ n → EvenOrOdd n
even-or-odd zero = inj₁ tt
even-or-odd (suc zero) = inj₂ tt
even-or-odd (suc (suc n)) = even-or-odd n
```

Each branch returns the appropriate tag. For `0` we say it is even; for `1` we say the successor of `0` is even, so `1` is odd; for `2 + n` we reuse the proof for `n`.

### Example: a conjunction with a witness

Using `_×_` and `Σ` we can state that there is an even number greater than any given number. The existential `Σ` demands a witness, and the conjunction bundles it with a proof.

```agda
_<_ : ℕ → ℕ → Set
m < n = suc m ≤ n

GreaterEven : ℕ → Set
GreaterEven n = Σ ℕ (λ m → T (even? m) × n < m)
```

Constructing a value of type `GreaterEven n` would mean producing a witness `m`, a proof that `m` is even, and a proof that `n < m`. This is direct evidence what connectives and quantifiers look like as Agda programs.


## From booleans to propositions: the `T` bridge

Many Agda developments start with a boolean function and then want a *proposition* (a `Set`) saying that the function returns `true`. The standard-library function `T : Bool → Set` does exactly this:

```agda
T : Bool → Set
T true  = ⊤
T false = ⊥
```

For example, here is a boolean test for evenness:

```agda
even? : ℕ → Bool
even? zero          = true
even? (suc zero)    = false
even? (suc (suc n)) = even? n
```

We turn it into a predicate on natural numbers:

```agda
Even : ℕ → Set
Even n = T (even? n)
```

Now `Even n` is a proposition:

* `Even zero` reduces to `⊤`, so it has the trivial proof `tt`.
* `Even 1` reduces to `⊥`, so it has no proof.
* `Even 2` reduces to `⊤` again.

This is the bridge between executable boolean predicates and logical propositions in Agda. It is used whenever boolean computations need to become logical propositions.


## Putting it together

The constructs above are exactly the ones used in PLFA-style Agda proofs. Consider the `≤` relation on natural numbers from the Relations section:

* an inductive datatype (`data _≤_`) defines the relation;
* pattern matching and recursion prove properties such as reflexivity and transitivity;
* propositional equality (`≡`) and equational reasoning handle arithmetic side-conditions;
* connectives and quantifiers appear when more complex lemmas are stated;
* decidability (`Dec`, `_≟_`) lets us branch on equality.

This same collection of ingredients—datatypes, functions, relations, equality, connectives, and decidability—is what you use whenever you formalise a language, a logic, or a program-correctness argument in Agda.

| Construct | Typical use | PLFA chapter |
|-----------|-------------|--------------|
| Modules and imports | Structuring a development | Getting Started |
| Inductive datatypes | Syntax, judgments, relations | Naturals / Relations |
| Pattern matching / recursion | Definitions and lemmas | Naturals |
| Decidable equality (`_≟_`, `Dec`) | Case analysis on equality | Decidable |
| Propositional equality and equational reasoning | Arithmetic and algebraic lemmas | Equality / Induction |
| Inductive relations | `_≤_`, evaluation relations, etc. | Relations |
| Connectives, negation, quantifiers | Logical combinators | Connectives / Negation / Quantifiers |
| `T : Bool → Set` | Turning boolean tests into propositions | Decidable |
| Lists | Sequences, environments | Lists |

You will see these ideas again when we turn to formal verification later in the module.


## A small file to try

Create `HelloAgda.agda`:

```agda
module HelloAgda where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero    n p = refl
+-assoc (suc m) n p = cong suc (+-assoc m n p)
```

In Emacs, load it with `C-c C-l`. If the file type-checks, you have a working Agda environment.


## Further reading

* PLFA Part 1: <https://plfa.github.io/> — especially [Naturals](https://plfa.github.io/Naturals/), [Induction](https://plfa.github.io/Induction/), [Relations](https://plfa.github.io/Relations/), [Equality](https://plfa.github.io/Equality/), [Connectives](https://plfa.github.io/Connectives/), [Negation](https://plfa.github.io/Negation/), [Quantifiers](https://plfa.github.io/Quantifiers/), [Decidable](https://plfa.github.io/Decidable/), and [Lists](https://plfa.github.io/Lists/).
* Agda User Manual: <https://agda.readthedocs.io/>
* PLFA Getting Started guide: <https://plfa.github.io/GettingStarted/>
