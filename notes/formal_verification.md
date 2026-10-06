---
title: '50.057 Formal Verification'
author:
- ISTD, SUTD
header-includes:
  - \usepackage{newunicodechar}
  - \newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
  - \newunicodechar{∀}{\ensuremath{\forall}}
---


# 50.057 Formal Verification


## Learning Outcomes

* Explain what software formal verification is.
* List the common techniques of software formal verification.
* Explain the advantange and disadvantage of Theorem Proving.
* Explain what partial correctness is.
* Apply Hoare Logic to verify a program's correctness given precondition, post-conditions and loop invariants.
* Apply Weakest Liberal Precondition to infer the precondition, postcondition annotations.

## What is Formal Verification?

Formal Verification is a study of using mathematical tools to prove or disprove the correctness of a system.
In the context of this module, our concern is the correctness of a software. 

## Software Formal Verification

In software formal verification, we often start with the 

1. the (formal) specification of the software and assumed context of execution
1. the software implementation (or the detailed design)
1. the desired property to be verified 

We model the above three using mathematical models to check that whether given the specification and the assume context, the implementation 
will logically entail the desired property.

## Common Techniques of Software Formal Verification

* Model Checking - to model the software system as a finite state machine and verify that the desired property is held in all states.
* Theorem Proving - to use a logical proposition representat that the desired property is implied by the given logical model of the program and the specification, then use a theorem prove to prove it. (We will look into this in this module).
* Abstract Interpretation - to use lattice to model a sound approximation of the desired property of the program, and by executing the fix-point algorithm to acertain that the property is valid in all program locations/states, (covered in 50.054).
* Symbolic Execution - to executes programs using symbolic values instead of concrete data to mathematically track conditions leading to different branches, (we have seen it in 50.003)


## Pros and Cons of Theorem Proving 

One advantage of using theorem proving technique software formal verification is that it is versatile and highly expressive. Unlike
type diven development which relies on the advance type features offered in the source language's compiler tool, theorem proving based verification 
does not require the specification and the goal property to be encoded using type system. 

One disadvantage of theorem proving is that translating the specification and desire goal into formal system such as predicate logic is non-trivial.
Constructing the invariant from the software program is undecidable in general (thanks to Kurt Gödel's theorem of incompleteness). The proving process itself could be tedious and subject to the underlying theorem prover limitation (more on this later).


## Theorem Provers

There are two main types of theorem provers, 

* Automated Theorem Provers, e.g. Microsoft's Z3, Prover9, Vampire
* Proof Assistants, e.g. Lean, Rocq, Agda and Isabelle. 

### Automated Theorem Provers versus Proof Assistants

The two families differ fundamentally in what they can promise, and the difference ultimately traces back to the undecidability results (Gödel, 1931; Turing and Church, 1936) we met in the dependent type notes.

| | Automated Theorem Provers | Proof Assistants |
|---|---|---|
| Examples | Z3 (an SMT solver), Prover9, Vampire | Lean, Rocq, Agda, Isabelle |
| Target logic | A fixed, usually decidable fragment, e.g. SMT theories (first-order logic combined with linear arithmetic, arrays, datatypes), or first-order proof search | A general, highly expressive logic: higher-order logic, intuitionistic type theory, often with dependent types |
| Decidability | For the decidable fragment it targets, an answer (yes or no) is guaranteed in principle; a first-order prover such as Prover9 can only *find* proofs, and may run forever | The logic is undecidable in general: no algorithm can decide provability, so a search may never terminate |
| Interaction | Fully automated: hand it a formula, wait for a model or a proof | Interactive: the user guides the proof with tactics and lemmas; the machine verifies every step |
| Meaning of a "no" answer | For a decidable-fragment solver, "no" means the formula is genuinely unprovable in that fragment; a first-order prover simply never answers "no" | The prover never returns a "no" — it either produces a verified proof, or the goal simply stays open |
| Expressiveness | First-order properties over the built-in theories | Inductive and dependent types, arbitrary program invariants, even program extraction from the proof |
| Trust | A "yes" comes with a checkable proof certificate; a "no" relies on the solver being complete for its fragment | Every step is re-checked by a small, independently audited kernel of trusted code |

Three practical observations follow from the table.

1. *Proof assistants borrow the power of ATPs.* In practice, a proof assistant will call an automated solver as a tactic whenever the current subgoal falls into a decidable fragment (say, linear arithmetic), and fall back to interactive proof construction otherwise.
2. *The undecidability is the dividing line.* Since no algorithm can decide in general whether a logical proposition is provable, no proof assistant can ever be a fully automated prover. What it offers instead is *certainty*: a finished proof has been checked step by step, so it is a genuine mathematical proof, not just the output of a heuristic search.
3. *Proof assistant and LLM* Recently, there is an uprising trend to use LLMs to help to complete a proof step by step and interactively verified by a proof assistant. This speed up the process of finding correct proofs. However as pointed out by many mathematicians, the generated proofs are yet need to digested and canonalicalized. 



## Partial Correctness 

To avoid "being cornered" by the halting problem, we would like to state the goal of 
software formal verification process by defining **partial correctness** as follows


A program $s$ is *partially correct* with respect to pre-/post-conditions $P$ and $Q$ iff 

* all executions of $s$ starting from states satisfying $P$ are free of runtime errors, and; 
* any such executions which terminate will do so in states satisfying $Q$.


## Some Motivating Examples 


### Example 1: `add_one`
Consider the following implementation of Rust function that takes an integer and add one to it.

```rust
fn add_one(n : i32) -> i32 {
    let mut r = n;
    r = r + 1;
    r
}
```
Suppose our claim is "for all integer `n`, `add_one(n)` is equal to `n+1`". We want to prove it. 

We could do it by annotating the program statement by statement, the annotations (as comments) contain
 some logical predicate that capture the states of the computation before and after that surrounded statement. 


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

In the annotated program above, we started off with the true predicate $n == n$ which is the same as $true$ (because we know that for all integer $n$, $n = n$.) This is the "initial" state of the computation defined by this function.

Note that the $n$ in the predicate (inside the comment) is a logical variable that represent the system state of the 
program variable `n`. Although they share the same name (in different font style when it is not in the comment block), they are two different entities. We can think of the logical variable $n$ in the predicate captures the  possible state of the program variable during run-time. 

In the annotation of the first statement `let mut r = n;` we have the following predicate

$$
r = n
$$

(recall that we can define $=$ as $eq(\_,\_)$)

which says that after executing the assignment statement, we establish the fact that the two variables `r` and `n` must hold the same value.

Note that by logical implication and the number system (for instance, Peano system) we find that the above predicate 
implies the following 

$$
r + 1 = n + 1
$$

(recall that $ \_ + 1$ can be defined as $suc(\_)$ in the Peano system)

Given the above "state", we can verify that after executing `r = r + 1;`, ( which semantically means 
"add 1 to the old value of `r` and assign the result to `r`") , we can conclude that

$$
r = n + 1
$$

we simply substitute the logic term $r + 1$ in the previous predicate by $r$ on the LHS of the equation.


We argue that the above is the proof to our claim. 

### Example 2: `fac` 

For a simple program without loop, the verification process is straight-forward. Things become complex in the presence of loops.

Consider the factorial implementation in Rust as follows, 

```rust
fn fac(n: i32) -> i32 { 
    // { n >= 0 }
    let mut i = n;
    // { i >= 0 & i = n } 
    let mut r = 1;
    // { i >= 0 & r = 1 }
    while i > 0 {
        r = r * i;
        i = i - 1;
    }
    // { i = 0 & r = n!}
    r
}

```
We have partially annotated the program with the predicates, except for the while loop. 

The question is: what shall we fill in between those statemenets inside the while loop body so that we have the same
mechanism to verify the claim $r = n!$?

What is missing here is what we call *loop invariant*, which is a predicate should be satisfied in all locations during the program execution. For now we skip the process of constructing the invariant, assume that we are given the loop invariant 

$$
i \ge 0 \wedge i! * r = n! 
$$

Let's call the above predicate $I$. If we include $I$  the inlined predicates with conjunction operator.

```rust
fn fac(n: i32) -> i32 { 
    // { n >= 0 }
    let mut i = n;
    // { i >= 0 & i = n } 
    let mut r = 1;
    // { i >= 0 & i! * r = n! }
    while i > 0 {
        r = r * i;
        i = i - 1;
    }
    // { i = 0 & i! * r = n!}
    r
}
```

We could verify the predicate before the while loop remains valid with the inclusion of $I$.

$$
i \ge 0 \wedge i! * r = n!  \iff i \ge 0 \wedge i = n \wedge r = 1 
$$

because $I$ on the LHS can be simplied to $n! * 1 = n!$ which is $True$.

Similarly we could verify the predicate after the while loop 

$$
i = 0 \wedge i! * r = n! \iff i = 0 \wedge r = n!
$$

All is good, let's consider the predicate annotations inside the while loop body. 


```rust
fn fac(n: i32) -> i32 { 
    // { n >= 0 }
    let mut i = n;
    // { i >= 0 & i = n } 
    let mut r = 1;
    // { i >= 0 & i! * r = n! }
    while i > 0 {
        // P1: { i > 0 & i! * r = n! }           
        r = r * i;
        // P2: { i > 0 & (i-1)! * r = n! }   
        i = i - 1;
        // P3: { i >= 0 & i! * r = n! }
    }
    // { i = 0 & i! * r = n!}
    r
}
```

We examine them one by one:

* in `P1`, i.e. the predicate before the statement `r = r * i`, we find that besides $I$, $ i > 0 $ must hold too, because if $i \le 0$ we would have exited the loop.
* In `P2`, i.e. the predicate after the stqatement `r = r * i`. we re-assign `r` to be `r * i`. To visualize how this affect the predicate, we start from the `P1`. 
    $$
    \begin{array}{rl}
        i > 0 \wedge i! * r = n! & \iff  \\ 
        i > 0 \wedge (i-1)! * i * r = n! & \iff  \\ 
        i > 0 \wedge (i-1)! * (r * i) = n! & \
    \end{array}
    $$

    Now after reassignment, the (updated) `r` is the (old) `r` times `i`, hence the final predicate in the above is just `P2`, namely
    $$
        i > 0 \wedge (i-1)! * r = n! 
    $$
* In `P3`, i.e. the predicate after `i = i - 1`, we re-assign `i` to `i-1`. we start from `P2`, rewrite it as 

    $$
        (i-1) + 1 > 0 \wedge (i-1)! * r = n! 
    $$

    and replace all the `i-1` by `i`, hence we have
    
    $$
    \begin{array}{rl}
        i+1 > 0 \wedge i! * r = n! & \iff  \\ 
        i \ge 0 \wedge i! * r = n!  
    \end{array}
    $$
    which is `P3`.


So we have a fully annotated `fac` program and we argue that the `fac` program is behaving as what we claimed.

> Question: Is the above annotations verify the full correctness or the partial correctness of the given claim? Think about a situation in which the while loop condition is an equality instead of inequality. 


We want to have a formal way to test whether the above program annotation is correct.
Pursuing this leads us to the Hoare Logic. 

## Hoare Logic 

Hoare Logic (proposed by Tony Hoare in 1970s) become popular in the Computer Science community in the context of software formal verification. 

Hoare Logic is an extension to first order logic with some special predicate and rules meant for proving program correctness.


### Hoare Triple

In Hoare logic, we introduce a new "built-in" predicate $hoare(\_,\_,\_)$ which expect three arguments, $P$ the precondition predicate, $s$ the program (statement) and $Q$ the postcondition predicate. For convenience, we write $\{P\} s \{Q\}$ instead of $hoare(P,s,Q)$.

$s$ refers to a Rust program statement. For simplicity, we restrict ourselves to a subset of the Rust program statements.

$$
\begin{array}{rrcl}
    \texttt{(Statement)} & s & ::= & \texttt{skip} \mid s;s \mid x = e \mid \texttt{if}\ e\ \texttt{then}\ s \ \texttt{else}\ s \mid \texttt{while}\ e\ s  \mid \texttt{return}\ e  \\ 
    \texttt{(Expression)} & e & ::= & c \mid x \mid e\ op\ e \\ 
    \texttt{(Constant)} & c & ::= & \texttt{True} \mid \texttt{False} \mid 0 \mid 1 \mid ...  \\ 
    \texttt{(Operator)} & op & ::= & + \mid - \mid * \mid / \mid \  = \  \mid ...  \\ 
    \texttt{(Prog Variable)} & x & ::= & {\tt n} \mid {\tt r} \mid {\tt i} \mid {\tt j} \mid ...  \\ 
\end{array}
$$

where $\texttt{skip}$ denotes a no-op statement, e.g. `{}` in Rust and `pass` in Python. $s_1;s_2$ denote statement sequence. We use ${\tt if}\ ...\ {\tt then}\ ...\ {\tt else}\ ...$ instead of ${\tt if}\ ...\ \{ ... \}\ {\tt else}\ \{  ... \}$ to avoid the confusion caused by the curly brackets.

$P$ and $Q$ are predicates in first order logic with Peano system, equality predicate, of which we've introduced in the earlier lessons. In addition, we also include the set of objects called *program variables* such as the $n$, $i$ and $r$ which appears in the statement $s$. 




### Hoare Logic Rules

Hoare Logic operates with the following set of deduction rules. 


##### Skip Rule

$$
\{P\} {\tt skip} \{P\} 
$$

This says that the no-op statement should not change the state of the program execution

##### Assign Rule 

$$
\{[e/x]P\} x = e \{P\} 
$$

$[e/x]P$ denotes a substitution. Informally, it creates a new predicate by replacing all occurences of $x$ in $P$ by $e$.

The assign rule states that, if the program state is modelled by $[e/x]P$ where $x$ has not been assigned with $e$ (thus we replace $x$ with its assigned value $e$), then after the assignment the program state should satisfies $P$. For instance, we can refer to earlier example, 

```rust
// P1: { i > 0 & i! * r = n! }           
r = r * i;
// P2: { i > 0 & (i-1)! * r = n! }   
```
`P1` holds iff  `[(r * i)/r]P2` holds.


##### Seq Rule 

$$
\begin{array}{c} 
\{P\} s_1 \{R\} \\  
\{R\} s_2 \{Q\} \\  
\hline
\{P\} s_1; s_2 \{Q\} 
\end{array}
$$

The seq rule states that the program states are propogated through sequence of statements.


##### If Rule

$$
\begin{array}{c}
\{ P \wedge e \} s_1 \{ Q \} \\
\{ P \wedge \neg e \} s_2 \{Q \}  \\
\hline 
\{P\} {\tt if}\ e \ {\tt then}\ s_1\ {\tt else} \ s_2 \{Q\}
\end{array}
$$

The if rule states that if under precondition $P \wedge e$, $s_1$ gives us postcondition $Q$ and under precondition $P \wedge \neg e$, $s_2$ gives us the postcondition $Q$, then the enire if-else statement give us postcondition $Q$ under precondition $P$.

##### While Rule 

$$
\begin{array}{c}
\{ P \wedge e \} s \{ P \} \\
\hline 
\{P\} {\tt while}\ e \ s \{P \wedge \neg e \}
\end{array}
$$

The while rule states that $P$ must be some invariant that holds before and afte the while loop.
When inside while loop, we add the loop condition $e$ to the precondition. After the while loop, $\neg e$ must hold besides $P$.


##### Consequence Rule 

$$
\begin{array}{c}
P \implies P' \\ 
\{ P' \} s \{ Q' \} \\
Q' \implies Q \\ 
\hline 
\{P\} s \{ Q \}
\end{array}
$$

The conseuqence rule says, that we can strengthen the precondition and weaken the postcondition of the Hoare Triple.

##### Verifying `add_one`


For example, we can verify  the `add_one`'s annotation 
```rust
fn add_one( n : i32) -> i32 { 
    // { n == n }
    let mut r = n;
    // { r == n } 
    r = r + 1;
    // { r == n + 1 }
    r
}
```

by applying the Hoare Logic rules 

$$
\begin{array}{|l|r|l|}
\hline 
1. & \{ n = n \} {\tt r = n } \{ r = n \} & Assign \\ 
2.1. & \{ r + 1 = n + 1 \} {\tt r = r + 1 } \{ r = n + 1\} & Assign \\
2. & \{ r = n \} {\tt r = r + 1 } \{ r = n + 1\} & Consequence\ 2.1 \\
  & \{ n = n \} {\tt r = n; r = r + 1 } \{ r = n + 1 \} & Seq\ 1\ and\ 2 \\ \hline
\end{array}
$$

##### Verifying `fac`

We verify the `fac` annotation from Example 2, reproduced below.

```rust

fn fac(n: i32) -> i32 { 
    // { n >= 0 }
    let mut i = n;
    // { i >= 0 & i = n } 
    let mut r = 1;
    // { i >= 0 & i! * r = n! }
    while i > 0 {
        // P1: { i > 0 & i! * r = n! }           
        r = r * i;
        // P2: { i > 0 & (i-1)! * r = n! }   
        i = i - 1;
        // P3: { i >= 0 & i! * r = n! }
    }
    // { i = 0 & i! * r = n!}
    r
}
```

Overall, step 1 proves the hoare triple of the first assignmnet statement, while step 2 proves the haore triple of the 2nd statment. step 3 handles the while loop.

$$
\begin{array}{|l|r|l|}
\hline 
1.1. & \{ n \ge 0 \wedge n = n \}                 {\tt i = n } \{ i \ge 0 \wedge i = n \}              & Assign  \\ 
1. & \{ n \ge 0 \}                 {\tt i = n } \{ i \ge 0 \wedge i = n \}              & Consequence\ 1.1 \\ 
2.1. & \{ i \ge 0 \wedge i = n \}              {\tt r = 1 } \{ i \ge 0  \wedge r = 1 \wedge i = n \} &  Assign \\ 
2. & \{ i \ge 0 \wedge i = n \}                {\tt r = 1 } \{ i \ge 0  \wedge i! * r = n! \} & Consequence\ 2.1 \\ \\ 

3.1.1.1.1. & \{ i > 0 \wedge (i-1)! * i * r = n! \} {\tt r = r * i } \{ i > 0 \wedge (i-1)! * r = n! \} & Assign \\
3.1.1.1. & \{ i > 0 \wedge i! * r = n! \} {\tt r = r * i } \{ i > 0 \wedge (i-1)! * r = n! \} & Consequence\ 3.1.1.1.1 \\
3.1.1.2.1. & \{ i-1 \ge 0 \wedge (i-1)! * r = n! \} {\tt i = i - 1 } \{ i \ge 0 \wedge i! * r = n! \} & Assign \\
3.1.1.2. & \{ i > 0 \wedge (i-1)! * r = n! \} {\tt i = i - 1 } \{ i \ge 0 \wedge i! * r = n! \} & Consequence\ 3.1.1.2.1 \\
3.1.1 & \{ i > 0 \wedge i! * r = n! \} {\tt r = r * i;\ i = i - 1 } \{ i \ge 0 \wedge i! * r = n! \} & Seq\ 3.1.1.1\ and\ 3.1.1.2 \\
3.1 & \{ I \} {\tt while}\ i > 0\ \{ ... \} \{ I \wedge \neg(i > 0) \} & While\ 3.1.1 \\
3. & \{ i \ge 0  \wedge i! * r = n!  \} {\tt while}\ i > 0\ \{ ... \} \{ i = 0 \wedge i! * r = n! \} & Consequence\ 3.1 \\ \\ 

  & \{ n \ge 0  \} {\tt i = n;\ r = 1;\ while\ ... } \{ i = 0 \wedge i! * r = n! \} & Seq\ 1,\ 2\ and\ 3 \\ \hline
\end{array}
$$

A few remarks on the non-obvious steps.

* In `3.1.1.1.1`, the assign rule uses the substitution $[(r * i)/r]$ on the postcondition $i > 0 \wedge (i-1)! * r = n!$, yielding the precondition $i > 0 \wedge (i-1)! * (r * i) = n!$. Step `3.1.1.1` strengthens this precondition to $P1$, which is justified by $i! = i * (i-1)!$. This is exactly the reasoning in Example 2.
* In `3.1.1.2.1`, the assign rule uses the substitution $[(i-1)/i]$ on the postcondition $J$, yielding the precondition $i-1 \ge 0 \wedge (i-1)! * r = n!$. Step `3.1.1.2` strengthens it to $P2$, which is justified since $i > 0$ implies $i - 1 \ge 0$ for integers. This produces $P3$.
* Step `3.1.1` uses the seq rule on `3.1.1.1` and `3.1.1.2` to show that one full iteration maps the precondition $i > 0 \wedge I$ to the postcondition $J$; in particular it preserves $I$.
* In `3.1` the while rule gives the postcondition $I \wedge \neg(i > 0)$.
* Step `3` applies the consequence rule to `3.1`. The precondition is the invariant $I$, and the postcondition $I \wedge \neg(i > 0)$ implies the annotated postcondition $i = 0 \wedge r = n! \wedge I$ because $i \le 0$ together with the fact that $i!$ is defined only for non-negative integers forces $i = 0$.

Finally, since $i = 0 \wedge i! * r = n!$ entails $r = n!$, the consequence rule gives the desired claim that the returned value `r` equals `n!` whenever `fac(n)` terminates.

### Hoare Logic is Sound

 Hoare Logic rules defined earlier are sound. 
 i.e. let $s$ be a terminating program such that $\{P\} s \{Q\}$ is provable, then then $P$ and $Q$ are the legal precondition and postcondition of $s$ w.r.t. to the run-time, 
 
> For those who have studied formal semantics: Let $\Delta$ and $\Delta'$ be the program run-time states (variables to values mappings). Then we have $\{P\} s \{Q\} \wedge (\Delta, s) \longrightarrow^* \Delta' \implies \Delta \vdash P \wedge \Delta' \vdash Q$. We write $\Delta \vdash P$ to denote that under the variable to value mapping $\Delta$, $P$ is valid. 

### Hoare Logic is not Complete

Hoare Logic rules is not complete, i.e. there might be valid program precondition / postcondition that can't be proven using the Hoare Logic rules, thanks to the consequence rule and Godel's theorem of incompleteness.


## Weakest Precondition 

One issue with Hoare Logic is that it only checks whether a given set of annotations and the program is valid. It does not infer / construct the annotations. 

One way to infer the annotations given the postcondition and loop invariants is the *weakest liberal precondition* (WLP). For a statement $s$ and a postcondition $Q$, the WLP $wlp(s, Q)$ is the weakest predicate $P$ such that the Hoare triple $\{P\} s \{Q\}$ is valid under partial correctness. "Weakest" means that if any other predicate $P'$ satisfies $\{P'\} s \{Q\}$, then $P' \implies wlp(s, Q)$. "Liberal" means we do not require termination.

The WLP is computed by walking backward through the program. For each kind of statement we have a rule:

$$
\begin{array}{|l|l|}
\hline
s & wlp(s, Q) \\
\hline
\texttt{skip} & Q \\
x = e & Q[e/x] \\
s_1; s_2 & wlp(s_1, wlp(s_2, Q)) \\
\texttt{if}\ e\ \texttt{then}\ s_1\ \texttt{else}\ s_2 & (e \implies wlp(s_1, Q)) \wedge (\neg e \implies wlp(s_2, Q)) \\
\texttt{while}\ e\ \texttt{inv}\ I\ \texttt{do}\ s & I \wedge (I \wedge e \implies wlp(s, I)) \wedge (I \wedge \neg e \implies Q) \\
\hline
\end{array}
$$

The assignment rule is the same backward substitution we used in the assign rule of Hoare Logic. The sequencing rule says: to find the precondition that makes $s_1; s_2$ end in $Q$, first find the precondition for $s_2$ to end in $Q$, then find the precondition for $s_1$ to end in that.

For a loop, we must supply an invariant $I$. The WLP then checks three things:

1. $I$ holds before the loop starts.
2. $I$ is preserved by one iteration of the body.
3. When the loop exits, $I$ together with the negated guard implies the desired postcondition.

### Example: computing WLP for `fac`

Suppose we want to verify that `fac(n)` returns `n!`. The desired postcondition for the whole function is $Q = r = n!$. We walk backward statement by statement.


**1. Return.** The last statement is `return r`. Its precondition is exactly the postcondition $Q$:

$$
wlp({\tt return}\ r, Q) = r = n!
$$

**2. While loop.** Before the return we have the `while` loop. We supply the invariant $I \equiv i \ge 0 \wedge i! * r = n!$ and apply the WLP rule for loops:

$$
wlp({\tt while}\ i>0\ {\tt inv}\ I\ {\tt do}\ s, Q) = I \wedge (I \wedge i>0 \implies wlp(s, I)) \wedge (I \wedge i \le 0 \implies Q)
$$

Let us check each conjunct.

*   *Exit conjunct.* $I \wedge i \le 0$ implies $Q = r = n!$: since $I$ already contains $i \ge 0$, combining $i \ge 0$ with $i \le 0$ gives $i = 0$, and then $0! * r = n!$ gives $r = n!$.

*   *Preservation conjunct.* We must show $I \wedge i > 0 \implies wlp(s, I)$, where $s$ is the loop body `r = i * r; i = i - 1`. Compute the WLP of the body from the inside out:

    $$
    \begin{array}{rcl}
    wlp(i = i - 1, I) & = & I[(i-1)/i] \\
    & = & (i-1) \ge 0 \wedge (i-1)! * r = n! \\
    wlp(r = i * r, (i-1) \ge 0 \wedge (i-1)! * r = n!) & = & (i-1) \ge 0 \wedge (i-1)! * (i * r) = n! \\
    & \iff & (i-1) \ge 0 \wedge i! * r = n!
    \end{array}
    $$

    So $wlp(s, I) = (i-1) \ge 0 \wedge i! * r = n!$. The preservation conjunct therefore becomes $I \wedge i > 0 \implies (i-1) \ge 0 \wedge i! * r = n!$, which holds because $i > 0$ implies $i - 1 \ge 0$ for integers, and $I$ already gives $i! * r = n!$.

Since the exit and preservation conjuncts hold, the WLP of the whole loop is just $I$.




**3. Assignment `r = 1`.** Continuing backward:

$$
\begin{array}{rcl}
wlp(r = 1, I) & = & I[1/r] \\
& = & i \ge 0 \wedge i! * 1 = n!
\end{array}
$$

**4. Assignment `i = n`.** Finally:

$$
\begin{array}{rcl}
wlp(i = n, i \ge 0 \wedge i! * 1 = n!) & = & n \ge 0 \wedge n! * 1 = n! \\
& \iff & n \ge 0
\end{array}
$$

Thus the weakest precondition of the whole function body with respect to $Q = r = n!$ is $n \ge 0$, exactly the precondition we started with.


The generated annotations are as follows.
```rust
// backward 
fn fac(n: i32) -> i32 { 
    // { n >= 0 }
    let mut i = n;
    // { i >= 0 & i! * 1 = n! }
    let mut r = 1;
    // { I: i >= 0 & i! * r = n! }
    while i > 0 {
        // { (i-1) >= 0 & (i-1)! * i * r = n! }
        r = i * r;
        // { (i-1) >= 0 & (i-1)! * r = n! }
        i = i - 1; 
        // { i >= 0 & i! * r = n! }
    } 
    // { i = 0 & i! * r = n! }
    r 
}
```

### Strongest Postcondition

The *strongest postcondition* (SP) is the forward companion to WLP. For a statement $s$ and a precondition $P$, the SP $sp(s, P)$ is the strongest predicate $Q$ such that the Hoare triple $\{P\} s \{Q\}$ is valid under partial correctness. "Strongest" means that if $\{P\} s \{Q'\}$ is valid for any other $Q'$, then $sp(s, P) \implies Q'$. SP is computed by walking forward through the program.

$$
\begin{array}{|l|l|}
\hline
s & sp(s, P) \\
\hline
\texttt{skip} & P \\
x = e & \exists x'.\ x = e[x'/x] \wedge P[x'/x] \\
s_1; s_2 & sp(s_2, sp(s_1, P)) \\
\texttt{if}\ e\ \texttt{then}\ s_1\ \texttt{else}\ s_2 & (e \wedge sp(s_1, P \wedge e)) \vee (\neg e \wedge sp(s_2, P \wedge \neg e)) \\
\texttt{while}\ e\ \texttt{inv}\ I\ \texttt{do}\ s & I \wedge \neg e \\
\hline
\end{array}
$$

The assignment rule uses a fresh variable $x'$ to hold the old value of $x$, then existentially quantifies it away. For deterministic assignments this can always be eliminated by substituting the value that $x$ had before the assignment.

For a loop, we again supply an invariant $I$ and check three conditions:

1. **Initiation.** $P \implies I$.
2. **Preservation.** $I \wedge e \implies sp(s, I \wedge e)$ and $sp(s, I \wedge e) \implies I$.
3. **Exit.** $I \wedge \neg e \implies Q$, where $Q$ is the desired postcondition.

When these hold, the strongest postcondition produced by the loop is $I \wedge \neg e$.

### Example: computing SP for `fac`

Suppose `fac(n)` starts with precondition $P = n \ge 0$ and we want the postcondition $Q = r = n!$. We walk forward statement by statement.

```rust
// forward 
fn fac(n: i32) -> i32 { 
    // { n >= 0 }
    let mut i = n;
    // { i >= 0 & i = n }
    let mut r = 1;
    // { i >= 0 & r = 1 & i = n }
    while i > 0 {
        // { I: i >= 0 & i! * r = n! }   // loop invariant
        r = i * r;
        // { i > 0 & (i-1)! * r = n! }
        i = i - 1; 
        // { i >= 0 & i! * r = n! }
    } 
    // { i = 0 & i! * r = n! }
    r 
}
```

**1. Assignment `i = n`.**

$$
\begin{array}{rcl}
sp(i = n, n \ge 0) & = & \exists i'.\ i = n \wedge n \ge 0 \\
& \iff & i \ge 0 \wedge i = n
\end{array}
$$

**2. Assignment `r = 1`.**

$$
\begin{array}{rcl}
sp(r = 1, i \ge 0 \wedge i = n) & = & \exists r'.\ r = 1 \wedge i \ge 0 \wedge i = n \\
& \iff & i \ge 0 \wedge r = 1 \wedge i = n
\end{array}
$$

**3. While loop.** We supply the invariant $I \equiv i \ge 0 \wedge i! * r = n!$.

*   *Initiation.* $i \ge 0 \wedge r = 1 \wedge i = n$ implies $i! * r = i! * 1 = i! = n!$ (using $i = n$), together with $i \ge 0$, which is exactly $I$.

*   *Preservation.* We compute the strongest postcondition of the loop body starting from $I \wedge i > 0$:

    $$
    \begin{array}{rcl}
    sp(r = i * r, I \wedge i > 0) & = & \exists r'.\ r = i * r' \wedge i \ge 0 \wedge i! * r' = n! \wedge i > 0 \\
    & \iff & i > 0 \wedge (i-1)! * r = n! \\
    sp(i = i - 1, i > 0 \wedge (i-1)! * r = n!) & = & \exists i'.\ i = i' - 1 \wedge i' > 0 \wedge (i'-1)! * r = n! \\
    & \iff & i \ge 0 \wedge i! * r = n! \\
    & = & I
    \end{array}
    $$

    The result is exactly $I$, so preservation holds.

*   *Exit.* $I \wedge \neg(i > 0) = I \wedge i \le 0 = i \ge 0 \wedge i! * r = n! \wedge i \le 0$. Since $i \ge 0$ and $i \le 0$ force $i = 0$, and then $0! * r = n!$ gives $r = n!$.

Therefore:

$$
sp({\tt while}\ i > 0\ {\tt inv}\ I\ {\tt do}\ s,\ i \ge 0 \wedge r = 1 \wedge i = n) = I \wedge \neg(i > 0) = i = 0 \wedge r = n!
$$

**4. Return.** The final statement returns `r`, and the postcondition is already $r = n!$.

Thus the strongest postcondition of the whole function body with respect to $P = n \ge 0$ is $sp({\tt fac\ body}, n \ge 0) = r = n!$, which is exactly the desired postcondition $Q$.

### WLP versus Hoare Logic

Hoare Logic lets us check a complete set of annotations. WLP lets us *generate* those annotations systematically, provided we know the loop invariants. For loops, the invariant is still an input supplied by the programmer or verifier; WLP does not magically discover it. Once the invariants are fixed, however, the remaining annotations for straight-line code, conditionals, and the loop body are obtained mechanically by applying the WLP rules.


### Modeling Heap State

Modern programming languages allow us to create data structures and put them in the Heap memory space. 
To verify program's correctness with heap memory store. An extension to Hoare Logic is needed, called *Seperation Logic*. Interested learner can find the refernces 

* https://softwarefoundations.cis.upenn.edu/slf-1.1/toc.html
* https://www.comp.nus.edu.sg/~cs6202/slides/08-seplogic.pdf

### Proof-Carrying Code

A related idea is *proof-carrying code* (PCC), introduced by Necula and Lee. Instead of verifying the source code once and discarding the proof, the program is shipped together with a machine-checkable proof of a desired property (for example, memory safety or partial correctness). A consumer can then check the proof efficiently instead of redoing the full verification from scratch. This is especially attractive when the producer is trusted less than the consumer, or when verification is expensive but proof checking is cheap.

Modern program-verification tools follow a similar spirit. For example, [Dafny](https://dafny.org/) is a programming language with a built-in verifier: the programmer writes specifications and loop invariants, and Dafny generates proof obligations that are discharged by an automated solver. In the PCC terminology, those discharged obligations play the role of the proof certificate checked by the consumer.


## Further Readings


https://www.cl.cam.ac.uk/teaching/1718/HLog+ModC/slides/lecture4-updated.pdf
https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture09.pdf
https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture10.pdf
https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture11.pdf
https://www.cs.cornell.edu/courses/cs4110/2018fa/lectures/lecture12.pdf
https://www.cs.utexas.edu/~EWD/ewd04xx/EWD472.PDF