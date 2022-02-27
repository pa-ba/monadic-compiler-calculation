This repository contains the supplementary material for the paper
*Monadic Compiler Calculation*. The material includes Agda
formalisations of all calculations in the paper. In addition, we also
include Agda formalisations for calculations that were mentioned but
not explicitly carried out in the paper.

To typecheck all Agda files, use the included makefile by simply
invoking `make` in this directory. All source files in this directory
have been typechecked using version 2.6.3 of Agda and version 1.7 of
the Agda standard library.

# Files

## Monads

- [Partial.agda](Partial.agda): Definition of the partiality monad
  `Partial` + proofs of its laws (section 2).
- [NonDeterm.agda](NonDeterm.agda): Definition of the non-determinism monad
  `ND` + proofs of its laws (section 4).
- [PartialNonDeterm.agda](PartialNonDeterm.agda): Definition of the
  `PND` monad that combines `Partial` and `ND` + proofs of its laws.

## Compiler calculations from the paper

- [Loop.agda](Loop.agda): Simple arithmetic language with a degenerate
  loop (section 2).
- [Lambda.agda](Lambda.agda): Call-by-value lambda calculus (section 3).
- [Interrupts.agda](Interrupts.agda): Interrupts language (section 4).

## Additional compiler calculations 

- [While.agda](While.agda): Simple arithmetic language with a while
  loop.
- [LambdaException.agda](LambdaException.agda): Call-by-value lambda
  calculus with exceptions and exception handling.
- [InterruptsLoop.agda](InterruptsLoop.agda): Interrupts language
  extended with a degenerate loop primitive; uses the `PND` monad.
- [LambdaCBName.agda](LambdaCBName.agda): Call-by-name lambda calculus.

## Termination arguments 

In some cases, Agda's termination checker rejects the definition of
the virtual machine `exec`. In these cases, the termination checker is
disabled for `exec` (using the `TERMINATING` pragma) and termination
is proved manually in the following modules:

- [Terminating/Lambda.agda](Terminating/Lambda.agda)
- [Terminating/Interrupts.agda](Terminating/Interrupts.agda)
- [Terminating/InterruptsLoop.agda](Terminating/InterruptsLoop.agda)
- [Terminating/LambdaException.agda](Terminating/LambdaException.agda)
- [Terminating/LambdaCBName.agda](Terminating/LambdaCBName.agda)

# Agda formalisation vs. paper proofs

In the paper, we use an idealised Haskell-like syntax for all
definitions. Here we outline how this idealised syntax is translated
into Agda.

## Sized coinductive types

In the paper, we use the `codata` syntax to distinguish coinductively
defined data types from inductive data types. In particular, we use
this for the coinductive `Partial` type:

```
codata Partial a = Now a | Later (Partial a)
```

In Agda we use coinductive record types to represent to coinductive
data types. Moreover, we use sized types to help the termination
checker to recognize productive corecursive function
definitions. Therefore, the `Partial` type has an additional parameter
of type `Size`:

```
data Partial (A : Set) (i : Size) : Set where
  now   : A → Partial A i
  later : ∞Partial A i → Partial A i

record ∞Partial (A : Set) (i : Size) : Set where
  coinductive
  constructor delay
  field
    force : {j : Size< i} → Partial A j
```
## Mutual inductive and co-inductive definitions

The semantic functions `eval` and `exec` are well-defined because
recursive calls take smaller arguments (either structurally or
according to some measure), or are guarded by `Later`. For example, in
the case of the Loop lanugage, `eval` is applied to the structurally
smaller `x` and `y` in the case of `Add` or is guarded by `Later` in
the case for `Loop`:

```
eval :: Expr -> Partial Int
eval (Val n)   = return n
eval (Add x y) = do m <- eval x
                    n <- eval y
                    return (m+n)
eval Loop      = Later (eval Loop)
```

This translates to two mutually recursive functions in Agda, one for
recursive calls (applied to smaller arguments) and one for
co-recursive calls (guarded by `Later`). We use the prefix `∞` to
distinguish the co-recursive function from the recursive function. For
example, for the Loop language we write an `eval` and an `∞eval`
function:

```
mutual
  eval : ∀ {i} → Expr → Partial ℕ i
  eval (Val x) = return x
  eval (Add x y) =
    do n ← eval x
       m ← eval y
       return (n + m)
  eval Loop = later (∞eval Loop)

  ∞eval : ∀ {i} → Expr → ∞Partial ℕ i
  force (∞eval x) = eval x
```

## Do notation pattern matching

Agda supports pattern matching syntax in do notation similarly to
Idris. For example, the syntax from the paper

```
eval' (Add x y) i = do Just m ← eval x i  | return Nothing
                       Just n ← eval y i  | return Nothing
                       return (Just (m + n))
```

can be translated to:

```
eval' (Add x y) i = do just m ← eval x i  where _ → return nothing
                       just n ← eval y i  where _ → return nothing
                       return (just (m + n))
```

However, using this syntax is inappropriate since the pattern matching
clauses are translated into fresh anonymous functions internally. This
has the undesireable effect that syntactically identical terms cannot
be proved equal. For example, we cannot prove the following equality:
```
(do just n ← eval x i  where _ → return nothing
    return (just n+1))
==
(do just n ← eval x i  where _ → return nothing
    return (just n+1))
```

Therefore, we use helper functions that encode the desired pattern
matching. For example, the abovementioned code from the paper is
translated into the following Agda code.
```
eval' (Add x y) i  =
   eval x i >>= getJust (return nothing) λ m →
   eval y i >>= getJust (return nothing) λ n →
   return (just (m + n))
```

Similarly, instead of partial pattern matching as in
```
eval (Add x y) e = do Num m <- eval x e
                      Num n <- eval y e
                      return (Num (m + n))
```

we use auxiliary function that performs the pattern matching:

```
eval (Add x y) e =
  do n ← eval x e >>= getNum
     m ← eval y e >>= getNum
     return (Num (n + m))
```
