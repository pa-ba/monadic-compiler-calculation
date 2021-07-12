# Monadic Compiler Calculation

This repository contains the supplementary material for the paper
*Monadic Compiler Calculation* by Patrick Bahr and Graham Hutton. The
material includes Agda formalisations of all calculations in the
paper. In addition, we also include Agda formalisations for
calculations that were mentioned but not explicitly carried out in the
paper.

To typecheck all Agda files, use the included makefile by simply
invoking `make` in this directory. All source files in this directory
have been typechecked using version 2.6.1.3 of Agda and version 1.6 of
the Agda standard library.


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
- [Lambda.agda](Lambda.agda): Lambda calculus (section 3);
  [LambdaTerminating.agda](LambdaTerminating.agda) proves that `exec`
  is terminating.
- [Interrupts.agda](Interrupts.agda): Interrupts language (section 4)

## Additional compiler calculations 

- [While.agda](While.agda): Simple arithmetic language with a while
  loop.
- [LambdaException.agda](LambdaException.agda): Lambda calculus with
  exceptions and exception handling.
- [InterruptsLoop.agda](InterruptsLoop.agda): Interrupts language
  extended with a degenerate loop primitive; uses the `PND` monad.
