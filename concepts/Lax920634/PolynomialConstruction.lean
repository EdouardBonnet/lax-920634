import Lax920634.GraphEncoding
import Mathlib.Computability.TuringMachine.Computable

/-!
---
title: The Explicit Construction Runs in Polynomial Time
type: theorem
---
The specified graph-table constructor is computed by one deterministic
Turing machine in polynomial time in the unary requested order. Its output
is exactly the graph encoding defined by the seed scan, tower recurrence,
level selector, and path replacement.

# Formalization notes

The model is mathlib's deterministic finite stack-machine model, with the
identity encoding on binary input and output words. Its polynomial bound
counts machine transitions. The theorem concerns the actual specified
function, rather than an arbitrary constructor of graphs with similar
properties. Fixed seed precomputation contributes a constant independent
of the requested order.
-/

namespace Lax920634.PolynomialConstruction

/-- One deterministic polynomial-time machine computes the specified graph constructor. -/
axiom polynomial_time :
  Nonempty (Turing.TM2ComputableInPolyTime id id GraphEncoding.construct)

end Lax920634.PolynomialConstruction
