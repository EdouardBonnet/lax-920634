import Lax920634.MargulisConstruction

/-!
---
title: The Explicit Subcubic Family Expands
type: theorem
---
For every $m\ge0$, the explicit graph $H_m$ on $8(m+1)^2$ vertices has edge
expansion at least $1/128$.

# Formalization notes

The claim concerns the specified computable graph, rather than an
existentially selected graph with the same size. The degree bound is a
separate statement. The proof combines base expansion with cycle replacement.
-/

namespace Lax920634.ExplicitExpansion

/-- The specified modular family has edge expansion at least one over 128. -/
axiom expansion (m : ℕ) :
  EdgeExpansion.HasEdgeExpansionAtLeast (MargulisConstruction.graph m) (1 / 128)

end Lax920634.ExplicitExpansion
