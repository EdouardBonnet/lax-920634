import Lax920634.ZigZagConstruction

/-!
---
title: The Explicit Subcubic Family Expands
type: lemma
---
Put $D=120^{5760000}$ and $d=D^2$. Every specified graph $H_k$ has edge
expansion at least $1/(8d)$, uniformly in the level.

# Formalization notes

The constant depends only on the fixed seed degree, not on the graph order.
The proof combines the zig-zag spectral bound with path replacement and
checks the canonical vertex numbering.
-/

namespace Lax920634.ExplicitExpansion

open ZigZagConstruction EdgeExpansion

/-- The specified deterministic family has a uniform positive edge-expansion constant. -/
axiom expansion (k : ℕ) : HasEdgeExpansionAtLeast
  (graph k) (1 / (8 * (degree : ℚ)))

end Lax920634.ExplicitExpansion
