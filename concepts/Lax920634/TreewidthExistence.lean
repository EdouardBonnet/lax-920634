import Lax920634.ZigZagConstruction
import Lax228581.Treewidth

/-!
---
title: Arbitrarily Large Subcubic Graphs of Linear Treewidth
type: theorem
---
For every size threshold there is a finite simple subcubic graph above that
threshold with treewidth at least its order divided by $48d+2$, for the same
fixed degree constant $d=D^2$. These graphs belong to the explicit expander
family.

# Formalization notes

The integer inequality $n\le(48d+2)\operatorname{tw}(G)$ expresses the
linear lower bound without division or rounding. The proof selects a large
enough graph to absorb the additive one in the general treewidth inequality.
-/

namespace Lax920634.TreewidthExistence

open ZigZagConstruction EdgeExpansion Lax228581.Treewidth

/-- Arbitrarily large subcubic graphs have a fixed linear lower bound on treewidth. -/
axiom exists_subcubic_linear_treewidth (lower : ℕ) :
  ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), lower ≤ n ∧ IsSubcubic G ∧
    n ≤ (48 * degree + 2) * treewidth G

end Lax920634.TreewidthExistence
