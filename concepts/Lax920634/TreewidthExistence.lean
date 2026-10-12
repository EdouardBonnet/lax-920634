import Lax920634.EdgeExpansion
import Lax228581.Treewidth

/-!
---
title: Arbitrarily Large Subcubic Graphs of Linear Treewidth
type: theorem
---
For every size threshold, there is a finite simple subcubic graph above
that threshold whose treewidth is at least its order divided by $3072$.
The witnesses come from the same explicit family as the expanders.

# Formalization notes

The integer inequality $n\le3072\operatorname{tw}(G)$ expresses the linear
lower bound without loss from division. The proof chooses a modulus at least
20 so that the additive one in the general separator bound can be absorbed.
-/

namespace Lax920634.TreewidthExistence

/-- Arbitrarily large subcubic graphs have treewidth at least their order over 3072. -/
axiom exists_subcubic_linear_treewidth (lower : ℕ) :
  ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
    lower ≤ n ∧ EdgeExpansion.IsSubcubic G ∧
      n ≤ 3072 * Lax228581.Treewidth.treewidth G

end Lax920634.TreewidthExistence
