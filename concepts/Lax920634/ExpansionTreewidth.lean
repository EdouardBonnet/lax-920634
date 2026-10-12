import Lax920634.EdgeExpansion
import Lax228581.Treewidth

/-!
---
title: Edge Expansion Forces Linear Treewidth
type: theorem
---
For a positive integer $d$, every finite subcubic graph with edge expansion
at least $1/(8d)$ satisfies
$|V|\le(24d+1)(\operatorname{tw}(G)+1)$.

If every component after deleting $X$ has size at most $|V|/2$, summing the
expansion inequalities over components gives
$|V\setminus X|\le24d|X|$. Thus a smaller deletion leaves a component
containing more than half the graph. These large connected sets form a
bramble. A bag of every tree decomposition hits the bramble, giving the bound.

# Formalization notes

Treewidth is the registered definition from `Lax228581.Treewidth`.
The additive one is necessary for graphs of treewidth zero. Empty graphs
are included. Natural-number multiplication avoids rounding conventions.
-/

namespace Lax920634.ExpansionTreewidth

/-- Uniform expansion in a subcubic graph gives a linear lower bound on treewidth. -/
axiom order_le_treewidth {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) (hd : 0 < d)
    (hdegree : EdgeExpansion.IsSubcubic G)
    (hex : EdgeExpansion.HasEdgeExpansionAtLeast G (1 / (8 * (d : ℚ)))) :
  n ≤ (24 * d + 1) * (Lax228581.Treewidth.treewidth G + 1)

end Lax920634.ExpansionTreewidth
