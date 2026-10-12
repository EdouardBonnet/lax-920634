import Lax920634.EdgeExpansion
import Lax228581.Treewidth

/-!
---
title: Edge Expansion Forces Linear Treewidth
type: theorem
---
A subcubic graph with edge expansion at least $1/128$ satisfies
$|V|\le1536(\operatorname{tw}(G)+1)$.

A tree decomposition provides a separator of size at most its largest bag,
with each component outside the separator containing at most half the
vertices. If the separator is smaller than $|V|/4$, a union of components
has size between $|V|/4$ and $|V|/2$. Expansion supplies at least
$|V|/512$ boundary edges, all incident with the separator. The degree bound
limits their number to three times its size.

# Formalization notes

Treewidth is the registered definition from `Lax228581.Treewidth`.
The additive one is required: even a one-vertex graph has treewidth zero.
The statement includes empty graphs and uses integer multiplication to avoid
rounding conventions.
-/

namespace Lax920634.ExpansionTreewidth

/-- Uniform edge expansion in a subcubic graph gives a linear treewidth bound. -/
axiom order_le_treewidth {n : ℕ} (G : SimpleGraph (Fin n))
    (hdegree : EdgeExpansion.IsSubcubic G)
    (hexpansion : EdgeExpansion.HasEdgeExpansionAtLeast G (1 / 128)) :
  n ≤ 1536 * (Lax228581.Treewidth.treewidth G + 1)

end Lax920634.ExpansionTreewidth
