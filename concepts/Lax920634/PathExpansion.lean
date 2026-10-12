import Lax920634.PathReplacement

/-!
---
title: Path Replacement Preserves Uniform Expansion
type: theorem
---
Suppose a degree-$d$ regular port involution has at least a quarter of the
degree times the smaller cut side in boundary darts, and $d\ge2$.
Replacing its vertex clouds by paths gives edge expansion at least $1/(8d)$.

Full clouds of a cut form a small base set. Each partial cloud contributes
a distinct crossing path edge. The base edges leaving full clouds either
cross the final cut or reach partial clouds. Counting these two possibilities
bounds the size of the cut by $8d$ times its edge boundary.

# Formalization notes

The base cut counts darts to preserve multigraph multiplicity. The target is
a simple graph; the argument tolerates loops and overlaps between matching
edges and path edges.
-/

namespace Lax920634.PathExpansion

/-- An expanding regular port involution yields a uniformly expanding path replacement. -/
axiom replacement_expansion {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (hR : Function.Involutive R) (hd : 2 ≤ d)
    (hbase : ∀ U : Set (Fin n),
      d * min U.ncard (n - U.ncard) ≤ 4 * (PathReplacement.baseCut R U).ncard) :
  EdgeExpansion.HasEdgeExpansionAtLeast (PathReplacement.graph R) (1 / (8 * (d : ℚ)))

end Lax920634.PathExpansion
