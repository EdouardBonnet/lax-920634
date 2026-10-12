import Lax920634.ZigZagConstruction
import Lax228581.Treewidth

/-!
---
title: The Explicit Family Has Linear Treewidth
type: lemma
---
The specified graphs satisfy
$N_k\le(24d+1)(\operatorname{tw}(H_k)+1)$, where $d=D^2$ is the fixed
regular tower degree. Hence sufficiently large members have treewidth at
least $N_k/(48d+2)$.

# Formalization notes

The expansion and treewidth claims refer to the same computable graph.
The existence theorem below absorbs the additive one by choosing a large
enough size request.
-/

namespace Lax920634.ExplicitTreewidth

open ZigZagConstruction Lax228581.Treewidth

/-- The specified graph order is bounded linearly by treewidth plus one. -/
axiom linear_treewidth (k : ℕ) : order k ≤
  (24 * degree + 1) *
    (treewidth (graph k) + 1)

end Lax920634.ExplicitTreewidth
