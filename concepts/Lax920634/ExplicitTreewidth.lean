import Lax920634.MargulisConstruction
import Lax228581.Treewidth

/-!
---
title: The Explicit Family Has Linear Treewidth
type: theorem
---
Every member of the modular family satisfies
$8(m+1)^2\le1536(\operatorname{tw}(H_m)+1)$.
Consequently, when $m\ge19$, its treewidth is at least its order divided
by $3072$.

# Formalization notes

This statement applies to exactly the graph appearing in the expansion
statement. The eventual lower bound without an additive term is used in the
separate existence theorem.
-/

namespace Lax920634.ExplicitTreewidth

/-- The explicit family's order is linearly bounded by its treewidth plus one. -/
axiom linear_treewidth (m : ℕ) :
  MargulisConstruction.order m ≤
    1536 * (Lax228581.Treewidth.treewidth (MargulisConstruction.graph m) + 1)

end Lax920634.ExplicitTreewidth
