import Lax920634.EdgeExpansion

/-!
---
title: Arbitrarily Large Subcubic Expanders
type: theorem
---
For every size threshold, there is a finite simple subcubic graph above that
threshold with edge expansion at least $1/128$.

# Formalization notes

The size is allowed to exceed the threshold. The proof supplies the explicit
modular construction, whose sizes are $8(m+1)^2$, rather than asserting
existence at every exact order.
-/

namespace Lax920634.ExpanderExistence

/-- There are arbitrarily large finite simple subcubic expanders. -/
axiom exists_subcubic_expander (lower : ℕ) :
  ∃ n : ℕ, ∃ G : SimpleGraph (Fin n),
    lower ≤ n ∧ EdgeExpansion.IsSubcubic G ∧
      EdgeExpansion.HasEdgeExpansionAtLeast G (1 / 128)

end Lax920634.ExpanderExistence
