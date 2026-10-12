import Lax920634.MargulisConstruction

/-!
---
title: The Explicit Graphs Are Subcubic
type: theorem
---
Every graph $H_m$ is subcubic. In fact the construction is cubic: its two
cycle neighbors and its opposite-port matching neighbor are distinct.
This includes modulus one.

# Formalization notes

The public statement records the degree bound needed in the two existence
theorems. Exact neighborhood formulas and the involution calculation belong
to its proof.
-/

namespace Lax920634.SubcubicConstruction

/-- Every member of the explicit family has maximum degree at most three. -/
axiom subcubic (m : ℕ) : EdgeExpansion.IsSubcubic (MargulisConstruction.graph m)

end Lax920634.SubcubicConstruction
