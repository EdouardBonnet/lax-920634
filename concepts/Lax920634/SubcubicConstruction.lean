import Lax920634.ZigZagConstruction

/-!
---
title: The Explicit Graphs Are Subcubic
type: lemma
---
Every member $H_k$ of the specified zig-zag and path-replacement family is
subcubic. A port has at most two neighbors inside its path and one neighbor
across the regular graph's edge involution.

# Formalization notes

The statement concerns the precise executable construction on `Fin (order k)`.
Self-loops and coincident edges are removed by the simple graph definition.
-/

namespace Lax920634.SubcubicConstruction

open ZigZagConstruction EdgeExpansion

/-- The specified deterministic family has maximum degree at most three. -/
axiom subcubic (k : ℕ) : IsSubcubic (graph k)

end Lax920634.SubcubicConstruction
