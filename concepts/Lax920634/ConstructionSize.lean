import Lax920634.GraphEncoding

/-!
---
title: The Constructor Meets the Requested Order
type: lemma
---
For every requested order $n$, the selector produces a graph with at least
$n$ vertices and at most $2dD^4(n+1)$ vertices. Thus the polynomial-time
algorithm constructs arbitrarily large graphs with only a fixed-factor
overshoot. Here $D=120^{5760000}$ and $d=D^2$ are fixed.

# Formalization notes

Both bounds concern the exact level used by the binary table constructor.
-/

namespace Lax920634.ConstructionSize

open ZigZagConstruction GraphEncoding SeedSearch

/-- The specified size selector meets the request with a fixed linear upper bound. -/
axiom size_bounds (n : ℕ) :
  n ≤ order (selectedLevel n) ∧
  order (selectedLevel n) ≤
    (2 * degree * seedDegree ^ 4) * (n + 1)

end Lax920634.ConstructionSize
