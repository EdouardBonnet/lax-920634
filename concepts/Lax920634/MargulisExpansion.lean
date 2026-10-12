import Lax920634.MargulisConstruction

/-!
---
title: The Modular Base Graph Expands
type: theorem
---
The Margulis–Gabber–Galil multigraph has at least $2|S|/5$ edges leaving
every set of at most half its vertices, uniformly in the positive modulus.

This is a deliberately weaker rational consequence of the classical bound
$\lambda_2\le5\sqrt2$: the spectral cut inequality gives
$|\partial S|\ge(8-5\sqrt2)|S|/2>2|S|/5$.
See Gabber and Galil (1981), and Construction 8.1 and Theorem 8.2 in
Hoory, Linial, and Wigderson (2006).

# Formalization notes

The statement counts base darts, retaining loops and parallel edges in the
underlying degree-eight graph. It is written for both sides of every cut,
using the smaller side; each crossing edge contributes exactly one dart.
-/

namespace Lax920634.MargulisExpansion

/-- Every base cut has at least two fifths as many edges as its smaller side. -/
axiom base_expansion (m : ℕ) (S : Set (Fin (MargulisConstruction.baseOrder m))) :
  2 * min S.ncard (MargulisConstruction.baseOrder m - S.ncard) ≤
    5 * (CycleReplacement.baseCut (MargulisConstruction.rotation m) S).ncard

end Lax920634.MargulisExpansion
