import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card
import Mathlib.Data.Rat.Defs

/-!
---
title: Edge Expansion and Subcubic Graphs
type: definition
---
The edge boundary of a vertex set $S$ consists of the edges with one endpoint
in $S$ and one outside. A finite graph has edge expansion at least $h$ if
$|\partial S|\ge h|S|$ whenever $|S|\le |V|/2$. A graph is subcubic if
every vertex has at most three neighbors.

# Formalization notes

Boundary edges are represented by ordered pairs with the first endpoint in
$S$ and the second outside, so each undirected boundary edge is counted once.
`Set.ncard` avoids imposing decidability on mathematical predicates; every
set counted here is finite. Expansion constants are rational numbers.
-/

namespace Lax920634.EdgeExpansion

/-- Boundary edges oriented from the set to its complement, each counted once. -/
def edgeBoundary {V : Type} (G : SimpleGraph V) (S : Set V) : Set (V × V) :=
  {e | e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2}

/-- Every vertex set of size at most half the graph has at least `h` times
its size in boundary edges. -/
def HasEdgeExpansionAtLeast {V : Type} [Fintype V]
    (G : SimpleGraph V) (h : ℚ) : Prop :=
  ∀ S : Set V, 2 * S.ncard ≤ Fintype.card V →
    h * (S.ncard : ℚ) ≤ ((edgeBoundary G S).ncard : ℚ)

/-- Every vertex has at most three distinct neighbors. -/
def IsSubcubic {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ v, (G.neighborSet v).ncard ≤ 3

end Lax920634.EdgeExpansion
