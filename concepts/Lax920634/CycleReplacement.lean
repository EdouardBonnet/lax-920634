import Lax920634.EdgeExpansion

/-!
---
title: Eight-Cycle Replacement
type: definition
---
An eight-regular undirected multigraph can be described by an involution $R$
on its ports $(i,v)\in\{0,\ldots,7\}\times V$: applying $R$ crosses an edge
and identifies its port at the other endpoint. Replace every vertex by an
eight-cycle, and join each port $p$ to $R(p)$.

# Formalization notes

The graph definition accepts arbitrary port maps. Its useful properties are
proved under the involution hypothesis. `SimpleGraph.fromRel` takes the
undirected closure and removes loops. The port condition $R(i,v)_1=i+4$
makes the matching edges distinct from cycle edges, even for base loops.
The separate base-cut definition retains multiplicity of the base edges.
-/

namespace Lax920634.CycleReplacement

/-- The next port in the cyclic order. -/
def nextPort (i : Fin 8) : Fin 8 := i + 1

/-- The previous port in the cyclic order. -/
def prevPort (i : Fin 8) : Fin 8 := i + 7

/-- The opposite port, used to pair each transformation with its inverse. -/
def oppositePort (i : Fin 8) : Fin 8 := i + 4

/-- Replace each base vertex by an eight-cycle and connect paired ports. -/
def replacementGraph {n : ℕ} (R : Fin 8 × Fin n → Fin 8 × Fin n) :
    SimpleGraph (Fin 8 × Fin n) :=
  SimpleGraph.fromRel (fun u v => v = (nextPort u.1, u.2) ∨ v = R u)

/-- Base boundary darts with source in `S` and target outside `S`. -/
def baseCut {n : ℕ} (R : Fin 8 × Fin n → Fin 8 × Fin n)
    (S : Set (Fin n)) : Set (Fin 8 × Fin n) :=
  {p | p.2 ∈ S ∧ (R p).2 ∉ S}

end Lax920634.CycleReplacement
