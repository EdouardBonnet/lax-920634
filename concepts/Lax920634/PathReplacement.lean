import Lax920634.EdgeExpansion

/-!
---
title: Path Replacement of a Regular Multigraph
type: definition
---
Replace every vertex of a degree-$d$ multigraph by a path of $d$ ports,
then join ports paired by the edge-reversing involution. Every port has at
most two path neighbors and one neighbor across an original edge. The
resulting simple graph is subcubic.

# Formalization notes

The port map need not pair distinct ports; loops and repeated edges in the
base graph are allowed. The undirected closure removes any loops and
identifies coincident edges. Base cut cardinalities count darts, preserving
the base multiplicities. Each crossing base edge has one source-side dart.
-/

namespace Lax920634.PathReplacement

/-- Replace each base vertex by a path of its ports and add the paired-port edges. -/
def graph {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d) :
    SimpleGraph (Fin n × Fin d) :=
  SimpleGraph.fromRel (fun u v =>
    (u.1 = v.1 ∧ u.2.val + 1 = v.2.val) ∨ v = R u)

/-- Base boundary darts with source in `S` and target outside `S`. -/
def baseCut {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (S : Set (Fin n)) : Set (Fin n × Fin d) :=
  {p | p.1 ∈ S ∧ (R p).1 ∉ S}

end Lax920634.PathReplacement
