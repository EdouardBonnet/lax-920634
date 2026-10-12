import Lax920634.GraphEncoding

/-!
---
title: A Word-Sized Encoding of the Constructed Graphs
type: definition
---
A graph is encoded by its order followed by one matching endpoint per vertex,
in numerical vertex order. Consecutive ports in each cloud supply the path
edges. Thus the encoding has exactly one more word than the graph has
vertices. It determines the entire simple graph, including loop removal and
merging of coincident edges.

# Formalization notes

The row number determines the base vertex and port by division and remainder
by the fixed degree. This encoding uses machine words for vertex labels,
rather than unary coordinates. The requested order is supplied as one word.
-/

namespace Lax920634.WordEncoding

/-- The complete matching table, with its graph order as a header. -/
def table (k : ℕ) : List ℕ := ZigZagConstruction.order k ::
  (List.range (ZigZagConstruction.order k)).map (ZigZagConstruction.matchingNeighbor k)

/-- Construct the word encoding for the same size selector as the binary constructor. -/
def construct (n : ℕ) : List ℕ := table (GraphEncoding.selectedLevel n)

/-- Decode the matching table at its declared graph order. Path edges are determined by row numbers. -/
def decode (n : ℕ) (tape : List ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v =>
    (u.val / ZigZagConstruction.degree = v.val / ZigZagConstruction.degree ∧ u.val+1 = v.val) ∨
      v.val = (tape.tail[u.val]?).getD 0)

end Lax920634.WordEncoding
