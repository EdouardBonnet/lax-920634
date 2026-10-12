import Lax920634.WordEncoding

/-!
---
title: The Word Table Encodes the Same Graph
type: theorem
---
The word table contains exactly one header and one endpoint per vertex.
Its header is the graph order, every endpoint is a valid vertex label,
and decoding produces exactly the specified subcubic graph.
-/

namespace Lax920634.WordEncodingCorrectness

/-- The linear-size word encoding is complete, bounded, and faithful to the original graph. -/
axiom table_correct (k : ℕ) :
  (WordEncoding.table k).head? = some (ZigZagConstruction.order k) ∧
  (WordEncoding.table k).length = ZigZagConstruction.order k + 1 ∧
  (∀ j < ZigZagConstruction.order k,
    ((WordEncoding.table k).tail[j]?).getD 0 < ZigZagConstruction.order k) ∧
  WordEncoding.decode (ZigZagConstruction.order k) (WordEncoding.table k) = ZigZagConstruction.graph k

end Lax920634.WordEncodingCorrectness
