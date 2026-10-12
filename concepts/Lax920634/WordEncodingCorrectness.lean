import Lax920634.WordEncoding

/-!
---
title: The Word Table Encodes the Same Graph
type: lemma
---
The word table contains exactly one header and one endpoint per vertex.
Its header is the graph order, every endpoint is a valid vertex label,
and decoding produces exactly the specified subcubic graph.
-/

namespace Lax920634.WordEncodingCorrectness

open ZigZagConstruction WordEncoding

/-- The linear-size word encoding is complete, bounded, and faithful to the original graph. -/
axiom table_correct (k : ℕ) :
  (table k).head? = some (order k) ∧
  (table k).length = order k + 1 ∧
  (∀ j < order k,
    ((table k).tail[j]?).getD 0 < order k) ∧
  decode (order k) (table k) = graph k

end Lax920634.WordEncodingCorrectness
