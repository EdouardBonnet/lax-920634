import Lax920634Proofs.RamArithmetic
import Lax920634.WordEncodingCorrectness

namespace Lax920634Proofs.WordEncoding

open Lax920634.ZigZagConstruction Lax920634.WordEncoding

attribute [local irreducible] Lax920634.SeedSearch.seedDegree Lax920634.SeedSearch.poweringExponent

theorem list_lookup (n : ℕ) (f : ℕ → ℕ) (j : ℕ) (hj : j < n) :
    ((n :: (List.range n).map f).tail[j]?).getD 0 = f j := by
  simp only [List.tail_cons,List.getElem?_map,List.getElem?_range hj,
    Option.map_some,Option.getD_some]

theorem list_length (n : ℕ) (f : ℕ → ℕ) :
    (n :: (List.range n).map f).length = n+1 := by
  simp only [List.length_cons,List.length_map,List.length_range]

theorem lookup (k j : ℕ) (hj : j < order k) :
    ((table k).tail[j]?).getD 0 = matchingNeighbor k j :=
  list_lookup (order k) (matchingNeighbor k) j hj

theorem decode_table (r n : ℕ) (f : ℕ → ℕ) :
    SimpleGraph.fromRel (fun u v : Fin n =>
      (u.val/r = v.val/r ∧ u.val+1 = v.val) ∨
        v.val = ((n :: (List.range n).map f).tail[u.val]?).getD 0) =
    SimpleGraph.fromRel (fun u v : Fin n =>
      (u.val/r = v.val/r ∧ u.val+1 = v.val) ∨ v.val = f u.val) := by
  apply congrArg SimpleGraph.fromRel
  funext u v
  rw [list_lookup n f u.val u.isLt]

/--
---
conclusion: Lax920634.WordEncodingCorrectness.table_correct
---
The complete numerical row scan has the stated length and header. Its
endpoints agree with the original matching formula and remain in range.
Substituting these entries into the decoder gives the original graph.
-/
lemma table_correct (k : ℕ) :
    (table k).head? = some (order k) ∧ (table k).length = order k+1 ∧
    (∀ j < order k, ((table k).tail[j]?).getD 0 < order k) ∧
    decode (order k) (table k) = graph k := by
  refine ⟨rfl,list_length _ _,?_,?_⟩
  · intro j hj
    rw [lookup k j hj]
    exact RamArithmetic.matching_bounds k j hj
  · exact decode_table degree (order k) (matchingNeighbor k)

end Lax920634Proofs.WordEncoding
