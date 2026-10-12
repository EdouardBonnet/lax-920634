import Lax920634Proofs.SeedGraph
import Lax920634.ZigZagConstruction

namespace Lax920634Proofs.Tower

attribute [local irreducible] Lax920634.SeedSearch.seedDegree
attribute [local irreducible] Lax920634.SeedSearch.poweringExponent


open Lax323828Proofs.PCPFoundation.Complexity
open Lax920634.ZigZagConstruction

/-- The fixed seed query agrees with the numbered base's numerical query. -/
theorem seedValue_eq (p : ℕ × ℕ) :
    seedValue p = SeedGraph.finBase.baseVal p.1 p.2 := by
  rfl

/-- The executable recurrence agrees with the proved numbered tower recurrence. -/
theorem rotation_eq (k : ℕ) (p : ℕ × ℕ) :
    rotation k p = SeedGraph.finBase.rotVal k p := by
  induction k generalizing p with
  | zero =>
    rcases p with ⟨v, i⟩
    simp only [rotation, FinBase.rotVal, seedValue_eq]
    rfl
  | succ k ih =>
    rcases p with ⟨v, i⟩
    simp only [rotation, FinBase.rotVal, ih, seedValue_eq]
    rfl

/-- The numbered tower computes the intended rotation on every valid vertex and dart. -/
theorem rotation_correct (k : ℕ) (v : Fin (baseOrder k)) (i : Fin degree) :
    rotation k (v.val, i.val) =
      (((SeedGraph.finBase.data k).val (v, i)).1.val,
       ((SeedGraph.finBase.data k).val (v, i)).2.val) := by
  exact (rotation_eq k (v.val, i.val)).trans (SeedGraph.finBase.rotVal_eq k v i)

/-- The fixed tower degree is at least four. -/
theorem degree_ge_four : 4 ≤ degree := by
  have hD : 1 < Lax920634.SeedSearch.seedDegree := by
    unfold Lax920634.SeedSearch.seedDegree
    apply Nat.one_lt_pow
    · norm_num [Lax920634.SeedSearch.poweringExponent]
    · norm_num
  change 4 ≤ Lax920634.SeedSearch.seedDegree ^ 2
  nlinarith

/-- Every regular graph in the tower has positive order. -/
theorem baseOrder_pos (k : ℕ) : 0 < baseOrder k := by
  have hD : 0 < Lax920634.SeedSearch.seedDegree := by
    unfold Lax920634.SeedSearch.seedDegree
    exact pow_pos (by norm_num : 0 < 120) _
  unfold baseOrder
  exact pow_pos (pow_pos hD _) _

end Lax920634Proofs.Tower
