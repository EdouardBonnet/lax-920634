import Lax920634Proofs.Algorithm

namespace Lax920634Proofs.Sizes

open Lax920634.GraphEncoding Lax920634.ZigZagConstruction
open Lax323828Proofs.PCPFoundation.Complexity

attribute [local irreducible] Lax920634.SeedSearch.seedDegree
attribute [local irreducible] Lax920634.SeedSearch.poweringExponent

/-- The fixed seed degree is greater than one. -/
theorem seedDegree_gt_one : 1 < Lax920634.SeedSearch.seedDegree := by
  have h := Tower.degree_ge_four
  change 4 ≤ Lax920634.SeedSearch.seedDegree ^ 2 at h
  nlinarith

/-- The bounded numerical level selector reaches the first sufficiently large tower member. -/
theorem selectedLevel_eq (n : ℕ) :
    selectedLevel n = SeedGraph.finBase.fitLevel seedDegree_gt_one n := by
  have h := SeedGraph.finBase.levelFn_fitLevel (2 * Polynomial.X) seedDegree_gt_one n
    (by simpa only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X] using SeedGraph.finBase.fitLevel_le seedDegree_gt_one n)
  change SeedGraph.finBase.searchLevel (2 * Polynomial.X) (List.replicate n true) = _ at h
  simpa only [Algorithm.searchLevel_eq, List.length_replicate] using h

/-- The selected regular graph has at least twice the requested number of vertices. -/
theorem request_le_baseOrder (n : ℕ) : 2 * n ≤ baseOrder (selectedLevel n) := by
  have h := SeedGraph.finBase.le_size_level seedDegree_gt_one (2 * n)
  change 2 * n ≤ baseOrder (SeedGraph.finBase.fitLevel seedDegree_gt_one n) at h
  rw [← selectedLevel_eq n] at h
  exact h

/-- The selected graph meets the requested order. -/
theorem request_le_order (n : ℕ) : n ≤ order (selectedLevel n) := by
  have h := request_le_baseOrder n
  have hd := Tower.degree_ge_four
  unfold order
  nlinarith

/-- Selected graph orders exceed the request by at most a fixed constant factor. -/
theorem order_bound (n : ℕ) :
    order (selectedLevel n) ≤
      (2 * degree * Lax920634.SeedSearch.seedDegree ^ 4) * (n + 1) := by
  have h := SeedGraph.finBase.size_searchLevel_le (2 * Polynomial.X) (List.replicate n true)
  rw [Algorithm.searchLevel_eq, List.length_replicate] at h
  change baseOrder (selectedLevel n) ≤ Lax920634.SeedSearch.seedDegree ^ 4 +
    2 * n * Lax920634.SeedSearch.seedDegree ^ 4 at h
  unfold order
  calc baseOrder (selectedLevel n) * degree ≤
      (Lax920634.SeedSearch.seedDegree ^ 4 + 2 * n * Lax920634.SeedSearch.seedDegree ^ 4) * degree :=
        Nat.mul_le_mul_right degree h
    _ ≤ (2 * degree * Lax920634.SeedSearch.seedDegree ^ 4) * (n + 1) := by nlinarith

end Lax920634Proofs.Sizes
