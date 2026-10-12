import Lax920634Proofs.Family
import Lax920634Proofs.Sizes
import Lax920634.WordEncoding
import Lax808846Proofs.Transfer

namespace Lax920634Proofs.RamArithmetic

open Lax920634.ZigZagConstruction
open Lax920634.SeedSearch

attribute [local irreducible] seedDegree poweringExponent

local notation "D" => seedDegree
local notation "d" => degree
local notation "b" => seedDegree ^ 4

/-- Pack a vertex and a port into one word. -/
def pack (r : ℕ) (p : ℕ × ℕ) : ℕ := p.2 + r * p.1

theorem D_pos : 0 < D := lt_trans (by decide : 0 < 1) Sizes.seedDegree_gt_one

theorem d_pos : 0 < d := by have := Tower.degree_ge_four; omega

theorem b_ge_two : 2 ≤ b := by
  have := Nat.one_lt_pow (by decide : 4 ≠ 0) Sizes.seedDegree_gt_one
  omega

theorem D_le_b : D ≤ b := Nat.le_self_pow (by decide : 4 ≠ 0) D

theorem d_le_b : d ≤ b := by
  change D ^ 2 ≤ D ^ 4
  exact Nat.pow_le_pow_right D_pos (by decide)

theorem b_le_order (k : ℕ) : b ≤ order k := by
  have h : b ≤ baseOrder k := by
    rw [← pow_one b]
    change b ^ 1 ≤ b ^ (k + 1)
    exact Nat.pow_le_pow_right (by have := b_ge_two; omega) (by omega)
  unfold order
  exact h.trans (Nat.le_mul_of_pos_right _ d_pos)

theorem order_succ (k : ℕ) : order (k + 1) = order k * b := by
  unfold order baseOrder
  rw [show k + 1 + 1 = (k + 1) + 1 by omega, pow_succ]
  ring

theorem order_mono {k l : ℕ} (h : k ≤ l) : order k ≤ order l := by
  unfold order baseOrder
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by have := b_ge_two; omega) (Nat.add_le_add_right h 1))

theorem order_pos (k : ℕ) : 0 < order k := Nat.mul_pos (Tower.baseOrder_pos k) d_pos

theorem matching_bounds (k j : ℕ) (hj : j < order k) : matchingNeighbor k j < order k := by
  have h := Family.matchingNeighbor_eq k ⟨j, hj⟩
  rw [h]
  exact Fin.isLt _

theorem rotation_bounds (k v i : ℕ) (hv : v < baseOrder k) (hi : i < d) :
    (rotation k (v,i)).1 < baseOrder k ∧ (rotation k (v,i)).2 < d := by
  rw [Tower.rotation_correct k ⟨v,hv⟩ ⟨i,hi⟩]
  exact ⟨Fin.isLt _, Fin.isLt _⟩

theorem guarded_bounds {n r : ℕ} (F : Fin n × Fin r → Fin n × Fin r)
    (v i : ℕ) (hv : v < n) (hi : i < r) :
    (if h : v < n ∧ i < r then
      let q := F (⟨v,h.1⟩,⟨i,h.2⟩)
      (q.1.val,q.2.val) else (0,0)).1 < n ∧
    (if h : v < n ∧ i < r then
      let q := F (⟨v,h.1⟩,⟨i,h.2⟩)
      (q.1.val,q.2.val) else (0,0)).2 < r := by
  rw [dif_pos ⟨hv,hi⟩]
  exact ⟨Fin.isLt _,Fin.isLt _⟩

theorem seed_bounds (v i : ℕ) (hv : v < b) (hi : i < D) :
    (seedValue (v,i)).1 < b ∧ (seedValue (v,i)).2 < D := by
  exact guarded_bounds Lax920634.SeedRotation.rotation v i hv hi

theorem pack_lt {r n : ℕ} {p : ℕ × ℕ} (hv : p.1 < n) (hi : p.2 < r) :
    pack r p < n * r := by unfold pack; nlinarith

theorem unpack_pack {r : ℕ} (hr : 0 < r) (p : ℕ × ℕ) (hi : p.2 < r) :
    (pack r p / r, pack r p % r) = p := by
  apply Prod.ext
  · simp only [pack, Nat.add_mul_div_left _ _ hr, Nat.div_eq_of_lt hi, Nat.zero_add]
  · simp [pack, Nat.add_mod, Nat.mod_eq_of_lt hi]

theorem row_unpack (v i : ℕ) (hi : i < d) :
    ((v * d + i) / d, (v * d + i) % d) = (v,i) := by
  simpa only [pack, Nat.add_comm, Nat.mul_comm] using unpack_pack d_pos (v,i) hi

theorem packed_rotation (k v i : ℕ) (hi : i < d) :
    pack d (rotation k (v,i)) = matchingNeighbor k (v * d + i) := by
  unfold matchingNeighbor
  rw [row_unpack v i hi]
  rfl

theorem first_level_min (n k : ℕ) (hk : k < Lax920634.GraphEncoding.selectedLevel n) :
    baseOrder k < 2 * n := by
  rw [Sizes.selectedLevel_eq] at hk
  have h := Nat.find_min (SeedGraph.finBase.exists_size_ge Sizes.seedDegree_gt_one (2*n)) hk
  change ¬ 2*n ≤ baseOrder k at h
  omega

theorem d_eq : d = D * D := by change D ^ 2 = D * D; ring

theorem b_eq : b = d * d := by change D ^ 4 = (D ^ 2) * (D ^ 2); ring

theorem D_le_d : D ≤ d := by rw [d_eq]; exact Nat.le_mul_of_pos_right _ D_pos

theorem seed_size_le_order (k : ℕ) : b * D ≤ order k := by
  have hb : b ≤ baseOrder k := by
    rw [← pow_one b]
    change b ^ 1 ≤ b ^ (k+1)
    exact Nat.pow_le_pow_right (by have := b_ge_two; omega) (by omega)
  exact Nat.mul_le_mul hb D_le_d

theorem baseOrder_succ (k : ℕ) : baseOrder (k+1) = baseOrder k * b := by
  unfold baseOrder
  rw [show k+1+1 = (k+1)+1 by omega, pow_succ]

end Lax920634Proofs.RamArithmetic
