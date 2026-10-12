import Lax920634Proofs.Tower
import Lax920634Proofs.SpectralExpansion
import Lax920634Proofs.Paths

namespace Lax920634Proofs.Family

open Lax920634.ZigZagConstruction Lax920634.EdgeExpansion
open Lax323828Proofs.PCPFoundation.Complexity

attribute [local irreducible] Lax920634.SeedSearch.seedDegree
attribute [local irreducible] Lax920634.SeedSearch.poweringExponent

/-- The semantic tower rotation, on the same numbered port types as the executable construction. -/
noncomputable def portRotation (k : ℕ) : Fin (baseOrder k) × Fin degree → Fin (baseOrder k) × Fin degree :=
  (SeedGraph.finBase.data k).val

/-- Number the vertices of the paths in the canonical carrier. -/
def numbering (k : ℕ) : (Fin (baseOrder k) × Fin degree) ≃ Fin (order k) := finProdFinEquiv

/-- The matching-neighbor formula computes the numbered paired port. -/
theorem matchingNeighbor_eq (k : ℕ) (v : Fin (order k)) :
    matchingNeighbor k v.val = (numbering k (portRotation k ((numbering k).symm v))).val := by
  unfold matchingNeighbor
  have h := Tower.rotation_correct k ((numbering k).symm v).1 ((numbering k).symm v).2
  change rotation k (v.val / degree, v.val % degree) = _ at h
  rw [h]
  rfl

/-- A path edge in numerical labels is precisely a consecutive pair of ports in one cloud. -/
theorem path_iff (k : ℕ) (u v : Fin (order k)) :
    (u.val / degree = v.val / degree ∧ u.val + 1 = v.val) ↔
      (((numbering k).symm u).1 = ((numbering k).symm v).1 ∧
        ((numbering k).symm u).2.val + 1 = ((numbering k).symm v).2.val) := by
  change (u.val / degree = v.val / degree ∧ u.val + 1 = v.val) ↔
    (((numbering k).symm u).1 = ((numbering k).symm v).1 ∧
      u.val % degree + 1 = v.val % degree)
  have hu := Nat.mod_add_div u.val degree
  have hv := Nat.mod_add_div v.val degree
  constructor
  · rintro ⟨hdiv, hval⟩
    refine ⟨Fin.ext hdiv, ?_⟩
    rw [hdiv] at hu
    omega
  · rintro ⟨hdiv, hmod⟩
    have hdiv' : u.val / degree = v.val / degree := congrArg Fin.val hdiv
    refine ⟨hdiv', ?_⟩
    rw [hdiv'] at hu
    omega

/-- The numerical construction is exactly the path replacement of the analyzed tower graph. -/
theorem graph_eq (k : ℕ) : graph k =
    (Lax920634.PathReplacement.graph (portRotation k)).comap (numbering k).symm := by
  apply SimpleGraph.ext
  funext u v
  apply propext
  have hne : u ≠ v ↔ (numbering k).symm u ≠ (numbering k).symm v := by
    constructor
    · intro h he
      exact h ((numbering k).symm.injective he)
    · intro h he
      exact h (congrArg (numbering k).symm he)
  have hm (u v : Fin (order k)) : v.val = matchingNeighbor k u.val ↔
      (numbering k).symm v = portRotation k ((numbering k).symm u) := by
    rw [matchingNeighbor_eq]
    constructor
    · intro h
      have he := congrArg (numbering k).symm (Fin.ext h)
      simpa only [Equiv.symm_apply_apply] using he
    · intro h
      have he := congrArg (numbering k) h
      exact congrArg Fin.val (by simpa only [Equiv.apply_symm_apply] using he)
  change (u ≠ v ∧ (((u.val / degree = v.val / degree ∧ u.val + 1 = v.val) ∨
    v.val = matchingNeighbor k u.val) ∨
    ((v.val / degree = u.val / degree ∧ v.val + 1 = u.val) ∨
    u.val = matchingNeighbor k v.val))) ↔ _
  rw [hne, path_iff, path_iff, hm, hm]
  rfl

/-- Relabeling preserves the bound on the number of neighbors. -/
theorem subcubic_comap {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (e : W ≃ V) (hG : IsSubcubic G) : IsSubcubic (G.comap e) := by
  intro v
  have he : e '' (G.comap e).neighborSet v = G.neighborSet (e v) := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro h
      exact ⟨e.symm w, by simpa using h, by simp⟩
  rw [← Set.ncard_image_of_injective ((G.comap e).neighborSet v) e.injective, he]
  exact hG (e v)

/-- Every graph returned by the construction is subcubic. -/
theorem subcubic (k : ℕ) : IsSubcubic (graph k) := by
  rw [graph_eq]
  apply subcubic_comap
  exact Paths.subcubic _ (SeedGraph.finBase.data k).property

/-- The numbered regular tower has the spectral cut inequality required by path replacement. -/
theorem base_expansion (k : ℕ) (U : Set (Fin (baseOrder k))) :
    degree * min U.ncard (baseOrder k - U.ncard) ≤
      4 * (Lax920634.PathReplacement.baseCut (portRotation k) U).ncard := by
  have hspec := SeedGraph.finBase.spectral_graphAt k
  have hd : 0 < degree := by have h := Tower.degree_ge_four; omega
  exact SpectralExpansion.base_cut_lower_bound (portRotation k) hd
    (SeedGraph.finBase.data k).property (Tower.baseOrder_pos k) hspec U

end Lax920634Proofs.Family
