import Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.EdgeExpansion
import Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.Expander
import Lax920634.PathReplacement
import Mathlib.Tactic

namespace Lax920634Proofs.SpectralExpansion
set_option backward.isDefEq.respectTransparency false

open Lax323828Proofs.PCPFoundation.Complexity

/-- Spectral bound two fifths gives at least a quarter-degree times the smaller cut side. -/
theorem cut_lower_bound (G : RegGraph) (hn : 0 < G.order)
    (hspec : G.SpectralBound (2 / 5)) (S : Finset G.V) :
    G.deg * min S.card Sᶜ.card ≤ 4 * (G.dartsBetween S Sᶜ).card := by
  have hc := G.card_dartsBetween_compl_ge (by norm_num : (0 : ℝ) ≤ 2 / 5) hspec hn S
  have hN : (S.card : ℝ) + (Sᶜ.card : ℝ) = G.order := by
    exact_mod_cast Finset.card_add_card_compl S
  have hmin : ((min S.card Sᶜ.card : ℕ) : ℝ) * G.order ≤ 2 * (S.card : ℝ) * Sᶜ.card := by
    rcases le_total S.card Sᶜ.card with h | h
    · rw [min_eq_left h]
      have h' : (S.card : ℝ) ≤ Sᶜ.card := by exact_mod_cast h
      nlinarith
    · rw [min_eq_right h]
      have h' : (Sᶜ.card : ℝ) ≤ S.card := by exact_mod_cast h
      nlinarith
  have hNpos : (0 : ℝ) < G.order := by exact_mod_cast hn
  have hm : (((min S.card Sᶜ.card : ℕ) : ℝ) / 2) ≤
      (S.card : ℝ) * Sᶜ.card / G.order := by
    apply (le_div_iff₀ hNpos).mpr
    nlinarith
  have hd : (0 : ℝ) ≤ G.deg := by positivity
  have hmul := mul_le_mul_of_nonneg_left hm (show 0 ≤ (1 - (2 / 5 : ℝ)) * G.deg by positivity)
  have hz : 0 ≤ (G.deg : ℝ) * (min S.card Sᶜ.card : ℕ) := by positivity
  have hout : (G.deg : ℝ) * (min S.card Sᶜ.card : ℕ) ≤
      4 * ((G.dartsBetween S Sᶜ).card : ℝ) := by nlinarith [hmul, hc]
  exact_mod_cast hout

/-- Translate the regular graph's dart cut into the corresponding set of raw ports. -/
theorem base_cut_lower_bound {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (hd : 0 < d) (hR : Function.Involutive R)
    (hn : 0 < n)
    (hspec : (RegGraph.ofRot d hd n R hR).SpectralBound (2 / 5))
    (U : Set (Fin n)) :
    d * min U.ncard (n - U.ncard) ≤ 4 * (Lax920634.PathReplacement.baseCut R U).ncard := by
  classical
  let G := RegGraph.ofRot d hd n R hR
  let S := (Set.toFinite U).toFinset
  have he : (Lax920634.PathReplacement.baseCut R U) = (↑(G.dartsBetween S Sᶜ) : Set (G.V × G.D)) := by
    ext p
    simp only [Lax920634.PathReplacement.baseCut, Set.mem_setOf_eq, Finset.mem_coe,
      RegGraph.dartsBetween, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl, Set.Finite.mem_toFinset, S, RegGraph.nbr, G, RegGraph.ofRot]
  have h := cut_lower_bound G (by simpa only [G, RegGraph.order, RegGraph.ofRot, Fintype.card_fin] using hn)
    hspec S
  have hdeg : G.deg = d := Fintype.card_fin d
  have hcard : S.card = U.ncard := (Set.ncard_eq_toFinset_card U).symm
  have hcomp : Sᶜ.card = n - S.card := by
    simpa only [Fintype.card_fin] using Finset.card_compl S
  rw [hdeg, hcomp, hcard] at h
  rw [he, Set.ncard_coe_finset]
  exact h

end Lax920634Proofs.SpectralExpansion
