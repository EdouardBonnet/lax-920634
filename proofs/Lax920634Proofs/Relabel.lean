import Lax920634.EdgeExpansion
import Mathlib.Tactic

namespace Lax920634Proofs.Relabel
open Lax920634.EdgeExpansion

/-- Relabeling by an equivalence preserves the boundary size. -/
theorem boundary_card_comap {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (e : W ≃ V) (S : Set W) :
    (edgeBoundary (G.comap e) S).ncard = (edgeBoundary G (e '' S)).ncard := by
  have he : (Equiv.prodCongr e e) '' edgeBoundary (G.comap e) S =
      edgeBoundary G (e '' S) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨q.1, hq.1, rfl⟩, ?_, hq.2.2⟩
      rintro ⟨w, hw, hew⟩
      exact hq.2.1 (e.injective hew ▸ hw)
    · rintro ⟨hu, hv, hadj⟩
      refine ⟨(e.symm p.1, e.symm p.2), ?_, by simp⟩
      refine ⟨?_, ?_, by simpa using hadj⟩
      · rcases hu with ⟨u, hu, heu⟩
        simpa [← heu] using hu
      · intro h
        exact hv ⟨e.symm p.2, h, by simp⟩
  rw [← he, Set.ncard_image_of_injective _ (Equiv.prodCongr e e).injective]

/-- Edge expansion is preserved by a computable vertex equivalence. -/
theorem expansion_comap {V W : Type} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (e : W ≃ V) (h : ℚ)
    (hex : HasEdgeExpansionAtLeast G h) : HasEdgeExpansionAtLeast (G.comap e) h := by
  intro S hS
  have hc : (e '' S).ncard = S.ncard := Set.ncard_image_of_injective S e.injective
  have hb := hex (e '' S) (by simpa [hc, Fintype.card_congr e] using hS)
  rw [boundary_card_comap, ← hc]
  exact hb


end Lax920634Proofs.Relabel
