import Lax920634.EdgeExpansion
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

namespace Lax920634Proofs.Components

open Lax920634.EdgeExpansion
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Set cardinality agrees with the cardinality of its finite subtype. -/
theorem card_set (S : Set V) [Fintype S] : S.ncard = Fintype.card S := by
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

/-- A partition of the undeleted vertices into sets closed under undeleted edges. -/
structure Partition (G : SimpleGraph V) (X : Set V) (C : Type) where
  piece : C → Set V
  outside : ∀ c v, v ∈ piece c → v ∉ X
  unique : ∀ v, v ∉ X → ∃! c, v ∈ piece c
  closed : ∀ c u v, u ∈ piece c → v ∉ X → G.Adj u v → v ∈ piece c

/-- Summing the sizes of the parts counts every undeleted vertex exactly once. -/
theorem sum_piece_card {G : SimpleGraph V} {X : Set V} {C : Type} [Fintype C]
    (P : Partition G X C) : ∑ c, (P.piece c).ncard = Xᶜ.ncard := by
  classical
  let f : (Σ c, {v : V // v ∈ P.piece c}) → {v : V // v ∉ X} :=
    fun p => ⟨p.2.val, P.outside p.1 p.2.val p.2.property⟩
  have hinj : Function.Injective f := by
    rintro ⟨c, u⟩ ⟨c', u'⟩ he
    have hv : u.val = u'.val := congrArg Subtype.val he
    have hc : c = c' := by
      obtain ⟨a, ha, hu⟩ := P.unique u.val (P.outside c u.val u.property)
      exact (hu c u.property).trans (hu c' (hv.symm ▸ u'.property)).symm
    cases hc
    exact congrArg (Sigma.mk c) (Subtype.ext hv)
  have hsurj : Function.Surjective f := by
    rintro ⟨v, hv⟩
    obtain ⟨c, hc, _⟩ := P.unique v hv
    exact ⟨⟨c, ⟨v, hc⟩⟩, rfl⟩
  have h := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  rw [Fintype.card_sigma] at h
  have he : {v : V // v ∉ X} = (Xᶜ : Set V) := rfl
  simpa only [Fintype.card_eq_nat_card, Nat.card_coe_set_eq, he] using h

/-- Summed boundary edges of the parts are bounded by the degrees of deleted vertices. -/
theorem sum_boundary_card_le {G : SimpleGraph V} {X : Set V} {C : Type} [Fintype C]
    (P : Partition G X C) (hdegree : IsSubcubic G) :
    ∑ c, (edgeBoundary G (P.piece c)).ncard ≤ 3 * X.ncard := by
  classical
  have hx (c : C) (e : (edgeBoundary G (P.piece c))) : e.val.2 ∈ X := by
    by_contra h
    exact e.property.2.1 (P.closed c _ _ e.property.1 h e.property.2.2)
  let f : (Σ c, edgeBoundary G (P.piece c)) →
      (Σ x : X, G.neighborSet x.val) :=
    fun p => ⟨⟨p.2.val.2, hx p.1 p.2⟩, ⟨p.2.val.1, p.2.property.2.2.symm⟩⟩
  have hinj : Function.Injective f := by
    rintro ⟨c, e⟩ ⟨c', e'⟩ he
    have hb : e.val.2 = e'.val.2 := congrArg (fun p => p.1.val) he
    have ha : e.val.1 = e'.val.1 := congrArg (fun p => p.2.val) he
    have hed : e.val = e'.val := Prod.ext ha hb
    have hc : c = c' := by
      obtain ⟨a, ha', hu⟩ := P.unique e.val.1 (P.outside c _ e.property.1)
      exact (hu c e.property.1).trans (hu c' (ha.symm ▸ e'.property.1)).symm
    cases hc
    exact congrArg (Sigma.mk c) (Subtype.ext hed)
  have h := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_sigma, Fintype.card_sigma] at h
  have hb : (∑ x : X, Fintype.card (G.neighborSet x.val)) ≤ 3 * X.ncard := by
    have hsum := Finset.sum_le_sum (fun (x : X) (_ : x ∈ Finset.univ) => hdegree x.val)
    simpa only [card_set, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using hsum
  have h' : (∑ c, (edgeBoundary G (P.piece c)).ncard) ≤
      ∑ x : X, Fintype.card (G.neighborSet x.val) := by
    simpa only [Fintype.card_eq_nat_card, Nat.card_coe_set_eq] using h
  exact h'.trans hb

/-- If all parts have size at most half the graph, expansion forces a large deletion set. -/
theorem deletion_large_of_small_parts {G : SimpleGraph V} {X : Set V} {C : Type}
    [Fintype C] (P : Partition G X C) (d : ℕ) (hd : 0 < d)
    (hdegree : IsSubcubic G)
    (hex : HasEdgeExpansionAtLeast G (1 / (8 * (d : ℚ))))
    (hsmall : ∀ c, 2 * (P.piece c).ncard ≤ Fintype.card V) :
    Fintype.card V ≤ (24 * d + 1) * X.ncard := by
  classical
  have hs := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) => hex (P.piece c) (hsmall c))
  simp only [← Finset.mul_sum, ← Nat.cast_sum, sum_piece_card P] at hs
  have hb : ((∑ c, (edgeBoundary G (P.piece c)).ncard : ℕ) : ℚ) ≤ 3 * (X.ncard : ℚ) := by
    exact_mod_cast sum_boundary_card_le P hdegree
  have hout : Xᶜ.ncard ≤ 24 * d * X.ncard := by
    have hq : (0 : ℚ) < 8 * (d : ℚ) := by positivity
    have hm := (div_le_iff₀ hq).mp (show (Xᶜ.ncard : ℚ) / (8 * (d : ℚ)) ≤
      3 * (X.ncard : ℚ) by simpa only [one_div_mul_eq_div] using hs.trans hb)
    exact_mod_cast (by nlinarith [hm] : (Xᶜ.ncard : ℚ) ≤ 24 * (d : ℚ) * (X.ncard : ℚ))
  have htotal : X.ncard + Xᶜ.ncard = Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using Set.ncard_add_ncard_compl X
  nlinarith

/-- The undeleted vertices of a component of the induced graph. -/
def componentPiece (G : SimpleGraph V) (X : Set V)
    (c : (G.induce Xᶜ).ConnectedComponent) : Set V := Subtype.val '' c.supp

/-- Connected components form a partition closed under every undeleted edge. -/
def componentPartition (G : SimpleGraph V) (X : Set V) :
    Partition G X (G.induce Xᶜ).ConnectedComponent where
  piece := componentPiece G X
  outside := by
    rintro c v ⟨u, hu, rfl⟩
    exact u.property
  unique := by
    intro v hv
    let u : (Xᶜ : Set V) := ⟨v, hv⟩
    refine ⟨(G.induce Xᶜ).connectedComponentMk u, ⟨u, rfl, rfl⟩, ?_⟩
    rintro c ⟨w, hw, he⟩
    have hw' : w = u := Subtype.ext he
    change (G.induce Xᶜ).connectedComponentMk w = c at hw
    rw [hw'] at hw
    exact hw.symm
  closed := by
    rintro c u v ⟨u', hu', rfl⟩ hv hadj
    let v' : (Xᶜ : Set V) := ⟨v, hv⟩
    refine ⟨v', ?_, rfl⟩
    have h : (G.induce Xᶜ).Adj u' v' := hadj
    exact (SimpleGraph.ConnectedComponent.mem_supp_congr_adj c h).mp hu' 

end Lax920634Proofs.Components
