import Lax920634.PathReplacement
import Mathlib.Tactic

namespace Lax920634Proofs.Paths

open Lax920634.PathReplacement Lax920634.EdgeExpansion

private def next {d : ℕ} (i : Fin d) : Fin d :=
  if h : i.val + 1 < d then ⟨i.val + 1, h⟩ else i

private def prev {d : ℕ} (i : Fin d) : Fin d := ⟨i.val - 1, by omega⟩

/-- Only the preceding, following and paired ports can be neighbors. -/
theorem neighbor_subset {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (hR : Function.Involutive R) (u : Fin n × Fin d) :
    (graph R).neighborSet u ⊆ {(next u.2 |> (u.1, ·)), (u.1, prev u.2), R u} := by
  intro v hv
  rcases hv.2 with h | h
  · rcases h with h | h
    · have hi : u.2.val + 1 < d := h.2 ▸ v.2.isLt
      have he : v = (u.1, next u.2) := by
        apply Prod.ext
        · exact h.1.symm
        · apply Fin.ext
          simp only [next, dif_pos hi]
          exact h.2.symm
      simp [he]
    · simp [h]
  · rcases h with h | h
    · have he : v = (u.1, prev u.2) := by
        apply Prod.ext
        · exact h.1
        · apply Fin.ext
          simp only [prev]
          omega
      simp [he]
    · have he : v = R u := by rw [h, hR]
      simp [he]

/-- Path replacement of an involutive port map has maximum degree at most three. -/
theorem subcubic {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (hR : Function.Involutive R) : IsSubcubic (graph R) := by
  intro u
  have hs := neighbor_subset R hR u
  have hc : ({(u.1, next u.2), (u.1, prev u.2), R u} : Set _).ncard ≤ 3 := by
    have h₁ := Set.ncard_insert_le (u.1, next u.2)
      ({(u.1, prev u.2), R u} : Set _)
    have h₂ := Set.ncard_insert_le (u.1, prev u.2) ({R u} : Set _)
    simp only [Set.ncard_singleton] at h₂
    exact (h₁.trans (Nat.add_le_add_right h₂ 1))
  exact (Set.ncard_le_ncard hs).trans hc

/-- A nonconstant membership predicate on a finite path changes across an edge. -/
theorem exists_transition {d : ℕ} (P : Fin d → Prop) (i j : Fin d)
    (hi : P i) (hj : ¬ P j) :
    ∃ a b : Fin d, a.val + 1 = b.val ∧ (P a ↔ ¬ P b) := by
  classical
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  by_contra! h
  have hn (a b : Fin d) (hab : a.val + 1 = b.val) : P a ↔ P b := by
    have hh := h a b hab
    tauto
  have hall : ∀ k : Fin d, P k ↔ P ⟨0, hd⟩ := by
    intro k
    induction hk : k.val using Nat.strong_induction_on generalizing k with
    | h m ih =>
      by_cases hm : m = 0
      · have he : k = ⟨0, hd⟩ := Fin.ext (hk.trans hm)
        simp [he]
      · let a : Fin d := ⟨m - 1, by omega⟩
        exact (hn a k (by simp only [a]; omega)).symm.trans (ih (m - 1) (by omega) a rfl)
  exact hj ((hall j).mpr ((hall i).mp hi))

/-- Base vertices whose entire path cloud lies in the cut. -/
def fullClouds {n d : ℕ} (S : Set (Fin n × Fin d)) : Set (Fin n) :=
  {v | ∀ i, (v, i) ∈ S}

/-- Base vertices whose path cloud meets both sides of the cut. -/
def partialClouds {n d : ℕ} (S : Set (Fin n × Fin d)) : Set (Fin n) :=
  {v | (∃ i, (v, i) ∈ S) ∧ (∃ j, (v, j) ∉ S)}

/-- Every occupied cloud is either full or partial. -/
theorem occupied_full_or_partial {n d : ℕ} (S : Set (Fin n × Fin d))
    (v : Fin n) (i : Fin d) (hi : (v, i) ∈ S) :
    v ∈ fullClouds S ∨ v ∈ partialClouds S := by
  classical
  by_cases hv : v ∈ fullClouds S
  · exact Or.inl hv
  · right
    refine ⟨⟨i, hi⟩, ?_⟩
    simpa only [fullClouds, Set.mem_setOf_eq, not_forall] using hv

/-- Each partial cloud supplies a distinct path edge crossing the cut. -/
theorem partial_card_le_boundary {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (S : Set (Fin n × Fin d)) (hd : 0 < d) :
    (partialClouds S).ncard ≤ (edgeBoundary (graph R) S).ncard := by
  classical
  have hex (v : Fin n) (hv : v ∈ partialClouds S) :
      ∃ e ∈ edgeBoundary (graph R) S, e.1.1 = v := by
    rcases hv with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    obtain ⟨a, b, hab, hp⟩ := exists_transition (fun i => (v, i) ∈ S) i j hi hj
    by_cases ha : (v, a) ∈ S
    · have hb : (v, b) ∉ S := hp.mp ha
      refine ⟨((v, a), (v, b)), ⟨ha, hb, ?_⟩, rfl⟩
      refine ⟨?_, Or.inl (Or.inl ⟨rfl, hab⟩)⟩
      intro he
      change (v, a) = (v, b) at he
      have he' : a.val = b.val := congrArg (fun p : Fin n × Fin d => p.2.val) he
      omega
    · have hb : (v, b) ∈ S := by tauto
      refine ⟨((v, b), (v, a)), ⟨hb, ha, ?_⟩, rfl⟩
      refine ⟨?_, Or.inr (Or.inl ⟨rfl, hab⟩)⟩
      intro he
      change (v, b) = (v, a) at he
      have he' : b.val = a.val := congrArg (fun p : Fin n × Fin d => p.2.val) he
      omega
  let f : Fin n → (Fin n × Fin d) × (Fin n × Fin d) := fun v =>
    if hv : v ∈ partialClouds S then Classical.choose (hex v hv)
    else ((v, ⟨0, hd⟩), (v, ⟨0, hd⟩))
  have hf (v : Fin n) (hv : v ∈ partialClouds S) :
      f v ∈ edgeBoundary (graph R) S ∧ (f v).1.1 = v := by
    simpa only [f, dif_pos hv] using Classical.choose_spec (hex v hv)
  apply Set.ncard_le_ncard_of_injOn f (fun v hv => (hf v hv).1)
  intro v hv w hw h
  exact ((hf v hv).2).symm.trans ((congrArg (fun e => e.1.1) h).trans (hf w hw).2)

/-- The size of a cut is bounded by the number of its occupied clouds. -/
theorem cut_card_le_clouds {n d : ℕ} (S : Set (Fin n × Fin d)) :
    S.ncard ≤ d * ((fullClouds S).ncard + (partialClouds S).ncard) := by
  have hsub : S ⊆ (fullClouds S ∪ partialClouds S) ×ˢ (Set.univ : Set (Fin d)) := by
    rintro ⟨v, i⟩ hi
    exact ⟨occupied_full_or_partial S v i hi, Set.mem_univ _⟩
  have hc := Set.ncard_le_ncard hsub
  rw [Set.ncard_prod] at hc
  simp only [Set.ncard_univ, Nat.card_fin] at hc
  exact hc.trans (by
    simpa only [Nat.mul_comm] using Nat.mul_le_mul_right d (Set.ncard_union_le _ _))

/-- Full clouds occupy exactly `d` vertices apiece. -/
theorem full_cloud_card_le_cut {n d : ℕ} (S : Set (Fin n × Fin d)) :
    d * (fullClouds S).ncard ≤ S.ncard := by
  have hs : fullClouds S ×ˢ (Set.univ : Set (Fin d)) ⊆ S := by
    rintro ⟨v, i⟩ h
    exact h.1 i
  simpa only [Set.ncard_prod, Set.ncard_univ, Nat.card_fin, Nat.mul_comm]
    using Set.ncard_le_ncard hs

/-- A base edge leaving a full cloud either crosses the cut or reaches a partial cloud. -/
theorem full_base_cut_le {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (hR : Function.Involutive R) (S : Set (Fin n × Fin d)) :
    (baseCut R (fullClouds S)).ncard ≤
      (edgeBoundary (graph R) S).ncard + d * (partialClouds S).ncard := by
  classical
  let B : Set (Fin n × Fin d) := baseCut R (fullClouds S)
  let good : Set (Fin n × Fin d) := {p | p ∈ B ∧ (R p).1 ∉ partialClouds S}
  let bad : Set (Fin n × Fin d) := {p | p ∈ B ∧ (R p).1 ∈ partialClouds S}
  have hsplit : B = good ∪ bad := by ext p; simp only [good, bad, Set.mem_union, Set.mem_setOf_eq]; tauto
  have hgood : good.ncard ≤ (edgeBoundary (graph R) S).ncard := by
    apply Set.ncard_le_ncard_of_injOn (fun p => (p, R p))
    · intro p hp
      have hsrc : p ∈ S := hp.1.1 p.2
      have htgt : R p ∉ S := by
        intro h
        rcases occupied_full_or_partial S (R p).1 (R p).2 h with h | h
        · exact hp.1.2 h
        · exact hp.2 h
      refine ⟨hsrc, htgt, ?_⟩
      refine ⟨?_, Or.inl (Or.inr rfl)⟩
      intro he
      change p = R p at he
      exact htgt (he ▸ hsrc)
    · intro p _ q _ he
      exact congrArg Prod.fst he
  have hbad : bad.ncard ≤ d * (partialClouds S).ncard := by
    have h := Set.ncard_le_ncard_of_injOn R
      (fun p (hp : p ∈ bad) => (show R p ∈ partialClouds S ×ˢ (Set.univ : Set (Fin d)) from
        ⟨hp.2, Set.mem_univ _⟩)) hR.injective.injOn
    simpa only [Set.ncard_prod, Set.ncard_univ, Nat.card_fin, Nat.mul_comm] using h
  change B.ncard ≤ _
  rw [hsplit]
  exact (Set.ncard_union_le good bad).trans (Nat.add_le_add hgood hbad)

/-- Expansion of the regular base graph survives path replacement. -/
theorem expansion {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (hR : Function.Involutive R) (hd : 2 ≤ d)
    (hbase : ∀ U : Set (Fin n),
      d * min U.ncard (n - U.ncard) ≤ 4 * (baseCut R U).ncard) :
    HasEdgeExpansionAtLeast (graph R) (1 / (8 * (d : ℚ))) := by
  intro S hS
  have hdpos : 0 < d := by omega
  have hc := full_cloud_card_le_cut S
  have hsmall : 2 * (fullClouds S).ncard ≤ n := by
    apply Nat.le_of_mul_le_mul_left (c := d) _ hdpos
    simp only [Fintype.card_prod, Fintype.card_fin] at hS
    nlinarith
  have hb := hbase (fullClouds S)
  rw [min_eq_left (by omega)] at hb
  have hp := partial_card_le_boundary R S hdpos
  have hcut := cut_card_le_clouds S
  have hbc := full_base_cut_le R hR S
  have hbound : S.ncard ≤ (8 * d) * (edgeBoundary (graph R) S).ncard := by
    nlinarith
  have hq : (0 : ℚ) < 8 * (d : ℚ) := by positivity
  rw [one_div_mul_eq_div, div_le_iff₀ hq]
  exact_mod_cast (by simpa only [Nat.mul_comm] using hbound :
    S.ncard ≤ (edgeBoundary (graph R) S).ncard * (8 * d))

end Lax920634Proofs.Paths
