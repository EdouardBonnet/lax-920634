import Lax920634.SeedSearch
import Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.ExpanderRandom
import Mathlib.Tactic

namespace Lax920634Proofs.Seed

open Lax920634.SeedSearch

/-- A successful seed table exists at every order. -/
theorem exists_good_table (n : ℕ) : ∃ T : Table n, GoodTable T := by
  obtain ⟨σ, hσ⟩ := Lax323828Proofs.PCPFoundation.Complexity.exists_good_perms n
  refine ⟨fun i v => σ i v, (fun i => (σ i).bijective), ?_⟩
  intro S hS
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp [escape]⟩
  · simpa only [escape, Lax323828Proofs.PCPFoundation.Complexity.escape] using hσ S hS hne

/-- Numerical candidate codes cover every finite table. -/
theorem decode_surjective (n : ℕ) : Function.Surjective (decode n) := by
  intro T
  let f : Fin (30 * n) → Fin n := fun j => T (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  refine ⟨finFunctionFinEquiv f, ?_⟩
  funext i v
  change finFunctionFinEquiv.symm (finFunctionFinEquiv f) (finProdFinEquiv (i, v)) = T i v
  rw [Equiv.symm_apply_apply]
  change T (finProdFinEquiv.symm (finProdFinEquiv (i, v))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, v))).2 = T i v
  rw [Equiv.symm_apply_apply]

/-- The deterministic seed scan succeeds and returns an expanding table. -/
theorem selectedTable_good (n : ℕ) : GoodTable (selectedTable n) := by
  obtain ⟨T, hT⟩ := exists_good_table n
  obtain ⟨code, hcode⟩ := decode_surjective n T
  have hsome : ((candidates n).find? fun code => decide (GoodTable (decode n code))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨code, by simp [candidates], by rw [hcode]; exact decide_eq_true hT⟩
  generalize he : (candidates n).find? (fun code => decide (GoodTable (decode n code))) = result at *
  cases result with
  | none => simp at hsome
  | some code =>
      have hc : GoodTable (decode n code) := of_decide_eq_true (List.find?_some (p := fun code => decide (GoodTable (decode n code))) he)
      unfold selectedTable
      rw [he]
      exact hc

/-- A finite inverse scan returns the actual preimage of a bijection. -/
theorem inverse_apply {n : ℕ} (f : Fin n → Fin n) (hf : Function.Bijective f) (v : Fin n) :
    f (inverse f v) = v := by
  obtain ⟨u, hu⟩ := hf.2 v
  have hsome : ((List.finRange n).find? fun u => decide (f u = v)).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨u, by simp, by simpa using hu⟩
  generalize he : (List.finRange n).find? (fun u => decide (f u = v)) = result at *
  cases result with
  | none => simp at hsome
  | some u =>
      have hu : f u = v := of_decide_eq_true (List.find?_some (p := fun u => decide (f u = v)) he)
      simpa [inverse, he] using hu

/-- The inverse scan also reverses an application of the bijection. -/
theorem inverse_apply_eq {n : ℕ} (f : Fin n → Fin n) (hf : Function.Bijective f) (v : Fin n) :
    inverse f (f v) = v := hf.1 (inverse_apply f hf (f v))

/-- An elementary geometric-decay estimate, avoiding evaluation of huge powers. -/
theorem decay (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    (1 - a) ^ k * (1 + (k : ℝ) * a) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hp : 0 ≤ (1 - a) ^ k := pow_nonneg (by linarith) _
      have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      nlinarith [mul_nonneg hp (mul_nonneg (by positivity : (0 : ℝ) ≤ k + 1) ha2)]

/-- The fixed exponent makes the lazy seed spectral bound at most one fifth. -/
theorem powered_bound : (1 - (1 : ℝ) / 1440000) ^ poweringExponent ≤ 1 / 5 := by
  have h := decay ((1 : ℝ) / 1440000) (by positivity) (by norm_num) poweringExponent
  have hc : 1 + (poweringExponent : ℝ) * ((1 : ℝ) / 1440000) = 5 := by
    norm_num [poweringExponent]
  rw [hc] at h
  linarith

end Lax920634Proofs.Seed
