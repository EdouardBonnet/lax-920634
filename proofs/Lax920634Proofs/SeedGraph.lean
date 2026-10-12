import Lax920634Proofs.Seed
import Lax920634.SeedCorrectness
import Lax920634.SeedRotation
import Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.TowerFin

namespace Lax920634Proofs.SeedGraph

set_option maxHeartbeats 300000

open Lax920634.SeedSearch Lax920634.SeedRotation
open Lax323828Proofs.PCPFoundation.Complexity

/-- The selected table rows, equipped with their computed inverses. -/
def permutations (n : ℕ) (i : Fin 30) : Equiv.Perm (Fin n) where
  toFun := selectedTable n i
  invFun := inverse (selectedTable n i)
  left_inv := Seed.inverse_apply_eq _ ((Lax920634.SeedCorrectness.table_good n).1 i)
  right_inv := Seed.inverse_apply _ ((Lax920634.SeedCorrectness.table_good n).1 i)

/-- The semantic lazy permutation graph, with the same numbered rotation. -/
noncomputable def lazyGraph (n : ℕ) : RegGraph :=
  ((RegGraph.permsGraph (by norm_num : 0 < 30) (permutations n)).padLoops 60).relabel lazyLabels

/-- The executable lazy rotation is precisely the semantic rotation. -/
theorem lazyRotation_eq (n : ℕ) : lazyRotation n = (lazyGraph n).rot := by
  funext p
  dsimp only [lazyRotation, lazyGraph, RegGraph.relabel, RegGraph.padLoops,
    RegGraph.permsGraph, RegGraph.permsRot, permutations]
  cases he : lazyLabels.symm p.2 with
  | inl ib =>
    rcases ib with ⟨i, b⟩
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> rfl
  | inr j => rfl

/-- The semantic and executable escape counts are equal. -/
theorem escape_eq (n : ℕ) (i : Fin 30) (S : Finset (Fin n)) :
    Lax323828Proofs.PCPFoundation.Complexity.escape (permutations n i) S =
      Lax920634.SeedSearch.escape (selectedTable n i) S := by
  unfold Lax323828Proofs.PCPFoundation.Complexity.escape Lax920634.SeedSearch.escape
  congr 1

/-- Lazy permutation graphs satisfy the fixed rational spectral bound. -/
theorem spectral_lazy_permutations (n : ℕ) (σ : Fin 30 → Equiv.Perm (Fin n))
    (hesc : ∀ S : Finset (Fin n), 2 * S.card ≤ n → ∃ i, S.card ≤ 10 *
      Lax323828Proofs.PCPFoundation.Complexity.escape (σ i) S) :
    ((RegGraph.permsGraph (by norm_num : 0 < 30) σ).padLoops 60).SpectralBound
      (1 - (1 : ℝ) / 1440000) := by
  have he := RegGraph.edgeExpansion_permsGraph (by norm_num : 0 < 30) σ 10 (by norm_num) hesc
  have hs := RegGraph.spectralBound_padLoops_of_edgeExpansion _ he (by norm_num)
  have hd : (RegGraph.permsGraph (by norm_num : 0 < 30) σ).deg = 60 := RegGraph.deg_permsGraph _ _
  rw [hd] at hs
  have hq : 1 - (1 / (2 * ((10 : ℕ) : ℝ) * ((30 : ℕ) : ℝ))) ^ 2 / 4 =
      1 - 1 / 1440000 := by norm_num
  rw [hq] at hs
  exact hs

/-- The lazy seed has spectral bound `1 - 1/1440000`. -/
theorem spectral_lazyGraph (n : ℕ) :
    (lazyGraph n).SpectralBound (1 - (1 : ℝ) / 1440000) := by
  have hesc (S : Finset (Fin n)) (hS : 2 * S.card ≤ n) :
      ∃ i, S.card ≤ 10 * Lax323828Proofs.PCPFoundation.Complexity.escape (permutations n i) S := by
    obtain ⟨i, hi⟩ := (Lax920634.SeedCorrectness.table_good n).2 S hS
    refine ⟨i, ?_⟩
    rw [escape_eq]
    exact hi
  unfold lazyGraph
  apply RegGraph.spectralBound_relabel
  exact spectral_lazy_permutations n (permutations n) hesc

/-- The semantic powered seed, with sequences numbered in base 120. -/
noncomputable def poweredGraph (n t : ℕ) : RegGraph :=
  ((lazyGraph n).power t).relabel finFunctionFinEquiv

/-- The executable path endpoint agrees with the semantic endpoint. -/
theorem walkEnd_eq (n t : ℕ) (v : Fin n) (s : Fin t → Fin 120) :
    walkEnd (lazyRotation n) t v s = (lazyGraph n).walkEnd t v s := by
  induction t generalizing v with
  | zero => rfl
  | succ t ih =>
    simp only [walkEnd, RegGraph.walkEnd, RegGraph.nbr, ← lazyRotation_eq]
    exact ih _ _

/-- The executable path trajectory agrees with the semantic trajectory. -/
theorem walkAt_eq (n t : ℕ) (v : Fin n) (s : Fin t → Fin 120) (k : ℕ) :
    walkAt (lazyRotation n) t v s k = (lazyGraph n).walkAt t v s k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [walkAt, RegGraph.walkAt, RegGraph.nbr, ← lazyRotation_eq, ih]
    rfl

/-- The executable powered rotation is the rotation analyzed by the spectral proof. -/
theorem powerRotation_eq (n t : ℕ) :
    powerRotation (lazyRotation n) t = (poweredGraph n t).rot := by
  funext p
  change (walkEnd (lazyRotation n) t p.1 (finFunctionFinEquiv.symm p.2),
    finFunctionFinEquiv (fun j => (lazyRotation n
      (walkAt (lazyRotation n) t p.1 (finFunctionFinEquiv.symm p.2)
        (Fin.rev j).val, finFunctionFinEquiv.symm p.2 (Fin.rev j))).2)) =
    ((lazyGraph n).walkEnd t p.1 (finFunctionFinEquiv.symm p.2),
      finFunctionFinEquiv ((lazyGraph n).revWalk p.1 (finFunctionFinEquiv.symm p.2)))
  rw [walkEnd_eq]
  apply Prod.ext
  · rfl
  · change finFunctionFinEquiv (fun j => (lazyRotation n
      (walkAt (lazyRotation n) t p.1 (finFunctionFinEquiv.symm p.2)
        (Fin.rev j).val, finFunctionFinEquiv.symm p.2 (Fin.rev j))).2) =
        finFunctionFinEquiv ((lazyGraph n).revWalk p.1 (finFunctionFinEquiv.symm p.2))
    apply congrArg finFunctionFinEquiv
    funext j
    rw [walkAt_eq, lazyRotation_eq]
    rfl

/-- The executable powered rotation is an involution. -/
theorem powerRotation_involutive (n t : ℕ) :
    Function.Involutive (powerRotation (lazyRotation n) t) := by
  rw [powerRotation_eq]
  exact (poweredGraph n t).rot_involutive

/-- The executable numbered powered seed has the established spectral bound. -/
theorem spectral_powerRotation (n t : ℕ) :
    (RegGraph.ofRot (120 ^ t) (pow_pos (by norm_num : 0 < 120) _) n
      (powerRotation (lazyRotation n) t) (powerRotation_involutive n t)).SpectralBound
      ((1 - (1 : ℝ) / 1440000) ^ t) := by
  have hs := RegGraph.spectralBound_relabel _ finFunctionFinEquiv
    (RegGraph.spectralBound_power _ (spectral_lazyGraph n) t)
  have he : RegGraph.ofRot (120 ^ t) (pow_pos (by norm_num : 0 < 120) _) n
      (powerRotation (lazyRotation n) t) (powerRotation_involutive n t) = poweredGraph n t := by
    let make : {R : Fin n × Fin (120 ^ t) → Fin n × Fin (120 ^ t) // Function.Involutive R} →
        RegGraph := fun r => RegGraph.ofRot (120 ^ t) (pow_pos (by norm_num : 0 < 120) _) n r.val r.property
    have hr : (⟨powerRotation (lazyRotation n) t, powerRotation_involutive n t⟩ :
        {R : Fin n × Fin (120 ^ t) → Fin n × Fin (120 ^ t) // Function.Involutive R}) =
        ⟨(poweredGraph n t).rot, (poweredGraph n t).rot_involutive⟩ :=
      Subtype.ext (powerRotation_eq n t)
    have h := congrArg make hr
    exact h.trans (by rfl)
  rw [he]
  exact hs

/-- The semantic seed is a numbered base for the proved zig-zag tower. -/
noncomputable def finBase : FinBase where
  deg := seedDegree
  deg_pos := pow_pos (by norm_num : 0 < 120) _
  rot := rotation
  rot_involutive := powerRotation_involutive seedOrder poweringExponent
  lam := (1 - (1 : ℝ) / 1440000) ^ poweringExponent
  lam_nonneg := pow_nonneg (by norm_num) _
  lam_le := Seed.powered_bound
  spectral := spectral_powerRotation seedOrder poweringExponent

end Lax920634Proofs.SeedGraph
