import Lax920634Proofs.RamExpressions

namespace Lax920634Proofs.RamInitialize

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile

/-- Emit the literals of one fixed finite table into zeroed RAM storage. -/
def command (a : String) (n : ℕ) (f : ℕ → ℕ) : Com :=
  match n with
  | 0 => .skip
  | n+1 => .seq (command a n f) (.store a (.lit n) (.lit (f n)))

/-- Array extents are preserved by every structured run. -/
theorem array_length {c : Com} {σ τ : Env} {k : ℕ} (h : BigStep c σ τ k) (a : String) :
    (τ.arrs a).length = (σ.arrs a).length := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => simp only [length_arrs_setArr]
  | seq _ _ ih ih' => exact ih'.trans ih
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact ih'.trans ih
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem run_array_length {B K : ℕ} {c : Com} {σ τ : Env} (h : Run B c σ τ K) (a : String) :
    (τ.arrs a).length = (σ.arrs a).length := by
  obtain ⟨_,_,h⟩ := h.bigStep
  exact array_length h a

/-- A prefix initializer includes the cost of every store and preserves all scalars and tapes. -/
theorem runs (a : String) (n : ℕ) (f : ℕ → ℕ) (B : ℕ) (σ : Env)
    (hn : n < B) (hv : ∀ j < n, f j < B) (hroom : n ≤ (σ.arrs a).length) :
    ∃ τ, Run B (command a n f) σ τ (3*n+1) ∧
      (∀ j < n, (τ.arrs a)[j]? = some (f j)) ∧
      τ.vars = σ.vars ∧ τ.inp = σ.inp ∧ τ.out = σ.out ∧
      (∀ a', a' ≠ a → τ.arrs a' = σ.arrs a') := by
  induction n with
  | zero => exact ⟨σ, Run.skip, by simp, rfl,rfl,rfl,fun _ _ => rfl⟩
  | succ n ih =>
    obtain ⟨τ,hr,hprefix,hvars,hin,hout,hother⟩ := ih (by omega)
      (fun j hj => hv j (by omega)) (by omega)
    have hlen := run_array_length hr a
    have hs : Run B (.store a (.lit n) (.lit (f n))) τ (τ.setArr a n (f n)) 3 := by
      simpa only [size_lit] using Run.store (evalB_lit (by omega))
        (evalB_lit (hv n (by omega))) (by omega)
    refine ⟨τ.setArr a n (f n), (hr.seq hs).mono (by omega), ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      simp only [arrs_setArr, if_true]
      by_cases he : n = j
      · subst j
        exact List.getElem?_set_self (by omega)
      · rw [List.getElem?_set_ne he]
        exact hprefix j (by omega)
    · exact hvars
    · exact hin
    · exact hout
    · intro a' hne
      simpa only [arrs_setArr, if_neg hne] using hother a' hne

theorem ok (L : Layout) (a : String) (n : ℕ) (f : ℕ → ℕ)
    (ha : a ∈ L.arrays) (ht : 0 < L.temps) : Com.Ok L (command a n f) := by
  induction n with
  | zero => exact Com.ok_skip L
  | succ n ih => exact ⟨ih,ha,Expr.ok_lit _ _ _,Expr.ok_lit _ _ _,ht⟩

end Lax920634Proofs.RamInitialize
