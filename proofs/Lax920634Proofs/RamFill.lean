import Lax920634Proofs.RamInitialize
import Lax808846Proofs.Spec

namespace Lax920634Proofs.RamFill

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax920634.ZigZagConstruction RamArithmetic RamExpressions

attribute [local irreducible] Lax920634.SeedSearch.seedDegree Lax920634.SeedSearch.poweringExponent

/-- One new row, then advance the row counter. -/
def step : Com := .seq
  (.store "table" (.add (.var "nextstart") (.var "j")) nextRow)
  (.assign "j" (.add (.var "j") (.lit 1)))

def command : Com := .seq (.assign "j" (.lit 0))
  (.while (.lt (.var "j") (.var "nextcount")) step)

def rowCost : ℕ := 8 + nextRow.size

def loopCost : ℕ := rowCost + 4

def Invariant (k off : ℕ) (σ : Env) : Prop :=
  SeedTable σ ∧ RotationTable k off σ ∧
  σ.vars "start" = off ∧
  σ.vars "nextstart" = off + order k ∧
  σ.vars "nextcount" = order (k+1) ∧
  σ.vars "j" ≤ order (k+1) ∧
  (∀ j < σ.vars "j", (σ.arrs "table")[off + order k + j]? =
    some (matchingNeighbor (k+1) j)) ∧
  off + order k + order (k+1) ≤ (σ.arrs "table").length

theorem step_spec (k off B : ℕ) (hB : off + order k + order (k+1) < B) :
    Spec B (fun σ => Invariant k off σ ∧ σ.vars "j" < order (k+1)) step
      (fun σ τ => Invariant k off τ ∧ τ.vars "j" = σ.vars "j"+1) rowCost := by
  rintro σ ⟨⟨hseed,hprev,hstart,hnewstart,hcount,hj,hfilled,hroom⟩,hlt⟩
  let j := σ.vars "j"
  have hjB : j < B := by dsimp [j]; omega
  have he := nextRow_eval (B := B) k off j hseed hprev hstart rfl hlt (by omega)
  have hindex : (Expr.add (.var "nextstart") (.var "j")).evalB B σ =
      some (off + order k + j) := by
    have h := eval_add (evalB_var (show σ.vars "nextstart" < B by rw [hnewstart]; omega))
      (evalB_var hjB) (show σ.vars "nextstart" + j < B by rw [hnewstart]; omega)
    simpa only [hnewstart] using h
  let ν := σ.setArr "table" (off + order k + j) (matchingNeighbor (k+1) j)
  have hs : Run B (.store "table" (.add (.var "nextstart") (.var "j")) nextRow) σ ν
      (4 + nextRow.size) := by
    exact Run.store hindex he (by omega)
  have hi : Run B (.assign "j" (.add (.var "j") (.lit 1))) ν (ν.setVar "j" (j+1)) 4 := by
    exact Run.assign (eval_add (evalB_var hjB) (evalB_lit (by omega)) (by
      have := order_pos (k+1); omega))
  have hp : RotationTable k off ν := by
    intro q hq
    simp only [ν, arrs_setArr, if_true]
    rw [List.getElem?_set_ne (show off + order k + j ≠ off + q by omega)]
    exact hprev q hq
  have hf : ∀ q < j+1, (ν.arrs "table")[off + order k + q]? =
      some (matchingNeighbor (k+1) q) := by
    intro q hq
    simp only [ν, arrs_setArr, if_true]
    by_cases heq : q = j
    · subst q
      exact List.getElem?_set_self (by omega)
    · rw [List.getElem?_set_ne (show off + order k + j ≠ off + order k + q by omega)]
      exact hfilled q (by omega)
  refine ⟨ν.setVar "j" (j+1), (hs.seq hi).mono (by unfold rowCost; omega), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [SeedTable,ν,arrs_setVar,arrs_setArr,if_neg (by decide : "seed" ≠ "table")] using hseed
    · simpa only [RotationTable,arrs_setVar] using hp
    · simpa only [ν,vars_setVar,vars_setArr,if_neg (by decide : "start" ≠ "j")] using hstart
    · simpa only [ν,vars_setVar,vars_setArr,if_neg (by decide : "nextstart" ≠ "j")] using hnewstart
    · simpa only [ν,vars_setVar,vars_setArr,if_neg (by decide : "nextcount" ≠ "j")] using hcount
    · simp only [vars_setVar,if_true]; dsimp [j]; omega
    · simpa only [vars_setVar,if_true,arrs_setVar] using hf
    · simpa only [ν,arrs_setVar,length_arrs_setArr] using hroom
  · simp only [ν,vars_setVar,if_true]; rfl

theorem runs (k off B : ℕ) (σ : Env)
    (hB : off + order k + order (k+1) < B)
    (hseed : SeedTable σ) (hprev : RotationTable k off σ)
    (hstart : σ.vars "start" = off)
    (hnewstart : σ.vars "nextstart" = off + order k)
    (hcount : σ.vars "nextcount" = order (k+1))
    (hroom : off + order k + order (k+1) ≤ (σ.arrs "table").length) :
    ∃ τ, Run B command σ τ (loopCost * order (k+1) + 6) ∧
      SeedTable τ ∧ RotationTable (k+1) (off + order k) τ ∧
      (∀ x, x ≠ "j" → τ.vars x = σ.vars x) ∧
      τ.out = σ.out := by
  have hloop := Spec.forRangeZero "j" "nextcount" (Invariant k off) (order (k+1)) rowCost
    (by omega) (fun _ h => h.2.2.2.2.2.1) (fun _ h => h.2.2.2.2.1) (step_spec k off B hB)
  have hinit : Invariant k off (σ.setVar "j" 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hseed
    · exact hprev
    · simpa only [vars_setVar,if_neg (by decide : "start" ≠ "j")] using hstart
    · simpa only [vars_setVar,if_neg (by decide : "nextstart" ≠ "j")] using hnewstart
    · simpa only [vars_setVar,if_neg (by decide : "nextcount" ≠ "j")] using hcount
    · simp only [vars_setVar,if_true]; omega
    · simp only [vars_setVar,if_true]; intro q hq; omega
    · exact hroom
  obtain ⟨τ,hr,hI,hj⟩ := hloop σ hinit
  refine ⟨τ,hr,hI.1,?_,?_,?_⟩
  · intro q hq
    exact hI.2.2.2.2.2.2.1 q (hj ▸ hq)
  · intro x hx
    apply hr.frame_var x
    simpa only [command,step,Com.wvars,List.mem_append,List.mem_cons,List.mem_singleton,
      List.not_mem_nil,or_false,false_or,or_self] using hx
  · exact hr.out_eq (by simp only [command,step,Com.NoWrite]; trivial)

end Lax920634Proofs.RamFill
