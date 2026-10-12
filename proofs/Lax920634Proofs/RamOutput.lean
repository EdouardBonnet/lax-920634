import Lax920634Proofs.RamGrowth

namespace Lax920634Proofs.RamOutput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax920634.ZigZagConstruction RamArithmetic RamExpressions

attribute [local irreducible] Lax920634.SeedSearch.seedDegree Lax920634.SeedSearch.poweringExponent

def step : Com := .seq (.write (.get "table" (.add (.var "start") (.var "j"))))
  (.assign "j" (.add (.var "j") (.lit 1)))

def scan : Com := .seq (.assign "j" (.lit 0))
  (.while (.lt (.var "j") (.var "count")) step)

def command : Com := .seq (.write (.var "count")) scan

def Invariant (k off : ℕ) (out : List ℕ) (σ : Env) : Prop :=
  RotationTable k off σ ∧ σ.vars "start" = off ∧ σ.vars "count" = order k ∧
  σ.vars "j" ≤ order k ∧
  σ.out = out ++ (List.range (σ.vars "j")).map (matchingNeighbor k)

theorem step_spec (k off B : ℕ) (out : List ℕ) (hB : off+order k < B) :
    Spec B (fun σ => Invariant k off out σ ∧ σ.vars "j" < order k) step
      (fun σ τ => Invariant k off out τ ∧ τ.vars "j" = σ.vars "j"+1) 9 := by
  rintro σ ⟨⟨hT,hs,hc,hj,ho⟩,hlt⟩
  let j := σ.vars "j"
  have hjB : j < B := by dsimp [j]; omega
  have hsB : σ.vars "start" < B := by rw [hs]; omega
  have heget : (Expr.get "table" (.add (.var "start") (.var "j"))).evalB B σ =
      some (matchingNeighbor k j) := by
    apply evalB_get
    · simpa only [hs] using eval_add (evalB_var hsB) (evalB_var hjB)
        (show σ.vars "start"+j < B by rw [hs]; omega)
    · exact hT j hlt
    · exact (matching_bounds k j hlt).trans (by omega)
  let ν : Env := {σ with out := σ.out ++ [matchingNeighbor k j]}
  have hw : Run B (.write (.get "table" (.add (.var "start") (.var "j")))) σ ν 5 :=
    Run.write heget
  have hi : Run B (.assign "j" (.add (.var "j") (.lit 1))) ν (ν.setVar "j" (j+1)) 4 :=
    Run.assign (eval_add (evalB_var hjB) (evalB_lit (by have := order_pos k; omega)) (by omega))
  refine ⟨ν.setVar "j" (j+1),hw.seq hi,?_,?_⟩
  · refine ⟨hT,?_,?_,?_,?_⟩
    · simpa only [ν,vars_setVar,if_neg (by decide : "start" ≠ "j")] using hs
    · simpa only [ν,vars_setVar,if_neg (by decide : "count" ≠ "j")] using hc
    · simp only [vars_setVar,if_true]; dsimp [j]; omega
    · simp only [ν,Env.setVar,vars_setVar,if_true]
      rw [ho]
      simp only [List.range_succ,List.map_append,List.map_singleton,List.append_assoc]
      rfl
  · simp only [vars_setVar,if_true]; rfl

theorem scan_runs (k off B : ℕ) (σ : Env) (hB : off+order k < B)
    (hT : RotationTable k off σ) (hs : σ.vars "start" = off)
    (hc : σ.vars "count" = order k) :
    ∃ τ, Run B scan σ τ (13*order k+6) ∧
      τ.out = σ.out ++ (List.range (order k)).map (matchingNeighbor k) := by
  have hloop := Spec.forRangeZero "j" "count" (Invariant k off σ.out) (order k) 9
    (by omega) (fun _ h => h.2.2.2.1) (fun _ h => h.2.2.1) (step_spec k off B σ.out hB)
  have hinit : Invariant k off σ.out (σ.setVar "j" 0) := by
    refine ⟨hT,?_,?_,?_,?_⟩
    · simpa only [vars_setVar,if_neg (by decide : "start" ≠ "j")] using hs
    · simpa only [vars_setVar,if_neg (by decide : "count" ≠ "j")] using hc
    · simp only [vars_setVar,if_true]; omega
    · simp only [Env.setVar,vars_setVar,if_true,List.range_zero,List.map_nil,List.append_nil]
  obtain ⟨τ,hr,hI,hj⟩ := hloop σ hinit
  exact ⟨τ,hr,by simpa only [hj] using hI.2.2.2.2⟩

theorem runs (k off B : ℕ) (σ : Env) (hB : off+order k < B)
    (hT : RotationTable k off σ) (hs : σ.vars "start" = off)
    (hc : σ.vars "count" = order k) :
    ∃ τ, Run B command σ τ (13*order k+8) ∧ τ.out = σ.out ++ Lax920634.WordEncoding.table k := by
  let ν : Env := {σ with out := σ.out ++ [order k]}
  have hw : Run B (.write (.var "count")) σ ν 2 := Run.write
    (by simpa only [hc] using evalB_var (show σ.vars "count" < B by rw [hc]; omega))
  obtain ⟨τ,hr,ho⟩ := scan_runs k off B ν hB hT hs hc
  refine ⟨τ,(hw.seq hr).mono (by omega),?_⟩
  simpa only [ν,Lax920634.WordEncoding.table,List.append_assoc,List.singleton_append] using ho

end Lax920634Proofs.RamOutput
