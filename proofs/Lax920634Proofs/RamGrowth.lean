import Lax920634Proofs.RamFill

namespace Lax920634Proofs.RamGrowth

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax920634.ZigZagConstruction RamArithmetic RamExpressions

local notation "b" => Lax920634.SeedSearch.seedDegree ^ 4
attribute [local irreducible] Lax920634.SeedSearch.seedDegree Lax920634.SeedSearch.poweringExponent

def command : Com := .seq
  (.assign "nextstart" (.add (.var "start") (.var "count"))) (.seq
  (.assign "nextcount" (.mul (.var "count") (.lit b))) (.seq
  RamFill.command (.seq
  (.assign "start" (.var "nextstart")) (.seq
  (.assign "count" (.var "nextcount"))
  (.assign "base" (.mul (.var "base") (.lit b)))))))

theorem runs (k off B : ℕ) (σ : Env)
    (hB : off + order k + order (k+1) < B)
    (hseed : SeedTable σ) (hprev : RotationTable k off σ)
    (hstart : σ.vars "start" = off) (hcount : σ.vars "count" = order k)
    (hbase : σ.vars "base" = baseOrder k)
    (hroom : off + order k + order (k+1) ≤ (σ.arrs "table").length) :
    ∃ τ, Run B command σ τ (RamFill.loopCost * order (k+1) + 22) ∧
      SeedTable τ ∧ RotationTable (k+1) (off + order k) τ ∧
      τ.vars "start" = off + order k ∧ τ.vars "count" = order (k+1) ∧
      τ.vars "base" = baseOrder (k+1) ∧
      (∀ x, x ∉ ["j","nextstart","nextcount","start","count","base"] →
        τ.vars x = σ.vars x) ∧ τ.out = σ.out := by
  have hsB : σ.vars "start" < B := by rw [hstart]; omega
  have hnB : σ.vars "count" < B := by rw [hcount]; omega
  have hbB : b < B := (b_le_order (k+1)).trans_lt (by omega)
  have hp : (Expr.add (.var "start") (.var "count")).evalB B σ = some (off+order k) := by
    simpa only [hstart,hcount] using eval_add (evalB_var hsB) (evalB_var hnB)
      (show σ.vars "start"+σ.vars "count" < B by rw [hstart,hcount]; omega)
  let σ₁ := σ.setVar "nextstart" (off+order k)
  have h₁ : Run B (.assign "nextstart" (.add (.var "start") (.var "count"))) σ σ₁ 4 :=
    Run.assign hp
  have hm : (Expr.mul (.var "count") (.lit b)).evalB B σ₁ = some (order (k+1)) := by
    have hc : (Expr.var "count").evalB B σ₁ = some (order k) := by
      simpa only [σ₁,vars_setVar,if_neg (by decide : "count" ≠ "nextstart"),hcount] using
        evalB_var (show σ₁.vars "count" < B by
          simpa only [σ₁,vars_setVar,if_neg (by decide : "count" ≠ "nextstart")] using hnB)
    simpa only [order_succ] using eval_mul hc (evalB_lit hbB)
      (show order k*b < B by rw [← order_succ]; omega)
  let σ₂ := σ₁.setVar "nextcount" (order (k+1))
  have h₂ : Run B (.assign "nextcount" (.mul (.var "count") (.lit b))) σ₁ σ₂ 4 := Run.assign hm
  have hσ₂start : σ₂.vars "start" = off := by
    simp only [σ₂,σ₁,vars_setVar,if_neg (by decide : "start" ≠ "nextcount"),
      if_neg (by decide : "start" ≠ "nextstart"),hstart]
  have hσ₂new : σ₂.vars "nextstart" = off+order k := by
    simp only [σ₂,σ₁,vars_setVar,if_neg (by decide : "nextstart" ≠ "nextcount"),if_true]
  have hσ₂count : σ₂.vars "nextcount" = order (k+1) := by simp only [σ₂,vars_setVar,if_true]
  obtain ⟨ν,hfill,hseedν,hprevν,hvars,hout⟩ := RamFill.runs k off B σ₂ hB
    hseed hprev hσ₂start hσ₂new hσ₂count hroom
  have hνnew : ν.vars "nextstart" = off+order k := (hvars _ (by decide)).trans hσ₂new
  have hνcount : ν.vars "nextcount" = order (k+1) := (hvars _ (by decide)).trans hσ₂count
  have hνbase : ν.vars "base" = baseOrder k := by
    rw [hvars "base" (by decide)]
    simpa only [σ₂,σ₁,vars_setVar,if_neg (by decide : "base" ≠ "nextcount"),
      if_neg (by decide : "base" ≠ "nextstart")] using hbase
  let ν₁ := ν.setVar "start" (off+order k)
  have h₃ : Run B (.assign "start" (.var "nextstart")) ν ν₁ 2 :=
    Run.assign (by simpa only [hνnew] using evalB_var (show ν.vars "nextstart" < B by rw [hνnew]; omega))
  let ν₂ := ν₁.setVar "count" (order (k+1))
  have h₄ : Run B (.assign "count" (.var "nextcount")) ν₁ ν₂ 2 := by
    have hn : ν₁.vars "nextcount" = order (k+1) := by
      simp only [ν₁,vars_setVar,if_neg (by decide : "nextcount" ≠ "start"),hνcount]
    have he : (Expr.var "nextcount").evalB B ν₁ = some (order (k+1)) := by
      simpa only [hn] using evalB_var (show ν₁.vars "nextcount" < B by rw [hn]; omega)
    exact Run.assign he

  have hν₂base : ν₂.vars "base" = baseOrder k := by
    simp only [ν₂,ν₁,vars_setVar,if_neg (by decide : "base" ≠ "count"),
      if_neg (by decide : "base" ≠ "start"),hνbase]
  have hbaselim : baseOrder (k+1) ≤ order (k+1) := Nat.le_mul_of_pos_right _ d_pos
  have hebase : (Expr.mul (.var "base") (.lit b)).evalB B ν₂ = some (baseOrder (k+1)) := by
    have eb : (Expr.var "base").evalB B ν₂ = some (baseOrder k) := by
      simpa only [hν₂base] using evalB_var (show ν₂.vars "base" < B by
        rw [hν₂base]
        have hp : baseOrder k ≤ order k := Nat.le_mul_of_pos_right _ d_pos
        exact hp.trans_lt (by omega))
    simpa only [baseOrder_succ] using eval_mul eb (evalB_lit hbB)
      (show baseOrder k*b < B by rw [← baseOrder_succ]; omega)
  let τ := ν₂.setVar "base" (baseOrder (k+1))
  have h₅ : Run B (.assign "base" (.mul (.var "base") (.lit b))) ν₂ τ 4 := Run.assign hebase
  have hr : Run B command σ τ (RamFill.loopCost * order (k+1) + 22) :=
    (h₁.seq (h₂.seq (hfill.seq (h₃.seq (h₄.seq h₅))))).mono (by omega)
  refine ⟨τ,hr,hseedν,hprevν,?_,?_,?_,?_,?_⟩
  · simp only [τ,ν₂,ν₁,vars_setVar,if_neg (by decide : "start" ≠ "base"),
      if_neg (by decide : "start" ≠ "count"),if_true]
  · simp only [τ,ν₂,vars_setVar,if_neg (by decide : "count" ≠ "base"),if_true]
  · simp only [τ,vars_setVar,if_true]
  · intro x hx
    apply hr.frame_var x
    simp only [command,RamFill.command,RamFill.step,Com.wvars,List.mem_append,
      List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,false_or,or_self] at hx ⊢
    tauto
  · exact hr.out_eq (by simp only [command,RamFill.command,RamFill.step,Com.NoWrite]; trivial)

end Lax920634Proofs.RamGrowth
