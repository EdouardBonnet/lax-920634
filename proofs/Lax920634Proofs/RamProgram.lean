import Lax920634Proofs.RamIteration

namespace Lax920634Proofs.RamProgram

set_option maxHeartbeats 600000

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax920634.ZigZagConstruction Lax920634.GraphEncoding RamArithmetic RamExpressions RamIteration

local notation "D" => Lax920634.SeedSearch.seedDegree
local notation "b" => Lax920634.SeedSearch.seedDegree ^ 4
attribute [local irreducible] Lax920634.SeedSearch.seedDegree Lax920634.SeedSearch.poweringExponent

def seedEntry (j : ℕ) : ℕ := pack D (seedValue (j/D,j%D))

def prelude : Com := .seq (.read "request") (.seq
  (.assign "target" (.mul (.var "request") (.lit 2))) (.seq
  (.assign "base" (.lit b)) (.seq
  (.assign "count" (.lit (order 0))) (.seq
  (.assign "start" (.lit 0)) (.seq
  (RamInitialize.command "seed" (b*D) seedEntry)
  (RamInitialize.command "table" (order 0) (matchingNeighbor 0)))))))

def command : Com := .seq prelude (.seq RamIteration.command RamOutput.command)

def layout : Layout where
  scalars := ["request","target","base","count","start","nextstart","nextcount","j"]
  arrays := ["seed","table"]
  temps := 64

/-- One fixed finite RAM program, independent of the request and word width. -/
def program : Lax808846.Ram.Program := compileProgram layout command

theorem seedEntry_bounds (j : ℕ) (hj : j < b*D) : seedEntry j < b*D := by
  have hx : j/D < b := (Nat.div_lt_iff_lt_mul D_pos).2 hj
  have hi : j%D < D := Nat.mod_lt _ D_pos
  have h := seed_bounds _ _ hx hi
  exact pack_lt h.1 h.2

theorem seedEntry_at (v i : ℕ) (hi : i < D) : seedEntry (v*D+i) = pack D (seedValue (v,i)) := by
  have he : ((v*D+i)/D,(v*D+i)%D) = (v,i) := by
    simpa only [pack,Nat.mul_comm,Nat.add_comm] using unpack_pack D_pos (v,i) hi
  unfold seedEntry
  rw [he]

theorem prelude_ok : Com.Ok layout prelude := by
  have hs := RamInitialize.ok layout "seed" (b*D) seedEntry (by decide) (by decide)
  have hg := RamInitialize.ok layout "table" (order 0) (matchingNeighbor 0) (by decide) (by decide)
  exact ⟨by simp [Com.Ok,layout], by simp [Com.Ok,Expr.Ok,layout],
    by simp [Com.Ok,Expr.Ok,layout], by simp [Com.Ok,Expr.Ok,layout],
    by simp [Com.Ok,Expr.Ok,layout],hs,hg⟩

theorem ok : Com.Ok layout command := by
  refine ⟨prelude_ok,?_,?_⟩
  · simp [RamIteration.command,RamIteration.test,RamGrowth.command,RamFill.command,RamFill.step,
      Com.Ok,Cond.Ok,condExpr,Expr.Ok,layout,nextRow,seedLookup,previousLookup,lookup,rem]
  · simp [RamOutput.command,RamOutput.scan,RamOutput.step,Com.Ok,Cond.Ok,condExpr,Expr.Ok,layout]

theorem prelude_runs (n : ℕ) :
    ∃ ext τ, Run (bound n) prelude (initEnv ext [n]) τ (6*N n+13) ∧ Invariant n τ := by
  let ext := fun _ : String => 2*N n
  let σ := initEnv ext [n]
  have hN0 : order 0 ≤ N n := order_mono (Nat.zero_le _)
  have hNpos := order_pos (selectedLevel n)
  change 0 < N n at hNpos
  have hn := Sizes.request_le_order n
  change n ≤ N n at hn
  have hnB : n < bound n := by unfold bound; omega
  have htwoB : 2*n < bound n := by unfold bound; omega
  have hN0B : order 0 < bound n := by unfold bound; omega
  have hbB : b < bound n := (b_le_order 0).trans_lt hN0B
  have hseedlen : b*D ≤ N n := (seed_size_le_order 0).trans hN0
  have hseedB : b*D < bound n := by unfold bound; omega
  let σ₁ : Env := {σ.setVar "request" n with inp := []}
  have hread : Run (bound n) (.read "request") σ σ₁ 1 := Run.read rfl
  have erequest : (Expr.var "request").evalB (bound n) σ₁ = some n := by
    exact evalB_var (σ := σ₁) (x := "request") hnB
  have etarget : (Expr.mul (.var "request") (.lit 2)).evalB (bound n) σ₁ = some (2*n) := by
    have h := eval_mul erequest (evalB_lit (show 2 < bound n by unfold bound; omega))
      (show n*2 < bound n by simpa only [Nat.mul_comm] using htwoB)
    simpa only [Nat.mul_comm] using h
  let σ₂ := σ₁.setVar "target" (2*n)
  have ht : Run (bound n) (.assign "target" (.mul (.var "request") (.lit 2))) σ₁ σ₂ 4 := by
    exact Run.assign etarget
  let σ₃ := σ₂.setVar "base" b
  have hb : Run (bound n) (.assign "base" (.lit b)) σ₂ σ₃ 2 := Run.assign (evalB_lit hbB)
  let σ₄ := σ₃.setVar "count" (order 0)
  have hc : Run (bound n) (.assign "count" (.lit (order 0))) σ₃ σ₄ 2 := Run.assign (evalB_lit hN0B)
  let σ₅ := σ₄.setVar "start" 0
  have hs : Run (bound n) (.assign "start" (.lit 0)) σ₄ σ₅ 2 :=
    Run.assign (evalB_lit (by unfold bound; omega))
  obtain ⟨ν,hseedRun,hseed,hvars₁,hin₁,hout₁,hother₁⟩ :=
    RamInitialize.runs "seed" (b*D) seedEntry (bound n) σ₅ hseedB
      (fun j hj => (seedEntry_bounds j hj).trans hseedB)
      (by change b*D ≤ (List.replicate (2*N n) 0).length; rw [List.length_replicate]; omega)
  have hνtable : (ν.arrs "table").length = 2*N n := by
    rw [hother₁ "table" (by decide)]
    change (List.replicate (2*N n) 0).length = 2*N n
    exact List.length_replicate
  obtain ⟨τ,hgraphRun,hgraph,hvars₂,hin₂,hout₂,hother₂⟩ :=
    RamInitialize.runs "table" (order 0) (matchingNeighbor 0) (bound n) ν hN0B
      (fun j hj => (matching_bounds 0 j hj).trans hN0B)
      (by rw [hνtable]; omega)
  have hr : Run (bound n) prelude σ τ (6*N n+13) :=
    (hread.seq (ht.seq (hb.seq (hc.seq (hs.seq (hseedRun.seq hgraphRun)))))).mono (by omega)
  have hvars : τ.vars = σ₅.vars := hvars₂.trans hvars₁
  have hseedτ : SeedTable τ := by
    intro v hv i hi
    rw [hother₂ "seed" (by decide)]
    have hindex : v*D+i < b*D := by
      simpa only [pack,Nat.mul_comm,Nat.add_comm] using pack_lt (p := (v,i)) hv hi
    simpa only [seedEntry_at v i hi] using hseed (v*D+i) hindex
  have hT : RotationTable 0 (offset 0) τ := by
    intro j hj
    simpa only [offset,Nat.zero_add] using hgraph j hj
  have hroom : (τ.arrs "table").length = 2*N n :=
    (RamInitialize.run_array_length hgraphRun _).trans hνtable
  refine ⟨ext,τ,hr,0,Nat.zero_le _,hseedτ,hT,?_,?_,?_,?_,hroom,?_⟩
  · rw [hvars]
    simp only [σ₅,vars_setVar,if_true,offset]
  · rw [hvars]
    simp only [σ₅,σ₄,vars_setVar,if_neg (by decide : "count" ≠ "start"),if_true]
  · rw [hvars]
    simp only [σ₅,σ₄,σ₃,vars_setVar,if_neg (by decide : "base" ≠ "start"),
      if_neg (by decide : "base" ≠ "count"),if_true,baseOrder,Nat.zero_add,pow_one]
  · rw [hvars]
    simp only [σ₅,σ₄,σ₃,σ₂,vars_setVar,if_neg (by decide : "target" ≠ "start"),
      if_neg (by decide : "target" ≠ "count"),if_neg (by decide : "target" ≠ "base"),if_true]
  · exact hout₂.trans hout₁

end Lax920634Proofs.RamProgram
