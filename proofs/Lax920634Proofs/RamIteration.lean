import Lax920634Proofs.RamOutput

namespace Lax920634Proofs.RamIteration

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax920634.ZigZagConstruction Lax920634.GraphEncoding RamArithmetic RamExpressions

local notation "b" => Lax920634.SeedSearch.seedDegree ^ 4
attribute [local irreducible] Lax920634.SeedSearch.seedDegree Lax920634.SeedSearch.poweringExponent

def offset : ℕ → ℕ
  | 0 => 0
  | k+1 => offset k + order k

def N (n : ℕ) : ℕ := order (selectedLevel n)

def bound (n : ℕ) : ℕ := 16*(N n+1)

def coefficient : ℕ := 2*(RamFill.loopCost+30)

def test : Cond := .lt (.var "base") (.var "target")

def command : Com := .while test RamGrowth.command

def Invariant (n : ℕ) (σ : Env) : Prop :=
  ∃ k, k ≤ selectedLevel n ∧ SeedTable σ ∧ RotationTable k (offset k) σ ∧
    σ.vars "start" = offset k ∧ σ.vars "count" = order k ∧
    σ.vars "base" = baseOrder k ∧ σ.vars "target" = 2*n ∧
    (σ.arrs "table").length = 2*N n ∧ σ.out = []

theorem offset_le (k : ℕ) : offset k ≤ order k := by
  induction k with
  | zero => simp only [offset]; omega
  | succ k ih =>
    rw [offset,order_succ]
    have h := Nat.mul_le_mul_left (order k) b_ge_two
    omega

theorem twice_order_le (k : ℕ) : 2*order k ≤ order (k+1) := by
  rw [order_succ]
  have h := Nat.mul_le_mul_left (order k) b_ge_two
  simpa only [Nat.mul_comm] using h

theorem stage_room (n k : ℕ) (hk : k+1 ≤ selectedLevel n) :
    offset k + order k + order (k+1) ≤ 2*N n := by
  have ho := offset_le (k+1)
  have hn : order (k+1) ≤ N n := order_mono hk
  rw [offset] at ho
  omega

/-- A geometric increase pays for the next table and the loop's control instructions. -/
theorem amortized (c total old new : ℕ) (hdouble : 2*old ≤ new)
    (hnew : new ≤ total) (hpos : 0 < new) :
    4 + (c*new+22) + 2*(c+30)*(total-new) ≤ 2*(c+30)*(total-old) := by
  have hold : old ≤ total := by omega
  have h₁ := Nat.sub_add_cancel hnew
  have h₂ := Nat.sub_add_cancel hold
  nlinarith

theorem runs (n : ℕ) (σ : Env) (hI : Invariant n σ) :
    ∃ τ, Run (bound n) command σ τ (coefficient*N n+4) ∧
      SeedTable τ ∧ RotationTable (selectedLevel n) (offset (selectedLevel n)) τ ∧
      τ.vars "start" = offset (selectedLevel n) ∧ τ.vars "count" = N n ∧ τ.out = [] := by
  let Φ := fun σ : Env => coefficient*(N n-σ.vars "count")
  have hdef : ∀ ρ, Invariant n ρ → ∃ v, test.evalB (bound n) ρ = some v := by
    rintro ρ ⟨k,hk,hseed,hT,hs,hc,hb,ht,hlen,ho⟩
    have hn : order k ≤ N n := order_mono hk
    have hbase : baseOrder k ≤ order k := Nat.le_mul_of_pos_right _ d_pos
    have hrequest := Sizes.request_le_order n
    change n ≤ N n at hrequest
    exact evalB_condLt_vars (by rw [hb]; unfold bound; omega)
      (by rw [ht]; unfold bound; omega)
  have hstep : ∀ ρ, Invariant n ρ → test.evalB (bound n) ρ = some true →
      ∃ ρ' K, Run (bound n) RamGrowth.command ρ ρ' K ∧ Invariant n ρ' ∧
        1+test.size+K+Φ ρ' ≤ Φ ρ := by
    rintro ρ ⟨k,hk,hseed,hT,hs,hc,hb,ht,hlen,ho⟩ hv
    have hsmall : baseOrder k < 2*n := by
      have h := lt_of_condLt_true hv
      simpa only [hb,ht] using h
    have hk' : k+1 ≤ selectedLevel n := by
      have hlarge := Sizes.request_le_baseOrder n
      by_contra h
      have he : k = selectedLevel n := by omega
      rw [he] at hsmall
      omega
    have hroom := stage_room n k hk'
    have hB : offset k + order k + order (k+1) < bound n := by unfold bound; omega
    obtain ⟨ρ',hr,hseed',hT',hs',hc',hb',hframe,hout⟩ := RamGrowth.runs k (offset k) (bound n)
      ρ hB hseed hT hs hc hb (by rw [hlen]; exact hroom)
    have htarget : ρ'.vars "target" = 2*n :=
      (hframe "target" (by decide)).trans ht
    have hlen' : (ρ'.arrs "table").length = 2*N n := (RamInitialize.run_array_length hr _).trans hlen
    have hI' : Invariant n ρ' := ⟨k+1,hk',hseed',hT',hs',hc',hb',htarget,hlen',hout.trans ho⟩
    refine ⟨ρ',RamFill.loopCost*order (k+1)+22,hr,hI',?_⟩
    have hnew : order (k+1) ≤ N n := order_mono hk'
    simpa only [Φ,coefficient,hc,hc',test,size_condLt,size_var,Nat.reduceAdd]
      using amortized RamFill.loopCost (N n) (order k) (order (k+1)) (twice_order_le k) hnew (order_pos _)
  obtain ⟨τ,K,hr,hI',hfalse,hcost⟩ := Run.while_potential (Invariant n) Φ hdef hstep hI
  obtain ⟨k,hk,hseed,hT,hs,hc,hb,ht,hlen,ho⟩ := hI'
  have he : k = selectedLevel n := by
    have hlarge : 2*n ≤ baseOrder k := by
      have h := le_of_condLt_false hfalse
      simpa only [hb,ht] using h
    by_contra h
    have hsmall := first_level_min n k (by omega)
    omega
  subst k
  refine ⟨τ,hr.mono ?_,hseed,hT,hs,hc,ho⟩
  have hp : Φ σ ≤ coefficient*N n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  change K + Φ τ ≤ Φ σ + 4 at hcost
  omega

end Lax920634Proofs.RamIteration
