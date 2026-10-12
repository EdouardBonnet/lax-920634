import Lax920634Proofs.RamProgram
import Lax920634.LinearConstruction

namespace Lax920634Proofs.RamLinear

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Transfer Lax808846Proofs.Simulation
open Lax920634.ZigZagConstruction Lax920634.GraphEncoding
open RamArithmetic RamIteration RamProgram

attribute [local irreducible] Lax920634.SeedSearch.seedDegree Lax920634.SeedSearch.poweringExponent

def timeConstant : ℕ := 10*(coefficient+44)+1

def wordConstant : ℕ := 128

/-- The verified fixed syntax gives this explicit RAM instruction coefficient. -/
theorem timeConstant_value : timeConstant = 25381 := by rfl

theorem structured_runs (n : ℕ) :
    ∃ ext τ, Run (bound n) RamProgram.command (initEnv ext [n]) τ ((coefficient+44)*(N n+1)) ∧
      τ.out = Lax920634.WordEncoding.construct n := by
  obtain ⟨ext,σ,hpre,hI⟩ := prelude_runs n
  obtain ⟨ν,hloop,hseed,hT,hstart,hcount,hout⟩ := RamIteration.runs n σ hI
  have hB : offset (selectedLevel n)+order (selectedLevel n) < bound n := by
    have h := offset_le (selectedLevel n)
    change offset (selectedLevel n) ≤ N n at h
    change offset (selectedLevel n)+N n < 16*(N n+1)
    omega
  obtain ⟨τ,houtput,ho⟩ := RamOutput.runs (selectedLevel n) (offset (selectedLevel n)) (bound n)
    ν hB hT hstart hcount
  refine ⟨ext,τ,(hpre.seq (hloop.seq houtput)).mono ?_,?_⟩
  · change 6*N n+13+(coefficient*N n+4+(13*N n+8)) ≤ (coefficient+44)*(N n+1)
    nlinarith
  · simpa only [hout,List.nil_append,Lax920634.WordEncoding.construct] using ho

theorem layout_fits (n w : ℕ) (hw : wordConstant*(N n+1) ≤ 2^w) :
    layout.FitsWords (bound n) w := by
  apply fitsWords_of_max_le (by unfold bound; omega)
  have hs : max (bound n) (layout.span (bound n)) ≤ wordConstant*(N n+1) := by
    apply max_le
    · unfold bound wordConstant; omega
    · simp only [layout,Layout.span,List.length_cons,List.length_nil,bound,wordConstant]
      omega
  exact hs.trans hw

/--
---
conclusion: Lax920634.LinearConstruction.linear_time
---
Compile one fixed structured program that initializes the deterministic seed,
materializes successive rotation tables, and prints the complete final table.

# Proof strategy

Each new row uses the exact zig-zag recurrence with indexed accesses to the
fixed seed and preceding table. The old tables occupy disjoint consecutive
memory blocks. A geometric potential pays for every growth stage. A final
linear scan writes one word per vertex and the order header. The verified
Lax808846 compiler bounds actual machine instructions and all physical
addresses at every sufficiently large word width.
-/
theorem linear_time : ∃ (p : Lax808846.Ram.Program) (ct cw : ℕ),
    0 < ct ∧ 0 < cw ∧ ∀ (n w : ℕ),
      cw*(order (selectedLevel n)+1) ≤ 2^w →
      ∃ t ≤ ct*(order (selectedLevel n)+1),
        Lax808846.Ram.RunsTo w p [n] (Lax920634.WordEncoding.construct n) t := by
  refine ⟨program,25381,wordConstant,by decide,by decide,?_⟩
  intro n w hw
  obtain ⟨ext,τ,⟨k,hk,hbs⟩,hout⟩ := structured_runs n
  have hin : ∀ v ∈ [n], v < bound n := by
    intro v hv
    have he : v = n := List.mem_singleton.mp hv
    subst v
    have hn := Sizes.request_le_order n
    change n ≤ N n at hn
    unfold bound
    omega
  obtain ⟨t,ht,hr⟩ := compileProgram_runsTo (layout_fits n w hw) RamProgram.ok hin hbs
  refine ⟨t,?_,?_⟩
  · have hcost := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_left layout.const hk) 1)
    change t ≤ 10*((coefficient+44)*(N n+1))+1 at hcost
    rw [← timeConstant_value]
    change t ≤ (10*(coefficient+44)+1)*(N n+1)
    nlinarith
  · simpa only [hout,RamProgram.program] using hr

end Lax920634Proofs.RamLinear
