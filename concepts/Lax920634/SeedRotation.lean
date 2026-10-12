import Lax920634.SeedSearch
import Mathlib.Logic.Equiv.Fin.Basic

/-!
---
title: Rotation Map of the Fixed Powered Seed
type: definition
---
The selected thirty permutations supply sixty forward and inverse darts.
Adding sixty stationary darts makes the walk lazy. Raising this fixed
120-regular graph to the power 5760000 gives a seed of degree
$D=120^{5760000}$ on $D^4$ vertices. Labels of powered edges encode their
sequences of original darts in base 120.

# Formalization notes

Every definition is executable. Finite inverse queries are computed by the
scan in `SeedSearch`. Powered edges reverse the traversed dart labels in
reverse order. The long exponent and seed size are fixed constants.
-/

namespace Lax920634.SeedRotation

/-- Number forward and inverse permutation darts by integers below sixty. -/
def permutationLabels : (Fin 30 × Bool) ≃ Fin 60 :=
  (Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv

/-- Number the permutation darts and the sixty stationary darts together. -/
def lazyLabels : ((Fin 30 × Bool) ⊕ Fin 60) ≃ Fin 120 :=
  (Equiv.sumCongr permutationLabels (Equiv.refl _)).trans finSumFinEquiv

/-- The rotation of the selected lazy permutation graph, with numbered labels. -/
def lazyRotation (n : ℕ) (p : Fin n × Fin 120) : Fin n × Fin 120 :=
  match lazyLabels.symm p.2 with
  | Sum.inl (i, false) =>
    (SeedSearch.selectedTable n i p.1, lazyLabels (Sum.inl (i, true)))
  | Sum.inl (i, true) =>
    (SeedSearch.inverse (SeedSearch.selectedTable n i) p.1,
      lazyLabels (Sum.inl (i, false)))
  | Sum.inr j => (p.1, lazyLabels (Sum.inr j))

/-- Follow a finite sequence of numbered darts to its endpoint. -/
def walkEnd {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d) :
    (t : ℕ) → Fin n → (Fin t → Fin d) → Fin n
  | 0, v, _ => v
  | t + 1, v, s => walkEnd R t (R (v, s 0)).1 (fun j => s j.succ)

/-- The vertex reached after a prescribed number of steps of a finite dart sequence. -/
def walkAt {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (t : ℕ) (v : Fin n) (s : Fin t → Fin d) : ℕ → Fin n
  | 0 => v
  | k + 1 => if h : k < t then
    (R (walkAt R t v s k, s ⟨k, h⟩)).1 else walkAt R t v s k

/-- The edge rotation of a graph power, with dart sequences numbered in base `d`. -/
def powerRotation {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (t : ℕ) (p : Fin n × Fin (d ^ t)) : Fin n × Fin (d ^ t) :=
  let s := finFunctionFinEquiv.symm p.2
  (walkEnd R t p.1 s, finFunctionFinEquiv (fun j =>
    (R (walkAt R t p.1 s (Fin.rev j).val, s (Fin.rev j))).2))

/-- The fixed seed's rotation map, after lazy powering. -/
def rotation : Fin SeedSearch.seedOrder × Fin SeedSearch.seedDegree →
    Fin SeedSearch.seedOrder × Fin SeedSearch.seedDegree :=
  powerRotation (lazyRotation SeedSearch.seedOrder) SeedSearch.poweringExponent

end Lax920634.SeedRotation
