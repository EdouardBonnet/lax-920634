import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Find

/-!
---
title: Deterministic Search for a Fixed Expander Seed
type: definition
---
Thirty permutations of a finite set are sufficient to make every set of at
most half its size escape by at least a tenth through some permutation.
A seed can therefore be found by checking finite tables in numerical order.
This search is used at one fixed size, independent of the requested output
order. Its cost is a constant in the construction of the infinite family.

# Formalization notes

Candidate tables are numbered by their base-$n$ digits. The test is a
finite predicate about injectivity and cardinalities. The selected table
is the first successful candidate, with identity as a total default;
the correctness proof shows that the default is never needed.
The search is implemented by a finite list scan and uses no choice operation.
-/

namespace Lax920634.SeedSearch

/-- A table of thirty maps on a numbered finite vertex set. -/
abbrev Table (n : ℕ) := Fin 30 → Fin n → Fin n

/-- The number of vertices of `S` whose image lies outside `S`. -/
def escape {n : ℕ} (f : Fin n → Fin n) (S : Finset (Fin n)) : ℕ :=
  (S.filter fun v => f v ∉ S).card

/-- Each row is a permutation, and some row moves at least a tenth of each small set out. -/
abbrev GoodTable {n : ℕ} (T : Table n) : Prop :=
  (∀ i, Function.Bijective (T i)) ∧
    ∀ S : Finset (Fin n), 2 * S.card ≤ n →
      ∃ i : Fin 30, S.card ≤ 10 * escape (T i) S

/-- The candidate table represented by a base-`n` integer. -/
def decode (n : ℕ) (code : Fin (n ^ (30 * n))) : Table n :=
  fun i v => finFunctionFinEquiv.symm code (finProdFinEquiv (i, v))

/-- All candidate codes in increasing numerical order. -/
def candidates (n : ℕ) : List (Fin (n ^ (30 * n))) := List.finRange _

/-- The first expanding permutation table found by the finite deterministic scan. -/
def selectedTable (n : ℕ) : Table n :=
  (((candidates n).find? fun code => decide (GoodTable (decode n code))).map
    (decode n)).getD (fun _ v => v)

/-- Find the inverse image by scanning a numbered finite vertex set. -/
def inverse {n : ℕ} (f : Fin n → Fin n) (v : Fin n) : Fin n :=
  ((List.finRange n).find? fun u => decide (f u = v)).getD v

/-- A fixed powering exponent sufficient for the lazy permutation seed. -/
def poweringExponent : ℕ := 5760000

/-- The fixed degree of the powered seed. -/
def seedDegree : ℕ := 120 ^ poweringExponent

/-- The fixed number of seed vertices, the fourth power of its degree. -/
def seedOrder : ℕ := seedDegree ^ 4

end Lax920634.SeedSearch
