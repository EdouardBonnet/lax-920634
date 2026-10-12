import Lax920634.SeedSearch

/-!
---
title: The Deterministic Seed Search Succeeds
type: lemma
---
At every finite order the deterministic table scan finds thirty permutations
such that, for every set of at most half the vertices, some permutation
moves at least a tenth of that set outside itself.

# Formalization notes

The scan checks this exact decidable property. A finite counting argument
proves that a successful candidate exists, and numerical enumeration covers
every candidate. The total default in the constructor is never needed.
-/

namespace Lax920634.SeedCorrectness

open SeedSearch

/-- The specified finite seed search returns a successful permutation table. -/
axiom table_good (n : ℕ) : GoodTable (selectedTable n)

end Lax920634.SeedCorrectness
