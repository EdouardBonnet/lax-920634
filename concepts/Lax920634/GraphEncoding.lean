import Lax920634.ZigZagConstruction
import Mathlib.Data.List.Basic

/-!
---
title: Selecting and Encoding the Constructed Graphs
type: definition
---
Given a requested order $n$ in unary, start at the smallest tower member and
advance while its regular-graph order is below $2n$. At most $2n$ advances
suffice. After path replacement this selects a graph of order between $n$
and a fixed constant times $n+1$.

The output lists the paired-port destination of every vertex, in numerical
order. A destination is recorded as its base vertex and its port, both in
unary. The two possible path neighbors follow directly from the row number.
This table determines the entire simple graph, including the removal of loops
and duplicate edges.

# Formalization notes

The binary serialization uses balanced brackets: `false` opens a list and
`true` closes one. A Boolean is an empty list for `false` and a list containing
one empty list for `true`. Records are pairs of unary Boolean words. The
whole table is a list of these records. The format is unambiguous; its unary
coordinates increase output size only polynomially.
-/

namespace Lax920634.GraphEncoding

/-- The bounded level-selection loop, carrying the level and current regular order. -/
def levelAfter (b n : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | j + 1, p =>
      let q := levelAfter b n j p
      if q.2 < 2 * n then (q.1 + 1, q.2 * b) else q

/-- The level selected for a requested order, after at most `2*n` advances. -/
def selectedLevel (n : ℕ) : ℕ :=
  (levelAfter (SeedSearch.seedDegree ^ 4) n (2 * n) (0, SeedSearch.seedDegree ^ 4)).1

/-- A Boolean serialized as an empty or singleton-empty bracketed list. -/
def encodeBit (b : Bool) : List Bool :=
  if b then [false, false, true, true] else [false, true]

/-- Serialize a Boolean word as a bracketed list of encoded Booleans. -/
def encodeWord (w : List Bool) : List Bool := false :: (w.flatMap encodeBit ++ [true])

/-- Serialize a pair of natural coordinates, each represented in unary. -/
def encodeRecord (p : ℕ × ℕ) : List Bool :=
  false :: (encodeWord (List.replicate p.1 true) ++
    encodeWord (List.replicate p.2 true) ++ [true])

/-- The paired-port destination of each vertex, in canonical row order. -/
def records (k : ℕ) : List (ℕ × ℕ) :=
  (List.range (ZigZagConstruction.order k)).map fun j =>
    ZigZagConstruction.rotation k (j / ZigZagConstruction.degree, j % ZigZagConstruction.degree)

/-- The binary table encoding of the entire subcubic graph at a specified level. -/
def encoding (k : ℕ) : List Bool := false :: ((records k).flatMap encodeRecord ++ [true])

/-- The specified deterministic graph construction on a unary size request. -/
def construct (input : List Bool) : List Bool := encoding (selectedLevel input.length)

end Lax920634.GraphEncoding
