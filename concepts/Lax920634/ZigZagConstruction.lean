import Lax920634.SeedRotation
import Lax920634.EdgeExpansion

/-!
---
title: Explicit Zig-Zag Family and Path Replacement
type: definition
---
Starting with the fixed powered seed of degree $D$, square it. Repeatedly
square the current graph and take its zig-zag product with the same seed.
The level-$k$ graph has degree $d=D^2$ and $(D^4)^{k+1}$ vertices.
Replace every vertex by a path of $d$ ports to obtain the subcubic graph
$H_k$ on $N_k=d(D^4)^{k+1}$ vertices.

The rotation query below gives the construction directly in integer
arithmetic. Each recursive level makes two queries at the preceding level
and two queries to the fixed seed. Thus the number of fixed-seed calls is
$2^{k+2}-2$, bounded by a constant times $N_k$. Each integer manipulated has
$O(\log N_k)$ bits. Enumerating all edges is consequently polynomial in
$N_k$. The fixed seed search has an enormous constant cost.

# Formalization notes

The construction uses numerical vertex labels and the concrete deterministic
seed scan. The graph is the simple undirected closure of the generated path
and matching edges. The proof connects this executable recurrence to the
numbered zig-zag tower and verifies every returned matching endpoint's bounds.
-/

namespace Lax920634.ZigZagConstruction

open SeedSearch

/-- The fixed degree of each regular graph in the tower. -/
def degree : ℕ := seedDegree ^ 2

/-- The number of vertices in the regular graph at a given level. -/
def baseOrder (k : ℕ) : ℕ := (seedDegree ^ 4) ^ (k + 1)

/-- The number of vertices after path replacement at a given level. -/
def order (k : ℕ) : ℕ := baseOrder k * degree

/-- A total numerical query to the fixed seed's edge rotation. -/
def seedValue (p : ℕ × ℕ) : ℕ × ℕ :=
  if h : p.1 < seedOrder ∧ p.2 < seedDegree then
    let r := SeedRotation.rotation (⟨p.1, h.1⟩, ⟨p.2, h.2⟩)
    (r.1.val, r.2.val)
  else (0, 0)

/-- The regular tower's rotation, computed by squaring and zig-zag steps. -/
def rotation : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, (v, i) =>
      let p₀ := seedValue (v, i / seedDegree)
      let p₁ := seedValue (p₀.1, i % seedDegree)
      (p₁.1, p₀.2 + seedDegree * p₁.2)
  | k + 1, (v, i) =>
      let p := seedValue (v % seedDegree ^ 4, i / seedDegree)
      let q₀ := rotation k (v / seedDegree ^ 4, p.1 / degree)
      let q₁ := rotation k (q₀.1, p.1 % degree)
      let r := seedValue (q₀.2 + degree * q₁.2, i % seedDegree)
      (r.1 + seedDegree ^ 4 * q₁.1, p.2 + seedDegree * r.2)

/-- The matching endpoint of a port, in the canonical vertex numbering. -/
def matchingNeighbor (k v : ℕ) : ℕ :=
  let r := rotation k (v / degree, v % degree)
  r.2 + degree * r.1

/-- The subcubic graph defined by the explicit tower and path-edge formulas. -/
def graph (k : ℕ) : SimpleGraph (Fin (order k)) :=
  SimpleGraph.fromRel (fun u v =>
    (u.val / degree = v.val / degree ∧ u.val + 1 = v.val) ∨
      v.val = matchingNeighbor k u.val)

/-- The candidate neighbors, omitting nonexistent endpoint edges of a path. -/
def neighbors (k v : ℕ) : List ℕ :=
  (if 0 < v % degree then [v - 1] else []) ++
    (if v % degree + 1 < degree then [v + 1] else []) ++
    [matchingNeighbor k v]

end Lax920634.ZigZagConstruction
