import Lax920634.CycleReplacement
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
---
title: Explicit Modular Construction
type: definition
---
Put $q=m+1$. On $(\mathbb Z/q\mathbb Z)^2$, use the four transformations
$(x,y)\mapsto(x+2y,y),(x+2y+1,y),(x,y+2x),(x,y+2x+1)$
and their inverses. Ports $0,1,2,3$ label these transformations; ports
$4,5,6,7$ label their respective inverses. Replace every base vertex by an
eight-cycle, pairing inverse ports across the cycle. The resulting graph
$H_m$ has $N_m=8(m+1)^2$ vertices.

Every vertex has two cycle neighbors and one matching neighbor. These
formulas give a deterministic neighbor query using a constant number of
arithmetic operations on integers of $O(\log(m+2))$ bits.

# Formalization notes

All public graphs have the canonical carrier `Fin (order m)`. Base vertices
are numbered by `finProdFinEquiv`; ports come first in the second product
numbering. Modular arithmetic uses `ZMod.finEquiv`, a computable equivalence.
The parameter $m$ is shifted by one to avoid a zero modulus. Neither the
construction nor the neighbor list uses a choice of an expander.
The complexity observation above is mathematical prose, rather than a
machine-model running-time claim.
-/

namespace Lax920634.MargulisConstruction

/-- The number of base vertices. -/
def baseOrder (m : ℕ) : ℕ := (m + 1) * (m + 1)

/-- The number of vertices after eight-cycle replacement. -/
def order (m : ℕ) : ℕ := 8 * baseOrder m

/-- The numbered base-vertex coordinates, with all arithmetic modulo `m + 1`. -/
def coordinates (m : ℕ) : Fin (baseOrder m) ≃ (ZMod (m + 1) × ZMod (m + 1)) :=
  finProdFinEquiv.symm.trans
    (Equiv.prodCongr (ZMod.finEquiv (m + 1)).toEquiv (ZMod.finEquiv (m + 1)).toEquiv)

/-- The base neighbor reached through a specified transformation port. -/
def baseNeighbor (m : ℕ) (v : Fin (baseOrder m)) (i : Fin 8) : Fin (baseOrder m) :=
  let z := coordinates m v
  (coordinates m).symm (match i.val with
    | 0 => (z.1 + 2 * z.2, z.2)
    | 1 => (z.1 + 2 * z.2 + 1, z.2)
    | 2 => (z.1, z.2 + 2 * z.1)
    | 3 => (z.1, z.2 + 2 * z.1 + 1)
    | 4 => (z.1 - 2 * z.2, z.2)
    | 5 => (z.1 - 2 * z.2 - 1, z.2)
    | 6 => (z.1, z.2 - 2 * z.1)
    | _ => (z.1, z.2 - 2 * z.1 - 1))

/-- Cross a base edge and change to the inverse transformation's port. -/
def rotation (m : ℕ) (p : Fin 8 × Fin (baseOrder m)) : Fin 8 × Fin (baseOrder m) :=
  (CycleReplacement.oppositePort p.1, baseNeighbor m p.2 p.1)

/-- Canonical numbering of the ports of all base vertices. -/
def numbering (m : ℕ) : (Fin 8 × Fin (baseOrder m)) ≃ Fin (order m) :=
  finProdFinEquiv

/-- The deterministic simple graph obtained by eight-cycle replacement. -/
def graph (m : ℕ) : SimpleGraph (Fin (order m)) :=
  (CycleReplacement.replacementGraph (rotation m)).comap (numbering m).symm

/-- The two cycle neighbors and the matching neighbor, in that order. -/
def neighbors (m : ℕ) (v : Fin (order m)) : List (Fin (order m)) :=
  let p := (numbering m).symm v
  [numbering m (CycleReplacement.nextPort p.1, p.2),
   numbering m (CycleReplacement.prevPort p.1, p.2),
   numbering m (rotation m p)]

end Lax920634.MargulisConstruction
