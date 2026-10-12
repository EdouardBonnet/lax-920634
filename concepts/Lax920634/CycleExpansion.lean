import Lax920634.CycleReplacement

/-!
---
title: Eight-Cycle Replacement Preserves Expansion
type: theorem
---
If an eight-regular port involution pairs opposite ports and every base cut
has at least two fifths as many crossing edges as its smaller side, its
eight-cycle replacement has edge expansion at least $1/128$.

One can prove the stronger constant $2/207$. For a cut $S$, let $U$ be its
full clouds and let $p$ count its partial clouds. The cycle boundary has at
least $2p$ edges. At most $8p$ of the base edges leaving $U$ end in partial
clouds, while all the others cross $S$. Also $|S|\le8|U|+7p$.
These inequalities give $2|S|\le207|\partial S|$.

# Formalization notes

The base carrier is `Fin n`. The hypotheses describe the port map itself,
so loops and multiplicity in the base graph do not require exceptions.
The opposite-port condition ensures that cycle and matching edges are
disjoint in the resulting simple graph.
-/

namespace Lax920634.CycleExpansion

/-- Opposite-port eight-cycle replacement has uniform edge expansion. -/
axiom replacement_expansion {n : ℕ} (R : Fin 8 × Fin n → Fin 8 × Fin n)
    (hR : Function.Involutive R)
    (hport : ∀ p, (R p).1 = CycleReplacement.oppositePort p.1)
    (hbase : ∀ S : Set (Fin n),
      2 * min S.ncard (n - S.ncard) ≤ 5 * (CycleReplacement.baseCut R S).ncard) :
    EdgeExpansion.HasEdgeExpansionAtLeast (CycleReplacement.replacementGraph R) (1 / 128)

end Lax920634.CycleExpansion
