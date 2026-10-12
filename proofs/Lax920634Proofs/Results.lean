import Lax920634Proofs.Family
import Lax920634Proofs.Sizes
import Lax920634Proofs.Relabel
import Lax920634Proofs.Treewidth
import Lax920634.SeedCorrectness
import Lax920634.PathExpansion
import Lax920634.SubcubicConstruction
import Lax920634.ExplicitExpansion
import Lax920634.ExpansionTreewidth
import Lax920634.ExplicitTreewidth
import Lax920634.ExpanderExistence
import Lax920634.TreewidthExistence
import Lax920634.ConstructionSize

namespace Lax920634Proofs.Results

open Lax920634

attribute [local irreducible] Lax920634.SeedSearch.seedDegree
attribute [local irreducible] Lax920634.SeedSearch.poweringExponent

/--
---
conclusion: Lax920634.SeedCorrectness.table_good
---
A finite counting argument guarantees a good table; exhaustive numerical enumeration finds it.
-/
theorem SeedCorrectness_table_good (n : ℕ) : SeedSearch.GoodTable (SeedSearch.selectedTable n) := by
  exact Seed.selectedTable_good n

/--
---
conclusion: Lax920634.PathExpansion.replacement_expansion
---
Count crossing edges in partial clouds and base edges leaving full clouds.
-/
theorem PathExpansion_replacement_expansion {n d : ℕ} (R : Fin n × Fin d → Fin n × Fin d)
    (hR : Function.Involutive R) (hd : 2 ≤ d)
    (hbase : ∀ U : Set (Fin n),
      d * min U.ncard (n - U.ncard) ≤ 4 * (PathReplacement.baseCut R U).ncard) :
  EdgeExpansion.HasEdgeExpansionAtLeast (PathReplacement.graph R) (1 / (8 * (d : ℚ))) := by
  exact Paths.expansion R hR hd hbase

/--
---
conclusion: Lax920634.SubcubicConstruction.subcubic
---
Identify the executable graph with path replacement. Each port has two path neighbors and at most one paired neighbor.
-/
theorem SubcubicConstruction_subcubic (k : ℕ) : EdgeExpansion.IsSubcubic (ZigZagConstruction.graph k) := by
  exact Family.subcubic k

/--
---
conclusion: Lax920634.ExplicitExpansion.expansion
---
The powered seed has spectral bound one fifth. Zig-zag iteration gives bound two fifths, and path replacement gives the stated edge expansion.
-/
theorem ExplicitExpansion_expansion (k : ℕ) : EdgeExpansion.HasEdgeExpansionAtLeast
  (ZigZagConstruction.graph k) (1 / (8 * (ZigZagConstruction.degree : ℚ))) := by
  rw [Family.graph_eq]
  apply Relabel.expansion_comap
  exact PathExpansion.replacement_expansion _ (SeedGraph.finBase.data k).property
    (by have h := Tower.degree_ge_four; omega) (Family.base_expansion k)

/--
---
conclusion: Lax920634.ExpansionTreewidth.order_le_treewidth
---
Small components after deletion force a large deletion set. Connected sets containing more than half the vertices form a bramble, and tree Helly supplies a bag meeting every member.
-/
theorem ExpansionTreewidth_order_le_treewidth {n : ℕ} (G : SimpleGraph (Fin n)) (d : ℕ) (hd : 0 < d)
    (hdegree : EdgeExpansion.IsSubcubic G)
    (hex : EdgeExpansion.HasEdgeExpansionAtLeast G (1 / (8 * (d : ℚ)))) :
  n ≤ (24 * d + 1) * (Lax228581.Treewidth.treewidth G + 1) := by
  simpa only [Fintype.card_fin] using Treewidth.order_le_treewidth G d hd hdegree hex

/--
---
conclusion: Lax920634.ExplicitTreewidth.linear_treewidth
---
Apply the expansion-to-treewidth inequality to the proved degree and expansion bounds of the same executable graph.
-/
theorem ExplicitTreewidth_linear_treewidth (k : ℕ) : ZigZagConstruction.order k ≤
  (24 * ZigZagConstruction.degree + 1) *
    (Lax228581.Treewidth.treewidth (ZigZagConstruction.graph k) + 1) := by
  exact ExpansionTreewidth.order_le_treewidth _ ZigZagConstruction.degree
    (by have h := Tower.degree_ge_four; omega)
    (SubcubicConstruction.subcubic k) (ExplicitExpansion.expansion k)

/--
---
conclusion: Lax920634.ExpanderExistence.exists_subcubic_expander
---
Select the first sufficiently large tower member, then use its proved subcubicity and uniform expansion.
-/
theorem ExpanderExistence_exists_subcubic_expander (lower : ℕ) :
  ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), lower ≤ n ∧
    EdgeExpansion.IsSubcubic G ∧
    EdgeExpansion.HasEdgeExpansionAtLeast G (1 / (8 * (ZigZagConstruction.degree : ℚ))) := by
  refine ⟨Lax920634.ZigZagConstruction.order (Lax920634.GraphEncoding.selectedLevel lower),
      Lax920634.ZigZagConstruction.graph (Lax920634.GraphEncoding.selectedLevel lower),
      (ConstructionSize.size_bounds lower).1, SubcubicConstruction.subcubic _, ExplicitExpansion.expansion _⟩

/--
---
conclusion: Lax920634.TreewidthExistence.exists_subcubic_linear_treewidth
---
Choose a graph of order at least twice the additive constant. Its treewidth is positive, so the additive one is absorbed into twice the linear coefficient.
-/
theorem TreewidthExistence_exists_subcubic_linear_treewidth (lower : ℕ) :
  ∃ n : ℕ, ∃ G : SimpleGraph (Fin n), lower ≤ n ∧ EdgeExpansion.IsSubcubic G ∧
    n ≤ (48 * ZigZagConstruction.degree + 2) * Lax228581.Treewidth.treewidth G := by
  let d := Lax920634.ZigZagConstruction.degree
  let C := 24 * d + 1
  let k := Lax920634.GraphEncoding.selectedLevel (lower + 2 * C)
  have hn := (ConstructionSize.size_bounds (lower + 2 * C)).1
  have ht := ExplicitTreewidth.linear_treewidth k
  change Lax920634.ZigZagConstruction.order k ≤ C *
    (Lax228581.Treewidth.treewidth (Lax920634.ZigZagConstruction.graph k) + 1) at ht
  have hc : 0 < C := by dsimp [C]; omega
  have hpos : 1 ≤ Lax228581.Treewidth.treewidth (Lax920634.ZigZagConstruction.graph k) := by
    change lower + 2 * C ≤ Lax920634.ZigZagConstruction.order k at hn
    nlinarith
  refine ⟨Lax920634.ZigZagConstruction.order k, Lax920634.ZigZagConstruction.graph k,
    by change lower + 2 * C ≤ Lax920634.ZigZagConstruction.order k at hn; omega,
    SubcubicConstruction.subcubic k, ?_⟩
  change Lax920634.ZigZagConstruction.order k ≤ (48 * d + 2) * _
  have he : 48 * d + 2 = 2 * C := by dsimp [C]; ring
  rw [he]
  nlinarith

/--
---
conclusion: Lax920634.ConstructionSize.size_bounds
---
The bounded level scan reaches the first sufficiently large regular tower
member. The preceding level was below twice the request, bounding overshoot.
-/
theorem ConstructionSize_size_bounds (n : ℕ) :
    n ≤ ZigZagConstruction.order (GraphEncoding.selectedLevel n) ∧
    ZigZagConstruction.order (GraphEncoding.selectedLevel n) ≤
      (2 * ZigZagConstruction.degree * SeedSearch.seedDegree ^ 4) * (n + 1) :=
  ⟨Sizes.request_le_order n, Sizes.order_bound n⟩

end Lax920634Proofs.Results
