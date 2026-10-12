import Lax920634Proofs.Components
import Lax920634Proofs.TreeHelly

namespace Lax920634Proofs.Treewidth
set_option backward.isDefEq.respectTransparency false

open SimpleGraph Lax228581.Treewidth
open Lax920634.EdgeExpansion Lax920634Proofs.Bramble Lax920634Proofs.Components

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The vertex set of an undeleted component induces a connected graph in the original graph. -/
theorem component_connected (G : SimpleGraph V) (X : Set V)
    (c : (G.induce Xᶜ).ConnectedComponent) :
    (G.induce (componentPiece G X c)).Connected := by
  classical
  let F := componentPiece G X c
  let H := G.induce Xᶜ
  let f : c.toSimpleGraph →g G.induce F :=
    ⟨fun u => ⟨u.val.val, ⟨u.val, u.property, rfl⟩⟩, by intro u v huv; exact huv⟩
  rw [SimpleGraph.connected_iff]
  constructor
  · rintro ⟨u, hu⟩ ⟨v, hv⟩
    rcases hu with ⟨u', hu', rfl⟩
    rcases hv with ⟨v', hv', rfl⟩
    exact (c.connected_toSimpleGraph ⟨u', hu'⟩ ⟨v', hv'⟩).map f
  · obtain ⟨u, hu⟩ := c.nonempty_supp
    exact ⟨⟨u.val, ⟨u, hu, rfl⟩⟩⟩

/-- The bramble of connected sets containing more than half of all vertices. -/
noncomputable def largeBramble (G : SimpleGraph V) : Finset (Finset V) :=
  by
    classical
    exact Finset.univ.filter fun A => (G.induce (A : Set V)).Connected ∧
      Fintype.card V < 2 * A.card

/-- Large connected sets pairwise meet and form a bramble. -/
theorem largeBramble_isBramble (G : SimpleGraph V) : IsBramble G (largeBramble G) := by
  classical
  constructor
  · intro A hA
    have ha := (Finset.mem_filter.mp hA).2
    refine ⟨?_, ha.1⟩
    apply Finset.card_pos.mp
    omega
  · intro A hA B hB
    have ha := (Finset.mem_filter.mp hA).2.2
    have hb := (Finset.mem_filter.mp hB).2.2
    left
    by_contra h
    have hd : Disjoint A B := Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    have hc : A.card + B.card ≤ Fintype.card V := by
      rw [← Finset.card_union_of_disjoint hd]
      exact Finset.card_le_card (Finset.subset_univ _)
    omega

/-- Any set hitting all large connected sets has size linear in the graph order. -/
theorem hitting_large (G : SimpleGraph V) (d : ℕ) (hd : 0 < d)
    (hdegree : IsSubcubic G)
    (hex : HasEdgeExpansionAtLeast G (1 / (8 * (d : ℚ))))
    (X : Finset V) (hhit : Hits X (largeBramble G)) :
    Fintype.card V ≤ (24 * d + 1) * X.card := by
  classical
  let P := componentPartition G (X : Set V)
  letI : Fintype (G.induce (X : Set V)ᶜ).ConnectedComponent := Fintype.ofFinite _
  have hs : ∀ c, 2 * (P.piece c).ncard ≤ Fintype.card V := by
    intro c
    by_contra! hc
    let A : Finset V := (Set.toFinite (P.piece c)).toFinset
    have ha : (A : Set V) = P.piece c := Set.Finite.coe_toFinset _
    have hamem : A ∈ largeBramble G := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [ha]
        exact component_connected G (X : Set V) c
      · simpa only [A, ← Set.ncard_eq_toFinset_card] using hc
    obtain ⟨v, hv⟩ := hhit A hamem
    have hvX := (Finset.mem_inter.mp hv).1
    have hvA : v ∈ P.piece c := by
      rw [← ha]
      exact (Finset.mem_inter.mp hv).2
    exact P.outside c v hvA hvX
  have h := deletion_large_of_small_parts P d hd hdegree hex hs
  simpa only [Set.ncard_coe_finset] using h

/-- The single-bag decomposition makes the set of admissible treewidth bounds nonempty. -/
noncomputable def oneBag (G : SimpleGraph V) : TreeDecomposition G where
  Node := PUnit
  tree := ⊥
  isTree := SimpleGraph.IsTree.of_subsingleton
  bag := fun _ => Finset.univ
  vertex_mem_bag := fun _ => ⟨PUnit.unit, Finset.mem_univ _⟩
  edge_mem_bag := by intro u v huv; exact ⟨PUnit.unit, Finset.mem_univ _, Finset.mem_univ _⟩
  bag_indices_connected := by
    intro v
    have he : {i : PUnit | v ∈ (Finset.univ : Finset V)} = Set.univ := by ext i; simp
    rw [he]
    exact (SimpleGraph.induceUnivIso (⊥ : SimpleGraph PUnit)).connected_iff.mpr
      SimpleGraph.IsTree.of_subsingleton.connected

/-- The least admissible width is itself an admissible width. -/
theorem treewidth_attained (G : SimpleGraph V) : HasTreewidthAtMost G (treewidth G) := by
  unfold treewidth
  change sInf {w | HasTreewidthAtMost G w} ∈ {w | HasTreewidthAtMost G w}
  apply Nat.sInf_mem
  refine ⟨Fintype.card V, oneBag G, ?_⟩
  intro i
  simp only [oneBag, Finset.card_univ]
  omega

/-- Uniform expansion gives a linear lower bound on treewidth, through the large-set bramble. -/
theorem order_le_treewidth (G : SimpleGraph V) (d : ℕ) (hd : 0 < d)
    (hdegree : IsSubcubic G)
    (hex : HasEdgeExpansionAtLeast G (1 / (8 * (d : ℚ)))) :
    Fintype.card V ≤ (24 * d + 1) * (treewidth G + 1) := by
  classical
  obtain ⟨D, hD⟩ := treewidth_attained G
  obtain ⟨i, hi⟩ := exists_bag_hits_bramble_of_finiteSubtreeHelly D
    (largeBramble_isBramble G) (finiteSubtreeHelly _)
  exact (hitting_large G d hd hdegree hex (D.bag i) hi).trans
    (Nat.mul_le_mul_left _ (hD i))

end Lax920634Proofs.Treewidth
