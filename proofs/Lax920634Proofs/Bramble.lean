import Lax228581.Treewidth
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

/-!
The bramble-to-bag reduction, adapted from the polynomial-grid-minor
formalization's TreewidthBramble.lean to the registered treewidth definition.
-/

namespace Lax920634Proofs.Bramble
open SimpleGraph Lax228581.Treewidth
set_option backward.isDefEq.respectTransparency false

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Two finite vertex sets touch if they meet or some graph edge joins them. -/
def Touches (G : _root_.SimpleGraph V) (A B : Finset V) : Prop :=
  (A ∩ B).Nonempty ∨
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b


/-- A finite set of vertices is a connected bramble piece. -/
def IsConnectedSet (G : _root_.SimpleGraph V) (A : Finset V) : Prop :=
  A.Nonempty ∧ (G.induce (A : Set V)).Connected

/-- A finite bramble, represented in the same form as the well-linked
development: a finite family of nonempty connected vertex finsets, pairwise
touching.  Quantifying also over equal members is equivalent to the customary
distinct-pair formulation because every member is nonempty. -/
def IsBramble (G : _root_.SimpleGraph V) (B : Finset (Finset V)) : Prop :=
  (∀ A ∈ B, IsConnectedSet G A) ∧
    ∀ A ∈ B, ∀ C ∈ B, Touches G A C

/-- `X` is a transversal (hitting set) of the finite family `B`. -/
def Hits (X : Finset V) (B : Finset (Finset V)) : Prop :=
  ∀ A ∈ B, (X ∩ A).Nonempty

section TreeDecomposition

variable {G : _root_.SimpleGraph V} (D : TreeDecomposition G)

/-- Decomposition nodes whose bags meet a vertex set.  Sets are used here
rather than finsets because this is exactly the vertex set of an induced
subgraph of the decomposition tree. -/
def meetingNodes (A : Finset V) : Set D.Node :=
  {i | (D.bag i ∩ A).Nonempty}

theorem mem_meetingNodes_iff {A : Finset V} {i : D.Node} :
    i ∈ meetingNodes D A ↔ ∃ v ∈ D.bag i, v ∈ A := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
  · rintro ⟨v, hvi, hvA⟩
    exact ⟨v, Finset.mem_inter.mpr ⟨hvi, hvA⟩⟩

/-- A walk contained in `A` lifts to reachability between any bags containing
its endpoints, while staying among bags that meet `A`. -/
theorem reachable_meetingNodes_of_walk {A : Finset V} {u v : V}
    (p : G.Walk u v) (hp : ∀ w ∈ p.support, w ∈ A)
    {i j : D.Node} (hui : u ∈ D.bag i) (hvj : v ∈ D.bag j) :
    (D.tree.induce (meetingNodes D A)).Reachable
      ⟨i, mem_meetingNodes_iff D |>.2 ⟨u, hui, hp u p.start_mem_support⟩⟩
      ⟨j, mem_meetingNodes_iff D |>.2 ⟨v, hvj, hp v p.end_mem_support⟩⟩ := by
  induction p generalizing i with
  | @nil x =>
      have hsub : {n : D.Node | x ∈ D.bag n} ⊆ meetingNodes D A := by
        intro n hn
        exact mem_meetingNodes_iff D |>.2
          ⟨x, hn, hp x (by simp)⟩
      have hreach := D.bag_indices_connected x ⟨i, hui⟩ ⟨j, hvj⟩
      convert hreach.map (D.tree.induceHomOfLE hsub).toHom using 1 <;> rfl
  | @cons u w v huw q ih =>
      obtain ⟨e, hue, hwe⟩ := D.edge_mem_bag huw
      have huA : u ∈ A := hp u (by simp)
      have hwA : w ∈ A := hp w (by simp)
      have hsub : {n : D.Node | u ∈ D.bag n} ⊆ meetingNodes D A := by
        intro n hn
        exact mem_meetingNodes_iff D |>.2 ⟨u, hn, huA⟩
      have hfirst0 := D.bag_indices_connected u ⟨i, hui⟩ ⟨e, hue⟩
      have hfirst := hfirst0.map (D.tree.induceHomOfLE hsub).toHom
      have hq : ∀ x ∈ q.support, x ∈ A := by
        intro x hx
        exact hp x (by simp [hx])
      have hsecond := ih hq hwe hvj
      convert hfirst.trans hsecond using 1 <;> rfl

/-- The bags meeting a nonempty connected vertex set induce a connected
subgraph of the decomposition tree. -/
theorem meetingNodes_connected {A : Finset V} (hA : IsConnectedSet G A) :
    (D.tree.induce (meetingNodes D A)).Connected := by
  rcases hA.1 with ⟨a, haA⟩
  rcases D.vertex_mem_bag a with ⟨root, haroot⟩
  have hroot : root ∈ meetingNodes D A :=
    mem_meetingNodes_iff D |>.2 ⟨a, haroot, haA⟩
  rw [_root_.SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨root, hroot⟩, ?_⟩
  rintro ⟨j, hj⟩
  rcases (mem_meetingNodes_iff D).1 hj with ⟨v, hvj, hvA⟩
  obtain ⟨q⟩ := hA.2 ⟨a, haA⟩ ⟨v, hvA⟩
  let inc : G.induce (A : Set V) →g G :=
    ⟨Subtype.val, by
      intro x y hxy
      exact hxy⟩
  let p : G.Walk a v := q.map inc
  have hp : ∀ x ∈ p.support, x ∈ A := by
    intro x hx
    simp only [p, _root_.SimpleGraph.Walk.support_map, List.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  simpa [p] using reachable_meetingNodes_of_walk D p hp haroot hvj

/-- Touching vertex sets give intersecting subtrees of decomposition nodes. -/
theorem meetingNodes_inter_nonempty {A C : Finset V} (h : Touches G A C) :
    (meetingNodes D A ∩ meetingNodes D C).Nonempty := by
  rcases h with hAC | ⟨a, ha, c, hc, hac⟩
  · obtain ⟨v, hv⟩ := hAC
    have ⟨hvA, hvC⟩ := Finset.mem_inter.mp hv
    rcases D.vertex_mem_bag v with ⟨i, hvi⟩
    exact ⟨i, mem_meetingNodes_iff D |>.2 ⟨v, hvi, hvA⟩,
      mem_meetingNodes_iff D |>.2 ⟨v, hvi, hvC⟩⟩
  · rcases D.edge_mem_bag hac with ⟨i, hai, hci⟩
    exact ⟨i, mem_meetingNodes_iff D |>.2 ⟨a, hai, ha⟩,
      mem_meetingNodes_iff D |>.2 ⟨c, hci, hc⟩⟩

end TreeDecomposition

/-- The precise finite-tree Helly property needed by the easy half of bramble
duality.  It is stated independently so the graph-theoretic reduction below
does not depend on a particular proof of subtree Helly. -/
def FiniteSubtreeHelly (I : Type*) [Fintype I] [DecidableEq I] : Prop :=
  ∀ {N : Type} [Fintype N] [DecidableEq N]
    (T : _root_.SimpleGraph N) (S : I → Set N),
    T.IsTree →
    (∀ i, (T.induce (S i)).Connected) →
    (∀ i j, (S i ∩ S j).Nonempty) →
    ∃ n : N, ∀ i, n ∈ S i

/-- Assuming finite subtree Helly, one bag of every tree decomposition hits
every member of a bramble.  All graph-specific work is discharged by
`meetingNodes_connected` and `meetingNodes_inter_nonempty`. -/
theorem exists_bag_hits_bramble_of_finiteSubtreeHelly
    {G : _root_.SimpleGraph V} (D : TreeDecomposition G)
    {B : Finset (Finset V)} (hB : IsBramble G B)
    (hHelly : FiniteSubtreeHelly {A : Finset V // A ∈ B}) :
    ∃ i : D.Node, Hits (D.bag i) B := by
  classical
  letI : Fintype D.Node := D.nodeFintype
  letI : DecidableEq D.Node := Classical.decEq D.Node
  let I := {A : Finset V // A ∈ B}
  letI : Fintype I := Fintype.ofFinite I
  letI : DecidableEq I := Classical.decEq I
  have hcommon := @hHelly D.Node inferInstance inferInstance
    D.tree (fun A : I => meetingNodes D A.1) D.isTree
    (fun (A : I) => meetingNodes_connected D (hB.1 A.1 A.2))
    (fun (A C : I) =>
      meetingNodes_inter_nonempty D (hB.2 A.1 A.2 C.1 C.2))
  obtain ⟨i, hi⟩ := hcommon
  refine ⟨i, ?_⟩
  intro A hA
  exact hi ⟨A, hA⟩


end Lax920634Proofs.Bramble
