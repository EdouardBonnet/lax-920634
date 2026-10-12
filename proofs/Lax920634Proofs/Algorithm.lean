import Lax920634Proofs.Tower
import Lax920634.PolynomialConstruction
import Lax323828Proofs.PCPFoundation.Classes.PCP.Internal.AlgFamily
import Lax323828Proofs.RegisteredBridge.MultitapeTransducer

namespace Lax920634Proofs.Algorithm

open Lax920634.GraphEncoding Lax920634.ZigZagConstruction
open Lax323828Proofs.PCPFoundation.Complexity

attribute [local irreducible] Lax920634.SeedSearch.seedDegree
attribute [local irreducible] Lax920634.SeedSearch.poweringExponent

/-- The numerical selector is the same bounded loop used in the polynomial-time table program. -/
theorem levelAfter_eq (b n j : ℕ) (p : ℕ × ℕ) :
    Lax920634.GraphEncoding.levelAfter b n j p =
      Lax323828Proofs.PCPFoundation.Complexity.levelAfter b n j p := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Lax920634.GraphEncoding.levelAfter,
      Lax323828Proofs.PCPFoundation.Complexity.levelAfter, ih]

/-- The polynomial-time selector reports exactly the specified level. -/
theorem searchLevel_eq (z : List Bool) :
    SeedGraph.finBase.searchLevel (2 * Polynomial.X) z = selectedLevel z.length := by
  unfold FinBase.searchLevel Lax323828Proofs.PCPFoundation.Complexity.levelFn
  rw [polyRuler_length, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  -- The initial size is the fourth power of the seed degree.
  have hinit4 : pair ([] : List Bool) (List.replicate (SeedGraph.finBase.deg ^ 4) true) =
    pair (List.replicate 0 true) (List.replicate (SeedGraph.finBase.deg ^ 4) true) := rfl
  rw [hinit4, levelStep_iterate, pairFst_pair, pairFst_pair, List.length_replicate]
  unfold selectedLevel
  rw [levelAfter_eq]
  rfl

/-- The bracket encoding of a bit agrees with the finite-data encoding used by the machine. -/
theorem encodeBit_eq (b : Bool) : encodeBit b = DataEncode.bitstringEncode b := by
  cases b <;> simp [encodeBit, DataEncode.bitstringEncode_def, DataEncode.encode, Data.toBits_l]

/-- The word serialization agrees with the finite-data encoding. -/
theorem encodeWord_eq (w : List Bool) : encodeWord w = DataEncode.bitstringEncode w := by
  rw [DataEncode.bitstringEncode_list]
  unfold encodeWord
  rw [show encodeBit = DataEncode.bitstringEncode from funext encodeBit_eq, List.flatMap_def]

/-- The serialized destination record agrees with the machine's paired-word encoding. -/
theorem encodeRecord_eq (p : ℕ × ℕ) : encodeRecord p =
    DataEncode.bitstringEncode (List.replicate p.1 true, List.replicate p.2 true) := by
  unfold encodeRecord
  rw [encodeWord_eq, encodeWord_eq]
  simp only [DataEncode.bitstringEncode_def, DataEncode_pair, Data.toBits_l,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- The specified graph encoding is precisely the table produced by the proved machine. -/
theorem encoding_eq (k : ℕ) : encoding k = SeedGraph.finBase.table k := by
  unfold encoding records FinBase.table FinBase.tableList
  rw [DataEncode.bitstringEncode_list]
  simp only [encodeRecord_eq, Tower.rotation_eq,
    List.flatMap_def, List.map_map, Function.comp_def]
  rfl

/-- The specified constructor is the function computed by the existing polynomial-time table program. -/
theorem construct_eq (z : List Bool) :
    construct z = SeedGraph.finBase.famTableFn (2 * Polynomial.X) z := by
  unfold construct FinBase.famTableFn
  rw [searchLevel_eq, encoding_eq]

/--
---
conclusion: Lax920634.PolynomialConstruction.polynomial_time
---
The output encoding is the rotation table of the selected tower member,
with each row interpreted as one path-replacement vertex.

# Proof strategy

Identify the numerical selector and bracket serialization with the proved
polynomial-time tower-table construction. Transfer its deterministic machine
through pointwise equality and the registered machine-model bridge.

# Attribution

The zig-zag product is due to Reingold, Vadhan, and Wigderson. The tower-table
and machine-model proofs are reused from the registered Lax323828 development,
including contributions by Bolton Bailey and Samuel Schlesinger.
-/
lemma polynomial_time : Nonempty (Turing.TM2ComputableInPolyTime id id construct) := by
  have hf : construct ∈ FP := mem_FP_of_eq (SeedGraph.finBase.famTableFn_mem_FP (2 * Polynomial.X))
    (fun z => (construct_eq z).symm)
  exact Lax323828Proofs.RegisteredBridge.FP_registered_computer hf

end Lax920634Proofs.Algorithm
