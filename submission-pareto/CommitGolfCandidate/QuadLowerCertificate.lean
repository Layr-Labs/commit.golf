import CommitGolfCandidate.QuadLowerAdapter
import CommitGolfCandidate.TwoPermutationQuad2Spec

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling CommitGolfCandidate.ShortTree
open TwoPermutationPrototype.Packed.Checker (RecordBlock)
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

theorem actual_lower_step : LowerStepRefines (adaptLowerStep levelResult) :=
  lower_step_from_level levelResult levelFacts

/-- The complete twelve-step actual-image binary path, including query rows,
proof cursor, scratch frame, exact charged run, and a generic honest-tree fold. -/
theorem actual_lower_run (oracle : Oracle) (ordinal : Nat) (index : Index)
    (state : MachineState) (room : checkProofByte ordinal+570≤MEMORY_BYTES)
    (cursor : LowerCursor ordinal index 0 state) :
    LowerRunFacts oracle ordinal index 0 12 state
      (runLower (adaptLowerStep levelResult) oracle ordinal index 12 0 state) :=
  run_lower_facts _ actual_lower_step oracle ordinal index 12 0 (by decide) room state cursor

theorem quad_honest_heap_climb (oracle : Oracle) (quad : QuadFunction) (leaves : DigestTape) (node : Nat)
    (positive : 2≤node) (bounded : node<LENGTH/8) :
    let heap := quad2Heap oracle.compression quad leaves
    padLow (oracle.compression (pathPair node (heap node) (heap (node ^^^ 1))))=heap (node/2) := by
  let heap := quad2Heap oracle.compression quad leaves
  change padLow (oracle.compression (pathPair node (heap node) (heap (node ^^^ 1))))=heap (node/2)
  have parent := quad2_heap_parent oracle.compression quad leaves (node/2) (by omega) (by change node/2<1048576; change node<2097152 at bounded; omega)
  change heap (node/2)=padLow (oracle.compression (heap (2*(node/2)+1) ++ heap (2*(node/2)))) at parent
  rw [parent]
  by_cases even : node%2=0
  · rw [pathPair,ite_eq_left even,Nat.xor_one_of_even (Nat.even_iff.mpr even)]
    rw [show 2*(node/2)+1=node+1 by omega,show 2*(node/2)=node by omega]
  · have odd : Odd node := Nat.odd_iff.mpr (by omega)
    rw [pathPair,ite_eq_right even,Nat.xor_one_of_odd odd]
    rw [show 2*(node/2)+1=node by omega,show 2*(node/2)=node-1 by omega]

theorem quad_lower_node_range (index : Index) (level : Nat) (within : level<12) :
    2≤lowerNode index level ∧ lowerNode index level<LENGTH/8 := by
  have scaleLow : 16≤(2:Nat)^(level+4) := by
    exact (show 16=(2:Nat)^4 by decide) ▸ Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (by omega)
  have scaleHigh : (2:Nat)^(level+4)≤32768 :=
    (Nat.pow_le_pow_right (by decide : 0<(2:Nat)) (show level+4≤15 by omega)).trans (by decide)
  have fit : index.val<16777216 := index.isLt
  constructor
  · apply (Nat.le_div_iff_mul_le (by positivity : 0<(2:Nat)^(level+4))).mpr
    change 2*2^(level+4)≤16777216+index.val
    omega
  · apply (Nat.div_lt_iff_lt_mul (by positivity : 0<(2:Nat)^(level+4))).mpr
    change 16777216+index.val<2097152*2^(level+4)
    omega

theorem quad_lower_climb (oracle : Oracle) (quad : QuadFunction) (leaves : DigestTape)
    (index : Index) (level : Nat) (within : level<12) :
    let heap := quad2Heap oracle.compression quad leaves
    padLow (oracle.compression (pathPair (lowerNode index level)
      (heap (lowerNode index level)) (heap (lowerNode index level ^^^ 1))))=
        heap (lowerNode index (level+1)) := by
  rw [lower_node_next]
  exact quad_honest_heap_climb oracle quad leaves _ (quad_lower_node_range index level within).1
    (quad_lower_node_range index level within).2

end TwoPermutationPrototype.Quad.Checker
