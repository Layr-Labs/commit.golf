import CommitGolfCandidate.TwoPermutationPackedLowerRecursion
import CommitGolfCandidate.TwoPermutationPackedLevelSpec
import CommitGolfCandidate.TwoPermutationPackedLevel

namespace TwoPermutationPrototype.Packed.Checker
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192

def adaptLowerStep (step : Oracle → MachineState → Nat → Nat → Nat → RecordBlock) (oracle : Oracle) (ordinal : Nat) (index : Index) (level : Nat)
    (state : MachineState) : RecordBlock :=
  step oracle state (Opening.lowerNode index (level+2)) (lowerProofByte ordinal level) (14-level)

/-- The lower-loop step of loop levels 0..4 (32-byte siblings at levels 0 and 1, the level-21 node whole). -/
def lowStep : Oracle → Nat → Index → Nat → MachineState → RecordBlock := adaptLowerStep levelResult

theorem low_step_facts (oracle : Oracle) (ordinal : Nat) (index : Index) (level : Nat) (state : MachineState)
    (low : level ≤ 4) (room : checkProofByte ordinal+536 ≤ MEMORY_BYTES)
    (cursor : LowerCursor ordinal index level state) :
    LowerStepFacts oracle ordinal index level state (lowStep oracle ordinal index level state) := by
  let node := Opening.lowerNode index (level+2)
  let proof := lowerProofByte ordinal level
  let left := 14-level
  have wideEq : wideSibling left = decide (level ≤ 1) := by
    unfold wideSibling; unfold left
    by_cases h : level ≤ 1
    · rw [decide_eq_true h, decide_eq_true (by omega)]
    · rw [decide_eq_false h, decide_eq_false (by omega)]
  have widthEq : width (wideSibling left) = lowerSiblingWidth level := by
    rw [wideEq, lower_sibling_width_low level low]; unfold width
    by_cases h : level ≤ 1
    · rw [decide_eq_true h, if_pos h]; rfl
    · rw [decide_eq_false h, if_neg h]; rfl
  have wireEq : wire state proof (wideSibling left) = lowerWireSibling state ordinal level := by
    rw [wideEq, lower_wire_sibling_low state ordinal level low]; unfold wire
    by_cases h : level ≤ 1
    · rw [decide_eq_true h, if_pos h]; rfl
    · rw [decide_eq_false h, if_neg h]; rfl
  have projectEq (x : BitVec 256) : levelProject left x = nodeKeep (Opening.lowerNode index (level+3)) x := by
    rw [node_keep_lower_low index level low x]
    unfold levelProject; unfold left
    by_cases h : level = 0
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  have bounds := lower_proof_byte_bounds ordinal level (by omega) room
  have nodeBound : node < 2^64 := by
    have fit := Opening.lower_node_bound index (level+2)
    change Opening.lowerNode index (level+2) < 33554432 at fit
    exact fit.trans (by decide)
  have ready : LevelReady state node proof left :=
    ⟨cursor.pc.trans (ite_eq_right (by omega)),cursor.node,cursor.proof,cursor.counter,
      cursor.digest,cursor.pair,cursor.selector,cursor.syscallBytes,cursor.syscallSelector,
      nodeBound,by unfold left; omega,by unfold left; omega,bounds.1,bounds.2.1,
      by rw [widthEq]; exact bounds.2.2⟩
  have realStep := levelFacts oracle state node proof left ready
  change LowerStepFacts oracle ordinal index level state (levelResult oracle state node proof left)
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,realStep.syscallBytes,realStep.syscallSelector⟩,
    realStep.cost,realStep.saved,realStep.frame,?_,?_,realStep.run⟩
  · simpa only [show left=1 ↔ level+1=14 by unfold left; omega] using realStep.pc
  · rw [show level+1+2 = (level+2)+1 by omega, Opening.lower_node_next index (level+2)]
    exact realStep.nodeReg
  · rw [lower_proof_byte_next ordinal level (by omega),← widthEq]
    exact realStep.proofReg
  · rw [show 14-(level+1)=left-1 by unfold left; omega]
    exact realStep.counter
  · exact (realStep.saved .x23 (by decide)).trans cursor.digest
  · exact (realStep.saved .x24 (by decide)).trans cursor.pair
  · exact (realStep.saved .x5 (by decide)).trans cursor.selector
  · have pairEq : levelPair state node proof left = pathPair (Opening.lowerNode index (level+2))
        (readBuffer state 12288 32) (lowerWireSibling state ordinal level) := by
      show pathPair node (readBuffer state 12288 32) (wire state proof (wideSibling left)) = _
      rw [wireEq] <;> rfl
    show readBuffer (levelResult oracle state node proof left).state 12288 32 =
      nodeKeep (Opening.lowerNode index (level+3)) (oracle.compression (pathPair (Opening.lowerNode index (level+2))
        (readBuffer state 12288 32) (lowerWireSibling state ordinal level)))
    rw [← pairEq]
    exact realStep.digest.trans (projectEq _)
  · simpa only [levelPair,wireEq] using realStep.row

end TwoPermutationPrototype.Packed.Checker
