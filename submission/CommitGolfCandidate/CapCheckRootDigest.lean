import CommitGolfCandidate.CapCheckFinal
import CommitGolfCandidate.CopyRefinement

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
set_option autoImplicit false

theorem cap_check_root_passed_digest (state : MachineState) (rootBase commitment : Nat)
    (roots : state.getReg .x18=BitVec.ofNat 64 rootBase)
    (claimed : state.getReg .x26=BitVec.ofNat 64 commitment)
    (rootAligned : rootBase%8=0) (commitmentAligned : commitment%8=0) :
    (capCheckRootLoop state 0 4).2=true ↔
      readBuffer state (rootBase+32) 32=
        readBuffer state commitment 32 := by
  have rootSlotAligned : (rootBase+32)%8=0 := by omega
  rw [cap_check_root_loop_passed,
    read_digest_eq_iff state state (rootBase+32) commitment rootSlotAligned commitmentAligned]
  constructor
  · intro equal word bounded
    have result := equal word bounded
    unfold CapCheckRootEqual at result
    rw [roots,claimed,Nat.zero_add] at result
    have rootOffset : signExtend12 (BitVec.ofNat 12 (32+8*word))=
        BitVec.ofNat 64 (32+8*word) := by interval_cases word <;> rfl
    have commitmentOffset : signExtend12 (BitVec.ofNat 12 (8*word))=
        BitVec.ofNat 64 (8*word) := by interval_cases word <;> rfl
    rw [rootOffset,commitmentOffset] at result
    simpa only [← BitVec.ofNat_add,Nat.add_assoc] using result
  · intro equal word bounded
    unfold CapCheckRootEqual
    rw [roots,claimed,Nat.zero_add]
    have rootOffset : signExtend12 (BitVec.ofNat 12 (32+8*word))=
        BitVec.ofNat 64 (32+8*word) := by interval_cases word <;> rfl
    have commitmentOffset : signExtend12 (BitVec.ofNat 12 (8*word))=
        BitVec.ofNat 64 (8*word) := by interval_cases word <;> rfl
    rw [rootOffset,commitmentOffset]
    simpa only [← BitVec.ofNat_add,Nat.add_assoc] using equal word bounded

theorem cap_check_final_success (state : MachineState) :
    (capCheckFinalResult state).exit=.success ↔
      state.getReg .x25=state.getReg .x22 ∧
        (capCheckRootLoop (capCheckProofEndState state) 0 4).2=true := by
  by_cases exhausted : state.getReg .x25=state.getReg .x22
  · simp only [capCheckFinalResult,if_pos exhausted,Execution.charge,exhausted,true_and]
    cases passed : (capCheckRootLoop (capCheckProofEndState state) 0 4).2
    · simp only [capCheckRootResult,passed,Bool.false_eq_true,↓reduceIte]
      simp
    · simp only [capCheckRootResult,passed,↓reduceIte]
  · simp only [capCheckFinalResult,if_neg exhausted,exhausted,false_and]
    simp

end CommitGolfCandidate
