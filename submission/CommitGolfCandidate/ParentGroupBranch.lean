import CommitGolfCandidate.ParentSequence

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def ParentGroupBranchFetched (image : Image) (pc : Word) (offset : BitVec 13) : Prop :=
  ∀ state : MachineState, state.pc=pc → fetch image state=some (.base (.BNE .x12 .x9 offset))

theorem parent_group_branch (image : Image) (branchPC target : Word) (offset : BitVec 13)
    (fetched : ParentGroupBranchFetched image branchPC offset)
    (jump : branchPC+signExtend13 offset=target)
    (state : MachineState) (remaining : Nat) (bounded : remaining<2^24)
    (pointers : ParentPointerInvariant state remaining) (fuel : Nat) :
    execute image (1+fuel) (state.setPC branchPC) true=
      (do let result ← execute image fuel
            (state.setPC (if remaining=0 then branchPC+4 else target)) true
          return result.charge 1 0) := by
  have done : state.getReg .x12=state.getReg .x9 ↔ remaining=0 := by
    rw [pointers.2,parent_pointer_done_iff _ remaining bounded]
  change state.regs .x12=state.regs .x9 ↔ remaining=0 at done
  have stepped : ordinaryStep (state.setPC branchPC) (.base (.BNE .x12 .x9 offset))=
      some (state.setPC (if remaining=0 then branchPC+4 else target)) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
      MachineState.getReg,MachineState.getReg_setPC,MachineState.setPC,done,jump]
    split <;> simp_all
  rw [Nat.add_comm 1 fuel,execute_ordinary_step _ _ _ _ _ _
    (fetched (state.setPC branchPC) rfl) stepped]
  rfl

theorem parent_group_sequence (image : Image) (start branchPC target : Word)
    (offset : BitVec 13) (count : Nat)
    (sequenceFetched : ParentSequenceFetched image start count)
    (branchFetched : ParentGroupBranchFetched image branchPC offset)
    (endPC : parentSequenceEnd start count=branchPC)
    (jump : branchPC+signExtend13 offset=target)
    (state : MachineState) (remaining : Nat) (bounded : remaining<2^24)
    (pointers : ParentPointerInvariant state (remaining+count))
    (constants : state.getReg .x5=0 ∧ state.getReg .x11=64 ∧ state.getReg .x13=0)
    (buffers : ParentBuffers (state.getReg .x9) (remaining+count)) (fuel : Nat) :
    execute image (3*count+1+fuel) (state.setPC start) true=
      (do let finished ← commitParents state count
          let result ← execute image fuel
            (finished.setPC (if remaining=0 then branchPC+4 else target)) true
          return result.charge (10*count+1) count) := by
  rw [show 3*count+1+fuel=3*count+(1+fuel) by omega,
    parent_sequence image start count remaining sequenceFetched state pointers constants buffers]
  apply bind_congr_of_forall_mem_support
  intro finished reached
  have invariants := parent_sequence_invariant state count remaining pointers constants buffers finished reached
  rw [endPC,parent_group_branch image branchPC target offset branchFetched jump finished remaining bounded invariants.1]
  simp [Execution.charge,← Nat.add_assoc]

end CommitGolfCandidate
