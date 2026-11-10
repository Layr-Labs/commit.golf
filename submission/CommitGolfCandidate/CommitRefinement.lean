import CommitGolfCandidate.CommitLoop
import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.StreamingRefinement

/-! Salt loading and heap writes of the actual commitment leaf iteration. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Commitment's three digest copies use the same load/store sequence as opening.
Only the source and destination registers differ. -/
theorem commit_copy_memory_as_opening (state : MachineState) (start : Nat)
    (location : start = 46 ∨ start = 55 ∨ start = 79) :
    (commitCopyState state start).mem =
      (openingCopyState
        ((state.setReg .x23 (if start = 46 then state.getReg .x18
          else if start = 55 then state.getReg .x21 else state.getReg .x9+32)).setReg .x25
          (if start = 46 then state.getReg .x21
          else if start = 55 then state.getReg .x23 else state.getReg .x26))).mem := by
  rcases location with rfl | rfl | rfl <;>
    rw [commit_copy_expansion, opening_copy_expansion] <;>
    simp [List.foldl, execInstrBr, signExtend12, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, MachineState.setMem, MachineState.getMem, BitVec.add_assoc]

/-- Copy a complete digest from one of the three commitment copy sites. -/
theorem commit_copy_digest (state : MachineState) (start source destination : Nat)
    (location : start = 46 ∨ start = 55 ∨ start = 79)
    (sourcePointer : (if start = 46 then state.getReg .x18
      else if start = 55 then state.getReg .x21 else state.getReg .x9+32) = BitVec.ofNat 64 source)
    (destinationPointer : (if start = 46 then state.getReg .x21
      else if start = 55 then state.getReg .x23 else state.getReg .x26) = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (destinationAligned : destination % 8 = 0)
    (sourceBound : source+32 ≤ 2^64) (destinationBound : destination+32 ≤ 2^64)
    (separate : source+32 ≤ destination ∨ destination+32 ≤ source) :
    readBuffer (commitCopyState state start) destination 32 = readBuffer state source 32 := by
  rw [read_buffer_memory_congr _ _ (commit_copy_memory_as_opening state start location)]
  rw [opening_copy_digest _ source destination (by simpa [MachineState.getReg, MachineState.setReg] using sourcePointer)
    (by simpa [MachineState.getReg, MachineState.setReg] using destinationPointer) sourceAligned destinationAligned sourceBound destinationBound separate]
  rfl

/-- The commitment copy preserves every disjoint complete digest. -/
theorem commit_copy_preserves_digest (state : MachineState) (start destination address : Nat)
    (location : start = 46 ∨ start = 55 ∨ start = 79)
    (destinationPointer : (if start = 46 then state.getReg .x21
      else if start = 55 then state.getReg .x23 else state.getReg .x26) = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (commitCopyState state start) address 32 = readBuffer state address 32 := by
  rw [read_buffer_memory_congr _ _ (commit_copy_memory_as_opening state start location)]
  rw [opening_copy_preserves_digest _ destination address (by simpa [MachineState.getReg, MachineState.setReg] using destinationPointer)
    aligned destinationBound readBound separate]
  rfl

/-- A complete leaf iteration evaluates the leaf subroutine, then copies its
result into the heap. This equality retains the actual interpreter memory state. -/
theorem commit_position_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (commitPositionRun state) =
      let leaf := checkEvaluation oracle
        (commitLeafLoop (commitLeafReadyState (commitPositionState state)) 8)
      (commitPositionNextState (commitCopyState (leaf.1.setPC 4316) 55), leaf.2) := by
  rw [commitPositionRun, check_evaluation_bind]
  simp only [check_evaluation_pure, Nat.add_zero]

/-- Convert the moving chain register to its nonwrapping natural address. -/
theorem commit_chain_pointer (state : MachineState) (source : Nat)
    (chain : state.getReg .x21 = state.getReg .x8 - 32)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 source) (above : 32 ≤ source) :
    state.getReg .x21 = BitVec.ofNat 64 (source - 32) := by
  rw [chain, pointer]
  exact BitVec.ofNat_sub_ofNat_of_le (w := 64) source 32 (by decide) above

/-- The salt initializes the chain prefix immediately before the leaf. -/
theorem commit_position_salt (state : MachineState) (source saltAddress : Nat)
    (chain : state.getReg .x21 = BitVec.ofNat 64 (source-32))
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (sourceAligned : source % 8 = 0) (aligned : saltAddress % 8 = 0)
    (above : 32 ≤ source) (separate : source ≤ saltAddress)
    (bounded : saltAddress+32 ≤ 2^64) :
    readBuffer (commitLeafReadyState (commitPositionState state)) (source-32) 32 =
      readBuffer state saltAddress 32 := by
  change readBuffer (commitCopyState state 46) (source-32) 32 = _
  exact commit_copy_digest state 46 saltAddress (source-32) (by simp) saltPointer chain
    aligned (by omega) bounded (by omega) (Or.inr (by omega))

/-- Salt initialization preserves any digest disjoint from the moving prefix. -/
theorem commit_position_input_digest (state : MachineState) (source address : Nat)
    (chain : state.getReg .x21 = BitVec.ofNat 64 (source-32))
    (above : 32 ≤ source) (aligned : address % 8 = 0)
    (sourceBound : source ≤ 2^64) (bounded : address+32 ≤ 2^64)
    (separate : address+32 ≤ source-32 ∨ source ≤ address) :
    readBuffer (commitLeafReadyState (commitPositionState state)) address 32 =
      readBuffer state address 32 := by
  change readBuffer (commitCopyState state 46) address 32 = _
  exact commit_copy_preserves_digest state 46 (source-32) address (by simp) chain aligned
    (by omega) bounded (by rcases separate with h | h <;> omega)

/-- Copy the final consumed block into the heap before the next salt overwrites it. -/
theorem commit_leaf_heap_write (leaf : MachineState) (source destination : Nat)
    (chain : leaf.getReg .x21 = BitVec.ofNat 64 (source+224))
    (heapPointer : leaf.getReg .x23 = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (aligned : destination % 8 = 0)
    (separate : source+256 ≤ destination) (bounded : destination+32 ≤ 2^64) :
    readBuffer (commitPositionNextState (commitCopyState (leaf.setPC 4316) 55)) destination 32 =
      readBuffer leaf (source+224) 32 := by
  change readBuffer (commitCopyState (leaf.setPC 4316) 55) destination 32 = _
  exact commit_copy_digest (leaf.setPC 4316) 55 (source+224) destination (by simp) chain heapPointer
    (by omega) aligned (by omega) bounded (Or.inl separate)

private theorem commit_heap_write_preserves (leaf : MachineState) (destination address : Nat)
    (heapPointer : leaf.getReg .x23 = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (commitPositionNextState (commitCopyState (leaf.setPC 4316) 55)) address 32 =
      readBuffer leaf address 32 := by
  change readBuffer (commitCopyState (leaf.setPC 4316) 55) address 32 = _
  exact commit_copy_preserves_digest (leaf.setPC 4316) 55 destination address (by simp)
    heapPointer aligned destinationBound readBound separate

attribute [local irreducible] commitPositionState commitLeafLoop checkEvaluation

/-- The actual streamed iteration computes the existing salted leaf hash. -/
theorem commit_position_digest (oracle : Oracle) (state : MachineState)
    (source saltAddress destination : Nat) (value : Entry)
    (scratch : state.getReg .x21 = state.getReg .x8 - 32)
    (messagePointer : state.getReg .x8 = BitVec.ofNat 64 source)
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 destination)
    (sourceAligned : source % 8 = 0) (saltAligned : saltAddress % 8 = 0)
    (destinationAligned : destination % 8 = 0)
    (sourceAbove : 32 ≤ source) (saltAfter : source+256 ≤ saltAddress)
    (destinationAfter : source+256 ≤ destination)
    (sourceBound : source+256 < 2^64) (saltBound : saltAddress+32 ≤ 2^64)
    (destinationBound : destination+32 ≤ 2^64)
    (data : ∀ block < 8, readBuffer state (source+32*block) 32 = value.extractLsb' (256*block) 256) :
    readBuffer (checkEvaluation oracle (commitPositionRun state)).1 destination 32 =
      leafDigest oracle.compression (readBuffer state saltAddress 32) value := by
  let ready := commitLeafReadyState (commitPositionState state)
  let leaf := (checkEvaluation oracle (commitLeafLoop ready 8)).1
  have chain := commit_chain_pointer state source scratch messagePointer sourceAbove
  have readyReg (reg : Reg) (notLink : reg ≠ .x1) (notTemporary : reg ≠ .x6) :
      ready.getReg reg = state.getReg reg := by
    rw [commit_leaf_ready_register]
    exact commit_position_register state reg notLink notTemporary
  have readyPointer := (readyReg .x8 (by decide) (by decide)).trans messagePointer
  have hashed : readBuffer leaf (source+224) 32 =
      leafDigest oracle.compression (readBuffer state saltAddress 32) value := by
    apply streaming_commit_leaf_hash oracle ready source _ value readyPointer
      sourceAligned sourceAbove sourceBound
    · exact commit_position_salt state source saltAddress chain saltPointer
        sourceAligned saltAligned sourceAbove (by omega) saltBound
    · intro block inside
      rw [commit_position_input_digest state source (source+32*block) chain sourceAbove
        (by omega) (by omega) (by omega) (Or.inr (by omega))]
      exact data block inside
  have reached := check_evaluation_support oracle (commitLeafLoop ready 8)
  have leafRegs := commit_leaf_loop_registers ready 8 leaf reached
  have finalChain : leaf.getReg .x21 = BitVec.ofNat 64 (source+224) := by
    rw [commit_leaf_loop_chain ready 8 leaf reached, readyPointer]
    change BitVec.ofNat 64 source + BitVec.ofNat 64 256 - BitVec.ofNat 64 32 = _
    rw [← BitVec.ofNat_add, BitVec.ofNat_sub_ofNat_of_le (w := 64) (source+256) 32 (by decide) (by omega)]
    congr 1
  rw [commit_position_evaluation]
  change readBuffer (commitPositionNextState (commitCopyState (leaf.setPC 4316) 55)) destination 32 = _
  rw [commit_leaf_heap_write leaf source destination finalChain
    ((leafRegs.2 .x23 (by decide)).trans ((readyReg .x23 (by decide) (by decide)).trans heapPointer))
    sourceAligned destinationAligned destinationAfter destinationBound]
  exact hashed

/-- A full iteration writes only its consumed prefix/leaf and one heap slot. -/
theorem commit_position_preserves_digest (oracle : Oracle) (state : MachineState)
    (source destination address : Nat)
    (scratch : state.getReg .x21 = state.getReg .x8 - 32)
    (messagePointer : state.getReg .x8 = BitVec.ofNat 64 source)
    (heapPointer : state.getReg .x23 = BitVec.ofNat 64 destination)
    (sourceAbove : 32 ≤ source) (sourceBound : source+256 < 2^64)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (sourceSeparate : address+32 ≤ source-32 ∨ source+256 ≤ address)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (checkEvaluation oracle (commitPositionRun state)).1 address 32 =
      readBuffer state address 32 := by
  let ready := commitLeafReadyState (commitPositionState state)
  let leaf := (checkEvaluation oracle (commitLeafLoop ready 8)).1
  have chain := commit_chain_pointer state source scratch messagePointer sourceAbove
  have readySource : ready.getReg .x8 = BitVec.ofNat 64 source := by
    rw [commit_leaf_ready_register]
    exact (commit_position_register state .x8 (by decide) (by decide)).trans messagePointer
  have readyPointer : ready.getReg .x23 = BitVec.ofNat 64 destination := by
    rw [commit_leaf_ready_register]
    exact (commit_position_register state .x23 (by decide) (by decide)).trans heapPointer
  have leafPointer : leaf.getReg .x23 = BitVec.ofNat 64 destination :=
    ((commit_leaf_loop_registers ready 8 leaf (check_evaluation_support oracle _)).2 .x23
      (by decide)).trans readyPointer
  rw [commit_position_evaluation]
  change readBuffer (commitPositionNextState (commitCopyState (leaf.setPC 4316) 55)) address 32 = _
  rw [commit_heap_write_preserves leaf destination address leafPointer aligned destinationBound readBound separate]
  rw [streaming_commit_leaf_read_outside oracle ready source 8 address 32 readySource sourceAbove
    (by simpa using sourceBound) readBound (by rcases sourceSeparate with h | h <;> omega)]
  exact commit_position_input_digest state source address chain sourceAbove aligned (by omega) readBound
    (by rcases sourceSeparate with h | h <;> omega)

end CommitGolfCandidate
