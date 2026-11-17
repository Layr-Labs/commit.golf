import CommitGolfCandidate.CommitLoop
import CommitGolfCandidate.CopyRefinement
import CommitGolfCandidate.NonceSaltMemory
import CommitGolfCandidate.StreamingRefinement

/-! Salt loading and heap writes of the actual commitment leaf iteration. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Commitment's three digest copies use the same load/store sequence as opening.
Only the source and destination registers differ. -/
theorem commit_copy_memory_as_opening (state : MachineState) (start : Nat)
    (location : start = 55 ∨ start = 79) :
    (commitCopyState state start).mem =
      (openingCopyState
        ((state.setReg .x23 (if start = 46 then state.getReg .x18
          else if start = 55 then state.getReg .x21 else state.getReg .x9+32)).setReg .x25
          (if start = 46 then state.getReg .x21
          else if start = 55 then state.getReg .x23 else state.getReg .x26))).mem := by
  rcases location with rfl | rfl <;>
    rw [commit_copy_expansion, opening_copy_expansion] <;>
    simp [List.foldl, execInstrBr, signExtend12, MachineState.getReg,
      MachineState.setReg, MachineState.setPC, MachineState.setMem, MachineState.getMem, BitVec.add_assoc]

/-- Copy a complete digest from one of the three commitment copy sites. -/
theorem commit_copy_digest (state : MachineState) (start source destination : Nat)
    (location : start = 55 ∨ start = 79)
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

theorem commit_nonce_copy_memory (state : MachineState) :
    (commitCopyState state 46).mem=
      (nonceSaltState (state.setReg .x10 (state.getReg .x21))).mem := by
  rw [commit_copy_expansion]
  simp [nonceSaltState,nonceSaltPrefix,nonceSaltInstructions,List.foldl,execInstrBr,
    signExtend12,MachineState.getReg,MachineState.setReg,MachineState.setPC,
    MachineState.setMem,MachineState.getMem]

theorem commit_nonce_copy_digest (state : MachineState) (source destination : Nat)
    (sourcePointer : state.getReg .x18=BitVec.ofNat 64 source)
    (destinationPointer : state.getReg .x21=BitVec.ofNat 64 destination)
    (sourceAligned : source%8=0) (destinationAligned : destination%8=0)
    (sourceBound : source+32≤2^64) (destinationBound : destination+32≤2^64)
    (separate : source+32≤destination ∨ destination+32≤source) :
    readBuffer (commitCopyState state 46) destination 32=readNonce state source := by
  rw [read_buffer_memory_congr _ _ (commit_nonce_copy_memory state)]
  exact nonce_salt_digest (state.setReg .x10 (state.getReg .x21)) source destination
    (by simpa [MachineState.getReg,MachineState.setReg] using sourcePointer)
    (by simpa [MachineState.getReg,MachineState.setReg] using destinationPointer)
    sourceAligned destinationAligned sourceBound destinationBound separate

theorem commit_copy_preserves_digest (state : MachineState) (start destination address : Nat)
    (location : start = 46 ∨ start = 55 ∨ start = 79)
    (destinationPointer : (if start = 46 then state.getReg .x21
      else if start = 55 then state.getReg .x23 else state.getReg .x26) = BitVec.ofNat 64 destination)
    (aligned : address % 8 = 0)
    (destinationBound : destination+32 ≤ 2^64) (readBound : address+32 ≤ 2^64)
    (separate : address+32 ≤ destination ∨ destination+32 ≤ address) :
    readBuffer (commitCopyState state start) address 32 = readBuffer state address 32 := by
  rcases location with rfl | location
  · rw [read_buffer_memory_congr _ _ (commit_nonce_copy_memory state)]
    exact nonce_salt_preserves_digest (state.setReg .x10 (state.getReg .x21)) destination address
      (by simpa [MachineState.getReg,MachineState.setReg] using destinationPointer)
      aligned destinationBound readBound separate
  · rw [read_buffer_memory_congr _ _ (commit_copy_memory_as_opening state start location)]
    rw [opening_copy_preserves_digest _ destination address
      (by simpa [MachineState.getReg,MachineState.setReg] using destinationPointer)
      aligned destinationBound readBound separate]
    rfl

theorem commit_position_evaluation (oracle : Oracle) (state : MachineState) :
    checkEvaluation oracle (commitPositionRun state) =
      let leaf := checkEvaluation oracle
        (commitLeafLoop (commitLeafReadyState (commitPositionState state)) 8)
      (commitPositionNextState (leaf.1.setPC 4348), leaf.2) := by
  rw [commitPositionRun, check_evaluation_bind]
  simp only [check_evaluation_pure, Nat.add_zero]

theorem commit_chain_pointer (state : MachineState) (source : Nat)
    (chain : state.getReg .x21 = state.getReg .x8 - 32)
    (pointer : state.getReg .x8 = BitVec.ofNat 64 source) (above : 32 ≤ source) :
    state.getReg .x21 = BitVec.ofNat 64 (source - 32) := by
  rw [chain, pointer]
  exact BitVec.ofNat_sub_ofNat_of_le (w := 64) source 32 (by decide) above

theorem commit_position_salt (state : MachineState) (source saltAddress : Nat)
    (chain : state.getReg .x21 = BitVec.ofNat 64 (source-32))
    (saltPointer : state.getReg .x18 = BitVec.ofNat 64 saltAddress)
    (sourceAligned : source % 8 = 0) (aligned : saltAddress % 8 = 0)
    (above : 32 ≤ source) (separate : source ≤ saltAddress)
    (bounded : saltAddress+32 ≤ 2^64) :
    readBuffer (commitLeafReadyState (commitPositionState state)) (source-32) 32 =
      readNonce state saltAddress := by
  change readBuffer (commitCopyState state 46) (source-32) 32 = _
  exact commit_nonce_copy_digest state saltAddress (source-32) saltPointer chain
    aligned (by omega) bounded (by omega) (Or.inr (by omega))

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

attribute [local irreducible] commitPositionState commitLeafLoop checkEvaluation

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
      leafDigest oracle.compression (readNonce state saltAddress) value := by
  let ready := commitLeafReadyState (commitPositionState state)
  let leaf := (checkEvaluation oracle (commitLeafLoop ready 8)).1
  have chain := commit_chain_pointer state source scratch messagePointer sourceAbove
  have readyReg (reg : Reg) (notLink : reg ≠ .x1) (notTemporary : reg ≠ .x6) :
      ready.getReg reg = state.getReg reg := by
    rw [commit_leaf_ready_register]
    exact commit_position_register state reg notLink notTemporary
  have readyPointer := (readyReg .x8 (by decide) (by decide)).trans messagePointer
  have hashed : readBuffer leaf destination 32 =
      leafDigest oracle.compression (readNonce state saltAddress) value := by
    apply streaming_commit_leaf_hash oracle ready source destination _ value readyPointer
      ((readyReg .x23 (by decide) (by decide)).trans heapPointer)
      sourceAligned sourceAbove sourceBound destinationBound
    · exact commit_position_salt state source saltAddress chain saltPointer
        sourceAligned saltAligned sourceAbove (by omega) saltBound
    · intro block inside
      rw [commit_position_input_digest state source (source+32*block) chain sourceAbove
        (by omega) (by omega) (by omega) (Or.inr (by omega))]
      exact data block inside
  rw [commit_position_evaluation]
  change readBuffer leaf destination 32 = _
  exact hashed

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
  rw [commit_position_evaluation]
  change readBuffer leaf address 32 = _
  rw [streaming_commit_leaf_read_outside oracle ready source 7 destination address 32
    readySource readyPointer sourceAbove (by simpa using sourceBound) destinationBound readBound
    (by rcases sourceSeparate with h | h <;> omega) separate]
  exact commit_position_input_digest state source address chain sourceAbove aligned (by omega) readBound
    (by rcases sourceSeparate with h | h <;> omega)

end CommitGolfCandidate
