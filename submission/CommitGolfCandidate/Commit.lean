import CommitGolfCandidate.CommitLeaf

/-! Commitment execution: initialize the heap and salt pointers, sample all private
salts, hash the leaves, and build the parent nodes. These proofs use the submitted
instruction image and the challenge interpreter. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def commitLoad (reg : Reg) (high : BitVec 12) : List Instr :=
  [.LUI reg (BitVec.ofNat 20 (high.toNat * 1024)), .JAL .x0 24]

private def commitSetupInstructions : List Instr :=
  [.ADDI .x9 .x12 0,.ADDI .x12 .x10 0,.ADDI .x26 .x11 0] ++
  commitLoad .x19 4 ++ commitLoad .x6 256 ++ [.ADD .x18 .x9 .x6] ++
  commitLoad .x6 128 ++ [.ADD .x23 .x9 .x6, .ADDI .x5 .x0 2, .ADDI .x10 .x18 0] ++
  commitLoad .x11 128

private def commitSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitSetupInstructions.take count).foldl execInstrBr state

def commitSetupState (state : MachineState) : MachineState := commitSetupPrefix state 15

set_option maxHeartbeats 1000000 in
/-- The 15-instruction setup computes pointers into the admitted private trapdoor
and the total salt length; it performs no memory access or oracle call. -/
theorem commit_setup (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (15 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitSetupState state) allowCoins
          return result.charge 15 0) := by
  apply execute_unit_steps (states := commitSetupPrefix state)
  intro i hi
  refine ⟨.base ((commitSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (([0,1,2,3,4,10,11,17,18,19,25,26,27,28,29] : List Nat)[i]!) _ (by interval_cases i <;> decide)
    · interval_cases i <;>
        simp [commitSetupPrefix, commitSetupInstructions, commitLoad, execInstrBr, signExtend21, pc,
          MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- Exact ABI-derived registers at the randomness syscall. -/
theorem commit_setup_registers (state : MachineState) :
    (commitSetupState state).getReg .x5 = 2 ∧
    (commitSetupState state).getReg .x12 = state.getReg .x10 ∧
    (commitSetupState state).getReg .x9 = state.getReg .x12 ∧
    (commitSetupState state).getReg .x10 = state.getReg .x12 + 1073741824 ∧
    (commitSetupState state).getReg .x11 = 536870912 ∧
    (commitSetupState state).getReg .x18 = state.getReg .x12 + 1073741824 ∧
    (commitSetupState state).getReg .x19 = 16777216 ∧
    (commitSetupState state).getReg .x23 = state.getReg .x12 + 536870912 ∧
    (commitSetupState state).getReg .x26 = state.getReg .x11 := by
  dsimp only [commitSetupState, commitSetupPrefix, commitSetupInstructions, commitLoad,
    List.append, List.take, List.foldl, execInstrBr, signExtend12,
    MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp [execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem commit_setup_pc (state : MachineState) (pc : state.pc = 4096) :
    (commitSetupState state).pc = 4236 := by
  simp [commitSetupState, commitSetupPrefix, commitSetupInstructions, commitLoad,
    execInstrBr, signExtend21, MachineState.setPC, pc]

/-- The real RANDOM syscall samples the salt buffer with private coins. Its cost is
one cycle plus one cycle per eight bytes; it makes no public oracle queries. -/
theorem commit_random (state : MachineState) (pc : state.pc = 4236)
    (selector : state.getReg .x5 = 2) (valid : randomArgumentsValid state = true)
    (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let answer ← liftM ($ᵗ BitVec (8 * (state.getReg .x11).toNat) :
            ProbComp (BitVec (8 * (state.getReg .x11).toNat)))
          let result ← execute (submission.image .commit) fuel
            (writeBits state (state.getReg .x10) answer) true
          return result.charge (1 + ((state.getReg .x11).toNat + 7) / 8) 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base .ECALL) := by
    apply commit_fetch _ 35 _ (by decide) pc; rfl
  rw [Nat.add_comm 1 fuel, execute, fetched]
  simp only [selector, valid]
  rfl

private def commitReadyInstructions : List Instr :=
  [.ADDI .x10 .x12 (-32),.ADDI .x5 .x0 0,.ADDI .x11 .x0 64,
   .ADDI .x13 .x0 0,.JAL .x0 24]

private def commitReadyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitReadyInstructions.take count).foldl execInstrBr state

def commitReadyState (state : MachineState) : MachineState := commitReadyPrefix state 5

/-- Initialize the first input pointer and fixed compression arguments after sampling salts.
The actual ABI and setup preserve the counters needed by the loop. -/
theorem commit_ready (state : MachineState) (pc : state.pc = 4240) (fuel : Nat) :
    execute (submission.image .commit) (5 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitReadyState state) true
          return result.charge 5 0) := by
  apply execute_unit_steps (states := commitReadyPrefix state)
  intro i hi
  refine ⟨.base ((commitReadyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (36 + i) _ (by omega)
    · interval_cases i <;>
        simp [commitReadyPrefix, commitReadyInstructions, execInstrBr, signExtend21, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem commit_ready_pc (state : MachineState) (pc : state.pc = 4240) :
    (commitReadyState state).pc = 4280 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr, signExtend21, pc, MachineState.setPC]

theorem commit_ready_counters (state : MachineState) :
    (commitReadyState state).getReg .x10 = state.getReg .x12 - 32 ∧ (commitReadyState state).getReg .x20 = state.getReg .x20 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]

theorem commit_ready_register (state : MachineState) (reg : Reg)
    (notScratch : reg ≠ .x10) (notCounter : reg ≠ .x20)
    (notArguments : reg ∉ [.x5,.x10,.x11,.x13,.x28]) :
    (commitReadyState state).getReg reg = state.getReg reg := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at notArguments
  rcases notArguments with ⟨not5,not10,not11,not13,not28⟩
  simp only [commitReadyState,commitReadyPrefix,commitReadyInstructions,List.take,List.foldl,execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notCounter),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not5),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not10),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not13),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28)]
  cases reg <;> simp_all [MachineState.setReg, MachineState.getReg, MachineState.setPC]

/-- The fixed oracle arguments are initialized once; untouched counters retain their input values. -/
theorem commit_ready_oracle (state : MachineState) : CommitLeafOracleReady (commitReadyState state) := by
  simp [commitReadyState,commitReadyPrefix,commitReadyInstructions,CommitLeafOracleReady, StreamingOracleReady,
    execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,MachineState.setPC]

theorem commit_ready_block_counter (state : MachineState) :
    (commitReadyState state).getReg .x28=state.getReg .x28 := rfl

private def commitCopySource (start : Nat) : Reg :=
  if start = 46 then .x18 else if start = 55 then .x10 else .x9
private def commitCopyDestination (start : Nat) : Reg :=
  if start = 46 then .x10 else if start = 55 then .x23 else .x26
private def commitCopyOffset (start : Nat) : Nat := if start = 91 then 32 else 0

private def commitCopyInstructions (start : Nat) : List Instr :=
  [.LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start)),
   .SD (commitCopyDestination start) .x6 0,
   .LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start + 8)),
   .SD (commitCopyDestination start) .x6 8,
   .LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start + 16)),
   .SD (commitCopyDestination start) .x6 16,
   .LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start + 24)),
   .SD (commitCopyDestination start) .x6 24]

private def commitCopyPrefix (state : MachineState) (start count : Nat) : MachineState :=
  ((commitCopyInstructions start).take count).foldl execInstrBr state

def commitCopyState (state : MachineState) (start : Nat) : MachineState := commitCopyPrefix state start 8

/-- Expose the decoded salt, leaf, and root copy instructions for memory refinement. -/
theorem commit_copy_expansion (state : MachineState) (start : Nat) :
    commitCopyState state start =
      let source := if start = 46 then Reg.x18 else if start = 55 then Reg.x10 else Reg.x9
      let destination := if start = 46 then Reg.x10 else if start = 55 then Reg.x23 else Reg.x26
      let offset := if start = 91 then 32 else 0
      ([.LD .x6 source (BitVec.ofNat 12 offset), .SD destination .x6 0,
        .LD .x6 source (BitVec.ofNat 12 (offset+8)), .SD destination .x6 8,
        .LD .x6 source (BitVec.ofNat 12 (offset+16)), .SD destination .x6 16,
        .LD .x6 source (BitVec.ofNat 12 (offset+24)), .SD destination .x6 24] : List Instr).foldl
          execInstrBr state := rfl

private theorem commit_copy_prefix_register (state : MachineState) (start count : Nat)
    (bounded : count ≤ 8) (reg : Reg) (notTemporary : reg ≠ .x6) :
    (commitCopyPrefix state start count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [commitCopyPrefix, commitCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notTemporary)]

theorem commit_copy_register (state : MachineState) (start : Nat) (reg : Reg) (notTemporary : reg ≠ .x6) :
    (commitCopyState state start).getReg reg = state.getReg reg :=
  commit_copy_prefix_register state start 8 (by decide) reg notTemporary

theorem commit_copy_pc (state : MachineState) (start : Nat) :
    (commitCopyState state start).pc = state.pc + 32 := by
  simp [commitCopyState, commitCopyPrefix, commitCopyInstructions, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

set_option maxHeartbeats 1000000 in
/-- The actual salt load, leaf-digest store, and final root copy each take eight
ordinary instructions. The hypotheses cover every source and destination access. -/
theorem commit_copy (state : MachineState) (start : Nat)
    (location : start = 46 ∨ start = 91)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg (commitCopySource start) +
        BitVec.ofNat 64 (commitCopyOffset start + 8 * word.val)) 8 = true)
    (destinationValid : ∀ word : Fin 4,
      accessValid (state.getReg (commitCopyDestination start) +
        BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitCopyState state start) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := commitCopyPrefix state start)
  intro i hi
  refine ⟨.base (((commitCopyInstructions start)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (start + i) _ (by rcases location with rfl | rfl <;> omega)
    · rcases location with rfl | rfl <;> interval_cases i <;>
        simp [commitCopyPrefix, commitCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl | rfl <;> interval_cases i <;> rfl
  · have sourceReg := commit_copy_prefix_register state start i (by omega) (commitCopySource start)
      (by rcases location with rfl | rfl <;> decide)
    have destinationReg := commit_copy_prefix_register state start i (by omega) (commitCopyDestination start)
      (by rcases location with rfl | rfl <;> decide)
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have d0 := destinationValid ⟨0, by decide⟩
    have d1 := destinationValid ⟨1, by decide⟩
    have d2 := destinationValid ⟨2, by decide⟩
    have d3 := destinationValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (commitCopyPrefix state start i)
        (((commitCopyInstructions start)[i]?).getD .EBREAK) = true := by
      rcases location with rfl | rfl <;> interval_cases i <;>
        simp only [commitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, destinationReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [commitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- The salt copy falls directly into the contiguous streaming leaf. -/
def commitLeafCallState (state : MachineState) : MachineState := state.setPC 4312

/-- Advance the two output pointers and branch on the consumed message range. -/
def commitPositionNextState (state : MachineState) : MachineState :=
  ((state.setReg .x18 (state.getReg .x18+32)).setReg .x23 (state.getReg .x23+32)).setPC
    (if BitVec.ult (state.getReg .x12) (state.getReg .x26) then 4280 else 4420)

private def commitNextPrefix (state : MachineState) (count : Nat) : MachineState :=
  ([.ADDI .x18 .x18 32,.ADDI .x23 .x23 32].take count).foldl execInstrBr state

theorem commit_next_pc_irrel (state : MachineState) (pc : Word) :
    commitPositionNextState (state.setPC pc)=commitPositionNextState state := by
  cases state
  rfl

theorem commit_leaf_next_position (state : MachineState) (pc : state.pc=4408) (fuel : Nat) :
    execute (submission.image .commit) (3+fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitPositionNextState state) true
          return result.charge 3 0) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (2+remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (commitNextPrefix state 2) true
            return result.charge 2 0) := by
    apply execute_unit_steps (states := commitNextPrefix state)
    intro i hi
    refine ⟨.base (([.ADDI .x18 .x18 32,.ADDI .x23 .x23 32][i]?).getD .EBREAK),?_,?_,?_⟩
    · apply commit_fetch _ (78+i) _ (by omega)
      · interval_cases i <;> simp [commitNextPrefix,execInstrBr,pc,MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (commitNextPrefix state 2) =
      some (.base (.BLTU .x12 .x26 8056)) := by
    apply commit_fetch _ 80 _ (by decide)
    · simp [commitNextPrefix,execInstrBr,pc,MachineState.setPC]
    · rfl
  have stepped : ordinaryStep (commitNextPrefix state 2) (.base (.BLTU .x12 .x26 8056)) =
      some (commitPositionNextState state) := by
    simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,signExtend13,signExtend12,
      commitNextPrefix,commitPositionNextState,MachineState.getReg,MachineState.setReg,
      MachineState.setPC,pc]
    split <;> simp_all
  rw [show 3+fuel=2+(fuel+1) by omega,setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles,Execution.charge,← Nat.add_assoc]

def commitPositionState (state : MachineState) : MachineState :=
  commitLeafCallState (commitCopyState state 46)

theorem commit_position_register (state : MachineState) (reg : Reg)
    (notLink : reg ≠ .x1) (notTemporary : reg ≠ .x6) :
    (commitPositionState state).getReg reg = state.getReg reg := by
  simp only [commitPositionState, commitLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notLink),
    commit_copy_register _ _ reg notTemporary]

/-- The exact state distribution after one salt/leaf/digest iteration. -/
def commitPositionRun (state : MachineState) : OracleComp World MachineState := do
  let leaf ← commitLeafLoop (commitLeafReadyState (commitPositionState state)) 8
  return commitPositionNextState (leaf.setPC 4408)

set_option maxHeartbeats 1000000 in
/-- Load the salt into the consumed prefix, stream eight compression queries,
store the digest, and advance. The exact cost is 35 instructions and 91 cycles. -/
theorem commit_position (state : MachineState) (pc : state.pc = 4280)
    (scratch : state.getReg .x10 = state.getReg .x12 - 32)
    (above : 32 ≤ (state.getReg .x12).toNat)
    (oracleReady : CommitLeafOracleReady state) (blockCounter : state.getReg .x28=0)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heapValid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (messageValid : ∀ word < 32,
      accessValid (state.getReg .x12 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (35 + fuel) state true =
      (do let finished ← commitPositionRun state
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 91 8) := by
  let ready := commitPositionState state
  let initialized := commitLeafReadyState ready
  obtain ⟨aligned, bounded⟩ := commit_leaf_source_range state messageValid
  have source : state.getReg .x12 = BitVec.ofNat 64 (state.getReg .x12).toNat := by
    simp
  have chainPrefix : state.getReg .x10 = BitVec.ofNat 64 ((state.getReg .x12).toNat - 32) := by
    rw [scratch]
    calc
      state.getReg .x12 - 32 = BitVec.ofNat 64 (state.getReg .x12).toNat - BitVec.ofNat 64 32 :=
        congrArg (fun value : Word => value - 32) source
      _ = _ := BitVec.ofNat_sub_ofNat_of_le (w := 64) _ 32 (by decide) above
  have scratchValid : ∀ word : Fin 4,
      accessValid (state.getReg .x10 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    intro word
    rw [chainPrefix, ← BitVec.ofNat_add]
    have small : (state.getReg .x12).toNat - 32 + 8 * word.val < 2^64 := by
      have hw := word.isLt; unfold MEMORY_BYTES at bounded; omega
    simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small,
      Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · have hw := word.isLt; omega
    · omega
  have copyPC : (commitCopyState state 46).pc = 4312 := by rw [commit_copy_pc, pc]; rfl
  have readyPC : ready.pc = 4312 := rfl
  have readySource : ready.getReg .x12 = state.getReg .x12 :=
    commit_position_register state .x12 (by decide) (by decide)
  have readyOracle : CommitLeafOracleReady ready := by
    rcases oracleReady with ⟨r5,r11,r13⟩
    exact ⟨(commit_position_register state .x5 (by decide) (by decide)).trans r5,
      (commit_position_register state .x11 (by decide) (by decide)).trans r11,
      (commit_position_register state .x13 (by decide) (by decide)).trans r13⟩
  have readyHeap : rangeValid (ready.getReg .x23) 32 = true ∧
      (ready.getReg .x23).toNat % 8 = 0 := by
    rw [commit_position_register state .x23 (by decide) (by decide)]
    exact commit_leaf_heap_range state heapValid
  have readyInput : ready.getReg .x10=BitVec.ofNat 64 ((ready.getReg .x12).toNat-32) := by
    rw [commit_position_register state .x10 (by decide) (by decide),readySource]
    exact chainPrefix
  have leafRun := commit_leaf_subroutine ready readyPC readyInput readyOracle
    (by simpa [readySource] using aligned) (by simpa [readySource] using above)
    (by simpa [readySource] using bounded) readyHeap (3 + fuel) true
  have callSame : commitPositionState state = commitCopyState state 46 := by
    unfold commitPositionState commitLeafCallState
    rw [← copyPC, hoist_pc_self]
  dsimp only [ready] at leafRun
  rw [callSame] at leafRun
  rw [show 35 + fuel = 8 + (24 + (3 + fuel)) by omega,
    commit_copy state 46 (Or.inl rfl) pc (by simpa [commitCopySource, commitCopyOffset] using saltValid) scratchValid,
    leafRun]
  simp only [commitPositionRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaf reached
  rw [commit_leaf_next_position (leaf.setPC 4408) rfl]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
