import CommitGolfCandidate.CommitLeaf

/-! Commitment execution: initialize the heap and salt pointers, sample all private
salts, hash the leaves, and build the parent nodes. These proofs use the submitted
instruction image and the challenge interpreter. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def commitLoad (reg : Reg) (high : BitVec 12) : List Instr :=
  [.LUI reg (BitVec.ofNat 20 (high.toNat * 1024)), .JAL .x0 24]

private def commitSetupInstructions : List Instr :=
  [.ADDI .x8 .x10 0, .ADDI .x26 .x11 0, .ADDI .x9 .x12 0] ++
  commitLoad .x19 4 ++ commitLoad .x6 256 ++ [.ADD .x18 .x9 .x6] ++
  commitLoad .x6 128 ++ [.ADD .x23 .x9 .x6, .ADDI .x5 .x0 2, .ADDI .x10 .x18 0] ++
  commitLoad .x11 96

private def commitSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitSetupInstructions.take count).foldl execInstrBr state

def commitSetupState (state : MachineState) : MachineState := commitSetupPrefix state 15

private def compactSetupInstructions : List Instr :=
  [.ADDI .x8 .x10 0,.ADDI .x26 .x11 0,.ADDI .x9 .x12 0,
   .LUI .x19 4096,.LUI .x6 262144,.ADD .x18 .x9 .x6,
   .LUI .x6 131072,.ADD .x23 .x9 .x6,.ADDI .x5 .x0 2,
   .ADDI .x10 .x18 0,.LUI .x11 98304,.JAL .x0 96]

private def compactSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (compactSetupInstructions.take count).foldl execInstrBr state

private theorem compact_setup_same (state : MachineState) :
    compactSetupPrefix state 12=commitSetupState state := by
  simp [compactSetupPrefix,compactSetupInstructions,commitSetupState,commitSetupPrefix,
    commitSetupInstructions,commitLoad,execInstrBr,signExtend21,signExtend12,
    MachineState.setPC,MachineState.setReg,MachineState.getReg,BitVec.add_assoc]

set_option maxHeartbeats 1000000 in
theorem commit_setup (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (12 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitSetupState state) allowCoins
          return result.charge 12 0) := by
  rw [← compact_setup_same]
  apply execute_unit_steps (states := compactSetupPrefix state)
  intro i hi
  refine ⟨.base ((compactSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ i _ (by omega)
    · interval_cases i <;>
        simp [compactSetupPrefix,compactSetupInstructions,execInstrBr,signExtend21,pc,
          MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

/-- Exact ABI-derived registers at the randomness syscall. -/
theorem commit_setup_registers (state : MachineState) :
    (commitSetupState state).getReg .x5 = 2 ∧
    (commitSetupState state).getReg .x8 = state.getReg .x10 ∧
    (commitSetupState state).getReg .x9 = state.getReg .x12 ∧
    (commitSetupState state).getReg .x10 = state.getReg .x12 + 1073741824 ∧
    (commitSetupState state).getReg .x11 = 402653184 ∧
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
  [.ADDI .x21 .x8 (-32), .ADDI .x22 .x18 0, .ADDI .x0 .x0 0, .ADDI .x20 .x0 0,
   .ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0, .ADDI .x28 .x0 0]

private def commitReadyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitReadyInstructions.take count).foldl execInstrBr state

def commitReadyState (state : MachineState) : MachineState := commitReadyPrefix state 10

private def compactReadyInstructions : List Instr :=
  [.ADDI .x21 .x8 (-32), .ADDI .x22 .x18 0, .ADDI .x20 .x0 0,
   .ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0, .ADDI .x28 .x0 0,
   .JAL .x0 36, .JAL .x1 144]

private def compactReadyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (compactReadyInstructions.take count).foldl execInstrBr state

private theorem compact_ready_same (state : MachineState) (pc : state.pc=4240) :
    compactReadyPrefix state 11 = ((commitReadyState state).setReg .x1 4316).setPC 4456 := by
  simp [compactReadyPrefix,compactReadyInstructions,commitReadyState,commitReadyPrefix,
    commitReadyInstructions,execInstrBr,signExtend21,signExtend12,pc,
    MachineState.setPC,MachineState.setReg,MachineState.getReg,BitVec.add_assoc]

theorem commit_ready_linked (state : MachineState) (pc : state.pc = 4240) (fuel : Nat) :
    execute (submission.image .commit) (11 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel
            (((commitReadyState state).setReg .x1 4316).setPC 4456) true
          return result.charge 11 0) := by
  rw [← compact_ready_same state pc]
  apply execute_unit_steps (states := compactReadyPrefix state)
  intro i hi
  refine ⟨.base ((compactReadyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (if i<10 then 36+i else 54) _ (by split <;> omega)
    · interval_cases i <;>
        simp [compactReadyPrefix,compactReadyInstructions,execInstrBr,pc,
          signExtend21,MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem commit_ready_pc (state : MachineState) (pc : state.pc = 4240) :
    (commitReadyState state).pc = 4280 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr, pc, MachineState.setPC]

theorem commit_ready_counters (state : MachineState) :
    (commitReadyState state).getReg .x21 = state.getReg .x8 - 32 ∧ (commitReadyState state).getReg .x20 = 0 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]

theorem commit_ready_input (state : MachineState) :
    (commitReadyState state).getReg .x10 = (commitReadyState state).getReg .x21 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem commit_ready_register (state : MachineState) (reg : Reg)
    (notScratch : reg ≠ .x21) (notCounter : reg ≠ .x20)
    (notArguments : reg ∉ [.x5,.x10,.x11,.x12,.x13,.x28,.x22]) :
    (commitReadyState state).getReg reg = state.getReg reg := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at notArguments
  rcases notArguments with ⟨not5,not10,not11,not12,not13,not28,not22⟩
  simp only [commitReadyState,commitReadyPrefix,commitReadyInstructions,List.take,List.foldl,execInstrBr,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notCounter),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not5),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not10),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not12),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not13),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not22)]
  cases reg <;> simp_all [MachineState.setReg, MachineState.getReg, MachineState.setPC]

theorem commit_ready_heap_end (state : MachineState) :
    (commitReadyState state).getReg .x22=state.getReg .x18 := by
  simp [commitReadyState,commitReadyPrefix,commitReadyInstructions,List.foldl,execInstrBr,
    signExtend12,MachineState.getReg,MachineState.setReg,MachineState.setPC]

theorem commit_ready_oracle (state : MachineState) : CommitLeafOracleReady (commitReadyState state) := by
  simp [commitReadyState,commitReadyPrefix,commitReadyInstructions,CommitLeafOracleReady, StreamingOracleReady,
    execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,MachineState.setPC]

theorem commit_ready_block_counter (state : MachineState) :
    (commitReadyState state).getReg .x28=0 := rfl

private def commitCopySource (start : Nat) : Reg :=
  if start = 46 then .x18 else if start = 55 then .x21 else .x9
private def commitCopyDestination (start : Nat) : Reg :=
  if start = 46 then .x21 else if start = 55 then .x23 else .x26
private def commitCopyOffset (start : Nat) : Nat := if start = 79 then 32 else 0

private def commitCopyInstructions (start : Nat) : List Instr :=
  [.LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start)),
   .SD (commitCopyDestination start) .x6 0,
   .LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start + 8)),
   .SD (commitCopyDestination start) .x6 8,
   .LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start + 16)),
   .SD (commitCopyDestination start) .x6 16,
   if start=46 then .ADDI .x6 .x6 0
     else .LD .x6 (commitCopySource start) (BitVec.ofNat 12 (commitCopyOffset start + 24)),
   .SD (commitCopyDestination start) (if start=46 then .x0 else .x6) 24]

private def commitCopyPrefix (state : MachineState) (start count : Nat) : MachineState :=
  ((commitCopyInstructions start).take count).foldl execInstrBr state

def commitCopyState (state : MachineState) (start : Nat) : MachineState := commitCopyPrefix state start 8

/-- Expose the decoded salt, leaf, and root copy instructions for memory refinement. -/
theorem commit_copy_expansion (state : MachineState) (start : Nat) :
    commitCopyState state start =
      let source := if start = 46 then Reg.x18 else if start = 55 then Reg.x21 else Reg.x9
      let destination := if start = 46 then Reg.x21 else if start = 55 then Reg.x23 else Reg.x26
      let offset := if start = 79 then 32 else 0
      ([.LD .x6 source (BitVec.ofNat 12 offset), .SD destination .x6 0,
        .LD .x6 source (BitVec.ofNat 12 (offset+8)), .SD destination .x6 8,
        .LD .x6 source (BitVec.ofNat 12 (offset+16)), .SD destination .x6 16,
        if start=46 then .ADDI .x6 .x6 0 else .LD .x6 source (BitVec.ofNat 12 (offset+24)),
        .SD destination (if start=46 then .x0 else .x6) 24] : List Instr).foldl
          execInstrBr state := rfl

private theorem commit_copy_prefix_register (state : MachineState) (start count : Nat)
    (bounded : count ≤ 8) (reg : Reg) (notTemporary : reg ≠ .x6) :
    (commitCopyPrefix state start count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  by_cases salt : start=46 <;> interval_cases count <;>
    simp only [commitCopyPrefix, commitCopyInstructions, salt,ite_true,ite_false, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notTemporary)]

theorem commit_copy_register (state : MachineState) (start : Nat) (reg : Reg) (notTemporary : reg ≠ .x6) :
    (commitCopyState state start).getReg reg = state.getReg reg :=
  commit_copy_prefix_register state start 8 (by decide) reg notTemporary

theorem commit_copy_pc (state : MachineState) (start : Nat) :
    (commitCopyState state start).pc = state.pc + 32 := by
  by_cases salt : start=46 <;> simp [salt,commitCopyState, commitCopyPrefix, commitCopyInstructions, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

set_option maxHeartbeats 1000000 in
theorem commit_copy (state : MachineState) (start : Nat)
    (location : start = 79)
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
  · apply commit_fetch _ (start + i) _ (by rcases location with rfl <;> omega)
    · rcases location with rfl <;> interval_cases i <;>
        simp [commitCopyPrefix, commitCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl <;> interval_cases i <;> rfl
  · have sourceReg := commit_copy_prefix_register state start i (by omega) (commitCopySource start)
      (by rcases location with rfl <;> decide)
    have destinationReg := commit_copy_prefix_register state start i (by omega) (commitCopyDestination start)
      (by rcases location with rfl <;> decide)
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
      rcases location with rfl <;> interval_cases i <;>
        simp only [commitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, destinationReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    rcases location with rfl <;> interval_cases i <;>
      simp only [commitCopyInstructions,show (79:Nat)≠46 by decide,ite_false, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · rcases location with rfl <;> interval_cases i <;> rfl

/-- The leaf call stores the actual continuation address, immediately before the digest store. -/
def commitLeafCallState (state : MachineState) : MachineState := (state.setReg .x1 4316).setPC 4456

theorem commit_leaf_call (state : MachineState) (pc : state.pc = 4312)
    (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitLeafCallState state) true
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base (.JAL .x1 144)) := by
    apply commit_fetch _ 54 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.JAL .x1 144)) = some (commitLeafCallState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      commitLeafCallState, MachineState.setPC, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

def commitPositionNextState (state : MachineState) : MachineState :=
  (((state.setReg .x18 (state.getReg .x18 + 24)).setReg .x23 (state.getReg .x23 + 32)).setReg
    .x20 (state.getReg .x20 + 1)).setPC
      (if BitVec.ult (state.getReg .x20 + 1) (state.getReg .x19) then 4280 else 4364)

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
  return commitPositionNextState (leaf.setPC 4348)

end CommitGolfCandidate
