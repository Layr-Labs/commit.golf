import CommitGolfCandidate.CommitLeaf

/-! Commitment execution: initialize the heap and salt pointers, sample all private
salts, hash the leaves, and build the parent nodes. These proofs use the submitted
instruction image and the challenge interpreter. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def commitLoad (reg : Reg) (high : BitVec 12) : List Instr :=
  [.ADDI reg .x0 0, .SLLI reg reg 11, .ADDI reg reg high,
   .SLLI reg reg 11, .ADDI reg reg 0, .SLLI reg reg 11, .ADDI reg reg 0]

private def commitSetupInstructions : List Instr :=
  [.ADDI .x8 .x10 0, .ADDI .x26 .x11 0, .ADDI .x9 .x12 0] ++
  commitLoad .x19 4 ++ commitLoad .x6 256 ++ [.ADD .x18 .x9 .x6] ++
  commitLoad .x6 128 ++ [.ADD .x23 .x9 .x6, .ADDI .x5 .x0 2, .ADDI .x10 .x18 0] ++
  commitLoad .x11 128

private def commitSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitSetupInstructions.take count).foldl execInstrBr state

def commitSetupState (state : MachineState) : MachineState := commitSetupPrefix state 35

set_option maxHeartbeats 1000000 in
/-- The 35-instruction setup computes pointers into the admitted private trapdoor
and the total salt length; it performs no memory access or oracle call. -/
theorem commit_setup (state : MachineState) (pc : state.pc = 4096)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (35 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitSetupState state) allowCoins
          return result.charge 35 0) := by
  apply execute_unit_steps (states := commitSetupPrefix state)
  intro i hi
  refine ⟨.base ((commitSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ i _ (by omega)
    · interval_cases i <;>
        simp [commitSetupPrefix, commitSetupInstructions, commitLoad, execInstrBr, pc,
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
    execInstrBr, MachineState.setPC, pc]

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
  [.ADDI .x21 .x0 0, .SLLI .x21 .x21 11, .ADDI .x21 .x21 256, .ADDI .x20 .x0 0]

private def commitReadyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitReadyInstructions.take count).foldl execInstrBr state

def commitReadyState (state : MachineState) : MachineState := commitReadyPrefix state 4

/-- Initialize the fixed scratch pointer and leaf counter after sampling salts. -/
theorem commit_ready (state : MachineState) (pc : state.pc = 4240) (fuel : Nat) :
    execute (submission.image .commit) (4 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitReadyState state) true
          return result.charge 4 0) := by
  apply execute_unit_steps (states := commitReadyPrefix state)
  intro i hi
  refine ⟨.base ((commitReadyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (36 + i) _ (by omega)
    · interval_cases i <;>
        simp [commitReadyPrefix, commitReadyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem commit_ready_pc (state : MachineState) (pc : state.pc = 4240) :
    (commitReadyState state).pc = 4256 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr, pc, MachineState.setPC]

theorem commit_ready_counters (state : MachineState) :
    (commitReadyState state).getReg .x21 = 256 ∧ (commitReadyState state).getReg .x20 = 0 := by
  simp [commitReadyState, commitReadyPrefix, commitReadyInstructions, execInstrBr,
    signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

theorem commit_ready_register (state : MachineState) (reg : Reg)
    (notScratch : reg ≠ .x21) (notCounter : reg ≠ .x20) :
    (commitReadyState state).getReg reg = state.getReg reg := by
  cases reg <;> simp_all [commitReadyState, commitReadyPrefix, commitReadyInstructions,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

private def commitCopySource (start : Nat) : Reg :=
  if start = 40 then .x18 else if start = 49 then .x21 else .x9
private def commitCopyDestination (start : Nat) : Reg :=
  if start = 40 then .x21 else if start = 49 then .x23 else .x26
private def commitCopyOffset (start : Nat) : Nat := if start = 73 then 32 else 0

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
      let source := if start = 40 then Reg.x18 else if start = 49 then Reg.x21 else Reg.x9
      let destination := if start = 40 then Reg.x21 else if start = 49 then Reg.x23 else Reg.x26
      let offset := if start = 73 then 32 else 0
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
    (location : start = 40 ∨ start = 49 ∨ start = 73)
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
  · apply commit_fetch _ (start + i) _ (by rcases location with rfl | rfl | rfl <;> omega)
    · rcases location with rfl | rfl | rfl <;> interval_cases i <;>
        simp [commitCopyPrefix, commitCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl | rfl | rfl <;> interval_cases i <;> rfl
  · have sourceReg := commit_copy_prefix_register state start i (by omega) (commitCopySource start)
      (by rcases location with rfl | rfl | rfl <;> decide)
    have destinationReg := commit_copy_prefix_register state start i (by omega) (commitCopyDestination start)
      (by rcases location with rfl | rfl | rfl <;> decide)
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
      rcases location with rfl | rfl | rfl <;> interval_cases i <;>
        simp only [commitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, destinationReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          exact d0 | exact d1 | exact d2 | exact d3
    interval_cases i <;>
      simp only [commitCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- The leaf call stores the actual continuation address, immediately before the digest store. -/
def commitLeafCallState (state : MachineState) : MachineState := (state.setReg .x1 4292).setPC 4432

theorem commit_leaf_call (state : MachineState) (pc : state.pc = 4288)
    (fuel : Nat) :
    execute (submission.image .commit) (1 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitLeafCallState state) true
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base (.JAL .x1 144)) := by
    apply commit_fetch _ 48 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.JAL .x1 144)) = some (commitLeafCallState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      commitLeafCallState, MachineState.setPC, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Advance the salt and heap pointers after storing a digest; loop while more
leaves remain. Both outcomes of the unsigned branch are represented. -/
def commitPositionNextState (state : MachineState) : MachineState :=
  (((state.setReg .x18 (state.getReg .x18 + 32)).setReg .x23 (state.getReg .x23 + 32)).setReg
    .x20 (state.getReg .x20 + 1)).setPC
      (if BitVec.ult (state.getReg .x20 + 1) (state.getReg .x19) then 4256 else 4340)

private def commitNextPrefix (state : MachineState) (count : Nat) : MachineState :=
  ([.ADDI .x18 .x18 32, .ADDI .x23 .x23 32, .ADDI .x20 .x20 1].take count).foldl execInstrBr state

theorem commit_leaf_next_position (state : MachineState) (pc : state.pc = 4324) (fuel : Nat) :
    execute (submission.image .commit) (4 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitPositionNextState state) true
          return result.charge 4 0) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (3 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (commitNextPrefix state 3) true
            return result.charge 3 0) := by
    apply execute_unit_steps (states := commitNextPrefix state)
    intro i hi
    refine ⟨.base (([.ADDI .x18 .x18 32, .ADDI .x23 .x23 32, .ADDI .x20 .x20 1][i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (57 + i) _ (by omega)
      · interval_cases i <;> simp [commitNextPrefix, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have fetched : fetch (submission.image .commit) (commitNextPrefix state 3) =
      some (.base (.BLTU .x20 .x19 8112)) := by
    apply commit_fetch _ 60 _ (by decide)
    · simp [commitNextPrefix, execInstrBr, pc, MachineState.setPC]
    · rfl
  have stepped : ordinaryStep (commitNextPrefix state 3) (.base (.BLTU .x20 .x19 8112)) =
      some (commitPositionNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13, signExtend12,
      commitNextPrefix, commitPositionNextState, MachineState.getReg, MachineState.setReg,
      MachineState.setPC, pc]
    split <;> simp_all
  rw [show 4 + fuel = 3 + (fuel + 1) by omega, setup,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

def commitPositionState (state : MachineState) : MachineState :=
  commitLeafCallState (commitCopyState state 40)

theorem commit_position_register (state : MachineState) (reg : Reg)
    (notLink : reg ≠ .x1) (notTemporary : reg ≠ .x6) :
    (commitPositionState state).getReg reg = state.getReg reg := by
  simp only [commitPositionState, commitLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notLink),
    commit_copy_register _ _ reg notTemporary]

/-- The exact state distribution after one salt/leaf/digest iteration. -/
def commitPositionRun (state : MachineState) : OracleComp World MachineState := do
  let leaf ← commitLeafLoop (commitLeafEntry (commitPositionState state)) 8
  return commitPositionNextState (commitCopyState (leaf.setPC 4292) 49)

set_option maxHeartbeats 400000 in
/-- One complete commitment leaf iteration: load its salt, hash 2048 bits, store
the resulting digest in the heap, then advance. All oracle replies are covered.
This takes 107 instructions, 163 cycles, and exactly eight public queries. -/
theorem commit_position (state : MachineState) (pc : state.pc = 4256)
    (scratch : state.getReg .x21 = 256)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x18 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (heapValid : ∀ word : Fin 4,
      accessValid (state.getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (messageValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) :
    execute (submission.image .commit) (107 + fuel) state true =
      (do let finished ← commitPositionRun state
          let result ← execute (submission.image .commit) fuel finished true
          return result.charge 163 8) := by
  let ready := commitPositionState state
  let initialized := commitLeafEntry ready
  have scratchValid : ∀ word : Fin 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [scratch]
    intro word
    fin_cases word <;> rfl
  have copyPC : (commitCopyState state 40).pc = 4288 := by rw [commit_copy_pc, pc]; rfl
  have readyPC : ready.pc = 4432 := rfl
  have readyLink : ready.getReg .x1 = 4292 := by
    simp only [ready, commitPositionState, commitLeafCallState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x1 ≠ .x0)]
  have readyScratch : ready.getReg .x21 = 256 :=
    (commit_position_register state .x21 (by decide) (by decide)).trans scratch
  have readyMessage : ∀ word < 32,
      accessValid (ready.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [commit_position_register state .x8 (by decide) (by decide)]
    exact messageValid
  have leafRun := commit_leaf_subroutine ready readyPC readyLink readyScratch readyMessage (8 + (4 + fuel)) true
  dsimp only [ready, commitPositionState] at leafRun
  rw [show 107 + fuel = 8 + (1 + (86 + (8 + (4 + fuel)))) by omega,
    commit_copy state 40 (Or.inl rfl) pc (by simpa [commitCopySource, commitCopyOffset] using saltValid) scratchValid,
    commit_leaf_call _ copyPC, leafRun]
  simp only [commitPositionRun, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaf reached
  have registers := (commit_leaf_loop_registers initialized 8 leaf reached).2
  have initRegister (reg : Reg) (preserved : reg ∉ [.x5, .x10, .x11, .x12, .x13, .x28]) :
      initialized.getReg reg = ready.getReg reg :=
    commit_leaf_entry_register ready reg preserved
  have leafScratch : (leaf.setPC 4292).getReg .x21 = 256 := by
    rw [MachineState.getReg_setPC, registers .x21 (by decide), initRegister .x21 (by decide)]
    exact readyScratch
  have sourceValid : ∀ word : Fin 4,
      accessValid ((leaf.setPC 4292).getReg .x21 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [leafScratch]
    intro word
    fin_cases word <;> rfl
  have destinationValid : ∀ word : Fin 4,
      accessValid ((leaf.setPC 4292).getReg .x23 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [MachineState.getReg_setPC, registers .x23 (by decide), initRegister .x23 (by decide),
      commit_position_register state .x23 (by decide) (by decide)]
    exact heapValid
  have storePC : (commitCopyState (leaf.setPC 4292) 49).pc = 4324 := by
    rw [commit_copy_pc]; rfl
  rw [commit_copy _ 49 (Or.inr (Or.inl rfl)) rfl (by simpa [commitCopySource, commitCopyOffset] using sourceValid) destinationValid,
    commit_leaf_next_position _ storePC]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
