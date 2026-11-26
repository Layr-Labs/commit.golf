import CommitGolfCandidate.CheckPath

/-! The checker's outer position loop. These proofs compose the actual index load,
salt copy, leaf hash, authentication path, and commitment comparison. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192

/-- Load the next opened index before copying its salt into the hash accumulator. -/
def checkIndexState (state : MachineState) : MachineState :=
  (state.setReg .x20 (state.getMem (state.getReg .x24))).setPC 4348

theorem check_index (state : MachineState) (pc : state.pc = 4344)
    (valid : accessValid (state.getReg .x24) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkIndexState state) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .check) state = some (.base (.LD .x20 .x24 0)) := by
    apply check_fetch _ 62 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.LD .x20 .x24 0)) = some (checkIndexState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend12, valid,
      execInstrBr, checkIndexState, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Advance past the 24-byte salt and call the leaf-hashing subroutine. -/
def checkLeafCallState (state : MachineState) : MachineState :=
  ((state.setReg .x25 (state.getReg .x25 + 24)).setReg .x1 4384).setPC 4640

theorem check_leaf_call (state : MachineState) (pc : state.pc = 4376)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafCallState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x25 (state.getReg .x25 + 24)).setPC 4380
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x25 .x25 24)) := by
    apply check_fetch _ 70 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) next = some (.base (.JAL .x1 260)) := by
    apply check_fetch _ 71 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x25 .x25 24)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend12, execInstrBr, next, pc]
  have s1 : ordinaryStep next (.base (.JAL .x1 260)) = some (checkLeafCallState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend21, execInstrBr,
      next, checkLeafCallState, MachineState.setPC, MachineState.setReg]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- Entry state of the leaf subroutine for one opened position. -/
def checkPositionState (state : MachineState) : MachineState :=
  checkLeafCallState (checkSaltCopyState (checkIndexState state))

theorem check_position_setup (state : MachineState) (pc : state.pc = 4344)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (scratch : state.getReg .x21 = 256)
    (saltValid : ∀ word : Fin 3,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (10 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkPositionState state) allowCoins
          return result.charge 10 0) := by
  have initialScratch : (checkIndexState state).getReg .x21 = 256 := by
    simpa [checkIndexState, MachineState.getReg, MachineState.setReg, MachineState.setPC] using scratch
  have sourceValid : ∀ word : Fin 3,
      accessValid ((checkIndexState state).getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    simpa [checkIndexState, MachineState.getReg, MachineState.setReg, MachineState.setPC] using saltValid
  have copyPC : (checkSaltCopyState (checkIndexState state)).pc = 4376 := by
    rw [check_salt_copy_pc]; rfl
  rw [show 10 + fuel = 1 + (7 + (2 + fuel)) by omega,
    check_index state pc indexValid,
    check_salt_copy (checkIndexState state) rfl initialScratch sourceValid,
    check_leaf_call _ copyPC]
  simp [checkPositionState, Execution.charge, ← Nat.add_assoc]

/-- Only the index, salt pointer, link, and copy scratch register change during setup. -/
theorem check_position_register (state : MachineState) (reg : Reg)
    (unchanged : reg ∉ [Reg.x1, .x6, .x20, .x25]) :
    (checkPositionState state).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at unchanged
  simp only [checkPositionState, checkLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm unchanged.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm unchanged.2.2.2),
    check_salt_copy_register _ reg unchanged.2.1,
    checkIndexState, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm unchanged.2.2.1)]

theorem check_position_index (state : MachineState) :
    (checkPositionState state).getReg .x20 = state.getMem (state.getReg .x24) := by
  simp only [checkPositionState, checkLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x20),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x25 ≠ .x20),
    check_salt_copy_register _ .x20 (by decide), checkIndexState,
    MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0)]

theorem check_position_proof_pointer (state : MachineState) :
    (checkPositionState state).getReg .x25 = state.getReg .x25 + 24 := by
  simp only [checkPositionState, checkLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x25),
    MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0),
    check_salt_copy_register _ .x25 (by decide), checkIndexState,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x25)]

/-- The machine-state distribution at the root comparison for one position. -/
def checkPositionHash (state : MachineState) : OracleComp World MachineState := do
  let leaf ← checkLeafLoop (((checkPositionState state).setReg .x28 4).setPC 4644) 4
  checkPathLoop (checkPathInitializedState (leaf.setPC 4384)) 17

set_option maxHeartbeats 300000 in
/-- A complete leaf and authentication-path computation, before root comparison.
The instruction and cycle totals account for the index's left/right branch choices;
all possible compression replies are included. Exactly 21 public calls are made. -/
theorem check_position_hash (state : MachineState) (pc : state.pc = 4344)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (scratch : state.getReg .x21 = 256)
    (proofValid : ∀ word < 71,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (valueValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check)
        (116 + pathInstructions (state.getMem (state.getReg .x24)) 17 + fuel) state allowCoins =
      (do let finished ← checkPositionHash state
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge (263 + pathInstructions (state.getMem (state.getReg .x24)) 17) 21) := by
  let ready := checkPositionState state
  let initialized := (ready.setReg .x28 4).setPC 4644
  have readyPC : ready.pc = 4640 := rfl
  have readyLink : ready.getReg .x1 = 4384 := by
    simp only [ready, checkPositionState, checkLeafCallState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x1 ≠ .x0)]
  have readyScratch : ready.getReg .x21 = 256 :=
    (check_position_register state .x21 (by decide)).trans scratch
  have readyValue : ∀ word < 32,
      accessValid (ready.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [check_position_register state .x8 (by decide)]
    exact valueValid
  have initRegister (reg : Reg) (notCounter : reg ≠ .x28) :
      initialized.getReg reg = ready.getReg reg := by
    simp only [initialized, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notCounter)]
  have saltValid : ∀ word : Fin 3,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
    fun word => proofValid word.val (by omega)
  rw [show 116 + pathInstructions (state.getMem (state.getReg .x24)) 17 + fuel =
      10 + (102 + (4 + pathInstructions (state.getMem (state.getReg .x24)) 17 + fuel)) by omega,
    check_position_setup state pc indexValid scratch saltValid,
    check_leaf_subroutine ready readyPC readyLink readyScratch readyValue]
  simp only [checkPositionHash, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaf reached
  have registers := (check_leaf_loop_registers initialized 4 leaf reached).2
  have leafIndex : (leaf.setPC 4384).getReg .x20 = state.getMem (state.getReg .x24) := by
    rw [MachineState.getReg_setPC, registers .x20 (by decide), initRegister .x20 (by decide)]
    exact check_position_index state
  have leafScratch : (leaf.setPC 4384).getReg .x21 = 256 := by
    rw [MachineState.getReg_setPC, registers .x21 (by decide), initRegister .x21 (by decide)]
    exact readyScratch
  have leafSource : ∀ word < 68,
      accessValid ((leaf.setPC 4384).getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [MachineState.getReg_setPC, registers .x25 (by decide), initRegister .x25 (by decide),
      check_position_proof_pointer state]
    intro word bounded
    have address : state.getReg .x25 + 24 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x25 + BitVec.ofNat 64 (8 * (word + 3)) := by
      rw [show 8 * (word + 3) = 24 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [address]
    exact proofValid (word + 3) (by omega)
  rw [← leafIndex, check_path_subroutine _ rfl leafScratch leafSource]
  simp only [leafIndex, bind_assoc, pure_bind]
  have charges (result : Execution) :
      ((result.charge (4 + pathInstructions (state.getMem (state.getReg .x24)) 17 + 119) 17).charge
        130 4).charge 10 0 =
      result.charge (263 + pathInstructions (state.getMem (state.getReg .x24)) 17) 21 := by
    cases result
    simp only [Execution.charge, Execution.mk.injEq, true_and]
    omega
  simp only [charges]

/-- Hashing one position reaches the cap-node selection and consumes exactly one
256-byte leaf and one 568-byte salt/path record. The index is shifted to its cap node. -/
theorem check_position_hash_registers (state finished : MachineState)
    (reachable : finished ∈ support (checkPositionHash state)) :
    finished.pc = 4548 ∧
    finished.getReg .x8 = state.getReg .x8 + 256 ∧
    finished.getReg .x25 = state.getReg .x25 + 568 ∧
    finished.getReg .x20 = state.getMem (state.getReg .x24) >>> 17 ∧
    ∀ reg ∈ [Reg.x21, .x24, .x26, .x27, .x30], finished.getReg reg = state.getReg reg := by
  simp only [checkPositionHash, mem_support_bind_iff] at reachable
  obtain ⟨leaf, leafReached, pathReached⟩ := reachable
  let initialized := ((checkPositionState state).setReg .x28 4).setPC 4644
  have leafRegs := check_leaf_loop_registers initialized 4 leaf leafReached
  have pathRegs := check_path_loop_registers _ 17 finished pathReached
  have pathIndex := check_path_loop_index _ 17 finished pathReached
  have initRegister (reg : Reg) (notCounter : reg ≠ .x28) :
      initialized.getReg reg = (checkPositionState state).getReg reg := by
    simp only [initialized, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notCounter)]
  refine ⟨(check_path_loop_finished _ 17 (by decide)
      (check_path_initialized_counter _) finished pathReached).2 (by decide), ?_, ?_, ?_, ?_⟩
  · rw [pathRegs.2 .x8 (by decide), check_path_setup_register _ .x8 (by decide),
      MachineState.getReg_setPC, leafRegs.1, initRegister .x8 (by decide),
      check_position_register state .x8 (by decide)]
    rfl
  · rw [pathRegs.1, check_path_setup_register _ .x25 (by decide), MachineState.getReg_setPC,
      leafRegs.2 .x25 (by decide), initRegister .x25 (by decide), check_position_proof_pointer]
    change state.getReg .x25 + 24 + 544 = state.getReg .x25 + 568
    rw [BitVec.add_assoc]; rfl
  · rw [pathIndex, check_path_setup_register _ .x20 (by decide), MachineState.getReg_setPC,
      leafRegs.2 .x20 (by decide), initRegister .x20 (by decide), check_position_index]
  · intro reg included
    have pathPreserved : reg ∉ [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x20, .x25, .x29,
        .x14, .x15, .x16, .x17, .x31] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl | rfl <;> decide
    have leafPreserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28,
        .x14, .x15, .x16, .x17, .x31] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl | rfl <;> decide
    have setupPreserved : reg ∉ [Reg.x1, .x6, .x20, .x25] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl | rfl <;> decide
    have not29 : reg ≠ .x29 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl | rfl <;> decide
    have not28 : reg ≠ .x28 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl | rfl <;> decide
    rw [pathRegs.2 reg pathPreserved, check_path_setup_register _ reg not29,
      MachineState.getReg_setPC, leafRegs.2 reg leafPreserved, initRegister reg not28,
      check_position_register state reg setupPreserved]

/-- Select the supplied cap node for the climbed index: x22 = x30 + 32 * (index >> 17). -/
def checkCapSelectState (state : MachineState) : MachineState :=
  ((state.setReg .x7 (state.getReg .x20 <<< 5)).setReg .x22
    (state.getReg .x30 + state.getReg .x20 <<< 5)).setPC 4556

theorem check_cap_select (state : MachineState) (pc : state.pc = 4548)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkCapSelectState state) allowCoins
          return result.charge 2 0) := by
  let shifted := (state.setReg .x7 (state.getReg .x20 <<< 5)).setPC 4552
  have f0 : fetch (submission.image .check) state = some (.base (.SLLI .x7 .x20 5)) := by
    apply check_fetch _ 113 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) shifted = some (.base (.ADD .x22 .x30 .x7)) := by
    apply check_fetch _ 114 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.SLLI .x7 .x20 5)) = some shifted := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, shifted, pc]
  have s1 : ordinaryStep shifted (.base (.ADD .x22 .x30 .x7)) = some (checkCapSelectState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, shifted, checkCapSelectState,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem check_cap_select_register (state : MachineState) (reg : Reg)
    (not7 : reg ≠ .x7) (not22 : reg ≠ .x22) :
    (checkCapSelectState state).getReg reg = state.getReg reg := by
  simp only [checkCapSelectState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not22),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not7)]

theorem check_cap_select_node (state : MachineState) :
    (checkCapSelectState state).getReg .x22 = state.getReg .x30 + state.getReg .x20 <<< 5 := by
  simp only [checkCapSelectState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0)]

theorem check_cap_select_memory (state : MachineState) :
    (checkCapSelectState state).mem = state.mem := rfl

theorem check_cap_select_pc (state : MachineState) : (checkCapSelectState state).pc = 4556 := rfl

/-- After a matching root, advance to the next index or the success exit. -/
def checkPositionNextState (state : MachineState) : MachineState :=
  ((state.setReg .x24 (state.getReg .x24 + 8)).setReg .x27 (state.getReg .x27 - 1)).setPC
    (if state.getReg .x27 - 1 = 0 then 4616 else 4344)

theorem check_position_next_pc (state : MachineState) :
    (checkPositionNextState state).pc =
      if state.getReg .x27 - 1 = 0 then 4616 else 4344 := rfl

theorem check_position_next_counter (state : MachineState) :
    (checkPositionNextState state).getReg .x27 = state.getReg .x27 - 1 := rfl

theorem check_position_next (state : MachineState) (pc : state.pc = 4604)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkPositionNextState state) allowCoins
          return result.charge 3 0) := by
  let next := (state.setReg .x24 (state.getReg .x24 + 8)).setPC 4608
  let decremented := (next.setReg .x27 (state.getReg .x27 - 1)).setPC 4612
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x24 .x24 8)) := by
    apply check_fetch _ 127 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) next = some (.base (.ADDI .x27 .x27 4095)) := by
    apply check_fetch _ 128 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .check) decremented = some (.base (.BNE .x27 .x0 7924)) := by
    apply check_fetch _ 129 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x24 .x24 8)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have s1 : ordinaryStep next (.base (.ADDI .x27 .x27 4095)) = some decremented := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, decremented, MachineState.getReg, MachineState.setReg, MachineState.setPC,
      BitVec.sub_eq_add_neg]
  have s2 : ordinaryStep decremented (.base (.BNE .x27 .x0 7924)) = some (checkPositionNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      decremented, next, checkPositionNextState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
