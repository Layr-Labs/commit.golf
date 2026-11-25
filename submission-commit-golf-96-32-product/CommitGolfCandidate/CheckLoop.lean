import CommitGolfCandidate.CheckPath

/-! The checker's unified outer position loop (`pathDepth = 24` in normal mode,
`pathDepth = 17` in cap mode). Composes index load, salt copy, leaf hash,
authentication path, target-address computation, digest comparison, and latch. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 4096

/-- Load the next opened index before copying its salt into the hash accumulator. -/
def checkIndexState (state : MachineState) : MachineState :=
  (state.setReg .x20 (state.getMem (state.getReg .x24))).setPC 4160

theorem check_index (state : MachineState) (pc : state.pc = 4156)
    (valid : accessValid (state.getReg .x24) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkIndexState state) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .check) state = some (.base (.LD .x20 .x24 0)) := by
    apply check_fetch _ 15 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.LD .x20 .x24 0)) = some (checkIndexState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend12, valid,
      execInstrBr, checkIndexState, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Advance past the 32-byte salt and call the leaf-hashing subroutine (at 4712). -/
def checkLeafCallState (state : MachineState) : MachineState :=
  ((state.setReg .x25 (state.getReg .x25 + 32)).setReg .x1 4200).setPC 4712

theorem check_leaf_call (state : MachineState) (pc : state.pc = 4192)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafCallState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x25 (state.getReg .x25 + 32)).setPC 4196
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x25 .x25 32)) := by
    apply check_fetch _ 24 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) next = some (.base (.JAL .x1 516)) := by
    apply check_fetch _ 25 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x25 .x25 32)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend12, execInstrBr, next, pc]
  have s1 : ordinaryStep next (.base (.JAL .x1 516)) = some (checkLeafCallState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend21, execInstrBr,
      next, checkLeafCallState, MachineState.setPC, MachineState.setReg]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- Entry state of the leaf subroutine for one opened position. -/
def checkPositionState (state : MachineState) : MachineState :=
  checkLeafCallState (checkPathCopyState (checkIndexState state) 16)

theorem check_position_setup (state : MachineState) (pc : state.pc = 4156)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (scratch : state.getReg .x21 = 256)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (11 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkPositionState state) allowCoins
          return result.charge 11 0) := by
  have initialScratch : (checkIndexState state).getReg .x21 = 256 := by
    simpa [checkIndexState, MachineState.getReg, MachineState.setReg, MachineState.setPC] using scratch
  have sourceValid : ∀ word : Fin 4,
      accessValid ((checkIndexState state).getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    simpa [checkIndexState, MachineState.getReg, MachineState.setReg, MachineState.setPC] using saltValid
  have copyPC : (checkPathCopyState (checkIndexState state) 16).pc = 4192 := by
    rw [check_path_copy_pc]; rfl
  rw [show 11 + fuel = 1 + (8 + (2 + fuel)) by omega,
    check_index state pc indexValid,
    check_path_copy (checkIndexState state) 16 (Or.inr (Or.inr (Or.inr rfl))) rfl initialScratch sourceValid,
    check_leaf_call _ copyPC]
  simp [checkPositionState, Execution.charge, ← Nat.add_assoc]

theorem check_position_register (state : MachineState) (reg : Reg)
    (unchanged : reg ∉ [Reg.x1, .x6, .x20, .x25]) :
    (checkPositionState state).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at unchanged
  simp only [checkPositionState, checkLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm unchanged.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm unchanged.2.2.2),
    check_path_copy_register _ _ reg unchanged.2.1,
    checkIndexState, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm unchanged.2.2.1)]

theorem check_position_index (state : MachineState) :
    (checkPositionState state).getReg .x20 = state.getMem (state.getReg .x24) := by
  simp only [checkPositionState, checkLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x20),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x25 ≠ .x20),
    check_path_copy_register _ _ .x20 (by decide), checkIndexState,
    MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0)]

theorem check_position_proof_pointer (state : MachineState) :
    (checkPositionState state).getReg .x25 = state.getReg .x25 + 32 := by
  simp only [checkPositionState, checkLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x25),
    MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0),
    check_path_copy_register _ _ .x25 (by decide), checkIndexState,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x25)]

/-- Compute the comparison target address `x23 = x26 + (x20 <<< 5)` (indices 64..65). -/
def checkTargetState (state : MachineState) : MachineState :=
  ((state.setReg .x7 (state.getReg .x20 <<< 5)).setReg .x23
    (state.getReg .x26 + (state.getReg .x20 <<< 5))).setPC 4360

theorem check_target (state : MachineState) (pc : state.pc = 4352)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkTargetState state) allowCoins
          return result.charge 2 0) := by
  let s1 := (state.setReg .x7 (state.getReg .x20 <<< 5)).setPC 4356
  have f0 : fetch (submission.image .check) state = some (.base (.SLLI .x7 .x20 5)) := by
    apply check_fetch _ 64 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) s1 = some (.base (.ADD .x23 .x26 .x7)) := by
    apply check_fetch _ 65 _ (by decide) rfl; rfl
  have st0 : ordinaryStep state (.base (.SLLI .x7 .x20 5)) = some s1 := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, s1, pc]
  have st1 : ordinaryStep s1 (.base (.ADD .x23 .x26 .x7)) = some (checkTargetState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, s1, checkTargetState,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, st0, f1, st1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- The machine-state distribution at the digest comparison (PC 4360) for one position
at path depth `pathDepth` (`24` or `17`). -/
def checkPositionHash (state : MachineState) (pathDepth : Nat) : OracleComp World MachineState := do
  let leaf ← checkLeafLoop (((checkPositionState state).setReg .x28 4).setPC 4716) 4
  let pathed ← checkPathLoop (checkPathInitializedState (leaf.setPC 4200)) pathDepth
  return checkTargetState pathed

set_option maxHeartbeats 400000 in
theorem check_position_hash (pathDepth : Nat) (depthPos : 0 < pathDepth)
    (depthBound : pathDepth ≤ 24) (state : MachineState) (pc : state.pc = 4156)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (scratch : state.getReg .x21 = 256)
    (proofValid : ∀ word < 4 * (pathDepth + 1),
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (valueValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check)
        (116 + pathInstructions (state.getMem (state.getReg .x24)) pathDepth + fuel) state allowCoins =
      (do let finished ← checkPositionHash state pathDepth
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge
            (144 + pathInstructions (state.getMem (state.getReg .x24)) pathDepth + 7 * pathDepth)
            (4 + pathDepth)) := by
  let ready := checkPositionState state
  let initialized := (ready.setReg .x28 4).setPC 4716
  have readyPC : ready.pc = 4712 := rfl
  have readyLink : ready.getReg .x1 = 4200 := by
    simp only [ready, checkPositionState, checkLeafCallState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x1 ≠ .x0)]
  have readyScratch : ready.getReg .x21 = 256 :=
    (check_position_register state .x21 (by decide)).trans scratch
  have readyValue : ∀ word < 32,
      accessValid (ready.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [check_position_register state .x8 (by decide)]; exact valueValid
  have initRegister (reg : Reg) (notCounter : reg ≠ .x28) :
      initialized.getReg reg = ready.getReg reg := by
    simp only [initialized, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notCounter)]
  have saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
    fun word => proofValid word.val (by omega)
  rw [show 116 + pathInstructions (state.getMem (state.getReg .x24)) pathDepth + fuel =
      11 + (102 + (1 + pathInstructions (state.getMem (state.getReg .x24)) pathDepth + (2 + fuel))) by omega,
    check_position_setup state pc indexValid scratch saltValid,
    check_leaf_subroutine ready readyPC readyLink readyScratch readyValue]
  simp only [checkPositionHash, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaf reached
  have registers := (check_leaf_loop_registers initialized 4 leaf reached).2
  have leafIndex : (leaf.setPC 4200).getReg .x20 = state.getMem (state.getReg .x24) := by
    rw [MachineState.getReg_setPC, registers .x20 (by decide), initRegister .x20 (by decide)]
    exact check_position_index state
  have leafScratch : (leaf.setPC 4200).getReg .x21 = 256 := by
    rw [MachineState.getReg_setPC, registers .x21 (by decide), initRegister .x21 (by decide)]
    exact readyScratch
  have leafDepth : (leaf.setPC 4200).getReg .x30 = BitVec.ofNat 64 pathDepth := by
    rw [MachineState.getReg_setPC, registers .x30 (by decide), initRegister .x30 (by decide),
      check_position_register state .x30 (by decide), depthReg]
  have leafSource : ∀ word < 4 * pathDepth,
      accessValid ((leaf.setPC 4200).getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [MachineState.getReg_setPC, registers .x25 (by decide), initRegister .x25 (by decide),
      check_position_proof_pointer state]
    intro word bounded
    have address : state.getReg .x25 + 32 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x25 + BitVec.ofNat 64 (8 * (word + 4)) := by
      rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    exact proofValid (word + 4) (by omega)
  rw [← leafIndex, check_path_subroutine pathDepth depthBound _ rfl leafDepth leafScratch leafSource]
  simp only [leafIndex, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro pathed pathReached
  have pathEnd := check_path_loop_finished _ pathDepth depthBound
    (by rw [check_path_initialized_counter, leafDepth]) pathed pathReached
  rw [check_target pathed (pathEnd.2 depthPos)]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro res
  congr 1
  simp only [Execution.charge, Execution.mk.injEq, true_and]
  constructor <;> omega

theorem check_position_hash_registers (pathDepth : Nat) (depthPos : 0 < pathDepth)
    (depthBound : pathDepth ≤ 24) (state finished : MachineState)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (reachable : finished ∈ support (checkPositionHash state pathDepth)) :
    finished.pc = 4360 ∧
    finished.getReg .x8 = state.getReg .x8 + 256 ∧
    finished.getReg .x25 = state.getReg .x25 + BitVec.ofNat 64 (32 + 32 * pathDepth) ∧
    finished.getReg .x23 = state.getReg .x26 + ((state.getMem (state.getReg .x24) >>> pathDepth) <<< 5) ∧
    ∀ reg ∈ [Reg.x21, .x24, .x26, .x27, .x30], finished.getReg reg = state.getReg reg := by
  simp only [checkPositionHash, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨leaf, leafReached, pathed, pathReached, rfl⟩ := reachable
  let initialized := ((checkPositionState state).setReg .x28 4).setPC 4716
  have leafRegs := check_leaf_loop_registers initialized 4 leaf leafReached
  have pathRegs := check_path_loop_registers _ pathDepth pathed pathReached
  have initRegister (reg : Reg) (notCounter : reg ≠ .x28) :
      initialized.getReg reg = (checkPositionState state).getReg reg := by
    simp only [initialized, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notCounter)]
  have keepPathed (reg : Reg) (included : reg ∈ [Reg.x21, .x24, .x26, .x27, .x30]) :
      pathed.getReg reg = state.getReg reg := by
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
    rw [pathRegs.2.2 reg pathPreserved, check_path_setup_register _ reg not29,
      MachineState.getReg_setPC, leafRegs.2 reg leafPreserved, initRegister reg not28,
      check_position_register state reg setupPreserved]
  have pathedX20 : pathed.getReg .x20 = state.getMem (state.getReg .x24) >>> pathDepth := by
    rw [pathRegs.2.1, check_path_setup_register _ .x20 (by decide), MachineState.getReg_setPC,
      leafRegs.2 .x20 (by decide), initRegister .x20 (by decide), check_position_index state]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp only [checkTargetState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x8),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x8)]
    rw [pathRegs.2.2 .x8 (by decide), check_path_setup_register _ .x8 (by decide),
      MachineState.getReg_setPC, leafRegs.1, initRegister .x8 (by decide),
      check_position_register state .x8 (by decide)]; rfl
  · simp only [checkTargetState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x25),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x25)]
    rw [pathRegs.1, check_path_setup_register _ .x25 (by decide), MachineState.getReg_setPC,
      leafRegs.2 .x25 (by decide), initRegister .x25 (by decide), check_position_proof_pointer,
      BitVec.ofNat_add, BitVec.add_assoc]; rfl
  · simp only [checkTargetState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x23 ≠ .x0),
      keepPathed .x26 (by simp), pathedX20]
  · intro reg included
    have not23 : reg ≠ .x23 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl | rfl <;> decide
    have not7 : reg ≠ .x7 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [checkTargetState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not23),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not7)]
    exact keepPathed reg included

/-- Every supported run of `checkPositionHash` preserves all memory outside `[256, 352)`. -/
theorem check_position_hash_support_outside (pathDepth : Nat) (state finished : MachineState)
    (reachable : finished ∈ support (checkPositionHash state pathDepth))
    (address : Word) (scratch : state.getReg .x21 = 256)
    (outside : ∀ i < 12, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
    finished.getMem address = state.getMem address := by
  simp only [checkPositionHash, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨leaf, leafReached, pathed, pathReached, rfl⟩ := reachable
  let initialized := ((checkPositionState state).setReg .x28 4).setPC 4716
  have initScratch : initialized.getReg .x21 = 256 := by
    simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using
      (check_position_register state .x21 (by decide)).trans scratch
  have leafScratch : (checkPathInitializedState (leaf.setPC 4200)).getReg .x21 = 256 := by
    rw [check_path_setup_register _ .x21 (by decide), MachineState.getReg_setPC,
      (check_leaf_loop_registers initialized 4 leaf leafReached).2 .x21 (by decide), initScratch]
  change pathed.getMem address = state.getMem address
  rw [check_path_loop_support_outside _ pathDepth pathed pathReached address leafScratch
    (fun i hi => outside i (by omega))]
  change leaf.getMem address = state.getMem address
  rw [check_leaf_loop_support_outside initialized 4 leaf leafReached address initScratch outside]
  change (checkPathCopyState (checkIndexState state) 16).getMem address = state.getMem address
  have idxScratch : (checkIndexState state).getReg .x21 = 256 := by
    simpa [checkIndexState, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using scratch
  exact path_copy_mem_outside (checkIndexState state) 16 (Or.inr (Or.inr (Or.inr rfl))) address
    idxScratch (fun i hi => outside i (by omega))

/-- After a matching digest comparison, advance to the next position (4156) or accept (4420). -/
def checkPositionNextState (state : MachineState) : MachineState :=
  ((state.setReg .x24 (state.getReg .x24 + 8)).setReg .x27 (state.getReg .x27 - 1)).setPC
    (if state.getReg .x27 - 1 = 0 then 4420 else 4156)

theorem check_position_next_pc (state : MachineState) :
    (checkPositionNextState state).pc =
      if state.getReg .x27 - 1 = 0 then 4420 else 4156 := rfl

theorem check_position_next_counter (state : MachineState) :
    (checkPositionNextState state).getReg .x27 = state.getReg .x27 - 1 := rfl

theorem check_position_next (state : MachineState) (pc : state.pc = 4408)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkPositionNextState state) allowCoins
          return result.charge 3 0) := by
  let next := (state.setReg .x24 (state.getReg .x24 + 8)).setPC 4412
  let decremented := (next.setReg .x27 (state.getReg .x27 - 1)).setPC 4416
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x24 .x24 8)) := by
    apply check_fetch _ 78 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) next = some (.base (.ADDI .x27 .x27 4095)) := by
    apply check_fetch _ 79 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .check) decremented = some (.base (.BNE .x27 .x0 7932)) := by
    apply check_fetch _ 80 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x24 .x24 8)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have s1 : ordinaryStep next (.base (.ADDI .x27 .x27 4095)) = some decremented := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, decremented, MachineState.getReg, MachineState.setReg, MachineState.setPC,
      BitVec.sub_eq_add_neg]
  have s2 : ordinaryStep decremented (.base (.BNE .x27 .x0 7932)) = some (checkPositionNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      decremented, next, checkPositionNextState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- Unified buffer and control invariants at the start of each outer iteration.
Works for both normal mode (`pathDepth = 24`, 1 target = commitment) and cap mode
(`pathDepth = 17`, 128 targets = cap table at `proof + 73728`). -/
structure CheckLoopInvariant (state : MachineState) (count pathDepth : Nat) : Prop where
  pc : state.pc = if count = 0 then 4420 else 4156
  counter : state.getReg .x27 = BitVec.ofNat 64 count
  scratch : state.getReg .x21 = 256
  depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth
  depthPos : 0 < pathDepth
  depthBound : pathDepth ≤ 24
  indices : ∀ word < count,
    accessValid (state.getReg .x24 + BitVec.ofNat 64 (8 * word)) 8 = true
  indexOutside : ∀ word < count, ∀ i < 12,
    state.getReg .x24 + BitVec.ofNat 64 (8 * word) ≠ BitVec.ofNat 64 (256 + 8 * i)
  indexValues : ∀ word < count,
    (state.getMem (state.getReg .x24 + BitVec.ofNat 64 (8 * word))).toNat < 2 ^ 24
  values : ∀ word < 32 * count,
    accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true
  proofs : ∀ word < 4 * (pathDepth + 1) * count,
    accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true
  targets : ∀ word < 4 * 2 ^ (24 - pathDepth),
    accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word)) 8 = true

theorem check_target_access_valid (pathDepth : Nat) (depthBound : pathDepth ≤ 24)
    (targetBase index : Word) (indexSmall : index.toNat < 2 ^ 24)
    (targets : ∀ word < 4 * 2 ^ (24 - pathDepth),
      accessValid (targetBase + BitVec.ofNat 64 (8 * word)) 8 = true)
    (word : Nat) (hw : word < 4) :
    accessValid (targetBase + ((index >>> pathDepth) <<< 5) + BitVec.ofNat 64 (8 * word)) 8 = true := by
  have qBound : index.toNat / 2 ^ pathDepth < 2 ^ (24 - pathDepth) := by
    have hpow : 2 ^ pathDepth * 2 ^ (24 - pathDepth) = 2 ^ 24 := by
      rw [← Nat.pow_add, Nat.add_sub_of_le depthBound]
    exact (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by rw [Nat.mul_comm, hpow]; exact indexSmall)
  have shiftVal : ((index >>> pathDepth) <<< 5) = BitVec.ofNat 64 (32 * (index.toNat / 2 ^ pathDepth)) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    have h1 : index.toNat / 2 ^ pathDepth * 2 ^ 5 = 32 * (index.toNat / 2 ^ pathDepth) := by omega
    rw [h1]
  have addrEq : targetBase + ((index >>> pathDepth) <<< 5) + BitVec.ofNat 64 (8 * word) =
      targetBase + BitVec.ofNat 64 (8 * (4 * (index.toNat / 2 ^ pathDepth) + word)) := by
    rw [shiftVal, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2; omega
  rw [addrEq]
  exact targets (4 * (index.toNat / 2 ^ pathDepth) + word) (by omega)

attribute [local irreducible] checkRootWordsState

theorem check_loop_next_invariant (state hashed : MachineState) (count pathDepth : Nat)
    (bounded : count < 2 ^ 24)
    (invariant : CheckLoopInvariant state (count + 1) pathDepth)
    (reachable : hashed ∈ support (checkPositionHash state pathDepth)) :
    CheckLoopInvariant (checkPositionNextState (checkRootWordsState hashed 66 4)) count pathDepth := by
  have hashRegs := check_position_hash_registers pathDepth invariant.depthPos invariant.depthBound
    state hashed invariant.depthReg reachable
  let compared := checkRootWordsState hashed 66 4
  have preserved (reg : Reg) (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) :
      compared.getReg reg = hashed.getReg reg :=
    (check_root_words_preserves hashed 66 4 reg not6 not7).1
  have counter : compared.getReg .x27 - 1 = BitVec.ofNat 64 count := by
    rw [preserved .x27 (by decide) (by decide), hashRegs.2.2.2.2 .x27 (by simp), invariant.counter]
    change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]; congr 1
  have indexPtr : (checkPositionNextState compared).getReg .x24 = state.getReg .x24 + 8 := by
    simp only [checkPositionNextState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x27 ≠ .x24),
      MachineState.getReg_setReg_eq (by decide : Reg.x24 ≠ .x0),
      preserved .x24 (by decide) (by decide), hashRegs.2.2.2.2 .x24 (by simp)]
  have otherReg (reg : Reg) (not24 : reg ≠ .x24) (not27 : reg ≠ .x27)
      (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) :
      (checkPositionNextState compared).getReg reg = hashed.getReg reg := by
    simp only [checkPositionNextState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not27),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not24), preserved reg not6 not7]
  have valuePtr : (checkPositionNextState compared).getReg .x8 = state.getReg .x8 + 256 :=
    (otherReg .x8 (by decide) (by decide) (by decide) (by decide)).trans hashRegs.2.1
  have proofPtr : (checkPositionNextState compared).getReg .x25 =
      state.getReg .x25 + BitVec.ofNat 64 (32 + 32 * pathDepth) :=
    (otherReg .x25 (by decide) (by decide) (by decide) (by decide)).trans hashRegs.2.2.1
  have targetPtr : (checkPositionNextState compared).getReg .x26 = state.getReg .x26 :=
    (otherReg .x26 (by decide) (by decide) (by decide) (by decide)).trans
      (hashRegs.2.2.2.2 .x26 (by simp))
  have nextMem : (checkPositionNextState compared).mem = hashed.mem :=
    (check_root_words_preserves hashed 66 4 .x21 (by decide) (by decide)).2
  refine ⟨?_, ?_, ?_, ?_, invariant.depthPos, invariant.depthBound, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [check_position_next_pc, counter]
    have zero : BitVec.ofNat 64 count = 0 ↔ count = 0 := by
      constructor
      · intro equal
        have numeric := congrArg BitVec.toNat equal
        change count % 18446744073709551616 = 0 at numeric; omega
      · rintro rfl; rfl
    simp only [zero]
  · rw [check_position_next_counter, counter]
  · rw [otherReg .x21 (by decide) (by decide) (by decide) (by decide),
      hashRegs.2.2.2.2 .x21 (by simp)]
    exact invariant.scratch
  · rw [otherReg .x30 (by decide) (by decide) (by decide) (by decide),
      hashRegs.2.2.2.2 .x30 (by simp)]
    exact invariant.depthReg
  · intro word smaller
    rw [indexPtr]
    have address : state.getReg .x24 + 8 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x24 + BitVec.ofNat 64 (8 * (word + 1)) := by
      rw [show 8 * (word + 1) = 8 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]; exact invariant.indices (word + 1) (by omega)
  · intro word smaller i hi
    rw [indexPtr]
    have address : state.getReg .x24 + 8 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x24 + BitVec.ofNat 64 (8 * (word + 1)) := by
      rw [show 8 * (word + 1) = 8 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]; exact invariant.indexOutside (word + 1) (by omega) i hi
  · intro word smaller
    rw [indexPtr]
    have address : state.getReg .x24 + 8 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x24 + BitVec.ofNat 64 (8 * (word + 1)) := by
      rw [show 8 * (word + 1) = 8 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    change ((checkPositionNextState compared).mem _).toNat < 2 ^ 24
    rw [nextMem]
    change (hashed.getMem (state.getReg .x24 + BitVec.ofNat 64 (8 * (word + 1)))).toNat < 2 ^ 24
    rw [check_position_hash_support_outside pathDepth state hashed reachable _ invariant.scratch
      (invariant.indexOutside (word + 1) (by omega))]
    exact invariant.indexValues (word + 1) (by omega)
  · intro word smaller
    rw [valuePtr]
    have address : state.getReg .x8 + 256 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x8 + BitVec.ofNat 64 (8 * (word + 32)) := by
      rw [show 8 * (word + 32) = 256 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]; exact invariant.values (word + 32) (by omega)
  · intro word smaller
    rw [proofPtr]
    have address : state.getReg .x25 + BitVec.ofNat 64 (32 + 32 * pathDepth) + BitVec.ofNat 64 (8 * word) =
        state.getReg .x25 + BitVec.ofNat 64 (8 * (word + 4 * (pathDepth + 1))) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
    rw [address]
    exact invariant.proofs (word + 4 * (pathDepth + 1)) (by
      have : 4 * (pathDepth + 1) * (count + 1) = 4 * (pathDepth + 1) * count + 4 * (pathDepth + 1) := by
        rw [Nat.mul_succ]
      omega)
  · rw [targetPtr]; exact invariant.targets

attribute [local irreducible] checkPositionNextState checkPositionHash
  execute pathInstructions

set_option maxHeartbeats 600000 in
/-- Every unified outer-loop execution terminates, even for incorrect proof contents.
Uses at most `1412` instructions, `159 + 52 * pathDepth` cycles, and `4 + pathDepth` public
queries per position (plus 3 cycles for the final exit). -/
theorem check_loop_terminates (state : MachineState) (count pathDepth : Nat)
    (bounded : count ≤ 2 ^ 24) (invariant : CheckLoopInvariant state count pathDepth)
    (fuel : Nat) (allowCoins : Bool) (result : Execution)
    (reachable : result ∈ support
      (execute (submission.image .check) (1412 * count + 3 + fuel) state allowCoins)) :
    result.exit ≠ .unfinished ∧ result.cycles ≤ (159 + 52 * pathDepth) * count + 3 ∧
      result.oracleCalls ≤ (4 + pathDepth) * count := by
  induction count generalizing state fuel result with
  | zero =>
    have pc : state.pc = 4420 := by simpa using invariant.pc
    rw [show 1412 * 0 + 3 + fuel = 3 + fuel by omega, check_exit state true pc] at reachable
    simp only [support_pure, Set.mem_singleton_iff] at reachable
    subst result
    simp
  | succ count ih =>
    have pc : state.pc = 4156 := by simpa using invariant.pc
    have indexValid : accessValid (state.getReg .x24) 8 = true := by
      simpa using invariant.indices 0 (by omega)
    have indexSmall : (state.getMem (state.getReg .x24)).toNat < 2 ^ 24 := by
      simpa using invariant.indexValues 0 (by omega)
    have proofValid : ∀ word < 4 * (pathDepth + 1),
        accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true :=
      fun word smaller => invariant.proofs word (by
        have : 4 * (pathDepth + 1) * 1 ≤ 4 * (pathDepth + 1) * (count + 1) :=
          Nat.mul_le_mul_left _ (by omega)
        omega)
    have valueValid : ∀ word < 32,
        accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true :=
      fun word smaller => invariant.values word (by omega)
    let steps := pathInstructions (state.getMem (state.getReg .x24)) pathDepth
    have stepBound : steps ≤ 45 * pathDepth := (path_instruction_bounds _ pathDepth).2
    have depthLe : pathDepth ≤ 24 := invariant.depthBound
    let extra := fuel + (1281 - steps)
    have budget : 1412 * (count + 1) + 3 + fuel =
        116 + steps + (15 + (1412 * count + 3 + extra)) := by dsimp [extra]; omega
    rw [budget, check_position_hash pathDepth invariant.depthPos invariant.depthBound state pc
      invariant.depthReg indexValid invariant.scratch proofValid valueValid] at reachable
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
    obtain ⟨hashed, hashedReached, continued, continuedReached, rfl⟩ := reachable
    have hashRegs := check_position_hash_registers pathDepth invariant.depthPos invariant.depthBound
      state hashed invariant.depthReg hashedReached
    have scratchValid : ∀ word < 4,
        accessValid (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true := by
      rw [hashRegs.2.2.2.2 .x21 (by simp), invariant.scratch]
      intro word smaller; interval_cases word <;> decide
    have targetValid : ∀ word < 4,
        accessValid (hashed.getReg .x23 + BitVec.ofNat 64 (8 * word)) 8 = true := by
      rw [hashRegs.2.2.2.1]
      exact check_target_access_valid pathDepth invariant.depthBound _ _ indexSmall invariant.targets
    by_cases agrees : ∀ word < 4,
        hashed.getMem (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
          hashed.getMem (hashed.getReg .x23 + BitVec.ofNat 64 (8 * word))
    · have comparedPC : (checkRootWordsState hashed 66 4).pc = 4408 :=
        check_root_words_pc hashed 66 (Or.inl rfl) hashRegs.1 4 (by decide) agrees
      rw [show 15 + (1412 * count + 3 + extra) = 12 + (3 + (1412 * count + 3 + extra)) by omega,
        check_root_matches hashed 66 (Or.inl rfl) hashRegs.1 scratchValid targetValid agrees,
        check_position_next _ comparedPC] at continuedReached
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at continuedReached
      obtain ⟨afterLatch, ⟨tail, tailReached, rfl⟩, rfl⟩ := continuedReached
      have nextInvariant := check_loop_next_invariant state hashed count pathDepth (by omega) invariant hashedReached
      have rest : tail.exit ≠ .unfinished ∧ tail.cycles ≤ (159 + 52 * pathDepth) * count + 3 ∧
          tail.oracleCalls ≤ (4 + pathDepth) * count :=
        ih (checkPositionNextState (checkRootWordsState hashed 66 4)) (by omega) nextInvariant extra tail tailReached
      simp only [Execution.charge]
      refine ⟨rest.1, ?_, ?_⟩
      · dsimp [steps] at stepBound; rw [Nat.mul_succ]; omega
      · rw [Nat.mul_succ]; omega
    · obtain ⟨failed, run, exit, cycles, queries⟩ :=
        check_root_rejects hashed 66 (Or.inl rfl) hashRegs.1 scratchValid targetValid agrees
          (1412 * count + 3 + extra) allowCoins
      rw [run] at continuedReached
      simp only [support_pure, Set.mem_singleton_iff] at continuedReached
      subst continued
      simp only [Execution.charge, exit]
      refine ⟨by decide, ?_, ?_⟩
      · dsimp [steps] at stepBound; rw [Nat.mul_succ]; omega
      · rw [Nat.mul_succ]; omega

end CommitGolfCandidate
