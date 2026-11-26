import CommitGolfCandidate.PairControl

import CommitGolfCandidate.CheckLoop

import CommitGolfCandidate.PairPath

namespace CommitGolfCandidate.PairCap

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 12000

set_option maxHeartbeats 1400000

def rec_checkIndexState (state : MachineState) : MachineState :=
  (state.setReg .x20 (state.getMem (state.getReg .x24))).setPC 5028

theorem rec_check_index (state : MachineState) (pc : state.pc = 5024)
    (valid : accessValid (state.getReg .x24) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (rec_checkIndexState state) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .check) state = some (.base (.LD .x20 .x24 0)) := by
    apply patchedFetch _ 232 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.LD .x20 .x24 0)) = some (rec_checkIndexState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend12, valid,
      execInstrBr, rec_checkIndexState, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

def rec_checkSaltTagInstructions : List Instr :=
  [.LD .x6 .x25 0, .SD .x21 .x6 0,
   .LD .x6 .x25 8, .SD .x21 .x6 8,
   .ADDI .x6 .x20 16, .SLLI .x6 .x6 8, .ADDI .x6 .x6 4072, .SD .x21 .x6 16]

def rec_checkSaltTagPrefix (state : MachineState) (count : Nat) : MachineState :=
  (rec_checkSaltTagInstructions.take count).foldl execInstrBr state

theorem rec_check_salt_tag_prefix_register (state : MachineState) (count : Nat)
    (bounded : count ≤ 8) (reg : Reg) (notScratch : reg ≠ .x6) :
    (rec_checkSaltTagPrefix state count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [rec_checkSaltTagPrefix, rec_checkSaltTagInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch)]

theorem rec_check_salt_tag (state : MachineState) (pc : state.pc = 5028)
    (scratch : state.getReg .x21 = 256)
    (saltValid : ∀ word : Fin 2,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkSaltTagState state) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := rec_checkSaltTagPrefix state)
  intro i hi
  refine ⟨.base ((rec_checkSaltTagInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply patchedFetch _ (233 + i) _ (by omega)
    · interval_cases i <;>
        simp [rec_checkSaltTagPrefix, rec_checkSaltTagInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have sourceReg := rec_check_salt_tag_prefix_register state i (by omega) .x25 (by decide)
    have scratchReg := (rec_check_salt_tag_prefix_register state i (by omega) .x21 (by decide)).trans scratch
    have s0 := saltValid ⟨0, by decide⟩
    have s1 := saltValid ⟨1, by decide⟩
    have valid : memoryArgumentsValid (rec_checkSaltTagPrefix state i)
        ((rec_checkSaltTagInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [rec_checkSaltTagInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12]
      · exact s0
      · rfl
      · exact s1
      · rfl
      · rfl
    interval_cases i <;>
      simp only [rec_checkSaltTagInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

def rec_checkLeafCallState (state : MachineState) : MachineState :=
  ((state.setReg .x25 (state.getReg .x25 + 16)).setReg .x1 5068).setPC 4712

theorem rec_check_leaf_call (state : MachineState) (pc : state.pc = 5060)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (rec_checkLeafCallState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x25 (state.getReg .x25 + 16)).setPC 5064
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x25 .x25 16)) := by
    apply patchedFetch _ 241 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) next = some (.base (.JAL .x1 2096800)) := by
    apply patchedFetch _ 242 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x25 .x25 16)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend12, execInstrBr, next, pc]
  have s1 : ordinaryStep next (.base (.JAL .x1 2096800)) = some (rec_checkLeafCallState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend21, execInstrBr,
      next, rec_checkLeafCallState, MachineState.setPC, MachineState.setReg]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

def rec_checkPositionState (state : MachineState) : MachineState :=
  rec_checkLeafCallState (checkSaltTagState (rec_checkIndexState state))

theorem rec_check_position_setup (state : MachineState) (pc : state.pc = 5024)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (scratch : state.getReg .x21 = 256)
    (saltValid : ∀ word : Fin 2,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (11 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (rec_checkPositionState state) allowCoins
          return result.charge 11 0) := by
  have initialScratch : (rec_checkIndexState state).getReg .x21 = 256 := by
    simpa [rec_checkIndexState, MachineState.getReg, MachineState.setReg, MachineState.setPC] using scratch
  have sourceValid : ∀ word : Fin 2,
      accessValid ((rec_checkIndexState state).getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    simpa [rec_checkIndexState, MachineState.getReg, MachineState.setReg, MachineState.setPC] using saltValid
  have copyPC : (checkSaltTagState (rec_checkIndexState state)).pc = 5060 := by
    rw [check_salt_tag_pc]; rfl
  rw [show 11 + fuel = 1 + (8 + (2 + fuel)) by omega,
    rec_check_index state pc indexValid,
    rec_check_salt_tag (rec_checkIndexState state) rfl initialScratch sourceValid,
    rec_check_leaf_call _ copyPC]
  simp [rec_checkPositionState, Execution.charge, ← Nat.add_assoc]

theorem rec_check_position_register (state : MachineState) (reg : Reg)
    (unchanged : reg ∉ [Reg.x1, .x6, .x20, .x25]) :
    (rec_checkPositionState state).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at unchanged
  simp only [rec_checkPositionState, rec_checkLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm unchanged.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm unchanged.2.2.2),
    check_salt_tag_register _ reg unchanged.2.1,
    rec_checkIndexState, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm unchanged.2.2.1)]

theorem rec_check_position_index (state : MachineState) :
    (rec_checkPositionState state).getReg .x20 = state.getMem (state.getReg .x24) := by
  simp only [rec_checkPositionState, rec_checkLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x20),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x25 ≠ .x20),
    check_salt_tag_register _ .x20 (by decide), rec_checkIndexState,
    MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0)]

theorem rec_check_position_proof_pointer (state : MachineState) :
    (rec_checkPositionState state).getReg .x25 = state.getReg .x25 + 16 := by
  simp only [rec_checkPositionState, rec_checkLeafCallState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x1 ≠ .x25),
    MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0),
    check_salt_tag_register _ .x25 (by decide), rec_checkIndexState,
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x25)]

def rec_checkTargetState (state : MachineState) : MachineState := state

def rec_checkPositionHash (state : MachineState) (pathDepth : Nat) : OracleComp World MachineState := do
  let leaf ← checkLeafSubroutineRun (rec_checkPositionState state)
  let pathed ← rec_checkPathLoop (rec_checkPathInitializedState (leaf.setPC 5068)) pathDepth
  return rec_checkTargetState pathed

theorem rec_check_position_hash (pathDepth : Nat) (depthPos : 0 < pathDepth)
    (depthBound : pathDepth ≤ 24) (state : MachineState) (pc : state.pc = 5024)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (scratch : state.getReg .x21 = 256)
    (proofValid : ∀ word < 2 + 4 * pathDepth,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (valueValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check)
        (114 + pathInstructions (state.getMem (state.getReg .x24)) pathDepth + fuel) state allowCoins =
      (do let finished ← rec_checkPositionHash state pathDepth
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge
            (142 + pathInstructions (state.getMem (state.getReg .x24)) pathDepth + 7 * pathDepth)
            (4 + pathDepth)) := by
  let ready := rec_checkPositionState state
  have readyPC : ready.pc = 4712 := rfl
  have readyLink : ready.getReg .x1 = 5068 := by
    simp only [ready, rec_checkPositionState, rec_checkLeafCallState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x1 ≠ .x0)]
  have readyScratch : ready.getReg .x21 = 256 :=
    (rec_check_position_register state .x21 (by decide)).trans scratch
  have readyValue : ∀ word < 32,
      accessValid (ready.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [rec_check_position_register state .x8 (by decide)]; exact valueValid
  have saltValid : ∀ word : Fin 2,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
    fun word => proofValid word.val (by omega)
  rw [show 114 + pathInstructions (state.getMem (state.getReg .x24)) pathDepth + fuel =
      11 + (102 + (1 + pathInstructions (state.getMem (state.getReg .x24)) pathDepth + fuel)) by omega,
    rec_check_position_setup state pc indexValid scratch saltValid,
    rec_check_leaf_subroutine ready readyPC readyLink readyScratch readyValue]
  simp only [rec_checkPositionHash, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaf reached
  have registers := (check_leaf_subroutine_registers ready leaf reached).2
  have leafIndex : (leaf.setPC 5068).getReg .x20 = state.getMem (state.getReg .x24) := by
    rw [MachineState.getReg_setPC, registers .x20 (by decide)]
    exact rec_check_position_index state
  have leafScratch : (leaf.setPC 5068).getReg .x21 = 256 := by
    rw [MachineState.getReg_setPC, registers .x21 (by decide)]
    exact readyScratch
  have leafDepth : (leaf.setPC 5068).getReg .x30 = BitVec.ofNat 64 pathDepth := by
    rw [MachineState.getReg_setPC, registers .x30 (by decide),
      rec_check_position_register state .x30 (by decide), depthReg]
  have leafSource : ∀ word < 4 * pathDepth,
      accessValid ((leaf.setPC 5068).getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [MachineState.getReg_setPC, registers .x25 (by decide),
      rec_check_position_proof_pointer state]
    intro word bounded
    have address : state.getReg .x25 + 16 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x25 + BitVec.ofNat 64 (8 * (word + 2)) := by
      rw [show 8 * (word + 2) = 16 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    exact proofValid (word + 2) (by omega)
  rw [← leafIndex, rec_check_path_subroutine pathDepth depthBound _ rfl leafDepth leafScratch leafSource]
  simp only [leafIndex, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro pathed pathReached
  change _ = _
  simp only [rec_checkTargetState, bind_assoc, pure_bind]
  apply bind_congr
  intro res
  congr 1
  simp only [Execution.charge, Execution.mk.injEq, true_and]
  constructor <;> omega

theorem rec_check_position_hash_registers (pathDepth : Nat) (depthPos : 0 < pathDepth)
    (depthBound : pathDepth ≤ 24) (state finished : MachineState)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (reachable : finished ∈ support (rec_checkPositionHash state pathDepth)) :
    finished.pc = 5220 ∧
    finished.getReg .x8 = state.getReg .x8 + 256 ∧
    finished.getReg .x25 = state.getReg .x25 + BitVec.ofNat 64 (16 + 32 * pathDepth) ∧
    finished.getReg .x20 = state.getMem (state.getReg .x24) >>> pathDepth ∧
    ∀ reg ∈ [Reg.x19, .x21, .x24, .x26, .x27, .x30], finished.getReg reg = state.getReg reg := by
  simp only [rec_checkPositionHash, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
  obtain ⟨leaf, leafReached, pathed, pathReached, eqFin⟩ := reachable
  subst finished
  have leafRegs := check_leaf_subroutine_registers (rec_checkPositionState state) leaf leafReached
  have pathRegs := rec_check_path_loop_registers _ pathDepth pathed pathReached
  have keepPathed (reg : Reg) (included : reg ∈ [Reg.x19, .x21, .x24, .x26, .x27, .x30]) :
      pathed.getReg reg = state.getReg reg := by
    have pathPreserved : reg ∉ [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x20, .x25, .x29,
        .x14, .x15, .x16, .x17, .x31] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have leafPreserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28,
        .x14, .x15, .x16, .x17, .x31] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have setupPreserved : reg ∉ [Reg.x1, .x6, .x20, .x25] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have not29 : reg ≠ .x29 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [pathRegs.2.2 reg pathPreserved, rec_check_path_setup_register _ reg not29,
      MachineState.getReg_setPC, leafRegs.2 reg leafPreserved,
      rec_check_position_register state reg setupPreserved]
  have pathedX20 : pathed.getReg .x20 = state.getMem (state.getReg .x24) >>> pathDepth := by
    rw [pathRegs.2.1, rec_check_path_setup_register _ .x20 (by decide), MachineState.getReg_setPC,
      leafRegs.2 .x20 (by decide), rec_check_position_index state]
  have depth : leaf.getReg .x30 = BitVec.ofNat 64 pathDepth := by
    rw [leafRegs.2 .x30 (by decide), rec_check_position_register state .x30 (by decide), depthReg]
  have endPc := (rec_check_path_loop_finished _ pathDepth depthBound
      (by rw [rec_check_path_initialized_counter]; exact depth) pathed pathReached).2 depthPos
  refine ⟨endPc, ?_, ?_, pathedX20, keepPathed⟩
  · change pathed.getReg .x8 = _
    rw [pathRegs.2.2 .x8 (by decide), rec_check_path_setup_register _ .x8 (by decide),
      MachineState.getReg_setPC, leafRegs.1, rec_check_position_register state .x8 (by decide)]
  · change pathed.getReg .x25 = _
    rw [pathRegs.1, rec_check_path_setup_register _ .x25 (by decide), MachineState.getReg_setPC,
      leafRegs.2 .x25 (by decide), rec_check_position_proof_pointer,
      BitVec.ofNat_add, BitVec.add_assoc]; rfl

end CommitGolfCandidate.PairCap
