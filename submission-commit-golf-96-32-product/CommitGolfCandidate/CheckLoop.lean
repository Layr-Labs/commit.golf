import CommitGolfCandidate.CheckPath

/-! The checker's outer position loop. These proofs compose the actual index load,
salt copy, leaf hash, authentication path, and commitment comparison. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Load the next opened index before copying its salt into the hash accumulator. -/
def checkIndexState (state : MachineState) : MachineState :=
  (state.setReg .x20 (state.getMem (state.getReg .x24))).setPC 4156

theorem check_index (state : MachineState) (pc : state.pc = 4152)
    (valid : accessValid (state.getReg .x24) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkIndexState state) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .check) state = some (.base (.LD .x20 .x24 0)) := by
    apply check_fetch _ 14 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.LD .x20 .x24 0)) = some (checkIndexState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend12, valid,
      execInstrBr, checkIndexState, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Advance past the 32-byte salt and call the leaf-hashing subroutine. -/
def checkLeafCallState (state : MachineState) : MachineState :=
  ((state.setReg .x25 (state.getReg .x25 + 32)).setReg .x1 4196).setPC 4444

theorem check_leaf_call (state : MachineState) (pc : state.pc = 4188)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkLeafCallState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x25 (state.getReg .x25 + 32)).setPC 4192
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x25 .x25 32)) := by
    apply check_fetch _ 23 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) next = some (.base (.JAL .x1 252)) := by
    apply check_fetch _ 24 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x25 .x25 32)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend12, execInstrBr, next, pc]
  have s1 : ordinaryStep next (.base (.JAL .x1 252)) = some (checkLeafCallState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, signExtend21, execInstrBr,
      next, checkLeafCallState, MachineState.setPC, MachineState.setReg]
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- Entry state of the leaf subroutine for one opened position. -/
def checkPositionState (state : MachineState) : MachineState :=
  checkLeafCallState (checkPathCopyState (checkIndexState state) 15)

theorem check_position_setup (state : MachineState) (pc : state.pc = 4152)
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
  have copyPC : (checkPathCopyState (checkIndexState state) 15).pc = 4188 := by
    rw [check_path_copy_pc]; rfl
  rw [show 11 + fuel = 1 + (8 + (2 + fuel)) by omega,
    check_index state pc indexValid,
    check_path_copy (checkIndexState state) 15 (Or.inr (Or.inr (Or.inr rfl))) rfl initialScratch sourceValid,
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

/-- The machine-state distribution at the root comparison for one position. -/
def checkPositionHash (state : MachineState) : OracleComp World MachineState := do
  let leaf ← checkLeafLoop (((checkPositionState state).setReg .x28 4).setPC 4448) 4
  checkPathLoop (checkPathInitializedState (leaf.setPC 4196)) 24

set_option maxHeartbeats 300000 in
/-- A complete leaf and authentication-path computation, before root comparison.
The instruction and cycle totals account for the index's left/right branch choices;
all possible compression replies are included. Exactly 28 public calls are made. -/
theorem check_position_hash (state : MachineState) (pc : state.pc = 4152)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (scratch : state.getReg .x21 = 256)
    (proofValid : ∀ word < 100,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (valueValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check)
        (117 + pathInstructions (state.getMem (state.getReg .x24)) 24 + fuel) state allowCoins =
      (do let finished ← checkPositionHash state
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge (313 + pathInstructions (state.getMem (state.getReg .x24)) 24) 28) := by
  let ready := checkPositionState state
  let initialized := (ready.setReg .x28 4).setPC 4448
  have readyPC : ready.pc = 4444 := rfl
  have readyLink : ready.getReg .x1 = 4196 := by
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
  have saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
    fun word => proofValid word.val (by omega)
  rw [show 117 + pathInstructions (state.getMem (state.getReg .x24)) 24 + fuel =
      11 + (102 + (4 + pathInstructions (state.getMem (state.getReg .x24)) 24 + fuel)) by omega,
    check_position_setup state pc indexValid scratch saltValid,
    check_leaf_subroutine ready readyPC readyLink readyScratch readyValue]
  simp only [checkPositionHash, bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro leaf reached
  have registers := (check_leaf_loop_registers initialized 4 leaf reached).2
  have leafIndex : (leaf.setPC 4196).getReg .x20 = state.getMem (state.getReg .x24) := by
    rw [MachineState.getReg_setPC, registers .x20 (by decide), initRegister .x20 (by decide)]
    exact check_position_index state
  have leafScratch : (leaf.setPC 4196).getReg .x21 = 256 := by
    rw [MachineState.getReg_setPC, registers .x21 (by decide), initRegister .x21 (by decide)]
    exact readyScratch
  have leafSource : ∀ word < 96,
      accessValid ((leaf.setPC 4196).getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [MachineState.getReg_setPC, registers .x25 (by decide), initRegister .x25 (by decide),
      check_position_proof_pointer state]
    intro word bounded
    have address : state.getReg .x25 + 32 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x25 + BitVec.ofNat 64 (8 * (word + 4)) := by
      rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [address]
    exact proofValid (word + 4) (by omega)
  rw [← leafIndex, check_path_subroutine _ rfl leafScratch leafSource]
  simp only [leafIndex, bind_assoc, pure_bind]
  have charges (result : Execution) :
      ((result.charge (4 + pathInstructions (state.getMem (state.getReg .x24)) 24 + 168) 24).charge
        130 4).charge 11 0 =
      result.charge (313 + pathInstructions (state.getMem (state.getReg .x24)) 24) 28 := by
    cases result
    simp only [Execution.charge, Execution.mk.injEq, true_and]
    omega
  simp only [charges]

/-- Hashing one position reaches the commitment comparison and consumes exactly
one 256-byte leaf and one 800-byte salt/path record. Outer-loop metadata survives. -/
theorem check_position_hash_registers (state finished : MachineState)
    (reachable : finished ∈ support (checkPositionHash state)) :
    finished.pc = 4360 ∧
    finished.getReg .x8 = state.getReg .x8 + 256 ∧
    finished.getReg .x25 = state.getReg .x25 + 800 ∧
    ∀ reg ∈ [Reg.x21, .x24, .x26, .x27], finished.getReg reg = state.getReg reg := by
  simp only [checkPositionHash, mem_support_bind_iff] at reachable
  obtain ⟨leaf, leafReached, pathReached⟩ := reachable
  let initialized := ((checkPositionState state).setReg .x28 4).setPC 4448
  have leafRegs := check_leaf_loop_registers initialized 4 leaf leafReached
  have pathRegs := check_path_loop_registers _ 24 finished pathReached
  have initRegister (reg : Reg) (notCounter : reg ≠ .x28) :
      initialized.getReg reg = (checkPositionState state).getReg reg := by
    simp only [initialized, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notCounter)]
  refine ⟨(check_path_loop_finished _ 24 (by decide)
      (check_path_initialized_counter _) finished pathReached).2 (by decide), ?_, ?_, ?_⟩
  · rw [pathRegs.2 .x8 (by decide), check_path_setup_register _ .x8 (by decide),
      MachineState.getReg_setPC, leafRegs.1, initRegister .x8 (by decide),
      check_position_register state .x8 (by decide)]
    rfl
  · rw [pathRegs.1, check_path_setup_register _ .x25 (by decide), MachineState.getReg_setPC,
      leafRegs.2 .x25 (by decide), initRegister .x25 (by decide), check_position_proof_pointer]
    change state.getReg .x25 + 32 + 768 = state.getReg .x25 + 800
    rw [BitVec.add_assoc]; rfl
  · intro reg included
    have pathPreserved : reg ∉ [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x20, .x25, .x29,
        .x14, .x15, .x16, .x17, .x31] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl <;> decide
    have leafPreserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28,
        .x14, .x15, .x16, .x17, .x31] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl <;> decide
    have setupPreserved : reg ∉ [Reg.x1, .x6, .x20, .x25] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl <;> decide
    have not29 : reg ≠ .x29 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl <;> decide
    have not28 : reg ≠ .x28 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at included
      rcases included with rfl | rfl | rfl | rfl <;> decide
    rw [pathRegs.2 reg pathPreserved, check_path_setup_register _ reg not29,
      MachineState.getReg_setPC, leafRegs.2 reg leafPreserved, initRegister reg not28,
      check_position_register state reg setupPreserved]

/-- A first mismatching word terminates the real checker, regardless of the remaining fuel. -/
theorem check_root_first_mismatch (state : MachineState) (pc : state.pc = 4360)
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (rootValid : ∀ word < 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (word : Nat) (bounded : word < 4)
    (earlier : ∀ index < word,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * index)) =
        state.getMem (state.getReg .x26 + BitVec.ofNat 64 (8 * index)))
    (different : state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) ≠
      state.getMem (state.getReg .x26 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 * word + 6 + fuel) state allowCoins =
      pure ⟨.failure, checkExitState (checkRootWordState (checkRootWordsState state word) word) false,
        3 * word + 6, 0⟩ := by
  have prefixPC := check_root_words_pc state pc word (by omega) earlier
  have scratchReg := (check_root_words_preserves state word .x21 (by decide) (by decide)).1
  have rootPreserves := check_root_words_preserves state word .x26 (by decide) (by decide)
  have rootReg := rootPreserves.1
  have scratchAccess : accessValid ((checkRootWordsState state word).getReg .x21 +
      BitVec.ofNat 64 (8 * word)) 8 = true := by rw [scratchReg]; exact scratchValid word bounded
  have rootAccess : accessValid ((checkRootWordsState state word).getReg .x26 +
      BitVec.ofNat 64 (8 * word)) 8 = true := by rw [rootReg]; exact rootValid word bounded
  have mismatch : (checkRootWordsState state word).getMem
        ((checkRootWordsState state word).getReg .x21 + BitVec.ofNat 64 (8 * word)) ≠
      (checkRootWordsState state word).getMem
        ((checkRootWordsState state word).getReg .x26 + BitVec.ofNat 64 (8 * word)) := by
    simpa only [scratchReg, rootReg, MachineState.getMem, rootPreserves.2] using different
  rw [Nat.add_assoc, check_root_prefix state pc scratchValid rootValid word (by omega) earlier,
    check_root_word_reject _ word bounded prefixPC scratchAccess rootAccess mismatch]
  simp [Execution.charge, Nat.add_comm]

/-- If any commitment word differs, the checker halts with failure within fifteen
instructions/cycles. Earlier matching words do not mask a later mismatch. -/
theorem check_root_rejects (state : MachineState) (pc : state.pc = 4360)
    (scratchValid : ∀ word < 4,
      accessValid (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (rootValid : ∀ word < 4,
      accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (different : ¬ ∀ word < 4,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
        state.getMem (state.getReg .x26 + BitVec.ofNat 64 (8 * word)))
    (fuel : Nat) (allowCoins : Bool) :
    ∃ result, execute (submission.image .check) (15 + fuel) state allowCoins = pure result ∧
      result.exit = .failure ∧ result.cycles ≤ 15 ∧ result.oracleCalls = 0 := by
  have existsMismatch : ∃ word, word < 4 ∧
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * word)) ≠
        state.getMem (state.getReg .x26 + BitVec.ofNat 64 (8 * word)) := by
    push Not at different
    exact different
  let word := Nat.find existsMismatch
  have bounded : word < 4 := (Nat.find_spec existsMismatch).1
  have mismatch := (Nat.find_spec existsMismatch).2
  have earlier : ∀ index < word,
      state.getMem (state.getReg .x21 + BitVec.ofNat 64 (8 * index)) =
        state.getMem (state.getReg .x26 + BitVec.ofNat 64 (8 * index)) := by
    intro index before
    have minimal := Nat.find_min existsMismatch before
    exact Classical.byContradiction (fun neq => minimal ⟨by omega, neq⟩)
  refine ⟨⟨.failure, checkExitState (checkRootWordState (checkRootWordsState state word) word) false,
    3 * word + 6, 0⟩, ?_, rfl, by dsimp; omega, rfl⟩
  have remaining : 15 + fuel = 3 * word + 6 + (9 - 3 * word + fuel) := by omega
  rw [remaining]
  exact check_root_first_mismatch state pc scratchValid rootValid word bounded earlier mismatch _ allowCoins

/-- After a matching root, advance to the next index or the success exit. -/
def checkPositionNextState (state : MachineState) : MachineState :=
  ((state.setReg .x24 (state.getReg .x24 + 8)).setReg .x27 (state.getReg .x27 - 1)).setPC
    (if state.getReg .x27 - 1 = 0 then 4420 else 4152)

theorem check_position_next_pc (state : MachineState) :
    (checkPositionNextState state).pc =
      if state.getReg .x27 - 1 = 0 then 4420 else 4152 := rfl

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
  have f2 : fetch (submission.image .check) decremented = some (.base (.BNE .x27 .x0 7928)) := by
    apply check_fetch _ 80 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x24 .x24 8)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have s1 : ordinaryStep next (.base (.ADDI .x27 .x27 4095)) = some decremented := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, decremented, MachineState.getReg, MachineState.setReg, MachineState.setPC,
      BitVec.sub_eq_add_neg]
  have s2 : ordinaryStep decremented (.base (.BNE .x27 .x0 7928)) = some (checkPositionNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      decremented, next, checkPositionNextState, MachineState.getReg,
      MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- Buffer and control invariants at the start of each outer iteration. These are
memory-safety conditions, not assumptions about the truth of the submitted proof. -/
structure CheckLoopInvariant (state : MachineState) (count : Nat) : Prop where
  pc : state.pc = if count = 0 then 4420 else 4152
  counter : state.getReg .x27 = BitVec.ofNat 64 count
  scratch : state.getReg .x21 = 256
  indices : ∀ word < count,
    accessValid (state.getReg .x24 + BitVec.ofNat 64 (8 * word)) 8 = true
  values : ∀ word < 32 * count,
    accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true
  proofs : ∀ word < 100 * count,
    accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true
  root : ∀ word < 4,
    accessValid (state.getReg .x26 + BitVec.ofNat 64 (8 * word)) 8 = true

/-- Successful root comparison preserves the invariants for the remaining positions. -/
theorem check_loop_next_invariant (state hashed : MachineState) (count : Nat)
    (bounded : count < 2 ^ 24)
    (invariant : CheckLoopInvariant state (count + 1))
    (reachable : hashed ∈ support (checkPositionHash state)) :
    CheckLoopInvariant (checkPositionNextState (checkRootWordsState hashed 4)) count := by
  have hashRegs := check_position_hash_registers state hashed reachable
  let compared := checkRootWordsState hashed 4
  have preserved (reg : Reg) (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) :
      compared.getReg reg = hashed.getReg reg :=
    (check_root_words_preserves hashed 4 reg not6 not7).1
  have counter : compared.getReg .x27 - 1 = BitVec.ofNat 64 count := by
    rw [preserved .x27 (by decide) (by decide), hashRegs.2.2.2 .x27 (by simp), invariant.counter]
    change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
    rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
    congr 1
  have indexPtr : (checkPositionNextState compared).getReg .x24 = state.getReg .x24 + 8 := by
    simp only [checkPositionNextState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x27 ≠ .x24),
      MachineState.getReg_setReg_eq (by decide : Reg.x24 ≠ .x0),
      preserved .x24 (by decide) (by decide), hashRegs.2.2.2 .x24 (by simp)]
  have otherReg (reg : Reg) (not24 : reg ≠ .x24) (not27 : reg ≠ .x27)
      (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) :
      (checkPositionNextState compared).getReg reg = hashed.getReg reg := by
    simp only [checkPositionNextState, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not27),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not24), preserved reg not6 not7]
  have valuePtr : (checkPositionNextState compared).getReg .x8 = state.getReg .x8 + 256 :=
    (otherReg .x8 (by decide) (by decide) (by decide) (by decide)).trans hashRegs.2.1
  have proofPtr : (checkPositionNextState compared).getReg .x25 = state.getReg .x25 + 800 :=
    (otherReg .x25 (by decide) (by decide) (by decide) (by decide)).trans hashRegs.2.2.1
  have rootPtr : (checkPositionNextState compared).getReg .x26 = state.getReg .x26 :=
    (otherReg .x26 (by decide) (by decide) (by decide) (by decide)).trans
      (hashRegs.2.2.2 .x26 (by simp))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [check_position_next_pc, counter]
    have zero : BitVec.ofNat 64 count = 0 ↔ count = 0 := by
      constructor
      · intro equal
        have numeric := congrArg BitVec.toNat equal
        change count % 18446744073709551616 = 0 at numeric
        omega
      · rintro rfl; rfl
    simp only [zero]
  · rw [check_position_next_counter, counter]
  · rw [otherReg .x21 (by decide) (by decide) (by decide) (by decide),
      hashRegs.2.2.2 .x21 (by simp)]
    exact invariant.scratch
  · intro word smaller
    rw [indexPtr]
    have address : state.getReg .x24 + 8 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x24 + BitVec.ofNat 64 (8 * (word + 1)) := by
      rw [show 8 * (word + 1) = 8 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    exact invariant.indices (word + 1) (by omega)
  · intro word smaller
    rw [valuePtr]
    have address : state.getReg .x8 + 256 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x8 + BitVec.ofNat 64 (8 * (word + 32)) := by
      rw [show 8 * (word + 32) = 256 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    exact invariant.values (word + 32) (by omega)
  · intro word smaller
    rw [proofPtr]
    have address : state.getReg .x25 + 800 + BitVec.ofNat 64 (8 * word) =
        state.getReg .x25 + BitVec.ofNat 64 (8 * (word + 100)) := by
      rw [show 8 * (word + 100) = 800 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]; rfl
    rw [address]
    exact invariant.proofs (word + 100) (by omega)
  · rw [rootPtr]
    exact invariant.root

attribute [local irreducible] checkRootWordsState checkPositionNextState checkPositionHash
  execute pathInstructions

set_option maxHeartbeats 500000 in
/-- Every outer-loop execution terminates, even for incorrect proof contents.
A uniform allowance of 1412 instructions per position suffices; cycles are at most
1612 per position and there are at most 32 public queries per position (exactly 28 are made). These are
worst-case bounds over all oracle answers, not test measurements. -/
theorem check_loop_terminates (state : MachineState) (count : Nat)
    (bounded : count ≤ 2 ^ 24) (invariant : CheckLoopInvariant state count)
    (fuel : Nat) (allowCoins : Bool) (result : Execution)
    (reachable : result ∈ support
      (execute (submission.image .check) (1412 * count + 3 + fuel) state allowCoins)) :
    result.exit ≠ .unfinished ∧ result.cycles ≤ 1612 * count + 3 ∧
      result.oracleCalls ≤ 32 * count := by
  induction count generalizing state fuel result with
  | zero =>
    have pc : state.pc = 4420 := by simpa using invariant.pc
    rw [show 1412 * 0 + 3 + fuel = 3 + fuel by omega, check_exit state true pc] at reachable
    simp only [support_pure, Set.mem_singleton_iff] at reachable
    subst result
    simp
  | succ count ih =>
    have pc : state.pc = 4152 := by simpa using invariant.pc
    have indexValid : accessValid (state.getReg .x24) 8 = true := by
      simpa using invariant.indices 0 (by omega)
    have proofValid : ∀ word < 100,
        accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true :=
      fun word smaller => invariant.proofs word (by omega)
    have valueValid : ∀ word < 32,
        accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true :=
      fun word smaller => invariant.values word (by omega)
    let steps := pathInstructions (state.getMem (state.getReg .x24)) 24
    have stepBound : steps ≤ 1080 := (path_instruction_bounds _ 24).2
    let extra := fuel + (1280 - steps)
    have budget : 1412 * (count + 1) + 3 + fuel =
        117 + steps + (15 + (1412 * count + 3 + extra)) := by dsimp [extra]; omega
    rw [budget, check_position_hash state pc indexValid invariant.scratch proofValid valueValid] at reachable
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at reachable
    obtain ⟨hashed, hashedReached, continued, continuedReached, rfl⟩ := reachable
    have hashRegs := check_position_hash_registers state hashed hashedReached
    have scratchValid : ∀ word < 4,
        accessValid (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true := by
      rw [hashRegs.2.2.2 .x21 (by simp), invariant.scratch]
      intro word smaller
      interval_cases word <;> decide
    have rootValid : ∀ word < 4,
        accessValid (hashed.getReg .x26 + BitVec.ofNat 64 (8 * word)) 8 = true := by
      rw [hashRegs.2.2.2 .x26 (by simp)]
      exact invariant.root
    by_cases agrees : ∀ word < 4,
        hashed.getMem (hashed.getReg .x21 + BitVec.ofNat 64 (8 * word)) =
          hashed.getMem (hashed.getReg .x26 + BitVec.ofNat 64 (8 * word))
    · have comparedPC : (checkRootWordsState hashed 4).pc = 4408 :=
        check_root_words_pc hashed hashRegs.1 4 (by decide) agrees
      rw [show 15 + (1412 * count + 3 + extra) = 12 + (3 + (1412 * count + 3 + extra)) by omega,
        check_root_matches hashed hashRegs.1 scratchValid rootValid agrees,
        check_position_next _ comparedPC] at continuedReached
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at continuedReached
      obtain ⟨afterLatch, ⟨tail, tailReached, rfl⟩, rfl⟩ := continuedReached
      have nextInvariant := check_loop_next_invariant state hashed count (by omega) invariant hashedReached
      have rest : tail.exit ≠ .unfinished ∧ tail.cycles ≤ 1612 * count + 3 ∧
          tail.oracleCalls ≤ 32 * count := by
        apply ih (checkPositionNextState (checkRootWordsState hashed 4)) (by omega) nextInvariant extra tail
        exact tailReached
      simp only [Execution.charge]
      refine ⟨rest.1, ?_, ?_⟩ <;> dsimp [steps] at stepBound <;> omega
    · obtain ⟨failed, run, exit, cycles, queries⟩ :=
        check_root_rejects hashed hashRegs.1 scratchValid rootValid agrees (1412 * count + 3 + extra) allowCoins
      rw [run] at continuedReached
      simp only [support_pure, Set.mem_singleton_iff] at continuedReached
      subst continued
      simp only [Execution.charge, exit]
      refine ⟨by decide, ?_, ?_⟩ <;> dsimp [steps] at stepBound <;> omega

end CommitGolfCandidate
