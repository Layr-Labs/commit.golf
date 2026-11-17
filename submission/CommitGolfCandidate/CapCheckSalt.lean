import CommitGolfCandidate.CapCheckStart

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckSaltLoadedState (state : MachineState) : MachineState :=
  execInstrBr state (.LD .x20 .x24 0)

def capCheckSaltCopiedState (state : MachineState) : MachineState :=
  capWordCopyPrefix .x25 .x21 0 0 (capCheckSaltLoadedState state) 8

def capCheckSaltState (state : MachineState) : MachineState :=
  execInstrBr (capCheckSaltCopiedState state) (.ADDI .x25 .x25 32)

theorem cap_check_salt_copy_fetched :
    CapWordCopyFetched ((capExperimental 24).image .check)
      .x25 .x21 0 0 4216 := by
  intro state i bounded pc
  apply cap_image_fetch _ _ (30 + i) _ (by omega)
  · rw [cap_word_copy_prefix_pc _ _ _ _ _ i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem cap_check_salt_loaded_pc (state : MachineState)
    (pc : state.pc = 4212) :
    (capCheckSaltLoadedState state).pc = 4216 := by
  simp only [capCheckSaltLoadedState, execInstrBr, MachineState.setPC, pc]
  rfl

theorem cap_check_salt_loaded_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x20) :
    (capCheckSaltLoadedState state).getReg reg = state.getReg reg := by
  simp only [capCheckSaltLoadedState, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem cap_check_salt_execute (state : MachineState) (pc : state.pc = 4212)
    (scratch : state.getReg .x21 = 256)
    (indexValid : accessValid (state.getReg .x24) 8 = true)
    (saltValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (10 + fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckSaltState state) allowCoins
          return result.charge 10 0) := by
  have fetched : fetch ((capExperimental 24).image .check) state =
      some (.base (.LD .x20 .x24 0)) := by
    apply cap_image_fetch _ state 29 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.LD .x20 .x24 0)) =
      some (capCheckSaltLoadedState state) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess,
      show signExtend12 (0 : BitVec 12) = (0 : Word) by rfl,
      capCheckSaltLoadedState]
    change (if accessValid (state.getReg .x24 + (0#64)) 8 = true then
      some (execInstrBr state (.LD .x20 .x24 0)) else none) = _
    rw [BitVec.add_zero, indexValid]
    rfl
  have copyPC := cap_check_salt_loaded_pc state pc
  have copyScratch := (cap_check_salt_loaded_register state .x21 (by decide)).trans scratch
  have source : ∀ word : Fin 4,
      accessValid ((capCheckSaltLoadedState state).getReg .x25 +
        signExtend12 (BitVec.ofNat 12 (0 + 8 * word.val))) 8 = true := by
    intro word
    rw [cap_check_salt_loaded_register state .x25 (by decide)]
    have offset : signExtend12 (BitVec.ofNat 12 (0 + 8 * word.val)) =
        BitVec.ofNat 64 (8 * word.val) := by
      fin_cases word <;> decide
    rw [offset]
    exact saltValid word
  have destination : ∀ word : Fin 4,
      accessValid ((capCheckSaltLoadedState state).getReg .x21 +
        signExtend12 (BitVec.ofNat 12 (0 + 8 * word.val))) 8 = true := by
    intro word
    rw [copyScratch]
    fin_cases word <;> decide
  have copiedPC : (capCheckSaltCopiedState state).pc = 4248 := by
    rw [capCheckSaltCopiedState,
      cap_word_copy_prefix_pc .x25 .x21 0 0 _ 8 (by decide), copyPC]
    rfl
  have advanceFetch : fetch ((capExperimental 24).image .check)
      (capCheckSaltCopiedState state) = some (.base (.ADDI .x25 .x25 32)) := by
    apply cap_image_fetch _ _ 38 _ (by decide) copiedPC
    rfl
  have advanceStep : ordinaryStep (capCheckSaltCopiedState state)
      (.base (.ADDI .x25 .x25 32)) = some (capCheckSaltState state) := rfl
  rw [show 10 + fuel = (8 + (1 + fuel)) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped,
    cap_word_copy_execute _ .x25 .x21 0 0 4216 cap_check_salt_copy_fetched
      _ copyPC (by decide) (by decide) source destination]
  change (do
    let result ← execute ((capExperimental 24).image .check) (1 + fuel)
      (capCheckSaltCopiedState state) allowCoins
    return result.charge 8 0) >>= (fun result => pure (result.charge 1 0)) = _
  rw [Nat.add_comm 1 fuel,
    execute_ordinary_step _ _ _ _ _ _ advanceFetch advanceStep]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
