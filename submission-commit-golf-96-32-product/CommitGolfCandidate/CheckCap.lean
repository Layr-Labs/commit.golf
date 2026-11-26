import CommitGolfCandidate.Check

/-! The checker's cap block: copy the 64 supplied cap pairs behind the chaining value
in scratch and make one direct 96-byte compression call per pair, starting from the
zero state. The resulting digest is compared with the commitment. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 8192

private theorem register_set_mem (state : MachineState) (address value : Word) (reg : Reg) :
    (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl

private def capSetupInstructions : List Instr :=
  [.ADDI .x30 .x25 0, .SD .x21 .x0 0, .SD .x21 .x0 8, .SD .x21 .x0 16, .SD .x21 .x0 24,
   .ADDI .x5 .x0 0, .ADDI .x11 .x0 96, .ADDI .x13 .x0 0,
   .ADDI .x28 .x0 0, .SLLI .x28 .x28 11, .ADDI .x28 .x28 64]

private def capSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capSetupInstructions.take count).foldl execInstrBr state

/-- Save the cap base, zero the chaining value, fix the syscall arguments, set the counter. -/
def checkCapSetupState (state : MachineState) : MachineState := capSetupPrefix state 11

theorem check_cap_setup_expansion (state : MachineState) :
    checkCapSetupState state =
      ([.ADDI .x30 .x25 0, .SD .x21 .x0 0, .SD .x21 .x0 8, .SD .x21 .x0 16, .SD .x21 .x0 24,
        .ADDI .x5 .x0 0, .ADDI .x11 .x0 96, .ADDI .x13 .x0 0,
        .ADDI .x28 .x0 0, .SLLI .x28 .x28 11, .ADDI .x28 .x28 64] : List Instr).foldl
          execInstrBr state := rfl

private theorem cap_setup_x21 (state : MachineState) (count : Nat) (bounded : count ≤ 11) :
    (capSetupPrefix state count).getReg .x21 = state.getReg .x21 := by
  interval_cases count <;>
    simp only [capSetupPrefix, capSetupInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, register_set_mem,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x30 ≠ .x21),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x5 ≠ .x21),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x11 ≠ .x21),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x13 ≠ .x21),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x21)]

set_option maxHeartbeats 1600000 in
theorem check_cap_setup (state : MachineState) (pc : state.pc = 4164)
    (scratch : state.getReg .x21 = 256) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (11 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkCapSetupState state) allowCoins
          return result.charge 11 0) := by
  apply execute_unit_steps (states := capSetupPrefix state)
  intro i hi
  refine ⟨.base ((capSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (17 + i) _ (by omega)
    · interval_cases i <;>
        simp [capSetupPrefix, capSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have scratchReg := (cap_setup_x21 state i (by omega)).trans scratch
    have valid : memoryArgumentsValid (capSetupPrefix state i)
        ((capSetupInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [capSetupInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, scratchReg, signExtend12] <;> rfl
    interval_cases i <;>
      simp only [capSetupInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

theorem check_cap_setup_register (state : MachineState) (reg : Reg)
    (not5 : reg ≠ .x5) (not11 : reg ≠ .x11) (not13 : reg ≠ .x13) (not28 : reg ≠ .x28)
    (not30 : reg ≠ .x30) :
    (checkCapSetupState state).getReg reg = state.getReg reg := by
  simp only [checkCapSetupState, capSetupPrefix, capSetupInstructions, List.take, List.foldl,
    execInstrBr, MachineState.getReg_setPC, register_set_mem,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not5),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not13),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not30)]

theorem check_cap_setup_registers (state : MachineState) (pc : state.pc = 4164) :
    (checkCapSetupState state).pc = 4208 ∧
    (checkCapSetupState state).getReg .x30 = state.getReg .x25 ∧
    (checkCapSetupState state).getReg .x28 = BitVec.ofNat 64 64 ∧
    (checkCapSetupState state).getReg .x5 = 0 ∧
    (checkCapSetupState state).getReg .x11 = 96 ∧
    (checkCapSetupState state).getReg .x13 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [checkCapSetupState, capSetupPrefix, capSetupInstructions, execInstrBr, pc,
      MachineState.setPC, MachineState.setMem] <;> rfl
  · simp only [checkCapSetupState, capSetupPrefix, capSetupInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC, register_set_mem,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x5 ≠ .x30),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x11 ≠ .x30),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x13 ≠ .x30),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x30),
      MachineState.getReg_setReg_eq (by decide : Reg.x30 ≠ .x0), signExtend12]
    simp
  all_goals
    simp only [checkCapSetupState, capSetupPrefix, capSetupInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC, register_set_mem, signExtend12,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x5),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x11),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x13),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x13 ≠ .x5),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x13 ≠ .x11),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x11 ≠ .x5),
      MachineState.getReg_setReg_eq (by decide : Reg.x5 ≠ .x0),
      MachineState.getReg_setReg_eq (by decide : Reg.x11 ≠ .x0),
      MachineState.getReg_setReg_eq (by decide : Reg.x13 ≠ .x0),
      MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ .x0)] <;> rfl

theorem check_cap_setup_memory (state : MachineState) (scratch : state.getReg .x21 = 256)
    (address : Word) (outside : ∀ i < 4, address ≠ BitVec.ofNat 64 (256 + 8 * i)) :
    (checkCapSetupState state).getMem address = state.getMem address := by
  have o0 : address ≠ 256#64 := outside 0 (by decide)
  have o1 : address ≠ 264#64 := outside 1 (by decide)
  have o2 : address ≠ 272#64 := outside 2 (by decide)
  have o3 : address ≠ 280#64 := outside 3 (by decide)
  rw [check_cap_setup_expansion]
  simp only [List.foldl, execInstrBr, signExtend12]
  simp [register_set_mem, scratch, o0, o1, o2, o3, MachineState.getReg_setReg_ne,
    MachineState.getReg_setReg_eq]

theorem check_cap_setup_zero (state : MachineState) (scratch : state.getReg .x21 = 256)
    (word : Nat) (bounded : word < 4) :
    (checkCapSetupState state).getMem (BitVec.ofNat 64 (256 + 8 * word)) = 0 := by
  rw [check_cap_setup_expansion]
  simp only [List.foldl, execInstrBr, signExtend12]
  interval_cases word <;>
    simp [register_set_mem, scratch, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq] <;> rfl

/-! One cap iteration: copy a 64-byte pair from x25 behind the chaining value, point
both syscall buffers at scratch, call, then advance the pointer and counter. -/

private def capCopyInstructions : List Instr :=
  [.LD .x6 .x25 0, .SD .x21 .x6 32, .LD .x6 .x25 8, .SD .x21 .x6 40,
   .LD .x6 .x25 16, .SD .x21 .x6 48, .LD .x6 .x25 24, .SD .x21 .x6 56,
   .LD .x6 .x25 32, .SD .x21 .x6 64, .LD .x6 .x25 40, .SD .x21 .x6 72,
   .LD .x6 .x25 48, .SD .x21 .x6 80, .LD .x6 .x25 56, .SD .x21 .x6 88,
   .ADDI .x10 .x21 0, .ADDI .x12 .x21 0]

private def capCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCopyInstructions.take count).foldl execInstrBr state

def checkCapCopyState (state : MachineState) : MachineState := capCopyPrefix state 18

theorem check_cap_copy_expansion (state : MachineState) :
    checkCapCopyState state =
      ([.LD .x6 .x25 0, .SD .x21 .x6 32, .LD .x6 .x25 8, .SD .x21 .x6 40,
        .LD .x6 .x25 16, .SD .x21 .x6 48, .LD .x6 .x25 24, .SD .x21 .x6 56,
        .LD .x6 .x25 32, .SD .x21 .x6 64, .LD .x6 .x25 40, .SD .x21 .x6 72,
        .LD .x6 .x25 48, .SD .x21 .x6 80, .LD .x6 .x25 56, .SD .x21 .x6 88,
        .ADDI .x10 .x21 0, .ADDI .x12 .x21 0] : List Instr).foldl execInstrBr state := rfl

private theorem cap_copy_register (state : MachineState) (count : Nat) (bounded : count ≤ 18)
    (reg : Reg) (not6 : reg ≠ .x6) (not10 : reg ≠ .x10) (not12 : reg ≠ .x12) :
    (capCopyPrefix state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [capCopyPrefix, capCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, register_set_mem,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not6),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not10),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not12)]

theorem check_cap_copy_register (state : MachineState) (reg : Reg)
    (not6 : reg ≠ .x6) (not10 : reg ≠ .x10) (not12 : reg ≠ .x12) :
    (checkCapCopyState state).getReg reg = state.getReg reg :=
  cap_copy_register state 18 (by decide) reg not6 not10 not12

theorem check_cap_copy_arguments (state : MachineState) (scratch : state.getReg .x21 = 256) :
    (checkCapCopyState state).getReg .x10 = 256 ∧ (checkCapCopyState state).getReg .x12 = 256 := by
  have x21 : (capCopyPrefix state 16).getReg .x21 = 256 :=
    (cap_copy_register state 16 (by decide) .x21 (by decide) (by decide) (by decide)).trans scratch
  have expand : checkCapCopyState state =
      ((((capCopyPrefix state 16).setReg .x10 ((capCopyPrefix state 16).getReg .x21 +
        signExtend12 0)).setPC ((capCopyPrefix state 16).pc + 4)).setReg .x12
          ((capCopyPrefix state 16).getReg .x21 + signExtend12 0)).setPC
            ((capCopyPrefix state 16).pc + 4 + 4) := rfl
  rw [expand]
  constructor
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10),
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), x21]
    rfl
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), x21]
    rfl

theorem check_cap_copy_pc (state : MachineState) :
    (checkCapCopyState state).pc = state.pc + 72 := by
  simp [checkCapCopyState, capCopyPrefix, capCopyInstructions, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

set_option maxHeartbeats 4000000 in
/-- Copy the next cap pair behind the chaining value and set both buffer pointers. -/
theorem check_cap_copy (state : MachineState) (pc : state.pc = 4208)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 8,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (18 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkCapCopyState state) allowCoins
          return result.charge 18 0) := by
  apply execute_unit_steps (states := capCopyPrefix state)
  intro i hi
  refine ⟨.base ((capCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (28 + i) _ (by omega)
    · interval_cases i <;>
        simp [capCopyPrefix, capCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · have sourceReg := cap_copy_register state i (by omega) .x25 (by decide) (by decide) (by decide)
    have scratchReg :=
      (cap_copy_register state i (by omega) .x21 (by decide) (by decide) (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have s4 := sourceValid ⟨4, by decide⟩
    have s5 := sourceValid ⟨5, by decide⟩
    have s6 := sourceValid ⟨6, by decide⟩
    have s7 := sourceValid ⟨7, by decide⟩
    have valid : memoryArgumentsValid (capCopyPrefix state i)
        ((capCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [capCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12]
      · exact s0
      · rfl
      · exact s1
      · rfl
      · exact s2
      · rfl
      · exact s3
      · rfl
      · exact s4
      · rfl
      · exact s5
      · rfl
      · exact s6
      · rfl
      · exact s7
      · rfl
    interval_cases i <;>
      simp only [capCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- The reply overwrites the chaining value in scratch. -/
def checkCapCallState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits state 256 answer

set_option maxHeartbeats 1600000 in
/-- The direct 96-byte call over scratch; the reply overwrites the chaining value. -/
theorem check_cap_call (state : MachineState) (pc : state.pc = 4280)
    (r5 : state.getReg .x5 = 0) (r10 : state.getReg .x10 = 256) (r11 : state.getReg .x11 = 96)
    (r12 : state.getReg .x12 = 256) (r13 : state.getReg .x13 = 0)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (1 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (leafQuery state)))
          let result ← execute (submission.image .check) fuel (checkCapCallState state answer) allowCoins
          return result.charge 8 1) := by
  have fetched : fetch (submission.image .check) state = some (.base .ECALL) := by
    apply check_fetch _ 46 _ (by decide) pc; rfl
  have input : oracleInput state = some (.inl (leafQuery state)) := by
    simp [oracleInput, r10, r11, r12, r13, COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH,
      rangeValid, MEMORY_BYTES]
    rw [r13]
    simp [leafQuery]
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos r5, input]
  simp only [writeOracleAnswer, r12, bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (leafQuery state)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  simp [oracleCycles, COMPRESSION_CYCLES, Execution.charge, checkCapCallState]
  rfl

/-- Advance to the next cap pair and count down; leave for the cap comparison at the end. -/
def checkCapNextState (state : MachineState) : MachineState :=
  ((state.setReg .x25 (state.getReg .x25 + 64)).setReg .x28 (state.getReg .x28 - 1)).setPC
    (if state.getReg .x28 - 1 = 0 then 4296 else 4208)

theorem check_cap_next (state : MachineState) (pc : state.pc = 4284)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkCapNextState state) allowCoins
          return result.charge 3 0) := by
  let advanced := (state.setReg .x25 (state.getReg .x25 + 64)).setPC 4288
  let next := (advanced.setReg .x28 (state.getReg .x28 - 1)).setPC 4292
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x25 .x25 64)) := by
    apply check_fetch _ 47 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) advanced = some (.base (.ADDI .x28 .x28 4095)) := by
    apply check_fetch _ 48 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .check) next = some (.base (.BNE .x28 .x0 8108)) := by
    apply check_fetch _ 49 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x25 .x25 64)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, advanced]
  have s1 : ordinaryStep advanced (.base (.ADDI .x28 .x28 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, next,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have s2 : ordinaryStep next (.base (.BNE .x28 .x0 8108)) = some (checkCapNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, next, checkCapNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- One cap iteration after a given reply. -/
def checkCapStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  checkCapNextState (checkCapCallState (checkCapCopyState state) answer)

theorem check_cap_step_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (not6 : reg ≠ .x6) (not10 : reg ≠ .x10) (not12 : reg ≠ .x12)
    (not25 : reg ≠ .x25) (not28 : reg ≠ .x28) :
    (checkCapStepState state answer).getReg reg = state.getReg reg := by
  simp only [checkCapStepState, checkCapNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not25), checkCapCallState, writeBits_register]
  exact check_cap_copy_register state reg not6 not10 not12

theorem check_cap_step_registers (state : MachineState) (answer : BitVec 256) :
    (checkCapStepState state answer).getReg .x25 = state.getReg .x25 + 64 ∧
    (checkCapStepState state answer).getReg .x28 = state.getReg .x28 - 1 := by
  simp only [checkCapStepState, checkCapNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x25), checkCapCallState,
    writeBits_register]
  rw [check_cap_copy_register state .x25 (by decide) (by decide) (by decide),
    check_cap_copy_register state .x28 (by decide) (by decide) (by decide)]
  exact ⟨rfl, rfl⟩

theorem check_cap_step_pc (state : MachineState) (answer : BitVec 256) :
    (checkCapStepState state answer).pc = if state.getReg .x28 - 1 = 0 then 4296 else 4208 := by
  change (if (checkCapCallState (checkCapCopyState state) answer).getReg .x28 - 1 = 0
    then 4296 else 4208) = _
  rw [checkCapCallState, writeBits_register, check_cap_copy_register state .x28 (by decide) (by decide) (by decide)]

theorem check_cap_iteration (state : MachineState) (pc : state.pc = 4208)
    (scratch : state.getReg .x21 = 256) (r5 : state.getReg .x5 = 0)
    (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (sourceValid : ∀ word : Fin 8,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (22 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (leafQuery (checkCapCopyState state))))
          let result ← execute (submission.image .check) fuel (checkCapStepState state answer) allowCoins
          return result.charge 29 1) := by
  let copied := checkCapCopyState state
  have copyPC : copied.pc = 4280 := by rw [check_cap_copy_pc, pc]; rfl
  have arguments := check_cap_copy_arguments state scratch
  have c5 : copied.getReg .x5 = 0 :=
    (check_cap_copy_register state .x5 (by decide) (by decide) (by decide)).trans r5
  have c11 : copied.getReg .x11 = 96 :=
    (check_cap_copy_register state .x11 (by decide) (by decide) (by decide)).trans r11
  have c13 : copied.getReg .x13 = 0 :=
    (check_cap_copy_register state .x13 (by decide) (by decide) (by decide)).trans r13
  have callPC (answer : BitVec 256) : (checkCapCallState copied answer).pc = 4284 := by
    simp only [checkCapCallState, writeBits, MachineState.setPC, copyPC]
    rfl
  rw [show 22 + fuel = 18 + (1 + (3 + fuel)) by omega, check_cap_copy state pc scratch sourceValid,
    check_cap_call copied copyPC c5 arguments.1 c11 arguments.2 c13]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (leafQuery copied)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  rw [check_cap_next _ (callPC answer)]
  simp [checkCapStepState, copied, Execution.charge, ← Nat.add_assoc]

/-- The cap chain loop, one exact query per pair. -/
def checkCapLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (leafQuery (checkCapCopyState state))))
      checkCapLoop (checkCapStepState state answer) count

theorem check_cap_loop (state : MachineState) (count : Nat) (bounded : count ≤ 64)
    (pc : 0 < count → state.pc = 4208) (counter : state.getReg .x28 = BitVec.ofNat 64 count)
    (scratch : state.getReg .x21 = 256) (r5 : state.getReg .x5 = 0)
    (r11 : state.getReg .x11 = 96) (r13 : state.getReg .x13 = 0)
    (sourceValid : ∀ word < 8 * count,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (22 * count + fuel) state allowCoins =
      (do let finished ← checkCapLoop state count
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge (29 * count) count) := by
  induction count generalizing state with
  | zero => simp [checkCapLoop, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 8) :
        accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have keep (answer : BitVec 256) (reg : Reg) (not6 : reg ≠ .x6) (not10 : reg ≠ .x10)
        (not12 : reg ≠ .x12) (not25 : reg ≠ .x25) (not28 : reg ≠ .x28) :=
      check_cap_step_register state answer reg not6 not10 not12 not25 not28
    have nextCounter (answer : BitVec 256) :
        (checkCapStepState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(check_cap_step_registers state answer).2, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have nextPC (answer : BitVec 256) (positive : 0 < count) :
        (checkCapStepState state answer).pc = 4208 := by
      rw [check_cap_step_pc]
      have nonzero : state.getReg .x28 - 1 ≠ 0 := by
        rw [← (check_cap_step_registers state answer).2, nextCounter]
        intro zero
        have := congrArg BitVec.toNat zero
        change count % 18446744073709551616 = 0 at this
        omega
      exact if_neg nonzero
    have nextValid (answer : BitVec 256) (word : Nat) (bound : word < 8 * count) :
        accessValid ((checkCapStepState state answer).getReg .x25 +
          BitVec.ofNat 64 (8 * word)) 8 = true := by
      have valid := sourceValid (word + 8) (by omega)
      rw [(check_cap_step_registers state answer).1]
      have address : state.getReg .x25 + 64 + BitVec.ofNat 64 (8 * word) =
          state.getReg .x25 + BitVec.ofNat 64 (8 * (word + 8)) := by
        rw [show 8 * (word + 8) = 64 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [address]
      exact valid
    rw [show 22 * (count + 1) + fuel = 22 + (22 * count + fuel) by omega,
      check_cap_iteration state (pc (by omega)) scratch r5 r11 r13 currentValid]
    simp only [checkCapLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl (leafQuery (checkCapCopyState state))))) :
        OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    rw [ih _ (by omega) (nextPC answer) (nextCounter answer)
      ((keep answer .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans scratch)
      ((keep answer .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans r5)
      ((keep answer .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans r11)
      ((keep answer .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans r13)
      (nextValid answer)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Every run of the loop consumes exactly 64 bytes per pair and preserves all other
registers except the copy and syscall pointers. A nonempty loop ends at the comparison. -/
theorem check_cap_loop_registers (state : MachineState) (count : Nat) (bounded : count ≤ 64)
    (counter : state.getReg .x28 = BitVec.ofNat 64 count) (finished : MachineState)
    (reachable : finished ∈ support (checkCapLoop state count)) :
    finished.getReg .x25 = state.getReg .x25 + BitVec.ofNat 64 (64 * count) ∧
    (0 < count → finished.pc = 4296) ∧
    ∀ reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x25 → reg ≠ .x28 →
      finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [checkCapLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨by simp, by omega, fun _ _ _ _ _ _ => rfl⟩
  | succ count ih =>
    simp only [checkCapLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have nextCounter : (checkCapStepState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(check_cap_step_registers state answer).2, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have rest := ih _ (by omega) nextCounter reached
    refine ⟨?_, ?_, ?_⟩
    · rw [rest.1, (check_cap_step_registers state answer).1]
      rw [show 64 * (count + 1) = 64 + 64 * count by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · intro _
      by_cases empty : count = 0
      · subst count
        simp only [checkCapLoop, support_pure, Set.mem_singleton_iff] at reached
        subst finished
        rw [check_cap_step_pc state answer, counter]
        rfl
      · exact rest.2.1 (by omega)
    · intro reg n6 n10 n12 n25 n28
      exact (rest.2.2 reg n6 n10 n12 n25 n28).trans
        (check_cap_step_register state answer reg n6 n10 n12 n25 n28)

/-- The whole cap block, from the cap entry to the commitment comparison: 1419
instructions, 1867 cycles, and exactly 64 public calls for every reply sequence. -/
theorem check_cap_phase (state : MachineState) (pc : state.pc = 4164)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 512,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (1419 + fuel) state allowCoins =
      (do let finished ← checkCapLoop (checkCapSetupState state) 64
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge 1867 64) := by
  have regs := check_cap_setup_registers state pc
  let ready := checkCapSetupState state
  have keep (reg : Reg) (not5 : reg ≠ .x5) (not11 : reg ≠ .x11) (not13 : reg ≠ .x13)
      (not28 : reg ≠ .x28) (not30 : reg ≠ .x30) :=
    check_cap_setup_register state reg not5 not11 not13 not28 not30
  have readyScratch : ready.getReg .x21 = 256 :=
    (keep .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans scratch
  have readySource : ∀ word < 8 * 64,
      accessValid (ready.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [keep .x25 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact sourceValid
  rw [show 1419 + fuel = 11 + (22 * 64 + fuel) by omega, check_cap_setup state pc scratch,
    check_cap_loop ready 64 (by decide) (fun _ => regs.1) regs.2.2.1 readyScratch regs.2.2.2.1
      regs.2.2.2.2.1 regs.2.2.2.2.2 readySource]
  simp [Execution.charge, ← Nat.add_assoc]
  rfl

theorem check_cap_phase_registers (state finished : MachineState) (pc : state.pc = 4164)
    (reachable : finished ∈ support (checkCapLoop (checkCapSetupState state) 64)) :
    finished.pc = 4296 ∧
    finished.getReg .x25 = state.getReg .x25 + 4096 ∧
    finished.getReg .x30 = state.getReg .x25 ∧
    ∀ reg, reg ∈ [Reg.x8, .x21, .x24, .x26, .x27] → finished.getReg reg = state.getReg reg := by
  have regs := check_cap_setup_registers state pc
  have loop := check_cap_loop_registers _ 64 (by decide) regs.2.2.1 finished reachable
  have keep (reg : Reg) (not5 : reg ≠ .x5) (not11 : reg ≠ .x11) (not13 : reg ≠ .x13)
      (not28 : reg ≠ .x28) (not30 : reg ≠ .x30) :=
    check_cap_setup_register state reg not5 not11 not13 not28 not30
  refine ⟨loop.2.1 (by decide), ?_, ?_, ?_⟩
  · rw [loop.1, keep .x25 (by decide) (by decide) (by decide) (by decide) (by decide)]
    rfl
  · rw [loop.2.2 .x30 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact regs.2.1
  · intro reg member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      exact (loop.2.2 _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        (keep _ (by decide) (by decide) (by decide) (by decide) (by decide))

end CommitGolfCandidate
