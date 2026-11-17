import CommitGolfCandidate.CapCheckGroupStart
import CommitGolfCandidate.CapCheckExit

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckDuplicateInstructions (word : Nat) : List Instr :=
  [.LD .x6 .x21 (BitVec.ofNat 12 (8*word)),
   .LD .x7 .x23 (BitVec.ofNat 12 (8*word)),
   .BNE .x6 .x7 (BitVec.ofNat 13 (352-12*word))]

def capCheckDuplicatePrefix (state : MachineState) (word count : Nat) : MachineState :=
  ((capCheckDuplicateInstructions word).take count).foldl execInstrBr state

theorem cap_check_duplicate_prefix_pc (state : MachineState) (word count : Nat)
    (bounded : count ≤ 2) :
    (capCheckDuplicatePrefix state word count).pc =
      state.pc + BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp only [capCheckDuplicatePrefix, capCheckDuplicateInstructions,
      List.take, List.foldl, execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_check_duplicate_prefix_register (state : MachineState) (word count : Nat)
    (bounded : count ≤ 2) (reg : Reg) (outside6 : reg ≠ .x6)
    (outside7 : reg ≠ .x7) :
    (capCheckDuplicatePrefix state word count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [capCheckDuplicatePrefix, capCheckDuplicateInstructions,
      List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside6),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside7)]

theorem cap_check_duplicate_execute (state : MachineState) (word : Nat)
    (bounded : word < 4) (pc : state.pc = BitVec.ofNat 64 (4448+12*word))
    (scratchValid : accessValid
      (state.getReg .x21 + signExtend12 (BitVec.ofNat 12 (8*word))) 8 = true)
    (rootValid : accessValid
      (state.getReg .x23 + signExtend12 (BitVec.ofNat 12 (8*word))) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (3+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckDuplicatePrefix state word 3) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := capCheckDuplicatePrefix state word)
  intro i inside
  refine ⟨.base (((capCheckDuplicateInstructions word)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (88+3*word+i) _ (by omega)
    · rw [cap_check_duplicate_prefix_pc state word i (by omega), pc]
      interval_cases word <;> interval_cases i <;> rfl
    · interval_cases word <;> interval_cases i <;> rfl
  · have scratch := cap_check_duplicate_prefix_register state word i (by omega)
      .x21 (by decide) (by decide)
    have root := cap_check_duplicate_prefix_register state word i (by omega)
      .x23 (by decide) (by decide)
    interval_cases i
    · simp only [capCheckDuplicateInstructions, List.getElem?_cons_zero,
        Option.getD_some, ordinaryStep, memoryArgumentsValid, memAccess, scratch,
        scratchValid, ↓reduceIte]
      rfl
    · simp only [capCheckDuplicateInstructions, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, ordinaryStep,
        memoryArgumentsValid, memAccess, root, rootValid, ↓reduceIte]
      rfl
    · rfl
  · interval_cases i <;> rfl

theorem cap_check_duplicate_memory (state : MachineState) (word : Nat) :
    (capCheckDuplicatePrefix state word 3).mem = state.mem := by
  have branchMemory (current : MachineState) (offset : BitVec 13) :
      (execInstrBr current (.BNE .x6 .x7 offset)).mem = current.mem := by
    simp only [execInstrBr]
    split <;> rfl
  change (execInstrBr (capCheckDuplicatePrefix state word 2)
    (.BNE .x6 .x7 (BitVec.ofNat 13 (352-12*word)))).mem = _
  rw [branchMemory]
  rfl

end CommitGolfCandidate
