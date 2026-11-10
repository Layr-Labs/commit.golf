import CommitGolfCandidate.CapCheckProofEnd

/-! Each final commitment comparison consists of two admitted loads and
one branch. It reads cap root slot 1 from x18+32 and the claimed commitment
from x26. A mismatch reaches the actual failure epilogue before later loads.
The ordinary three-instruction bridge specializes the earlier duplicate-word
method to these distinct registers, offsets and final image sites. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckRootInstructions (word : Nat) : List Instr :=
  [.LD .x6 .x18 (BitVec.ofNat 12 (32+8*word)),
   .LD .x7 .x26 (BitVec.ofNat 12 (8*word)),
   .BNE .x6 .x7 (BitVec.ofNat 13 (60-12*word))]

def capCheckRootPrefix (state : MachineState) (word count : Nat) : MachineState :=
  ((capCheckRootInstructions word).take count).foldl execInstrBr state

theorem cap_check_root_prefix_pc (state : MachineState) (word count : Nat)
    (bounded : count ≤ 2) :
    (capCheckRootPrefix state word count).pc =
      state.pc + BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp only [capCheckRootPrefix, capCheckRootInstructions,
      List.take, List.foldl, execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_check_root_prefix_register (state : MachineState) (word count : Nat)
    (bounded : count ≤ 2) (reg : Reg) (outside6 : reg ≠ .x6)
    (outside7 : reg ≠ .x7) :
    (capCheckRootPrefix state word count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [capCheckRootPrefix, capCheckRootInstructions,
      List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside6),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside7)]

theorem cap_check_root_execute (state : MachineState) (word : Nat)
    (bounded : word < 4) (pc : state.pc = BitVec.ofNat 64 (4740+12*word))
    (scratchValid : accessValid
      (state.getReg .x18 + signExtend12 (BitVec.ofNat 12 (32+8*word))) 8 = true)
    (rootValid : accessValid
      (state.getReg .x26 + signExtend12 (BitVec.ofNat 12 (8*word))) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (3+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckRootPrefix state word 3) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := capCheckRootPrefix state word)
  intro i inside
  refine ⟨.base (((capCheckRootInstructions word)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (161+3*word+i) _ (by omega)
    · rw [cap_check_root_prefix_pc state word i (by omega), pc]
      interval_cases word <;> interval_cases i <;> rfl
    · interval_cases word <;> interval_cases i <;> rfl
  · have scratch := cap_check_root_prefix_register state word i (by omega)
      .x18 (by decide) (by decide)
    have root := cap_check_root_prefix_register state word i (by omega)
      .x26 (by decide) (by decide)
    interval_cases i
    · simp only [capCheckRootInstructions, List.getElem?_cons_zero,
        Option.getD_some, ordinaryStep, memoryArgumentsValid, memAccess, scratch,
        scratchValid, ↓reduceIte]
      rfl
    · simp only [capCheckRootInstructions, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, ordinaryStep,
        memoryArgumentsValid, memAccess, root, rootValid, ↓reduceIte]
      rfl
    · rfl
  · interval_cases i <;> rfl

theorem cap_check_root_memory (state : MachineState) (word : Nat) :
    (capCheckRootPrefix state word 3).mem = state.mem := by
  have branchMemory (current : MachineState) (offset : BitVec 13) :
      (execInstrBr current (.BNE .x6 .x7 offset)).mem = current.mem := by
    simp only [execInstrBr]
    split <;> rfl
  change (execInstrBr (capCheckRootPrefix state word 2)
    (.BNE .x6 .x7 (BitVec.ofNat 13 (60-12*word)))).mem = _
  rw [branchMemory]
  rfl

end CommitGolfCandidate
