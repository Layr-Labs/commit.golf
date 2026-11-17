import CommitGolfCandidate.CapCheckGroupStart

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capCheckRecordNextInstructions : List Instr :=
  [.ADDI .x24 .x24 8, .ADDI .x27 .x27 4095, .BNE .x27 .x0 7860]

def capCheckRecordNextPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capCheckRecordNextInstructions.take count).foldl execInstrBr state


theorem cap_check_record_next_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 2) :
    (capCheckRecordNextPrefix state count).pc = state.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp only [capCheckRecordNextPrefix, capCheckRecordNextInstructions,
      List.take, List.foldl, execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl


private theorem next_prefix (state : MachineState) (i : Nat) (bounded : i < 3) :
    capCheckRecordNextPrefix state (i+1) =
      execInstrBr (capCheckRecordNextPrefix state i)
        ((capCheckRecordNextInstructions[i]?).getD .EBREAK) := by
  have inside : i < capCheckRecordNextInstructions.length := bounded
  unfold capCheckRecordNextPrefix
  rw [List.take_succ_eq_append_getElem inside,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,
    getElem?_pos capCheckRecordNextInstructions i inside,Option.getD_some]

private theorem next_step (current : MachineState) (i : Nat) (bounded : i < 3) :
    ordinaryStep current (.base ((capCheckRecordNextInstructions[i]?).getD .EBREAK)) =
      some (execInstrBr current ((capCheckRecordNextInstructions[i]?).getD .EBREAK)) := by
  interval_cases i <;> rfl


attribute [local irreducible] execute

theorem cap_check_record_next_execute (state : MachineState)
    (pc : state.pc = 4536) (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .check) (3+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .check) fuel
            (capCheckRecordNextPrefix state 3) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := capCheckRecordNextPrefix state)
  intro i bounded
  refine ⟨.base ((capCheckRecordNextInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (110+i) _ (by omega)
    · rw [cap_check_record_next_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · rw [next_prefix state i bounded]
    exact next_step _ i bounded
  · interval_cases i <;> rfl


private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE .x27 .x0 offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x27 .x0 offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> simp only [MachineState.setPC]

theorem cap_check_record_next_memory (state : MachineState) :
    (capCheckRecordNextPrefix state 3).mem = state.mem := by
  rw [next_prefix state 2 (by decide)]
  simp only [capCheckRecordNextInstructions,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  rw [branch_memory]
  simp only [capCheckRecordNextPrefix,capCheckRecordNextInstructions,
    List.take,List.foldl,execInstrBr,MachineState.setPC,MachineState.setReg]

theorem cap_check_record_next_register (state : MachineState) (reg : Reg)
    (outside24 : reg ≠ .x24) (outside27 : reg ≠ .x27) :
    (capCheckRecordNextPrefix state 3).getReg reg = state.getReg reg := by
  rw [next_prefix state 2 (by decide)]
  simp only [capCheckRecordNextInstructions,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  rw [branch_register]
  simp only [capCheckRecordNextPrefix, capCheckRecordNextInstructions,
    List.take, List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside24),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside27)]

theorem cap_check_record_next_projection (state : MachineState) :
    (capCheckRecordNextPrefix state 3).getReg .x24 = state.getReg .x24+8 ∧
    (capCheckRecordNextPrefix state 3).getReg .x27 = state.getReg .x27-1 := by
  have last (reg : Reg) : (capCheckRecordNextPrefix state 3).getReg reg =
      (capCheckRecordNextPrefix state 2).getReg reg := by
    rw [next_prefix state 2 (by decide)]
    simp only [capCheckRecordNextInstructions,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some]
    exact branch_register _ _ reg
  rw [last .x24,last .x27]
  simp only [capCheckRecordNextPrefix, capCheckRecordNextInstructions, List.take,
    List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, signExtend12]
  constructor
  · rfl
  · rw [BitVec.sub_eq_add_neg]
    rfl


theorem cap_check_record_next_counter (state : MachineState) (remaining : Nat)
    (positive : 0 < remaining)
    (counter : state.getReg .x27 = BitVec.ofNat 64 remaining) :
    (capCheckRecordNextPrefix state 3).getReg .x27 = BitVec.ofNat 64 (remaining-1) := by
  rw [(cap_check_record_next_projection state).2,counter]
  exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by omega)

theorem cap_check_record_next_exit (state : MachineState) (remaining : Nat)
    (pc : state.pc = 4536) (positive : 0 < remaining) (bounded : remaining < 2^64)
    (counter : state.getReg .x27 = BitVec.ofNat 64 remaining) :
    (capCheckRecordNextPrefix state 3).pc = if remaining=1 then 4548 else 4212 := by
  have earlyPC : (capCheckRecordNextPrefix state 2).pc = 4544 := by
    rw [cap_check_record_next_pc state 2 (by decide),pc]
    rfl
  have earlyCounter : (capCheckRecordNextPrefix state 2).getReg .x27 =
      BitVec.ofNat 64 (remaining-1) := by
    have result := cap_check_record_next_counter state remaining positive counter
    rw [next_prefix state 2 (by decide)] at result
    simp only [capCheckRecordNextInstructions,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some] at result
    rw [branch_register] at result
    exact result
  have zero : (BitVec.ofNat 64 (remaining-1)=(0:Word)) ↔ remaining=1 := by
    constructor
    · intro equal
      have natural := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : remaining-1<2^64)] at natural
      change remaining-1=0 at natural
      omega
    · intro one
      subst remaining
      rfl
  rw [next_prefix state 2 (by decide)]
  simp only [capCheckRecordNextInstructions,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some]
  simp only [execInstrBr,earlyPC,earlyCounter,
    show (capCheckRecordNextPrefix state 2).getReg .x0=0 from rfl]
  by_cases last : remaining=1
  · subst remaining
    simp only [Nat.sub_self, show BitVec.ofNat 64 0=(0:Word) by rfl,
      bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, MachineState.setPC]
    rfl
  · have nonzero : BitVec.ofNat 64 (remaining-1) ≠ 0 :=
      fun equal => last (zero.mp equal)
    rw [ite_eq_left (bne_iff_ne.mpr nonzero)]
    simp only [MachineState.setPC,last,ite_false]
    decide

end CommitGolfCandidate
