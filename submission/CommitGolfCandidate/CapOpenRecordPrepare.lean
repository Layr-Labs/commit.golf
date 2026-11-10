import CommitGolfCandidate.CapDigestCopy

/-! Actual opening record entry: read one requested index, select its retained
salt and enter the eight-instruction salt copy. Sorted-position/value meaning
comes from the loader byte frame, not from this checked instruction macro. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def capOpenRecordInstructions : List Instr :=
  [.LD .x20 .x24 0, .SLLI .x6 .x20 5, .ADD .x23 .x18 .x6]
def capOpenRecordPrefix (state : MachineState) (count : Nat) : MachineState :=
  (capOpenRecordInstructions.take count).foldl execInstrBr state

private theorem add_zero_word (word : Word) : word + (0 : Word) = word :=
  BitVec.add_zero word

theorem cap_open_record_prepare_succ (state : MachineState) (count : Nat)
    (bounded : count < 3) :
    capOpenRecordPrefix state (count+1) =
      execInstrBr (capOpenRecordPrefix state count)
        ((capOpenRecordInstructions[count]?).getD .EBREAK) := by
  interval_cases count <;> rfl

theorem cap_open_record_prepare_pc (state : MachineState) (count : Nat)
    (bounded : count ≤ 3) :
    (capOpenRecordPrefix state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp only [capOpenRecordPrefix, capOpenRecordInstructions, List.take, List.foldl,
      execInstrBr, MachineState.setPC, BitVec.add_assoc]
  · simp
  all_goals rfl

theorem cap_open_record_prepare_memory (state : MachineState) (count : Nat)
    (bounded : count ≤ 3) : (capOpenRecordPrefix state count).mem = state.mem := by
  interval_cases count <;> rfl

theorem cap_open_record_prepare_register (state : MachineState) (count : Nat)
    (bounded : count ≤ 3) (reg : Reg)
    (outside : reg ≠ .x20 ∧ reg ≠ .x6 ∧ reg ≠ .x23) :
    (capOpenRecordPrefix state count).getReg reg = state.getReg reg := by
  interval_cases count <;>
    simp only [capOpenRecordPrefix, capOpenRecordInstructions, List.take, List.foldl,
      execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2)]

theorem cap_open_record_index (state : MachineState) :
    (capOpenRecordPrefix state 3).getReg .x20 = state.getMem (state.getReg .x24) := by
  simp (disch := decide) only [capOpenRecordPrefix, capOpenRecordInstructions,
    List.take, List.foldl, execInstrBr, signExtend12,
    show BitVec.signExtend 64 (0 : BitVec 12) = (0 : Word) by decide,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    add_zero_word]

theorem cap_open_record_salt_address (state : MachineState) (position saltBase : Nat)
    (loaded : state.getMem (state.getReg .x24) = BitVec.ofNat 64 position)
    (salts : state.getReg .x18 = BitVec.ofNat 64 saltBase) :
    (capOpenRecordPrefix state 3).getReg .x23 =
      BitVec.ofNat 64 (saltBase + 32*position) := by
  simp (disch := decide) only [capOpenRecordPrefix, capOpenRecordInstructions,
    List.take, List.foldl, execInstrBr, signExtend12,
    show BitVec.signExtend 64 (0 : BitVec 12) = (0 : Word) by decide,
    MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    add_zero_word, loaded, salts, show (5 : BitVec 6).toNat = 5 by decide]
  rw [BitVec.shiftLeft_eq_mul_twoPow,
    show BitVec.twoPow 64 5 = BitVec.ofNat 64 32 by decide,
    ← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm position 32]

theorem cap_open_record_prepare_execute (state : MachineState)
    (pc : state.pc = 4212) (valid : accessValid (state.getReg .x24) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute ((capExperimental 24).image .opening) (3+fuel) state allowCoins =
      (do let result ← execute ((capExperimental 24).image .opening) fuel
            (capOpenRecordPrefix state 3) allowCoins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := capOpenRecordPrefix state)
  intro i bounded
  refine ⟨.base ((capOpenRecordInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply cap_image_fetch _ _ (29+i) _ (by omega)
    · rw [cap_open_record_prepare_pc state i (by omega), pc]
      interval_cases i <;> rfl
    · interval_cases i <;> rfl
  · rw [cap_open_record_prepare_succ state i bounded]
    interval_cases i <;>
      simp only [capOpenRecordInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some, ordinaryStep,
        memoryArgumentsValid, memAccess, capOpenRecordPrefix, List.take_zero,
        List.foldl_nil, signExtend12,
        show BitVec.signExtend 64 (0 : BitVec 12) = (0 : Word) by decide,
        add_zero_word, valid, ↓reduceIte]
  · interval_cases i <;> rfl

theorem cap_open_record_salt_copy_fetched :
    CapDigestCopyFetched ((capExperimental 24).image .opening) false 4224 := by
  intro state i bounded pc
  apply cap_image_fetch _ _ (32+i) _ (by omega)
  · rw [cap_copy_prefix_pc false state i (by omega), pc]
    interval_cases i <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate
