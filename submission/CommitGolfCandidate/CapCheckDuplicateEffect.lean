import CommitGolfCandidate.CapCheckDuplicateWord

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def CapCheckDuplicateEqual (state : MachineState) (word : Nat) : Prop :=
  state.getMem (state.getReg .x21 + signExtend12 (BitVec.ofNat 12 (8*word))) =
    state.getMem (state.getReg .x23 + signExtend12 (BitVec.ofNat 12 (8*word)))

instance (state : MachineState) (word : Nat) :
    Decidable (CapCheckDuplicateEqual state word) :=
  inferInstanceAs (Decidable (_ = _))

private theorem bne_register (current : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr current (.BNE .x6 .x7 offset)).getReg reg = current.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem cap_check_duplicate_register (state : MachineState) (word : Nat) (reg : Reg)
    (outside6 : reg ≠ .x6) (outside7 : reg ≠ .x7) :
    (capCheckDuplicatePrefix state word 3).getReg reg = state.getReg reg := by
  change (execInstrBr (capCheckDuplicatePrefix state word 2)
    (.BNE .x6 .x7 (BitVec.ofNat 13 (352-12*word)))).getReg reg = _
  rw [bne_register]
  exact cap_check_duplicate_prefix_register state word 2 (by decide) reg outside6 outside7

theorem cap_check_duplicate_loaded (state : MachineState) (word : Nat) :
    (capCheckDuplicatePrefix state word 2).getReg .x6 =
      state.getMem (state.getReg .x21 + signExtend12 (BitVec.ofNat 12 (8*word))) ∧
    (capCheckDuplicatePrefix state word 2).getReg .x7 =
      state.getMem (state.getReg .x23 + signExtend12 (BitVec.ofNat 12 (8*word))) := by
  simp only [capCheckDuplicatePrefix, capCheckDuplicateInstructions, List.take,
    List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setPC, MachineState.getMem_setReg]
  exact ⟨rfl,rfl⟩

theorem cap_check_duplicate_exit (state : MachineState) (word : Nat)
    (bounded : word < 4) (pc : state.pc = BitVec.ofNat 64 (4448+12*word)) :
    (capCheckDuplicatePrefix state word 3).pc =
      if CapCheckDuplicateEqual state word then BitVec.ofNat 64 (4460+12*word)
      else 4808 := by
  have loaded := cap_check_duplicate_loaded state word
  have atBranch := cap_check_duplicate_prefix_pc state word 2 (by decide)
  change (execInstrBr (capCheckDuplicatePrefix state word 2)
    (.BNE .x6 .x7 (BitVec.ofNat 13 (352-12*word)))).pc = _
  simp only [execInstrBr, loaded.1, loaded.2, MachineState.setPC, atBranch, pc]
  by_cases equal : CapCheckDuplicateEqual state word
  · rw [if_pos equal]
    unfold CapCheckDuplicateEqual at equal
    simp only [equal, bne_self_eq_false, ↓reduceIte]
    interval_cases word <;> rfl
  · rw [if_neg equal]
    unfold CapCheckDuplicateEqual at equal
    have different : (state.getMem (state.getReg .x21 +
        signExtend12 (BitVec.ofNat 12 (8*word))) !=
        state.getMem (state.getReg .x23 +
        signExtend12 (BitVec.ofNat 12 (8*word)))) = true := by
      exact bne_iff_ne.mpr equal
    simp only [different, ↓reduceIte]
    interval_cases word <;> rfl

end CommitGolfCandidate
