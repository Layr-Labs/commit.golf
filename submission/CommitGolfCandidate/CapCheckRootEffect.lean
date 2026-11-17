import CommitGolfCandidate.CapCheckRootWord

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

def CapCheckRootEqual (state : MachineState) (word : Nat) : Prop :=
  state.getMem (state.getReg .x18 + signExtend12 (BitVec.ofNat 12 (32+8*word))) =
    state.getMem (state.getReg .x26 + signExtend12 (BitVec.ofNat 12 (8*word)))

instance (state : MachineState) (word : Nat) :
    Decidable (CapCheckRootEqual state word) :=
  inferInstanceAs (Decidable (_ = _))

private theorem bne_register (current : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr current (.BNE .x6 .x7 offset)).getReg reg = current.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem cap_check_root_register (state : MachineState) (word : Nat) (reg : Reg)
    (outside6 : reg ≠ .x6) (outside7 : reg ≠ .x7) :
    (capCheckRootPrefix state word 3).getReg reg = state.getReg reg := by
  change (execInstrBr (capCheckRootPrefix state word 2)
    (.BNE .x6 .x7 (BitVec.ofNat 13 (60-12*word)))).getReg reg = _
  rw [bne_register]
  exact cap_check_root_prefix_register state word 2 (by decide) reg outside6 outside7

theorem cap_check_root_loaded (state : MachineState) (word : Nat) :
    (capCheckRootPrefix state word 2).getReg .x6 =
      state.getMem (state.getReg .x18 + signExtend12 (BitVec.ofNat 12 (32+8*word))) ∧
    (capCheckRootPrefix state word 2).getReg .x7 =
      state.getMem (state.getReg .x26 + signExtend12 (BitVec.ofNat 12 (8*word))) := by
  simp only [capCheckRootPrefix, capCheckRootInstructions, List.take,
    List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
    MachineState.getMem_setPC, MachineState.getMem_setReg]
  exact ⟨rfl,rfl⟩

theorem cap_check_root_exit (state : MachineState) (word : Nat)
    (bounded : word < 4) (pc : state.pc = BitVec.ofNat 64 (4740+12*word)) :
    (capCheckRootPrefix state word 3).pc =
      if CapCheckRootEqual state word then BitVec.ofNat 64 (4752+12*word)
      else 4808 := by
  have loaded := cap_check_root_loaded state word
  have atBranch := cap_check_root_prefix_pc state word 2 (by decide)
  change (execInstrBr (capCheckRootPrefix state word 2)
    (.BNE .x6 .x7 (BitVec.ofNat 13 (60-12*word)))).pc = _
  simp only [execInstrBr, loaded.1, loaded.2, MachineState.setPC, atBranch, pc]
  by_cases equal : CapCheckRootEqual state word
  · rw [if_pos equal]
    unfold CapCheckRootEqual at equal
    simp only [equal, bne_self_eq_false, ↓reduceIte]
    interval_cases word <;> rfl
  · rw [if_neg equal]
    unfold CapCheckRootEqual at equal
    have different : (state.getMem (state.getReg .x18 +
        signExtend12 (BitVec.ofNat 12 (32+8*word))) !=
        state.getMem (state.getReg .x26 +
        signExtend12 (BitVec.ofNat 12 (8*word)))) = true := by
      exact bne_iff_ne.mpr equal
    simp only [different, ↓reduceIte]
    interval_cases word <;> rfl

end CommitGolfCandidate
