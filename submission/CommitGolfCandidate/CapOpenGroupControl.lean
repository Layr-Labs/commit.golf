import CommitGolfCandidate.CapOpenGroupEffect

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem branch_register (state : MachineState) (offset : BitVec 13)
    (reg : Reg) :
    (execInstrBr state (.BNE .x27 .x0 offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

private theorem store_register (state : MachineState) (address value : Word)
    (reg : Reg) : (state.setMem address value).getReg reg = state.getReg reg := by
  cases reg <;> rfl

theorem cap_open_group_projection (state : MachineState) :
    (capOpenGroupPrefix state 6).getReg .x24 = state.getReg .x24 + 8 ∧
    (capOpenGroupPrefix state 6).getReg .x27 = state.getReg .x27 - 1 := by
  have last (reg : Reg) : (capOpenGroupPrefix state 6).getReg reg =
      (capOpenGroupPrefix state 5).getReg reg := by
    rw [cap_open_group_succ state 5 (by decide)]
    exact branch_register _ _ reg
  rw [last .x24, last .x27]
  simp (disch := decide) only [capOpenGroupPrefix, capOpenGroupInstructions,
    List.take, List.foldl, execInstrBr, signExtend12,
    MachineState.getReg_setPC, store_register,
    MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne]
  constructor
  · rfl
  · rw [BitVec.sub_eq_add_neg]
    rfl

theorem cap_open_group_counter (state : MachineState) (remaining : Nat)
    (positive : 0 < remaining)
    (counter : state.getReg .x27 = BitVec.ofNat 64 remaining) :
    (capOpenGroupPrefix state 6).getReg .x27 =
      BitVec.ofNat 64 (remaining-1) := by
  rw [(cap_open_group_projection state).2, counter]
  exact BitVec.ofNat_sub_ofNat_of_le remaining 1 (by decide) (by omega)

theorem cap_open_group_exit (state : MachineState) (remaining : Nat)
    (pc : state.pc = 4340) (positive : 0 < remaining)
    (bounded : remaining < 2^64)
    (counter : state.getReg .x27 = BitVec.ofNat 64 remaining) :
    (capOpenGroupPrefix state 6).pc = if remaining = 1 then 4364 else 4212 := by
  have earlyPC : (capOpenGroupPrefix state 5).pc = 4360 := by
    rw [cap_open_group_pc state 5 (by decide), pc]
    rfl
  have earlyCount : (capOpenGroupPrefix state 5).getReg .x27 =
      BitVec.ofNat 64 (remaining-1) := by
    have final := cap_open_group_counter state remaining positive counter
    rw [cap_open_group_succ state 5 (by decide)] at final
    change (execInstrBr (capOpenGroupPrefix state 5) (.BNE .x27 .x0 8044)).getReg .x27 =
      BitVec.ofNat 64 (remaining-1) at final
    rw [branch_register] at final
    exact final
  have zero : (BitVec.ofNat 64 (remaining-1) = (0 : Word)) ↔ remaining = 1 := by
    constructor
    · intro equal
      have value := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : remaining-1 < 2^64)] at value
      change remaining-1 = 0 at value
      omega
    · intro one
      subst remaining
      rfl
  rw [cap_open_group_succ state 5 (by decide)]
  change (execInstrBr (capOpenGroupPrefix state 5) (.BNE .x27 .x0 8044)).pc = _
  simp only [execInstrBr, earlyPC, earlyCount,
    show (capOpenGroupPrefix state 5).getReg .x0 = 0 from rfl]
  by_cases last : remaining = 1
  · subst remaining
    simp only [Nat.sub_self, show BitVec.ofNat 64 0 = (0 : Word) by rfl,
      bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, MachineState.setPC]
    rfl
  · have nonzero : BitVec.ofNat 64 (remaining-1) ≠ 0 :=
      fun equal => last (zero.mp equal)
    rw [ite_eq_left (bne_iff_ne.mpr nonzero)]
    simp only [MachineState.setPC, last, ite_false]
    decide

end CommitGolfCandidate
