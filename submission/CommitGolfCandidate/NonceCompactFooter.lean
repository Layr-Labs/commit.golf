import CommitGolfCandidate.NonceCompactExit

/-! The actual footer setup computes the remaining word count from the saved
old proof end, then branches around the copy if no footer words remain. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceCompactFooterInstructions : List Instr :=
  [.SUB .x28 .x22 .x23, .SRLI .x28 .x28 3, .BEQ .x28 .x0 8]

def nonceCompactFooterPrefix (state : MachineState) (count : Nat) : MachineState :=
  (nonceCompactFooterInstructions.take count).foldl execInstrBr state

theorem nonce_compact_footer_execute (state : MachineState) (pc : state.pc=5112)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (3+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceCompactFooterPrefix state 3) coins
          return result.charge 3 0) := by
  apply execute_unit_steps (states := nonceCompactFooterPrefix state)
  intro count bounded
  refine ⟨.base ((nonceCompactFooterInstructions[count]?).getD .EBREAK),?_,?_,?_⟩
  · apply cap_image_fetch _ _ (254+count) _ (by omega)
    · interval_cases count <;>
        simp [nonceCompactFooterPrefix, nonceCompactFooterInstructions, execInstrBr,
          MachineState.setPC, pc]
    · interval_cases count <;> rfl
  · interval_cases count <;> rfl
  · interval_cases count <;> rfl

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BEQ .x28 .x0 offset)).mem=state.mem := by
  simp only [execInstrBr]
  split <;> rfl

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BEQ .x28 .x0 offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem nonce_compact_footer_memory (state : MachineState) :
    (nonceCompactFooterPrefix state 3).mem=state.mem := by
  change (execInstrBr (nonceCompactFooterPrefix state 2) (.BEQ .x28 .x0 8)).mem=_
  rw [branch_memory]
  rfl

theorem nonce_compact_footer_register (state : MachineState) (reg : Reg) (outside : reg ≠ .x28) :
    (nonceCompactFooterPrefix state 3).getReg reg=state.getReg reg := by
  change (execInstrBr (nonceCompactFooterPrefix state 2) (.BEQ .x28 .x0 8)).getReg reg=_
  rw [branch_register]
  simp only [nonceCompactFooterPrefix, nonceCompactFooterInstructions, List.take,
    List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem nonce_compact_footer_counter (state : MachineState) (source words : Nat)
    (start : state.getReg .x23=BitVec.ofNat 64 source)
    (finish : state.getReg .x22=BitVec.ofNat 64 (source+8*words))
    (small : source+8*words<2^64) :
    (nonceCompactFooterPrefix state 3).getReg .x28=BitVec.ofNat 64 words := by
  change (execInstrBr (nonceCompactFooterPrefix state 2) (.BEQ .x28 .x0 8)).getReg .x28=_
  rw [branch_register]
  have raw : (nonceCompactFooterPrefix state 2).getReg .x28=
      (state.getReg .x22-state.getReg .x23) >>> 3 := by
    simp [nonceCompactFooterPrefix, nonceCompactFooterInstructions, execInstrBr,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  rw [raw, finish, start, BitVec.ofNat_add, BitVec.add_comm, BitVec.add_sub_cancel]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  change (8*words)%2^64/8=words%2^64
  rw [Nat.mod_eq_of_lt (by omega : 8*words<2^64),
    Nat.mod_eq_of_lt (by omega : words<2^64)]
  omega

end CommitGolfCandidate
