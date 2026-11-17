import CommitGolfCandidate.NonceCompactFooter
import CommitGolfCandidate.NonceCompactRecord

/-! The footer branch selects its true finish or a real call to the shared
copy routine, whose link points directly to the compacting success epilogue. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BEQ .x28 .x0 offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem nonce_compact_footer_pc (state : MachineState) (pc : state.pc=5112)
    (source words : Nat) (start : state.getReg .x23=BitVec.ofNat 64 source)
    (finish : state.getReg .x22=BitVec.ofNat 64 (source+8*words))
    (small : source+8*words<2^64) :
    (nonceCompactFooterPrefix state 3).pc=if words=0 then 5128 else 5124 := by
  have counter:=nonce_compact_footer_counter state source words start finish small
  change (execInstrBr (nonceCompactFooterPrefix state 2) (.BEQ .x28 .x0 8)).getReg .x28=_ at counter
  rw [branch_register] at counter
  have prefixPc : (nonceCompactFooterPrefix state 2).pc=5120 := by
    simp [nonceCompactFooterPrefix, nonceCompactFooterInstructions, execInstrBr,
      MachineState.setPC, pc]
  have zero : (BitVec.ofNat 64 words : Word)=0 ↔ words=0 := by
    constructor
    · intro equal
      have numeric:=congrArg BitVec.toNat equal
      change words%2^64=0 at numeric
      rw [Nat.mod_eq_of_lt (by omega)] at numeric
      exact numeric
    · rintro rfl
      rfl
  change (execInstrBr (nonceCompactFooterPrefix state 2) (.BEQ .x28 .x0 8)).pc=_
  simp only [execInstrBr, counter,
    show (nonceCompactFooterPrefix state 2).getReg .x0=0 from rfl, beq_iff_eq, zero]
  by_cases empty : words=0 <;> simp [empty, MachineState.setPC, prefixPc, signExtend13]

def nonceCompactFooterCall (state : MachineState) : MachineState :=
  execInstrBr state (.JAL .x1 20)

theorem nonce_compact_footer_call_execute (state : MachineState) (pc : state.pc=5124)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (1+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceCompactFooterCall state) coins
          return result.charge 1 0) := by
  have fetched : fetch nonceCompactImage state=some (.base (.JAL .x1 20)) := by
    apply cap_image_fetch _ state 257 _ (by decide) pc
    rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step nonceCompactImage _ state
    (nonceCompactFooterCall state) fuel coins fetched (by rfl)]
  rfl

theorem nonce_compact_footer_call_memory (state : MachineState) :
    (nonceCompactFooterCall state).mem=state.mem := rfl

theorem nonce_compact_footer_call_register (state : MachineState) (reg : Reg) (outside : reg ≠ .x1) :
    (nonceCompactFooterCall state).getReg reg=state.getReg reg := by
  simp only [nonceCompactFooterCall, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem nonce_compact_footer_call_pc (state : MachineState) (pc : state.pc=5124) :
    (nonceCompactFooterCall state).pc=5144 ∧ (nonceCompactFooterCall state).getReg .x1=5128 := by
  simp [nonceCompactFooterCall, execInstrBr, MachineState.setPC, MachineState.getReg,
    MachineState.setReg, signExtend21, pc]

theorem nonce_compact_footer_return_pc (state : MachineState) (pc : state.pc=5124) (words : Nat) :
    (nonceCopyReturned (nonceCompactFooterCall state) words).pc=5128 := by
  have link:=(nonce_compact_footer_call_pc state pc).2
  rw [nonceCopyReturned, NonceCopyProcedure.loop_return_pc]
  · exact link
  · rw [link]
    decide

end CommitGolfCandidate
