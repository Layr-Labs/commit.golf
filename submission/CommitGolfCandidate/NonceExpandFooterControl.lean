import CommitGolfCandidate.NonceExpandSetup

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceExpandGuardState (state : MachineState) : MachineState :=
  execInstrBr state (.BEQ .x24 .x0 36)

theorem nonce_expand_guard_execute (state : MachineState) (pc : state.pc=5012)
    (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (1+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel (nonceExpandGuardState state) coins
          return result.charge 1 0) := by
  have fetched : fetch nonceExpandedImage state=some (.base (.BEQ .x24 .x0 36)) := by
    apply cap_image_fetch _ state 229 _ (by decide) pc
    rfl
  rw [Nat.add_comm 1 fuel, execute_ordinary_step nonceExpandedImage _ state
    (nonceExpandGuardState state) fuel coins fetched (by rfl)]
  rfl

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BEQ .x24 .x0 offset)).mem=state.mem := by
  simp only [execInstrBr]
  split <;> rfl

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BEQ .x24 .x0 offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem nonce_expand_guard_memory (state : MachineState) :
    (nonceExpandGuardState state).mem=state.mem := branch_memory state 36

theorem nonce_expand_guard_register (state : MachineState) (reg : Reg) :
    (nonceExpandGuardState state).getReg reg=state.getReg reg := branch_register state 36 reg

theorem nonce_expand_guard_pc (state : MachineState) (pc : state.pc=5012)
    (count : Nat) (small : count<2^64)
    (counter : state.getReg .x24=BitVec.ofNat 64 count) :
    (nonceExpandGuardState state).pc=if count=0 then 5048 else 5016 := by
  have zero : (BitVec.ofNat 64 count : Word)=0 ↔ count=0 := by
    constructor
    · intro equal
      have numeric:=congrArg BitVec.toNat equal
      change count%2^64=0 at numeric
      rw [Nat.mod_eq_of_lt small] at numeric
      exact numeric
    · rintro rfl
      rfl
  simp only [nonceExpandGuardState, execInstrBr, counter,
    show state.getReg .x0=0 from rfl, beq_iff_eq, zero]
  by_cases empty : count=0 <;>
    simp [empty, MachineState.setPC, pc, signExtend13]

def nonceExpandFooterCall (state : MachineState) : MachineState := execInstrBr state (.JAL .x1 88)

theorem nonce_expand_footer_call_execute (state : MachineState) (pc : state.pc=5008)
    (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (1+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel (nonceExpandFooterCall state) coins
          return result.charge 1 0) := by
  have fetched : fetch nonceExpandedImage state=some (.base (.JAL .x1 88)) := by
    apply cap_image_fetch _ state 228 _ (by decide) pc
    rfl
  rw [Nat.add_comm 1 fuel,execute_ordinary_step nonceExpandedImage _ state
    (nonceExpandFooterCall state) fuel coins fetched (by rfl)]
  rfl

theorem nonce_expand_footer_call_memory (state : MachineState) : (nonceExpandFooterCall state).mem=state.mem := rfl

theorem nonce_expand_footer_call_register (state : MachineState) (reg : Reg) (outside : reg ≠ .x1) :
    (nonceExpandFooterCall state).getReg reg=state.getReg reg := by
  simp only [nonceExpandFooterCall,execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside)]

theorem nonce_expand_footer_call_pc (state : MachineState) (pc : state.pc=5008) :
    (nonceExpandFooterCall state).pc=5096 ∧ (nonceExpandFooterCall state).getReg .x1=5012 := by
  simp [nonceExpandFooterCall,execInstrBr,MachineState.setPC,MachineState.getReg,MachineState.setReg,signExtend21,pc]

theorem nonce_expand_footer_return_pc (state : MachineState) (pc : state.pc=5008) (words : Nat) :
    (nonceBackwardReturned (nonceExpandFooterCall state) words).pc=5012 := by
  have link:=(nonce_expand_footer_call_pc state pc).2
  rw [nonceBackwardReturned,NonceCopyProcedure.loop_return_pc]
  · exact link
  · rw [link]
    decide

end CommitGolfCandidate
