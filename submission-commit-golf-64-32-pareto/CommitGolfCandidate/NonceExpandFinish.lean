import CommitGolfCandidate.NonceExpandOuter

/-! The real expansion epilogue restores all scratch registers to loader
values, moves the expanded byte length into x17 and jumps to the retained
initializer tail. The ten resets are actual emitted instructions. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceExpandResetRegisters : List Reg := [.x1,.x6,.x7,.x18,.x19,.x23,.x24,.x25,.x28,.x29]

def nonceExpandFinishInstructions : List Instr :=
  [.ADDI .x17 .x18 0] ++ (nonceExpandResetRegisters.map fun reg => .ADDI reg .x0 0) ++ [.JAL .x0 2096160]

def nonceExpandFinishPrefix (state : MachineState) (count : Nat) : MachineState :=
  (nonceExpandFinishInstructions.take count).foldl execInstrBr state

theorem nonce_expand_finish_prefix_pc (state : MachineState) (count : Nat) (bounded : count ≤ 11) :
    (nonceExpandFinishPrefix state count).pc=state.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;>
    simp [nonceExpandFinishPrefix,nonceExpandFinishInstructions,nonceExpandResetRegisters,
      execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem nonce_expand_finish_execute (state : MachineState) (pc : state.pc=5048)
    (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (12+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel (nonceExpandFinishPrefix state 12) coins
          return result.charge 12 0) := by
  apply execute_unit_steps (states := nonceExpandFinishPrefix state)
  intro count bounded
  refine ⟨.base ((nonceExpandFinishInstructions[count]?).getD .EBREAK),?_,?_,?_⟩
  · apply cap_image_fetch _ _ (238+count) _ (by omega)
    · rw [nonce_expand_finish_prefix_pc state count (by omega),pc]
      interval_cases count <;> rfl
    · interval_cases count <;> rfl
  · interval_cases count <;> rfl
  · interval_cases count <;> rfl

theorem nonce_expand_finish_pc (state : MachineState) (pc : state.pc=5048) :
    (nonceExpandFinishPrefix state 12).pc=4100 := by
  change (execInstrBr (nonceExpandFinishPrefix state 11) (.JAL .x0 2096160)).pc=4100
  simp only [execInstrBr,MachineState.setPC]
  rw [nonce_expand_finish_prefix_pc state 11 (by decide),pc]
  decide

theorem nonce_expand_finish_memory (state : MachineState) :
    (nonceExpandFinishPrefix state 12).mem=state.mem := rfl

private theorem addi_register (state : MachineState) (rd source reg : Reg) (offset : BitVec 12)
    (outside : rd ≠ reg) :
    (execInstrBr state (.ADDI rd source offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ outside]

private theorem zero_value (state : MachineState) (rd : Reg) :
    (execInstrBr state (.ADDI rd .x0 0)).getReg rd=0 := by
  cases rd <;> simp [execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,MachineState.setPC]

private theorem reset_register (registers : List Reg) (state : MachineState) (reg : Reg) :
    ((registers.map fun rd => Instr.ADDI rd .x0 0).foldl execInstrBr state).getReg reg=
      if reg ∈ registers then 0 else state.getReg reg := by
  induction registers generalizing state with
  | nil => simp
  | cons rd registers ih =>
    rw [List.map_cons,List.foldl_cons,ih]
    by_cases later : reg ∈ registers
    · simp only [if_pos later,List.mem_cons,later,or_true,ite_true]
    · rw [if_neg later]
      by_cases equal : reg=rd
      · subst reg
        rw [zero_value]
        simp
      · rw [addi_register _ rd .x0 reg 0 (Ne.symm equal)]
        simp only [List.mem_cons,equal,later,false_or,ite_false]

private theorem jump_register (state : MachineState) (offset : BitVec 21) (reg : Reg) :
    (execInstrBr state (.JAL .x0 offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr,MachineState.getReg_setPC]
  rfl

private theorem finish_decompose (state : MachineState) :
    nonceExpandFinishPrefix state 12=execInstrBr
      ((nonceExpandResetRegisters.map fun reg => Instr.ADDI reg .x0 0).foldl execInstrBr
        (execInstrBr state (.ADDI .x17 .x18 0))) (.JAL .x0 2096160) := rfl

theorem nonce_expand_finish_length (state : MachineState) :
    (nonceExpandFinishPrefix state 12).getReg .x17=state.getReg .x18 := by
  rw [finish_decompose,jump_register,reset_register,if_neg (by decide : Reg.x17 ∉ nonceExpandResetRegisters)]
  simp [execInstrBr,MachineState.getReg,MachineState.setReg,MachineState.setPC,signExtend12]

theorem nonce_expand_finish_zero (state : MachineState) (reg : Reg)
    (reset : reg ∈ nonceExpandResetRegisters) :
    (nonceExpandFinishPrefix state 12).getReg reg=0 := by
  rw [finish_decompose,jump_register,reset_register,if_pos reset]

theorem nonce_expand_finish_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x17 ∧ reg ∉ nonceExpandResetRegisters) :
    (nonceExpandFinishPrefix state 12).getReg reg=state.getReg reg := by
  rw [finish_decompose,jump_register,reset_register,if_neg outside.2]
  exact addi_register state .x17 .x18 reg 0 (Ne.symm outside.1)

end CommitGolfCandidate
