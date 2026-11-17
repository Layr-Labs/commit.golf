import CommitGolfCandidate.NonceExpandMinimum

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceExpandCapacityInstructions : List Instr :=
  [.SLLI .x7 .x16 3,.ADD .x18 .x17 .x7,.ADDI .x19 .x0 0,
    .SLLI .x19 .x19 11,.ADDI .x19 .x19 1,.SLLI .x19 .x19 11,
    .ADDI .x19 .x19 1152,.SLLI .x19 .x19 11,.ADDI .x19 .x19 0,
    .SLLI .x19 .x19 11,.ADDI .x19 .x19 0,.BLTU .x19 .x18 8024]

def nonceExpandCapacityPrefix (state : MachineState) (count : Nat) : MachineState :=
  (nonceExpandCapacityInstructions.take count).foldl execInstrBr state

theorem nonce_expand_capacity_prefix_next (state : MachineState) (count : Nat) (bounded : count<12) :
    nonceExpandCapacityPrefix state (count+1)=execInstrBr (nonceExpandCapacityPrefix state count)
      ((nonceExpandCapacityInstructions[count]?).getD .EBREAK) := by
  have inside : count<nonceExpandCapacityInstructions.length := by simpa [nonceExpandCapacityInstructions] using bounded
  unfold nonceExpandCapacityPrefix
  rw [List.take_succ_eq_append_getElem inside,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,getElem?_pos nonceExpandCapacityInstructions count inside,Option.getD_some]

theorem nonce_expand_capacity_last (state : MachineState) :
    nonceExpandCapacityPrefix state 12=execInstrBr (nonceExpandCapacityPrefix state 11) (.BLTU .x19 .x18 8024) :=
  nonce_expand_capacity_prefix_next state 11 (by decide)

attribute [local irreducible] nonceExpandCapacityPrefix

theorem nonce_expand_capacity_prefix_pc (state : MachineState) (count : Nat) (bounded : count ≤ 11) :
    (nonceExpandCapacityPrefix state count).pc=state.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> simp [nonceExpandCapacityPrefix,nonceExpandCapacityInstructions,
    execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem nonce_expand_capacity_execute (state : MachineState) (pc : state.pc=4932)
    (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (12+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel (nonceExpandCapacityPrefix state 12) coins
          return result.charge 12 0) := by
  have zero : nonceExpandCapacityPrefix state 0=state := by unfold nonceExpandCapacityPrefix; rfl
  conv_lhs => rw [←zero]
  apply execute_unit_steps (states := nonceExpandCapacityPrefix state)
  intro count bounded
  refine ⟨.base ((nonceExpandCapacityInstructions[count]?).getD .EBREAK),?_,?_,?_⟩
  · apply cap_image_fetch _ _ (209+count) _ (by omega)
    · rw [nonce_expand_capacity_prefix_pc state count (by omega),pc]
      interval_cases count <;> rfl
    · interval_cases count <;> rfl
  · rw [nonce_expand_capacity_prefix_next state count bounded]
    interval_cases count <;> rfl
  · interval_cases count <;> rfl

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BLTU .x19 .x18 offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BLTU .x19 .x18 offset)).mem=state.mem := by
  simp only [execInstrBr]
  split <;> rfl

theorem nonce_expand_capacity_memory (state : MachineState) :
    (nonceExpandCapacityPrefix state 12).mem=state.mem := by
  rw [nonce_expand_capacity_last]
  rw [branch_memory]
  unfold nonceExpandCapacityPrefix
  rfl

theorem nonce_expand_capacity_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x7 ∧ reg ≠ .x18 ∧ reg ≠ .x19) :
    (nonceExpandCapacityPrefix state 12).getReg reg=state.getReg reg := by
  rw [nonce_expand_capacity_last]
  rw [branch_register]
  simp only [nonceExpandCapacityPrefix,nonceExpandCapacityInstructions,List.take,List.foldl_cons,List.foldl_nil,
    execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2.2)]

theorem nonce_expand_capacity_raw (state : MachineState) :
    (nonceExpandCapacityPrefix state 11).getReg .x18=state.getReg .x17+(state.getReg .x16 <<< 3) := by
  unfold nonceExpandCapacityPrefix
  rfl

theorem nonce_expand_capacity_limit (state : MachineState) :
    (nonceExpandCapacityPrefix state 11).getReg .x19=13421772800 := by
  simp [nonceExpandCapacityPrefix,nonceExpandCapacityInstructions,execInstrBr,signExtend12,
    MachineState.getReg,MachineState.setReg,MachineState.setPC]

theorem nonce_expand_capacity_length (state : MachineState) (length count : Nat)
    (reported : state.getReg .x17=BitVec.ofNat 64 length)
    (counter : state.getReg .x16=BitVec.ofNat 64 count) :
    (nonceExpandCapacityPrefix state 12).getReg .x18=BitVec.ofNat 64 (length+8*count) := by
  rw [nonce_expand_capacity_last]
  rw [branch_register,nonce_expand_capacity_raw,reported,counter]
  have shift : (BitVec.ofNat 64 count <<< 3)=BitVec.ofNat 64 (8*count) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 count*BitVec.ofNat 64 8=_
    rw [←BitVec.ofNat_mul,Nat.mul_comm]
  rw [shift,←BitVec.ofNat_add]

theorem nonce_expand_capacity_pc (state : MachineState) (pc : state.pc=4932) (length count : Nat)
    (small : length+8*count<2^64) (reported : state.getReg .x17=BitVec.ofNat 64 length)
    (counter : state.getReg .x16=BitVec.ofNat 64 count) :
    (nonceExpandCapacityPrefix state 12).pc=if 13421772800<length+8*count then 4808 else 4980 := by
  have lengthReg : (nonceExpandCapacityPrefix state 11).getReg .x18=BitVec.ofNat 64 (length+8*count) := by
    have final:=nonce_expand_capacity_length state length count reported counter
    rw [nonce_expand_capacity_last] at final
    simpa only [branch_register] using final
  rw [nonce_expand_capacity_last]
  have limitNat : (13421772800:Word).toNat=13421772800 := by decide
  simp only [execInstrBr,nonce_expand_capacity_limit,lengthReg,BitVec.ult_iff_toNat_lt,limitNat,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  by_cases oversized : 13421772800<length+8*count <;>
    simp [oversized,MachineState.setPC,nonce_expand_capacity_prefix_pc state 11 (by decide),pc,signExtend13]

end CommitGolfCandidate
