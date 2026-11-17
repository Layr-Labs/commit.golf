import CommitGolfCandidate.NonceExpandHeader
import CommitGolfCandidate.CostedExecution

namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceExpandMinimumInstructions : List Instr :=
  [.ADDI .x29 .x0 0,.SLLI .x29 .x29 11,.ADDI .x29 .x29 536,
    .MUL .x6 .x16 .x29,.BLTU .x17 .x6 8072]

def nonceExpandMinimumPrefix (state : MachineState) (count : Nat) : MachineState :=
  (nonceExpandMinimumInstructions.take count).foldl execInstrBr state

theorem nonce_expand_minimum_prefix_next (state : MachineState) (count : Nat) (bounded : count<5) :
    nonceExpandMinimumPrefix state (count+1)=execInstrBr (nonceExpandMinimumPrefix state count)
      ((nonceExpandMinimumInstructions[count]?).getD .EBREAK) := by
  have inside : count<nonceExpandMinimumInstructions.length := by simpa [nonceExpandMinimumInstructions] using bounded
  unfold nonceExpandMinimumPrefix
  rw [List.take_succ_eq_append_getElem inside,List.foldl_append]
  simp only [List.foldl_cons,List.foldl_nil,getElem?_pos nonceExpandMinimumInstructions count inside,Option.getD_some]

theorem nonce_expand_minimum_last (state : MachineState) :
    nonceExpandMinimumPrefix state 5=execInstrBr (nonceExpandMinimumPrefix state 4) (.BLTU .x17 .x6 8072) :=
  nonce_expand_minimum_prefix_next state 4 (by decide)

attribute [local irreducible] nonceExpandMinimumPrefix

theorem nonce_expand_minimum_prefix_pc (state : MachineState) (count : Nat) (bounded : count ≤ 4) :
    (nonceExpandMinimumPrefix state count).pc=state.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> simp [nonceExpandMinimumPrefix,nonceExpandMinimumInstructions,
    execInstrBr,MachineState.setPC,BitVec.add_assoc]

theorem nonce_expand_minimum_execute (state : MachineState) (pc : state.pc=4912)
    (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (5+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel (nonceExpandMinimumPrefix state 5) coins
          return result.charge 8 0) := by
  have zero : nonceExpandMinimumPrefix state 0=state := by unfold nonceExpandMinimumPrefix; rfl
  have execution:=execute_costed_steps nonceExpandedImage 5 fuel (nonceExpandMinimumPrefix state)
    (fun index => if index=3 then 4 else 1) coins (by
      intro count bounded
      refine ⟨.base ((nonceExpandMinimumInstructions[count]?).getD .EBREAK),?_,?_,?_⟩
      · apply cap_image_fetch _ _ (204+count) _ (by omega)
        · rw [nonce_expand_minimum_prefix_pc state count (by omega),pc]
          interval_cases count <;> rfl
        · interval_cases count <;> rfl
      · rw [nonce_expand_minimum_prefix_next state count bounded]
        interval_cases count <;> rfl
      · interval_cases count <;> rfl)
  simpa only [zero,show linearTraceCost 5 (fun index => if index=3 then 4 else 1)=8 by decide] using execution

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BLTU .x17 .x6 offset)).getReg reg=state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BLTU .x17 .x6 offset)).mem=state.mem := by
  simp only [execInstrBr]
  split <;> rfl

theorem nonce_expand_minimum_memory (state : MachineState) :
    (nonceExpandMinimumPrefix state 5).mem=state.mem := by
  rw [nonce_expand_minimum_last]
  rw [branch_memory]
  unfold nonceExpandMinimumPrefix
  rfl

theorem nonce_expand_minimum_register (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x29) :
    (nonceExpandMinimumPrefix state 5).getReg reg=state.getReg reg := by
  rw [nonce_expand_minimum_last]
  rw [branch_register]
  simp only [nonceExpandMinimumPrefix,nonceExpandMinimumInstructions,List.take,List.foldl_cons,List.foldl_nil,
    execInstrBr,MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.1),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm outside.2)]

theorem nonce_expand_minimum_raw (state : MachineState) :
    (nonceExpandMinimumPrefix state 4).getReg .x6=state.getReg .x16*536 := by
  simp [nonceExpandMinimumPrefix,nonceExpandMinimumInstructions,execInstrBr,signExtend12,
    MachineState.getReg,MachineState.setReg,MachineState.setPC]

theorem nonce_expand_minimum_product (state : MachineState) (count : Nat)
    (counter : state.getReg .x16=BitVec.ofNat 64 count) :
    (nonceExpandMinimumPrefix state 5).getReg .x6=BitVec.ofNat 64 (536*count) := by
  rw [nonce_expand_minimum_last]
  rw [branch_register,nonce_expand_minimum_raw,counter]
  change BitVec.ofNat 64 count*BitVec.ofNat 64 536=_
  rw [←BitVec.ofNat_mul,Nat.mul_comm]

theorem nonce_expand_minimum_pc (state : MachineState) (pc : state.pc=4912) (length count : Nat)
    (lengthSmall : length<2^64) (productSmall : 536*count<2^64)
    (reported : state.getReg .x17=BitVec.ofNat 64 length)
    (counter : state.getReg .x16=BitVec.ofNat 64 count) :
    (nonceExpandMinimumPrefix state 5).pc=if length<536*count then 4808 else 4932 := by
  have product : (nonceExpandMinimumPrefix state 4).getReg .x6=BitVec.ofNat 64 (536*count) := by
    have final:=nonce_expand_minimum_product state count counter
    rw [nonce_expand_minimum_last] at final
    simpa only [branch_register] using final
  have lengthReg : (nonceExpandMinimumPrefix state 4).getReg .x17=BitVec.ofNat 64 length := by
    have final:=nonce_expand_minimum_register state .x17 (by decide)
    rw [nonce_expand_minimum_last] at final
    rw [branch_register] at final
    exact final.trans reported
  rw [nonce_expand_minimum_last]
  simp only [execInstrBr,product,lengthReg,BitVec.ult_iff_toNat_lt,BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt lengthSmall,Nat.mod_eq_of_lt productSmall]
  by_cases short : length<536*count <;>
    simp [short,MachineState.setPC,nonce_expand_minimum_prefix_pc state 4 (by decide),pc,signExtend13]

end CommitGolfCandidate
