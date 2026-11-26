import CommitGolfCandidate.ChainedFooterEmit

/-! Actual four-instruction mark lookup before each native footer subtree. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setReg_ne

@[local simp] private theorem lookup_pc_set (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem lookup_zero (s : MachineState) : s.getReg .x0=0#64 := rfl

def footerLookupOps : List Instr :=
  [.SLLI .x31 .x30 3,.ADD .x31 .x8 .x31,.LD .x31 .x31 0,.BEQ .x31 .x0 16]
def footerMarkAddress (s : MachineState) : Word := s.getReg .x8+(s.getReg .x30<<<3)
def footerLookupPrefix (s : MachineState) (count : Nat) : MachineState :=
  (footerLookupOps.take count).foldl execInstrBr s

theorem opening_footer_lookup_layout : openingControllerOps=openingControllerOps.take 2078++
    footerLookupOps++openingControllerOps.drop 2082 := by decide
theorem controller_footer_lookup_at : OpsAt openingControllerImage 12408 footerLookupOps := by
  have code := opening_controller_ops_at
  rw [opening_footer_lookup_layout,List.append_assoc] at code
  have body := ops_at_right openingControllerImage 4096 (openingControllerOps.take 2078) _ code
  rw [List.length_take,opening_controller_ops_length] at body
  exact ops_at_left openingControllerImage _ _ _ body

private theorem lookup_succ (s : MachineState) (index : Nat) (inside : index<4) :
    footerLookupPrefix s (index+1)=execInstrBr (footerLookupPrefix s index) (footerLookupOps.getD index .EBREAK) := by
  interval_cases index <;> rfl

theorem footer_mark_address_eq (s : MachineState) (node : Nat)
    (base : s.getReg .x8=4096) (cursor : s.getReg .x30=BitVec.ofNat 64 node) :
    footerMarkAddress s=BitVec.ofNat 64 (4096+8*node) := by
  rw [footerMarkAddress,base,cursor,BitVec.shiftLeft_eq_mul_twoPow]
  change BitVec.ofNat 64 4096+BitVec.ofNat 64 node*BitVec.ofNat 64 8=_
  rw [←BitVec.ofNat_mul,←BitVec.ofNat_add,Nat.mul_comm node]

theorem footer_lookup_pc (s : MachineState) (pc : s.pc=12408) :
    (footerLookupPrefix s 4).pc=if s.getMem (footerMarkAddress s)=0 then 12436 else 12424 := by
  by_cases empty : s.getMem (footerMarkAddress s)=0#64 <;>
    simp [footerMarkAddress] at empty ⊢ <;>
    simp [footerLookupPrefix,footerLookupOps,execInstrBr,signExtend12,signExtend13,pc,empty]

theorem footer_lookup_register (s : MachineState) (reg : Reg) (different : reg≠.x31) :
    (footerLookupPrefix s 4).getReg reg=s.getReg reg := by
  by_cases empty : s.getMem (footerMarkAddress s)=0#64 <;>
    simp [footerMarkAddress] at empty <;>
    simp [footerLookupPrefix,footerLookupOps,execInstrBr,signExtend12,empty,Ne.symm different]

theorem footer_lookup_memory (s : MachineState) (query : Word) : (footerLookupPrefix s 4).getMem query=s.getMem query := by
  by_cases empty : s.getMem (footerMarkAddress s)=0#64 <;>
    simp [footerMarkAddress] at empty <;>
    simp [footerLookupPrefix,footerLookupOps,execInstrBr,signExtend12,empty]
theorem footer_lookup_byte (s : MachineState) (query : Word) : (footerLookupPrefix s 4).getByte query=s.getByte query := by
  simp only [MachineState.getByte,footer_lookup_memory]

theorem footer_lookup_execution (s : MachineState) (pc : s.pc=12408)
    (valid : accessValid (footerMarkAddress s) 8=true) (fuel : Nat) (coins : Bool) :
    execute openingControllerImage (4+fuel) s coins=
      (do let result ← execute openingControllerImage fuel (footerLookupPrefix s 4) coins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := footerLookupPrefix s)
  intro index inside
  refine ⟨.base (footerLookupOps.getD index .EBREAK),?_,?_,?_⟩
  · apply controller_footer_lookup_at index (by simpa [footerLookupOps] using inside)
    interval_cases index <;> simp [footerLookupPrefix,footerLookupOps,execInstrBr,pc]
  · rw [lookup_succ s index inside]
    simp only [footerMarkAddress] at valid
    interval_cases index <;> simp [ordinaryStep,memoryArgumentsValid,memAccess,footerLookupPrefix,footerLookupOps,
      execInstrBr,signExtend12,valid]
  · interval_cases index <;> rfl

end CommitGolfCandidate.Chained.Native
