import CommitGolfCandidate.QuadNodeCode
import CommitGolfCandidate.TwoPermutationPackedCapBytes

namespace TwoPermutationPrototype.Quad.Checker
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 200000
attribute [local irreducible] execute ByteCopy.copyField ByteCopy.copyRun ByteCopy.copyStep
attribute [local simp] Opening.getReg_setReg Opening.getReg_setMem MachineState.getReg_setPC
@[local simp] private theorem loop_set_pc (s : MachineState) (pc : Word) : (s.setPC pc).pc=pc := rfl
@[local simp] private theorem loop_zero (s : MachineState) : s.getReg .x0=0#64 := rfl

def quadSlotPrefixCode : List Instr :=
  [.ADDI .x29 .x29 32,.ANDI .x29 .x29 127,.ADD .x28 .x10 .x29]

def quadSlotPrefix (s : MachineState) (n : Nat) : MachineState :=
  (quadSlotPrefixCode.take n).foldl execInstrBr s

def quadSlotLatchCode : List Instr :=
  [.ADDI .x21 .x21 32,.ADDI .x30 .x30 4095,.BNE .x30 .x0 8044]

def quadSlotLatch (s : MachineState) (n : Nat) : MachineState :=
  (quadSlotLatchCode.take n).foldl execInstrBr s

def quadSlot (s : MachineState) : MachineState :=
  quadSlotLatch (ByteCopy.copyField quadSiblingCode (quadSlotPrefix s 3)) 3

def quadNextSlot (r : Fin 4) : Fin 4 := ⟨(r.val+1)%4,Nat.mod_lt _ (by decide)⟩

def quadTarget (r : Fin 4) : Nat := 12872+32*(quadNextSlot r).val





theorem quad_slot_prefix_hop (s : MachineState) (pc : s.pc=5652) :
    GroupHop s (quadSlotPrefix s 3) 3 := by
  intro fuel
  apply execute_unit_steps (states := quadSlotPrefix s)
  intro i bounded
  refine ⟨.base (quadSlotPrefixCode[i]?.getD .EBREAK),?_,?_,?_⟩
  · apply fetch_at _ (389+i) _ (by omega)
    · interval_cases i <;> simp [quadSlotPrefix,quadSlotPrefixCode,execInstrBr,pc]
    · interval_cases i <;> rfl
  · interval_cases i <;> simp only [quadSlotPrefix,quadSlotPrefixCode,
      List.take,List.foldl,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
      ordinaryStep,memoryArgumentsValid,memAccess,ite_true]
  · interval_cases i <;> rfl



theorem quad_slot_prefix_post (s : MachineState) (r : Fin 4)
    (pc : s.pc=5652) (base : s.getReg .x10=12800)
    (offset : s.getReg .x29=BitVec.ofNat 64 (32*r.val)) :
    let t := quadSlotPrefix s 3
    t.pc=5664 ∧ t.getReg .x29=BitVec.ofNat 64 (32*(quadNextSlot r).val) ∧
    t.getReg .x28+72#64=BitVec.ofNat 64 (quadTarget r) := by
  fin_cases r <;> simp [quadSlotPrefix,quadSlotPrefixCode,execInstrBr,signExtend12,pc,base,offset,quadNextSlot,quadTarget]



theorem quad_slot_prefix_register (s : MachineState) (reg : Reg)
    (a : reg≠.x29) (b : reg≠.x28) : (quadSlotPrefix s 3).getReg reg=s.getReg reg := by
  simp only [quadSlotPrefix,quadSlotPrefixCode,List.take,List.foldl,execInstrBr,
    MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm a),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm b)]



theorem quad_slot_latch_hop (s : MachineState) (left : Nat) (positive : 0<left) (bound : left≤3)
    (pc : s.pc=5792) (counter : s.getReg .x30=BitVec.ofNat 64 left) :
    GroupHop s (quadSlotLatch s 3) 3 := by
  intro fuel
  apply execute_unit_steps (states := quadSlotLatch s)
  intro i bounded
  refine ⟨.base (quadSlotLatchCode[i]?.getD .EBREAK),?_,?_,?_⟩
  · apply fetch_at _ (424+i) _ (by omega)
    · interval_cases i <;> simp [quadSlotLatch,quadSlotLatchCode,execInstrBr,pc]
    · interval_cases i <;> rfl
  · interval_cases left <;> interval_cases i <;>
      simp [quadSlotLatch,quadSlotLatchCode,ordinaryStep,memoryArgumentsValid,memAccess,
        execInstrBr,signExtend12,signExtend13,counter]
  · interval_cases i <;> rfl

theorem quad_slot_latch_post (s : MachineState) (left : Nat) (positive : 0<left) (bound : left≤3)
    (pc : s.pc=5792) (counter : s.getReg .x30=BitVec.ofNat 64 left) :
    let t := quadSlotLatch s 3
    t.pc=(if left=1 then 5804 else 5652) ∧
    t.getReg .x30=BitVec.ofNat 64 (left-1) ∧ t.getReg .x21=s.getReg .x21+32 := by
  interval_cases left <;> simp [quadSlotLatch,quadSlotLatchCode,execInstrBr,signExtend12,signExtend13,pc,counter]



theorem quad_slot_latch_register (s : MachineState) (reg : Reg)
    (a : reg≠.x21) (b : reg≠.x30) (left : Nat)
    (positive : 0<left) (bound : left≤3) (counter : s.getReg .x30=BitVec.ofNat 64 left) :
    (quadSlotLatch s 3).getReg reg=s.getReg reg := by
  interval_cases left <;>
    simp [quadSlotLatch,quadSlotLatchCode,execInstrBr,signExtend12,signExtend13,counter,Ne.symm a,Ne.symm b]

end TwoPermutationPrototype.Quad.Checker
