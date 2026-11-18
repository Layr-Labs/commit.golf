import CommitGolfCandidate.TwoPermutationWideLeafFetch
import CommitGolfCandidate.TwoPermutationLeafRun
import CommitGolfCandidate.OverlapWordMemory

namespace TwoPermutationPrototype.RV64.WideLeaves
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000

abbrev firstInstructions (slot : Fin 256) := wideFirstOps slot.val
abbrev secondInstructions (slot : Fin 256) := wideSecondOps slot.val

def leafInstructions (slot : Fin 256) : List Instr :=
  firstInstructions slot ++ [.ECALL] ++ secondInstructions slot ++ [.ECALL,.ADDI .x10 .x10 192]

private theorem reg_store (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r=s.getReg r := by cases r <;> rfl

def firstMemory (s : MachineState) := s.setMem (s.getReg .x10) 0

theorem first_execution (s : MachineState) (slot : Fin 256) :
    let t := (firstInstructions slot).foldl execInstrBr s
    t.mem=(firstMemory s).mem ∧ t.getReg .x10=s.getReg .x10 ∧
    t.getReg .x12=s.getReg .x10 + (-96 : Word) ∧ t.getReg .x5=s.getReg .x5 ∧
    t.getReg .x11=s.getReg .x11 ∧ t.getReg .x13=s.getReg .x13 ∧ t.pc=s.pc+8 := by
  simp [firstInstructions,wideFirstOps,firstMemory,execInstrBr,MachineState.getReg,
    MachineState.setMem,MachineState.setReg,MachineState.setPC,signExtend12,BitVec.add_assoc]

theorem nonce_offsets : ∀ slot : Fin 256,
    signExtend12 (BitVec.ofNat 12 (16*(slot.val%128))) = BitVec.ofNat 64 (16*(slot.val%128)) ∧
    signExtend12 (BitVec.ofNat 12 (16*(slot.val%128)+8)) = BitVec.ofNat 64 (16*(slot.val%128)+8) := by decide

theorem heap_offset : ∀ slot : Fin 256,
    signExtend12 (BitVec.ofNat 12 (32*(slot.val%64)))=BitVec.ofNat 64 (32*(slot.val%64)) := by decide

/-- Actual store/load order, so no separation assumption is needed at this layer. -/
def secondMemory (s : MachineState) (slot : Fin 256) : MachineState :=
  let w := s.getReg .x10+64
  let tape := s.getReg .x22
  let t := s.setMem w w
  let u := t.setMem (w+40) (t.getMem (tape + BitVec.ofNat 64 (16*(slot.val%128))))
  u.setMem (w+48) (u.getMem (tape + BitVec.ofNat 64 (16*(slot.val%128)+8)))

theorem second_execution (s : MachineState) (slot : Fin 256) :
    let t := (secondInstructions slot).foldl execInstrBr s
    t.mem=(secondMemory s slot).mem ∧ t.getReg .x10=s.getReg .x10+64 ∧
    t.getReg .x12=s.getReg .x20+BitVec.ofNat 64 (32*(slot.val%64)) ∧
    t.getReg .x5=s.getReg .x5 ∧ t.getReg .x11=s.getReg .x11 ∧
    t.getReg .x13=s.getReg .x13 ∧ t.pc=s.pc+28 := by
  have offs := nonce_offsets slot
  simp only [secondInstructions,wideSecondOps,secondMemory,List.foldl_cons,List.foldl_nil,execInstrBr,
    show signExtend12 0=(0:Word) by decide,show signExtend12 64=(64:Word) by decide,
    show signExtend12 40=(40:Word) by decide,show signExtend12 48=(48:Word) by decide,
    offs.1,offs.2,heap_offset slot,MachineState.getReg_setPC,reg_store,
    MachineState.getMem_setReg,MachineState.getMem_setPC,BitVec.add_zero]
  simp [MachineState.getReg,MachineState.setReg,MachineState.setPC,MachineState.setMem,
    MachineState.getMem,BitVec.add_assoc]

end TwoPermutationPrototype.RV64.WideLeaves
