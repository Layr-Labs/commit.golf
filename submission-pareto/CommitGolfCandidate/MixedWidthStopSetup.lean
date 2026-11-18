import CommitGolfCandidate.MixedWidthParentControl

namespace TwoPermutationPrototype.RV64
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- x17 holds the address of node2^21−1, the last node left for the projected phase. -/
def mixedStopOps : List Instr :=
  [.LUI .x17 16384,.ADD .x17 .x9 .x17,.ADDI .x17 .x17 4064]

def mixedStopSetup (state : MachineState) : MachineState :=
  mixedStopOps.foldl execInstrBr state

theorem mixed_stop_memory (state : MachineState) :
    (mixedStopSetup state).mem=state.mem := rfl

theorem mixed_stop_register (state : MachineState) (reg : Reg) (kept : Reg.x17≠reg) :
    (mixedStopSetup state).getReg reg=state.getReg reg := by
  simp only [mixedStopSetup,mixedStopOps,List.foldl_cons,List.foldl_nil,execInstrBr,
    MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ kept]

theorem mixed_stop_parent_regs (state : MachineState) (n : Nat) (regs : ParentRegs state n) :
    ParentRegs (mixedStopSetup state) n := by
  constructor
  · exact (mixed_stop_register state .x10 (by decide)).trans regs.source
  · exact (mixed_stop_register state .x12 (by decide)).trans regs.target
  · exact (mixed_stop_register state .x5 (by decide)).trans regs.selector
  · exact (mixed_stop_register state .x11 (by decide)).trans regs.size
  · exact (mixed_stop_register state .x13 (by decide)).trans regs.primitive
  · exact (mixed_stop_register state .x9 (by decide)).trans regs.heap

theorem mixed_stop_value (state : MachineState) (n : Nat) (regs : ParentRegs state n) :
    (mixedStopSetup state).getReg .x17=wordAddress (treeWord 2097151) := by
  have value : (mixedStopSetup state).getReg .x17=
      state.getReg .x9+67108864+signExtend12 4064 := by
    rfl
  rw [value,regs.heap]
  rfl

theorem mixed_stop_pc (state : MachineState) : (mixedStopSetup state).pc=state.pc+12 := by
  change state.pc+4+4+4=state.pc+12
  rw [BitVec.add_assoc,BitVec.add_assoc]
  rfl

end TwoPermutationPrototype.RV64
