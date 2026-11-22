import CommitGolfCandidate.Layout2Steps

/-! Layout 2 V2a opener: generic `jal x0` and `addi` effects used by the record loop (V2a has no first-record entry
stub: the pass jumps to phase 0's header). -/
namespace TwoPermutationPrototype.GroupedOpening.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

/-! Generic `jal x0` and `addi` effects with the offset as a variable: the kernel never evaluates a concrete
offset (unfolding `execInstrBr` on a concrete negative `jal` offset is very expensive for the kernel). -/
theorem jal0_mem (u : MachineState) (off : BitVec 21) : (execInstrBr u (.JAL .x0 off)).mem=u.mem := by
  simp only [execInstrBr]; rw [mem_of_set, mem_of_reg]
theorem jal0_reg (u : MachineState) (off : BitVec 21) (r : Reg) : (execInstrBr u (.JAL .x0 off)).getReg r=u.getReg r := by
  simp only [execInstrBr]; rw [MachineState.getReg_setPC, Opening.getReg_setReg]; simp
theorem jal0_pc (u : MachineState) (off : BitVec 21) : (execInstrBr u (.JAL .x0 off)).pc=u.pc+signExtend21 off := by
  simp only [execInstrBr]; rfl
theorem addi_mem (u : MachineState) (rd rs : Reg) (imm : BitVec 12) : (execInstrBr u (.ADDI rd rs imm)).mem=u.mem := by
  simp only [execInstrBr]; rw [mem_of_set, mem_of_reg]
theorem addi_pc (u : MachineState) (rd rs : Reg) (imm : BitVec 12) : (execInstrBr u (.ADDI rd rs imm)).pc=u.pc+4 := by
  simp only [execInstrBr]; rfl
theorem addi_other (u : MachineState) (rd rs : Reg) (imm : BitVec 12) (r : Reg) (h : r ≠ rd) :
    (execInstrBr u (.ADDI rd rs imm)).getReg r=u.getReg r := by
  simp only [execInstrBr]; rw [MachineState.getReg_setPC, Opening.getReg_setReg]; simp [Ne.symm h]
theorem addi_self (u : MachineState) (rd rs : Reg) (imm : BitVec 12) (h : rd ≠ .x0) :
    (execInstrBr u (.ADDI rd rs imm)).getReg rd=u.getReg rs+signExtend12 imm := by
  simp only [execInstrBr]; rw [MachineState.getReg_setPC, Opening.getReg_setReg]; simp [h]

end TwoPermutationPrototype.GroupedOpening.Layout2
