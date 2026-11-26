import CommitGolfCandidate.S5Trace
import CommitGolfCandidate.S5ReadWindow
namespace CommitGolfCandidate.S5Machine.Reader
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def refillPrefix : PathCode := [(38,.BGEU .x22 .x6 36),(39,.BLTU .x19 .x20 8)]
def loadByte : PathCode := [(41,.LBU .x7 .x19 0),(42,.ADDI .x19 .x19 1),(43,.SLL .x7 .x7 .x22),
  (44,.OR .x21 .x21 .x7),(45,.ADDI .x22 .x22 8),(46,.JAL .x0 2097120)]
def loaded (s : MachineState) :=pathEnd s loadByte

private theorem branches (s : MachineState) (ip : s.pc=pcAt 38) (few : (s.getReg .x22).ult (s.getReg .x6)=true)
    (more : (s.getReg .x19).ult (s.getReg .x20)=true) :
    pathReady s refillPrefix ∧ pathEnd s refillPrefix=s.setPC (pcAt 41) := by
  change (s.regs .x22).ult (s.regs .x6)=true at few
  change (s.regs .x19).ult (s.regs .x20)=true at more
  simp +decide [refillPrefix,pathReady,pathEnd,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,
    MachineState.getReg,MachineState.setPC,pcAt,ip,signExtend13,few,more] <;> simp_all

theorem load_byte (s : MachineState) (pc : s.pc=pcAt 41) (valid : accessValid (s.getReg .x19) 1=true) :
    pathReady s loadByte ∧
    let t:=loaded s
    t.pc=pcAt 38 ∧ t.getReg .x19=s.getReg .x19+1 ∧ t.getReg .x22=s.getReg .x22+8 ∧
    t.getReg .x21=(s.getReg .x21 ||| ((s.getByte (s.getReg .x19)).zeroExtend 64 <<< ((s.getReg .x22).toNat%64))) ∧ t.mem=s.mem := by
  change accessValid (s.regs .x19) 1=true at valid
  simp +decide [loadByte,loaded,pathEnd,pathReady,ordinaryStep,execInstrBr,memoryArgumentsValid,memAccess,
    MachineState.getReg,MachineState.setReg,MachineState.setPC,MachineState.getByte,MachineState.getMem,
    pcAt,pc,signExtend12,signExtend21,valid] <;> simp_all +decide

theorem refill (s : MachineState) (pc : s.pc=pcAt 38) (few : (s.getReg .x22).ult (s.getReg .x6)=true)
    (more : (s.getReg .x19).ult (s.getReg .x20)=true) (valid : accessValid (s.getReg .x19) 1=true) (fuel : Nat) :
    let t:=loaded (s.setPC (pcAt 41))
    execute (image .check) (fuel+8) s false=(do let r←execute (image .check) fuel t false;return r.charge 8 0) ∧
    t.pc=pcAt 38 ∧ t.getReg .x19=s.getReg .x19+1 ∧ t.getReg .x22=s.getReg .x22+8 ∧
    t.getReg .x21=(s.getReg .x21 ||| ((s.getByte (s.getReg .x19)).zeroExtend 64 <<< ((s.getReg .x22).toNat%64))) ∧ t.mem=s.mem := by
  obtain ⟨ok,land⟩:=branches s pc few more
  let u:=s.setPC (pcAt 41)
  obtain ⟨ok',rest⟩:=load_byte u rfl valid
  refine ⟨?_,rest⟩
  have headRun:=path_run .check false s refillPrefix (by decide +kernel) ok (fuel+6)
  have suffix:=path_run .check false u loadByte (by decide +kernel) ok' fuel
  rw [show fuel+8=(fuel+6)+refillPrefix.length by rfl,headRun,land]
  change (do let r←execute (image .check) (fuel+loadByte.length) u false;return r.charge 2 0)=_
  rw [suffix]
  simp only [bind_assoc,pure_bind];apply bind_congr;intro r;congr 1 <;> simp [Execution.charge,loadByte] <;> omega
end CommitGolfCandidate.S5Machine.Reader
