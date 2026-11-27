import CommitGolfCandidate.Stage3cCheckMask
import CommitGolfCandidate.Stage3cCheckMaskNumber
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf Chained CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000
def maskSetup : PathCode := [(217,.ADDI .x6 .x31 3872),(218,.ADDI .x7 .x0 1),(219,.SLL .x7 .x7 .x6),(220,.ADDI .x7 .x7 4095)]
def maskWrite : PathCode := [(221,.LHU .x28 .x12 28),(222,.AND .x28 .x28 .x7),(223,.SW .x12 .x28 28)]
def preparedMask (s : MachineState) := pathEnd s maskSetup
def writtenMask (s : MachineState) := pathEnd s maskWrite

theorem mask_frame (s : MachineState) (pc : s.pc=pcAt 217) :
    pathReady s maskSetup ∧ (preparedMask s).pc=pcAt 221 ∧ (preparedMask s).mem=s.mem ∧ (preparedMask s).getReg .x12=s.getReg .x12 := by
  let a:=execInstrBr s (.ADDI .x6 .x31 3872)
  let b:=execInstrBr a (.ADDI .x7 .x0 1)
  let c:=execInstrBr b (.SLL .x7 .x7 .x6)
  have pa : a.pc=pcAt 218:=by change s.pc+4=_;rw [pc];rfl
  have pb : b.pc=pcAt 219:=by change a.pc+4=_;rw [pa];rfl
  have pcc : c.pc=pcAt 220:=by change b.pc+4=_;rw [pb];rfl
  have pd : (preparedMask s).pc=pcAt 221:=by change c.pc+4=_;rw [pcc];rfl
  have ready : pathReady s maskSetup:=⟨pc,rfl,rfl,pa,rfl,rfl,pb,rfl,rfl,pcc,rfl,rfl,True.intro⟩
  exact ⟨ready,pd,rfl,rfl⟩
end CommitGolfCandidate.Chained.BinaryMachine.Check
