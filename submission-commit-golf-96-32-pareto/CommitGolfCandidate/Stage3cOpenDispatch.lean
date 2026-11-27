import CommitGolfCandidate.Stage3cOpenFrame
import CommitGolfCandidate.Stage3cOpenCode
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def dispatch (batch : Bool) : PathCode :=
  [(0,.BNE .x16 .x0 20),(5,.ADDI .x6 .x0 128),(6,.BEQ .x16 .x6 8)]++
    if batch then [] else [(7,.JAL .x0 1444)]

theorem dispatch_run (s : MachineState) (pc : s.pc=pcAt 0) (nonempty : s.getReg .x16≠0)
    (batch : Bool) (size : (s.getReg .x16==128)=batch) :
    let path:=dispatch batch
    let t:=pathEnd s path
    Runs s t path.length path.length ∧ t.pc=pcAt (if batch then 8 else 368) ∧ t.mem=s.mem ∧
      ∀ r, r≠.x6→t.getReg r=s.getReg r := by
  have layout : (dispatch batch).all (matchesWord .opening) := by cases batch <;> decide +kernel
  change s.regs .x16≠0 at nonempty
  change (s.regs .x16==128#64)=batch at size
  have branch : pathReady s (dispatch batch) ∧ (pathEnd s (dispatch batch)).pc=pcAt (if batch then 8 else 368) ∧
      (pathEnd s (dispatch batch)).mem=s.mem := by
    cases batch
    · have ne : s.regs .x16≠128#64 := by simpa using size
      simp +decide [dispatch,pathReady,pathEnd,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,pcAt,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,nonempty,ne,signExtend12,signExtend13,signExtend21] <;> simp_all +decide
    · have eq:=beq_iff_eq.mp size
      simp +decide [dispatch,pathReady,pathEnd,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pc,pcAt,
        MachineState.getReg,MachineState.setReg,MachineState.setPC,eq,nonempty,signExtend12,signExtend13] <;> simp_all +decide
  refine ⟨path_run _ true _ _ layout branch.1,branch.2.1,branch.2.2,?_⟩
  intro r ne
  by_cases zero : r=.x0
  · subst r;rfl
  · apply path_keeps_reg
    cases batch <;> cases r <;> first | decide | contradiction
end CommitGolfCandidate.Chained.BinaryMachine.Open
