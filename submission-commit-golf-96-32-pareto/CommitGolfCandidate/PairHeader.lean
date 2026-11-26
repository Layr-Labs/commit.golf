import CommitGolfCandidate.PairBatchSteps
import CommitGolfCandidate.PairUpper
namespace CommitGolfCandidate.PairCap.Batch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 12000

def lengthBranch (s : MachineState) := execInstrBr (lengthState (dispatched s)) (.BNE .x6 .x17 7628)
def initialRows (s : MachineState) := readyState (lengthBranch s)

private theorem gate (s : MachineState) (batch : s.getReg .x16 = 128) :
    (dispatched s).pc = 4984 ∧ (lengthState (dispatched s)).pc = 4996 ∧
    (lengthState (dispatched s)).getReg .x6 = 71680 ∧
    (lengthState (dispatched s)).getReg .x17 = s.getReg .x17 := by
  simp [dispatched,dispatchPrefix,dispatchOps,lengthState,lengthOps,batch,execInstrBr,
    MachineState.setPC,MachineState.setReg,MachineState.getReg,signExtend12] at *
  simp [batch]

private theorem decideBranch (s : MachineState) (batch : s.getReg .x16 = 128) :
    (lengthBranch s).pc = if s.getReg .x17 = 71680 then 5000 else 4432 := by
  obtain ⟨_,pc,reg6,reg17⟩ := gate s batch
  simp only [lengthBranch,execInstrBr,reg6,reg17]
  by_cases eqn : s.getReg .x17 = 71680
  · simp [eqn,pc,MachineState.setPC]
  · have ne : s.getReg .x17 ≠ 71680#64 := eqn
    simp [Ne.symm ne,ne,pc,MachineState.setPC,signExtend13]

theorem lengthReject (s : MachineState) (pc : s.pc = 4096) (batch : s.getReg .x16 = 128)
    (wrong : s.getReg .x17 ≠ 71680) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (14+fuel) s coins =
      pure ⟨.failure,top_checkExitState (lengthBranch s) false,14,0⟩ := by
  have pre := gate s batch
  have target : (lengthBranch s).pc = 4432 := by rw [decideBranch s batch,if_neg wrong]
  rw [show 14+fuel = 7+(3+((3+fuel)+1)) by omega,patchedDispatch s pc,lengthRun _ pre.1,
    edge225 _ pre.2.1]
  erw [top_check_exit (lengthBranch s) false target]
  rfl

theorem headerRun (s : MachineState) (pc : s.pc = 4096) (batch : s.getReg .x16 = 128)
    (size : s.getReg .x17 = 71680) (fuel : Nat) (coins : Bool) :
    execute (submission.image .check) (17+fuel) s coins =
      (do let next ← execute (submission.image .check) fuel (initialRows s) coins
          return next.charge 17 0) := by
  have pre := gate s batch
  have target : (lengthBranch s).pc = 5000 := by rw [decideBranch s batch,if_pos size]
  rw [show 17+fuel = 7+(3+((6+fuel)+1)) by omega,patchedDispatch s pc,lengthRun _ pre.1,
    edge225 _ pre.2.1]
  erw [readyRun (lengthBranch s) target]
  simp [initialRows,Execution.charge,← Nat.add_assoc]

theorem rowsRegisters (s : MachineState) (batch : s.getReg .x16 = 128) (size : s.getReg .x17 = 71680) :
    let r := initialRows s
    r.pc=5024 ∧ r.getReg .x27=128 ∧ r.getReg .x24=s.getReg .x13 ∧
    r.getReg .x8=s.getReg .x14 ∧ r.getReg .x25=s.getReg .x15 ∧
    r.getReg .x26=s.getReg .x11 ∧ r.getReg .x19=s.getReg .x15+67584 ∧
    r.getReg .x21=256 ∧ r.getReg .x30=16 ∧ r.mem=s.mem := by
  have pc := decideBranch s batch
  simp only [size,if_pos rfl] at pc
  simp [initialRows,readyState,readyOps,execInstrBr,MachineState.setPC,pc,signExtend12,
    MachineState.setReg,MachineState.getReg,lengthBranch,lengthState,lengthOps,dispatched,
    dispatchPrefix,dispatchOps] at batch size ⊢
  simp [batch,size,MachineState.setPC,MachineState.getReg,MachineState.setReg]

end CommitGolfCandidate.PairCap.Batch
