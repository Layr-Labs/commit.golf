import CommitGolfCandidate.ReconstructedCheckStraight
import CommitGolfCandidate.ReconstructedCheckOrdinary

namespace CommitGolfCandidate.Reconstruction.CheckBranch
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckOrdinary CheckRecorded

def branch (kind : Cond) (a b : Reg) (off : BitVec 13) : Instr :=
  match kind with | .eq=>.BEQ a b off | .ne=>.BNE a b off | .lt=>.BLTU a b off | .ge=>.BGEU a b off

theorem event (o : Oracle) (s : MachineState) (pc dest : Nat) (kind : Cond) (a b : Reg) (off : BitVec 13)
    (bound : pc<796) (pos : s.pc=CommitBlocks.addr pc) (word : CheckStraight.actualAt pc=some (.base (branch kind a b off)))
    (target : CommitBlocks.addr pc + signExtend13 off=CommitBlocks.addr dest) :
    let next:=if kind.test (s.getReg a) (s.getReg b) then CommitBlocks.addr dest else CommitBlocks.addr (pc+1)
    Segment o 1 s (s.setPC next) [] := by
  have f:=CheckStraight.present pc _ bound word s pos
  apply plain o s _ _ f
  rw [CommitBlocks.addr_next]
  cases kind <;> simp [branch,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,Cond.test,pos,target] <;>
    split <;> simp_all

theorem jump (o : Oracle) (s : MachineState) (pc dest : Nat) (off : BitVec 21) (inside : pc<796)
    (pos : s.pc=CommitBlocks.addr pc) (word : CheckStraight.actualAt pc=some (.base (.JAL .x0 off)))
    (target : CommitBlocks.addr pc+signExtend21 off=CommitBlocks.addr dest) :
    Segment o 1 s (s.setPC (CommitBlocks.addr dest)) [] := by
  apply plain o s _ _ (CheckStraight.present pc _ inside word s pos)
  simp [ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,pos,target,MachineState.setReg]

end CommitGolfCandidate.Reconstruction.CheckBranch
