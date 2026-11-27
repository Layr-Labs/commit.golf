import CommitGolfCandidate.Stage3cCheckCells
set_option Elab.async false
namespace CommitGolfCandidate.Chained.BinaryMachine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Digest)
theorem pair_cells (s : MachineState) (a b : Digest)
    (cells : CellData s (setCell (setCell (fun _=>0) 0 a) 1 b)) : readBuffer s rowBuf 96=Late.parentBlock a b := by
  let f:=setCell (setCell (fun _=>0) 0 a) 1 b
  have top : f 2=0:=by simp only [f,setCell,Nat.reduceEqDiff,ite_false]
  have right : f 1=b:=by simp only [f,setCell,ite_true]
  have left : f 0=a:=by simp only [f,setCell,Nat.reduceEqDiff,ite_false,ite_true]
  have high:=congrArg₂ (fun (u v : Digest)=>u++v) top right
  exact (cells_row s f cells).trans (congrArg₂ (fun (u : BitVec 512) (v : Digest)=>u++v) high left)
end CommitGolfCandidate.Chained.BinaryMachine.Check
