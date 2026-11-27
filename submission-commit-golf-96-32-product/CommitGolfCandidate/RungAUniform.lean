import CommitGolfCandidate.R4CommitBase
import CommitGolfCandidate.RungAInterface
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option Elab.async false
set_option maxRecDepth 12000
set_option maxHeartbeats 1200000
attribute [local irreducible] execute readBuffer

private theorem charge_eq (price : Nat) (p : 58721306≤price) (s : MachineState) :
    (commitExec (price-58721306) s).charge 58721306 0=commitExec price s := by
  have total : 58721306+(price-58721306)=price:=by omega
  simp only [commitExec,Execution.charge,Nat.zero_add,total]

theorem uniform (o : Oracle) (img : Image) (init : MachineState) (fuel : Nat)
    (one : Tape→MachineState) (end_ : Tape→MachineState) (price : Nat) (hpp : 58721306≤price)
    (pre : o.run (execute img (16778266+fuel) init true) =ᵈ
        (($ᵗ Tape) >>= fun r=>(fun x : Execution×Nat=>(x.1.charge 58721306 0,x.2)) <$> o.run (execute img fuel (one r) true)))
    (finish : ∀ r,o.run (execute img fuel (one r) true)=pure (commitExec (price-58721306) (end_ r),commitCalls)) :
    o.run (execute img (16778266+fuel) init true) =ᵈ (($ᵗ Tape) >>= fun r=>pure (commitExec price (end_ r),commitCalls)) := by
  refine pre.trans ?_
  apply EvalDistEq.bind_right
  intro r;rw [finish,map_pure,charge_eq _ hpp]

end CommitGolfCandidate.RungA
