import CommitGolfCandidate.Stage3cCode
import CommitGolfCandidate.Counting
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def Runs (pg : Program) (coins : Bool) (o : Oracle) (s t : MachineState) (steps cyc q : Nat) :=
  ∀ fuel,o.run (execute (image pg) (fuel+steps) s coins)=
    (do let (out,k)←o.run (execute (image pg) fuel t coins);return (out.charge cyc q,q+k))

theorem runs_id (pg : Program) (coins : Bool) (o : Oracle) (s : MachineState) : Runs pg coins o s s 0 0 0 := by
  intro fuel;simp [Execution.charge]

theorem runs_comp {pg coins o s t u n c q m d k}
    (head : Runs pg coins o s t n c q) (tail : Runs pg coins o t u m d k) :
    Runs pg coins o s u (n+m) (c+d) (q+k) := by
  intro fuel
  rw [show fuel+(n+m)=(fuel+m)+n by omega,head,tail]
  simp only [bind_assoc,pure_bind]
  apply bind_congr;rintro ⟨out,x⟩
  simp [Execution.charge,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem runs_pure {pg coins o s t n c}
    (law : ∀ fuel, execute (image pg) (fuel+n) s coins=
      (do let r←execute (image pg) fuel t coins;return r.charge c 0)) : Runs pg coins o s t n c 0 := by
  intro f;rw [law,oracle_run_bind];simp only [oracle_run_pure,pure_bind,Nat.add_zero,Nat.zero_add]

theorem runs_step {pg coins o s t op} (found : fetch (image pg) s=some op) (ok : ordinaryStep s op=some t) :
    Runs pg coins o s t 1 (instructionCycles op) 0 :=
  runs_pure fun fuel=>execute_ordinary_step _ _ _ _ _ _ found ok

end CommitGolfCandidate.Chained.BinaryMachine
