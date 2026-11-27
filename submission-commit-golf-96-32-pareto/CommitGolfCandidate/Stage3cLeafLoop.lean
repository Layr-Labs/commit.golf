import CommitGolfCandidate.Stage3cPtrTail
import CommitGolfCandidate.Stage3cLeafContents
namespace CommitGolfCandidate.Chained.BinaryMachine
open CommitGolf Late CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option Elab.async false
def leafFold (h : Compression) : Nat → Nat → MachineState → MachineState
  | 0, _, s => s
  | n+1, k, s => leafFold h n (k+1) (afterLeaf h s k)

theorem leafFoldRun (o : Oracle) (n k : Nat) (s : MachineState) (regs : AtLeaf s k) (bound:k+n≤LENGTH) :
    Runs .commit true o s (leafFold o.compression n k s) (leafSteps k n) (leafCycles k n) (4*n) := by
  induction n generalizing s k with
  | zero=>simpa only [leafFold,leafSteps,leafCycles,Nat.add_zero,Nat.mul_zero,Nat.sub_self] using runs_id .commit true o s
  | succ n ih=>
    have hi:k<LENGTH:=by omega
    have e:=runs_comp (fixed_iteration o regs hi) (ih (k+1) _ (after_at _ regs hi) (by omega))
    have eff:=controls_succ k n bound
    unfold controls at eff
    have ns:leafSteps k (n+1)=12+tailCount k+leafSteps (k+1) n:=by unfold leafSteps;omega
    have nc:leafCycles k (n+1)=40+tailCount k+leafCycles (k+1) n:=by unfold leafCycles;omega
    rw [ns,nc,show 4*(n+1)=4+4*n by omega];exact e

theorem leaf_fold_run (o : Oracle) (n k : Nat) (s : MachineState) (a : AtLeaf s k)
    (bound:k+n≤LENGTH) (fuel : Nat) :
    o.run (execute commitImage (fuel+leafSteps k n) s true) =
      (do let (out,q)←o.run (execute commitImage fuel (leafFold o.compression n k s) true)
          return (out.charge (leafCycles k n) (4*n),4*n+q)) := leafFoldRun o n k s a bound fuel

theorem leaf_fold_registers (h : Compression) (n k : Nat) (s : MachineState) (a : AtLeaf s k)
    (bound:k+n≤LENGTH) : AtLeaf (leafFold h n k s) (k+n) := by
  induction n generalizing k s with
  | zero=>exact a
  | succ n ih=>exact (show (k+1)+n=k+(n+1) by omega) ▸ ih (k+1) _ (after_at h a (by omega)) (by omega)

theorem leaf_fold_contents (h : Compression) (m : Message) (salt : SaltTape) (n k : Nat) (s : MachineState)
    (a : AtLeaf s k) (old : LeafContents h m salt k s) (bound:k+n≤LENGTH) :
    LeafContents h m salt (k+n) (leafFold h n k s) := by
  induction n generalizing k s with
  | zero=>exact old
  | succ n ih=>
    have hi:k<LENGTH:=by omega
    have next:=executed_leaf_contents h m salt s k hi a.toLeafRegs old
    exact (show (k+1)+n=k+(n+1) by omega) ▸ ih (k+1) _ (after_at h a hi) next (by omega)
end CommitGolfCandidate.Chained.BinaryMachine
