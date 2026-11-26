import CommitGolfCandidate.LateLeafNext
import CommitGolfCandidate.LateLeafContents

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def leafFold (h : Compression) : Nat → Nat → MachineState → MachineState
  | 0, _, s => s
  | n+1, k, s => leafFold h n (k+1) (afterLeaf h s k)

def controls (k n : Nat) := ((k+n)/16-k/16) + ((k+n)/16-k/16) + 3*((k+n)/32-k/32)
def leafSteps (k n : Nat) := 12*n + controls k n
def leafCycles (k n : Nat) := 40*n + controls k n

private theorem tail_formula (k : Nat) :
    tailCount k = (if k%16=15 then 1 else 0) + (if k%16=15 then 1 else 0) +
      (if k%32=31 then 3 else 0) := by
  have rem : k%32%16 = k%16 := by omega
  by_cases a : k%16=15 <;> by_cases b : k%32=31 <;>
    simp [tailCount,updates,slotIndex,rem,a,b] <;> omega

private theorem controls_succ (k n : Nat) : controls k (n+1) = tailCount k + controls (k+1) n := by
  rw [tail_formula]; unfold controls
  by_cases a : k%16=15 <;> by_cases b : k%32=31 <;>
    simp only [a,b,↓reduceIte] <;> omega

theorem leaf_fold_run (o : Oracle) (n k : Nat) (s : MachineState) (a : AtLeaf s k)
    (bound : k+n ≤ LENGTH) (fuel : Nat) :
    o.run (execute commitImage (fuel+leafSteps k n) s true) =
      (do let (out,c) ← o.run (execute commitImage fuel (leafFold o.compression n k s) true)
          return (out.charge (leafCycles k n) (4*n),4*n+c)) := by
  induction n generalizing k s with
  | zero => simp [leafFold,leafSteps,leafCycles,controls,Execution.charge]
  | succ n ih =>
    have hi : k < LENGTH := by omega
    have cost : fuel+leafSteps k (n+1) =
        (fuel+leafSteps (k+1) n)+(12+tailCount k) := by
      simp only [leafSteps, controls_succ]; omega
    rw [cost, fixed_iteration o s k hi a, ih (k+1) _ (after_regs _ _ _ hi a) (by omega)]
    simp only [leafFold, bind_assoc,pure_bind]
    apply bind_congr
    rintro ⟨out,c⟩
    simp only [Execution.charge,leafCycles,controls_succ, Nat.mul_add,Nat.mul_succ,Nat.mul_one]
    ac_rfl

theorem leaf_fold_registers (h : Compression) (n k : Nat) (s : MachineState) (a : AtLeaf s k)
    (bound : k+n ≤ LENGTH) : AtLeaf (leafFold h n k s) (k+n) := by
  induction n generalizing k s with
  | zero => simpa [leafFold] using a
  | succ n ih =>
    have next := ih (k+1) _ (after_regs h s k (by omega) a) (by omega)
    simpa only [leafFold, show k+1+n=k+(n+1) by omega] using next

theorem leaf_fold_contents (h : Compression) (m : Message) (salt : SaltTape)
    (n k : Nat) (s : MachineState) (a : AtLeaf s k) (start : LeafContents h m salt k s)
    (bound : k+n ≤ LENGTH) : LeafContents h m salt (k+n) (leafFold h n k s) := by
  induction n generalizing k s with
  | zero => simpa only [Nat.add_zero,leafFold] using start
  | succ n ih =>
    have count : 32*(k/32)+(slotIndex k).val = k := Nat.div_add_mod k 32
    have lo : k < LENGTH := by omega
    have step := executed_leaf_contents h m salt s (k/32) (slotIndex k) (by rw [count]; exact lo) (toRegs a)
      (by rw [count]; exact start)
    rw [count] at step
    have tail := ih (k+1) _ (after_regs h s k lo a) (contents_congr (tail_mem h s k) step) (by omega)
    simpa only [leafFold,show k+1+n=k+(n+1) by omega] using tail

end CommitGolfCandidate.Late
