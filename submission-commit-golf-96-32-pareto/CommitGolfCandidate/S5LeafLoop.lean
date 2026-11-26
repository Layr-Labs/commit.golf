import CommitGolfCandidate.S5NextLeaf
namespace CommitGolfCandidate.S5Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
open CommitGolfCandidate.Late (SaltTape)

def controlPrefix (k : Nat) := 28*(k/256)+(k%256)/16+(k%256)/42+(k%256)/128-(if k=LENGTH then 1 else 0)
private theorem slot_cost (j : Fin 255) :
    (j.val+1)/16+(j.val+1)/42+(j.val+1)/128 =
      j.val/16+j.val/42+j.val/128+(updates ⟨j.val,by omega⟩).length :=
  (by decide +kernel : ∀ t : Fin 255, (t.val+1)/16+(t.val+1)/42+(t.val+1)/128 =
     t.val/16+t.val/42+t.val/128+(updates ⟨t.val,by omega⟩).length) j

private theorem prefix_step (k : Nat) (inside : k<LENGTH) : controlPrefix (k+1)=controlPrefix k+tailCount k := by
  by_cases ending : k%256=255
  · have id : slotIndex k=(255:Fin 256):=Fin.ext ending
    simp only [controlPrefix,tailCount,id,ending,branchSteps,ite_true,if_neg (Nat.ne_of_lt inside),
      show (k+1)%256=0 by omega,show (k+1)/256=k/256+1 by omega,
      show (updates (255:Fin 256)).length=4 by decide]
    by_cases done : k+1=LENGTH <;> simp [done] <;> (try split_ifs) <;> omega
  · have small : k%256<255:=by omega
    have notDone : k+1≠LENGTH := by change k<16777216 at inside;change k+1≠16777216;omega
    have step:=slot_cost ⟨k%256,small⟩
    change ((k%256)+1)/16+((k%256)+1)/42+((k%256)+1)/128 =
      k%256/16+k%256/42+k%256/128+(updates (slotIndex k)).length at step
    simp only [controlPrefix,tailCount,if_neg notDone,if_neg (Nat.ne_of_lt inside),if_neg ending,
      Nat.sub_zero,Nat.add_zero,show (k+1)%256=k%256+1 by omega,show (k+1)/256=k/256 by omega]
    omega

private theorem prefix_le (k n : Nat) (room : k+n≤LENGTH) : controlPrefix k≤controlPrefix (k+n) := by
  induction n with
  | zero=>simp
  | succ n ih=>rw [Nat.add_succ,prefix_step _ (by omega)];exact (ih (by omega)).trans (Nat.le_add_right ..)

def controls (k n : Nat) := controlPrefix (k+n)-controlPrefix k
def leafSteps (k n : Nat) :=12*n+controls k n
def leafCycles (k n : Nat) :=40*n+controls k n
private theorem controls_succ (k n : Nat) (room : k+(n+1)≤LENGTH) :
    controls k (n+1)=tailCount k+controls (k+1) n := by
  have inc:=prefix_step k (by omega)
  have hi:=prefix_le (k+1) n (by omega)
  unfold controls;rw [show k+(n+1)=(k+1)+n by omega];omega

def leafFold (h : Compression) : Nat → Nat → MachineState → MachineState
  | 0, _, s => s
  | n+1, k, s => leafFold h n (k+1) (afterLeaf h s k)

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
      simp only [leafSteps, controls_succ k n bound]; omega
    rw [cost, fixed_iteration o s k hi a, ih (k+1) _ (after_regs _ _ _ hi a) (by omega)]
    simp only [leafFold, bind_assoc,pure_bind]
    apply bind_congr
    rintro ⟨out,c⟩
    simp only [Execution.charge,leafCycles,controls_succ k n bound, Nat.mul_add,Nat.mul_succ,Nat.mul_one]
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
    have count : 256*(k/256)+(slotIndex k).val = k := Nat.div_add_mod k 256
    have lo : k < LENGTH := by omega
    have step := executed_leaf_contents h m salt s (k/256) (slotIndex k) (by rw [count]; exact lo) (toRegs a)
      (by rw [count]; exact start)
    rw [count] at step
    have tail := ih (k+1) _ (after_regs h s k lo a) (contents_congr (tail_mem h s k) step) (by omega)
    simpa only [leafFold,show k+1+n=k+(n+1) by omega] using tail

end CommitGolfCandidate.S5Machine
