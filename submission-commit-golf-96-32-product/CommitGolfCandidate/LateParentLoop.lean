import CommitGolfCandidate.LateParentFrame
import CommitGolfCandidate.LateTreeMemory

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def parentFold (h : Compression) (s : MachineState) (d : Fin 24) : Nat → MachineState
  | 0 => s
  | p+1 => parentTick h (parentFold h s d p) d p

theorem parents_frame (h : Compression) (s : MachineState) (d : Fin 24)
    (start : ParentFrame s d 0) (n : Nat) (le : n ≤ levelSize d) :
    ParentFrame (parentFold h s d n) d n := by
  induction n with
  | zero => exact start
  | succ n ih => exact tick_frame h (by omega) (ih (by omega))

theorem parents_memory (h : Compression) (s : MachineState) (d : Fin 24)
    (start : ParentFrame s d 0) (n : Nat) (le : n ≤ levelSize d) :
    (parentFold h s d n).mem = (fillLevel h d n s).mem := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let t := parentFold h s d n
    let u := fillLevel h d n s
    have old : t.mem = u.mem := ih (by omega)
    have read := read_congr_mem t u (nodeAddress d (2*n)) 96 old
    apply (tick_mem h (parents_frame h s d start n (by omega)).toParentRegs (by exact Nat.lt_of_lt_of_le (Nat.lt_succ_self n) le)).trans
    change (store t _ (h (readBuffer t _ 96))).mem = (store u _ (h (readBuffer u _ 96))).mem
    rw [read]
    exact write_bits_memory_congr _ _ _ _ old

def levelSteps (n : Nat) := 3*n+4*(n/32)
def levelCycles (n : Nat) := 10*n+4*(n/32)

theorem parents_run (o : Oracle) (s : MachineState) (d : Fin 24) (start : ParentFrame s d 0)
    (n : Nat) (le : n≤levelSize d) (fuel : Nat) :
    o.run (execute commitImage (fuel+levelSteps n) s true) =
      (do let (out,c) ← o.run (execute commitImage fuel (parentFold o.compression s d n) true)
          return (out.charge (levelCycles n) n,n+c)) := by
  induction n generalizing fuel with
  | zero => simp [levelSteps,levelCycles,parentFold,Execution.charge]
  | succ n ih =>
    have hi : n < levelSize d := by omega
    have frame := parents_frame o.compression s d start n (by omega)
    have pc := frame.pc
    rw [parentNextPC,if_pos hi] at pc
    have steps : fuel+levelSteps (n+1) =
        (fuel+(3+if n%32=31 then 4 else 0))+levelSteps n := by unfold levelSteps; split <;> omega
    rw [steps,ih (by omega), parent_tick_run o frame.toParentRegs hi pc]
    simp only [bind_assoc,pure_bind,parentFold,Execution.charge]
    apply bind_congr
    rintro ⟨out,c⟩
    have price : levelCycles (n+1) = levelCycles n + (10 + if n%32=31 then 4 else 0) := by
      unfold levelCycles; split <;> omega
    simp only [price,Nat.succ_eq_add_one, Nat.add_assoc]

end CommitGolfCandidate.Late
