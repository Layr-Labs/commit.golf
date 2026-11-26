import CommitGolfCandidate.LateOpenPathStep

namespace CommitGolfCandidate.Late.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def walk : Nat → MachineState → MachineState
  | 0,s => s | n+1,s => walk n (oneSibling s)

structure WalkResult (s : MachineState) (tree : Levels) (i : Index) (d l out n : Nat) : Prop where
  run : Runs s (walk n s) (19*n) (19*n)
  pc : (walk n s).pc=pcAt (if l+n<d then 38 else 57)
  frame : PathFrame (walk n s) i d (l+n) out
  anchor : Keeps s (walk n s)
  bytes : Written s (walk n s) (out+32*l) (pathBytes tree i l n)

theorem walk_path (s : MachineState) (tree : Levels) (salts : SaltTape) (xs : List Index)
    (i : Index) (d l out n : Nat) (h : l+n≤d) (depth : d≤LOG_LENGTH)
    (pc : s.pc=pcAt (if l<d then 38 else 57)) (f : PathFrame s i d l out)
    (src : Sources s xs tree salts) (size : xs.length≤LENGTH)
    (high : proofBase≤out) (aligned : out%8=0) (bound : out+32*d≤MEMORY_BYTES) : WalkResult s tree i d l out n := by
  induction n generalizing l s with
  | zero => exact ⟨Runs.refl s,by simpa only [walk,Nat.add_zero] using pc,f,fun _ _ => rfl,Written.empty s _⟩
  | succ n ih =>
    have lt : l<d := by omega
    rw [if_pos lt] at pc
    let bs := bytes (n:=32) (node tree l (mate i l))
    have len : bs.length=32 := by simp [bs,bytes]
    have one := sibling_run s tree i d l out lt depth pc f
      (src.node l (by omega) _ (mate_bound i l (by omega))) high aligned bound
    have valid := src.after size (out+32*l) bs.length one.bytes.outside (by omega) (by omega) (by omega)
    have tail := ih (oneSibling s) (l+1) (by omega) one.pc one.frame valid
    have sumEq : l+1+n=l+(n+1) := by omega
    have nxt : out+32*l+bs.length=out+32*(l+1) := by omega
    have second : Written (oneSibling s) (walk n (oneSibling s)) (out+32*l+bs.length) (pathBytes tree i (l+1) n) :=
      nxt.symm ▸ tail.bytes
    refine ⟨?_,by simpa only [walk,sumEq] using tail.pc,by simpa only [walk,sumEq] using tail.frame,
      one.common.then tail.anchor,?_⟩
    · simpa only [walk,Nat.mul_succ,Nat.add_comm 19 (19*n)] using one.run.trans tail.run
    · rw [path_cons]
      have length : (bytes (n:=32) (node tree l (mate i l))).length=32 := len
      exact one.bytes.append second (by rw [length]; omega) (by rw [path_len];omega) (by rw [length];omega)

end CommitGolfCandidate.Late.Open
