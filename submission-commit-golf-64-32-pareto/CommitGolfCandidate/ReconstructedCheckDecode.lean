import CommitGolfCandidate.ReconstructedCheckLink

namespace CommitGolfCandidate.Reconstruction.CheckDecode
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckLink
set_option maxRecDepth 9000
set_option maxHeartbeats 900000

def same : Option Instruction→Instruction→Bool
  | some (.base x),.base y=>decide (x=y)
  | some (.word a b c d),.word e f g h=>decide (a=e ∧ b=f ∧ c=g ∧ d=h)
  | some (.sraiw a b c),.sraiw d e f=>decide (a=d ∧ b=e ∧ c=f)
  | _,_=>false

theorem same_sound {i : Option Instruction} {op : Instruction} (h : same i op=true) : i=some op := by
  cases i with
  | none=>cases op <;> contradiction
  | some x=>cases x <;> cases op <;> simp_all [same]

def checked (pc : Nat) : List CheckLink.Op→Bool
  | []=>true
  | op::ops=>if h : pc<796 then
    same (decodeInstruction (Artifact.checkCode.get 32 ⟨pc,h⟩)) op.instr && checked (pc+1) ops
  else false

theorem sound (ops : List CheckLink.Op) (pc : Nat) (ok : checked pc ops=true) : Decoded ops (CommitBlocks.addr pc) := by
  induction ops generalizing pc with
  | nil=>trivial
  | cons op ops ih=>
    by_cases h : pc<796
    · simp only [checked,h,dite_true,Bool.and_eq_true] at ok
      refine ⟨?_,?_⟩
      · intro s addr
        rw [fetch_packed image Artifact.checkCode rfl _ h (by omega) s addr]
        exact same_sound ok.1
      · have p : CommitBlocks.addr (pc+1)=CommitBlocks.addr pc+4 := by
          unfold CommitBlocks.addr;rw [show 4096+4*(pc+1)=(4096+4*pc)+4 by omega,BitVec.ofNat_add];rfl
        rw [←p];exact ih (pc+1) ok.2
    · simp [checked,h] at ok

end CommitGolfCandidate.Reconstruction.CheckDecode
