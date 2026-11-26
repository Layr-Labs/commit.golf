import CommitGolfCandidate.S4Pieces
import CommitGolfCandidate.S4ReadField
namespace CommitGolfCandidate.S4.Machine
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (pcAt)

def dwords (n : Nat) := List.replicate n Width.dword
def doubleCopies (sr dr : Reg) (si di n : Nat) := moveCode sr dr si di (dwords n)
private theorem short : ∀ j : Fin 257,signExtend12 (BitVec.ofNat 12 j.val)=W j.val := by
  set_option maxRecDepth 4000 in decide
theorem dwordSize (n : Nat) : bytesOf (dwords n)=8*n := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [dwords,List.replicate_succ];change 8+bytesOf (dwords n)=_;rw [ih,Nat.mul_succ,Nat.add_comm]

private theorem validDwords (src dst a b n : Nat) (al : (src+a)%8=0) (dl : (dst+b)%8=0)
    (immS : a+8*n≤256) (immD : b+8*n≤256)
    (boundS : src+a+8*n≤MEMORY_BYTES) (boundD : dst+b+8*n≤MEMORY_BYTES) :
    validOffsets src dst a b (dwords n) := by
  induction n generalizing a b with
  | zero=>trivial
  | succ k ih=>
    rw [dwords,List.replicate_succ,validOffsets]
    refine ⟨⟨by change src+a+8≤MEMORY_BYTES;omega,al⟩,⟨by change dst+b+8≤MEMORY_BYTES;omega,dl⟩,
      short ⟨a,by omega⟩,short ⟨b,by omega⟩,?_⟩
    apply ih (a+8) (b+8) <;> omega

theorem dwordBlock (c : Code) (s : MachineState) (sr dr : Reg) (pc src dst a b n : Nat)
    (neS : Reg.x6≠sr) (neD : Reg.x6≠dr) (start : s.pc=pcAt pc) (bound : pc+2*n≤c.count)
    (code : Matches c pc (doubleCopies sr dr a b n)) (r1 : s.getReg sr=W src) (r2 : s.getReg dr=W dst)
    (al : (src+a)%8=0) (dl : (dst+b)%8=0) (immS : a+8*n≤256) (immD : b+8*n≤256)
    (bs : src+a+8*n≤MEMORY_BYTES) (bd : dst+b+8*n≤MEMORY_BYTES) (out : src+a+8*n≤dst+b ∨ dst+b+8*n≤src+a) :
    AfterCopy c pc s (copyBlock sr dr a b (dwords n) s) (src+a) (dst+b) (8*n) (2*n) := by
  have e:=copyBlockRun c sr dr src dst a b pc (dwords n) s neS neD r1 r2 start
    (by simpa only [dwords,List.length_replicate] using bound)
    (validDwords _ _ _ _ _ al dl immS immD bs bd) (by rw [dwordSize];exact bs) (by rw [dwordSize];exact out) code
  rw [dwordSize,show (dwords n).length=n from List.length_replicate] at e;exact e
end CommitGolfCandidate.S4.Machine
