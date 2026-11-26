import CommitGolfCandidate.LateLeafWrites
import CommitGolfCandidate.S4Model
namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def writeParent (H : Compression) (s : MachineState) (h p : Nat) := compressAt H s (rowAddress h p) (nodeAddress (h+1) p)
theorem readTriple (s : MachineState) (a : Nat) :
    readBuffer s a 96=readBuffer s (a+64) 32 ++ readBuffer s (a+32) 32 ++ readBuffer s a 32 := by
  have hi:=read_join s (a+32) 32 32
  change _=(readBuffer s (a+32) 64).extractLsb' 0 512 at hi
  rw [show a+32+32=a+64 by omega,BitVec.extractLsb'_eq_self] at hi
  have lo:=read_join s a 32 64
  change _=(readBuffer s a 96).extractLsb' 0 768 at lo
  rw [←hi,BitVec.extractLsb'_eq_self] at lo;exact lo.symm

theorem gap_mono (i j : Nat) (hi : i<j) : gapOffset i+32≤gapOffset j := by unfold gapOffset;omega
theorem parent_separate (s : MachineState) (H : Compression) (height p : Nat)
    (ht : height < LOG_LENGTH) (inside : p < levelCount (height+1)) (i : Nat) (prev : i<p) :
    readBuffer (writeParent H s height p) (nodeAddress (height+1) i) 32=readBuffer s (nodeAddress (height+1) i) 32 := by
  have b:=parent_below_salts _ _ inside
  have c:=parent_below_salts (height+1) i (by omega)
  unfold writeParent compressAt
  apply store_away
  · unfold rowBase at b;omega
  · unfold rowBase at c;omega
  · left;rw [binaryAddress,binaryAddress];have:=gap_mono i p prev;omega
end CommitGolfCandidate.Late
