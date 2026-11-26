import CommitGolfCandidate.LateLeafWrites

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

def writeParent (h : Compression) (s : MachineState) (height p : Nat) :=
  compressAt h s (nodeAddress height (2*p)) (nodeAddress (height+1) p)

theorem parent_input (s : MachineState) (height p : Nat) (a b : Digest)
    (left : readBuffer s (nodeAddress height (2*p)) 32 = a)
    (right : readBuffer s (nodeAddress height (2*p+1)) 32 = b)
    (zero : readBuffer s (nodeAddress height (2*p)+64) 32 = 0) :
    readBuffer s (nodeAddress height (2*p)) 96 = parentBlock a b := by
  let src := nodeAddress height (2*p)
  have r : readBuffer s (src+32) 32 = b := (children_contiguous height p).1 ▸ right
  have hi := read_join s (src+32) 32 32
  change _ = (readBuffer s (src+32) 64).extractLsb' 0 512 at hi
  rw [show src+32+32 = src+64 by omega, zero, r, BitVec.extractLsb'_eq_self] at hi
  have lo := read_join s src 32 64
  change _ = (readBuffer s src 96).extractLsb' 0 768 at lo
  rw [← hi, left, BitVec.extractLsb'_eq_self] at lo
  exact lo.symm

theorem parent_output (h : Compression) (s : MachineState) (height p : Nat) (a b : Digest)
    (left : readBuffer s (nodeAddress height (2*p)) 32 = a)
    (right : readBuffer s (nodeAddress height (2*p+1)) 32 = b)
    (zero : readBuffer s (nodeAddress height (2*p)+64) 32 = 0) :
    readBuffer (writeParent h s height p) (nodeAddress (height+1) p) 32 =
      h (parentBlock a b) := by
  unfold writeParent compressAt
  erw [store_read, parent_input s height p a b left right zero]

theorem gap_mono (i j : Nat) (lt : i < j) : gapOffset i+32 ≤ gapOffset j := by
  unfold gapOffset; omega

theorem parent_separate (s : MachineState) (h : Compression) (height p : Nat)
    (heightOk : height < LOG_LENGTH) (inside : p < levelCount (height+1)) (i : Nat)
    (previous : i < p) :
    readBuffer (writeParent h s height p) (nodeAddress (height+1) i) 32 =
      readBuffer s (nodeAddress (height+1) i) 32 := by
  have hi := parent_below_salts (height+1) p inside
  have prev := parent_below_salts (height+1) i (by omega)
  have m := gap_mono i p previous
  unfold writeParent compressAt
  apply store_away
  · unfold rowBase at hi; omega
  · unfold rowBase at prev; omega
  · left; unfold nodeAddress; omega

end CommitGolfCandidate.Late
