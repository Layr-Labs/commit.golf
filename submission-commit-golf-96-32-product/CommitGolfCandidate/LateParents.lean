import CommitGolfCandidate.LateLeafWrites
import CommitGolfCandidate.CMHalf

namespace CommitGolfCandidate.Late
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- One parent: the compression call, then (at the truncated heights 3..17) the halfword store
clearing the top two bytes of the new node. -/
def writeParent (h : Compression) (s : MachineState) (height p : Nat) :=
  let t := compressAt h s (nodeAddress height (2*p)) (nodeAddress (height+1) p)
  if CutHeight (height+1) then cmZeroTop t (nodeAddress (height+1) p) else t

theorem node_aligned (height p : Nat) : nodeAddress height p % 8 = 0 := by
  unfold nodeAddress levelOffset gapOffset; omega

/-- Reads disjoint from the new node slot do not see the parent write. -/
theorem write_parent_away (h : Compression) (s : MachineState) (height p : Nat)
    (inside : p < levelCount (height+1)) (r n : Nat) (hr : r+n ≤ 2^64)
    (disjoint : r+n ≤ nodeAddress (height+1) p ∨ nodeAddress (height+1) p+32 ≤ r) :
    readBuffer (writeParent h s height p) r n = readBuffer s r n := by
  have b := parent_below_salts (height+1) p inside
  unfold rowBase at b
  have st : readBuffer (compressAt h s (nodeAddress height (2*p)) (nodeAddress (height+1) p)) r n =
      readBuffer s r n := by
    unfold compressAt; exact store_away _ _ _ _ _ (by omega) hr disjoint
  unfold writeParent
  split
  · unfold cmZeroTop
    rw [cm_trunc_store_outside _ _ _ _ (node_aligned _ _) (by omega) hr disjoint, st]
  · exact st

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

theorem write_parent_mem_congr (h : Compression) (s t : MachineState) (height p : Nat) (same : s.mem = t.mem) :
    (writeParent h s height p).mem = (writeParent h t height p).mem := by
  have read : readBuffer s (nodeAddress height (2*p)) 96 = readBuffer t (nodeAddress height (2*p)) 96 := by
    simp only [readBuffer, MachineState.getByte, MachineState.getMem, same]
  have st : (compressAt h s (nodeAddress height (2*p)) (nodeAddress (height+1) p)).mem =
      (compressAt h t (nodeAddress height (2*p)) (nodeAddress (height+1) p)).mem := by
    unfold compressAt store
    rw [read]
    exact write_bits_memory_congr _ _ _ _ same
  unfold writeParent
  split
  · exact cm_set_halfword_mem_congr _ _ st _ _
  · exact st

theorem parent_output (h : Compression) (s : MachineState) (height p : Nat) (a b : Digest)
    (inside : p < levelCount (height+1))
    (left : readBuffer s (nodeAddress height (2*p)) 32 = a)
    (right : readBuffer s (nodeAddress height (2*p+1)) 32 = b)
    (zero : readBuffer s (nodeAddress height (2*p)+64) 32 = 0) :
    readBuffer (writeParent h s height p) (nodeAddress (height+1) p) 32 =
      cut (height+1) (h (parentBlock a b)) := by
  have stored : readBuffer (compressAt h s (nodeAddress height (2*p)) (nodeAddress (height+1) p))
      (nodeAddress (height+1) p) 32 = h (parentBlock a b) := by
    unfold compressAt
    erw [store_read, parent_input s height p a b left right zero]
  have bd := parent_below_salts (height+1) p inside
  unfold rowBase at bd
  unfold writeParent
  split
  · rename_i c
    unfold cmZeroTop
    rw [cm_trunc_store_digest _ _ (node_aligned _ _) (by omega), stored]
    exact (cut_of_cut c _).symm
  · rename_i c
    rw [stored]
    exact (cut_of_not c _).symm

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
  apply write_parent_away h s height p inside
  · unfold rowBase at prev; omega
  · left; unfold nodeAddress; omega

end CommitGolfCandidate.Late
