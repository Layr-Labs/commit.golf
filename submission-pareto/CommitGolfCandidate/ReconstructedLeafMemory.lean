import CommitGolfCandidate.ReconstructedCommitWrite

namespace CommitGolfCandidate.Reconstruction.LeafMemory
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype (Memory Words window writeWindow writeWord)
open CommitWindows

def Agrees (m n : Memory) := ∀ w < 2^33, m w = n w

private theorem bound (i : Index) : 512 ≤ entryStart i ∧ entryStart i+32 ≤ 2^33 := by
  have n : i.val < 2^24 := i.isLt
  unfold entryStart; omega

theorem window_congr {m n : Memory} (same : Agrees m n) {w count : Nat} (fits : w+count ≤ 2^33) :
    (window m w : Words count) = window n w := by
  funext j
  exact same _ (by have := j.isLt; omega)

theorem write_window {m n : Memory} (same : Agrees m n) (w : Nat) {len : Nat} (v : Words len) :
    Agrees (writeWindow m w v) (writeWindow n w v) := by
  intro j hj
  unfold writeWindow
  split
  · rfl
  · exact same _ hj

theorem write_word {m n : Memory} (same : Agrees m n) (w : Nat) (v : Word) :
    Agrees (writeWord m w v) (writeWord n w v) := by
  intro j hj
  unfold writeWord
  split
  · rfl
  · exact same _ hj

def raw (s : MachineState) (i : Index) (a : BitVec 1600) :=
  writeBits s (wordAddress (entryStart i-4)) a

def tapeAfter (s : MachineState) (i : Index) (a b : BitVec 1600) :=
  writeBits (raw s i a) (wordAddress (entryStart i-15)) b

theorem raw_words (s : MachineState) (i : Index) (a : BitVec 1600) :
    Agrees (memoryView (raw s i a)) (writeWindow (memoryView s) (entryStart i-4) (replyWords a)) := by
  intro w hw
  exact permutation_write_memory _ _ _ a (by have := bound i; omega) hw

theorem tape_words (s : MachineState) (i : Index) (a tape : BitVec 1600) :
    Agrees (memoryView (tapeAfter s i a tape)) (generatedFirst (memoryView s) i a tape) := by
  intro w hw
  exact (permutation_write_memory _ _ _ tape (by have := bound i; omega) hw).trans
    (write_window (raw_words s i a) (entryStart i-15) (replyWords tape) w hw)

def tagZero (s : MachineState) (i : Index) :=
  let p := entryStart i+7
  (s.setMem (wordAddress p) (pinnedPositionTag i)).setByte (BitVec.ofNat 64 (8*(p+2)+7)) 0

/-- After the generator write, SD writes the tag and SB clears the last salt byte.
The following query therefore has exactly the pinned leaf input on the actual machine. -/
theorem zero_second (s : MachineState) (i : Index) (a tape : BitVec 1600) :
    window (memoryView (tagZero (tapeAfter s i a tape) i)) (entryStart i+7) =
      pinnedSecondInput i (zeroNonce tape) (replyWords a) (window (memoryView s) (entryStart i)) := by
  let p := entryStart i+7
  let t := tapeAfter s i a tape
  let u := t.setMem (wordAddress p) (pinnedPositionTag i)
  let m := generatedFirst (memoryView s) i a tape
  have h := bound i
  have same : Agrees (memoryView t) m := tape_words s i a tape
  have tagged : Agrees (memoryView u) (writeWord m p (pinnedPositionTag i)) := by
    intro w hw
    exact (memory_at_store (by dsimp [p]; omega) (by omega)).trans
      (write_word same p (pinnedPositionTag i) w hw)
  have high : memoryView u (p+2) = m (p+2) := by
    rw [tagged (p+2) (by dsimp [p]; omega)]
    simp [writeWord]
  have both : Agrees (memoryView (tagZero t i)) (firstHeader (memoryView s) i a tape) := by
    intro w hw
    have out := CommitWrite.clear_salt_byte u (p+2) w (by dsimp [p]; omega) (by omega)
    rw [high] at out
    exact out.trans (write_word tagged (p+2) (m (p+2) &&& 0x00ffffffffffffff) w hw)
  exact (window_congr both (by omega)).trans (lane_zero_input ..)

def tagLater (s : MachineState) (i : Index) (low high : Word) :=
  let p := entryStart i+7
  (((s.setMem (wordAddress p) (pinnedPositionTag i)).setMem (wordAddress (p+1)) low).setMem
    (wordAddress (p+2)) high).setByte (BitVec.ofNat 64 (8*(p+2)+7)) 0

def nonce (low high : Word) : Words 2 := fun j =>
  if j.val = 0 then low else high &&& 0x00ffffffffffffff

theorem tag_window (mem : Memory) (i : Index) (a : BitVec 1600) (lo hi : Word) :
    let p := entryStart i+7
    let m := writeWindow mem (entryStart i-4) (replyWords a)
    window (writeWord (writeWord (writeWord m p (pinnedPositionTag i)) (p+1) lo)
      (p+2) (hi &&& 0x00ffffffffffffff)) p =
      pinnedSecondInput i (nonce lo hi) (replyWords a) (window mem (entryStart i)) := by
  dsimp only
  funext j
  have room := bound i
  by_cases hdr : j.val < 3
  · have cases3 : j.val=0 ∨ j.val=1 ∨ j.val=2 := by omega
    rcases cases3 with e|e|e <;> simp [window,writeWord,pinnedSecondInput,nonce,e]
  · have nz : j.val ≠ 0 := by omega
    have p0 : entryStart i+7+j.val ≠ entryStart i+7 := by omega
    have p1 : entryStart i+7+j.val ≠ entryStart i+7+1 := by omega
    have p2 : entryStart i+7+j.val ≠ entryStart i+7+2 := by omega
    simp only [window,writeWord,p0,p1,p2,ite_false,pinnedSecondInput,nz,hdr,dite_false,writeWindow]
    by_cases mid : j.val < 14
    · rw [dif_pos (by omega),dif_pos mid]
      apply congrArg (replyWords a)
      apply Fin.ext
      change entryStart i+7+j.val-(entryStart i-4) = j.val+11
      omega
    · rw [dif_neg (by omega),dif_neg mid]
      congr 1 <;> omega

/-- Each later lane stages its two selected generator words through registers. Clearing
the high byte implements the same 120-bit nonce layout for all eleven other lanes. -/
theorem later_second (s : MachineState) (i : Index) (a : BitVec 1600) (lo hi : Word) :
    window (memoryView (tagLater (raw s i a) i lo hi)) (entryStart i+7) =
      pinnedSecondInput i (nonce lo hi) (replyWords a) (window (memoryView s) (entryStart i)) := by
  let p := entryStart i+7
  let t := raw s i a
  let m := writeWindow (memoryView s) (entryStart i-4) (replyWords a)
  let u := ((t.setMem (wordAddress p) (pinnedPositionTag i)).setMem (wordAddress (p+1)) lo).setMem
    (wordAddress (p+2)) hi
  let m' := writeWord (writeWord m p (pinnedPositionTag i)) (p+1) lo
  have room := bound i
  have stored {v : Word} {st : MachineState} {model : Memory} {dst : Nat} (ok : dst < 2^33)
      (rel : Agrees (memoryView st) model) :
      Agrees (memoryView (st.setMem (wordAddress dst) v)) (writeWord model dst v) := by
    intro w hw
    exact (memory_at_store (by omega) (by omega)).trans (write_word rel dst v w hw)
  have beforeClear : Agrees (memoryView u) (writeWord m' (p+2) hi) :=
    stored (by dsimp [p]; omega) (stored (by dsimp [p]; omega)
      (stored (by dsimp [p]; omega) (raw_words s i a)))
  have high : memoryView u (p+2) = hi := by
    rw [beforeClear _ (by dsimp [p]; omega)]; simp [writeWord]
  have final : Agrees (memoryView (tagLater t i lo hi)) (writeWord m' (p+2) (hi &&& 0x00ffffffffffffff)) := by
    intro w hw
    have out := CommitWrite.clear_salt_byte u (p+2) w (by dsimp [p]; omega) (by omega)
    rw [high] at out
    refine out.trans ?_
    unfold writeWord
    split
    · rfl
    · rename_i ne
      simpa only [writeWord,ne,ite_false] using beforeClear w hw
  exact (window_congr final (by omega)).trans (tag_window ..)

end CommitGolfCandidate.Reconstruction.LeafMemory
