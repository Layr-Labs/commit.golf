import CommitGolfCandidate.ReconstructedLeafNonce
import CommitGolfCandidate.ReconstructedCommitKey

namespace CommitGolfCandidate.Reconstruction.LeafContent
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype (Memory Words window writeWindow writeWord)
open Generator CommitWindows

def heapBase := 603980388
def location (j : Index) := heapBase+4*j.val

def tapeReply (o : Oracle) (k : Key) (j : Index) :=
  o.permutation (packBuffer fun w => inputWord (tileOf j) (groupOf j) k w.val)

def firstReply (o : Oracle) (m : Message) (j : Index) : BitVec 1600 :=
  o.permutation (packBuffer (pinnedFirstInput (messageWords m j)))

def lastReply (o : Oracle) (k : Key) (m : Message) (j : Index) : BitVec 1600 :=
  o.permutation (packBuffer (pinnedSecondInput j
    (saltWords ((LeafNonce.selected (tapeReply o k j) (laneOf j)).setWidth 128))
    (replyWords (firstReply o m j)) (messageWords m j)))

def markedReply (b : BitVec 1600) : Words 4 := fun j =>
  let w := replyWords b ⟨j.val,by have := j.isLt; omega⟩
  if j.val=3 then w ||| 0xffff000000000000 else w

def putLeaf (mem : Memory) (j : Index) (b : BitVec 1600) : Memory :=
  writeWord (writeWindow mem (location j) (replyWords b)) (location j+3)
    ((replyWords b 3) ||| 0xffff000000000000)

theorem inserted (mem : Memory) (j : Index) (b : BitVec 1600) :
    window (putLeaf mem j b) (location j) = markedReply b := by
  funext w
  have inside : location j ≤ location j+w.val ∧ location j+w.val < location j+25 := by have := w.isLt; omega
  unfold putLeaf window markedReply writeWord writeWindow
  by_cases tag : w.val = 3
  · simp [tag]
  · simp [tag,inside]

theorem outside (mem : Memory) (j : Index) (b : BitVec 1600) (w : Nat)
    (sep : w < location j ∨ location j+25 ≤ w) : putLeaf mem j b w = mem w := by
  have notTagged : w ≠ location j+3 := by omega
  have notWritten : ¬ (location j ≤ w ∧ w < location j+25) := by omega
  simp [putLeaf,writeWord,writeWindow,notTagged,notWritten]

/-- Only the counter word of the permanent key window can change during a tile. -/
def KeyRegion (m : Memory) (k : Key) := ∀ w, generatorBase-16 ≤ w → w < generatorBase+25 →
  w ≠ generatorBase+1 → m w = generatorMemory 0 0 k w

/-- The inductive memory contract across the 2^24 leaves. It includes the reserved
parent area, which supplies the all-zero right half of every future continuation. -/
structure Prefix (o : Oracle) (k : Key) (message : Message) (count : Nat) (mem : Memory) : Prop where
  future : ∀ j : Index, count ≤ j.val → window mem (entryStart j) = messageWords message j
  past : ∀ j : Index, j.val < count → window mem (location j) = markedReply (lastReply o k message j)
  parents : ∀ w, 4294971424 ≤ 8*w → w < heapBase → mem w = 0
  header : KeyRegion mem k

theorem initial (o : Oracle) (r : BitVec 192) (m : Message) :
    Prefix o (CommitKey.key r) m 0
      (memoryView (CommitKey.tileStart (Artifact.submission.initialState .commit m) r)) := by
  let s := Artifact.submission.initialState .commit m
  let k := CommitKey.key r
  have state := CommitKey.start_memory s r
  have away (w : Nat) (hw : w < generatorBase) :
      memoryView (CommitKey.tileStart s r) w = memoryView s w := by
    have small : generatorBase < 2^33 := by decide
    rw [state w (by omega)]
    simp [writeWord,writeWindow,show w≠generatorBase by omega,show ¬(generatorBase+4≤w ∧ w<generatorBase+4+3) by omega]
  constructor
  · intro j _
    refine Eq.trans ?_ (CommitInput.message_window m j)
    funext p
    exact away _ (by have jh : j.val < 2^24 := j.isLt; have ph := p.isLt; unfold entryStart generatorBase; omega)
  · intro j h; omega
  · intro w lo hi
    have below : w < generatorBase := by unfold heapBase at hi; unfold generatorBase; omega
    exact (away w below).trans (CommitInput.empty_word m w (by omega) (by unfold generatorBase at below; omega))
  · intro w lo hi noncounter
    rw [state w (by unfold generatorBase at hi; omega)]
    simp only [writeWord,writeWindow,generatorMemory,noncounter,ite_false]
    split
    · rfl
    split
    · rfl
    · exact CommitInput.empty_word m w (by unfold generatorBase at lo; omega) (by unfold generatorBase at hi; omega)

end CommitGolfCandidate.Reconstruction.LeafContent
