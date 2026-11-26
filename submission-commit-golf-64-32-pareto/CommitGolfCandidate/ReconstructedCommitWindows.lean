import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.ReconstructedGenerator

namespace CommitGolfCandidate.Reconstruction.CommitWindows
open CommitGolf RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype (window writeWindow writeWord Memory Words)
open Generator

set_option maxRecDepth 8192

/-- All offsets in this module are 64-bit word offsets, as in the interpreter's memory view. -/
def entryStart (i : Index) := 512 + 32*i.val
def generatorBase := 704643566

def generatorMemory (tile : Fin 4096) (group : Fin 342) (k : Key) (w : Nat) : Word :=
  if w = generatorBase then -1
  else if w = generatorBase+1 then BitVec.ofNat 64 (counter tile group)
  else if h : generatorBase+4 ≤ w ∧ w < generatorBase+7 then k ⟨w-(generatorBase+4),by omega⟩
  else 0

theorem generator_window (t : Fin 4096) (g : Fin 342) (k : Key) :
    window (generatorMemory t g k) (generatorBase - marker g) =
      (fun i : Fin 25 => inputWord t g k i.val) := by
  funext i
  have bound : marker g ≤ 16 := by simp [marker]; omega
  let w := generatorBase - marker g + i.val
  have big : marker g ≤ generatorBase := by unfold generatorBase; omega
  have markerAt : w = generatorBase ↔ i.val = marker g := by dsimp [w]; omega
  have counterAt : w = generatorBase+1 ↔ i.val = marker g+1 := by dsimp [w]; omega
  have keysAt : (generatorBase+4 ≤ w ∧ w < generatorBase+7) ↔
      (marker g+4 ≤ i.val ∧ i.val < marker g+7) := by dsimp [w]; omega
  change generatorMemory t g k w = _
  unfold generatorMemory inputWord
  by_cases m : i.val = marker g
  · rw [if_pos (markerAt.mpr m),if_pos m]
  rw [if_neg (mt markerAt.mp m),if_neg m]
  by_cases c : i.val = marker g+1
  · rw [if_pos (counterAt.mpr c),if_pos c]
  rw [if_neg (mt counterAt.mp c),if_neg c]
  by_cases key : marker g+4 ≤ i.val ∧ i.val < marker g+7
  · rw [dif_pos (keysAt.mpr key),dif_pos key]
    apply congrArg k
    apply Fin.ext
    change w-(generatorBase+4) = i.val-(marker g+4)
    dsimp [w]; omega
  · rw [dif_neg (mt keysAt.mp key),dif_neg key]

def generatedFirst (memory : Memory) (i : Index) (first tape : BitVec 1600) : Memory :=
  writeWindow (writeWindow memory (entryStart i - 4) (replyWords first))
    (entryStart i - 15) (replyWords tape)

/-- The generator output can overlap the low part of the preceding reply. Every one of
the eleven first-reply words consumed by the second permutation survives that overwrite. -/
theorem retained_first (mem : Memory) (i : Index) (a tape : BitVec 1600) (j : Fin 11) :
    generatedFirst mem i a tape (entryStart i + 10 + j.val) =
      replyWords a ⟨14+j.val, by omega⟩ := by
  have room : 15 ≤ entryStart i := by unfold entryStart; omega
  have small := j.isLt
  have off : entryStart i + 10 + j.val - (entryStart i - 4) = 14+j.val := by omega
  unfold generatedFirst writeWindow
  split
  · omega
  split
  · congr 1 <;> apply Fin.ext <;> omega
  · omega

theorem tape_slot (mem : Memory) (i : Index) (a tape : BitVec 1600) (j : Fin 25) :
    generatedFirst mem i a tape (entryStart i-15+j.val) = replyWords tape j := by
  unfold generatedFirst writeWindow
  rw [dif_pos (by have := j.isLt; omega)]
  apply congrArg (replyWords tape)
  apply Fin.ext
  change entryStart i - 15 + j.val - (entryStart i-15) = j.val
  omega

/-- A complete lane-zero leaf after the two header words are installed and the high
salt byte is cleared. The earlier tape write takes its low salt word from tape slot 23. -/
def firstHeader (mem : Memory) (i : Index) (a tape : BitVec 1600) : Memory :=
  let m := generatedFirst mem i a tape
  let p := entryStart i + 7
  writeWord (writeWord m p (pinnedPositionTag i)) (p+2)
    ((m (p+2)) &&& 0x00ffffffffffffff)

def zeroNonce (tape : BitVec 1600) : Words 2 := fun j =>
  if j.val = 0 then replyWords tape 23 else replyWords tape 24 &&& 0x00ffffffffffffff

theorem lane_zero_input (mem : Memory) (i : Index) (a tape : BitVec 1600) :
    window (firstHeader mem i a tape) (entryStart i+7) =
      pinnedSecondInput i (zeroNonce tape) (replyWords a) (window mem (entryStart i)) := by
  have room : 15 ≤ entryStart i := by unfold entryStart; omega
  funext j
  by_cases h : j.val < 3
  · have choices : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 := by omega
    have s23 := tape_slot mem i a tape 23
    have s24 := tape_slot mem i a tape 24
    change generatedFirst mem i a tape (entryStart i - 15 + 23) = _ at s23
    change generatedFirst mem i a tape (entryStart i - 15 + 24) = _ at s24
    rw [show entryStart i - 15 + 23 = entryStart i + 7 + 1 by omega] at s23
    rw [show entryStart i - 15 + 24 = entryStart i + 7 + 2 by omega] at s24
    rcases choices with e|e|e <;>
      simp [window,firstHeader,writeWord,pinnedSecondInput,zeroNonce,e,s23,s24]
  · have nz : j.val ≠ 0 := by omega
    have ne₁ : entryStart i + 7 + j.val ≠ entryStart i+7 := by omega
    have ne₂ : entryStart i + 7 + j.val ≠ entryStart i+7+2 := by omega
    simp only [window,firstHeader,writeWord,ne₁,ne₂,ite_false,pinnedSecondInput,nz,h,dite_false]
    by_cases middle : j.val < 14
    · simp only [middle,dite_true]
      have e := retained_first mem i a tape ⟨j.val-3,by omega⟩
      have addr : entryStart i + 7 + j.val = entryStart i + 10 + (j.val-3) := by omega
      rw [addr,e]
      apply congrArg (replyWords a)
      apply Fin.ext
      change 14+(j.val-3) = j.val+11
      omega
    · simp only [middle,dite_false,generatedFirst,writeWindow]
      (repeat' split) <;> try omega
      congr 1 <;> omega

end CommitGolfCandidate.Reconstruction.CommitWindows
