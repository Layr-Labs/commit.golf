import CommitGolf.Artifact
import CommitGolfCandidate.InputMemory
import CommitGolfCandidate.TaggedPinnedModel
import CommitGolfCandidate.ReconstructedSeed

namespace CommitGolfCandidate.Reconstruction.CommitInput
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype (window Words)

attribute [local irreducible] ArtifactEncoding.decode
set_option maxRecDepth 8192

private theorem byte_message (s : Submission) (base : s.layout.message = 4096)
    (m : Message) (i : Index) (j : Nat) (inside : j < 256) :
    (s.initialState .commit m).getByte (BitVec.ofNat 64 (4096+256*i.val+j)) =
      (m i).extractLsb' (8*j) 8 := by
  have n : i.val < 2^24 := i.isLt
  rw [initial_input_byte s .commit m _ (by omega)]
  have selected : 4096 ≤ 4096+256*i.val+j ∧ 4096+256*i.val+j < 4096+LENGTH*(LEAF_SIZE/8) := by
    change _ ∧ _ < 4096+16777216*256; omega
  simp only [inputByte,Submission.inputBuffers,List.find?_cons,messageBuffer,base,
    selected,and_self,decide_true]
  have quotient : (4096+256*i.val+j-4096)/(LEAF_SIZE/8)=i.val := by change _/256=_; omega
  have remainder : (4096+256*i.val+j-4096)%(LEAF_SIZE/8)=j := by change _%256=_; omega
  simp only [quotient,remainder,i.isLt,dite_true]

private theorem word_read (s : MachineState) (w : Nat) : readBuffer s (8*w) 8 = memoryView s w := by
  have sliced := read_buffer_slice s (8*w) 32 0 8 (by decide)
  have word := read_digest_word s (8*w) 0 (by omega) (by decide)
  simpa only [Nat.mul_zero,Nat.add_zero,memoryView,wordAddress] using sliced.symm.trans word

/-- Each aligned input window contains the promised 256-byte entry, including the last entry. -/
theorem message_window (m : Message) (i : Index) :
    window (memoryView (Artifact.submission.initialState .commit m)) (512+32*i.val) =
      messageWords m i := by
  funext j
  change memoryView _ (512+32*i.val+j.val) = _
  rw [← word_read]
  have v := read_serialized_slice (Artifact.submission.initialState .commit m) (m i)
    (8*(512+32*i.val+j.val)) (8*j.val) 8 (by
      intro b hb
      rw [show 8*(512+32*i.val+j.val)+b = 4096+256*i.val+(8*j.val+b) by omega]
      exact byte_message _ rfl m i _ (by have := j.isLt; omega))
  simpa only [messageWords,← Nat.mul_assoc] using v

private theorem empty_data : dataBase (Artifact.submission.image .commit) = 2^36 := by
  change 16*((2^36-(ArtifactEncoding.decode 8 Artifact.commitData).length)/16) = _
  rw [ArtifactEncoding.length_decode]; decide

/-- After the last entry, the commitment loader initializes the entire heap and generator
scratch area to zero. The result is stated on words to use directly at syscall boundaries. -/
theorem empty_word (m : Message) (w : Nat) (lo : 4294971392 ≤ 8*w)
    (hi : 8*w+8 ≤ 2^36) : memoryView (Artifact.submission.initialState .commit m) w = 0 := by
  unfold memoryView wordAddress
  rw [initial_input_word Artifact.submission .commit m _ (by omega)]
  have byte (j : Nat) (inside : j ∈ Finset.range 8) :
      inputByte Artifact.submission .commit m (8*w+j) = 0 := by
    have bound := Finset.mem_range.mp inside
    have base : Artifact.submission.layout.message = 4096 := rfl
    have after : ¬ (4096 ≤ 8*w+j ∧ 8*w+j < 4096+LENGTH*(LEAF_SIZE/8)) := by
      change ¬ (_ ∧ _ < 4294971392); omega
    have below : ¬ (68719476736 ≤ 8*w+j) := by omega
    simp [inputByte,Submission.inputBuffers,List.find?,messageBuffer,base,after,empty_data,below]
  rw [Finset.sum_eq_zero (fun j hj => by rw [byte j hj]; exact Nat.zero_mul _)]
  rfl
  
end CommitGolfCandidate.Reconstruction.CommitInput
