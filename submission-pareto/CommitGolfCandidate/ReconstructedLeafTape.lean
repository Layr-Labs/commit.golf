import CommitGolfCandidate.ReconstructedLeafContent
import CommitGolfCandidate.ReconstructedHidingTranscript

namespace CommitGolfCandidate.Reconstruction.LeafTape
open CommitGolf TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open Generator HidingTape LeafContent

/-- The shared hiding game and the submitted word-oriented ECALL use the same
1,600-bit encoding for every generator query. -/
theorem address (k : Generator.Key) (t : Fin 4096) (g : Fin 342) :
    packBuffer (fun w => inputWord t g k w.val) = packedAddress k (blockNumber (t,g)) := by
  apply BitVec.eq_of_getLsbD_eq
  intro n hn
  let j : Fin 1600 := ⟨n,hn⟩
  let word : Fin 25 := ⟨n/64,by omega⟩
  have h := congrArg (fun v : BitVec 64 => v.getLsbD (n%64)) (packed_word (fun w => inputWord t g k w.val) word)
  have en : 64*word.val+n%64 = n := by dsimp only [word];omega
  simp only [BitVec.getLsbD_extractLsb',show n%64<64 by omega,decide_true,Bool.true_and,en] at h
  refine h.trans ?_
  have rhs := packedAddress_bit k (blockNumber (t,g)) j
  change (packedAddress k (blockNumber (t,g))).getLsbD n =
    (inputWord (groupIndex (blockNumber (t,g))).1 (groupIndex (blockNumber (t,g))).2 k (n/64)).getLsbD (n%64) at rhs
  rw [index_blockNumber] at rhs
  exact rhs.symm

theorem salt (o : Oracle) (k : Generator.Key) (i : Index) :
    LeafNonce.selected (tapeReply o k i) (laneOf i) = generatedSalts o.permutation k i := by
  let t := tileOf i
  let g := groupOf i
  change saltAt (o.permutation (packBuffer (fun w => inputWord t g k w.val))) (laneOf i) =
    saltAt (o.permutation (packedAddress k (blockNumber (t,g)))) (laneOf i)
  rw [address]

theorem digest (o : Oracle) (k : Generator.Key) (msg : Message) (i : Index) :
    outputDigest (lastReply o k msg i) =
      pinnedFullLeafDigests (BiPermutation.equiv Block o.permutation) msg (actualTape o.permutation k) i := by
  have h := congrArg (fun s : BitVec 120 => s.setWidth 128) (salt o k i)
  change _ = pinnedLeafDigest o.permutation i (saltWords ((generatedSalts o.permutation k i).setWidth 128)) (messageWords msg i)
  unfold lastReply
  rw [h]; rfl

end CommitGolfCandidate.Reconstruction.LeafTape
