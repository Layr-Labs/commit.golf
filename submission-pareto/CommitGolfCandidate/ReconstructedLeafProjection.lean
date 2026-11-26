import CommitGolfCandidate.ReconstructedEncoding

namespace CommitGolfCandidate.Reconstruction.LeafProjection
open CommitGolf TwoPermutationPrototype.Sampling TwoPermutationPrototype.RV64
open LeafTree LeafContent Encoding Generator
set_option maxRecDepth 8192

private theorem bottom (b : BitVec 1600) : ((replyWords b 2 ++ replyWords b 1) ++ replyWords b 0) =
    (Binding.unpack (outputDigest b)).1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change (((b.extractLsb' 128 64 ++ b.extractLsb' 64 64) ++ b.extractLsb' 0 64).getLsbD j) =
    (((b.extractLsb' 0 256).extractLsb' 0 192).getLsbD j)
  simp only [BitVec.getLsbD_append,BitVec.getLsbD_extractLsb',Nat.zero_add]
  by_cases first : j<64 <;> by_cases second : j-64<64 <;>
    simp only [first,second,show j<256 by omega,show j<192 by omega, show j-64-64<64 by omega,
      decide_true,decide_false,ite_true,ite_false,Bool.true_and,Bool.false_and,
      Bool.and_true,Bool.and_false] <;> congr 1 <;> omega

private theorem upper (b : BitVec 1600) : (Binding.unpack (outputDigest b)).2 = replyWords b 3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change (((b.extractLsb' 0 256).extractLsb' 192 64).getLsbD j) = (b.extractLsb' 192 64).getLsbD j
  simp only [BitVec.getLsbD_extractLsb',hj,show 192+j<256 by omega,Nat.zero_add,decide_true,Bool.true_and]

theorem projected_digest (b : BitVec 1600) :
    LeafTree.digest b = Binding.project 24 (Binding.unpack (outputDigest b)) := by
  apply Prod.ext
  · exact bottom b
  · apply BitVec.eq_of_toNat_eq
    change ((replyWords b 3) &&& _).toNat = _
    rw [Binding.project_hi,upper,show Binding.radix 24=2^48 by decide,BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 48

/-- The honest commitment is exactly the root supplied to the statistical hiding
transcript builder once the sampled key determines the 120-bit salt tape. -/
theorem reference_tree (o : Oracle) (k : Generator.Key) (msg : Message) :
    LeafTree.tree o k msg = Encoding.reference o.compression
      (pinnedFullLeafDigests (BiPermutation.equiv TwoPermutationPrototype.Sampling.Block o.permutation) msg (HidingTape.actualTape o.permutation k)) := by
  apply congrArg (CommitParents.node (CommitParents.rawC o))
  funext j
  exact (projected_digest _).trans (congrArg (fun x => Binding.project 24 (Binding.unpack x))
    (LeafTape.digest o k msg (LeafTree.leafNumber j)))

end CommitGolfCandidate.Reconstruction.LeafProjection
