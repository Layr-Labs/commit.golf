import CommitGolfCandidate.TwoPermutationPinnedRecorded
import CommitGolfCandidate.TwoPermutationCheckerPaths

namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation TwoPermutationPrototype.RV64
set_option maxRecDepth 8192

structure PeerLeafLayout where
  salt : Index → BitVec 128 → BitVec 256
  first : ∀ (index : Index) (value : CommitGolf.Entry),
    packBuffer (pinnedFirstInput (entryWords value)) = s3First value
  second : ∀ (index : Index) (value : CommitGolf.Entry) (nonce : BitVec 128) (reply : Block),
    packBuffer (pinnedSecondInput index (saltWords nonce) (replyWords reply) (entryWords value)) =
      s3Second (salt index nonce) reply value

/-- The pinned two-call hash with its digest cut to the low 240 bits. -/
def s3PinCallLeaf : PinCall S3State (BitVec 1600) (BitVec 192) (BitVec 704) (BitVec 256)
    (BitVec 448) (BitVec 256) :=
  { s3PinCall with trunc := fun o => BitVec.ofNat 256 (o.toNat % 2^240) }

theorem s3_trunc_leaf_fiber (d : BitVec 256) :
    (Finset.univ.filter fun s : S3State => s3PinCallLeaf.trunc s = d).card ≤ 2 ^ 1360 := by
  have h := Finset.card_le_card_of_injOn (s := Finset.univ.filter fun s : S3State => s3PinCallLeaf.trunc s = d)
    (t := (Finset.univ : Finset (BitVec 1360))) (fun s => BitVec.ofNat 1360 (s.toNat / 2 ^ 240))
    (by intro a _; simp) (by
      intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
      have e1 := congrArg BitVec.toNat (ha.trans hb.symm)
      have e2 := congrArg BitVec.toNat hab
      simp only [s3PinCallLeaf, BitVec.toNat_ofNat] at e1 e2
      have hA := s3_state_lt a
      have hB := s3_state_lt b
      apply BitVec.eq_of_toNat_eq
      omega)
  rwa [Finset.card_univ, s3_card_bitvec] at h

private theorem trunc_digest (reply : Block) :
    s3PinCallLeaf.trunc reply = leafDigest reply := by
  change BitVec.ofNat 256 (reply.toNat % 2^240) = BitVec.ofNat 256 ((reply.extractLsb' 0 256).toNat % 2^240)
  congr 1
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (by decide : 2^240 ∣ 2^256)]

private theorem stored_evaluation (layout : PeerLeafLayout) (t : Trace PermState) (rows : List PublicRow)
    (stored : PinnedRowsStored rows t) (perm : Block → Block) (i : Index)
    (salt : BitVec 128) (value : CommitGolf.Entry)
    (ha : let a := pinnedFirstRow perm (entryWords value); PublicRow.permutation a.1 a.2 ∈ rows)
    (hb : let a := pinnedFirstRow perm (entryWords value)
          let b := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
          PublicRow.permutation b.1 b.2 ∈ rows) :
    let a := pinnedFirstRow perm (entryWords value)
    let b := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
    s3PinCallLeaf.Evaluates t (s3Input (layout.salt i salt,value)) (leafDigest b.2) := by
  let leaf := (layout.salt i salt,value)
  let a := pinnedFirstRow perm (entryWords value)
  let b := pinnedSecondRow perm i (saltWords salt) a.2 (entryWords value)
  obtain ⟨e,he,ein,eout⟩ := stored a.1 a.2 ha
  obtain ⟨f,hf,fin,fout⟩ := stored b.1 b.2 hb
  have first : e.inp = s3PinCall.enc1 (s3Input leaf).1 :=
    ein.trans ((layout.first i value).trans (s3_first_eq leaf))
  refine ⟨e,he,f,hf,first,?_,?_⟩
  · rw [eout,first]
    exact fin.trans ((layout.second i value salt a.2).trans (s3_second_eq leaf a.2))
  · exact (congrArg s3PinCallLeaf.trunc fout).trans (trunc_digest b.2)

theorem pinned_witness_bad (layout : PeerLeafLayout) (t : Trace PermState) (rows : List PublicRow) (stored : PinnedRowsStored rows t)
    (hit : PinnedLeafWitness rows) : ¬ s3PinCallLeaf.badSpec.Good t := by
  obtain ⟨perm,i,n,m,v,w,a₀,a₁,b₀,b₁,digest,conflict⟩ := hit
  obtain ⟨salt₀,hs₀⟩ := (split_blocks_bijective 64 2 (by decide)).2 n
  obtain ⟨salt₁,hs₁⟩ := (split_blocks_bijective 64 2 (by decide)).2 m
  obtain ⟨value₀,hv₀⟩ := (split_blocks_bijective 64 32 (by decide)).2 v
  obtain ⟨value₁,hv₁⟩ := (split_blocks_bijective 64 32 (by decide)).2 w
  change saltWords salt₀=n at hs₀
  change saltWords salt₁=m at hs₁
  change entryWords value₀=v at hv₀
  change entryWords value₁=w at hv₁
  subst n m v w
  have distinct : value₀ ≠ value₁ := fun h => conflict (congrArg entryWords h)
  have left := stored_evaluation layout t rows stored perm i salt₀ value₀ a₀ b₀
  have right := stored_evaluation layout t rows stored perm i salt₁ value₁ a₁ b₁
  refine s3PinCallLeaf.collision_imp_bad (s3_input_ne (leaf := (layout.salt i salt₀,value₀))
    (leaf' := (layout.salt i salt₁,value₁)) distinct) left ?_
  exact digest.symm ▸ right

end TwoPermutationPrototype.Sampling
