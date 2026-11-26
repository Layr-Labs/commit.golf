import CommitGolfCandidate.ReconstructedHidingBaseGate
import CommitGolfCandidate.TaggedPinnedCommon

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp Generator HidingReplay HidingTraffic TwoPermutationPrototype.Sampling
set_option maxRecDepth 10000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048
attribute [local irreducible] pinnedFirstAddresses runPinnedHigh blockSplit packedAddress

def highOverlap {G : Type} {base : Cache} (cache : PinnedHighCache base) (blocks : G → SaltBlock) :=
  ∃ g,∃ row ∈ cache.added,tailSignature row.upper = signature (blocks g)

theorem new_high_cost {G : Type} [Fintype G] (base : Cache) (p : Positions) (left right : Message)
    (op : OpenedSalts p) (room : base.entries.length+2*LENGTH+p.card≤2^121) (blocks : G → SaltBlock) :
    Pr{let st ← pinnedCommonHigh base p left right op}[highOverlap st.final blocks] ≤
      (Fintype.card G:ENNReal)*((2*LENGTH:ENNReal)/2^359) + (Fintype.card G:ENNReal)*(p.card/2^359) := by
  classical
  let empty := PinnedHighCache.empty base
  let raw := pinnedFirstAddresses left right
  let before := runPinnedHigh empty 0 [] (pinnedConstantPlans raw)
  let opened (a : List (BitVec 1344) × PinnedHighCache base) := pinnedOpenedAddresses p left
    (fun input => pinnedOutputTail (a.2.zero.example.val.forward input)) op
  let after (a : List (BitVec 1344) × PinnedHighCache base) : ProbComp (PinnedCommonHigh base) := do
    let b ← runPinnedHigh a.2 (2*LENGTH) [] (pinnedConstantPlans (opened a))
    pure ⟨a.2,b.2,opened a⟩
  let bad := fun a : List (BitVec 1344) × PinnedHighCache base => highOverlap a.2 blocks
  have firstRoom : empty.zero.entries.length+raw.length≤2^121 := by
    simp only [empty,raw,PinnedHighCache.zero,PinnedHighCache.empty_realize,pinned_first_addresses_length]
    omega
  have firstBound : Pr{let a ← before}[bad a] ≤ (Fintype.card G:ENNReal)*((2*LENGTH:ENNReal)/2^359) := by
    have cost := generated_new_signatures_le empty 0 [] (pinnedConstantPlans raw)
      (by simpa only [pinnedConstantPlans,List.length_map] using firstRoom) blocks
    rw [show (pinnedConstantPlans raw).length=2*LENGTH by simpa only [pinnedConstantPlans,List.length_map] using pinned_first_addresses_length left right,Nat.cast_mul,Nat.cast_ofNat] at cost
    refine (prEvent_mono before bad _ ?_).trans cost
    rintro a ⟨g,row,member,same⟩
    exact ⟨g,row.upper,same,row,member,List.not_mem_nil,_root_.rfl⟩
  have secondBound (a : List (BitVec 1344) × PinnedHighCache base) (reached : a∈support before) (clean : ¬bad a) :
      Pr{let st ← after a}[highOverlap st.final blocks] ≤ (Fintype.card G:ENNReal)*(p.card/2^359) := by
    obtain ⟨_,len,_,_⟩ := pinned_high_const_support empty 0 [] raw (pinned_high_empty_valid base) firstRoom a reached
    simp only [empty,raw,PinnedHighCache.zero,PinnedHighCache.empty_realize,pinned_first_addresses_length] at len
    have n : (pinnedConstantPlans (opened a)).length=p.card := by simp [pinnedConstantPlans,opened,pinned_opened_addresses_length]
    have fits : a.2.zero.entries.length+(pinnedConstantPlans (opened a)).length≤2^121 := by
      rw [n]; change a.2.zero.entries.length≤base.entries.length+2*LENGTH at len; omega
    have cost := generated_new_signatures_le a.2 (2*LENGTH) [] (pinnedConstantPlans (opened a)) fits blocks
    rw [n] at cost
    unfold after
    rw [bind_pure_comp,prEvent_map]
    refine (prEvent_mono _ _ _ ?_).trans cost
    rintro b ⟨g,row,member,same⟩
    exact ⟨g,row.upper,same,row,member,fun present => clean ⟨g,row,present,same⟩,rfl⟩
  exact (prEvent_bind_le_prEvent_add_of_support before after bad _ secondBound).trans (add_le_add firstBound le_rfl)

def jointGate {base : Cache} (xs : List Reply) (p : Positions) (v : VisibleGenerator p)
    (cache : PinnedHighCache base) (s : Secrets (ClosedIx p)) :=
  baseGood base xs ((openingGenerators p).symm (v,s)) ∧ ¬highOverlap cache (knownBlocks p v.1 v.2 s.1.2)

theorem gated_blocks {base : Cache} (xs : List Reply) (p : Positions) (v : VisibleGenerator p)
    (cache : PinnedHighCache base) (s : Secrets (ClosedIx p)) (ok : jointGate xs p v cache s) :
    Function.Injective (knownBlocks p v.1 v.2 s.1.2) := by
  intro a b same
  have eq (g : Group) : publicBlocks blockSplit (proposedReplies (knownBlocks p v.1 v.2) s) (blockNumber g)=
      knownBlocks p v.1 v.2 s.1.2 g := by
    unfold publicBlocks
    exact (opening_blocks p v s (blockNumber g)).trans (congrArg _ (index_blockNumber g))
  have j : blockNumber a=blockNumber b := ok.1.2.2.2 ((eq a).trans (same.trans (eq b).symm))
  exact (index_blockNumber a).symm.trans ((congrArg groupIndex j).trans (index_blockNumber b))

theorem gated_reverse {base : Cache} (xs : List Reply) (p : Positions) (v : VisibleGenerator p)
    (cache : PinnedHighCache base) (s : Secrets (ClosedIx p)) (ok : jointGate xs p v cache s)
    (g : Group) (hi : BitVec 1344) (found : (reverseUpper cache hi).isSome) :
    signature (knownBlocks p v.1 v.2 s.1.2 g) ≠ tailSignature hi := by
  classical
  unfold reverseUpper at found
  split at found
  · rename_i present
    obtain ⟨a,seen⟩ := present
    unfold pinnedAddedUpper at seen
    split at seen
    · rename_i rows
      have source := Classical.choose_spec rows
      exact fun matchSig => ok.2 ⟨g,_,source.1,(congrArg tailSignature (Option.some.inj seen)).trans matchSig.symm⟩
    · cases seen
  · cases found

theorem gated_cached {base : Cache} (xs : List Reply) (p : Positions) (v : VisibleGenerator p)
    (cache : PinnedHighCache base) (s : Secrets (ClosedIx p)) (ok : jointGate xs p v cache s)
    (low : PinnedLowTape) (x y : Reply) (stored : (x,y) ∈ (cache.realize low).entries) (g : Group) :
    blockSplit.symm (knownBlocks p v.1 v.2 s.1.2 g,s.2 g) ≠ y := by
  intro hit
  have sig : signature (knownBlocks p v.1 v.2 s.1.2 g)=tailSignature (outputTail y) := by
    have head := congrArg Prod.fst (blockSplit.apply_symm_apply (knownBlocks p v.1 v.2 s.1.2 g,s.2 g))
    rw [hit] at head
    exact (congrArg signature head.symm).trans (signature_tail y)
  change (x,y) ∈ cache.added.map (fun r => r.realize low) ++ base.entries at stored
  rcases List.mem_append.mp stored with added|known
  · obtain ⟨row,present,eq⟩ := List.mem_map.mp added
    have hi : outputTail y = row.upper := by
      change pinnedOutputTail y = _
      rw [←show (row.realize low).2=y from congrArg Prod.snd eq]
      exact pinned_high_row_tail row low
    exact ok.2 ⟨g,row,present,(congrArg tailSignature hi).symm.trans sig.symm⟩
  · obtain ⟨i,eq⟩ := List.mem_iff_get.mp known
    apply ok.1.2.2.1
    refine ⟨blockNumber g,i,?_⟩
    have block : (blockSplit (proposedReplies (knownBlocks p v.1 v.2) s (blockNumber g))).1 =
        knownBlocks p v.1 v.2 s.1.2 g := (opening_blocks p v s (blockNumber g)).trans (congrArg _ (index_blockNumber g))
    exact (congrArg signature block).trans (sig.trans (congrArg (fun row : Row => tailSignature (outputTail row.2)) eq).symm)

end CommitGolfCandidate.Reconstruction.HidingTape
