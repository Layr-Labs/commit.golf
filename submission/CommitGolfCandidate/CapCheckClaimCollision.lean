import CommitGolfCandidate.CapCheckReplayAccepted

/-! A winning claim against the actual cap checker yields, for the fixed oracle,
a compression reply collision in two paid batch replays or a collision among
the replayed stage-3 leaves. The selected records retain the original shared
Index and different supplied values. The reply probe pays for every repeated
query too; the ROM reduction supplies cache preservation and probability. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option autoImplicit false

theorem cap_check_claim_probe_collision (oracle : Oracle) (claim : Scheme.Claim)
    (breaks : capProgram.scheme.Breaks oracle claim) :
    (∃ replies calls,
      oracle.run (capProbePair
        (capCheckLoadedRecords (claimLeft claim)) (capCheckLoadedRecords (claimRight claim))
        (capCheckSuffixWords (claimLeft claim) (544*claim.positions₀.card))
        (capCheckSuffixWords (claimRight claim) (544*claim.positions₁.card))
        claim.root)=pure (replies,calls) ∧ ReplyCollision replies) ∨
    LeafCollision (s3LeafReplies oracle.permutation
      (capRecordLeaves (capCheckLoadedRecords (claimLeft claim)) ++
        capRecordLeaves (capCheckLoadedRecords (claimRight claim)))) := by
  obtain ⟨index,leftMember,rightMember,different⟩ := breaks.1
  have leftNonempty : 0<claim.positions₀.card :=
    Finset.card_pos.mpr ⟨index,leftMember⟩
  have rightNonempty : 0<claim.positions₁.card :=
    Finset.card_pos.mpr ⟨index,rightMember⟩
  obtain ⟨leftRecord,leftPresent,leftIndex,leftValue⟩ :=
    cap_check_loaded_record_for_position (claimLeft claim) index leftMember
  obtain ⟨rightRecord,rightPresent,rightIndex,rightValue⟩ :=
    cap_check_loaded_record_for_position (claimRight claim) index rightMember
  obtain ⟨leftRoots,leftLower,leftCap⟩ :=
    cap_check_accepted_batch oracle (claimLeft claim) breaks.2.1 leftNonempty
  obtain ⟨rightRoots,rightLower,rightCap⟩ :=
    cap_check_accepted_batch oracle (claimRight claim) breaks.2.2 rightNonempty
  have differentRecords : leftRecord.value≠rightRecord.value := by
    rw [leftValue,rightValue]
    exact different
  exact cap_accepted_pair_collision oracle
    (capCheckLoadedRecords (claimLeft claim)) (capCheckLoadedRecords (claimRight claim))
    (capCheckSuffixWords (claimLeft claim) (544*claim.positions₀.card))
    (capCheckSuffixWords (claimRight claim) (544*claim.positions₁.card))
    claim.root leftRoots rightRoots leftLower rightLower leftCap rightCap
    leftRecord rightRecord leftPresent rightPresent
    (leftIndex.trans rightIndex.symm) differentRecords

end CommitGolfCandidate
