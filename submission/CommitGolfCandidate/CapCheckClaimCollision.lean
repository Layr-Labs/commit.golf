import CommitGolfCandidate.CapCheckReplayAccepted

/-! A winning claim against the actual cap checker yields a collision in two
paid batch replays. The selected records retain the original shared Index and
different supplied values. The reply probe pays for every repeated query too;
the later ROM reduction still supplies cache preservation and probability. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
set_option autoImplicit false

theorem cap_check_replay_trace_unique (oracle : Oracle)
    (computation : OracleComp World (Option (List (BitVec 512))))
    (inputs inputs' : List (BitVec 512)) (calls calls' : Nat)
    (first : oracle.run computation=pure (some inputs,calls))
    (second : oracle.run computation=pure (some inputs',calls')) :
    inputs=inputs' := by
  have reachable : (some inputs,calls) ∈ support (oracle.run computation) := by
    rw [first]
    simp
  rw [second] at reachable
  have same := eq_of_mem_support_pure (some inputs',calls') reachable
  exact Option.some.inj (congrArg Prod.fst same)

theorem cap_check_claim_probe_collision (oracle : Oracle) (claim : Scheme.Claim)
    (breaks : capProgram.scheme.Breaks oracle claim) :
    ∃ replies calls,
      oracle.run (capProbePair
        (capCheckLoadedRecords (claimLeft claim)) (capCheckLoadedRecords (claimRight claim))
        (capCheckSuffixWords (claimLeft claim) (576*claim.positions₀.card))
        (capCheckSuffixWords (claimRight claim) (576*claim.positions₁.card))
        claim.root)=pure (replies,calls) ∧ ReplyCollision replies := by
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
  obtain ⟨leftCapInputs,rightCapInputs,leftRun,rightRun,collision⟩ :=
    cap_batch_collision oracle
      (capCheckLoadedRecords (claimLeft claim)) (capCheckLoadedRecords (claimRight claim))
      (capCheckSuffixWords (claimLeft claim) (576*claim.positions₀.card))
      (capCheckSuffixWords (claimRight claim) (576*claim.positions₁.card))
      claim.root leftRoots rightRoots leftLower rightLower leftCap rightCap
      leftRecord rightRecord leftPresent rightPresent
      (leftIndex.trans rightIndex.symm) differentRecords
  obtain ⟨leftInputs,leftCalls,leftAccepted,leftBound⟩ :=
    cap_check_accepted_replay oracle (claimLeft claim) breaks.2.1 leftNonempty
  obtain ⟨rightInputs,rightCalls,rightAccepted,rightBound⟩ :=
    cap_check_accepted_replay oracle (claimRight claim) breaks.2.2 rightNonempty
  have leftSame := cap_check_replay_trace_unique oracle _
    (capLowerBatchInputs oracle.compression (capCheckLoadedRecords (claimLeft claim))++
      leftCapInputs) leftInputs _ leftCalls leftRun leftAccepted
  have rightSame := cap_check_replay_trace_unique oracle _
    (capLowerBatchInputs oracle.compression (capCheckLoadedRecords (claimRight claim))++
      rightCapInputs) rightInputs _ rightCalls rightRun rightAccepted
  apply cap_probe_pair_collision oracle _ _ _ _ _ _ _ _ _ leftRun rightRun
  · rw [leftSame,cap_check_loaded_records_length]
    exact leftBound
  · rw [rightSame,cap_check_loaded_records_length]
    exact rightBound
  · exact collision

end CommitGolfCandidate
