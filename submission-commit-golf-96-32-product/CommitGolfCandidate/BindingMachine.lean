import CommitGolfCandidate.Binding
import CommitGolfCandidate.CheckInputSound

/-! Deterministic collision extraction from an actual successful binding claim. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64

/-- The two check inputs in the binding game, with their actual supplied bytes. -/
def claimLeft (claim : Scheme.Claim) : CheckInput :=
  ⟨claim.root, claim.positions₀, claim.values₀, claim.proof₀⟩

def claimRight (claim : Scheme.Claim) : CheckInput :=
  ⟨claim.root, claim.positions₁, claim.values₁, claim.proof₁⟩

/-- An ordinal pair witnessing a conflict is chosen solely from the claim, before
any replay queries. Both supplied records concern the same vector position. -/
def ConflictingRecords (claim : Scheme.Claim) (left right : Nat) : Prop :=
  left < claim.positions₀.card ∧ right < claim.positions₁.card ∧
  recordIndex (claimLeft claim) left = recordIndex (claimRight claim) right ∧
  recordValue (claimLeft claim) left ≠ recordValue (claimRight claim) right

theorem conflicting_records_exist (claim : Scheme.Claim) (conflicting : claim.Conflicting) :
    ∃ left right, ConflictingRecords claim left right := by
  obtain ⟨index, leftMember, rightMember, different⟩ := conflicting
  obtain ⟨left, leftBound, leftIndex, leftValue⟩ := record_for_position (claimLeft claim) index leftMember
  obtain ⟨right, rightBound, rightIndex, rightValue⟩ := record_for_position (claimRight claim) index rightMember
  exact ⟨left, right, leftBound, rightBound, leftIndex.trans rightIndex.symm,
    by rw [leftValue, rightValue]; exact different⟩

/-- Compression inputs for replaying one record parsed from the submitted proof, up to
the commitment: its leaf chain, its 17-level path and the chain over the supplied cap. -/
def recordInputs (compress : Compression) (input : CheckInput) (ordinal : Nat) : List (BitVec COMPRESSION_INPUT_LENGTH) :=
  capOpeningInputs compress (recordSalt input ordinal) (recordValue input ordinal)
    (recordPath (recordIndex input ordinal) (recordSibling input ordinal)) (recordCap input)

theorem record_inputs_length (compress : Compression) (input : CheckInput) (ordinal : Nat) :
    (recordInputs compress input ordinal).length = 85 := by
  rw [recordInputs, capOpeningInputs_length, record_path_length]
  decide

theorem record_cap_node_bound (input : CheckInput) (ordinal : Nat) :
    (recordIndex input ordinal).val / 2^PATH_LEVELS < 2*CAP_PAIRS := by
  have := (recordIndex input ordinal).isLt
  change _ < 16777216 at this
  simp only [PATH_LEVELS, CAP_PAIRS]
  omega

/-- Any conflicting ordinal pair in a successful machine binding claim yields a
compression collision among the 85 replay inputs of each record. This theorem uses
actual checker acceptance, not an assumed abstract verifier. -/
theorem binding_claim_collision (oracle : Oracle) (claim : Scheme.Claim) (left right : Nat)
    (records : ConflictingRecords claim left right)
    (leftAccepted : (oracle.eval (submission.scheme.check claim.root claim.positions₀ claim.values₀ claim.proof₀)).1 = true)
    (rightAccepted : (oracle.eval (submission.scheme.check claim.root claim.positions₁ claim.values₁ claim.proof₁)).1 = true) :
    ∃ input ∈ recordInputs oracle.compression (claimLeft claim) left,
      ∃ input' ∈ recordInputs oracle.compression (claimRight claim) right,
        input ≠ input' ∧ oracle.compression input = oracle.compression input' := by
  have leftRoot := check_input_sound oracle (claimLeft claim) leftAccepted left records.1
  have rightRoot := check_input_sound oracle (claimRight claim) rightAccepted right records.2.1
  apply collision_of_cap_openings_eq oracle.compression
    (recordSalt (claimLeft claim) left) (recordSalt (claimRight claim) right)
    (recordValue (claimLeft claim) left) (recordValue (claimRight claim) right)
    (recordPath (recordIndex (claimLeft claim) left) (recordSibling (claimLeft claim) left))
    (recordPath (recordIndex (claimRight claim) right) (recordSibling (claimRight claim) right))
    (recordCap (claimLeft claim)) (recordCap (claimRight claim))
    ((recordIndex (claimLeft claim) left).val / 2^PATH_LEVELS)
    (record_cap_node_bound _ _)
  · rw [records.2.2.1]
    exact record_path_directions _ _ _
  · exact records.2.2.2
  · exact leftRoot.1
  · rw [records.2.2.1]; exact rightRoot.1
  · exact leftRoot.2.trans rightRoot.2.symm

/-- A winning binding-game claim forces a collision detectable by replaying at
most 170 compression calls, independently of the sizes of its two opening batches. -/
theorem breaks_implies_collision (oracle : Oracle) (claim : Scheme.Claim)
    (breaks : submission.scheme.Breaks oracle claim) :
    ∃ left right, ConflictingRecords claim left right ∧
      (recordInputs oracle.compression (claimLeft claim) left).length +
        (recordInputs oracle.compression (claimRight claim) right).length = 170 ∧
      ∃ input ∈ recordInputs oracle.compression (claimLeft claim) left,
        ∃ input' ∈ recordInputs oracle.compression (claimRight claim) right,
          input ≠ input' ∧ oracle.compression input = oracle.compression input' := by
  obtain ⟨left, right, records⟩ := conflicting_records_exist claim breaks.1
  refine ⟨left, right, records, ?_, binding_claim_collision oracle claim left right records breaks.2.1 breaks.2.2⟩
  rw [record_inputs_length, record_inputs_length]

end CommitGolfCandidate
