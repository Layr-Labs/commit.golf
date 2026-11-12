import CommitGolfCandidate.CapHonestLowerBytes

/-! The digest parser is a left inverse of the exact lower-record encoding.
The values and index order remain supplied by the ABI; the arbitrary cap
suffix is returned unchanged, including the empty case. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxHeartbeats 200000

private theorem sibling_lookup (sibling : Fin 16 → Digest) (suffix : List Digest)
    (level : Fin 16) :
    ((List.ofFn sibling) ++ suffix)[level.val]?.getD 0 = sibling level := by
  rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_append_left
    (by simp only [List.length_ofFn]; exact level.isLt), List.getElem_ofFn]
  rfl

theorem cap_parse_encoded_lower (values : Index → Entry) (records : List CapLowerRecord)
    (consistent : ∀ record ∈ records, record.value = values record.index)
    (suffix : List Digest) :
    capParseLower values (records.map CapLowerRecord.index)
      (capLowerTranscript records ++ suffix) = some (records, suffix) := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      have current := consistent record (by simp)
      have later : ∀ entry ∈ rest, entry.value = values entry.index := by
        intro entry member
        exact consistent entry (by simp [member])
      have tail := ih later
      have siblings : (fun level : Fin 16 =>
          ((List.ofFn record.sibling) ++
            (capLowerTranscript rest ++ suffix))[level.val]?.getD 0) =
              record.sibling := by
        funext level
        exact sibling_lookup record.sibling _ level
      have reconstructed :
          (⟨record.index, values record.index, record.salt,
            fun level => ((List.ofFn record.sibling) ++
              (capLowerTranscript rest ++ suffix))[level.val]?.getD 0⟩ : CapLowerRecord) =
            record := by
        cases record
        simp only [CapLowerRecord.mk.injEq]
        exact ⟨trivial, current.symm, trivial, siblings⟩
      change capParseLower values (record.index :: rest.map CapLowerRecord.index)
        (record.salt :: ((List.ofFn record.sibling) ++
          (capLowerTranscript rest ++ suffix))) = some (record :: rest, suffix)
      rw [capParseLower]
      have enough : 16 ≤
          ((List.ofFn record.sibling) ++ (capLowerTranscript rest ++ suffix)).length := by
        simp only [List.length_append, List.length_ofFn]
        omega
      rw [if_pos enough]
      have dropped : ((List.ofFn record.sibling) ++
          (capLowerTranscript rest ++ suffix)).drop 16 =
          capLowerTranscript rest ++ suffix := by
        simpa only [List.length_ofFn] using
          (List.drop_left (l₁ := List.ofFn record.sibling)
            (l₂ := capLowerTranscript rest ++ suffix))
      rw [dropped, tail]
      change some
        ((⟨record.index, values record.index, record.salt,
          fun level => ((List.ofFn record.sibling) ++
            (capLowerTranscript rest ++ suffix))[level.val]?.getD 0⟩ : CapLowerRecord)
          :: rest, suffix) = some (record :: rest, suffix)
      rw [reconstructed]

end CommitGolfCandidate
