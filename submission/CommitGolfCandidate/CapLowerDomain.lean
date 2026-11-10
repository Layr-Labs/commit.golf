import CommitGolfCandidate.CapHonestCollect

/-! The forward lower-record collector occupies exactly the groups supplied
by the ABI records, in addition to any previously occupied entry groups.
Root-value agreement and occupancy are deliberately separate invariants. -/
namespace CommitGolfCandidate
open CommitGolf
set_option maxHeartbeats 200000

theorem cap_lower_batch_domain (compress : Compression) (records : List CapLowerRecord)
    (roots finalRoots : CapRootMap)
    (accepted : capLowerBatchRoots compress records roots = some finalRoots)
    (group : Nat) :
    (finalRoots group).isSome = true ↔
      (roots group).isSome = true ∨
        ∃ record ∈ records, (capGroup record.index).val = group := by
  induction records generalizing roots with
  | nil =>
      simp only [capLowerBatchRoots, Option.some.injEq] at accepted
      subst finalRoots
      simp
  | cons head rest ih =>
      cases inserted : capInsert roots (capGroup head.index).val (head.root compress) with
      | none => simp [capLowerBatchRoots, inserted] at accepted
      | some next =>
          have later : capLowerBatchRoots compress rest next = some finalRoots := by
            simpa [capLowerBatchRoots, inserted] using accepted
          rw [ih next later, cap_insert_lookup roots next _ group _ inserted]
          by_cases same : group = (capGroup head.index).val
          · simp [same]
          · simp [same, Ne.symm same, List.mem_cons]

theorem cap_honest_lower_domain (oracle : Oracle) (message : Message)
    (committed : RiscvZkvm.Rv64.MachineState) (positions : Positions)
    (roots : CapRootMap)
    (accepted : capLowerBatchRoots oracle.compression
      (capHonestLowerRecords message committed positions) (fun _ => none) = some roots)
    (group : Nat) :
    (roots group).isSome = true ↔
      ∃ index ∈ positions, (capGroup index).val = group := by
  rw [cap_lower_batch_domain _ _ _ _ accepted]
  simp only [Option.isSome_none, Bool.false_eq_true, false_or,
    capHonestLowerRecords, List.mem_map]
  constructor
  · rintro ⟨record, ⟨index, member, same⟩, chosen⟩
    subst record
    exact ⟨index, by simpa only [capOpenRequestedIndices, Finset.mem_sort] using member,
      chosen⟩
  · rintro ⟨index, member, chosen⟩
    refine ⟨capHonestLowerRecord message committed index,
      ⟨index, ?_, rfl⟩, chosen⟩
    simpa only [capOpenRequestedIndices, Finset.mem_sort] using member

end CommitGolfCandidate
