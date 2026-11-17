import CommitGolfCandidate.CapHonestLowerBytes
import CommitGolfCandidate.CapRequestedGroups

/-! Honest lower records never fail the duplicate-group check. A generic
partial-map invariant carries agreement with the same reference heap through
each insertion; repeated groups are compared rather than silently discarded. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
set_option maxHeartbeats 200000

def CapRootsAgree (expected : Nat → Digest) (roots : CapRootMap) : Prop :=
  ∀ group value, roots group = some value → value = expected group

theorem cap_insert_agrees (expected : Nat → Digest) (roots : CapRootMap)
    (agree : CapRootsAgree expected roots) (group : Nat) :
    ∃ next, capInsert roots group (expected group) = some next ∧
      CapRootsAgree expected next := by
  cases prior : roots group with
  | none =>
      refine ⟨fun index => if index = group then some (expected group) else roots index,
        by simp [capInsert, prior], ?_⟩
      intro index value known
      by_cases same : index = group
      · subst index
        simp only [ite_true, Option.some.injEq] at known
        exact known.symm
      · exact agree index value (by simpa only [if_neg same] using known)
  | some value =>
      have correct := agree group value prior
      refine ⟨roots, ?_, agree⟩
      simp only [capInsert, prior, correct, ite_true]

theorem cap_lower_batch_agrees (compress : Compression) (permutation : Perm)
    (records : List CapLowerRecord)
    (expected : Nat → Digest)
    (honest : ∀ record ∈ records, record.root compress permutation = expected (capGroup record.index).val)
    (roots : CapRootMap) (agree : CapRootsAgree expected roots) :
    ∃ finalRoots, capLowerBatchRoots compress permutation records roots = some finalRoots ∧
      CapRootsAgree expected finalRoots := by
  induction records generalizing roots with
  | nil => exact ⟨roots, rfl, agree⟩
  | cons head rest ih =>
      obtain ⟨next, inserted, nextAgree⟩ := cap_insert_agrees expected roots agree
        (capGroup head.index).val
      have headRoot := honest head (by simp)
      have laterHonest : ∀ record ∈ rest,
          record.root compress permutation = expected (capGroup record.index).val := by
        intro record member
        exact honest record (by simp [member])
      obtain ⟨finalRoots, later, finalAgree⟩ := ih laterHonest next nextAgree
      refine ⟨finalRoots, ?_, finalAgree⟩
      simp only [capLowerBatchRoots, headRoot, inserted]
      exact later

theorem cap_honest_lower_collection (oracle : Oracle) (message : Message)
    (committed : MachineState) (correct : CommittedState oracle message committed)
    (positions : Positions) :
    ∃ roots, capLowerBatchRoots oracle.compression oracle.permutation
        (capHonestLowerRecords message committed positions) (fun _ => none) = some roots ∧
      CapRootsAgree (fun group => heapDigest committed 4294971424 (256+group)) roots := by
  apply cap_lower_batch_agrees
  · intro record member
    obtain ⟨index, requested, rfl⟩ := List.mem_map.mp member
    exact cap_honest_lower_root oracle message committed correct index
  · intro group value known
    cases known

end CommitGolfCandidate
