import CommitGolfCandidate.GroupedPhysicalBase
import CommitGolfCandidate.GroupedQMeaning
import CommitGolfCandidate.QuartetPhysicalInputs
import CommitGolfCandidate.QuartetRVModel
import CommitGolfCandidate.TwoPermutationRootBytes
import CommitGolfCandidate.MaterializedManifest

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.QuartetCommit (qSource qSalt qLeaf qUpper digestWords originalLeaf physicalHeap upper_sequence_semantics upper_groups_semantics UpperContent PaddedLeaves physical_heap_parent physical_heap_leaf packed_sequence_keeps_output wide_parent_full_register)
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 18000
set_option maxHeartbeats 1000000
attribute [local irreducible] readBuffer checkEvaluation qGroups qUnits scan fixedScan packedParentsTrace packedParentGroups rootPrefix physicalHeap originalLeaf readyState
def seededLeaves (o : Oracle) (m : Message) (k : Key) :=
  fixedScan o N 0 (readyState (actual.initialState .commit m) k)

private theorem fixed_supported (o : Oracle) (s : MachineState) (n j : Nat) (b : j+n≤N) :
    fixedScan o n j s∈support (scan n j s) := by
  let z : MachineState × Nat := (fixedScan o n j s,Q (j+n)-Q j)
  have hit : z∈support (o.run (scan n j s)) := by
    rw [fixed_scan_run o n j s b,support_pure,Set.mem_singleton_iff]
  exact writer_support (o.world.withAddCost Oracle.callCost) (scan n j s) z hit

private theorem seeded_summary (o : Oracle) (m : Message) (k : Key) (s : MachineState) (n : Nat) (bound : n≤N)
    (start : Live s 0) (good : Good o k m (memoryView s) 0) :
    Live (fixedScan o n 0 s) n ∧ Good o k m (memoryView (fixedScan o n 0 s)) n := by
  have b : 0+n≤N := by omega
  have live := scan_post n 0 s (fixedScan o n 0 s) b start (fixed_supported o s n 0 b)
  have endGood := scan_content o k m n 0 s b start good (by intro h;exact False.elim ((Nat.lt_irrefl 0) h))
  simpa only [Nat.zero_add] using And.intro live endGood

theorem seeded_content (o : Oracle) (m : Message) (k : Key) :
    Live (seededLeaves o m k) N ∧ Good o k m (memoryView (seededLeaves o m k)) N := by
  unfold seededLeaves
  exact seeded_summary o m k _ N le_rfl (ready_live _ ⟨rfl,rfl,rfl,rfl⟩ k) (initially_good o k m)
end TwoPermutationPrototype.Grouped
