import CommitGolfCandidate.Execution
import CommitGolfCandidate.QuartetCommitLeafOps
import CommitGolfCandidate.QuartetCommitRanges
import CommitGolfCandidate.QuartetManifest
import CommitGolfCandidate.TwoPermutationCommitSetup
import CommitGolfCandidate.TwoPermutationCounted
import CommitGolfCandidate.TwoPermutationManifest
import CommitGolfCandidate.TwoPermutationPackedParents
import CommitGolfCandidate.TwoPermutationPackedParentControl

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 1700000
attribute [local irreducible] execute packedParentsTrace packedParentGroups

structure Carried (s : MachineState) : Prop where
  heap : s.getReg .x9=4294971424
  output : s.getReg .x8=4294971392
  stride : s.getReg .x19=536870912

theorem packed_sequence_keeps_output (remaining count : Nat) (state : MachineState) {out : MachineState}
    (reached : out ∈ support (packedParentsTrace remaining count state)) :
    out.getReg .x8=state.getReg .x8 := by
  induction count generalizing state with
  | zero =>
    simp only [packedParentsTrace,support_pure,Set.mem_singleton_iff] at reached
    rw [reached]
  | succ count ih =>
    simp only [packedParentsTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    exact (ih _ tail).trans (packed_parent_keeps_register state _ answer .x8 (by decide) (by decide))

theorem wide_parent_full_register (base : Word) (span groups : Nat)
    (state : MachineState) {out : MachineState}
    (reached : out ∈ support (packedParentGroups base span groups state)) :
    out.getReg .x8=state.getReg .x8 := by
  induction groups generalizing state with
  | zero =>
    simp only [packedParentGroups,support_pure,Set.mem_singleton_iff] at reached
    rw [reached]
  | succ groups ih =>
    simp only [packedParentGroups,mem_support_bind_iff] at reached
    obtain ⟨body,path,tail⟩ := reached
    have later := ih _ tail
    rw [MachineState.getReg_setPC] at later
    exact later.trans (packed_sequence_keeps_output _ _ _ (out := body) path)


end TwoPermutationPrototype.QuartetCommit
