import CommitGolfCandidate.QuartetCommitQPost
import CommitGolfCandidate.QuartetCommitLeafLatch
import CommitGolfCandidate.QuartetCommitUpperImage

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 16384
set_option maxHeartbeats 1700000
attribute [local irreducible] execute qPhase qGroups qUnits QuartetLeaves.groups packedParentsTrace packedParentGroups rootPrefix

structure Carried (s : MachineState) : Prop where
  heap : s.getReg .x9=4294971424
  output : s.getReg .x8=4294971392
  stride : s.getReg .x19=536870912

theorem start_q (before : MachineState) (r : StartLeafRegs before) {s : MachineState}
    (hit : s ∈ support (QuartetLeaves.groups 4096 0 before)) :
    s.pc=wordPC 45224 ∧ (qStartPrefix s 3).pc=wordPC 45227 ∧ QRegs (qStartPrefix s 3) 0 ∧ Carried (qStartPrefix s 3) := by
  obtain ⟨wherePC,keep⟩ := QuartetLeaves.groups_post before 4096 0 (by decide)
    (QuartetLeaves.entry_regs _ r) (by decide) hit
  have carry : Carried s := ⟨(keep .x9 (by simp [QuartetLeaves.SavedReg])).trans r.heap,(keep .x8 (by simp [QuartetLeaves.SavedReg])).trans r.output,
    (keep .x19 (by simp [QuartetLeaves.SavedReg])).trans r.stride⟩
  refine ⟨wherePC,?_,?_,⟨carry.heap,carry.output,carry.stride⟩⟩
  · change s.pc+4+4+4=wordPC 45227;rw [wherePC];rfl
  · constructor
    · change s.getReg .x21+0=_;rw [keep .x21 (by simp [QuartetLeaves.SavedReg]),r.quartet];rfl
    · change s.getReg .x9 + (s.getReg .x19 >>> (2 : Nat))=_;rw [carry.heap,carry.stride];rfl
    · exact (keep .x5 (by simp [QuartetLeaves.SavedReg])).trans r.selector
    · exact (keep .x11 (by simp [QuartetLeaves.SavedReg])).trans r.size
    · exact (keep .x13 (by simp [QuartetLeaves.SavedReg])).trans r.primitive
    · exact (keep .x24 (by simp [QuartetLeaves.SavedReg])).trans r.stop

theorem start_upper (before : MachineState) (r : QRegs before 0) (pc : before.pc=wordPC 45227)
    (carry : Carried before) {s : MachineState} (hit : s ∈ support (qPhase before)) :
    s.pc=wordPC 46765 ∧ (upStartPrefix s 6).pc=191180 ∧ ParentRegs (upStartPrefix s 6) 4194303 ∧
      (upStartPrefix s 6).getReg .x8=4294971392 := by
  obtain ⟨regs,here⟩ := q_phase_end before r hit
  have stride := (q_phase_saved before .x19 (by decide) (by decide) hit).trans carry.stride
  have heap := (q_phase_saved before .x9 (by decide) (by decide) hit).trans carry.heap
  have output := (q_phase_saved before .x8 (by decide) (by decide) hit).trans carry.output
  refine ⟨here,?_,?_,output⟩
  · change s.pc+4+4+4+4+4+4=_;rw [here];rfl
  · refine ⟨?_,?_,regs.selector,rfl,rfl,heap⟩
    · change s.getReg .x12+signExtend12 4032=_;rw [regs.dest];rfl
    · change s.getReg .x12-(s.getReg .x19 >>> (2 : Nat))+signExtend12 4064=_;rw [regs.dest,stride];rfl

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
