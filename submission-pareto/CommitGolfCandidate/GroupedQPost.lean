import CommitGolfCandidate.GroupedQLoop

/-! Registers other than `x10`/`x12` survive the record's packed parent loop (levels 20..1). -/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 850000

theorem parents_keep_register (remaining count : Nat) (s : MachineState) (reg : Reg)
    (keptSource : .x10≠reg) (keptTarget : .x12≠reg)
    {out : MachineState} (reached : out ∈ support (packedParentsTrace remaining count s)) :
    out.getReg reg=s.getReg reg := by
  induction count generalizing s with
  | zero =>
    simp only [packedParentsTrace,support_pure,Set.mem_singleton_iff] at reached
    subst out; rfl
  | succ count ih =>
    simp only [packedParentsTrace,mem_support_bind_iff] at reached
    obtain ⟨answer,_,tail⟩ := reached
    exact (ih _ tail).trans (packed_parent_keeps_register s _ answer reg keptSource keptTarget)

theorem parent_groups_keep_register (base : Word) (span groups : Nat) (s : MachineState) (reg : Reg)
    (keptSource : .x10≠reg) (keptTarget : .x12≠reg)
    {out : MachineState} (reached : out ∈ support (packedParentGroups base span groups s)) :
    out.getReg reg=s.getReg reg := by
  induction groups generalizing s with
  | zero =>
    simp only [packedParentGroups,support_pure,Set.mem_singleton_iff] at reached
    subst out; rfl
  | succ groups ih =>
    simp only [packedParentGroups,mem_support_bind_iff] at reached
    obtain ⟨body,path,tail⟩ := reached
    have rest := ih _ tail
    rw [MachineState.getReg_setPC] at rest
    exact rest.trans (parents_keep_register _ _ _ reg keptSource keptTarget path)

end TwoPermutationPrototype.Grouped
