import CommitGolfCandidate.ChainedRootExecution

/-! Register and terminal-PC postconditions of all 24 native parent levels. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def ParentSaved (reg : Reg) : Prop :=
  reg ∉ ([.x1,.x4,.x6,.x7,.x14,.x15,.x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30] : List Reg)

theorem stage_register (s out : MachineState) (h : Height) (reached : out ∈ support (stageTrace h s))
    (reg : Reg) (kept : ParentSaved reg) : out.getReg reg = s.getReg reg := by
  simp only [stageTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reached
  obtain ⟨before,last,rfl⟩ := reached
  rw [shift_register before reg (by simp_all [ParentSaved])]
  exact heap_level_register s before h _ last reg (by simp_all [ParentSaved])

theorem parent_levels_register (remaining : Nat) (s out : MachineState)
    (reached : out ∈ support (parentLevels remaining s)) (reg : Reg) (kept : ParentSaved reg) :
    out.getReg reg = s.getReg reg := by
  induction remaining generalizing s with
  | zero =>
    simp only [parentLevels,support_pure,Set.mem_singleton_iff] at reached
    subst out
    rfl
  | succ remaining ih =>
    simp only [parentLevels,mem_support_bind_iff] at reached
    obtain ⟨mid,first,last⟩ := reached
    exact (ih mid last).trans (stage_register s mid _ first reg kept)

theorem parent_levels_pc (remaining : Nat) (small : remaining ≤ 24) (positive : 0 < remaining)
    (s out : MachineState)
    (ready : HeapLevelReady s (heightAt remaining) (heightCount (heightAt remaining)))
    (reached : out ∈ support (parentLevels remaining s)) : out.pc = 186568 := by
  induction remaining generalizing s with
  | zero => omega
  | succ remaining ih =>
    simp only [parentLevels,mem_support_bind_iff] at reached
    obtain ⟨mid,first,last⟩ := reached
    cases remaining with
    | zero =>
      simp only [parentLevels,support_pure,Set.mem_singleton_iff] at last
      subst out
      simp only [stageTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at first
      obtain ⟨before,node,rfl⟩ := first
      rw [shift_pc,heap_level_pc s before _ _ ready node]
      rfl
    | succ n =>
      exact ih (by omega) (by omega) mid (stage_next (n+1) (by omega) (by omega) s mid ready first) last

end CommitGolfCandidate.Chained.Native
