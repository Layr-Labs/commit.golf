import CommitGolfCandidate.QuartetCommitQLoop

namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
set_option maxRecDepth 8192
set_option maxHeartbeats 850000
attribute [local irreducible] qAfter

theorem q_units_saved (s : MachineState) (g count : Nat) (reg : Reg) (src : reg≠.x10) (dst : reg≠.x12)
    {out : MachineState} (hit : out ∈ support (qUnits count g s)) : out.getReg reg=s.getReg reg := by
  induction count generalizing s g with
  | zero => simp only [qUnits,support_pure,Set.mem_singleton_iff] at hit;subst out;rfl
  | succ n ih =>
    simp only [qUnits,mem_support_bind_iff] at hit
    obtain ⟨answer,_,rest⟩ := hit
    exact (ih _ (g+1) rest).trans (q_saved s g answer reg src dst)

theorem q_groups_saved (s : MachineState) (k count : Nat) (reg : Reg) (src : reg≠.x10) (dst : reg≠.x12)
    {out : MachineState} (hit : out ∈ support (qGroups count k s)) : out.getReg reg=s.getReg reg := by
  induction count generalizing s k with
  | zero => simp only [qGroups,support_pure,Set.mem_singleton_iff] at hit;subst out;rfl
  | succ n ih =>
    simp only [qGroups,mem_support_bind_iff] at hit
    obtain ⟨mid,path,rest⟩ := hit
    have tail := ih _ (k+1) rest
    rw [MachineState.getReg_setPC] at tail
    exact tail.trans (q_units_saved s (512*k) 512 reg src dst path)

theorem q_groups_end (s : MachineState) (count k : Nat) (finish : k+count=8192) (positive : 0<count)
    (r : QRegs s (512*k)) (pc : s.pc=quadPC 0) {out : MachineState}
    (hit : out ∈ support (qGroups count k s)) : QRegs out 4194304 ∧ out.pc=wordPC 46765 := by
  induction count generalizing s k with
  | zero => omega
  | succ n ih =>
    simp only [qGroups,mem_support_bind_iff] at hit
    obtain ⟨mid,path,rest⟩ := hit
    obtain ⟨next,_⟩ := q_segment_post s (512*k) 0 512 r pc path
    let after := mid.setPC (qLatchPC k)
    have nextRegs : QRegs mid (512*(k+1)) := by simpa only [Nat.mul_succ] using next
    have regs : QRegs after (512*(k+1)) := ⟨nextRegs.source,nextRegs.dest,nextRegs.selector,
      nextRegs.size,nextRegs.primitive,nextRegs.stop⟩
    cases n with
    | zero =>
      simp only [qGroups,support_pure,Set.mem_singleton_iff] at rest;subst out
      have last : k+1=8192 := by omega
      rw [last] at regs
      exact ⟨regs,by change qLatchPC k=_;rw [qLatchPC,if_pos last]⟩
    | succ n =>
      exact ih after (k+1) (by omega) (by omega) regs (by change qLatchPC k=_;rw [qLatchPC,if_neg (by omega)]) rest
end TwoPermutationPrototype.QuartetCommit
