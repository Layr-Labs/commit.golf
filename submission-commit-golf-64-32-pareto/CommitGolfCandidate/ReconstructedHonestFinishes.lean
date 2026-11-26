import CommitGolfCandidate.ReconstructedHonestCuts

namespace CommitGolfCandidate.Reconstruction.HonestFinishes
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCuts HonestFlow

/-- A single ordinary instruction, or a public oracle syscall in mode zero,
cannot successfully halt. HALT is handled in the separately certified epilogue. -/
private theorem ongoing (im : Image) (s : MachineState) (op : Instruction) (coins : Bool)
    (read : fetch im s=some op) (pub : op=.base .ECALL → s.getReg .x5=0)
    (r : Execution) (run : r∈support (execute im 1 s coins)) : r.exit≠.success := by
  by_cases call : op=.base .ECALL
  · subst op
    rw [execute,read] at run
    simp only [pub rfl,ite_true] at run
    cases input : oracleInput s with
    | none => simp only [input,support_pure,Set.mem_singleton_iff] at run; subst r; intro h; cases h
    | some q =>
      simp only [input,mem_support_bind_iff] at run
      obtain ⟨_,_,run⟩ := run
      simp only [execute,support_pure,Set.mem_singleton_iff] at run
      obtain ⟨_,rfl,rfl⟩ := run; intro h; cases h
  · cases op with
    | base op =>
      cases op <;> simp only [execute,read] at run
      all_goals first | contradiction | skip
      all_goals split at run
      all_goals simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at run
      all_goals subst r; intro h; cases h
    | word _ _ _ _ | sraiw _ _ _ =>
      simp only [execute,read] at run
      split at run <;> simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at run <;> subst r <;> intro h <;> cases h

def SuccessPost (im : Image) (coins : Bool) (good : MachineState→Prop) (s : MachineState) :=
  ∀ f r, r∈support (execute im f s coins) → r.exit=.success → good r.state

/-- A property of successful final states crosses a checked block when every
actual reachable boundary supplies that property for its remaining execution. -/
theorem from_cut {im : Image} {active cut zero : Word→Bool} {rank : Word→Nat} {good : MachineState→Prop}
    (cert : Ranking im active cut zero rank) (s : MachineState) (coins : Bool) (entry : active s.pc=true)
    (safe : zero s.pc=true → s.getReg .x5=0)
    (boundary : ∀ t, Reaches im coins cut s t → SuccessPost im coins good t) : SuccessPost im coins good s := by
  intro f r run success
  induction f generalizing s r with
  | zero => simp only [execute,support_pure,Set.mem_singleton_iff] at run; subst r; cases success
  | succ f ih =>
    obtain ⟨op,read,dir,mode,_,edges⟩ := cert.step s entry
    rw [show f+1=1+f by omega,execute_add,mem_support_bind_iff] at run
    obtain ⟨mid,first,rest⟩ := run
    by_cases cont : mid.exit=.unfinished
    · simp only [resume,cont,ite_true,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at rest
      obtain ⟨out,tail,rfl⟩ := rest
      obtain ⟨target,clear⟩ := ((charged_successors im s op coins read dir (safe ∘ mode) mid first).2 cont)
      cases stop : cut mid.state.pc with
      | true => exact boundary _ (.hit first cont stop) f out tail success
      | false =>
        have edge := edges _ target
        simp only [stop,Bool.false_eq_true,false_or] at edge
        exact ih mid.state edge.1 (clear ∘ edge.2.2) (fun t w => boundary t (.more first cont stop w)) out tail success
    · simp only [resume,cont,ite_false,support_pure,Set.mem_singleton_iff] at rest
      subst r; exact False.elim (ongoing im s op coins read (safe ∘ mode) mid first success)

end CommitGolfCandidate.Reconstruction.HonestFinishes
