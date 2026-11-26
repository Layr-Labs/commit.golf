import CommitGolfCandidate.ReconstructedHonestCuts
import CommitGolfCandidate.ReconstructedCommitExact
import CommitGolfCandidate.Machine

namespace CommitGolfCandidate.Reconstruction.HonestObserve
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestCuts
attribute [local irreducible] ArtifactEncoding.decode

/-- A property that holds whenever a supported partial run is at one chosen PC. -/
def At (im : Image) (s : MachineState) (location : Word) (good : MachineState→Prop) : Prop :=
  ∀ f r, r∈support (execute im f s true) → r.exit=.unfinished → r.state.pc=location → good r.state

/-- Split a partial observation at every actual cut. The interior is disjoint
from the watched PC by construction. -/
theorem cuts (im : Image) (s : MachineState) (cut : Word→Bool) (location : Word) (good : MachineState→Prop)
    (included : cut location=true) (entry : s.pc=location → good s)
    (boundary : ∀ t, Reaches im true cut s t → At im t location good) : At im s location good := by
  intro fuel
  induction fuel generalizing s with
  | zero =>
    intro r run _ hit
    simp only [execute,support_pure,Set.mem_singleton_iff] at run
    subst r; exact entry hit
  | succ f ih =>
    intro r run live hit
    rw [show f+1=1+f by omega,execute_add,mem_support_bind_iff] at run
    obtain ⟨mid,first,rest⟩ := run
    by_cases cont : mid.exit=.unfinished
    · simp only [resume,cont,ite_true,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at rest
      obtain ⟨out,remain,rfl⟩ := rest
      cases stop : cut mid.state.pc with
      | true => exact boundary mid.state (.hit first cont stop) f out remain live hit
      | false =>
        apply ih mid.state (fun quo => False.elim (by rw [quo,included] at stop;cases stop))
          (fun t path => boundary t (.more first cont stop path)) out remain live hit
    · simp only [resume,cont,ite_false,support_pure,Set.mem_singleton_iff] at rest
      subst r; exact False.elim (cont live)

theorem segment {o : Oracle} {im : Image} {n : Nat} {s t : MachineState} (part : CommitExact.Segment o im n s t)
    {location : Word} {good : MachineState→Prop} (observes : At im s location good) (endAt : t.pc=location) : good t := by
  obtain ⟨c,q,run⟩ := part
  have h := run 0
  simp only [Nat.add_zero,execute,fixed_oracle_run_pure,map_pure] at h
  let r : Execution := ⟨.unfinished,t,c,q⟩
  have fixed : r∈support (fixedOracleRun o (execute im n s true)) := by
    rw [h,support_pure,Set.mem_singleton_iff]; simp [r,Execution.charge]
  simp only [fixedOracleRun,support_map,Set.mem_image] at fixed
  obtain ⟨counted,possible,eq⟩ := fixed
  have raw := writer_support (o.world.withAddCost Oracle.callCost) _ counted possible
  rw [eq] at raw
  exact observes n r raw rfl endAt

end CommitGolfCandidate.Reconstruction.HonestObserve
