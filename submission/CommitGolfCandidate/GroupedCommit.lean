import CommitGolfCandidate.GroupedSetup
import CommitGolfCandidate.GroupedTailEval

/-!
# The whole commit run

Setup (key draw) | 2^24 leaf slots of the body (scan) | tail (level-21 loop, heap loop, root copy, halt).
Steps 33 + 187,449,344 + 14,942,749, cycles 36 + 462,385,152 + 44,302,870 = 506,688,058,
oracle calls 39,276,544 + 4,194,303 = 43,470,847.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource)
set_option maxRecDepth 32000
set_option maxHeartbeats 1800000
attribute [local irreducible] execute image GroupedUpper.packedWideCommitImage scan tailBody

/-- Steps of the whole commit run (programs-final-v2). -/
def commitSteps : Nat := 202392126

theorem image_eq_packed : image=GroupedUpper.packedWideCommitImage :=
  exact_image.trans GroupedUpper.packed_manifest_image.symm

theorem tail_entry (s : MachineState) (r : Live s N) : TailEntry s where
  pc := by rw [r.pc];unfold startPC;rw [if_pos rfl];rfl
  selector := r.selector
  out := r.out
  heap := r.heapBase
  cells := r.quartet.trans (by unfold qSource cellFirst;rfl)
  key := r.counter.trans (by rfl)

def commitTrace (s : MachineState) : OracleComp World Execution := do
  let key ← liftM ($ᵗ Key : ProbComp Key)
  let leaves ← scan N 0 (readyState s key)
  let out ← tailBody leaves
  return ⟨.success,out,commitCycles,commitCalls⟩

attribute [local irreducible] readyState

theorem full_commit (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute image (commitSteps+fuel) s true = commitTrace s := by
  rw [show commitSteps+fuel=33+(187449344+(14942749+fuel)) by unfold commitSteps;omega,setup_run s e]
  simp only [commitTrace,bind_assoc,pure_bind];apply bind_congr;intro key
  have read := ready_live s e key
  have run := run_scan N 0 _ (by decide) read (14942749+fuel)
  rw [show S (0+N)-S 0=187449344 by decide,show C (0+N)-C 0=462385152 by decide,
    show Q (0+N)-Q 0=39276544 by decide] at run
  rw [run];simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support;intro leaves hit
  have last := scan_post N 0 _ _ (by decide) read hit
  rw [image_eq_packed,tail_run leaves (tail_entry leaves (by simpa only [Nat.zero_add] using last))]
  simp only [bind_assoc,pure_bind,Execution.charge,commitCycles,commitCalls]

theorem commit_of_image (program : Submission) (im : program.image .commit=image)
    (allowance : commitSteps≤program.steps .commit) (m : Message) (e : CommitEntry (program.initialState .commit m)) :
    program.run .commit m = commitTrace (program.initialState .commit m) := by
  change execute (program.image .commit) (program.steps .commit) _ true=_
  rw [im, show program.steps .commit=commitSteps+(program.steps .commit-commitSteps) by omega]
  exact full_commit _ e _

theorem actual_commit (m : Message) : K1Artifact.submission.run .commit m =
    commitTrace (K1Artifact.submission.initialState .commit m) :=
  commit_of_image _ exact_image.symm (by decide) m ⟨rfl,rfl,rfl,rfl⟩

theorem commit_resources (m : Message) (z : Execution) (reachable : z∈support (K1Artifact.submission.run .commit m)) :
    z.exit=.success ∧ z.cycles=commitCycles ∧ z.oracleCalls≤COMMIT_BUDGET := by
  rw [actual_commit] at reachable
  simp only [commitTrace,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at reachable
  obtain ⟨_,_,_,_,_,_,rfl⟩:=reachable
  exact ⟨rfl,rfl,show commitCalls≤COMMIT_BUDGET by decide⟩

end TwoPermutationPrototype.Grouped
