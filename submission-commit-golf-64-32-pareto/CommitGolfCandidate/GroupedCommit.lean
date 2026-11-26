import CommitGolfCandidate.GroupedSetup
import CommitGolfCandidate.GroupedTailEval

/-!
# The whole commit run

Setup (key draw) | 2^24 leaf slots of the body (scan) | six post words | tail (level-21 loop, heap loop, root
copy, halt). Steps 40 + 185,356,288 + 6 + 14,942,621 = 200,298,955, cycles 43 + 460,292,096 + 6 + 44,302,742 =
504,594,887, oracle calls 39,276,544 + 4,194,303 = 43,470,847.
-/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.QuartetCommit (qSource)
set_option maxRecDepth 32000
set_option maxHeartbeats 1800000
attribute [local irreducible] execute image GroupedUpper.packedWideCommitImage scan tailBody

/-- Steps of the whole commit run (odd-quartet image). -/
def commitSteps : Nat := 200290336

theorem image_eq_packed : image=GroupedUpper.packedWideCommitImage :=
  exact_image.trans GroupedUpper.packed_manifest_image.symm

theorem tail_entry (s : MachineState) (r : Live s N) : TailEntry (tailPostPrefix s 6) := by
  obtain ⟨pc,sel,out,heap,cells,key⟩ := tail_post_regs s r
  exact ⟨pc.trans rfl,sel,out,heap,cells.trans (by unfold cellFirst;rfl),key⟩

def commitTrace (s : MachineState) : OracleComp World Execution := do
  let key ← liftM ($ᵗ Key : ProbComp Key)
  let leaves ← scan N 0 (readyState s key)
  let out ← tailBody (tailPostPrefix leaves 6)
  return ⟨.success,out,commitCycles,commitCalls⟩

attribute [local irreducible] readyState

theorem full_commit (s : MachineState) (e : CommitEntry s) (fuel : Nat) :
    execute image (commitSteps+fuel) s true = commitTrace s := by
  rw [show commitSteps+fuel=38+(185347071+(6+(14943221+fuel))) by unfold commitSteps;omega,setup_run s e]
  simp only [commitTrace,bind_assoc,pure_bind];apply bind_congr;intro key
  have read := ready_live s e key
  have run := run_scan N 0 _ (by decide) read (6+(14943221+fuel))
  rw [show S (0+N)-S 0=185347071 by decide,show C (0+N)-C 0=1324366847 by decide,
    show Q (0+N)-Q 0=39276544 by decide] at run
  rw [run];simp only [bind_assoc,pure_bind]
  apply bind_congr_of_forall_mem_support;intro leaves hit
  have last : Live leaves N := by simpa only [Nat.zero_add] using scan_post N 0 _ _ (by decide) read hit
  rw [tail_post_run leaves (by rw [last.pc];unfold startPC;rw [if_pos rfl]),image_eq_packed,
    tail_run (tailPostPrefix leaves 6) (tail_entry leaves last)]
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
