import CommitGolfCandidate.QuartetCommitQFrame
import CommitGolfCandidate.TwoPermutationHeapInvariant
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64
open CommitGolfCandidate (checkEvaluation check_evaluation_bind check_evaluation_pure)
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
attribute [local irreducible] checkEvaluation qAfter packBuffer

theorem q_units_content (oracle : Oracle) (before : Memory) (children : Nat → Words 4) (s : MachineState) (g count : Nat)
    (limit : g+count≤4194304) (ready : PaddedLeaves before children) (inv : QuadPrefix oracle before children s g) :
    QuadPrefix oracle before children (checkEvaluation oracle (qUnits count g s)).1 (g+count) := by
  induction count generalizing s g with
  | zero => simpa only [qUnits,check_evaluation_pure,Nat.add_zero] using inv
  | succ n ih =>
    simp only [qUnits,CommitGolfCandidate.check_evaluation_public_bind]
    rw [show g+(n+1)=g+1+n by omega]
    exact ih _ (g+1) (by omega) (quad_prefix_step oracle before children s g (by omega) ready inv)

private theorem qprefix_setpc (oracle : Oracle) (before : Memory) (children : Nat → Words 4) (s : MachineState)
    (n : Nat) (pc : Word) (r : QuadPrefix oracle before children s n) : QuadPrefix oracle before children (s.setPC pc) n :=
  ⟨r.upper,r.high⟩

attribute [local irreducible] qUnits

theorem q_groups_content (oracle : Oracle) (before : Memory) (children : Nat → Words 4) (s : MachineState) (k count : Nat)
    (limit : k+count≤12300) (ready : PaddedLeaves before children) (inv : QuadPrefix oracle before children s (4+341*k)) :
    QuadPrefix oracle before children (checkEvaluation oracle (qGroups count k s)).1 (4+341*(k+count)) := by
  induction count generalizing s k with
  | zero => simpa only [qGroups,check_evaluation_pure,Nat.add_zero] using inv
  | succ n ih =>
    rw [qGroups,check_evaluation_bind,show k+(n+1)=k+1+n by omega]
    apply ih _ (k+1) (by omega)
    have step := q_units_content oracle before children s (4+341*k) 341 (by omega) ready inv
    have shifted := qprefix_setpc oracle before children _ (4+341*k+341) (qLatchPC k) step
    simpa only [Nat.mul_succ,Nat.add_assoc] using shifted

theorem q_units_counted (oracle : Oracle) (s : MachineState) (g count : Nat) : RunPublic oracle (qUnits count g s) count := by
  induction count generalizing s g with
  | zero => rw [qUnits];exact run_pure_public ..
  | succ n ih =>
    rw [qUnits,show n+1=1+n by omega]
    exact run_bind_public _ _ _ 1 n (run_query_public ..) (fun _ => ih _ _)

theorem q_groups_counted (oracle : Oracle) (s : MachineState) (k count : Nat) : RunPublic oracle (qGroups count k s) (341*count) := by
  induction count generalizing s k with
  | zero => exact run_pure_public ..
  | succ n ih =>
    rw [qGroups,show 341*(n+1)=341+341*n by omega]
    exact run_bind_public _ _ _ 341 _ (q_units_counted ..) (fun _ => ih _ _)

attribute [local irreducible] qGroups

private theorem q_phase_content_aux (oracle : Oracle) (before : Memory) (children : Nat → Words 4) (s : MachineState)
    (count : Nat) (bound : count≤12300)
    (ready : PaddedLeaves before children) (inv : QuadPrefix oracle before children s 0) :
    QuadPrefix oracle before children (checkEvaluation oracle (do
      let mid ← qUnits 4 0 (s.setPC (quadPC 337))
      qGroups count 0 (mid.setPC (quadPC 0)))).1 (4+341*count) := by
  rw [check_evaluation_bind]
  have first := q_units_content oracle before children (s.setPC (quadPC 337)) 0 4 (by decide) ready
    (qprefix_setpc oracle before children s 0 (quadPC 337) inv)
  let mid := (checkEvaluation oracle (qUnits 4 0 (s.setPC (quadPC 337)))).1
  simpa only [Nat.zero_add] using q_groups_content oracle before children (mid.setPC (quadPC 0)) 0 count (by omega) ready
    (qprefix_setpc oracle before children mid 4 (quadPC 0) first)

theorem q_phase_content (oracle : Oracle) (before : Memory) (children : Nat → Words 4) (s : MachineState)
    (ready : PaddedLeaves before children) (inv : QuadPrefix oracle before children s 0) :
    QuadPrefix oracle before children (checkEvaluation oracle (qPhase s)).1 4194304 :=
  q_phase_content_aux oracle before children s 12300 (by decide) ready inv

theorem q_phase_counted (oracle : Oracle) (s : MachineState) : RunPublic oracle (qPhase s) 4194304 := by
  rw [qPhase,show 4194304=4+341*12300 by decide]
  exact run_bind_public _ _ _ 4 _ (q_units_counted ..) (fun _ => q_groups_counted ..)

end TwoPermutationPrototype.QuartetCommit
