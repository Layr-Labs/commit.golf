import CommitGolfCandidate.P4Commit
import CommitGolfCandidate.GroupedKeyLive
import CommitGolfCandidate.MixedWidthParentMeaning
import CommitGolfCandidate.TwoPermutationRootBytes
import CommitGolfCandidate.TwoPermutationSubmission
import CommitGolfCandidate.CountingCoins

/-! The P4 commitment as a function of the key: the leaves are the fixed grouped scan (2a19be00's
`GroupedSeededLeaves`), the tail is 04680e02's parent sweep and root copy. The serialized commitment is the root of
the mixed-width tree over two-permutation leaves with counter-mode salts, every heap node is in the trapdoor, and
the key sits in the first tape words, where the opener reads it. -/

namespace TwoPermutationPrototype.Grouped
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.CounterSalt (salts)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

abbrev actual : Submission := Artifact.submission

def seededLeaves (o : Oracle) (m : Message) (k : Key) :=
  fixedScan o N 0 (keyReady (actual.initialState .commit m) k)

private theorem fixed_supported (o : Oracle) (s : MachineState) (n j : Nat) (b : j+n≤N) :
    fixedScan o n j s∈support (scan n j s) := by
  let z : MachineState × Nat := (fixedScan o n j s,Q (j+n)-Q j)
  have hit : z∈support (o.run (scan n j s)) := by
    rw [fixed_scan_run o n j s b,support_pure,Set.mem_singleton_iff]
  exact writer_support (o.world.withAddCost Oracle.callCost) (scan n j s) z hit

theorem entry (m : Message) : CommitEntry (actual.initialState .commit m) := ⟨rfl,rfl,rfl,rfl⟩

private theorem seeded_summary (o : Oracle) (m : Message) (k : Key) (s : MachineState) (n : Nat) (bound : n≤N)
    (start : Live s 0) (good : Good o k m (memoryView s) 0) :
    Live (fixedScan o n 0 s) n ∧ Good o k m (memoryView (fixedScan o n 0 s)) n := by
  have b : 0+n≤N := by omega
  have live := scan_post n 0 s (fixedScan o n 0 s) b start (fixed_supported o s n 0 b)
  have endGood := scan_content o k m n 0 s b start good (by intro h;exact False.elim ((Nat.lt_irrefl 0) h))
  simpa only [Nat.zero_add] using And.intro live endGood

theorem seeded_content (o : Oracle) (m : Message) (k : Key) :
    Live (seededLeaves o m k) N ∧ Good o k m (memoryView (seededLeaves o m k)) N := by
  unfold seededLeaves
  exact seeded_summary o m k _ N le_rfl (ready_live _ (entry m) k) (initially_good o k m)

def packedOutput (o : Oracle) (leaves : MachineState) : Execution :=
  ⟨.success,(checkEvaluation o (postLeaves leaves)).1,600134811,51859455⟩

theorem tail_counted (o : Oracle) (s : MachineState) : RunPublic o (postLeaves s) 16777215 := by
  unfold postLeaves
  apply run_bind_public _ _ _ (32768*448) (16513*127) (counted_full_width_groups ..);intro full
  exact run_bind_public _ _ _ (16513*127) 0 (counted_packed_groups ..) (fun _ => run_pure_public ..)

theorem commit_execution (initial : MachineState) (e : CommitEntry initial) (fuel : Nat) :
    execute image (237118623+fuel) initial true = commitTrace initial := by
  rw [show 237118623+fuel=21+(184688639+(5+(3+(44041087+(8388857+(11+fuel)))))) by omega,prologue_run initial e]
  unfold commitTrace
  apply bind_congr;intro k
  rw [body_run _ (ready_live initial e k)]
  simp only [bind_assoc,pure_bind,Execution.charge]

theorem commit_of_image (program : Submission) (im : program.image .commit=image)
    (allowance : 237118623≤program.steps .commit) (m : Message) (e : CommitEntry (program.initialState .commit m)) :
    program.run .commit m=commitTrace (program.initialState .commit m) := by
  change execute (program.image .commit) (program.steps .commit) _ true=_
  rw [im,show program.steps .commit=237118623+(program.steps .commit-237118623) by omega]
  exact commit_execution _ e _

theorem commit_run (m : Message) : actual.run .commit m=commitTrace (actual.initialState .commit m) :=
  commit_of_image _ exact_image.symm (by decide) m (entry m)

attribute [local irreducible] fixedScan postLeaves checkEvaluation keyReady

theorem counted_body (o : Oracle) (ready : MachineState) :
    o.run (do let state ← body ready; return (⟨.success,state,600134811,51859455⟩ : Execution)) =
      pure (⟨.success,(checkEvaluation o (postLeaves (fixedScan o N 0 ready))).1,600134811,51859455⟩,51859455) := by
  unfold body
  simp only [bind_assoc]
  rw [oracle_run_bind,fixed_scan_run _ _ _ _ (by decide),pure_bind];dsimp only
  rw [oracle_run_bind,show o.run (postLeaves _)=_ from tail_counted o _,pure_bind]
  simp only [oracle_run_pure,pure_bind]
  rw [show Q (0+N)-Q 0+(16777215+0)=51859455 by decide]

theorem counted_commit (o : Oracle) (m : Message) :
    o.run (actual.run .commit m)=(do let k ← $ᵗ Key;return (packedOutput o (seededLeaves o m k),51859455)) := by
  rw [commit_run m]
  unfold commitTrace;rw [oracle_run_coins_bind];apply bind_congr;intro k
  rw [counted_body]
  rfl

end TwoPermutationPrototype.Grouped
