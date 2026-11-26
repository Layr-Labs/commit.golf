import CommitGolfCandidate.ReconstructedCommitOutcome
import CommitGolfCandidate.ReconstructedLeafProjection

namespace CommitGolfCandidate.Reconstruction.OpeningView
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling
open HidingTape Generator
local instance discrete {α : Type} : MeasurableSpace α := ⊤
attribute [local irreducible] Riscv.execute ArtifactEncoding.decode
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

noncomputable def view (o : Oracle) (k : Key) (msg : Message) (positions : Positions) :=
  pinnedHonestView Encoding.build o.compression (BiPermutation.equiv TwoPermutationPrototype.Sampling.Block o.permutation) msg positions
    (actualTape o.permutation k)

theorem root (o : Oracle) (k : Key) (msg : Message) (positions : Positions) :
    Binding.pack (LeafTree.tree o k msg 0 1) = (view o k msg positions).1 := by
  rw [LeafProjection.reference_tree]
  rfl

private theorem grouped {T : Type} (o : Oracle) (commit : OracleComp World Execution)
    (read : Execution → Commitment × T) (opener : T → OracleComp World Proof) :
    fixedOracleRun o (do
      let (r,t) ← read <$> commit
      let pf ← opener t
      pure (r,pf)) =
    (fixedOracleRun o commit >>= fun e => Prod.mk (read e).1 <$> fixedOracleRun o (opener (read e).2)) := by
  rw [fixed_oracle_run_bind,fixed_oracle_run_map,bind_map_left]
  apply bind_congr
  intro e
  cases pair : read e with
  | mk r t =>
    change fixedOracleRun o (opener t >>= fun pf => pure (r,pf)) = _
    rw [bind_pure_comp,fixed_oracle_run_map]

/-- Projecting out the private state after a completed commitment preserves the uniform
key distribution and the shared fixed oracle used by both stages of the hiding game. -/
theorem transcript
    (emits : ∀ (o : Oracle) (k : Key) (msg : Message) (t : CommitStorage.Trapdoor) (ps : Positions),
      CommitStorage.Stored o k msg t →
      fixedOracleRun o (Artifact.submission.scheme.opening t ps) = pure (view o k msg ps).2) :
    HidingTape.KeyedTranscriptRefines Artifact.submission.scheme Encoding.build := by
  intro o msg ps
  let next (e : Execution) := (Prod.mk (Artifact.submission.readCommit e).1) <$>
    fixedOracleRun o (Artifact.submission.scheme.opening (Artifact.submission.readCommit e).2 ps)
  have rewriteTranscript : fixedOracleRun o (executableTranscript Artifact.submission.scheme msg ps) =
      (fixedOracleRun o (Artifact.submission.run .commit msg) >>= next) := by
    exact grouped o (Artifact.submission.run .commit msg) Artifact.submission.readCommit
      (fun t => Artifact.submission.scheme.opening t ps)
  rw [rewriteTranscript]
  let expected := fun k => (pure (view o k msg ps) : ProbComp _)
  have equal := CommitMachine.key_average o msg next expected (by
    intro k e done
    simp only [next,expected,emits o k msg _ ps done.contents,map_pure,done.output]
    rw [root o k msg ps])
  have converted := @SampleableType.map_uniformSample_evalDistEq_of_bijective Key Key
    inferInstance HidingTape.transcriptKeys id Function.bijective_id
  have transport := converted.bind_left expected
  rw [id_map] at transport
  exact (EvalDistEq.of_evalDist_eq equal).trans transport

end CommitGolfCandidate.Reconstruction.OpeningView
