import CommitGolfCandidate.QuartetPhysical
import CommitGolfCandidate.QuartetChainMemory
import CommitGolfCandidate.QuartetChainRepresentation

/-! The Quartet commitment with chain salts (generator layer from submission c28dd9ca): exact
public-call count, the commit distribution over a uniform 192-bit key, the transcript refinement
and the hiding clause. -/
namespace TwoPermutationPrototype.QuartetCommit
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.RV64 TwoPermutationPrototype.Sampling
open CommitGolfCandidate.Permutation.NonceChain (Key actualNonces)
set_option maxRecDepth 16384
set_option maxHeartbeats 1700000
local instance quartetCommitDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
attribute [local irreducible] checkEvaluation QuartetLeaves.groups qPhase qGroups packedParentsTrace packedParentGroups rootPrefix packedOutput

theorem counted_body (oracle : Oracle) (ready : MachineState) :
    RunPublic oracle (commitBody ready) 41943039 := by
  unfold commitBody
  apply run_bind_public _ _ _ 33554432 8388607 (QuartetLeaves.counted_groups ..); intro leaves
  apply run_bind_public _ _ _ 4194304 4194303 (q_phase_counted ..);intro quad
  apply run_bind_public _ _ _ 127 4194176 (counted_packed_parents ..);intro finalPre
  exact run_bind_public _ _ _ 4194176 0 (counted_packed_groups ..) (fun _ => run_pure_public ..)

attribute [local irreducible] commitBody

theorem counted_trace (oracle : Oracle) (initial : MachineState) :
    oracle.run (commitTrace initial) =
      (do let k ← $ᵗ Key
          return (packedOutput oracle (QuartetChain.chainFinalReady oracle.permutation initial k),43468241)) := by
  unfold commitTrace
  rw [oracle_run_coins_bind]
  apply bind_congr
  intro k
  have expand : oracle.run (QuartetChain.expansion initial k) =
      pure (QuartetChain.evalChain oracle.permutation 0 (QuartetChain.chainInitial initial k) QuartetChain.nonceChainCount,
        QuartetChain.nonceChainCount) := QuartetChain.chain_fixed_run ..
  rw [oracle_run_bind,expand,pure_bind]
  simp only
  rw [oracle_run_bind,show oracle.run (commitBody _) = _ from counted_body oracle _,pure_bind]
  simp only [oracle_run_pure,pure_bind]
  unfold packedOutput QuartetChain.chainFinalReady
  rfl

noncomputable def commitTrapdoor (oracle : Oracle) (msg : Message) (k : Key) : BitVec (8*actual.sizes.trapdoor) :=
  (actual.readCommit (packedOutput oracle (QuartetChain.chainFinalReady oracle.permutation (actual.initialState .commit msg) k))).2

attribute [local irreducible] commitTrace physicalHeap prePrefix QuartetChain.chainFinalReady

private theorem selected_run {α : Type} (oracle : Oracle) (s : MachineState) (f : Execution → α) :
    fixedOracleRun oracle (f <$> commitTrace s) =
      (do let k ← $ᵗ Key; pure (f (packedOutput oracle (QuartetChain.chainFinalReady oracle.permutation s k)))) := by
  rw [fixed_oracle_run_map];unfold fixedOracleRun;rw [counted_trace]
  simp only [map_bind,map_pure]

private theorem physical_pair (oracle : Oracle) (msg : Message) (k : Key) :
    actual.readCommit (packedOutput oracle (QuartetChain.chainFinalReady oracle.permutation (actual.initialState .commit msg) k)) =
      (physicalHeap oracle msg (actualNonces oracle.permutation k) 1,commitTrapdoor oracle msg k) := by
  have frame := QuartetChain.final_content oracle msg k
  rw [commitTrapdoor]
  exact Prod.ext (physical_results oracle msg _ _ frame.1 frame.2).1 rfl

theorem fixed_key_distribution (oracle : Oracle) (msg : Message) :
    fixedOracleRun oracle (actual.scheme.commit msg) =
      (do let k ← $ᵗ Key
          pure (physicalHeap oracle msg (actualNonces oracle.permutation k) 1,commitTrapdoor oracle msg k)) := by
  let s:=actual.initialState .commit msg
  have equality:=congrArg (fun p : OracleComp World Execution => fixedOracleRun oracle (actual.readCommit <$> p)) (artifact_run msg)
  refine equality.trans ((selected_run oracle s actual.readCommit).trans ?_)
  apply bind_congr;intro k
  exact congrArg (fun pair => (pure pair : ProbComp (Commitment × BitVec (8*actual.sizes.trapdoor)))) (physical_pair oracle msg k)

/-- The commitment's distribution: heap and trapdoor of the chain salts of a uniform key. -/
theorem tape_distribution (oracle : Oracle) (msg : Message) :
    fixedOracleRun oracle (actual.scheme.commit msg) =ᵈ
      (do let k ← $ᵗ Key
          pure (physicalHeap oracle msg (actualNonces oracle.permutation k) 1,commitTrapdoor oracle msg k)) := by
  rw [fixed_key_distribution]

theorem commit_really_refines : Sampling.Quartet.ChainQuartetRefines actual.scheme := by
  apply QuartetRV.chain_transcript_refines actual QuartetRV.manifest_abi commitTrapdoor
  · intro oracle msg
    simpa only [physicalHeap] using tape_distribution oracle msg
  · intro oracle msg k i
    have frame := QuartetChain.final_content oracle msg k
    exact (physical_results oracle msg _ _ frame.1 frame.2).2.2.2 i
  · intro oracle msg k i
    have frame := QuartetChain.final_content oracle msg k
    have val := (physical_results oracle msg _ _ frame.1 frame.2).2.2.1 i
    simpa only [commitTrapdoor,originalLeaf,Sampling.Quartet.leafAt,dif_pos i.isLt,Fin.eta] using val
  · intro oracle msg k n lo hi
    have frame := QuartetChain.final_content oracle msg k
    have val := (physical_results oracle msg _ _ frame.1 frame.2).2.1 n lo hi
    simpa only [commitTrapdoor,physicalHeap] using val

theorem actual_hiding : actual.scheme.Hiding (fun _ budget => min 1 (((budget : ℝ)+1)/2^120)) :=
  Sampling.Quartet.scheme_hiding_of_chain actual.scheme commit_really_refines

end TwoPermutationPrototype.QuartetCommit
