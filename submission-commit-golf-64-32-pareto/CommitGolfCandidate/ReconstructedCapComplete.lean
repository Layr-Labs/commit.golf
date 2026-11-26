import CommitGolfCandidate.ReconstructedCapIterate
import CommitGolfCandidate.ReconstructedCapLevel

namespace CommitGolfCandidate.Reconstruction.CapComplete
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 16384
attribute [local irreducible] ArtifactEncoding.decode execute

/-- Complete nonfaulting execution of the shared multiproof cap and its ABI
return from the state produced by all lower records. -/
theorem run (o : Oracle) (key : Generator.Key) (msg : Message) (trap : CommitStorage.Trapdoor) (ps : Positions)
    (storage : CommitStorage.Stored o key msg trap) (nonempty : 0<ps.card) (salts : OpenedSalts ps) (s : MachineState)
    (ready : CapEntry.Ready s trap ps (CapIterate.records (LeafTree.tree o key msg) ps salts)) :
    ∃ n t c q, n≤62395 ∧
      (∀ fuel, fixedOracleRun o (execute (Artifact.submission.image .opening) (n+fuel) s true)=
        pure (⟨.success,t,c,q⟩ : Execution)) ∧
      ∀ c' q', Artifact.submission.openingSucceeded ⟨.success,t,c',q'⟩=true ∧
        Artifact.submission.readProof ⟨.success,t,c',q'⟩=Wire.bytes (Encoding.fields (LeafTree.tree o key msg) ps salts) :=
  CapIterate.complete o key msg trap ps (CapLevel.run o key msg trap ps storage nonempty) salts s ready

end CommitGolfCandidate.Reconstruction.CapComplete
