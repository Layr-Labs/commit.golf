import CommitGolfCandidate.ReconstructedOpeningView
import CommitGolfCandidate.ReconstructedHidingComplete
import CommitGolfCandidate.ReconstructedEmpty

namespace CommitGolfCandidate.Reconstruction.OpeningView
open CommitGolf CommitGolf.Riscv OracleComp TwoPermutationPrototype.Sampling
open Generator
set_option maxRecDepth 12000
attribute [local irreducible] ArtifactEncoding.decode Riscv.execute

private theorem no_fields (tree : Encoding.Tree) (salts : OpenedSalts ∅) : Wire.bytes (Encoding.fields tree ∅ salts)=[] := by
  apply List.length_eq_zero_iff.mp
  rw [Wire.byte_count,Encoding.all_bits]
  rw [Finset.sort_empty]
  change alignedBytes (Frontier.cursor [])=0
  decide +kernel

theorem empty_view (o : Oracle) (key : Key) (msg : Message) : (view o key msg ∅).2=[] := no_fields _ _

private theorem empty_read (s : RiscvZkvm.Rv64.MachineState) :
    Artifact.submission.readProof ⟨.success,emptyFinal s,5,0⟩=[] := by
  have size : ((emptyFinal s).getReg .x11).toNat=0 := rfl
  simp [Submission.readProof,size]

theorem empty_emits (o : Oracle) (key : Key) (msg : Message) (t : CommitStorage.Trapdoor) :
    fixedOracleRun o (Artifact.submission.scheme.opening t ∅)=pure (view o key msg ∅).2 := by
  rw [empty_view]
  change fixedOracleRun o (Artifact.submission.readProof <$> Artifact.submission.run .opening (t,∅))=_
  rw [run_empty_opening,map_pure,empty_read]
  exact fixed_oracle_run_pure o _

/-- Once physical byte serialization has been established on nonempty legal inputs,
the official hiding field follows for the submitted machine, including empty openings. -/
theorem secure (emits : ∀ (o : Oracle) (key : Key) (msg : Message) (t : CommitStorage.Trapdoor) (ps : Positions),
    0<ps.card → CommitStorage.Stored o key msg t →
    fixedOracleRun o (Artifact.submission.scheme.opening t ps)=pure (view o key msg ps).2) :
    Artifact.submission.scheme.Hiding HIDING_ERROR := by
  apply HidingTape.hiding_of_reconstructed_transcript _ Encoding.build
  apply transcript
  intro o k msg t ps stored
  by_cases positive : 0<ps.card
  · exact emits o k msg t ps positive stored
  · have e : ps=∅ := Finset.card_eq_zero.mp (by omega)
    subst ps
    exact empty_emits o k msg t

end CommitGolfCandidate.Reconstruction.OpeningView
