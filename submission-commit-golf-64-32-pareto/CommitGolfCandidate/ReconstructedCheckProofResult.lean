import CommitGolfCandidate.ReconstructedCheckEmptyTrace
import CommitGolfCandidate.ReconstructedCheckLaunchGate
import CommitGolfCandidate.ReconstructedCheckCertificateFields

namespace CommitGolfCandidate.Reconstruction.CheckProofResult
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckRecorded CheckLoader
open TwoPermutationPrototype.Sampling TwoPermutationPrototype.Checker
set_option maxRecDepth 10000
set_option maxHeartbeats 1250000
attribute [local irreducible] execute ArtifactEncoding.decode

def Valid (o : Oracle) (input : CheckInput) (rs : List PublicRow) :=
  rs.length≤2^31 ∧ ∀ p : {k // k∈input.positions},Nonempty (Binding.Opening o p.val (input.values p) input.commitment rs)

def Report (o : Oracle) (input : CheckInput) :=
  let obs:=checkObservation Artifact.submission o input
  obs.1.1.exit≠.unfinished ∧ (obs.1.1.exit= .success → obs.2≤2^31 ∧
    ∀ p : {k // k∈input.positions},Nonempty (Binding.Opening o p.val (input.values p) input.commitment obs.1.2))

def End (o : Oracle) (s : MachineState) (n : Nat) (exit : Riscv.Exit) := ∀ fuel,
  let obs:=observation o (n+fuel) s
  obs.1.1.exit=exit ∧ obs.1.2=[] ∧ obs.2=0

theorem publish (o : Oracle) (input : CheckInput) (fits : input.proof.length≤Artifact.submission.sizes.proof)
    (t : MachineState) (n m : Nat) (rs : List PublicRow) (e : Riscv.Exit)
    (room : n+m≤274877906944) (pre : Segment o n (initial input) t rs) (final_ : End o t m e)
    (finite : e≠.unfinished) (valid : e=.success→Valid o input rs) : Report o input := by
  let f:=274877906944-(n+m)
  have split : 274877906944=n+(m+f):=by dsimp [f];omega
  obtain ⟨cost,run⟩:=pre
  obtain ⟨last,trace,queries⟩:=final_ f
  unfold Report
  rw [CheckEmptyTrace.within o input fits,split,run]
  simp only [Execution.charge,trace,queries,List.append_nil,Nat.add_zero,last]
  exact ⟨finite,valid⟩

theorem reject (o : Oracle) (input : CheckInput) (fits : input.proof.length≤Artifact.submission.sizes.proof)
    (t : MachineState) (n m : Nat) (rs : List PublicRow)
    (room : n+m≤274877906944) (pre : Segment o n (initial input) t rs) (last : CheckLaunchGate.Reject o m t) : Report o input := by
  apply publish o input fits t n m rs .failure room pre _ (by decide) (fun h=>by cases h)
  intro f;have h:=last f;exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem emptyInput (o : Oracle) (input : CheckInput) (fits : input.proof.length≤Artifact.submission.sizes.proof) (zero : input.positions.card=0) :
    Report o input := by
  obtain ⟨_,q⟩:=CheckEmptyTrace.traces o input zero fits
  refine ⟨CheckEmptyTrace.finishes o input zero fits,fun _=>⟨by omega,?_⟩⟩
  intro p;have pos : 0 < input.positions.card:=Finset.card_pos.mpr ⟨p.val,p.property⟩
  omega

theorem tooLarge (o : Oracle) (input : CheckInput) (bad : ¬input.proof.length≤Artifact.submission.sizes.proof) : Report o input := by
  have fail:=CheckEmptyTrace.oversized o input bad
  dsimp only [Report];rw [fail];exact ⟨by decide,fun h=>by cases h⟩

end CommitGolfCandidate.Reconstruction.CheckProofResult
