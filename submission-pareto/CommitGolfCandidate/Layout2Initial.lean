import CommitGolfCandidate.Layout2Table

namespace CommitGolfCandidate.Layout2
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype TwoPermutationPrototype.RV64
open TwoPermutationPrototype.Checker (check_scratch_word_zero)
open CommitGolfCandidate.Layout2Helpers (byte_at)
set_option maxRecDepth 6000
attribute [local irreducible] ArtifactEncoding.decode
set_option maxHeartbeats 1600000
def converted (τ : Tables) (i : CheckInput) : CheckInput := { i with proof:=convert τ i.positions.card i.proof }
@[simp] theorem converted_id (i : CheckInput) : converted identityTable i=i := by simp [converted]

private theorem same_low_load (x y : Submission) (i : CheckInput) (q : Nat) (fit : q<2^64)
    (same : x.inputBuffers .check i=y.inputBuffers .check i)
    (loX : q<dataBase (x.image .check)) (loY : q<dataBase (y.image .check)) :
    byte (x.initialState .check i) q=byte (y.initialState .check i) q := by
  refine (initial_input_byte x .check i q fit).trans (Eq.trans ?_ (initial_input_byte y .check i q fit).symm)
  unfold inputByte
  rw [same]
  split
  · rfl
  · simp [Nat.not_le_of_lt loX,Nat.not_le_of_lt loY]

theorem below_table (i : CheckInput) (q : Nat) (low : q<tableBase) :
    byte (candidate.initialState .check i) q=byte (QAssembly.submission.initialState .check i) q := by
  have old : (QAssembly.submission.image .check).data=ArtifactEncoding.decode 8 QuartetArtifact.checkData := rfl
  have layout : candidate.layout=QAssembly.submission.layout := rfl
  have buffers : candidate.inputBuffers .check i=QAssembly.submission.inputBuffers .check i := by
    simp only [Submission.inputBuffers,layout]
  apply same_low_load candidate QAssembly.submission i q (by unfold tableBase at low;omega) buffers
    (by rw [data_base];exact low)
  unfold dataBase
  rw [old,ArtifactEncoding.length_decode]
  change q<68719476736;unfold tableBase at low;omega

theorem scratch_clean (i : CheckInput) (j : Nat) (small : j<2136) :
    byte (candidate.initialState .check i) (scratchBase+j)=0 := by
  let a:=scratchBase+j
  rw [below_table i _ (by unfold scratchBase tableBase;omega)]
  have w := check_scratch_word_zero i (8*(a/8)) (by dsimp [a,scratchBase];omega)
  have e:=byte_at (QAssembly.submission.initialState .check i) (8*(a/8)) (a%8)
    (by omega) (by omega) (by dsimp [a,scratchBase];omega)
  rw [show 8*(a/8)+a%8=a by omega,w] at e
  simpa [byte,a,extractByte] using e

theorem other_proof (i : CheckInput) (p : Proof) (len : p.length=i.proof.length) (q : Nat) (small : q<2^64)
    (outside : q<proofBase ∨ proofBase+i.proof.length≤q) :
    byte (QAssembly.submission.initialState .check {i with proof:=p}) q =
      byte (QAssembly.submission.initialState .check i) q := by
  refine (initial_input_byte QAssembly.submission .check {i with proof:=p} q small).trans
    (Eq.trans ?_ (initial_input_byte QAssembly.submission .check i q small).symm)
  have none : ¬(QAssembly.submission.layout.proof≤q ∧ q<QAssembly.submission.layout.proof+i.proof.length) := by
    change ¬(proofBase≤q ∧ q<proofBase+i.proof.length);omega
  simp only [inputByte,Submission.inputBuffers,List.find?_cons,len,none,decide_false,cond_false,List.find?_nil]

end CommitGolfCandidate.Layout2
