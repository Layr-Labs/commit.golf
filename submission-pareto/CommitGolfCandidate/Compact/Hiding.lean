import CommitGolfCandidate.Compact.OpeningCodec
import CommitGolfCandidate.ProofCodec
import CommitGolfCandidate.CompactProofCodec
/-! Statistical hiding for the actual compact machine scheme, transported through its proved opening encoding; the game never calls verification. -/
namespace CommitGolfCandidate.Compact
open CommitGolf OracleComp

def checkedCodecScheme : Scheme :=
  { (ProofCodec.applyCodec CommitGolfCandidate.submission.scheme NonceCodec.codec) with
    opening := submission.scheme.opening }

theorem scheme_opening_encoded (td : BitVec (8*submission.sizes.trapdoor)) (positions : Positions) :
    submission.scheme.opening td positions=
      NonceCodec.encode positions.card <$> CommitGolfCandidate.submission.scheme.opening td positions := by
  rw [opening_scheme_execution td positions,CommitGolfCandidate.opening_scheme_execution td positions]
  simp only [map_pure]
  exact congrArg (fun proof : Proof => (pure proof : OracleComp World Proof))
    (opening_proof_encoded td positions)

theorem checked_codec_scheme_eq : checkedCodecScheme=
    ProofCodec.applyCodec CommitGolfCandidate.submission.scheme NonceCodec.codec := by
  have openingEq : submission.scheme.opening =
      (ProofCodec.applyCodec CommitGolfCandidate.submission.scheme NonceCodec.codec).opening := by
    funext td positions
    exact scheme_opening_encoded td positions
  unfold checkedCodecScheme
  rw [openingEq]


theorem compact_hiding : submission.scheme.Hiding HIDING_ERROR := by
  have secure : checkedCodecScheme.Hiding HIDING_ERROR := by
    rw [checked_codec_scheme_eq]
    exact ProofCodec.codec_hiding _ _ _ CommitGolfCandidate.submission_hiding
  exact secure
end CommitGolfCandidate.Compact
