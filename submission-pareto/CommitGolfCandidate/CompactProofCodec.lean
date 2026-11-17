import CommitGolfCandidate.NoncePadding
import CommitGolfCandidate.NonceCodec
import CommitGolfCandidate.ProofCodec
/-! The original machine’s zero padding supplies the inverse law required by the generic proof-encoding security transport. -/
namespace CommitGolfCandidate.NonceCodec
open CommitGolf OracleComp

def codec : ProofCodec.Codec := ⟨fun positions => encode positions.card,
  fun positions => decode positions.card⟩

theorem opening_good (td : BitVec (8*submission.sizes.trapdoor)) (positions : Positions) :
    Good positions.card (submission.readProof (openingResult td positions)) :=
  good_of_records _ _ (opening_proof_length td positions) (opening_padding td positions)

theorem decoded_opening (td : BitVec (8*submission.sizes.trapdoor)) (positions : Positions) :
    codec.decode positions <$> (codec.encode positions <$> submission.scheme.opening td positions)=
      submission.scheme.opening td positions := by
  rw [opening_scheme_execution]
  simp only [map_pure,codec]
  rw [decode_encode _ _ (opening_good td positions)]
theorem codec_inverse (oracle : Oracle) (td : submission.scheme.Trapdoor)
    (positions : Positions) (result : Proof×Nat)
    (reached : result ∈ support (oracle.run (submission.scheme.opening td positions))) :
    codec.decode positions (codec.encode positions result.1)=result.1 := by
  rw [opening_scheme_execution td positions,oracle_run_pure] at reached
  simp only [support_pure,Set.mem_singleton_iff] at reached
  subst result
  exact decode_encode _ _ (opening_good td positions)

theorem compact_completeness : (ProofCodec.applyCodec submission.scheme codec).Completeness :=
  ProofCodec.codec_completeness _ _ codec_inverse submission_completeness

theorem compact_budgets : (ProofCodec.applyCodec submission.scheme codec).HonestBudgets :=
  ProofCodec.codec_budgets _ _ codec_inverse submission_honest_budgets

theorem compact_binding : (ProofCodec.applyCodec submission.scheme codec).Binding :=
  ProofCodec.codec_binding _ _ submission_binding
end CommitGolfCandidate.NonceCodec
