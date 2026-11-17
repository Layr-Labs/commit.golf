import CommitGolfCandidate.NonceCheckScheme
import CommitGolfCandidate.CapBindingSecurity

namespace CommitGolfCandidate
open CommitGolf OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 500000

def nonceExpandClaim (claim : Scheme.Claim) : Scheme.Claim :=
  {claim with
    proof₀:=NonceCodec.expand 0 claim.positions₀.card claim.proof₀
    proof₁:=NonceCodec.expand 0 claim.positions₁.card claim.proof₁}

theorem nonce_breaks_expand (oracle : Oracle) (claim : Scheme.Claim)
    (broken : nonceCompressedProgram.scheme.Breaks oracle claim) :
    capProgram.scheme.Breaks oracle (nonceExpandClaim claim) := by
  refine ⟨broken.1,?_,?_⟩
  · exact nonce_check_acceptance_expand oracle
      ⟨claim.root,claim.positions₀,claim.values₀,claim.proof₀⟩ broken.2.1
  · exact nonce_check_acceptance_expand oracle
      ⟨claim.root,claim.positions₁,claim.values₁,claim.proof₁⟩ broken.2.2

theorem nonce_binding_game_map (adversary : Scheme.Adversary) :
    Scheme.bindingGame (nonceExpandClaim <$> adversary)=
      (fun result : Oracle × Scheme.Claim × Nat => (result.1,nonceExpandClaim result.2.1,result.2.2)) <$>
        Scheme.bindingGame adversary := by
  simp only [Scheme.bindingGame,oracle_run_map,bind_map_left,map_bind,map_pure]

theorem nonce_compressed_binding : nonceCompressedProgram.scheme.Binding := by
  intro adversary budget positive
  have bound:=cap_program_binding (nonceExpandClaim <$> adversary) budget positive
  rw [nonce_binding_game_map] at bound
  simp only [Functor.map_map,Function.comp_def] at bound
  apply le_trans _ bound
  apply prEvent_mono_of_support
  intro result _ winning
  exact ⟨nonce_breaks_expand result.1 result.2.1 winning.1,winning.2⟩
end CommitGolfCandidate
