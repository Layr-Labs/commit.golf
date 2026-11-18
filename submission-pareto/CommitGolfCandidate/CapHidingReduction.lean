import CommitGolf.Hiding

/-! Preserve the complete adaptive two-stage adversary while transforming its
observed proof bytes. Requested positions are retained alongside its private
state. The transformer is a pure function and adds no public or private query. -/
namespace CommitGolfCandidate
open CommitGolf OracleComp
set_option autoImplicit false

def capLiftHidingChallenge {State : Type} {openingSize : Nat}
    (challenge : Hiding.HidingChallenge State openingSize) :
    Hiding.HidingChallenge (State × Positions) openingSize where
  message₀ := challenge.message₀
  message₁ := challenge.message₁
  positions := challenge.positions
  size_eq := challenge.size_eq
  agree := challenge.agree
  aux := (challenge.aux,challenge.positions)

def capTransformAdversary {State Output : Type} {openingSize : Nat}
    (transform : Positions → Proof → Proof)
    (adversary : Hiding.HidingAdversary State Output openingSize) :
    Hiding.HidingAdversary (State × Positions) Output openingSize where
  choose := capLiftHidingChallenge <$> adversary.choose
  observe := fun state root proof => adversary.observe state.1 root (transform state.2 proof)

theorem cap_transform_query_bound {State Output : Type} {openingSize budget : Nat}
    (transform : Positions → Proof → Proof)
    (adversary : Hiding.HidingAdversary State Output openingSize)
    (bounded : Hiding.QueryBound adversary budget) :
    Hiding.QueryBound (capTransformAdversary transform adversary) budget := by
  intro first reached
  change first ∈ support
    (costDist (capLiftHidingChallenge <$> adversary.choose) ⟨Oracle.callCost⟩) at reached
  rw [costDist_map,support_map] at reached
  obtain ⟨original,possible,rfl⟩ := reached
  have originalBound := bounded original possible
  constructor
  · exact originalBound.1
  · intro root proof last observed
    exact originalBound.2 root (transform original.1.positions proof) last observed

end CommitGolfCandidate
