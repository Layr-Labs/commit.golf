import CommitGolfCandidate.FastOpeningCertificate
/-! Pure proof encodings preserve binding and hiding; decode/encode cancellation also preserves completeness and query budgets. These lemmas are later specialized to the actual machine-derived scheme. -/
namespace CommitGolfCandidate.ProofCodec
open CommitGolf OracleComp OracleSpec
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

structure Codec where
  encode : Positions → Proof → Proof
  decode : Positions → Proof → Proof

def applyCodec (base : Scheme) (codec : Codec) : Scheme where
  Trapdoor := base.Trapdoor
  commit := base.commit
  opening td positions := codec.encode positions <$> base.opening td positions
  check root positions values proof := base.check root positions values (codec.decode positions proof)

def decodeClaim (codec : Codec) (claim : Scheme.Claim) : Scheme.Claim :=
  { root := claim.root
    positions₀ := claim.positions₀
    values₀ := claim.values₀
    proof₀ := codec.decode claim.positions₀ claim.proof₀
    positions₁ := claim.positions₁
    values₁ := claim.values₁
    proof₁ := codec.decode claim.positions₁ claim.proof₁ }

theorem codec_breaks (base : Scheme) (codec : Codec) (oracle : Oracle) (claim : Scheme.Claim) :
    (applyCodec base codec).Breaks oracle claim ↔ base.Breaks oracle (decodeClaim codec claim) := Iff.rfl

theorem codec_binding_game (codec : Codec) (adversary : Scheme.Adversary) :
    Scheme.bindingGame (decodeClaim codec <$> adversary)=
      (fun result : Oracle×Scheme.Claim×Nat => (result.1,decodeClaim codec result.2.1,result.2.2)) <$>
        Scheme.bindingGame adversary := by
  simp only [Scheme.bindingGame,oracle_run_map,map_bind,map_pure,bind_map_left]

theorem codec_binding (base : Scheme) (codec : Codec) (secure : base.Binding) :
    (applyCodec base codec).Binding := by
  intro adversary budget positive
  have bound := secure (decodeClaim codec <$> adversary) budget positive
  simpa only [codec_binding_game,Functor.map_map,Function.comp_def,codec_breaks] using bound

def liftChallenge {A : Type} {size : Nat} (challenge : Hiding.HidingChallenge A size) :
    Hiding.HidingChallenge (A×Positions) size where
  message₀ := challenge.message₀
  message₁ := challenge.message₁
  positions := challenge.positions
  size_eq := challenge.size_eq
  agree := challenge.agree
  aux := (challenge.aux,challenge.positions)

def liftAdversary {A O : Type} {size : Nat} (codec : Codec)
    (adversary : Hiding.HidingAdversary A O size) : Hiding.HidingAdversary (A×Positions) O size where
  choose := liftChallenge <$> adversary.choose
  observe aux root proof := adversary.observe aux.1 root (codec.encode aux.2 proof)

theorem codec_query_bound {A O : Type} {size : Nat} (codec : Codec)
    (adversary : Hiding.HidingAdversary A O size) (budget : Nat)
    (bound : Hiding.QueryBound adversary budget) :
    Hiding.QueryBound (liftAdversary codec adversary) budget := by
  intro first reached
  change first∈support (Hiding.counted (liftChallenge <$> adversary.choose)) at reached
  rw [Hiding.counted,costDist_map] at reached
  obtain ⟨original,originalReached,rfl⟩ := mem_support_map_peel
    (fun result : Hiding.HidingChallenge A size×Nat => (liftChallenge result.1,result.2))
    (Hiding.counted adversary.choose) reached
  have originalBound := bound original originalReached
  refine ⟨originalBound.1,?_⟩
  intro root proof last lastReached
  exact originalBound.2 root (codec.encode original.1.positions proof) last lastReached

theorem codec_experiment {A O : Type} {size : Nat} (base : Scheme) (codec : Codec)
    (adversary : Hiding.HidingAdversary A O size) (second : Bool) :
    Hiding.hidingExperiment (applyCodec base codec) adversary second=
      Hiding.hidingExperiment base (liftAdversary codec adversary) second := by
  simp only [Hiding.hidingExperiment,applyCodec,liftAdversary,liftChallenge,bind_map_left]

theorem codec_hiding (base : Scheme) (codec : Codec) (error : Nat→Nat→ℝ)
    (secure : base.Hiding error) : (applyCodec base codec).Hiding error := by
  refine ⟨secure.1,?_⟩
  intro size budget sizeBound A O adversary bounded
  have bound := secure.2 size budget sizeBound (A×Positions) O
    (liftAdversary codec adversary) (codec_query_bound codec adversary budget bounded)
  simpa only [codec_experiment] using bound
theorem codec_completeness (base : Scheme) (codec : Codec)
    (inverse : ∀ (oracle : Oracle) (td : base.Trapdoor) (positions : Positions)
      (result : Proof×Nat), result ∈ support (oracle.run (base.opening td positions)) →
      codec.decode positions (codec.encode positions result.1)=result.1)
    (complete : base.Completeness) : (applyCodec base codec).Completeness := by
  intro oracle message positions
  have original := (OracleComp.prEvent_eq_one_iff _ _).mp (complete oracle message positions)
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,applyCodec,oracle_run_map,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root,td⟩,commitCalls⟩,committed,opened⟩ := reached
  rw [support_map] at opened
  obtain ⟨encoded,⟨source,sourceReached,rfl⟩,returned⟩ := opened
  simp only [support_pure,Set.mem_singleton_iff] at returned
  subst result
  simp only [inverse oracle td positions source sourceReached]
  let honestResult : Scheme.HonestResult :=
    { accepted := (oracle.eval (base.check root positions (message.restrict positions) source.1)).1
      commitCalls := commitCalls
      openCalls := source.2
      checkCalls := (oracle.eval (base.check root positions (message.restrict positions) source.1)).2
      proofBytes := source.1.length }
  exact original honestResult (by
    simp only [Scheme.honest,mem_support_bind_iff]
    refine ⟨((root,td),commitCalls),committed,source,sourceReached,?_⟩
    simp only [support_pure,Set.mem_singleton_iff];rfl)
theorem codec_budgets (base : Scheme) (codec : Codec)
    (inverse : ∀ (oracle : Oracle) (td : base.Trapdoor) (positions : Positions)
      (result : Proof×Nat), result ∈ support (oracle.run (base.opening td positions)) →
      codec.decode positions (codec.encode positions result.1)=result.1)
    (complete : base.HonestBudgets) : (applyCodec base codec).HonestBudgets := by
  intro oracle message positions
  have original := (OracleComp.prEvent_eq_one_iff _ _).mp (complete oracle message positions)
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result reached
  simp only [Scheme.honest,applyCodec,oracle_run_map,mem_support_bind_iff] at reached
  obtain ⟨⟨⟨root,td⟩,commitCalls⟩,committed,opened⟩ := reached
  rw [support_map] at opened
  obtain ⟨encoded,⟨source,sourceReached,rfl⟩,returned⟩ := opened
  simp only [support_pure,Set.mem_singleton_iff] at returned
  subst result
  simp only [inverse oracle td positions source sourceReached]
  let honestResult : Scheme.HonestResult :=
    { accepted := (oracle.eval (base.check root positions (message.restrict positions) source.1)).1
      commitCalls := commitCalls
      openCalls := source.2
      checkCalls := (oracle.eval (base.check root positions (message.restrict positions) source.1)).2
      proofBytes := source.1.length }
  exact original honestResult (by
    simp only [Scheme.honest,mem_support_bind_iff]
    refine ⟨((root,td),commitCalls),committed,source,sourceReached,?_⟩
    simp only [support_pure,Set.mem_singleton_iff];rfl)
end CommitGolfCandidate.ProofCodec
