import CommitGolf

/-! Regression tests for the fixed oracle pair and the security definitions.
These toy functions test execution; they are not secure submissions. -/
namespace CommitGolf.Tests
open OracleComp OracleSpec

example : Entry = BitVec 2048 := rfl
example : Commitment = BitVec 256 := rfl

private def functions : Oracle := ⟨fun x => x.setWidth COMPRESSION_OUTPUT_LENGTH, Equiv.swap 7 9⟩

-- Both primitives can be used together. Every call, including inverse and repeats, costs one.
private def combined : OracleComp PublicSpec (BitVec COMPRESSION_OUTPUT_LENGTH × BitVec PERMUTATION_WIDTH × BitVec PERMUTATION_WIDTH) := do
  let hash ← (PublicSpec.query (.inl 7) :)
  let forward ← (PublicSpec.query (.inr (.inl (hash.setWidth PERMUTATION_WIDTH))) :)
  let inverse ← (PublicSpec.query (.inr (.inr forward)) :)
  return (hash, forward, inverse)
#guard functions.eval combined == ((7, 9, 7), 3)

private def repeated : OracleComp PublicSpec (BitVec COMPRESSION_OUTPUT_LENGTH × BitVec COMPRESSION_OUTPUT_LENGTH) := do
  let a ← (PublicSpec.query (.inl 3) :)
  let b ← (PublicSpec.query (.inl 3) :)
  return (a, b)
#guard functions.eval repeated == ((3, 3), 2)

example : Oracle.callCost (.inl 1) = 0 := rfl
example : Oracle.callCost (.inr (.inl 0)) = 1 := rfl
example : Oracle.callCost (.inr (.inr (.inl 0))) = 1 := rfl
example : Oracle.callCost (.inr (.inr (.inr 0))) = 1 := rfl

example : Oracle.sample = (do
    let compression ← $ᵗ Compression
    let permutation ← $ᵗ Perm
    return ⟨compression, permutation⟩) := rfl

example (adversary : Scheme.Adversary) : Scheme.bindingGame adversary = (do
    let oracle ← Oracle.sample
    let (claim, calls) ← oracle.run adversary
    return (oracle, claim, calls)) := rfl

example {α : Type} (c : ProbComp α) : Pr[⊥ | c] = 0 := probFailure_eq_zero
example (scheme : Scheme) (oracle : Oracle) (m : Message) (I : Positions) :
    Pr[⊥ | scheme.honest oracle m I] = 0 := probFailure_eq_zero
example (adversary : Scheme.Adversary) : Pr[⊥ | Scheme.bindingGame adversary] = 0 :=
  probFailure_eq_zero

end CommitGolf.Tests

/-! Regression checks for the hiding specification, not a secure VC construction. -/
namespace CommitGolf.HidingTests
open OracleComp OracleSpec CommitGolf.Hiding

-- A message-independent toy scheme witnesses that the definition is satisfiable for every
-- oracle pair. It is deliberately not binding and is not a challenge submission.
private def constantScheme : Scheme where
  Trapdoor := Unit
  commit _ := pure (0, ())
  opening _ _ := pure []
  check _ _ _ _ := pure true

example : constantScheme.Hiding (fun _ _ => 0) := by
  refine ⟨fun _ _ => le_refl 0, ?_⟩
  intro openingSize queryBudget _ AdversaryState Output adversary _
  have heq : hidingExperiment constantScheme adversary false =
      hidingExperiment constantScheme adversary true := rfl
  rw [heq, tvDist_self]

private def challenge : HidingChallenge Unit 0 :=
  ⟨fun _ => 0, fun _ => 0, ∅, rfl, rfl, ()⟩


-- One query in each stage must consume two calls in total, even for repeated inputs.
private def twoStage : HidingAdversary Unit (BitVec COMPRESSION_OUTPUT_LENGTH) 0 where
  choose := do
    let _ ← (World.query (.inr (.inl 0)) :)
    return challenge
  observe _ _ _ := (World.query (.inr (.inl 0)) :)

private lemma first_support : support (counted twoStage.choose) =
    {(challenge, 1)} := by
  change support ((fun _ : BitVec COMPRESSION_OUTPUT_LENGTH => (challenge, 1)) <$>
    (liftM (World.query (.inr (.inl 0))) : OracleComp World (BitVec COMPRESSION_OUTPUT_LENGTH))) = _
  rw [support_map]
  simp

private lemma last_support (root : Commitment) (proof : Proof) :
    support (counted (twoStage.observe () root proof)) =
      {z | z.2 = 1} := by
  change support ((fun x : BitVec COMPRESSION_OUTPUT_LENGTH => (x, 1)) <$>
    (liftM (World.query (.inr (.inl 0))) : OracleComp World (BitVec COMPRESSION_OUTPUT_LENGTH))) = _
  rw [support_map]
  ext ⟨x, n⟩
  simp [eq_comm]

example : QueryBound twoStage 2 := by
  intro first hf
  rw [first_support, Set.mem_singleton_iff] at hf
  subst first
  refine ⟨by decide, ?_⟩
  intro root proof last hl
  rw [last_support] at hl
  change last.2 = 1 at hl
  simp [hl]

example : ¬ QueryBound twoStage 1 := by
  intro h
  have hf : (challenge, 1) ∈ support (counted twoStage.choose) := by
    rw [first_support]; exact Set.mem_singleton _
  have hl : ((0 : BitVec COMPRESSION_OUTPUT_LENGTH), 1) ∈
      support (counted (twoStage.observe () 0 [])) := by
    rw [last_support]; rfl
  have impossible := (h _ hf).2 0 [] _ hl
  norm_num at impossible

-- Ordinary computation and coins do not consume the public-query budget.
private def coinOnly : HidingAdversary Unit Bool 0 where
  choose := pure challenge
  observe _ _ _ := do
    let x ← (World.query (.inl 1) :)
    return x.val == 0

example : QueryBound coinOnly 0 := by
  intro first hf
  have heq : counted coinOnly.choose =
      (pure (challenge, 0) : OracleComp World _) := rfl
  rw [heq] at hf
  have hf' := OracleComp.eq_of_mem_support_pure (challenge, 0) hf
  subst first
  refine ⟨by decide, ?_⟩
  intro root proof last hl
  have heq : counted (coinOnly.observe () root proof) =
      (fun x : Fin 2 => (x.val == 0, 0)) <$>
        (liftM (World.query (.inl 1)) : OracleComp World (Fin 2)) := rfl
  rw [heq] at hl
  obtain ⟨x, _, hx⟩ := OracleComp.mem_support_map_peel _ _ hl
  simp [hx]

-- The entire hiding experiment uses one fixed realization, even across stages.
private def remembers : HidingAdversary (BitVec COMPRESSION_OUTPUT_LENGTH) (BitVec COMPRESSION_OUTPUT_LENGTH × BitVec COMPRESSION_OUTPUT_LENGTH) 0 where
  choose := do
    let x ← (World.query (.inr (.inl 0)) :)
    return ⟨fun _ => 0, fun _ => 0, ∅, rfl, rfl, x⟩
  observe x _ _ := do
    let y ← (World.query (.inr (.inl 0)) :)
    return (x, y)

example (oracle : Oracle) :
    oracle.run (hidingExperiment constantScheme remembers false) =
      pure ((oracle.compression 0, oracle.compression 0), 2) := rfl

-- Empty openings allow different messages. The selector really changes the honest input.
private def differentMessages : HidingChallenge Unit 0 where
  message₀ := fun _ => 0
  message₁ := fun _ => 1
  positions := ∅
  size_eq := rfl
  agree := by funext i; exact False.elim (Finset.notMem_empty i.val i.property)
  aux := ()

private def leakingScheme : Scheme where
  Trapdoor := Unit
  commit message := pure ((message ⟨0, by decide⟩).setWidth DIGEST_BITS, ())
  opening _ _ := pure []
  check _ _ _ _ := pure true

private def observesRoot : HidingAdversary Unit Commitment 0 where
  choose := pure differentMessages
  observe _ root _ := pure root

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 4096 in
example : hidingExperiment leakingScheme observesRoot false = pure 0 := rfl
set_option exponentiation.threshold 2048 in
set_option maxRecDepth 4096 in
example : hidingExperiment leakingScheme observesRoot true = pure 1 := rfl

-- The challenge certificate always includes hiding.
example (scheme : Scheme) (proofBytes checkCalls : Nat)
    (certificate : Certificate scheme proofBytes checkCalls) :
    scheme.Hiding HIDING_ERROR := certificate.hidingProperty

end CommitGolf.HidingTests
