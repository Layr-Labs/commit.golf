import CommitGolf
import CommitGolf.Oracle.Tests
import CommitGolfBaseline
import Std.Tactic.BVDecide

/-! # Regression tests

The constants' values; runs of the Merkle baseline on an 8-leaf tree and of its `check` at full
depth; the fact, assumed by the statements, that VCVio computations never fail; and the axioms of
the baseline's certificate. -/

namespace CommitGolf.Tests
open OracleComp OracleSpec Baseline

/-! ### Constants -/

example : LENGTH = 16777216 := by decide
-- A Merkle compression leaves 1088 bits of capacity once two digests fill the state.
example : WIDTH - 2 * DIGEST_BITS = 1088 := by decide
example : COMMIT_BUDGET = 1677721600 ∧ OPEN_BUDGET BATCH = 10000 ∧ CHECK_BUDGET BATCH = 10000 := by
  decide
-- The baseline's scores: unpruned Merkle paths for `BATCH` positions.
example : BATCH * LOG_LENGTH * DIGEST_BYTES = 76800 ∧ BATCH * LOG_LENGTH = 2400 := by decide

/-! ### The baseline on a small tree -/

/-- A toy permutation, only for running code: XOR bits 256–511, rotated by one, into bits 0–255.
It leaves bits 256–511 unchanged, so it is an involution. It gives `C(L, R) = R ⊕ rotl₁ L`, which
depends on the order of the children. -/
private def mix (x : BitVec 1600) : BitVec 1600 :=
  x ^^^ (((x >>> 256).setWidth 256).rotateLeft 1).setWidth 1600

private theorem mix_mix (x : BitVec 1600) : mix (mix x) = x := by
  simp only [mix]; bv_decide

private def toyPerm : Perm := Function.Involutive.toPerm mix mix_mix

private def toyLeaves : List Digest := (List.range 8).map fun i => BitVec.ofNat DIGEST_BITS (i + 1)
private def toyTree : List (List Digest) := (toyPerm.eval (layers 3 toyLeaves)).1

-- The compression depends on the order of the children.
#guard (toyPerm.eval (compress 3 5)).1 != (toyPerm.eval (compress 5 3)).1

-- An 8-leaf tree has layers of sizes 8, 4, 2, 1, built with 7 compressions.
#guard toyTree.map List.length == [8, 4, 2, 1]
#guard (toyPerm.eval (layers 3 toyLeaves)).2 == 7

-- Every honest path climbs back to the root, with one compression per level.
#guard (List.range 8).all fun i =>
  let (root, calls) := toyPerm.eval (climb i (toyLeaves.getD i 0) (copath toyTree 3 i))
  root == rootOf toyTree && calls == 3

-- A wrong leaf value does not climb to the root.
#guard (List.range 8).all fun i =>
  (toyPerm.eval (climb i (toyLeaves.getD i 0 + 1) (copath toyTree 3 i))).1 != rootOf toyTree

-- Digests round-trip through their byte encoding.
#guard (Digest.ofBytes (Digest.toBytes (BitVec.ofNat DIGEST_BITS 0xdeadbeef))) ==
  BitVec.ofNat DIGEST_BITS 0xdeadbeef
#guard (Digest.toBytes (BitVec.ofNat DIGEST_BITS 0xdeadbeef)).length == DIGEST_BYTES

/-! ### `check` at full depth -/

private def sibs : List Digest := (List.range LOG_LENGTH).map fun k => BitVec.ofNat _ (1000 + k)
private def leaf : Digest := 7
private def rt : Commitment := (toyPerm.eval (climb 5 leaf sibs)).1
private def pf : Proof := sibs.flatMap Digest.toBytes
private def I : Positions := {⟨5, by decide⟩}

-- `check` accepts a valid path with `LOG_LENGTH` calls, and rejects a wrong length or value.
#guard toyPerm.eval (merkle.check rt I (fun _ => leaf) pf) == (true, LOG_LENGTH)
#guard toyPerm.eval (merkle.check rt I (fun _ => leaf) (pf ++ [0])) == (false, 0)
#guard !(toyPerm.eval (merkle.check rt I (fun _ => leaf + 1) pf)).1

/-! ### VCVio computations never fail

Statements 1–4 are stated as probability `1`. That reads as "always" only because
computations in the pinned VCVio cannot fail: no probability mass is lost to failure. A VCVio update
that added failure to `OracleComp` would break these checks. -/

example {α : Type} (c : ProbComp α) : Pr[⊥ | c] = 0 := probFailure_eq_zero
example (scheme : Scheme) (π : scheme.oracles.Realization) (m : Message) (I : Positions) :
    Pr[⊥ | scheme.honest π m I] = 0 := probFailure_eq_zero
example (adversary : Scheme.Adversary) : Pr[⊥ | Scheme.bindingGame adversary] = 0 :=
  probFailure_eq_zero

/-! ### The baseline's certificate

`merkle_certificate` proves `Certificate merkle 76800 2400`. Its transitive axioms must be exactly
the three the rules allow; `#guard_msgs` fails the build otherwise (in particular on `sorryAx`). -/

/-- info: 'CommitGolf.Baseline.merkle_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms merkle_certificate

/-! ### Compression baseline execution -/

private def toyHash (x : CompressionBaseline.Input) : CompressionBaseline.Digest :=
  x.setWidth DIGEST_BITS ^^^ ((x >>> DIGEST_BITS).setWidth DIGEST_BITS).rotateLeft 1
private def compressionTree :=
  (CompressionBaseline.Hash.eval toyHash (CompressionBaseline.layers 3 toyLeaves)).1

#guard compressionTree.map List.length == [8, 4, 2, 1]
#guard (CompressionBaseline.Hash.eval toyHash (CompressionBaseline.layers 3 toyLeaves)).2 == 7
#guard (List.range 8).all fun i =>
  let (root, calls) := CompressionBaseline.Hash.eval toyHash
    (CompressionBaseline.climb i (toyLeaves.getD i 0) (CompressionBaseline.copath compressionTree 3 i))
  root == CompressionBaseline.rootOf compressionTree && calls == 3
#guard (List.range 8).all fun i =>
  (CompressionBaseline.Hash.eval toyHash
    (CompressionBaseline.climb i (toyLeaves.getD i 0 + 1)
      (CompressionBaseline.copath compressionTree 3 i))).1 != CompressionBaseline.rootOf compressionTree

/-- info: 'CommitGolf.CompressionBaseline.merkle_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CompressionBaseline.merkle_certificate

end CommitGolf.Tests

-- The unified game preserves finite-domain binding without additional axioms.
/-- info: 'CommitGolf.Scheme.bindingProbability_eq_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms CommitGolf.Scheme.bindingProbability_eq_finite

/-! Regression checks for the hiding specification, not a secure VC construction. -/
namespace CommitGolf.HidingTests
open OracleComp OracleSpec CommitGolf.Hiding

-- A message-independent toy scheme witnesses that the definition is satisfiable for every
-- oracle family. It is deliberately not binding and is not a challenge submission.
private def constantScheme (F : OracleFamily) : Scheme where
  oracles := F
  Trapdoor := Unit
  commit _ := pure (0, ())
  opening _ _ := pure []
  check _ _ _ _ := pure true

private def constantSimulator (F : OracleFamily) : HidingSimulator (constantScheme F) :=
  fun _ _ => pure (0, [])

example (F : OracleFamily) :
    StatisticalHiding (constantScheme F) (constantSimulator F) (fun _ _ => 0) := by
  intro q t hq Aux Output A hbound
  have heq : realHidingExperiment (constantScheme F) A =
      idealHidingExperiment (constantScheme F) (constantSimulator F) A := by
    rfl
  rw [heq, tvDist_self]

private def challenge : HidingChallenge Unit 0 :=
  ⟨fun _ => 0, ∅, rfl, ()⟩

private abbrev R : OracleFamily := .randomOracleFixedOutput 2 (by decide)

-- One query in each stage must consume two calls in total, even for repeated inputs.
private def twoStage : HidingAdversary R Unit (BitVec 2) 0 where
  choose := do
    let _ ← (R.world.query (.inr []) :)
    return challenge
  observe _ _ _ := (R.world.query (.inr []) :)

private lemma first_support : support (counted twoStage.choose) =
    {(challenge, 1)} := by
  change support ((fun _ : BitVec 2 => (challenge, 1)) <$>
    (liftM (R.world.query (.inr [])) : OracleComp R.world (BitVec 2))) = _
  rw [support_map]
  simp

private lemma last_support (root : Commitment) (proof : Proof) :
    support (counted (twoStage.observe () root proof)) =
      {z | z.2 = 1} := by
  change support ((fun x : BitVec 2 => (x, 1)) <$>
    (liftM (R.world.query (.inr [])) : OracleComp R.world (BitVec 2))) = _
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
  have hl : ((0 : BitVec 2), 1) ∈
      support (counted (twoStage.observe () 0 [])) := by
    rw [last_support]; rfl
  have impossible := (h _ hf).2 0 [] _ hl
  norm_num at impossible

-- Ordinary computation and coins do not consume the public-query budget.
private def coinOnly : HidingAdversary R Unit Bool 0 where
  choose := pure challenge
  observe _ _ _ := do
    let x ← (R.world.query (.inl 1) :)
    return x.val == 0

example : QueryBound coinOnly 0 := by
  intro first hf
  have heq : counted coinOnly.choose =
      (pure (challenge, 0) : OracleComp R.world _) := rfl
  rw [heq] at hf
  have hf' := OracleComp.eq_of_mem_support_pure (challenge, 0) hf
  subst first
  refine ⟨by decide, ?_⟩
  intro root proof last hl
  have heq : counted (coinOnly.observe () root proof) =
      (fun x : Fin 2 => (x.val == 0, 0)) <$>
        (liftM (R.world.query (.inl 1)) : OracleComp R.world (Fin 2)) := rfl
  rw [heq] at hl
  obtain ⟨x, _, hx⟩ := OracleComp.mem_support_map_peel _ _ hl
  simp [hx]

-- Repeated queries across the two adversary stages reuse the same lazy cache.
private def remembers : HidingAdversary R (BitVec 2) (BitVec 2 × BitVec 2) 0 where
  choose := do
    let x ← (R.world.query (.inr []) :)
    return ⟨fun _ => 0, ∅, rfl, x⟩
  observe x _ _ := do
    let y ← (R.world.query (.inr []) :)
    return (x, y)

example : runHiding (constantScheme R) (realHidingExperiment (constantScheme R) remembers) =
    (do let x ← $ᵗ BitVec 2; return (x, x)) := by
  simp [realHidingExperiment, remembers, constantScheme]
  change runHiding (constantScheme R) (do
    let x ← (liftM (R.world.query (.inr [])) : OracleComp R.world (BitVec 2))
    let y ← (liftM (R.world.query (.inr [])) : OracleComp R.world (BitVec 2))
    return (x, y)) = _
  simp [runHiding, constantScheme, OracleFamily.initialState, OracleFamily.runShared,
    map_eq_bind_pure_comp]
  change ((do
    let x ← R.sharedAnswer []
    let y ← R.sharedAnswer []
    return ((x, y), 2)) : StateT R.State ProbComp ((BitVec 2 × BitVec 2) × Nat)).run ∅
      >>= (fun z => pure z.1.1) = _
  simp [OracleFamily.sharedAnswer, RandomOracleFixedOutput.answer, map_eq_bind_pure_comp]

-- Specialization preserves the exact oracle program, including its private randomness and
-- public queries. This checks the interface transport only, not a PPT claim for this profile.
example (scheme : Scheme) (simulate : HidingSimulator scheme) (n : Nat)
    (positions : Positions) (values : Values positions) :
    specialize
      (parameters := fun _ => parametersOfScheme scheme)
      (fun _ input => simulate input.1 input.2) scheme n rfl positions values =
        simulate positions values := rfl

-- A family may genuinely vary dimensions. Packing retains the parameter in both the input
-- and output, so a uniform witness cannot silently erase which family member was requested.
private def dimensions (n : Nat) : HidingParameters :=
  ⟨n, n + 1, n + 1, .idealXof⟩

private def zeroFamily : HidingSimulatorFamily dimensions := fun _ _ => pure (0, [])

example (n : Nat) (input : SimulatorInput (dimensions n)) :
    SecurityFamily.packProgram zeroFamily ⟨n, input⟩ =
      pure (⟨n, (0, [])⟩ : SecurityFamily.Output (fun n => SimulatorOutput (dimensions n))) := rfl

end CommitGolf.HidingTests
