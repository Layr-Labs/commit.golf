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

example {α : Type} (c : ProbComp α) : prFail (c) = 0 := OracleComp.prFail_eq_zero _
example (scheme : Scheme) (oracle : Oracle) (m : Message) (I : Positions) :
    prFail (scheme.honest oracle m I) = 0 := OracleComp.prFail_eq_zero _
example (adversary : Scheme.Adversary) : prFail (Scheme.bindingGame adversary) = 0 :=
  OracleComp.prFail_eq_zero _

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
  let : MeasurableSpace Output := ⊤
  have heq : hidingExperiment constantScheme adversary false =
      hidingExperiment constantScheme adversary true := rfl
  rw [heq, measureTVDist_self]

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
example (submission : Submission) (proofBytes commitCycles openingCycles : Nat)
    (certificate : Certificate submission proofBytes commitCycles openingCycles) :
    submission.scheme.Hiding HIDING_ERROR := certificate.hidingProperty

end CommitGolf.HidingTests

namespace CommitGolf.RiscvTests
open OracleComp OracleSpec Riscv RiscvZkvm.Rv64

private def oracle : Oracle := ⟨fun x => x.setWidth COMPRESSION_OUTPUT_LENGTH, Equiv.swap 0 9⟩
-- Fix coins to zero only in these deterministic interpreter regression tests.
private def fixed : QueryImpl World Id
  | .inl n => pure (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inr q => oracle.answer q

private def addi (rd rs immediate : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((immediate % 4096) * 2 ^ 20 + rs * 2 ^ 15 + rd * 2 ^ 7 + 0x13)
private def halt : List (BitVec 32) := [addi 5 0 1, addi 10 0 0, 0x73]
private def runSmall (code : List (BitVec 32)) (state : MachineState := initialMachine) : Execution :=
  Id.run (simulateQ fixed (execute ⟨code, []⟩ 20 state))
private def syscallState (kind bytes : Nat) : MachineState :=
  ((initialMachine.setReg .x11 (BitVec.ofNat 64 bytes)).setReg .x12 256).setReg .x13
    (BitVec.ofNat 64 kind)
private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

#eval do
  let halted := runSmall [addi 5 0 1, 0x73]
  check "HALT is charged" (halted.exit == Exit.success && halted.cycles == 2)
  let compressed := runSmall (0x73 :: halt) (syscallState 0 64 |>.setByte 0 7)
  check "compression routing and charge"
    (compressed.exit == Exit.success && compressed.cycles == 11 && compressed.oracleCalls == 1 &&
      compressed.state.getByte 256 == 7)
  let forward := runSmall (0x73 :: halt) (syscallState 1 200)
  check "forward permutation routing and charge"
    (forward.exit == Exit.success && forward.cycles == 11 && forward.oracleCalls == 1 &&
      forward.state.getByte 256 == 9)
  let inverse := runSmall (0x73 :: halt) (syscallState 2 200 |>.setByte 0 9)
  check "inverse permutation routing and charge"
    (inverse.exit == Exit.success && inverse.cycles == 11 && inverse.oracleCalls == 1 &&
      inverse.state.getByte 256 == 0)
  let randomState := (syscallState 0 9).setReg .x5 2
  let random := runSmall (0x73 :: halt) randomState
  check "private randomness costs cycles but no public queries"
    (random.exit == Exit.success && random.cycles == 6 && random.oracleCalls == 0)
  check "multiplication and division cost four cycles"
    ((runSmall ([0x020000b3, 0x020040b3, 0x020070bb, 0x000000b3] ++ halt)).cycles == 16)
  let looping := runSmall [0x0000006f]
  check "step exhaustion is not success" (looping.exit == Exit.unfinished && looping.cycles == 20)
  for (kind, bytes) in [(0, 63), (1, 32), (2, 199), (3, 200)] do
    let invalid := runSmall (0x73 :: halt) (syscallState kind bytes)
    check "invalid oracle arguments reject without queries"
      (invalid.exit == Exit.failure && invalid.oracleCalls == 0 && invalid.cycles == 1)
  check "unaligned oracle input rejects"
    ((runSmall (0x73 :: halt) (syscallState 0 64 |>.setReg .x10 1)).exit == Exit.failure)
  check "oracle output beyond memory rejects"
    ((runSmall (0x73 :: halt) (syscallState 1 200 |>.setReg .x12
      (BitVec.ofNat 64 (MEMORY_BYTES - 8)))).exit == Exit.failure)
  check "unsupported service rejects"
    ((runSmall [0x73] (initialMachine.setReg .x5 7)).exit == Exit.failure)
  check "EBREAK rejects" ((runSmall [0x00100073]).exit == Exit.failure)
  check "malformed ECALL does not decode" (decodeInstruction 0x000000f3 |>.isNone)
  check "CSR instructions do not decode" (decodeInstruction 0x00002073 |>.isNone)

end CommitGolf.RiscvTests

namespace CommitGolf.ProgramTests
open OracleComp OracleSpec Riscv RiscvZkvm.Rv64

-- Deliberately insecure executable fixture: tests the ABI and scoring, not eligibility.
private def addi (rd rs immediate : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((immediate % 4096) * 2 ^ 20 + rs * 2 ^ 15 + rd * 2 ^ 7 + 0x13)
private def halt : List (BitVec 32) := [addi 5 0 1, addi 10 0 0, 0x73]
private def submission : Submission where
  sizes := ⟨8, 16⟩
  layout := ⟨0, 2^32, 2^32 + 32, 2^32 + 40, 2^33, 2^34⟩
  steps := fun _ => 30
  image
    | .commit => ⟨[addi 6 0 7, 0x0065b023, addi 6 0 9, 0x00663023] ++ halt, []⟩
    | .opening => ⟨[0x00063303, 0x0067b023, addi 11 0 8] ++ halt, []⟩
    | .check => ⟨halt, []⟩
private def oracle : Oracle := ⟨fun _ => 0, Equiv.refl _⟩
private def fixed : QueryImpl World Id
  | .inl n => pure (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))
  | .inr q => oracle.answer q
private def run {α : Type} (c : OracleComp World α) : α := Id.run (simulateQ fixed c)
private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

example : BATCH = 128 := rfl
example : score 8 7 6 = 104 := rfl
example (s : Submission) (bytes commitCycles openingCycles : Nat)
    (certificate : Certificate s bytes commitCycles openingCycles) :
    s.MachineSuccess ∧ s.ProverCycles commitCycles openingCycles :=
  ⟨certificate.machineSuccess, certificate.proverCycles⟩

#eval do
  let message : Message := fun _ => 0
  let committed := run (submission.run .commit message)
  let (root, trapdoor) := submission.readCommit committed
  check "commitment and trapdoor decode from program memory"
    (committed.exit == Exit.success && root == 7 && trapdoor == 9)
  let opened := run (submission.run .opening (trapdoor, ∅))
  check "opening consumes the serialized trapdoor and returns its declared proof length"
    (submission.openingSucceeded opened && submission.readProof opened == [9, 0, 0, 0, 0, 0, 0, 0])
  let honest := run (submission.honestMachine message ∅)
  check "full commitment and opening cycles both count"
    (honest.success && honest.commitCycles == 7 && honest.openingCycles == 6 && honest.proofBytes == 8)
  let (derivedRoot, derivedTrapdoor) := run (submission.scheme.commit message)
  check "security-game scheme uses the same programs"
    (derivedRoot == root && (derivedTrapdoor : BitVec 64).toNat == (trapdoor : BitVec 64).toNat &&
      run (submission.scheme.opening derivedTrapdoor ∅) == submission.readProof opened)
  let short : Submission := { submission with steps := fun _ => 1 }
  check "cutoff cannot count as a successful honest run" (!(run (short.honestMachine message ∅)).success)
  let oversized : Submission := { submission with image := fun p =>
    if p = Program.opening then ⟨[addi 11 0 17] ++ halt, []⟩ else submission.image p }
  check "oversized proof cannot count as success" (!(run (oversized.honestMachine message ∅)).success)
  let randomizedCheck : Submission := { submission with image := fun p =>
    if p = Program.check then ⟨[addi 5 0 2, 0x73] ++ halt, []⟩ else submission.image p }
  check "check forbids private randomness"
    (!(oracle.eval (randomizedCheck.scheme.check 0 ∅ (fun i => nomatch i) [])).1)
  check "oversized adversarial proof rejects"
    (!(oracle.eval (submission.scheme.check 0 ∅ (fun i => nomatch i) (List.replicate 17 0))).1)
  let buffer := positionsBuffer 0 ({(⟨5, by decide⟩ : Index), (⟨2, by decide⟩ : Index)} : Positions)
  check "positions are sorted little-endian indices"
    (buffer.length == 16 && buffer.byteAt 0 == 2 && buffer.byteAt 8 == 5)

end CommitGolf.ProgramTests

namespace CommitGolf.ArtifactEncodingTests
open ArtifactEncoding

-- Counts preserve trailing zero elements, and concatenation preserves little-endian order.
private def bytes : Packed 5 := .join (.chunk 2 0x3412) (.chunk 3 0x007856)
example : decode 8 bytes = [0x12, 0x34, 0x56, 0x78, 0] := by decide
example : (decode 8 bytes).length = 5 := length_decode 8 bytes
example : (decode 8 bytes).getD 2 0 = 0x56 := by
  rw [getD_decode 8 bytes 2 (by decide)]
  decide
example : decode 32 (.chunk 3 0x00000000ffffffff12345678) = [0x12345678, 0xffffffff, 0] := by decide
example : decode 8 (.chunk 0 0) = [] := rfl

private def wordBoundary : Packed 65 :=
  .join (.chunk 64 (0x12345678 <<< (32 * 63))) (.chunk 1 0x90abcdef)
example : (decode 32 wordBoundary).getD 63 0 = 0x12345678 := by
  rw [getD_decode 32 wordBoundary 63 (by decide)]
  decide
example : (decode 32 wordBoundary).getD 64 0 = 0x90abcdef := by
  rw [getD_decode 32 wordBoundary 64 (by decide)]
  decide
private def byteBoundary : Packed 257 := .join (.chunk 256 (0xa5 <<< (8 * 255))) (.chunk 1 0)
example : (decode 8 byteBoundary).getD 255 0 = 0xa5 := by
  rw [getD_decode 8 byteBoundary 255 (by decide)]
  decide
example : (decode 8 byteBoundary).getD 256 0 = 0 := by
  rw [getD_decode 8 byteBoundary 256 (by decide)]
  decide

end CommitGolf.ArtifactEncodingTests
