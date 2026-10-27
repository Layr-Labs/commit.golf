import CommitGolfCandidate.Xof.CompressionProof.Honest
import CommitGolf.Oracle.Finite

/-! # Merkle constructions using a random oracle or an XOF

Both constructions reuse the compression Merkle tree. Each 512-bit child pair becomes one
512-bit oracle input; the XOF requests 256 output bits. The transport below preserves the
honest run and its query counts. The binding arguments are in `RandomOracleProof` and `XofProof`.
-/

namespace CommitGolf.MerkleAdapter
open OracleComp OracleSpec
abbrev Source := CompressionBaseline.family
/-- Replace each compression call with exactly one public query. -/
structure Interface (F : OracleFamily) where
  input : CompressionBaseline.Input → F.Domain
  output : (x : CompressionBaseline.Input) → F.spec.Range (input x) → CompressionBaseline.Digest
namespace Interface
variable {F : OracleFamily} (I : Interface F)
def impl : QueryImpl Source.spec (OracleComp F.spec) := fun x => do
  let y ← (F.spec.query (I.input x) :)
  return I.output x y
def worldImpl : QueryImpl Source.world (OracleComp F.world)
  | .inl n => (F.world.query (.inl n) :)
  | .inr x => do
      let y ← (F.world.query (.inr (I.input x)) : OracleComp F.world _)
      return I.output x y
def project (H : F.Realization) : CompressionBaseline.Hash :=
  fun x => I.output x (F.answer H (m := Id) (I.input x))
def scheme : Scheme where
  oracles := F
  Trapdoor := CompressionBaseline.merkle.Trapdoor
  commit m := simulateQ I.worldImpl (CompressionBaseline.merkle.commit m)
  opening td ps := simulateQ I.worldImpl (CompressionBaseline.merkle.opening td ps)
  check rt ps vs pf := simulateQ I.impl (CompressionBaseline.merkle.check rt ps vs pf)

theorem eval_map (H : F.Realization) {α : Type} (c : OracleComp Source.spec α) :
    F.eval H (simulateQ I.impl c) = Source.eval (I.project H) c := by
  unfold OracleFamily.eval
  rw [← QueryImpl.simulateQ_compose]
  congr 2

theorem run_map (H : F.Realization) {α : Type} (c : OracleComp Source.world α) :
    F.run H (simulateQ I.worldImpl c) = Source.run (I.project H) c := by
  unfold OracleFamily.run
  rw [← QueryImpl.simulateQ_compose]
  congr 2
  funext x
  cases x with
  | inl n => simp [QueryImpl.compose, worldImpl, OracleFamily.callCost]
  | inr x =>
    simp only [QueryImpl.compose, worldImpl, simulateQ_bind, simulateQ_query]
    simp [OracleFamily.callCost, OracleFamily.answer, Source, project]
    rw [F.answer_eq_pure H (m := ProbComp)]
    rfl

theorem honest_map (H : F.Realization) (m : Message) (ps : Positions) :
    I.scheme.honest H m ps = CompressionBaseline.merkle.honest (I.project H) m ps := by
  unfold Scheme.honest
  dsimp only [scheme]
  simp only [I.run_map, I.eval_map]

theorem completeness : I.scheme.Completeness := by
  intro H m ps
  rw [I.honest_map H m ps]
  exact CompressionBaseline.merkle_completeness _ _ _

theorem honestBudgets : I.scheme.HonestBudgets := by
  intro H m ps
  rw [I.honest_map H m ps]
  exact CompressionBaseline.merkle_honestBudgets _ _ _

theorem proofSize : I.scheme.ProofSize 76800 := by
  intro H m ps hps
  rw [I.honest_map H m ps]
  exact CompressionBaseline.merkle_proofSize _ _ _ hps

theorem verificationCost : I.scheme.VerificationCost 2400 := by
  intro H m ps hps
  rw [I.honest_map H m ps]
  exact CompressionBaseline.merkle_verificationCost _ _ _ hps
end Interface
end CommitGolf.MerkleAdapter
namespace CommitGolf
open OracleComp OracleSpec
namespace RandomOracleBaseline
/-- The two children, encoded as 512 bits in least-significant-bit order. -/
def encode (x : CompressionBaseline.Input) : List Bool :=
  List.ofFn fun i : Fin (DIGEST_BITS + DIGEST_BITS) => x.getLsbD i

theorem encode_injective : Function.Injective encode := by
  intro x y h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hf := List.ofFn_inj.mp h
  exact congrFun hf ⟨i, hi⟩

abbrev family : OracleFamily := .randomOracleFixedOutput DIGEST_BITS (by decide)
def interface : MerkleAdapter.Interface family where
  input := encode
  output _ y := y
abbrev merkle : Scheme := interface.scheme

theorem merkle_completeness : merkle.Completeness := interface.completeness
theorem merkle_honestBudgets : merkle.HonestBudgets := interface.honestBudgets
theorem merkle_proofSize : merkle.ProofSize 76800 := interface.proofSize
theorem merkle_verificationCost : merkle.VerificationCost 2400 := interface.verificationCost
end RandomOracleBaseline
namespace XofBaseline
abbrev family : OracleFamily := .idealXof
def interface : MerkleAdapter.Interface family where
  input x := (RandomOracleBaseline.encode x, DIGEST_BITS)
  output _ y := y
abbrev merkle : Scheme := interface.scheme

theorem merkle_completeness : merkle.Completeness := interface.completeness
theorem merkle_honestBudgets : merkle.HonestBudgets := interface.honestBudgets
theorem merkle_proofSize : merkle.ProofSize 76800 := interface.proofSize
theorem merkle_verificationCost : merkle.VerificationCost 2400 := interface.verificationCost
end XofBaseline
end CommitGolf
