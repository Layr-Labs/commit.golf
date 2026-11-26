import CommitGolfCandidate.CommitSemantics
import Mathlib.Data.Fintype.EquivFin
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! The commitment machine's single random-byte request is exactly a vector of
independent uniform salts. No pseudorandomness assumption or additional sampler
is introduced by switching to the vector representation. -/
namespace CommitGolfCandidate

-- Observations retain the discrete measurable structure used by the contract.
local instance hidingSaltsDiscreteSpace {α : Type} : MeasurableSpace α := ⊤
open CommitGolf CommitGolf.Riscv OracleComp

/-- Split a packed bit string into equal-width, little-endian blocks. -/
def splitBlocks (width count : Nat) (packed : BitVec (width*count)) : Fin count → BitVec width :=
  fun index => packed.extractLsb' (width*index.val) width

theorem split_blocks_injective (width count : Nat) (positive : 0 < width) :
    Function.Injective (splitBlocks width count) := by
  intro left right same
  apply BitVec.eq_of_getLsbD_eq
  intro bit below
  have block : bit/width < count := (Nat.div_lt_iff_lt_mul positive).mpr
    (by simpa only [Nat.mul_comm] using below)
  have offset : bit%width < width := Nat.mod_lt _ positive
  have aligned : width*(bit/width)+bit%width = bit := Nat.div_add_mod bit width
  have equal := congrArg (fun value : BitVec width => value.getLsbD (bit%width))
    (congrFun same ⟨bit/width, block⟩)
  simpa only [splitBlocks, BitVec.getLsbD_extractLsb', offset, decide_true,
    Bool.true_and, aligned] using equal

/-- Splitting retains all bits, and domain and codomain have equal finite size. -/
theorem split_blocks_bijective (width count : Nat) (positive : 0 < width) :
    Function.Bijective (splitBlocks width count) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨split_blocks_injective width count positive, ?_⟩
  have card (n : Nat) : Fintype.card (BitVec n) = 2^n := by
    simp
  simp only [Fintype.card_fun, Fintype.card_fin, card]
  exact pow_mul 2 width count

/-- Uniform packed randomness becomes uniform over all salt vectors. -/
theorem split_blocks_uniform (width count : Nat) (positive : 0 < width) :
    𝒟[splitBlocks width count <$> ($ᵗ BitVec (width*count))] =
      𝒟[$ᵗ (Fin count → BitVec width)] := by
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (split_blocks_bijective width count positive)).evalDist_eq

/-- The same equality holds inside an arbitrary randomized continuation, which
may use the oracle and reveal salts for the selected opening positions. -/
theorem split_blocks_uniform_bind (width count : Nat) (positive : 0 < width)
    {α : Type} (next : (Fin count → BitVec width) → ProbComp α) :
    𝒟[($ᵗ BitVec (width*count)) >>= fun packed => next (splitBlocks width count packed)] =
      𝒟[($ᵗ (Fin count → BitVec width)) >>= next] := by
  rw [← bind_map_left]
  exact ((SampleableType.map_uniformSample_evalDistEq_of_bijective
    (split_blocks_bijective width count positive)).bind_left next).evalDist_eq

private theorem sized_salts {bits : Nat} (width : bits = 192*LENGTH)
    {α : Type} (next : (Index → BitVec 192) → ProbComp α) :
    𝒟[($ᵗ BitVec bits) >>= fun packed => next (fun index => packed.extractLsb' (192*index.val) 192)] =
      𝒟[($ᵗ (Index → BitVec 192)) >>= next] := by
  subst bits
  exact split_blocks_uniform_bind 192 LENGTH (by decide) next

/-- The actual RANDOM syscall has precisely the independent 192-bit salt distribution
used by the mathematical hiding experiment. -/
theorem commit_salts_uniform {α : Type} (message : Message)
    (next : (Index → BitVec 192) → ProbComp α) :
    𝒟[commitSaltCoins message >>= fun packed =>
      next (fun index => packed.extractLsb' (192*index.val) 192)] =
      𝒟[($ᵗ (Index → BitVec 192)) >>= next] := by
  unfold commitSaltCoins
  exact sized_salts (commit_salt_width message) next

end CommitGolfCandidate
