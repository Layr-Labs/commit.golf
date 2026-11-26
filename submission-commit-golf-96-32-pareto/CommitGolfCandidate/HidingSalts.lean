import CommitGolfCandidate.CommitSemantics
import Mathlib.Data.Fintype.EquivFin
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-! The commitment machine's single random-byte request is exactly a vector of
independent uniform 128-bit salts. -/
namespace CommitGolfCandidate

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

theorem split_blocks_bijective (width count : Nat) (positive : 0 < width) :
    Function.Bijective (splitBlocks width count) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨split_blocks_injective width count positive, ?_⟩
  have card (n : Nat) : Fintype.card (BitVec n) = 2^n := by
    simp
  simp only [Fintype.card_fun, Fintype.card_fin, card]
  exact pow_mul 2 width count

theorem split_blocks_uniform (width count : Nat) (positive : 0 < width) :
    𝒟[splitBlocks width count <$> ($ᵗ BitVec (width*count))] =
      𝒟[$ᵗ (Fin count → BitVec width)] := by
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (split_blocks_bijective width count positive)).evalDist_eq

theorem split_blocks_uniform_bind (width count : Nat) (positive : 0 < width)
    {α : Type} (next : (Fin count → BitVec width) → ProbComp α) :
    𝒟[($ᵗ BitVec (width*count)) >>= fun packed => next (splitBlocks width count packed)] =
      𝒟[($ᵗ (Fin count → BitVec width)) >>= next] := by
  rw [← bind_map_left]
  exact ((SampleableType.map_uniformSample_evalDistEq_of_bijective
    (split_blocks_bijective width count positive)).bind_left next).evalDist_eq

private theorem sized_salts {bits : Nat} (width : bits = 128*LENGTH)
    {α : Type} (next : (Index → Salt) → ProbComp α) :
    𝒟[($ᵗ BitVec bits) >>= fun packed => next (fun index => packed.extractLsb' (128*index.val) 128)] =
      𝒟[($ᵗ (Index → Salt)) >>= next] := by
  subst bits
  exact split_blocks_uniform_bind 128 LENGTH (by decide) next

/-- The actual RANDOM syscall has precisely the independent 128-bit salt distribution. -/
theorem commit_salts_uniform {α : Type} (message : Message)
    (next : (Index → Salt) → ProbComp α) :
    𝒟[commitSaltCoins message >>= fun packed =>
      next (fun index => packed.extractLsb' (128*index.val) 128)] =
      𝒟[($ᵗ (Index → Salt)) >>= next] := by
  unfold commitSaltCoins
  exact sized_salts (commit_salt_width message) next

end CommitGolfCandidate
