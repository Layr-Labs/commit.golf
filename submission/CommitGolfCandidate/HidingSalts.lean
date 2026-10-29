import CommitGolfCandidate.CommitSemantics
import Mathlib.Data.Fintype.EquivFin

/-! The commitment machine's single random-byte request is exactly a vector of
independent uniform salts. No pseudorandomness assumption or additional sampler
is introduced by switching to the vector representation. -/
namespace CommitGolfCandidate
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
    𝒮[splitBlocks width count <$> ($ᵗ BitVec (width*count))] =
      𝒮[$ᵗ (Fin count → BitVec width)] := by
  apply evalSPMF_ext
  intro salt
  exact probOutput_map_bijective_uniform_cross _ _ (split_blocks_bijective width count positive) salt

/-- The same equality holds inside an arbitrary randomized continuation, which
may use the oracle and reveal salts for the selected opening positions. -/
theorem split_blocks_uniform_bind (width count : Nat) (positive : 0 < width)
    {α : Type} (next : (Fin count → BitVec width) → ProbComp α) :
    𝒮[($ᵗ BitVec (width*count)) >>= fun packed => next (splitBlocks width count packed)] =
      𝒮[($ᵗ (Fin count → BitVec width)) >>= next] := by
  apply evalSPMF_ext
  intro output
  exact probOutput_bind_bijective_uniform_cross _ _ (split_blocks_bijective width count positive) next output

private theorem sized_salts {bits : Nat} (width : bits = 256*LENGTH)
    {α : Type} (next : (Index → Digest) → ProbComp α) :
    𝒮[($ᵗ BitVec bits) >>= fun packed => next (fun index => packed.extractLsb' (256*index.val) 256)] =
      𝒮[($ᵗ (Index → Digest)) >>= next] := by
  subst bits
  exact split_blocks_uniform_bind 256 LENGTH (by decide) next

/-- The actual RANDOM syscall has precisely the independent-salt distribution
used by the mathematical hiding experiment. -/
theorem commit_salts_uniform {α : Type} (message : Message)
    (next : (Index → Digest) → ProbComp α) :
    𝒮[commitSaltCoins message >>= fun packed =>
      next (fun index => packed.extractLsb' (256*index.val) 256)] =
      𝒮[($ᵗ (Index → Digest)) >>= next] := by
  unfold commitSaltCoins
  exact sized_salts (commit_salt_width message) next

end CommitGolfCandidate
