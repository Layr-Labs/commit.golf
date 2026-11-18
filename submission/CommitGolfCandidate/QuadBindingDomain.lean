import CommitGolfCandidate.TwoPermutationQuadSpec
import CommitGolfCandidate.TwoPermutationPinnedRecorded
import CommitGolfCandidate.S3PermSingleCall
import CommitGolfCandidate.TwoPermutationProjectionEvent

/-! Quad binding includes every public permutation query, in both directions.
Raw first-leaf inputs may belong to D2; there is no domain-separation premise. -/
namespace TwoPermutationPrototype.Sampling
open CommitGolf CommitGolfCandidate CommitGolfCandidate.Permutation OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option exponentiation.threshold 2100

/-- D2 is the 576-zero-bit prefix domain, little-endian. -/
def quadDomain : Set Block := {b | b.extractLsb' 0 576 = 0}

def quadEncode (x : BitVec 1024) : Block := x ++ (0#576)

theorem quad_encode_injective : Function.Injective quadEncode := by
  intro x y eq
  have hit := congrArg (fun b : Block => b.extractLsb' 576 1024) eq
  change (x ++ (0#576)).extractLsb' 576 1024 = (y ++ (0#576)).extractLsb' 576 1024 at hit
  exact BitVec.extractLsb'_append_eq_left.symm.trans (hit.trans BitVec.extractLsb'_append_eq_left)

def quadSingleCall : SingleCall Block (BitVec 1024) (BitVec 256) :=
  ⟨quadEncode, quad_encode_injective, fun b => b.extractLsb' 0 256⟩

theorem quad_input_encoded (c : Fin 4 → BitVec 256) :
    quadInput c = quadEncode (((c 3 ++ c 2) ++ c 1) ++ c 0) := rfl

theorem quad_input_domain (c : Fin 4 → BitVec 256) : quadInput c ∈ quadDomain := by
  change (quadInput c).extractLsb' 0 576 = 0
  exact BitVec.extractLsb'_append_eq_right

theorem quad_binding_domain_size : quadDomain.encard ≤ ((2^1024 : Nat) : ℕ∞) := by
  exact slice_fiber_size (low := 0) (width := 576) (high := 1024) (by decide) 0

/-- The sharp lazy-cache denominator; conditioning need not preserve 2^-576. -/
theorem fresh_inverse_quad_domain_ratio (cache : Cache) (output : Block)
    (fresh : UnusedOutput cache.entries output) :
    Pr{let answer ← @uniformSample _ (cache.inverseSampler output fresh)}[answer.val ∈ quadDomain] ≤
      (2^1024 : ENNReal) / (2^1600 - cache.entries.length : Nat) := by
  have bound := inverse_fresh_event_le cache output fresh quadDomain (2^1024) quad_binding_domain_size
  simpa only [Fintype.card_bitVec, PERMUTATION_WIDTH, Nat.cast_pow, Nat.cast_ofNat] using bound

/-- Uniform bound for an adaptive cache of at most 2^121 rows. -/
theorem fresh_inverse_quad_domain_le (cache : Cache) (output : Block)
    (fresh : UnusedOutput cache.entries output) (room : cache.entries.length ≤ 2^121) :
    Pr{let answer ← @uniformSample _ (cache.inverseSampler output fresh)}[answer.val ∈ quadDomain] ≤
      (1 : ENNReal)/2^575 := by
  exact fresh_inverse_slice_le cache output fresh (low := 0) (width := 576) (high := 1024)
    (by decide) (by decide) room 0

/-- Distinct D2 inputs with equal low-256-bit outputs, including calls originating
as raw first-leaf queries rather than quad queries. -/
def QuadWitness (rows : List PublicRow) : Prop :=
  ∃ (x y : BitVec 1024) (a b : Block),
    PublicRow.permutation (quadEncode x) a ∈ rows ∧
    PublicRow.permutation (quadEncode y) b ∈ rows ∧
    x ≠ y ∧ a.extractLsb' 0 256 = b.extractLsb' 0 256

theorem QuadWitness.mono {earlier later : List PublicRow}
    (contained : ∀ row ∈ earlier, row ∈ later) (hit : QuadWitness earlier) : QuadWitness later := by
  obtain ⟨x,y,a,b,ha,hb,ne,eq⟩ := hit
  exact ⟨x,y,a,b,contained _ ha,contained _ hb,ne,eq⟩

theorem quad_witness_bad (t : Trace PermState) (rows : List PublicRow)
    (stored : PinnedRowsStored rows t) (hit : QuadWitness rows) :
    ¬ quadSingleCall.badSpec.Good t := by
  obtain ⟨x,y,a,b,ha,hb,ne,eq⟩ := hit
  obtain ⟨e,he,hin,hout⟩ := stored _ _ ha
  obtain ⟨f,hf,fin,fout⟩ := stored _ _ hb
  exact (quadSingleCall.not_good_iff t).2 (quadSingleCall.collision_imp_bad ne
    ⟨e,he,hin,congrArg (fun r : Block => r.extractLsb' 0 256) hout⟩
    ⟨f,hf,fin,(congrArg (fun r : Block => r.extractLsb' 0 256) fout).trans eq.symm⟩)

end TwoPermutationPrototype.Sampling
