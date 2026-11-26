import CommitGolfCandidate.ReconstructedHidingSwitch
import CommitGolfCandidate.ReconstructedHidingDistribution

namespace CommitGolfCandidate.Reconstruction.HidingTape
open Generator CommitGolfCandidate.Permutation CommitGolfCandidate.Permutation.NonceChain
open CommitGolfCandidate.Reconstruction.HidingReplay
set_option exponentiation.threshold 2048
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

abbrev groupCount := 4096*342

def groupIndex (j : Fin groupCount) : Group :=
  (⟨j.val / 342,by have := j.isLt; unfold groupCount at this; omega⟩,⟨j.val%342,by omega⟩)

private theorem groupIndex_injective : Function.Injective groupIndex := by
  intro i j eq
  have a := congrArg (fun v : Group => v.1.val) eq
  have b := congrArg (fun v : Group => v.2.val) eq
  change i.val/342 = j.val/342 at a
  change i.val%342 = j.val%342 at b
  exact Fin.ext (by omega)

private def packedBits (t : Fin 4096) (g : Fin 342) (k : Key) (i : Fin 1600) :=
  (inputWord t g k (i.val / 64)).getLsbD (i.val % 64)

def packedAddress (k : Key) (j : Fin groupCount) : Reply :=
  let bits := List.ofFn (packedBits (groupIndex j).1 (groupIndex j).2 k)
  (BitVec.ofBoolListLE bits).cast (by exact List.length_ofFn)

theorem packedAddress_bit (k : Key) (j : Fin groupCount) (i : Fin 1600) :
    (packedAddress k j).getLsbD i.val = packedBits (groupIndex j).1 (groupIndex j).2 k i := by
  simp only [packedAddress, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]

theorem packedAddress_unique (k k' : Key) (j j' : Fin groupCount)
    (same : packedAddress k j = packedAddress k' j') : k = k' ∧ j = j' := by
  have words (w : Nat) (hw : w < 25) : inputWord (groupIndex j).1 (groupIndex j).2 k w =
      inputWord (groupIndex j').1 (groupIndex j').2 k' w := by
    apply BitVec.eq_of_getLsbD_eq
    intro b hb
    let i : Fin 1600 := ⟨64*w+b,by omega⟩
    have e := congrArg (fun r : Reply => r.getLsbD i.val) same
    rw [packedAddress_bit, packedAddress_bit] at e
    simpa only [packedBits,i,show (64*w+b)/64=w by omega,show (64*w+b)%64=b by omega] using e
  obtain ⟨tiles,groups,keys⟩ := input_injective _ _ _ _ _ _ words
  exact ⟨keys,groupIndex_injective (Prod.ext tiles groups)⟩

/-- The repaired generator can reveal every salt block to an arbitrary adaptive
strategy. Its additional distinguishing probability in the shared public
permutation is at most one term for each exposed endpoint and one birthday
term for duplicate visible blocks. -/
theorem generator_switch (q : Nat) (g : (Fin groupCount → SaltBlock) → Strat Reply Bool)
    (bounded : ∀ d, (g d).QB q) :
    idealRun g ≤ realRun blockSplit packedAddress g +
      ((q:ℝ)/2^192 + q/2^160 + (groupCount:ℝ)*groupCount/2^1440) := by
  have card (k : Nat) : Fintype.card (BitVec k) = 2^k := by
    rw [← FinEnum.card_eq_fintypeCard, FinEnum.card_bitVec]
  have keySize : Fintype.card Key = 2^192 := by
    change Fintype.card (Fin 3 → BitVec 64) = _
    rw [Fintype.card_fun,card,Fintype.card_fin]; norm_num
  have residueSize : Fintype.card Residue = 2^160 := by
    change Fintype.card (Fin 160 → Bool) = _
    rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  have blockSize : Fintype.card SaltBlock = 2^1440 := by
    change Fintype.card (Fin 12 → BitVec 120) = _
    rw [Fintype.card_fun,card,Fintype.card_fin]; norm_num
  have bound := keyed_switch blockSplit packedAddress packedAddress_unique g q bounded
  simpa only [keySize,residueSize,blockSize,Nat.cast_pow,Nat.cast_ofNat] using bound

end CommitGolfCandidate.Reconstruction.HidingTape
