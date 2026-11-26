import CommitGolfCandidate.ReconstructedHidingJointPay
import CommitGolfCandidate.TaggedPinnedFreshGuess

namespace CommitGolfCandidate.Reconstruction.HidingTape
open CommitGolf OracleComp TwoPermutationPrototype.Sampling
set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
set_option exponentiation.threshold 2048

private def gapBit (j : Fin 984) : Nat :=
  if j.val < 768 then j.val else if j.val < 776 then j.val+120
    else if j.val < 784 then j.val+240 else j.val+360

private theorem upper_bit_cases (b : Nat) (h : b < 1344) :
    (∃ l : Fin 3, ∃ j : Fin 120, 768+128*l.val+j.val=b) ∨ (∃ j : Fin 984, gapBit j=b) := by
  by_cases a : b < 768
  · right; exact ⟨⟨b,by omega⟩,by simp [gapBit,a]⟩
  by_cases b₁ : b < 888
  · left; exact ⟨0,⟨b-768,by omega⟩,by simp; omega⟩
  by_cases b₂ : b < 896
  · right; exact ⟨⟨b-120,by omega⟩,by dsimp [gapBit]; split_ifs <;> omega⟩
  by_cases b₃ : b < 1016
  · left; exact ⟨1,⟨b-896,by omega⟩,by simp; omega⟩
  by_cases b₄ : b < 1024
  · right; exact ⟨⟨b-240,by omega⟩,by dsimp [gapBit]; split_ifs <;> omega⟩
  by_cases b₅ : b < 1144
  · left; exact ⟨2,⟨b-1024,by omega⟩,by simp; omega⟩
  · right; exact ⟨⟨b-360,by omega⟩,by dsimp [gapBit]; split_ifs <;> omega⟩

theorem upper_fiber_card (sig : Signature) : Fintype.card {tail : BitVec 1344 // tailSignature tail = sig} ≤ 2^984 := by
  let read (tail : {v : BitVec 1344 // tailSignature v = sig}) (j : Fin 984) := tail.val.getLsbD (gapBit j)
  have inj : Function.Injective read := by
    intro a b same
    apply Subtype.ext
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rcases upper_bit_cases i hi with ⟨l,j,bits⟩|⟨j,bits⟩
    · have equal := congrFun (a.property.trans b.property.symm) l
      have matching := congrArg (fun v : Salt => v.getLsbD j.val) equal
      change ((a.val.extractLsb' (768+128*l.val) 120).getLsbD j.val) = _ at matching
      rw [←bits]
      simpa only [tailSignature,BitVec.getLsbD_extractLsb',j.isLt,decide_true,Bool.true_and] using matching
    · rw [←bits]
      exact congrFun same j
  have bound := Fintype.card_le_of_injective read inj
  simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using bound

theorem new_signature_le {base : Cache} (cache : PinnedHighCache base) (slot : Nat)
    (answers : List (BitVec 1344)) (plans : List PinnedHighPlan)
    (room : cache.zero.entries.length+plans.length ≤ 2^121) (sig : Signature) :
    Pr{let out ← runPinnedHigh cache slot answers plans}[∃ hi, tailSignature hi = sig ∧ cache.NewTail out.2 hi] ≤
      (plans.length:ENNReal)/2^359 := by
  classical
  let carrier := {hi : BitVec 1344 // tailSignature hi = sig}
  let d := runPinnedHigh cache slot answers plans
  have bound := prEvent_exists_le_card_mul d (fun (h : carrier) out => cache.NewTail out.2 h.val)
    (fun h => pinned_high_new_tail_le cache slot answers plans room h.val)
  have small : (Fintype.card carrier:ENNReal) ≤ (2:ENNReal)^984 := by exact_mod_cast upper_fiber_card sig
  calc
    _ ≤ Pr{let out ← d}[∃ h : carrier, cache.NewTail out.2 h.val] := by
      apply prEvent_mono
      rintro out ⟨hi,same,found⟩
      exact ⟨⟨hi,same⟩,found⟩
    _ ≤ _ := bound
    _ ≤ 2^984*((plans.length:ENNReal)/2^1343) := mul_le_mul_of_nonneg_right small zero_le
    _ = _ := by
      apply le_antisymm
      all_goals
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        simp only [ENNReal.toReal_mul,ENNReal.toReal_div,ENNReal.toReal_pow,ENNReal.toReal_ofNat,ENNReal.toReal_natCast]
        norm_num
        ring_nf
        exact le_rfl

theorem generated_new_signatures_le {G : Type} [Fintype G] {base : Cache}
    (cache : PinnedHighCache base) (slot : Nat) (answers : List (BitVec 1344)) (plans : List PinnedHighPlan)
    (room : cache.zero.entries.length+plans.length ≤ 2^121) (blocks : G → SaltBlock) :
    Pr{let out ← runPinnedHigh cache slot answers plans}[∃ g : G, ∃ hi, tailSignature hi = signature (blocks g) ∧ cache.NewTail out.2 hi] ≤
      (Fintype.card G:ENNReal)*(plans.length/2^359) :=
  prEvent_exists_le_card_mul _ _ (fun g => new_signature_le cache slot answers plans room (signature (blocks g)))

end CommitGolfCandidate.Reconstruction.HidingTape
