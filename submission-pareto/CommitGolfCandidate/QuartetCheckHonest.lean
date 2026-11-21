import CommitGolfCandidate.QuartetCheckHeap
import CommitGolfCandidate.QuartetRVLeafFields

/-! A 1024-bit quartet is determined by its four 256-bit slots, and the honest payload's slot `k`
is the leaf `4g+k`. -/

namespace TwoPermutationPrototype.QuartetCheck
open CommitGolf CommitGolfCandidate TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.Sampling.Quartet (quartetPayload leafAt)

set_option autoImplicit false

theorem quartet_eq_of_slots (x y : BitVec 1024)
    (slots : ∀ k < 4, x.extractLsb' (256*k) 256 = y.extractLsb' (256*k) 256) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i inside
  have slot := congrArg (fun z : BitVec 256 => z.getLsbD (i % 256)) (slots (i/256) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show i % 256 < 256 by omega, decide_true, Bool.true_and] at slot
  rwa [show 256*(i/256) + i % 256 = i by omega] at slot

theorem quartet_payload_slot (leaves : DigestTape) (g k : Nat) (small : k < 4) :
    (quartetPayload leaves g).extractLsb' (256*k) 256 = leafAt leaves (4*g+k) := by
  unfold quartetPayload
  interval_cases k
  · change ((leafAt leaves (4*g+3) ++ leafAt leaves (4*g+2) ++ leafAt leaves (4*g+1)) ++ leafAt leaves (4*g)).extractLsb' 0 256 = _
    rw [BitVec.extractLsb'_append_eq_right]; rfl
  · change ((leafAt leaves (4*g+3) ++ leafAt leaves (4*g+2) ++ leafAt leaves (4*g+1)) ++ leafAt leaves (4*g)).extractLsb' 256 256 = _
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 256), Nat.sub_self,
      BitVec.extractLsb'_append_eq_right]
  · change ((leafAt leaves (4*g+3) ++ leafAt leaves (4*g+2) ++ leafAt leaves (4*g+1)) ++ leafAt leaves (4*g)).extractLsb' 512 256 = _
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512), show 512-256 = 256 by decide,
      BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 256), Nat.sub_self,
      BitVec.extractLsb'_append_eq_right]
  · change ((leafAt leaves (4*g+3) ++ leafAt leaves (4*g+2) ++ leafAt leaves (4*g+1)) ++ leafAt leaves (4*g)).extractLsb' 768 256 = _
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 768), show 768-256 = 512 by decide,
      BitVec.extractLsb'_append_eq_of_le (by decide : 256 ≤ 512), show 512-256 = 256 by decide,
      BitVec.extractLsb'_append_eq_left]

theorem xor_slot (i j : Nat) (small : j < 4) : i ^^^ j = 4*(i/4) + (i % 4 ^^^ j) := by
  obtain ⟨g, p⟩ := QuartetRV.xor_group i j small
  have split := Nat.div_add_mod (i ^^^ j) 4
  rw [g, p] at split
  omega

/-- If the leaf sits in slot `i % 4` and slot `(i % 4) ^^^ j` holds the leaf `i ^^^ j`, the quartet
is the honest payload of group `i / 4`. -/
theorem honest_quartet (leaves : DigestTape) (i : Nat) (x : BitVec 1024)
    (leaf : x.extractLsb' (256*(i % 4)) 256 = leafAt leaves i)
    (siblings : ∀ j, 1 ≤ j → j ≤ 3 → x.extractLsb' (256*((i % 4) ^^^ j)) 256 = leafAt leaves (i ^^^ j)) :
    x = quartetPayload leaves (i/4) := by
  apply quartet_eq_of_slots
  intro k small
  rw [quartet_payload_slot leaves (i/4) k small]
  have hr : i % 4 < 4 := Nat.mod_lt _ (by decide)
  by_cases same : k = i % 4
  · subst same
    rw [leaf, show 4*(i/4) + i % 4 = i by omega]
  · let j := i % 4 ^^^ k
    have back : i % 4 ^^^ j = k := by
      have cancel : ∀ r < 4, ∀ k < 4, r ^^^ (r ^^^ k) = k := by decide
      exact cancel _ hr _ small
    have jRange : 1 ≤ j ∧ j ≤ 3 := by
      have range : ∀ r < 4, ∀ k < 4, k ≠ r → 1 ≤ r ^^^ k ∧ r ^^^ k ≤ 3 := by decide
      exact range _ hr _ small same
    have sib := siblings j jRange.1 jRange.2
    rw [back] at sib
    rw [sib, xor_slot i j (by omega), back]

end TwoPermutationPrototype.QuartetCheck
