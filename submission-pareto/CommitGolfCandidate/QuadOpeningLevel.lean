import CommitGolfCandidate.QuadOpeningRun

/-! One level of a penta record: `x6 = index / 5^k` gives the group base of the four other
children in the trapdoor; they are appended to the output as 16 doublewords. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open QOpening (trapdoorBase proofBase nonceBase)

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

/-! ### Record layout -/

/-- Initial address of doubleword `d < 98` of the record of position `i`: the salt, then the four
other slots of the level-`k` group (`k < 4`, rotation order), the three other children of the 4-ary
level-4 group (rotation order mod 4), then the binary siblings of levels 5-9. -/
def recordSource (i d : Nat) : Nat :=
  if d < 2 then nonceBase+16*i+8*d
  else if d < 66 then
    trapdoorBase+pentaGroupSlotOffset ((d-2)/16) (i/5^((d-2)/16+1)) ((i/5^((d-2)/16)%5+(d-2)%16/4+1)%5)+8*((d-2)%4)
  else if d < 78 then
    trapdoorBase+pentaGroupSlotOffset 4 (i/625/4) (1+(i/625%4+(d-66)/4+1)%4)+8*((d-66)%4)
  else
    trapdoorBase+pentaGroupSlotOffset (5+(d-78)/4) (i/(2500*2^((d-78)/4))/2) (4-i/(2500*2^((d-78)/4))%2)+8*((d-78)%4)

/-- The position written by record `o` (0 past the end). -/
def ordinalIndex (positions : Positions) (o : Nat) : Nat :=
  (((positions.sort (· ≤ ·))[o]?).map Fin.val).getD 0

/-- Record doublewords at stride 98 (784-byte records). -/
def wordSource (positions : Positions) (u : Nat) : Nat := recordSource (ordinalIndex positions (u/98)) (u%98)

theorem word_source_salt (positions : Positions) (o w : Nat) (hw : w < 2) :
    wordSource positions (98*o+w) = nonceBase+16*ordinalIndex positions o+8*w := by
  unfold wordSource recordSource
  rw [show (98*o+w)/98 = o by omega, show (98*o+w)%98 = w by omega, if_pos hw]

theorem word_source_penta (positions : Positions) (o k j w : Nat) (hk : k < 4) (hj : j < 4) (hw : w < 4) :
    wordSource positions (98*o+2+16*k+4*j+w) =
      trapdoorBase+pentaGroupSlotOffset k (ordinalIndex positions o/5^(k+1))
        ((ordinalIndex positions o/5^k%5+j+1)%5)+8*w := by
  unfold wordSource recordSource
  rw [show (98*o+2+16*k+4*j+w)/98 = o by omega, show (98*o+2+16*k+4*j+w)%98 = 2+16*k+4*j+w by omega,
    if_neg (by omega), if_pos (by omega)]
  rw [show (2+16*k+4*j+w-2)/16 = k by omega, show (2+16*k+4*j+w-2)%16/4 = j by omega,
    show (2+16*k+4*j+w-2)%4 = w by omega]

theorem word_source_quad (positions : Positions) (o t w : Nat) (ht : t < 3) (hw : w < 4) :
    wordSource positions (98*o+66+4*t+w) =
      trapdoorBase+pentaGroupSlotOffset 4 (ordinalIndex positions o/625/4)
        (1+(ordinalIndex positions o/625%4+t+1)%4)+8*w := by
  unfold wordSource recordSource
  rw [show (98*o+66+4*t+w)/98 = o by omega, show (98*o+66+4*t+w)%98 = 66+4*t+w by omega,
    if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  rw [show (66+4*t+w-66)/4 = t by omega, show (66+4*t+w-66)%4 = w by omega]

theorem word_source_bin (positions : Positions) (o m w : Nat) (hm : m < 5) (hw : w < 4) :
    wordSource positions (98*o+78+4*m+w) =
      trapdoorBase+pentaGroupSlotOffset (5+m) (ordinalIndex positions o/(2500*2^m)/2)
        (4-ordinalIndex positions o/(2500*2^m)%2)+8*w := by
  unfold wordSource recordSource
  rw [show (98*o+78+4*m+w)/98 = o by omega, show (98*o+78+4*m+w)%98 = 78+4*m+w by omega,
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [show (78+4*m+w-78)/4 = m by omega, show (78+4*m+w-78)%4 = w by omega]

theorem place_value_low (k : Nat) (hk : k ≤ 4) : placeValue k = 5^k := by
  interval_cases k <;> rfl

theorem place_value_bin (m : Nat) (hm : m ≤ 5) : placeValue (5+m) = 2500*2^m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 5+(m+1) = (5+m)+1 by omega, placeValue, ih (by omega), pow_succ,
      radix_mid (5+m) (by unfold BIN_LOW; omega) (by unfold PENTA_HIGH; omega)]
    ring

theorem div_lt_count (i : Nat) (inside : i < LENGTH) : ∀ k, i/placeValue k < pentaCount k
  | 0 => by simpa [pentaCount, placeValue] using inside
  | k+1 => by
    have ih := div_lt_count i inside k
    rw [placeValue, ← Nat.div_div_eq_div_mul]
    show i/placeValue k/radix k < (pentaCount k+radix k-1)/radix k
    unfold radix; split_ifs <;> omega

theorem group_room : ∀ k < 22, pentaGroupBase k+368*pentaCount (k+1) ≤ 1728786760 := by decide
theorem group_aligned : ∀ k < 23, (pentaGroupBase k+40) % 4096 = 0 := by decide

/-! ### Register arithmetic -/

theorem word_lt (n : Nat) (small : n < 2^64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]

theorem divu_five (n : Nat) (small : n < 2^40) :
    rv64_divu (BitVec.ofNat 64 n) (BitVec.ofNat 64 5) = BitVec.ofNat 64 (n/5) := by
  unfold rv64_divu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, word_lt n (by omega), word_lt 5 (by decide), word_lt _ (by omega)]

theorem remu_five (n : Nat) (small : n < 2^40) :
    rv64_remu (BitVec.ofNat 64 n) (BitVec.ofNat 64 5) = BitVec.ofNat 64 (n%5) := by
  unfold rv64_remu
  rw [if_neg (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, word_lt n (by omega), word_lt 5 (by decide), word_lt _ (by omega)]

theorem rem_by_shift (n : Nat) (small : n < 2^40) :
    BitVec.ofNat 64 n - ((BitVec.ofNat 64 (n/5) <<< 2) + BitVec.ofNat 64 (n/5)) = BitVec.ofNat 64 (n%5) := by
  apply BitVec.eq_of_toNat_eq
  have five : (BitVec.ofNat 64 (n/5) <<< 2) + BitVec.ofNat 64 (n/5) = BitVec.ofNat 64 (5*(n/5)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
    omega
  rw [five, BitVec.toNat_sub, word_lt _ (by omega), word_lt _ (by omega), word_lt _ (by omega)]
  omega

theorem mul_width (q : Nat) (small : q < 2^40) :
    BitVec.ofNat 64 q * BitVec.ofNat 64 368 = BitVec.ofNat 64 (368*q) := by
  rw [← BitVec.ofNat_mul]
  congr 1
  omega

theorem lui_page : ∀ k < 7,
    ((BitVec.ofNat 20 (groupPage k)).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 (pentaGroupBase k+40) := by
  decide

theorem hyb_page : ∀ k < 17,
    ((hybPage k).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 (pentaGroupBase k+40) := by
  decide

theorem shift_slot (m : Nat) (small : m < 2^40) : BitVec.ofNat 64 m <<< (5 : Nat) = BitVec.ofNat 64 (32*m) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
  show m*2^5 % 2^64 = _
  omega

theorem and_three (n : Nat) (small : n < 2^64) :
    BitVec.ofNat 64 n &&& signExtend12 3#12 = BitVec.ofNat 64 (n%4) := by
  rw [show signExtend12 3#12 = BitVec.ofNat 64 3 by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, word_lt n small, word_lt 3 (by decide), word_lt _ (by omega)]
  exact Nat.and_two_pow_sub_one_eq_mod n 2

theorem shr_two (n : Nat) (small : n < 2^64) :
    BitVec.ofNat 64 n >>> (2#6).toNat = BitVec.ofNat 64 (n/4) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, word_lt n small, word_lt _ (by omega), Nat.shiftRight_eq_div_pow]
  rfl

theorem addi_small : ∀ j < 4, signExtend12 (BitVec.ofNat 12 (j+1)) = BitVec.ofNat 64 (j+1) := by decide

def tableBase : Nat := 4096+4*159

theorem pc_offset (start i : Nat) :
    BitVec.ofNat 64 (4096+4*start) + BitVec.ofNat 64 (4*i) = BitVec.ofNat 64 (4096+4*(start+i)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

end TwoPermutationPrototype.QuadOpening
