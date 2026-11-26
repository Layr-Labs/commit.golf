import CommitGolfCandidate.QuadOpeningRun

/-! One level of a penta record: `x6 = index / 5^k` gives the group base of the four other
children in the trapdoor; they are appended to the output as 16 doublewords. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open QOpening (trapdoorBase proofBase nonceBase)

attribute [local simp] QOpening.getReg_setReg MachineState.getReg_setPC

/-! ### Record layout -/

/-- Level-`k` node index of the `j`-th other child (Nat version of `pentaNeighbour`). -/
def neighbourNat (i k j : Nat) : Nat := 5*(i/5^(k+1)) + (i/5^k%5+j+1)%5

theorem neighbour_nat (index : Index) (k j : Nat) : pentaNeighbour index k j = neighbourNat index.val k j := rfl

/-- Initial address of doubleword `d < 142` of the record of position `i`: the salt, then the five
slots of the level-`k` group of `i` (`k = (d-2)/20`). -/
def recordSource (i d : Nat) : Nat :=
  if d < 2 then nonceBase+16*i+8*d
  else trapdoorBase+pentaGroupBase ((d-2)/20)+40+368*(i/5^((d-2)/20+1))+8*((d-2)%20)

/-- The position written by record `o` (0 past the end). -/
def ordinalIndex (positions : Positions) (o : Nat) : Nat :=
  (((positions.sort (· ≤ ·))[o]?).map Fin.val).getD 0

/-- Record doublewords at stride 142 (1136-byte records; the table has its own source map). -/
def wordSource (positions : Positions) (u : Nat) : Nat := recordSource (ordinalIndex positions (u/142)) (u%142)

theorem word_source_level (positions : Positions) (o k m : Nat) (hk : k < 7) (hm : m < 20) :
    wordSource positions (142*o+2+20*k+m) =
      trapdoorBase+pentaGroupBase k+40+368*(ordinalIndex positions o/5^(k+1))+8*m := by
  unfold wordSource recordSource
  have q : (142*o+2+20*k+m)/142 = o := by omega
  have r : (142*o+2+20*k+m)%142 = 2+20*k+m := by omega
  rw [q, r, if_neg (by omega)]
  have a : (2+20*k+m-2)/20 = k := by omega
  have b : (2+20*k+m-2)%20 = m := by omega
  rw [a, b]

theorem word_source_salt (positions : Positions) (o w : Nat) (hw : w < 2) :
    wordSource positions (142*o+w) = nonceBase+16*ordinalIndex positions o+8*w := by
  unfold wordSource recordSource
  have q : (142*o+w)/142 = o := by omega
  have r : (142*o+w)%142 = w := by omega
  rw [q, r, if_pos hw]

theorem div_lt_count (i : Nat) (inside : i < LENGTH) : ∀ k, i/5^k < pentaCount k
  | 0 => by simpa [pentaCount] using inside
  | k+1 => by
    have ih := div_lt_count i inside k
    rw [pow_succ, ← Nat.div_div_eq_div_mul]
    show i/5^k/5 < (pentaCount k+4)/5
    omega

theorem group_room : ∀ k < 11, pentaGroupBase k+368*pentaCount (k+1) ≤ 1543577600 := by decide
theorem group_aligned : ∀ k < 11, (pentaGroupBase k+40) % 8 = 0 := by decide

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

theorem lui_page : ∀ k < 11,
    ((BitVec.ofNat 20 (groupPage k)).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 (pentaGroupBase k+40) := by
  decide

theorem shift_slot (m : Nat) (small : m < 2^40) : BitVec.ofNat 64 m <<< (5 : Nat) = BitVec.ofNat 64 (32*m) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, word_lt _ (by omega), word_lt _ (by omega), Nat.shiftLeft_eq]
  show m*2^5 % 2^64 = _
  omega

theorem addi_small : ∀ j < 4, signExtend12 (BitVec.ofNat 12 (j+1)) = BitVec.ofNat 64 (j+1) := by decide

def tableBase : Nat := 4096+4*159

theorem pc_offset (start i : Nat) :
    BitVec.ofNat 64 (4096+4*start) + BitVec.ofNat 64 (4*i) = BitVec.ofNat 64 (4096+4*(start+i)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

end TwoPermutationPrototype.QuadOpening
