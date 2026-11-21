import CommitGolfCandidate.GroupOpenImage
import CommitGolfCandidate.TwoPermutationMemoryBridge

/-! The opening image's embedded data: the first-pass table, 4096 entries of 16 bytes at
`dataBase openingImage = tableBase = 2^36 - 65536`, which the ABI leaves in `sp`.

Entry `e` (the tile offset `e = i % 4096` of position `i`) sits at `tableBase + 16 e`:
- dword 0: `tabT e | tabS e << 16 | tabR e << 32 | tabG e << 48`, where `tabT e` is the byte address of
  link-block word `3139 - (e % 374) / 11` (the chain entry of the position), `tabS e = 1536 + tabOff (e % 11)`
  is the address of the salt in the generator reply (rank `e % 11`), and `tabR e`, `tabG e` are the signed
  16-bit offsets from a quartet block to its reply and to the sibling quartet's node (`168, 136` for even
  quartets `e / 4`, `-1056, -856` for odd ones);
- dword 1: `tabD e = 4352 - 256 (e % 374)` modulo `2^64`, so that `256 i + tabD e` is the keyed
  generator's counter.

`table_data` reads every byte of the delivered data, checked once by the kernel (`bytes_ok`). -/
namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 TwoPermutationPrototype.RV64

/-- Byte address of the table: `dataBase openingImage`. -/
abbrev tableBase : Nat := 68719411200
/-- Word index of dword 0 of entry `e`. -/
abbrev tableWord (e : Nat) : Nat := 8589926400 + 2*e

/-- Byte offset of the salt of rank `r` in the K1 generator reply (`offAt`). -/
def tabOff (r : Nat) : Nat := if r=0 then 0 else if r=1 then 184 else 16*(r-1)
/-- Chain entry: byte address of word `3139 - (e % 374) / 11`. -/
def tabT (e : Nat) : Nat := 4096 + 4*(3139 - (e%374)/11)
/-- Salt source address in the reply at 1536. -/
def tabS (e : Nat) : Nat := 1536 + tabOff (e%11)
/-- Counter offset `4352 - 256 (e % 374)` as a 64-bit two's-complement value. -/
def tabD (e : Nat) : Nat := (18446744073709551616 + 4352 - 256*(e%374)) % 18446744073709551616
/-- Reply offset from the quartet block, as a 16-bit two's-complement value (`168` / `-1056`). -/
def tabR (e : Nat) : Nat := if e/4%2=1 then 64480 else 168
/-- Sibling-node offset from the quartet block, 16-bit two's complement (`136` / `-856`). -/
def tabG (e : Nat) : Nat := if e/4%2=1 then 64680 else 136
/-- Dword `h` (0 or 1) of entry `e`. -/
def tabEntry (e h : Nat) : Nat :=
  if h=0 then tabT e + 65536*tabS e + 4294967296*tabR e + 281474976710656*tabG e else tabD e
/-- Byte `k` of the table. -/
def tableByte (k : Nat) : Nat := tabEntry (k/16) (k/8%2) / 2^(8*(k%8)) % 256

/-- Byte `k` of a packed byte list, by the same tree lookup as `Packed.get 8`. -/
def pget : {n : Nat} → ArtifactEncoding.Packed n → Nat → Nat
  | _, .chunk _ payload, k => (payload >>> (8*k)) % 256
  | _, @ArtifactEncoding.Packed.join l _ left right, k => if k < l then pget left k else pget right (k-l)

theorem pget_get : ∀ {n : Nat} (packed : ArtifactEncoding.Packed n) (k : Fin n),
    (packed.get 8 k).toNat = pget packed k.val
  | _, .chunk _ payload, k => by
    simp [ArtifactEncoding.Packed.get, pget, BitVec.toNat_ofNat]
  | _, @ArtifactEncoding.Packed.join l r left right, k => by
    by_cases h : k.val < l
    · rw [ArtifactEncoding.get_join_left 8 left right k h, pget_get left]
      simp [pget, h]
    · rw [ArtifactEncoding.get_join_right 8 left right k h, pget_get right]
      simp [pget, h]

/-- `n` table bytes from `start` agree with the delivered data. -/
def checkRange (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => (pget K1Artifact.openingData (start+n) == tableByte (start+n)) && checkRange start n

theorem checkRange_sound (start : Nat) : ∀ n, checkRange start n = true → ∀ k, start ≤ k → k < start+n →
    pget K1Artifact.openingData k = tableByte k
  | 0, _, k, _, hi => absurd hi (by omega)
  | n+1, h, k, lo, hi => by
    simp only [checkRange, Bool.and_eq_true, beq_iff_eq] at h
    by_cases e : k = start+n
    · subst e; exact h.1
    · exact checkRange_sound start n h.2 k lo (by omega)

theorem bytes_ok_0 : checkRange 0 16384 = true := by decide +kernel
theorem bytes_ok_1 : checkRange 16384 16384 = true := by decide +kernel
theorem bytes_ok_2 : checkRange 32768 16384 = true := by decide +kernel
theorem bytes_ok_3 : checkRange 49152 16384 = true := by decide +kernel

theorem all_bytes (k : Nat) (hk : k < 65536) : pget K1Artifact.openingData k = tableByte k := by
  by_cases a : k < 16384
  · exact checkRange_sound 0 16384 bytes_ok_0 k (by omega) (by omega)
  by_cases b : k < 32768
  · exact checkRange_sound 16384 16384 bytes_ok_1 k (by omega) (by omega)
  by_cases c : k < 49152
  · exact checkRange_sound 32768 16384 bytes_ok_2 k (by omega) (by omega)
  · exact checkRange_sound 49152 16384 bytes_ok_3 k (by omega) (by omega)

theorem opening_data_eq : openingImage.data = ArtifactEncoding.decode 8 K1Artifact.openingData := by
  rw [← image_actual]
  dsimp only [K1Artifact.submission]

theorem table_length : openingImage.data.length = 65536 := by
  rw [opening_data_eq]; exact ArtifactEncoding.length_decode 8 _

theorem table_base_eq : dataBase openingImage = tableBase := by
  unfold dataBase; rw [table_length]; decide

theorem table_byte_lt (k : Nat) : tableByte k < 256 := by
  unfold tableByte; exact Nat.mod_lt _ (by decide)

/-- Every delivered data byte is the table byte. -/
theorem table_data (k : Nat) (hk : k < 65536) :
    openingImage.data[k]?.getD 0 = BitVec.ofNat 8 (tableByte k) := by
  rw [← List.getD_eq_getElem?_getD, opening_data_eq, ArtifactEncoding.getD_decode 8 _ k hk]
  apply BitVec.eq_of_toNat_eq
  rw [pget_get, BitVec.toNat_ofNat, all_bytes k hk, Nat.mod_eq_of_lt (table_byte_lt k)]

theorem tab_entry_lt (e h : Nat) : tabEntry e h < 2^64 := by
  unfold tabEntry tabT tabS tabOff tabD tabR tabG
  split_ifs <;> omega

/-- The table is in place: both dwords of every entry. -/
def TableAt (s : MachineState) : Prop :=
  ∀ e < 4096, ∀ h < 2, memoryView s (tableWord e + h) = BitVec.ofNat 64 (tabEntry e h)

/-- Eight little-endian bytes of a 64-bit value reassemble it. -/
theorem bytes_reassemble (w : Nat) (hw : w < 2^64) :
    (∑ j ∈ Finset.range 8, (w / 2^(8*j) % 256) * 2^(8*j)) = w := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  omega

/-- The aligned base plus the byte offset reconstructs the address (as in `riscv-zkvm`'s `ByteOps`,
restated here so the opener modules do not import its separation-logic `pure`). -/
theorem table_align_add (addr : Word) :
    alignToDword addr + BitVec.ofNat 64 (byteOffset addr) = addr := by
  unfold alignToDword byteOffset
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hdisj : (addr &&& ~~~7#64) &&& (addr &&& 7#64) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    rcases Bool.eq_false_or_eq_true ((7#64)[i]) with h7 | h7 <;> simp [h7]
  have hor : (addr &&& ~~~7#64) ||| (addr &&& 7#64) = addr := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    rcases Bool.eq_false_or_eq_true (addr[i]) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true ((7#64)[i]) with h7 | h7 <;>
    simp [ha, h7]
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, hor]

theorem table_offset_nat (q : Nat) (fit : q < 2^64) : byteOffset (BitVec.ofNat 64 q) = q % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit,
    show (7#64 : Word).toNat = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem table_align_eq (q : Nat) (fit : q < 2^64) :
    alignToDword (BitVec.ofNat 64 q) = BitVec.ofNat 64 (q - q % 8) := by
  let word : Word := BitVec.ofNat 64 q
  have wordAsNat : word.toNat = q := by
    simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  have alignedAtMost : (alignToDword word).toNat ≤ q := by
    rw [show (alignToDword word).toNat = word.toNat &&& (~~~7#64).toNat by exact BitVec.toNat_and _ _]
    exact Nat.and_le_left.trans (le_of_eq wordAsNat)
  have offset : byteOffset word = q % 8 := table_offset_nat q fit
  have whole := congrArg BitVec.toNat (table_align_add word)
  change ((alignToDword word)+BitVec.ofNat 64 (byteOffset word)).toNat = word.toNat at whole
  rw [BitVec.toNat_add, wordAsNat, BitVec.toNat_ofNat, offset, Nat.mod_eq_of_lt (by omega : q % 8 < 2^64),
    Nat.mod_eq_of_lt (by omega)] at whole
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  change (alignToDword word).toNat = _
  omega

/-- A halfword load inside an aligned dword. -/
theorem table_half (s : MachineState) (w j : Nat) (fit : 8*w+8 ≤ 2^64) (hj : j < 4) :
    s.getHalfword (BitVec.ofNat 64 (8*w+2*j)) = (s.getMem (BitVec.ofNat 64 (8*w)) >>> (j*16)).truncate 16 := by
  unfold MachineState.getHalfword extractHalfword
  rw [table_align_eq _ (by omega), table_offset_nat _ (by omega),
    show 8*w+2*j - (8*w+2*j)%8 = 8*w by omega, show (8*w+2*j)%8/2 = j by omega]

/-- The four halfwords of dword 0. -/
theorem half0 (v s r g : Nat) (hv : v < 65536) (_hs : s < 65536) (_hr : r < 65536) (_hg : g < 65536) :
    ((BitVec.ofNat 64 (v + 65536*s + 4294967296*r + 281474976710656*g) >>> (0*16)).truncate 16).zeroExtend 64 =
      BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow]
  omega

theorem half1 (v s r g : Nat) (hv : v < 65536) (hs : s < 65536) (hr : r < 65536) (hg : g < 65536) :
    ((BitVec.ofNat 64 (v + 65536*s + 4294967296*r + 281474976710656*g) >>> (1*16)).truncate 16).zeroExtend 64 =
      BitVec.ofNat 64 s := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow]
  omega

theorem half2 (v s r g : Nat) (hv : v < 65536) (hs : s < 65536) (hr : r < 65536) (hg : g < 65536) :
    ((BitVec.ofNat 64 (v + 65536*s + 4294967296*r + 281474976710656*g) >>> (2*16)).truncate 16) =
      BitVec.ofNat 16 r := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow]
  omega

theorem half3 (v s r g : Nat) (hv : v < 65536) (hs : s < 65536) (hr : r < 65536) (hg : g < 65536) :
    ((BitVec.ofNat 64 (v + 65536*s + 4294967296*r + 281474976710656*g) >>> (3*16)).truncate 16) =
      BitVec.ofNat 16 g := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow]
  omega

theorem tab_t_lt (e : Nat) : tabT e < 65536 := by unfold tabT; omega
theorem tab_s_lt (e : Nat) : tabS e < 65536 := by unfold tabS tabOff; split_ifs <;> omega
theorem tab_r_lt (e : Nat) : tabR e < 65536 := by unfold tabR; split_ifs <;> omega
theorem tab_g_lt (e : Nat) : tabG e < 65536 := by unfold tabG; split_ifs <;> omega

/-- Accesses inside the table are valid. -/
theorem table_access (q n : Nat) (al : q % n = 0) (room : q+n ≤ 2^36) :
    accessValid (BitVec.ofNat 64 q) n = true := by
  have small : q < 2^64 := by omega
  have nat : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  simp [accessValid, rangeValid, nat, al, MEMORY_BYTES]
  omega

end TwoPermutationPrototype.GroupedOpening
