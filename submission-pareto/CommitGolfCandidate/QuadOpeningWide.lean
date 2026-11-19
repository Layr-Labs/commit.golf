import CommitGolfCandidate.QuadOpeningCapMoves
import CommitGolfCandidate.QuadOpeningBytes
import CommitGolfCandidate.ProjectedHalfwordMemory
import CommitGolfCandidate.QOpeningFootprint
import RiscvZkvm.Rv64.Logic.ByteOps

/-! Wide record copies for the quad2 opener (opening words 773..882).

Each of the 18 wide copy sites (three leaf mates, three quad mates and the quad2 sibling, 32 bytes;
eleven projected siblings, 30 bytes) starts with `jal x10,<stub>`. The stub for its size tests the
destination's alignment (`x21 & 7`, with `x7` the 8-aligned source): an 8-aligned destination copies
doublewords, a 4-aligned one words, and a destination at 2 mod 4 loads doublewords and stores each as
a halfword, a shifted word and a shifted halfword. Every path returns with `jalr x0,back(x10)` to the
word after the site's halfword pairs, having changed only `x10` and `x31`. The idea of word-wide
record copies through a `jal x10` stub, and the byte lemmas below up to `half_store`, follow
kaankolcu's 5d0c1c31 (GroupOpenWideCopy); the split path for 2 mod 4 destinations is new. -/

namespace TwoPermutationPrototype.QuadOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
set_option maxRecDepth 8192

namespace Wide

theorem offset_nat (q : Nat) (fit : q < 2^64) : byteOffset (BitVec.ofNat 64 q) = q % 8 := by
  unfold byteOffset
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit,
    show (7#64 : Word).toNat = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem align_nat (q : Nat) (fit : q < 2^64) : (alignToDword (BitVec.ofNat 64 q)).toNat = q - q % 8 := by
  let word : Word := BitVec.ofNat 64 q
  let aligned := alignToDword word
  have wordAsNat : word.toNat = q := by
    simp only [word, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : q < 2^64)]
  have alignedAtMost : aligned.toNat ≤ q := by
    rw [show aligned.toNat = word.toNat &&& (~~~7#64).toNat by exact BitVec.toNat_and _ _]
    exact Nat.and_le_left.trans (le_of_eq wordAsNat)
  have offset : byteOffset word = q % 8 := offset_nat q (by omega)
  have whole := congrArg BitVec.toNat (alignToDword_add_byteOffset word)
  change (aligned+BitVec.ofNat 64 (byteOffset word)).toNat = word.toNat at whole
  rw [BitVec.toNat_add, wordAsNat, BitVec.toNat_ofNat, offset, Nat.mod_eq_of_lt (by omega : q % 8 < 2^64),
    Nat.mod_eq_of_lt (by omega)] at whole
  change aligned.toNat = _
  omega

theorem align_eq (q : Nat) (fit : q < 2^64) :
    alignToDword (BitVec.ofNat 64 q) = BitVec.ofNat 64 (q - q % 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [align_nat q fit, BitVec.toNat_ofNat]
  exact (Nat.mod_eq_of_lt (by omega)).symm

theorem of_align (q : Word) (base : Nat)
    (same : alignToDword q = BitVec.ofNat 64 base) :
    q = BitVec.ofNat 64 (base + byteOffset q) := by
  have whole := alignToDword_add_byteOffset q
  rw [same, ← BitVec.ofNat_add] at whole
  exact whole.symm

theorem word_byte (d : Word) (q i : Nat) (hq : q < 2) (hi : i < 4) :
    ((extractWord32 d q) >>> (8*i)).truncate 8 = extractByte d (4*q+i) := by
  unfold extractWord32 extractByte
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  rw [show q * 32 + (8 * i + j) = (4*q+i)*8 + j by omega, show decide (8 * i + j < 32) = true by simp; omega,
    Bool.true_and]

theorem half_byte (d : Word) (q i : Nat) (hq : q < 4) (hi : i < 2) :
    ((extractHalfword d q) >>> (8*i)).truncate 8 = extractByte d (2*q+i) := by
  unfold extractHalfword extractByte
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  rw [show q * 16 + (8 * i + j) = (2*q+i)*8 + j by omega, show decide (8 * i + j < 16) = true by simp; omega,
    Bool.true_and]

theorem byte_at (s : MachineState) (base i : Nat) (aligned : base % 8 = 0) (small : i < 8) (fit : base+8 ≤ 2^64) :
    s.getByte (BitVec.ofNat 64 (base+i)) = extractByte (s.getMem (BitVec.ofNat 64 base)) i := by
  unfold MachineState.getByte
  rw [align_eq (base+i) (by omega), offset_nat (base+i) (by omega),
    show base+i - (base+i)%8 = base by omega, show (base+i)%8 = i by omega]

/-- `ld; sd` between 8-aligned dwords copies the 8 bytes and touches only the target dword. -/
theorem dword_store (s : MachineState) (S T : Nat) (sa : S % 8 = 0) (ta : T % 8 = 0)
    (sf : S+8 ≤ 2^64) (tf : T+8 ≤ 2^64) :
    ByteCopy s (s.setMem (BitVec.ofNat 64 T) (s.getMem (BitVec.ofNat 64 S))) S T 8 ∧
    ∀ q, q ≠ BitVec.ofNat 64 T →
      (s.setMem (BitVec.ofNat 64 T) (s.getMem (BitVec.ofNat 64 S))).getMem q = s.getMem q := by
  refine ⟨⟨fun i inside => ?_, fun q outside => ?_⟩, fun q other => MachineState.getMem_setMem_ne other⟩
  · rw [byte_at _ T i ta inside tf, byte_at _ S i sa inside sf, MachineState.getMem_setMem_eq]
  · unfold MachineState.getByte
    by_cases same : alignToDword q = BitVec.ofNat 64 T
    · exfalso
      exact outside (byteOffset q) byteOffset_lt_8 (of_align q T same)
    · rw [MachineState.getMem_setMem_ne same]

theorem mask_bit (n : Nat) : (4294967295#64).getLsbD n = decide (n < 32) := by
  rw [show (4294967295#64) = BitVec.ofNat 64 (2^32-1) from rfl, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  by_cases h : n < 32
  · simp [h]; omega
  · simp [h]

theorem mask_elem (n : Nat) (h : n < 64) : (4294967295#64)[n] = decide (n < 32) := by
  rw [← BitVec.getLsbD_eq_getElem]; exact mask_bit n

set_option linter.unusedSimpArgs false in
theorem replace_word_byte (w : Word) (v : BitVec 32) (p j : Nat) (hp : p < 2) (hj : j < 8) :
    extractByte (replaceWord32 w p v) j =
      if 4*p ≤ j ∧ j < 4*p+4 then (v >>> (8*(j-4*p))).truncate 8 else extractByte w j := by
  unfold extractByte replaceWord32
  dsimp only
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  by_cases inside : 4*p ≤ j ∧ j < 4*p+4
  · rw [if_pos inside]
    have e : j * 8 + k - p * 32 = 8 * (j - 4 * p) + k := by omega
    have l1 : j*8+k < 64 := by omega
    have l2 : ¬ (j*8+k < p*32) := by omega
    have l3 : j*8+k-p*32 < 64 := by omega
    have l4 : j*8+k-p*32 < 32 := by omega
    simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hk, mask_bit, l1, l2, l3, l4, e,
      mask_elem (8 * (j - 4 * p) + k) (by omega), show 8 * (j - 4 * p) + k < 32 by omega]
  · rw [if_neg inside]
    have l1 : j*8+k < 64 := by omega
    simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.getLsbD_or, BitVec.getLsbD_and,
      BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, hk, mask_bit, l1]
    by_cases below : j*8+k < p*32
    · simp [below]
    · have out : ¬ (j*8+k-p*32 < 32) := by omega
      have out64 : j*8+k-p*32 < 64 := by omega
      simp [below, out, out64, mask_elem (j * 8 + k - p * 32) out64, BitVec.getLsbD_of_ge v _ (by omega : 32 ≤ j * 8 + k - p * 32)]

/-- `lw; sw` between 4-aligned words copies the 4 bytes and touches only the target dword. -/
theorem word_store (s : MachineState) (S T : Nat) (sa : S % 4 = 0) (ta : T % 4 = 0)
    (sf : S+4 ≤ 2^64) (tf : T+4 ≤ 2^64) :
    ByteCopy s (s.setWord32 (BitVec.ofNat 64 T) (s.getWord32 (BitVec.ofNat 64 S))) S T 4 ∧
    ∀ q, q ≠ alignToDword (BitVec.ofNat 64 T) →
      (s.setWord32 (BitVec.ofNat 64 T) (s.getWord32 (BitVec.ofNat 64 S))).getMem q = s.getMem q := by
  have offT := offset_nat T (by omega)
  have offS := offset_nat S (by omega)
  have alignT := align_eq T (by omega)
  have alignS := align_eq S (by omega)
  have pos : byteOffset (BitVec.ofNat 64 T) / 4 < 2 := by rw [offT]; omega
  refine ⟨⟨fun i inside => ?_, fun q outside => ?_⟩, fun q other => ?_⟩
  · have alignTi : alignToDword (BitVec.ofNat 64 (T+i)) = alignToDword (BitVec.ofNat 64 T) := by
      rw [align_eq (T+i) (by omega), alignT, show T+i - (T+i)%8 = T - T%8 by omega]
    have alignSi : alignToDword (BitVec.ofNat 64 (S+i)) = alignToDword (BitVec.ofNat 64 S) := by
      rw [align_eq (S+i) (by omega), alignS, show S+i - (S+i)%8 = S - S%8 by omega]
    unfold MachineState.getByte MachineState.setWord32 MachineState.getWord32
    dsimp only
    rw [alignTi, alignSi, MachineState.getMem_setMem_eq, offset_nat (T+i) (by omega), offset_nat (S+i) (by omega),
      replace_word_byte _ _ _ _ pos (by omega), offT, if_pos (by omega), offS,
      show 8 * ((T+i)%8 - 4*(T%8/4)) = 8*i by omega, word_byte _ _ _ (by omega) inside,
      show 4*(S%8/4)+i = (S+i)%8 by omega]
  · unfold MachineState.getByte MachineState.setWord32
    dsimp only
    by_cases same : alignToDword q = alignToDword (BitVec.ofNat 64 T)
    · rw [same, MachineState.getMem_setMem_eq, replace_word_byte _ _ _ _ pos byteOffset_lt_8]
      by_cases hit : 4 * (byteOffset (BitVec.ofNat 64 T) / 4) ≤ byteOffset q ∧
          byteOffset q < 4 * (byteOffset (BitVec.ofNat 64 T) / 4) + 4
      · exfalso
        rw [offT] at hit
        have back := of_align q (T - T%8) (by rw [same, alignT])
        apply outside (byteOffset q - T%8) (by omega)
        exact back.trans (congrArg (BitVec.ofNat 64) (by omega))
      · rw [if_neg hit]
    · rw [MachineState.getMem_setMem_ne same]
  · unfold MachineState.setWord32
    dsimp only
    exact MachineState.getMem_setMem_ne other

/-- `lhu; sh` between 2-aligned halfwords copies the 2 bytes and touches only the target dword. -/
theorem half_store (s : MachineState) (S T : Nat) (sa : S % 2 = 0) (ta : T % 2 = 0)
    (sf : S+2 ≤ 2^64) (tf : T+2 ≤ 2^64) :
    ByteCopy s (s.setHalfword (BitVec.ofNat 64 T) (s.getHalfword (BitVec.ofNat 64 S))) S T 2 ∧
    ∀ q, q ≠ alignToDword (BitVec.ofNat 64 T) →
      (s.setHalfword (BitVec.ofNat 64 T) (s.getHalfword (BitVec.ofNat 64 S))).getMem q = s.getMem q := by
  have offT := offset_nat T (by omega)
  have offS := offset_nat S (by omega)
  have alignT := align_eq T (by omega)
  have alignS := align_eq S (by omega)
  refine ⟨⟨fun i inside => ?_, fun q outside => ?_⟩, fun q other => ?_⟩
  · have alignTi : alignToDword (BitVec.ofNat 64 (T+i)) = alignToDword (BitVec.ofNat 64 T) := by
      rw [align_eq (T+i) (by omega), alignT, show T+i - (T+i)%8 = T - T%8 by omega]
    have alignSi : alignToDword (BitVec.ofNat 64 (S+i)) = alignToDword (BitVec.ofNat 64 S) := by
      rw [align_eq (S+i) (by omega), alignS, show S+i - (S+i)%8 = S - S%8 by omega]
    rw [ProjectedHalfword.store_byte, if_pos ⟨alignTi, by rw [offset_nat (T+i) (by omega), offT]; omega⟩,
      offset_nat (T+i) (by omega)]
    unfold MachineState.getHalfword MachineState.getByte
    rw [alignSi, offS, offset_nat (S+i) (by omega), show (T+i)%8%2*8 = 8*i by omega,
      half_byte _ _ _ (by omega) inside, show 2*(S%8/2)+i = (S+i)%8 by omega]
  · rw [ProjectedHalfword.store_byte]
    by_cases hit : alignToDword q = alignToDword (BitVec.ofNat 64 T) ∧
        byteOffset q / 2 = byteOffset (BitVec.ofNat 64 T) / 2
    · exfalso
      rw [offT] at hit
      have back := of_align q (T - T%8) (by rw [hit.1, alignT])
      have ob := @byteOffset_lt_8 q
      apply outside (byteOffset q - T%8) (by omega)
      exact back.trans (congrArg (BitVec.ofNat 64) (by omega))
    · rw [if_neg hit]
  · unfold MachineState.setHalfword
    dsimp only
    exact MachineState.getMem_setMem_ne other

/-! #### Stores of shifted pieces of a loaded doubleword (the 2 mod 4 path) -/

theorem bits_low (v : Word) (i : Nat) (hi : i < 2) :
    ((v.truncate 16) >>> (8*i)).truncate 8 = extractByte v i := by
  unfold extractByte
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  rw [show 8 * i + j = i * 8 + j by omega]
  have b : i * 8 + j < 16 := by omega
  simp [b]

theorem bits_mid (v : Word) (m : Nat) (hm : m < 4) :
    (((v >>> 16).truncate 32) >>> (8*m)).truncate 8 = extractByte v (2+m) := by
  unfold extractByte
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  rw [show 16 + (8 * m + j) = (2 + m) * 8 + j by omega]
  have b : 8 * m + j < 32 := by omega
  simp [b]

theorem bits_high (v : Word) (m : Nat) (hm : m < 2) :
    ((((v >>> 16) >>> 32).truncate 16) >>> (8*m)).truncate 8 = extractByte v (6+m) := by
  unfold extractByte
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  rw [show 48 + (8 * m + j) = (6 + m) * 8 + j by omega]
  have b : 8 * m + j < 16 := by omega
  simp [b]

theorem put_half_hit (s : MachineState) (T i : Nat) (u : BitVec 16) (ta : T % 2 = 0) (hi : i < 2)
    (tf : T+2 ≤ 2^64) :
    (s.setHalfword (BitVec.ofNat 64 T) u).getByte (BitVec.ofNat 64 (T+i)) = (u >>> (8*i)).truncate 8 := by
  rw [ProjectedHalfword.store_byte, if_pos]
  · rw [offset_nat (T+i) (by omega), show (T+i) % 8 % 2 * 8 = 8*i by omega]
  · refine ⟨?_, ?_⟩
    · rw [align_eq (T+i) (by omega), align_eq T (by omega), show T+i - (T+i)%8 = T - T%8 by omega]
    · rw [offset_nat (T+i) (by omega), offset_nat T (by omega)]; omega

theorem put_half_miss (s : MachineState) (T : Nat) (u : BitVec 16) (ta : T % 2 = 0) (tf : T+2 ≤ 2^64)
    (q : Word) (outside : ∀ i < 2, q ≠ BitVec.ofNat 64 (T+i)) :
    (s.setHalfword (BitVec.ofNat 64 T) u).getByte q = s.getByte q := by
  rw [ProjectedHalfword.store_byte, if_neg]
  intro hit
  have offT := offset_nat T (by omega)
  rw [offT] at hit
  have back := of_align q (T - T%8) (by rw [hit.1, align_eq T (by omega)])
  have ob := @byteOffset_lt_8 q
  apply outside (byteOffset q - T%8) (by omega)
  exact back.trans (congrArg (BitVec.ofNat 64) (by omega))

theorem put_word_hit (s : MachineState) (T i : Nat) (u : BitVec 32) (ta : T % 4 = 0) (hi : i < 4)
    (tf : T+4 ≤ 2^64) :
    (s.setWord32 (BitVec.ofNat 64 T) u).getByte (BitVec.ofNat 64 (T+i)) = (u >>> (8*i)).truncate 8 := by
  have offT := offset_nat T (by omega)
  have alignT := align_eq T (by omega)
  have pos : byteOffset (BitVec.ofNat 64 T) / 4 < 2 := by rw [offT]; omega
  have alignTi : alignToDword (BitVec.ofNat 64 (T+i)) = alignToDword (BitVec.ofNat 64 T) := by
    rw [align_eq (T+i) (by omega), alignT, show T+i - (T+i)%8 = T - T%8 by omega]
  unfold MachineState.getByte MachineState.setWord32
  dsimp only
  rw [alignTi, MachineState.getMem_setMem_eq, offset_nat (T+i) (by omega),
    replace_word_byte _ _ _ _ pos (by omega), offT, if_pos (by omega),
    show 8 * ((T+i)%8 - 4*(T%8/4)) = 8*i by omega]

theorem put_word_miss (s : MachineState) (T : Nat) (u : BitVec 32) (ta : T % 4 = 0) (tf : T+4 ≤ 2^64)
    (q : Word) (outside : ∀ i < 4, q ≠ BitVec.ofNat 64 (T+i)) :
    (s.setWord32 (BitVec.ofNat 64 T) u).getByte q = s.getByte q := by
  have offT := offset_nat T (by omega)
  have alignT := align_eq T (by omega)
  have pos : byteOffset (BitVec.ofNat 64 T) / 4 < 2 := by rw [offT]; omega
  unfold MachineState.getByte MachineState.setWord32
  dsimp only
  by_cases same : alignToDword q = alignToDword (BitVec.ofNat 64 T)
  · rw [same, MachineState.getMem_setMem_eq, replace_word_byte _ _ _ _ pos byteOffset_lt_8]
    by_cases hit : 4 * (byteOffset (BitVec.ofNat 64 T) / 4) ≤ byteOffset q ∧
        byteOffset q < 4 * (byteOffset (BitVec.ofNat 64 T) / 4) + 4
    · exfalso
      rw [offT] at hit
      have back := of_align q (T - T%8) (by rw [same, alignT])
      apply outside (byteOffset q - T%8) (by omega)
      exact back.trans (congrArg (BitVec.ofNat 64) (by omega))
    · rw [if_neg hit]
  · rw [MachineState.getMem_setMem_ne same]

end Wide

open Wide

theorem copy_congr_mem {s t u : MachineState} {S T n : Nat} (same : t.mem = u.mem)
    (copy : ByteCopy s u S T n) : ByteCopy s t S T n :=
  ⟨fun i inside => by simpa only [MachineState.getByte, MachineState.getMem, same] using copy.copied i inside,
   fun q outside => by simpa only [MachineState.getByte, MachineState.getMem, same] using copy.frame q outside⟩

theorem copy_congr_before {s s' t : MachineState} {S T n : Nat} (same : s.mem = s'.mem)
    (copy : ByteCopy s' t S T n) : ByteCopy s t S T n :=
  ⟨fun i inside => by simpa only [MachineState.getByte, MachineState.getMem, same] using copy.copied i inside,
   fun q outside => by simpa only [MachineState.getByte, MachineState.getMem, same] using copy.frame q outside⟩

/-- Two adjacent copies whose second source the first does not overwrite. -/
theorem copy_extend {before middle after : MachineState} {source target first second : Nat}
    (head : ByteCopy before middle source target first)
    (tail : ByteCopy middle after (source+first) (target+first) second)
    (apart : source+first+second ≤ target) (fit : target+first+second ≤ 2^64) :
    ByteCopy before after source target (first+second) := by
  constructor
  · intro i inside
    by_cases low : i < first
    · rw [tail.frame]
      · exact head.copied i low
      · intro j hj same
        have eq := QOpening.nat_address_injective (by omega) (by omega) same
        omega
    · have shifted := tail.copied (i-first) (by omega)
      rw [show target+first+(i-first) = target+i by omega, show source+first+(i-first) = source+i by omega] at shifted
      rw [shifted, head.frame]
      intro j hj same
      have eq := QOpening.nat_address_injective (by omega) (by omega) same
      omega
  · intro address outside
    rw [tail.frame _ (fun j hj => by
      have := outside (first+j) (by omega)
      rwa [← Nat.add_assoc] at this)]
    exact head.frame _ (fun j hj => outside j (by omega))

/-! ### Code -/

/-- Copy sites routed through a stub. -/
def CopySite.wide : CopySite → Bool
  | .nonce | .cap => false
  | _ => true

/-- Bytes copied by a wide site's stub. -/
def CopySite.size : CopySite → Nat
  | .sibling _ => 30
  | _ => 32

def CopySite.stub (site : CopySite) : Nat := if site.size = 32 then 773 else 828

def Decodes (word : Nat) (instruction : Instr) : Prop :=
  (openingImage.code[word]?).bind QOpening.decodeBase = some instruction

instance (word : Nat) (instruction : Instr) : Decidable (Decodes word instruction) := by
  unfold Decodes; infer_instance

def wideLoad (width : Nat) (imm : Nat) : Instr :=
  if width = 8 then .LD .x31 .x7 (BitVec.ofNat 12 imm)
  else if width = 4 then .LW .x31 .x7 (BitVec.ofNat 12 imm)
  else .LHU .x31 .x7 (BitVec.ofNat 12 imm)

def wideStore (width : Nat) (imm : Nat) : Instr :=
  if width = 8 then .SD .x21 .x31 (BitVec.ofNat 12 imm)
  else if width = 4 then .SW .x21 .x31 (BitVec.ofNat 12 imm)
  else .SH .x21 .x31 (BitVec.ofNat 12 imm)

/-- `count` load/store pairs of `width` bytes at words `word, word+1, ...`, the `k`-th reading
`load+width*k(x7)` and writing `load+width*k(x21)`. -/
def PairsAt (word count width load : Nat) : Prop :=
  ∀ k < count, Decodes (word+2*k) (wideLoad width (load+width*k)) ∧
    Decodes (word+2*k+1) (wideStore width (load+width*k))

instance (word count width load : Nat) : Decidable (PairsAt word count width load) := by
  unfold PairsAt; infer_instance

/-- One split chunk at `word`: `ld x31,k(x7); sh x31,k(x21); srli x31,16; sw x31,k+2(x21)`, followed
(for a full chunk) by `srli x31,32; sh x31,k+6(x21)`. -/
def SplitAt (word k : Nat) (full : Bool) : Prop :=
  Decodes word (.LD .x31 .x7 (BitVec.ofNat 12 k)) ∧ Decodes (word+1) (.SH .x21 .x31 (BitVec.ofNat 12 k)) ∧
  Decodes (word+2) (.SRLI .x31 .x31 16) ∧ Decodes (word+3) (.SW .x21 .x31 (BitVec.ofNat 12 (k+2))) ∧
  (full = true → Decodes (word+4) (.SRLI .x31 .x31 32) ∧
    Decodes (word+5) (.SH .x21 .x31 (BitVec.ofNat 12 (k+6))))

instance (word k : Nat) (full : Bool) : Decidable (SplitAt word k full) := by
  unfold SplitAt; infer_instance

def SplitsAt (word count : Nat) : Prop := ∀ j < count, SplitAt (word+6*j) (8*j) true

instance (word count : Nat) : Decidable (SplitsAt word count) := by
  unfold SplitsAt; infer_instance

/-- The dispatch words shared by both stubs, relative to `base`. -/
structure Dispatch (base dword : Nat) : Prop where
  test : Decodes base (.ANDI .x31 .x21 7)
  eight : Decodes (base+1) (.BEQ .x31 .x0 (BitVec.ofNat 13 (4*(dword-1))))
  less : Decodes (base+2) (.ADDI .x31 .x31 4092)
  four : Decodes (base+3) (.BEQ .x31 .x0 140)

structure Stub32Code : Prop where
  dispatch : Dispatch 773 29
  splits : SplitsAt 777 4
  splitBack : Decodes 801 (.JALR .x0 .x10 124)
  dwords : PairsAt 802 4 8 0
  dwordsBack : Decodes 810 (.JALR .x0 .x10 124)
  words : PairsAt 811 8 4 0
  wordsBack : Decodes 827 (.JALR .x0 .x10 124)

structure Stub30Code : Prop where
  dispatch : Dispatch 828 27
  splits : SplitsAt 832 3
  tail : SplitAt 850 24 false
  splitBack : Decodes 854 (.JALR .x0 .x10 116)
  dwords : PairsAt 855 3 8 0
  dwordWord : PairsAt 861 1 4 24
  dwordHalf : PairsAt 863 1 2 28
  dwordsBack : Decodes 865 (.JALR .x0 .x10 116)
  words : PairsAt 866 7 4 0
  wordHalf : PairsAt 880 1 2 28
  wordsBack : Decodes 882 (.JALR .x0 .x10 116)

set_option maxHeartbeats 4000000 in
theorem stub32_code : Stub32Code := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

set_option maxHeartbeats 4000000 in
theorem stub30_code : Stub30Code := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

def entryJump (site : CopySite) : Instr := .JAL .x10 (BitVec.ofNat 21 (4*(site.stub-site.start)))

structure SiteFacts (site : CopySite) : Prop where
  size : site.size = 32 ∨ site.size = 30
  startFit : site.start+site.size ≤ 773
  entry : Decodes site.start (entryJump site)
  jump : BitVec.ofNat 64 (4096+4*site.start) + signExtend21 (BitVec.ofNat 21 (4*(site.stub-site.start))) =
    BitVec.ofNat 64 (4096+4*site.stub)
  back : (BitVec.ofNat 64 (4096+4*(site.start+1)) + signExtend12 (BitVec.ofNat 12 (4*(site.size-1)))) &&& ~~~1#64 =
    BitVec.ofNat 64 (4096+4*(site.start+site.size))

set_option maxHeartbeats 4000000 in
theorem site_facts (site : CopySite) (wide : site.wide = true) : SiteFacts site := by
  cases site with
  | leaf j => clear wide; constructor <;> revert j <;> decide
  | quad j => clear wide; constructor <;> revert j <;> decide
  | firstSibling => constructor <;> decide
  | sibling l => clear wide; constructor <;> revert l <;> decide
  | _ => simp [CopySite.wide] at wide

/-! ### One step -/

def stepKind : Instr → Bool
  | .LHU .. | .SH .. | .LW .. | .SW .. | .LD .. | .SD .. | .ADDI .. | .ANDI .. | .SRLI .. | .BEQ .. | .JAL .. | .JALR .. =>
    true
  | _ => false

theorem run_step (s : MachineState) (word : Nat) (i : Instr) (bounded : word < 883)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*word)) (dec : Decodes word i) (kind : stepKind i = true)
    (valid : memoryArgumentsValid s i = true) : RunsOpeningBlock s (execInstrBr s i) 1 := by
  intro fuel coins
  have run := execute_unit_steps openingImage 1 fuel (fun n => if n = 0 then s else execInstrBr s i) coins (by
    intro n hn
    have n0 : n = 0 := by omega
    subst n0
    refine ⟨.base i, by simpa using packed_fetch_base s word i bounded pc dec, ?_, ?_⟩
    · simp only [if_pos, Nat.zero_add, show (1 = 0) = False from by simp, if_false]
      cases i <;> simp_all [stepKind, ordinaryStep]
    · cases i <;> simp_all [stepKind] <;> rfl)
  simpa using run

theorem sign12 (n : Nat) (small : n < 2048) : signExtend12 (BitVec.ofNat 12 n) = BitVec.ofNat 64 n := by
  unfold signExtend12
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · rw [BitVec.msb_eq_decide]
    simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]
    omega

theorem access_ok (a w : Nat) (aligned : a % w = 0) (fit : a+w ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 a) w = true := by
  have small : a < 2^64 := by unfold MEMORY_BYTES at fit; omega
  unfold accessValid rangeValid
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
  simp only [aligned, decide_true, Bool.and_true, decide_eq_true_eq]
  exact fit

private theorem mem_setReg' (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl

theorem getMem_congr {a b : MachineState} (same : a.mem = b.mem) (q : Word) : a.getMem q = b.getMem q := by
  simp only [MachineState.getMem, same]

theorem reg_setHalfword (u : MachineState) (a : Word) (v : BitVec 16) (r : Reg) :
    (u.setHalfword a v).getReg r = u.getReg r := by cases r <;> rfl

theorem reg_setWord32 (u : MachineState) (a : Word) (v : BitVec 32) (r : Reg) :
    (u.setWord32 a v).getReg r = u.getReg r := by cases r <;> rfl

theorem reg_setMem (u : MachineState) (a v : Word) (r : Reg) :
    (u.setMem a v).getReg r = u.getReg r := by cases r <;> rfl

theorem sign_truncate (v : BitVec 32) : (v.signExtend 64).truncate 32 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.truncate, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi]
  intro _; omega

theorem zero_truncate (v : BitVec 16) : (v.zeroExtend 64).truncate 16 = v := by
  apply BitVec.eq_of_toNat_eq
  have fit : v.toNat < 2^16 := v.isLt
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt fit, Nat.mod_eq_of_lt (show v.toNat < 2^64 by omega)]

/-! ### Load/store pairs -/

def pairStep (width load k : Nat) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (wideLoad width (load+width*k))) (wideStore width (load+width*k))

def pairsRun (width load : Nat) : Nat → Nat → MachineState → MachineState
  | _, 0, s => s
  | k, n+1, s => pairsRun width load (k+1) n (pairStep width load k s)

structure PairPost (s t : MachineState) (S T width : Nat) : Prop where
  pc : t.pc = s.pc + BitVec.ofNat 64 8
  regs : ∀ r, r ≠ .x31 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T width
  frame : ∀ q : Word, q ≠ alignToDword (BitVec.ofNat 64 T) → t.getMem q = s.getMem q

theorem pair_post (width : Nat) (hw : width = 2 ∨ width = 4 ∨ width = 8)
    (load k S T : Nat) (s : MachineState)
    (sr : s.getReg .x7 = BitVec.ofNat 64 S) (dr : s.getReg .x21 = BitVec.ofNat 64 T)
    (immL : load + width*k < 2048)
    (sa : (S+load+width*k) % width = 0) (ta : (T+load+width*k) % width = 0)
    (sf : S+load+width*k+width ≤ MEMORY_BYTES) (tf : T+load+width*k+width ≤ MEMORY_BYTES) :
    memoryArgumentsValid s (wideLoad width (load+width*k)) = true ∧
    memoryArgumentsValid (execInstrBr s (wideLoad width (load+width*k))) (wideStore width (load+width*k)) = true ∧
    PairPost s (pairStep width load k s) (S+load+width*k) (T+load+width*k) width := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  have srcAddr : s.getReg .x7 + signExtend12 (BitVec.ofNat 12 (load+width*k)) =
      BitVec.ofNat 64 (S+load+width*k) := by
    rw [sr, sign12 _ immL, ← BitVec.ofNat_add, Nat.add_assoc]
  have dstAddr (u : MachineState) (same : u.getReg .x21 = s.getReg .x21) :
      u.getReg .x21 + signExtend12 (BitVec.ofNat 12 (load+width*k)) = BitVec.ofNat 64 (T+load+width*k) := by
    rw [same, dr, sign12 _ immL, ← BitVec.ofNat_add, Nat.add_assoc]
  have regs (u : MachineState) (r : Reg) (h : r ≠ .x31) (v : Word) : (u.setReg .x31 v).getReg r = u.getReg r :=
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  have eight : s.pc + 4 + 4 = s.pc + BitVec.ofNat 64 8 := by rw [BitVec.add_assoc]; rfl
  rcases hw with rfl | rfl | rfl
  · -- halfwords
    simp only [pairStep, wideLoad, wideStore, show (2 = 8) = False from by decide, show (2 = 4) = False from by decide,
      if_false]
    let a := execInstrBr s (.LHU .x31 .x7 (BitVec.ofNat 12 (load+2*k)))
    have aMem : a.mem = s.mem := by simp only [a, execInstrBr, MachineState.setPC, mem_setReg']
    have a21 : a.getReg .x21 = s.getReg .x21 := by
      simp only [a, execInstrBr, MachineState.getReg_setPC]; exact regs _ _ (by decide) _
    have a31 : (a.getReg .x31).truncate 16 = s.getHalfword (BitVec.ofNat 64 (S+load+2*k)) := by
      simp only [a, execInstrBr, MachineState.getReg_setPC, srcAddr,
        MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0), zero_truncate]
    obtain ⟨copy, frame⟩ := half_store s (S+load+2*k) (T+load+2*k) sa ta (by omega) (by omega)
    have tMem : (execInstrBr a (.SH .x21 .x31 (BitVec.ofNat 12 (load+2*k)))).mem =
        (s.setHalfword (BitVec.ofNat 64 (T+load+2*k)) (s.getHalfword (BitVec.ofNat 64 (S+load+2*k)))).mem := by
      simp only [execInstrBr, MachineState.setPC, dstAddr a a21, a31]
      unfold MachineState.setHalfword
      simp only [MachineState.setMem, MachineState.getMem, aMem]
    refine ⟨?_, ?_, ⟨?_, ?_, copy_congr_mem tMem copy, fun q other => (getMem_congr tMem q).trans (frame q other)⟩⟩
    · unfold memoryArgumentsValid
      simp only [memAccess]
      rw [srcAddr]
      exact access_ok _ _ sa (by omega)
    · unfold memoryArgumentsValid
      simp only [memAccess]
      rw [dstAddr a a21]
      exact access_ok _ _ ta (by omega)
    · simp only [execInstrBr, MachineState.setPC, a]
      exact eight
    · intro r h
      simp only [execInstrBr, MachineState.getReg_setPC, a, reg_setHalfword]
      exact regs _ _ h _
  · -- words
    simp only [pairStep, wideLoad, wideStore, show (4 = 8) = False from by decide, if_true, if_false]
    let a := execInstrBr s (.LW .x31 .x7 (BitVec.ofNat 12 (load+4*k)))
    have aMem : a.mem = s.mem := by simp only [a, execInstrBr, MachineState.setPC, mem_setReg']
    have a21 : a.getReg .x21 = s.getReg .x21 := by
      simp only [a, execInstrBr, MachineState.getReg_setPC]; exact regs _ _ (by decide) _
    have a31 : (a.getReg .x31).truncate 32 = s.getWord32 (BitVec.ofNat 64 (S+load+4*k)) := by
      simp only [a, execInstrBr, MachineState.getReg_setPC, srcAddr,
        MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0), sign_truncate]
    obtain ⟨copy, frame⟩ := word_store s (S+load+4*k) (T+load+4*k) sa ta (by omega) (by omega)
    have tMem : (execInstrBr a (.SW .x21 .x31 (BitVec.ofNat 12 (load+4*k)))).mem =
        (s.setWord32 (BitVec.ofNat 64 (T+load+4*k)) (s.getWord32 (BitVec.ofNat 64 (S+load+4*k)))).mem := by
      simp only [execInstrBr, MachineState.setPC, dstAddr a a21, a31]
      unfold MachineState.setWord32
      simp only [MachineState.setMem, MachineState.getMem, aMem]
    refine ⟨?_, ?_, ⟨?_, ?_, copy_congr_mem tMem copy, fun q other => (getMem_congr tMem q).trans (frame q other)⟩⟩
    · unfold memoryArgumentsValid
      simp only [memAccess]
      rw [srcAddr]
      exact access_ok _ _ sa (by omega)
    · unfold memoryArgumentsValid
      simp only [memAccess]
      rw [dstAddr a a21]
      exact access_ok _ _ ta (by omega)
    · simp only [execInstrBr, MachineState.setPC, a]
      exact eight
    · intro r h
      simp only [execInstrBr, MachineState.getReg_setPC, a, reg_setWord32]
      exact regs _ _ h _
  · -- dwords
    simp only [pairStep, wideLoad, wideStore, if_true]
    let a := execInstrBr s (.LD .x31 .x7 (BitVec.ofNat 12 (load+8*k)))
    have aMem : a.mem = s.mem := by simp only [a, execInstrBr, MachineState.setPC, mem_setReg']
    have a21 : a.getReg .x21 = s.getReg .x21 := by
      simp only [a, execInstrBr, MachineState.getReg_setPC]; exact regs _ _ (by decide) _
    have a31 : a.getReg .x31 = s.getMem (BitVec.ofNat 64 (S+load+8*k)) := by
      simp only [a, execInstrBr, MachineState.getReg_setPC, srcAddr,
        MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0)]
    obtain ⟨copy, frame⟩ := dword_store s (S+load+8*k) (T+load+8*k) sa ta (by omega) (by omega)
    have tMem : (execInstrBr a (.SD .x21 .x31 (BitVec.ofNat 12 (load+8*k)))).mem =
        (s.setMem (BitVec.ofNat 64 (T+load+8*k)) (s.getMem (BitVec.ofNat 64 (S+load+8*k)))).mem := by
      simp only [execInstrBr, MachineState.setPC, dstAddr a a21, a31]
      simp only [MachineState.setMem, aMem]
    have alignT : alignToDword (BitVec.ofNat 64 (T+load+8*k)) = BitVec.ofNat 64 (T+load+8*k) := by
      rw [align_eq _ (by omega), ta, Nat.sub_zero]
    refine ⟨?_, ?_, ⟨?_, ?_, copy_congr_mem tMem copy,
      fun q other => (getMem_congr tMem q).trans (frame q (by rwa [alignT] at other))⟩⟩
    · unfold memoryArgumentsValid
      simp only [memAccess]
      rw [srcAddr]
      exact access_ok _ _ sa (by omega)
    · unfold memoryArgumentsValid
      simp only [memAccess]
      rw [dstAddr a a21]
      exact access_ok _ _ ta (by omega)
    · simp only [execInstrBr, MachineState.setPC, a]
      exact eight
    · intro r h
      simp only [execInstrBr, MachineState.getReg_setPC, a, reg_setMem]
      exact regs _ _ h _

theorem load_pc (s : MachineState) (width : Nat) (imm : Nat) :
    (execInstrBr s (wideLoad width imm)).pc = s.pc + 4 := by
  unfold wideLoad; split <;> (try split) <;> rfl

theorem load_kind (width : Nat) (imm : Nat) : stepKind (wideLoad width imm) = true := by
  unfold wideLoad; split <;> (try split) <;> rfl

theorem store_kind (width : Nat) (imm : Nat) : stepKind (wideStore width imm) = true := by
  unfold wideStore; split <;> (try split) <;> rfl

theorem run_zero (s : MachineState) : RunsOpeningBlock s s 0 := by
  intro fuel coins
  simp [Execution.charge]

/-- Facts about a straight-line block that copies `size` bytes from `S` (`x7`) to `T` (`x21`). -/
structure BlockPost (s t : MachineState) (S T size : Nat) : Prop where
  regs : ∀ r, r ≠ .x31 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T size
  below : ∀ q : Word, q.toNat < T - T % 8 → t.getMem q = s.getMem q

theorem run_pairs (width : Nat) (hw : width = 2 ∨ width = 4 ∨ width = 8)
    (word load S T : Nat) (sa : (S+load) % width = 0) (ta : (T+load) % width = 0) :
    ∀ (n j : Nat) (s : MachineState), PairsAt word (j+n) width load → word+2*(j+n) ≤ 883 →
      s.pc = BitVec.ofNat 64 (4096+4*(word+2*j)) →
      s.getReg .x7 = BitVec.ofNat 64 S → s.getReg .x21 = BitVec.ofNat 64 T →
      load + width*(j+n) ≤ 2048 →
      S+load+width*(j+n) ≤ T → T+load+width*(j+n) ≤ MEMORY_BYTES →
      RunsOpeningBlock s (pairsRun width load j n s) (2*n) ∧
      (pairsRun width load j n s).pc = BitVec.ofNat 64 (4096+4*(word+2*(j+n))) ∧
      BlockPost s (pairsRun width load j n s) (S+load+width*j) (T+load+width*j) (width*n) := by
  have wpos : 2 ≤ width := by omega
  intro n
  induction n with
  | zero =>
    intro j s _ _ pc _ _ _ _ _
    refine ⟨run_zero s, by simpa [pairsRun] using pc, ⟨fun r _ => rfl, ⟨fun i h => absurd h (by omega), fun q _ => rfl⟩,
      fun q _ => rfl⟩⟩
  | succ n ih =>
    intro j s code fits pc sr dr immL apart room
    have e3 : width*(j+1) = width*j + width := by rw [Nat.mul_add, Nat.mul_one]
    have e4 : width*(n+1) = width + width*n := by rw [Nat.mul_add, Nat.mul_one]; omega
    have e1 : width*(j+(n+1)) = width*j + width*n + width := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
    have e2 : width*(j+1+n) = width*j + width*n + width := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
    have saj : (S+load+width*j) % width = 0 := by rw [Nat.add_mul_mod_self_left]; exact sa
    have taj : (T+load+width*j) % width = 0 := by rw [Nat.add_mul_mod_self_left]; exact ta
    obtain ⟨vl, vs, post⟩ := pair_post width hw load j S T s sr dr (by omega) saj taj (by omega) (by omega)
    let m := pairStep width load j s
    have codeJ := code j (by omega)
    have ranPair : RunsOpeningBlock s m 2 :=
      (run_step s (word+2*j) _ (by omega) pc codeJ.1 (load_kind _ _) vl).next
        (run_step _ (word+2*j+1) _ (by omega) (by
          rw [load_pc, pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]; congr 1)
          codeJ.2 (store_kind _ _) vs)
    have mpc : m.pc = BitVec.ofNat 64 (4096+4*(word+2*(j+1))) := by
      rw [post.pc, pc, ← BitVec.ofNat_add]; congr 1
    have rest := ih (j+1) m (by rw [show j+1+n = j+(n+1) by omega]; exact code) (by omega) mpc
      ((post.regs .x7 (by decide)).trans sr) ((post.regs .x21 (by decide)).trans dr) (by omega)
      (by omega) (by omega)
    obtain ⟨rRun, rPC, ⟨rRegs, rCopy, rFrame⟩⟩ := rest
    have total : pairsRun width load j (n+1) s = pairsRun width load (j+1) n m := rfl
    rw [total]
    refine ⟨?_, by rw [rPC]; congr 2; omega, ⟨fun r h => (rRegs r h).trans (post.regs r h), ?_, ?_⟩⟩
    · rw [show 2*(n+1) = 2+2*n by omega]; exact ranPair.next rRun
    · have tail : ByteCopy m (pairsRun width load (j+1) n m) (S+load+width*j+width) (T+load+width*j+width)
          (width*n) := by
        rw [show S+load+width*j+width = S+load+width*(j+1) by omega,
          show T+load+width*j+width = T+load+width*(j+1) by omega]
        exact rCopy
      rw [e4]
      exact copy_extend post.bytes tail (by omega) (by unfold MEMORY_BYTES at room; omega)
    · intro q below
      rw [rFrame q (by omega)]
      apply post.frame
      intro same
      have := align_nat (T+load+width*j) (by unfold MEMORY_BYTES at room; omega)
      rw [← same] at this
      omega

/-! ### Split chunks -/

def splitPrefix (k : Nat) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr (execInstrBr s (.LD .x31 .x7 (BitVec.ofNat 12 k)))
    (.SH .x21 .x31 (BitVec.ofNat 12 k))) (.SRLI .x31 .x31 16)) (.SW .x21 .x31 (BitVec.ofNat 12 (k+2)))

def splitStep (k : Nat) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (splitPrefix k s) (.SRLI .x31 .x31 32)) (.SH .x21 .x31 (BitVec.ofNat 12 (k+6)))

def splitsRun : Nat → Nat → MachineState → MachineState
  | _, 0, s => s
  | j, n+1, s => splitsRun (j+1) n (splitStep (8*j) s)

theorem setHalfword_mem_congr {a b : MachineState} (h : a.mem = b.mem) (x : Word) (u : BitVec 16) :
    (a.setHalfword x u).mem = (b.setHalfword x u).mem := by
  unfold MachineState.setHalfword; simp only [MachineState.setMem, MachineState.getMem, h]

private theorem ne_of_nat {a b : Nat} (fa : a < 2^64) (fb : b < 2^64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun same => h (QOpening.nat_address_injective fa fb same)

private theorem below_align (T q : Nat) (fit : T < 2^64) (below : q < T - T % 8) :
    BitVec.ofNat 64 q ≠ alignToDword (BitVec.ofNat 64 T) := by
  intro same
  have := align_nat T fit
  rw [← same, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
  omega

private theorem word_below {q : Word} {T : Nat} (fit : T < 2^64) (below : q.toNat < T - T % 8) :
    q ≠ alignToDword (BitVec.ofNat 64 T) := by
  intro same
  have := align_nat T fit
  rw [← same] at this
  omega

theorem split_chunk (word k S T : Nat) (full : Bool) (s : MachineState) (code : SplitAt word k full)
    (fits : word+6 ≤ 883) (pc : s.pc = BitVec.ofNat 64 (4096+4*word))
    (sr : s.getReg .x7 = BitVec.ofNat 64 S) (dr : s.getReg .x21 = BitVec.ofNat 64 T)
    (immK : k+6 < 2048) (sa : (S+k) % 8 = 0) (ta : (T+k) % 4 = 2)
    (sf : S+k+8 ≤ MEMORY_BYTES) (tfAny : T+k+(if full then 8 else 6) ≤ MEMORY_BYTES) :
    let t := if full then splitStep k s else splitPrefix k s
    RunsOpeningBlock s t (if full then 6 else 4) ∧
    t.pc = BitVec.ofNat 64 (4096+4*(word+(if full then 6 else 4))) ∧
    BlockPost s t (S+k) (T+k) (if full then 8 else 6) := by
  intro t
  have ram : MEMORY_BYTES < 2^64 := by decide
  have tf : T+k+6 ≤ MEMORY_BYTES := by cases full <;> simp at tfAny <;> omega
  let v := s.getMem (BitVec.ofNat 64 (S+k))
  have regs (u : MachineState) (r : Reg) (h : r ≠ .x31) (x : Word) : (u.setReg .x31 x).getReg r = u.getReg r :=
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  -- the six states
  let a := execInstrBr s (.LD .x31 .x7 (BitVec.ofNat 12 k))
  let b := execInstrBr a (.SH .x21 .x31 (BitVec.ofNat 12 k))
  let c := execInstrBr b (.SRLI .x31 .x31 16)
  let d := execInstrBr c (.SW .x21 .x31 (BitVec.ofNat 12 (k+2)))
  let e := execInstrBr d (.SRLI .x31 .x31 32)
  let f := execInstrBr e (.SH .x21 .x31 (BitVec.ofNat 12 (k+6)))
  have hd : splitPrefix k s = d := rfl
  have hf : splitStep k s = f := rfl
  have srcAddr : s.getReg .x7 + signExtend12 (BitVec.ofNat 12 k) = BitVec.ofNat 64 (S+k) := by
    rw [sr, sign12 _ (by omega), ← BitVec.ofNat_add]
  have dstAddr (u : MachineState) (same : u.getReg .x21 = s.getReg .x21) (o : Nat) (small : o < 2048) :
      u.getReg .x21 + signExtend12 (BitVec.ofNat 12 o) = BitVec.ofNat 64 (T+o) := by
    rw [same, dr, sign12 _ small, ← BitVec.ofNat_add]
  have aR (r : Reg) (h : r ≠ .x31) : a.getReg r = s.getReg r := by
    simp only [a, execInstrBr, MachineState.getReg_setPC]; exact regs _ _ h _
  have a31 : a.getReg .x31 = v := by
    simp only [a, execInstrBr, MachineState.getReg_setPC, srcAddr,
      MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0)]
    rfl
  have aMem : a.mem = s.mem := by simp only [a, execInstrBr, MachineState.setPC, mem_setReg']
  have bR (r : Reg) : b.getReg r = a.getReg r := by
    simp only [b, execInstrBr, MachineState.getReg_setPC, reg_setHalfword]
  have bMem : b.mem = (s.setHalfword (BitVec.ofNat 64 (T+k)) (v.truncate 16)).mem := by
    simp only [b, execInstrBr, MachineState.setPC, dstAddr a (aR .x21 (by decide)) k (by omega), a31]
    unfold MachineState.setHalfword
    simp only [MachineState.setMem, MachineState.getMem, aMem]
  have cR (r : Reg) (h : r ≠ .x31) : c.getReg r = s.getReg r := by
    simp only [c, execInstrBr, MachineState.getReg_setPC]; rw [regs _ _ h, bR, aR r h]
  have c31 : c.getReg .x31 = v >>> 16 := by
    simp only [c, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
      bR, a31]
    rfl
  have cMem : c.mem = b.mem := by simp only [c, execInstrBr, MachineState.setPC, mem_setReg']
  have dR (r : Reg) : d.getReg r = c.getReg r := by
    simp only [d, execInstrBr, MachineState.getReg_setPC, reg_setWord32]
  have dMem : d.mem = ((s.setHalfword (BitVec.ofNat 64 (T+k)) (v.truncate 16)).setWord32
      (BitVec.ofNat 64 (T+(k+2))) ((v >>> 16).truncate 32)).mem := by
    simp only [d, execInstrBr, MachineState.setPC, dstAddr c (cR .x21 (by decide)) (k+2) (by omega), c31]
    unfold MachineState.setWord32
    simp only [MachineState.setMem, MachineState.getMem, cMem, bMem]
  have eR (r : Reg) (h : r ≠ .x31) : e.getReg r = s.getReg r := by
    simp only [e, execInstrBr, MachineState.getReg_setPC]; rw [regs _ _ h, dR, cR r h]
  have e31 : e.getReg .x31 = (v >>> 16) >>> 32 := by
    simp only [e, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0),
      dR, c31]
    rfl
  have eMem : e.mem = d.mem := by simp only [e, execInstrBr, MachineState.setPC, mem_setReg']
  have fR (r : Reg) : f.getReg r = e.getReg r := by
    simp only [f, execInstrBr, MachineState.getReg_setPC, reg_setHalfword]
  have fMem : f.mem = (((s.setHalfword (BitVec.ofNat 64 (T+k)) (v.truncate 16)).setWord32
      (BitVec.ofNat 64 (T+(k+2))) ((v >>> 16).truncate 32)).setHalfword
      (BitVec.ofNat 64 (T+(k+6))) (((v >>> 16) >>> 32).truncate 16)).mem := by
    have step : f.mem = (d.setHalfword (BitVec.ofNat 64 (T+(k+6))) (((v >>> 16) >>> 32).truncate 16)).mem := by
      simp only [f, execInstrBr, MachineState.setPC, dstAddr e (eR .x21 (by decide)) (k+6) (by omega), e31]
      unfold MachineState.setHalfword
      simp only [MachineState.setMem, MachineState.getMem, eMem]
    exact step.trans (setHalfword_mem_congr dMem _ _)
  -- pure memory states
  let m1 := s.setHalfword (BitVec.ofNat 64 (T+k)) (v.truncate 16)
  let m2 := m1.setWord32 (BitVec.ofNat 64 (T+(k+2))) ((v >>> 16).truncate 32)
  let m3 := m2.setHalfword (BitVec.ofNat 64 (T+(k+6))) (((v >>> 16) >>> 32).truncate 16)
  have even0 : (T+k) % 2 = 0 := by omega
  have word2 : (T+(k+2)) % 4 = 0 := by omega
  have even6 : (T+(k+6)) % 2 = 0 := by omega
  have src (i : Nat) (hi : i < 8) : s.getByte (BitVec.ofNat 64 (S+k+i)) = extractByte v i :=
    byte_at s (S+k) i sa hi (by omega)
  have lowBytes (i : Nat) (hi : i < 2) : m1.getByte (BitVec.ofNat 64 (T+k+i)) = extractByte v i := by
    rw [put_half_hit s (T+k) i _ even0 hi (by omega), bits_low v i hi]
  have midBytes (i : Nat) (hi : 2 ≤ i) (hj : i < 6) : m2.getByte (BitVec.ofNat 64 (T+k+i)) = extractByte v i := by
    have := put_word_hit m1 (T+(k+2)) (i-2) ((v >>> 16).truncate 32) word2 (by omega) (by omega)
    rw [show T+(k+2)+(i-2) = T+k+i by omega] at this
    rw [this, bits_mid v (i-2) (by omega), show 2+(i-2) = i by omega]
  have m2low (i : Nat) (hi : i < 2) : m2.getByte (BitVec.ofNat 64 (T+k+i)) = m1.getByte (BitVec.ofNat 64 (T+k+i)) :=
    put_word_miss m1 (T+(k+2)) _ word2 (by omega) _ (fun j hj => ne_of_nat (by omega) (by omega) (by omega))
  have m3keep (i : Nat) (hi : i < 6) : m3.getByte (BitVec.ofNat 64 (T+k+i)) = m2.getByte (BitVec.ofNat 64 (T+k+i)) :=
    put_half_miss m2 (T+(k+6)) _ even6 (by omega) _ (fun j hj => ne_of_nat (by omega) (by omega) (by omega))
  have highBytes (i : Nat) (hi : 6 ≤ i) (hj : i < 8) : m3.getByte (BitVec.ofNat 64 (T+k+i)) = extractByte v i := by
    have := put_half_hit m2 (T+(k+6)) (i-6) (((v >>> 16) >>> 32).truncate 16) even6 (by omega) (by omega)
    rw [show T+(k+6)+(i-6) = T+k+i by omega] at this
    rw [this, bits_high v (i-6) (by omega), show 6+(i-6) = i by omega]
  have m1frame (q : Word) (out : ∀ i < 2, q ≠ BitVec.ofNat 64 (T+k+i)) : m1.getByte q = s.getByte q :=
    put_half_miss s (T+k) _ even0 (by omega) q out
  have m2frame (q : Word) (out : ∀ i < 4, q ≠ BitVec.ofNat 64 (T+(k+2)+i)) : m2.getByte q = m1.getByte q :=
    put_word_miss m1 (T+(k+2)) _ word2 (by omega) q out
  have m3frame (q : Word) (out : ∀ i < 2, q ≠ BitVec.ofNat 64 (T+(k+6)+i)) : m3.getByte q = m2.getByte q :=
    put_half_miss m2 (T+(k+6)) _ even6 (by omega) q out
  have memBelow (base : Nat) (q : Word) (hb : (T+k) ≤ base) (fb : base < 2^64)
      (below : q.toNat < (T+k) - (T+k) % 8) : q ≠ alignToDword (BitVec.ofNat 64 base) := by
    intro same
    have := align_nat base fb
    rw [← same] at this
    omega
  have m1mem (q : Word) (below : q.toNat < (T+k) - (T+k) % 8) : m1.getMem q = s.getMem q := by
    unfold m1 MachineState.setHalfword; dsimp only
    exact MachineState.getMem_setMem_ne (memBelow (T+k) q (by omega) (by omega) below)
  have m2mem (q : Word) (below : q.toNat < (T+k) - (T+k) % 8) : m2.getMem q = m1.getMem q := by
    unfold m2 MachineState.setWord32; dsimp only
    exact MachineState.getMem_setMem_ne (memBelow (T+(k+2)) q (by omega) (by omega) below)
  have m3mem (q : Word) (below : q.toNat < (T+k) - (T+k) % 8) : m3.getMem q = m2.getMem q := by
    unfold m3 MachineState.setHalfword; dsimp only
    exact MachineState.getMem_setMem_ne (memBelow (T+(k+6)) q (by omega) (by omega) below)
  -- validity and steps
  have code' := code
  obtain ⟨cLD, cSH, cSR, cSW, cRest⟩ := code'
  have vLD : memoryArgumentsValid s (.LD .x31 .x7 (BitVec.ofNat 12 k)) = true := by
    unfold memoryArgumentsValid; simp only [memAccess]; rw [srcAddr]; exact access_ok _ _ sa (by omega)
  have vSH : memoryArgumentsValid a (.SH .x21 .x31 (BitVec.ofNat 12 k)) = true := by
    unfold memoryArgumentsValid; simp only [memAccess]
    rw [dstAddr a (aR .x21 (by decide)) k (by omega)]; exact access_ok _ _ even0 (by omega)
  have vSW : memoryArgumentsValid c (.SW .x21 .x31 (BitVec.ofNat 12 (k+2))) = true := by
    unfold memoryArgumentsValid; simp only [memAccess]
    rw [dstAddr c (cR .x21 (by decide)) (k+2) (by omega)]; exact access_ok _ _ word2 (by omega)
  have vSH6 (tf8 : T+k+8 ≤ MEMORY_BYTES) : memoryArgumentsValid e (.SH .x21 .x31 (BitVec.ofNat 12 (k+6))) = true := by
    unfold memoryArgumentsValid; simp only [memAccess]
    rw [dstAddr e (eR .x21 (by decide)) (k+6) (by omega)]; exact access_ok _ _ even6 (by omega)
  have pcStep (u : MachineState) (n : Nat) (h : u.pc = BitVec.ofNat 64 (4096+4*(word+n))) :
      u.pc + 4 = BitVec.ofNat 64 (4096+4*(word+(n+1))) := by
    rw [h, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]; congr 1
  have pa : a.pc = BitVec.ofNat 64 (4096+4*(word+1)) := pcStep s 0 (by simpa using pc)
  have pb : b.pc = BitVec.ofNat 64 (4096+4*(word+2)) := pcStep a 1 pa
  have pcc : c.pc = BitVec.ofNat 64 (4096+4*(word+3)) := pcStep b 2 pb
  have pd : d.pc = BitVec.ofNat 64 (4096+4*(word+4)) := pcStep c 3 pcc
  have r1 := run_step s word _ (by omega) pc cLD rfl vLD
  have r2 := run_step a (word+1) _ (by omega) pa cSH rfl vSH
  have r3 := run_step b (word+2) _ (by omega) pb cSR rfl rfl
  have r4 := run_step c (word+3) _ (by omega) pcc cSW rfl vSW
  have prefixRun : RunsOpeningBlock s d 4 := ((r1.next r2).next r3).next r4
  have prefixPost : BlockPost s d (S+k) (T+k) 6 := by
    refine ⟨fun r h => by rw [dR, cR r h], ⟨fun i hi => ?_, fun q out => ?_⟩, fun q below => ?_⟩
    · rw [show d.getByte (BitVec.ofNat 64 (T+k+i)) = m2.getByte (BitVec.ofNat 64 (T+k+i)) by
        simp only [MachineState.getByte, MachineState.getMem, dMem]; rfl, src i (by omega)]
      by_cases low : i < 2
      · rw [m2low i low, lowBytes i low]
      · exact midBytes i (by omega) hi
    · rw [show d.getByte q = m2.getByte q by simp only [MachineState.getByte, MachineState.getMem, dMem]; rfl,
        m2frame q (fun i hi => by have := out (2+i) (by omega); rwa [show T+k+(2+i) = T+(k+2)+i by omega] at this),
        m1frame q (fun i hi => out i (by omega))]
    · rw [show d.getMem q = m2.getMem q by simp only [MachineState.getMem, dMem]; rfl, m2mem q below, m1mem q below]
  cases full with
  | false =>
    simp only [t, if_false, Bool.false_eq_true, hd]
    exact ⟨prefixRun, pd, prefixPost⟩
  | true =>
    simp only [t, if_true, hf]
    obtain ⟨cSR2, cSH2⟩ := cRest rfl
    have pe : e.pc = BitVec.ofNat 64 (4096+4*(word+5)) := pcStep d 4 pd
    have pf : f.pc = BitVec.ofNat 64 (4096+4*(word+6)) := pcStep e 5 pe
    have r5 := run_step d (word+4) _ (by omega) pd cSR2 rfl rfl
    have r6 := run_step e (word+5) _ (by omega) pe cSH2 rfl (vSH6 (by simpa using tfAny))
    refine ⟨(prefixRun.next r5).next r6, pf, ⟨fun r h => by rw [fR, eR r h], ⟨fun i hi => ?_, fun q out => ?_⟩,
      fun q below => ?_⟩⟩
    · rw [show f.getByte (BitVec.ofNat 64 (T+k+i)) = m3.getByte (BitVec.ofNat 64 (T+k+i)) by
        simp only [MachineState.getByte, MachineState.getMem, fMem]; rfl, src i hi]
      by_cases high : 6 ≤ i
      · exact highBytes i high hi
      · rw [m3keep i (by omega)]
        by_cases low : i < 2
        · rw [m2low i low, lowBytes i low]
        · exact midBytes i (by omega) (by omega)
    · rw [show f.getByte q = m3.getByte q by simp only [MachineState.getByte, MachineState.getMem, fMem]; rfl,
        m3frame q (fun i hi => by have := out (6+i) (by omega); rwa [show T+k+(6+i) = T+(k+6)+i by omega] at this),
        m2frame q (fun i hi => by have := out (2+i) (by omega); rwa [show T+k+(2+i) = T+(k+2)+i by omega] at this),
        m1frame q (fun i hi => out i (by omega))]
    · rw [show f.getMem q = m3.getMem q by simp only [MachineState.getMem, fMem]; rfl, m3mem q below, m2mem q below,
        m1mem q below]

theorem run_splits (word S T : Nat) (sa : S % 8 = 0) (ta : T % 4 = 2) :
    ∀ (n j : Nat) (s : MachineState), SplitsAt word (j+n) → word+6*(j+n) ≤ 883 →
      s.pc = BitVec.ofNat 64 (4096+4*(word+6*j)) →
      s.getReg .x7 = BitVec.ofNat 64 S → s.getReg .x21 = BitVec.ofNat 64 T →
      8*(j+n) ≤ 2040 → S+8*(j+n) ≤ T → T+8*(j+n) ≤ MEMORY_BYTES →
      RunsOpeningBlock s (splitsRun j n s) (6*n) ∧
      (splitsRun j n s).pc = BitVec.ofNat 64 (4096+4*(word+6*(j+n))) ∧
      BlockPost s (splitsRun j n s) (S+8*j) (T+8*j) (8*n) := by
  intro n
  induction n with
  | zero =>
    intro j s _ _ pc _ _ _ _ _
    refine ⟨run_zero s, by simpa [splitsRun] using pc, ⟨fun r _ => rfl, ⟨fun i h => absurd h (by omega), fun q _ => rfl⟩,
      fun q _ => rfl⟩⟩
  | succ n ih =>
    intro j s code fits pc sr dr imm apart room
    obtain ⟨cRun, cPC, cPost⟩ := split_chunk (word+6*j) (8*j) S T true s (code j (by omega)) (by omega) pc sr dr
      (by omega) (by omega) (by omega) (by omega) (by rw [if_pos rfl]; omega)
    simp only [if_true] at cRun cPC cPost
    let m := splitStep (8*j) s
    have mpc : m.pc = BitVec.ofNat 64 (4096+4*(word+6*(j+1))) := by rw [cPC]; congr 2 <;> omega
    have rest := ih (j+1) m (by rw [show j+1+n = j+(n+1) by omega]; exact code) (by omega) mpc
      ((cPost.regs .x7 (by decide)).trans sr) ((cPost.regs .x21 (by decide)).trans dr) (by omega) (by omega) (by omega)
    obtain ⟨rRun, rPC, ⟨rRegs, rCopy, rFrame⟩⟩ := rest
    have total : splitsRun j (n+1) s = splitsRun (j+1) n m := rfl
    rw [total]
    refine ⟨?_, by rw [rPC]; congr 2; omega, ⟨fun r h => (rRegs r h).trans (cPost.regs r h), ?_, ?_⟩⟩
    · rw [show 6*(n+1) = 6+6*n by omega]; exact cRun.next rRun
    · have tail : ByteCopy m (splitsRun (j+1) n m) (S+8*j+8) (T+8*j+8) (8*n) := by
        rw [show S+8*j+8 = S+8*(j+1) by omega, show T+8*j+8 = T+8*(j+1) by omega]
        exact rCopy
      rw [show 8*(n+1) = 8+8*n by omega]
      exact copy_extend cPost.bytes tail (by omega) (by unfold MEMORY_BYTES at room; omega)
    · intro q below
      rw [rFrame q (by omega)]
      exact cPost.below q (by omega)

/-! ### The stub paths -/

structure Moves (u v : MachineState) (changed : Reg) : Prop where
  regs : ∀ r, r ≠ changed → v.getReg r = u.getReg r
  mem : v.mem = u.mem

theorem x0_any (u v : MachineState) : v.getReg .x0 = u.getReg .x0 := rfl

theorem keep_x0 {u v : MachineState} (m : Moves u v .x0) (r : Reg) : v.getReg r = u.getReg r := by
  by_cases z : r = .x0
  · subst z; exact x0_any _ _
  · exact m.regs r z

theorem jal_facts (u : MachineState) (off : BitVec 21) :
    let v := execInstrBr u (.JAL .x10 off)
    v.pc = u.pc + signExtend21 off ∧ v.getReg .x10 = u.pc + 4 ∧ Moves u v .x10 := by
  refine ⟨rfl, by simp only [execInstrBr, MachineState.getReg_setPC]; exact MachineState.getReg_setReg_eq (by decide),
    fun r h => ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  · simp only [execInstrBr, MachineState.setPC, mem_setReg']

theorem andi_facts (u : MachineState) :
    let v := execInstrBr u (.ANDI .x31 .x21 7)
    v.pc = u.pc + 4 ∧ v.getReg .x31 = u.getReg .x21 &&& signExtend12 7 ∧ Moves u v .x31 := by
  refine ⟨rfl, by simp only [execInstrBr, MachineState.getReg_setPC]; exact MachineState.getReg_setReg_eq (by decide),
    fun r h => ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  · simp only [execInstrBr, MachineState.setPC, mem_setReg']

theorem addi_facts (u : MachineState) :
    let v := execInstrBr u (.ADDI .x31 .x31 4092)
    v.pc = u.pc + 4 ∧ v.getReg .x31 = u.getReg .x31 + signExtend12 4092 ∧ Moves u v .x31 := by
  refine ⟨rfl, by simp only [execInstrBr, MachineState.getReg_setPC]; exact MachineState.getReg_setReg_eq (by decide),
    fun r h => ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  · simp only [execInstrBr, MachineState.setPC, mem_setReg']

theorem beq_facts (u : MachineState) (off : BitVec 13) :
    let v := execInstrBr u (.BEQ .x31 .x0 off)
    v.pc = (if u.getReg .x31 = 0#64 then u.pc + signExtend13 off else u.pc + 4) ∧ Moves u v .x0 := by
  refine ⟨?_, fun r _ => ?_, ?_⟩
  · simp only [execInstrBr, show (u.getReg .x0) = 0#64 from rfl]
    by_cases h : u.getReg .x31 = 0#64 <;> simp [h, MachineState.setPC]
  · simp only [execInstrBr]; split <;> rfl
  · simp only [execInstrBr]; split <;> rfl

theorem jalr_facts (u : MachineState) (off : BitVec 12) :
    let v := execInstrBr u (.JALR .x0 .x10 off)
    v.pc = (u.getReg .x10 + signExtend12 off) &&& ~~~1#64 ∧ Moves u v .x0 := by
  refine ⟨rfl, fun r h => ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  · simp only [execInstrBr, MachineState.setPC, mem_setReg']

theorem ofNat_step (a b : Nat) : BitVec.ofNat 64 (4096+4*a) + BitVec.ofNat 64 (4*b) = BitVec.ofNat 64 (4096+4*(a+b)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

theorem ofNat_four (a : Nat) : BitVec.ofNat 64 (4096+4*a) + 4 = BitVec.ofNat 64 (4096+4*(a+1)) := by
  rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]; congr 1

private theorem low_bits (x : Word) (T : Nat) (fit : T < 2^64) (sum : x = BitVec.ofNat 64 T) :
    x &&& signExtend12 7 = BitVec.ofNat 64 (T % 8) := by
  subst sum
  apply BitVec.eq_of_toNat_eq
  rw [show signExtend12 7 = (7#64 : Word) from rfl, BitVec.toNat_and,
    show (7#64 : Word).toNat = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt fit]
  omega

/-- Distance (in words) from a stub's first word to its doubleword path. -/
def CopySite.dword (site : CopySite) : Nat := if site.size = 32 then 29 else 27

def enterState (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr s (entryJump site)) (.ANDI .x31 .x21 7))
    (.BEQ .x31 .x0 (BitVec.ofNat 13 (4*(site.dword-1))))

def slowState (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (enterState site s) (.ADDI .x31 .x31 4092)) (.BEQ .x31 .x0 140)

structure WideInputs (site : CopySite) (s : MachineState) (S T : Nat) : Prop where
  wide : site.wide = true
  pc : s.pc = BitVec.ofNat 64 (4096+4*site.start)
  src : s.getReg .x7 = BitVec.ofNat 64 S
  dst : s.getReg .x21 = BitVec.ofNat 64 T
  srcAligned : S % 8 = 0
  dstEven : T % 2 = 0
  apart : S+site.size ≤ T
  room : T+site.size ≤ MEMORY_BYTES

structure Entered (site : CopySite) (s e : MachineState) (S T : Nat) : Prop where
  x10 : e.getReg .x10 = BitVec.ofNat 64 (4096+4*(site.start+1))
  src : e.getReg .x7 = BitVec.ofNat 64 S
  dst : e.getReg .x21 = BitVec.ofNat 64 T
  mem : e.mem = s.mem
  regs : ∀ r, r ≠ .x31 → r ≠ .x10 → e.getReg r = s.getReg r

theorem stub_dispatch (site : CopySite) (wide : site.wide = true) : Dispatch site.stub site.dword := by
  have facts := site_facts site wide
  unfold CopySite.stub CopySite.dword
  rcases facts.size with h | h <;> simp only [h, if_true, show (30 = 32) = False by decide, if_false]
  · exact stub32_code.dispatch
  · exact stub30_code.dispatch

theorem enter_facts (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T) :
    RunsOpeningBlock s (enterState site s) 3 ∧ Entered site s (enterState site s) S T ∧
    (enterState site s).getReg .x31 = BitVec.ofNat 64 (T % 8) ∧
    (enterState site s).pc = (if T % 8 = 0 then BitVec.ofNat 64 (4096+4*(site.stub+site.dword))
      else BitVec.ofNat 64 (4096+4*(site.stub+2))) := by
  have facts := site_facts site input.wide
  have code := stub_dispatch site input.wide
  have sf := facts.startFit
  have stubSmall : site.stub+55 ≤ 883 := by unfold CopySite.stub; split <;> decide
  have dw : site.dword = 29 ∨ site.dword = 27 := by unfold CopySite.dword; split <;> simp
  have andBits := low_bits (s.getReg .x21) T (by have := input.room; unfold MEMORY_BYTES at this; omega) input.dst
  have run1 := run_step s site.start _ (by omega) input.pc facts.entry rfl rfl
  obtain ⟨p1, x10a, m1⟩ := jal_facts s (BitVec.ofNat 21 (4*(site.stub-site.start)))
  generalize he1 : execInstrBr s (.JAL .x10 (BitVec.ofNat 21 (4*(site.stub-site.start)))) = e1 at p1 x10a m1
  have run1' : RunsOpeningBlock s e1 1 := by rw [← he1]; exact run1
  have pc1 : e1.pc = BitVec.ofNat 64 (4096+4*site.stub) := by rw [p1, input.pc]; exact facts.jump
  have run2 := run_step e1 site.stub _ (by omega) pc1 code.test rfl rfl
  obtain ⟨p2, x31b, m2⟩ := andi_facts e1
  generalize he2 : execInstrBr e1 (.ANDI .x31 .x21 7) = e2 at p2 x31b m2 run2
  have pc2 : e2.pc = BitVec.ofNat 64 (4096+4*(site.stub+1)) := by rw [p2, pc1, ofNat_four]
  have v31 : e2.getReg .x31 = BitVec.ofNat 64 (T % 8) := by rw [x31b, m1.regs .x21 (by decide), andBits]
  have run3 := run_step e2 (site.stub+1) _ (by omega) pc2 code.eight rfl rfl
  obtain ⟨p3, m3⟩ := beq_facts e2 (BitVec.ofNat 13 (4*(site.dword-1)))
  generalize he3 : execInstrBr e2 (.BEQ .x31 .x0 (BitVec.ofNat 13 (4*(site.dword-1)))) = e3 at p3 m3 run3
  have same : enterState site s = e3 := by rw [← he3, ← he2, ← he1]; unfold enterState entryJump; exact Eq.refl _
  rw [same]
  have keep (r : Reg) (a : r ≠ .x31) (b : r ≠ .x10) : e3.getReg r = s.getReg r := by
    by_cases z : r = .x0
    · subst z; exact x0_any _ _
    · rw [m3.regs r z, m2.regs r a, m1.regs r b]
  have total := (run1'.next run2).next run3
  rw [show 1+1+1 = 3 from rfl] at total
  refine ⟨total, ⟨?_, ?_, ?_, ?_, keep⟩, by rw [m3.regs .x31 (by decide), v31], ?_⟩
  · rw [m3.regs .x10 (by decide), m2.regs .x10 (by decide), x10a, input.pc, ofNat_four]
  · rw [keep _ (by decide) (by decide), input.src]
  · rw [keep .x21 (by decide) (by decide)]; exact input.dst
  · rw [m3.mem, m2.mem, m1.mem]
  · rw [p3, v31, pc2]
    have cls : T % 8 = 0 ∨ T % 8 = 2 ∨ T % 8 = 4 ∨ T % 8 = 6 := by have := input.dstEven; omega
    rcases cls with h | h | h | h <;> rw [h]
    · rw [if_pos rfl, if_pos rfl]
      rcases dw with d | d <;> rw [d]
      · rw [show site.stub+29 = site.stub+1+28 by omega,
          show signExtend13 (BitVec.ofNat 13 (4*(29-1))) = BitVec.ofNat 64 (4*28) from rfl, ofNat_step]
      · rw [show site.stub+27 = site.stub+1+26 by omega,
          show signExtend13 (BitVec.ofNat 13 (4*(27-1))) = BitVec.ofNat 64 (4*26) from rfl, ofNat_step]
    all_goals rw [if_neg (by decide), if_neg (by decide), ofNat_four]

theorem slow_facts (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (slow : T % 8 ≠ 0) :
    RunsOpeningBlock s (slowState site s) 5 ∧ Entered site s (slowState site s) S T ∧
    (slowState site s).pc = (if T % 8 = 4 then BitVec.ofNat 64 (4096+4*(site.stub+38))
      else BitVec.ofNat 64 (4096+4*(site.stub+4))) := by
  have code := stub_dispatch site input.wide
  have stubSmall : site.stub+55 ≤ 883 := by unfold CopySite.stub; split <;> decide
  obtain ⟨run3, entered, x31e, pc3⟩ := enter_facts site s S T input
  rw [if_neg slow] at pc3
  generalize he3 : enterState site s = e3 at run3 entered pc3 x31e
  have run4 := run_step e3 (site.stub+2) _ (by omega) pc3 code.less rfl rfl
  obtain ⟨p4, x31c, m4⟩ := addi_facts e3
  generalize he4 : execInstrBr e3 (.ADDI .x31 .x31 4092) = e4 at p4 x31c m4 run4
  have pc4 : e4.pc = BitVec.ofNat 64 (4096+4*(site.stub+3)) := by rw [p4, pc3, ofNat_four]
  have run5 := run_step e4 (site.stub+3) _ (by omega) pc4 code.four rfl rfl
  obtain ⟨p5, m5⟩ := beq_facts e4 140
  generalize he5 : execInstrBr e4 (.BEQ .x31 .x0 140) = e5 at p5 m5 run5
  have same : slowState site s = e5 := by rw [← he5, ← he4, ← he3]; unfold slowState; exact Eq.refl _
  rw [same]
  have keep (r : Reg) (a : r ≠ .x31) : e5.getReg r = e3.getReg r := by
    by_cases z : r = .x0
    · subst z; exact x0_any _ _
    · rw [m5.regs r z, m4.regs r a]
  have total := (run3.next run4).next run5
  rw [show 3+1+1 = 5 from rfl] at total
  refine ⟨total, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [keep .x10 (by decide)]; exact entered.x10
  · rw [keep _ (by decide)]; exact entered.src
  · rw [keep .x21 (by decide)]; exact entered.dst
  · rw [m5.mem, m4.mem]; exact entered.mem
  · intro r a b; rw [keep r a]; exact entered.regs r a b
  · rw [p5, x31c, x31e, pc4]
    have cls : T % 8 = 2 ∨ T % 8 = 4 ∨ T % 8 = 6 := by have := input.dstEven; omega
    rcases cls with h | h | h <;> rw [h]
    · rw [if_neg (by decide), if_neg (by decide), ofNat_four]
    · rw [if_pos (by decide), if_pos rfl, show site.stub+38 = site.stub+3+35 by omega,
        show signExtend13 140 = BitVec.ofNat 64 (4*35) from rfl, ofNat_step]
    · rw [if_neg (by decide), if_neg (by decide), ofNat_four]

/-! ### The six paths -/

def dword32 (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (pairsRun 8 0 0 4 (enterState site s)) (.JALR .x0 .x10 124)

def word32 (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (pairsRun 4 0 0 8 (slowState site s)) (.JALR .x0 .x10 124)

def split32 (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (splitsRun 0 4 (slowState site s)) (.JALR .x0 .x10 124)

def dword30 (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (pairsRun 2 28 0 1 (pairsRun 4 24 0 1 (pairsRun 8 0 0 3 (enterState site s)))) (.JALR .x0 .x10 116)

def word30 (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (pairsRun 2 28 0 1 (pairsRun 4 0 0 7 (slowState site s))) (.JALR .x0 .x10 116)

def split30 (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (splitPrefix 24 (splitsRun 0 3 (slowState site s))) (.JALR .x0 .x10 116)

/-- The state after a wide site's copy: the path picked by the stub for the destination `x21`. -/
def wideState (site : CopySite) (s : MachineState) : MachineState :=
  let t := (s.getReg .x21).toNat % 8
  if site.size = 32 then
    if t = 0 then dword32 site s else if t = 4 then word32 site s else split32 site s
  else
    if t = 0 then dword30 site s else if t = 4 then word30 site s else split30 site s

/-- Cycles of a wide site's copy into `target`, including the `jal` and the dispatch. -/
def wideCost (site : CopySite) (target : Nat) : Nat :=
  if site.size = 32 then
    (if target % 8 = 0 then 12 else if target % 8 = 4 then 22 else 30)
  else
    (if target % 8 = 0 then 14 else if target % 8 = 4 then 22 else 28)

structure WideDone (site : CopySite) (s t : MachineState) (S T cost : Nat) : Prop where
  run : RunsOpeningBlock s t cost
  pc : t.pc = BitVec.ofNat 64 (4096+4*(site.start+site.size))
  regs : ∀ r, r ≠ .x31 → r ≠ .x10 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T site.size
  below : ∀ q : Word, q.toNat < T - T % 8 → t.getMem q = s.getMem q

private theorem stub_of (site : CopySite) (h : site.size = 32) : site.stub = 773 ∧ site.dword = 29 := by
  unfold CopySite.stub CopySite.dword; simp [h]

private theorem stub_of30 (site : CopySite) (h : site.size = 30) : site.stub = 828 ∧ site.dword = 27 := by
  unfold CopySite.stub CopySite.dword; simp [h]

private theorem finish (site : CopySite) (wide : site.wide = true) (s e c f : MachineState) (S T cost : Nat) (sz : Nat)
    (hsz : site.size = sz) (back : BitVec 12) (hback : back = BitVec.ofNat 12 (4*(sz-1)))
    (entered : Entered site s e S T) (run : RunsOpeningBlock s f cost)
    (post : BlockPost e c S T sz) (hf : f = execInstrBr c (.JALR .x0 .x10 back)) :
    WideDone site s f S T cost := by
  have facts := site_facts site wide
  obtain ⟨pJ, mJ⟩ := jalr_facts c back
  rw [← hf] at pJ mJ
  refine ⟨run, ?_, ?_, ?_, ?_⟩
  · rw [pJ, post.regs .x10 (by decide), entered.x10, hback]
    have := facts.back
    rw [hsz] at this ⊢
    exact this
  · intro r a b; rw [keep_x0 mJ r, post.regs r a, entered.regs r a b]
  · rw [hsz]; exact copy_congr_mem mJ.mem (copy_congr_before entered.mem.symm post.bytes)
  · intro q below; rw [getMem_congr mJ.mem, post.below q below, getMem_congr entered.mem]

private theorem post_join {s m t : MachineState} {S T a b : Nat}
    (first : BlockPost s m S T a) (second : BlockPost m t (S+a) (T+a) b)
    (apart : S+a+b ≤ T) (fit : T+a+b ≤ 2^64) : BlockPost s t S T (a+b) :=
  ⟨fun r h => (second.regs r h).trans (first.regs r h), copy_extend first.bytes second.bytes apart fit,
    fun q below => (second.below q (by omega)).trans (first.below q below)⟩

theorem dword32_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (sz : site.size = 32) (h : T % 8 = 0) : WideDone site s (dword32 site s) S T 12 := by
  have code := stub32_code
  have apart := input.apart
  have room := input.room
  rw [sz] at apart room
  obtain ⟨stubEq, dwEq⟩ := stub_of site sz
  obtain ⟨run3, entered, _, pc3⟩ := enter_facts site s S T input
  rw [if_pos h, stubEq, dwEq] at pc3
  generalize he3 : enterState site s = e3 at run3 entered pc3
  obtain ⟨runP, pcP, postP⟩ := run_pairs 8 (by decide) 802 0 S T (by simpa using input.srcAligned)
    (by simpa using h) 4 0 e3 (by simpa using code.dwords) (by norm_num) (by simpa using pc3) entered.src entered.dst
    (by norm_num) (by omega) (by omega)
  generalize hc : pairsRun 8 0 0 4 e3 = c at runP pcP postP
  have runJ := run_step c 810 _ (by norm_num) (by simpa using pcP) code.dwordsBack rfl rfl
  have same : dword32 site s = execInstrBr c (.JALR .x0 .x10 124) := by rw [← hc, ← he3]; rfl
  rw [same]
  exact finish site input.wide s e3 c _ S T 12 32 sz 124 rfl entered (by simpa using (run3.next runP).next runJ)
    (by simpa using postP) rfl

theorem word32_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (sz : site.size = 32) (h : T % 8 = 4) : WideDone site s (word32 site s) S T 22 := by
  have code := stub32_code
  have apart := input.apart
  have room := input.room
  rw [sz] at apart room
  obtain ⟨stubEq, _⟩ := stub_of site sz
  obtain ⟨run5, entered, pc5⟩ := slow_facts site s S T input (by omega)
  rw [if_pos h, stubEq] at pc5
  generalize he5 : slowState site s = e5 at run5 entered pc5
  obtain ⟨runP, pcP, postP⟩ := run_pairs 4 (by decide) 811 0 S T (by have := input.srcAligned; omega)
    (by omega) 8 0 e5 (by simpa using code.words) (by norm_num) (by simpa using pc5) entered.src entered.dst
    (by norm_num) (by omega) (by omega)
  generalize hc : pairsRun 4 0 0 8 e5 = c at runP pcP postP
  have runJ := run_step c 827 _ (by norm_num) (by simpa using pcP) code.wordsBack rfl rfl
  have same : word32 site s = execInstrBr c (.JALR .x0 .x10 124) := by rw [← hc, ← he5]; rfl
  rw [same]
  exact finish site input.wide s e5 c _ S T 22 32 sz 124 rfl entered (by simpa using (run5.next runP).next runJ)
    (by simpa using postP) rfl

theorem split32_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (sz : site.size = 32) (h0 : T % 8 ≠ 0) (h4 : T % 8 ≠ 4) : WideDone site s (split32 site s) S T 30 := by
  have code := stub32_code
  have apart := input.apart
  have room := input.room
  have even := input.dstEven
  rw [sz] at apart room
  obtain ⟨stubEq, _⟩ := stub_of site sz
  obtain ⟨run5, entered, pc5⟩ := slow_facts site s S T input h0
  rw [if_neg h4, stubEq] at pc5
  generalize he5 : slowState site s = e5 at run5 entered pc5
  obtain ⟨runP, pcP, postP⟩ := run_splits 777 S T input.srcAligned (by omega) 4 0 e5 (by simpa using code.splits)
    (by norm_num) (by simpa using pc5) entered.src entered.dst (by norm_num) (by omega) (by omega)
  generalize hc : splitsRun 0 4 e5 = c at runP pcP postP
  have runJ := run_step c 801 _ (by norm_num) (by simpa using pcP) code.splitBack rfl rfl
  have same : split32 site s = execInstrBr c (.JALR .x0 .x10 124) := by rw [← hc, ← he5]; rfl
  rw [same]
  exact finish site input.wide s e5 c _ S T 30 32 sz 124 rfl entered (by simpa using (run5.next runP).next runJ)
    (by simpa using postP) rfl

theorem dword30_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (sz : site.size = 30) (h : T % 8 = 0) : WideDone site s (dword30 site s) S T 14 := by
  have code := stub30_code
  have apart := input.apart
  have room := input.room
  have sa := input.srcAligned
  rw [sz] at apart room
  obtain ⟨stubEq, dwEq⟩ := stub_of30 site sz
  obtain ⟨run3, entered, _, pc3⟩ := enter_facts site s S T input
  rw [if_pos h, stubEq, dwEq] at pc3
  generalize he3 : enterState site s = e3 at run3 entered pc3
  obtain ⟨runA, pcA, postA⟩ := run_pairs 8 (by decide) 855 0 S T (by simpa using sa)
    (by simpa using h) 3 0 e3 (by simpa using code.dwords) (by norm_num) (by simpa using pc3) entered.src entered.dst
    (by norm_num) (by omega) (by omega)
  generalize hA : pairsRun 8 0 0 3 e3 = a at runA pcA postA
  obtain ⟨runB, pcB, postB⟩ := run_pairs 4 (by decide) 861 24 S T (by omega) (by omega) 1 0 a
    (by simpa using code.dwordWord) (by norm_num) (by simpa using pcA) ((postA.regs .x7 (by decide)).trans entered.src)
    ((postA.regs .x21 (by decide)).trans entered.dst) (by norm_num) (by omega) (by omega)
  generalize hB : pairsRun 4 24 0 1 a = b at runB pcB postB
  obtain ⟨runC, pcC, postC⟩ := run_pairs 2 (by decide) 863 28 S T (by omega) (by omega) 1 0 b
    (by simpa using code.dwordHalf) (by norm_num) (by simpa using pcB)
    ((postB.regs .x7 (by decide)).trans ((postA.regs .x7 (by decide)).trans entered.src))
    ((postB.regs .x21 (by decide)).trans ((postA.regs .x21 (by decide)).trans entered.dst)) (by norm_num) (by omega)
    (by omega)
  generalize hC : pairsRun 2 28 0 1 b = c at runC pcC postC
  have runJ := run_step c 865 _ (by norm_num) (by simpa using pcC) code.dwordsBack rfl rfl
  have same : dword30 site s = execInstrBr c (.JALR .x0 .x10 116) := by rw [← hC, ← hB, ← hA, ← he3]; rfl
  rw [same]
  have ab : BlockPost e3 b S T (24+4) :=
    post_join (by simpa using postA) (by simpa using postB) (by omega) (by unfold MEMORY_BYTES at room; omega)
  have abc : BlockPost e3 c S T (24+4+2) :=
    post_join ab (by simpa using postC) (by omega) (by unfold MEMORY_BYTES at room; omega)
  exact finish site input.wide s e3 c _ S T 14 30 sz 116 rfl entered
    (by simpa using (((run3.next runA).next runB).next runC).next runJ) (by simpa using abc) rfl

theorem word30_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (sz : site.size = 30) (h : T % 8 = 4) : WideDone site s (word30 site s) S T 22 := by
  have code := stub30_code
  have apart := input.apart
  have room := input.room
  have sa := input.srcAligned
  rw [sz] at apart room
  obtain ⟨stubEq, _⟩ := stub_of30 site sz
  obtain ⟨run5, entered, pc5⟩ := slow_facts site s S T input (by omega)
  rw [if_pos h, stubEq] at pc5
  generalize he5 : slowState site s = e5 at run5 entered pc5
  obtain ⟨runA, pcA, postA⟩ := run_pairs 4 (by decide) 866 0 S T (by omega) (by omega) 7 0 e5
    (by simpa using code.words) (by norm_num) (by simpa using pc5) entered.src entered.dst (by norm_num) (by omega)
    (by omega)
  generalize hA : pairsRun 4 0 0 7 e5 = a at runA pcA postA
  obtain ⟨runB, pcB, postB⟩ := run_pairs 2 (by decide) 880 28 S T (by omega) (by omega) 1 0 a
    (by simpa using code.wordHalf) (by norm_num) (by simpa using pcA) ((postA.regs .x7 (by decide)).trans entered.src)
    ((postA.regs .x21 (by decide)).trans entered.dst) (by norm_num) (by omega) (by omega)
  generalize hB : pairsRun 2 28 0 1 a = c at runB pcB postB
  have runJ := run_step c 882 _ (by norm_num) (by simpa using pcB) code.wordsBack rfl rfl
  have same : word30 site s = execInstrBr c (.JALR .x0 .x10 116) := by rw [← hB, ← hA, ← he5]; rfl
  rw [same]
  have ab : BlockPost e5 c S T (28+2) :=
    post_join (by simpa using postA) (by simpa using postB) (by omega) (by unfold MEMORY_BYTES at room; omega)
  exact finish site input.wide s e5 c _ S T 22 30 sz 116 rfl entered
    (by simpa using ((run5.next runA).next runB).next runJ) (by simpa using ab) rfl

theorem split30_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (sz : site.size = 30) (h0 : T % 8 ≠ 0) (h4 : T % 8 ≠ 4) : WideDone site s (split30 site s) S T 28 := by
  have code := stub30_code
  have apart := input.apart
  have room := input.room
  have even := input.dstEven
  have sa := input.srcAligned
  rw [sz] at apart room
  obtain ⟨stubEq, _⟩ := stub_of30 site sz
  obtain ⟨run5, entered, pc5⟩ := slow_facts site s S T input h0
  rw [if_neg h4, stubEq] at pc5
  generalize he5 : slowState site s = e5 at run5 entered pc5
  obtain ⟨runA, pcA, postA⟩ := run_splits 832 S T sa (by omega) 3 0 e5 (by simpa using code.splits)
    (by norm_num) (by simpa using pc5) entered.src entered.dst (by norm_num) (by omega) (by omega)
  generalize hA : splitsRun 0 3 e5 = a at runA pcA postA
  obtain ⟨runB, pcB, postB⟩ := split_chunk 850 24 S T false a code.tail (by norm_num) (by simpa using pcA)
    ((postA.regs .x7 (by decide)).trans entered.src) ((postA.regs .x21 (by decide)).trans entered.dst)
    (by norm_num) (by omega) (by omega) (by omega) (by rw [if_neg (by decide)]; omega)
  simp only [Bool.false_eq_true, if_false] at runB pcB postB
  generalize hB : splitPrefix 24 a = c at runB pcB postB
  have runJ := run_step c 854 _ (by norm_num) (by simpa using pcB) code.splitBack rfl rfl
  have same : split30 site s = execInstrBr c (.JALR .x0 .x10 116) := by rw [← hB, ← hA, ← he5]; rfl
  rw [same]
  have ab : BlockPost e5 c S T (24+6) :=
    post_join (by simpa using postA) (by simpa using postB) (by omega) (by unfold MEMORY_BYTES at room; omega)
  exact finish site input.wide s e5 c _ S T 28 30 sz 116 rfl entered
    (by simpa using ((run5.next runA).next runB).next runJ) (by simpa using ab) rfl

/-- A wide site's copy: the cycles depend on the destination's alignment; everything else is as for
the halfword copy it replaces, except that `x10` is clobbered too. -/
theorem wide_copy (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T) :
    WideDone site s (wideState site s) S T (wideCost site T) := by
  have facts := site_facts site input.wide
  have fit : T < 2^64 := by have := input.room; unfold MEMORY_BYTES at this; omega
  have low : (s.getReg .x21).toNat % 8 = T % 8 := by
    rw [input.dst, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
  unfold wideState wideCost
  simp only [low]
  rcases facts.size with sz | sz
  · simp only [sz, if_true]
    by_cases h0 : T % 8 = 0
    · rw [if_pos h0, if_pos h0]; exact dword32_done site s S T input sz h0
    · rw [if_neg h0, if_neg h0]
      by_cases h4 : T % 8 = 4
      · rw [if_pos h4, if_pos h4]; exact word32_done site s S T input sz h4
      · rw [if_neg h4, if_neg h4]; exact split32_done site s S T input sz h0 h4
  · simp only [sz, show (30 = 32) = False by decide, if_false]
    by_cases h0 : T % 8 = 0
    · rw [if_pos h0, if_pos h0]; exact dword30_done site s S T input sz h0
    · rw [if_neg h0, if_neg h0]
      by_cases h4 : T % 8 = 4
      · rw [if_pos h4, if_pos h4]; exact word30_done site s S T input sz h4
      · rw [if_neg h4, if_neg h4]; exact split30_done site s S T input sz h0 h4

theorem pair_regs (width load k : Nat) (s : MachineState) (r : Reg) (h : r ≠ .x31) :
    (pairStep width load k s).getReg r = s.getReg r := by
  have keep (u : MachineState) (v : Word) : (u.setReg .x31 v).getReg r = u.getReg r :=
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  unfold pairStep wideLoad wideStore
  by_cases h8 : width = 8
  · simp only [h8, ite_true, execInstrBr, MachineState.getReg_setPC, reg_setMem, keep]
  · by_cases h4 : width = 4
    · simp only [h4, show (4 = 8) = False from by decide, ite_true, ite_false, execInstrBr,
        MachineState.getReg_setPC, reg_setWord32, keep]
    · simp only [h8, h4, ite_false, execInstrBr, MachineState.getReg_setPC, reg_setHalfword, keep]

theorem pairs_regs (width load : Nat) (r : Reg) (h : r ≠ .x31) :
    ∀ n k (s : MachineState), (pairsRun width load k n s).getReg r = s.getReg r := by
  intro n
  induction n with
  | zero => intro k s; rfl
  | succ n ih => intro k s; exact (ih (k+1) _).trans (pair_regs width load k s r h)

theorem prefix_regs (k : Nat) (s : MachineState) (r : Reg) (h : r ≠ .x31) :
    (splitPrefix k s).getReg r = s.getReg r := by
  have keep (u : MachineState) (v : Word) : (u.setReg .x31 v).getReg r = u.getReg r :=
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  simp only [splitPrefix, execInstrBr, MachineState.getReg_setPC, reg_setWord32, reg_setHalfword, keep]

theorem split_regs (k : Nat) (s : MachineState) (r : Reg) (h : r ≠ .x31) :
    (splitStep k s).getReg r = s.getReg r := by
  have keep (u : MachineState) (v : Word) : (u.setReg .x31 v).getReg r = u.getReg r :=
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  simp only [splitStep, execInstrBr, MachineState.getReg_setPC, reg_setHalfword, keep]
  exact prefix_regs k s r h

theorem splits_regs (r : Reg) (h : r ≠ .x31) :
    ∀ n j (s : MachineState), (splitsRun j n s).getReg r = s.getReg r := by
  intro n
  induction n with
  | zero => intro j s; rfl
  | succ n ih => intro j s; exact (ih (j+1) _).trans (split_regs (8*j) s r h)

/-- Whatever the inputs, a wide site's copy changes no register but `x10` and `x31`. -/
theorem wide_regs (site : CopySite) (s : MachineState) (r : Reg) (a : r ≠ .x31) (b : r ≠ .x10) :
    (wideState site s).getReg r = s.getReg r := by
  have enter : (enterState site s).getReg r = s.getReg r := by
    unfold enterState entryJump
    rw [keep_x0 (beq_facts _ _).2, (andi_facts _).2.2.regs r a, (jal_facts _ _).2.2.regs r b]
  have slow : (slowState site s).getReg r = s.getReg r := by
    unfold slowState
    rw [keep_x0 (beq_facts _ 140).2, (addi_facts _).2.2.regs r a, enter]
  have jr (u : MachineState) (off : BitVec 12) : (execInstrBr u (.JALR .x0 .x10 off)).getReg r = u.getReg r :=
    keep_x0 (jalr_facts u off).2 r
  unfold wideState
  dsimp only
  split
  · split
    · unfold dword32; rw [jr, pairs_regs _ _ r a, enter]
    · split
      · unfold word32; rw [jr, pairs_regs _ _ r a, slow]
      · unfold split32; rw [jr, splits_regs r a, slow]
  · split
    · unfold dword30; rw [jr, pairs_regs _ _ r a, pairs_regs _ _ r a, pairs_regs _ _ r a, enter]
    · split
      · unfold word30; rw [jr, pairs_regs _ _ r a, pairs_regs _ _ r a, slow]
      · unfold split30; rw [jr, prefix_regs _ _ r a, splits_regs r a, slow]

end TwoPermutationPrototype.QuadOpening
