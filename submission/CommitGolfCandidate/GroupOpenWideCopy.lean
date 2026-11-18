import CommitGolfCandidate.GroupOpenCapMoves
import CommitGolfCandidate.TwoPermutationPackedOpeningBytes
import CommitGolfCandidate.ProjectedHalfwordMemory
import RiscvZkvm.Rv64.Logic.ByteOps

/-! Wide record copies (opening words 930..1061, after the 33-call salt chain).

Rows 43, 79, 115 (the three quartet mates) and 153 (the level-0 sibling) hold `jal x29,<stub>`. A stub tests the
destination's alignment (`x21 & 7`; the site offsets are multiples of 8): an 8-aligned destination copies four
dwords, a 4-aligned one eight words, and a 2-aligned one copies its first halfword in the stub and returns to the
site's own halfword pairs 1..15. Every path ends at the site's word `start+32` with only `x29` and `x31` changed.
The stub design and its measurement are the climber's (levers/climb/wide-copy.md); this module proves it. -/

namespace TwoPermutationPrototype.GroupedOpening
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64
open PackedOpening (ByteCopy)
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

/-- A word whose dword is `base` (8-aligned) is `base + offset`. -/
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
        have eq := Opening.nat_address_injective (by omega) (by omega) same
        omega
    · have shifted := tail.copied (i-first) (by omega)
      rw [show target+first+(i-first) = target+i by omega, show source+first+(i-first) = source+i by omega] at shifted
      rw [shifted, head.frame]
      intro j hj same
      have eq := Opening.nat_address_injective (by omega) (by omega) same
      omega
  · intro address outside
    rw [tail.frame _ (fun j hj => by
      have := outside (first+j) (by omega)
      rwa [← Nat.add_assoc] at this)]
    exact head.frame _ (fun j hj => outside j (by omega))

/-! ### Code -/

def CopySite.stub : CopySite → Nat
  | .quartet j => 930+33*j.val
  | .firstSibling => 1029
  | _ => 0

def Decodes (word : Nat) (instruction : Instr) : Prop :=
  (openingImage.code[word]?).bind Opening.decodeBase = some instruction

instance (word : Nat) (instruction : Instr) : Decidable (Decodes word instruction) := by
  unfold Decodes; infer_instance

def wideLoad (width : Nat) (src : Reg) (imm : Nat) : Instr :=
  if width = 8 then .LD .x31 src (BitVec.ofNat 12 imm)
  else if width = 4 then .LW .x31 src (BitVec.ofNat 12 imm)
  else .LHU .x31 src (BitVec.ofNat 12 imm)

def wideStore (width : Nat) (imm : Nat) : Instr :=
  if width = 8 then .SD .x21 .x31 (BitVec.ofNat 12 imm)
  else if width = 4 then .SW .x21 .x31 (BitVec.ofNat 12 imm)
  else .SH .x21 .x31 (BitVec.ofNat 12 imm)

/-- `count` load/store pairs of `width` bytes at words `word, word+1, ...`, the `k`-th reading
`load+width*k(src)` and writing `store+width*k(x21)`. -/
def PairsAt (word count width : Nat) (src : Reg) (load store : Nat) : Prop :=
  ∀ k < count, Decodes (word+2*k) (wideLoad width src (load+width*k)) ∧
    Decodes (word+2*k+1) (wideStore width (store+width*k))

instance (word count width : Nat) (src : Reg) (load store : Nat) :
    Decidable (PairsAt word count width src load store) := by
  unfold PairsAt; infer_instance

structure StubCode (site : CopySite) : Prop where
  entry : Decodes site.start (.JAL .x29 (BitVec.ofNat 21 (4*(site.stub-site.start))))
  test : Decodes site.stub (.ANDI .x31 .x21 7)
  eight : Decodes (site.stub+1) (.BEQ .x31 .x0 24)
  less : Decodes (site.stub+2) (.ADDI .x31 .x31 4092)
  four : Decodes (site.stub+3) (.BEQ .x31 .x0 52)
  firstHalf : PairsAt (site.stub+4) 1 2 site.source 0 site.destOffset
  back : Decodes (site.stub+6) (.JALR .x0 .x29 4)
  dwords : PairsAt (site.stub+7) 4 8 site.source 0 site.destOffset
  dwordsBack : Decodes (site.stub+15) (.JALR .x0 .x29 124)
  words : PairsAt (site.stub+16) 8 4 site.source 0 site.destOffset
  wordsBack : Decodes (site.stub+32) (.JALR .x0 .x29 124)
  halves : PairsAt (site.start+2) 15 2 site.source 2 (site.destOffset+2)

set_option maxHeartbeats 4000000 in
theorem stub_code_quartet : ∀ j : Fin 3, StubCode (.quartet j) := by
  intro j
  constructor <;> revert j <;> decide

set_option maxHeartbeats 4000000 in
theorem stub_code_first : StubCode .firstSibling := by
  constructor <;> decide

theorem stub_code (site : CopySite) (wide : site.wide = true) : StubCode site := by
  cases site with
  | quartet j => exact stub_code_quartet j
  | firstSibling => exact stub_code_first
  | _ => simp [CopySite.wide] at wide

/-! ### One step -/

def stepKind : Instr → Bool
  | .LHU .. | .SH .. | .LW .. | .SW .. | .LD .. | .SD .. | .ADDI .. | .ANDI .. | .BEQ .. | .JAL .. | .JALR .. => true
  | _ => false

theorem run_step (s : MachineState) (word : Nat) (i : Instr) (bounded : word < 1062)
    (pc : s.pc = BitVec.ofNat 64 (4096+4*word)) (dec : Decodes word i) (kind : stepKind i = true)
    (valid : memoryArgumentsValid s i = true) : RunsOpeningBlock s (execInstrBr s i) 1 := by
  intro fuel coins
  have run := execute_unit_steps openingImage 1 fuel (fun n => if n = 0 then s else execInstrBr s i) coins (by
    intro n hn
    have n0 : n = 0 := by omega
    subst n0
    refine ⟨.base i, by simpa using packed_fetch_all s word i bounded pc dec, ?_, ?_⟩
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

/-! ### Load/store pairs -/

def pairStep (width : Nat) (src : Reg) (load store k : Nat) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr s (wideLoad width src (load+width*k))) (wideStore width (store+width*k))

def pairsRun (width : Nat) (src : Reg) (load store : Nat) : Nat → Nat → MachineState → MachineState
  | _, 0, s => s
  | k, n+1, s => pairsRun width src load store (k+1) n (pairStep width src load store k s)

structure PairPost (s t : MachineState) (S T width : Nat) : Prop where
  pc : t.pc = s.pc + BitVec.ofNat 64 8
  regs : ∀ r, r ≠ .x31 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T width
  frame : ∀ q : Word, q ≠ alignToDword (BitVec.ofNat 64 T) → t.getMem q = s.getMem q

private theorem mem_setReg' (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl

private theorem setMem_congr {a b : MachineState} (same : a.mem = b.mem) (q v : Word) :
    (a.setMem q v).mem = (b.setMem q v).mem := by
  simp only [MachineState.setMem, same]

private theorem getMem_congr {a b : MachineState} (same : a.mem = b.mem) (q : Word) : a.getMem q = b.getMem q := by
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

theorem pair_post (width : Nat) (hw : width = 2 ∨ width = 4 ∨ width = 8) (src : Reg) (st : src ≠ .x31)
    (load store k S T : Nat) (s : MachineState)
    (sr : s.getReg src = BitVec.ofNat 64 S) (dr : s.getReg .x21 + BitVec.ofNat 64 store = BitVec.ofNat 64 T)
    (immL : load + width*k < 2048) (immS : store + width*k < 2048)
    (sa : (S+load+width*k) % width = 0) (ta : (T+width*k) % width = 0)
    (sf : S+load+width*k+width ≤ MEMORY_BYTES) (tf : T+width*k+width ≤ MEMORY_BYTES) :
    memoryArgumentsValid s (wideLoad width src (load+width*k)) = true ∧
    memoryArgumentsValid (execInstrBr s (wideLoad width src (load+width*k))) (wideStore width (store+width*k)) = true ∧
    PairPost s (pairStep width src load store k s) (S+load+width*k) (T+width*k) width := by
  have ram : MEMORY_BYTES < 2^64 := by decide
  have srcAddr : s.getReg src + signExtend12 (BitVec.ofNat 12 (load+width*k)) = BitVec.ofNat 64 (S+load+width*k) := by
    rw [sr, sign12 _ immL, ← BitVec.ofNat_add, Nat.add_assoc]
  have dstAddr (u : MachineState) (same : u.getReg .x21 = s.getReg .x21) :
      u.getReg .x21 + signExtend12 (BitVec.ofNat 12 (store+width*k)) = BitVec.ofNat 64 (T+width*k) := by
    rw [same, sign12 _ immS, BitVec.ofNat_add, ← BitVec.add_assoc, dr, ← BitVec.ofNat_add]
  have regs (u : MachineState) (r : Reg) (h : r ≠ .x31) (v : Word) : (u.setReg .x31 v).getReg r = u.getReg r :=
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  have eight : s.pc + 4 + 4 = s.pc + BitVec.ofNat 64 8 := by rw [BitVec.add_assoc]; rfl
  rcases hw with rfl | rfl | rfl
  · -- halfwords
    simp only [pairStep, wideLoad, wideStore, show (2 = 8) = False from by decide, show (2 = 4) = False from by decide,
      if_false]
    let a := execInstrBr s (.LHU .x31 src (BitVec.ofNat 12 (load+2*k)))
    have aMem : a.mem = s.mem := by simp only [a, execInstrBr, MachineState.setPC, mem_setReg']
    have a21 : a.getReg .x21 = s.getReg .x21 := by
      simp only [a, execInstrBr, MachineState.getReg_setPC]; exact regs _ _ (by decide) _
    have a31 : (a.getReg .x31).truncate 16 = s.getHalfword (BitVec.ofNat 64 (S+load+2*k)) := by
      simp only [a, execInstrBr, MachineState.getReg_setPC, srcAddr,
        MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0), zero_truncate]
    obtain ⟨copy, frame⟩ := half_store s (S+load+2*k) (T+2*k) sa ta (by omega) (by omega)
    have tMem : (execInstrBr a (.SH .x21 .x31 (BitVec.ofNat 12 (store+2*k)))).mem =
        (s.setHalfword (BitVec.ofNat 64 (T+2*k)) (s.getHalfword (BitVec.ofNat 64 (S+load+2*k)))).mem := by
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
    let a := execInstrBr s (.LW .x31 src (BitVec.ofNat 12 (load+4*k)))
    have aMem : a.mem = s.mem := by simp only [a, execInstrBr, MachineState.setPC, mem_setReg']
    have a21 : a.getReg .x21 = s.getReg .x21 := by
      simp only [a, execInstrBr, MachineState.getReg_setPC]; exact regs _ _ (by decide) _
    have a31 : (a.getReg .x31).truncate 32 = s.getWord32 (BitVec.ofNat 64 (S+load+4*k)) := by
      simp only [a, execInstrBr, MachineState.getReg_setPC, srcAddr,
        MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0), sign_truncate]
    obtain ⟨copy, frame⟩ := word_store s (S+load+4*k) (T+4*k) sa ta (by omega) (by omega)
    have tMem : (execInstrBr a (.SW .x21 .x31 (BitVec.ofNat 12 (store+4*k)))).mem =
        (s.setWord32 (BitVec.ofNat 64 (T+4*k)) (s.getWord32 (BitVec.ofNat 64 (S+load+4*k)))).mem := by
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
    let a := execInstrBr s (.LD .x31 src (BitVec.ofNat 12 (load+8*k)))
    have aMem : a.mem = s.mem := by simp only [a, execInstrBr, MachineState.setPC, mem_setReg']
    have a21 : a.getReg .x21 = s.getReg .x21 := by
      simp only [a, execInstrBr, MachineState.getReg_setPC]; exact regs _ _ (by decide) _
    have a31 : a.getReg .x31 = s.getMem (BitVec.ofNat 64 (S+load+8*k)) := by
      simp only [a, execInstrBr, MachineState.getReg_setPC, srcAddr,
        MachineState.getReg_setReg_eq (by decide : Reg.x31 ≠ .x0)]
    obtain ⟨copy, frame⟩ := dword_store s (S+load+8*k) (T+8*k) sa ta (by omega) (by omega)
    have tMem : (execInstrBr a (.SD .x21 .x31 (BitVec.ofNat 12 (store+8*k)))).mem =
        (s.setMem (BitVec.ofNat 64 (T+8*k)) (s.getMem (BitVec.ofNat 64 (S+load+8*k)))).mem := by
      simp only [execInstrBr, MachineState.setPC, dstAddr a a21, a31]
      simp only [MachineState.setMem, aMem]
    have alignT : alignToDword (BitVec.ofNat 64 (T+8*k)) = BitVec.ofNat 64 (T+8*k) := by
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

theorem load_pc (s : MachineState) (width : Nat) (src : Reg) (imm : Nat) :
    (execInstrBr s (wideLoad width src imm)).pc = s.pc + 4 := by
  unfold wideLoad; split <;> (try split) <;> rfl

theorem load_kind (width : Nat) (src : Reg) (imm : Nat) : stepKind (wideLoad width src imm) = true := by
  unfold wideLoad; split <;> (try split) <;> rfl

theorem store_kind (width : Nat) (imm : Nat) : stepKind (wideStore width imm) = true := by
  unfold wideStore; split <;> (try split) <;> rfl

theorem run_zero (s : MachineState) : RunsOpeningBlock s s 0 := by
  intro fuel coins
  simp [Execution.charge]

theorem run_pairs (width : Nat) (hw : width = 2 ∨ width = 4 ∨ width = 8) (src : Reg) (st : src ≠ .x31)
    (word load store S T : Nat) (sa : (S+load) % width = 0) (ta : T % width = 0) :
    ∀ (n j : Nat) (s : MachineState), PairsAt word (j+n) width src load store → word+2*(j+n) ≤ 1062 →
      s.pc = BitVec.ofNat 64 (4096+4*(word+2*j)) →
      s.getReg src = BitVec.ofNat 64 S → s.getReg .x21 + BitVec.ofNat 64 store = BitVec.ofNat 64 T →
      load + width*(j+n) ≤ 2048 → store + width*(j+n) ≤ 2048 →
      S+load+width*(j+n) ≤ T → T+width*(j+n) ≤ MEMORY_BYTES →
      RunsOpeningBlock s (pairsRun width src load store j n s) (2*n) ∧
      (pairsRun width src load store j n s).pc = BitVec.ofNat 64 (4096+4*(word+2*(j+n))) ∧
      (∀ r, r ≠ .x31 → (pairsRun width src load store j n s).getReg r = s.getReg r) ∧
      ByteCopy s (pairsRun width src load store j n s) (S+load+width*j) (T+width*j) (width*n) ∧
      (∀ q : Word, q.toNat < T - T % 8 → (pairsRun width src load store j n s).getMem q = s.getMem q) := by
  have wpos : 2 ≤ width := by omega
  intro n
  induction n with
  | zero =>
    intro j s _ _ pc _ _ _ _ _ _
    refine ⟨run_zero s, by simpa [pairsRun] using pc, fun r _ => rfl, ⟨fun i h => absurd h (by omega), fun q _ => rfl⟩,
      fun q _ => rfl⟩
  | succ n ih =>
    intro j s code fits pc sr dr immL immS apart room
    have e1 : width*(j+(n+1)) = width*j + width*n + width := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
    have e2 : width*(j+1+n) = width*j + width*n + width := by rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]; omega
    have e3 : width*(j+1) = width*j + width := by rw [Nat.mul_add, Nat.mul_one]
    have e4 : width*(n+1) = width + width*n := by rw [Nat.mul_add, Nat.mul_one]; omega
    have wj : width ≤ width*j + width := by omega
    have saj : (S+load+width*j) % width = 0 := by rw [Nat.add_mul_mod_self_left]; exact sa
    have taj : (T+width*j) % width = 0 := by rw [Nat.add_mul_mod_self_left]; exact ta
    obtain ⟨vl, vs, post⟩ := pair_post width hw src st load store j S T s sr dr (by omega) (by omega) saj taj
      (by omega) (by omega)
    let m := pairStep width src load store j s
    have codeJ := code j (by omega)
    have ranPair : RunsOpeningBlock s m 2 :=
      (run_step s (word+2*j) _ (by omega) pc codeJ.1 (load_kind _ _ _) vl).next
        (run_step _ (word+2*j+1) _ (by omega) (by
          rw [load_pc, pc, show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]; congr 1)
          codeJ.2 (store_kind _ _) vs)
    have mpc : m.pc = BitVec.ofNat 64 (4096+4*(word+2*(j+1))) := by
      rw [post.pc, pc, ← BitVec.ofNat_add]; congr 1
    have rest := ih (j+1) m (by rw [show j+1+n = j+(n+1) by omega]; exact code) (by omega) mpc
      ((post.regs src st).trans sr) ((by rw [post.regs .x21 (by decide)]; exact dr)) (by omega) (by omega)
      (by omega) (by omega)
    obtain ⟨rRun, rPC, rRegs, rCopy, rFrame⟩ := rest
    have total : pairsRun width src load store j (n+1) s = pairsRun width src load store (j+1) n m := rfl
    rw [total]
    refine ⟨?_, by rw [rPC]; congr 2; omega, fun r h => (rRegs r h).trans (post.regs r h), ?_, ?_⟩
    · rw [show 2*(n+1) = 2+2*n by omega]; exact ranPair.next rRun
    · have tail : ByteCopy m (pairsRun width src load store (j+1) n m) (S+load+width*j+width) (T+width*j+width)
          (width*n) := by
        rw [show S+load+width*j+width = S+load+width*(j+1) by omega, show T+width*j+width = T+width*(j+1) by omega]
        exact rCopy
      rw [e4]
      exact copy_extend post.bytes tail (by omega) (by unfold MEMORY_BYTES at room; omega)
    · intro q below
      rw [rFrame q below]
      apply post.frame
      intro same
      have := align_nat (T+width*j) (by unfold MEMORY_BYTES at room; omega)
      rw [← same] at this
      omega

/-! ### The stub paths -/

def entryJump (site : CopySite) : Instr := .JAL .x29 (BitVec.ofNat 21 (4*(site.stub-site.start)))

def enterState (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (execInstrBr s (entryJump site)) (.ANDI .x31 .x21 7)) (.BEQ .x31 .x0 24)

def slowState (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (execInstrBr (enterState site s) (.ADDI .x31 .x31 4092)) (.BEQ .x31 .x0 52)

def dwordPath (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (pairsRun 8 site.source 0 site.destOffset 0 4 (enterState site s)) (.JALR .x0 .x29 124)

def wordPath (site : CopySite) (s : MachineState) : MachineState :=
  execInstrBr (pairsRun 4 site.source 0 site.destOffset 0 8 (slowState site s)) (.JALR .x0 .x29 124)

def halfPath (site : CopySite) (s : MachineState) : MachineState :=
  pairsRun 2 site.source 2 (site.destOffset+2) 0 15
    (execInstrBr (pairsRun 2 site.source 0 site.destOffset 0 1 (slowState site s)) (.JALR .x0 .x29 4))

/-- The state after a wide site's copy: the stub path picked by the destination's alignment. -/
def wideState (site : CopySite) (s : MachineState) : MachineState :=
  if (s.getReg .x21).toNat % 8 = 0 then dwordPath site s
  else if (s.getReg .x21).toNat % 8 = 4 then wordPath site s else halfPath site s

/-- Cycles of a wide site's copy into `target`: 12 (8-aligned), 22 (4-aligned) or 38. -/
def wideCost (target : Nat) : Nat := if target % 8 = 0 then 12 else if target % 8 = 4 then 22 else 38

structure WideInputs (site : CopySite) (s : MachineState) (S T : Nat) : Prop where
  wide : site.wide = true
  pc : s.pc = BitVec.ofNat 64 (4096+4*site.start)
  src : s.getReg site.source = BitVec.ofNat 64 S
  dst : s.getReg .x21 + BitVec.ofNat 64 site.destOffset = BitVec.ofNat 64 T
  srcAligned : S % 8 = 0
  dstEven : T % 2 = 0
  apart : S+32 ≤ T
  room : T+32 ≤ MEMORY_BYTES

structure SiteFacts (site : CopySite) : Prop where
  startFit : site.start+32 ≤ 1062
  stubFit : site.stub+33 ≤ 1062
  jump : BitVec.ofNat 64 (4096+4*site.start) + signExtend21 (BitVec.ofNat 21 (4*(site.stub-site.start))) =
    BitVec.ofNat 64 (4096+4*site.stub)
  back124 : (BitVec.ofNat 64 (4096+4*(site.start+1)) + signExtend12 124) &&& ~~~1#64 =
    BitVec.ofNat 64 (4096+4*(site.start+32))
  back4 : (BitVec.ofNat 64 (4096+4*(site.start+1)) + signExtend12 4) &&& ~~~1#64 =
    BitVec.ofNat 64 (4096+4*(site.start+2))
  src31 : site.source ≠ .x31
  src29 : site.source ≠ .x29
  src0 : site.source ≠ .x0
  offAligned : site.destOffset % 8 = 0
  offSmall : site.destOffset+32 ≤ 2000

theorem site_facts (site : CopySite) (wide : site.wide = true) : SiteFacts site := by
  cases site with
  | quartet j => clear wide; constructor <;> revert j <;> decide
  | firstSibling => constructor <;> decide
  | _ => simp [CopySite.wide] at wide

private theorem low_bits (x : Word) (d T : Nat) (fit : T < 2^64) (aligned : d % 8 = 0)
    (sum : x + BitVec.ofNat 64 d = BitVec.ofNat 64 T) :
    x.toNat % 8 = T % 8 ∧ x &&& signExtend12 7 = BitVec.ofNat 64 (T % 8) := by
  have total := congrArg BitVec.toNat sum
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit] at total
  have low : x.toNat % 8 = T % 8 := by
    have dm : d % 2^64 % 8 = 0 := by rw [Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2^64)]; exact aligned
    rw [← total, Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2^64)]
    omega
  refine ⟨low, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [show signExtend12 7 = (7#64 : Word) from rfl, BitVec.toNat_and,
    show (7#64 : Word).toNat = 2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat]
  omega

private theorem zero_reg (u : MachineState) : u.getReg .x0 = 0#64 := rfl

private theorem plain_valid (u : MachineState) (i : Instr) (none : memAccess u i = none) :
    memoryArgumentsValid u i = true := by
  unfold memoryArgumentsValid; rw [none]

structure Moves (u v : MachineState) (changed : Reg) : Prop where
  regs : ∀ r, r ≠ changed → v.getReg r = u.getReg r
  mem : v.mem = u.mem

theorem jal_facts (u : MachineState) (off : BitVec 21) :
    let v := execInstrBr u (.JAL .x29 off)
    v.pc = u.pc + signExtend21 off ∧ v.getReg .x29 = u.pc + 4 ∧ Moves u v .x29 := by
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
  · simp only [execInstrBr, zero_reg]
    by_cases h : u.getReg .x31 = 0#64 <;> simp [h, MachineState.setPC]
  · simp only [execInstrBr]; split <;> rfl
  · simp only [execInstrBr]; split <;> rfl

theorem jalr_facts (u : MachineState) (off : BitVec 12) :
    let v := execInstrBr u (.JALR .x0 .x29 off)
    v.pc = (u.getReg .x29 + signExtend12 off) &&& ~~~1#64 ∧ Moves u v .x0 := by
  refine ⟨rfl, fun r h => ?_, ?_⟩
  · simp only [execInstrBr, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  · simp only [execInstrBr, MachineState.setPC, mem_setReg']

theorem ofNat_step (a b : Nat) : BitVec.ofNat 64 (4096+4*a) + BitVec.ofNat 64 (4*b) = BitVec.ofNat 64 (4096+4*(a+b)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

theorem ofNat_four (a : Nat) : BitVec.ofNat 64 (4096+4*a) + 4 = BitVec.ofNat 64 (4096+4*(a+1)) := by
  rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]; congr 1

theorem copy_zero (s : MachineState) (S T : Nat) : ByteCopy s s S T 0 :=
  ⟨fun i h => absurd h (by omega), fun _ _ => rfl⟩

theorem copy_after {s t u : MachineState} {S T n : Nat} (copy : ByteCopy s t S T n) (same : u.mem = t.mem) :
    ByteCopy s u S T n := copy_congr_mem same copy

structure Entered (site : CopySite) (s e : MachineState) (S T : Nat) : Prop where
  x29 : e.getReg .x29 = BitVec.ofNat 64 (4096+4*(site.start+1))
  src : e.getReg site.source = BitVec.ofNat 64 S
  dst : e.getReg .x21 + BitVec.ofNat 64 site.destOffset = BitVec.ofNat 64 T
  mem : e.mem = s.mem
  regs : ∀ r, r ≠ .x31 → r ≠ .x29 → e.getReg r = s.getReg r

theorem moves_reg {u v : MachineState} {changed : Reg} (m : Moves u v changed) (r : Reg) (h : r ≠ changed)
    (zero : changed = .x0 → r ≠ .x0 ∨ True := fun _ => Or.inr trivial) : v.getReg r = u.getReg r := m.regs r h

theorem x0_any (u v : MachineState) : v.getReg .x0 = u.getReg .x0 := rfl

theorem enter_facts (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T) :
    RunsOpeningBlock s (enterState site s) 3 ∧ Entered site s (enterState site s) S T ∧
    (enterState site s).getReg .x31 = BitVec.ofNat 64 (T % 8) ∧
    (enterState site s).pc = (if T % 8 = 0 then BitVec.ofNat 64 (4096+4*(site.stub+7))
      else BitVec.ofNat 64 (4096+4*(site.stub+2))) := by
  have facts := site_facts site input.wide
  have code := stub_code site input.wide
  have sf := facts.startFit
  have bf := facts.stubFit
  obtain ⟨low, andBits⟩ := low_bits (s.getReg .x21) site.destOffset T
    (by have := input.room; unfold MEMORY_BYTES at this; omega) facts.offAligned input.dst
  have run1 := run_step s site.start _ (by omega) input.pc code.entry rfl rfl
  obtain ⟨p1, x29a, m1⟩ := jal_facts s (BitVec.ofNat 21 (4*(site.stub-site.start)))
  generalize he1 : execInstrBr s (.JAL .x29 (BitVec.ofNat 21 (4*(site.stub-site.start)))) = e1 at p1 x29a m1
  have run1' : RunsOpeningBlock s e1 1 := by rw [← he1]; exact run1
  have pc1 : e1.pc = BitVec.ofNat 64 (4096+4*site.stub) := by rw [p1, input.pc]; exact facts.jump
  have run2 := run_step e1 site.stub _ (by omega) pc1 code.test rfl rfl
  obtain ⟨p2, x31b, m2⟩ := andi_facts e1
  generalize he2 : execInstrBr e1 (.ANDI .x31 .x21 7) = e2 at p2 x31b m2 run2
  have pc2 : e2.pc = BitVec.ofNat 64 (4096+4*(site.stub+1)) := by rw [p2, pc1, ofNat_four]
  have v31 : e2.getReg .x31 = BitVec.ofNat 64 (T % 8) := by rw [x31b, m1.regs .x21 (by decide), andBits]
  have run3 := run_step e2 (site.stub+1) _ (by omega) pc2 code.eight rfl rfl
  obtain ⟨p3, m3⟩ := beq_facts e2 24
  generalize he3 : execInstrBr e2 (.BEQ .x31 .x0 24) = e3 at p3 m3 run3
  have same : enterState site s = e3 := by rw [← he3, ← he2, ← he1]; unfold enterState entryJump; exact Eq.refl _
  rw [same]
  have keep (r : Reg) (a : r ≠ .x31) (b : r ≠ .x29) : e3.getReg r = s.getReg r := by
    by_cases z : r = .x0
    · subst z; exact x0_any _ _
    · rw [m3.regs r z, m2.regs r a, m1.regs r b]
  have total := (run1'.next run2).next run3
  rw [show 1+1+1 = 3 from rfl] at total
  refine ⟨total, ⟨?_, ?_, ?_, ?_, keep⟩, by rw [m3.regs .x31 (by decide), v31], ?_⟩
  · rw [m3.regs .x29 (by decide), m2.regs .x29 (by decide), x29a, input.pc, ofNat_four]
  · rw [keep _ facts.src31 facts.src29, input.src]
  · rw [keep .x21 (by decide) (by decide)]; exact input.dst
  · rw [m3.mem, m2.mem, m1.mem]
  · rw [p3, v31, pc2]
    have cls : T % 8 = 0 ∨ T % 8 = 2 ∨ T % 8 = 4 ∨ T % 8 = 6 := by have := input.dstEven; omega
    rcases cls with h | h | h | h <;> rw [h]
    · rw [if_pos rfl, if_pos rfl, show signExtend13 24 = BitVec.ofNat 64 (4*6) from rfl, ofNat_step]
    all_goals rw [if_neg (by decide), if_neg (by decide), ofNat_four]

theorem slow_facts (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (slow : T % 8 ≠ 0) :
    RunsOpeningBlock s (slowState site s) 5 ∧ Entered site s (slowState site s) S T ∧
    (slowState site s).pc = (if T % 8 = 4 then BitVec.ofNat 64 (4096+4*(site.stub+16))
      else BitVec.ofNat 64 (4096+4*(site.stub+4))) := by
  have facts := site_facts site input.wide
  have code := stub_code site input.wide
  have bf := facts.stubFit
  obtain ⟨run3, entered, x31e, pc3⟩ := enter_facts site s S T input
  rw [if_neg slow] at pc3
  generalize he3 : enterState site s = e3 at run3 entered pc3 x31e
  have run4 := run_step e3 (site.stub+2) _ (by omega) pc3 code.less rfl rfl
  obtain ⟨p4, x31c, m4⟩ := addi_facts e3
  generalize he4 : execInstrBr e3 (.ADDI .x31 .x31 4092) = e4 at p4 x31c m4 run4
  have pc4 : e4.pc = BitVec.ofNat 64 (4096+4*(site.stub+3)) := by rw [p4, pc3, ofNat_four]
  have run5 := run_step e4 (site.stub+3) _ (by omega) pc4 code.four rfl rfl
  obtain ⟨p5, m5⟩ := beq_facts e4 52
  generalize he5 : execInstrBr e4 (.BEQ .x31 .x0 52) = e5 at p5 m5 run5
  have same : slowState site s = e5 := by rw [← he5, ← he4, ← he3]; unfold slowState; exact Eq.refl _
  rw [same]
  have keep (r : Reg) (a : r ≠ .x31) : e5.getReg r = e3.getReg r := by
    by_cases z : r = .x0
    · subst z; exact x0_any _ _
    · rw [m5.regs r z, m4.regs r a]
  have total := (run3.next run4).next run5
  rw [show 3+1+1 = 5 from rfl] at total
  refine ⟨total, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [keep .x29 (by decide)]; exact entered.x29
  · rw [keep _ facts.src31]; exact entered.src
  · rw [keep .x21 (by decide)]; exact entered.dst
  · rw [m5.mem, m4.mem]; exact entered.mem
  · intro r a b; rw [keep r a]; exact entered.regs r a b
  · rw [p5, x31c, x31e, pc4]
    have cls : T % 8 = 2 ∨ T % 8 = 4 ∨ T % 8 = 6 := by have := input.dstEven; omega
    rcases cls with h | h | h <;> rw [h]
    · rw [if_neg (by decide), if_neg (by decide), ofNat_four]
    · rw [if_pos (by decide), if_pos rfl, show signExtend13 52 = BitVec.ofNat 64 (4*13) from rfl, ofNat_step]
    · rw [if_neg (by decide), if_neg (by decide), ofNat_four]

structure WideDone (site : CopySite) (s t : MachineState) (S T cost : Nat) : Prop where
  run : RunsOpeningBlock s t cost
  pc : t.pc = BitVec.ofNat 64 (4096+4*(site.start+32))
  regs : ∀ r, r ≠ .x31 → r ≠ .x29 → t.getReg r = s.getReg r
  bytes : ByteCopy s t S T 32
  below : ∀ q : Word, q.toNat < T - T % 8 → t.getMem q = s.getMem q

theorem keep_x0 {u v : MachineState} (m : Moves u v .x0) (r : Reg) : v.getReg r = u.getReg r := by
  by_cases z : r = .x0
  · subst z; exact x0_any _ _
  · exact m.regs r z

theorem dword_path_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (h : T % 8 = 0) : WideDone site s (dwordPath site s) S T 12 := by
  have facts := site_facts site input.wide
  have code := stub_code site input.wide
  have sf := facts.startFit
  have bf := facts.stubFit
  have off := facts.offSmall
  have room := input.room
  obtain ⟨run3, entered, _, pc3⟩ := enter_facts site s S T input
  rw [if_pos h] at pc3
  generalize he3 : enterState site s = e3 at run3 entered pc3
  obtain ⟨runP, pcP, regsP, copyP, belowP⟩ := run_pairs 8 (by decide) site.source facts.src31 (site.stub+7) 0
    site.destOffset S T (by have := input.srcAligned; omega) h 4 0 e3 (by simpa using code.dwords) (by omega)
    (by simpa using pc3) entered.src entered.dst (by omega) (by omega) (by have := input.apart; omega) (by omega)
  generalize hc : pairsRun 8 site.source 0 site.destOffset 0 4 e3 = c at runP pcP regsP copyP belowP
  have pcC : c.pc = BitVec.ofNat 64 (4096+4*(site.stub+15)) := by rw [pcP]
  have runJ := run_step c (site.stub+15) _ (by omega) pcC code.dwordsBack rfl rfl
  obtain ⟨pJ, mJ⟩ := jalr_facts c 124
  generalize hf : execInstrBr c (.JALR .x0 .x29 124) = f at pJ mJ runJ
  have same : dwordPath site s = f := by rw [← hf, ← hc, ← he3]; unfold dwordPath; exact Eq.refl _
  rw [same]
  have total := (run3.next runP).next runJ
  rw [show 3+2*4+1 = 12 from rfl] at total
  refine ⟨total, ?_, ?_, ?_, ?_⟩
  · rw [pJ, regsP .x29 (by decide), entered.x29]; exact facts.back124
  · intro r a b; rw [keep_x0 mJ r, regsP r a, entered.regs r a b]
  · have c32 : ByteCopy e3 c S T 32 := by simpa using copyP
    exact copy_congr_mem mJ.mem (copy_congr_before entered.mem.symm c32)
  · intro q below
    rw [getMem_congr mJ.mem, belowP q below, getMem_congr entered.mem]

theorem word_path_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (h : T % 8 = 4) : WideDone site s (wordPath site s) S T 22 := by
  have facts := site_facts site input.wide
  have code := stub_code site input.wide
  have sf := facts.startFit
  have bf := facts.stubFit
  have off := facts.offSmall
  have room := input.room
  obtain ⟨run5, entered, pc5⟩ := slow_facts site s S T input (by omega)
  rw [if_pos h] at pc5
  generalize he5 : slowState site s = e5 at run5 entered pc5
  obtain ⟨runP, pcP, regsP, copyP, belowP⟩ := run_pairs 4 (by decide) site.source facts.src31 (site.stub+16) 0
    site.destOffset S T (by have := input.srcAligned; omega) (by omega) 8 0 e5 (by simpa using code.words) (by omega)
    (by simpa using pc5) entered.src entered.dst (by omega) (by omega) (by have := input.apart; omega) (by omega)
  generalize hc : pairsRun 4 site.source 0 site.destOffset 0 8 e5 = c at runP pcP regsP copyP belowP
  have pcC : c.pc = BitVec.ofNat 64 (4096+4*(site.stub+32)) := by rw [pcP]
  have runJ := run_step c (site.stub+32) _ (by omega) pcC code.wordsBack rfl rfl
  obtain ⟨pJ, mJ⟩ := jalr_facts c 124
  generalize hf : execInstrBr c (.JALR .x0 .x29 124) = f at pJ mJ runJ
  have same : wordPath site s = f := by rw [← hf, ← hc, ← he5]; unfold wordPath; exact Eq.refl _
  rw [same]
  have total := (run5.next runP).next runJ
  rw [show 5+2*8+1 = 22 from rfl] at total
  refine ⟨total, ?_, ?_, ?_, ?_⟩
  · rw [pJ, regsP .x29 (by decide), entered.x29]; exact facts.back124
  · intro r a b; rw [keep_x0 mJ r, regsP r a, entered.regs r a b]
  · have c32 : ByteCopy e5 c S T 32 := by simpa using copyP
    exact copy_congr_mem mJ.mem (copy_congr_before entered.mem.symm c32)
  · intro q below
    rw [getMem_congr mJ.mem, belowP q below, getMem_congr entered.mem]

theorem half_path_done (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T)
    (h : T % 8 ≠ 0) (h4 : T % 8 ≠ 4) : WideDone site s (halfPath site s) S T 38 := by
  have facts := site_facts site input.wide
  have code := stub_code site input.wide
  have sf := facts.startFit
  have bf := facts.stubFit
  have off := facts.offSmall
  have room := input.room
  have apart := input.apart
  have even := input.dstEven
  obtain ⟨run5, entered, pc5⟩ := slow_facts site s S T input h
  rw [if_neg h4] at pc5
  generalize he5 : slowState site s = e5 at run5 entered pc5
  obtain ⟨runA, pcA, regsA, copyA, belowA⟩ := run_pairs 2 (by decide) site.source facts.src31 (site.stub+4) 0
    site.destOffset S T (by have := input.srcAligned; omega) (by omega) 1 0 e5 (by simpa using code.firstHalf)
    (by omega) (by simpa using pc5) entered.src entered.dst (by omega) (by omega) (by omega) (by omega)
  generalize hc : pairsRun 2 site.source 0 site.destOffset 0 1 e5 = c at runA pcA regsA copyA belowA
  have pcC : c.pc = BitVec.ofNat 64 (4096+4*(site.stub+6)) := by rw [pcA]
  have runJ := run_step c (site.stub+6) _ (by omega) pcC code.back rfl rfl
  obtain ⟨pJ, mJ⟩ := jalr_facts c 4
  generalize hr : execInstrBr c (.JALR .x0 .x29 4) = r at pJ mJ runJ
  have pcR : r.pc = BitVec.ofNat 64 (4096+4*(site.start+2+2*0)) := by
    rw [pJ, regsA .x29 (by decide), entered.x29]; exact facts.back4
  have srcR : r.getReg site.source = BitVec.ofNat 64 S := by
    rw [keep_x0 mJ, regsA _ facts.src31]; exact entered.src
  have dstR : r.getReg .x21 + BitVec.ofNat 64 (site.destOffset+2) = BitVec.ofNat 64 (T+2) := by
    rw [keep_x0 mJ, regsA .x21 (by decide), BitVec.ofNat_add, ← BitVec.add_assoc, entered.dst, ← BitVec.ofNat_add]
  obtain ⟨runB, pcB, regsB, copyB, belowB⟩ := run_pairs 2 (by decide) site.source facts.src31 (site.start+2) 2
    (site.destOffset+2) S (T+2) (by have := input.srcAligned; omega) (by omega) 15 0 r (by simpa using code.halves)
    (by omega) pcR srcR dstR (by omega) (by omega) (by omega) (by omega)
  generalize hf : pairsRun 2 site.source 2 (site.destOffset+2) 0 15 r = f at runB pcB regsB copyB belowB
  have same : halfPath site s = f := by rw [← hf, ← hr, ← hc, ← he5]; unfold halfPath; exact Eq.refl _
  rw [same]
  have total := ((run5.next runA).next runJ).next runB
  rw [show 5+2*1+1+2*15 = 38 from rfl] at total
  refine ⟨total, ?_, ?_, ?_, ?_⟩
  · rw [pcB]
  · intro x a b; rw [regsB x a, keep_x0 mJ x, regsA x a, entered.regs x a b]
  · have head : ByteCopy e5 c S T 2 := by simpa using copyA
    have tail : ByteCopy c f (S+2) (T+2) 30 := copy_congr_before mJ.mem.symm (by simpa using copyB)
    have whole := copy_extend head tail (by omega) (by unfold MEMORY_BYTES at room; omega)
    exact copy_congr_before entered.mem.symm whole
  · intro q below
    rw [belowB q (by omega), getMem_congr mJ.mem, belowA q below, getMem_congr entered.mem]

/-- A wide site's copy: the cycles depend on the destination's alignment, everything else is as for the
halfword copy it replaces (`x29` is clobbered too). -/
theorem wide_copy (site : CopySite) (s : MachineState) (S T : Nat) (input : WideInputs site s S T) :
    WideDone site s (wideState site s) S T (wideCost T) := by
  have facts := site_facts site input.wide
  obtain ⟨low, _⟩ := low_bits (s.getReg .x21) site.destOffset T
    (by have := input.room; unfold MEMORY_BYTES at this; omega) facts.offAligned input.dst
  unfold wideState wideCost
  rw [low]
  by_cases h0 : T % 8 = 0
  · rw [if_pos h0, if_pos h0]; exact dword_path_done site s S T input h0
  · rw [if_neg h0, if_neg h0]
    by_cases h4 : T % 8 = 4
    · rw [if_pos h4, if_pos h4]; exact word_path_done site s S T input h4
    · rw [if_neg h4, if_neg h4]; exact half_path_done site s S T input h0 h4

theorem pair_regs (width : Nat) (src : Reg) (load store k : Nat) (s : MachineState) (r : Reg) (h : r ≠ .x31) :
    (pairStep width src load store k s).getReg r = s.getReg r := by
  have keep (u : MachineState) (v : Word) : (u.setReg .x31 v).getReg r = u.getReg r :=
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h)
  unfold pairStep wideLoad wideStore
  by_cases h8 : width = 8
  · simp only [h8, ite_true, execInstrBr, MachineState.getReg_setPC, reg_setMem, keep]
  · by_cases h4 : width = 4
    · simp only [h4, show (4 = 8) = False from by decide, ite_true, ite_false, execInstrBr,
        MachineState.getReg_setPC, reg_setWord32, keep]
    · simp only [h8, h4, ite_false, execInstrBr, MachineState.getReg_setPC, reg_setHalfword, keep]

theorem pairs_regs (width : Nat) (src : Reg) (load store : Nat) (r : Reg) (h : r ≠ .x31) :
    ∀ n k (s : MachineState), (pairsRun width src load store k n s).getReg r = s.getReg r := by
  intro n
  induction n with
  | zero => intro k s; rfl
  | succ n ih => intro k s; exact (ih (k+1) _).trans (pair_regs width src load store k s r h)

/-- Whatever the inputs, a wide site's copy changes no register but `x29` and `x31`. -/
theorem wide_regs (site : CopySite) (s : MachineState) (r : Reg) (a : r ≠ .x31) (b : r ≠ .x29) :
    (wideState site s).getReg r = s.getReg r := by
  have enter : (enterState site s).getReg r = s.getReg r := by
    unfold enterState entryJump
    rw [keep_x0 (beq_facts _ 24).2, (andi_facts _).2.2.regs r a, (jal_facts _ _).2.2.regs r b]
  have slow : (slowState site s).getReg r = s.getReg r := by
    unfold slowState
    rw [keep_x0 (beq_facts _ 52).2, (addi_facts _).2.2.regs r a, enter]
  unfold wideState
  split
  · unfold dwordPath; rw [keep_x0 (jalr_facts _ 124).2, pairs_regs _ _ _ _ r a, enter]
  · split
    · unfold wordPath; rw [keep_x0 (jalr_facts _ 124).2, pairs_regs _ _ _ _ r a, slow]
    · unfold halfPath; rw [pairs_regs _ _ _ _ r a, keep_x0 (jalr_facts _ 4).2, pairs_regs _ _ _ _ r a, slow]

end TwoPermutationPrototype.GroupedOpening
