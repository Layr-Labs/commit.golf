import CommitGolfCandidate.GroupOpenCapMoves
import CommitGolfCandidate.TwoPermutationPackedOpeningBytes
import CommitGolfCandidate.ProjectedHalfwordMemory
import RiscvZkvm.Rv64.Logic.ByteOps

/-! Width-generic copy refinements and decoding of the four 32-byte copy stubs.
The inline test falls through to shifted loads for 2-mod-4 destinations;
the other destinations branch to four dwords or eight words in the stub,
whose direct jumps return to the site's continuation. -/

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
  test : Decodes site.start (.ANDI .x31 .x21 3)
  aligned : Decodes (site.start+1) (.BEQ .x31 .x0
    (BitVec.ofNat 13 (4*(site.stub+2-(site.start+1)))))
  test8 : Decodes (site.stub+2) (.ANDI .x31 .x21 7)
  four : Decodes (site.stub+3) (.BNE .x31 .x0 52)
  dwords : PairsAt (site.stub+4) 4 8 site.source 0 site.destOffset
  dwordsBack : Decodes (site.stub+12) (.JAL .x0
    (BitVec.ofNat 21 (2^21+4*(site.start+32)-4*(site.stub+12))))
  words : PairsAt (site.stub+16) 8 4 site.source 0 site.destOffset
  wordsBack : Decodes (site.stub+32) (.JAL .x0
    (BitVec.ofNat 21 (2^21+4*(site.start+32)-4*(site.stub+32))))
  shiftedBack : Decodes (site.start+26) (.JAL .x0 24)

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
  | .OR .. | .LUI .. | .XORI .. | .SLLI .. | .ADD .. | .SRLI .. | .LHU .. | .SH .. | .LW .. | .SW .. | .LD .. | .SD .. | .ADDI .. | .ANDI .. | .BEQ .. | .BNE .. | .JAL .. | .JALR .. => true
  | _ => false

theorem run_step (s : MachineState) (word : Nat) (i : Instr) (bounded : word < 7872)
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

theorem mem_setReg' (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl

private theorem setMem_congr {a b : MachineState} (same : a.mem = b.mem) (q v : Word) :
    (a.setMem q v).mem = (b.setMem q v).mem := by
  simp only [MachineState.setMem, same]

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
    ∀ (n j : Nat) (s : MachineState), PairsAt word (j+n) width src load store → word+2*(j+n) ≤ 7872 →
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

theorem ofNat_step (a b : Nat) : BitVec.ofNat 64 (4096+4*a) + BitVec.ofNat 64 (4*b) = BitVec.ofNat 64 (4096+4*(a+b)) := by
  rw [← BitVec.ofNat_add]; congr 1; omega

theorem ofNat_four (a : Nat) : BitVec.ofNat 64 (4096+4*a) + 4 = BitVec.ofNat 64 (4096+4*(a+1)) := by
  rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, ← BitVec.ofNat_add]; congr 1

end TwoPermutationPrototype.GroupedOpening
