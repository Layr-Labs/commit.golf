import CommitGolfCandidate.MoonOpenBase

/-! Universal parameterized block execution lemmas (`dwords`, `copy30`, `copy29`, negative-counter
`tailMerge` and `tailPush6`) shared across `rec_r0..r7`, `slow_mid`, `slow_tail`, `copy*`
subroutines, and `cap_pass`. -/
namespace CommitGolfCandidate.MoonOpen
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.MoonOpenCode

attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setPC
  MachineState.getMem_setPC MachineState.getMem_setReg getReg_setMem getReg_setByte getReg_setWord32

/-! ### 1. Tail-Buffer Write Framing & Byte-Slice Helpers -/

/-- Writes restricted to the scratch tail buffer `[tailBufBase, 68719475936)`. -/
def TailWritePreserves (s s' : MachineState) : Prop :=
  ∀ a : Word, ¬ (tailBufBase ≤ a.toNat ∧ a.toNat < 68719475936) → s'.getMem a = s.getMem a

theorem TailWritePreserves.refl (s : MachineState) : TailWritePreserves s s :=
  fun _ _ => rfl

theorem TailWritePreserves.setMem_tail {s : MachineState} {addr : Nat} {v : Word}
    (hlo : tailBufBase ≤ addr) (hhi : addr < 68719475936) (hal : addr % 8 = 0) :
    TailWritePreserves s (s.setMem (BitVec.ofNat 64 addr) v) := by
  intro a ha
  have hne : a ≠ BitVec.ofNat 64 addr := by
    intro heq; apply ha
    rw [heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold tailBufBase at hlo; omega)]
    exact ⟨hlo, hhi⟩
  exact MachineState.getMem_setMem_ne hne

theorem writerState_of_tailWrite {clean : Prop} {s s' : MachineState}
    {r : Fin 8} {flushedR4 : Bool} {base dstOff : Nat} {written : List Byte}
    (hw : WriterState clean s r flushedR4 base dstOff written)
    (htw : TailWritePreserves s s')
    (hx25 : s'.getReg .x25 = s.getReg .x25)
    (hx12 : s'.getReg .x12 = s.getReg .x12) :
    WriterState clean s' r flushedR4 base dstOff written := by
  have hbyte : ∀ q < 8556390424,
      s'.getByte (BitVec.ofNat 64 (11341403200 + q)) = s.getByte (BitVec.ofNat 64 (11341403200 + q)) := by
    intro q hq
    simp only [MachineState.getByte]
    congr 1
    apply htw
    have hal := alignToDword_ofNat_eq (8 * ((11341403200 + q) / 8)) ((11341403200 + q) % 8) (by omega) (by omega)
    rw [show 8 * ((11341403200 + q) / 8) + (11341403200 + q) % 8 = 11341403200 + q by omega] at hal
    rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    unfold tailBufBase; omega
  have hbd := hw.hbound
  have hrv_lt := r.isLt
  refine ⟨hw.hbase8, hw.hdst8, hw.hlen, hw.hbound, hx25.trans hw.rx25, hw.hflushed_ok,
    fun hcl j hj => by rw [hbyte j (by omega)]; exact hw.hbytes hcl j hj,
    fun hcl => ?_⟩
  have hrem := hw.hrem hcl
  cases flushedR4 with
  | true =>
    simp only [↓reduceIte] at hrem ⊢
    intro j hj
    have hq := hbyte (base + dstOff + j) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at hq
    exact hq.trans (hrem j hj)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hrem ⊢
    by_cases hr0 : r.val = 0
    · simp only [hr0, ↓reduceIte]
    · simp only [hr0, ↓reduceIte] at hrem ⊢
      simpa only [hx12] using hrem

theorem readOnlyPreserved_of_tailWrite {s0 s s' : MachineState}
    (hro : ReadOnlyPreserved s0 s) (htw : TailWritePreserves s s') :
    ReadOnlyPreserved s0 s' := by
  intro a ha
  have hnot : ¬ (tailBufBase ≤ a.toNat ∧ a.toNat < 68719475936) := by
    unfold tailBufBase; omega
  exact (htw a hnot).trans (hro a ha)

def bytesOfWord (w : Word) : List Byte :=
  (List.range 8).map fun j => w.extractLsb' (8 * j) 8

theorem bytesOfWord_length (w : Word) : (bytesOfWord w).length = 8 := by
  simp [bytesOfWord]

theorem bytesOfWord_getElem (w : Word) (j : Nat) (hj : j < 8) :
    (bytesOfWord w)[j]'(by simp [bytesOfWord]; exact hj) = w.extractLsb' (8 * j) 8 := by
  simp [bytesOfWord]

theorem bitsToBytes_take_dwords {w : Nat} (v : BitVec w) (k : Nat) :
    bitsToBytes v (8 * k) =
      (List.range k).flatMap (fun i => bytesOfWord (v.extractLsb' (64 * i) 64)) := by
  induction k with
  | zero => simp [bitsToBytes]
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      ← ih]
    apply List.ext_getElem
    · simp [bitsToBytes, bytesOfWord]; omega
    · intro j hj1 hj2
      simp only [bitsToBytes, List.length_map, List.length_range, List.getElem_map, List.getElem_range] at hj1 ⊢
      by_cases hlt : j < 8 * k
      · rw [List.getElem_append_left (by simp [bitsToBytes]; exact hlt)]
        simp [bitsToBytes]
      · rw [List.getElem_append_right (by simp [bitsToBytes]; omega)]
        simp only [bitsToBytes, List.length_map, List.length_range, bytesOfWord,
          List.getElem_map, List.getElem_range]
        rw [extractLsb'_extractLsb' _ _ _ _ _ (by omega)]
        congr 1; omega

theorem bitsToBytes_24_append (d : Digest) (m : Nat) (hm : m ≤ 8) :
    bitsToBytes d 24 ++ (List.range m).map (fun j => (d.extractLsb' 192 64).extractLsb' (8 * j) 8) =
      bitsToBytes d (24 + m) := by
  apply List.ext_getElem
  · simp [bitsToBytes]
  · intro j hj1 hj2
    simp only [bitsToBytes, List.length_map, List.length_range] at hj2
    by_cases hlt : j < 24
    · rw [List.getElem_append_left (by simp [bitsToBytes]; exact hlt)]
      simp [bitsToBytes]
    · rw [List.getElem_append_right (by simp [bitsToBytes]; omega)]
      simp only [bitsToBytes, List.length_map, List.length_range, List.getElem_map, List.getElem_range]
      rw [extractLsb'_extractLsb' _ _ _ _ _ (by omega)]
      congr 1; omega

theorem getMem_of_bytes_eq {w : Nat} {s : MachineState} {addr k : Nat} {v : BitVec w}
    (hal : addr % 8 = 0)
    (hbytes : ∀ j < 8, s.getByte (BitVec.ofNat 64 (addr + 8 * k + j)) = v.extractLsb' (8 * (8 * k + j)) 8) :
    s.getMem (BitVec.ofNat 64 (addr + 8 * k)) = v.extractLsb' (64 * k) 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  have hj : b / 8 < 8 := by omega
  have hbi : b % 8 < 8 := by omega
  have hm := congrArg (fun x : Byte => x.getLsbD (b % 8))
    (getMem_extractByte (s := s) (addr := addr + 8 * k) (j := b / 8) (by omega) hj)
  rw [hbytes (b / 8) hj] at hm
  simp only [BitVec.getLsbD_extractLsb', hbi, decide_true, Bool.true_and] at hm
  rw [show 8 * (b / 8) + b % 8 = b by omega] at hm
  rw [hm]
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and]
  congr 1; omega

/-! ### 2. Universal 1-Dword and Multi-Dword Copy Lemmas (`dwordsCode`) -/

def dwordOneCode (r : Fin 8) (srcReg : Reg) (srcOff dstOff : Nat)
    (flushedR4 keepR4 : Bool) : List Instruction :=
  match r.val with
  | 0 =>
    [.base (.LD .x5 srcReg (BitVec.ofNat 12 srcOff)),
     .base (.SD .x25 .x5 (BitVec.ofNat 12 dstOff))]
  | 4 =>
    (if flushedR4 then [] else [.base (.SW .x25 .x12 (BitVec.ofNat 12 dstOff))]) ++
    [.base (.LD .x5 srcReg (BitVec.ofNat 12 srcOff)),
     .base (.SW .x25 .x5 (BitVec.ofNat 12 (dstOff + 4)))] ++
    (if keepR4 then
      [.base (.SRLI .x5 .x5 (32#6)),
       .base (.SW .x25 .x5 (BitVec.ofNat 12 (dstOff + 8)))]
     else
      [.base (.SRLI .x12 .x5 (32#6))])
  | rv =>
    [.base (.LD .x5 srcReg (BitVec.ofNat 12 srcOff)),
     .base (.SLLI .x6 .x5 (BitVec.ofNat 6 (8 * rv))),
     .base (.OR .x12 .x12 .x6),
     .base (.SD .x25 .x12 (BitVec.ofNat 12 dstOff)),
     .base (.SRLI .x12 .x5 (BitVec.ofNat 6 (64 - 8 * rv)))]

def dwordsCode (r : Fin 8) : Nat → Reg → Nat → Nat → Bool → Bool → List Instruction
  | 0, _, _, _, _, _ => []
  | 1, srcReg, srcOff, dstOff, flushedR4, keepR4 =>
      dwordOneCode r srcReg srcOff dstOff flushedR4 keepR4
  | k + 2, srcReg, srcOff, dstOff, flushedR4, keepR4 =>
      dwordOneCode r srcReg srcOff dstOff flushedR4 true ++
      dwordsCode r (k + 1) srcReg (srcOff + 8) (dstOff + 8) (r.val == 4) keepR4

private theorem truncate32_extract_byte (w : Word) (j : Nat) (hj : j < 4) :
    (w.truncate 32).extractLsb' (8 * j) 8 = w.extractLsb' (8 * j) 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro b hb
  simp [BitVec.truncate, hb, show 8 * j + b < 32 by omega]

private theorem ushr32_truncate32_extract_byte (w : Word) (j : Nat) (hj : j < 4) :
    ((w >>> 32).truncate 32).extractLsb' (8 * j) 8 = w.extractLsb' (8 * (j + 4)) 8 := by
  rw [truncate32_extract_byte _ j hj]
  have h := word_ushr_byte w 4 (by omega) j (by omega)
  simpa only [show 8 * 4 = 32 from rfl, show j + 4 < 8 by omega, ↓reduceIte] using h

/-- Step one aligned 8-byte dword through `dwordOneCode` at ANY residue `r : Fin 8`. -/
theorem openRuns_dword_one {clean : Prop} {s : MachineState} {pc : Nat}
    {r : Fin 8} {srcReg : Reg} {srcBase srcOff base dstOff : Nat}
    {flushedR4 keepR4 : Bool} {written : List Byte} {srcVal : Word}
    (hcode : CodeAt pc (dwordOneCode r srcReg srcOff dstOff flushedR4 keepR4))
    (hpc : s.pc = pcAt pc)
    (hsrc_ne : srcReg ≠ .x5 ∧ srcReg ≠ .x6 ∧ srcReg ≠ .x12 ∧ srcReg ≠ .x25)
    (hsrc_reg : s.getReg srcReg = BitVec.ofNat 64 srcBase)
    (hsrc_al : (srcBase + srcOff) % 8 = 0)
    (hsrc_off : srcOff < 2048)
    (hsrc_bd : srcBase + srcOff + 8 ≤ 11341403200)
    (hsrc_mem : clean → s.getMem (BitVec.ofNat 64 (srcBase + srcOff)) = srcVal)
    (hdst_off : dstOff + 8 < 2048)
    (hdst_bd : base + dstOff + 16 ≤ 8556390424)
    (hw : WriterState clean s r flushedR4 base dstOff written) :
    ∃ s' : MachineState,
      OpenRuns s (dwordOneCode r srcReg srcOff dstOff flushedR4 keepR4).length
        (dwordOneCode r srcReg srcOff dstOff flushedR4 keepR4).length s' ∧
      s'.pc = pcAt (pc + (dwordOneCode r srcReg srcOff dstOff flushedR4 keepR4).length) ∧
      RegsEqExcept [.x5, .x6, .x12] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState clean s' r (r.val == 4 && keepR4) base (dstOff + 8) (written ++ bytesOfWord srcVal) := by
  have hbase8 := hw.hbase8
  have hdst8 := hw.hdst8
  have hrx25 := hw.rx25
  rcases r with ⟨rv, hrv⟩
  have hlen : written.length = base + dstOff + rv := hw.hlen
  have hsrc_valid : accessValid (BitVec.ofNat 64 srcBase + signExtend12 (BitVec.ofNat 12 srcOff)) 8 = true := by
    rw [signExtend12_nonneg srcOff hsrc_off, ← BitVec.ofNat_add]
    exact accessValid_ofNat (srcBase + srcOff) 8 (by omega) hsrc_al
  have hdst0_valid8 : accessValid (BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 dstOff)) 8 = true := by
    rw [signExtend12_nonneg dstOff (by omega), ← BitVec.ofNat_add]
    exact accessValid_ofNat (11341403200 + base + dstOff) 8 (by omega) (by omega)
  have hsrc_addr : BitVec.ofNat 64 srcBase + signExtend12 (BitVec.ofNat 12 srcOff) = BitVec.ofNat 64 (srcBase + srcOff) := by
    rw [signExtend12_nonneg srcOff hsrc_off, ← BitVec.ofNat_add]
  have hdst0_addr : BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 dstOff) =
      BitVec.ofNat 64 (11341403200 + base + dstOff) := by
    rw [signExtend12_nonneg dstOff (by omega), ← BitVec.ofNat_add]
  by_cases hr0 : rv = 0
  · subst hr0
    have h0 := hcode.2 0 (by simp [dwordOneCode])
    have h1 := hcode.2 1 (by simp [dwordOneCode])
    simp only [dwordOneCode, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1
    have hcodeLen : (dwordOneCode ⟨0, hrv⟩ srcReg srcOff dstOff flushedR4 keepR4).length = 2 := by
      simp [dwordOneCode]
    have hs1 := step_LD (by have := hcode.1; rw [hcodeLen] at this; omega) hpc h0 (by rw [hsrc_reg]; exact hsrc_valid)
    set s1 := (s.setReg .x5 (s.getMem (s.getReg srcReg + signExtend12 (BitVec.ofNat 12 srcOff)))).setPC (pcAt (pc + 1))
    have hs1_x25 : s1.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by
      simp [s1, getReg_setReg_ne', hrx25]
    have hs1_x5 : s1.getReg .x5 = s.getMem (BitVec.ofNat 64 (srcBase + srcOff)) := by
      simp [s1, hsrc_reg, hsrc_addr]
    have hs2 := step_SD (s := s1) (by have := hcode.1; rw [hcodeLen] at this; omega) rfl h1 (by rw [hs1_x25]; exact hdst0_valid8)
    set s2 := (s1.setMem (s1.getReg .x25 + signExtend12 (BitVec.ofNat 12 dstOff)) (s1.getReg .x5)).setPC (pcAt (pc + 1 + 1))
    refine ⟨s2, by rw [hcodeLen]; exact hs1.trans hs2, by rw [hcodeLen]; rfl, ?_, ?_, ?_⟩
    · intro reg hreg
      have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
      simp [s2, s1, getReg_setMem, getReg_setReg_ne' .x5 reg hne5.symm]
    · intro a ha
      simp only [s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hs1_x25, hdst0_addr]
      exact ProofWritePreserves.setMem_proof (by omega) (by omega) (by omega) a ha
    · refine ⟨hbase8, by omega, by simp [bytesOfWord_length]; omega, by omega,
        by simp [s2, s1, getReg_setMem, getReg_setReg_ne', hrx25],
        fun h => by simp at h, fun hcl j hj => ?_, fun _ => by simp⟩
      simp only [s2, s1, MachineState.getByte, MachineState.getMem_setPC, hs1_x25, hdst0_addr, hs1_x5, hsrc_mem hcl]
      change (s.setMem (BitVec.ofNat 64 (11341403200 + base + dstOff)) srcVal).getByte (BitVec.ofNat 64 (11341403200 + j)) = _
      by_cases hlt : j < base + dstOff
      · rw [setMem_getByte_ofNat s (11341403200 + base + dstOff) (11341403200 + j) srcVal (by omega) (by omega) (by omega) (by omega)]
        rw [List.getElem_append_left (by omega)]
        exact hw.hbytes hcl j hlt
      · have hk : j - (base + dstOff) < 8 := by omega
        have heq : 11341403200 + j = (11341403200 + base + dstOff) + (j - (base + dstOff)) := by omega
        rw [heq, setMem_getByte_inside s (11341403200 + base + dstOff) (j - (base + dstOff)) srcVal (by omega) hk]
        rw [List.getElem_append_right (by omega)]
        have hsub : j - written.length = j - (base + dstOff) := by omega
        simp only [hsub, bytesOfWord_getElem _ _ hk]
  · by_cases hr4 : rv = 4
    · subst hr4
      have hdst0_valid4 : accessValid (BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 dstOff)) 4 = true := by
        rw [signExtend12_nonneg dstOff (by omega), ← BitVec.ofNat_add]
        exact accessValid_ofNat (11341403200 + base + dstOff) 4 (by omega) (by omega)
      have hdst4_valid4 : accessValid (BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 4))) 4 = true := by
        rw [signExtend12_nonneg (dstOff + 4) (by omega), ← BitVec.ofNat_add]
        exact accessValid_ofNat (11341403200 + base + dstOff + 4) 4 (by omega) (by omega)
      have hdst8_valid4 : accessValid (BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 8))) 4 = true := by
        rw [signExtend12_nonneg (dstOff + 8) (by omega), ← BitVec.ofNat_add]
        exact accessValid_ofNat (11341403200 + base + dstOff + 8) 4 (by omega) (by omega)
      have hdst4_addr : BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 4)) =
          BitVec.ofNat 64 (11341403200 + base + dstOff + 4) := by
        rw [signExtend12_nonneg (dstOff + 4) (by omega), ← BitVec.ofNat_add, ← Nat.add_assoc]
      have hdst8_addr : BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 8)) =
          BitVec.ofNat 64 (11341403200 + base + dstOff + 8) := by
        rw [signExtend12_nonneg (dstOff + 8) (by omega), ← BitVec.ofNat_add, ← Nat.add_assoc]
      -- Step 0: optional leading SW when flushedR4 = false
      have hpre : ∃ (preLen : Nat) (sa : MachineState),
          preLen = (if flushedR4 then 0 else 1) ∧
          OpenRuns s preLen preLen sa ∧
          sa.pc = pcAt (pc + preLen) ∧
          RegsEqExcept [] s sa ∧
          ProofWritePreserves s sa ∧
          (clean → ∀ j (hj : j < base + dstOff + 4),
            sa.getByte (BitVec.ofNat 64 (11341403200 + j)) = written[j]'(by omega)) := by
        cases hfl : flushedR4
        · have h0 : openInstr pc = .base (.SW .x25 .x12 (BitVec.ofNat 12 dstOff)) := by
            have hc := hcode.2 0 (by simp [dwordOneCode, hfl])
            simpa [dwordOneCode, hfl] using hc
          have hs0 := step_SW (by have := hcode.1; simp [dwordOneCode, hfl] at this; omega) hpc h0 (by rw [hrx25]; exact hdst0_valid4)
          set sa := (s.setWord32 (s.getReg .x25 + signExtend12 (BitVec.ofNat 12 dstOff)) ((s.getReg .x12).truncate 32)).setPC (pcAt (pc + 1))
          refine ⟨1, sa, rfl, hs0, rfl, fun reg _ => by simp [sa, getReg_setWord32], ?_, ?_⟩
          · intro a ha
            simp only [sa, MachineState.getMem_setPC, hrx25, hdst0_addr]
            exact ProofWritePreserves.setWord32_proof (by omega) (by omega) (by omega) a ha
          · intro hcl j hj
            simp only [sa, getByte_setPC, hrx25, hdst0_addr]
            rw [setWord32_getByte_ofNat s (11341403200 + base + dstOff) (11341403200 + j) _ (by omega) (by omega) (by omega)]
            split_ifs with hin
            · have hrem := hw.hrem hcl
              simp only [hfl, Bool.false_eq_true, ↓reduceIte, show ¬ ((4 : Nat) = 0) by omega] at hrem
              have hk : j - (base + dstOff) < 4 := by omega
              have hsub : 11341403200 + j - (11341403200 + base + dstOff) = j - (base + dstOff) := by omega
              rw [hsub, truncate32_extract_byte _ _ hk, hrem.1 (j - (base + dstOff)) hk]
              congr 1; omega
            · exact hw.hbytes hcl j (by omega)
        · refine ⟨0, s, rfl, OpenRuns.refl s, by simpa using hpc, fun _ _ => rfl, ProofWritePreserves.refl s, ?_⟩
          intro hcl j hj
          by_cases hlt : j < base + dstOff
          · exact hw.hbytes hcl j hlt
          · have hrem := hw.hrem hcl
            simp only [hfl, ↓reduceIte] at hrem
            have hk : j - (base + dstOff) < 4 := by omega
            have h1 := hrem (j - (base + dstOff)) hk
            simpa only [show 11341403200 + base + dstOff + (j - (base + dstOff)) = 11341403200 + j by omega,
              show base + dstOff + (j - (base + dstOff)) = j by omega] using h1
      obtain ⟨preLen, sa, hpreLen, hra, hpca, hregsa, hpa, hbytesa⟩ := hpre
      -- Step 1 & 2: LD x5, srcOff(srcReg); SW x25, x5, dstOff + 4
      have hcodeMid : openInstr (pc + preLen) = .base (.LD .x5 srcReg (BitVec.ofNat 12 srcOff)) ∧
          openInstr (pc + preLen + 1) = .base (.SW .x25 .x5 (BitVec.ofNat 12 (dstOff + 4))) := by
        cases hfl : flushedR4 <;> subst hpreLen <;>
        · constructor
          · have hc := hcode.2 (if flushedR4 then 0 else 1) (by cases keepR4 <;> simp [dwordOneCode, hfl])
            simpa [dwordOneCode, hfl] using hc
          · have hc := hcode.2 ((if flushedR4 then 0 else 1) + 1) (by cases keepR4 <;> simp [dwordOneCode, hfl])
            simpa [dwordOneCode, hfl, Nat.add_assoc] using hc
      have hsa_src : sa.getReg srcReg = BitVec.ofNat 64 srcBase := (hregsa srcReg (by simp)).trans hsrc_reg
      have hsa_x25 : sa.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := (hregsa .x25 (by simp)).trans hrx25
      have hmid_lt : pc + preLen + 1 < OPEN_CODE_LEN := by
        have := hcode.1; cases hfl : flushedR4 <;> cases hkp : keepR4 <;> simp [dwordOneCode, hfl, hkp] at this hpreLen <;> omega
      have hs1 := step_LD (by omega) hpca hcodeMid.1 (by rw [hsa_src]; exact hsrc_valid)
      set s1 := (sa.setReg .x5 (sa.getMem (sa.getReg srcReg + signExtend12 (BitVec.ofNat 12 srcOff)))).setPC (pcAt (pc + preLen + 1))
      have hs1_x25 : s1.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by
        simp [s1, getReg_setReg_ne', hsa_x25]
      have hsa_srcMem : clean → sa.getMem (BitVec.ofNat 64 (srcBase + srcOff)) = srcVal := by
        intro hcl
        have hnot : ¬ (11341403200 ≤ (BitVec.ofNat 64 (srcBase + srcOff)).toNat ∧
            (BitVec.ofNat 64 (srcBase + srcOff)).toNat < 19897793624) := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
        exact (hpa _ hnot).trans (hsrc_mem hcl)
      have hs1_x5 : clean → s1.getReg .x5 = srcVal := by
        intro hcl; simp [s1, hsa_src, hsrc_addr, hsa_srcMem hcl]
      have hs2 := step_SW (s := s1) hmid_lt rfl hcodeMid.2 (by rw [hs1_x25]; exact hdst4_valid4)
      set s2 := (s1.setWord32 (s1.getReg .x25 + signExtend12 (BitVec.ofNat 12 (dstOff + 4))) ((s1.getReg .x5).truncate 32)).setPC (pcAt (pc + preLen + 1 + 1))
      have hp2 : ProofWritePreserves s s2 := by
        refine hpa.trans ?_
        intro a ha
        simp only [s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hs1_x25, hdst4_addr]
        exact ProofWritePreserves.setWord32_proof (by omega) (by omega) (by omega) a ha
      have hlen4 : written.length = base + dstOff + 4 := hlen
      have hbytes2 : clean → ∀ j (hj : j < base + (dstOff + 8)),
          s2.getByte (BitVec.ofNat 64 (11341403200 + j)) = (written ++ bytesOfWord srcVal)[j]'(by simp [bytesOfWord_length]; omega) := by
        intro hcl j hj
        simp only [s2, getByte_setPC, hs1_x25, hdst4_addr, hs1_x5 hcl]
        rw [setWord32_getByte_ofNat s1 (11341403200 + base + dstOff + 4) (11341403200 + j) _ (by omega) (by omega) (by omega)]
        split_ifs with hin
        · have hk : j - (base + dstOff + 4) < 4 := by omega
          have hsub : 11341403200 + j - (11341403200 + base + dstOff + 4) = j - (base + dstOff + 4) := by omega
          rw [hsub, truncate32_extract_byte _ _ hk, List.getElem_append_right (by omega), bytesOfWord_getElem _ _ (by omega)]
          congr 1; omega
        · simp only [s1, getByte_setPC, getByte_setReg]
          rw [List.getElem_append_left (by omega)]
          exact hbytesa hcl j (by omega)
      -- Step 3 (and 4 if keepR4 = true): SRLI + optional SW
      cases hkp : keepR4
      · -- keepR4 = false: SRLI x12, x5, 32
        have hlen_eq : (dwordOneCode ⟨4, hrv⟩ srcReg srcOff dstOff flushedR4 false).length = preLen + 3 := by
          cases hfl : flushedR4 <;> simp [dwordOneCode, hfl, hpreLen]
        have hlast : openInstr (pc + preLen + 1 + 1) = .base (.SRLI .x12 .x5 (32#6)) := by
          cases hfl : flushedR4 <;> subst hpreLen <;>
          · have hc := hcode.2 ((if flushedR4 then 0 else 1) + 2) (by simp [dwordOneCode, hfl, hkp])
            simpa [dwordOneCode, hfl, hkp, Nat.add_assoc] using hc
        have hs3 := step_SRLI (s := s2) (by have := hcode.1; rw [hkp, hlen_eq] at this; omega) rfl hlast
        set s3 := (s2.setReg .x12 (s2.getReg .x5 >>> (32#6).toNat)).setPC (pcAt (pc + preLen + 1 + 1 + 1))
        refine ⟨s3, by rw [hlen_eq]; simpa [Nat.add_assoc] using (hra.trans hs1).trans (hs2.trans hs3),
          by rw [hlen_eq]; congr 1, ?_, ?_, ?_⟩
        · intro reg hreg
          have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
          have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
          simp [s3, s2, s1, getReg_setWord32, getReg_setReg_ne' .x12 reg hne12.symm,
            getReg_setReg_ne' .x5 reg hne5.symm, hregsa reg (by simp)]
        · intro a ha; simp only [s3, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hp2 a ha
        · refine ⟨hbase8, by omega, by simp [bytesOfWord_length]; omega, by omega,
            by simp [s3, s2, s1, getReg_setWord32, getReg_setReg_ne', hsa_x25],
            fun h => by simp at h,
            fun hcl j hj => by simp only [s3, getByte_setPC, getByte_setReg]; exact hbytes2 hcl j hj,
            fun hcl => ?_⟩
          simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte, show ¬ ((4 : Nat) = 0) by omega]
          have hs3_x12 : s3.getReg .x12 = srcVal >>> 32 := by
            simp [s3, s2, getReg_setWord32, hs1_x5 hcl]
          refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
          · rw [hs3_x12]
            have hb := word_ushr_byte srcVal 4 (by omega) j (by omega)
            rw [show 8 * 4 = 32 from rfl, if_pos (by omega)] at hb
            rw [hb, List.getElem_append_right (by omega), bytesOfWord_getElem _ _ (by omega)]
            congr 1; omega
          · rw [hs3_x12]
            have hb := word_ushr_byte srcVal 4 (by omega) j hj2
            simpa only [show 8 * 4 = 32 from rfl, show ¬ (j + 4 < 8) by omega, ↓reduceIte] using hb
      · -- keepR4 = true: SRLI x5, x5, 32; SW x25, x5, dstOff + 8
        have hlen_eq : (dwordOneCode ⟨4, hrv⟩ srcReg srcOff dstOff flushedR4 true).length = preLen + 4 := by
          cases hfl : flushedR4 <;> simp [dwordOneCode, hfl, hpreLen]
        have hlast1 : openInstr (pc + preLen + 1 + 1) = .base (.SRLI .x5 .x5 (32#6)) := by
          cases hfl : flushedR4 <;> subst hpreLen <;>
          · have hc := hcode.2 ((if flushedR4 then 0 else 1) + 2) (by simp [dwordOneCode, hfl, hkp])
            simpa [dwordOneCode, hfl, hkp, Nat.add_assoc] using hc
        have hlast2 : openInstr (pc + preLen + 1 + 1 + 1) = .base (.SW .x25 .x5 (BitVec.ofNat 12 (dstOff + 8))) := by
          cases hfl : flushedR4 <;> subst hpreLen <;>
          · have hc := hcode.2 ((if flushedR4 then 0 else 1) + 3) (by simp [dwordOneCode, hfl, hkp])
            simpa [dwordOneCode, hfl, hkp, Nat.add_assoc] using hc
        have hs3 := step_SRLI (s := s2) (by have := hcode.1; rw [hkp, hlen_eq] at this; omega) rfl hlast1
        set s3 := (s2.setReg .x5 (s2.getReg .x5 >>> (32#6).toNat)).setPC (pcAt (pc + preLen + 1 + 1 + 1))
        have hs3_x25 : s3.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by
          simp [s3, s2, getReg_setWord32, getReg_setReg_ne', hs1_x25]
        have hs4 := step_SW (s := s3) (by have := hcode.1; rw [hkp, hlen_eq] at this; omega) rfl hlast2 (by rw [hs3_x25]; exact hdst8_valid4)
        set s4 := (s3.setWord32 (s3.getReg .x25 + signExtend12 (BitVec.ofNat 12 (dstOff + 8))) ((s3.getReg .x5).truncate 32)).setPC (pcAt (pc + preLen + 1 + 1 + 1 + 1))
        refine ⟨s4, by rw [hlen_eq]; simpa [Nat.add_assoc] using ((hra.trans hs1).trans (hs2.trans hs3)).trans hs4,
          by rw [hlen_eq]; congr 1, ?_, ?_, ?_⟩
        · intro reg hreg
          have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
          simp [s4, s3, s2, s1, getReg_setWord32, getReg_setReg_ne' .x5 reg hne5.symm, hregsa reg (by simp)]
        · refine hp2.trans ?_
          intro a ha
          simp only [s4, s3, MachineState.getMem_setPC, MachineState.getMem_setReg, hs3_x25, hdst8_addr]
          exact ProofWritePreserves.setWord32_proof (by omega) (by omega) (by omega) a ha
        · refine ⟨hbase8, by omega, by simp [bytesOfWord_length]; omega, by omega,
            by simp [s4, s3, s2, s1, getReg_setWord32, getReg_setReg_ne', hsa_x25],
            fun _ => rfl, fun hcl j hj => ?_, fun hcl => ?_⟩
          · simp only [s4, getByte_setPC, hs3_x25, hdst8_addr]
            rw [setWord32_getByte_ofNat s3 (11341403200 + base + dstOff + 8) (11341403200 + j) _ (by omega) (by omega) (by omega)]
            rw [dif_neg (by omega)]
            simp only [s3, getByte_setPC, getByte_setReg]
            exact hbytes2 hcl j hj
          · simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
            intro j hj
            simp only [s4, getByte_setPC, hs3_x25, hdst8_addr]
            have hadd : 11341403200 + base + (dstOff + 8) + j = 11341403200 + (base + dstOff + 8 + j) := by omega
            rw [hadd, setWord32_getByte_ofNat s3 (11341403200 + base + dstOff + 8) (11341403200 + (base + dstOff + 8 + j)) _ (by omega) (by omega) (by omega)]
            rw [dif_pos (by omega)]
            have hs3_x5 : s3.getReg .x5 = srcVal >>> 32 := by simp [s3, s2, getReg_setWord32, hs1_x5 hcl]
            rw [hs3_x5, show 11341403200 + (base + dstOff + 8 + j) - (11341403200 + base + dstOff + 8) = j by omega,
              ushr32_truncate32_extract_byte srcVal j hj, List.getElem_append_right (by omega), bytesOfWord_getElem _ _ (by omega)]
            congr 1; omega
    · -- General r ∈ {1, 2, 3, 5, 6, 7}: 5-instruction pipeline
      have hfl_false : flushedR4 = false := by
        cases hf : flushedR4
        · rfl
        · exact absurd (hw.hflushed_ok hf) hr4
      subst hfl_false
      have hlen_rv : written.length = base + dstOff + rv := hlen
      have hcode_eq : dwordOneCode ⟨rv, hrv⟩ srcReg srcOff dstOff false keepR4 =
          [.base (.LD .x5 srcReg (BitVec.ofNat 12 srcOff)),
           .base (.SLLI .x6 .x5 (BitVec.ofNat 6 (8 * rv))),
           .base (.OR .x12 .x12 .x6),
           .base (.SD .x25 .x12 (BitVec.ofNat 12 dstOff)),
           .base (.SRLI .x12 .x5 (BitVec.ofNat 6 (64 - 8 * rv)))] := by
        have hcs : rv = 1 ∨ rv = 2 ∨ rv = 3 ∨ rv = 5 ∨ rv = 6 ∨ rv = 7 := by omega
        rcases hcs with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      have hcodeLen : (dwordOneCode ⟨rv, hrv⟩ srcReg srcOff dstOff false keepR4).length = 5 := by
        rw [hcode_eq]; rfl
      have hi0 : openInstr pc = .base (.LD .x5 srcReg (BitVec.ofNat 12 srcOff)) := by
        have h := hcode.2 0 (by rw [hcodeLen]; omega); simp only [hcode_eq, Nat.add_zero] at h; exact h
      have hi1 : openInstr (pc + 1) = .base (.SLLI .x6 .x5 (BitVec.ofNat 6 (8 * rv))) := by
        have h := hcode.2 1 (by rw [hcodeLen]; omega); simp only [hcode_eq] at h; exact h
      have hi2 : openInstr (pc + 2) = .base (.OR .x12 .x12 .x6) := by
        have h := hcode.2 2 (by rw [hcodeLen]; omega); simp only [hcode_eq] at h; exact h
      have hi3 : openInstr (pc + 3) = .base (.SD .x25 .x12 (BitVec.ofNat 12 dstOff)) := by
        have h := hcode.2 3 (by rw [hcodeLen]; omega); simp only [hcode_eq] at h; exact h
      have hi4 : openInstr (pc + 4) = .base (.SRLI .x12 .x5 (BitVec.ofNat 6 (64 - 8 * rv))) := by
        have h := hcode.2 4 (by rw [hcodeLen]; omega); simp only [hcode_eq] at h; exact h
      have hpc_bd : pc + 5 ≤ OPEN_CODE_LEN := by have := hcode.1; rw [hcodeLen] at this; exact this
      have hs1 := step_LD (by omega) hpc hi0 (by rw [hsrc_reg]; exact hsrc_valid)
      set s1 := (s.setReg .x5 (s.getMem (s.getReg srcReg + signExtend12 (BitVec.ofNat 12 srcOff)))).setPC (pcAt (pc + 1))
      have hs2 := step_SLLI (s := s1) (by omega) rfl hi1
      set s2 := (s1.setReg .x6 (s1.getReg .x5 <<< (BitVec.ofNat 6 (8 * rv)).toNat)).setPC (pcAt (pc + 1 + 1))
      have hs3 := step_OR (s := s2) (by omega) (by congr 1) hi2
      set s3 := (s2.setReg .x12 (s2.getReg .x12 ||| s2.getReg .x6)).setPC (pcAt (pc + 2 + 1))
      have hs3_x25 : s3.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by
        simp [s3, s2, s1, getReg_setReg_ne', hrx25]
      have hs4 := step_SD (s := s3) (by omega) (by congr 1) hi3 (by rw [hs3_x25]; exact hdst0_valid8)
      set s4 := (s3.setMem (s3.getReg .x25 + signExtend12 (BitVec.ofNat 12 dstOff)) (s3.getReg .x12)).setPC (pcAt (pc + 3 + 1))
      have hs5 := step_SRLI (s := s4) (by omega) (by congr 1) hi4
      set s5 := (s4.setReg .x12 (s4.getReg .x5 >>> (BitVec.ofNat 6 (64 - 8 * rv)).toNat)).setPC (pcAt (pc + 4 + 1))
      have hshL : (BitVec.ofNat 6 (8 * rv)).toNat = 8 * rv := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hshR : (BitVec.ofNat 6 (64 - 8 * rv)).toNat = 64 - 8 * rv := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hs1_x5 : clean → s1.getReg .x5 = srcVal := by
        intro hcl; simp [s1, hsrc_reg, hsrc_addr, hsrc_mem hcl]
      have hs3_x12 : clean → s3.getReg .x12 = s.getReg .x12 ||| (srcVal <<< (8 * rv)) := by
        intro hcl; simp [s3, s2, s1, getReg_setReg_ne', hs1_x5 hcl, hshL]
      have hs5_x12 : clean → s5.getReg .x12 = srcVal >>> (8 * (8 - rv)) := by
        intro hcl
        have h5 : s4.getReg .x5 = srcVal := by simp [s4, s3, s2, getReg_setReg_ne', hs1_x5 hcl]
        simp only [s5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
          h5, hshR]
        congr 1; omega
      have hbeq4 : (rv == 4) = false := by simp [hr4]
      refine ⟨s5, by rw [hcodeLen]; exact (((hs1.trans hs2).trans hs3).trans hs4).trans hs5,
        by rw [hcodeLen]; congr 1, ?_, ?_, ?_⟩
      · intro reg hreg
        have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
        have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
        have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
        simp [s5, s4, s3, s2, s1, getReg_setMem, getReg_setReg_ne' .x12 reg hne12.symm,
          getReg_setReg_ne' .x6 reg hne6.symm, getReg_setReg_ne' .x5 reg hne5.symm]
      · intro a ha
        simp only [s5, s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hs3_x25, hdst0_addr]
        exact ProofWritePreserves.setMem_proof (by omega) (by omega) (by omega) a ha
      · refine ⟨hbase8, by omega, by simp [bytesOfWord_length]; omega, by omega,
          by simp [s5, s4, s3, s2, s1, getReg_setMem, getReg_setReg_ne', hrx25],
          by simp [hbeq4], fun hcl j hj => ?_, fun hcl => ?_⟩
        · have hrem := hw.hrem hcl
          simp only [Bool.false_eq_true, ↓reduceIte, hr0] at hrem
          simp only [s5, s4, getByte_setPC, getByte_setReg, hs3_x25, hdst0_addr, hs3_x12 hcl]
          change (s.setMem (BitVec.ofNat 64 (11341403200 + base + dstOff)) (s.getReg .x12 ||| (srcVal <<< (8 * rv)))).getByte (BitVec.ofNat 64 (11341403200 + j)) = _
          by_cases hlt : j < base + dstOff
          · rw [setMem_getByte_ofNat s (11341403200 + base + dstOff) (11341403200 + j) _ (by omega) (by omega) (by omega) (by omega)]
            rw [List.getElem_append_left (by omega)]
            exact hw.hbytes hcl j hlt
          · have hk : j - (base + dstOff) < 8 := by omega
            have heq : 11341403200 + j = (11341403200 + base + dstOff) + (j - (base + dstOff)) := by omega
            rw [heq, setMem_getByte_inside s (11341403200 + base + dstOff) (j - (base + dstOff)) _ (by omega) hk]
            rw [word_or_shl_byte (s.getReg .x12) srcVal rv hrv hrem.2 (j - (base + dstOff)) hk]
            split_ifs with hkr
            · rw [hrem.1 (j - (base + dstOff)) hkr, List.getElem_append_left (by omega)]
              congr 1; omega
            · rw [List.getElem_append_right (by omega), bytesOfWord_getElem _ _ (by omega)]
              congr 1; omega
        · simp only [hbeq4, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hr0]
          refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
          · rw [hs5_x12 hcl, word_ushr_byte srcVal (8 - rv) (by omega) j (by omega), if_pos (by omega)]
            rw [List.getElem_append_right (by omega), bytesOfWord_getElem _ _ (by omega)]
            congr 1; omega
          · rw [hs5_x12 hcl, word_ushr_byte srcVal (8 - rv) (by omega) j hj2, if_neg (by omega)]

/-- Step `count` consecutive aligned 8-byte dwords through `dwordsCode` at ANY residue `r : Fin 8`. -/
theorem openRuns_dwords {clean : Prop} {r : Fin 8} :
    ∀ (count : Nat) {s : MachineState} {pc : Nat} {srcReg : Reg}
      {srcBase srcOff base dstOff : Nat} {flushedR4 keepR4 : Bool}
      {written : List Byte} {vals : Nat → Word},
      0 < count →
      CodeAt pc (dwordsCode r count srcReg srcOff dstOff flushedR4 keepR4) →
      s.pc = pcAt pc →
      (srcReg ≠ .x5 ∧ srcReg ≠ .x6 ∧ srcReg ≠ .x12 ∧ srcReg ≠ .x25) →
      s.getReg srcReg = BitVec.ofNat 64 srcBase →
      (srcBase + srcOff) % 8 = 0 →
      srcOff + 8 * (count - 1) < 2048 →
      srcBase + srcOff + 8 * count ≤ 11341403200 →
      (clean → ∀ k < count, s.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k)) = vals k) →
      dstOff + 8 * count < 2048 →
      base + dstOff + 8 * count + 8 ≤ 8556390424 →
      WriterState clean s r flushedR4 base dstOff written →
      ∃ s' : MachineState,
        OpenRuns s (dwordsCode r count srcReg srcOff dstOff flushedR4 keepR4).length
          (dwordsCode r count srcReg srcOff dstOff flushedR4 keepR4).length s' ∧
        s'.pc = pcAt (pc + (dwordsCode r count srcReg srcOff dstOff flushedR4 keepR4).length) ∧
        RegsEqExcept [.x5, .x6, .x12] s s' ∧
        ProofWritePreserves s s' ∧
        WriterState clean s' r (r.val == 4 && keepR4) base (dstOff + 8 * count)
          (written ++ (List.range count).flatMap (fun k => bytesOfWord (vals k))) := by
  intro count
  induction count with
  | zero => intro _ _ _ _ _ _ _ _ _ _ hpos; omega
  | succ n ih =>
    cases n with
    | zero =>
      intro s pc srcReg srcBase srcOff base dstOff flushedR4 keepR4 written vals _ hcode hpc hne hreg hal hoff hbd hmem hdoff hdbd hw
      have h1 := openRuns_dword_one hcode hpc hne hreg hal (by omega) (by omega)
        (fun hcl => by simpa only [Nat.mul_zero, Nat.add_zero] using hmem hcl 0 (by omega))
        (by omega) (by omega) hw
      dsimp only [dwordsCode]
      rw [show 8 * 1 = 8 from rfl, List.range_one, List.flatMap_singleton]
      exact h1
    | succ m =>
      intro s pc srcReg srcBase srcOff base dstOff flushedR4 keepR4 written vals _ hcode hpc hne hreg hal hoff hbd hmem hdoff hdbd hw
      have hcodeL : CodeAt pc (dwordOneCode r srcReg srcOff dstOff flushedR4 true) := hcode.left
      have hcodeR : CodeAt (pc + (dwordOneCode r srcReg srcOff dstOff flushedR4 true).length)
          (dwordsCode r (m + 1) srcReg (srcOff + 8) (dstOff + 8) (r.val == 4) keepR4) := hcode.right
      obtain ⟨s1, hr1, hpc1, hregs1, hp1, hw1⟩ := openRuns_dword_one hcodeL hpc hne hreg hal
        (by omega) (by omega)
        (fun hcl => by simpa only [Nat.mul_zero, Nat.add_zero] using hmem hcl 0 (by omega))
        (by omega) (by omega) hw
      have hfl1 : (r.val == 4 && true) = (r.val == 4) := by simp
      rw [hfl1] at hw1
      have hs1_src : s1.getReg srcReg = BitVec.ofNat 64 srcBase :=
        (hregs1 srcReg (by simp [hne.1, hne.2.1, hne.2.2.1])).trans hreg
      have hs1_mem : clean → ∀ k < m + 1,
          s1.getMem (BitVec.ofNat 64 (srcBase + (srcOff + 8) + 8 * k)) = vals (k + 1) := by
        intro hcl k hk
        have hnot : ¬ (11341403200 ≤ (BitVec.ofNat 64 (srcBase + (srcOff + 8) + 8 * k)).toNat ∧
            (BitVec.ofNat 64 (srcBase + (srcOff + 8) + 8 * k)).toNat < 19897793624) := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
        rw [hp1 _ hnot, show srcBase + (srcOff + 8) + 8 * k = srcBase + srcOff + 8 * (k + 1) by omega]
        exact hmem hcl (k + 1) (by omega)
      obtain ⟨s2, hr2, hpc2, hregs2, hp2, hw2⟩ := ih (s := s1) (vals := fun k => vals (k + 1))
        (by omega) hcodeR hpc1 hne hs1_src (by omega) (by omega) (by omega) hs1_mem (by omega) (by omega) hw1
      have hlen_c : (dwordsCode r (m + 2) srcReg srcOff dstOff flushedR4 keepR4).length =
          (dwordOneCode r srcReg srcOff dstOff flushedR4 true).length +
          (dwordsCode r (m + 1) srcReg (srcOff + 8) (dstOff + 8) (r.val == 4) keepR4).length := by
        simp [dwordsCode]
      have hflat : written ++ bytesOfWord (vals 0) ++
          (List.range (m + 1)).flatMap (fun k => bytesOfWord (vals (k + 1))) =
          written ++ (List.range (m + 2)).flatMap (fun k => bytesOfWord (vals k)) := by
        rw [List.append_assoc]
        congr 1
        rw [List.range_succ_eq_map (n := m + 1), List.flatMap_cons, List.flatMap_map]
      refine ⟨s2, by rw [hlen_c]; exact hr1.trans hr2, by rw [hlen_c, ← Nat.add_assoc]; exact hpc2,
        fun reg hreg => (hregs2 reg hreg).trans (hregs1 reg hreg), hp1.trans hp2, ?_⟩
      rw [hflat, show dstOff + 8 + 8 * (m + 1) = dstOff + 8 * (m + 2) by omega] at hw2
      exact hw2

/-! ### 3. Universal 30-Byte Clean-Node Copy Lemma (`copy30Code`) -/

def copy30NextR (r : Fin 8) : Fin 8 := ⟨(r.val + 6) % 8, Nat.mod_lt _ (by omega)⟩

def copy30NextDstOff (r : Fin 8) (dstOff : Nat) : Nat :=
  if r.val < 2 then dstOff + 24 else dstOff + 32

def copy30TailCode (r : Fin 8) (srcReg : Reg) (dstOff : Nat) : List Instruction :=
  match r.val with
  | 0 => [.base (.LD .x12 srcReg (24#12))]
  | 1 => [.base (.LD .x5 srcReg (24#12)),
          .base (.SLLI .x6 .x5 (8#6)),
          .base (.OR .x12 .x12 .x6)]
  | 2 => [.base (.LD .x5 srcReg (24#12)),
          .base (.SLLI .x6 .x5 (16#6)),
          .base (.OR .x12 .x12 .x6),
          .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24)))]
  | 4 => [.base (.LD .x5 srcReg (24#12)),
          .base (.SW .x25 .x5 (BitVec.ofNat 12 (dstOff + 28))),
          .base (.SRLI .x12 .x5 (32#6))]
  | rv =>
         [.base (.LD .x5 srcReg (24#12)),
          .base (.SLLI .x6 .x5 (BitVec.ofNat 6 (8 * rv))),
          .base (.OR .x12 .x12 .x6),
          .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24))),
          .base (.SRLI .x12 .x5 (BitVec.ofNat 6 (64 - 8 * rv)))]

def copy30Code (r : Fin 8) (srcReg : Reg) (dstOff : Nat) (flushedR4 : Bool) : List Instruction :=
  dwordsCode r 3 srcReg 0 dstOff flushedR4 (r.val == 4) ++ copy30TailCode r srcReg dstOff

/-- Step a full 30-byte `mask240`-clean node through `copy30Code` at ANY residue `r : Fin 8`. -/
theorem openRuns_copy30 {clean : Prop} {s : MachineState} {pc : Nat}
    {r : Fin 8} {srcReg : Reg} {srcBase base dstOff : Nat}
    {flushedR4 : Bool} {written : List Byte} {d : Digest}
    (hcode : CodeAt pc (copy30Code r srcReg dstOff flushedR4))
    (hpc : s.pc = pcAt pc)
    (hsrc_ne : srcReg ≠ .x5 ∧ srcReg ≠ .x6 ∧ srcReg ≠ .x12 ∧ srcReg ≠ .x25)
    (hsrc_reg : s.getReg srcReg = BitVec.ofNat 64 srcBase)
    (hsrc_al : srcBase % 8 = 0)
    (hsrc_bd : srcBase + 32 ≤ 11341403200)
    (hsrc_mem : clean → ∀ k < 4, s.getMem (BitVec.ofNat 64 (srcBase + 8 * k)) = d.extractLsb' (64 * k) 64)
    (hd_clean : clean → mask240 d = d)
    (hdst_off : dstOff + 32 < 2048)
    (hdst_bd : base + dstOff + 40 ≤ 8556390424)
    (hw : WriterState clean s r flushedR4 base dstOff written) :
    ∃ s' : MachineState,
      OpenRuns s (copy30Code r srcReg dstOff flushedR4).length
        (copy30Code r srcReg dstOff flushedR4).length s' ∧
      s'.pc = pcAt (pc + (copy30Code r srcReg dstOff flushedR4).length) ∧
      RegsEqExcept [.x5, .x6, .x12] s s' ∧
      ProofWritePreserves s s' ∧
      WriterState clean s' (copy30NextR r) false base (copy30NextDstOff r dstOff)
        (written ++ bitsToBytes d 30) := by
  have hcodeL := hcode.left
  have hcodeR := hcode.right
  obtain ⟨s1, hr1, hpc1, hregs1, hp1, hw1⟩ := openRuns_dwords 3 (s := s) (vals := fun k => d.extractLsb' (64 * k) 64)
    (by omega) hcodeL hpc hsrc_ne hsrc_reg (by omega) (by omega) (by omega)
    (fun hcl k hk => by simpa only [Nat.add_zero] using hsrc_mem hcl k (by omega))
    (by omega) (by omega) hw
  have h24 : (List.range 3).flatMap (fun k => bytesOfWord (d.extractLsb' (64 * k) 64)) = bitsToBytes d 24 :=
    (bitsToBytes_take_dwords d 3).symm
  rw [h24] at hw1
  set d3 : Word := d.extractLsb' 192 64
  have h30_eq : written ++ bitsToBytes d 24 ++ (List.range 6).map (fun j => d3.extractLsb' (8 * j) 8) =
      written ++ bitsToBytes d 30 := by
    rw [List.append_assoc, bitsToBytes_24_append d 6 (by omega)]
  have hs1_src : s1.getReg srcReg = BitVec.ofNat 64 srcBase :=
    (hregs1 srcReg (by simp [hsrc_ne.1, hsrc_ne.2.1, hsrc_ne.2.2.1])).trans hsrc_reg
  have hs1_d3 : clean → s1.getMem (BitVec.ofNat 64 (srcBase + 24)) = d3 := by
    intro hcl
    have hnot : ¬ (11341403200 ≤ (BitVec.ofNat 64 (srcBase + 24)).toNat ∧
        (BitVec.ofNat 64 (srcBase + 24)).toNat < 19897793624) := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    rw [hp1 _ hnot]
    simpa only [show 8 * 3 = 24 from rfl, show 64 * 3 = 192 from rfl] using hsrc_mem hcl 3 (by omega)
  have hd3_hi : clean → ∀ j, 6 ≤ j → j < 8 → d3.extractLsb' (8 * j) 8 = 0#8 := by
    intro hcl
    refine word_clean240_hi d3 d (hd_clean hcl) (fun j hj => ?_)
    rw [extractLsb'_extractLsb' d 192 64 (8 * (6 + j)) 8 (by omega)]
    congr 1; omega
  have hsrc24_valid : accessValid (BitVec.ofNat 64 srcBase + signExtend12 (24#12)) 8 = true := by
    rw [signExtend12_nonneg 24 (by omega), ← BitVec.ofNat_add]
    exact accessValid_ofNat (srcBase + 24) 8 (by omega) (by omega)
  have hsrc24_addr : BitVec.ofNat 64 srcBase + signExtend12 (24#12) = BitVec.ofNat 64 (srcBase + 24) := by
    rw [signExtend12_nonneg 24 (by omega), ← BitVec.ofNat_add]
  set pc1 := pc + (dwordsCode r 3 srcReg 0 dstOff flushedR4 (r.val == 4)).length
  have hrx25_1 : s1.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := hw1.rx25
  have hbase8 := hw1.hbase8
  have hdst8 := hw.hdst8
  have hlen1 : (written ++ bitsToBytes d 24).length = base + (dstOff + 24) + r.val := hw1.hlen
  have hdst24_addr : BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 24)) =
      BitVec.ofNat 64 (11341403200 + base + (dstOff + 24)) := by
    rw [signExtend12_nonneg (dstOff + 24) (by omega), ← BitVec.ofNat_add]
  have hdst24_valid8 : accessValid (BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 24))) 8 = true := by
    rw [hdst24_addr]; exact accessValid_ofNat _ 8 (by omega) (by omega)
  have hdst28_addr : BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 28)) =
      BitVec.ofNat 64 (11341403200 + base + dstOff + 28) := by
    rw [signExtend12_nonneg (dstOff + 28) (by omega), ← BitVec.ofNat_add, ← Nat.add_assoc]
  have hdst28_valid4 : accessValid (BitVec.ofNat 64 (11341403200 + base) + signExtend12 (BitVec.ofNat 12 (dstOff + 28))) 4 = true := by
    rw [hdst28_addr]; exact accessValid_ofNat _ 4 (by omega) (by omega)
  have hcode_tot : (copy30Code r srcReg dstOff flushedR4).length =
      (dwordsCode r 3 srcReg 0 dstOff flushedR4 (r.val == 4)).length + (copy30TailCode r srcReg dstOff).length := by
    simp [copy30Code]
  rcases r with ⟨rv, hrv⟩
  have hlen_rv : written.length = base + dstOff + rv := hw.hlen
  have hlen1' : (written ++ bitsToBytes d 24).length = base + (dstOff + 24) + rv := hw1.hlen
  -- Helper for extracting byte j of `written ++ bitsToBytes d 30` when j >= base+dstOff+24
  have hget30_left : ∀ j (hj : j < (written ++ bitsToBytes d 24).length),
      (written ++ bitsToBytes d 30)[j]'(by simp [bitsToBytes_length] at hj ⊢; omega) =
        (written ++ bitsToBytes d 24)[j]'hj := by
    intro j hj
    have h1 : (written ++ bitsToBytes d 30)[j]'(by simp [bitsToBytes_length] at hj ⊢; omega) =
        (written ++ bitsToBytes d 24 ++ (List.range 6).map (fun j => d3.extractLsb' (8 * j) 8))[j]'(by rw [h30_eq]; simp [bitsToBytes_length] at hj ⊢; omega) := by
      revert h30_eq; generalize written ++ bitsToBytes d 24 ++ (List.range 6).map (fun j => d3.extractLsb' (8 * j) 8) = lhs; rintro rfl; rfl
    rw [h1, List.getElem_append_left hj]
  have hbyte_tail : ∀ (_ : clean) j (hj1 : base + dstOff + 24 + rv ≤ j) (hj2 : j < base + dstOff + 30 + rv),
      (written ++ bitsToBytes d 30)[j]'(by simp [bitsToBytes_length]; omega) =
        d3.extractLsb' (8 * (j - (base + dstOff + 24 + rv))) 8 := by
    intro hcl j hj1 hj2
    have h1 : (written ++ bitsToBytes d 30)[j]'(by simp [bitsToBytes_length]; omega) =
        (written ++ bitsToBytes d 24 ++ (List.range 6).map (fun j => d3.extractLsb' (8 * j) 8))[j]'(by rw [h30_eq]; simp [bitsToBytes_length]; omega) := by
      revert h30_eq; generalize written ++ bitsToBytes d 24 ++ (List.range 6).map (fun j => d3.extractLsb' (8 * j) 8) = lhs; rintro rfl; rfl
    rw [h1, List.getElem_append_right (by omega)]
    simp only [List.getElem_map, List.getElem_range]
    congr 1; omega
  -- Case split on rv = 0, 1, 2, 4, and {3, 5, 6, 7}
  by_cases hr0 : rv = 0
  · subst hr0
    have hi0 : openInstr pc1 = .base (.LD .x12 srcReg (24#12)) := by
      have h := hcodeR.2 0 (by simp [copy30TailCode]); simpa [copy30TailCode] using h
    have htlen : (copy30TailCode ⟨0, hrv⟩ srcReg dstOff).length = 1 := rfl
    have ha1 := step_LD (s := s1) (by have := hcodeR.1; rw [htlen] at this; omega) hpc1 hi0 (by rw [hs1_src]; exact hsrc24_valid)
    set s2 := (s1.setReg .x12 (s1.getMem (s1.getReg srcReg + signExtend12 (24#12)))).setPC (pcAt (pc1 + 1))
    refine ⟨s2, by rw [hcode_tot, htlen]; exact hr1.trans ha1, by rw [hcode_tot, htlen, ← Nat.add_assoc]; rfl,
      fun reg hreg => by
        have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
        exact (by simp [s2, getReg_setReg_ne' .x12 reg hne12.symm] : s2.getReg reg = s1.getReg reg).trans (hregs1 reg hreg),
      hp1.trans (fun a _ => by simp [s2]), ?_⟩
    refine ⟨hbase8, by simp [copy30NextDstOff]; omega, by simp [copy30NextR, copy30NextDstOff, bitsToBytes_length]; omega,
      by simp [copy30NextDstOff]; omega, by simp [s2, getReg_setReg_ne', hrx25_1],
      by simp, fun hcl j hj => ?_, fun hcl => ?_⟩
    · simp only [copy30NextDstOff, show (0 : Nat) < 2 by omega, ↓reduceIte] at hj
      simp only [s2, getByte_setPC, getByte_setReg]
      rw [hget30_left j (by omega)]
      exact hw1.hbytes hcl j hj
    · simp only [copy30NextR, copy30NextDstOff, show (0 : Nat) < 2 by omega, Bool.false_eq_true, ↓reduceIte,
        show ¬ (((0 + 6) % 8 : Nat) = 0) by decide]
      have hx12 : s2.getReg .x12 = d3 := by simp [s2, hs1_src, hsrc24_addr, hs1_d3 hcl]
      refine ⟨fun j hj => ?_, fun j hj1 hj2 => by rw [hx12]; exact hd3_hi hcl j hj1 hj2⟩
      rw [hx12, hbyte_tail hcl (base + (dstOff + 24) + j) (by omega) (by omega)]
      congr 1; omega
  · by_cases hrv1 : rv = 1
    · subst hrv1
      have htlen : (copy30TailCode ⟨1, hrv⟩ srcReg dstOff).length = 3 := rfl
      have hi0 : openInstr pc1 = .base (.LD .x5 srcReg (24#12)) := by
        have h := hcodeR.2 0 (by simp [copy30TailCode]); simpa [copy30TailCode] using h
      have hi1 : openInstr (pc1 + 1) = .base (.SLLI .x6 .x5 (8#6)) := by
        have h := hcodeR.2 1 (by simp [copy30TailCode]); simpa [copy30TailCode] using h
      have hi2 : openInstr (pc1 + 2) = .base (.OR .x12 .x12 .x6) := by
        have h := hcodeR.2 2 (by simp [copy30TailCode]); simpa [copy30TailCode] using h
      have hbd : pc1 + 3 ≤ OPEN_CODE_LEN := by have := hcodeR.1; rw [htlen] at this; exact this
      have ha1 := step_LD (s := s1) (by omega) hpc1 hi0 (by rw [hs1_src]; exact hsrc24_valid)
      set s2 := (s1.setReg .x5 (s1.getMem (s1.getReg srcReg + signExtend12 (24#12)))).setPC (pcAt (pc1 + 1))
      have ha2 := step_SLLI (s := s2) (by omega) rfl hi1
      set s3 := (s2.setReg .x6 (s2.getReg .x5 <<< (8#6).toNat)).setPC (pcAt (pc1 + 1 + 1))
      have ha3 := step_OR (s := s3) (by omega) (by congr 1) hi2
      set s4 := (s3.setReg .x12 (s3.getReg .x12 ||| s3.getReg .x6)).setPC (pcAt (pc1 + 2 + 1))
      refine ⟨s4, by rw [hcode_tot, htlen]; exact (hr1.trans ha1).trans (ha2.trans ha3),
        by rw [hcode_tot, htlen, ← Nat.add_assoc]; congr 1, ?_, hp1.trans (fun a _ => by simp [s4, s3, s2]), ?_⟩
      · intro reg hreg
        have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
        have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
        have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
        exact (by simp [s4, s3, s2, getReg_setReg_ne' .x12 reg hne12.symm,
          getReg_setReg_ne' .x6 reg hne6.symm, getReg_setReg_ne' .x5 reg hne5.symm] : s4.getReg reg = s1.getReg reg).trans (hregs1 reg hreg)
      · refine ⟨hbase8, by simp [copy30NextDstOff]; omega, by simp [copy30NextR, copy30NextDstOff, bitsToBytes_length]; omega,
          by simp [copy30NextDstOff]; omega, by simp [s4, s3, s2, getReg_setReg_ne', hrx25_1],
          by simp, fun hcl j hj => ?_, fun hcl => ?_⟩
        · simp only [copy30NextDstOff, show (1 : Nat) < 2 by omega, ↓reduceIte] at hj
          simp only [s4, s3, s2, getByte_setPC, getByte_setReg]
          rw [hget30_left j (by omega)]
          exact hw1.hbytes hcl j hj
        · simp only [copy30NextR, copy30NextDstOff, show (1 : Nat) < 2 by omega, Bool.false_eq_true, ↓reduceIte,
            show ¬ (((1 + 6) % 8 : Nat) = 0) by decide]
          have hrem1 := hw1.hrem hcl
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, show ¬ ((1 : Nat) = 0) by omega] at hrem1
          have hx12 : s4.getReg .x12 = s1.getReg .x12 ||| (d3 <<< (8 * 1)) := by
            simp [s4, s3, s2, getReg_setReg_ne', hs1_src, hsrc24_addr, hs1_d3 hcl]
          refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
          · rw [hx12, word_or_shl_byte (s1.getReg .x12) d3 1 (by omega) hrem1.2 j (by omega)]
            split_ifs with hj0
            · rw [hrem1.1 j hj0, hget30_left (base + (dstOff + 24) + j) (by omega)]
            · rw [hbyte_tail hcl (base + (dstOff + 24) + j) (by omega) (by omega)]; congr 1; omega
          · rw [hx12, word_or_shl_byte (s1.getReg .x12) d3 1 (by omega) hrem1.2 j hj2, if_neg (by omega)]
            exact hd3_hi hcl (j - 1) (by omega) (by omega)
    · by_cases hr2 : rv = 2
      · subst hr2
        have htlen : (copy30TailCode ⟨2, hrv⟩ srcReg dstOff).length = 4 := rfl
        have hi0 : openInstr pc1 = .base (.LD .x5 srcReg (24#12)) := by
          have h := hcodeR.2 0 (by simp [copy30TailCode]); simpa [copy30TailCode] using h
        have hi1 : openInstr (pc1 + 1) = .base (.SLLI .x6 .x5 (16#6)) := by
          have h := hcodeR.2 1 (by simp [copy30TailCode]); simpa [copy30TailCode] using h
        have hi2 : openInstr (pc1 + 2) = .base (.OR .x12 .x12 .x6) := by
          have h := hcodeR.2 2 (by simp [copy30TailCode]); simpa [copy30TailCode] using h
        have hi3 : openInstr (pc1 + 3) = .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24))) := by
          have h := hcodeR.2 3 (by simp [copy30TailCode]); simpa [copy30TailCode] using h
        have hbd : pc1 + 4 ≤ OPEN_CODE_LEN := by have := hcodeR.1; rw [htlen] at this; exact this
        have ha1 := step_LD (s := s1) (by omega) hpc1 hi0 (by rw [hs1_src]; exact hsrc24_valid)
        set s2 := (s1.setReg .x5 (s1.getMem (s1.getReg srcReg + signExtend12 (24#12)))).setPC (pcAt (pc1 + 1))
        have ha2 := step_SLLI (s := s2) (by omega) rfl hi1
        set s3 := (s2.setReg .x6 (s2.getReg .x5 <<< (16#6).toNat)).setPC (pcAt (pc1 + 1 + 1))
        have ha3 := step_OR (s := s3) (by omega) (by congr 1) hi2
        set s4 := (s3.setReg .x12 (s3.getReg .x12 ||| s3.getReg .x6)).setPC (pcAt (pc1 + 2 + 1))
        have hs4_x25 : s4.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by
          simp [s4, s3, s2, getReg_setReg_ne', hrx25_1]
        have ha4 := step_SD (s := s4) (by omega) (by congr 1) hi3 (by rw [hs4_x25]; exact hdst24_valid8)
        set s5 := (s4.setMem (s4.getReg .x25 + signExtend12 (BitVec.ofNat 12 (dstOff + 24))) (s4.getReg .x12)).setPC (pcAt (pc1 + 3 + 1))
        refine ⟨s5, by rw [hcode_tot, htlen]; exact ((hr1.trans ha1).trans (ha2.trans ha3)).trans ha4,
          by rw [hcode_tot, htlen, ← Nat.add_assoc]; congr 1, ?_, ?_, ?_⟩
        · intro reg hreg
          have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
          have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
          have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
          exact (by simp [s5, s4, s3, s2, getReg_setMem, getReg_setReg_ne' .x12 reg hne12.symm,
            getReg_setReg_ne' .x6 reg hne6.symm, getReg_setReg_ne' .x5 reg hne5.symm] : s5.getReg reg = s1.getReg reg).trans (hregs1 reg hreg)
        · refine hp1.trans ?_
          intro a ha
          simp only [s5, s4, s3, s2, MachineState.getMem_setPC, MachineState.getMem_setReg, hs4_x25, hdst24_addr]
          exact ProofWritePreserves.setMem_proof (by omega) (by omega) (by omega) a ha
        · refine ⟨hbase8, by simp [copy30NextDstOff]; omega,
            by simp [copy30NextR, copy30NextDstOff, bitsToBytes_length]; omega,
            by simp [copy30NextDstOff]; omega,
            by simp [s5, s4, s3, s2, getReg_setMem, getReg_setReg_ne', hrx25_1],
            by simp, fun hcl j hj => ?_, fun _ => by simp [copy30NextR]⟩
          simp only [copy30NextDstOff, show ¬ ((2 : Nat) < 2) by omega, ↓reduceIte] at hj
          have hrem1 := hw1.hrem hcl
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, show ¬ ((2 : Nat) = 0) by omega] at hrem1
          have hs4_x12 : s4.getReg .x12 = s1.getReg .x12 ||| (d3 <<< (8 * 2)) := by
            simp [s4, s3, s2, getReg_setReg_ne', hs1_src, hsrc24_addr, hs1_d3 hcl]
          simp only [s5, getByte_setPC, hs4_x25, hdst24_addr, hs4_x12]
          change (s1.setMem (BitVec.ofNat 64 (11341403200 + base + (dstOff + 24))) (s1.getReg .x12 ||| (d3 <<< (8 * 2)))).getByte (BitVec.ofNat 64 (11341403200 + j)) = _
          by_cases hlt : j < base + (dstOff + 24)
          · rw [setMem_getByte_ofNat s1 (11341403200 + base + (dstOff + 24)) (11341403200 + j) _ (by omega) (by omega) (by omega) (by omega)]
            rw [hget30_left j (by omega)]
            exact hw1.hbytes hcl j hlt
          · have hk : j - (base + (dstOff + 24)) < 8 := by omega
            have heq : 11341403200 + j = (11341403200 + base + (dstOff + 24)) + (j - (base + (dstOff + 24))) := by omega
            rw [heq, setMem_getByte_inside s1 (11341403200 + base + (dstOff + 24)) _ _ (by omega) hk]
            rw [word_or_shl_byte (s1.getReg .x12) d3 2 (by omega) hrem1.2 _ hk]
            split_ifs with hkr
            · rw [hrem1.1 _ hkr, hget30_left j (by omega)]; first | rfl | (congr 1; omega)
            · rw [hbyte_tail hcl j (by omega) (by omega)]; first | rfl | (congr 1; omega)
      · by_cases hr4 : rv = 4
        · subst hr4
          have htlen : (copy30TailCode ⟨4, hrv⟩ srcReg dstOff).length = 3 := rfl
          have hi0 : openInstr pc1 = .base (.LD .x5 srcReg (24#12)) := by
            have h := hcodeR.2 0 (by simp [copy30TailCode]); simpa [copy30TailCode] using h
          have hi1 : openInstr (pc1 + 1) = .base (.SW .x25 .x5 (BitVec.ofNat 12 (dstOff + 28))) := by
            have h := hcodeR.2 1 (by simp [copy30TailCode]); simpa [copy30TailCode] using h
          have hi2 : openInstr (pc1 + 2) = .base (.SRLI .x12 .x5 (32#6)) := by
            have h := hcodeR.2 2 (by simp [copy30TailCode]); simpa [copy30TailCode] using h
          have hbd : pc1 + 3 ≤ OPEN_CODE_LEN := by have := hcodeR.1; rw [htlen] at this; exact this
          have ha1 := step_LD (s := s1) (by omega) hpc1 hi0 (by rw [hs1_src]; exact hsrc24_valid)
          set s2 := (s1.setReg .x5 (s1.getMem (s1.getReg srcReg + signExtend12 (24#12)))).setPC (pcAt (pc1 + 1))
          have hs2_x25 : s2.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by
            simp [s2, getReg_setReg_ne', hrx25_1]
          have ha2 := step_SW (s := s2) (by omega) rfl hi1 (by rw [hs2_x25]; exact hdst28_valid4)
          set s3 := (s2.setWord32 (s2.getReg .x25 + signExtend12 (BitVec.ofNat 12 (dstOff + 28))) ((s2.getReg .x5).truncate 32)).setPC (pcAt (pc1 + 1 + 1))
          have ha3 := step_SRLI (s := s3) (by omega) (by congr 1) hi2
          set s4 := (s3.setReg .x12 (s3.getReg .x5 >>> (32#6).toNat)).setPC (pcAt (pc1 + 2 + 1))
          refine ⟨s4, by rw [hcode_tot, htlen]; exact (hr1.trans ha1).trans (ha2.trans ha3),
            by rw [hcode_tot, htlen, ← Nat.add_assoc]; congr 1, ?_, ?_, ?_⟩
          · intro reg hreg
            have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
            have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
            exact (by simp [s4, s3, s2, getReg_setWord32, getReg_setReg_ne' .x12 reg hne12.symm,
              getReg_setReg_ne' .x5 reg hne5.symm] : s4.getReg reg = s1.getReg reg).trans (hregs1 reg hreg)
          · refine hp1.trans ?_
            intro a ha
            simp only [s4, s3, s2, MachineState.getMem_setPC, MachineState.getMem_setReg, hs2_x25, hdst28_addr]
            exact ProofWritePreserves.setWord32_proof (by omega) (by omega) (by omega) a ha
          · refine ⟨hbase8, by simp [copy30NextDstOff]; omega,
              by simp [copy30NextR, copy30NextDstOff, bitsToBytes_length]; omega,
              by simp [copy30NextDstOff]; omega,
              by simp [s4, s3, s2, getReg_setWord32, getReg_setReg_ne', hrx25_1],
              by simp, fun hcl j hj => ?_, fun hcl => ?_⟩
            · simp only [copy30NextDstOff, show ¬ ((4 : Nat) < 2) by omega, ↓reduceIte] at hj
              have hs2_x5 : s2.getReg .x5 = d3 := by simp [s2, hs1_src, hsrc24_addr, hs1_d3 hcl]
              simp only [s4, s3, getByte_setPC, getByte_setReg, hs2_x25, hdst28_addr, hs2_x5]
              rw [setWord32_getByte_ofNat s2 (11341403200 + base + dstOff + 28) (11341403200 + j) _ (by omega) (by omega) (by omega)]
              split_ifs with hin
              · have hk : j - (base + dstOff + 28) < 4 := by omega
                rw [show 11341403200 + j - (11341403200 + base + dstOff + 28) = j - (base + dstOff + 28) by omega,
                  truncate32_extract_byte _ _ hk, hbyte_tail hcl j (by omega) (by omega)]
              · simp only [s2, getByte_setPC, getByte_setReg]
                rw [hget30_left j (by omega)]
                by_cases hlt24 : j < base + (dstOff + 24)
                · exact hw1.hbytes hcl j hlt24
                · have hrem1 := hw1.hrem hcl
                  simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte] at hrem1
                  have h1 := hrem1 (j - (base + (dstOff + 24))) (by omega)
                  simpa only [show 11341403200 + base + (dstOff + 24) + (j - (base + (dstOff + 24))) = 11341403200 + j by omega,
                    show base + (dstOff + 24) + (j - (base + (dstOff + 24))) = j by omega] using h1
            · simp only [copy30NextR, copy30NextDstOff, show ¬ ((4 : Nat) < 2) by omega, Bool.false_eq_true, ↓reduceIte,
                show ¬ (((4 + 6) % 8 : Nat) = 0) by decide]
              have hx12 : s4.getReg .x12 = d3 >>> 32 := by
                simp [s4, s3, s2, getReg_setWord32, hs1_src, hsrc24_addr, hs1_d3 hcl]
              refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
              · rw [hx12]
                have hb := word_ushr_byte d3 4 (by omega) j (by omega)
                rw [show 8 * 4 = 32 from rfl, if_pos (by omega)] at hb
                rw [hb, hbyte_tail hcl (base + (dstOff + 32) + j) (by omega) (by omega)]; congr 1; omega
              · rw [hx12]
                have hb := word_ushr_byte d3 4 (by omega) j hj2
                rw [show 8 * 4 = 32 from rfl] at hb
                rw [hb]
                split_ifs with hlt8
                · exact hd3_hi hcl (j + 4) (by omega) hlt8
                · rfl
        · -- General rv ∈ {3, 5, 6, 7}: 5-instruction spill!
          have htail_eq : copy30TailCode ⟨rv, hrv⟩ srcReg dstOff =
              [.base (.LD .x5 srcReg (24#12)),
               .base (.SLLI .x6 .x5 (BitVec.ofNat 6 (8 * rv))),
               .base (.OR .x12 .x12 .x6),
               .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24))),
               .base (.SRLI .x12 .x5 (BitVec.ofNat 6 (64 - 8 * rv)))] := by
            have hcs : rv = 3 ∨ rv = 5 ∨ rv = 6 ∨ rv = 7 := by omega
            rcases hcs with rfl | rfl | rfl | rfl <;> rfl
          have htlen : (copy30TailCode ⟨rv, hrv⟩ srcReg dstOff).length = 5 := by rw [htail_eq]; rfl
          have hi0 : openInstr pc1 = .base (.LD .x5 srcReg (24#12)) := by
            have h := hcodeR.2 0 (by rw [htlen]; omega); simp only [htail_eq, Nat.add_zero] at h; exact h
          have hi1 : openInstr (pc1 + 1) = .base (.SLLI .x6 .x5 (BitVec.ofNat 6 (8 * rv))) := by
            have h := hcodeR.2 1 (by rw [htlen]; omega); simp only [htail_eq] at h; exact h
          have hi2 : openInstr (pc1 + 2) = .base (.OR .x12 .x12 .x6) := by
            have h := hcodeR.2 2 (by rw [htlen]; omega); simp only [htail_eq] at h; exact h
          have hi3 : openInstr (pc1 + 3) = .base (.SD .x25 .x12 (BitVec.ofNat 12 (dstOff + 24))) := by
            have h := hcodeR.2 3 (by rw [htlen]; omega); simp only [htail_eq] at h; exact h
          have hi4 : openInstr (pc1 + 4) = .base (.SRLI .x12 .x5 (BitVec.ofNat 6 (64 - 8 * rv))) := by
            have h := hcodeR.2 4 (by rw [htlen]; omega); simp only [htail_eq] at h; exact h
          have hbd : pc1 + 5 ≤ OPEN_CODE_LEN := by have := hcodeR.1; rw [htlen] at this; exact this
          have ha1 := step_LD (s := s1) (by omega) hpc1 hi0 (by rw [hs1_src]; exact hsrc24_valid)
          set s2 := (s1.setReg .x5 (s1.getMem (s1.getReg srcReg + signExtend12 (24#12)))).setPC (pcAt (pc1 + 1))
          have ha2 := step_SLLI (s := s2) (by omega) rfl hi1
          set s3 := (s2.setReg .x6 (s2.getReg .x5 <<< (BitVec.ofNat 6 (8 * rv)).toNat)).setPC (pcAt (pc1 + 1 + 1))
          have ha3 := step_OR (s := s3) (by omega) (by congr 1) hi2
          set s4 := (s3.setReg .x12 (s3.getReg .x12 ||| s3.getReg .x6)).setPC (pcAt (pc1 + 2 + 1))
          have hs4_x25 : s4.getReg .x25 = BitVec.ofNat 64 (11341403200 + base) := by
            simp [s4, s3, s2, getReg_setReg_ne', hrx25_1]
          have ha4 := step_SD (s := s4) (by omega) (by congr 1) hi3 (by rw [hs4_x25]; exact hdst24_valid8)
          set s5 := (s4.setMem (s4.getReg .x25 + signExtend12 (BitVec.ofNat 12 (dstOff + 24))) (s4.getReg .x12)).setPC (pcAt (pc1 + 3 + 1))
          have ha5 := step_SRLI (s := s5) (by omega) (by congr 1) hi4
          set s6 := (s5.setReg .x12 (s5.getReg .x5 >>> (BitVec.ofNat 6 (64 - 8 * rv)).toNat)).setPC (pcAt (pc1 + 4 + 1))
          have hshL : (BitVec.ofNat 6 (8 * rv)).toNat = 8 * rv := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hshR : (BitVec.ofNat 6 (64 - 8 * rv)).toNat = 64 - 8 * rv := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hge3 : 3 ≤ rv := by omega
          have hnr_ne0 : (rv + 6) % 8 ≠ 0 := by omega
          have hbeq4 : (rv == 4) = false := by simp [hr4]
          refine ⟨s6, by rw [hcode_tot, htlen]; exact ((((hr1.trans ha1).trans ha2).trans ha3).trans ha4).trans ha5,
            by rw [hcode_tot, htlen, ← Nat.add_assoc]; congr 1, ?_, ?_, ?_⟩
          · intro reg hreg
            have hne5 : reg ≠ .x5 := fun h => hreg (by simp [h])
            have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
            have hne12 : reg ≠ .x12 := fun h => hreg (by simp [h])
            exact (by simp [s6, s5, s4, s3, s2, getReg_setMem, getReg_setReg_ne' .x12 reg hne12.symm,
              getReg_setReg_ne' .x6 reg hne6.symm, getReg_setReg_ne' .x5 reg hne5.symm] : s6.getReg reg = s1.getReg reg).trans (hregs1 reg hreg)
          · refine hp1.trans ?_
            intro a ha
            simp only [s6, s5, s4, s3, s2, MachineState.getMem_setPC, MachineState.getMem_setReg, hs4_x25, hdst24_addr]
            exact ProofWritePreserves.setMem_proof (by omega) (by omega) (by omega) a ha
          · refine ⟨hbase8, by simp [copy30NextDstOff, show ¬ (rv < 2) by omega]; omega,
              by simp [copy30NextR, copy30NextDstOff, show ¬ (rv < 2) by omega, bitsToBytes_length]; omega,
              by simp [copy30NextDstOff, show ¬ (rv < 2) by omega]; omega,
              by simp [s6, s5, s4, s3, s2, getReg_setMem, getReg_setReg_ne', hrx25_1],
              by simp, fun hcl j hj => ?_, fun hcl => ?_⟩
            · simp only [copy30NextDstOff, show ¬ (rv < 2) by omega, ↓reduceIte] at hj
              have hrem1 := hw1.hrem hcl
              simp only [hbeq4, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hr0] at hrem1
              have hs4_x12 : s4.getReg .x12 = s1.getReg .x12 ||| (d3 <<< (8 * rv)) := by
                simp [s4, s3, s2, getReg_setReg_ne', hs1_src, hsrc24_addr, hs1_d3 hcl, hshL]
              simp only [s6, s5, getByte_setPC, getByte_setReg, hs4_x25, hdst24_addr, hs4_x12]
              change (s1.setMem (BitVec.ofNat 64 (11341403200 + base + (dstOff + 24))) (s1.getReg .x12 ||| (d3 <<< (8 * rv)))).getByte (BitVec.ofNat 64 (11341403200 + j)) = _
              by_cases hlt : j < base + (dstOff + 24)
              · rw [setMem_getByte_ofNat s1 (11341403200 + base + (dstOff + 24)) (11341403200 + j) _ (by omega) (by omega) (by omega) (by omega)]
                rw [hget30_left j (by omega)]
                exact hw1.hbytes hcl j hlt
              · have hk : j - (base + (dstOff + 24)) < 8 := by omega
                have heq : 11341403200 + j = (11341403200 + base + (dstOff + 24)) + (j - (base + (dstOff + 24))) := by omega
                rw [heq, setMem_getByte_inside s1 (11341403200 + base + (dstOff + 24)) _ _ (by omega) hk]
                rw [word_or_shl_byte (s1.getReg .x12) d3 rv hrv hrem1.2 _ hk]
                split_ifs with hkr
                · rw [hrem1.1 _ hkr, hget30_left j (by omega)]; congr 1; omega
                · rw [hbyte_tail hcl j (by omega) (by omega)]; congr 1; omega
            · simp only [copy30NextR, copy30NextDstOff, show ¬ (rv < 2) by omega, Bool.false_eq_true, ↓reduceIte, hnr_ne0]
              have hx12 : s6.getReg .x12 = d3 >>> (8 * (8 - rv)) := by
                have h5 : s5.getReg .x5 = d3 := by simp [s5, s4, s3, s2, getReg_setMem, getReg_setReg_ne', hs1_src, hsrc24_addr, hs1_d3 hcl]
                simp only [s6, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
                  h5, hshR]
                congr 1; omega
              refine ⟨fun j hj => ?_, fun j hj1 hj2 => ?_⟩
              · rw [hx12, word_ushr_byte d3 (8 - rv) (by omega) j (by omega), if_pos (by omega)]
                rw [hbyte_tail hcl (base + (dstOff + 32) + j) (by omega) (by omega)]; congr 1; omega
              · rw [hx12, word_ushr_byte d3 (8 - rv) (by omega) j hj2]
                split_ifs with hlt8
                · exact hd3_hi hcl (j + (8 - rv)) (by omega) hlt8
                · rfl

/-! ### 4. Universal Negative-Counter Tail Merge (`tailMergeCode`) and Cap Tail Push (`tailPush6Code`) -/

def tailMergeCode (bits : Nat) : List Instruction :=
  [.base (.SLL .x6 .x8 .x17),
   .base (.OR .x16 .x16 .x6),
   .base (.SUB .x28 .x0 .x17),
   .base (.ADDI .x17 .x17 (BitVec.ofNat 12 bits)),
   .base (.BLT .x17 .x0 (20#13)),
   .base (.SD .x15 .x16 (0#12)),
   .base (.ADDI .x15 .x15 (8#12)),
   .base (.SRL .x16 .x8 .x28),
   .base (.ADDI .x17 .x17 (4032#12))]

/-- Step a `bits = 6 * ts.length`-bit tail merge (`1 ≤ ts.length ≤ 9`) into `(x15, x16, x17)`. -/
theorem openRuns_tailMerge_neg {clean : Prop} {s : MachineState} {pc : Nat}
    {tails ts : List (BitVec 6)} {flushes : Nat}
    (hts1 : 1 ≤ ts.length) (hts9 : ts.length ≤ 9)
    (hcode : CodeAt pc (tailMergeCode (6 * ts.length)))
    (hpc : s.pc = pcAt pc)
    (hx8 : clean → s.getReg .x8 = BitVec.ofNat 64 (bitsOf6 ts))
    (ht : TailState clean s tails flushes)
    (hbd_next : 8 * (flushes + 1) + 16 ≤ 48719475936) :
    let tCnt := (6 * tails.length) % 64
    let fl : Nat := if tCnt + 6 * ts.length < 64 then 0 else 1
    let cyc : Nat := 5 + 4 * fl
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt (pc + 9) ∧
      RegsEqExcept [.x6, .x15, .x16, .x17, .x28] s s' ∧
      TailWritePreserves s s' ∧
      TailState clean s' (tails ++ ts) (flushes + fl) := by
  set tCnt := (6 * tails.length) % 64
  have htCnt_lt : tCnt < 64 := Nat.mod_lt _ (by omega)
  have hcodeLen : (tailMergeCode (6 * ts.length)).length = 9 := rfl
  have hbd : pc + 9 ≤ OPEN_CODE_LEN := by have := hcode.1; rw [hcodeLen] at this; exact this
  have hi0 : openInstr pc = .base (.SLL .x6 .x8 .x17) := by have h := hcode.2 0 (by omega); simpa [tailMergeCode] using h
  have hi1 : openInstr (pc + 1) = .base (.OR .x16 .x16 .x6) := by have h := hcode.2 1 (by omega); simpa [tailMergeCode] using h
  have hi2 : openInstr (pc + 2) = .base (.SUB .x28 .x0 .x17) := by have h := hcode.2 2 (by omega); simpa [tailMergeCode] using h
  have hi3 : openInstr (pc + 3) = .base (.ADDI .x17 .x17 (BitVec.ofNat 12 (6 * ts.length))) := by
    have h := hcode.2 3 (by omega); simpa [tailMergeCode] using h
  have hi4 : openInstr (pc + 4) = .base (.BLT .x17 .x0 (20#13)) := by have h := hcode.2 4 (by omega); simpa [tailMergeCode] using h
  have hi5 : openInstr (pc + 5) = .base (.SD .x15 .x16 (0#12)) := by have h := hcode.2 5 (by omega); simpa [tailMergeCode] using h
  have hi6 : openInstr (pc + 6) = .base (.ADDI .x15 .x15 (8#12)) := by have h := hcode.2 6 (by omega); simpa [tailMergeCode] using h
  have hi7 : openInstr (pc + 7) = .base (.SRL .x16 .x8 .x28) := by have h := hcode.2 7 (by omega); simpa [tailMergeCode] using h
  have hi8 : openInstr (pc + 8) = .base (.ADDI .x17 .x17 (4032#12)) := by have h := hcode.2 8 (by omega); simpa [tailMergeCode] using h
  have hs1 := step_SLL (by omega) hpc hi0
  set s1 := (s.setReg .x6 (s.getReg .x8 <<< ((s.getReg .x17).toNat % 64))).setPC (pcAt (pc + 1))
  have hs2 := step_OR (s := s1) (by omega) rfl hi1
  set s2 := (s1.setReg .x16 (s1.getReg .x16 ||| s1.getReg .x6)).setPC (pcAt (pc + 1 + 1))
  have hs3 := step_SUB (s := s2) (by omega) (by congr 1) hi2
  set s3 := (s2.setReg .x28 (s2.getReg .x0 - s2.getReg .x17)).setPC (pcAt (pc + 2 + 1))
  have hs4 := step_ADDI (s := s3) (by omega) (by congr 1) hi3
  set s4 := (s3.setReg .x17 (s3.getReg .x17 + signExtend12 (BitVec.ofNat 12 (6 * ts.length)))).setPC (pcAt (pc + 3 + 1))
  have hrx17 : s.getReg .x17 = negCnt tCnt := ht.rx17
  have hs3_x17 : s3.getReg .x17 = negCnt tCnt := by simp [s3, s2, s1, getReg_setReg_ne', hrx17]
  have hs3_x28 : s3.getReg .x28 = BitVec.ofNat 64 (64 - tCnt) := by
    simp [s3, s2, s1, getReg_setReg_ne', hrx17, show s.getReg .x0 = 0#64 from rfl, zero_sub_negCnt tCnt htCnt_lt]
  have hts_lt : bitsOf6 ts < 2 ^ (6 * ts.length) := bitsOf6_lt ts
  have hts_lt64 : bitsOf6 ts < 2 ^ 64 := by
    have : 2 ^ (6 * ts.length) ≤ 2 ^ 54 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hbits_append : 6 * (tails ++ ts).length = 64 * flushes + (tCnt + 6 * ts.length) := by
    simp only [List.length_append]; have := ht.hbits; omega
  by_cases hnf : tCnt + 6 * ts.length < 64
  · -- No flush: BLT taken -> pc + 9 (5 cycles)
    have hs4_x17 : s4.getReg .x17 = negCnt (tCnt + 6 * ts.length) := by
      simp [s4, hs3_x17, negCnt_add_lt tCnt (6 * ts.length) hnf]
    have hlt_slt : BitVec.slt (s4.getReg .x17) (s4.getReg .x0) = true := by
      rw [hs4_x17, show s4.getReg .x0 = 0#64 from rfl]; exact negCnt_slt_zero _ hnf
    have htgt : pcAt (pc + 4) + signExtend13 (20#13) = pcAt (pc + 9) := by
      simpa only [show 4 * (pc + 9 - (pc + 4)) = 20 by omega] using pcAt_add_pos13 (pc + 4) (pc + 9) (by omega) (by omega)
    have hs5 := step_BLT_taken (s := s4) (by omega) (by congr 1) hi4 hlt_slt htgt
    set s5 := s4.setPC (pcAt (pc + 9))
    simp only [hnf, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
    refine ⟨s5, (((hs1.trans hs2).trans hs3).trans hs4).trans hs5, rfl, ?_, TailWritePreserves.refl s, ?_⟩
    · intro reg hreg
      have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
      have hne16 : reg ≠ .x16 := fun h => hreg (by simp [h])
      have hne17 : reg ≠ .x17 := fun h => hreg (by simp [h])
      have hne28 : reg ≠ .x28 := fun h => hreg (by simp [h])
      simp [s5, s4, s3, s2, s1, getReg_setReg_ne' .x17 reg hne17.symm,
        getReg_setReg_ne' .x28 reg hne28.symm, getReg_setReg_ne' .x16 reg hne16.symm,
        getReg_setReg_ne' .x6 reg hne6.symm]
    · have hmod : (6 * (tails ++ ts).length) % 64 = tCnt + 6 * ts.length := by
        rw [hbits_append, Nat.mul_add_mod, Nat.mod_eq_of_lt hnf]
      refine ⟨by rw [hmod, hbits_append], ht.hbound,
        by simp [s5, s4, s3, s2, s1, getReg_setReg_ne', ht.rx15],
        by rw [hmod]; exact hs4_x17, fun hcl => ?_⟩
      obtain ⟨tBuf, htBuf_lt, hx16, hsum⟩ := ht.hdata hcl
      have hnew_lt : tBuf + bitsOf6 ts * 2 ^ tCnt < 2 ^ (tCnt + 6 * ts.length) := by
        rw [Nat.pow_add, Nat.mul_comm (2 ^ tCnt)]
        have h1 : bitsOf6 ts + 1 ≤ 2 ^ (6 * ts.length) := by omega
        have h2 := Nat.mul_le_mul_right (2 ^ tCnt) h1
        linarith
      have hnew_lt64 : tBuf + bitsOf6 ts * 2 ^ tCnt < 2 ^ 64 := by
        have : 2 ^ (tCnt + 6 * ts.length) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      refine ⟨tBuf + bitsOf6 ts * 2 ^ tCnt, by rw [hmod]; exact hnew_lt, ?_, ?_⟩
      · have hs5_x16 : s5.getReg .x16 = BitVec.ofNat 64 tBuf ||| (BitVec.ofNat 64 (bitsOf6 ts) <<< tCnt) := by
          simp [s5, s4, s3, s2, s1, getReg_setReg_ne', hx16, hx8 hcl, hrx17, negCnt_mod64 tCnt htCnt_lt]
        rw [hs5_x16]
        apply BitVec.eq_of_toNat_eq
        rw [word_or_shl_add_low64 tBuf tCnt (bitsOf6 ts) htCnt_lt htBuf_lt hts_lt64,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt hnew_lt64]
      · have hmem : ∀ j, s5.getByte j = s.getByte j := fun j => by simp [s5, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
        simp only [hmem, bitsOf6_append]
        have hpow : 2 ^ (64 * flushes) * 2 ^ tCnt = 2 ^ (6 * tails.length) := by
          rw [← Nat.pow_add, ht.hbits]
        calc
          bytesToNat ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) +
              2 ^ (64 * flushes) * (tBuf + bitsOf6 ts * 2 ^ tCnt)
            = (bytesToNat ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) +
                2 ^ (64 * flushes) * tBuf) + (2 ^ (64 * flushes) * 2 ^ tCnt) * bitsOf6 ts := by ring
          _ = bitsOf6 tails + 2 ^ (6 * tails.length) * bitsOf6 ts := by rw [hsum, hpow]
  · -- Flush: BLT not taken -> SD + ADDI x15 + SRL x16 + ADDI x17 (-64) (9 cycles)
    have hge64 : 64 ≤ tCnt + 6 * ts.length := by omega
    have hnew_cnt_lt : tCnt + 6 * ts.length - 64 < 64 := by omega
    have htCnt_pos : 0 < tCnt := by omega
    have hs4_x17 : s4.getReg .x17 = BitVec.ofNat 64 (tCnt + 6 * ts.length - 64) := by
      simp [s4, hs3_x17, negCnt_add_ge tCnt (6 * ts.length) htCnt_lt (by omega) hge64]
    have hslt_f : BitVec.slt (s4.getReg .x17) (s4.getReg .x0) = false := by
      rw [hs4_x17, show s4.getReg .x0 = 0#64 from rfl]; exact nonneg_not_slt_zero _ hnew_cnt_lt
    have hs5 := step_BLT_not_taken (s := s4) (by omega) (by congr 1) hi4 hslt_f
    set s5 := s4.setPC (pcAt (pc + 4 + 1))
    have hs5_x15 : s5.getReg .x15 = BitVec.ofNat 64 (tailBufBase + 8 * flushes) := by
      simp [s5, s4, s3, s2, s1, getReg_setReg_ne', ht.rx15]
    have hsd_valid : accessValid (s5.getReg .x15 + signExtend12 (0#12)) 8 = true := by
      rw [hs5_x15, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
      have htbb : tailBufBase = 20000000000 := rfl
      exact accessValid_ofNat (tailBufBase + 8 * flushes) 8 (by have := ht.hbound; omega) (by omega)
    have hsd_addr : s5.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + 8 * flushes) := by
      rw [hs5_x15, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hs6 := step_SD (s := s5) (by omega) (by congr 1) hi5 hsd_valid
    set s6 := (s5.setMem (s5.getReg .x15 + signExtend12 (0#12)) (s5.getReg .x16)).setPC (pcAt (pc + 5 + 1))
    have hs7 := step_ADDI (s := s6) (by omega) (by congr 1) hi6
    set s7 := (s6.setReg .x15 (s6.getReg .x15 + signExtend12 (8#12))).setPC (pcAt (pc + 6 + 1))
    have hs8 := step_SRL (s := s7) (by omega) (by congr 1) hi7
    set s8 := (s7.setReg .x16 (s7.getReg .x8 >>> ((s7.getReg .x28).toNat % 64))).setPC (pcAt (pc + 7 + 1))
    have hs9 := step_ADDI (s := s8) (by omega) (by congr 1) hi8
    set s9 := (s8.setReg .x17 (s8.getReg .x17 + signExtend12 (4032#12))).setPC (pcAt (pc + 8 + 1))
    simp only [hnf, ↓reduceIte, Nat.mul_one]
    have hmod : (6 * (tails ++ ts).length) % 64 = tCnt + 6 * ts.length - 64 := by
      have h1 : 6 * (tails ++ ts).length = 64 * (flushes + 1) + (tCnt + 6 * ts.length - 64) := by omega
      rw [h1, Nat.mul_add_mod, Nat.mod_eq_of_lt hnew_cnt_lt]
    refine ⟨s9, (((((((hs1.trans hs2).trans hs3).trans hs4).trans hs5).trans hs6).trans hs7).trans hs8).trans hs9,
      by congr 1, ?_, ?_, ?_⟩
    · intro reg hreg
      have hne6 : reg ≠ .x6 := fun h => hreg (by simp [h])
      have hne15 : reg ≠ .x15 := fun h => hreg (by simp [h])
      have hne16 : reg ≠ .x16 := fun h => hreg (by simp [h])
      have hne17 : reg ≠ .x17 := fun h => hreg (by simp [h])
      have hne28 : reg ≠ .x28 := fun h => hreg (by simp [h])
      simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, getReg_setMem,
        getReg_setReg_ne' .x17 reg hne17.symm, getReg_setReg_ne' .x16 reg hne16.symm,
        getReg_setReg_ne' .x15 reg hne15.symm, getReg_setReg_ne' .x28 reg hne28.symm,
        getReg_setReg_ne' .x6 reg hne6.symm]
    · intro a ha
      simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hsd_addr]
      have htbb : tailBufBase = 20000000000 := rfl
      exact TailWritePreserves.setMem_tail (by omega) (by have := ht.hbound; omega) (by omega) a ha
    · have hs9_x15 : s9.getReg .x15 = BitVec.ofNat 64 (tailBufBase + 8 * (flushes + 1)) := by
        simp [s9, s8, s7, s6, getReg_setMem, getReg_setReg_ne', hs5_x15, signExtend12_nonneg 8 (by omega),
          ← BitVec.ofNat_add, show tailBufBase + 8 * flushes + 8 = tailBufBase + 8 * (flushes + 1) by omega]
      have hs9_x17 : s9.getReg .x17 = negCnt (tCnt + 6 * ts.length - 64) := by
        have h8 : s8.getReg .x17 = BitVec.ofNat 64 (tCnt + 6 * ts.length - 64) := by
          simp [s8, s7, s6, s5, getReg_setMem, getReg_setReg_ne', hs4_x17]
        simp [s9, h8, show (4032#12 : BitVec 12) = BitVec.ofNat 12 (4096 - 64) from rfl,
          negCnt_sub64 _ hnew_cnt_lt]
      refine ⟨by omega, hbd_next, hs9_x15, by rw [hmod]; exact hs9_x17, fun hcl => ?_⟩
      obtain ⟨tBuf, htBuf_lt, hx16, hsum⟩ := ht.hdata hcl
      set newBuf := (tBuf + bitsOf6 ts * 2 ^ tCnt) / 2 ^ 64
      have hnew_lt : newBuf < 2 ^ (tCnt + 6 * ts.length - 64) := by
        have htot : tBuf + bitsOf6 ts * 2 ^ tCnt < 2 ^ (tCnt + 6 * ts.length) := by
          rw [Nat.pow_add, Nat.mul_comm (2 ^ tCnt)]
          have h1 : bitsOf6 ts + 1 ≤ 2 ^ (6 * ts.length) := by omega
          have h2 := Nat.mul_le_mul_right (2 ^ tCnt) h1
          linarith
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)]
        rw [← Nat.pow_add, show tCnt + 6 * ts.length - 64 + 64 = tCnt + 6 * ts.length by omega]
        exact htot
      refine ⟨newBuf, by rw [hmod]; exact hnew_lt, ?_, ?_⟩
      · have hs7_x8 : s7.getReg .x8 = BitVec.ofNat 64 (bitsOf6 ts) := by
          simp [s7, s6, s5, s4, s3, s2, s1, getReg_setMem, getReg_setReg_ne', hx8 hcl]
        have hs7_x28 : (s7.getReg .x28).toNat % 64 = 64 - tCnt := by
          have h7 : s7.getReg .x28 = BitVec.ofNat 64 (64 - tCnt) := by
            simp [s7, s6, s5, s4, getReg_setMem, getReg_setReg_ne', hs3_x28]
          rw [h7, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 64 - tCnt < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : 64 - tCnt < 64)]
        have hs9_x16 : s9.getReg .x16 = BitVec.ofNat 64 (bitsOf6 ts) >>> (64 - tCnt) := by
          simp [s9, s8, getReg_setReg_ne', hs7_x8, hs7_x28]
        rw [hs9_x16]
        apply BitVec.eq_of_toNat_eq
        rw [tail_hi_ushr tBuf tCnt (bitsOf6 ts) htCnt_lt htBuf_lt hts_lt64 htCnt_pos,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
            have : 2 ^ (tCnt + 6 * ts.length - 64) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by omega) (by omega)
            omega)]
      · -- Show writtenBytes' = writtenBytes ++ bytesOfWord (s5.getReg .x16)
        have hs5_x16 : s5.getReg .x16 = BitVec.ofNat 64 tBuf ||| (BitVec.ofNat 64 (bitsOf6 ts) <<< tCnt) := by
          simp [s5, s4, s3, s2, s1, getReg_setReg_ne', hx16, hx8 hcl, hrx17, negCnt_mod64 tCnt htCnt_lt]
        have hlow64 : (s5.getReg .x16).toNat = (tBuf + bitsOf6 ts * 2 ^ tCnt) % 2 ^ 64 := by
          rw [hs5_x16]; exact word_or_shl_add_low64 tBuf tCnt (bitsOf6 ts) htCnt_lt htBuf_lt hts_lt64
        have hmap_eq : ((List.range (8 * (flushes + 1))).map fun j => s9.getByte (BitVec.ofNat 64 (tailBufBase + j))) =
            ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) ++
            bytesOfWord (s5.getReg .x16) := by
          apply List.ext_getElem
          · simp [bytesOfWord_length]; omega
          · intro j hj1 hj2
            simp only [List.length_map, List.length_range] at hj1
            simp only [List.getElem_map, List.getElem_range]
            simp only [s9, s8, s7, s6, getByte_setPC, getByte_setReg, hsd_addr]
            change (s.setMem (BitVec.ofNat 64 (tailBufBase + 8 * flushes)) (s5.getReg .x16)).getByte (BitVec.ofNat 64 (tailBufBase + j)) = _
            have htbb : tailBufBase = 20000000000 := rfl
            by_cases hlt : j < 8 * flushes
            · rw [setMem_getByte_ofNat s (tailBufBase + 8 * flushes) (tailBufBase + j) _ (by omega) (by have := ht.hbound; omega) (by have := ht.hbound; omega) (by omega)]
              rw [List.getElem_append_left (by simp; exact hlt)]
              simp
            · have hk : j - 8 * flushes < 8 := by omega
              have heq : tailBufBase + j = (tailBufBase + 8 * flushes) + (j - 8 * flushes) := by omega
              rw [heq, setMem_getByte_inside s (tailBufBase + 8 * flushes) _ _ (by omega) hk]
              rw [List.getElem_append_right (by simp; omega)]
              simp only [List.length_map, List.length_range, bytesOfWord_getElem _ _ hk]
        rw [hmap_eq, bytesToNat_append, List.length_map, List.length_range, bytesOfWord, bytesToNat_word_bytes, hlow64, bitsOf6_append]
        have hpow64 : 2 ^ (64 * (flushes + 1)) = 2 ^ (64 * flushes) * 2 ^ 64 := by
          rw [show 64 * (flushes + 1) = 64 * flushes + 64 by omega, Nat.pow_add]
        have hpow_t : 2 ^ (64 * flushes) * 2 ^ tCnt = 2 ^ (6 * tails.length) := by
          rw [← Nat.pow_add, ht.hbits]
        have hdm : (tBuf + bitsOf6 ts * 2 ^ tCnt) % 2 ^ 64 + 2 ^ 64 * newBuf = tBuf + bitsOf6 ts * 2 ^ tCnt := by
          unfold newBuf; omega
        calc
          bytesToNat ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) +
              2 ^ (8 * (8 * flushes)) * ((tBuf + bitsOf6 ts * 2 ^ tCnt) % 2 ^ 64) +
              2 ^ (64 * (flushes + 1)) * newBuf
            = bytesToNat ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) +
                2 ^ (64 * flushes) * ((tBuf + bitsOf6 ts * 2 ^ tCnt) % 2 ^ 64 + 2 ^ 64 * newBuf) := by
              rw [show 8 * (8 * flushes) = 64 * flushes by omega, hpow64]; ring
          _ = bytesToNat ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) +
                2 ^ (64 * flushes) * tBuf + (2 ^ (64 * flushes) * 2 ^ tCnt) * bitsOf6 ts := by
              rw [hdm]; ring
          _ = bitsOf6 tails + 2 ^ (6 * tails.length) * bitsOf6 ts := by rw [hsum, hpow_t]

end CommitGolfCandidate.MoonOpen
