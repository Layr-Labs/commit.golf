import CommitGolfCandidate.MoonOpenBlocks

/-! Epilogue symbolic execution (`PC 7223..7429`):
1. `openRuns_flush_wbuf` (`7223..7229`): flushes remaining `r.val` bytes of the forward proof writer (`2 + 5 * r.val` cycles).
2. `openRuns_flush_tail64` (`7230..7236`): flushes remaining `(tCnt + 7) / 8` bytes of the 64-bit tail packer (`2 + 5 * ((tCnt + 7) / 8) ≤ 42` cycles) and proves exact byte equality with `pack6Bits tails`.
3. `openRuns_rev_tail` (`7237..7418`): 64/16/1 unrolled byte reversal appending `pack6BitsRev tails` to the proof buffer (`≤ 2086` cycles for `n ≤ 993`).
4. `openRuns_open_finish` (`7419..7428`): sets `x11 = totalProofLen`, `x5 = 1`, `x10 = 0`, landing at `ECALL` (`PC 7429`) in `10` cycles (`11` with `ECALL`). -/
namespace CommitGolfCandidate.MoonOpen
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp CommitGolfCandidate.MoonOpenCode

attribute [local simp] MachineState.getReg_setReg_eq MachineState.getReg_setPC
  MachineState.getMem_setPC MachineState.getMem_setReg getReg_setMem getReg_setByte getReg_setWord32

/-! ### 1. Pure Helpers (`bytesToNat` of Extracted Bytes, Signed `BLT`, and Reverse Cycle Bound) -/

private theorem bytesToNat_append_list (a b : List Byte) :
    bytesToNat (a ++ b) = bytesToNat a + 2 ^ (8 * a.length) * bytesToNat b := by
  induction a with
  | nil => simp [bytesToNat]
  | cons x xs ih =>
    simp only [List.cons_append, bytesToNat_cons, List.length_cons, ih]
    rw [show 8 * (xs.length + 1) = 8 + 8 * xs.length by omega, Nat.pow_add,
      show (2 : Nat) ^ 8 = 256 by decide]
    ring

private theorem bytesToNat_ofNat_div (v n : Nat) (hv : v < 2 ^ (8 * n)) :
    bytesToNat ((List.range n).map fun j => BitVec.ofNat 8 (v / 2 ^ (8 * j))) = v := by
  induction n generalizing v with
  | zero => simp at hv; simp [hv, bytesToNat]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, bytesToNat_cons, List.map_map]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, BitVec.toNat_ofNat]
    have hpow : 2 ^ (8 * (n + 1)) = 256 * 2 ^ (8 * n) := by
      rw [show 8 * (n + 1) = 8 + 8 * n by omega, Nat.pow_add]
    have hdiv_lt : v / 256 < 2 ^ (8 * n) := by omega
    have hmap : ((List.range n).map ((fun j => BitVec.ofNat 8 (v / 2 ^ (8 * j))) ∘ Nat.succ)) =
        (List.range n).map (fun j => BitVec.ofNat 8 ((v / 256) / 2 ^ (8 * j))) := by
      apply List.map_congr_left
      intro j _
      simp only [Function.comp_apply]
      congr 1
      rw [show 8 * (j + 1) = 8 + 8 * j by omega, Nat.pow_add, show (2 : Nat) ^ 8 = 256 by decide,
        Nat.div_div_eq_div_mul]
    rw [hmap, ih (v / 256) hdiv_lt]
    omega

private theorem bv64_ushr8_ofNat (v : Nat) (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 v) >>> 8 = BitVec.ofNat 64 (v / 256) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt (by omega : v / 256 < 2 ^ 64),
    Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 8 = 256 by decide]

private theorem bv64_extract_byte_ushr8 (w : Word) (j : Nat) (hj : j + 1 < 8) :
    (w >>> 8).extractLsb' (8 * j) 8 = w.extractLsb' (8 * (j + 1)) 8 := by
  have h := word_ushr_byte w 1 (by omega) j (by omega)
  simp only [show 8 * 1 = 8 from rfl, show j + 1 < 8 by omega, ↓reduceIte] at h
  exact h

private theorem bv64_truncate8_eq_extract0 (w : Word) :
    w.truncate 8 = w.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.truncate, hi]

private theorem tailWritePreserves_trans {s1 s2 s3 : MachineState}
    (h1 : TailWritePreserves s1 s2) (h2 : TailWritePreserves s2 s3) :
    TailWritePreserves s1 s3 :=
  fun a ha => (h2 a ha).trans (h1 a ha)

private theorem codeAt_append {pc : Nat} {xs ys : List Instruction}
    (hx : CodeAt pc xs) (hy : CodeAt (pc + xs.length) ys) :
    CodeAt pc (xs ++ ys) := by
  refine ⟨by have := hy.1; simp [List.length_append]; omega, fun j hj => ?_⟩
  simp only [List.length_append] at hj
  by_cases hlt : j < xs.length
  · rw [List.getElem_append_left hlt]; exact hx.2 j hlt
  · rw [List.getElem_append_right (by omega)]
    simpa only [show pc + xs.length + (j - xs.length) = pc + j by omega] using hy.2 (j - xs.length) (by omega)

private theorem list_getElem_of_eq {α : Type} {l1 l2 : List α} (h : l1 = l2) {j : Nat}
    (h1 : j < l1.length) (h2 : j < l2.length) : l1[j]'h1 = l2[j]'h2 := by
  subst h; rfl

private theorem bv64_slt_zero_pos (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 63) :
    BitVec.slt 0#64 (BitVec.ofNat 64 n) = true := by
  rw [BitVec.slt_eq_decide]
  have h0 : (0#64 : Word).toInt = 0 := by decide
  have hn : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_cond]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)]
    rw [if_pos (by omega)]
  rw [h0, hn]; exact decide_eq_true (by omega)

private theorem bv64_slt_zero_nonpos (n : Nat) (h : n ≤ 8) :
    BitVec.slt 0#64 (BitVec.ofNat 64 n + signExtend12 (4088#12)) = false := by
  have hse : signExtend12 (4088#12) = BitVec.ofNat 64 (2 ^ 64 - 8) :=
    signExtend12_neg 8 (by omega) (by omega)
  rw [hse, ← BitVec.ofNat_add, BitVec.slt_eq_decide]
  have h0 : (0#64 : Word).toInt = 0 := by decide
  rw [h0, decide_eq_false_iff_not]
  by_cases h8 : n = 8
  · subst h8
    have hz : BitVec.ofNat 64 (8 + (2 ^ 64 - 8)) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; simp [show 8 + (2 ^ 64 - 8) = 2 ^ 64 by omega]
    rw [hz, h0]; omega
  · have hlt : n + (2 ^ 64 - 8) < 2 ^ 64 := by omega
    have hge : 2 ^ 63 ≤ n + (2 ^ 64 - 8) := by omega
    have hto : (BitVec.ofNat 64 (n + (2 ^ 64 - 8))).toInt = ((n + (2 ^ 64 - 8) : Nat) : Int) - (2 ^ 64 : Nat) := by
      rw [BitVec.toInt_eq_toNat_cond]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      rw [if_neg (by omega)]
    rw [hto]; omega

private theorem bv64_sub_small (a b : Nat) (hb1 : 1 ≤ b) (hb2 : b ≤ 2048) (hab : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a + signExtend12 (BitVec.ofNat 12 (4096 - b)) = BitVec.ofNat 64 (a - b) := by
  rw [signExtend12_neg b hb1 hb2, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [show a + (2 ^ 64 - b) = (a - b) + 2 ^ 64 by omega, Nat.add_mod_right]

private theorem setByte_proof_getByte {s : MachineState} {dst query : Nat} {b : Byte}
    (hdst : dst < 2 ^ 64) (hq : query < 2 ^ 64) :
    (s.setByte (BitVec.ofNat 64 dst) b).getByte (BitVec.ofNat 64 query) =
      if query = dst then b else s.getByte (BitVec.ofNat 64 query) := by
  rw [set_byte_read]
  by_cases h : query = dst
  · subst h; simp
  · have hne : BitVec.ofNat 64 query ≠ BitVec.ofNat 64 dst := by
      intro heq; have hn := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hdst] at hn; omega
    rw [if_neg hne, if_neg h]

private theorem rev_tail_cyc_le (n : Nat) (hn : n ≤ 993) :
    6 + 2 + 131 * (n / 64) + 2 + 35 * ((n % 64) / 16) + 1 + 5 * (n % 16) ≤ 2086 := by
  have hcases : n / 64 ≤ 14 ∨ (n / 64 = 15 ∧ (n % 64) / 16 ≤ 1) ∨
      (n / 64 = 15 ∧ (n % 64) / 16 = 2 ∧ n % 16 ≤ 1) := by omega
  rcases hcases with h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;> omega

/-! ### 2. Flush Forward Write Buffer (`PC 7223..7229`, `2 + 5 * r.val` cycles) -/

private theorem openRuns_flush_wbuf_loop {clean : Prop} {base : Nat} {written : List Byte}
    (hbd : base + 8 ≤ 8556390424) :
    ∀ k (hk1 : 1 ≤ k) (hk8 : k ≤ 8) (m : Nat) (hm : m + k ≤ 8) (hlen : written.length = base + m + k) (s : MachineState),
      s.pc = pcAt 7225 →
      s.getReg .x10 = BitVec.ofNat 64 (11341403200 + base + m) →
      s.getReg .x14 = BitVec.ofNat 64 (8 * k) →
      (clean → ∀ j (hj : j < base + m), s.getByte (BitVec.ofNat 64 (11341403200 + j)) = written[j]'(by omega)) →
      (clean → ∀ j (hj : j < k), (s.getReg .x12).extractLsb' (8 * j) 8 = written[base + m + j]'(by omega)) →
      ∃ s' : MachineState,
        OpenRuns s (5 * k) (5 * k) s' ∧
        s'.pc = pcAt 7230 ∧
        s'.getReg .x10 = BitVec.ofNat 64 (11341403200 + written.length) ∧
        RegsEqExcept [.x10, .x12, .x14] s s' ∧
        ProofWritePreserves s s' ∧
        (clean → ProofPrefix s' written) := by
  intro k
  induction k with
  | zero => intro hk1; omega
  | succ k ih =>
    intro _ hk8 m hm hlen s hpc hx10 hx14 hbytes hrem
    have hsb_addr : s.getReg .x10 + signExtend12 (0#12) = BitVec.ofNat 64 (11341403200 + base + m) := by
      rw [hx10, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hsb_val : accessValid (s.getReg .x10 + signExtend12 (0#12)) 1 = true := by
      rw [hsb_addr]; exact accessValid_ofNat _ 1 (by omega) (by omega)
    have h0 := step_SB (s := s) (by decide) hpc (rfl : openInstr 7225 = .base (.SB .x10 .x12 (0#12))) hsb_val
    set s1 := (s.setByte (s.getReg .x10 + signExtend12 (0#12)) ((s.getReg .x12).truncate 8)).setPC (pcAt 7226)
    have h1 := step_ADDI (s := s1) (by decide) rfl (rfl : openInstr 7226 = .base (.ADDI .x10 .x10 (1#12)))
    set s2 := (s1.setReg .x10 (s1.getReg .x10 + signExtend12 (1#12))).setPC (pcAt 7227)
    have h2 := step_SRLI (s := s2) (by decide) rfl (rfl : openInstr 7227 = .base (.SRLI .x12 .x12 (8#6)))
    set s3 := (s2.setReg .x12 (s2.getReg .x12 >>> (8#6).toNat)).setPC (pcAt 7228)
    have h3 := step_ADDI (s := s3) (by decide) rfl (rfl : openInstr 7228 = .base (.ADDI .x14 .x14 (4088#12)))
    set s4 := (s3.setReg .x14 (s3.getReg .x14 + signExtend12 (4088#12))).setPC (pcAt 7229)
    have hs4_x10 : s4.getReg .x10 = BitVec.ofNat 64 (11341403200 + base + (m + 1)) := by
      simp only [s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hx10,
        signExtend12_nonneg 1 (by omega), ← BitVec.ofNat_add]
      congr 1
    have hs4_x14 : s4.getReg .x14 = BitVec.ofNat 64 (8 * k) := by
      simp only [s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hx14]
      simpa only [show 8 * (k + 1) - 8 = 8 * k by omega, show (BitVec.ofNat 12 (4096 - 8)) = 4088#12 from rfl] using
        bv64_sub_small (8 * (k + 1)) 8 (by omega) (by omega) (by omega) (by omega)
    have hs4_x12 : s4.getReg .x12 = (s.getReg .x12) >>> 8 := by
      simp [s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne']
    have hp4 : ProofWritePreserves s s4 := by
      intro a ha
      simp only [s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hsb_addr]
      exact ProofWritePreserves.setByte_proof (by omega) (by omega) a ha
    have hregs4 : RegsEqExcept [.x10, .x12, .x14] s s4 := by
      intro reg hreg
      have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
      have h12' : reg ≠ .x12 := fun h => hreg (by simp [h])
      have h14' : reg ≠ .x14 := fun h => hreg (by simp [h])
      simp [s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne' .x14 reg h14'.symm,
        getReg_setReg_ne' .x12 reg h12'.symm, getReg_setReg_ne' .x10 reg h10'.symm]
    have hbytes4 : clean → ∀ j (hj : j < base + (m + 1)),
        s4.getByte (BitVec.ofNat 64 (11341403200 + j)) = written[j]'(by omega) := by
      intro hcl j hj
      simp only [s4, s3, s2, s1, getByte_setPC, getByte_setReg, hsb_addr]
      rw [setByte_proof_getByte (by omega) (by omega)]
      by_cases hlast : j = base + m
      · rw [if_pos (by omega), bv64_truncate8_eq_extract0]
        simpa only [Nat.mul_zero, Nat.add_zero, hlast] using hrem hcl 0 (by omega)
      · rw [if_neg (by omega)]
        exact hbytes hcl j (by omega)
    cases k with
    | zero =>
      have h4 := step_BNE_not_taken (s := s4) (by decide) rfl
        (rfl : openInstr 7229 = .base (.BNE .x14 .x0 (8176#13))) (by rw [hs4_x14]; rfl)
      set s5 := s4.setPC (pcAt 7230)
      refine ⟨s5, (((h0.trans h1).trans h2).trans h3).trans h4, rfl,
        by simpa only [s5, MachineState.getReg_setPC, hlen, Nat.add_assoc] using hs4_x10,
        fun r hr => (by simp [s5] : s5.getReg r = s4.getReg r).trans (hregs4 r hr),
        hp4.trans (fun _ _ => by simp [s5]),
        fun hcl j hj => by simp only [s5, getByte_setPC]; exact hbytes4 hcl j (by omega)⟩
    | succ k' =>
      have hne0 : s4.getReg .x14 ≠ s4.getReg .x0 := by
        rw [hs4_x14]; intro h; have hn := congrArg BitVec.toNat h
        simp only [show (s4.getReg .x0).toNat = 0 from rfl, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega : 8 * (k' + 1) < 2 ^ 64)] at hn; omega
      have hbr : pcAt 7229 + signExtend13 (8176#13) = pcAt 7225 := by
        simpa only [show 8192 - 4 * (7229 - 7225) = 8176 by decide] using pcAt_add_neg13 7229 7225 (by omega) (by omega)
      have h4 := step_BNE_taken (s := s4) (by decide) rfl
        (rfl : openInstr 7229 = .base (.BNE .x14 .x0 (8176#13))) hne0 hbr
      set s5 := s4.setPC (pcAt 7225)
      have hrem5 : clean → ∀ j (hj : j < k' + 1),
          (s5.getReg .x12).extractLsb' (8 * j) 8 = written[base + (m + 1) + j]'(by omega) := by
        intro hcl j hj
        rw [show s5.getReg .x12 = (s.getReg .x12) >>> 8 by simpa [s5] using hs4_x12,
          bv64_extract_byte_ushr8 _ j (by omega)]
        simpa only [show base + (m + 1) + j = base + m + (j + 1) by omega] using hrem hcl (j + 1) (by omega)
      obtain ⟨s', hrest, hpc', h10', hreg', hp', hpref'⟩ := ih (by omega) (by omega) (m + 1) (by omega) (by omega) s5 rfl
        (by simpa [s5] using hs4_x10) (by simpa [s5] using hs4_x14)
        (fun hcl j hj => by simp only [s5, getByte_setPC]; exact hbytes4 hcl j hj) hrem5
      have hp5 : ProofWritePreserves s4 s5 := fun _ _ => by simp [s5]
      refine ⟨s', ?_, hpc', h10',
        fun r hr => (hreg' r hr).trans ((by simp [s5] : s5.getReg r = s4.getReg r).trans (hregs4 r hr)),
        hp4.trans (hp5.trans hp'), hpref'⟩
      have htot := ((((h0.trans h1).trans h2).trans h3).trans h4).trans hrest
      simpa only [show 1 + 1 + 1 + 1 + 1 + 5 * (k' + 1) = 5 * (k' + 1 + 1) by omega] using htot

/-- Flush remaining `r.val` buffered proof bytes (`PC 7223..7229`, `2 + 5 * r.val` cycles). -/
theorem openRuns_flush_wbuf {clean : Prop} {r : Fin 8} {base : Nat} {written : List Byte} {s : MachineState}
    (hpc : s.pc = pcAt 7223)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r.val))
    (hw : WriterState clean s r false base 0 written) :
    ∃ s' : MachineState,
      OpenRuns s (2 + 5 * r.val) (2 + 5 * r.val) s' ∧
      s'.pc = pcAt PC_flush_tail64 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (11341403200 + written.length) ∧
      RegsEqExcept [.x10, .x12, .x14] s s' ∧
      ProofWritePreserves s s' ∧
      (clean → ProofPrefix s' written) := by
  have hlen := hw.hlen
  have hbd := hw.hbound
  have h0 := step_ADDI (s := s) (by decide) hpc (rfl : openInstr 7223 = .base (.ADDI .x10 .x25 (0#12)))
  set s1 := (s.setReg .x10 (s.getReg .x25 + signExtend12 (0#12))).setPC (pcAt 7224)
  have hs1_10 : s1.getReg .x10 = BitVec.ofNat 64 (11341403200 + base) := by
    simp [s1, hw.rx25, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl]
  have hs1_14 : s1.getReg .x14 = BitVec.ofNat 64 (8 * r.val) := by simp [s1, getReg_setReg_ne', hx14]
  by_cases hr0 : r.val = 0
  · have hbr : pcAt 7224 + signExtend13 (24#13) = pcAt 7230 := by
      simpa only [show 4 * (7230 - 7224) = 24 by decide] using pcAt_add_pos13 7224 7230 (by omega) (by omega)
    have h1 := step_BEQ_taken (s := s1) (by decide) rfl
      (rfl : openInstr 7224 = .base (.BEQ .x14 .x0 (24#13))) (by rw [hs1_14, hr0]; rfl) hbr
    set s2 := s1.setPC (pcAt 7230)
    refine ⟨s2, by simpa only [hr0] using h0.trans h1, rfl,
      by simp [s2, hs1_10, hlen, hr0],
      fun reg hreg => by have h10' : reg ≠ .x10 := fun h => hreg (by simp [h]); simp [s2, s1, getReg_setReg_ne' .x10 reg h10'.symm],
      fun _ _ => by simp [s2, s1],
      fun hcl j hj => by simp only [s2, s1, getByte_setPC, getByte_setReg]; exact hw.hbytes hcl j (by omega)⟩
  · have hne0 : s1.getReg .x14 ≠ s1.getReg .x0 := by
      rw [hs1_14]; intro h; have hn := congrArg BitVec.toNat h
      have := r.isLt
      simp only [show (s1.getReg .x0).toNat = 0 from rfl, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : 8 * r.val < 2 ^ 64)] at hn; omega
    have h1 := step_BEQ_not_taken (s := s1) (by decide) rfl
      (rfl : openInstr 7224 = .base (.BEQ .x14 .x0 (24#13))) hne0
    set s2 := s1.setPC (pcAt 7225)
    have hr_lt := r.isLt
    obtain ⟨s', hrest, hpc', h10', hreg', hp', hpref'⟩ := openRuns_flush_wbuf_loop (clean := clean) (base := base)
      (written := written) (by omega) r.val (by omega) (by omega) 0 (by omega) (by omega) s2 rfl
      (by simpa [s2] using hs1_10) (by simpa [s2] using hs1_14)
      (fun hcl j hj => by simp only [s2, s1, getByte_setPC, getByte_setReg]; exact hw.hbytes hcl j (by omega))
      (fun hcl j hj => by
        have hrem := hw.hrem hcl
        simp only [Bool.false_eq_true, hr0, ↓reduceIte] at hrem
        have hx12_eq : s2.getReg .x12 = s.getReg .x12 := by simp [s2, s1, getReg_setReg_ne']
        rw [hx12_eq]
        exact hrem.1 j hj)
    have hp2 : ProofWritePreserves s s2 := fun _ _ => by simp [s2, s1]
    refine ⟨s', by simpa only [show 1 + 1 + 5 * r.val = 2 + 5 * r.val by omega] using (h0.trans h1).trans hrest,
      hpc', h10',
      fun reg hreg => (hreg' reg hreg).trans (by
        have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
        simp [s2, s1, getReg_setReg_ne' .x10 reg h10'.symm]),
      hp2.trans hp', hpref'⟩

/-! ### 3. Flush Remaining Tail Bits (`PC 7230..7236`, `≤ 42` cycles) & `pack6Bits` Equivalence -/

private theorem openRuns_flush_tail64_loop {clean : Prop} {tBuf tCnt flushes : Nat}
    (hbd : 8 * flushes + 16 ≤ 48719475936) (htBuf : tBuf < 2 ^ tCnt) (htCnt : tCnt < 64) :
    ∀ k (hk1 : 1 ≤ k) (m remBits : Nat) (hrem_pos : 1 ≤ remBits) (hrem_eq : k = (remBits + 7) / 8)
      (hm : m + k = (tCnt + 7) / 8) (s : MachineState),
      s.pc = pcAt 7232 →
      s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + 8 * flushes + m) →
      s.getReg .x17 = BitVec.ofNat 64 remBits →
      (clean → s.getReg .x16 = BitVec.ofNat 64 (tBuf / 2 ^ (8 * m))) →
      (clean → ∀ j < m, s.getByte (BitVec.ofNat 64 (tailBufBase + 8 * flushes + j)) =
          BitVec.ofNat 8 (tBuf / 2 ^ (8 * j))) →
      ∃ s' : MachineState,
        OpenRuns s (5 * k) (5 * k) s' ∧
        s'.pc = pcAt PC_rev_tail_start ∧
        s'.getReg .x15 = BitVec.ofNat 64 (tailBufBase + 8 * flushes + (tCnt + 7) / 8) ∧
        RegsEqExcept [.x15, .x16, .x17] s s' ∧
        TailWritePreserves s s' ∧
        (∀ j < 8 * flushes, s'.getByte (BitVec.ofNat 64 (tailBufBase + j)) =
            s.getByte (BitVec.ofNat 64 (tailBufBase + j))) ∧
        (clean → ∀ j < (tCnt + 7) / 8, s'.getByte (BitVec.ofNat 64 (tailBufBase + 8 * flushes + j)) =
            BitVec.ofNat 8 (tBuf / 2 ^ (8 * j))) := by
  intro k
  induction k with
  | zero => intro hk1; omega
  | succ k ih =>
    intro _ m remBits hrem_pos hrem_eq hm s hpc hx15 hx17 hx16 hbytes
    have htBuf64 : tBuf < 2 ^ 64 := lt_of_lt_of_le htBuf (Nat.pow_le_pow_right (by omega) (by omega))
    have hsb_addr : s.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + 8 * flushes + m) := by
      rw [hx15, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hsb_val : accessValid (s.getReg .x15 + signExtend12 (0#12)) 1 = true := by
      rw [hsb_addr]; exact accessValid_ofNat _ 1 (by unfold tailBufBase; omega) (by unfold tailBufBase; omega)
    have h0 := step_SB (s := s) (by decide) hpc (rfl : openInstr 7232 = .base (.SB .x15 .x16 (0#12))) hsb_val
    set s1 := (s.setByte (s.getReg .x15 + signExtend12 (0#12)) ((s.getReg .x16).truncate 8)).setPC (pcAt 7233)
    have h1 := step_ADDI (s := s1) (by decide) rfl (rfl : openInstr 7233 = .base (.ADDI .x15 .x15 (1#12)))
    set s2 := (s1.setReg .x15 (s1.getReg .x15 + signExtend12 (1#12))).setPC (pcAt 7234)
    have h2 := step_SRLI (s := s2) (by decide) rfl (rfl : openInstr 7234 = .base (.SRLI .x16 .x16 (8#6)))
    set s3 := (s2.setReg .x16 (s2.getReg .x16 >>> (8#6).toNat)).setPC (pcAt 7235)
    have h3 := step_ADDI (s := s3) (by decide) rfl (rfl : openInstr 7235 = .base (.ADDI .x17 .x17 (4088#12)))
    set s4 := (s3.setReg .x17 (s3.getReg .x17 + signExtend12 (4088#12))).setPC (pcAt 7236)
    have hs4_x15 : s4.getReg .x15 = BitVec.ofNat 64 (tailBufBase + 8 * flushes + (m + 1)) := by
      simp only [s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hx15,
        signExtend12_nonneg 1 (by omega), ← BitVec.ofNat_add]
      congr 1
    have hs4_x17_raw : s4.getReg .x17 = BitVec.ofNat 64 remBits + signExtend12 (4088#12) := by
      simp [s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hx17]
    have hs4_x16 : clean → s4.getReg .x16 = BitVec.ofNat 64 (tBuf / 2 ^ (8 * (m + 1))) := fun hcl => by
      simp only [s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hx16 hcl,
        show (8#6 : BitVec 6).toNat = 8 from rfl]
      rw [bv64_ushr8_ofNat _ (lt_of_le_of_lt (Nat.div_le_self _ _) htBuf64)]
      congr 1
      rw [Nat.div_div_eq_div_mul, show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_add,
        show 8 * m + 8 = 8 * (m + 1) by omega]
    have htw4 : TailWritePreserves s s4 := by
      intro a ha
      simp only [s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hsb_addr]
      have halA : alignToDword (BitVec.ofNat 64 (tailBufBase + 8 * flushes + m)) =
          BitVec.ofNat 64 (8 * ((tailBufBase + 8 * flushes + m) / 8)) := by
        simpa only [show 8 * ((tailBufBase + 8 * flushes + m) / 8) + (tailBufBase + 8 * flushes + m) % 8 =
            tailBufBase + 8 * flushes + m by omega] using
          alignToDword_ofNat_eq (8 * ((tailBufBase + 8 * flushes + m) / 8))
            ((tailBufBase + 8 * flushes + m) % 8) (by omega) (by unfold tailBufBase; omega)
      have hne : a ≠ alignToDword (BitVec.ofNat 64 (tailBufBase + 8 * flushes + m)) := by
        rw [halA]; intro h; apply ha
        rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]
        unfold tailBufBase; omega
      simp only [MachineState.setByte]
      exact MachineState.getMem_setMem_ne hne
    have hregs4 : RegsEqExcept [.x15, .x16, .x17] s s4 := by
      intro reg hreg
      have h15' : reg ≠ .x15 := fun h => hreg (by simp [h])
      have h16' : reg ≠ .x16 := fun h => hreg (by simp [h])
      have h17' : reg ≠ .x17 := fun h => hreg (by simp [h])
      simp [s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne' .x17 reg h17'.symm,
        getReg_setReg_ne' .x16 reg h16'.symm, getReg_setReg_ne' .x15 reg h15'.symm]
    have hfl_pres4 : ∀ j < 8 * flushes,
        s4.getByte (BitVec.ofNat 64 (tailBufBase + j)) = s.getByte (BitVec.ofNat 64 (tailBufBase + j)) := by
      intro j hj
      simp only [s4, s3, s2, s1, getByte_setPC, getByte_setReg, hsb_addr]
      rw [setByte_proof_getByte (by unfold tailBufBase; omega) (by unfold tailBufBase; omega), if_neg (by omega)]
    have hbytes4 : clean → ∀ j < m + 1,
        s4.getByte (BitVec.ofNat 64 (tailBufBase + 8 * flushes + j)) = BitVec.ofNat 8 (tBuf / 2 ^ (8 * j)) := by
      intro hcl j hj
      simp only [s4, s3, s2, s1, getByte_setPC, getByte_setReg, hsb_addr]
      rw [setByte_proof_getByte (by unfold tailBufBase; omega) (by unfold tailBufBase; omega)]
      by_cases hlast : j = m
      · rw [if_pos (by omega), hx16 hcl, hlast]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
        exact Nat.mod_mod_of_dvd _ (by decide)
      · rw [if_neg (by omega)]; exact hbytes hcl j (by omega)
    cases k with
    | zero =>
      have hle8 : remBits ≤ 8 := by omega
      have hslt : BitVec.slt (s4.getReg .x0) (s4.getReg .x17) = false := by
        rw [show s4.getReg .x0 = 0#64 from rfl, hs4_x17_raw]
        exact bv64_slt_zero_nonpos remBits hle8
      have h4 := step_BLT_not_taken (s := s4) (by decide) rfl
        (rfl : openInstr 7236 = .base (.BLT .x0 .x17 (8176#13))) hslt
      set s5 := s4.setPC (pcAt 7237)
      refine ⟨s5, (((h0.trans h1).trans h2).trans h3).trans h4, rfl,
        by simpa only [s5, MachineState.getReg_setPC, show m + 1 = (tCnt + 7) / 8 by omega] using hs4_x15,
        fun r hr => (by simp [s5] : s5.getReg r = s4.getReg r).trans (hregs4 r hr),
        tailWritePreserves_trans htw4 (fun _ _ => by simp [s5]),
        fun j hj => by simp only [s5, getByte_setPC]; exact hfl_pres4 j hj,
        fun hcl j hj => by simp only [s5, getByte_setPC]; exact hbytes4 hcl j (by omega)⟩
    | succ k' =>
      have hgt8 : 9 ≤ remBits := by omega
      have hrem_le64 : remBits ≤ 64 := by omega
      have hs4_x17 : s4.getReg .x17 = BitVec.ofNat 64 (remBits - 8) := by
        rw [hs4_x17_raw]
        simpa only [show (BitVec.ofNat 12 (4096 - 8)) = 4088#12 from rfl] using
          bv64_sub_small remBits 8 (by omega) (by omega) (by omega) (by omega)
      have hslt : BitVec.slt (s4.getReg .x0) (s4.getReg .x17) = true := by
        rw [show s4.getReg .x0 = 0#64 from rfl, hs4_x17]
        exact bv64_slt_zero_pos (remBits - 8) (by omega) (by omega)
      have hbr : pcAt 7236 + signExtend13 (8176#13) = pcAt 7232 := by
        simpa only [show 8192 - 4 * (7236 - 7232) = 8176 by decide] using pcAt_add_neg13 7236 7232 (by omega) (by omega)
      have h4 := step_BLT_taken (s := s4) (by decide) rfl
        (rfl : openInstr 7236 = .base (.BLT .x0 .x17 (8176#13))) hslt hbr
      set s5 := s4.setPC (pcAt 7232)
      obtain ⟨s', hrest, hpc', h15', hreg', htw', hfl', hbytes'⟩ :=
        ih (by omega) (m + 1) (remBits - 8) (by omega) (by omega) (by omega) s5 rfl
          (by simpa [s5] using hs4_x15) (by simpa [s5] using hs4_x17)
          (fun hcl => by simpa [s5] using hs4_x16 hcl)
          (fun hcl j hj => by simp only [s5, getByte_setPC]; exact hbytes4 hcl j hj)
      refine ⟨s', ?_, hpc', h15',
        fun r hr => (hreg' r hr).trans ((by simp [s5] : s5.getReg r = s4.getReg r).trans (hregs4 r hr)),
        tailWritePreserves_trans htw4 (tailWritePreserves_trans (fun _ _ => by simp [s5]) htw'),
        fun j hj => (hfl' j hj).trans (by simp only [s5, getByte_setPC]; exact hfl_pres4 j hj),
        hbytes'⟩
      have htot := ((((h0.trans h1).trans h2).trans h3).trans h4).trans hrest
      simpa only [show 1 + 1 + 1 + 1 + 1 + 5 * (k' + 1) = 5 * (k' + 1 + 1) by omega] using htot

/-- Flush remaining partial 64-bit tail word (`PC 7230..7236`, `≤ 42` cycles) and match `pack6Bits tails` byte-for-byte. -/
theorem openRuns_flush_tail64 {clean : Prop} {tails : List (BitVec 6)} {flushes : Nat} {s : MachineState}
    (hpc : s.pc = pcAt PC_flush_tail64)
    (ht : TailState clean s tails flushes) :
    let n := (pack6Bits tails).length
    ∃ cyc s',
      OpenRuns s cyc cyc s' ∧
      cyc ≤ 42 ∧
      s'.pc = pcAt PC_rev_tail_start ∧
      s'.getReg .x15 = BitVec.ofNat 64 (tailBufBase + n) ∧
      RegsEqExcept [.x15, .x16, .x17] s s' ∧
      TailWritePreserves s s' ∧
      (clean → ∀ j (hj : j < n), s'.getByte (BitVec.ofNat 64 (tailBufBase + j)) = (pack6Bits tails)[j]) := by
  set tCnt := (6 * tails.length) % 64
  have htCnt_lt : tCnt < 64 := Nat.mod_lt _ (by omega)
  have hbits := ht.hbits
  have hbd := ht.hbound
  have hn_eq : (pack6Bits tails).length = 8 * flushes + (tCnt + 7) / 8 := by
    rw [pack6Bits_length]; omega
  have h0 := step_ADDI (s := s) (by decide) hpc (rfl : openInstr 7230 = .base (.ADDI .x17 .x17 (64#12)))
  set s1 := (s.setReg .x17 (s.getReg .x17 + signExtend12 (64#12))).setPC (pcAt 7231)
  have hs1_17 : s1.getReg .x17 = BitVec.ofNat 64 tCnt := by
    simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
      ht.rx17, signExtend12_nonneg 64 (by omega), negCnt, ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [show 2 ^ 64 - 64 + tCnt + 64 = tCnt + 2 ^ 64 by omega, Nat.add_mod_right]
  have hs1_15 : s1.getReg .x15 = BitVec.ofNat 64 (tailBufBase + 8 * flushes) := by
    simp [s1, getReg_setReg_ne', ht.rx15]
  by_cases ht0 : tCnt = 0
  · have hbr : pcAt 7231 + signExtend13 (24#13) = pcAt 7237 := by
      simpa only [show 4 * (7237 - 7231) = 24 by decide] using pcAt_add_pos13 7231 7237 (by omega) (by omega)
    have h1 := step_BEQ_taken (s := s1) (by decide) rfl
      (rfl : openInstr 7231 = .base (.BEQ .x17 .x0 (24#13))) (by rw [hs1_17, ht0]; rfl) hbr
    set s2 := s1.setPC (pcAt 7237)
    have hn0 : (pack6Bits tails).length = 8 * flushes := by rw [hn_eq, ht0]; omega
    refine ⟨2, s2, h0.trans h1, by omega, rfl, by simp [s2, hs1_15, hn0],
      fun reg hreg => by have h17' : reg ≠ .x17 := fun h => hreg (by simp [h]); simp [s2, s1, getReg_setReg_ne' .x17 reg h17'.symm],
      fun _ _ => by simp [s2, s1], fun hcl => ?_⟩
    obtain ⟨tBuf, htBuf_lt, _, hsum⟩ := ht.hdata hcl
    have htBuf0 : tBuf = 0 := by simp [tCnt, ht0] at htBuf_lt; exact htBuf_lt
    rw [htBuf0, Nat.mul_zero, Nat.add_zero] at hsum
    set actual := (List.range (8 * flushes)).map fun j => s2.getByte (BitVec.ofNat 64 (tailBufBase + j))
    have hact_eq : actual = (List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j)) := by
      apply List.map_congr_left; intro j _; simp [s2, s1, getByte_setPC, getByte_setReg]
    have hlist_eq : actual = pack6Bits tails := by
      apply bytesToNat_inj
      · simp [actual, hn0]
      · rw [hact_eq, hsum, pack6Bits_bytesToNat]
    intro j hj
    have hj' : j < 8 * flushes := by omega
    have hget : actual[j]'(by simp [actual, hj']) = s2.getByte (BitVec.ofNat 64 (tailBufBase + j)) := by
      simp [actual]
    exact hget.symm.trans (list_getElem_of_eq hlist_eq _ hj)
  · have hne0 : s1.getReg .x17 ≠ s1.getReg .x0 := by
      rw [hs1_17]; intro h; have hn := congrArg BitVec.toNat h
      simp only [show (s1.getReg .x0).toNat = 0 from rfl, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : tCnt < 2 ^ 64)] at hn; omega
    have h1 := step_BEQ_not_taken (s := s1) (by decide) rfl
      (rfl : openInstr 7231 = .base (.BEQ .x17 .x0 (24#13))) hne0
    set s2 := s1.setPC (pcAt 7232)
    set remB := (tCnt + 7) / 8
    -- Extract conditional tBuf cleanly using Classical.em or existential on clean
    have hrun_any : ∃ s' : MachineState,
        OpenRuns s2 (5 * remB) (5 * remB) s' ∧
        s'.pc = pcAt PC_rev_tail_start ∧
        s'.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (pack6Bits tails).length) ∧
        RegsEqExcept [.x15, .x16, .x17] s2 s' ∧
        TailWritePreserves s2 s' ∧
        (clean → ∀ j (hj : j < (pack6Bits tails).length),
          s'.getByte (BitVec.ofNat 64 (tailBufBase + j)) = (pack6Bits tails)[j]) := by
      by_cases hcl : clean
      · obtain ⟨tBuf, htBuf_lt, hx16, hsum⟩ := ht.hdata hcl
        obtain ⟨s', hrest, hpc', h15', hreg', htw', hfl', hbytes'⟩ :=
          openRuns_flush_tail64_loop (clean := clean) (tBuf := tBuf) (tCnt := tCnt) (flushes := flushes)
            hbd htBuf_lt htCnt_lt remB (by omega) 0 tCnt (by omega) rfl (by omega) s2 rfl
            (by simpa [s2] using hs1_15) (by simpa [s2] using hs1_17)
            (fun _ => by simpa [s2, s1, getReg_setReg_ne'] using hx16)
            (fun _ j hj => by omega)
        refine ⟨s', hrest, hpc', by simpa only [hn_eq, Nat.add_assoc] using h15', hreg', htw', fun _ => ?_⟩
        set actual := (List.range (8 * flushes + remB)).map fun j => s'.getByte (BitVec.ofNat 64 (tailBufBase + j))
        have hact_split : actual =
            ((List.range (8 * flushes)).map fun j => s.getByte (BitVec.ofNat 64 (tailBufBase + j))) ++
            ((List.range remB).map fun j => BitVec.ofNat 8 (tBuf / 2 ^ (8 * j))) := by
          unfold actual
          rw [List.range_add, List.map_append, List.map_map]
          congr 1
          · apply List.map_congr_left; intro j hj
            rw [hfl' j (List.mem_range.mp hj)]; simp [s2, s1, getByte_setPC, getByte_setReg]
          · apply List.map_congr_left; intro j hj
            simpa only [Function.comp_apply, Nat.add_assoc] using hbytes' hcl j (List.mem_range.mp hj)
        have htBuf_rem : tBuf < 2 ^ (8 * remB) :=
          lt_of_lt_of_le htBuf_lt (Nat.pow_le_pow_right (by omega) (by omega))
        have hlist_eq : actual = pack6Bits tails := by
          apply bytesToNat_inj
          · simp [actual, hn_eq, remB]
          · rw [hact_split, bytesToNat_append_list, List.length_map, List.length_range,
              show 8 * (8 * flushes) = 64 * flushes by omega, bytesToNat_ofNat_div tBuf remB htBuf_rem,
              hsum, pack6Bits_bytesToNat]
        intro j hj
        have hj' : j < 8 * flushes + remB := by omega
        have hget : actual[j]'(by simp [actual, hj']) = s'.getByte (BitVec.ofNat 64 (tailBufBase + j)) := by
          simp [actual]
        exact hget.symm.trans (list_getElem_of_eq hlist_eq _ hj)
      · obtain ⟨s', hrest, hpc', h15', hreg', htw', _, _⟩ :=
          openRuns_flush_tail64_loop (clean := clean) (tBuf := 0) (tCnt := tCnt) (flushes := flushes)
            hbd (by positivity) htCnt_lt remB (by omega) 0 tCnt (by omega) rfl (by omega) s2 rfl
            (by simpa [s2] using hs1_15) (by simpa [s2] using hs1_17)
            (fun h => absurd h hcl) (fun h => absurd h hcl)
        exact ⟨s', hrest, hpc', by simpa only [hn_eq, Nat.add_assoc] using h15', hreg', htw',
          fun h => absurd h hcl⟩
    obtain ⟨s', hrest, hpc', h15', hreg', htw', hbytes'⟩ := hrun_any
    refine ⟨2 + 5 * remB, s', by simpa only [show 1 + 1 + 5 * remB = 2 + 5 * remB by omega] using (h0.trans h1).trans hrest,
      by omega, hpc', h15',
      fun reg hreg => (hreg' reg hreg).trans (by
        have h17' : reg ≠ .x17 := fun h => hreg (by simp [h])
        simp [s2, s1, getReg_setReg_ne' .x17 reg h17'.symm]),
      tailWritePreserves_trans (fun _ _ => by simp [s2, s1]) htw', hbytes'⟩

/-! ### 4. Unrolled 64/16/1 Tail Reversal (`PC 7237..7418`, `≤ 2086` cycles) -/

def revPairsCode (k : Nat) : List Instruction :=
  (List.range k).flatMap fun j =>
    [.base (.LBU .x6 .x15 (BitVec.ofNat 12 (k - 1 - j))),
     .base (.SB .x10 .x6 (BitVec.ofNat 12 j))]

private def revPairsSlice (k start count : Nat) : List Instruction :=
  (List.range count).flatMap fun i =>
    [.base (.LBU .x6 .x15 (BitVec.ofNat 12 (k - 1 - (start + i)))),
     .base (.SB .x10 .x6 (BitVec.ofNat 12 (start + i)))]

private theorem codeAt_rev64_0 : CodeAt 7246 (revPairsSlice 64 0 16) :=
  codeAt_of_list_eq _ _ (by decide) rfl

private theorem codeAt_rev64_1 : CodeAt 7278 (revPairsSlice 64 16 16) :=
  codeAt_of_list_eq _ _ (by decide) rfl

private theorem codeAt_rev64_2 : CodeAt 7310 (revPairsSlice 64 32 16) :=
  codeAt_of_list_eq _ _ (by decide) rfl

private theorem codeAt_rev64_3 : CodeAt 7342 (revPairsSlice 64 48 16) :=
  codeAt_of_list_eq _ _ (by decide) rfl

private theorem revPairsCode_64_split :
    revPairsCode 64 = ((revPairsSlice 64 0 16 ++ revPairsSlice 64 16 16) ++ revPairsSlice 64 32 16) ++ revPairsSlice 64 48 16 := by
  have hr : List.range 64 =
      ((List.range 16 ++ (List.range 16).map (16 + ·)) ++ (List.range 16).map (32 + ·)) ++
      (List.range 16).map (48 + ·) := by decide
  unfold revPairsCode revPairsSlice
  rw [hr, List.flatMap_append, List.flatMap_append, List.flatMap_append,
    List.flatMap_map, List.flatMap_map, List.flatMap_map]
  rfl

private theorem codeAt_rev64 : CodeAt 7246 (revPairsCode 64) := by
  rw [revPairsCode_64_split]
  exact codeAt_append (codeAt_append (codeAt_append codeAt_rev64_0 codeAt_rev64_1) codeAt_rev64_2) codeAt_rev64_3

private theorem codeAt_rev16 : CodeAt 7379 (revPairsCode 16) :=
  codeAt_of_list_eq _ _ (by decide) rfl

private theorem revPairsCode_length (k : Nat) : (revPairsCode k).length = 2 * k := by
  unfold revPairsCode
  rw [List.length_flatMap]
  have : ((List.range k).map fun j => ([.base (.LBU .x6 .x15 (BitVec.ofNat 12 (k - 1 - j))),
      .base (.SB .x10 .x6 (BitVec.ofNat 12 j))] : List Instruction).length) = List.replicate k 2 := by
    apply List.ext_getElem <;> simp
  rw [this, List.sum_replicate, smul_eq_mul]; omega

private theorem openRuns_rev_pairs_aux {pc0 k srcOff dstOff : Nat}
    (hk : k ≤ 64)
    (hsrc_bd : srcOff + k ≤ 48719475936)
    (hdst_bd : dstOff + k ≤ 8556390424)
    (hcode : CodeAt pc0 (revPairsCode k)) :
    ∀ m (hm : m ≤ k) (s : MachineState),
      s.pc = pcAt (pc0 + 2 * m) →
      s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + srcOff) →
      s.getReg .x10 = BitVec.ofNat 64 (11341403200 + dstOff) →
      ∃ s' : MachineState,
        OpenRuns s (2 * (k - m)) (2 * (k - m)) s' ∧
        s'.pc = pcAt (pc0 + 2 * k) ∧
        RegsEqExcept [.x6] s s' ∧
        ProofWritePreserves s s' ∧
        (∀ q < dstOff + m, s'.getByte (BitVec.ofNat 64 (11341403200 + q)) =
            s.getByte (BitVec.ofNat 64 (11341403200 + q))) ∧
        (∀ j, m ≤ j → j < k → s'.getByte (BitVec.ofNat 64 (11341403200 + dstOff + j)) =
            s.getByte (BitVec.ofNat 64 (tailBufBase + srcOff + (k - 1 - j)))) := by
  intro m hm
  induction hrem : k - m generalizing m with
  | zero =>
    intro s hpc _ _
    have hmk : m = k := by omega
    subst hmk
    exact ⟨s, OpenRuns.refl s, hpc, fun _ _ => rfl, ProofWritePreserves.refl s,
      fun _ _ => rfl, fun j hj1 hj2 => by omega⟩
  | succ d ih =>
    intro s hpc hx15 hx10
    have hmlt : m < k := by omega
    have hbd : pc0 + 2 * k ≤ OPEN_CODE_LEN := by have := hcode.1; rw [revPairsCode_length] at this; exact this
    have hget_pair : ∀ j (hj : j < k),
        openInstr (pc0 + 2 * j) = .base (.LBU .x6 .x15 (BitVec.ofNat 12 (k - 1 - j))) ∧
        openInstr (pc0 + 2 * j + 1) = .base (.SB .x10 .x6 (BitVec.ofNat 12 j)) := by
      intro j hj
      have hflat : revPairsCode k =
          ((List.range j).flatMap fun i => [.base (.LBU .x6 .x15 (BitVec.ofNat 12 (k - 1 - i))), .base (.SB .x10 .x6 (BitVec.ofNat 12 i))]) ++
          [.base (.LBU .x6 .x15 (BitVec.ofNat 12 (k - 1 - j))), .base (.SB .x10 .x6 (BitVec.ofNat 12 j))] ++
          (((List.range (k - 1 - j)).map (fun i => j + 1 + i)).flatMap fun i =>
            [.base (.LBU .x6 .x15 (BitVec.ofNat 12 (k - 1 - i))), .base (.SB .x10 .x6 (BitVec.ofNat 12 i))]) := by
        unfold revPairsCode
        have hrange : List.range k = List.range j ++ [j] ++ (List.range (k - 1 - j)).map (fun i => j + 1 + i) := by
          apply List.ext_getElem
          · simp; omega
          · intro idx h1 h2
            simp only [List.length_range] at h1
            by_cases ha : idx < j
            · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]; simp
            · by_cases hb : idx = j
              · subst hb; rw [List.getElem_append_left (by simp), List.getElem_append_right (by simp)]; simp
              · rw [List.getElem_append_right (by simp; omega)]; simp; omega
        rw [hrange, List.flatMap_append, List.flatMap_append, List.flatMap_singleton]
      have hlen_l : ((List.range j).flatMap fun i =>
          ([.base (.LBU .x6 .x15 (BitVec.ofNat 12 (k - 1 - i))), .base (.SB .x10 .x6 (BitVec.ofNat 12 i))] : List Instruction)).length = 2 * j := by
        rw [List.length_flatMap]
        have : ((List.range j).map fun i => ([.base (.LBU .x6 .x15 (BitVec.ofNat 12 (k - 1 - i))),
            .base (.SB .x10 .x6 (BitVec.ofNat 12 i))] : List Instruction).length) = List.replicate j 2 := by
          apply List.ext_getElem <;> simp
        rw [this, List.sum_replicate, smul_eq_mul]; omega
      have h0 := (hcode.2 (2 * j) (by rw [revPairsCode_length]; omega)).trans
        (list_getElem_of_eq hflat _ (by simp [hlen_l]))
      have h1 := (hcode.2 (2 * j + 1) (by rw [revPairsCode_length]; omega)).trans
        (list_getElem_of_eq hflat _ (by simp [hlen_l]))
      rw [List.getElem_append_left (by simp [hlen_l]), List.getElem_append_right (by omega)] at h0 h1
      simp only [hlen_l, Nat.sub_self, List.getElem_cons_zero] at h0
      simp only [hlen_l, show 2 * j + 1 - 2 * j = 1 by omega, List.getElem_cons_succ, List.getElem_cons_zero] at h1
      exact ⟨h0, h1⟩
    have ⟨hi0, hi1⟩ := hget_pair m hmlt
    have hlbu_addr : s.getReg .x15 + signExtend12 (BitVec.ofNat 12 (k - 1 - m)) =
        BitVec.ofNat 64 (tailBufBase + srcOff + (k - 1 - m)) := by
      rw [hx15, signExtend12_nonneg (k - 1 - m) (by omega), ← BitVec.ofNat_add]
    have hlbu_val : accessValid (s.getReg .x15 + signExtend12 (BitVec.ofNat 12 (k - 1 - m))) 1 = true := by
      rw [hlbu_addr]; exact accessValid_ofNat _ 1 (by unfold tailBufBase; omega) (by unfold tailBufBase; omega)
    have h0 := step_LBU (s := s) (by omega) hpc hi0 hlbu_val
    set s1 := (s.setReg .x6 ((s.getByte (s.getReg .x15 + signExtend12 (BitVec.ofNat 12 (k - 1 - m)))).zeroExtend 64)).setPC (pcAt (pc0 + 2 * m + 1))
    have hs1_10 : s1.getReg .x10 = BitVec.ofNat 64 (11341403200 + dstOff) := by simp [s1, getReg_setReg_ne', hx10]
    have hsb_addr : s1.getReg .x10 + signExtend12 (BitVec.ofNat 12 m) =
        BitVec.ofNat 64 (11341403200 + dstOff + m) := by
      rw [hs1_10, signExtend12_nonneg m (by omega), ← BitVec.ofNat_add]
    have hsb_val : accessValid (s1.getReg .x10 + signExtend12 (BitVec.ofNat 12 m)) 1 = true := by
      rw [hsb_addr]; exact accessValid_ofNat _ 1 (by omega) (by omega)
    have h1 := step_SB (s := s1) (by omega) rfl hi1 hsb_val
    set s2 := (s1.setByte (s1.getReg .x10 + signExtend12 (BitVec.ofNat 12 m)) ((s1.getReg .x6).truncate 8)).setPC (pcAt (pc0 + 2 * m + 1 + 1))
    have hs1_x6_tr : (s1.getReg .x6).truncate 8 = s.getByte (BitVec.ofNat 64 (tailBufBase + srcOff + (k - 1 - m))) := by
      simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hlbu_addr]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [BitVec.truncate, BitVec.zeroExtend, hi]
    have hp2 : ProofWritePreserves s s2 := by
      intro a ha
      simp only [s2, MachineState.getMem_setPC, hsb_addr]
      exact (ProofWritePreserves.setByte_proof (by omega) (by omega) a ha).trans (by simp [s1])
    have hs2_tail : ∀ j < k, s2.getByte (BitVec.ofNat 64 (tailBufBase + srcOff + j)) =
        s.getByte (BitVec.ofNat 64 (tailBufBase + srcOff + j)) := by
      intro j hj
      simp only [s2, getByte_setPC, hsb_addr]
      rw [setByte_proof_getByte (by omega) (by unfold tailBufBase; omega), if_neg (by unfold tailBufBase; omega)]
      simp [s1, getByte_setPC, getByte_setReg]
    have hs2_pre : ∀ q < dstOff + m, s2.getByte (BitVec.ofNat 64 (11341403200 + q)) =
        s.getByte (BitVec.ofNat 64 (11341403200 + q)) := by
      intro q hq
      simp only [s2, getByte_setPC, hsb_addr]
      rw [setByte_proof_getByte (by omega) (by omega), if_neg (by omega)]
      simp [s1, getByte_setPC, getByte_setReg]
    have hs2_cur : s2.getByte (BitVec.ofNat 64 (11341403200 + dstOff + m)) =
        s.getByte (BitVec.ofNat 64 (tailBufBase + srcOff + (k - 1 - m))) := by
      simp only [s2, getByte_setPC, hsb_addr, hs1_x6_tr]
      rw [setByte_proof_getByte (by omega) (by omega), if_pos rfl]
    obtain ⟨s', hrest, hpc', hreg', hp', hpre', hwr'⟩ :=
      ih (m + 1) (by omega) (by omega) s2 rfl
        (by simp [s2, s1, getReg_setByte, getReg_setReg_ne', hx15])
        (by simp [s2, s1, getReg_setByte, getReg_setReg_ne', hx10])
    refine ⟨s', by simpa only [show 1 + 1 + 2 * d = 2 * (d + 1) by omega] using (h0.trans h1).trans hrest,
      hpc',
      fun reg hreg => (hreg' reg hreg).trans (by
        have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
        simp [s2, s1, getReg_setByte, getReg_setReg_ne' .x6 reg h6'.symm]),
      hp2.trans hp',
      fun q hq => (hpre' q (by omega)).trans (hs2_pre q hq),
      fun j hj1 hj2 => ?_⟩
    by_cases hjm : j = m
    · subst hjm
      have hq := hpre' (dstOff + j) (by omega)
      rw [show 11341403200 + (dstOff + j) = 11341403200 + dstOff + j by omega] at hq
      exact hq.trans hs2_cur
    · exact (hwr' j (by omega) hj2).trans (hs2_tail (k - 1 - j) (by omega))

private theorem openRuns_rev_chunk_loop {pc0 k brOff : Nat}
    (hk1 : 1 ≤ k) (hk64 : k ≤ 64)
    (hcode : CodeAt (pc0 + 1) (revPairsCode k))
    (hi_sub : openInstr pc0 = .base (.ADDI .x15 .x15 (BitVec.ofNat 12 (4096 - k))))
    (hi_add : openInstr (pc0 + 1 + 2 * k) = .base (.ADDI .x10 .x10 (BitVec.ofNat 12 k)))
    (hi_bge : openInstr (pc0 + 2 + 2 * k) = .base (.BGEU .x15 .x7 (BitVec.ofNat 13 brOff)))
    (hbr : pcAt (pc0 + 2 + 2 * k) + signExtend13 (BitVec.ofNat 13 brOff) = pcAt pc0)
    (hbd_code : pc0 + 3 + 2 * k ≤ OPEN_CODE_LEN) :
    ∀ q (hq1 : 1 ≤ q) (rem dstOff : Nat) (hrem_lt : rem < k)
      (hsrc_bd : k * q + rem ≤ 48719475936) (hdst_bd : dstOff + k * q ≤ 8556390424) (s : MachineState),
      s.pc = pcAt pc0 →
      s.getReg .x7 = BitVec.ofNat 64 (tailBufBase + k) →
      s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + k * q + rem) →
      s.getReg .x10 = BitVec.ofNat 64 (11341403200 + dstOff) →
      ∃ s' : MachineState,
        OpenRuns s ((3 + 2 * k) * q) ((3 + 2 * k) * q) s' ∧
        s'.pc = pcAt (pc0 + 3 + 2 * k) ∧
        s'.getReg .x15 = BitVec.ofNat 64 (tailBufBase + rem) ∧
        s'.getReg .x10 = BitVec.ofNat 64 (11341403200 + dstOff + k * q) ∧
        RegsEqExcept [.x6, .x10, .x15] s s' ∧
        ProofWritePreserves s s' ∧
        (∀ p < dstOff, s'.getByte (BitVec.ofNat 64 (11341403200 + p)) =
            s.getByte (BitVec.ofNat 64 (11341403200 + p))) ∧
        (∀ j < k * q, s'.getByte (BitVec.ofNat 64 (11341403200 + dstOff + j)) =
            s.getByte (BitVec.ofNat 64 (tailBufBase + (k * q + rem - 1 - j)))) := by
  intro q
  induction q with
  | zero => intro hq1; omega
  | succ q ih =>
    intro _ rem dstOff hrem_lt hsrc_bd hdst_bd s hpc hx7 hx15 hx10
    have hkq0 : k * (q + 1) = k * q + k := by ring
    have h0 := step_ADDI (s := s) (by omega) hpc hi_sub
    set s1 := (s.setReg .x15 (s.getReg .x15 + signExtend12 (BitVec.ofNat 12 (4096 - k)))).setPC (pcAt (pc0 + 1))
    have hs1_15 : s1.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (k * q + rem)) := by
      simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hx15]
      rw [bv64_sub_small (tailBufBase + k * (q + 1) + rem) k hk1 (by omega) (by unfold tailBufBase; omega) (by unfold tailBufBase; omega)]
      congr 1; omega
    have hs1_10 : s1.getReg .x10 = BitVec.ofNat 64 (11341403200 + dstOff) := by simp [s1, getReg_setReg_ne', hx10]
    have hs1_7 : s1.getReg .x7 = BitVec.ofNat 64 (tailBufBase + k) := by simp [s1, getReg_setReg_ne', hx7]
    obtain ⟨s2, hr2, hpc2, hreg2, hp2, hpre2, hwr2⟩ := openRuns_rev_pairs_aux hk64 (srcOff := k * q + rem) (dstOff := dstOff)
      (by omega) (by omega) hcode 0 (by omega) s1 rfl hs1_15 hs1_10
    have hs2_pc : s2.pc = pcAt (pc0 + 1 + 2 * k) := hpc2
    have h1 := step_ADDI (s := s2) (by omega) hs2_pc hi_add
    set s3 := (s2.setReg .x10 (s2.getReg .x10 + signExtend12 (BitVec.ofNat 12 k))).setPC (pcAt (pc0 + 1 + 2 * k + 1))
    have hs3_pc : s3.pc = pcAt (pc0 + 2 + 2 * k) := by dsimp only [s3, MachineState.setPC]; congr 1; omega
    have hs3_15 : s3.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (k * q + rem)) := by
      simp [s3, getReg_setReg_ne', (hreg2 .x15 (by simp)).trans hs1_15]
    have hs3_7 : s3.getReg .x7 = BitVec.ofNat 64 (tailBufBase + k) := by
      have hs2_7 : s2.getReg .x7 = BitVec.ofNat 64 (tailBufBase + k) := (hreg2 .x7 (by simp)).trans hs1_7
      simp [s3, getReg_setReg_ne', hs2_7]
    have hs3_10 : s3.getReg .x10 = BitVec.ofNat 64 (11341403200 + (dstOff + k)) := by
      simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true,
        (hreg2 .x10 (by simp)).trans hs1_10, signExtend12_nonneg k (by omega), ← BitVec.ofNat_add]
      congr 1; omega
    have hp1 : ProofWritePreserves s s1 := fun _ _ => by simp [s1]
    have hp3' : ProofWritePreserves s2 s3 := fun _ _ => by simp [s3]
    have hp3 : ProofWritePreserves s s3 := hp1.trans (hp2.trans hp3')
    have hreg3 : RegsEqExcept [.x6, .x10, .x15] s s3 := by
      intro reg hreg
      have h6' : reg ≠ .x6 := fun h => hreg (by simp [h])
      have h10' : reg ≠ .x10 := fun h => hreg (by simp [h])
      have h15' : reg ≠ .x15 := fun h => hreg (by simp [h])
      exact (by simp [s3, getReg_setReg_ne' .x10 reg h10'.symm] : s3.getReg reg = s2.getReg reg).trans
        ((hreg2 reg (by simp [h6'])).trans (by simp [s1, getReg_setReg_ne' .x15 reg h15'.symm]))
    have hpre3 : ∀ p < dstOff, s3.getByte (BitVec.ofNat 64 (11341403200 + p)) =
        s.getByte (BitVec.ofNat 64 (11341403200 + p)) := fun p hp => by
      simp only [s3, getByte_setPC, getByte_setReg]
      exact (hpre2 p (by omega)).trans (by simp [s1, getByte_setPC, getByte_setReg])
    have hwr3 : ∀ j < k, s3.getByte (BitVec.ofNat 64 (11341403200 + dstOff + j)) =
        s.getByte (BitVec.ofNat 64 (tailBufBase + (k * q + rem) + (k - 1 - j))) := fun j hj => by
      simp only [s3, getByte_setPC, getByte_setReg]
      exact (hwr2 j (by omega) hj).trans (by simp [s1, getByte_setPC, getByte_setReg])
    cases q with
    | zero =>
      have hlt : (s3.getReg .x15).toNat < (s3.getReg .x7).toNat := by
        rw [hs3_15, hs3_7, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by unfold tailBufBase; omega), Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]
        omega
      have h2 := step_BGEU_not_taken (s := s3) (by omega) hs3_pc hi_bge hlt
      set s4 := s3.setPC (pcAt (pc0 + 2 + 2 * k + 1))
      refine ⟨s4, by simpa only [show 1 + 2 * (k - 0) + 1 + 1 = (3 + 2 * k) * (0 + 1) by omega] using ((h0.trans hr2).trans h1).trans h2,
        by dsimp only [s4, MachineState.setPC]; congr 1; omega,
        by simpa [s4] using hs3_15, by simpa [s4, Nat.add_assoc] using hs3_10,
        fun r hr => (by simp [s4] : s4.getReg r = s3.getReg r).trans (hreg3 r hr),
        hp3.trans (fun _ _ => by simp [s4]),
        fun p hp => by simp only [s4, getByte_setPC]; exact hpre3 p hp,
        fun j hj => by
          simp only [s4, getByte_setPC]
          simpa only [show k * 0 + rem + (k - 1 - j) = k * 1 + rem - 1 - j by omega, Nat.add_assoc] using hwr3 j (by omega)⟩
    | succ q' =>
      have hkq : k * (q' + 1 + 1) = k * (q' + 1) + k := by ring
      have hge : (s3.getReg .x7).toNat ≤ (s3.getReg .x15).toNat := by
        rw [hs3_15, hs3_7, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by unfold tailBufBase; omega), Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]
        have : k ≤ k * (q' + 1) := Nat.le_mul_of_pos_right k (by omega)
        omega
      have h2 := step_BGEU_taken (s := s3) (by omega) hs3_pc hi_bge hge hbr
      set s4 := s3.setPC (pcAt pc0)
      obtain ⟨s', hrest, hpc', h15', h10', hreg', hp', hpre', hwr'⟩ :=
        ih (by omega) rem (dstOff + k) hrem_lt (by omega) (by omega) s4 rfl
          (by simpa [s4] using hs3_7) (by simpa [s4, Nat.add_assoc] using hs3_15) (by simpa [s4] using hs3_10)
      have hs4_tail : ∀ a < 48719475936, s4.getByte (BitVec.ofNat 64 (tailBufBase + a)) = s.getByte (BitVec.ofNat 64 (tailBufBase + a)) := by
        intro a ha
        have halA : alignToDword (BitVec.ofNat 64 (tailBufBase + a)) =
            BitVec.ofNat 64 (8 * ((tailBufBase + a) / 8)) := by
          simpa only [show 8 * ((tailBufBase + a) / 8) + (tailBufBase + a) % 8 = tailBufBase + a by omega] using
            alignToDword_ofNat_eq (8 * ((tailBufBase + a) / 8)) ((tailBufBase + a) % 8) (by omega) (by unfold tailBufBase; omega)
        simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
        exact (show s4.getMem _ = s3.getMem _ from rfl).trans (hp3 _ (by
          rw [halA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]; unfold tailBufBase; omega))
      have hp4' : ProofWritePreserves s3 s4 := fun _ _ => rfl
      refine ⟨s', ?_, hpc', h15',
        by simpa only [show 11341403200 + (dstOff + k) + k * (q' + 1) = 11341403200 + dstOff + k * (q' + 1 + 1) by omega] using h10',
        fun r hr => (hreg' r hr).trans ((by simp [s4] : s4.getReg r = s3.getReg r).trans (hreg3 r hr)),
        hp3.trans (hp4'.trans hp'),
        fun p hp => (hpre' p (by omega)).trans (by simp only [s4, getByte_setPC]; exact hpre3 p hp),
        fun j hj => ?_⟩
      · have htot := (((h0.trans hr2).trans h1).trans h2).trans hrest
        have hstep_c : 1 + 2 * (k - 0) + 1 + 1 + (3 + 2 * k) * (q' + 1) = (3 + 2 * k) * (q' + 1 + 1) := by
          simp only [Nat.sub_zero]; ring
        simpa only [hstep_c] using htot
      · by_cases hjk : j < k
        · have hq := hpre' (dstOff + j) (by omega)
          rw [show 11341403200 + (dstOff + j) = 11341403200 + dstOff + j by omega] at hq
          have h := hq.trans (by simp only [s4, getByte_setPC]; exact hwr3 j hjk)
          simpa only [show tailBufBase + (k * (q' + 1) + rem) + (k - 1 - j) =
              tailBufBase + (k * (q' + 1 + 1) + rem - 1 - j) by omega] using h
        · have h := hwr' (j - k) (by omega)
          rw [show 11341403200 + (dstOff + k) + (j - k) = 11341403200 + dstOff + j by omega] at h
          have ht := h.trans (hs4_tail _ (by omega))
          simpa only [show k * (q' + 1) + rem - 1 - (j - k) = k * (q' + 1 + 1) + rem - 1 - j by omega] using ht

private theorem openRuns_rev1_loop :
    ∀ rem (hrem1 : 1 ≤ rem) (dstOff : Nat) (hrem_bd : rem ≤ 48719475936) (hdst_bd : dstOff + rem ≤ 8556390424)
      (s : MachineState),
      s.pc = pcAt PC_rev_tail_1 →
      s.getReg .x31 = BitVec.ofNat 64 tailBufBase →
      s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + rem) →
      s.getReg .x10 = BitVec.ofNat 64 (11341403200 + dstOff) →
      ∃ s' : MachineState,
        OpenRuns s (5 * rem) (5 * rem) s' ∧
        s'.pc = pcAt PC_open_finish ∧
        s'.getReg .x10 = BitVec.ofNat 64 (11341403200 + dstOff + rem) ∧
        ProofWritePreserves s s' ∧
        (∀ p < dstOff, s'.getByte (BitVec.ofNat 64 (11341403200 + p)) =
            s.getByte (BitVec.ofNat 64 (11341403200 + p))) ∧
        (∀ j < rem, s'.getByte (BitVec.ofNat 64 (11341403200 + dstOff + j)) =
            s.getByte (BitVec.ofNat 64 (tailBufBase + (rem - 1 - j)))) := by
  intro rem
  induction rem with
  | zero => intro h; omega
  | succ rem ih =>
    intro _ dstOff hrem_bd hdst_bd s hpc hx31 hx15 hx10
    have h0 := step_ADDI (s := s) (by decide) hpc (rfl : openInstr 7414 = .base (.ADDI .x15 .x15 (4095#12)))
    set s1 := (s.setReg .x15 (s.getReg .x15 + signExtend12 (4095#12))).setPC (pcAt 7415)
    have hs1_15 : s1.getReg .x15 = BitVec.ofNat 64 (tailBufBase + rem) := by
      simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hx15]
      simpa only [show tailBufBase + (rem + 1) - 1 = tailBufBase + rem by omega, show (BitVec.ofNat 12 (4096 - 1)) = 4095#12 from rfl] using
        bv64_sub_small (tailBufBase + (rem + 1)) 1 (by omega) (by omega) (by unfold tailBufBase; omega) (by unfold tailBufBase; omega)
    have hlbu_addr : s1.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + rem) := by
      rw [hs1_15, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hlbu_val : accessValid (s1.getReg .x15 + signExtend12 (0#12)) 1 = true := by
      rw [hlbu_addr]; exact accessValid_ofNat _ 1 (by unfold tailBufBase; omega) (by unfold tailBufBase; omega)
    have h1 := step_LBU (s := s1) (by decide) rfl (rfl : openInstr 7415 = .base (.LBU .x6 .x15 (0#12))) hlbu_val
    set s2 := (s1.setReg .x6 ((s1.getByte (s1.getReg .x15 + signExtend12 (0#12))).zeroExtend 64)).setPC (pcAt 7416)
    have hs2_10 : s2.getReg .x10 = BitVec.ofNat 64 (11341403200 + dstOff) := by simp [s2, s1, getReg_setReg_ne', hx10]
    have hsb_addr : s2.getReg .x10 + signExtend12 (0#12) = BitVec.ofNat 64 (11341403200 + dstOff) := by
      rw [hs2_10, signExtend12_nonneg 0 (by omega), show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]
    have hsb_val : accessValid (s2.getReg .x10 + signExtend12 (0#12)) 1 = true := by
      rw [hsb_addr]; exact accessValid_ofNat _ 1 (by omega) (by omega)
    have h2 := step_SB (s := s2) (by decide) rfl (rfl : openInstr 7416 = .base (.SB .x10 .x6 (0#12))) hsb_val
    set s3 := (s2.setByte (s2.getReg .x10 + signExtend12 (0#12)) ((s2.getReg .x6).truncate 8)).setPC (pcAt 7417)
    have h3 := step_ADDI (s := s3) (by decide) rfl (rfl : openInstr 7417 = .base (.ADDI .x10 .x10 (1#12)))
    set s4 := (s3.setReg .x10 (s3.getReg .x10 + signExtend12 (1#12))).setPC (pcAt 7418)
    have hs2_x6_tr : (s2.getReg .x6).truncate 8 = s.getByte (BitVec.ofNat 64 (tailBufBase + rem)) := by
      simp only [s2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hlbu_addr]
      simp only [s1, getByte_setPC, getByte_setReg]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simp [BitVec.truncate, BitVec.zeroExtend, hi]
    have hs4_15 : s4.getReg .x15 = BitVec.ofNat 64 (tailBufBase + rem) := by
      simp [s4, s3, s2, getReg_setByte, getReg_setReg_ne', hs1_15]
    have hs4_31 : s4.getReg .x31 = BitVec.ofNat 64 tailBufBase := by
      simp [s4, s3, s2, s1, getReg_setByte, getReg_setReg_ne', hx31]
    have hs4_10 : s4.getReg .x10 = BitVec.ofNat 64 (11341403200 + (dstOff + 1)) := by
      simp only [s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne',
        MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hx10,
        signExtend12_nonneg 1 (by omega), ← BitVec.ofNat_add, Nat.add_assoc]
    have hp4 : ProofWritePreserves s s4 := by
      intro a ha
      simp only [s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg, hsb_addr]
      exact ProofWritePreserves.setByte_proof (by omega) (by omega) a ha
    have hpre4 : ∀ p < dstOff, s4.getByte (BitVec.ofNat 64 (11341403200 + p)) =
        s.getByte (BitVec.ofNat 64 (11341403200 + p)) := fun p hp => by
      simp only [s4, s3, getByte_setPC, getByte_setReg, hsb_addr]
      rw [setByte_proof_getByte (by omega) (by omega), if_neg (by omega)]
      simp [s2, s1, getByte_setPC, getByte_setReg]
    have hcur4 : s4.getByte (BitVec.ofNat 64 (11341403200 + dstOff)) =
        s.getByte (BitVec.ofNat 64 (tailBufBase + rem)) := by
      simp only [s4, s3, getByte_setPC, getByte_setReg, hsb_addr, hs2_x6_tr]
      rw [setByte_proof_getByte (by omega) (by omega), if_pos rfl]
    cases rem with
    | zero =>
      have h4 := step_BNE_not_taken (s := s4) (by decide) rfl
        (rfl : openInstr 7418 = .base (.BNE .x15 .x31 (8176#13))) (by rw [hs4_15, hs4_31]; simp)
      set s5 := s4.setPC (pcAt 7419)
      refine ⟨s5, (((h0.trans h1).trans h2).trans h3).trans h4, rfl,
        by simpa [s5, Nat.add_assoc] using hs4_10, hp4.trans (fun _ _ => by simp [s5]),
        fun p hp => by simp only [s5, getByte_setPC]; exact hpre4 p hp,
        fun j hj => by
          have hj0 : j = 0 := by omega
          subst hj0
          simp only [s5, getByte_setPC, Nat.add_zero, show (0 : Nat) + 1 - 1 - 0 = 0 from rfl]
          exact hcur4⟩
    | succ rem' =>
      have hne : s4.getReg .x15 ≠ s4.getReg .x31 := by
        rw [hs4_15, hs4_31]; intro h; have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold tailBufBase; omega : tailBufBase + (rem' + 1) < 2 ^ 64),
          Nat.mod_eq_of_lt (by unfold tailBufBase; omega : tailBufBase < 2 ^ 64)] at hn; omega
      have hbr : pcAt 7418 + signExtend13 (8176#13) = pcAt 7414 := by
        simpa only [show 8192 - 4 * (7418 - 7414) = 8176 by decide] using pcAt_add_neg13 7418 7414 (by omega) (by omega)
      have h4 := step_BNE_taken (s := s4) (by decide) rfl
        (rfl : openInstr 7418 = .base (.BNE .x15 .x31 (8176#13))) hne hbr
      set s5 := s4.setPC (pcAt 7414)
      obtain ⟨s', hrest, hpc', h10', hp', hpre', hwr'⟩ := ih (by omega) (dstOff + 1) (by omega) (by omega) s5 rfl
        (by simpa [s5] using hs4_31) (by simpa [s5] using hs4_15) (by simpa [s5] using hs4_10)
      have hs5_tail : ∀ a < 48719475936, s5.getByte (BitVec.ofNat 64 (tailBufBase + a)) = s.getByte (BitVec.ofNat 64 (tailBufBase + a)) := by
        intro a ha
        have halA : alignToDword (BitVec.ofNat 64 (tailBufBase + a)) = BitVec.ofNat 64 (8 * ((tailBufBase + a) / 8)) := by
          simpa only [show 8 * ((tailBufBase + a) / 8) + (tailBufBase + a) % 8 = tailBufBase + a by omega] using
            alignToDword_ofNat_eq (8 * ((tailBufBase + a) / 8)) ((tailBufBase + a) % 8) (by omega) (by unfold tailBufBase; omega)
        simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
        exact (show s5.getMem _ = s4.getMem _ from rfl).trans (hp4 _ (by
          rw [halA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]; unfold tailBufBase; omega))
      have hp5' : ProofWritePreserves s4 s5 := fun _ _ => rfl
      refine ⟨s', by simpa only [show 1 + 1 + 1 + 1 + 1 + 5 * (rem' + 1) = 5 * (rem' + 1 + 1) by omega] using
          ((((h0.trans h1).trans h2).trans h3).trans h4).trans hrest,
        hpc', by simpa only [show 11341403200 + (dstOff + 1) + (rem' + 1) = 11341403200 + dstOff + (rem' + 1 + 1) by omega] using h10',
        hp4.trans (hp5'.trans hp'),
        fun p hp => (hpre' p (by omega)).trans (by simp only [s5, getByte_setPC]; exact hpre4 p hp),
        fun j hj => ?_⟩
      by_cases hj0 : j = 0
      · subst hj0
        have hq := hpre' dstOff (by omega)
        exact hq.trans (by simp only [s5, getByte_setPC]; exact hcur4)
      · have h := hwr' (j - 1) (by omega)
        rw [show 11341403200 + (dstOff + 1) + (j - 1) = 11341403200 + dstOff + j by omega] at h
        have ht := h.trans (hs5_tail _ (by omega))
        simpa only [show rem' + 1 - 1 - (j - 1) = rem' + 1 + 1 - 1 - j by omega] using ht

/-- Full unrolled 64/16/1 tail reversal (`PC 7237..7418`). -/
theorem openRuns_rev_tail {clean : Prop} {fwdBytes : List Byte} {tails : List (BitVec 6)} {s : MachineState}
    (hbd_t : (pack6Bits tails).length ≤ 48719475936)
    (hbd_p : fwdBytes.length + (pack6Bits tails).length ≤ 8556390424)
    (hpc : s.pc = pcAt PC_rev_tail_start)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length))
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (pack6Bits tails).length))
    (hfwd : clean → ProofPrefix s fwdBytes)
    (htail : clean → ∀ j (hj : j < (pack6Bits tails).length),
      s.getByte (BitVec.ofNat 64 (tailBufBase + j)) = (pack6Bits tails)[j]) :
    let n := (pack6Bits tails).length
    let cyc := 6 + 2 + 131 * (n / 64) + 2 + 35 * ((n % 64) / 16) + 1 + 5 * (n % 16)
    ∃ s' : MachineState,
      OpenRuns s cyc cyc s' ∧
      s'.pc = pcAt PC_open_finish ∧
      s'.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length + n) ∧
      (clean → ProofPrefix s' (fwdBytes ++ pack6BitsRev tails)) := by
  set n := (pack6Bits tails).length
  -- 1. Load tailBufBase = 20000000000 into x31 (7237..7242, 6 cyc)
  have hl0 := step_ADDI (s := s) (by decide) hpc (rfl : openInstr 7237 = .base (.ADDI .x31 .x0 (2#12)))
  set s1 := (s.setReg .x31 (s.getReg .x0 + signExtend12 (2#12))).setPC (pcAt 7238)
  have hl1 := step_SLLI (s := s1) (by decide) rfl (rfl : openInstr 7238 = .base (.SLLI .x31 .x31 (11#6)))
  set s2 := (s1.setReg .x31 (s1.getReg .x31 <<< (11#6).toNat)).setPC (pcAt 7239)
  have hl2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 7239 = .base (.ADDI .x31 .x31 (672#12)))
  set s3 := (s2.setReg .x31 (s2.getReg .x31 + signExtend12 (672#12))).setPC (pcAt 7240)
  have hl3 := step_SLLI (s := s3) (by decide) rfl (rfl : openInstr 7240 = .base (.SLLI .x31 .x31 (11#6)))
  set s4 := (s3.setReg .x31 (s3.getReg .x31 <<< (11#6).toNat)).setPC (pcAt 7241)
  have hl4 := step_ADDI (s := s4) (by decide) rfl (rfl : openInstr 7241 = .base (.ADDI .x31 .x31 (761#12)))
  set s5 := (s4.setReg .x31 (s4.getReg .x31 + signExtend12 (761#12))).setPC (pcAt 7242)
  have hl5 := step_SLLI (s := s5) (by decide) rfl (rfl : openInstr 7242 = .base (.SLLI .x31 .x31 (11#6)))
  set s6 := (s5.setReg .x31 (s5.getReg .x31 <<< (11#6).toNat)).setPC (pcAt 7243)
  have hload := ((((hl0.trans hl1).trans hl2).trans hl3).trans hl4).trans hl5
  have hs6_31 : s6.getReg .x31 = BitVec.ofNat 64 tailBufBase := by
    simp only [s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, reduceCtorEq, not_false_eq_true, show s.getReg .x0 = 0#64 from rfl]
    decide
  have hs6_10 : s6.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length) := by
    simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx10]
  have hs6_15 : s6.getReg .x15 = BitVec.ofNat 64 (tailBufBase + n) := by
    simp [s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx15]
  have hs6_mem : ∀ a, s6.getMem a = s.getMem a := fun _ => by simp [s6, s5, s4, s3, s2, s1]
  -- 2. 64-byte stage (7243..7375)
  have h64_0 := step_ADDI (s := s6) (by decide) rfl (rfl : openInstr 7243 = .base (.ADDI .x7 .x31 (64#12)))
  set s7 := (s6.setReg .x7 (s6.getReg .x31 + signExtend12 (64#12))).setPC (pcAt 7244)
  have hs7_7 : s7.getReg .x7 = BitVec.ofNat 64 (tailBufBase + 64) := by
    simp [s7, hs6_31, signExtend12_nonneg 64 (by omega), ← BitVec.ofNat_add]
  have hs7_15 : s7.getReg .x15 = BitVec.ofNat 64 (tailBufBase + n) := by simp [s7, getReg_setReg_ne', hs6_15]
  have hs7_10 : s7.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length) := by simp [s7, getReg_setReg_ne', hs6_10]
  have hs7_31 : s7.getReg .x31 = BitVec.ofNat 64 tailBufBase := by simp [s7, getReg_setReg_ne', hs6_31]
  set q64 := n / 64
  set r64 := n % 64
  have hstage64 : ∃ sa : MachineState,
      OpenRuns s7 (1 + 131 * q64) (1 + 131 * q64) sa ∧
      sa.pc = pcAt PC_rev_tail_16_chk ∧
      sa.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
      sa.getReg .x15 = BitVec.ofNat 64 (tailBufBase + r64) ∧
      sa.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length + 64 * q64) ∧
      ProofWritePreserves s sa ∧
      (∀ p < fwdBytes.length, sa.getByte (BitVec.ofNat 64 (11341403200 + p)) = s.getByte (BitVec.ofNat 64 (11341403200 + p))) ∧
      (∀ j < 64 * q64, sa.getByte (BitVec.ofNat 64 (11341403200 + fwdBytes.length + j)) =
          s.getByte (BitVec.ofNat 64 (tailBufBase + (n - 1 - j)))) := by
    by_cases hq0 : q64 = 0
    · have hr64_eq : r64 = n := by omega
      have hlt : (s7.getReg .x15).toNat < (s7.getReg .x7).toNat := by
        rw [hs7_15, hs7_7, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by unfold tailBufBase; omega), Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]; omega
      have hbr : pcAt 7244 + signExtend13 (528#13) = pcAt 7376 := by
        simpa only [show 4 * (7376 - 7244) = 528 by decide] using pcAt_add_pos13 7244 7376 (by omega) (by omega)
      have hb := step_BLTU_taken (s := s7) (by decide) rfl
        (rfl : openInstr 7244 = .base (.BLTU .x15 .x7 (528#13))) hlt hbr
      set sa := s7.setPC (pcAt 7376)
      exact ⟨sa, by simpa only [hq0, Nat.mul_zero, Nat.add_zero] using hb, rfl,
        by simp [sa, hs7_31], by simp [sa, hs7_15, hr64_eq], by simp [sa, hs7_10, hq0],
        fun _ _ => by simp [sa, s7, hs6_mem],
        fun p _ => by simp [sa, s7, MachineState.getByte, hs6_mem],
        fun j hj => by omega⟩
    · have hge : (s7.getReg .x7).toNat ≤ (s7.getReg .x15).toNat := by
        rw [hs7_15, hs7_7, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by unfold tailBufBase; omega), Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]; omega
      have hb := step_BLTU_not_taken (s := s7) (by decide) rfl
        (rfl : openInstr 7244 = .base (.BLTU .x15 .x7 (528#13))) hge
      set s8 := s7.setPC (pcAt 7245)
      have hbr64 : pcAt (7245 + 2 + 2 * 64) + signExtend13 (BitVec.ofNat 13 7672) = pcAt 7245 := by
        simpa only [show 8192 - 4 * (7375 - 7245) = 7672 by decide] using pcAt_add_neg13 7375 7245 (by omega) (by omega)
      obtain ⟨sa, hr_a, hpc_a, h15_a, h10_a, hreg_a, hp_a, hpre_a, hwr_a⟩ :=
        openRuns_rev_chunk_loop (pc0 := 7245) (k := 64) (brOff := 7672) (by omega) (by omega)
          codeAt_rev64 rfl rfl rfl hbr64 (by decide) q64 (by omega) r64 fwdBytes.length (by omega)
          (by omega) (by omega) s8 rfl (by simp [s8, hs7_7])
          (by simpa only [s8, MachineState.getReg_setPC, show tailBufBase + 64 * q64 + r64 = tailBufBase + n by omega] using hs7_15)
          (by simp [s8, hs7_10])
      have hp8_s : ProofWritePreserves s s8 := fun _ _ => by simp [s8, s7, hs6_mem]
      refine ⟨sa, by simpa only [show 3 + 2 * 64 = 131 from rfl] using hb.trans hr_a, hpc_a,
        (hreg_a .x31 (by simp)).trans (by simp [s8, hs7_31]), h15_a, h10_a,
        hp8_s.trans hp_a,
        fun p hp' => (hpre_a p hp').trans (by simp [s8, s7, MachineState.getByte, hs6_mem]),
        fun j hj => (hwr_a j hj).trans (by simp [s8, s7, MachineState.getByte, hs6_mem, show 64 * q64 + r64 = n by omega])⟩
  obtain ⟨sa, hra, hpca, hsa_31, hsa_15, hsa_10, hpa, hpre_a, hwr_a⟩ := hstage64
  -- 3. 16-byte stage (7376..7412)
  have h16_0 := step_ADDI (s := sa) (by decide) hpca (rfl : openInstr 7376 = .base (.ADDI .x7 .x31 (16#12)))
  set sa1 := (sa.setReg .x7 (sa.getReg .x31 + signExtend12 (16#12))).setPC (pcAt 7377)
  have hsa1_7 : sa1.getReg .x7 = BitVec.ofNat 64 (tailBufBase + 16) := by
    simp [sa1, hsa_31, signExtend12_nonneg 16 (by omega), ← BitVec.ofNat_add]
  have hsa1_15 : sa1.getReg .x15 = BitVec.ofNat 64 (tailBufBase + r64) := by simp [sa1, getReg_setReg_ne', hsa_15]
  have hsa1_10 : sa1.getReg .x10 = BitVec.ofNat 64 (11341403200 + (fwdBytes.length + 64 * q64)) := by
    simp [sa1, getReg_setReg_ne', hsa_10, Nat.add_assoc]
  have hsa1_31 : sa1.getReg .x31 = BitVec.ofNat 64 tailBufBase := by simp [sa1, getReg_setReg_ne', hsa_31]
  set q16 := r64 / 16
  set r16 := r64 % 16
  have hr16_eq : r16 = n % 16 := by omega
  have hstage16 : ∃ sb : MachineState,
      OpenRuns sa1 (1 + 35 * q16) (1 + 35 * q16) sb ∧
      sb.pc = pcAt PC_rev_tail_rem ∧
      sb.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
      sb.getReg .x15 = BitVec.ofNat 64 (tailBufBase + r16) ∧
      sb.getReg .x10 = BitVec.ofNat 64 (11341403200 + (fwdBytes.length + 64 * q64 + 16 * q16)) ∧
      ProofWritePreserves sa sb ∧
      (∀ p < fwdBytes.length + 64 * q64, sb.getByte (BitVec.ofNat 64 (11341403200 + p)) =
          sa.getByte (BitVec.ofNat 64 (11341403200 + p))) ∧
      (∀ j < 16 * q16, sb.getByte (BitVec.ofNat 64 (11341403200 + (fwdBytes.length + 64 * q64) + j)) =
          sa.getByte (BitVec.ofNat 64 (tailBufBase + (r64 - 1 - j)))) := by
    by_cases hq0 : q16 = 0
    · have hr_eq : r16 = r64 := by omega
      have hlt : (sa1.getReg .x15).toNat < (sa1.getReg .x7).toNat := by
        rw [hsa1_15, hsa1_7, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by unfold tailBufBase; omega), Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]; omega
      have hbr : pcAt 7377 + signExtend13 (144#13) = pcAt 7413 := by
        simpa only [show 4 * (7413 - 7377) = 144 by decide] using pcAt_add_pos13 7377 7413 (by omega) (by omega)
      have hb := step_BLTU_taken (s := sa1) (by decide) rfl
        (rfl : openInstr 7377 = .base (.BLTU .x15 .x7 (144#13))) hlt hbr
      set sb := sa1.setPC (pcAt 7413)
      exact ⟨sb, by simpa only [hq0, Nat.mul_zero, Nat.add_zero] using hb, rfl,
        by simp [sb, hsa1_31], by simp [sb, hsa1_15, hr_eq], by simp [sb, hsa1_10, hq0],
        fun _ _ => by simp [sb, sa1], fun p _ => by simp [sb, sa1, getByte_setPC, getByte_setReg],
        fun j hj => by omega⟩
    · have hge : (sa1.getReg .x7).toNat ≤ (sa1.getReg .x15).toNat := by
        rw [hsa1_15, hsa1_7, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by unfold tailBufBase; omega), Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]; omega
      have hb := step_BLTU_not_taken (s := sa1) (by decide) rfl
        (rfl : openInstr 7377 = .base (.BLTU .x15 .x7 (144#13))) hge
      set sa2 := sa1.setPC (pcAt 7378)
      have hbr16 : pcAt (7378 + 2 + 2 * 16) + signExtend13 (BitVec.ofNat 13 8056) = pcAt 7378 := by
        simpa only [show 8192 - 4 * (7412 - 7378) = 8056 by decide] using pcAt_add_neg13 7412 7378 (by omega) (by omega)
      obtain ⟨sb, hr_b, hpc_b, h15_b, h10_b, hreg_b, hp_b, hpre_b, hwr_b⟩ :=
        openRuns_rev_chunk_loop (pc0 := 7378) (k := 16) (brOff := 8056) (by omega) (by omega)
          codeAt_rev16 rfl rfl rfl hbr16 (by decide) q16 (by omega) r16 (fwdBytes.length + 64 * q64) (by omega)
          (by omega) (by omega) sa2 rfl (by simp [sa2, hsa1_7])
          (by simpa only [sa2, MachineState.getReg_setPC, show tailBufBase + 16 * q16 + r16 = tailBufBase + r64 by omega] using hsa1_15)
          (by simp [sa2, hsa1_10])
      have hp_sa2 : ProofWritePreserves sa sa2 := fun _ _ => by simp [sa2, sa1]
      refine ⟨sb, by simpa only [show 3 + 2 * 16 = 35 from rfl] using hb.trans hr_b, hpc_b,
        (hreg_b .x31 (by simp)).trans (by simp [sa2, hsa1_31]), h15_b, by simpa only [Nat.add_assoc] using h10_b,
        hp_sa2.trans hp_b,
        fun p hp' => (hpre_b p hp').trans (by simp [sa2, sa1, getByte_setPC, getByte_setReg]),
        fun j hj => (hwr_b j hj).trans (by simp [sa2, sa1, getByte_setPC, getByte_setReg, show 16 * q16 + r16 = r64 by omega])⟩
  obtain ⟨sb, hrb, hpcb, hsb_31, hsb_15, hsb_10, hpb, hpre_b, hwr_b⟩ := hstage16
  -- 4. 1-byte remainder stage (7413..7418)
  have hstage1 : ∃ sc : MachineState,
      OpenRuns sb (1 + 5 * r16) (1 + 5 * r16) sc ∧
      sc.pc = pcAt PC_open_finish ∧
      sc.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length + n) ∧
      (∀ p < fwdBytes.length + 64 * q64 + 16 * q16, sc.getByte (BitVec.ofNat 64 (11341403200 + p)) =
          sb.getByte (BitVec.ofNat 64 (11341403200 + p))) ∧
      (∀ j < r16, sc.getByte (BitVec.ofNat 64 (11341403200 + (fwdBytes.length + 64 * q64 + 16 * q16) + j)) =
          sb.getByte (BitVec.ofNat 64 (tailBufBase + (r16 - 1 - j)))) := by
    by_cases hr0 : r16 = 0
    · have hbr : pcAt 7413 + signExtend13 (24#13) = pcAt 7419 := by
        simpa only [show 4 * (7419 - 7413) = 24 by decide] using pcAt_add_pos13 7413 7419 (by omega) (by omega)
      have hb := step_BEQ_taken (s := sb) (by decide) hpcb
        (rfl : openInstr 7413 = .base (.BEQ .x15 .x31 (24#13))) (by rw [hsb_15, hsb_31, hr0]; simp) hbr
      set sc := sb.setPC (pcAt 7419)
      refine ⟨sc, by simpa only [hr0, Nat.mul_zero, Nat.add_zero] using hb, rfl,
        by simpa only [sc, MachineState.getReg_setPC, show 11341403200 + (fwdBytes.length + 64 * q64 + 16 * q16) = 11341403200 + fwdBytes.length + n by omega] using hsb_10,
        fun p _ => by simp [sc, getByte_setPC], fun j hj => by omega⟩
    · have hne : sb.getReg .x15 ≠ sb.getReg .x31 := by
        rw [hsb_15, hsb_31]; intro h; have hn := congrArg BitVec.toNat h
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold tailBufBase; omega : tailBufBase + r16 < 2 ^ 64),
          Nat.mod_eq_of_lt (by unfold tailBufBase; omega : tailBufBase < 2 ^ 64)] at hn; omega
      have hb := step_BEQ_not_taken (s := sb) (by decide) hpcb
        (rfl : openInstr 7413 = .base (.BEQ .x15 .x31 (24#13))) hne
      set sb1 := sb.setPC (pcAt 7414)
      obtain ⟨sc, hr_c, hpc_c, h10_c, _, hpre_c, hwr_c⟩ := openRuns_rev1_loop r16 (by omega)
        (fwdBytes.length + 64 * q64 + 16 * q16) (by omega) (by omega) sb1 rfl
        (by simp [sb1, hsb_31]) (by simp [sb1, hsb_15]) (by simp [sb1, hsb_10])
      exact ⟨sc, hb.trans hr_c, hpc_c,
        by simpa only [show 11341403200 + (fwdBytes.length + 64 * q64 + 16 * q16) + r16 = 11341403200 + fwdBytes.length + n by omega] using h10_c,
        fun p hp => (hpre_c p hp).trans (by simp [sb1, getByte_setPC]),
        fun j hj => (hwr_c j hj).trans (by simp [sb1, getByte_setPC])⟩
  obtain ⟨sc, hrc, hpcc, hsc_10, hpre_c, hwr_c⟩ := hstage1
  have hp_sa_s : ∀ a < 48719475936, sa.getByte (BitVec.ofNat 64 (tailBufBase + a)) = s.getByte (BitVec.ofNat 64 (tailBufBase + a)) := by
    intro a ha
    have halA : alignToDword (BitVec.ofNat 64 (tailBufBase + a)) = BitVec.ofNat 64 (8 * ((tailBufBase + a) / 8)) := by
      simpa only [show 8 * ((tailBufBase + a) / 8) + (tailBufBase + a) % 8 = tailBufBase + a by omega] using
        alignToDword_ofNat_eq (8 * ((tailBufBase + a) / 8)) ((tailBufBase + a) % 8) (by omega) (by unfold tailBufBase; omega)
    simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
    exact hpa _ (by rw [halA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]; unfold tailBufBase; omega)
  have hp_sb_s : ∀ a < 48719475936, sb.getByte (BitVec.ofNat 64 (tailBufBase + a)) = s.getByte (BitVec.ofNat 64 (tailBufBase + a)) := by
    intro a ha
    have halA : alignToDword (BitVec.ofNat 64 (tailBufBase + a)) = BitVec.ofNat 64 (8 * ((tailBufBase + a) / 8)) := by
      simpa only [show 8 * ((tailBufBase + a) / 8) + (tailBufBase + a) % 8 = tailBufBase + a by omega] using
        alignToDword_ofNat_eq (8 * ((tailBufBase + a) / 8)) ((tailBufBase + a) % 8) (by omega) (by unfold tailBufBase; omega)
    simp only [MachineState.getByte]; apply congrArg (fun w => extractByte w _)
    exact (hpa.trans hpb) _ (by rw [halA, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold tailBufBase; omega)]; unfold tailBufBase; omega)
  refine ⟨sc, ?_, hpcc, hsc_10, fun hcl j hj => ?_⟩
  · have htot := ((((hload.trans h64_0).trans hra).trans h16_0).trans hrb).trans hrc
    have heq : 1 + 1 + 1 + 1 + 1 + 1 + 1 + (1 + 131 * q64) + 1 + (1 + 35 * q16) + (1 + 5 * r16) =
        6 + 2 + 131 * (n / 64) + 2 + 35 * ((n % 64) / 16) + 1 + 5 * (n % 16) := by omega
    simpa only [heq] using htot
  · simp only [List.length_append, pack6BitsRev, List.length_reverse] at hj
    by_cases hlt_f : j < fwdBytes.length
    · rw [List.getElem_append_left hlt_f]
      have h1 := hpre_c j (by omega)
      have h2 := hpre_b j (by omega)
      have h3 := hpre_a j hlt_f
      exact h1.trans (h2.trans (h3.trans (hfwd hcl j hlt_f)))
    · rw [List.getElem_append_right (by omega)]
      simp only [pack6BitsRev, List.getElem_reverse]
      set k := j - fwdBytes.length
      have hk_lt : k < n := by omega
      have hrev_idx : n - 1 - k < (pack6Bits tails).length := by omega
      have hgoal_eq : sc.getByte (BitVec.ofNat 64 (11341403200 + j)) =
          s.getByte (BitVec.ofNat 64 (tailBufBase + (n - 1 - k))) := by
        by_cases hk64 : k < 64 * q64
        · have h1 := hpre_c j (by omega)
          have h2 := hpre_b j (by omega)
          have h3 := hwr_a k hk64
          rw [show 11341403200 + fwdBytes.length + k = 11341403200 + j by omega] at h3
          exact h1.trans (h2.trans h3)
        · by_cases hk16 : k < 64 * q64 + 16 * q16
          · have h1 := hpre_c j (by omega)
            have h2 := hwr_b (k - 64 * q64) (by omega)
            rw [show 11341403200 + (fwdBytes.length + 64 * q64) + (k - 64 * q64) = 11341403200 + j by omega,
              show r64 - 1 - (k - 64 * q64) = n - 1 - k by omega] at h2
            exact h1.trans (h2.trans (hp_sa_s _ (by omega)))
          · have h1 := hwr_c (k - 64 * q64 - 16 * q16) (by omega)
            rw [show 11341403200 + (fwdBytes.length + 64 * q64 + 16 * q16) + (k - 64 * q64 - 16 * q16) = 11341403200 + j by omega,
              show r16 - 1 - (k - 64 * q64 - 16 * q16) = n - 1 - k by omega] at h1
            exact h1.trans (hp_sb_s _ (by omega))
      exact hgoal_eq.trans (htail hcl (n - 1 - k) hrev_idx)

/-! ### 5. Finish & Halt (`PC 7419..7428`, `10` cycles + `ECALL` at `7429`) -/

theorem openRuns_open_finish {totalLen : Nat} {s : MachineState}
    (hlen_bd : totalLen ≤ 8556390424)
    (hpc : s.pc = pcAt PC_open_finish)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (11341403200 + totalLen)) :
    ∃ s' : MachineState,
      OpenRuns s 10 10 s' ∧
      s'.pc = pcAt 7429 ∧
      s'.getReg .x5 = 1#64 ∧
      s'.getReg .x10 = 0#64 ∧
      s'.getReg .x11 = BitVec.ofNat 64 totalLen ∧
      (∀ a, s'.getMem a = s.getMem a) := by
  have h0 := step_ADDI (s := s) (by decide) hpc (rfl : openInstr 7419 = .base (.ADDI .x26 .x0 (1#12)))
  set s1 := (s.setReg .x26 (s.getReg .x0 + signExtend12 (1#12))).setPC (pcAt 7420)
  have h1 := step_SLLI (s := s1) (by decide) rfl (rfl : openInstr 7420 = .base (.SLLI .x26 .x26 (11#6)))
  set s2 := (s1.setReg .x26 (s1.getReg .x26 <<< (11#6).toNat)).setPC (pcAt 7421)
  have h2 := step_ADDI (s := s2) (by decide) rfl (rfl : openInstr 7421 = .base (.ADDI .x26 .x26 (656#12)))
  set s3 := (s2.setReg .x26 (s2.getReg .x26 + signExtend12 (656#12))).setPC (pcAt 7422)
  have h3 := step_SLLI (s := s3) (by decide) rfl (rfl : openInstr 7422 = .base (.SLLI .x26 .x26 (11#6)))
  set s4 := (s3.setReg .x26 (s3.getReg .x26 <<< (11#6).toNat)).setPC (pcAt 7423)
  have h4 := step_ADDI (s := s4) (by decide) rfl (rfl : openInstr 7423 = .base (.ADDI .x26 .x26 (2#12)))
  set s5 := (s4.setReg .x26 (s4.getReg .x26 + signExtend12 (2#12))).setPC (pcAt 7424)
  have h5 := step_SLLI (s := s5) (by decide) rfl (rfl : openInstr 7424 = .base (.SLLI .x26 .x26 (11#6)))
  set s6 := (s5.setReg .x26 (s5.getReg .x26 <<< (11#6).toNat)).setPC (pcAt 7425)
  have h6 := step_ADDI (s := s6) (by decide) rfl (rfl : openInstr 7425 = .base (.ADDI .x26 .x26 (1088#12)))
  set s7 := (s6.setReg .x26 (s6.getReg .x26 + signExtend12 (1088#12))).setPC (pcAt 7426)
  have hs7_26 : s7.getReg .x26 = BitVec.ofNat 64 11341403200 := by
    simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, reduceCtorEq, not_false_eq_true, show s.getReg .x0 = 0#64 from rfl]
    decide
  have hs7_10 : s7.getReg .x10 = BitVec.ofNat 64 (11341403200 + totalLen) := by
    simp [s7, s6, s5, s4, s3, s2, s1, getReg_setReg_ne', hx10]
  have h7 := step_SUB (s := s7) (by decide) rfl (rfl : openInstr 7426 = .base (.SUB .x11 .x10 .x26))
  set s8 := (s7.setReg .x11 (s7.getReg .x10 - s7.getReg .x26)).setPC (pcAt 7427)
  have h8 := step_ADDI (s := s8) (by decide) rfl (rfl : openInstr 7427 = .base (.ADDI .x5 .x0 (1#12)))
  set s9 := (s8.setReg .x5 (s8.getReg .x0 + signExtend12 (1#12))).setPC (pcAt 7428)
  have h9 := step_ADDI (s := s9) (by decide) rfl (rfl : openInstr 7428 = .base (.ADDI .x10 .x0 (0#12)))
  set s10 := (s9.setReg .x10 (s9.getReg .x0 + signExtend12 (0#12))).setPC (pcAt 7429)
  have hrun := ((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans h9
  refine ⟨s10, hrun, rfl, ?_, ?_, ?_, fun _ => by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]⟩
  · simp [s10, s9, getReg_setReg_ne', show s8.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 1 (by omega)]
  · simp [s10, show s9.getReg .x0 = 0#64 from rfl, signExtend12_nonneg 0 (by omega)]
  · simp only [s10, s9, s8, MachineState.getReg_setPC, getReg_setReg_ne',
      MachineState.getReg_setReg_eq, ne_eq, reduceCtorEq, not_false_eq_true, hs7_10, hs7_26]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : 11341403200 + totalLen < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : 11341403200 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : totalLen < 2 ^ 64)]
    rw [show 2 ^ 64 - 11341403200 + (11341403200 + totalLen) = totalLen + 2 ^ 64 by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- Complete epilogue from `PC 7223` (`flush_wbuf` -> `flush_tail64` -> `rev_tail` -> `open_finish`)
to `ECALL` at `PC 7429`, exporting exact cycle count `2 + 5 * r.val + tailEpiCyc` (`tailEpiCyc ≤ 2138` when `n ≤ 993`). -/
theorem openRuns_epilogue {clean : Prop} {r : Fin 8} {base flushes : Nat}
    {fwdBytes : List Byte} {tails : List (BitVec 6)} {s : MachineState}
    (hbd_p : fwdBytes.length + (pack6Bits tails).length ≤ 8556390424)
    (hpc : s.pc = pcAt 7223)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (8 * r.val))
    (hw : WriterState clean s r false base 0 fwdBytes)
    (ht : TailState clean s tails flushes) :
    let n := (pack6Bits tails).length
    ∃ tailEpiCyc s',
      OpenRuns s ((2 + 5 * r.val) + tailEpiCyc) ((2 + 5 * r.val) + tailEpiCyc) s' ∧
      tailEpiCyc ≤ 42 + (6 + 2 + 131 * (n / 64) + 2 + 35 * ((n % 64) / 16) + 1 + 5 * (n % 16)) + 10 ∧
      (n ≤ 993 → tailEpiCyc ≤ 2138) ∧
      s'.pc = pcAt 7429 ∧
      s'.getReg .x5 = 1#64 ∧
      s'.getReg .x10 = 0#64 ∧
      s'.getReg .x11 = BitVec.ofNat 64 (fwdBytes.length + n) ∧
      (clean → ProofPrefix s' (fwdBytes ++ pack6BitsRev tails)) := by
  set n := (pack6Bits tails).length
  obtain ⟨s1, hr1, hpc1, hs1_10, hreg1, hp1, hpref1⟩ := openRuns_flush_wbuf hpc hx14 hw
  have ht1 : TailState clean s1 tails flushes :=
    TailState.of_proofWrite ht hp1 (hreg1 .x15 (by decide)) (hreg1 .x16 (by decide)) (hreg1 .x17 (by decide))
  obtain ⟨c2, s2, hr2, hc2, hpc2, hs2_15, hreg2, htw2, htail2⟩ := openRuns_flush_tail64 hpc1 ht1
  have hs2_10 : s2.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length) :=
    (hreg2 .x10 (by decide)).trans hs1_10
  have hpref2 : clean → ProofPrefix s2 fwdBytes := by
    intro hcl j hj
    have hbd_f := hw.hbound; have hlen_f := hw.hlen
    have hal : alignToDword (BitVec.ofNat 64 (11341403200 + j)) =
        BitVec.ofNat 64 (8 * ((11341403200 + j) / 8)) := by
      simpa only [show 8 * ((11341403200 + j) / 8) + (11341403200 + j) % 8 = 11341403200 + j by omega] using
        alignToDword_ofNat_eq (8 * ((11341403200 + j) / 8)) ((11341403200 + j) % 8) (by omega) (by omega)
    have hmem : s2.getMem (alignToDword (BitVec.ofNat 64 (11341403200 + j))) =
        s1.getMem (alignToDword (BitVec.ofNat 64 (11341403200 + j))) :=
      htw2 _ (by rw [hal, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; unfold tailBufBase; omega)
    exact (by simp only [MachineState.getByte, hmem] : s2.getByte _ = s1.getByte _).trans (hpref1 hcl j hj)
  have hbd_t : n ≤ 48719475936 := by
    have := ht.hbits; have := ht.hbound; have := pack6Bits_length tails; omega
  obtain ⟨s3, hr3, hpc3, hs3_10, hpref3⟩ := openRuns_rev_tail hbd_t hbd_p hpc2 hs2_10 hs2_15 hpref2 htail2
  obtain ⟨s4, hr4, hpc4, hs4_5, hs4_10, hs4_11, hmem4⟩ := openRuns_open_finish hbd_p hpc3 (by simpa only [Nat.add_assoc] using hs3_10)
  set revCyc := 6 + 2 + 131 * (n / 64) + 2 + 35 * ((n % 64) / 16) + 1 + 5 * (n % 16)
  refine ⟨c2 + revCyc + 10, s4, ?_, by omega, fun hn => by have := rev_tail_cyc_le n hn; omega,
    hpc4, hs4_5, hs4_10, hs4_11, fun hcl j hj => ?_⟩
  · have htot := ((hr1.trans hr2).trans hr3).trans hr4
    simpa only [Nat.add_assoc] using htot
  · have hgb : s4.getByte (BitVec.ofNat 64 (11341403200 + j)) = s3.getByte (BitVec.ofNat 64 (11341403200 + j)) := by
      simp only [MachineState.getByte, hmem4]
    exact hgb.trans (hpref3 hcl j hj)

end CommitGolfCandidate.MoonOpen
