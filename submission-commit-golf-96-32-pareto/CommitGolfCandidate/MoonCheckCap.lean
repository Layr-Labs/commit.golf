import CommitGolfCandidate.MoonCheckPos

/-! Symbolic execution of the `check` program cap phase (`pc[156..249]`) and epilogue
(`pc[250..268]`): cap setup, 142-iteration 3-ary internal cap loop, 2-ary root hash,
exact proof-length check, and 32-byte commitment comparison. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Pure Cap-Frontier Prefix Helpers -/

def capFrontierCountPrefix (positions : Positions) (n : Nat) : Nat :=
  ∑ j ∈ Finset.range n, capNodeFrontierCount positions j

def capMarkedInternalPrefix (positions : Positions) (n : Nat) : Nat :=
  ∑ j ∈ Finset.range n, if capMark positions (286 + j) then 1 else 0

def capMarkPrefix (positions : Positions) (n u : Nat) : Bool :=
  if u < 286 + n then capMark positions u else false

def capChildOff (positions : Positions) (baseOff j r : Nat) : Nat :=
  let off0 := baseOff + 32 * capFrontierCountPrefix positions j
  if j < 142 then
    if r = 0 then off0
    else if r = 1 then off0 + (if !capMark positions (3 * j) then 32 else 0)
    else off0 + (if !capMark positions (3 * j) then 32 else 0) +
                (if !capMark positions (3 * j + 1) then 32 else 0)
  else
    if r = 0 then off0
    else off0 + (if !capMark positions 426 then 32 else 0)

theorem capFrontierCountPrefix_zero (positions : Positions) :
    capFrontierCountPrefix positions 0 = 0 := rfl

theorem capFrontierCountPrefix_succ (positions : Positions) (n : Nat) :
    capFrontierCountPrefix positions (n + 1) =
      capFrontierCountPrefix positions n + capNodeFrontierCount positions n :=
  Finset.sum_range_succ _ n

theorem capFrontierCountPrefix_le (positions : Positions) {n : Nat} (hn : n ≤ 143) :
    capFrontierCountPrefix positions n ≤ capFrontierCount positions :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hn)

theorem capFrontierCountPrefix_143 (positions : Positions) :
    capFrontierCountPrefix positions 143 = capFrontierCount positions := rfl

theorem capMarkedInternalPrefix_zero (positions : Positions) :
    capMarkedInternalPrefix positions 0 = 0 := rfl

theorem capMarkedInternalPrefix_succ (positions : Positions) (n : Nat) :
    capMarkedInternalPrefix positions (n + 1) =
      capMarkedInternalPrefix positions n + (if capMark positions (286 + n) then 1 else 0) :=
  Finset.sum_range_succ _ n

theorem capMarkedInternalPrefix_143 (positions : Positions) :
    capMarkedInternalPrefix positions 143 = capMarkedInternalCount positions := rfl

private theorem k_cap_ecall_ex (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (s : MachineState) (idx src dst : Nat)
    (hhi : idx < 269) (hpc : s.pc = kPcAt idx) (hi : checkInstr idx = .base .ECALL)
    (hx5 : s.getReg .x5 = 0#64) (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx11 : s.getReg .x11 = BitVec.ofNat 64 96) (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hx13 : s.getReg .x13 = 0#64)
    (hsAl : src % 8 = 0) (hsBd : src + 96 ≤ 68719476736)
    (hdAl : dst % 8 = 0) (hdBd : dst + 32 ≤ 68719476736) :
    ∃ s',
      StepsTo oracle s s' 1 1
        [((readBuffer s src 96).cast h768.symm, oracle.compression ((readBuffer s src 96).cast h768.symm))] ∧
      s'.pc = kPcAt (idx + 1) ∧
      (∀ r, s'.getReg r = s.getReg r) ∧
      readBuffer s' dst 32 = oracle.compression ((readBuffer s src 96).cast h768.symm) ∧
      MemEqOutside s s' dst (dst + 32) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := k_step_ecall_compress h768 oracle s idx src dst
    hhi hpc hi hx5 hx10 hx11 hx12 hx13 hsAl hsBd hdAl hdBd
  exact ⟨_, h1, h2, h3, h4, h5⟩

private theorem detExec_zero_calls_trace_nil (oracle : Oracle) (image : Image) :
    ∀ steps s, (detExec oracle image steps s).1.oracleCalls = 0 →
      (detExec oracle image steps s).2 = [] := by
  intro steps
  induction steps with
  | zero => intro _ _; rfl
  | succ n ih =>
    intro s h0
    cases hfetch : fetch image s with
    | none => simp only [detExec_succ_none oracle image n s hfetch]
    | some instr =>
      by_cases he : instr = .base .ECALL
      · subst he
        rw [detExec_succ_ecall oracle image n s hfetch] at h0 ⊢
        by_cases hx5 : s.getReg .x5 = 0
        · simp only [hx5, ite_true] at h0 ⊢
          cases hin : oracleInput s with
          | none => rfl
          | some inp =>
            cases inp with
            | inl x =>
              simp only [hin, Execution.charge] at h0
              omega
            | inr pq =>
              simp only [hin, Execution.charge] at h0 ⊢
              exact ih _ (by omega)
        · simp only [hx5, ite_false] at h0 ⊢
          by_cases hx51 : s.getReg .x5 = 1 <;> (simp only [hx51, ite_true, ite_false]; rfl)
      · rw [detExec_succ_other oracle image n s instr he hfetch] at h0 ⊢
        cases hstep : ordinaryStep s instr with
        | none => rfl
        | some next =>
          simp only [hstep, Execution.charge] at h0 ⊢
          exact ih next (by omega)

private theorem haltsWith_zero_calls_nil {oracle : Oracle} {s : MachineState} {k : Nat}
    {exit : Exit} {tr : CompressionReplies}
    (hh : HaltsWith oracle s k 0 exit tr) : tr = [] := by
  obtain ⟨_, h1, h2⟩ := hh.2 0
  exact h2.symm.trans (detExec_zero_calls_trace_nil oracle _ _ _ h1)

/-! ### 2. Branch Targets and Isolated Backward-Branch Lemmas (`pc[156..268]`) -/

private theorem k_tgt_169 : kPcAt 169 + signExtend13 (180#13)  = kPcAt 214 := by decide
private theorem k_tgt_172 : kPcAt 172 + signExtend13 (52#13)   = kPcAt 185 := by decide
private theorem k_tgt_175 : kPcAt 175 + signExtend13 (364#13)  = kPcAt 266 := by decide
private theorem k_tgt_185 : kPcAt 185 + signExtend13 (52#13)   = kPcAt 198 := by decide
private theorem k_tgt_188 : kPcAt 188 + signExtend13 (312#13)  = kPcAt 266 := by decide
private theorem k_tgt_198 : kPcAt 198 + signExtend13 (52#13)   = kPcAt 211 := by decide
private theorem k_tgt_201 : kPcAt 201 + signExtend13 (260#13)  = kPcAt 266 := by decide
private theorem k_tgt_218 : kPcAt 218 + signExtend13 (7976#13) = kPcAt 164 := by decide
private theorem k_tgt_220 : kPcAt 220 + signExtend13 (52#13)   = kPcAt 233 := by decide
private theorem k_tgt_223 : kPcAt 223 + signExtend13 (172#13)  = kPcAt 266 := by decide
private theorem k_tgt_234 : kPcAt 234 + signExtend13 (52#13)   = kPcAt 247 := by decide
private theorem k_tgt_237 : kPcAt 237 + signExtend13 (116#13)  = kPcAt 266 := by decide
private theorem k_tgt_250 : kPcAt 250 + signExtend13 (64#13)   = kPcAt 266 := by decide
private theorem k_tgt_253 : kPcAt 253 + signExtend13 (52#13)   = kPcAt 266 := by decide
private theorem k_tgt_256 : kPcAt 256 + signExtend13 (40#13)   = kPcAt 266 := by decide
private theorem k_tgt_259 : kPcAt 259 + signExtend13 (28#13)   = kPcAt 266 := by decide
private theorem k_tgt_262 : kPcAt 262 + signExtend13 (16#13)   = kPcAt 266 := by decide

private theorem k_step_218_back (oracle : Oracle) {s : MachineState} {a b : Nat}
    (hpc : s.pc = kPcAt 218)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 a)
    (hx16 : s.getReg .x16 = BitVec.ofNat 64 b)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    StepsTo oracle s (s.setPC (kPcAt 164)) 1 0 [] :=
  k_step_BNE_taken (oracle := oracle) (by decide) hpc rfl
    (by rw [hx15, hx16]; exact k_bv_ne ha hb hne) k_tgt_218

private theorem k_step_218_done (oracle : Oracle) {s : MachineState} {a : Nat}
    (hpc : s.pc = kPcAt 218)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 a)
    (hx16 : s.getReg .x16 = BitVec.ofNat 64 a) :
    StepsTo oracle s (s.setPC (kPcAt 219)) 1 0 [] :=
  k_step_BNE_not_taken (oracle := oracle) (by decide) hpc rfl (by rw [hx15, hx16])

/-! ### 3. Cap Setup (`pc[156..163]`) and Reusable Conditional 32-Byte Proof Read -/

private theorem check_cap_setup (oracle : Oracle) (input : CheckInput) {s : MachineState}
    (hpc : s.pc = kPcAt 156) (hfix : CheckFixedRegs input s) :
    ∃ s' : MachineState,
      StepsTo oracle s s' 8 0 [] ∧
      s'.pc = kPcAt 164 ∧
      s'.mem = s.mem ∧
      CheckFixedRegs input s' ∧
      s'.getReg .x14 = BitVec.ofNat 64 4096 ∧
      s'.getReg .x15 = BitVec.ofNat 64 (4096 + 286) ∧
      s'.getReg .x16 = BitVec.ofNat 64 (4096 + 428) ∧
      s'.getReg .x17 = BitVec.ofNat 64 8192 ∧
      s'.getReg .x28 = BitVec.ofNat 64 (8192 + 32 * 286) ∧
      s'.getReg .x20 = s.getReg .x20 := by
  have h156 := k_step_ADDI (oracle := oracle) (s := s)  (idx := 156) (by decide) hpc rfl
  let t1 := (s.setReg .x14 (s.getReg .x24 + signExtend12 0#12)).setPC (kPcAt 157)
  have h157 := k_step_ADDI (oracle := oracle) (s := t1) (idx := 157) (by decide) rfl rfl
  let t2 := (t1.setReg .x15 (t1.getReg .x24 + signExtend12 286#12)).setPC (kPcAt 158)
  have h158 := k_step_ADDI (oracle := oracle) (s := t2) (idx := 158) (by decide) rfl rfl
  let t3 := (t2.setReg .x16 (t2.getReg .x24 + signExtend12 428#12)).setPC (kPcAt 159)
  have h159 := k_step_ADDI (oracle := oracle) (s := t3) (idx := 159) (by decide) rfl rfl
  let t4 := (t3.setReg .x17 (t3.getReg .x25 + signExtend12 0#12)).setPC (kPcAt 160)
  have h160 := k_step_ADDI (oracle := oracle) (s := t4) (idx := 160) (by decide) rfl rfl
  let t5 := (t4.setReg .x6  (t4.getReg .x0  + signExtend12 4#12)).setPC (kPcAt 161)
  have h161 := k_step_SLLI (oracle := oracle) (s := t5) (idx := 161) (by decide) rfl rfl
  let t6 := (t5.setReg .x6  (t5.getReg .x6  <<< (11#6 : BitVec 6).toNat)).setPC (kPcAt 162)
  have h162 := k_step_ADDI (oracle := oracle) (s := t6) (idx := 162) (by decide) rfl rfl
  let t7 := (t6.setReg .x6  (t6.getReg .x6  + signExtend12 960#12)).setPC (kPcAt 163)
  have h163 := k_step_ADD  (oracle := oracle) (s := t7) (idx := 163) (by decide) rfl rfl
  let t8 := (t7.setReg .x28 (t7.getReg .x25 + t7.getReg .x6)).setPC (kPcAt 164)
  have hrun : StepsTo oracle s t8 8 0 [] := by
    simpa only [show 4 + 4 = 8 from rfl, List.append_nil] using
      ((h156.trans h157).trans (h158.trans h159)).trans ((h160.trans h161).trans (h162.trans h163))
  have hreg : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x6 → r ≠ .x28 →
      t8.getReg r = s.getReg r := fun r h14 h15 h16 h17 h6 h28 => by
    simp only [t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h28),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h6),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h17),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h16),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h15),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h14)]
  have hx6_7 : t7.getReg .x6 = BitVec.ofNat 64 9152 := by
    simp only [t7, t6, t5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
  refine ⟨t8, hrun, rfl,
    by simp only [t8, t7, t6, t5, t4, t3, t2, t1, k_mem_setPC, k_mem_setReg],
    hfix.of_agree (fun r hr => hreg r (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl)
      (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl)
      (isCheckFixedReg_ne hr rfl)),
    ?_, ?_, ?_, ?_, ?_,
    hreg .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
  · simp only [t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x24]; decide
  · simp only [t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x24]; decide
  · simp only [t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x24]; decide
  · simp only [t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x25]; decide
  · have h25 : t7.getReg .x25 = BitVec.ofNat 64 8192 := by
      simp only [t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        ne_eq, not_false_eq_true, reduceCtorEq, hfix.x25]
    simp only [t8, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h25, hx6_7]; decide

/-- Conditional 32-byte cap frontier read (`BNE flagReg x0 +52; bounds check 32; copy32; x20 += 32`). -/
private theorem check_cap_cond_read32 (oracle : Oracle) (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    {s : MachineState} {idx dstOff base17 off : Nat} {flagReg : Reg} {flag : Bool} {brRej : BitVec 13}
    (hhi : idx + 12 < 269) (hpc : s.pc = kPcAt idx)
    (htSkip : kPcAt idx + signExtend13 (52#13) = kPcAt (idx + 13))
    (htRej : kPcAt (idx + 3) + signExtend13 brRej = kPcAt 266)
    (hdo : dstOff + 24 < 2048) (hdo8 : dstOff % 8 = 0)
    (hiB  : checkInstr idx = .base (.BNE flagReg .x0 (52#13)))
    (hiS  : checkInstr (idx + 1) = .base (.SUB .x30 .x21 .x20))
    (hi32 : checkInstr (idx + 2) = .base (.ADDI .x31 .x0 (32#12)))
    (hiLT : checkInstr (idx + 3) = .base (.BLTU .x30 .x31 brRej))
    (hi0  : checkInstr (idx + 4)  = .base (.LD .x30 .x20 (BitVec.ofNat 12 0)))
    (hi1  : checkInstr (idx + 5)  = .base (.SD .x17 .x30 (BitVec.ofNat 12 dstOff)))
    (hi2  : checkInstr (idx + 6)  = .base (.LD .x30 .x20 (BitVec.ofNat 12 8)))
    (hi3  : checkInstr (idx + 7)  = .base (.SD .x17 .x30 (BitVec.ofNat 12 (dstOff + 8))))
    (hi4  : checkInstr (idx + 8)  = .base (.LD .x30 .x20 (BitVec.ofNat 12 16)))
    (hi5  : checkInstr (idx + 9)  = .base (.SD .x17 .x30 (BitVec.ofNat 12 (dstOff + 16))))
    (hi6  : checkInstr (idx + 10) = .base (.LD .x30 .x20 (BitVec.ofNat 12 24)))
    (hi7  : checkInstr (idx + 11) = .base (.SD .x17 .x30 (BitVec.ofNat 12 (dstOff + 24))))
    (hiA  : checkInstr (idx + 12) = .base (.ADDI .x20 .x20 (32#12)))
    (hfix : CheckFixedRegs input s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hflag : s.getReg flagReg = if flag then 1#64 else 0#64)
    (hx17 : s.getReg .x17 = BitVec.ofNat 64 base17)
    (hb17_lo : 8192 ≤ base17) (hb17_hi : base17 + dstOff + 32 ≤ 8192 + 32 * 428) (hb17_8 : base17 % 8 = 0)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + off))
    (hoff_le : off ≤ input.proof.length) (hoff8 : off % 8 = 0) :
    let s0 := submission.initialState .check input
    let addOff := if !flag then 32 else 0
    PhaseOutcome oracle s 13 0 (input.proof.length < off + addOff)
      (fun s' q tr =>
        q = 0 ∧ tr = [] ∧
        off + addOff ≤ input.proof.length ∧
        s'.pc = kPcAt (idx + 13) ∧
        (∀ r, r ≠ .x20 → r ≠ .x30 → r ≠ .x31 → s'.getReg r = s.getReg r) ∧
        s'.getReg .x20 = BitVec.ofNat 64 (11072966688 + (off + addOff)) ∧
        (flag = true → s'.mem = s.mem) ∧
        (flag = false →
          readBuffer s' (base17 + dstOff) 32 = readBuffer s0 (11072966688 + off) 32 ∧
          MemEqOutside s s' (base17 + dstOff) (base17 + dstOff + 32))) := by
  intro s0 addOff
  have hproof_bd : input.proof.length ≤ 11140077536 := hvalid
  cases flag with
  | true =>
    have h0 := k_step_BNE_taken (oracle := oracle) (s := s) (idx := idx) (tgt := idx + 13)
      (by omega) hpc hiB (by rw [hflag, k_getReg_x0]; decide) htSkip
    exact .continued (s.setPC (kPcAt (idx + 13))) 1 0 [] (by omega) (by omega) h0
      ⟨rfl, rfl, by simp [addOff, hoff_le], rfl, fun r _ _ _ => k_getReg_setPC s _ r,
        by simp [addOff, MachineState.getReg_setPC, hx20], fun _ => rfl, fun h => by cases h⟩
  | false =>
    have h0 := k_step_BNE_not_taken (oracle := oracle) (s := s) (idx := idx)
      (by omega) hpc hiB (by rw [hflag, k_getReg_x0]; rfl)
    let t1 := s.setPC (kPcAt (idx + 1))
    have h1 := k_step_SUB (oracle := oracle) (s := t1) (idx := idx + 1) (by omega) rfl hiS
    let t2 := (t1.setReg .x30 (t1.getReg .x21 - t1.getReg .x20)).setPC (kPcAt (idx + 2))
    have h2 := k_step_ADDI (oracle := oracle) (s := t2) (idx := idx + 2) (by omega) rfl hi32
    let t3 := (t2.setReg .x31 (t2.getReg .x0 + signExtend12 32#12)).setPC (kPcAt (idx + 3))
    have hx30_3 : t3.getReg .x30 = BitVec.ofNat 64 (input.proof.length - off) := by
      simp only [t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hfix.x21, hx20]
      rw [k_bv_sub _ _ (by omega)]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx31_3 : t3.getReg .x31 = BitVec.ofNat 64 32 := by
      simp only [t3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
    have hpre3 : StepsTo oracle s t3 3 0 [] := by
      simpa only [show 1 + 1 + 1 = 3 from rfl, List.append_nil] using (h0.trans h1).trans h2
    by_cases hlt32 : input.proof.length < off + 32
    · have h3 := k_step_BLTU_taken (oracle := oracle) (s := t3) (idx := idx + 3) (tgt := 266) (by omega) rfl hiLT
        (by rw [hx30_3, hx31_3, k_toNat_ofNat _ (by omega), k_toNat_ofNat 32 (by omega)]; omega) htRej
      have hh := k_step_halt_reject oracle (t3.setPC (kPcAt 266)) rfl
      exact .rejected 7 0 [] (by simpa [addOff] using hlt32) (by omega) (by omega)
        (by simpa using (hpre3.trans h3).halt hh)
    · have hge32 : off + 32 ≤ input.proof.length := by omega
      have h3 := k_step_BLTU_not_taken (oracle := oracle) (s := t3) (idx := idx + 3) (by omega) rfl hiLT
        (by rw [hx30_3, hx31_3, k_toNat_ofNat 32 (by omega), k_toNat_ofNat _ (by omega)]; omega)
      let t4 := t3.setPC (kPcAt (idx + 4))
      have hmem4 : t4.mem = s.mem := by simp only [t4, t3, t2, t1, k_mem_setPC, k_mem_setReg]
      have hreg4_s : ∀ r, r ≠ .x30 → r ≠ .x31 → t4.getReg r = s.getReg r := fun r h30 h31 => by
        simp only [t4, t3, t2, t1, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h31),
          MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h30)]
      obtain ⟨t5, hcp, hpc5, hreg5, hbuf5, hfr5⟩ := k_copy_32 oracle (s := t4) (idx := idx + 4) (tmp := .x30)
        (srcReg := .x20) (dstReg := .x17) (srcOff := 0) (dstOff := dstOff) (by omega) rfl (by decide) hdo
        hi0 hi1 hi2 hi3 hi4 hi5 hi6 hi7 (by decide) (by decide) (by decide)
        ((hreg4_s .x20 (by decide) (by decide)).trans hx20) ((hreg4_s .x17 (by decide) (by decide)).trans hx17)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      have hA := k_step_ADDI (oracle := oracle) (s := t5) (idx := idx + 12) (by omega)
        (by simpa only [show idx + 4 + 8 = idx + 12 by omega] using hpc5) hiA
      let t6 := (t5.setReg .x20 (t5.getReg .x20 + signExtend12 32#12)).setPC (kPcAt (idx + 13))
      have hx20_5 : t5.getReg .x20 = BitVec.ofNat 64 (11072966688 + off) :=
        (hreg5 .x20 (by decide)).trans ((hreg4_s .x20 (by decide) (by decide)).trans hx20)
      have hrun : StepsTo oracle s t6 13 0 [] := by
        simpa only [show 3 + 1 + 8 + 1 = 13 from rfl, List.append_nil, Nat.add_assoc,
          show idx + 12 + 1 = idx + 13 by omega] using ((hpre3.trans h3).trans hcp).trans hA
      refine .continued t6 13 0 [] le_rfl le_rfl hrun
        ⟨rfl, rfl, by simpa [addOff] using hge32, rfl,
          fun r h20 h30 h31 => by
            simp only [t6, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h20)]
            exact (hreg5 r h30).trans (hreg4_s r h30 h31),
          by simp only [t6, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
               hx20_5, show signExtend12 32#12 = BitVec.ofNat 64 32 by decide, k_bv_add, addOff, Bool.not_false, ite_true, Nat.add_assoc],
          (fun h => by cases h), fun _ => ⟨?_, ?_⟩⟩
      · have hm6 : t6.mem = t5.mem := by simp only [t6, k_mem_setPC, k_mem_setReg]
        rw [(MemEqOutside.of_mem_eq hm6 0 0).readBuffer_eq (by omega) (by omega)]
        simpa only [Nat.add_zero] using
          hbuf5.trans (((MemEqOutside.of_mem_eq hmem4 0 0).readBuffer_eq (by omega) (by omega)).trans
            (hhigh.readBuffer_eq (by omega) (by omega)))
      · exact (MemEqOutside.of_mem_eq hmem4 (base17 + dstOff) (base17 + dstOff + 32)).trans
          (hfr5.trans (MemEqOutside.of_mem_eq (by simp only [t6, k_mem_setPC, k_mem_setReg]) (base17 + dstOff) (base17 + dstOff + 32)))

/-! ### 4. Cap Loop (`pc[164..218]`, `j = 0..141`) and Root (`pc[219..249]`) -/

structure CapLoopInv (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (baseOff : Nat) (sPos : MachineState) (n : Nat)
    (s : MachineState) (tr : CompressionReplies) : Prop where
  fixed    : CheckFixedRegs input s
  high     : HighMemPreserved (submission.initialState .check input) s
  pc       : s.pc = if n = 142 then kPcAt 219 else kPcAt 164
  x14      : s.getReg .x14 = BitVec.ofNat 64 (4096 + 3 * n)
  x15      : s.getReg .x15 = BitVec.ofNat 64 (4096 + 286 + n)
  x16      : s.getReg .x16 = BitVec.ofNat 64 (4096 + 428)
  x17      : s.getReg .x17 = BitVec.ofNat 64 (8192 + 96 * n)
  x28      : s.getReg .x28 = BitVec.ofNat 64 (8192 + 32 * (286 + n))
  x20      : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + (baseOff + 32 * capFrontierCountPrefix input.positions n))
  len_le   : baseOff + 32 * capFrontierCountPrefix input.positions n ≤ input.proof.length
  marks    : ∀ u < 429, s.getByte (BitVec.ofNat 64 (4096 + u)) =
    if capMarkPrefix input.positions n u then 1#8 else 0#8
  val_428_zero : readBuffer s (8192 + 32 * 428) 32 = 0#256
  val_leaf_marked : ∀ c < 286, capMark input.positions c = true →
    readBuffer s (8192 + 32 * c) 32 = readBuffer sPos (8192 + 32 * c) 32
  val_internal : ∀ j < n, capMark input.positions (286 + j) = true →
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let d0 := readBuffer s (8192 + 32 * (3 * j)) 32
    let d1 := readBuffer s (8192 + 32 * (3 * j + 1)) 32
    let d2 := readBuffer s (8192 + 32 * (3 * j + 2)) 32
    readBuffer s (8192 + 32 * (286 + j)) 32 = c96 (ternaryInput d0 d1 d2) ∧
    InTrace h768 oracle tr (ternaryInput d0 d1 d2) ∧
    (capMark input.positions (3 * j) = false → d0 = readBuffer s0 (11072966688 + capChildOff input.positions baseOff j 0) 32) ∧
    (capMark input.positions (3 * j + 1) = false → d1 = readBuffer s0 (11072966688 + capChildOff input.positions baseOff j 1) 32) ∧
    (capMark input.positions (3 * j + 2) = false → d2 = readBuffer s0 (11072966688 + capChildOff input.positions baseOff j 2) 32)

private theorem check_cap_step (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    {baseOff j : Nat} {sPos s : MachineState} {tr : CompressionReplies}
    (hbase8 : baseOff % 8 = 0) (hj : j < 142)
    (hinv : CapLoopInv h768 oracle input baseOff sPos j s tr) :
    let capEnd := baseOff + 32 * capFrontierCount input.positions
    PhaseOutcome oracle s 55 (if capMark input.positions (286 + j) then 1 else 0)
      (input.proof.length < capEnd)
      (fun s' q' tr' =>
        q' = (if capMark input.positions (286 + j) then 1 else 0) ∧
        CapLoopInv h768 oracle input baseOff sPos (j + 1) s' (tr ++ tr')) := by
  intro capEnd
  let s0 := submission.initialState .check input
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hpc164 : s.pc = kPcAt 164 := by
    have h := hinv.pc; simp only [show j ≠ 142 by omega, ite_false] at h; exact h
  let m0 := capMark input.positions (3 * j)
  let m1 := capMark input.positions (3 * j + 1)
  let m2 := capMark input.positions (3 * j + 2)
  have hm_eq : capMark input.positions (286 + j) = (m0 || m1 || m2) := capMark_internal input.positions j hj
  let off0 := baseOff + 32 * capFrontierCountPrefix input.positions j
  have hoff0_8 : off0 % 8 = 0 := by dsimp only [off0]; omega
  -- pc[164..168]: load mark[3j..3j+2] and OR into x30
  have ha164 : s.getReg .x14 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + 3 * j) := by
    rw [hinv.x14, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
  have h164 := k_step_LBU (oracle := oracle) (s := s) (idx := 164) (by decide) hpc164 rfl
    (by rw [ha164]; exact k_accessValid _ 1 (by omega) (by omega))
  let t1 := (s.setReg .x6 ((s.getByte (s.getReg .x14 + signExtend12 0#12)).zeroExtend 64)).setPC (kPcAt 165)
  have ha165 : t1.getReg .x14 + signExtend12 1#12 = BitVec.ofNat 64 (4096 + (3 * j + 1)) := by
    simp only [t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x14),
      hinv.x14, show signExtend12 1#12 = BitVec.ofNat 64 1 by decide, k_bv_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have h165 := k_step_LBU (oracle := oracle) (s := t1) (idx := 165) (by decide) rfl rfl
    (by rw [ha165]; exact k_accessValid _ 1 (by omega) (by omega))
  let t2 := (t1.setReg .x7 ((t1.getByte (t1.getReg .x14 + signExtend12 1#12)).zeroExtend 64)).setPC (kPcAt 166)
  have ha166 : t2.getReg .x14 + signExtend12 2#12 = BitVec.ofNat 64 (4096 + (3 * j + 2)) := by
    simp only [t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq,
      hinv.x14, show signExtend12 2#12 = BitVec.ofNat 64 2 by decide, k_bv_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have h166 := k_step_LBU (oracle := oracle) (s := t2) (idx := 166) (by decide) rfl rfl
    (by rw [ha166]; exact k_accessValid _ 1 (by omega) (by omega))
  let t3 := (t2.setReg .x29 ((t2.getByte (t2.getReg .x14 + signExtend12 2#12)).zeroExtend 64)).setPC (kPcAt 167)
  have h167 := k_step_OR (oracle := oracle) (s := t3) (idx := 167) (by decide) rfl rfl
  let t4 := (t3.setReg .x30 (t3.getReg .x6 ||| t3.getReg .x7)).setPC (kPcAt 168)
  have h168 := k_step_OR (oracle := oracle) (s := t4) (idx := 168) (by decide) rfl rfl
  let t5 := (t4.setReg .x30 (t4.getReg .x30 ||| t4.getReg .x29)).setPC (kPcAt 169)
  have hpre5 : StepsTo oracle s t5 5 0 [] := by
    simpa only [show 1 + 1 + 1 + 1 + 1 = 5 from rfl, List.append_nil] using
      ((h164.trans h165).trans (h166.trans h167)).trans h168
  have hmem5 : t5.mem = s.mem := by simp only [t5, t4, t3, t2, t1, k_mem_setPC, k_mem_setReg]
  have hreg5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x29 → r ≠ .x30 → t5.getReg r = s.getReg r := fun r h6 h7 h29 h30 => by
    simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h30),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h29),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h7),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h6)]
  have hfix5 : CheckFixedRegs input t5 := hinv.fixed.of_agree (fun r hr =>
    hreg5 r (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl))
  have hx6_5 : t5.getReg .x6 = if m0 then 1#64 else 0#64 := by
    have hcm : capMarkPrefix input.positions j (3 * j) = m0 := by unfold capMarkPrefix; simp [show 3 * j < 286 + j by omega, m0]
    simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, ha164, hinv.marks (3 * j) (by omega), hcm]
    exact k_bool_byte_zext m0
  have hx7_5 : t5.getReg .x7 = if m1 then 1#64 else 0#64 := by
    have hcm : capMarkPrefix input.positions j (3 * j + 1) = m1 := by unfold capMarkPrefix; simp [show 3 * j + 1 < 286 + j by omega, m1]
    simp only [t5, t4, t3, t2, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, ha165]
    simp only [t1, k_getByte_setPC, k_getByte_setReg, hinv.marks (3 * j + 1) (by omega), hcm]
    exact k_bool_byte_zext m1
  have hx29_5 : t5.getReg .x29 = if m2 then 1#64 else 0#64 := by
    have hcm : capMarkPrefix input.positions j (3 * j + 2) = m2 := by unfold capMarkPrefix; simp [show 3 * j + 2 < 286 + j by omega, m2]
    simp only [t5, t4, t3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, ha166]
    simp only [t2, t1, k_getByte_setPC, k_getByte_setReg, hinv.marks (3 * j + 2) (by omega), hcm]
    exact k_bool_byte_zext m2
  have hx30_5 : t5.getReg .x30 = if (m0 || m1 || m2) then 1#64 else 0#64 := by
    have h6_3 : t3.getReg .x6 = if m0 then 1#64 else 0#64 := by
      simpa only [t5, t4, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq] using hx6_5
    have h7_3 : t3.getReg .x7 = if m1 then 1#64 else 0#64 := by
      simpa only [t5, t4, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq] using hx7_5
    have h29_4 : t4.getReg .x29 = if m2 then 1#64 else 0#64 := by
      simpa only [t5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq] using hx29_5
    have h30_4 : t4.getReg .x30 = if (m0 || m1) then 1#64 else 0#64 := by
      simp only [t4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h6_3, h7_3, k_bool_word_or]
    simp only [t5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h30_4, h29_4, k_bool_word_or]
  -- Helper for tail pc[214..218] (5 steps, 0 calls)
  have htail_fn : ∀ (u : MachineState) (qMid : Nat) (trMid : CompressionReplies),
      u.pc = kPcAt 214 → CheckFixedRegs input u →
      u.getReg .x14 = BitVec.ofNat 64 (4096 + 3 * j) →
      u.getReg .x15 = BitVec.ofNat 64 (4096 + 286 + j) →
      u.getReg .x16 = BitVec.ofNat 64 (4096 + 428) →
      u.getReg .x17 = BitVec.ofNat 64 (8192 + 96 * j) →
      u.getReg .x28 = BitVec.ofNat 64 (8192 + 32 * (286 + j)) →
      u.getReg .x20 = BitVec.ofNat 64 (11072966688 + (baseOff + 32 * capFrontierCountPrefix input.positions (j + 1))) →
      baseOff + 32 * capFrontierCountPrefix input.positions (j + 1) ≤ input.proof.length →
      HighMemPreserved s0 u →
      (∀ x < 429, u.getByte (BitVec.ofNat 64 (4096 + x)) = if capMarkPrefix input.positions (j + 1) x then 1#8 else 0#8) →
      readBuffer u (8192 + 32 * 428) 32 = 0#256 →
      (∀ c < 286, capMark input.positions c = true → readBuffer u (8192 + 32 * c) 32 = readBuffer sPos (8192 + 32 * c) 32) →
      (∀ j' < j + 1, capMark input.positions (286 + j') = true →
        let d0 := readBuffer u (8192 + 32 * (3 * j')) 32
        let d1 := readBuffer u (8192 + 32 * (3 * j' + 1)) 32
        let d2 := readBuffer u (8192 + 32 * (3 * j' + 2)) 32
        readBuffer u (8192 + 32 * (286 + j')) 32 = c96 (ternaryInput d0 d1 d2) ∧
        InTrace h768 oracle (tr ++ trMid) (ternaryInput d0 d1 d2) ∧
        (capMark input.positions (3 * j') = false → d0 = readBuffer s0 (11072966688 + capChildOff input.positions baseOff j' 0) 32) ∧
        (capMark input.positions (3 * j' + 1) = false → d1 = readBuffer s0 (11072966688 + capChildOff input.positions baseOff j' 1) 32) ∧
        (capMark input.positions (3 * j' + 2) = false → d2 = readBuffer s0 (11072966688 + capChildOff input.positions baseOff j' 2) 32)) →
      ∃ s', StepsTo oracle u s' 5 0 [] ∧ CapLoopInv h768 oracle input baseOff sPos (j + 1) s' (tr ++ trMid) := by
    intro u _ trMid hpcu hfixu hx14u hx15u hx16u hx17u hx28u hx20u hlenu hhighu hmarku h428u hleafu hintu
    have h214 := k_step_ADDI (oracle := oracle) (s := u) (idx := 214) (by decide) hpcu rfl
    let v1 := (u.setReg .x14 (u.getReg .x14 + signExtend12 3#12)).setPC (kPcAt 215)
    have h215 := k_step_ADDI (oracle := oracle) (s := v1) (idx := 215) (by decide) rfl rfl
    let v2 := (v1.setReg .x15 (v1.getReg .x15 + signExtend12 1#12)).setPC (kPcAt 216)
    have h216 := k_step_ADDI (oracle := oracle) (s := v2) (idx := 216) (by decide) rfl rfl
    let v3 := (v2.setReg .x17 (v2.getReg .x17 + signExtend12 96#12)).setPC (kPcAt 217)
    have h217 := k_step_ADDI (oracle := oracle) (s := v3) (idx := 217) (by decide) rfl rfl
    let v4 := (v3.setReg .x28 (v3.getReg .x28 + signExtend12 32#12)).setPC (kPcAt 218)
    have hx14_v4 : v4.getReg .x14 = BitVec.ofNat 64 (4096 + 3 * (j + 1)) := by
      simp only [v4, v3, v2, v1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hx14u, show signExtend12 3#12 = BitVec.ofNat 64 3 by decide, k_bv_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx15_v4 : v4.getReg .x15 = BitVec.ofNat 64 (4096 + 286 + (j + 1)) := by
      simp only [v4, v3, v2, v1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hx15u, show signExtend12 1#12 = BitVec.ofNat 64 1 by decide, k_bv_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx16_v4 : v4.getReg .x16 = BitVec.ofNat 64 (4096 + 428) := by
      simp only [v4, v3, v2, v1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx16u]
    have hx17_v4 : v4.getReg .x17 = BitVec.ofNat 64 (8192 + 96 * (j + 1)) := by
      simp only [v4, v3, v2, v1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hx17u, show signExtend12 96#12 = BitVec.ofNat 64 96 by decide, k_bv_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx28_v4 : v4.getReg .x28 = BitVec.ofNat 64 (8192 + 32 * (286 + (j + 1))) := by
      simp only [v4, v3, v2, v1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hx28u, show signExtend12 32#12 = BitVec.ofNat 64 32 by decide, k_bv_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hx20_v4 : v4.getReg .x20 = u.getReg .x20 := by
      simp only [v4, v3, v2, v1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq]
    let s' := v4.setPC (if j + 1 = 142 then kPcAt 219 else kPcAt 164)
    have h218 : StepsTo oracle v4 s' 1 0 [] := by
      by_cases hend : j + 1 = 142
      · have h15_eq : v4.getReg .x15 = BitVec.ofNat 64 (4096 + 428) := by
          rw [hx15_v4]; exact congrArg (BitVec.ofNat 64) (by omega)
        simpa only [s', hend, ite_true] using k_step_218_done oracle (s := v4) rfl h15_eq hx16_v4
      · simpa only [s', hend, ite_false] using
          k_step_218_back oracle (s := v4) rfl hx15_v4 hx16_v4 (by omega) (by omega) (by omega)
    have hmem' : s'.mem = u.mem := by simp only [s', v4, v3, v2, v1, k_mem_setPC, k_mem_setReg]
    have hrb_eq : ∀ addr n, readBuffer s' addr n = readBuffer u addr n := fun addr n => by
      apply k_readBuffer_congr2; intro k _; simp only [MachineState.getByte, MachineState.getMem, hmem']
    refine ⟨s', by simpa only [show 1 + 1 + 1 + 1 + 1 = 5 from rfl, List.append_nil] using
        ((h214.trans h215).trans (h216.trans h217)).trans h218,
      ⟨hfixu.of_agree (fun r hr => by
        have h14 := isCheckFixedReg_ne hr (r' := .x14) rfl
        have h15 := isCheckFixedReg_ne hr (r' := .x15) rfl
        have h17 := isCheckFixedReg_ne hr (r' := .x17) rfl
        have h28 := isCheckFixedReg_ne hr (r' := .x28) rfl
        simp only [s', v4, v3, v2, v1, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h28.symm,
          MachineState.getReg_setReg_ne _ _ _ _ h17.symm,
          MachineState.getReg_setReg_ne _ _ _ _ h15.symm,
          MachineState.getReg_setReg_ne _ _ _ _ h14.symm]),
       hhighu.trans (MemEqOutside.of_mem_eq hmem' 0 4294971392),
       rfl, (k_getReg_setPC v4 _ .x14).trans hx14_v4, (k_getReg_setPC v4 _ .x15).trans hx15_v4,
       (k_getReg_setPC v4 _ .x16).trans hx16_v4, (k_getReg_setPC v4 _ .x17).trans hx17_v4,
       (k_getReg_setPC v4 _ .x28).trans hx28_v4,
       ((k_getReg_setPC v4 _ .x20).trans hx20_v4).trans hx20u,
       hlenu,
       fun x hx => by simp only [MachineState.getByte, MachineState.getMem, hmem']; exact hmarku x hx,
       by rw [hrb_eq]; exact h428u,
       fun c hc hmc => by rw [hrb_eq]; exact hleafu c hc hmc,
       fun j' hj' hmj' => by simp only [hrb_eq]; exact hintu j' hj' hmj'⟩⟩
  -- Split on whether parent 286 + j is marked
  cases hpar : (m0 || m1 || m2) with
  | false =>
    have hpar_eq : capMark input.positions (286 + j) = false := hm_eq.trans hpar
    have h169 := k_step_BEQ_taken (oracle := oracle) (s := t5) (idx := 169) (tgt := 214) (by decide) rfl rfl
      (by rw [hx30_5, hpar, k_getReg_x0]; rfl) k_tgt_169
    let u := t5.setPC (kPcAt 214)
    have hcnt0 : capNodeFrontierCount input.positions j = 0 := by
      unfold capNodeFrontierCount; simp [hj, hpar_eq]
    have hpref_eq : capFrontierCountPrefix input.positions (j + 1) = capFrontierCountPrefix input.positions j := by
      rw [capFrontierCountPrefix_succ, hcnt0, Nat.add_zero]
    have hmem_u : u.mem = s.mem := hmem5
    obtain ⟨s', htail, hinv'⟩ := htail_fn u 0 [] rfl
      (hfix5.of_agree (fun r _ => k_getReg_setPC t5 _ r))
      ((k_getReg_setPC t5 _ .x14).trans ((hreg5 .x14 (by decide) (by decide) (by decide) (by decide)).trans hinv.x14))
      ((k_getReg_setPC t5 _ .x15).trans ((hreg5 .x15 (by decide) (by decide) (by decide) (by decide)).trans hinv.x15))
      ((k_getReg_setPC t5 _ .x16).trans ((hreg5 .x16 (by decide) (by decide) (by decide) (by decide)).trans hinv.x16))
      ((k_getReg_setPC t5 _ .x17).trans ((hreg5 .x17 (by decide) (by decide) (by decide) (by decide)).trans hinv.x17))
      ((k_getReg_setPC t5 _ .x28).trans ((hreg5 .x28 (by decide) (by decide) (by decide) (by decide)).trans hinv.x28))
      (by rw [hpref_eq]; exact (k_getReg_setPC t5 _ .x20).trans ((hreg5 .x20 (by decide) (by decide) (by decide) (by decide)).trans hinv.x20))
      (by rw [hpref_eq]; exact hinv.len_le)
      (hinv.high.trans (MemEqOutside.of_mem_eq hmem_u 0 4294971392))
      (fun x hx => by
        simp only [MachineState.getByte, MachineState.getMem, hmem_u]
        change s.getByte (BitVec.ofNat 64 (4096 + x)) = _
        rw [hinv.marks x hx]
        unfold capMarkPrefix
        by_cases hlt : x < 286 + j
        · simp [hlt, show x < 286 + (j + 1) by omega]
        · by_cases heq : x = 286 + j
          · subst heq; simp [hpar_eq]
          · simp [hlt, show ¬ (x < 286 + (j + 1)) by omega])
      (by rw [(MemEqOutside.of_mem_eq hmem_u 0 0).readBuffer_eq (by omega) (by omega)]; exact hinv.val_428_zero)
      (fun c hc hmc => by rw [(MemEqOutside.of_mem_eq hmem_u 0 0).readBuffer_eq (by omega) (by omega)]; exact hinv.val_leaf_marked c hc hmc)
      (fun j' hj' hmj' => by
        have hj'_lt : j' < j := by
          by_cases heq : j' = j
          · subst heq; rw [hpar_eq] at hmj'; cases hmj'
          · omega
        obtain ⟨hv, htrv, hc0, hc1, hc2⟩ := hinv.val_internal j' hj'_lt hmj'
        have hm_eq := MemEqOutside.of_mem_eq hmem_u 0 0
        have hm0 : readBuffer u (8192 + 32 * (3 * j')) 32 = readBuffer s (8192 + 32 * (3 * j')) 32 :=
          hm_eq.readBuffer_eq (by omega) (by omega)
        have hm1 : readBuffer u (8192 + 32 * (3 * j' + 1)) 32 = readBuffer s (8192 + 32 * (3 * j' + 1)) 32 :=
          hm_eq.readBuffer_eq (by omega) (by omega)
        have hm2 : readBuffer u (8192 + 32 * (3 * j' + 2)) 32 = readBuffer s (8192 + 32 * (3 * j' + 2)) 32 :=
          hm_eq.readBuffer_eq (by omega) (by omega)
        have hmp : readBuffer u (8192 + 32 * (286 + j')) 32 = readBuffer s (8192 + 32 * (286 + j')) 32 :=
          hm_eq.readBuffer_eq (by omega) (by omega)
        dsimp only
        rw [hm0, hm1, hm2, hmp]
        simp only [List.append_nil]
        exact ⟨hv, htrv, hc0, hc1, hc2⟩)
    exact .continued s' 11 0 [] (by omega) (by rw [hpar_eq]; exact le_rfl)
      (by simpa only [show 5 + 1 + 5 = 11 from rfl, List.append_nil] using (hpre5.trans h169).trans htail)
      ⟨by rw [hpar_eq]; rfl, hinv'⟩
  | true =>
    have hpar_eq : capMark input.positions (286 + j) = true := hm_eq.trans hpar
    have h169 := k_step_BEQ_not_taken (oracle := oracle) (s := t5) (idx := 169) (by decide) rfl rfl
      (by rw [hx30_5, hpar, k_getReg_x0]; decide)
    let u1 := t5.setPC (kPcAt 170)
    have h170 := k_step_ADDI (oracle := oracle) (s := u1) (idx := 170) (by decide) rfl rfl
    let u2 := (u1.setReg .x30 (u1.getReg .x0 + signExtend12 1#12)).setPC (kPcAt 171)
    have hx15_u2 : u2.getReg .x15 = BitVec.ofNat 64 (4096 + 286 + j) := by
      simp only [u2, u1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x30 ≠ .x15)]
      exact (hreg5 .x15 (by decide) (by decide) (by decide) (by decide)).trans hinv.x15
    have ha171 : u2.getReg .x15 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + (286 + j)) := by
      rw [hx15_u2, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have h171 := k_step_SB (oracle := oracle) (s := u2) (idx := 171) (by decide) rfl rfl
      (by rw [ha171]; exact k_accessValid _ 1 (by omega) (by omega))
    let u3 := (u2.setByte (u2.getReg .x15 + signExtend12 0#12) ((u2.getReg .x30).truncate 8)).setPC (kPcAt 172)
    have htr1 : (u2.getReg .x30).truncate 8 = 1#8 := by
      have h30 : u2.getReg .x30 = 1#64 := by
        simp only [u2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, k_getReg_x0]; decide
      rw [h30]; decide
    have hpre8 : StepsTo oracle s u3 8 0 [] := by
      simpa only [show 5 + 1 + 1 + 1 = 8 from rfl, List.append_nil] using ((hpre5.trans h169).trans h170).trans h171
    have hreg_u3 : ∀ r, r ≠ .x30 → u3.getReg r = t5.getReg r := fun r h30 => by
      simp only [u3, u2, u1, MachineState.getReg_setPC, k_getReg_setByte,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h30)]
    have hfix_u3 : CheckFixedRegs input u3 := hfix5.of_agree (fun r hr => hreg_u3 r (isCheckFixedReg_ne hr rfl))
    have hm_u2 : u2.mem = s.mem := by simp only [u2, u1, k_mem_setPC, k_mem_setReg, hmem5]
    have hfr_s_u3 : MemEqOutside s u3 (4096 + (286 + j)) (4096 + (286 + j) + 1) := by
      intro a ha hout
      simp only [u3, k_getByte_setPC, ha171, set_byte_read,
        k_bv_ne ha (show 4096 + (286 + j) < 2 ^ 64 by omega) (by omega), ite_false]
      simp only [MachineState.getByte, MachineState.getMem, hm_u2]
    have hhigh_u3 : HighMemPreserved s0 u3 := hinv.high.trans (hfr_s_u3.mono (by omega) (by omega))
    have hmark_u3 : ∀ x < 429, u3.getByte (BitVec.ofNat 64 (4096 + x)) =
        if capMarkPrefix input.positions (j + 1) x then 1#8 else 0#8 := fun x hx => by
      simp only [u3, k_getByte_setPC, ha171, htr1, set_byte_read]
      unfold capMarkPrefix
      by_cases heq : x = 286 + j
      · subst heq; simp [hpar_eq]
      · simp only [k_bv_ne (show 4096 + x < 2 ^ 64 by omega) (show 4096 + (286 + j) < 2 ^ 64 by omega) (by omega), ite_false]
        have hb : u2.getByte (BitVec.ofNat 64 (4096 + x)) = s.getByte (BitVec.ofNat 64 (4096 + x)) := by
          simp only [MachineState.getByte, MachineState.getMem, hm_u2]
        rw [hb, hinv.marks x hx]; unfold capMarkPrefix
        by_cases hlt : x < 286 + j
        · simp [hlt, show x < 286 + (j + 1) by omega]
        · simp [hlt, show ¬ (x < 286 + (j + 1)) by omega]
    have hcnt_j : capNodeFrontierCount input.positions j =
        (if !m0 then 1 else 0) + (if !m1 then 1 else 0) + (if !m2 then 1 else 0) := by
      unfold capNodeFrontierCount; simp [hj, hpar_eq, m0, m1, m2]
    have hpref_next : capFrontierCountPrefix input.positions (j + 1) =
        capFrontierCountPrefix input.positions j + ((if !m0 then 1 else 0) + (if !m1 then 1 else 0) + (if !m2 then 1 else 0)) := by
      rw [capFrontierCountPrefix_succ, hcnt_j]
    have hpref_le_cap : capFrontierCountPrefix input.positions (j + 1) ≤ capFrontierCount input.positions :=
      capFrontierCountPrefix_le input.positions (by omega)
    let a0 := if !m0 then 32 else 0
    let a1 := if !m1 then 32 else 0
    let a2 := if !m2 then 32 else 0
    have ha012 : a0 + a1 + a2 = 32 * ((if !m0 then 1 else 0) + (if !m1 then 1 else 0) + (if !m2 then 1 else 0)) := by
      dsimp only [a0, a1, a2]; cases m0 <;> cases m1 <;> cases m2 <;> decide
    have hco0 : capChildOff input.positions baseOff j 0 = off0 := by
      unfold capChildOff; simp [hj, off0]
    have hco1 : capChildOff input.positions baseOff j 1 = off0 + a0 := by
      unfold capChildOff; simp [hj, off0, a0, m0]
    have hco2 : capChildOff input.positions baseOff j 2 = off0 + a0 + a1 := by
      unfold capChildOff; simp [hj, off0, a0, a1, m0, m1]
    -- pc[172..184]: conditional read 0
    have hr0 := check_cap_cond_read32 oracle input hvalid (s := u3) (idx := 172) (dstOff := 0)
      (base17 := 8192 + 96 * j) (off := off0) (flagReg := .x6) (flag := m0) (brRej := 364#13)
      (by decide) rfl k_tgt_172 k_tgt_175 (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hfix_u3 hhigh_u3 ((hreg_u3 .x6 (by decide)).trans hx6_5)
      ((hreg_u3 .x17 (by decide)).trans ((hreg5 .x17 (by decide) (by decide) (by decide) (by decide)).trans hinv.x17))
      (by omega) (by omega) (by omega)
      ((hreg_u3 .x20 (by decide)).trans ((hreg5 .x20 (by decide) (by decide) (by decide) (by decide)).trans hinv.x20))
      hinv.len_le hoff0_8
    cases hr0 with
    | rejected k0 q0 tr0 hlt0 hk0 hq0 hh0 =>
      exact .rejected (8 + k0) (0 + q0) ([] ++ tr0) (by dsimp only [capEnd]; omega)
        (by omega) (by rw [hpar_eq]; omega) (hpre8.halt hh0)
    | continued w1 k0 q0 tr0 hk0 hq0 hst0 hp0 =>
      obtain ⟨hq1, htr1w, hge1, hpc1, hreg1, hx20_1, htr_m0, hfa_m0⟩ := hp0
      subst hq1; subst htr1w
      have hfr1 : MemEqOutside u3 w1 (8192 + 32 * (3 * j)) (8192 + 32 * (3 * j) + 32) := by
        cases hm0 : m0 with
        | true => exact MemEqOutside.of_mem_eq (htr_m0 hm0) _ _
        | false => simpa only [show 8192 + 96 * j + 0 = 8192 + 32 * (3 * j) by omega] using (hfa_m0 hm0).2
      have hfix1 : CheckFixedRegs input w1 := hfix_u3.of_agree (fun r hr =>
        hreg1 r (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl))
      have hhigh1 : HighMemPreserved s0 w1 := hhigh_u3.trans (hfr1.mono (by omega) (by omega))
      -- pc[185..197]: conditional read 1
      have hr1 := check_cap_cond_read32 oracle input hvalid (s := w1) (idx := 185) (dstOff := 32)
        (base17 := 8192 + 96 * j) (off := off0 + a0) (flagReg := .x7) (flag := m1) (brRej := 312#13)
        (by decide) hpc1 k_tgt_185 k_tgt_188 (by decide) (by decide)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        hfix1 hhigh1 ((hreg1 .x7 (by decide) (by decide) (by decide)).trans ((hreg_u3 .x7 (by decide)).trans hx7_5))
        ((hreg1 .x17 (by decide) (by decide) (by decide)).trans ((hreg_u3 .x17 (by decide)).trans
          ((hreg5 .x17 (by decide) (by decide) (by decide) (by decide)).trans hinv.x17)))
        (by omega) (by omega) (by omega) hx20_1 hge1 (by dsimp only [a0]; split_ifs <;> omega)
      cases hr1 with
      | rejected k1 q1 tr1 hlt1 hk1 hq1 hh1 =>
        exact .rejected (8 + k0 + k1) (0 + 0 + q1) ([] ++ [] ++ tr1) (by dsimp only [capEnd]; omega)
          (by omega) (by rw [hpar_eq]; omega) ((hpre8.trans hst0).halt hh1)
      | continued w2 k1 q1 tr1 hk1 hq1 hst1 hp1 =>
        obtain ⟨hq2, htr2w, hge2, hpc2, hreg2, hx20_2, htr_m1, hfa_m1⟩ := hp1
        subst hq2; subst htr2w
        have hfr2 : MemEqOutside w1 w2 (8192 + 32 * (3 * j + 1)) (8192 + 32 * (3 * j + 1) + 32) := by
          cases hm1 : m1 with
          | true => exact MemEqOutside.of_mem_eq (htr_m1 hm1) _ _
          | false => simpa only [show 8192 + 96 * j + 32 = 8192 + 32 * (3 * j + 1) by omega] using (hfa_m1 hm1).2
        have hfix2 : CheckFixedRegs input w2 := hfix1.of_agree (fun r hr =>
          hreg2 r (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl))
        have hhigh2 : HighMemPreserved s0 w2 := hhigh1.trans (hfr2.mono (by omega) (by omega))
        -- pc[198..210]: conditional read 2
        have hr2 := check_cap_cond_read32 oracle input hvalid (s := w2) (idx := 198) (dstOff := 64)
          (base17 := 8192 + 96 * j) (off := off0 + a0 + a1) (flagReg := .x29) (flag := m2) (brRej := 260#13)
          (by decide) hpc2 k_tgt_198 k_tgt_201 (by decide) (by decide)
          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          hfix2 hhigh2
          ((hreg2 .x29 (by decide) (by decide) (by decide)).trans
            ((hreg1 .x29 (by decide) (by decide) (by decide)).trans ((hreg_u3 .x29 (by decide)).trans hx29_5)))
          ((hreg2 .x17 (by decide) (by decide) (by decide)).trans
            ((hreg1 .x17 (by decide) (by decide) (by decide)).trans ((hreg_u3 .x17 (by decide)).trans
              ((hreg5 .x17 (by decide) (by decide) (by decide) (by decide)).trans hinv.x17))))
          (by omega) (by omega) (by omega) hx20_2 hge2 (by dsimp only [a0, a1]; split_ifs <;> omega)
        cases hr2 with
        | rejected k2 q2 tr2 hlt2 hk2 hq2 hh2 =>
          exact .rejected (8 + k0 + k1 + k2) (0 + 0 + 0 + q2) ([] ++ [] ++ [] ++ tr2) (by dsimp only [capEnd]; omega)
            (by omega) (by rw [hpar_eq]; omega) (((hpre8.trans hst0).trans hst1).halt hh2)
        | continued w3 k2 q2 tr2 hk2 hq2 hst2 hp2 =>
          obtain ⟨hq3, htr3w, hge3, hpc3, hreg3, hx20_3, htr_m2, hfa_m2⟩ := hp2
          subst hq3; subst htr3w
          have hfr3 : MemEqOutside w2 w3 (8192 + 32 * (3 * j + 2)) (8192 + 32 * (3 * j + 2) + 32) := by
            cases hm2 : m2 with
            | true => exact MemEqOutside.of_mem_eq (htr_m2 hm2) _ _
            | false => simpa only [show 8192 + 96 * j + 64 = 8192 + 32 * (3 * j + 2) by omega] using (hfa_m2 hm2).2
          have hreg3_u3 : ∀ r, r ≠ .x20 → r ≠ .x30 → r ≠ .x31 → w3.getReg r = u3.getReg r := fun r h20 h30 h31 =>
            (hreg3 r h20 h30 h31).trans ((hreg2 r h20 h30 h31).trans (hreg1 r h20 h30 h31))
          have hfix3 : CheckFixedRegs input w3 := hfix2.of_agree (fun r hr =>
            hreg3 r (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl))
          -- pc[211..213]: ECALL (x17 -> x28)
          have h211 := k_step_ADDI (oracle := oracle) (s := w3) (idx := 211) (by decide) hpc3 rfl
          let w4 := (w3.setReg .x10 (w3.getReg .x17 + signExtend12 0#12)).setPC (kPcAt 212)
          have h212 := k_step_ADDI (oracle := oracle) (s := w4) (idx := 212) (by decide) rfl rfl
          let w5 := (w4.setReg .x12 (w4.getReg .x28 + signExtend12 0#12)).setPC (kPcAt 213)
          have hx17_w3 : w3.getReg .x17 = BitVec.ofNat 64 (8192 + 96 * j) :=
            (hreg3_u3 .x17 (by decide) (by decide) (by decide)).trans
              ((hreg_u3 .x17 (by decide)).trans ((hreg5 .x17 (by decide) (by decide) (by decide) (by decide)).trans hinv.x17))
          have hx28_w3 : w3.getReg .x28 = BitVec.ofNat 64 (8192 + 32 * (286 + j)) :=
            (hreg3_u3 .x28 (by decide) (by decide) (by decide)).trans
              ((hreg_u3 .x28 (by decide)).trans ((hreg5 .x28 (by decide) (by decide) (by decide) (by decide)).trans hinv.x28))
          have hx10_w5 : w5.getReg .x10 = BitVec.ofNat 64 (8192 + 96 * j) := by
            simp only [w5, w4, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
              ne_eq, not_false_eq_true, reduceCtorEq, hx17_w3, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
          have hx12_w5 : w5.getReg .x12 = BitVec.ofNat 64 (8192 + 32 * (286 + j)) := by
            simp only [w5, w4, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
              ne_eq, not_false_eq_true, reduceCtorEq, hx28_w3, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
          have hfix5w : CheckFixedRegs input w5 := hfix3.of_agree (fun r hr => by
            have h10 := isCheckFixedReg_ne hr (r' := .x10) rfl
            have h12 := isCheckFixedReg_ne hr (r' := .x12) rfl
            simp only [w5, w4, MachineState.getReg_setPC,
              MachineState.getReg_setReg_ne _ _ _ _ h12.symm,
              MachineState.getReg_setReg_ne _ _ _ _ h10.symm])
          have hmem5w : w5.mem = w3.mem := by simp only [w5, w4, k_mem_setPC, k_mem_setReg]
          obtain ⟨w6, h213, hpc6, hreg6, hdig6, hfr6⟩ := k_cap_ecall_ex h768 oracle w5 213
            (8192 + 96 * j) (8192 + 32 * (286 + j)) (by decide) rfl rfl
            hfix5w.x5 hx10_w5 hfix5w.x11 hx12_w5 hfix5w.x13 (by omega) (by omega) (by omega) (by omega)
          have hfr_u3_w3 : MemEqOutside u3 w3 (8192 + 96 * j) (8192 + 96 * j + 96) :=
            (hfr1.mono (by omega) (by omega)).trans
              ((hfr2.mono (by omega) (by omega)).trans (hfr3.mono (by omega) (by omega)))
          have hfr_w3_w6 : MemEqOutside w3 w6 (8192 + 32 * (286 + j)) (8192 + 32 * (286 + j) + 32) :=
            (MemEqOutside.of_mem_eq hmem5w _ _).trans hfr6
          -- Key immutability lemma: any marked slot u < 286 + j, OR any slot u < 3 * j, is preserved from s to w6!
          have hpres_slot : ∀ u < 286 + j, (u < 3 * j ∨ capMark input.positions u = true) →
              readBuffer w6 (8192 + 32 * u) 32 = readBuffer s (8192 + 32 * u) 32 := by
            intro u hu hcond
            rw [hfr_w3_w6.readBuffer_eq (by omega) (by omega)]
            have h1 : readBuffer w3 (8192 + 32 * u) 32 = readBuffer w2 (8192 + 32 * u) 32 := by
              by_cases heq : u = 3 * j + 2
              · subst heq; rcases hcond with hlt | hm
                · omega
                · exact (MemEqOutside.of_mem_eq (htr_m2 hm) 0 0).readBuffer_eq (by omega) (by omega)
              · exact hfr3.readBuffer_eq (by omega) (by omega)
            have h2 : readBuffer w2 (8192 + 32 * u) 32 = readBuffer w1 (8192 + 32 * u) 32 := by
              by_cases heq : u = 3 * j + 1
              · subst heq; rcases hcond with hlt | hm
                · omega
                · exact (MemEqOutside.of_mem_eq (htr_m1 hm) 0 0).readBuffer_eq (by omega) (by omega)
              · exact hfr2.readBuffer_eq (by omega) (by omega)
            have h3 : readBuffer w1 (8192 + 32 * u) 32 = readBuffer u3 (8192 + 32 * u) 32 := by
              by_cases heq : u = 3 * j
              · subst heq; rcases hcond with hlt | hm
                · omega
                · exact (MemEqOutside.of_mem_eq (htr_m0 hm) 0 0).readBuffer_eq (by omega) (by omega)
              · exact hfr1.readBuffer_eq (by omega) (by omega)
            rw [h1, h2, h3, hfr_s_u3.readBuffer_eq (by omega) (by omega)]
          have hinp_w5 : readBuffer w5 (8192 + 96 * j) 96 =
              ternaryInput (readBuffer w6 (8192 + 32 * (3 * j)) 32)
                           (readBuffer w6 (8192 + 32 * (3 * j + 1)) 32)
                           (readBuffer w6 (8192 + 32 * (3 * j + 2)) 32) := by
            rw [readBuffer_ternary w5 (8192 + 96 * j)]
            have ha1' : 8192 + 96 * j + 32 = 8192 + 32 * (3 * j + 1) := by omega
            have ha2' : 8192 + 96 * j + 64 = 8192 + 32 * (3 * j + 2) := by omega
            have ha0' : 8192 + 96 * j = 8192 + 32 * (3 * j) := by omega
            rw [ha1', ha2', ha0',
              ← hfr6.readBuffer_eq (by omega) (by omega),
              ← hfr6.readBuffer_eq (by omega) (by omega),
              ← hfr6.readBuffer_eq (by omega) (by omega)]
          have hreg6_u3 : ∀ r, r ≠ .x10 → r ≠ .x12 → r ≠ .x20 → r ≠ .x30 → r ≠ .x31 →
              w6.getReg r = u3.getReg r := fun r h10 h12 h20 h30 h31 => by
            rw [hreg6 r]
            simp only [w5, w4, MachineState.getReg_setPC,
              MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h12),
              MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h10)]
            exact hreg3_u3 r h20 h30 h31
          have hx20_w6 : w6.getReg .x20 = BitVec.ofNat 64
              (11072966688 + (baseOff + 32 * capFrontierCountPrefix input.positions (j + 1))) := by
            rw [hreg6 .x20]; simp only [w5, w4, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx20_3]
            exact congrArg (BitVec.ofNat 64) (by rw [hpref_next]; omega)
          obtain ⟨s', htail, hinv'⟩ := htail_fn w6 1
            [((readBuffer w5 (8192 + 96 * j) 96).cast h768.symm,
              oracle.compression ((readBuffer w5 (8192 + 96 * j) 96).cast h768.symm))]
            hpc6 (hfix5w.of_agree (fun r _ => hreg6 r))
            ((hreg6_u3 .x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              ((hreg_u3 .x14 (by decide)).trans ((hreg5 .x14 (by decide) (by decide) (by decide) (by decide)).trans hinv.x14)))
            ((hreg6_u3 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              ((hreg_u3 .x15 (by decide)).trans ((hreg5 .x15 (by decide) (by decide) (by decide) (by decide)).trans hinv.x15)))
            ((hreg6_u3 .x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              ((hreg_u3 .x16 (by decide)).trans ((hreg5 .x16 (by decide) (by decide) (by decide) (by decide)).trans hinv.x16)))
            ((hreg6_u3 .x17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              ((hreg_u3 .x17 (by decide)).trans ((hreg5 .x17 (by decide) (by decide) (by decide) (by decide)).trans hinv.x17)))
            ((hreg6_u3 .x28 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              ((hreg_u3 .x28 (by decide)).trans ((hreg5 .x28 (by decide) (by decide) (by decide) (by decide)).trans hinv.x28)))
            hx20_w6
            (by rw [hpref_next]; omega)
            (hhigh_u3.trans ((hfr_u3_w3.mono (by omega) (by omega)).trans (hfr_w3_w6.mono (by omega) (by omega))))
            (fun x hx => by
              rw [hfr_w3_w6 (4096 + x) (by omega) (by omega), hfr_u3_w3 (4096 + x) (by omega) (by omega)]
              exact hmark_u3 x hx)
            (by rw [hfr_w3_w6.readBuffer_eq (by omega) (by omega), hfr_u3_w3.readBuffer_eq (by omega) (by omega),
                  hfr_s_u3.readBuffer_eq (by omega) (by omega), hinv.val_428_zero])
            (fun c hc hmc => (hpres_slot c (by omega) (Or.inr hmc)).trans (hinv.val_leaf_marked c hc hmc))
            (fun j' hj' hmj' => by
              by_cases hlt' : j' < j
              · have hp0 := hpres_slot (3 * j') (by omega) (Or.inl (by omega))
                have hp1 := hpres_slot (3 * j' + 1) (by omega) (Or.inl (by omega))
                have hp2 := hpres_slot (3 * j' + 2) (by omega) (Or.inl (by omega))
                have hpp := hpres_slot (286 + j') (by omega) (Or.inr hmj')
                obtain ⟨hv, htrv, hc0, hc1, hc2⟩ := hinv.val_internal j' hlt' hmj'
                rw [hp0, hp1, hp2, hpp]
                exact ⟨hv, htrv.append_left, hc0, hc1, hc2⟩
              · have heq : j' = j := by omega
                subst j'
                refine ⟨by rw [hdig6, congrArg (·.cast h768.symm) hinp_w5],
                  by unfold InTrace; rw [← hinp_w5]; exact List.mem_append_right tr List.mem_cons_self,
                  fun hm0f => by
                    rw [hfr_w3_w6.readBuffer_eq (by omega) (by omega), hfr3.readBuffer_eq (by omega) (by omega),
                      hfr2.readBuffer_eq (by omega) (by omega), hco0]
                    simpa only [show 8192 + 96 * j + 0 = 8192 + 32 * (3 * j) by omega] using (hfa_m0 hm0f).1,
                  fun hm1f => by
                    rw [hfr_w3_w6.readBuffer_eq (by omega) (by omega), hfr3.readBuffer_eq (by omega) (by omega), hco1]
                    simpa only [show 8192 + 96 * j + 32 = 8192 + 32 * (3 * j + 1) by omega] using (hfa_m1 hm1f).1,
                  fun hm2f => by
                    rw [hfr_w3_w6.readBuffer_eq (by omega) (by omega), hco2]
                    simpa only [show 8192 + 96 * j + 64 = 8192 + 32 * (3 * j + 2) by omega] using (hfa_m2 hm2f).1⟩)
          have hfin : StepsTo oracle w3 s' 8 1
              [((readBuffer w5 (8192 + 96 * j) 96).cast h768.symm,
                oracle.compression ((readBuffer w5 (8192 + 96 * j) 96).cast h768.symm))] := by
            simpa only [show 1 + 1 + 1 + 5 = 8 from rfl, List.nil_append, List.append_nil] using
              ((h211.trans h212).trans h213).trans htail
          have hall : StepsTo oracle s s' (8 + k0 + k1 + k2 + 8) 1
              [((readBuffer w5 (8192 + 96 * j) 96).cast h768.symm,
                oracle.compression ((readBuffer w5 (8192 + 96 * j) 96).cast h768.symm))] := by
            simpa only [Nat.add_zero, Nat.zero_add, List.nil_append] using
              (((hpre8.trans hst0).trans hst1).trans hst2).trans hfin
          exact .continued s' (8 + k0 + k1 + k2 + 8) 1 _ (by omega) (by rw [hpar_eq]; exact le_rfl) hall
            ⟨by rw [hpar_eq]; rfl, hinv'⟩

structure CapDoneInv (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (baseOff : Nat) (sPos s : MachineState)
    (tr : CompressionReplies) : Prop where
  fixed    : CheckFixedRegs input s
  high     : HighMemPreserved (submission.initialState .check input) s
  pc       : s.pc = kPcAt 250
  x28      : s.getReg .x28 = BitVec.ofNat 64 (8192 + 32 * 428)
  x20      : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + (baseOff + 32 * capFrontierCount input.positions))
  len_le   : baseOff + 32 * capFrontierCount input.positions ≤ input.proof.length
  val_leaf_marked : ∀ c < 286, capMark input.positions c = true →
    readBuffer s (8192 + 32 * c) 32 = readBuffer sPos (8192 + 32 * c) 32
  val_internal : ∀ j < 142, capMark input.positions (286 + j) = true →
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let d0 := readBuffer s (8192 + 32 * (3 * j)) 32
    let d1 := readBuffer s (8192 + 32 * (3 * j + 1)) 32
    let d2 := readBuffer s (8192 + 32 * (3 * j + 2)) 32
    readBuffer s (8192 + 32 * (286 + j)) 32 = c96 (ternaryInput d0 d1 d2) ∧
    InTrace h768 oracle tr (ternaryInput d0 d1 d2) ∧
    (capMark input.positions (3 * j) = false → d0 = readBuffer s0 (11072966688 + capChildOff input.positions baseOff j 0) 32) ∧
    (capMark input.positions (3 * j + 1) = false → d1 = readBuffer s0 (11072966688 + capChildOff input.positions baseOff j 1) 32) ∧
    (capMark input.positions (3 * j + 2) = false → d2 = readBuffer s0 (11072966688 + capChildOff input.positions baseOff j 2) 32)
  val_root :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let d0 := readBuffer s (8192 + 32 * 426) 32
    let d1 := readBuffer s (8192 + 32 * 427) 32
    readBuffer s (8192 + 32 * 428) 32 = c96 (ternaryInput d0 d1 0#256) ∧
    InTrace h768 oracle tr (ternaryInput d0 d1 0#256) ∧
    (capMark input.positions 426 = false → d0 = readBuffer s0 (11072966688 + capChildOff input.positions baseOff 142 0) 32) ∧
    (capMark input.positions 427 = false → d1 = readBuffer s0 (11072966688 + capChildOff input.positions baseOff 142 1) 32)

private theorem capFrontierCount_142 (positions : Positions) (hne : positions.Nonempty)
    (m0 m1 : Bool) (hm0 : capMark positions 426 = m0) (hm1 : capMark positions 427 = m1) :
    capFrontierCount positions =
      capFrontierCountPrefix positions 142 + ((if !m0 then 1 else 0) + (if !m1 then 1 else 0)) := by
  have h428 := capMark_428_eq_true positions hne
  have hcnt142 : capNodeFrontierCount positions 142 = (if !m0 then 1 else 0) + (if !m1 then 1 else 0) := by
    unfold capNodeFrontierCount
    simp only [show ¬ (142 < 142) by omega, ite_false, ite_true, h428, hm0, hm1]
  rw [← capFrontierCountPrefix_143, show (143 : Nat) = 142 + 1 from rfl,
    capFrontierCountPrefix_succ positions 142, hcnt142]

private theorem cap_mul32_two (b0 b1 : Bool) :
    32 * ((if !b0 then 1 else 0) + (if !b1 then 1 else 0)) =
      (if !b0 then 32 else 0) + (if !b1 then 32 else 0) := by
  cases b0 <;> cases b1 <;> decide

private theorem check_cap_root_reads (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    {s : MachineState}
    (off0 : Nat) (hoff0_le : off0 ≤ input.proof.length) (hoff0_8 : off0 % 8 = 0)
    (m0 m1 : Bool)
    (hpc219 : s.pc = kPcAt 219)
    (hfix : CheckFixedRegs input s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (h14_init : s.getReg .x14 = BitVec.ofNat 64 (4096 + 426))
    (h17_init : s.getReg .x17 = BitVec.ofNat 64 (8192 + 32 * 426))
    (h28_init : s.getReg .x28 = BitVec.ofNat 64 (8192 + 32 * 428))
    (h20_init : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + off0))
    (hmark426 : s.getByte (BitVec.ofNat 64 (4096 + 426)) = if m0 then 1#8 else 0#8)
    (hmark427 : s.getByte (BitVec.ofNat 64 (4096 + 427)) = if m1 then 1#8 else 0#8) :
    let a0 := if !m0 then 32 else 0
    let a1 := if !m1 then 32 else 0
    let s0 := submission.initialState .check input
    PhaseOutcome oracle s 28 0 (input.proof.length < off0 + a0 + a1)
      (fun t4 q tr' =>
        q = 0 ∧ tr' = [] ∧
        t4.pc = kPcAt 247 ∧
        CheckFixedRegs input t4 ∧
        t4.getReg .x17 = BitVec.ofNat 64 (8192 + 32 * 426) ∧
        t4.getReg .x28 = BitVec.ofNat 64 (8192 + 32 * 428) ∧
        t4.getReg .x20 = BitVec.ofNat 64 (11072966688 + (off0 + a0 + a1)) ∧
        off0 + a0 + a1 ≤ input.proof.length ∧
        MemEqOutside s t4 (8192 + 32 * 426) (8192 + 32 * 428) ∧
        (m0 = true → readBuffer t4 (8192 + 32 * 426) 32 = readBuffer s (8192 + 32 * 426) 32) ∧
        (m1 = true → readBuffer t4 (8192 + 32 * 427) 32 = readBuffer s (8192 + 32 * 427) 32) ∧
        (m0 = false → readBuffer t4 (8192 + 32 * 426) 32 = readBuffer s0 (11072966688 + off0) 32) ∧
        (m1 = false → readBuffer t4 (8192 + 32 * 427) 32 = readBuffer s0 (11072966688 + (off0 + a0)) 32)) := by
  intro a0 a1 s0
  -- pc[219]: LBU x6, 0(x14)
  have ha219 : s.getReg .x14 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + 426) := by
    rw [h14_init, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
  have h219 := k_step_LBU (oracle := oracle) (s := s) (idx := 219) (by decide) hpc219 rfl
    (by rw [ha219]; exact k_accessValid _ 1 (by omega) (by omega))
  let t1 := (s.setReg .x6 ((s.getByte (s.getReg .x14 + signExtend12 0#12)).zeroExtend 64)).setPC (kPcAt 220)
  have hx6_1 : t1.getReg .x6 = if m0 then 1#64 else 0#64 := by
    simp only [t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      ha219, hmark426]
    exact k_bool_byte_zext m0
  have hfix1 : CheckFixedRegs input t1 := hfix.of_agree (fun r hr => by
    have h6 := isCheckFixedReg_ne hr (r' := .x6) rfl
    simp only [t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm])
  have hm1_mem : t1.mem = s.mem := by simp only [t1, k_mem_setPC, k_mem_setReg]
  have hhigh1 : HighMemPreserved s0 t1 := hhigh.trans (MemEqOutside.of_mem_eq hm1_mem 0 4294971392)
  have hx17_1 : t1.getReg .x17 = BitVec.ofNat 64 (8192 + 32 * 426) := by
    simp only [t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x17), h17_init]
  have hx20_1 : t1.getReg .x20 = BitVec.ofNat 64 (11072966688 + off0) := by
    simp only [t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x20), h20_init]
  -- pc[220..232]: conditional read for 426
  have hr0 := check_cap_cond_read32 oracle input hvalid (s := t1) (idx := 220) (dstOff := 0)
    (base17 := 8192 + 32 * 426) (off := off0) (flagReg := .x6) (flag := m0) (brRej := 172#13)
    (by decide) rfl k_tgt_220 k_tgt_223 (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hfix1 hhigh1 hx6_1 hx17_1 (by omega) (by omega) (by omega) hx20_1 hoff0_le hoff0_8
  cases hr0 with
  | rejected k0 q0 tr0 hlt0 hk0 hq0 hh0 =>
    exact .rejected (1 + k0) (0 + q0) ([] ++ tr0) (by dsimp only [a0, a1]; omega)
      (by omega) (by omega) (h219.halt hh0)
  | continued t2 k0 q0 tr0 hk0 hq0 hst0 hp0 =>
    obtain ⟨hq2, htr2, hge2, hpc2, hreg2, hx20_2, htr_m0, hfa_m0⟩ := hp0
    subst hq2; subst htr2
    have hfr2 : MemEqOutside s t2 (8192 + 32 * 426) (8192 + 32 * 426 + 32) := by
      refine (MemEqOutside.of_mem_eq hm1_mem _ _).trans ?_
      cases hm0 : m0 with
      | true => exact MemEqOutside.of_mem_eq (htr_m0 hm0) _ _
      | false => simpa only [Nat.add_zero] using (hfa_m0 hm0).2
    -- pc[233]: LBU x7, 1(x14)
    have hx14_2 : t2.getReg .x14 = BitVec.ofNat 64 (4096 + 426) := by
      rw [hreg2 .x14 (by decide) (by decide) (by decide)]
      simp only [t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x14), h14_init]
    have ha233 : t2.getReg .x14 + signExtend12 1#12 = BitVec.ofNat 64 (4096 + 427) := by
      rw [hx14_2, show signExtend12 1#12 = BitVec.ofNat 64 1 by decide, k_bv_add]
    have h233 := k_step_LBU (oracle := oracle) (s := t2) (idx := 233) (by decide) hpc2 rfl
      (by rw [ha233]; exact k_accessValid _ 1 (by omega) (by omega))
    let t3 := (t2.setReg .x7 ((t2.getByte (t2.getReg .x14 + signExtend12 1#12)).zeroExtend 64)).setPC (kPcAt 234)
    have hx7_3 : t3.getReg .x7 = if m1 then 1#64 else 0#64 := by
      simp only [t3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, ha233]
      rw [hfr2 (4096 + 427) (by omega) (by omega), hmark427]
      exact k_bool_byte_zext m1
    have hfix3 : CheckFixedRegs input t3 := (hfix1.of_agree (fun r hr =>
      hreg2 r (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl))).of_agree (fun r hr => by
        have h7 := isCheckFixedReg_ne hr (r' := .x7) rfl
        simp only [t3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h7.symm])
    have hm3_mem : t3.mem = t2.mem := by simp only [t3, k_mem_setPC, k_mem_setReg]
    have hhigh3 : HighMemPreserved s0 t3 := hhigh.trans ((hfr2.mono (by omega) (by omega)).trans
      (MemEqOutside.of_mem_eq hm3_mem 0 4294971392))
    have hx17_3 : t3.getReg .x17 = BitVec.ofNat 64 (8192 + 32 * 426) := by
      simp only [t3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x17)]
      exact (hreg2 .x17 (by decide) (by decide) (by decide)).trans hx17_1
    have hx20_3 : t3.getReg .x20 = BitVec.ofNat 64 (11072966688 + (off0 + a0)) := by
      simp only [t3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x20), hx20_2, a0]
    -- pc[234..246]: conditional read for 427
    have hr1 := check_cap_cond_read32 oracle input hvalid (s := t3) (idx := 234) (dstOff := 32)
      (base17 := 8192 + 32 * 426) (off := off0 + a0) (flagReg := .x7) (flag := m1) (brRej := 116#13)
      (by decide) rfl k_tgt_234 k_tgt_237 (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hfix3 hhigh3 hx7_3 hx17_3 (by omega) (by omega) (by omega) hx20_3 hge2
      (by dsimp only [a0]; split_ifs <;> omega)
    cases hr1 with
    | rejected k1 q1 tr1 hlt1 hk1 hq1 hh1 =>
      exact .rejected (1 + k0 + 1 + k1) (0 + 0 + 0 + q1) ([] ++ [] ++ [] ++ tr1) hlt1
        (by omega) (by omega) (((h219.trans hst0).trans h233).halt hh1)
    | continued t4 k1 q1 tr1 hk1 hq1 hst1 hp1 =>
      obtain ⟨hq4, htr4, hge4, hpc4, hreg4, hx20_4, htr_m1, hfa_m1⟩ := hp1
      subst hq4; subst htr4
      have hfr4 : MemEqOutside t2 t4 (8192 + 32 * 427) (8192 + 32 * 427 + 32) := by
        refine (MemEqOutside.of_mem_eq hm3_mem _ _).trans ?_
        cases hm1 : m1 with
        | true => exact MemEqOutside.of_mem_eq (htr_m1 hm1) _ _
        | false => simpa only [show 8192 + 32 * 426 + 32 = 8192 + 32 * 427 by omega] using (hfa_m1 hm1).2
      have hfix4 : CheckFixedRegs input t4 := hfix3.of_agree (fun r hr =>
        hreg4 r (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl) (isCheckFixedReg_ne hr rfl))
      have hx17_4 : t4.getReg .x17 = BitVec.ofNat 64 (8192 + 32 * 426) :=
        (hreg4 .x17 (by decide) (by decide) (by decide)).trans hx17_3
      have hx28_4 : t4.getReg .x28 = BitVec.ofNat 64 (8192 + 32 * 428) := by
        rw [hreg4 .x28 (by decide) (by decide) (by decide)]
        simp only [t3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x28)]
        rw [hreg2 .x28 (by decide) (by decide) (by decide)]
        simp only [t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28), h28_init]
      have hall : StepsTo oracle s t4 (1 + k0 + 1 + k1) 0 [] := by
        simpa only [Nat.add_zero, List.append_nil] using ((h219.trans hst0).trans h233).trans hst1
      exact .continued t4 (1 + k0 + 1 + k1) 0 [] (by omega) le_rfl hall
        ⟨rfl, rfl, hpc4, hfix4, hx17_4, hx28_4, hx20_4, hge4,
          (hfr2.mono (by omega) (by omega)).trans (hfr4.mono (by omega) (by omega)),
          fun hm0 => by
            rw [hfr4.readBuffer_eq (by omega) (by omega)]
            exact (MemEqOutside.of_mem_eq ((htr_m0 hm0).trans hm1_mem) 0 0).readBuffer_eq (by omega) (by omega),
          fun hm1 => (MemEqOutside.of_mem_eq ((htr_m1 hm1).trans hm3_mem) 0 0).readBuffer_eq (by omega) (by omega) |>.trans
            (hfr2.readBuffer_eq (by omega) (by omega)),
          fun hm0 => by
            rw [hfr4.readBuffer_eq (by omega) (by omega)]
            simpa only [Nat.add_zero] using (hfa_m0 hm0).1,
          fun hm1 => by
            simpa only [show 8192 + 32 * 426 + 32 = 8192 + 32 * 427 by omega] using (hfa_m1 hm1).1⟩

private theorem check_cap_root (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hne : input.positions.Nonempty) {baseOff : Nat} {sPos s : MachineState} {tr : CompressionReplies}
    (hbase8 : baseOff % 8 = 0)
    (hinv : CapLoopInv h768 oracle input baseOff sPos 142 s tr) :
    let capEnd := baseOff + 32 * capFrontierCount input.positions
    PhaseOutcome oracle s 31 1 (input.proof.length < capEnd)
      (fun s' q' tr' => q' = 1 ∧ CapDoneInv h768 oracle input baseOff sPos s' (tr ++ tr')) := by
  intro capEnd
  have hpc219 : s.pc = kPcAt 219 := by have h := hinv.pc; simpa only [ite_true] using h
  have h14_init : s.getReg .x14 = BitVec.ofNat 64 (4096 + 426) :=
    hinv.x14.trans (congrArg (BitVec.ofNat 64) (by omega))
  have h17_init : s.getReg .x17 = BitVec.ofNat 64 (8192 + 32 * 426) :=
    hinv.x17.trans (congrArg (BitVec.ofNat 64) (by omega))
  have h28_init : s.getReg .x28 = BitVec.ofNat 64 (8192 + 32 * 428) :=
    hinv.x28.trans (congrArg (BitVec.ofNat 64) (by omega))
  have hm426 : s.getByte (BitVec.ofNat 64 (4096 + 426)) = if capMark input.positions 426 then 1#8 else 0#8 := by
    have h := hinv.marks 426 (by omega)
    unfold capMarkPrefix at h
    simpa only [show 426 < 286 + 142 by omega, ite_true] using h
  have hm427 : s.getByte (BitVec.ofNat 64 (4096 + 427)) = if capMark input.positions 427 then 1#8 else 0#8 := by
    have h := hinv.marks 427 (by omega)
    unfold capMarkPrefix at h
    simpa only [show 427 < 286 + 142 by omega, ite_true] using h
  have hcap_add : capEnd =
      (baseOff + 32 * capFrontierCountPrefix input.positions 142) +
      (if !capMark input.positions 426 then 32 else 0) +
      (if !capMark input.positions 427 then 32 else 0) := by
    dsimp only [capEnd]
    rw [capFrontierCount_142 input.positions hne _ _ rfl rfl, Nat.mul_add, cap_mul32_two]
    omega
  have hco0 : capChildOff input.positions baseOff 142 0 =
      baseOff + 32 * capFrontierCountPrefix input.positions 142 := by
    unfold capChildOff; simp only [show ¬ (142 < 142) by omega, ite_false, ite_true]
  have hco1 : capChildOff input.positions baseOff 142 1 =
      (baseOff + 32 * capFrontierCountPrefix input.positions 142) +
      (if !capMark input.positions 426 then 32 else 0) := by
    unfold capChildOff; simp only [show ¬ (142 < 142) by omega, show (1 : Nat) ≠ 0 by omega, ite_false]
  have hreads := check_cap_root_reads oracle input hvalid
    (baseOff + 32 * capFrontierCountPrefix input.positions 142) hinv.len_le (by omega)
    (capMark input.positions 426) (capMark input.positions 427)
    hpc219 hinv.fixed hinv.high h14_init h17_init h28_init hinv.x20 hm426 hm427
  cases hreads with
  | rejected k q tr' hlt hk hq hh =>
    rw [← hcap_add] at hlt
    exact .rejected k q tr' hlt (by omega) (by omega) hh
  | continued t4 k q tr' hk hq hst hp =>
    obtain ⟨hq0, htr0, hpc4, hfix4, hx17_4, hx28_4, hx20_4, hge4, hfr_s_t4,
      hm0_t, hm1_t, hm0_f, hm1_f⟩ := hp
    subst hq0; subst htr0
    rw [← hcap_add] at hx20_4 hge4
    -- pc[247..249]: ECALL (x17 -> x28)
    have h247 := k_step_ADDI (oracle := oracle) (s := t4) (idx := 247) (by decide) hpc4 rfl
    let t5 := (t4.setReg .x10 (t4.getReg .x17 + signExtend12 0#12)).setPC (kPcAt 248)
    have h248 := k_step_ADDI (oracle := oracle) (s := t5) (idx := 248) (by decide) rfl rfl
    let t6 := (t5.setReg .x12 (t5.getReg .x28 + signExtend12 0#12)).setPC (kPcAt 249)
    have hx10_6 : t6.getReg .x10 = BitVec.ofNat 64 (8192 + 32 * 426) := by
      simp only [t6, t5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hx17_4, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
    have hx12_6 : t6.getReg .x12 = BitVec.ofNat 64 (8192 + 32 * 428) := by
      simp only [t6, t5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, MachineState.getReg_setReg_eq,
        ne_eq, not_false_eq_true, reduceCtorEq, hx28_4, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
    have hfix6 : CheckFixedRegs input t6 := hfix4.of_agree (fun r hr => by
      have h10 := isCheckFixedReg_ne hr (r' := .x10) rfl
      have h12 := isCheckFixedReg_ne hr (r' := .x12) rfl
      simp only [t6, t5, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h12.symm,
        MachineState.getReg_setReg_ne _ _ _ _ h10.symm])
    have hmem6 : t6.mem = t4.mem := by simp only [t6, t5, k_mem_setPC, k_mem_setReg]
    obtain ⟨t7, h249, hpc7, hreg7, hdig7, hfr7⟩ := k_cap_ecall_ex h768 oracle t6 249
      (8192 + 32 * 426) (8192 + 32 * 428) (by decide) rfl rfl
      hfix6.x5 hx10_6 hfix6.x11 hx12_6 hfix6.x13 (by omega) (by omega) (by omega) (by omega)
    have hfr_t4_t7 : MemEqOutside t4 t7 (8192 + 32 * 428) (8192 + 32 * 428 + 32) :=
      (MemEqOutside.of_mem_eq hmem6 _ _).trans hfr7
    have hpres_slot : ∀ u < 428, (u < 426 ∨ capMark input.positions u = true) →
        readBuffer t7 (8192 + 32 * u) 32 = readBuffer s (8192 + 32 * u) 32 := by
      intro u hu hcond
      rw [hfr_t4_t7.readBuffer_eq (by omega) (by omega)]
      by_cases h426 : u < 426
      · exact hfr_s_t4.readBuffer_eq (by omega) (by omega)
      · rcases hcond with hlt | hm
        · omega
        · by_cases heq : u = 426
          · subst heq; exact hm0_t hm
          · have h427 : u = 427 := by omega
            subst h427; exact hm1_t hm
    have hzero_t6 : readBuffer t6 (8192 + 32 * 428) 32 = 0#256 := by
      rw [(MemEqOutside.of_mem_eq hmem6 0 0).readBuffer_eq (by omega) (by omega),
        hfr_s_t4.readBuffer_eq (by omega) (by omega), hinv.val_428_zero]
    have hinp_t6 : readBuffer t6 (8192 + 32 * 426) 96 =
        ternaryInput (readBuffer t7 (8192 + 32 * 426) 32) (readBuffer t7 (8192 + 32 * 427) 32) 0#256 := by
      rw [readBuffer_ternary t6 (8192 + 32 * 426)]
      have ha1 : 8192 + 32 * 426 + 32 = 8192 + 32 * 427 := by omega
      have ha2 : 8192 + 32 * 426 + 64 = 8192 + 32 * 428 := by omega
      rw [ha1, ha2, hzero_t6, ← hfr7.readBuffer_eq (by omega) (by omega), ← hfr7.readBuffer_eq (by omega) (by omega)]
    have hfin : StepsTo oracle t4 t7 3 1
        [((readBuffer t6 (8192 + 32 * 426) 96).cast h768.symm,
          oracle.compression ((readBuffer t6 (8192 + 32 * 426) 96).cast h768.symm))] := by
      simpa only [show 1 + 1 + 1 = 3 from rfl, List.nil_append] using (h247.trans h248).trans h249
    have hall : StepsTo oracle s t7 (k + 3) 1
        [((readBuffer t6 (8192 + 32 * 426) 96).cast h768.symm,
          oracle.compression ((readBuffer t6 (8192 + 32 * 426) 96).cast h768.symm))] := by
      simpa only [Nat.zero_add, List.nil_append] using hst.trans hfin
    exact .continued t7 (k + 3) 1 _ (by omega) le_rfl hall
      ⟨rfl, ⟨hfix6.of_agree (fun r _ => hreg7 r),
        hinv.high.trans ((hfr_s_t4.mono (by omega) (by omega)).trans (hfr_t4_t7.mono (by omega) (by omega))),
        hpc7,
        by rw [hreg7 .x28]; simp only [t6, t5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx28_4],
        by rw [hreg7 .x20]; simp only [t6, t5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx20_4]; rfl,
        hge4,
        fun c hc hmc => (hpres_slot c (by omega) (Or.inl (by omega))).trans (hinv.val_leaf_marked c hc hmc),
        fun j' hj' hmj' => by
          have hp0 := hpres_slot (3 * j') (by omega) (Or.inl (by omega))
          have hp1 := hpres_slot (3 * j' + 1) (by omega) (Or.inl (by omega))
          have hp2 := hpres_slot (3 * j' + 2) (by omega) (Or.inl (by omega))
          have hpp := hpres_slot (286 + j') (by omega) (Or.inr hmj')
          obtain ⟨hv, htrv, hc0, hc1, hc2⟩ := hinv.val_internal j' hj' hmj'
          rw [hp0, hp1, hp2, hpp]
          exact ⟨hv, htrv.append_left, hc0, hc1, hc2⟩,
        ⟨by rw [hdig7, congrArg (·.cast h768.symm) hinp_t6],
         by unfold InTrace; rw [← hinp_t6]; exact List.mem_append_right tr List.mem_cons_self,
         fun hm0f => (hfr_t4_t7.readBuffer_eq (by omega) (by omega)).trans ((hm0_f hm0f).trans (by rw [← hco0])),
         fun hm1f => (hfr_t4_t7.readBuffer_eq (by omega) (by omega)).trans ((hm1_f hm1f).trans (by rw [← hco1]))⟩⟩⟩

/-- Full cap phase (`pc[156..249]`): setup + 142-iter cap loop + root hash. -/
theorem check_cap_walk (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (hne : input.positions.Nonempty) (sPos : MachineState) (trPos : CompressionReplies)
    (hinvPos : PosLoopInv h768 oracle input input.positions.card sPos trPos) :
    let baseOff := posRecordOff input.positions input.positions.card
    let capEnd := baseOff + 32 * capFrontierCount input.positions
    PhaseOutcome oracle sPos 8000 (capMarkedInternalCount input.positions)
      (input.proof.length < capEnd)
      (fun sCap _ trCap => CapDoneInv h768 oracle input baseOff sPos sCap trCap) := by
  intro baseOff capEnd
  have hpc156 : sPos.pc = kPcAt 156 := by have h := hinvPos.pc; simpa only [ite_true] using h
  obtain ⟨sInit, hsetup, hpc164, hmemInit, hfixInit, hx14, hx15, hx16, hx17, hx28, hx20⟩ :=
    check_cap_setup oracle input hpc156 hinvPos.fixed
  have hbase8 : baseOff % 8 = 0 := posRecordOff_mod8 _ _
  have hinitCap : CapLoopInv h768 oracle input baseOff sPos 0 sInit [] :=
    ⟨hfixInit, hinvPos.high.trans (MemEqOutside.of_mem_eq hmemInit 0 4294971392),
     by simp [hpc164], hx14, hx15, hx16, hx17, hx28,
     by simpa [capFrontierCountPrefix_zero] using hx20.trans hinvPos.x20,
     by simpa [capFrontierCountPrefix_zero] using hinvPos.len_le,
     fun u hu => by
       simp only [MachineState.getByte, MachineState.getMem, hmemInit]
       change sPos.getByte (BitVec.ofNat 64 (4096 + u)) = _
       unfold capMarkPrefix
       by_cases h286 : u < 286
       · simp only [Nat.add_zero, h286, ite_true]
         rw [hinvPos.marks_lo u h286, posMarked_card_eq_capMark input.positions u h286]
       · simp only [Nat.add_zero, h286, ite_false]
         exact hinvPos.marks_hi u (by omega) hu,
     by rw [(MemEqOutside.of_mem_eq hmemInit 0 0).readBuffer_eq (by omega) (by omega)]
        exact readBuffer_zero_of_bytes sPos (8192 + 32 * 428) 32 (fun j hj => hinvPos.vals_hi _ (by omega) (by omega)),
     fun c _ _ => (MemEqOutside.of_mem_eq hmemInit 0 0).readBuffer_eq (by omega) (by omega),
     fun _ h => (Nat.not_lt_zero _ h).elim⟩
  have hloop : ∀ n ≤ 142,
      PhaseOutcome oracle sInit (55 * n) (capMarkedInternalPrefix input.positions n)
        (input.proof.length < capEnd)
        (fun s' _ tr' => CapLoopInv h768 oracle input baseOff sPos n s' tr') := by
    intro n hn
    induction n with
    | zero => exact .continued sInit 0 0 [] le_rfl le_rfl (StepsTo.refl oracle sInit) hinitCap
    | succ k ih =>
      refine ((ih (by omega)).bind_dep id (fun sk _ trk hinvk =>
        (check_cap_step h768 oracle input hvalid hbase8 (by omega) hinvk).weaken
          le_rfl le_rfl id (fun s' _ tr' hp => hp.2))).weaken
        (by omega) (by rw [capMarkedInternalPrefix_succ]) id (fun _ _ _ h => h)
  have h428 := capMark_428_eq_true input.positions hne
  have htot_calls : capMarkedInternalPrefix input.positions 142 + 1 = capMarkedInternalCount input.positions := by
    rw [← capMarkedInternalPrefix_143, show (143 : Nat) = 142 + 1 from rfl,
      capMarkedInternalPrefix_succ input.positions 142, h428]; simp
  refine (hsetup.prepend_pure ((hloop 142 le_rfl).bind_dep id (fun s142 _ tr142 hinv142 =>
    (check_cap_root h768 oracle input hvalid hne hbase8 hinv142).weaken
      le_rfl le_rfl id (fun s' _ tr' hp => hp.2)))).weaken
    (by omega) (by rw [htot_calls]) id (fun _ _ _ h => h)

/-! ### 5. Epilogue (`pc[250..268]`): Exact Proof Length and Commitment Equality -/

theorem check_epilogue (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    {baseOff : Nat} {sPos sCap : MachineState} {trCap : CompressionReplies}
    (hdone : CapDoneInv h768 oracle input baseOff sPos sCap trCap) :
    let capEnd := baseOff + 32 * capFrontierCount input.positions
    ∃ k ≤ 20,
      HaltsWith oracle sCap k 0
        (if capEnd == input.proof.length &&
            readBuffer sCap (8192 + 32 * 428) 32 == (input.commitment : BitVec (8 * 32))
         then .success else .failure) [] := by
  intro capEnd
  have hproof_bd : input.proof.length ≤ 11140077536 := hvalid
  have hlen_le := hdone.len_le
  have hbeq_f : ∀ (a b : BitVec (8 * 32)), a ≠ b → (a == b) = false := fun a b hne => by
    cases h : (a == b)
    · rfl
    · exact (hne (eq_of_beq h)).elim
  have hbeq_t : ∀ (a b : BitVec (8 * 32)), a = b → (a == b) = true := fun a b heq => by
    subst heq; exact beq_self_eq_true _
  by_cases hlen : capEnd = input.proof.length
  · have hlen' : baseOff + 32 * capFrontierCount input.positions = input.proof.length := hlen
    have h250 := k_step_BNE_not_taken (oracle := oracle) (s := sCap) (idx := 250) (by decide) hdone.pc rfl
      (by rw [hdone.x20, hdone.fixed.x21, hlen'])
    let s1 := sCap.setPC (kPcAt 251)
    have hcmp := k_cmp32_or_reject oracle (s := s1) (idx := 251) (aReg := .x28) (bReg := .x8)
      (aOff := 0) (bOff := 0) (a := 8192 + 32 * 428) (b := 4294971392)
      (by decide) rfl (by decide) (by decide)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      k_tgt_253 k_tgt_256 k_tgt_259 k_tgt_262
      (by decide) (by decide) (by decide) (by decide)
      hdone.x28 hdone.fixed.x8 (by omega) (by omega) (by omega) (by omega)
    have hm1 : s1.mem = sCap.mem := rfl
    have hcmt : readBuffer s1 (4294971392 + 0) 32 = input.commitment := by
      rw [Nat.add_zero, (MemEqOutside.of_mem_eq hm1 0 0).readBuffer_eq (by omega) (by omega),
        hdone.high.readBuffer_eq (by omega) (by omega), check_initial_commitment]
    have hrt : readBuffer s1 (8192 + 32 * 428 + 0) 32 = readBuffer sCap (8192 + 32 * 428) 32 := by
      rw [Nat.add_zero]; rfl
    cases hcmp with
    | rejected k q tr hne hk hq hh =>
      have hq0 : q = 0 := by omega
      subst hq0
      have htr0 : tr = [] := haltsWith_zero_calls_nil hh
      subst htr0
      rw [hrt, hcmt] at hne
      have hcond : (capEnd == input.proof.length &&
          readBuffer sCap (8192 + 32 * 428) 32 == (input.commitment : BitVec (8 * 32))) = false := by
        rw [hbeq_f _ _ hne, Bool.and_false]
      rw [hcond]
      exact ⟨1 + k, by omega, by simpa using h250.halt hh⟩
    | continued s2 k q tr hk hq hs hp =>
      obtain ⟨hq2, htr2, hpc2, heq, _, _⟩ := hp
      subst hq2; subst htr2
      rw [hrt, hcmt] at heq
      have hcond : (capEnd == input.proof.length &&
          readBuffer sCap (8192 + 32 * 428) 32 == (input.commitment : BitVec (8 * 32))) = true := by
        rw [beq_iff_eq.mpr hlen, hbeq_t _ _ heq, Bool.and_true]
      rw [hcond]
      have hacc := k_step_halt_accept oracle s2 hpc2
      exact ⟨1 + k + 3, by omega, by simpa using (h250.trans hs).halt hacc⟩
  · have h250 := k_step_BNE_taken (oracle := oracle) (s := sCap) (idx := 250) (tgt := 266) (by decide) hdone.pc rfl
      (by rw [hdone.x20, hdone.fixed.x21]; exact k_bv_ne (by omega) (by omega) (by omega)) k_tgt_250
    have hrej := k_step_halt_reject oracle (sCap.setPC (kPcAt 266)) rfl
    have hcond : (capEnd == input.proof.length &&
        readBuffer sCap (8192 + 32 * 428) 32 == (input.commitment : BitVec (8 * 32))) = false := by
      rw [beq_eq_false_iff_ne.mpr hlen, Bool.false_and]
    rw [hcond]
    exact ⟨4, by omega, by simpa using h250.halt hrej⟩

end CommitGolfCandidate
