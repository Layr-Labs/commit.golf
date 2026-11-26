import CommitGolfCandidate.MoonCheckPos

/-! Cap-walk binary-heap geometry, `CapWalkInv`, and single cap-node symbolic execution (`pc[198..224]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! #### Cap-Walk Descending Geometry and Counting Lemmas -/

def pairFrontierCountRev (positions : Positions) (l k : Nat) : Nat :=
  ((Finset.range k).filter fun j =>
    let q := levelSize (l + 1) - 1 - j
    capMark positions l (2 * q) != capMark positions l (2 * q + 1)).card

def pairMarkedNextCountRev (positions : Positions) (l k : Nat) : Nat :=
  ((Finset.range k).filter fun j =>
    capMark positions (l + 1) (levelSize (l + 1) - 1 - j)).card

def capFrontierPrefix (positions : Positions) (step : Nat) : Nat :=
  ∑ d ∈ Finset.range step, levelFrontierCount positions (16 + d)

theorem pairFrontierCountRev_zero (positions : Positions) (l : Nat) :
    pairFrontierCountRev positions l 0 = 0 := by
  simp [pairFrontierCountRev]

theorem pairFrontierCountRev_succ (positions : Positions) (l k : Nat) :
    pairFrontierCountRev positions l (k + 1) =
      pairFrontierCountRev positions l k +
        if (capMark positions l (2 * (levelSize (l + 1) - 1 - k)) !=
            capMark positions l (2 * (levelSize (l + 1) - 1 - k) + 1))
        then 1 else 0 := by
  unfold pairFrontierCountRev
  rw [Finset.range_add_one, Finset.filter_insert]
  have hnot : k ∉ (Finset.range k).filter (fun j =>
      let q := levelSize (l + 1) - 1 - j
      capMark positions l (2 * q) != capMark positions l (2 * q + 1)) := by
    simp
  split <;> simp [Finset.card_insert_of_notMem, hnot]

theorem pairFrontierCountRev_mono (positions : Positions) (l : Nat) {a b : Nat} (hab : a ≤ b) :
    pairFrontierCountRev positions l a ≤ pairFrontierCountRev positions l b :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hab))

theorem pairFrontierCountRev_full (positions : Positions) (l : Nat) (hl : l < 24) :
    pairFrontierCountRev positions l (levelSize (l + 1)) = levelFrontierCount positions l := by
  unfold pairFrontierCountRev levelFrontierCount
  rw [levelSize_succ l hl]
  let m := levelSize l / 2
  have hm : levelSize (l + 1) = m := levelSize_succ l hl
  simp only [hm]
  refine Finset.card_bij (fun j _ => m - 1 - j) ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨by omega, hj.2⟩
  · intro j1 hj1 j2 hj2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at hj1 hj2
    omega
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    refine ⟨m - 1 - q, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [show m - 1 - (m - 1 - q) = q by omega]; exact hq.2⟩

theorem pairMarkedNextCountRev_zero (positions : Positions) (l : Nat) :
    pairMarkedNextCountRev positions l 0 = 0 := by
  simp [pairMarkedNextCountRev]

theorem pairMarkedNextCountRev_succ (positions : Positions) (l k : Nat) :
    pairMarkedNextCountRev positions l (k + 1) =
      pairMarkedNextCountRev positions l k +
        if capMark positions (l + 1) (levelSize (l + 1) - 1 - k) then 1 else 0 := by
  unfold pairMarkedNextCountRev
  rw [Finset.range_add_one, Finset.filter_insert]
  have hnot : k ∉ (Finset.range k).filter (fun j =>
      capMark positions (l + 1) (levelSize (l + 1) - 1 - j)) := by simp
  split <;> simp [Finset.card_insert_of_notMem, hnot]

private theorem levelMarked_le_card (positions : Positions) (l : Nat) (hl1 : 16 ≤ l) (hl2 : l ≤ 24) :
    ((Finset.range (levelSize l)).filter (fun idx => capMark positions l idx)).card ≤ positions.card := by
  obtain ⟨d, rfl⟩ : ∃ d, l = 16 + d := ⟨l - 16, by omega⟩
  induction d with
  | zero =>
    have hsub : (Finset.range (levelSize 16)).filter (fun idx => capMark positions 16 idx) ⊆
        positions.image capLeafOf := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_range, capMark_16, decide_eq_true_eq] at hc
      obtain ⟨i, hi, rfl⟩ := hc.2
      exact Finset.mem_image_of_mem capLeafOf hi
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  | succ d ih =>
    have hlt : 16 + d < 24 := by omega
    have hd : levelSize (16 + d) = 2 * levelSize (16 + (d + 1)) := by
      simpa only [Nat.add_assoc] using levelSize_double (16 + d) hlt
    have hsub : (Finset.range (levelSize (16 + (d + 1)))).filter
        (fun q => capMark positions (16 + (d + 1)) q) ⊆
        ((Finset.range (levelSize (16 + d))).filter (fun idx => capMark positions (16 + d) idx)).image (· / 2) := by
      intro q hq
      simp only [Finset.mem_filter, Finset.mem_range] at hq
      have hsucc : capMark positions (16 + (d + 1)) q =
          (capMark positions (16 + d) (2 * q) || capMark positions (16 + d) (2 * q + 1)) := by
        simpa only [Nat.add_assoc] using capMark_succ positions (16 + d) q (by omega) hq.1
      rw [hsucc, Bool.or_eq_true] at hq
      rcases hq.2 with hL | hR
      · refine Finset.mem_image.mpr ⟨2 * q, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hL⟩
      · refine Finset.mem_image.mpr ⟨2 * q + 1, ?_, by omega⟩
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, hR⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (ih (by omega) (by omega)))

theorem pairMarkedNextCountRev_le_card (positions : Positions) (l : Nat) (hl1 : 16 ≤ l) (hl2 : l < 24) :
    pairMarkedNextCountRev positions l (levelSize (l + 1)) ≤ positions.card := by
  unfold pairMarkedNextCountRev
  have heq : ((Finset.range (levelSize (l + 1))).filter
      (fun j => capMark positions (l + 1) (levelSize (l + 1) - 1 - j))).card =
      ((Finset.range (levelSize (l + 1))).filter (fun q => capMark positions (l + 1) q)).card := by
    let m := levelSize (l + 1)
    refine Finset.card_bij (fun j _ => m - 1 - j) ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨by omega, hj.2⟩
    · intro j1 hj1 j2 hj2 heq
      simp only [Finset.mem_filter, Finset.mem_range] at hj1 hj2; omega
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_range] at hq
      refine ⟨m - 1 - q, ?_, by omega⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by rw [show m - 1 - (m - 1 - q) = q by omega]; exact hq.2⟩
  rw [heq]
  exact levelMarked_le_card positions (l + 1) (by omega) (by omega)

theorem capFrontierPrefix_zero (positions : Positions) :
    capFrontierPrefix positions 0 = 0 := by
  simp [capFrontierPrefix]

theorem capFrontierPrefix_succ (positions : Positions) (step : Nat) :
    capFrontierPrefix positions (step + 1) =
      capFrontierPrefix positions step + levelFrontierCount positions (16 + step) :=
  Finset.sum_range_succ _ step

theorem capFrontierPrefix_8 (positions : Positions) :
    capFrontierPrefix positions 8 = capFrontierCount positions := rfl

theorem capFrontierPrefix_mono (positions : Positions) {a b : Nat} (hab : a ≤ b) :
    capFrontierPrefix positions a ≤ capFrontierPrefix positions b :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

theorem levelSize_cap_le256 (l : Nat) (hl1 : 16 ≤ l) (hl2 : l ≤ 24) :
    levelSize l ≤ 256 := by
  interval_cases l <;> decide

theorem heapIdx_cap_lt512 (l idx : Nat) (hl1 : 16 ≤ l) (hl2 : l ≤ 24) (hidx : idx < levelSize l) :
    heapIdx l idx < 512 := by
  unfold heapIdx
  have := levelSize_cap_le256 l hl1 hl2
  omega

theorem heapIdx_lt_of_gt {l1 l2 idx1 idx2 : Nat} (hl : l1 < l2) (hl2 : l2 ≤ 24) (h2 : idx2 < levelSize l2) :
    heapIdx l2 idx2 < heapIdx l1 idx1 := by
  unfold heapIdx levelSize at *
  have hpow : 2 ^ (24 - l2 + 1) ≤ 2 ^ (24 - l1) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  rw [Nat.pow_succ] at hpow
  omega

theorem cap_level_steps_sum :
    (∑ step ∈ Finset.range 8, 225 * levelSize (16 + step + 1)) + 1 ≤ 60000 := by
  decide

/-! #### Cap-Walk Invariant (`CapWalkInv`) -/

/-- Cap-walk invariant after completing `step` cap levels (`0 ≤ step ≤ 8`, levels `16 .. 16 + step - 1`). -/
structure CapWalkInv (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (sPos : MachineState) (step : Nat) (s : MachineState)
    (tr : List PublicRow) : Prop where
  fixed : CheckFixedRegs s
  x11 : s.getReg .x11 = 64#64
  x13 : s.getReg .x13 = 0#64
  cursor : ProofCursor (submission.initialState .check input) input.proof.length
    (498 * input.positions.card + 29 * capFrontierPrefix input.positions step)
    (10 * input.positions.card + capFrontierPrefix input.positions step) s
  high : HighMemPreserved (submission.initialState .check input) s
  pc : s.pc = if step = 8 then pcWord 225 else pcWord 198
  x23 : s.getReg .x23 = BitVec.ofNat 64 (levelSize (16 + step) - 1)
  mark_cur : step < 8 → ∀ idx < levelSize (16 + step),
    s.getByte (BitVec.ofNat 64 (8192 + heapIdx (16 + step) idx)) =
      if capMark input.positions (16 + step) idx then 1#8 else 0#8
  mark_lo_zero : step < 8 → ∀ h < levelSize (16 + step),
    s.getByte (BitVec.ofNat 64 (8192 + h)) = 0#8
  val16_marked : ∀ c < 256, capMark input.positions 16 c = true →
    readBuffer s (16384 + 32 * (256 + c)) 32 = readBuffer sPos (16384 + 32 * (256 + c)) 32
  levels_done : ∀ d < step,
    let l := 16 + d
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let s0 := submission.initialState .check input
    let pBase := 498 * input.positions.card
    let tBase := 10 * input.positions.card
    ∀ q < levelSize (l + 1), capMark input.positions (l + 1) q = true →
      let k := levelSize (l + 1) - 1 - q
      let dL := readBuffer s (16384 + 32 * heapIdx l (2 * q)) 32
      let dR := readBuffer s (16384 + 32 * heapIdx l (2 * q + 1)) 32
      let pAt := pBase + 29 * (capFrontierPrefix input.positions d + pairFrontierCountRev input.positions l k)
      let tAt := tBase + (capFrontierPrefix input.positions d + pairFrontierCountRev input.positions l k)
      readBuffer s (16384 + 32 * heapIdx (l + 1) q) 32 =
        (if l = 23 then c64 (binaryInput dL dR) else mask238 (c64 (binaryInput dL dR))) ∧
      InCompRows h512 oracle tr (binaryInput dL dR) ∧
      (capMark input.positions l (2 * q) = false → dL = proofDigest238 s0 input.proof.length (10804531232 + pAt) tAt) ∧
      (capMark input.positions l (2 * q + 1) = false → dR = proofDigest238 s0 input.proof.length (10804531232 + pAt) tAt)

/-! #### Single Cap-Node Stepper (`pc[198..224]`) -/

private theorem pc_203_skip : pcWord 203 + signExtend13 80#13 = pcWord 223 := by decide
private theorem pc_208_both : pcWord 208 + signExtend13 28#13 = pcWord 215 := by decide
private theorem pc_210_left : pcWord 210 + signExtend13 8#13 = pcWord 212 := by decide
private theorem pc_219_root : pcWord 219 + signExtend13 16#13 = pcWord 223 := by decide
private theorem pc_224_loop : pcWord 224 + signExtend13 8088#13 = pcWord 198 := by decide
private theorem checkInstr_224 : checkInstr 224 = .base (.BNE .x23 .x0 8088#13) := rfl

private theorem step_bne_224 (oracle : Oracle) (hPrev : Nat) (hh_lt : hPrev < 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcWord 224) (h23 : s.getReg .x23 = BitVec.ofNat 64 hPrev) :
    ∃ s', StepsTo oracle s s' 1 0 [] ∧
      s'.pc = (if hPrev = 0 then pcWord 225 else pcWord 198) ∧
      s'.mem = s.mem ∧
      ∀ r, s'.getReg r = s.getReg r := by
  refine ⟨execInstrBr s (.BNE .x23 .x0 8088#13),
    step_ordinary oracle s 224 (.BNE .x23 .x0 8088#13) (by decide) hpc checkInstr_224
      (by intro h; cases h) (ordinaryStep_BNE_base s .x23 .x0 8088#13),
    ?_, execInstrBr_BNE_mem_base s .x23 .x0 8088#13, execInstrBr_BNE_getReg_base s .x23 .x0 8088#13⟩
  have hne_iff : (s.getReg .x23 != s.getReg .x0) = decide (hPrev ≠ 0) := by
    rw [getReg_x0 s, h23]
    exact bv64_bne_eq hPrev 0 hh_lt (by omega)
  by_cases hz : hPrev = 0
  · rw [if_pos hz]
    have hf : (s.getReg .x23 != s.getReg .x0) = false := by rw [hne_iff, hz]; rfl
    exact (execInstrBr_BNE_pc_false_base s .x23 .x0 8088#13 hf).trans
      ((congrArg (· + (4 : Word)) hpc).trans (pcWord_add_four 224))
  · rw [if_neg hz]
    have ht : (s.getReg .x23 != s.getReg .x0) = true := by rw [hne_iff]; exact decide_eq_true hz
    exact (execInstrBr_BNE_pc_true_base s .x23 .x0 8088#13 ht).trans
      ((congrArg (· + signExtend13 8088#13) hpc).trans pc_224_loop)

/-- One cap-heap node iteration `h = heapIdx (l + 1) q` (`16 ≤ l < 24`, `q < levelSize (l + 1)`, `pc[198..224]`). -/
theorem step_cap_node (h512 : COMPRESSION_INPUT_LENGTH = 512) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (l q pCur tCur : Nat) (hl1 : 16 ≤ l) (hl2 : l < 24) (hq : q < levelSize (l + 1))
    (s : MachineState) (hpc : s.pc = pcWord 198)
    (hfix : CheckFixedRegs s)
    (hx11 : s.getReg .x11 = 64#64) (hx13 : s.getReg .x13 = 0#64)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pCur tCur s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx23 : s.getReg .x23 = BitVec.ofNat 64 (heapIdx (l + 1) q))
    (hmL : s.getByte (BitVec.ofNat 64 (8192 + heapIdx l (2 * q))) =
      if capMark input.positions l (2 * q) then 1#8 else 0#8)
    (hmR : s.getByte (BitVec.ofNat 64 (8192 + heapIdx l (2 * q + 1))) =
      if capMark input.positions l (2 * q + 1) then 1#8 else 0#8)
    (hmParent0 : s.getByte (BitVec.ofNat 64 (8192 + heapIdx (l + 1) q)) = 0#8) :
    let s0 := submission.initialState .check input
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let h := heapIdx (l + 1) q
    let mL := capMark input.positions l (2 * q)
    let mR := capMark input.positions l (2 * q + 1)
    let pNext := pCur + if (mL != mR) then 29 else 0
    let tNext := tCur + if (mL != mR) then 1 else 0
    PhaseOutcome oracle s 225 (if (mL || mR) then 1 else 0)
      ((mL != mR) = true ∧ input.proof.length < pCur + 29 + tailBytes (tCur + 1))
      (fun s' calls tr =>
        calls ≤ (if (mL || mR) then 1 else 0) ∧
        s'.pc = (if h - 1 = 0 then pcWord 225 else pcWord 198) ∧
        CheckFixedRegs s' ∧
        s'.getReg .x11 = 64#64 ∧
        s'.getReg .x13 = 0#64 ∧
        ProofCursor s0 input.proof.length pNext tNext s' ∧
        s'.getReg .x23 = BitVec.ofNat 64 (h - 1) ∧
        s'.getByte (BitVec.ofNat 64 (8192 + h)) = (if (mL || mR) then 1#8 else 0#8) ∧
        ((mL || mR) = true →
          let dL := readBuffer s' (16384 + 32 * heapIdx l (2 * q)) 32
          let dR := readBuffer s' (16384 + 32 * heapIdx l (2 * q + 1)) 32
          readBuffer s' (16384 + 32 * h) 32 =
            (if l = 23 then c64 (binaryInput dL dR) else mask238 (c64 (binaryInput dL dR))) ∧
          InCompRows h512 oracle tr (binaryInput dL dR) ∧
          (mL = false → dL = proofDigest238 s0 input.proof.length (10804531232 + pCur) tCur) ∧
          (mR = false → dR = proofDigest238 s0 input.proof.length (10804531232 + pCur) tCur)) ∧
        (mL = false → mR = false → s'.mem = s.mem) ∧
        (∀ a : Nat, a < 2 ^ 64 →
          a ≠ 8192 + h →
          (mL = mR ∨
            let u := if !mL then heapIdx l (2 * q) else heapIdx l (2 * q + 1)
            a < 16384 + 32 * u ∨ 16384 + 32 * u + 32 ≤ a) →
          (a < 16384 + 32 * h ∨ 16384 + 32 * h + 32 ≤ a) →
          s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a))) := by
  intro s0 c64 h mL mR pNext tNext
  have hh_pos : 1 ≤ h := heapIdx_pos (l + 1) q
  have hh_lt256 : h < 256 := by
    have hls : levelSize (l + 1) ≤ 128 := by
      have : l + 1 ≥ 17 ∧ l + 1 ≤ 24 := by omega
      have h17 : l + 1 = 17 ∨ l + 1 = 18 ∨ l + 1 = 19 ∨ l + 1 = 20 ∨ l + 1 = 21 ∨ l + 1 = 22 ∨ l + 1 = 23 ∨ l + 1 = 24 := by omega
      rcases h17 with he | he | he | he | he | he | he | he <;> rw [he] <;> decide
    unfold h heapIdx; omega
  have h2h : 2 * h = heapIdx l (2 * q) := heapIdx_left_child l q hl2
  have h2h1 : 2 * h + 1 = heapIdx l (2 * q + 1) := heapIdx_right_child l q hl2
  have hh_eq1_iff : h = 1 ↔ l = 23 := by
    constructor
    · intro h1
      by_contra hne
      have hge : 2 ≤ levelSize (l + 1) := by
        have hcases : l = 16 ∨ l = 17 ∨ l = 18 ∨ l = 19 ∨ l = 20 ∨ l = 21 ∨ l = 22 := by omega
        rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      unfold h heapIdx at h1; omega
    · intro h23; subst h23
      have hq0 : q = 0 := by rw [levelSize_24] at hq; omega
      subst hq0; decide
  -- pc[198..203]: load mL, mR, OR -> x14, BEQ x14, x0, pc[223]
  have hst198 := step_ordinary oracle s 198 (.SLLI .x6 .x23 1#6) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.SLLI .x6 .x23 1#6)
  have hpc1 : s1.pc = pcWord 199 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst199 := step_ordinary oracle s1 199 (.ADD .x6 .x18 .x6) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADD .x6 .x18 .x6)
  have hpc2 : s2.pc = pcWord 200 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx6_2 : s2.getReg .x6 = BitVec.ofNat 64 (8192 + 2 * h) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, decide_not, not_false_eq_true, reduceCtorEq,
      hfix.x18, hx23, show (1#6 : BitVec 6).toNat = 1 by decide]
    rw [bv64_shl h 1 (by omega)]
    change BitVec.ofNat 64 8192 + BitVec.ofNat 64 (h * 2) = _
    rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hmem2 : s2.mem = s.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg2 : ∀ r, r ≠ .x6 → s2.getReg r = s.getReg r := fun r h6 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
  have ha200 : s2.getReg .x6 + signExtend12 0#12 = BitVec.ofNat 64 (8192 + 2 * h) := by
    rw [hx6_2, se12_0, BitVec.add_zero]
  have hv200 : memoryArgumentsValid s2 (.LBU .x7 .x6 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha200]
    exact accessValid_ofNat (8192 + 2 * h) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst200 := step_ordinary oracle s2 200 (.LBU .x7 .x6 0#12) (by decide) hpc2 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv200])
  let s3 := execInstrBr s2 (.LBU .x7 .x6 0#12)
  have hpc3 : s3.pc = pcWord 201 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hx6_3 : s3.getReg .x6 = BitVec.ofNat 64 (8192 + 2 * h) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6), hx6_2]
  have ha201 : s3.getReg .x6 + signExtend12 1#12 = BitVec.ofNat 64 (8192 + (2 * h + 1)) := by
    rw [hx6_3, se12_1]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 1 = _; rw [bv64_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hv201 : memoryArgumentsValid s3 (.LBU .x8 .x6 1#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha201]
    exact accessValid_ofNat (8192 + (2 * h + 1)) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst201 := step_ordinary oracle s3 201 (.LBU .x8 .x6 1#12) (by decide) hpc3 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv201])
  let s4 := execInstrBr s3 (.LBU .x8 .x6 1#12)
  have hpc4 : s4.pc = pcWord 202 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hmem4 : s4.mem = s.mem := by simpa [s4, s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
  have hx7_4 : s4.getReg .x7 = if mL then 1#64 else 0#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x7)]
    simp only [s3, execInstrBr, MachineState.getReg_setPC, ha200]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hb : s2.getByte (BitVec.ofNat 64 (8192 + 2 * h)) = if mL then 1#8 else 0#8 := by
      rw [h2h]; simpa only [MachineState.getByte, MachineState.getMem, hmem2] using hmL
    rw [hb, bool_byte_zeroExtend]
  have hx8_4 : s4.getReg .x8 = if mR then 1#64 else 0#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, ha201]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
    have hb : s3.getByte (BitVec.ofNat 64 (8192 + (2 * h + 1))) = if mR then 1#8 else 0#8 := by
      rw [h2h1]; simpa only [MachineState.getByte, MachineState.getMem, hmem3] using hmR
    rw [hb, bool_byte_zeroExtend]
  have hst202 := step_ordinary oracle s4 202 (.OR .x14 .x7 .x8) (by decide) hpc4 rfl (by intro h; cases h) rfl
  let s5 := execInstrBr s4 (.OR .x14 .x7 .x8)
  have hpc5 : s5.pc = pcWord 203 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem5 : s5.mem = s.mem := by simpa [s5, execInstrBr, mem_setPC, mem_setReg] using hmem4
  have hx14_5 : s5.getReg .x14 = if (mL || mR) then 1#64 else 0#64 := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx7_4, hx8_4, bool_word_or]
  have hx7_5 : s5.getReg .x7 = if mL then 1#64 else 0#64 := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x14 ≠ .x7), hx7_4]
  have hx8_5 : s5.getReg .x8 = if mR then 1#64 else 0#64 := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x14 ≠ .x8), hx8_4]
  have hreg5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x14 → s5.getReg r = s.getReg r := fun r h6 h7 h8 h14 => by
    simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h14.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h8.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
    exact hreg2 r h6
  have hst203 := step_ordinary oracle s5 203 (.BEQ .x14 .x0 80#13) (by decide) hpc5 rfl (by intro h; cases h) rfl
  let s6 := execInstrBr s5 (.BEQ .x14 .x0 80#13)
  have hs_198_203 : StepsTo oracle s s6 6 0 [] :=
    ((((hst198.trans hst199).trans hst200).trans (hst201.trans hst202)).trans hst203).eq_of
      rfl (by decide) (by decide) (by simp)
  -- Common loop footer pc[223..224] (2 steps)
  have hloop_tail : ∀ (s223 : MachineState) (kPre qPre : Nat) (trPre : List PublicRow),
      kPre ≤ 223 → qPre ≤ (if (mL || mR) then 1 else 0) →
      StepsTo oracle s s223 kPre qPre trPre →
      s223.pc = pcWord 223 →
      CheckFixedRegs s223 →
      s223.getReg .x11 = 64#64 → s223.getReg .x13 = 0#64 →
      ProofCursor s0 input.proof.length pNext tNext s223 →
      s223.getReg .x23 = BitVec.ofNat 64 h →
      s223.getByte (BitVec.ofNat 64 (8192 + h)) = (if (mL || mR) then 1#8 else 0#8) →
      ((mL || mR) = true →
        let dL := readBuffer s223 (16384 + 32 * heapIdx l (2 * q)) 32
        let dR := readBuffer s223 (16384 + 32 * heapIdx l (2 * q + 1)) 32
        readBuffer s223 (16384 + 32 * h) 32 =
          (if l = 23 then c64 (binaryInput dL dR) else mask238 (c64 (binaryInput dL dR))) ∧
        InCompRows h512 oracle trPre (binaryInput dL dR) ∧
        (mL = false → dL = proofDigest238 s0 input.proof.length (10804531232 + pCur) tCur) ∧
        (mR = false → dR = proofDigest238 s0 input.proof.length (10804531232 + pCur) tCur)) →
      (mL = false → mR = false → s223.mem = s.mem) →
      (∀ a : Nat, a < 2 ^ 64 →
        a ≠ 8192 + h →
        (mL = mR ∨
          let u := if !mL then heapIdx l (2 * q) else heapIdx l (2 * q + 1)
          a < 16384 + 32 * u ∨ 16384 + 32 * u + 32 ≤ a) →
        (a < 16384 + 32 * h ∨ 16384 + 32 * h + 32 ≤ a) →
        s223.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) →
      PhaseOutcome oracle s 225 (if (mL || mR) then 1 else 0)
        ((mL != mR) = true ∧ input.proof.length < pCur + 29 + tailBytes (tCur + 1))
        (fun s' calls tr =>
          calls ≤ (if (mL || mR) then 1 else 0) ∧
          s'.pc = (if h - 1 = 0 then pcWord 225 else pcWord 198) ∧
          CheckFixedRegs s' ∧ s'.getReg .x11 = 64#64 ∧ s'.getReg .x13 = 0#64 ∧
          ProofCursor s0 input.proof.length pNext tNext s' ∧
          s'.getReg .x23 = BitVec.ofNat 64 (h - 1) ∧
          s'.getByte (BitVec.ofNat 64 (8192 + h)) = (if (mL || mR) then 1#8 else 0#8) ∧
          ((mL || mR) = true →
            let dL := readBuffer s' (16384 + 32 * heapIdx l (2 * q)) 32
            let dR := readBuffer s' (16384 + 32 * heapIdx l (2 * q + 1)) 32
            readBuffer s' (16384 + 32 * h) 32 =
              (if l = 23 then c64 (binaryInput dL dR) else mask238 (c64 (binaryInput dL dR))) ∧
            InCompRows h512 oracle tr (binaryInput dL dR) ∧
            (mL = false → dL = proofDigest238 s0 input.proof.length (10804531232 + pCur) tCur) ∧
            (mR = false → dR = proofDigest238 s0 input.proof.length (10804531232 + pCur) tCur)) ∧
          (mL = false → mR = false → s'.mem = s.mem) ∧
          (∀ a : Nat, a < 2 ^ 64 →
            a ≠ 8192 + h →
            (mL = mR ∨
              let u := if !mL then heapIdx l (2 * q) else heapIdx l (2 * q + 1)
              a < 16384 + 32 * u ∨ 16384 + 32 * u + 32 ≤ a) →
            (a < 16384 + 32 * h ∨ 16384 + 32 * h + 32 ≤ a) →
            s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a))) := by
    intro s223 kPre qPre trPre hkPre hqPre hstPre hpc223 hfix223 h11_223 h13_223 hcur223 h23_223
      hmk223 hval223 hmeq223 hout223
    have hst223 := step_ordinary oracle s223 223 (.ADDI .x23 .x23 4095#12) (by decide) hpc223 rfl (by intro h; cases h) rfl
    let s224 := execInstrBr s223 (.ADDI .x23 .x23 4095#12)
    have hpc224 : s224.pc = pcWord 224 := by simp only [s224, execInstrBr, MachineState.setPC, hpc223, pcWord_add_four]
    have hx23_224 : s224.getReg .x23 = BitVec.ofNat 64 (h - 1) := by
      simp only [s224, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), h23_223, show h = (h - 1) + 1 by omega]
      exact bv64_add_neg1 (h - 1)
    obtain ⟨sFin, hst224, hpcFin, hmem224, hreg224⟩ :=
      step_bne_224 oracle (h - 1) (by omega) s224 hpc224 hx23_224
    have hmemFin : sFin.mem = s223.mem := hmem224.trans (by simp [s224, execInstrBr, mem_setPC, mem_setReg])
    have hregFin : ∀ r, r ≠ .x23 → sFin.getReg r = s223.getReg r := fun r h23r => by
      rw [hreg224 r]; simp only [s224, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h23r.symm
    have hrb_eq : ∀ addr n, readBuffer sFin addr n = readBuffer s223 addr n := fun addr n =>
      readBuffer_congr2 _ _ _ _ _ (fun _ _ => by simp [MachineState.getByte, MachineState.getMem, hmemFin])
    refine .continued sFin (kPre + 2) qPre trPre (by omega) hqPre
      ((hstPre.trans (hst223.trans hst224)).eq_of rfl (by omega) (by omega) (by simp))
      ⟨hqPre, hpcFin,
       hfix223.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)),
       (hregFin .x11 (by decide)).trans h11_223, (hregFin .x13 (by decide)).trans h13_223,
       hcur223.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)),
       (hreg224 .x23).trans hx23_224,
       by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hmk223,
       fun hm => by simpa only [hrb_eq] using hval223 hm,
       fun h1 h2 => hmemFin.trans (hmeq223 h1 h2),
       fun a ha h1 h2 h3 => by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hout223 a ha h1 h2 h3⟩
  -- Case split on (mL || mR)
  by_cases hor : (mL || mR) = false
  · -- Branch A: neither child marked -> jump straight to pc[223]
    have hmLf : mL = false := (Bool.or_eq_false_iff.mp hor).1
    have hmRf : mR = false := (Bool.or_eq_false_iff.mp hor).2
    have hpn_eq : pNext = pCur := by simp [pNext, hmLf, hmRf]
    have htn_eq : tNext = tCur := by simp [tNext, hmLf, hmRf]
    have hx14z : s5.getReg .x14 = 0#64 := by simp only [hx14_5, hor, Bool.false_eq_true, ite_false]
    have hpc6 : s6.pc = pcWord 223 := by
      simp only [s6, execInstrBr, hx14z, getReg_x0, beq_self_eq_true, ite_true, MachineState.setPC, hpc5]
      exact pc_203_skip
    have hmem6 : s6.mem = s.mem := by simpa [s6, execInstrBr, hx14z, getReg_x0, MachineState.setPC] using hmem5
    have hreg6 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x14 → s6.getReg r = s.getReg r := fun r h6 h7 h8 h14 => by
      have : s6.getReg r = s5.getReg r := by simp [s6, execInstrBr, hx14z, getReg_x0, MachineState.getReg_setPC]
      exact this.trans (hreg5 r h6 h7 h8 h14)
    refine hloop_tail s6 6 0 [] (by decide) (by simp [hor]) hs_198_203 hpc6
      (hfix.of_agree (fun r hr => hreg6 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
      ((hreg6 .x11 (by decide) (by decide) (by decide) (by decide)).trans hx11)
      ((hreg6 .x13 (by decide) (by decide) (by decide) (by decide)).trans hx13)
      (by rw [hpn_eq, htn_eq]
          exact hcur.of_agree (fun r hr => hreg6 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
            (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      ((hreg6 .x23 (by decide) (by decide) (by decide) (by decide)).trans hx23)
      (by simp only [hor, Bool.false_eq_true, ite_false, MachineState.getByte, MachineState.getMem, hmem6]; exact hmParent0)
      (fun h => by rw [hor] at h; cases h)
      (fun _ _ => hmem6)
      (fun a _ _ _ _ => by simp [MachineState.getByte, MachineState.getMem, hmem6])
  · -- Branch B: at least one child marked -> pc[204..222] -> pc[223]
    have horT : (mL || mR) = true := Bool.eq_true_of_not_eq_false hor
    have hx14o : s5.getReg .x14 = 1#64 := by simp only [hx14_5, horT, ite_true]
    have hpc6 : s6.pc = pcWord 204 := by
      simp only [s6, execInstrBr, hx14o, getReg_x0, show (1#64 == 0#64) = false by decide,
        Bool.false_eq_true, ite_false, MachineState.setPC, hpc5, pcWord_add_four]
    have hmem6 : s6.mem = s.mem := by
      simpa [s6, execInstrBr, hx14o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.setPC] using hmem5
    have hreg6_5 : ∀ r, s6.getReg r = s5.getReg r := fun r => by
      simp [s6, execInstrBr, hx14o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
    -- pc[204..208]: mark[h] = 1, x10 = 16384 + 64 * h, BEQ x7, x8, pc[215]
    have hst204 := step_ordinary oracle s6 204 (.ADD .x6 .x18 .x23) (by decide) hpc6 rfl (by intro h; cases h) rfl
    let s7 := execInstrBr s6 (.ADD .x6 .x18 .x23)
    have hpc7 : s7.pc = pcWord 205 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
    have hx6_7 : s7.getReg .x6 = BitVec.ofNat 64 (8192 + h) := by
      simp only [s7, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), hreg6_5, hreg5 .x18 (by decide) (by decide) (by decide) (by decide),
        hfix.x18, hreg6_5, hreg5 .x23 (by decide) (by decide) (by decide) (by decide), hx23]
      change BitVec.ofNat 64 8192 + BitVec.ofNat 64 h = _; exact bv64_add 8192 h
    have ha205 : s7.getReg .x6 + signExtend12 0#12 = BitVec.ofNat 64 (8192 + h) := by
      rw [hx6_7, se12_0, BitVec.add_zero]
    have hv205 : memoryArgumentsValid s7 (.SB .x6 .x14 0#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha205]
      exact accessValid_ofNat (8192 + h) 1 (by unfold MEMORY_BYTES; omega) (by omega)
    have hst205 := step_ordinary oracle s7 205 (.SB .x6 .x14 0#12) (by decide) hpc7 rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv205])
    let s8 := execInstrBr s7 (.SB .x6 .x14 0#12)
    have hpc8 : s8.pc = pcWord 206 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
    have hmem7 : s7.mem = s.mem := by simpa [s7, execInstrBr, mem_setPC, mem_setReg] using hmem6
    have hx14_7 : s7.getReg .x14 = 1#64 := by
      simp only [s7, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x14), hreg6_5, hx14o]
    have hbyte8 : ∀ q', s8.getByte q' = (s.setByte (BitVec.ofNat 64 (8192 + h)) 1#8).getByte q' := fun q' => by
      simp only [s8, execInstrBr, ha205, hx14_7, show (1#64 : Word).truncate 8 = 1#8 by decide,
        MachineState.getByte, MachineState.setByte, MachineState.getMem, MachineState.setMem, mem_setPC, hmem7]
    have hout8 : MemEqOutside s s8 (8192 + h) (8192 + h + 1) := by
      intro a ha hout; rw [hbyte8]; exact MemEqOutside_setByte s (8192 + h) 1#8 (by omega) a ha hout
    have hmk8 : s8.getByte (BitVec.ofNat 64 (8192 + h)) = 1#8 := by rw [hbyte8, set_byte_read]; simp
    have hreg8_5 : ∀ r, r ≠ .x6 → s8.getReg r = s5.getReg r := fun r h6 => by
      have : s8.getReg r = s7.getReg r := by
        simp [s8, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      rw [this]; simp only [s7, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm, hreg6_5]
    have hst206 := step_ordinary oracle s8 206 (.SLLI .x6 .x23 6#6) (by decide) hpc8 rfl (by intro h; cases h) rfl
    let s9 := execInstrBr s8 (.SLLI .x6 .x23 6#6)
    have hpc9 : s9.pc = pcWord 207 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
    have hst207 := step_ordinary oracle s9 207 (.ADD .x10 .x19 .x6) (by decide) hpc9 rfl (by intro h; cases h) rfl
    let s10 := execInstrBr s9 (.ADD .x10 .x19 .x6)
    have hpc10 : s10.pc = pcWord 208 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9, pcWord_add_four]
    have hmem10 : s10.mem = s8.mem := by simp [s10, s9, execInstrBr, mem_setPC, mem_setReg]
    have hx10_10 : s10.getReg .x10 = BitVec.ofNat 64 (16384 + 64 * h) := by
      simp only [s10, s9, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
        MachineState.getReg_setReg_ne, ne_eq, decide_not, not_false_eq_true, reduceCtorEq,
        hreg8_5 .x19 (by decide), hreg5 .x19 (by decide) (by decide) (by decide) (by decide), hfix.x19,
        hreg8_5 .x23 (by decide), hreg5 .x23 (by decide) (by decide) (by decide) (by decide), hx23,
        show (6#6 : BitVec 6).toNat = 6 by decide]
      rw [bv64_shl h 6 (by omega)]
      change BitVec.ofNat 64 16384 + BitVec.ofNat 64 (h * 64) = _
      rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
    have hreg10_5 : ∀ r, r ≠ .x6 → r ≠ .x10 → s10.getReg r = s5.getReg r := fun r h6 h10 => by
      simp only [s10, s9, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h10.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h6.symm, hreg8_5 r h6]
    have hst208 := step_ordinary oracle s10 208 (.BEQ .x7 .x8 28#13) (by decide) hpc10 rfl (by intro h; cases h) rfl
    let s11 := execInstrBr s10 (.BEQ .x7 .x8 28#13)
    have hpre11 : StepsTo oracle s s11 11 0 [] :=
      (hs_198_203.trans (((hst204.trans hst205).trans (hst206.trans hst207)).trans hst208)).eq_of
        rfl (by decide) (by decide) (by simp)
    -- Common compress + mask238 (if h ≠ 1) from pc[215..222] -> pc[223] (≤ 8 steps, 1 call)
    have hcomp215 : ∀ (s215 : MachineState) (kMid : Nat),
        kMid ≤ 215 →
        StepsTo oracle s s215 kMid 0 [] →
        s215.pc = pcWord 215 →
        CheckFixedRegs s215 →
        s215.getReg .x11 = 64#64 → s215.getReg .x13 = 0#64 →
        ProofCursor s0 input.proof.length pNext tNext s215 →
        s215.getReg .x10 = BitVec.ofNat 64 (16384 + 64 * h) →
        s215.getReg .x23 = BitVec.ofNat 64 h →
        s215.getByte (BitVec.ofNat 64 (8192 + h)) = 1#8 →
        (mL = false → readBuffer s215 (16384 + 32 * heapIdx l (2 * q)) 32 =
          proofDigest238 s0 input.proof.length (10804531232 + pCur) tCur) →
        (mR = false → readBuffer s215 (16384 + 32 * heapIdx l (2 * q + 1)) 32 =
          proofDigest238 s0 input.proof.length (10804531232 + pCur) tCur) →
        (∀ a : Nat, a < 2 ^ 64 →
          a ≠ 8192 + h →
          (mL = mR ∨
            let u := if !mL then heapIdx l (2 * q) else heapIdx l (2 * q + 1)
            a < 16384 + 32 * u ∨ 16384 + 32 * u + 32 ≤ a) →
          s215.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) →
        PhaseOutcome oracle s 225 (if (mL || mR) then 1 else 0)
          ((mL != mR) = true ∧ input.proof.length < pCur + 29 + tailBytes (tCur + 1))
          (fun s' calls tr =>
            calls ≤ (if (mL || mR) then 1 else 0) ∧
            s'.pc = (if h - 1 = 0 then pcWord 225 else pcWord 198) ∧
            CheckFixedRegs s' ∧ s'.getReg .x11 = 64#64 ∧ s'.getReg .x13 = 0#64 ∧
            ProofCursor s0 input.proof.length pNext tNext s' ∧
            s'.getReg .x23 = BitVec.ofNat 64 (h - 1) ∧
            s'.getByte (BitVec.ofNat 64 (8192 + h)) = (if (mL || mR) then 1#8 else 0#8) ∧
            ((mL || mR) = true →
              let dL := readBuffer s' (16384 + 32 * heapIdx l (2 * q)) 32
              let dR := readBuffer s' (16384 + 32 * heapIdx l (2 * q + 1)) 32
              readBuffer s' (16384 + 32 * h) 32 =
                (if l = 23 then c64 (binaryInput dL dR) else mask238 (c64 (binaryInput dL dR))) ∧
              InCompRows h512 oracle tr (binaryInput dL dR) ∧
              (mL = false → dL = proofDigest238 s0 input.proof.length (10804531232 + pCur) tCur) ∧
              (mR = false → dR = proofDigest238 s0 input.proof.length (10804531232 + pCur) tCur)) ∧
            (mL = false → mR = false → s'.mem = s.mem) ∧
            (∀ a : Nat, a < 2 ^ 64 →
              a ≠ 8192 + h →
              (mL = mR ∨
                let u := if !mL then heapIdx l (2 * q) else heapIdx l (2 * q + 1)
                a < 16384 + 32 * u ∨ 16384 + 32 * u + 32 ≤ a) →
              (a < 16384 + 32 * h ∨ 16384 + 32 * h + 32 ≤ a) →
              s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a))) := by
      intro s215 kMid hkMid hmid hpc215 hfix215 h11_215 h13_215 hcur215 hx10_215 hx23_215 hmk215 hfrL hfrR hout215
      have hst215 := step_ordinary oracle s215 215 (.SLLI .x6 .x23 5#6) (by decide) hpc215 rfl (by intro h; cases h) rfl
      let s216 := execInstrBr s215 (.SLLI .x6 .x23 5#6)
      have hpc216 : s216.pc = pcWord 216 := by simp only [s216, execInstrBr, MachineState.setPC, hpc215, pcWord_add_four]
      have hst216 := step_ordinary oracle s216 216 (.ADD .x12 .x19 .x6) (by decide) hpc216 rfl (by intro h; cases h) rfl
      let s217 := execInstrBr s216 (.ADD .x12 .x19 .x6)
      have hpc217 : s217.pc = pcWord 217 := by simp only [s217, execInstrBr, MachineState.setPC, hpc216, pcWord_add_four]
      have hmem217 : s217.mem = s215.mem := by simp [s217, s216, execInstrBr, mem_setPC, mem_setReg]
      have hreg217 : ∀ r, r ≠ .x6 → r ≠ .x12 → s217.getReg r = s215.getReg r := fun r h6 h12 => by
        simp only [s217, s216, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
      have hx12_217 : s217.getReg .x12 = BitVec.ofNat 64 (16384 + 32 * h) := by
        simp only [s217, s216, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
          MachineState.getReg_setReg_ne, ne_eq, decide_not, not_false_eq_true, reduceCtorEq,
          hfix215.x19, hx23_215, show (5#6 : BitVec 6).toNat = 5 by decide]
        rw [bv64_shl h 5 (by omega)]
        change BitVec.ofNat 64 16384 + BitVec.ofNat 64 (h * 32) = _
        rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
      let dL := readBuffer s215 (16384 + 32 * heapIdx l (2 * q)) 32
      let dR := readBuffer s215 (16384 + 32 * heapIdx l (2 * q + 1)) 32
      have hinp217 : readBuffer s217 (16384 + 64 * h) 64 = binaryInput dL dR := by
        rw [(MemEqOutside.of_mem_eq hmem217 0 0).readBuffer_eq (by omega) (by omega),
          readBuffer_binary s215 (16384 + 64 * h)]
        rw [show 16384 + 64 * h = 16384 + 32 * heapIdx l (2 * q) by omega,
          show 16384 + 32 * heapIdx l (2 * q) + 32 = 16384 + 32 * heapIdx l (2 * q + 1) by omega]
      have hec := step_ecall_compress h512 oracle s217 217 (16384 + 64 * h) (16384 + 32 * h) (by decide) hpc217 rfl
        ((hreg217 .x5 (by decide) (by decide)).trans hfix215.x5)
        ((hreg217 .x11 (by decide) (by decide)).trans h11_215)
        ((hreg217 .x13 (by decide) (by decide)).trans h13_215)
        ((hreg217 .x10 (by decide) (by decide)).trans hx10_215) hx12_217 (by omega) (by omega)
        (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
      rw [hinp217] at hec
      let s218 := writeBits s217 (BitVec.ofNat 64 (16384 + 32 * h)) (c64 (binaryInput dL dR))
      have hpc218 : s218.pc = pcWord 218 := by simp only [s218, writeBits, MachineState.setPC, hpc217, pcWord_add_four]
      have hreg218 : ∀ r, r ≠ .x6 → r ≠ .x12 → s218.getReg r = s215.getReg r := fun r h6 h12 =>
        (writeBits_register s217 _ _ r).trans (hreg217 r h6 h12)
      have hx12_218 : s218.getReg .x12 = BitVec.ofNat 64 (16384 + 32 * h) :=
        (writeBits_register s217 _ _ .x12).trans hx12_217
      have hout_215_218 : MemEqOutside s215 s218 (16384 + 32 * h) (16384 + 32 * h + 32) :=
        (MemEqOutside.of_mem_eq hmem217 _ _).trans (MemEqOutside_writeBits_digest s217 _ _ (by omega))
      -- pc[218..219]: ADDI x6, x0, 1; BEQ x23, x6, pc[223]
      have hst218 := step_ordinary oracle s218 218 (.ADDI .x6 .x0 1#12) (by decide) hpc218 rfl (by intro h; cases h) rfl
      let s219 := execInstrBr s218 (.ADDI .x6 .x0 1#12)
      have hpc219 : s219.pc = pcWord 219 := by simp only [s219, execInstrBr, MachineState.setPC, hpc218, pcWord_add_four]
      have hx6_219 : s219.getReg .x6 = 1#64 := by
        simp only [s219, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
          ne_eq, decide_not, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
      have hx23_219 : s219.getReg .x23 = BitVec.ofNat 64 h := by
        simp only [s219, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x23),
          hreg218 .x23 (by decide) (by decide), hx23_215]
      have hst219 := step_ordinary oracle s219 219 (.BEQ .x23 .x6 16#13) (by decide) hpc219 rfl (by intro h; cases h) rfl
      let s220 := execInstrBr s219 (.BEQ .x23 .x6 16#13)
      have heq1 : (s219.getReg .x23 == s219.getReg .x6) = decide (l = 23) := by
        rw [hx23_219, hx6_219]
        change (BitVec.ofNat 64 h == BitVec.ofNat 64 1) = _
        rw [bv64_beq_eq h 1 (by omega) (by omega), decide_eq_decide]
        exact hh_eq1_iff
      have hmem220 : s220.mem = s218.mem := by
        simp only [s220, execInstrBr]; split <;> simp [s219, execInstrBr, mem_setPC, mem_setReg]
      have hreg220 : ∀ r, r ≠ .x6 → r ≠ .x12 → s220.getReg r = s215.getReg r := fun r h6 h12 => by
        have : s220.getReg r = s219.getReg r := by simp only [s220, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
        rw [this]; simp only [s219, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]; exact hreg218 r h6 h12
      have hpre220 := (hmid.trans ((hst215.trans hst216).trans hec)).trans (hst218.trans hst219)
      -- Complete to pc[223] in ≤ 3 more steps
      have hto223 : ∃ s223 kM, kM ≤ 3 ∧ StepsTo oracle s220 s223 kM 0 [] ∧
          s223.pc = pcWord 223 ∧
          (∀ r, r ≠ .x6 → r ≠ .x12 → s223.getReg r = s215.getReg r) ∧
          MemEqOutside s218 s223 (16384 + 32 * h) (16384 + 32 * h + 32) ∧
          readBuffer s223 (16384 + 32 * h) 32 =
            if l = 23 then c64 (binaryInput dL dR) else mask238 (c64 (binaryInput dL dR)) := by
        by_cases hl23 : l = 23
        · have hpc220 : s220.pc = pcWord 223 := by
            simp only [s220, execInstrBr, heq1, hl23, decide_true, ite_true, MachineState.setPC, hpc219]
            exact pc_219_root
          refine ⟨s220, 0, by decide, StepsTo.refl oracle s220, hpc220, hreg220,
            MemEqOutside.of_mem_eq hmem220 _ _, ?_⟩
          rw [if_pos hl23, (MemEqOutside.of_mem_eq hmem220 0 0).readBuffer_eq (by omega) (by omega),
            writeBits_readBuffer_digest]
        · have hpc220 : s220.pc = pcWord 220 := by
            simp only [s220, execInstrBr, heq1, hl23, decide_false, Bool.false_eq_true, ite_false,
              MachineState.setPC, hpc219, pcWord_add_four]
          have hx12_220 : s220.getReg .x12 = BitVec.ofNat 64 (16384 + 32 * h) := by
            have : s220.getReg .x12 = s219.getReg .x12 := by
              simp only [s220, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
            rw [this]; simp only [s219, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x12), hx12_218]
          obtain ⟨s223, hs223, hpc223, hreg223, hdig223, hout223⟩ :=
            step_mask238 oracle 220 .x12 s220 (16384 + 32 * h) (by decide) (by decide) rfl rfl rfl hpc220
              hx12_220 ((hreg220 .x9 (by decide) (by decide)).trans hfix215.x9)
              (by omega) (by unfold MEMORY_BYTES; omega)
          refine ⟨s223, 3, by decide, hs223, hpc223, fun r h6 h12 => (hreg223 r h6).trans (hreg220 r h6 h12),
            (MemEqOutside.of_mem_eq hmem220 _ _).trans hout223, ?_⟩
          rw [if_neg hl23, hdig223, (MemEqOutside.of_mem_eq hmem220 0 0).readBuffer_eq (by omega) (by omega),
            writeBits_readBuffer_digest]
      obtain ⟨s223, kM, hkM, hsM, hpc223, hreg223, hout223, hdig223⟩ := hto223
      have hout_215_223 : MemEqOutside s215 s223 (16384 + 32 * h) (16384 + 32 * h + 32) :=
        hout_215_218.trans hout223
      have hdL_eq : readBuffer s223 (16384 + 32 * heapIdx l (2 * q)) 32 = dL :=
        hout_215_223.readBuffer_eq (by omega) (by omega)
      have hdR_eq : readBuffer s223 (16384 + 32 * heapIdx l (2 * q + 1)) 32 = dR :=
        hout_215_223.readBuffer_eq (by omega) (by omega)
      refine hloop_tail s223 (kMid + 5 + kM) 1
        [PublicRow.compression ((binaryInput dL dR).cast h512.symm) (c64 (binaryInput dL dR))]
        (by omega) (by simp [horT])
        ((hpre220.trans hsM).eq_of rfl (by omega) (by decide) (by simp [c64]))
        hpc223
        (hfix215.of_agree (fun r hr => hreg223 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        ((hreg223 .x11 (by decide) (by decide)).trans h11_215)
        ((hreg223 .x13 (by decide) (by decide)).trans h13_215)
        (hcur215.of_agree (fun r hr => hreg223 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
        ((hreg223 .x23 (by decide) (by decide)).trans hx23_215)
        (by rw [horT, if_pos rfl, hout_215_223 (8192 + h) (by omega) (by omega), hmk215])
        (fun _ => by
          rw [hdL_eq, hdR_eq]
          exact ⟨hdig223, InCompRows.singleton h512 oracle (binaryInput dL dR), hfrL, hfrR⟩)
        (fun h1 h2 => by simp [h1, h2] at horT)
        (fun a ha hne hfr hdst => (hout_215_223 a ha hdst).trans (hout215 a ha hne hfr))
    -- Dispatch on mL = mR (both true) vs mL ≠ mR (frontier read29_tail6)
    by_cases hsame : mL = mR
    · have hmLt : mL = true := by
        cases h1 : mL with
        | true => rfl
        | false =>
          cases h2 : mR with
          | false => rw [h1, h2] at horT; cases horT
          | true => rw [h1, h2] at hsame; exact hsame
      have hmRt : mR = true := by rw [← hsame, hmLt]
      have hpn_eq : pNext = pCur := by simp [pNext, hmLt, hmRt]
      have htn_eq : tNext = tCur := by simp [tNext, hmLt, hmRt]
      have hx7_10 : s10.getReg .x7 = 1#64 := by rw [hreg10_5 .x7 (by decide) (by decide), hx7_5, hmLt]; rfl
      have hx8_10 : s10.getReg .x8 = 1#64 := by rw [hreg10_5 .x8 (by decide) (by decide), hx8_5, hmRt]; rfl
      have hpc11 : s11.pc = pcWord 215 := by
        simp only [s11, execInstrBr, hx7_10, hx8_10, beq_self_eq_true, ite_true, MachineState.setPC, hpc10]
        exact pc_208_both
      have hmem11 : s11.mem = s8.mem := by
        simpa [s11, execInstrBr, hx7_10, hx8_10, MachineState.setPC] using hmem10
      have hreg11_10 : ∀ r, s11.getReg r = s10.getReg r := fun r => by
        simp [s11, execInstrBr, hx7_10, hx8_10, MachineState.getReg_setPC]
      have hreg11_s : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x14 → s11.getReg r = s.getReg r :=
        fun r h6 h7 h8 h10 h14 => (hreg11_10 r).trans ((hreg10_5 r h6 h10).trans (hreg5 r h6 h7 h8 h14))
      refine hcomp215 s11 11 (by decide) hpre11 hpc11
        (hfix.of_agree (fun r hr => hreg11_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        ((hreg11_s .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11)
        ((hreg11_s .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13)
        (by rw [hpn_eq, htn_eq]
            exact hcur.of_agree (fun r hr => hreg11_s r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
              (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
        ((hreg11_10 .x10).trans hx10_10)
        ((hreg11_s .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23)
        (by simp [MachineState.getByte, MachineState.getMem, hmem11]; exact hmk8)
        (fun h => by rw [hmLt] at h; cases h)
        (fun h => by rw [hmRt] at h; cases h)
        (fun a ha hne _ => by simp only [MachineState.getByte, MachineState.getMem, hmem11]; exact hout8 a ha (by omega))
    · -- Frontier case: mL ≠ mR -> pc[209..214] -> pc[215]
      have hbne : (mL != mR) = true := bne_iff_ne.mpr hsame
      have hpn_eq : pNext = pCur + 29 := by simp [pNext, hbne]
      have htn_eq : tNext = tCur + 1 := by simp [tNext, hbne]
      have hx7_10 : s10.getReg .x7 = if mL then 1#64 else 0#64 :=
        (hreg10_5 .x7 (by decide) (by decide)).trans hx7_5
      have hx8_10 : s10.getReg .x8 = if mR then 1#64 else 0#64 :=
        (hreg10_5 .x8 (by decide) (by decide)).trans hx8_5
      have hbeq_f : (s10.getReg .x7 == s10.getReg .x8) = false := by
        rw [hx7_10, hx8_10]
        cases h1 : mL <;> cases h2 : mR <;> rw [h1, h2] at hsame <;>
          first | exact (hsame rfl).elim | decide
      have hpc11 : s11.pc = pcWord 209 := by
        simp only [s11, execInstrBr, hbeq_f, Bool.false_eq_true, ite_false, MachineState.setPC, hpc10, pcWord_add_four]
      have hmem11 : s11.mem = s8.mem := by
        simpa [s11, execInstrBr, hbeq_f, MachineState.setPC] using hmem10
      have hreg11_10 : ∀ r, s11.getReg r = s10.getReg r := fun r => by
        simp [s11, execInstrBr, hbeq_f, MachineState.getReg_setPC]
      -- pc[209..212]: set x12 = 16384 + 32 * u, x15 = 16384 + 64 * h (≤ 4 steps)
      let u : Nat := if !mL then heapIdx l (2 * q) else heapIdx l (2 * q + 1)
      have hu_addr : 16384 + 32 * u = if !mL then 16384 + 64 * h else 16384 + 64 * h + 32 := by
        dsimp only [u]; cases mL <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] <;> omega
      have hst209 := step_ordinary oracle s11 209 (.ADDI .x12 .x10 0#12) (by decide) hpc11 rfl (by intro h; cases h) rfl
      let s12 := execInstrBr s11 (.ADDI .x12 .x10 0#12)
      have hpc12 : s12.pc = pcWord 210 := by simp only [s12, execInstrBr, MachineState.setPC, hpc11, pcWord_add_four]
      have hx12_12 : s12.getReg .x12 = BitVec.ofNat 64 (16384 + 64 * h) := by
        simp only [s12, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hreg11_10, hx10_10, se12_0, BitVec.add_zero]
      have hx7_12 : s12.getReg .x7 = if mL then 1#64 else 0#64 := by
        simp only [s12, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), hreg11_10, hx7_10]
      have hst210 := step_ordinary oracle s12 210 (.BEQ .x7 .x0 8#13) (by decide) hpc12 rfl (by intro h; cases h) rfl
      let s13 := execInstrBr s12 (.BEQ .x7 .x0 8#13)
      have hmem12 : s12.mem = s8.mem := by simpa [s12, execInstrBr, mem_setPC, mem_setReg] using hmem11
      have hto212 : ∃ s212 kD, kD ≤ 3 ∧ StepsTo oracle s11 s212 kD 0 [] ∧
          s212.pc = pcWord 212 ∧ s212.mem = s8.mem ∧
          s212.getReg .x12 = BitVec.ofNat 64 (16384 + 32 * u) ∧
          s212.getReg .x10 = BitVec.ofNat 64 (16384 + 64 * h) ∧
          (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x12 → r ≠ .x14 → s212.getReg r = s.getReg r) := by
        cases hmL_val : mL with
        | false =>
          have hx7z : s12.getReg .x7 = 0#64 := by rw [hx7_12, hmL_val]; rfl
          have hpc13 : s13.pc = pcWord 212 := by
            simp only [s13, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, MachineState.setPC, hpc12]
            exact pc_210_left
          have hmem13 : s13.mem = s8.mem := by simpa [s13, execInstrBr, hx7z, getReg_x0, MachineState.setPC] using hmem12
          have hreg13 : ∀ r, s13.getReg r = s12.getReg r := fun r => by
            simp [s13, execInstrBr, hx7z, getReg_x0, MachineState.getReg_setPC]
          refine ⟨s13, 2, by decide, (hst209.trans hst210).eq_of rfl (by decide) (by decide) (by simp),
            hpc13, hmem13, by rw [hu_addr, hmL_val]; exact (hreg13 .x12).trans hx12_12,
            (hreg13 .x10).trans (by
              simp only [s12, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hreg11_10, hx10_10]),
            fun r h6 h7 h8 h10 h12 h14 => by
              rw [hreg13]; simp only [s12, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg11_10, hreg10_5 r h6 h10, hreg5 r h6 h7 h8 h14]⟩
        | true =>
          have hx7o : s12.getReg .x7 = 1#64 := by rw [hx7_12, hmL_val]; rfl
          have hpc13 : s13.pc = pcWord 211 := by
            simp only [s13, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
              Bool.false_eq_true, ite_false, MachineState.setPC, hpc12, pcWord_add_four]
          have hmem13 : s13.mem = s8.mem := by
            simpa [s13, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.setPC] using hmem12
          have hreg13 : ∀ r, s13.getReg r = s12.getReg r := fun r => by
            simp [s13, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
          have hst211 := step_ordinary oracle s13 211 (.ADDI .x12 .x10 32#12) (by decide) hpc13 rfl (by intro h; cases h) rfl
          let s14 := execInstrBr s13 (.ADDI .x12 .x10 32#12)
          have hpc14 : s14.pc = pcWord 212 := by simp only [s14, execInstrBr, MachineState.setPC, hpc13, pcWord_add_four]
          have hx10_13 : s13.getReg .x10 = BitVec.ofNat 64 (16384 + 64 * h) := by
            rw [hreg13]; simp only [s12, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hreg11_10, hx10_10]
          refine ⟨s14, 3, by decide, ((hst209.trans hst210).trans hst211).eq_of rfl (by decide) (by decide) (by simp),
            hpc14, by simpa [s14, execInstrBr, mem_setPC, mem_setReg] using hmem13,
            by rw [hu_addr, hmL_val]; simp only [s14, execInstrBr, MachineState.getReg_setPC]
               rw [MachineState.getReg_setReg_eq (by decide), hx10_13, se12_32]
               change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; exact bv64_add _ 32,
            by simp only [s14, execInstrBr, MachineState.getReg_setPC]
               rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hx10_13],
            fun r h6 h7 h8 h10 h12 h14 => by
              simp only [s14, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg13]
              simp only [s12, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, hreg11_10, hreg10_5 r h6 h10, hreg5 r h6 h7 h8 h14]⟩
      obtain ⟨s212, kD, hkD, hsD, hpc212, hmem212, hx12_212, hx10_212, hreg212⟩ := hto212
      -- pc[212]: ADDI x15, x10, 0
      have hst212 := step_ordinary oracle s212 212 (.ADDI .x15 .x10 0#12) (by decide) hpc212 rfl (by intro h; cases h) rfl
      let s213 := execInstrBr s212 (.ADDI .x15 .x10 0#12)
      have hpc213 : s213.pc = pcWord 213 := by simp only [s213, execInstrBr, MachineState.setPC, hpc212, pcWord_add_four]
      have hmem213 : s213.mem = s8.mem := by simpa [s213, execInstrBr, mem_setPC, mem_setReg] using hmem212
      have hx15_213 : s213.getReg .x15 = BitVec.ofNat 64 (16384 + 64 * h) := by
        simp only [s213, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hx10_212, se12_0, BitVec.add_zero]
      have hreg213 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x12 → r ≠ .x14 → r ≠ .x15 →
          s213.getReg r = s.getReg r := fun r h6 h7 h8 h10 h12 h14 h15 => by
        simp only [s213, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h15.symm]
        exact hreg212 r h6 h7 h8 h10 h12 h14
      have hu_lt512 : u < 512 := by
        dsimp only [u]; cases mL <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] <;> omega
      have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 213 s213 pCur tCur (16384 + 32 * u)
        (by decide) rfl hpc213
        (hcur.of_agree (fun r hr => hreg213 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
        ((hhigh.trans_low hout8 (by omega)).trans_mem_eq hmem213)
        (by simp only [s213, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x15 ≠ .x12), hx12_212])
        (by omega)
      have hpre213 : StepsTo oracle s s213 (11 + kD + 1) 0 [] :=
        ((hpre11.trans hsD).trans hst212).eq_of rfl (by omega) (by decide) (by simp)
      cases hread with
      | rejected kR qR trR hr hkR hqR hhR =>
        exact .rejected (11 + kD + 1 + kR) qR trR ⟨hbne, hr⟩ (by omega) (by omega)
          (by simpa [Nat.add_assoc] using hpre213.halt hhR)
      | continued s214 kR qR trR hkR hqR hsR hpR =>
        obtain ⟨rfl, rfl, hpc214, hcur214, hreg214, hdig214, hout214⟩ := hpR
        -- pc[214]: ADDI x10, x15, 0 -> pc[215]
        have hst214 := step_ordinary oracle s214 214 (.ADDI .x10 .x15 0#12) (by decide) hpc214 rfl (by intro h; cases h) rfl
        let s215 := execInstrBr s214 (.ADDI .x10 .x15 0#12)
        have hpc215 : s215.pc = pcWord 215 := by simp only [s215, execInstrBr, MachineState.setPC, hpc214, pcWord_add_four]
        have hmem215 : s215.mem = s214.mem := by simp [s215, execInstrBr, mem_setPC, mem_setReg]
        have hx10_215 : s215.getReg .x10 = BitVec.ofNat 64 (16384 + 64 * h) := by
          simp only [s215, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide),
            hreg214 .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hx15_213, se12_0, BitVec.add_zero]
        have hreg215_s : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 →
            r ≠ .x10 → r ≠ .x12 → r ≠ .x14 → r ≠ .x15 → r ≠ .x25 → r ≠ .x31 → s215.getReg r = s.getReg r :=
          fun r h1 h3 h4 h6 h7 h8 h10 h12 h14 h15 h25 h31 => by
            simp only [s215, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ h10.symm, hreg214 r h1 h3 h4 h6 h7 h12 h25 h31]
            exact hreg213 r h6 h7 h8 h10 h12 h14 h15
        have hdig215 : readBuffer s215 (16384 + 32 * u) 32 =
            proofDigest238 s0 input.proof.length (10804531232 + pCur) tCur :=
          ((MemEqOutside.of_mem_eq hmem215 0 0).readBuffer_eq (by omega) (by omega)).trans hdig214
        have hout_s_215 : ∀ a : Nat, a < 2 ^ 64 → a ≠ 8192 + h →
            (a < 16384 + 32 * u ∨ 16384 + 32 * u + 32 ≤ a) →
            s215.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a) := fun a ha hne hout => by
          have h1 : s215.getByte (BitVec.ofNat 64 a) = s214.getByte (BitVec.ofNat 64 a) := by
            simp [MachineState.getByte, MachineState.getMem, hmem215]
          have h2 : s214.getByte (BitVec.ofNat 64 a) = s213.getByte (BitVec.ofNat 64 a) := hout214 a ha hout
          have h3 : s213.getByte (BitVec.ofNat 64 a) = s8.getByte (BitVec.ofNat 64 a) := by
            simp [MachineState.getByte, MachineState.getMem, hmem213]
          exact h1.trans (h2.trans (h3.trans (hout8 a ha (by omega))))
        refine hcomp215 s215 (11 + kD + 1 + kR + 1) (by omega)
          (((hpre213.trans hsR).trans hst214).eq_of rfl (by omega) (by decide) (by simp))
          hpc215
          (hfix.of_agree (fun r hr => hreg215_s r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl)))
          ((hreg215_s .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11)
          ((hreg215_s .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13)
          (by rw [hpn_eq, htn_eq]
              exact hcur214.of_agree (fun r hr => by
                simp only [s215, execInstrBr, MachineState.getReg_setPC]
                exact MachineState.getReg_setReg_ne _ _ _ _ (isCursorReg_ne_of_false hr rfl).symm))
          hx10_215
          ((hreg215_s .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23)
          (by have h1 : s215.getByte (BitVec.ofNat 64 (8192 + h)) = s214.getByte (BitVec.ofNat 64 (8192 + h)) := by
                simp [MachineState.getByte, MachineState.getMem, hmem215]
              have h2 : s214.getByte (BitVec.ofNat 64 (8192 + h)) = s213.getByte (BitVec.ofNat 64 (8192 + h)) :=
                hout214 (8192 + h) (by omega) (by omega)
              have h3 : s213.getByte (BitVec.ofNat 64 (8192 + h)) = s8.getByte (BitVec.ofNat 64 (8192 + h)) := by
                simp [MachineState.getByte, MachineState.getMem, hmem213]
              exact h1.trans (h2.trans (h3.trans hmk8)))
          (fun hmLf => by simpa only [u, hmLf, Bool.not_false, ite_true] using hdig215)
          (fun hmRf => by
            have hmLt : mL = true := by
              cases h1 : mL <;> rw [h1, hmRf] at horT <;> first | rfl | cases horT
            simpa only [u, hmLt, Bool.not_true, Bool.false_eq_true, ite_false] using hdig215)
          (fun a ha hne hfr => by
            rcases hfr with heq | hout
            · exact (hsame heq).elim
            · exact hout_s_215 a ha hne hout)

end CommitGolfCandidate
