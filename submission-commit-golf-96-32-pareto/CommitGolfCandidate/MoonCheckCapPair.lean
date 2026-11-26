import CommitGolfCandidate.MoonCheckPos

/-! Symbolic execution of cap-walk geometry, `CapWalkInv`, and per-pair compression (`pc[309..337]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! #### Cap Walk Geometry and Invariant (`pc[296..363]`) -/

def pairFrontierCount (positions : Positions) (l n : Nat) : Nat :=
  ((Finset.range n).filter
    (fun q => capMark positions l (2 * q) != capMark positions l (2 * q + 1))).card

def pairMarkedNextCount (positions : Positions) (l n : Nat) : Nat :=
  ((Finset.range n).filter (fun q => capMark positions (l + 1) q)).card

def capFrontierPrefix (positions : Positions) (step : Nat) : Nat :=
  ∑ d ∈ Finset.range step, levelFrontierCount positions (14 + d)

theorem pairFrontierCount_zero (positions : Positions) (l : Nat) :
    pairFrontierCount positions l 0 = 0 := by
  simp [pairFrontierCount]

theorem pairFrontierCount_succ (positions : Positions) (l q : Nat) :
    pairFrontierCount positions l (q + 1) =
      pairFrontierCount positions l q +
        if (capMark positions l (2 * q) != capMark positions l (2 * q + 1)) then 1 else 0 := by
  unfold pairFrontierCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split <;> simp [Finset.card_insert_of_notMem]

theorem pairFrontierCount_full (positions : Positions) (l : Nat) :
    pairFrontierCount positions l (levelSize l / 2) = levelFrontierCount positions l := rfl

theorem pairFrontierCount_mono (positions : Positions) (l : Nat) {a b : Nat} (hab : a ≤ b) :
    pairFrontierCount positions l a ≤ pairFrontierCount positions l b :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hab))

theorem pairMarkedNextCount_zero (positions : Positions) (l : Nat) :
    pairMarkedNextCount positions l 0 = 0 := by
  simp [pairMarkedNextCount]

theorem pairMarkedNextCount_succ (positions : Positions) (l q : Nat) :
    pairMarkedNextCount positions l (q + 1) =
      pairMarkedNextCount positions l q + if capMark positions (l + 1) q then 1 else 0 := by
  unfold pairMarkedNextCount
  rw [Finset.range_add_one, Finset.filter_insert]
  split <;> simp [Finset.card_insert_of_notMem]

theorem pairMarkedNextCount_le_card (positions : Positions) (l : Nat) (hl : 14 ≤ l) :
    pairMarkedNextCount positions l (levelSize l / 2) ≤ positions.card := by
  have hsub : (Finset.range (levelSize l / 2)).filter (fun q => capMark positions (l + 1) q) ⊆
      (Finset.range (levelSize (l + 1))).filter (fun q => capMark positions (l + 1) q) := by
    apply Finset.filter_subset_filter
    apply Finset.range_mono
    rw [levelSize_step l (by omega)]
    omega
  exact (Finset.card_le_card hsub).trans (levelMarked_le_card positions (l + 1) (by omega))

theorem capFrontierPrefix_zero (positions : Positions) :
    capFrontierPrefix positions 0 = 0 := by
  simp [capFrontierPrefix]

theorem capFrontierPrefix_succ (positions : Positions) (step : Nat) :
    capFrontierPrefix positions (step + 1) =
      capFrontierPrefix positions step + levelFrontierCount positions (14 + step) :=
  Finset.sum_range_succ _ step

theorem capFrontierPrefix_9 (positions : Positions) :
    capFrontierPrefix positions 9 = capFrontierCount positions := rfl

theorem capFrontierPrefix_mono (positions : Positions) {a b : Nat} (hab : a ≤ b) :
    capFrontierPrefix positions a ≤ capFrontierPrefix positions b :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

theorem capMarkOff_step_le (l : Nat) (hl1 : 14 ≤ l) (hl2 : l < 23) :
    capMarkOff l + levelSize l ≤ capMarkOff (l + 1) := by
  interval_cases l <;> decide

theorem capMarkOff_mono {l1 l2 : Nat} (h1 : 14 ≤ l1) (hle : l1 ≤ l2) (h2 : l2 ≤ 23) :
    capMarkOff l1 ≤ capMarkOff l2 := by
  have : l1 ≤ 23 := by omega
  interval_cases l1 <;> interval_cases l2 <;> decide

theorem capValOff_step_eq (l : Nat) (hl1 : 14 ≤ l) (hl2 : l < 23) :
    capValOff (l + 1) = capValOff l + ((levelSize l + 1) / 2) * 96 := by
  interval_cases l <;> decide

theorem capValOff_mono {l1 l2 : Nat} (h1 : 14 ≤ l1) (hle : l1 ≤ l2) (h2 : l2 ≤ 23) :
    capValOff l1 ≤ capValOff l2 := by
  have : l1 ≤ 23 := by omega
  interval_cases l1 <;> interval_cases l2 <;> decide

theorem capValOff_lt_44000 (l : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 23) :
    capValOff l + levelBytes l ≤ 44000 := by
  interval_cases l <;> decide

theorem capValOff_mod8 (l : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 23) :
    capValOff l % 8 = 0 := by
  interval_cases l <;> decide

theorem capMarkOff_lt_5120 (l : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 23) :
    4096 + capMarkOff l + levelSize l ≤ 5120 := by
  interval_cases l <;> decide

theorem capValOff_add_levelBytes_eq (a : Nat) (ha1 : 14 ≤ a) (ha2 : a < 23) :
    capValOff a + levelBytes a = capValOff (a + 1) := by
  interval_cases a <;> decide

theorem capValOff_add_levelBytes_le {a b : Nat} (ha : 14 ≤ a) (hab : a < b) (hb : b ≤ 23) :
    capValOff a + levelBytes a ≤ capValOff b := by
  have : a < 23 := by omega
  interval_cases a <;> interval_cases b <;> decide

theorem levelSize_cap_le456 (a : Nat) (ha1 : 14 ≤ a) (ha2 : a < 23) :
    levelSize a ≤ 456 := by
  interval_cases a <;> decide

theorem cap_lt22_of_odd (a : Nat) (ha1 : 14 ≤ a) (ha2 : a < 23)
    (hodd : levelSize a % 2 = 1) : a < 22 := by
  interval_cases a <;> first | decide | (exfalso; revert hodd; decide)

theorem levelSize_cap_pairs_pos (l : Nat) (hl1 : 14 ≤ l) (hl2 : l < 23) :
    0 < levelSize l / 2 := by
  interval_cases l <;> decide

theorem cap_level_steps_sum :
    (∑ step ∈ Finset.range 9, (37 + 225 * (levelSize (14 + step) / 2))) + 2 ≤ 110000 := by
  decide

theorem cap_gapOffset_bound (l idx : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 23)
    (hidx : idx < levelSize l) :
    gapOffset idx + 32 ≤ levelBytes l := by
  by_cases h23 : l = 23
  · subst h23
    have : idx = 0 := by rw [levelSize_23] at hidx; omega
    subst this; decide
  · exact gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx

theorem cap_val_next_bound (l idx : Nat) (hl1 : 14 ≤ l) (hl2 : l < 23)
    (hidx : idx < levelSize (l + 1)) :
    capValOff (l + 1) + gapOffset idx + 32 ≤ 44000 := by
  have h1 := cap_gapOffset_bound (l + 1) idx (by omega) (by omega) hidx
  have h2 := capValOff_lt_44000 (l + 1) (by omega) (by omega)
  omega

theorem cap_val_next_lt_next (l idx : Nat) (hl1 : 14 ≤ l) (hl2 : l < 22)
    (hidx : idx < levelSize (l + 1)) :
    capValOff (l + 1) + gapOffset idx + 32 ≤ capValOff (l + 2) := by
  have h1 := cap_gapOffset_bound (l + 1) idx (by omega) (by omega) hidx
  have h2 : capValOff (l + 1) + levelBytes (l + 1) = capValOff (l + 2) := by
    interval_cases l <;> decide
  omega

/-- Cap-walk invariant after completing `step` cap levels (`0 ≤ step ≤ 9`, levels `15 .. 14 + step - 1`). -/
structure CapWalkInv (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (sPos : MachineState) (step : Nat) (s : MachineState)
    (tr : CompressionReplies) : Prop where
  fixed : CheckFixedRegs s
  cursor : ProofCursor (submission.initialState .check input) input.proof.length
    (posRecordOff input.positions input.positions.card + 29 * capFrontierPrefix input.positions step)
    (posTailOff input.positions input.positions.card + capFrontierPrefix input.positions step) s
  high : HighMemPreserved (submission.initialState .check input) s
  pc : s.pc = if step = 9 then pcWord 364 else pcWord 298
  x29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (14 + step))
  x30 : s.getReg .x30 = BitVec.ofNat 64 (68719475968 + 736)
  mark_cur : step < 9 → ∀ idx < levelSize (14 + step),
    s.getByte (BitVec.ofNat 64 (4096 + capMarkOff (14 + step) + idx)) =
      if capMark input.positions (14 + step) idx then 1#8 else 0#8
  mark_hi_zero : step < 9 → ∀ a, 4096 + capMarkOff (14 + step + 1) ≤ a → a < 5120 →
    s.getByte (BitVec.ofNat 64 a) = 0#8
  val_cur_gap_zero : step < 9 → ∀ q < levelSize (14 + step) / 2, ∀ b < 32,
    s.getByte (BitVec.ofNat 64 (8192 + capValOff (14 + step) + 96 * q + 64 + b)) = 0#8
  val_hi_zero : step < 9 → ∀ a, 8192 + capValOff (14 + step + 1) ≤ a → a < 8192 + 44000 →
    s.getByte (BitVec.ofNat 64 a) = 0#8
  val14_marked : ∀ c < 456, capMark input.positions 14 c = true →
    readBuffer s (8192 + capValOff 14 + gapOffset c) 32 = readBuffer sPos (8192 + gapOffset c) 32
  levels_done : ∀ d < step,
    let l := 14 + d
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let s0 := submission.initialState .check input
    let pBase := posRecordOff input.positions input.positions.card
    let tBase := posTailOff input.positions input.positions.card
    (∀ q < levelSize l / 2, capMark input.positions (l + 1) q = true →
      let dL := readBuffer s (8192 + capValOff l + gapOffset (2 * q)) 32
      let dR := readBuffer s (8192 + capValOff l + gapOffset (2 * q + 1)) 32
      let pAt := pBase + 29 * (capFrontierPrefix input.positions d + pairFrontierCount input.positions l q)
      let tAt := tBase + (capFrontierPrefix input.positions d + pairFrontierCount input.positions l q)
      readBuffer s (8192 + capValOff (l + 1) + gapOffset q) 32 =
        (if l = 22 then c96 (binaryInput dL dR) else mask238 (c96 (binaryInput dL dR))) ∧
      InTrace h768 oracle tr (binaryInput dL dR) ∧
      (capMark input.positions l (2 * q) = false → dL = proofDigest238 s0 input.proof.length (11162446080 + pAt) tAt) ∧
      (capMark input.positions l (2 * q + 1) = false → dR = proofDigest238 s0 input.proof.length (11162446080 + pAt) tAt)) ∧
    (levelSize l % 2 = 1 → capMark input.positions l (2 * (levelSize l / 2)) = true →
      readBuffer s (8192 + capValOff (l + 1) + gapOffset (levelSize l / 2)) 32 =
        readBuffer s (8192 + capValOff l + gapOffset (2 * (levelSize l / 2))) 32)

private theorem pc_337_branch : pcWord 337 + signExtend13 8080#13 = pcWord 309 := by decide
private theorem pc_314_branch : pcWord 314 + signExtend13 88#13 = pcWord 336 := by decide
private theorem pc_321_branch : pcWord 321 + signExtend13 20#13 = pcWord 326 := by decide
private theorem pc_323_branch : pcWord 323 + signExtend13 8#13 = pcWord 325 := by decide
private theorem pc_332_branch : pcWord 332 + signExtend13 16#13 = pcWord 336 := by decide

private def capPairAddrInstrs : List Instr :=
  [.SLLI .x6 .x23 6#6, .SLLI .x28 .x23 5#6, .ADD .x10 .x6 .x28, .ADD .x10 .x16 .x10]

private def capPairDstInstrs : List Instr :=
  [.SRLI .x6 .x23 1#6, .ADD .x6 .x23 .x6, .SLLI .x6 .x6 5#6, .ADD .x12 .x17 .x6]

/-- One pair iteration `q < levelSize l / 2` in cap level `l ∈ 14..22` (`pc[309..337]`). -/
theorem step_cap_pair (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (l q pCur tCur : Nat) (hl1 : 14 ≤ l) (hl2 : l < 23) (hq : q < levelSize l / 2)
    (s : MachineState) (hpc : s.pc = pcWord 309)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pCur tCur s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (levelSize l))
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l))
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)))
    (hx16 : s.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l))
    (hx17 : s.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)))
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2))
    (hx23 : s.getReg .x23 = BitVec.ofNat 64 q)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475968 + 736))
    (hmL : s.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q)) =
      if capMark input.positions l (2 * q) then 1#8 else 0#8)
    (hmR : s.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1))) =
      if capMark input.positions l (2 * q + 1) then 1#8 else 0#8)
    (hmNext0 : s.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) = 0#8)
    (hgap : ∀ b < 32, s.getByte (BitVec.ofNat 64 (8192 + capValOff l + 96 * q + 64 + b)) = 0#8) :
    let s0 := submission.initialState .check input
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let mL := capMark input.positions l (2 * q)
    let mR := capMark input.positions l (2 * q + 1)
    let pNext := pCur + if (mL != mR) then 29 else 0
    let tNext := tCur + if (mL != mR) then 1 else 0
    PhaseOutcome oracle s 225 (if (mL || mR) then 1 else 0)
      ((mL != mR) = true ∧ input.proof.length < pCur + 29 + tailBytes (tCur + 1))
      (fun s' calls tr =>
        calls ≤ (if (mL || mR) then 1 else 0) ∧
        s'.pc = (if q + 1 = levelSize l / 2 then pcWord 338 else pcWord 309) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length pNext tNext s' ∧
        s'.getReg .x20 = BitVec.ofNat 64 (levelSize l) ∧
        s'.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
        s'.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
        s'.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) ∧
        s'.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) ∧
        s'.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) ∧
        s'.getReg .x23 = BitVec.ofNat 64 (q + 1) ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 736) ∧
        s'.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) =
          (if (mL || mR) then 1#8 else 0#8) ∧
        (mL || mR = true →
          let dL := readBuffer s' (8192 + capValOff l + gapOffset (2 * q)) 32
          let dR := readBuffer s' (8192 + capValOff l + gapOffset (2 * q + 1)) 32
          readBuffer s' (8192 + capValOff (l + 1) + gapOffset q) 32 =
            (if l = 22 then c96 (binaryInput dL dR) else mask238 (c96 (binaryInput dL dR))) ∧
          InTrace h768 oracle tr (binaryInput dL dR) ∧
          (mL = false → dL = proofDigest238 s0 input.proof.length (11162446080 + pCur) tCur) ∧
          (mR = false → dR = proofDigest238 s0 input.proof.length (11162446080 + pCur) tCur)) ∧
        (mL = false → mR = false → s'.mem = s.mem) ∧
        (∀ a : Nat, a < 2 ^ 64 →
          a ≠ 4096 + capMarkOff (l + 1) + q →
          (mL = mR ∨
            let u := if !mL then 2 * q else 2 * q + 1
            a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
          (a < 8192 + capValOff (l + 1) + gapOffset q ∨ 8192 + capValOff (l + 1) + gapOffset q + 32 ≤ a) →
          s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a))) := by
  intro s0 c96 mL mR pNext tNext
  have hplen_bd : input.proof.length ≤ 8669633152 := hvalid
  have hls_le : levelSize l ≤ 456 := levelSize_cap_le456 l hl1 hl2
  have hpairs_lt : levelSize l / 2 ≤ 228 := by omega
  have hq_lt_next : q < levelSize (l + 1) := by rw [levelSize_step l (by omega)]; omega
  have hmo_l_bd := capMarkOff_lt_5120 l hl1 (by omega)
  have hmo_n_bd := capMarkOff_lt_5120 (l + 1) (by omega) (by omega)
  have hvo_l_bd := capValOff_lt_44000 l hl1 (by omega)
  have hvo_n_bd := capValOff_lt_44000 (l + 1) (by omega) (by omega)
  have hvo_step := capValOff_step_eq l hl1 hl2
  have hvo_l_al := capValOff_mod8 l hl1 (by omega)
  have hvo_n_al := capValOff_mod8 (l + 1) (by omega) (by omega)
  have hdst_bd : capValOff (l + 1) + gapOffset q + 32 ≤ 44000 := cap_val_next_bound l q hl1 hl2 hq_lt_next
  have hsrc_le_next : capValOff l + 96 * q + 96 ≤ capValOff (l + 1) := by
    rw [hvo_step]; omega
  -- pc[309..314]: load mL, mR, compute mL || mR, branch if 0
  have hst309 := step_ordinary oracle s 309 (.SLLI .x6 .x23 1#6) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.SLLI .x6 .x23 1#6)
  have hpc1 : s1.pc = pcWord 310 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst310 := step_ordinary oracle s1 310 (.ADD .x6 .x14 .x6) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADD .x6 .x14 .x6)
  have hpc2 : s2.pc = pcWord 311 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx6_2 : s2.getReg .x6 = BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx14, hx23,
      show (1#6 : BitVec 6).toNat = 1 by decide]
    rw [bv64_shl q 1 (by omega), bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hmem2 : s2.mem = s.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg2 : ∀ r, r ≠ .x6 → s2.getReg r = s.getReg r := fun r h6 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
  have ha311 : s2.getReg .x6 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) := by
    rw [hx6_2, se12_0, BitVec.add_zero]
  have hv311 : memoryArgumentsValid s2 (.LBU .x7 .x6 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha311]
    exact accessValid_ofNat (4096 + capMarkOff l + 2 * q) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst311 := step_ordinary oracle s2 311 (.LBU .x7 .x6 0#12) (by decide) hpc2 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv311])
  let s3 := execInstrBr s2 (.LBU .x7 .x6 0#12)
  have hpc3 : s3.pc = pcWord 312 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hx6_3 : s3.getReg .x6 = BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6), hx6_2]
  have ha312 : s3.getReg .x6 + signExtend12 1#12 = BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1)) := by
    rw [hx6_3, se12_1]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 1 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv312 : memoryArgumentsValid s3 (.LBU .x8 .x6 1#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha312]
    exact accessValid_ofNat (4096 + capMarkOff l + (2 * q + 1)) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst312 := step_ordinary oracle s3 312 (.LBU .x8 .x6 1#12) (by decide) hpc3 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv312])
  let s4 := execInstrBr s3 (.LBU .x8 .x6 1#12)
  have hpc4 : s4.pc = pcWord 313 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hmem4 : s4.mem = s.mem := by
    simpa [s4, s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
  have hx7_4 : s4.getReg .x7 = if mL then 1#64 else 0#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x7)]
    simp only [s3, execInstrBr, MachineState.getReg_setPC, ha311]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hb : s2.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q)) = if mL then 1#8 else 0#8 := by
      simpa only [MachineState.getByte, MachineState.getMem, hmem2] using hmL
    rw [hb, bool_byte_zeroExtend]
  have hx8_4 : s4.getReg .x8 = if mR then 1#64 else 0#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, ha312]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
    have hb : s3.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1))) = if mR then 1#8 else 0#8 := by
      simpa only [MachineState.getByte, MachineState.getMem, hmem3] using hmR
    rw [hb, bool_byte_zeroExtend]
  have hst313 := step_ordinary oracle s4 313 (.OR .x28 .x7 .x8) (by decide) hpc4 rfl (by intro h; cases h) rfl
  let s5 := execInstrBr s4 (.OR .x28 .x7 .x8)
  have hpc5 : s5.pc = pcWord 314 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem5 : s5.mem = s.mem := by simpa [s5, execInstrBr, mem_setPC, mem_setReg] using hmem4
  have hx28_5 : s5.getReg .x28 = if (mL || mR) then 1#64 else 0#64 := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hx7_4, hx8_4, bool_word_or]
  have hx7_5 : s5.getReg .x7 = if mL then 1#64 else 0#64 := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x7), hx7_4]
  have hx8_5 : s5.getReg .x8 = if mR then 1#64 else 0#64 := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x8), hx8_4]
  have hreg5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x28 → s5.getReg r = s.getReg r := fun r h6 h7 h8 h28 => by
    simp only [s5, s4, s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h28.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h8.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
    exact hreg2 r h6
  have hst314 := step_ordinary oracle s5 314 (.BEQ .x28 .x0 88#13) (by decide) hpc5 rfl (by intro h; cases h) rfl
  let s6 := execInstrBr s5 (.BEQ .x28 .x0 88#13)
  have hs_309_314 : StepsTo oracle s s6 6 0 [] := by
    simpa using (((hst309.trans hst310).trans hst311).trans (hst312.trans hst313)).trans hst314
  -- Common tail pc[336..337]
  have hloop_tail : ∀ (s336 : MachineState) (kPre qPre : Nat) (trPre : CompressionReplies),
      kPre ≤ 223 → qPre ≤ (if (mL || mR) then 1 else 0) →
      StepsTo oracle s s336 kPre qPre trPre →
      s336.pc = pcWord 336 →
      CheckFixedRegs s336 →
      ProofCursor s0 input.proof.length pNext tNext s336 →
      s336.getReg .x20 = BitVec.ofNat 64 (levelSize l) →
      s336.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) →
      s336.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) →
      s336.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) →
      s336.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) →
      s336.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) →
      s336.getReg .x23 = BitVec.ofNat 64 q →
      s336.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) →
      s336.getReg .x30 = BitVec.ofNat 64 (68719475968 + 736) →
      s336.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) =
        (if (mL || mR) then 1#8 else 0#8) →
      (mL || mR = true →
        let dL := readBuffer s336 (8192 + capValOff l + gapOffset (2 * q)) 32
        let dR := readBuffer s336 (8192 + capValOff l + gapOffset (2 * q + 1)) 32
        readBuffer s336 (8192 + capValOff (l + 1) + gapOffset q) 32 =
          (if l = 22 then c96 (binaryInput dL dR) else mask238 (c96 (binaryInput dL dR))) ∧
        InTrace h768 oracle trPre (binaryInput dL dR) ∧
        (mL = false → dL = proofDigest238 s0 input.proof.length (11162446080 + pCur) tCur) ∧
        (mR = false → dR = proofDigest238 s0 input.proof.length (11162446080 + pCur) tCur)) →
      (mL = false → mR = false → s336.mem = s.mem) →
      (∀ a : Nat, a < 2 ^ 64 →
        a ≠ 4096 + capMarkOff (l + 1) + q →
        (mL = mR ∨
          let u := if !mL then 2 * q else 2 * q + 1
          a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
        (a < 8192 + capValOff (l + 1) + gapOffset q ∨ 8192 + capValOff (l + 1) + gapOffset q + 32 ≤ a) →
        s336.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) →
      PhaseOutcome oracle s 225 (if (mL || mR) then 1 else 0)
        ((mL != mR) = true ∧ input.proof.length < pCur + 29 + tailBytes (tCur + 1))
        (fun s' calls tr =>
          calls ≤ (if (mL || mR) then 1 else 0) ∧
          s'.pc = (if q + 1 = levelSize l / 2 then pcWord 338 else pcWord 309) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length pNext tNext s' ∧
          s'.getReg .x20 = BitVec.ofNat 64 (levelSize l) ∧
          s'.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
          s'.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
          s'.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) ∧
          s'.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) ∧
          s'.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) ∧
          s'.getReg .x23 = BitVec.ofNat 64 (q + 1) ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 736) ∧
          s'.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) =
            (if (mL || mR) then 1#8 else 0#8) ∧
          (mL || mR = true →
            let dL := readBuffer s' (8192 + capValOff l + gapOffset (2 * q)) 32
            let dR := readBuffer s' (8192 + capValOff l + gapOffset (2 * q + 1)) 32
            readBuffer s' (8192 + capValOff (l + 1) + gapOffset q) 32 =
              (if l = 22 then c96 (binaryInput dL dR) else mask238 (c96 (binaryInput dL dR))) ∧
            InTrace h768 oracle tr (binaryInput dL dR) ∧
            (mL = false → dL = proofDigest238 s0 input.proof.length (11162446080 + pCur) tCur) ∧
            (mR = false → dR = proofDigest238 s0 input.proof.length (11162446080 + pCur) tCur)) ∧
          (mL = false → mR = false → s'.mem = s.mem) ∧
          (∀ a : Nat, a < 2 ^ 64 →
            a ≠ 4096 + capMarkOff (l + 1) + q →
            (mL = mR ∨
              let u := if !mL then 2 * q else 2 * q + 1
              a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
            (a < 8192 + capValOff (l + 1) + gapOffset q ∨ 8192 + capValOff (l + 1) + gapOffset q + 32 ≤ a) →
            s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a))) := by
    intro s336 kPre qPre trPre hkPre hqPre hstPre hpc336 hfix336 hcur336 h20 h14 h15 h16 h17 h22 h23 h29 h30
      hmk336 hval336 hmeq336 hout336
    have hst336 := step_ordinary oracle s336 336 (.ADDI .x23 .x23 1#12) (by decide) hpc336 rfl (by intro h; cases h) rfl
    let s337 := execInstrBr s336 (.ADDI .x23 .x23 1#12)
    have hpc337 : s337.pc = pcWord 337 := by simp only [s337, execInstrBr, MachineState.setPC, hpc336, pcWord_add_four]
    have hx23_337 : s337.getReg .x23 = BitVec.ofNat 64 (q + 1) := by
      simp only [s337, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), h23, se12_1]
      change BitVec.ofNat 64 q + BitVec.ofNat 64 1 = _; exact bv64_add q 1
    have hx22_337 : s337.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) := by
      simp only [s337, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x22), h22]
    obtain ⟨sFin, hst337, hpcFin, hregFin_b, hmemFin_b⟩ :=
      step_bne_reg oracle 337 309 .x23 .x22 8080#13 (by decide) rfl pc_337_branch
        s337 (q + 1) (levelSize l / 2) (by omega) (by omega) hpc337 hx23_337 hx22_337
    have hmemFin : sFin.mem = s336.mem :=
      hmemFin_b.trans (by simp [s337, execInstrBr, mem_setPC, mem_setReg])
    have hregFin : ∀ r, r ≠ .x23 → sFin.getReg r = s336.getReg r := fun r h23r => by
      rw [hregFin_b]; simp only [s337, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h23r.symm
    have hx23Fin : sFin.getReg .x23 = BitVec.ofNat 64 (q + 1) := (hregFin_b .x23).trans hx23_337
    have hrb_eq : ∀ addr n, readBuffer sFin addr n = readBuffer s336 addr n := fun addr n => by
      apply readBuffer_congr2; intro j _; simp [MachineState.getByte, MachineState.getMem, hmemFin]
    refine .continued sFin (kPre + 2) qPre trPre (by omega) hqPre
      (by simpa [Nat.add_assoc] using hstPre.trans (hst336.trans hst337))
      ⟨hqPre, hpcFin,
       hfix336.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)),
       hcur336.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)),
       (hregFin .x20 (by decide)).trans h20, (hregFin .x14 (by decide)).trans h14,
       (hregFin .x15 (by decide)).trans h15, (hregFin .x16 (by decide)).trans h16,
       (hregFin .x17 (by decide)).trans h17, (hregFin .x22 (by decide)).trans h22,
       hx23Fin, (hregFin .x29 (by decide)).trans h29, (hregFin .x30 (by decide)).trans h30,
       by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hmk336,
       fun hm => by simpa only [hrb_eq] using hval336 hm,
       fun h1 h2 => hmemFin.trans (hmeq336 h1 h2),
       fun a ha h1 h2 h3 => by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hout336 a ha h1 h2 h3⟩
  -- Case split on (mL || mR)
  by_cases hor : (mL || mR) = false
  · -- Branch A: neither child marked -> jump straight to pc[336]
    have hmLf : mL = false := (Bool.or_eq_false_iff.mp hor).1
    have hmRf : mR = false := (Bool.or_eq_false_iff.mp hor).2
    have hpn_eq : pNext = pCur := by simp [pNext, hmLf, hmRf]
    have htn_eq : tNext = tCur := by simp [tNext, hmLf, hmRf]
    have hx28z : s5.getReg .x28 = 0#64 := by simp only [hx28_5, hor, Bool.false_eq_true, ite_false]
    have hpc6 : s6.pc = pcWord 336 := by
      simp only [s6, execInstrBr, hx28z, getReg_x0, beq_self_eq_true, ite_true,
        MachineState.setPC, hpc5]; exact pc_314_branch
    have hmem6 : s6.mem = s.mem := by
      simpa [s6, execInstrBr, hx28z, getReg_x0, MachineState.setPC] using hmem5
    have hreg6 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x28 → s6.getReg r = s.getReg r := fun r h6 h7 h8 h28 => by
      have : s6.getReg r = s5.getReg r := by simp [s6, execInstrBr, hx28z, getReg_x0, MachineState.getReg_setPC]
      exact this.trans (hreg5 r h6 h7 h8 h28)
    refine hloop_tail s6 6 0 [] (by decide) (by simp [hor]) hs_309_314 hpc6
      (hfix.of_agree (fun r hr => hreg6 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
      (by rw [hpn_eq, htn_eq]
          exact hcur.of_agree (fun r hr => hreg6 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
            (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      ((hreg6 .x20 (by decide) (by decide) (by decide) (by decide)).trans hx20)
      ((hreg6 .x14 (by decide) (by decide) (by decide) (by decide)).trans hx14)
      ((hreg6 .x15 (by decide) (by decide) (by decide) (by decide)).trans hx15)
      ((hreg6 .x16 (by decide) (by decide) (by decide) (by decide)).trans hx16)
      ((hreg6 .x17 (by decide) (by decide) (by decide) (by decide)).trans hx17)
      ((hreg6 .x22 (by decide) (by decide) (by decide) (by decide)).trans hx22)
      ((hreg6 .x23 (by decide) (by decide) (by decide) (by decide)).trans hx23)
      ((hreg6 .x29 (by decide) (by decide) (by decide) (by decide)).trans hx29)
      ((hreg6 .x30 (by decide) (by decide) (by decide) (by decide)).trans hx30)
      (by simp only [hor, Bool.false_eq_true, ite_false, MachineState.getByte, MachineState.getMem, hmem6]; exact hmNext0)
      (fun h => by rw [hmLf, hmRf] at h; cases h)
      (fun _ _ => hmem6)
      (fun a _ _ _ _ => by simp only [MachineState.getByte, MachineState.getMem, hmem6])
  · -- Branch B: at least one child marked -> mark parent, optional frontier read, compress
    have horT : (mL || mR) = true := Bool.eq_true_of_not_eq_false hor
    have hx28o : s5.getReg .x28 = 1#64 := by simp only [hx28_5, horT, ite_true]
    have hpc6 : s6.pc = pcWord 315 := by
      simp only [s6, execInstrBr, hx28o, getReg_x0, show (1#64 == 0#64) = false by decide,
        Bool.false_eq_true, ite_false, MachineState.setPC, hpc5, pcWord_add_four]
    have hmem6 : s6.mem = s.mem := by
      simpa [s6, execInstrBr, hx28o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.setPC] using hmem5
    have hreg6 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x28 → s6.getReg r = s.getReg r := fun r h6 h7 h8 h28 => by
      have : s6.getReg r = s5.getReg r := by
        simp [s6, execInstrBr, hx28o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
      exact this.trans (hreg5 r h6 h7 h8 h28)
    have hx28_6 : s6.getReg .x28 = 1#64 := by
      simp [s6, execInstrBr, hx28o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
    have hx7_6 : s6.getReg .x7 = if mL then 1#64 else 0#64 := by
      have : s6.getReg .x7 = s5.getReg .x7 := by
        simp [s6, execInstrBr, hx28o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
      exact this.trans hx7_5
    have hx8_6 : s6.getReg .x8 = if mR then 1#64 else 0#64 := by
      have : s6.getReg .x8 = s5.getReg .x8 := by
        simp [s6, execInstrBr, hx28o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
      exact this.trans hx8_5
    -- pc[315..316]: mark capMark[l+1][q] = 1
    have hst315 := step_ordinary oracle s6 315 (.ADD .x6 .x15 .x23) (by decide) hpc6 rfl (by intro h; cases h) rfl
    let s7 := execInstrBr s6 (.ADD .x6 .x15 .x23)
    have hpc7 : s7.pc = pcWord 316 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
    have hx6_7 : s7.getReg .x6 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) := by
      simp only [s7, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        hreg6 .x15 (by decide) (by decide) (by decide) (by decide), hx15,
        hreg6 .x23 (by decide) (by decide) (by decide) (by decide), hx23, bv64_add]
    have hx28_7 : s7.getReg .x28 = 1#64 := by
      simp only [s7, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28), hx28_6]
    have ha316 : s7.getReg .x6 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) := by
      rw [hx6_7, se12_0, BitVec.add_zero]
    have hv316 : memoryArgumentsValid s7 (.SB .x6 .x28 0#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha316]
      exact accessValid_ofNat (4096 + capMarkOff (l + 1) + q) 1 (by unfold MEMORY_BYTES; omega) (by omega)
    have hst316 := step_ordinary oracle s7 316 (.SB .x6 .x28 0#12) (by decide) hpc7 rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv316])
    let s8 := execInstrBr s7 (.SB .x6 .x28 0#12)
    have hpc8 : s8.pc = pcWord 317 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
    have hmem7 : s7.mem = s.mem := by simpa [s7, execInstrBr, mem_setPC, mem_setReg] using hmem6
    have hbyte8 : ∀ a, s8.getByte a = (s.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) 1#8).getByte a := fun a => by
      simp only [s8, execInstrBr, ha316, hx28_7, show (1#64 : Word).truncate 8 = 1#8 by decide,
        MachineState.getByte, MachineState.setByte, MachineState.getMem,
        MachineState.setMem, mem_setPC, hmem7]
    have hout8 : MemEqOutside s s8 (4096 + capMarkOff (l + 1) + q) (4096 + capMarkOff (l + 1) + q + 1) := by
      intro a ha hout; rw [hbyte8]; exact MemEqOutside_setByte s _ 1#8 (by omega) a ha hout
    have hreg8 : ∀ r, r ≠ .x6 → s8.getReg r = s6.getReg r := fun r h6 => by
      have : s8.getReg r = s7.getReg r := by
        simp [s8, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      rw [this]; simp only [s7, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h6.symm
    -- pc[317..320]: x10 = 8192 + capValOff l + 96 * q
    have hcodeP : ∀ j (hj : j < capPairAddrInstrs.length), checkInstr (317 + j) = .base (capPairAddrInstrs[j]'hj) := by
      intro j hj; have hj' : j < 4 := hj; interval_cases j <;> rfl
    have hpureP : ∀ j (hj : j < capPairAddrInstrs.length),
        Instruction.base (capPairAddrInstrs[j]'hj) ≠ .base .ECALL ∧
        ∀ st, ordinaryStep st (.base (capPairAddrInstrs[j]'hj)) = some (execInstrBr st (capPairAddrInstrs[j]'hj)) ∧
              (execInstrBr st (capPairAddrInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
              (execInstrBr st (capPairAddrInstrs[j]'hj)).mem = st.mem := by
      intro j hj; have hj' : j < 4 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
    obtain ⟨hs9, hpc9, hmem9⟩ := step_pure_list oracle 317 capPairAddrInstrs s8 (by decide) hcodeP hpureP hpc8
    let s9 := runInstrs s8 capPairAddrInstrs
    have hs9 : StepsTo oracle s8 s9 4 0 [] := hs9
    have hpc9 : s9.pc = pcWord 321 := hpc9
    have hmem9 : s9.mem = s8.mem := hmem9
    have hx10_9 : s9.getReg .x10 = BitVec.ofNat 64 (8192 + capValOff l + 96 * q) := by
      have hx23_8 : s8.getReg .x23 = BitVec.ofNat 64 q :=
        (hreg8 .x23 (by decide)).trans ((hreg6 .x23 (by decide) (by decide) (by decide) (by decide)).trans hx23)
      have hx16_8 : s8.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) :=
        (hreg8 .x16 (by decide)).trans ((hreg6 .x16 (by decide) (by decide) (by decide) (by decide)).trans hx16)
      simp only [s9, runInstrs, capPairAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq,
        hx23_8, hx16_8, show (6#6 : BitVec 6).toNat = 6 by decide, show (5#6 : BitVec 6).toNat = 5 by decide]
      rw [bv64_shl q 6 (by omega), bv64_shl q 5 (by omega), bv64_add, bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
    have hreg9 : ∀ r, r ≠ .x6 → r ≠ .x10 → r ≠ .x28 → s9.getReg r = s8.getReg r := fun r h6 h10 h28 => by
      simp only [s9, runInstrs, capPairAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ h10.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ h28.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
    have hx7_9 : s9.getReg .x7 = if mL then 1#64 else 0#64 :=
      (hreg9 .x7 (by decide) (by decide) (by decide)).trans ((hreg8 .x7 (by decide)).trans hx7_6)
    have hx8_9 : s9.getReg .x8 = if mR then 1#64 else 0#64 :=
      (hreg9 .x8 (by decide) (by decide) (by decide)).trans ((hreg8 .x8 (by decide)).trans hx8_6)
    -- pc[321]: BEQ x7, x8, pc[326]
    have hst321 := step_ordinary oracle s9 321 (.BEQ .x7 .x8 20#13) (by decide) hpc9 rfl (by intro h; cases h) rfl
    let s10 := execInstrBr s9 (.BEQ .x7 .x8 20#13)
    have hs_309_321 : StepsTo oracle s s10 13 0 [] := by
      simpa using (hs_309_314.trans (hst315.trans hst316)).trans (hs9.trans hst321)
    -- Common compression + mask238 block pc[326..335] -> pc[336]
    have hcompress : ∀ (s326 : MachineState) (kPre : Nat),
        kPre ≤ 213 →
        StepsTo oracle s s326 kPre 0 [] →
        s326.pc = pcWord 326 →
        CheckFixedRegs s326 →
        ProofCursor s0 input.proof.length pNext tNext s326 →
        s326.getReg .x10 = BitVec.ofNat 64 (8192 + capValOff l + 96 * q) →
        s326.getReg .x20 = BitVec.ofNat 64 (levelSize l) →
        s326.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) →
        s326.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) →
        s326.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) →
        s326.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) →
        s326.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) →
        s326.getReg .x23 = BitVec.ofNat 64 q →
        s326.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) →
        s326.getReg .x30 = BitVec.ofNat 64 (68719475968 + 736) →
        s326.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) = 1#8 →
        (∀ b < 32, s326.getByte (BitVec.ofNat 64 (8192 + capValOff l + 96 * q + 64 + b)) = 0#8) →
        (mL = false → readBuffer s326 (8192 + capValOff l + gapOffset (2 * q)) 32 =
          proofDigest238 s0 input.proof.length (11162446080 + pCur) tCur) →
        (mR = false → readBuffer s326 (8192 + capValOff l + gapOffset (2 * q + 1)) 32 =
          proofDigest238 s0 input.proof.length (11162446080 + pCur) tCur) →
        (∀ a : Nat, a < 2 ^ 64 →
          a ≠ 4096 + capMarkOff (l + 1) + q →
          (mL = mR ∨
            let u := if !mL then 2 * q else 2 * q + 1
            a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
          s326.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) →
        PhaseOutcome oracle s 225 (if (mL || mR) then 1 else 0)
          ((mL != mR) = true ∧ input.proof.length < pCur + 29 + tailBytes (tCur + 1))
          (fun s' calls tr =>
            calls ≤ (if (mL || mR) then 1 else 0) ∧
            s'.pc = (if q + 1 = levelSize l / 2 then pcWord 338 else pcWord 309) ∧
            CheckFixedRegs s' ∧
            ProofCursor s0 input.proof.length pNext tNext s' ∧
            s'.getReg .x20 = BitVec.ofNat 64 (levelSize l) ∧
            s'.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
            s'.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
            s'.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) ∧
            s'.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) ∧
            s'.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) ∧
            s'.getReg .x23 = BitVec.ofNat 64 (q + 1) ∧
            s'.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) ∧
            s'.getReg .x30 = BitVec.ofNat 64 (68719475968 + 736) ∧
            s'.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) =
              (if (mL || mR) then 1#8 else 0#8) ∧
            (mL || mR = true →
              let dL := readBuffer s' (8192 + capValOff l + gapOffset (2 * q)) 32
              let dR := readBuffer s' (8192 + capValOff l + gapOffset (2 * q + 1)) 32
              readBuffer s' (8192 + capValOff (l + 1) + gapOffset q) 32 =
                (if l = 22 then c96 (binaryInput dL dR) else mask238 (c96 (binaryInput dL dR))) ∧
              InTrace h768 oracle tr (binaryInput dL dR) ∧
              (mL = false → dL = proofDigest238 s0 input.proof.length (11162446080 + pCur) tCur) ∧
              (mR = false → dR = proofDigest238 s0 input.proof.length (11162446080 + pCur) tCur)) ∧
            (mL = false → mR = false → s'.mem = s.mem) ∧
            (∀ a : Nat, a < 2 ^ 64 →
              a ≠ 4096 + capMarkOff (l + 1) + q →
              (mL = mR ∨
                let u := if !mL then 2 * q else 2 * q + 1
                a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
              (a < 8192 + capValOff (l + 1) + gapOffset q ∨ 8192 + capValOff (l + 1) + gapOffset q + 32 ≤ a) →
              s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a))) := by
      intro s326 kPre hkPre hstPre hpc326 hfix326 hcur326 h10 h20 h14 h15 h16 h17 h22 h23 h29 h30
        hmk326 hgap326 hdL_fr hdR_fr hout326
      have hcodeD : ∀ j (hj : j < capPairDstInstrs.length), checkInstr (326 + j) = .base (capPairDstInstrs[j]'hj) := by
        intro j hj; have hj' : j < 4 := hj; interval_cases j <;> rfl
      have hpureD : ∀ j (hj : j < capPairDstInstrs.length),
          Instruction.base (capPairDstInstrs[j]'hj) ≠ .base .ECALL ∧
          ∀ st, ordinaryStep st (.base (capPairDstInstrs[j]'hj)) = some (execInstrBr st (capPairDstInstrs[j]'hj)) ∧
                (execInstrBr st (capPairDstInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
                (execInstrBr st (capPairDstInstrs[j]'hj)).mem = st.mem := by
        intro j hj; have hj' : j < 4 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
      obtain ⟨hsD, hpcD, hmemD⟩ := step_pure_list oracle 326 capPairDstInstrs s326 (by decide) hcodeD hpureD hpc326
      let sD := runInstrs s326 capPairDstInstrs
      have hsD : StepsTo oracle s326 sD 4 0 [] := hsD
      have hpcD : sD.pc = pcWord 330 := hpcD
      have hmemD : sD.mem = s326.mem := hmemD
      have hregD : ∀ r, r ≠ .x6 → r ≠ .x12 → sD.getReg r = s326.getReg r := fun r h6 h12 => by
        simp only [sD, runInstrs, capPairDstInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
      have hx12_D : sD.getReg .x12 = BitVec.ofNat 64 (8192 + capValOff (l + 1) + gapOffset q) := by
        simp only [sD, runInstrs, capPairDstInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq,
          h23, h17, show (1#6 : BitVec 6).toNat = 1 by decide, show (5#6 : BitVec 6).toNat = 5 by decide]
        rw [bv64_shr q 1 (by omega), Nat.pow_one, bv64_add, bv64_shl _ 5 (by omega), bv64_add]
        exact congrArg (BitVec.ofNat 64) (by unfold gapOffset; omega)
      -- pc[330]: ECALL compress
      let dL0 := readBuffer s326 (8192 + capValOff l + gapOffset (2 * q)) 32
      let dR0 := readBuffer s326 (8192 + capValOff l + gapOffset (2 * q + 1)) 32
      have hinpD : readBuffer sD (8192 + capValOff l + 96 * q) 96 = binaryInput dL0 dR0 := by
        rw [(MemEqOutside.of_mem_eq hmemD 0 0).readBuffer_eq (by omega) (by omega)]
        rw [readBuffer_binary_of_zero_gap s326 _ (readBuffer_zero_of_bytes s326 _ 32 (fun b hb => hgap326 b hb))]
        simp only [dL0, dR0, gapOffset_even, gapOffset_odd, Nat.add_assoc]
      have hgo_al : gapOffset q % 8 = 0 := by unfold gapOffset; omega
      have hec := step_ecall_compress h768 oracle sD 330
        (8192 + capValOff l + 96 * q) (8192 + capValOff (l + 1) + gapOffset q) (by decide) hpcD rfl
        ((hregD .x5 (by decide) (by decide)).trans hfix326.x5)
        ((hregD .x11 (by decide) (by decide)).trans hfix326.x11)
        ((hregD .x13 (by decide) (by decide)).trans hfix326.x13)
        ((hregD .x10 (by decide) (by decide)).trans h10) hx12_D
        (by omega) (by omega) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
      rw [hinpD] at hec
      let sE := writeBits sD (BitVec.ofNat 64 (8192 + capValOff (l + 1) + gapOffset q)) (c96 (binaryInput dL0 dR0))
      have hpcE : sE.pc = pcWord 331 := by simp only [sE, writeBits, MachineState.setPC, hpcD, pcWord_add_four]
      have hregE : ∀ r, sE.getReg r = sD.getReg r := fun r => writeBits_register sD _ _ r
      have houtE : MemEqOutside s326 sE (8192 + capValOff (l + 1) + gapOffset q)
          (8192 + capValOff (l + 1) + gapOffset q + 32) :=
        (MemEqOutside.of_mem_eq hmemD _ _).trans (MemEqOutside_writeBits_digest sD _ _ (by omega))
      have hrbE : readBuffer sE (8192 + capValOff (l + 1) + gapOffset q) 32 = c96 (binaryInput dL0 dR0) :=
        writeBits_readBuffer_digest sD _ _
      -- pc[331..332]: ADDI x6, x2, 704; BEQ x29, x6, pc[336]
      have hst331 := step_ordinary oracle sE 331 (.ADDI .x6 .x2 704#12) (by decide) hpcE rfl (by intro h; cases h) rfl
      let sF := execInstrBr sE (.ADDI .x6 .x2 704#12)
      have hpcF : sF.pc = pcWord 332 := by simp only [sF, execInstrBr, MachineState.setPC, hpcE, pcWord_add_four]
      have hx6_F : sF.getReg .x6 = BitVec.ofNat 64 (68719475968 + 704) := by
        simp only [sF, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hregE, hregD .x2 (by decide) (by decide), hfix326.x2,
          se12_704, bv64_add]
      have hx29_F : sF.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := by
        simp only [sF, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x29), hregE,
          hregD .x29 (by decide) (by decide), h29]
      have hst332 := step_ordinary oracle sF 332 (.BEQ .x29 .x6 16#13) (by decide) hpcF rfl (by intro h; cases h) rfl
      let sG := execInstrBr sF (.BEQ .x29 .x6 16#13)
      have heq22 : (sF.getReg .x29 == sF.getReg .x6) = decide (l = 22) := by
        rw [hx29_F, hx6_F, bv64_beq_eq _ _ (by omega) (by omega)]
        exact decide_eq_decide.mpr (by omega)
      have hmemG : sG.mem = sE.mem := by
        simp only [sG, execInstrBr]; split <;> simp [sF, execInstrBr, mem_setPC, mem_setReg]
      have hregG : ∀ r, r ≠ .x6 → sG.getReg r = sD.getReg r := fun r h6 => by
        have : sG.getReg r = sF.getReg r := by simp only [sG, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
        rw [this]; simp only [sF, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm, hregE]
      have hdisj_src_dst : 8192 + capValOff l + 96 * q + 64 ≤ 8192 + capValOff (l + 1) + gapOffset q := by
        omega
      by_cases hl22 : l = 22
      · -- Root level l = 22: skip mask238, jump to pc[336]
        have hpcG : sG.pc = pcWord 336 := by
          simp only [sG, execInstrBr, heq22, hl22, decide_true, ite_true, MachineState.setPC, hpcF]
          exact pc_332_branch
        have houtG : MemEqOutside s326 sG (8192 + capValOff (l + 1) + gapOffset q)
            (8192 + capValOff (l + 1) + gapOffset q + 32) :=
          houtE.trans (MemEqOutside.of_mem_eq hmemG _ _)
        have hdL_G : readBuffer sG (8192 + capValOff l + gapOffset (2 * q)) 32 = dL0 :=
          houtG.readBuffer_eq (by unfold gapOffset; omega) (by rw [gapOffset_even]; omega)
        have hdR_G : readBuffer sG (8192 + capValOff l + gapOffset (2 * q + 1)) 32 = dR0 :=
          houtG.readBuffer_eq (by unfold gapOffset; omega) (by rw [gapOffset_odd]; omega)
        have htot := (hstPre.trans (hsD.trans hec)).trans (hst331.trans hst332)
        refine hloop_tail sG (kPre + 7) 1 [((binaryInput dL0 dR0).cast h768.symm, c96 (binaryInput dL0 dR0))]
          (by omega) (by simp [horT])
          (htot.eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl)) hpcG
          (hfix326.of_agree (fun r hr => (hregG r (isFixedReg_ne_of_false hr rfl)).trans
            (hregD r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))))
          (hcur326.of_agree (fun r hr => (hregG r (isCursorReg_ne_of_false hr rfl)).trans
            (hregD r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl))))
          ((hregG .x20 (by decide)).trans ((hregD .x20 (by decide) (by decide)).trans h20))
          ((hregG .x14 (by decide)).trans ((hregD .x14 (by decide) (by decide)).trans h14))
          ((hregG .x15 (by decide)).trans ((hregD .x15 (by decide) (by decide)).trans h15))
          ((hregG .x16 (by decide)).trans ((hregD .x16 (by decide) (by decide)).trans h16))
          ((hregG .x17 (by decide)).trans ((hregD .x17 (by decide) (by decide)).trans h17))
          ((hregG .x22 (by decide)).trans ((hregD .x22 (by decide) (by decide)).trans h22))
          ((hregG .x23 (by decide)).trans ((hregD .x23 (by decide) (by decide)).trans h23))
          ((hregG .x29 (by decide)).trans ((hregD .x29 (by decide) (by decide)).trans h29))
          ((hregG .x30 (by decide)).trans ((hregD .x30 (by decide) (by decide)).trans h30))
          (by simp only [horT, ite_true]; exact (houtG _ (by omega) (by omega)).trans hmk326)
          (fun _ => by
            dsimp only
            rw [hdL_G, hdR_G, ite_eq_left_iff.mpr (fun h => (h hl22).elim)]
            exact ⟨((MemEqOutside.of_mem_eq hmemG 0 0).readBuffer_eq (by omega) (by omega)).trans hrbE,
              InTrace.singleton h768 oracle _, hdL_fr, hdR_fr⟩)
          (fun h1 h2 => by simp [h1, h2] at horT)
          (fun a ha h1 h2 h3 => (houtG a ha h3).trans (hout326 a ha h1 h2))
      · -- l < 22: mask238 at pc[333..335] -> pc[336]
        have hpcG : sG.pc = pcWord 333 := by
          simp only [sG, execInstrBr, heq22, hl22, decide_false, Bool.false_eq_true, ite_false,
            MachineState.setPC, hpcF, pcWord_add_four]
        obtain ⟨sH, hsH, hpcH, hregH, hrbH_raw, houtGH⟩ :=
          step_mask238 oracle 333 .x12 sG (8192 + capValOff (l + 1) + gapOffset q)
            (by decide) (by decide) rfl rfl rfl hpcG
            ((hregG .x12 (by decide)).trans hx12_D)
            ((hregG .x9 (by decide)).trans ((hregD .x9 (by decide) (by decide)).trans hfix326.x9))
            (by omega) (by unfold MEMORY_BYTES; omega)
        have houtH : MemEqOutside s326 sH (8192 + capValOff (l + 1) + gapOffset q)
            (8192 + capValOff (l + 1) + gapOffset q + 32) :=
          (houtE.trans (MemEqOutside.of_mem_eq hmemG _ _)).trans houtGH
        have hrbH : readBuffer sH (8192 + capValOff (l + 1) + gapOffset q) 32 = mask238 (c96 (binaryInput dL0 dR0)) := by
          rw [hrbH_raw, (MemEqOutside.of_mem_eq hmemG 0 0).readBuffer_eq (by omega) (by omega), hrbE]
        have hdL_H : readBuffer sH (8192 + capValOff l + gapOffset (2 * q)) 32 = dL0 :=
          houtH.readBuffer_eq (by unfold gapOffset; omega) (by rw [gapOffset_even]; omega)
        have hdR_H : readBuffer sH (8192 + capValOff l + gapOffset (2 * q + 1)) 32 = dR0 :=
          houtH.readBuffer_eq (by unfold gapOffset; omega) (by rw [gapOffset_odd]; omega)
        have htot := (hstPre.trans (hsD.trans hec)).trans ((hst331.trans hst332).trans hsH)
        refine hloop_tail sH (kPre + 10) 1 [((binaryInput dL0 dR0).cast h768.symm, c96 (binaryInput dL0 dR0))]
          (by omega) (by simp [horT])
          (htot.eq_of rfl (by omega) rfl (by simp only [List.nil_append, List.append_nil]; rfl)) hpcH
          (hfix326.of_agree (fun r hr => (hregH r (isFixedReg_ne_of_false hr rfl)).trans
            ((hregG r (isFixedReg_ne_of_false hr rfl)).trans
              (hregD r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))))
          (hcur326.of_agree (fun r hr => (hregH r (isCursorReg_ne_of_false hr rfl)).trans
            ((hregG r (isCursorReg_ne_of_false hr rfl)).trans
              (hregD r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))))
          ((hregH .x20 (by decide)).trans ((hregG .x20 (by decide)).trans ((hregD .x20 (by decide) (by decide)).trans h20)))
          ((hregH .x14 (by decide)).trans ((hregG .x14 (by decide)).trans ((hregD .x14 (by decide) (by decide)).trans h14)))
          ((hregH .x15 (by decide)).trans ((hregG .x15 (by decide)).trans ((hregD .x15 (by decide) (by decide)).trans h15)))
          ((hregH .x16 (by decide)).trans ((hregG .x16 (by decide)).trans ((hregD .x16 (by decide) (by decide)).trans h16)))
          ((hregH .x17 (by decide)).trans ((hregG .x17 (by decide)).trans ((hregD .x17 (by decide) (by decide)).trans h17)))
          ((hregH .x22 (by decide)).trans ((hregG .x22 (by decide)).trans ((hregD .x22 (by decide) (by decide)).trans h22)))
          ((hregH .x23 (by decide)).trans ((hregG .x23 (by decide)).trans ((hregD .x23 (by decide) (by decide)).trans h23)))
          ((hregH .x29 (by decide)).trans ((hregG .x29 (by decide)).trans ((hregD .x29 (by decide) (by decide)).trans h29)))
          ((hregH .x30 (by decide)).trans ((hregG .x30 (by decide)).trans ((hregD .x30 (by decide) (by decide)).trans h30)))
          (by simp only [horT, ite_true]; exact (houtH _ (by omega) (by omega)).trans hmk326)
          (fun _ => by
            dsimp only
            rw [hdL_H, hdR_H, ite_eq_right_iff.mpr (fun h => (hl22 h).elim)]
            exact ⟨hrbH, InTrace.singleton h768 oracle _, hdL_fr, hdR_fr⟩)
          (fun h1 h2 => by simp [h1, h2] at horT)
          (fun a ha h1 h2 h3 => (houtH a ha h3).trans (hout326 a ha h1 h2))
    -- Now split on mL = mR (both marked) vs mL ≠ mR (frontier read via chk_read29_tail)
    by_cases hsame : mL = mR
    · -- Both mL = true and mR = true -> BEQ taken to pc[326]
      have hmLt : mL = true := by
        rw [← hsame, Bool.or_self] at horT; exact horT
      have hmRt : mR = true := by rw [← hsame, hmLt]
      have hpn_eq : pNext = pCur := by simp [pNext, hsame]
      have htn_eq : tNext = tCur := by simp [tNext, hsame]
      have hpc10 : s10.pc = pcWord 326 := by
        simp only [s10, execInstrBr, hx7_9, hx8_9, hsame, beq_self_eq_true, ite_true,
          MachineState.setPC, hpc9]; exact pc_321_branch
      have hmem10 : s10.mem = s8.mem := by
        simpa [s10, execInstrBr, hx7_9, hx8_9, hsame, MachineState.setPC] using hmem9
      have hreg10 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x28 → s10.getReg r = s.getReg r :=
        fun r h6 h7 h8 h10 h28 => by
          have : s10.getReg r = s9.getReg r := by
            simp [s10, execInstrBr, hx7_9, hx8_9, hsame, MachineState.getReg_setPC]
          exact this.trans ((hreg9 r h6 h10 h28).trans ((hreg8 r h6).trans (hreg6 r h6 h7 h8 h28)))
      have hx10_10 : s10.getReg .x10 = BitVec.ofNat 64 (8192 + capValOff l + 96 * q) := by
        have : s10.getReg .x10 = s9.getReg .x10 := by
          simp [s10, execInstrBr, hx7_9, hx8_9, hsame, MachineState.getReg_setPC]
        exact this.trans hx10_9
      have hout10 : MemEqOutside s s10 (4096 + capMarkOff (l + 1) + q) (4096 + capMarkOff (l + 1) + q + 1) :=
        hout8.trans (MemEqOutside.of_mem_eq hmem10 _ _)
      refine hcompress s10 13 (by decide) hs_309_321 hpc10
        (hfix.of_agree (fun r hr => hreg10 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        (by rw [hpn_eq, htn_eq]
            exact hcur.of_agree (fun r hr => hreg10 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
              (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
        hx10_10
        ((hreg10 .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20)
        ((hreg10 .x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx14)
        ((hreg10 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx15)
        ((hreg10 .x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx16)
        ((hreg10 .x17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx17)
        ((hreg10 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22)
        ((hreg10 .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23)
        ((hreg10 .x29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29)
        ((hreg10 .x30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30)
        (by simp only [MachineState.getByte, MachineState.getMem, hmem10]
            change s8.getByte _ = 1#8; rw [hbyte8, set_byte_read]; simp only [ite_true])
        (fun b hb => (hout10 _ (by omega) (by omega)).trans (hgap b hb))
        (fun h => by rw [hmLt] at h; cases h)
        (fun h => by rw [hmRt] at h; cases h)
        (fun a ha hne _ => hout10 a ha (by omega))
    · -- Frontier pair: mL ≠ mR -> fall through to pc[322..325]
      have hne_b : (mL != mR) = true := bne_iff_ne.mpr hsame
      have hpn_eq : pNext = pCur + 29 := by simp [pNext, hne_b]
      have htn_eq : tNext = tCur + 1 := by simp [tNext, hne_b]
      have hbeq_f : (s9.getReg .x7 == s9.getReg .x8) = false := by
        rw [hx7_9, hx8_9]
        cases hm1 : mL <;> cases hm2 : mR <;>
          first | decide | (exfalso; apply hsame; rw [hm1, hm2])
      have hpc10 : s10.pc = pcWord 322 := by
        simp only [s10, execInstrBr, hbeq_f, Bool.false_eq_true, ite_false, MachineState.setPC, hpc9, pcWord_add_four]
      have hmem10 : s10.mem = s8.mem := by
        simpa [s10, execInstrBr, hbeq_f, MachineState.setPC] using hmem9
      have hreg10 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x28 → s10.getReg r = s.getReg r :=
        fun r h6 h7 h8 h10 h28 => by
          have : s10.getReg r = s9.getReg r := by simp [s10, execInstrBr, hbeq_f, MachineState.getReg_setPC]
          exact this.trans ((hreg9 r h6 h10 h28).trans ((hreg8 r h6).trans (hreg6 r h6 h7 h8 h28)))
      have hx10_10 : s10.getReg .x10 = BitVec.ofNat 64 (8192 + capValOff l + 96 * q) := by
        have : s10.getReg .x10 = s9.getReg .x10 := by simp [s10, execInstrBr, hbeq_f, MachineState.getReg_setPC]
        exact this.trans hx10_9
      have hx7_10 : s10.getReg .x7 = if mL then 1#64 else 0#64 := by
        have : s10.getReg .x7 = s9.getReg .x7 := by simp [s10, execInstrBr, hbeq_f, MachineState.getReg_setPC]
        exact this.trans hx7_9
      -- pc[322..324]: set x12 = 8192 + capValOff l + gapOffset u where u = if !mL then 2*q else 2*q+1
      let u := if !mL then 2 * q else 2 * q + 1
      have hu_go : gapOffset u = if !mL then 96 * q else 96 * q + 32 := by
        cases hm1 : mL <;> simp [u, hm1, gapOffset_even, gapOffset_odd]
      have hst322 := step_ordinary oracle s10 322 (.ADDI .x12 .x10 0#12) (by decide) hpc10 rfl (by intro h; cases h) rfl
      let s11 := execInstrBr s10 (.ADDI .x12 .x10 0#12)
      have hpc11 : s11.pc = pcWord 323 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10, pcWord_add_four]
      have hx12_11 : s11.getReg .x12 = BitVec.ofNat 64 (8192 + capValOff l + 96 * q) := by
        simp only [s11, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hx10_10, se12_0, BitVec.add_zero]
      have hx7_11 : s11.getReg .x7 = if mL then 1#64 else 0#64 := by
        simp only [s11, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), hx7_10]
      have hst323 := step_ordinary oracle s11 323 (.BEQ .x7 .x0 8#13) (by decide) hpc11 rfl (by intro h; cases h) rfl
      let s12 := execInstrBr s11 (.BEQ .x7 .x0 8#13)
      have hreach325 : ∃ s325 kSel, kSel ≤ 3 ∧ StepsTo oracle s10 s325 kSel 0 [] ∧
          s325.pc = pcWord 325 ∧ s325.mem = s8.mem ∧
          s325.getReg .x12 = BitVec.ofNat 64 (8192 + capValOff l + gapOffset u) ∧
          (∀ r, r ≠ .x12 → s325.getReg r = s10.getReg r) := by
        cases hm1 : mL with
        | false =>
          have hx7z : s11.getReg .x7 = 0#64 := by simp only [hx7_11, hm1, Bool.false_eq_true, ite_false]
          refine ⟨s12, 2, by decide, by simpa using hst322.trans hst323, ?_, ?_, ?_, ?_⟩
          · simp only [s12, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true,
              MachineState.setPC, hpc11]; exact pc_323_branch
          · have h1211 : s12.mem = s11.mem := by
              simp only [s12, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true, mem_setPC]
            have h1110 : s11.mem = s10.mem := by simp only [s11, execInstrBr, mem_setPC, mem_setReg]
            exact h1211.trans (h1110.trans hmem10)
          · have : s12.getReg .x12 = s11.getReg .x12 := by
              simp [s12, execInstrBr, hx7z, getReg_x0, MachineState.getReg_setPC]
            simp only [this, hx12_11, hu_go, hm1, Bool.not_false, ite_true]
          · intro r hr12
            have : s12.getReg r = s11.getReg r := by
              simp [s12, execInstrBr, hx7z, getReg_x0, MachineState.getReg_setPC]
            rw [this]; simp only [s11, execInstrBr, MachineState.getReg_setPC]
            exact MachineState.getReg_setReg_ne _ _ _ _ hr12.symm
        | true =>
          have hx7o : s11.getReg .x7 = 1#64 := by simp only [hx7_11, hm1, ite_true]
          have hpc12 : s12.pc = pcWord 324 := by
            simp only [s12, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
              Bool.false_eq_true, ite_false, MachineState.setPC, hpc11, pcWord_add_four]
          have hst324 := step_ordinary oracle s12 324 (.ADDI .x12 .x10 32#12) (by decide) hpc12 rfl (by intro h; cases h) rfl
          let s13 := execInstrBr s12 (.ADDI .x12 .x10 32#12)
          refine ⟨s13, 3, by decide, by simpa using (hst322.trans hst323).trans hst324,
            by simp only [s13, execInstrBr, MachineState.setPC, hpc12, pcWord_add_four], ?_, ?_, ?_⟩
          · have h1312 : s13.mem = s12.mem := by simp only [s13, execInstrBr, mem_setPC, mem_setReg]
            have h1211 : s12.mem = s11.mem := by
              simp only [s12, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
                Bool.false_eq_true, ite_false, mem_setPC]
            have h1110 : s11.mem = s10.mem := by simp only [s11, execInstrBr, mem_setPC, mem_setReg]
            exact h1312.trans (h1211.trans (h1110.trans hmem10))
          · simp only [s13, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_eq (by decide)]
            have hx10_12 : s12.getReg .x10 = BitVec.ofNat 64 (8192 + capValOff l + 96 * q) := by
              have : s12.getReg .x10 = s11.getReg .x10 := by
                simp [s12, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
              rw [this]; simp only [s11, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x10), hx10_10]
            rw [hx10_12, se12_32, hu_go, hm1]
            simp only [Bool.not_true, Bool.false_eq_true, ite_false]
            change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _
            rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
          · intro r hr12
            simp only [s13, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_ne _ _ _ _ hr12.symm]
            have : s12.getReg r = s11.getReg r := by
              simp [s12, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
            rw [this]; simp only [s11, execInstrBr, MachineState.getReg_setPC]
            exact MachineState.getReg_setReg_ne _ _ _ _ hr12.symm
      obtain ⟨s325, kSel, hkSel, hsSel, hpc325, hmem272, hx12_272, hreg325⟩ := hreach325
      -- pc[325]: JAL x1, chk_read29_tail (pc[393])
      have hu_go_bd : gapOffset u + 32 ≤ 96 * q + 64 := by
        rw [hu_go]; cases mL <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] <;> omega
      have hcur325 : ProofCursor s0 input.proof.length pCur tCur s325 :=
        hcur.of_agree (fun r hr => (hreg325 r (isCursorReg_ne_of_false hr rfl)).trans
          (hreg10 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
            (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      have hout_s_325 : MemEqOutside s s325 (4096 + capMarkOff (l + 1) + q) (4096 + capMarkOff (l + 1) + q + 1) :=
        hout8.trans (MemEqOutside.of_mem_eq hmem272 _ _)
      have hread := step_call_read29_tail oracle s0 input.proof.length hvalid 325 s325 pCur tCur
        (8192 + capValOff l + gapOffset u) (by decide) rfl hpc325 hcur325
        (hhigh.trans (hout_s_325.mono (by omega) (by omega))) hx12_272 (by omega)
      cases hread with
      | rejected kR qR trR hrR hkR hqR hhR =>
        have htot := (hs_309_321.trans hsSel).halt hhR
        exact .rejected (13 + kSel + kR) qR trR ⟨hne_b, hrR⟩ (by omega) (by omega)
          (by simpa only [Nat.zero_add, List.nil_append] using htot)
      | continued s326 kR qR trR hkR hqR hs273 hp273 =>
        obtain ⟨rfl, rfl, hpc326, hcur326, hreg326, hrb_u, hout326⟩ := hp273
        have hreg326_10 : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x25 → r ≠ .x31 →
            s326.getReg r = s10.getReg r := fun r h1 h3 h4 h6 h7 h12 h25 h31 =>
          (hreg326 r h1 h3 h4 h6 h7 h12 h25 h31).trans (hreg325 r h12)
        have hout_s_326 : ∀ a : Nat, a < 2 ^ 64 →
            a ≠ 4096 + capMarkOff (l + 1) + q →
            (a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
            s326.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a) := fun a ha hne hout =>
          (hout326 a ha hout).trans (hout_s_325 a ha (by omega))
        have htot_pre := (hs_309_321.trans hsSel).trans hs273
        refine hcompress s326 (13 + kSel + kR) (by omega)
          (htot_pre.eq_of rfl (by omega) rfl (by simp only [List.append_nil]))
          hpc326
          (hfix.of_agree (fun r hr => (hreg326_10 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)).trans
            (hreg10 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
              (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))))
          (by rw [hpn_eq, htn_eq]; exact hcur326)
          ((hreg326_10 .x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx10_10)
          ((hreg326_10 .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20))
          ((hreg326_10 .x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx14))
          ((hreg326_10 .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx15))
          ((hreg326_10 .x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx16))
          ((hreg326_10 .x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx17))
          ((hreg326_10 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22))
          ((hreg326_10 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23))
          ((hreg326_10 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29))
          ((hreg326_10 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30))
          (by rw [hout326 _ (by omega) (by omega)]
              have h2 : s325.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) =
                  s8.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) := by
                simp [MachineState.getByte, MachineState.getMem, hmem272]
              rw [h2, hbyte8, set_byte_read]; simp only [ite_true])
          (fun b hb =>
            (hout_s_326 _ (by omega) (by omega) (Or.inr (by omega))).trans (hgap b hb))
          (fun hmLf => by simpa only [u, hmLf, Bool.not_false, ite_true] using hrb_u)
          (fun hmRf => by
            have hmLt : mL = true := by
              cases hm1 : mL
              · exfalso; apply hsame; rw [hm1, hmRf]
              · rfl
            simpa only [u, hmLt, Bool.not_true, Bool.false_eq_true, ite_false] using hrb_u)
          (fun a ha hne hout => by
            rcases hout with heq | hdisj
            · exact (hsame heq).elim
            · exact hout_s_326 a ha hne hdisj)

end CommitGolfCandidate
