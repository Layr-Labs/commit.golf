import CommitGolfCandidate.MoonCheckPos

/-! Symbolic execution of cap-walk geometry, `CapWalkInv`, and per-pair variable-width
frontier read + chained compression (`pc[222..247]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! #### Cap Walk Geometry and Invariant (`pc[209..267]`) -/

def pairFrontierCount (positions : Positions) (l n : Nat) : Nat :=
  ((Finset.range n).filter
    (fun q => capMark positions l (2 * q) != capMark positions l (2 * q + 1))).card

def pairMarkedNextCount (positions : Positions) (l n : Nat) : Nat :=
  ((Finset.range n).filter (fun q => capMark positions (l + 1) q)).card

def capFrontierBytesPrefix (positions : Positions) (step : Nat) : Nat :=
  ∑ d ∈ Finset.range step, levelBodyBytes (14 + d) * levelFrontierCount positions (14 + d)

def capFrontierTailBitsPrefix (positions : Positions) (step : Nat) : Nat :=
  ∑ d ∈ Finset.range step, levelTailBits (14 + d) * levelFrontierCount positions (14 + d)

def capFrontierBytes (positions : Positions) : Nat :=
  capFrontierBytesPrefix positions 10

def capFrontierTailBits (positions : Positions) : Nat :=
  capFrontierTailBitsPrefix positions 10

theorem pairFrontierCount_zero (positions : Positions) (l : Nat) :
    pairFrontierCount positions l 0 = 0 := by
  simp [pairFrontierCount]

theorem pairFrontierCount_succ (positions : Positions) (l q : Nat) :
    pairFrontierCount positions l (q + 1) =
      pairFrontierCount positions l q +
        if (capMark positions l (2 * q) != capMark positions l (2 * q + 1)) then 1 else 0 := by
  unfold pairFrontierCount
  rw [Finset.range_add_one, Finset.filter_insert]
  have hnot : q ∉ (Finset.range q).filter
      (fun x => capMark positions l (2 * x) != capMark positions l (2 * x + 1)) := by
    simp
  split <;> simp [Finset.card_insert_of_notMem, hnot]

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
  have hnot : q ∉ (Finset.range q).filter (fun x => capMark positions (l + 1) x) := by simp
  split <;> simp [Finset.card_insert_of_notMem, hnot]

theorem pairMarkedNextCount_add_odd_eq (positions : Positions) (l : Nat) (hl : 14 ≤ l) :
    pairMarkedNextCount positions l (levelSize l / 2) +
      (if levelSize l % 2 = 1 ∧ capMark positions l (2 * (levelSize l / 2)) = true then 1 else 0) =
      levelMarkedCount positions (l + 1) := by
  unfold pairMarkedNextCount levelMarkedCount
  have hstep : levelSize (l + 1) = (levelSize l + 1) / 2 := levelSize_step l (by omega)
  rw [hstep]
  rcases Nat.even_or_odd' (levelSize l) with ⟨k, hk | hk⟩
  · have hdiv : levelSize l / 2 = k := by omega
    have hnext : (levelSize l + 1) / 2 = k := by omega
    have hmod : ¬ (levelSize l % 2 = 1) := by omega
    simp [hdiv, hnext, hmod]
  · have hdiv : levelSize l / 2 = k := by omega
    have hnext : (levelSize l + 1) / 2 = k + 1 := by omega
    have hmod : levelSize l % 2 = 1 := by omega
    rw [hdiv, hnext, Finset.range_add_one, Finset.filter_insert]
    have hnot : k ∉ (Finset.range k).filter (fun q => capMark positions (l + 1) q = true) := by simp
    have hcm : capMark positions (l + 1) k = capMark positions l (2 * k) := by
      rw [capMark_succ positions l k hl, if_neg (by omega), if_pos (by omega)]
    rw [hcm]
    cases hm : capMark positions l (2 * k) <;> simp [hmod, Finset.card_insert_of_notMem, hnot]

theorem capFrontierBytesPrefix_zero (positions : Positions) :
    capFrontierBytesPrefix positions 0 = 0 := by
  simp [capFrontierBytesPrefix]

theorem capFrontierBytesPrefix_succ (positions : Positions) (step : Nat) :
    capFrontierBytesPrefix positions (step + 1) =
      capFrontierBytesPrefix positions step +
        levelBodyBytes (14 + step) * levelFrontierCount positions (14 + step) :=
  Finset.sum_range_succ _ step

theorem capFrontierBytesPrefix_10 (positions : Positions) :
    capFrontierBytesPrefix positions 10 = capFrontierBytes positions := rfl

theorem capFrontierBytesPrefix_mono (positions : Positions) {a b : Nat} (hab : a ≤ b) :
    capFrontierBytesPrefix positions a ≤ capFrontierBytesPrefix positions b :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

theorem capFrontierTailBitsPrefix_zero (positions : Positions) :
    capFrontierTailBitsPrefix positions 0 = 0 := by
  simp [capFrontierTailBitsPrefix]

theorem capFrontierTailBitsPrefix_succ (positions : Positions) (step : Nat) :
    capFrontierTailBitsPrefix positions (step + 1) =
      capFrontierTailBitsPrefix positions step +
        levelTailBits (14 + step) * levelFrontierCount positions (14 + step) :=
  Finset.sum_range_succ _ step

theorem capFrontierTailBitsPrefix_10 (positions : Positions) :
    capFrontierTailBitsPrefix positions 10 = capFrontierTailBits positions := rfl

theorem capFrontierTailBitsPrefix_mono (positions : Positions) {a b : Nat} (hab : a ≤ b) :
    capFrontierTailBitsPrefix positions a ≤ capFrontierTailBitsPrefix positions b :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hab)

theorem capMarkOff_step_le (l : Nat) (hl1 : 14 ≤ l) (hl2 : l < 24) :
    capMarkOff l + levelSize l ≤ capMarkOff (l + 1) := by
  interval_cases l <;> decide

theorem capMarkOff_mono {l1 l2 : Nat} (h1 : 14 ≤ l1) (hle : l1 ≤ l2) (h2 : l2 ≤ 24) :
    capMarkOff l1 ≤ capMarkOff l2 := by
  have : l1 ≤ 24 := by omega
  interval_cases l1 <;> interval_cases l2 <;> decide

theorem capValOff_step_eq (l : Nat) (hl1 : 14 ≤ l) (hl2 : l < 24) :
    capValOff (l + 1) = capValOff l + ((levelSize l + 1) / 2) * 96 := by
  interval_cases l <;> decide

theorem capValOff_mono {l1 l2 : Nat} (h1 : 14 ≤ l1) (hle : l1 ≤ l2) (h2 : l2 ≤ 24) :
    capValOff l1 ≤ capValOff l2 := by
  have : l1 ≤ 24 := by omega
  interval_cases l1 <;> interval_cases l2 <;> decide

theorem capValOff_lt_65984 (l : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 24) :
    capValOff l + levelBytes l ≤ 65984 := by
  interval_cases l <;> decide

theorem capValOff_mod8 (l : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 24) :
    capValOff l % 8 = 0 := by
  interval_cases l <;> decide

theorem capMarkOff_lt_5512 (l : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 24) :
    4096 + capMarkOff l + levelSize l ≤ 5512 := by
  interval_cases l <;> decide

theorem capValOff_add_levelBytes_eq (a : Nat) (ha1 : 14 ≤ a) (ha2 : a < 24) :
    capValOff a + levelBytes a = capValOff (a + 1) := by
  interval_cases a <;> decide

theorem capValOff_add_levelBytes_le {a b : Nat} (ha : 14 ≤ a) (hab : a < b) (hb : b ≤ 24) :
    capValOff a + levelBytes a ≤ capValOff b := by
  have : a < 24 := by omega
  interval_cases a <;> interval_cases b <;> decide

theorem levelSize_cap_le683 (a : Nat) (ha1 : 14 ≤ a) (ha2 : a < 24) :
    levelSize a ≤ 683 := by
  interval_cases a <;> decide

theorem cap_lt23_of_odd (a : Nat) (ha1 : 14 ≤ a) (ha2 : a < 24)
    (hodd : levelSize a % 2 = 1) : a < 23 := by
  interval_cases a <;> first | decide | (exfalso; revert hodd; decide)

theorem levelSize_cap_pairs_pos (l : Nat) (hl1 : 14 ≤ l) (hl2 : l < 24) :
    0 < levelSize l / 2 := by
  interval_cases l <;> decide

theorem cap_level_steps_sum :
    (∑ step ∈ Finset.range 10, (118 + 320 * (levelSize (14 + step) / 2))) + 2 ≤ 250000 := by
  decide

theorem cap_level_chains_sum :
    ∑ step ∈ Finset.range 10, levelChain (15 + step) = 30 := by
  decide

theorem cap_gapOffset_bound (l idx : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 24)
    (hidx : idx < levelSize l) :
    gapOffset idx + 32 ≤ levelBytes l := by
  by_cases h24 : l = 24
  · subst h24
    have : idx = 0 := by rw [levelSize_24] at hidx; omega
    subst this; decide
  · exact gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx

theorem cap_val_next_bound (l idx : Nat) (hl1 : 14 ≤ l) (hl2 : l < 24)
    (hidx : idx < levelSize (l + 1)) :
    capValOff (l + 1) + gapOffset idx + 32 ≤ 65984 := by
  have h1 := cap_gapOffset_bound (l + 1) idx (by omega) (by omega) hidx
  have h2 := capValOff_lt_65984 (l + 1) (by omega) (by omega)
  omega

theorem cap_val_next_lt_next (l idx : Nat) (hl1 : 14 ≤ l) (hl2 : l < 23)
    (hidx : idx < levelSize (l + 1)) :
    capValOff (l + 1) + gapOffset idx + 32 ≤ capValOff (l + 2) := by
  have h1 := cap_gapOffset_bound (l + 1) idx (by omega) (by omega) hidx
  have h2 : capValOff (l + 1) + levelBytes (l + 1) = capValOff (l + 2) := by
    interval_cases l <;> decide
  omega

/-- Cap-walk invariant after completing `step` cap levels (`0 ≤ step ≤ 10`, levels `14 .. 14 + step - 1`). -/
structure CapWalkInv (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (sPos : MachineState) (step : Nat) (s : MachineState)
    (tr : CompressionReplies) : Prop where
  fixed : CheckFixedRegs s
  cursor : ProofCursor (submission.initialState .check input) input.proof.length
    (posRecordOff input.positions input.positions.card + capFrontierBytesPrefix input.positions step)
    (posTailBitsOff input.positions input.positions.card + capFrontierTailBitsPrefix input.positions step) s
  high : HighMemPreserved (submission.initialState .check input) s
  zero : ChainScratchZero s
  pc : s.pc = if step = 10 then pcWord 268 else pcWord 211
  x29 : s.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (14 + step))
  x30 : s.getReg .x30 = BitVec.ofNat 64 (68719475728 + 960)
  mark_cur : step < 10 → ∀ idx < levelSize (14 + step),
    s.getByte (BitVec.ofNat 64 (4096 + capMarkOff (14 + step) + idx)) =
      if capMark input.positions (14 + step) idx then 1#8 else 0#8
  mark_hi_zero : step < 10 → ∀ a, 4096 + capMarkOff (14 + step + 1) ≤ a → a < 5512 →
    s.getByte (BitVec.ofNat 64 a) = 0#8
  val_cur_gap_zero : step < 10 → ∀ q < (levelSize (14 + step) + 1) / 2, ∀ b < 32,
    s.getByte (BitVec.ofNat 64 (8192 + capValOff (14 + step) + 96 * q + 64 + b)) = 0#8
  val_cur_odd_right_zero : step < 10 → levelSize (14 + step) % 2 = 1 → ∀ b < 32,
    s.getByte (BitVec.ofNat 64 (8192 + capValOff (14 + step) + 96 * (levelSize (14 + step) / 2) + 32 + b)) = 0#8
  val_hi_zero : step < 10 → ∀ a, 8192 + capValOff (14 + step + 1) ≤ a → a < 8192 + 65984 →
    s.getByte (BitVec.ofNat 64 a) = 0#8
  val14_marked : ∀ c < 683, capMark input.positions 14 c = true →
    readBuffer s (8192 + capValOff 14 + gapOffset c) 32 = readBuffer sPos (8192 + gapOffset c) 32
  levels_done : ∀ d < step,
    let l := 14 + d
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let s0 := submission.initialState .check input
    let pBase := posRecordOff input.positions input.positions.card
    let bBase := posTailBitsOff input.positions input.positions.card
    (∀ q < levelSize l / 2, capMark input.positions (l + 1) q = true →
      let dL := readBuffer s (8192 + capValOff l + gapOffset (2 * q)) 32
      let dR := readBuffer s (8192 + capValOff l + gapOffset (2 * q + 1)) 32
      let pAt := pBase + capFrontierBytesPrefix input.positions d +
        levelBodyBytes l * pairFrontierCount input.positions l q
      let bAt := bBase + capFrontierTailBitsPrefix input.positions d +
        levelTailBits l * pairFrontierCount input.positions l q
      readBuffer s (8192 + capValOff (l + 1) + gapOffset q) 32 = chainHash c96 (l + 1) dL dR ∧
      (∀ x ∈ chainInputs c96 (l + 1) dL dR, InTrace h768 oracle tr x) ∧
      (capMark input.positions l (2 * q) = false → dL = proofDigestVar s0 input.proof.length (11341403200 + pAt) bAt l) ∧
      (capMark input.positions l (2 * q + 1) = false → dR = proofDigestVar s0 input.proof.length (11341403200 + pAt) bAt l)) ∧
    (levelSize l % 2 = 1 → capMark input.positions l (2 * (levelSize l / 2)) = true →
      let dL := readBuffer s (8192 + capValOff l + gapOffset (2 * (levelSize l / 2))) 32
      readBuffer s (8192 + capValOff (l + 1) + gapOffset (levelSize l / 2)) 32 = chainHash c96 (l + 1) dL 0 ∧
      ∀ x ∈ chainInputs c96 (l + 1) dL 0, InTrace h768 oracle tr x)

private theorem pc_247_branch : pcWord 247 + signExtend13 8092#13 = pcWord 222 := by decide
private theorem pc_227_branch : pcWord 227 + signExtend13 76#13 = pcWord 246 := by decide
private theorem pc_234_branch : pcWord 234 + signExtend13 24#13 = pcWord 240 := by decide
private theorem pc_236_branch : pcWord 236 + signExtend13 8#13 = pcWord 238 := by decide

private theorem bne_mem_cap (st : MachineState) (r1 r2 : Reg) (off : BitVec 13) :
    (execInstrBr st (.BNE r1 r2 off)).mem = st.mem := by
  simp only [execInstrBr]; split <;> rfl

private theorem bne_getReg_cap (st : MachineState) (r1 r2 : Reg) (off : BitVec 13) (r : Reg) :
    (execInstrBr st (.BNE r1 r2 off)).getReg r = st.getReg r := by
  simp only [execInstrBr]; split <;> simp only [MachineState.getReg_setPC]

private theorem se12_72_cap : signExtend12 72#12 = 72#64 := by decide
private theorem checkInstr_239 : checkInstr 239 = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (297 - 239)))) := rfl
private theorem checkInstr_245 : checkInstr 245 = .base (.JAL .x1 (BitVec.ofNat 21 (4 * (325 - 245)))) := rfl

private def capPairAddrInstrs : List Instr :=
  [.SLLI .x6 .x23 6#6, .SLLI .x28 .x23 5#6, .ADD .x10 .x6 .x28, .ADD .x10 .x16 .x10]

private def capPairDstInstrs : List Instr :=
  [.SRLI .x6 .x23 1#6, .ADD .x6 .x23 .x6, .SLLI .x6 .x6 5#6, .ADD .x12 .x17 .x6]

/-- One pair iteration `q < levelSize l / 2` in cap level `l ∈ 14..23` (`pc[222..247]`). -/
theorem step_cap_pair (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (l q pCur bCur : Nat) (hl1 : 14 ≤ l) (hl2 : l < 24) (hq : q < levelSize l / 2)
    (s : MachineState) (hpc : s.pc = pcWord 222)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pCur bCur s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s)
    (hzero : ChainScratchZero s)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (levelSize l))
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l))
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)))
    (hx16 : s.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l))
    (hx17 : s.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)))
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2))
    (hx23 : s.getReg .x23 = BitVec.ofNat 64 q)
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475728 + 960))
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
    let pNext := pCur + if (mL != mR) then levelBodyBytes l else 0
    let bNext := bCur + if (mL != mR) then levelTailBits l else 0
    PhaseOutcome oracle s 320 (if (mL || mR) then levelChain (l + 1) else 0)
      ((mL != mR) = true ∧
        input.proof.length < pCur + levelBodyBytes l + tailBytesBits (bCur + levelTailBits l))
      (fun s' calls tr =>
        calls ≤ (if (mL || mR) then levelChain (l + 1) else 0) ∧
        s'.pc = (if q + 1 = levelSize l / 2 then pcWord 248 else pcWord 222) ∧
        CheckFixedRegs s' ∧
        ProofCursor s0 input.proof.length pNext bNext s' ∧
        ChainScratchZero s' ∧
        s'.getReg .x20 = BitVec.ofNat 64 (levelSize l) ∧
        s'.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
        s'.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
        s'.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) ∧
        s'.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) ∧
        s'.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) ∧
        s'.getReg .x23 = BitVec.ofNat 64 (q + 1) ∧
        s'.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) ∧
        s'.getReg .x30 = BitVec.ofNat 64 (68719475728 + 960) ∧
        s'.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) =
          (if (mL || mR) then 1#8 else 0#8) ∧
        (mL || mR = true →
          let dL := readBuffer s' (8192 + capValOff l + gapOffset (2 * q)) 32
          let dR := readBuffer s' (8192 + capValOff l + gapOffset (2 * q + 1)) 32
          readBuffer s' (8192 + capValOff (l + 1) + gapOffset q) 32 = chainHash c96 (l + 1) dL dR ∧
          (∀ x ∈ chainInputs c96 (l + 1) dL dR, InTrace h768 oracle tr x) ∧
          (mL = false → dL = proofDigestVar s0 input.proof.length (11341403200 + pCur) bCur l) ∧
          (mR = false → dR = proofDigestVar s0 input.proof.length (11341403200 + pCur) bCur l)) ∧
        (mL = false → mR = false → s'.mem = s.mem) ∧
        (∀ a : Nat, a < 2 ^ 64 →
          (a < 512 ∨ 608 ≤ a) →
          a ≠ 4096 + capMarkOff (l + 1) + q →
          (mL = mR ∨
            let u := if !mL then 2 * q else 2 * q + 1
            a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
          (a < 8192 + capValOff (l + 1) + gapOffset q ∨ 8192 + capValOff (l + 1) + gapOffset q + 32 ≤ a) →
          s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a))) := by
  intro s0 c96 mL mR pNext bNext
  have hplen_bd : input.proof.length ≤ 8556390424 := hvalid
  have hls_le : levelSize l ≤ 683 := levelSize_cap_le683 l hl1 hl2
  have hpairs_lt : levelSize l / 2 ≤ 341 := by omega
  have hq_lt_next : q < levelSize (l + 1) := by rw [levelSize_step l (by omega)]; omega
  have hmo_l_bd := capMarkOff_lt_5512 l hl1 (by omega)
  have hmo_n_bd := capMarkOff_lt_5512 (l + 1) (by omega) (by omega)
  have hvo_l_bd := capValOff_lt_65984 l hl1 (by omega)
  have hvo_n_bd := capValOff_lt_65984 (l + 1) (by omega) (by omega)
  have hvo_step := capValOff_step_eq l hl1 hl2
  have hvo_l_al := capValOff_mod8 l hl1 (by omega)
  have hvo_n_al := capValOff_mod8 (l + 1) (by omega) (by omega)
  have hdst_bd : capValOff (l + 1) + gapOffset q + 32 ≤ 65984 := cap_val_next_bound l q hl1 hl2 hq_lt_next
  have hsrc_le_next : capValOff l + 96 * q + 96 ≤ capValOff (l + 1) := by
    rw [hvo_step]; omega
  -- pc[222..227]: load mL, mR, compute mL || mR, branch if 0
  have hst222 := step_ordinary oracle s 222 (.SLLI .x6 .x23 1#6) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.SLLI .x6 .x23 1#6)
  have hpc1 : s1.pc = pcWord 223 := by simp only [s1, execInstrBr, MachineState.setPC, hpc, pcWord_add_four]
  have hst223 := step_ordinary oracle s1 223 (.ADD .x6 .x14 .x6) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADD .x6 .x14 .x6)
  have hpc2 : s2.pc = pcWord 224 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hx6_2 : s2.getReg .x6 = BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx14, hx23,
      show (1#6 : BitVec 6).toNat = 1 by decide]
    rw [bv64_shl q 1 (by omega), bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hmem2 : s2.mem = s.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg2 : ∀ r, r ≠ .x6 → s2.getReg r = s.getReg r := fun r h6 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
  have ha224 : s2.getReg .x6 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) := by
    rw [hx6_2, se12_0, BitVec.add_zero]
  have hv224 : memoryArgumentsValid s2 (.LBU .x7 .x6 0#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha224]
    exact accessValid_ofNat (4096 + capMarkOff l + 2 * q) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst224 := step_ordinary oracle s2 224 (.LBU .x7 .x6 0#12) (by decide) hpc2 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv224])
  let s3 := execInstrBr s2 (.LBU .x7 .x6 0#12)
  have hpc3 : s3.pc = pcWord 225 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hx6_3 : s3.getReg .x6 = BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6), hx6_2]
  have ha225 : s3.getReg .x6 + signExtend12 1#12 = BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1)) := by
    rw [hx6_3, se12_1]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 1 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv225 : memoryArgumentsValid s3 (.LBU .x8 .x6 1#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha225]
    exact accessValid_ofNat (4096 + capMarkOff l + (2 * q + 1)) 1 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst225 := step_ordinary oracle s3 225 (.LBU .x8 .x6 1#12) (by decide) hpc3 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv225])
  let s4 := execInstrBr s3 (.LBU .x8 .x6 1#12)
  have hpc4 : s4.pc = pcWord 226 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hmem4 : s4.mem = s.mem := by
    simpa [s4, s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
  have hx7_4 : s4.getReg .x7 = if mL then 1#64 else 0#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x7)]
    simp only [s3, execInstrBr, MachineState.getReg_setPC, ha224]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hb : s2.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q)) = if mL then 1#8 else 0#8 := by
      simpa only [MachineState.getByte, MachineState.getMem, hmem2] using hmL
    rw [hb, bool_byte_zeroExtend]
  have hx8_4 : s4.getReg .x8 = if mR then 1#64 else 0#64 := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, ha225]
    rw [MachineState.getReg_setReg_eq (by decide)]
    have hmem3 : s3.mem = s.mem := by simpa [s3, execInstrBr, mem_setPC, mem_setReg] using hmem2
    have hb : s3.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1))) = if mR then 1#8 else 0#8 := by
      simpa only [MachineState.getByte, MachineState.getMem, hmem3] using hmR
    rw [hb, bool_byte_zeroExtend]
  have hst226 := step_ordinary oracle s4 226 (.OR .x28 .x7 .x8) (by decide) hpc4 rfl (by intro h; cases h) rfl
  let s5 := execInstrBr s4 (.OR .x28 .x7 .x8)
  have hpc5 : s5.pc = pcWord 227 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
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
  have hst227 := step_ordinary oracle s5 227 (.BEQ .x28 .x0 76#13) (by decide) hpc5 rfl (by intro h; cases h) rfl
  let s6 := execInstrBr s5 (.BEQ .x28 .x0 76#13)
  have hs_222_227 : StepsTo oracle s s6 6 0 [] := by
    simpa using (((hst222.trans hst223).trans hst224).trans (hst225.trans hst226)).trans hst227
  -- Common tail pc[246..247]
  have hloop_tail : ∀ (s246 : MachineState) (kPre qPre : Nat) (trPre : CompressionReplies),
      kPre ≤ 318 → qPre ≤ (if (mL || mR) then levelChain (l + 1) else 0) →
      StepsTo oracle s s246 kPre qPre trPre →
      s246.pc = pcWord 246 →
      CheckFixedRegs s246 →
      ProofCursor s0 input.proof.length pNext bNext s246 →
      ChainScratchZero s246 →
      s246.getReg .x20 = BitVec.ofNat 64 (levelSize l) →
      s246.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) →
      s246.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) →
      s246.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) →
      s246.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) →
      s246.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) →
      s246.getReg .x23 = BitVec.ofNat 64 q →
      s246.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) →
      s246.getReg .x30 = BitVec.ofNat 64 (68719475728 + 960) →
      s246.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) =
        (if (mL || mR) then 1#8 else 0#8) →
      (mL || mR = true →
        let dL := readBuffer s246 (8192 + capValOff l + gapOffset (2 * q)) 32
        let dR := readBuffer s246 (8192 + capValOff l + gapOffset (2 * q + 1)) 32
        readBuffer s246 (8192 + capValOff (l + 1) + gapOffset q) 32 = chainHash c96 (l + 1) dL dR ∧
        (∀ x ∈ chainInputs c96 (l + 1) dL dR, InTrace h768 oracle trPre x) ∧
        (mL = false → dL = proofDigestVar s0 input.proof.length (11341403200 + pCur) bCur l) ∧
        (mR = false → dR = proofDigestVar s0 input.proof.length (11341403200 + pCur) bCur l)) →
      (mL = false → mR = false → s246.mem = s.mem) →
      (∀ a : Nat, a < 2 ^ 64 →
        (a < 512 ∨ 608 ≤ a) →
        a ≠ 4096 + capMarkOff (l + 1) + q →
        (mL = mR ∨
          let u := if !mL then 2 * q else 2 * q + 1
          a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
        (a < 8192 + capValOff (l + 1) + gapOffset q ∨ 8192 + capValOff (l + 1) + gapOffset q + 32 ≤ a) →
        s246.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) →
      PhaseOutcome oracle s 320 (if (mL || mR) then levelChain (l + 1) else 0)
        ((mL != mR) = true ∧
          input.proof.length < pCur + levelBodyBytes l + tailBytesBits (bCur + levelTailBits l))
        (fun s' calls tr =>
          calls ≤ (if (mL || mR) then levelChain (l + 1) else 0) ∧
          s'.pc = (if q + 1 = levelSize l / 2 then pcWord 248 else pcWord 222) ∧
          CheckFixedRegs s' ∧
          ProofCursor s0 input.proof.length pNext bNext s' ∧
          ChainScratchZero s' ∧
          s'.getReg .x20 = BitVec.ofNat 64 (levelSize l) ∧
          s'.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
          s'.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
          s'.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) ∧
          s'.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) ∧
          s'.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) ∧
          s'.getReg .x23 = BitVec.ofNat 64 (q + 1) ∧
          s'.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) ∧
          s'.getReg .x30 = BitVec.ofNat 64 (68719475728 + 960) ∧
          s'.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) =
            (if (mL || mR) then 1#8 else 0#8) ∧
          (mL || mR = true →
            let dL := readBuffer s' (8192 + capValOff l + gapOffset (2 * q)) 32
            let dR := readBuffer s' (8192 + capValOff l + gapOffset (2 * q + 1)) 32
            readBuffer s' (8192 + capValOff (l + 1) + gapOffset q) 32 = chainHash c96 (l + 1) dL dR ∧
            (∀ x ∈ chainInputs c96 (l + 1) dL dR, InTrace h768 oracle tr x) ∧
            (mL = false → dL = proofDigestVar s0 input.proof.length (11341403200 + pCur) bCur l) ∧
            (mR = false → dR = proofDigestVar s0 input.proof.length (11341403200 + pCur) bCur l)) ∧
          (mL = false → mR = false → s'.mem = s.mem) ∧
          (∀ a : Nat, a < 2 ^ 64 →
            (a < 512 ∨ 608 ≤ a) →
            a ≠ 4096 + capMarkOff (l + 1) + q →
            (mL = mR ∨
              let u := if !mL then 2 * q else 2 * q + 1
              a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
            (a < 8192 + capValOff (l + 1) + gapOffset q ∨ 8192 + capValOff (l + 1) + gapOffset q + 32 ≤ a) →
            s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a))) := by
    intro s246 kPre qPre trPre hkPre hqPre hstPre hpc246 hfix246 hcur246 hzero246
      h20 h14 h15 h16 h17 h22 h23 h29 h30 hmk246 hval246 hmeq246 hout246
    have hst246 := step_ordinary oracle s246 246 (.ADDI .x23 .x23 1#12) (by decide) hpc246 rfl (by intro h; cases h) rfl
    let s247 := execInstrBr s246 (.ADDI .x23 .x23 1#12)
    have hpc247 : s247.pc = pcWord 247 := by simp only [s247, execInstrBr, MachineState.setPC, hpc246, pcWord_add_four]
    have hx23_247 : s247.getReg .x23 = BitVec.ofNat 64 (q + 1) := by
      simp only [s247, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), h23, se12_1]
      change BitVec.ofNat 64 q + BitVec.ofNat 64 1 = _; exact bv64_add q 1
    have hx22_247 : s247.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) := by
      simp only [s247, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x23 ≠ .x22), h22]
    have hst247 := step_ordinary oracle s247 247 (.BNE .x23 .x22 8092#13) (by decide) hpc247 rfl (by intro h; cases h) rfl
    let sFin := execInstrBr s247 (.BNE .x23 .x22 8092#13)
    have hmemFin : sFin.mem = s246.mem :=
      (bne_mem_cap s247 .x23 .x22 8092#13).trans (by simp [s247, execInstrBr, mem_setPC, mem_setReg])
    have hregFin : ∀ r, r ≠ .x23 → sFin.getReg r = s246.getReg r := fun r h23r => by
      rw [bne_getReg_cap s247 .x23 .x22 8092#13 r]
      simp only [s247, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h23r.symm
    have hx23Fin : sFin.getReg .x23 = BitVec.ofNat 64 (q + 1) :=
      (bne_getReg_cap s247 .x23 .x22 8092#13 .x23).trans hx23_247
    have hne_iff : (s247.getReg .x23 != s247.getReg .x22) = decide (q + 1 ≠ levelSize l / 2) := by
      rw [hx23_247, hx22_247]
      exact bv64_bne_eq _ _ (by omega) (by omega)
    have hpcFin : sFin.pc = if q + 1 = levelSize l / 2 then pcWord 248 else pcWord 222 := by
      by_cases hdone : q + 1 = levelSize l / 2
      · simp only [sFin, execInstrBr, hne_iff, hdone, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ite_false, ite_true, MachineState.setPC, hpc247, pcWord_add_four]
      · simp only [sFin, execInstrBr, hne_iff, hdone, ne_eq, not_false_eq_true, decide_true,
          ite_true, ite_false, MachineState.setPC, hpc247]; exact pc_247_branch
    have hrb_eq : ∀ addr n, readBuffer sFin addr n = readBuffer s246 addr n := fun addr n => by
      apply readBuffer_congr2; intro j _; simp [MachineState.getByte, MachineState.getMem, hmemFin]
    refine .continued sFin (kPre + 2) qPre trPre (by omega) hqPre
      ((hstPre.trans (hst246.trans hst247)).eq_of rfl (by omega) (by omega) (by simp))
      ⟨hqPre, hpcFin,
       hfix246.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)),
       hcur246.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)),
       hzero246.of_mem_eq hmemFin,
       (hregFin .x20 (by decide)).trans h20, (hregFin .x14 (by decide)).trans h14,
       (hregFin .x15 (by decide)).trans h15, (hregFin .x16 (by decide)).trans h16,
       (hregFin .x17 (by decide)).trans h17, (hregFin .x22 (by decide)).trans h22,
       hx23Fin, (hregFin .x29 (by decide)).trans h29, (hregFin .x30 (by decide)).trans h30,
       by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hmk246,
       fun hm => by simpa only [hrb_eq] using hval246 hm,
       fun h1 h2 => hmemFin.trans (hmeq246 h1 h2),
       fun a ha h512 h1 h2 h3 => by simpa [MachineState.getByte, MachineState.getMem, hmemFin] using hout246 a ha h512 h1 h2 h3⟩
  -- Case split on (mL || mR)
  by_cases hor : (mL || mR) = false
  · -- Branch A: neither child marked -> jump straight to pc[246]
    have hmLf : mL = false := (Bool.or_eq_false_iff.mp hor).1
    have hmRf : mR = false := (Bool.or_eq_false_iff.mp hor).2
    have hpn_eq : pNext = pCur := by simp [pNext, hmLf, hmRf]
    have hbn_eq : bNext = bCur := by simp [bNext, hmLf, hmRf]
    have hx28z : s5.getReg .x28 = 0#64 := by simp only [hx28_5, hor, Bool.false_eq_true, ite_false]
    have hpc6 : s6.pc = pcWord 246 := by
      simp only [s6, execInstrBr, hx28z, getReg_x0, beq_self_eq_true, ite_true,
        MachineState.setPC, hpc5]; exact pc_227_branch
    have hmem6 : s6.mem = s.mem := by
      simpa [s6, execInstrBr, hx28z, getReg_x0, MachineState.setPC] using hmem5
    have hreg6 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x28 → s6.getReg r = s.getReg r := fun r h6 h7 h8 h28 => by
      have : s6.getReg r = s5.getReg r := by simp [s6, execInstrBr, hx28z, getReg_x0, MachineState.getReg_setPC]
      exact this.trans (hreg5 r h6 h7 h8 h28)
    refine hloop_tail s6 6 0 [] (by decide) (by simp [hor]) hs_222_227 hpc6
      (hfix.of_agree (fun r hr => hreg6 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
        (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
      (by rw [hpn_eq, hbn_eq]
          exact hcur.of_agree (fun r hr => hreg6 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
            (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      (hzero.of_mem_eq hmem6)
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
      (fun a _ _ _ _ _ => by simp only [MachineState.getByte, MachineState.getMem, hmem6])
  · -- Branch B: at least one child marked -> mark parent, optional readVarDigest, hashLevelNode
    have horT : (mL || mR) = true := Bool.eq_true_of_not_eq_false hor
    have hx28o : s5.getReg .x28 = 1#64 := by simp only [hx28_5, horT, ite_true]
    have hpc6 : s6.pc = pcWord 228 := by
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
    -- pc[228..229]: mark capMark[l+1][q] = 1
    have hst228 := step_ordinary oracle s6 228 (.ADD .x6 .x15 .x23) (by decide) hpc6 rfl (by intro h; cases h) rfl
    let s7 := execInstrBr s6 (.ADD .x6 .x15 .x23)
    have hpc7 : s7.pc = pcWord 229 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
    have hx6_7 : s7.getReg .x6 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) := by
      simp only [s7, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide),
        hreg6 .x15 (by decide) (by decide) (by decide) (by decide), hx15,
        hreg6 .x23 (by decide) (by decide) (by decide) (by decide), hx23, bv64_add]
    have hx28_7 : s7.getReg .x28 = 1#64 := by
      simp only [s7, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x28), hx28_6]
    have ha229 : s7.getReg .x6 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) := by
      rw [hx6_7, se12_0, BitVec.add_zero]
    have hv229 : memoryArgumentsValid s7 (.SB .x6 .x28 0#12) = true := by
      simp only [memoryArgumentsValid, memAccess, ha229]
      exact accessValid_ofNat (4096 + capMarkOff (l + 1) + q) 1 (by unfold MEMORY_BYTES; omega) (by omega)
    have hst229 := step_ordinary oracle s7 229 (.SB .x6 .x28 0#12) (by decide) hpc7 rfl (by intro h; cases h)
      (by simp [ordinaryStep, hv229])
    let s8 := execInstrBr s7 (.SB .x6 .x28 0#12)
    have hpc8 : s8.pc = pcWord 230 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
    have hmem7 : s7.mem = s.mem := by simpa [s7, execInstrBr, mem_setPC, mem_setReg] using hmem6
    have hbyte8 : ∀ a, s8.getByte a = (s.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) 1#8).getByte a := fun a => by
      simp only [s8, execInstrBr, ha229, hx28_7, show (1#64 : Word).truncate 8 = 1#8 by decide,
        MachineState.getByte, MachineState.setByte, MachineState.getMem,
        MachineState.setMem, mem_setPC, hmem7]
    have hout8 : MemEqOutside s s8 (4096 + capMarkOff (l + 1) + q) (4096 + capMarkOff (l + 1) + q + 1) := by
      intro a ha hout; rw [hbyte8]; exact MemEqOutside_setByte s _ 1#8 (by omega) a ha hout
    have hreg8 : ∀ r, r ≠ .x6 → s8.getReg r = s6.getReg r := fun r h6 => by
      have : s8.getReg r = s7.getReg r := by
        simp [s8, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
      rw [this]; simp only [s7, execInstrBr, MachineState.getReg_setPC]
      exact MachineState.getReg_setReg_ne _ _ _ _ h6.symm
    -- pc[230..233]: x10 = 8192 + capValOff l + 96 * q
    have hcodeP : ∀ j (hj : j < capPairAddrInstrs.length), checkInstr (230 + j) = .base (capPairAddrInstrs[j]'hj) := by
      intro j hj; have hj' : j < 4 := hj; interval_cases j <;> rfl
    have hpureP : ∀ j (hj : j < capPairAddrInstrs.length),
        Instruction.base (capPairAddrInstrs[j]'hj) ≠ .base .ECALL ∧
        ∀ st, ordinaryStep st (.base (capPairAddrInstrs[j]'hj)) = some (execInstrBr st (capPairAddrInstrs[j]'hj)) ∧
              (execInstrBr st (capPairAddrInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
              (execInstrBr st (capPairAddrInstrs[j]'hj)).mem = st.mem := by
      intro j hj; have hj' : j < 4 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
    obtain ⟨hs9, hpc9, hmem9⟩ := step_pure_list oracle 230 capPairAddrInstrs s8 (by decide) hcodeP hpureP hpc8
    let s9 := runInstrs s8 capPairAddrInstrs
    have hs9 : StepsTo oracle s8 s9 4 0 [] := hs9
    have hpc9 : s9.pc = pcWord 234 := hpc9
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
    -- pc[234]: BEQ x7, x8, pc[240]
    have hst234 := step_ordinary oracle s9 234 (.BEQ .x7 .x8 24#13) (by decide) hpc9 rfl (by intro h; cases h) rfl
    let s10 := execInstrBr s9 (.BEQ .x7 .x8 24#13)
    have hs_222_234 : StepsTo oracle s s10 13 0 [] := by
      simpa using (hs_222_227.trans (hst228.trans hst229)).trans (hs9.trans hst234)
    -- Common hash block pc[240..245] -> pc[246] via hashLevelNode (lvl = l + 1)
    have hcompress : ∀ (s240 : MachineState) (kPre : Nat),
        kPre ≤ 229 →
        StepsTo oracle s s240 kPre 0 [] →
        s240.pc = pcWord 240 →
        CheckFixedRegs s240 →
        ProofCursor s0 input.proof.length pNext bNext s240 →
        ChainScratchZero s240 →
        s240.getReg .x10 = BitVec.ofNat 64 (8192 + capValOff l + 96 * q) →
        s240.getReg .x20 = BitVec.ofNat 64 (levelSize l) →
        s240.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) →
        s240.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) →
        s240.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) →
        s240.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) →
        s240.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) →
        s240.getReg .x23 = BitVec.ofNat 64 q →
        s240.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) →
        s240.getReg .x30 = BitVec.ofNat 64 (68719475728 + 960) →
        s240.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) = 1#8 →
        (∀ b < 32, s240.getByte (BitVec.ofNat 64 (8192 + capValOff l + 96 * q + 64 + b)) = 0#8) →
        (mL = false → readBuffer s240 (8192 + capValOff l + gapOffset (2 * q)) 32 =
          proofDigestVar s0 input.proof.length (11341403200 + pCur) bCur l) →
        (mR = false → readBuffer s240 (8192 + capValOff l + gapOffset (2 * q + 1)) 32 =
          proofDigestVar s0 input.proof.length (11341403200 + pCur) bCur l) →
        (∀ a : Nat, a < 2 ^ 64 →
          a ≠ 4096 + capMarkOff (l + 1) + q →
          (mL = mR ∨
            let u := if !mL then 2 * q else 2 * q + 1
            a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
          s240.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) →
        PhaseOutcome oracle s 320 (if (mL || mR) then levelChain (l + 1) else 0)
          ((mL != mR) = true ∧
            input.proof.length < pCur + levelBodyBytes l + tailBytesBits (bCur + levelTailBits l))
          (fun s' calls tr =>
            calls ≤ (if (mL || mR) then levelChain (l + 1) else 0) ∧
            s'.pc = (if q + 1 = levelSize l / 2 then pcWord 248 else pcWord 222) ∧
            CheckFixedRegs s' ∧
            ProofCursor s0 input.proof.length pNext bNext s' ∧
            ChainScratchZero s' ∧
            s'.getReg .x20 = BitVec.ofNat 64 (levelSize l) ∧
            s'.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
            s'.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
            s'.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) ∧
            s'.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) ∧
            s'.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) ∧
            s'.getReg .x23 = BitVec.ofNat 64 (q + 1) ∧
            s'.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) ∧
            s'.getReg .x30 = BitVec.ofNat 64 (68719475728 + 960) ∧
            s'.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) =
              (if (mL || mR) then 1#8 else 0#8) ∧
            (mL || mR = true →
              let dL := readBuffer s' (8192 + capValOff l + gapOffset (2 * q)) 32
              let dR := readBuffer s' (8192 + capValOff l + gapOffset (2 * q + 1)) 32
              readBuffer s' (8192 + capValOff (l + 1) + gapOffset q) 32 = chainHash c96 (l + 1) dL dR ∧
              (∀ x ∈ chainInputs c96 (l + 1) dL dR, InTrace h768 oracle tr x) ∧
              (mL = false → dL = proofDigestVar s0 input.proof.length (11341403200 + pCur) bCur l) ∧
              (mR = false → dR = proofDigestVar s0 input.proof.length (11341403200 + pCur) bCur l)) ∧
            (mL = false → mR = false → s'.mem = s.mem) ∧
            (∀ a : Nat, a < 2 ^ 64 →
              (a < 512 ∨ 608 ≤ a) →
              a ≠ 4096 + capMarkOff (l + 1) + q →
              (mL = mR ∨
                let u := if !mL then 2 * q else 2 * q + 1
                a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
              (a < 8192 + capValOff (l + 1) + gapOffset q ∨ 8192 + capValOff (l + 1) + gapOffset q + 32 ≤ a) →
              s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a))) := by
      intro s240 kPre hkPre hstPre hpc240 hfix240 hcur240 hzero240 h10 h20 h14 h15 h16 h17 h22 h23 h29 h30
        hmk240 hgap240 hdL_fr hdR_fr hout240
      have hhigh240 : HighMemPreserved s0 s240 := fun a ha hge => by
        have hgo_u : gapOffset (if !mL then 2 * q else 2 * q + 1) + 32 ≤ 96 * q + 64 := by
          unfold gapOffset; split <;> omega
        exact (hout240 a ha (by omega) (Or.inr (Or.inr (by omega)))).trans (hhigh a ha hge)
      have hcodeD : ∀ j (hj : j < capPairDstInstrs.length), checkInstr (240 + j) = .base (capPairDstInstrs[j]'hj) := by
        intro j hj; have hj' : j < 4 := hj; interval_cases j <;> rfl
      have hpureD : ∀ j (hj : j < capPairDstInstrs.length),
          Instruction.base (capPairDstInstrs[j]'hj) ≠ .base .ECALL ∧
          ∀ st, ordinaryStep st (.base (capPairDstInstrs[j]'hj)) = some (execInstrBr st (capPairDstInstrs[j]'hj)) ∧
                (execInstrBr st (capPairDstInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
                (execInstrBr st (capPairDstInstrs[j]'hj)).mem = st.mem := by
        intro j hj; have hj' : j < 4 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
      obtain ⟨hsD, hpcD, hmemD⟩ := step_pure_list oracle 240 capPairDstInstrs s240 (by decide) hcodeD hpureD hpc240
      let sD := runInstrs s240 capPairDstInstrs
      have hsD : StepsTo oracle s240 sD 4 0 [] := hsD
      have hpcD : sD.pc = pcWord 244 := hpcD
      have hmemD : sD.mem = s240.mem := hmemD
      have hregD : ∀ r, r ≠ .x6 → r ≠ .x12 → sD.getReg r = s240.getReg r := fun r h6 h12 => by
        simp only [sD, runInstrs, capPairDstInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
      have hx12_D : sD.getReg .x12 = BitVec.ofNat 64 (8192 + capValOff (l + 1) + gapOffset q) := by
        simp only [sD, runInstrs, capPairDstInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq,
          h23, h17, show (1#6 : BitVec 6).toNat = 1 by decide, show (5#6 : BitVec 6).toNat = 5 by decide]
        rw [bv64_shr q 1 (by omega), Nat.pow_one, bv64_add, bv64_shl _ 5 (by omega), bv64_add]
        exact congrArg (BitVec.ofNat 64) (by unfold gapOffset; omega)
      -- pc[244]: LD x6, 72(x29) -> levelMetaOC (l + 1)
      have ha244 : sD.getReg .x29 + signExtend12 72#12 =
          BitVec.ofNat 64 (68719475728 + (40 * (l + 1) + 32)) := by
        rw [hregD .x29 (by decide) (by decide), h29, se12_72_cap]
        change BitVec.ofNat 64 _ + BitVec.ofNat 64 72 = _; rw [bv64_add]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have hv244 : memoryArgumentsValid sD (.LD .x6 .x29 72#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha244]
        exact accessValid_ofNat (68719475728 + (40 * (l + 1) + 32)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
      have hst244 := step_ordinary oracle sD 244 (.LD .x6 .x29 72#12) (by decide) hpcD rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv244])
      let sE := execInstrBr sD (.LD .x6 .x29 72#12)
      have hpcE : sE.pc = pcWord 245 := by simp only [sE, execInstrBr, MachineState.setPC, hpcD, pcWord_add_four]
      have hmemE : sE.mem = s240.mem := by simpa [sE, execInstrBr, mem_setPC, mem_setReg] using hmemD
      have hregE : ∀ r, r ≠ .x6 → r ≠ .x12 → sE.getReg r = s240.getReg r := fun r h6 h12 => by
        simp only [sE, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]; exact hregD r h6 h12
      have hx12_E : sE.getReg .x12 = BitVec.ofNat 64 (8192 + capValOff (l + 1) + gapOffset q) := by
        simp only [sE, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x12), hx12_D]
      have hx6_E : sE.getReg .x6 = BitVec.ofNat 64 (levelMetaOC (l + 1)) := by
        simp only [sE, execInstrBr, MachineState.getReg_setPC, ha244]
        rw [MachineState.getReg_setReg_eq (by decide)]
        have hm : sD.getMem (BitVec.ofNat 64 (68719475728 + (40 * (l + 1) + 32))) =
            s240.getMem (BitVec.ofNat 64 (68719475728 + (40 * (l + 1) + 32))) := by simp [MachineState.getMem, hmemD]
        rw [hm, hhigh240.getMem_eq (by omega) (by omega) (by omega),
          check_initial_data_dword input hvalid (40 * (l + 1) + 32) (by omega)]
        exact openingData_dword_4 ⟨l + 1, by omega⟩
      have hfixE : CheckFixedRegs sE :=
        hfix240.of_agree (fun r hr => hregE r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))
      have hgo_al : gapOffset q % 8 = 0 := by unfold gapOffset; omega
      have hgapE : readBuffer sE (8192 + capValOff l + 96 * q + 64) 32 = 0 :=
        readBuffer_zero_of_bytes sE _ 32 (fun b hb => by
          simp only [MachineState.getByte, MachineState.getMem, hmemE]; exact hgap240 b hb)
      -- pc[245]: JAL x1, 320 -> hashLevelNode (lvl = l + 1)
      obtain ⟨sF, kH, trH, hkH, hstepH, hpcF, hregH, hdigH, hzeroF, houtH, htrH⟩ :=
        step_call_hashLevelNode h768 oracle 245 sE
          (8192 + capValOff l + 96 * q) (8192 + capValOff (l + 1) + gapOffset q) (l + 1)
          (by omega) (by omega) (by decide) checkInstr_245 hpcE hfixE hx6_E
          ((hregE .x10 (by decide) (by decide)).trans h10) hx12_E
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          hgapE (hzero240.of_mem_eq hmemE)
      have hregF : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x9 → r ≠ .x10 → r ≠ .x12 → r ≠ .x28 →
          sF.getReg r = s240.getReg r := fun r h1 h6 h7 h9 h10 h12 h28 =>
        (hregH r h1 h7 h9 h10 h12 h28).trans (hregE r h6 h12)
      let dL0 := readBuffer s240 (8192 + capValOff l + gapOffset (2 * q)) 32
      let dR0 := readBuffer s240 (8192 + capValOff l + gapOffset (2 * q + 1)) 32
      have hdL_E : readBuffer sE (8192 + capValOff l + 96 * q) 32 = dL0 := by
        rw [show dL0 = readBuffer s240 (8192 + capValOff l + 96 * q) 32 by simp only [dL0, gapOffset_even]]
        exact (MemEqOutside.of_mem_eq hmemE 0 0).readBuffer_eq (by omega) (by omega)
      have hdR_E : readBuffer sE (8192 + capValOff l + 96 * q + 32) 32 = dR0 := by
        rw [show dR0 = readBuffer s240 (8192 + capValOff l + 96 * q + 32) 32 by
          simp only [dR0, gapOffset_odd, Nat.add_assoc]]
        exact (MemEqOutside.of_mem_eq hmemE 0 0).readBuffer_eq (by omega) (by omega)
      rw [hdL_E, hdR_E] at hdigH htrH
      have hdL_F : readBuffer sF (8192 + capValOff l + gapOffset (2 * q)) 32 = dL0 := by
        rw [gapOffset_even]
        apply readBuffer_congr2; intro b hb
        rw [houtH (8192 + capValOff l + 96 * q + b) (by omega) (Or.inl (by omega)) (Or.inr (by omega))]
        simp [MachineState.getByte, MachineState.getMem, hmemE, gapOffset_even]
      have hdR_F : readBuffer sF (8192 + capValOff l + gapOffset (2 * q + 1)) 32 = dR0 := by
        rw [gapOffset_odd]
        apply readBuffer_congr2; intro b hb
        rw [houtH (8192 + capValOff l + (96 * q + 32) + b) (by omega) (Or.inl (by omega)) (Or.inr (by omega))]
        simp [MachineState.getByte, MachineState.getMem, hmemE, gapOffset_odd]
      have htot := hstPre.trans ((hsD.trans hst244).trans hstepH)
      refine hloop_tail sF (kPre + 5 + kH) (levelChain (l + 1)) trH (by omega) (by simp [horT])
        (htot.eq_of rfl (by omega) (by omega) (by simp)) hpcF
        (hfix240.of_agree (fun r hr => hregF r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        (hcur240.of_agree (fun r hr => hregF r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
          (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
        hzeroF
        ((hregF .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h20)
        ((hregF .x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h14)
        ((hregF .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h15)
        ((hregF .x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16)
        ((hregF .x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17)
        ((hregF .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h22)
        ((hregF .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h23)
        ((hregF .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h29)
        ((hregF .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h30)
        (by rw [if_pos horT, houtH _ (by omega) (Or.inl (by omega)) (Or.inr (by omega))]
            simp only [MachineState.getByte, MachineState.getMem, hmemE]; exact hmk240)
        (fun _ => by
          dsimp only
          rw [hdL_F, hdR_F]
          exact ⟨hdigH, htrH, hdL_fr, hdR_fr⟩)
        (fun h1 h2 => by simp [h1, h2] at horT)
        (fun a ha h512 h1 h2 h3 => by
          rw [houtH a ha h3 h512]
          simp only [MachineState.getByte, MachineState.getMem, hmemE]
          exact hout240 a ha h1 h2)
    -- Now split on mL = mR (both marked) vs mL ≠ mR (frontier read via readVarDigest)
    by_cases hsame : mL = mR
    · -- Both mL = true and mR = true -> BEQ taken to pc[240]
      have hmLt : mL = true := by
        rw [← hsame, Bool.or_self] at horT; exact horT
      have hmRt : mR = true := by rw [← hsame, hmLt]
      have hpn_eq : pNext = pCur := by simp [pNext, hsame]
      have hbn_eq : bNext = bCur := by simp [bNext, hsame]
      have hpc10 : s10.pc = pcWord 240 := by
        simp only [s10, execInstrBr, hx7_9, hx8_9, hsame, beq_self_eq_true, ite_true,
          MachineState.setPC, hpc9]; exact pc_234_branch
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
      refine hcompress s10 13 (by decide) hs_222_234 hpc10
        (hfix.of_agree (fun r hr => hreg10 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)))
        (by rw [hpn_eq, hbn_eq]
            exact hcur.of_agree (fun r hr => hreg10 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
              (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
        (hzero.of_outside hout10 (by omega) (by omega))
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
    · -- Frontier pair: mL ≠ mR -> fall through to pc[235..239]
      have hne_b : (mL != mR) = true := bne_iff_ne.mpr hsame
      have hpn_eq : pNext = pCur + levelBodyBytes l := by simp [pNext, hne_b]
      have hbn_eq : bNext = bCur + levelTailBits l := by simp [bNext, hne_b]
      have hbeq_f : (s9.getReg .x7 == s9.getReg .x8) = false := by
        rw [hx7_9, hx8_9]
        cases hm1 : mL <;> cases hm2 : mR <;>
          first | decide | (exfalso; apply hsame; rw [hm1, hm2])
      have hpc10 : s10.pc = pcWord 235 := by
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
      -- pc[235..237]: set x12 = 8192 + capValOff l + gapOffset u where u = if !mL then 2*q else 2*q+1
      let u := if !mL then 2 * q else 2 * q + 1
      have hu_go : gapOffset u = if !mL then 96 * q else 96 * q + 32 := by
        cases hm1 : mL <;> simp [u, hm1, gapOffset_even, gapOffset_odd]
      have hst235 := step_ordinary oracle s10 235 (.ADDI .x12 .x10 0#12) (by decide) hpc10 rfl (by intro h; cases h) rfl
      let s11 := execInstrBr s10 (.ADDI .x12 .x10 0#12)
      have hpc11 : s11.pc = pcWord 236 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10, pcWord_add_four]
      have hx12_11 : s11.getReg .x12 = BitVec.ofNat 64 (8192 + capValOff l + 96 * q) := by
        simp only [s11, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide), hx10_10, se12_0, BitVec.add_zero]
      have hx7_11 : s11.getReg .x7 = if mL then 1#64 else 0#64 := by
        simp only [s11, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x12 ≠ .x7), hx7_10]
      have hst236 := step_ordinary oracle s11 236 (.BEQ .x7 .x0 8#13) (by decide) hpc11 rfl (by intro h; cases h) rfl
      let s12 := execInstrBr s11 (.BEQ .x7 .x0 8#13)
      have hreach238 : ∃ s238 kSel, kSel ≤ 3 ∧ StepsTo oracle s10 s238 kSel 0 [] ∧
          s238.pc = pcWord 238 ∧ s238.mem = s8.mem ∧
          s238.getReg .x12 = BitVec.ofNat 64 (8192 + capValOff l + gapOffset u) ∧
          (∀ r, r ≠ .x12 → s238.getReg r = s10.getReg r) := by
        cases hm1 : mL with
        | false =>
          have hx7z : s11.getReg .x7 = 0#64 := by simp only [hx7_11, hm1, Bool.false_eq_true, ite_false]
          refine ⟨s12, 2, by decide, by simpa using hst235.trans hst236, ?_, ?_, ?_, ?_⟩
          · simp only [s12, execInstrBr, hx7z, getReg_x0, beq_self_eq_true, ite_true,
              MachineState.setPC, hpc11]; exact pc_236_branch
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
          have hpc12 : s12.pc = pcWord 237 := by
            simp only [s12, execInstrBr, hx7o, getReg_x0, show (1#64 == 0#64) = false by decide,
              Bool.false_eq_true, ite_false, MachineState.setPC, hpc11, pcWord_add_four]
          have hst237 := step_ordinary oracle s12 237 (.ADDI .x12 .x10 32#12) (by decide) hpc12 rfl (by intro h; cases h) rfl
          let s13 := execInstrBr s12 (.ADDI .x12 .x10 32#12)
          refine ⟨s13, 3, by decide, by simpa using (hst235.trans hst236).trans hst237,
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
      obtain ⟨s238, kSel, hkSel, hsSel, hpc238, hmem238, hx12_238, hreg238⟩ := hreach238
      -- pc[238]: LD x6, 32(x29) -> levelMetaOC l
      have hout_s_238 : MemEqOutside s s238 (4096 + capMarkOff (l + 1) + q) (4096 + capMarkOff (l + 1) + q + 1) :=
        hout8.trans (MemEqOutside.of_mem_eq hmem238 _ _)
      have ha238 : s238.getReg .x29 + signExtend12 32#12 = BitVec.ofNat 64 (68719475728 + (40 * l + 32)) := by
        rw [hreg238 .x29 (by decide), hreg10 .x29 (by decide) (by decide) (by decide) (by decide) (by decide), hx29, se12_32]
        change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
      have hv238 : memoryArgumentsValid s238 (.LD .x6 .x29 32#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha238]
        exact accessValid_ofNat (68719475728 + (40 * l + 32)) 8 (by unfold MEMORY_BYTES; omega) (by omega)
      have hst238 := step_ordinary oracle s238 238 (.LD .x6 .x29 32#12) (by decide) hpc238 rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv238])
      let s239 := execInstrBr s238 (.LD .x6 .x29 32#12)
      have hpc239 : s239.pc = pcWord 239 := by simp only [s239, execInstrBr, MachineState.setPC, hpc238, pcWord_add_four]
      have hmem239 : s239.mem = s8.mem := by simpa [s239, execInstrBr, mem_setPC, mem_setReg] using hmem238
      have hout_s_239 : MemEqOutside s s239 (4096 + capMarkOff (l + 1) + q) (4096 + capMarkOff (l + 1) + q + 1) :=
        hout8.trans (MemEqOutside.of_mem_eq hmem239 _ _)
      have hreg239 : ∀ r, r ≠ .x6 → r ≠ .x12 → s239.getReg r = s10.getReg r := fun r h6 h12 => by
        simp only [s239, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ h6.symm]; exact hreg238 r h12
      have hx12_239 : s239.getReg .x12 = BitVec.ofNat 64 (8192 + capValOff l + gapOffset u) := by
        simp only [s239, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x12), hx12_238]
      have hx6_239 : s239.getReg .x6 = BitVec.ofNat 64 (levelMetaOC l) := by
        simp only [s239, execInstrBr, MachineState.getReg_setPC, ha238]
        rw [MachineState.getReg_setReg_eq (by decide)]
        rw [(hhigh.trans (hout_s_238.mono (by omega) (by omega))).getMem_eq (by omega) (by omega) (by omega),
          check_initial_data_dword input hvalid (40 * l + 32) (by omega)]
        exact openingData_dword_4 ⟨l, by omega⟩
      -- pc[239]: JAL x1, 232 -> readVarDigest (pc[297])
      have hu_go_bd : gapOffset u + 32 ≤ 96 * q + 64 := by
        rw [hu_go]; cases mL <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false] <;> omega
      have hu_al : gapOffset u % 8 = 0 := by unfold gapOffset; omega
      have hcur239 : ProofCursor s0 input.proof.length pCur bCur s239 :=
        hcur.of_agree (fun r hr => (hreg239 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)).trans
          (hreg10 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
            (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)))
      have hread := step_call_readVarDigest oracle s0 input.proof.length hvalid 239 s239 pCur bCur
        (8192 + capValOff l + gapOffset u) l (by omega) (by omega) (by decide) checkInstr_239
        hpc239 hx6_239 hcur239 (hhigh.trans (hout_s_239.mono (by omega) (by omega)))
        hx12_239 (by omega) (by omega)
      cases hread with
      | rejected kR qR trR hrR hkR hqR hhR =>
        have htot := ((hs_222_234.trans hsSel).trans hst238).halt hhR
        exact .rejected (13 + kSel + 1 + kR) qR trR ⟨hne_b, hrR⟩ (by omega) (by omega)
          (by simpa only [Nat.add_assoc, Nat.zero_add, List.nil_append] using htot)
      | continued s240 kR qR trR hkR hqR hs240 hp240 =>
        obtain ⟨rfl, rfl, hpc240, hcur240, hreg240, hrb_u, hout240⟩ := hp240
        have hreg240_10 : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x4 → r ≠ .x6 → r ≠ .x7 → r ≠ .x9 → r ≠ .x12 → r ≠ .x25 → r ≠ .x31 →
            s240.getReg r = s10.getReg r := fun r h1 h3 h4 h6 h7 h9 h12 h25 h31 =>
          (hreg240 r h1 h3 h4 h7 h9 h12 h25 h31).trans (hreg239 r h6 h12)
        have hout_s_240 : ∀ a : Nat, a < 2 ^ 64 →
            a ≠ 4096 + capMarkOff (l + 1) + q →
            (a < 8192 + capValOff l + gapOffset u ∨ 8192 + capValOff l + gapOffset u + 32 ≤ a) →
            s240.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a) := fun a ha hne hout =>
          (hout240 a ha hout).trans (hout_s_239 a ha (by omega))
        have htot_pre := ((hs_222_234.trans hsSel).trans hst238).trans hs240
        refine hcompress s240 (13 + kSel + 1 + kR) (by omega)
          (htot_pre.eq_of rfl (by omega) (by decide) (by simp))
          hpc240
          (hfix.of_agree (fun r hr => (hreg240_10 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
            (isFixedReg_ne_of_false hr rfl)).trans
            (hreg10 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
              (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl))))
          (by rw [hpn_eq, hbn_eq]; exact hcur240)
          ⟨fun a h1 h2 => (hout_s_240 a (by omega) (by omega) (Or.inl (by omega))).trans (hzero.1 a h1 h2),
           fun a h1 h2 => (hout_s_240 a (by omega) (by omega) (Or.inl (by omega))).trans (hzero.2 a h1 h2)⟩
          ((hreg240_10 .x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx10_10)
          ((hreg240_10 .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20))
          ((hreg240_10 .x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx14))
          ((hreg240_10 .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx15))
          ((hreg240_10 .x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx16))
          ((hreg240_10 .x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx17))
          ((hreg240_10 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22))
          ((hreg240_10 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx23))
          ((hreg240_10 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx29))
          ((hreg240_10 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hreg10 .x30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx30))
          (by rw [hout240 _ (by omega) (by omega)]
              have h2 : s239.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) =
                  s8.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) := by
                simp [MachineState.getByte, MachineState.getMem, hmem239]
              rw [h2, hbyte8, set_byte_read]; simp only [ite_true])
          (fun b hb =>
            (hout_s_240 _ (by omega) (by omega) (Or.inr (by omega))).trans (hgap b hb))
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
            · exact hout_s_240 a ha hne hdisj)

end CommitGolfCandidate
