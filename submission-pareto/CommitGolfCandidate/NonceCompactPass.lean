import CommitGolfCandidate.NonceCompactCopy

/-! One record of the compaction (words 197..208): 16 nonce bytes, then 128 bytes, then the 13
siblings by the field copy. 949 cycles per record. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem s6_addi_zero (state : MachineState) (rd : Reg) (imm : BitVec 12) (nonzero : rd ≠ .x0) :
    (execInstrBr state (.ADDI rd .x0 imm)).getReg rd = signExtend12 imm := by
  rw [s6_addi_self _ _ _ _ nonzero]
  change (0 : Word) + signExtend12 imm = _
  simp

theorem s6_head_sources (count record i : Nat) (present : record < count) (inside : i < 16) :
    s6PackSource count (560 * record + i) = 576 * record + i := by
  rw [s6_pack_source_record count record i present (by omega)]
  simp only [s6RecordSource]
  split_ifs <;> omega

theorem s6_middle_sources (count record i : Nat) (present : record < count) (inside : i < 128) :
    s6PackSource count (560 * record + 16 + i) = 576 * record + 32 + i := by
  rw [show 560 * record + 16 + i = 560 * record + (16 + i) by omega,
    s6_pack_source_record count record _ present (by omega)]
  simp only [s6RecordSource]
  split_ifs <;> omega

theorem s6_sibling_sources (count record j i : Nat) (present : record < count) (sibling : j < 13)
    (inside : i < 32) :
    s6PackSource count (560 * record + 144 + 32 * j + i) = 576 * record + 160 + 32 * j + i := by
  rw [show 560 * record + 144 + 32 * j + i = 560 * record + (144 + 32 * j + i) by omega,
    s6_pack_source_record count record _ present (by omega)]
  simp only [s6RecordSource, s6NodeSource]
  split_ifs <;> omega

/-- One sibling (words 203..206): call the field copy, a zero read-side skip, count down. -/
theorem s6_sibling_pass (orig state : MachineState) (base count n source left : Nat)
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * 11))
    (counter : state.getReg .x29 = BitVec.ofNat 64 (left + 1))
    (read : state.getReg .x23 = BitVec.ofNat 64 (base + source))
    (write : state.getReg .x25 = BitVec.ofNat 64 (base + n))
    (before : NonceCompacted orig base count n state)
    (sources : ∀ i < 32, s6PackSource count (n + i) = source + i)
    (ahead : n ≤ source) (evenBase : base % 2 = 0) (evenSource : source % 2 = 0) (evenN : n % 2 = 0)
    (small : base + source + 32 ≤ MEMORY_BYTES) (leftSmall : left + 1 < 2 ^ 64) :
    ∃ next, NonceRuns s6OpeningImage 39 state next ∧
      next.pc = (if left = 0 then BitVec.ofNat 64 (4864 + 4 * 15) else BitVec.ofNat 64 (4864 + 4 * 11)) ∧
      next.getReg .x29 = BitVec.ofNat 64 left ∧
      next.getReg .x23 = BitVec.ofNat 64 (base + source + 32) ∧
      next.getReg .x25 = BitVec.ofNat 64 (base + n + 32) ∧
      (∀ reg, reg ≠ .x1 → reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → reg ≠ .x29 →
        next.getReg reg = state.getReg reg) ∧
      NonceCompacted orig base count (n + 32) next := by
  have twoExt : signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 0 := by decide
  let called := execInstrBr state (.JAL .x1 84)
  have callRuns := s6_step state 11 (by omega) (.JAL .x1 84) rfl pc rfl rfl
  have call := s6_jal_effect state .x1 84 (by decide)
  have calledPc : called.pc = BitVec.ofNat 64 (4864 + 4 * 32) := by
    rw [call.1, pc]
    decide
  have calledLink : called.getReg .x1 = BitVec.ofNat 64 (4864 + 4 * 12) := by
    rw [call.2.1, pc]
    decide
  obtain ⟨fielded, fieldRuns, fieldPc, fieldRead, fieldWrite, fieldReg, fieldBytes⟩ :=
    s6_field_runs orig called base count n source calledPc
      (by rw [call.2.2.1 _ (by decide), read]) (by rw [call.2.2.1 _ (by decide), write])
      (by rw [calledLink]; decide) (nonce_compacted_mem before call.2.2.2) sources ahead evenBase
      evenSource evenN (by omega)
  rw [calledLink] at fieldPc
  let s1 := execInstrBr fielded (.ADDI .x23 .x23 0)
  let s2 := execInstrBr s1 (.ADDI .x29 .x29 4095)
  have run1 := s6_step fielded 12 (by omega) (.ADDI .x23 .x23 0) rfl fieldPc rfl rfl
  have run2 := s6_step s1 13 (by omega) (.ADDI .x29 .x29 4095) rfl
    (by rw [s6_addi_pc, fieldPc, s6_pc_next]) rfl rfl
  have pc2 : s2.pc = BitVec.ofNat 64 (4864 + 4 * 14) := by
    rw [s6_addi_pc, s6_addi_pc, fieldPc, s6_pc_next, s6_pc_next]
  have run3 := s6_step s2 14 (by omega) (.BNE .x29 .x0 8180) rfl pc2 rfl rfl
  have counter2 : s2.getReg .x29 = BitVec.ofNat 64 left := by
    rw [s6_addi_self _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide),
      fieldReg _ (by decide) (by decide) (by decide), call.2.2.1 _ (by decide), counter,
      s6_decrement _ (by omega)]
    rfl
  have branch := s6_branch_reg s2 .x29 .x0 8180
  refine ⟨_, nonce_runs_trans (nonce_runs_trans (nonce_runs_trans (nonce_runs_trans callRuns fieldRuns)
    run1) run2) run3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s6_bne_pc s2 .x29 8180 left (by omega) counter2, pc2]
    by_cases empty : left = 0
    · rw [if_pos empty, if_pos empty, s6_pc_next]
    · rw [if_neg empty, if_neg empty]
      decide
  · rw [(branch .x29).1, counter2]
  · rw [(branch .x23).1, s6_addi_reg _ _ _ _ _ (by decide), s6_addi_self _ _ _ _ (by decide), fieldRead,
      twoExt, s6_add_ofNat]
  · rw [(branch .x25).1, s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide), fieldWrite]
  · intro reg r1 r6 r23 r25 r29
    rw [(branch reg).1, s6_addi_reg _ _ _ _ _ r29, s6_addi_reg _ _ _ _ _ r23, fieldReg _ r6 r23 r25,
      call.2.2.1 _ r1]
  · exact nonce_compacted_mem fieldBytes
      (by rw [(s6_branch_mem s2 .x29 .x0 8180).1, s6_addi_mem, s6_addi_mem])

/-- The 13 siblings of a record; `left + 1` of them are still to do. -/
theorem s6_siblings_runs (orig : MachineState) (base count record : Nat) (present : record < count)
    (evenBase : base % 2 = 0) (window : base + 576 * count ≤ MEMORY_BYTES) :
    ∀ (left : Nat) (state : MachineState), left < 13 →
    state.pc = BitVec.ofNat 64 (4864 + 4 * 11) →
    state.getReg .x29 = BitVec.ofNat 64 (left + 1) →
    state.getReg .x23 = BitVec.ofNat 64 (base + (576 * record + 160 + 32 * (12 - left))) →
    state.getReg .x25 = BitVec.ofNat 64 (base + (560 * record + 144 + 32 * (12 - left))) →
    NonceCompacted orig base count (560 * record + 144 + 32 * (12 - left)) state →
    ∃ next, NonceRuns s6OpeningImage (39 * (left + 1)) state next ∧
      next.pc = BitVec.ofNat 64 (4864 + 4 * 15) ∧
      next.getReg .x23 = BitVec.ofNat 64 (base + 576 * (record + 1)) ∧
      next.getReg .x25 = BitVec.ofNat 64 (base + 560 * (record + 1)) ∧
      (∀ reg, reg ≠ .x1 → reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → reg ≠ .x29 →
        next.getReg reg = state.getReg reg) ∧
      NonceCompacted orig base count (560 * (record + 1)) next := by
  have room : base + 576 * (record + 1) ≤ MEMORY_BYTES := by
    have : 576 * (record + 1) ≤ 576 * count := Nat.mul_le_mul_left _ present
    omega
  intro left
  induction left with
  | zero =>
    intro state _ pc counter read write before
    obtain ⟨next, runs, nextPc, nextCounter, nextRead, nextWrite, nextOther, nextBytes⟩ :=
      s6_sibling_pass orig state base count _ _ 0 pc counter read write before
        (fun i inside => s6_sibling_sources count record 12 i present (by omega) inside)
        (by omega) evenBase (by omega) (by omega) (by omega) (by decide)
    refine ⟨next, runs, by rw [nextPc, if_pos rfl], ?_, ?_, nextOther, ?_⟩
    · exact nextRead.trans (congrArg (BitVec.ofNat 64) (by omega))
    · exact nextWrite.trans (congrArg (BitVec.ofNat 64) (by omega))
    · rw [show 560 * (record + 1) = 560 * record + 144 + 32 * (12 - 0) + 32 by omega]
      exact nextBytes
  | succ left ih =>
    intro state bound pc counter read write before
    obtain ⟨mid, runs, midPc, midCounter, midRead, midWrite, midOther, midBytes⟩ :=
      s6_sibling_pass orig state base count _ _ (left + 1) pc counter read write before
        (fun i inside => by
          have shifted := s6_sibling_sources count record (12 - (left + 1)) i present (by omega) inside
          rw [shifted])
        (by omega) evenBase (by omega) (by omega) (by omega) (by omega)
    rw [if_neg (by omega)] at midPc
    obtain ⟨next, nextRuns, nextPc, nextRead, nextWrite, nextOther, nextBytes⟩ :=
      ih mid (by omega) midPc midCounter
        (midRead.trans (congrArg (BitVec.ofNat 64) (by omega)))
        (midWrite.trans (congrArg (BitVec.ofNat 64) (by omega)))
        (by rw [show 560 * record + 144 + 32 * (12 - left) = 560 * record + 144 + 32 * (12 - (left + 1)) + 32 by
              omega]
            exact midBytes)
    refine ⟨next, ?_, nextPc, nextRead, nextWrite, ?_, nextBytes⟩
    · have total := nonce_runs_trans runs nextRuns
      rwa [show 39 + 39 * (left + 1) = 39 * (left + 1 + 1) by ring] at total
    · intro reg r1 r6 r23 r25 r29
      rw [nextOther reg r1 r6 r23 r25 r29, midOther reg r1 r6 r23 r25 r29]

/-- One whole record (words 197..208). -/
theorem s6_record_runs (orig state : MachineState) (base count record : Nat) (present : record < count)
    (evenBase : base % 2 = 0) (window : base + 576 * count ≤ MEMORY_BYTES) (countSmall : count < 2 ^ 64)
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * 5))
    (counter : state.getReg .x24 = BitVec.ofNat 64 (count - record))
    (read : state.getReg .x23 = BitVec.ofNat 64 (base + 576 * record))
    (write : state.getReg .x25 = BitVec.ofNat 64 (base + 560 * record))
    (before : NonceCompacted orig base count (560 * record) state) :
    ∃ next, NonceRuns s6OpeningImage 949 state next ∧
      next.pc = (if record + 1 = count then BitVec.ofNat 64 (4864 + 4 * 17)
        else BitVec.ofNat 64 (4864 + 4 * 5)) ∧
      next.getReg .x24 = BitVec.ofNat 64 (count - (record + 1)) ∧
      next.getReg .x23 = BitVec.ofNat 64 (base + 576 * (record + 1)) ∧
      next.getReg .x25 = BitVec.ofNat 64 (base + 560 * (record + 1)) ∧
      (∀ reg, reg ≠ .x1 → reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x24 → reg ≠ .x25 → reg ≠ .x28 → reg ≠ .x29 →
        next.getReg reg = state.getReg reg) ∧
      NonceCompacted orig base count (560 * (record + 1)) next := by
  have room : base + 576 * (record + 1) ≤ MEMORY_BYTES := by
    have : 576 * (record + 1) ≤ 576 * count := Nat.mul_le_mul_left _ present
    omega
  have sixteenExt : signExtend12 (16 : BitVec 12) = BitVec.ofNat 64 16 := by decide
  -- head: 8 halfwords
  let s1 := execInstrBr state (.ADDI .x28 .x0 8)
  have run1 := s6_step state 5 (by omega) (.ADDI .x28 .x0 8) rfl pc rfl rfl
  have pc1 : s1.pc = BitVec.ofNat 64 (4864 + 4 * 6) := by rw [s6_addi_pc, pc, s6_pc_next]
  let s2 := execInstrBr s1 (.JAL .x1 76)
  have run2 := s6_step s1 6 (by omega) (.JAL .x1 76) rfl pc1 rfl rfl
  have call2 := s6_jal_effect s1 .x1 76 (by decide)
  have link2 : s2.getReg .x1 = BitVec.ofNat 64 (4864 + 4 * 7) := by rw [call2.2.1, pc1]; decide
  have at2 : S6HalvesAt orig base count (560 * record) (576 * record) (7 + 1) s2 := by
    refine ⟨by rw [call2.1, pc1]; decide, ?_, ?_, ?_, ?_⟩
    · rw [call2.2.2.1 _ (by decide), s6_addi_zero _ _ _ (by decide)]
      decide
    · rw [call2.2.2.1 _ (by decide), s6_addi_reg _ _ _ _ _ (by decide), read]
    · rw [call2.2.2.1 _ (by decide), s6_addi_reg _ _ _ _ _ (by decide), write]
    · exact nonce_compacted_mem before (by rw [call2.2.2.2, s6_addi_mem])
  obtain ⟨s3, run3, pc3, read3, write3, other3, bytes3⟩ :=
    s6_halves_runs orig base count 7 (560 * record) (576 * record) s2 at2
      (fun i inside => s6_head_sources count record i present (by omega)) (by omega) evenBase (by omega)
      (by omega) (by omega) (by rw [link2]; decide)
  rw [link2] at pc3
  -- skip the tag and zero word, 64 halfwords
  let s4 := execInstrBr s3 (.ADDI .x23 .x23 16)
  have run4 := s6_step s3 7 (by omega) (.ADDI .x23 .x23 16) rfl pc3 rfl rfl
  let s5 := execInstrBr s4 (.ADDI .x28 .x0 64)
  have run5 := s6_step s4 8 (by omega) (.ADDI .x28 .x0 64) rfl (by rw [s6_addi_pc, pc3, s6_pc_next]) rfl rfl
  have pc5 : s5.pc = BitVec.ofNat 64 (4864 + 4 * 9) := by
    rw [s6_addi_pc, s6_addi_pc, pc3, s6_pc_next, s6_pc_next]
  let s6 := execInstrBr s5 (.JAL .x1 64)
  have run6 := s6_step s5 9 (by omega) (.JAL .x1 64) rfl pc5 rfl rfl
  have call6 := s6_jal_effect s5 .x1 64 (by decide)
  have link6 : s6.getReg .x1 = BitVec.ofNat 64 (4864 + 4 * 10) := by rw [call6.2.1, pc5]; decide
  have at6 : S6HalvesAt orig base count (560 * record + 16) (576 * record + 32) (63 + 1) s6 := by
    refine ⟨by rw [call6.1, pc5]; decide, ?_, ?_, ?_, ?_⟩
    · rw [call6.2.2.1 _ (by decide), s6_addi_zero _ _ _ (by decide)]
      decide
    · rw [call6.2.2.1 _ (by decide), s6_addi_reg _ _ _ _ _ (by decide), s6_addi_self _ _ _ _ (by decide),
        read3, sixteenExt, s6_add_ofNat]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · rw [call6.2.2.1 _ (by decide), s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide),
        write3]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · exact nonce_compacted_mem bytes3 (by rw [call6.2.2.2, s6_addi_mem, s6_addi_mem])
  obtain ⟨s7, run7, pc7, read7, write7, other7, bytes7⟩ :=
    s6_halves_runs orig base count 63 (560 * record + 16) (576 * record + 32) s6 at6
      (fun i inside => s6_middle_sources count record i present (by omega)) (by omega) evenBase (by omega)
      (by omega) (by omega) (by rw [link6]; decide)
  rw [link6] at pc7
  -- the 13 siblings
  let s8 := execInstrBr s7 (.ADDI .x29 .x0 13)
  have run8 := s6_step s7 10 (by omega) (.ADDI .x29 .x0 13) rfl pc7 rfl rfl
  obtain ⟨s9, run9, pc9, read9, write9, other9, bytes9⟩ :=
    s6_siblings_runs orig base count record present evenBase window 12 s8 (by omega)
      (by rw [s6_addi_pc, pc7, s6_pc_next])
      (by rw [s6_addi_zero _ _ _ (by decide)]; decide)
      (by rw [s6_addi_reg _ _ _ _ _ (by decide), read7]; exact congrArg (BitVec.ofNat 64) (by omega))
      (by rw [s6_addi_reg _ _ _ _ _ (by decide), write7]; exact congrArg (BitVec.ofNat 64) (by omega))
      (nonce_compacted_mem (by
          rw [show 560 * record + 144 + 32 * (12 - 12) = 560 * record + 16 + 2 * (63 + 1) by omega]
          exact bytes7) (s6_addi_mem _ _ _ _))
  -- count down the records
  let s10 := execInstrBr s9 (.ADDI .x24 .x24 4095)
  have run10 := s6_step s9 15 (by omega) (.ADDI .x24 .x24 4095) rfl pc9 rfl rfl
  have pc10 : s10.pc = BitVec.ofNat 64 (4864 + 4 * 16) := by rw [s6_addi_pc, pc9, s6_pc_next]
  have run11 := s6_step s10 16 (by omega) (.BNE .x24 .x0 8148) rfl pc10 rfl rfl
  have keep : ∀ reg, reg ≠ .x1 → reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x24 → reg ≠ .x25 → reg ≠ .x28 →
      reg ≠ .x29 → s9.getReg reg = state.getReg reg := by
    intro reg r1 r6 r23 r24 r25 r28 r29
    rw [other9 reg r1 r6 r23 r25 r29, s6_addi_reg _ _ _ _ _ r29, other7 reg r6 r23 r25 r28,
      call6.2.2.1 _ r1, s6_addi_reg _ _ _ _ _ r28, s6_addi_reg _ _ _ _ _ r23, other3 reg r6 r23 r25 r28,
      call2.2.2.1 _ r1, s6_addi_reg _ _ _ _ _ r28]
  have counter9 : s9.getReg .x24 = BitVec.ofNat 64 (count - record) := by
    rw [other9 .x24 (by decide) (by decide) (by decide) (by decide) (by decide), s6_addi_reg _ _ _ _ _ (by decide),
      other7 .x24 (by decide) (by decide) (by decide) (by decide), call6.2.2.1 _ (by decide),
      s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide),
      other3 .x24 (by decide) (by decide) (by decide) (by decide), call2.2.2.1 _ (by decide),
      s6_addi_reg _ _ _ _ _ (by decide), counter]
  have counter10 : s10.getReg .x24 = BitVec.ofNat 64 (count - (record + 1)) := by
    rw [s6_addi_self _ _ _ _ (by decide), counter9, s6_decrement _ (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have branch := s6_branch_reg s10 .x24 .x0 8148
  have total := nonce_runs_trans (nonce_runs_trans (nonce_runs_trans (nonce_runs_trans (nonce_runs_trans
    (nonce_runs_trans (nonce_runs_trans (nonce_runs_trans (nonce_runs_trans (nonce_runs_trans
      run1 run2) run3) run4) run5) run6) run7) run8) run9) run10) run11
  refine ⟨_, total, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [s6_bne_pc s10 .x24 8148 (count - (record + 1)) (by omega) counter10, pc10]
    by_cases last : record + 1 = count
    · rw [if_pos (by omega : count - (record + 1) = 0), if_pos last, s6_pc_next]
    · rw [if_neg (by omega : ¬ count - (record + 1) = 0), if_neg last]
      decide
  · rw [(branch .x24).1, counter10]
  · rw [(branch .x23).1, s6_addi_reg _ _ _ _ _ (by decide), read9]
  · rw [(branch .x25).1, s6_addi_reg _ _ _ _ _ (by decide), write9]
  · intro reg r1 r6 r23 r24 r25 r28 r29
    rw [(branch reg).1, s6_addi_reg _ _ _ _ _ r24, keep reg r1 r6 r23 r24 r25 r28 r29]
  · exact nonce_compacted_mem bytes9 (by rw [(s6_branch_mem s10 .x24 .x0 8148).1, s6_addi_mem])

end CommitGolfCandidate
