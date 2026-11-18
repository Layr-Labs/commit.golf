import CommitGolfCandidate.NonceCompactPass

/-! The whole compaction from its entry (word 192) to its success halt: entry moves, all records,
the footer nodes and the length report. Exactly `10 + 949 count + 39 nodes` cycles, no oracle call;
the output bytes are `s6Pack` of the internal proof (pointwise, as `NonceCompacted`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Cycles of the compaction for `count` records and `nodes` footer nodes. -/
def nonceCodecCycles (count nodes : Nat) : Nat := 10 + 949 * count + 39 * nodes

theorem s6_records_runs (orig : MachineState) (base count : Nat)
    (evenBase : base % 2 = 0) (window : base + 576 * count ≤ MEMORY_BYTES) (countSmall : count < 2 ^ 64) :
    ∀ (left record : Nat) (state : MachineState), record + (left + 1) = count →
    state.pc = BitVec.ofNat 64 (4864 + 4 * 5) →
    state.getReg .x24 = BitVec.ofNat 64 (count - record) →
    state.getReg .x23 = BitVec.ofNat 64 (base + 576 * record) →
    state.getReg .x25 = BitVec.ofNat 64 (base + 560 * record) →
    NonceCompacted orig base count (560 * record) state →
    ∃ next, NonceRuns s6OpeningImage (949 * (left + 1)) state next ∧
      next.pc = BitVec.ofNat 64 (4864 + 4 * 17) ∧
      next.getReg .x23 = BitVec.ofNat 64 (base + 576 * count) ∧
      next.getReg .x25 = BitVec.ofNat 64 (base + 560 * count) ∧
      (∀ reg, reg ≠ .x1 → reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x24 → reg ≠ .x25 → reg ≠ .x28 → reg ≠ .x29 →
        next.getReg reg = state.getReg reg) ∧
      NonceCompacted orig base count (560 * count) next := by
  intro left
  induction left with
  | zero =>
    intro record state total pc counter read write before
    obtain ⟨next, runs, nextPc, _, nextRead, nextWrite, nextOther, nextBytes⟩ :=
      s6_record_runs orig state base count record (by omega) evenBase window countSmall pc counter read
        write before
    rw [if_pos (by omega)] at nextPc
    have last : record + 1 = count := by omega
    rw [last] at nextRead nextWrite nextBytes
    exact ⟨next, runs, nextPc, nextRead, nextWrite, nextOther, nextBytes⟩
  | succ left ih =>
    intro record state total pc counter read write before
    obtain ⟨mid, runs, midPc, midCounter, midRead, midWrite, midOther, midBytes⟩ :=
      s6_record_runs orig state base count record (by omega) evenBase window countSmall pc counter read
        write before
    rw [if_neg (by omega)] at midPc
    obtain ⟨next, nextRuns, nextPc, nextRead, nextWrite, nextOther, nextBytes⟩ :=
      ih (record + 1) mid (by omega) midPc midCounter midRead midWrite midBytes
    refine ⟨next, ?_, nextPc, nextRead, nextWrite, ?_, nextBytes⟩
    · have whole := nonce_runs_trans runs nextRuns
      rwa [show 949 + 949 * (left + 1) = 949 * (left + 1 + 1) by ring] at whole
    · intro reg r1 r6 r23 r24 r25 r28 r29
      rw [nextOther reg r1 r6 r23 r24 r25 r28 r29, midOther reg r1 r6 r23 r24 r25 r28 r29]

theorem s6_footer_sources (count node i : Nat) (inside : i < 32) :
    s6PackSource count (560 * count + 32 * node + i) = 576 * count + 32 * node + i := by
  rw [show 560 * count + 32 * node + i = 560 * count + (32 * node + i) by omega, s6_pack_source_footer]
  simp only [s6NodeSource]
  omega

theorem s6_footer_runs (orig : MachineState) (base count nodes : Nat) (evenBase : base % 2 = 0)
    (window : base + 576 * count + 32 * nodes ≤ MEMORY_BYTES) :
    ∀ (left node : Nat) (state : MachineState), node + left = nodes →
    state.pc = BitVec.ofNat 64 (4864 + 4 * 17) →
    state.getReg .x23 = BitVec.ofNat 64 (base + (576 * count + 32 * node)) →
    state.getReg .x25 = BitVec.ofNat 64 (base + (560 * count + 32 * node)) →
    state.getReg .x22 = BitVec.ofNat 64 (base + 576 * count + 32 * nodes) →
    NonceCompacted orig base count (560 * count + 32 * node) state →
    ∃ next, NonceRuns s6OpeningImage (39 * left + 1) state next ∧
      next.pc = BitVec.ofNat 64 (4864 + 4 * 21) ∧
      next.getReg .x25 = BitVec.ofNat 64 (base + (560 * count + 32 * nodes)) ∧
      (∀ reg, reg ≠ .x1 → reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → next.getReg reg = state.getReg reg) ∧
      NonceCompacted orig base count (560 * count + 32 * nodes) next := by
  have small : base + 576 * count + 32 * nodes < 2 ^ 64 := by unfold MEMORY_BYTES at window; omega
  have twoExt : signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 0 := by decide
  intro left
  induction left with
  | zero =>
    intro node state total pc read write finish before
    have same : state.getReg .x23 = state.getReg .x22 := by
      rw [read, finish]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have run := s6_step state 17 (by omega) (.BEQ .x23 .x22 16) rfl pc rfl rfl
    have branch := s6_branch_reg state .x23 .x22 16
    refine ⟨_, run, ?_, ?_, ?_, ?_⟩
    · rw [s6_beq_pc, if_pos same, pc]
      decide
    · rw [(branch .x25).2, write]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · intro reg _ _ _ _
      exact (branch reg).2
    · have shape : node = nodes := by omega
      rw [shape] at before
      exact nonce_compacted_mem before (s6_branch_mem state .x23 .x22 16).2
  | succ left ih =>
    intro node state total pc read write finish before
    have different : state.getReg .x23 ≠ state.getReg .x22 := by
      rw [read, finish]
      exact s6_ofNat_ne (by omega) (by omega) (by omega)
    let s1 := execInstrBr state (.BEQ .x23 .x22 16)
    have run1 := s6_step state 17 (by omega) (.BEQ .x23 .x22 16) rfl pc rfl rfl
    have pc1 : s1.pc = BitVec.ofNat 64 (4864 + 4 * 18) := by
      rw [s6_beq_pc, if_neg different, pc, s6_pc_next]
    have branch1 := s6_branch_reg state .x23 .x22 16
    let s2 := execInstrBr s1 (.JAL .x1 56)
    have run2 := s6_step s1 18 (by omega) (.JAL .x1 56) rfl pc1 rfl rfl
    have call := s6_jal_effect s1 .x1 56 (by decide)
    have link : s2.getReg .x1 = BitVec.ofNat 64 (4864 + 4 * 19) := by rw [call.2.1, pc1]; decide
    obtain ⟨s3, run3, pc3, read3, write3, other3, bytes3⟩ :=
      s6_field_runs orig s2 base count (560 * count + 32 * node) (576 * count + 32 * node)
        (by rw [call.1, pc1]; decide)
        (by rw [call.2.2.1 _ (by decide), (branch1 .x23).2, read])
        (by rw [call.2.2.1 _ (by decide), (branch1 .x25).2, write])
        (by rw [link]; decide)
        (nonce_compacted_mem before (by rw [call.2.2.2, (s6_branch_mem state .x23 .x22 16).2]))
        (fun i inside => s6_footer_sources count node i inside)
        (by omega) evenBase (by omega) (by omega) (by unfold MEMORY_BYTES; unfold MEMORY_BYTES at window; omega)
    rw [link] at pc3
    let s4 := execInstrBr s3 (.ADDI .x23 .x23 0)
    have run4 := s6_step s3 19 (by omega) (.ADDI .x23 .x23 0) rfl pc3 rfl rfl
    have pc4 : s4.pc = BitVec.ofNat 64 (4864 + 4 * 20) := by rw [s6_addi_pc, pc3, s6_pc_next]
    let s5 := execInstrBr s4 (.JAL .x0 2097140)
    have run5 := s6_step s4 20 (by omega) (.JAL .x0 2097140) rfl pc4 rfl rfl
    have back := s6_compact_jal_zero s4 2097140
    have keep : ∀ reg, reg ≠ .x1 → reg ≠ .x6 → reg ≠ .x23 → reg ≠ .x25 → s5.getReg reg = state.getReg reg := by
      intro reg r1 r6 r23 r25
      rw [back.2.1, s6_addi_reg _ _ _ _ _ r23, other3 reg r6 r23 r25, call.2.2.1 _ r1, (branch1 reg).2]
    obtain ⟨next, nextRuns, nextPc, nextWrite, nextOther, nextBytes⟩ :=
      ih (node + 1) s5 (by omega) (by rw [back.1, pc4]; decide)
        (by rw [back.2.1, s6_addi_self _ _ _ _ (by decide), read3, twoExt, s6_add_ofNat]
            exact congrArg (BitVec.ofNat 64) (by omega))
        (by rw [back.2.1, s6_addi_reg _ _ _ _ _ (by decide), write3]
            exact congrArg (BitVec.ofNat 64) (by omega))
        (by rw [keep .x22 (by decide) (by decide) (by decide) (by decide), finish])
        (nonce_compacted_mem (by
            rw [show 560 * count + 32 * (node + 1) = 560 * count + 32 * node + 32 by ring]
            exact bytes3) (by rw [back.2.2, s6_addi_mem]))
    refine ⟨next, ?_, nextPc, nextWrite, ?_, nextBytes⟩
    · have whole := nonce_runs_trans (nonce_runs_trans (nonce_runs_trans (nonce_runs_trans
        (nonce_runs_trans run1 run2) run3) run4) run5) nextRuns
      rwa [show 1 + 1 + 35 + 1 + 1 + (39 * left + 1) = 39 * (left + 1) + 1 by ring] at whole
    · intro reg r1 r6 r23 r25
      rw [nextOther reg r1 r6 r23 r25, keep reg r1 r6 r23 r25]

theorem s6_sub_self (state : MachineState) (rd rs1 rs2 : Reg) (nonzero : rd ≠ .x0) :
    (execInstrBr state (.SUB rd rs1 rs2)).getReg rd = state.getReg rs1 - state.getReg rs2 := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq nonzero]

theorem s6_sub_mem (state : MachineState) (rd rs1 rs2 : Reg) :
    (execInstrBr state (.SUB rd rs1 rs2)).mem = state.mem := by
  simp only [execInstrBr, MachineState.setPC, s6_set_reg_mem]

/-- The length report and success halt (words 213..216). -/
theorem s6_exit_runs (state : MachineState) (base length : Nat)
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * 21))
    (proofBase : state.getReg .x15 = BitVec.ofNat 64 base)
    (finish : state.getReg .x25 = BitVec.ofNat 64 (base + length)) (noWrap : base + length < 2 ^ 64) :
    ∃ final, (∀ fuel coins, execute s6OpeningImage (4 + fuel) state coins = pure ⟨.success, final, 4, 0⟩) ∧
      (final.getReg .x11).toNat = length ∧ final.mem = state.mem := by
  let s1 := execInstrBr state (.SUB .x11 .x25 .x15)
  have run1 := s6_step state 21 (by omega) (.SUB .x11 .x25 .x15) rfl pc rfl rfl
  let s2 := execInstrBr s1 (.ADDI .x5 .x0 1)
  have run2 := s6_step s1 22 (by omega) (.ADDI .x5 .x0 1) rfl
    (by change state.pc + 4 = _; rw [pc, s6_pc_next]) rfl rfl
  let s3 := execInstrBr s2 (.ADDI .x10 .x0 0)
  have pc2 : s2.pc = BitVec.ofNat 64 (4864 + 4 * 23) := by
    change state.pc + 4 + 4 = _
    rw [pc, s6_pc_next, s6_pc_next]
  have run3 := s6_step s2 23 (by omega) (.ADDI .x10 .x0 0) rfl pc2 rfl rfl
  have pc3 : s3.pc = BitVec.ofNat 64 (4864 + 4 * 24) := by rw [s6_addi_pc, pc2, s6_pc_next]
  have fetched : fetch s6OpeningImage s3 = some (.base .ECALL) := s6_compact_fetch s3 24 (by omega) pc3
  have selector : s3.getReg .x5 = 1 := by
    rw [s6_addi_reg _ _ _ _ _ (by decide), s6_addi_zero _ _ _ (by decide)]
    decide
  have success : s3.getReg .x10 = 0 := by
    rw [s6_addi_zero _ _ _ (by decide)]
    decide
  have halt : ∀ fuel coins, execute s6OpeningImage (1 + fuel) s3 coins = pure ⟨.success, s3, 1, 0⟩ := by
    intro fuel coins
    rw [Nat.add_comm 1 fuel]
    simp [execute, fetched, selector, success]
  have runs := nonce_runs_trans (nonce_runs_trans run1 run2) run3
  refine ⟨s3, ?_, ?_, ?_⟩
  · intro fuel coins
    rw [show 4 + fuel = 1 + 1 + 1 + (1 + fuel) by omega, runs, halt]
    simp [Execution.charge]
  · have report : s3.getReg .x11 = state.getReg .x25 - state.getReg .x15 := by
      rw [s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide), s6_sub_self _ _ _ _ (by decide)]
    rw [report, finish, proofBase, BitVec.ofNat_add, BitVec.add_comm, BitVec.add_sub_cancel,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [s6_addi_mem, s6_addi_mem, s6_sub_mem]

/-- The whole compaction, from word 192 with the internal proof of `count` records and `nodes`
footer nodes at `base` (end in x25), to the success halt. -/
theorem s6_compact_run (state : MachineState) (base count nodes : Nat)
    (pc : state.pc = BitVec.ofNat 64 4864)
    (proofBase : state.getReg .x15 = BitVec.ofNat 64 base)
    (counter : state.getReg .x16 = BitVec.ofNat 64 count)
    (oldEnd : state.getReg .x25 = BitVec.ofNat 64 (base + 576 * count + 32 * nodes))
    (aligned : base % 8 = 0) (window : base + 576 * count + 32 * nodes ≤ MEMORY_BYTES) :
    ∃ final, (∀ fuel coins, execute s6OpeningImage (nonceCodecCycles count nodes + fuel) state coins =
        pure ⟨.success, final, nonceCodecCycles count nodes, 0⟩) ∧
      (final.getReg .x11).toNat = 560 * count + 32 * nodes ∧
      NonceCompacted state base count (560 * count + 32 * nodes) final := by
  have small : base + 576 * count + 32 * nodes < 2 ^ 64 := by unfold MEMORY_BYTES at window; omega
  have countSmall : count < 2 ^ 64 := by omega
  have zeroExt : signExtend12 (0 : BitVec 12) = BitVec.ofNat 64 0 := by decide
  -- entry (words 192..196)
  let s1 := execInstrBr state (.ADDI .x22 .x25 0)
  let s2 := execInstrBr s1 (.ADDI .x23 .x15 0)
  let s3 := execInstrBr s2 (.ADDI .x25 .x15 0)
  let s4 := execInstrBr s3 (.ADDI .x24 .x16 0)
  have run1 := s6_step state 0 (by omega) (.ADDI .x22 .x25 0) rfl (by rw [pc]) rfl rfl
  have run2 := s6_step s1 1 (by omega) (.ADDI .x23 .x15 0) rfl (by rw [s6_addi_pc, pc]; decide) rfl rfl
  have pc2 : s2.pc = BitVec.ofNat 64 (4864 + 4 * 2) := by rw [s6_addi_pc, s6_addi_pc, pc]; decide
  have run3 := s6_step s2 2 (by omega) (.ADDI .x25 .x15 0) rfl pc2 rfl rfl
  have run4 := s6_step s3 3 (by omega) (.ADDI .x24 .x16 0) rfl (by rw [s6_addi_pc, pc2, s6_pc_next]) rfl rfl
  have pc4 : s4.pc = BitVec.ofNat 64 (4864 + 4 * 4) := by rw [s6_addi_pc, s6_addi_pc, pc2, s6_pc_next, s6_pc_next]
  let s5 := execInstrBr s4 (.BEQ .x24 .x0 52)
  have run5 := s6_step s4 4 (by omega) (.BEQ .x24 .x0 52) rfl pc4 rfl rfl
  have branch := s6_branch_reg s4 .x24 .x0 52
  have finish5 : s5.getReg .x22 = BitVec.ofNat 64 (base + 576 * count + 32 * nodes) := by
    rw [(branch .x22).2, s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide),
      s6_addi_reg _ _ _ _ _ (by decide), s6_addi_self _ _ _ _ (by decide), oldEnd, zeroExt, s6_add_ofNat,
      Nat.add_zero]
  have read5 : s5.getReg .x23 = BitVec.ofNat 64 (base + 0) := by
    rw [(branch .x23).2, s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide),
      s6_addi_self _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide), proofBase, zeroExt, s6_add_ofNat]
  have write5 : s5.getReg .x25 = BitVec.ofNat 64 (base + 0) := by
    rw [(branch .x25).2, s6_addi_reg _ _ _ _ _ (by decide), s6_addi_self _ _ _ _ (by decide),
      s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide), proofBase, zeroExt, s6_add_ofNat]
  have counter5 : s5.getReg .x24 = BitVec.ofNat 64 (count - 0) := by
    rw [(branch .x24).2, s6_addi_self _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide),
      s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide), counter, zeroExt, s6_add_ofNat,
      Nat.add_zero, Nat.sub_zero]
  have base5 : s5.getReg .x15 = BitVec.ofNat 64 base := by
    rw [(branch .x15).2, s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide),
      s6_addi_reg _ _ _ _ _ (by decide), s6_addi_reg _ _ _ _ _ (by decide), proofBase]
  have mem5 : s5.mem = state.mem := by
    rw [(s6_branch_mem s4 .x24 .x0 52).2, s6_addi_mem, s6_addi_mem, s6_addi_mem, s6_addi_mem]
  have bytes5 : NonceCompacted state base count 0 s5 :=
    nonce_compacted_mem (nonce_compacted_start state base count) mem5
  have entry := nonce_runs_trans (nonce_runs_trans (nonce_runs_trans (nonce_runs_trans run1 run2) run3) run4) run5
  have pc5 : s5.pc = (if count = 0 then BitVec.ofNat 64 (4864 + 4 * 17) else BitVec.ofNat 64 (4864 + 4 * 5)) := by
    have zero : s4.getReg .x0 = 0 := rfl
    have value : s4.getReg .x24 = BitVec.ofNat 64 count := by
      rw [← (branch .x24).2, counter5, Nat.sub_zero]
    rw [s6_beq_pc, value, zero, pc4]
    by_cases empty : count = 0
    · rw [if_pos (by rw [empty]; rfl), if_pos empty]
      decide
    · rw [if_neg (fun same => empty ((s6_ofNat_eq_zero count countSmall).mp same)), if_neg empty, s6_pc_next]
  -- all records, then the footer: reach word 209 with the record part done
  have records : ∃ middle, NonceRuns s6OpeningImage (5 + 949 * count) state middle ∧
      middle.pc = BitVec.ofNat 64 (4864 + 4 * 17) ∧
      middle.getReg .x23 = BitVec.ofNat 64 (base + (576 * count + 32 * 0)) ∧
      middle.getReg .x25 = BitVec.ofNat 64 (base + (560 * count + 32 * 0)) ∧
      middle.getReg .x22 = BitVec.ofNat 64 (base + 576 * count + 32 * nodes) ∧
      middle.getReg .x15 = BitVec.ofNat 64 base ∧
      NonceCompacted state base count (560 * count + 32 * 0) middle := by
    by_cases empty : count = 0
    · rw [if_pos empty] at pc5
      subst count
      exact ⟨s5, entry, pc5, read5, write5, finish5, base5, bytes5⟩
    · rw [if_neg empty] at pc5
      obtain ⟨middle, recordRuns, middlePc, middleRead, middleWrite, middleOther, middleBytes⟩ :=
        s6_records_runs state base count (by omega) (by omega) countSmall (count - 1) 0 s5 (by omega) pc5
          counter5 (by rw [read5]) (by rw [write5]) (by simpa using bytes5)
      refine ⟨middle, ?_, middlePc, ?_, ?_, ?_, ?_, ?_⟩
      · have whole := nonce_runs_trans entry recordRuns
        rwa [show 1 + 1 + 1 + 1 + 1 + 949 * (count - 1 + 1) = 5 + 949 * count by
          rw [Nat.sub_add_cancel (by omega)]] at whole
      · rw [middleRead]; exact congrArg (BitVec.ofNat 64) (by omega)
      · rw [middleWrite]; exact congrArg (BitVec.ofNat 64) (by omega)
      · rw [middleOther .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          finish5]
      · rw [middleOther .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          base5]
      · simpa using middleBytes
  obtain ⟨middle, recordRuns, middlePc, middleRead, middleWrite, middleFinish, middleBase, middleBytes⟩ := records
  obtain ⟨footed, footerRuns, footedPc, footedWrite, footedOther, footedBytes⟩ :=
    s6_footer_runs state base count nodes (by omega) window nodes 0 middle (by omega) middlePc middleRead
      middleWrite middleFinish middleBytes
  obtain ⟨final, finalRuns, finalReport, finalMem⟩ :=
    s6_exit_runs footed base (560 * count + 32 * nodes) footedPc
      (by rw [footedOther .x15 (by decide) (by decide) (by decide) (by decide), middleBase])
      footedWrite (by omega)
  have prefixRuns := nonce_runs_trans recordRuns footerRuns
  refine ⟨final, ?_, finalReport, nonce_compacted_mem footedBytes finalMem⟩
  intro fuel coins
  rw [show nonceCodecCycles count nodes + fuel = 5 + 949 * count + (39 * nodes + 1) + (4 + fuel) by
    unfold nonceCodecCycles; ring, prefixRuns, finalRuns]
  simp only [pure_bind, Execution.charge]
  congr 2
  unfold nonceCodecCycles
  ring

end CommitGolfCandidate
