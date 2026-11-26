import CommitGolfCandidate.MoonCommitLeaf

/-! Exact RV64IM execution proof for Phase 2 (pure 3-ary FIFO queue loop, `8,388,608` calls,
`U_Q3 = 256`, `32,768` chunks, words `3374..4149`) and Phase 3 (copy 32-byte `ROOT` to
`commitment` + `HALT(0)`, words `4150..4160`) of the `commit` image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Phase 2 Setup (`words 3374..3380`) and Branch Arithmetic -/

private def commitMid1CInstrs : List Instr :=
  [.ADDI .x10 .x9 (4000#12),
   .ADDI .x6 .x0 (128#12), .SLLI .x6 .x6 (11#6), .SLLI .x6 .x6 (11#6),
   .ADD .x12 .x9 .x6, .ADDI .x12 .x12 (4064#12),
   .ADDI .x19 .x18 (4000#12)]

private theorem pc_bne_4149 :
    BitVec.ofNat 64 (0x1000 + 4 * 4149) + signExtend13 (5120#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 3381) := by decide

private theorem commit_mid1C_run (oracle : Oracle) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 3374)) :
    DetRun oracle (submission.image .commit) s0 7 (commitMid1CInstrs.foldl execInstrBr s0) 7 0 := by
  have hall : ∀ ins ∈ commitMid1CInstrs, isPureAlu ins = true := by decide
  apply exec_alu_list commitMid1CInstrs s0
  intro i hi
  have hi' : i < 7 := hi
  have hpc_i : ((commitMid1CInstrs.take i).foldl execInstrBr s0).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (3374 + i)) := by
    have h := foldl_pureAlu_pc (commitMid1CInstrs.take i) s0 (0x1000 + 4 * 3374)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitMid1CInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem commit_mid1C_spec (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 3374))
    (hx5 : s0.getReg .x5 = 0#64)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64)
    (hx13 : s0.getReg .x13 = 0#64)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s1 := commitMid1CInstrs.foldl execInstrBr s0
    s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 3381) ∧
    s1.mem = s0.mem ∧
    s1.getReg .x5 = 0#64 ∧
    s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s1.getReg .x10 = BitVec.ofNat 64 (C_TD - 96) ∧
    s1.getReg .x11 = 96#64 ∧
    s1.getReg .x12 = BitVec.ofNat 64 (C_TD + 536870912 - 32) ∧
    s1.getReg .x13 = 0#64 ∧
    s1.getReg .x19 = BitVec.ofNat 64 (C_ROW - 96) ∧
    s1.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ commitMid1CInstrs, isPureAlu ins = true := by decide
  refine ⟨?_, foldl_pureAlu_mem commitMid1CInstrs s0 hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (foldl_pureAlu_pc commitMid1CInstrs s0 (0x1000 + 4 * 3374) hall hpc).trans (by decide)
  all_goals (
    simp only [commitMid1CInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx5, hx9, hx11, hx13, hx18, hx26]
    try decide)

/-! ### 2. Single Queue Step, 256-Call Chunk, and Full `8,388,608`-Call Queue Loop -/

private theorem commit_q3_step (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (k j : Nat) (hk : k < 256) (hj : j < QUEUE_CALLS)
    (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (3381 + 3 * k)))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * j - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + j) - 32))
    (hprev : ∀ v < LENGTH + j,
      readBuffer s (C_TD + 32 * v) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts v)
    (hzeroRoot : j = QUEUE_CALLS - 1 → readBuffer s (C_TD + 32 * ROOT_NODE) 32 = 0) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s',
      DetRun oracle (submission.image .commit) s 3 s' 10 1 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (3381 + 3 * (k + 1))) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (j + 1) - 96) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + (j + 1)) - 32) ∧
      readBuffer s' (C_TD + 32 * (LENGTH + j)) 32 = nodeVal c96 msg salts (LENGTH + j) ∧
      MemPreservedOutside s s' (C_TD + 32 * (LENGTH + j)) (C_TD + 32 * (LENGTH + j) + 32) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hQC : QUEUE_CALLS = 8388608 := queueCalls_eq
  have hRN : ROOT_NODE = 25165823 := rootNode_eq
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let out := nodeVal c96 msg salts (LENGTH + j)
  have hout : oracle.compression ((readBuffer s (C_TD + 96 * j - 96 + 96) 96).cast h768.symm) = out := by
    have hsrc : C_TD + 96 * j - 96 + 96 = C_TD + 32 * (3 * j) := by omega
    rw [hsrc, readBuffer_ternary]
    have ha1 : C_TD + 32 * (3 * j) + 32 = C_TD + 32 * (3 * j + 1) := by omega
    have ha2 : C_TD + 32 * (3 * j) + 64 = C_TD + 32 * (3 * j + 2) := by omega
    rw [ha1, ha2, hprev (3 * j) (by omega), hprev (3 * j + 1) (by omega)]
    by_cases hlast : j = QUEUE_CALLS - 1
    · subst hlast
      have h2eq : 3 * (QUEUE_CALLS - 1) + 2 = ROOT_NODE := by omega
      have h1eq : 3 * (QUEUE_CALLS - 1) + 1 = 25165822 := by omega
      have h0eq : 3 * (QUEUE_CALLS - 1) = 25165821 := by omega
      have hrt : LENGTH + (QUEUE_CALLS - 1) = ROOT_NODE := by omega
      rw [h2eq, hzeroRoot rfl, h1eq, h0eq]
      change c96 (ternaryInput (nodeVal c96 msg salts 25165821) (nodeVal c96 msg salts 25165822) 0) = out
      dsimp only [out]
      unfold nodeVal
      rw [hrt, nodeValFromLeaves_root]
    · rw [hprev (3 * j + 2) (by omega)]
      dsimp only [out]
      unfold nodeVal
      rw [nodeValFromLeaves_internal c96 _ j (by omega)]
  obtain ⟨s', hrun, hpc', hreg', hx10', hx12', hdig, hpres⟩ :=
    commit_inc_compress h768 oracle s (3381 + 3 * k)
      (C_TD + 96 * j - 96) (C_TD + 32 * (LENGTH + j) - 32) 96 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hpc hx5 hx11 hx13 hx10 hx12
      (commit_fetch_q3 s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc))
      (fun st hst => commit_fetch_q3 st k 1 hk (by omega) hst)
      (fun st hst => commit_fetch_q3 st k 2 hk (by omega) hst) out hout
  refine ⟨s', hrun,
    hpc'.trans (congrArg (BitVec.ofNat 64) (by omega)), hreg',
    hx10'.trans (congrArg (BitVec.ofNat 64) (by omega)),
    hx12'.trans (congrArg (BitVec.ofNat 64) (by omega)),
    ?_, ?_⟩
  · simpa only [show C_TD + 32 * (LENGTH + j) - 32 + 32 = C_TD + 32 * (LENGTH + j) by omega] using hdig
  · simpa only [show C_TD + 32 * (LENGTH + j) - 32 + 32 = C_TD + 32 * (LENGTH + j) by omega] using hpres

private theorem commit_q3_chunk (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (ch : Nat) (hch : ch < 32768)
    (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 3381))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (256 * ch) - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 256 * ch) - 32))
    (hx19 : s.getReg .x19 = BitVec.ofNat 64 (C_ROW - 96))
    (hprev : ∀ v < LENGTH + 256 * ch,
      readBuffer s (C_TD + 32 * v) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts v)
    (hzeroRoot : readBuffer s (C_TD + 32 * ROOT_NODE) 32 = 0) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s',
      DetRun oracle (submission.image .commit) s 769 s' 2561 256 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (if ch + 1 < 32768 then 3381 else 4150)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (256 * (ch + 1)) - 96) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 256 * (ch + 1)) - 32) ∧
      (∀ v < LENGTH + 256 * (ch + 1),
        readBuffer s' (C_TD + 32 * v) 32 = nodeVal c96 msg salts v) ∧
      MemPreservedOutside s s' (C_TD + 32 * (LENGTH + 256 * ch)) (C_TD + 32 * (LENGTH + 256 * (ch + 1))) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5100277792 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hQC : QUEUE_CALLS = 8388608 := queueCalls_eq
  have hRN : ROOT_NODE = 25165823 := rootNode_eq
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hbody : ∀ k ≤ 256,
      ∃ sk,
        DetRun oracle (submission.image .commit) s (3 * k) sk (10 * k) k ∧
        sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (3381 + 3 * k)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sk.getReg r = s.getReg r) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (256 * ch + k) - 96) ∧
        sk.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + (256 * ch + k)) - 32) ∧
        (∀ v < LENGTH + (256 * ch + k),
          readBuffer sk (C_TD + 32 * v) 32 = nodeVal c96 msg salts v) ∧
        MemPreservedOutside s sk (C_TD + 32 * (LENGTH + 256 * ch)) (C_TD + 32 * (LENGTH + 256 * ch + k)) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨s, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12, by simpa using hprev,
        MemPreservedOutside.refl _ _ _⟩
    | succ k ih =>
      obtain ⟨sk, hrun, hpck, hregk, hx10k, hx12k, hdigk, hpresk⟩ := ih (by omega)
      have hzr : 256 * ch + k = QUEUE_CALLS - 1 → readBuffer sk (C_TD + 32 * ROOT_NODE) 32 = 0 := by
        intro hlast
        rw [hpresk.readBuffer_eq (by omega) (by omega)]
        exact hzeroRoot
      obtain ⟨sk1, hr1, hpc1, hreg1, hx10_1, hx12_1, hdig1, hp1⟩ :=
        commit_q3_step h768 oracle msg salts k (256 * ch + k) (by omega) (by omega) sk hpck
          ((hregk .x5 (by decide) (by decide)).trans hx5)
          ((hregk .x11 (by decide) (by decide)).trans hx11)
          ((hregk .x13 (by decide) (by decide)).trans hx13) hx10k hx12k hdigk hzr
      refine ⟨sk1, ?_, hpc1,
        fun r h10 h12 => (hreg1 r h10 h12).trans (hregk r h10 h12),
        hx10_1.trans (congrArg (BitVec.ofNat 64) (by omega)),
        hx12_1.trans (congrArg (BitVec.ofNat 64) (by omega)),
        ?_,
        (hpresk.mono (le_refl _) (by omega)).trans (hp1.mono (by omega) (by omega))⟩
      · have h := hrun.trans hr1
        rw [show 3 * k + 3 = 3 * (k + 1) by omega,
            show 10 * k + 10 = 10 * (k + 1) by omega] at h
        exact h
      · intro v hv
        by_cases heq : v = LENGTH + (256 * ch + k)
        · subst heq; exact hdig1
        · rw [hp1.readBuffer_eq (by omega) (by omega)]
          exact hdigk v (by omega)
  obtain ⟨sb, hrunb, hpcb, hregb, hx10b, hx12b, hdigb, hpresb⟩ := hbody 256 (le_refl _)
  have hpcb' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 4149) := by
    simpa only [show 3381 + 3 * 256 = 4149 by omega] using hpcb
  have hfetch_bne : fetch (submission.image .commit) sb = some (.base (.BNE .x10 .x19 (5120#13))) :=
    commit_fetch_commitTailInstr sb 4149 (by omega) (by omega) hpcb'
  let sbne := execInstrBr sb (.BNE .x10 .x19 (5120#13))
  have hbne_run : DetRun oracle (submission.image .commit) sb 1 sbne 1 0 :=
    DetRun.step1 hfetch_bne rfl
  have hmem_bne : sbne.mem = sb.mem := mem_exec_BNE sb .x10 .x19 (5120#13)
  have hreg_bne : ∀ r : Reg, sbne.getReg r = sb.getReg r := reg_exec_BNE sb .x10 .x19 (5120#13)
  have hx19b : sb.getReg .x19 = BitVec.ofNat 64 (C_ROW - 96) :=
    (hregb .x19 (by decide) (by decide)).trans hx19
  have hpc_bne : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if ch + 1 < 32768 then 3381 else 4150)) := by
    by_cases hlt : ch + 1 < 32768
    · have hne : (sb.getReg .x10 != sb.getReg .x19) = true := by
        rw [hx10b, hx19b, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hlt, ite_true, sbne, execInstrBr, hne, pc_setPC, hpcb']
      exact pc_bne_4149
    · have heq : (sb.getReg .x10 != sb.getReg .x19) = false := by
        rw [hx10b, hx19b, show C_TD + 96 * (256 * ch + 256) - 96 = C_ROW - 96 by omega]
        exact bne_self_eq_false _
      simp only [hlt, ite_false, sbne, execInstrBr, heq, Bool.false_eq_true, pc_setPC]
      exact pc_step_idx sb 4149 hpcb'
  refine ⟨sbne, by simpa using hrunb.trans hbne_run, hpc_bne,
    fun r h10 h12 => (hreg_bne r).trans (hregb r h10 h12),
    (hreg_bne .x10).trans (hx10b.trans (congrArg (BitVec.ofNat 64) (by omega))),
    (hreg_bne .x12).trans (hx12b.trans (congrArg (BitVec.ofNat 64) (by omega))),
    fun v hv => by
      rw [readBuffer_of_mem_eq hmem_bne]
      exact hdigb v (by omega),
    (hpresb.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmem_bne _ _)⟩

/-! ### 3. Phase 3: Copy 32-Byte Root to `commitment` + `HALT(0)` (`words 4150..4160`) -/

private theorem commit_copy_root_halt (oracle : Oracle) (root : Digest) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 4150))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * ROOT_NODE))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hroot : readBuffer s (C_TD + 32 * ROOT_NODE) 32 = root) :
    ∃ sfin,
      (∀ extra,
        oracle.run (execute (submission.image .commit) (11 + extra) s true) =
          pure (⟨.success, sfin, 11, 0⟩, 0)) ∧
      readBuffer sfin C_CMT 32 = root ∧
      MemPreservedOutside s sfin C_CMT (C_CMT + 32) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_CMT : C_CMT = 4294971392 := rfl
  have hRN : ROOT_NODE = 25165823 := rootNode_eq
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  obtain ⟨s4, hcopy_run, hpc4, _, hcmt4, hpres4⟩ :=
    commit_copy32 oracle s 4150 .x12 .x26 (C_TD + 32 * ROOT_NODE) C_CMT 0 0
      (by decide) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      hpc hx12 hx26
      (fun k hk st => by
        constructor
        · intro hpc'
          have h := commit_fetch_commitTailInstr st (4150 + 2 * k) (by omega) (by omega) hpc'
          interval_cases k <;> simpa [commitTailInstr] using h
        · intro hpc'
          have h := commit_fetch_commitTailInstr st (4150 + 2 * k + 1) (by omega) (by omega) hpc'
          interval_cases k <;> simpa [commitTailInstr] using h)
  -- 3 halt instructions (`words 4158..4160`): `ADDI x5, x0, 1; ADDI x10, x0, 0; ECALL`
  let s5 := execInstrBr s4 (.ADDI .x5 .x0 (1#12))
  let s6 := execInstrBr s5 (.ADDI .x10 .x0 (0#12))
  have hpc4' : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * 4158) := hpc4
  have hpc5 : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * 4159) := pc_step_idx s4 4158 hpc4'
  have hpc6 : s6.pc = BitVec.ofNat 64 (0x1000 + 4 * 4160) := pc_step_idx s5 4159 hpc5
  have hr5 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (commit_fetch_commitTailInstr s4 4158 (by omega) (by omega) hpc4') rfl
  have hr6 : DetRun oracle (submission.image .commit) s5 1 s6 1 0 :=
    DetRun.step1 (commit_fetch_commitTailInstr s5 4159 (by omega) (by omega) hpc5) rfl
  have hpre10 : DetRun oracle (submission.image .commit) s 10 s6 10 0 := by
    simpa using (hcopy_run.trans hr5).trans hr6
  have hx5_6 : s6.getReg .x5 = 1#64 := by
    simp only [s6, s5, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x10 .x5 (by decide), MachineState.getReg_setReg_eq (by decide : Reg.x5 ≠ .x0),
      c_getReg_x0]; decide
  have hx10_6 : s6.getReg .x10 = 0#64 := by
    simp only [s6, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), c_getReg_x0]; decide
  have hfetch_halt : fetch (submission.image .commit) s6 = some (.base .ECALL) :=
    commit_fetch_commitTailInstr s6 4160 (by omega) (by omega) hpc6
  have hmem6 : s6.mem = s4.mem := (mem_exec_ADDI s5 _ _ _).trans (mem_exec_ADDI s4 _ _ _)
  have hcmt_root : readBuffer s6 C_CMT 32 = root := by
    rw [readBuffer_of_mem_eq hmem6]
    simpa only [Nat.add_zero] using hcmt4.trans (by simpa only [Nat.add_zero] using hroot)
  refine ⟨s6, ?_, hcmt_root, ?_⟩
  · intro extra
    have hsp : 11 + extra = 10 + (1 + extra) := by omega
    rw [hsp, hpre10 (1 + extra), DetRun.halt_ok hfetch_halt hx5_6 hx10_6 extra, map_pure]
    rfl
  · simpa only [Nat.add_zero] using hpres4.trans (MemPreservedOutside.of_mem_eq hmem6 _ _)

/-! ### 4. Complete Phase 2 + Phase 3 Composition (`words 3374..4160`) -/

/-- Complete Phase 2 + Phase 3 (`words 3374..4160`):
`25,198,610` steps (`7 + 32768 * 769 + 11`), `83,918,866` cycles (`7 + 32768 * 2561 + 11`),
`8,388,608` compression calls. Computes every queue node `v ∈ [LENGTH, TREE_NODES)`,
copies `ROOT` to `C_CMT`, and halts with `.success`. -/
theorem commit_phase2_3 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 3374))
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hl0 : ∀ idx < LENGTH,
      readBuffer s0 (C_TD + 32 * idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts idx)
    (hzeroRoot : readBuffer s0 (C_TD + 32 * ROOT_NODE) 32 = 0) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ sfin,
      (∀ extra,
        oracle.run (execute (submission.image .commit) (25198610 + extra) s0 true) =
          pure (⟨.success, sfin, 83918866, 8388608⟩, 8388608)) ∧
      readBuffer sfin C_CMT 32 = rootVal c96 msg salts ∧
      (∀ v < TREE_NODES, readBuffer sfin (C_TD + 32 * v) 32 = nodeVal c96 msg salts v) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (C_ROW ≤ q ∨ (C_CMT + 32 ≤ q ∧ q < C_TD + 536870912)) →
        sfin.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
  intro c96
  have hC_CMT : C_CMT = 4294971392 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5100277792 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hTN : TREE_NODES = 25165824 := treeNodes_eq
  have hRN : ROOT_NODE = 25165823 := rootNode_eq
  let s1 := commitMid1CInstrs.foldl execInstrBr s0
  have hr1 := commit_mid1C_run oracle s0 hpc
  obtain ⟨hpc1, hmem1, hx5_1, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1, hx19_1, hx26_1⟩ :=
    commit_mid1C_spec s0 hpc hx5 hx9 hx11 hx13 hx18 hx26
  have hloop : ∀ n ≤ 32768,
      ∃ sn,
        DetRun oracle (submission.image .commit) s1 (769 * n) sn (2561 * n) (256 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 32768 then 3381 else 4150)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sn.getReg r = s1.getReg r) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (256 * n) - 96) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 256 * n) - 32) ∧
        (∀ v < LENGTH + 256 * n, readBuffer sn (C_TD + 32 * v) 32 = nodeVal c96 msg salts v) ∧
        MemPreservedOutside s1 sn (C_TD + 32 * LENGTH) (C_TD + 32 * (LENGTH + 256 * n)) := by
    intro n hn; induction n with
    | zero =>
      refine ⟨s1, DetRun.refl _ _ _, by simpa using hpc1, fun _ _ _ => rfl,
        hx10_1, hx12_1,
        fun v hv => by rw [readBuffer_of_mem_eq hmem1]; exact hl0 v (by omega),
        MemPreservedOutside.refl _ _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hregn, hx10n, hx12n, hdign, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 3381) := by
        simpa only [show n < 32768 by omega, ite_true] using hpcn
      have hzr_n : readBuffer sn (C_TD + 32 * ROOT_NODE) 32 = 0 := by
        rw [hpresn.readBuffer_eq (by omega) (by omega), readBuffer_of_mem_eq hmem1]
        exact hzeroRoot
      obtain ⟨sm, hrun1, hpcm, hreg1, hx10m, hx12m, hdigm, hpres1⟩ :=
        commit_q3_chunk h768 oracle msg salts n (by omega) sn hpc_in
          ((hregn .x5 (by decide) (by decide)).trans hx5_1)
          ((hregn .x11 (by decide) (by decide)).trans hx11_1)
          ((hregn .x13 (by decide) (by decide)).trans hx13_1)
          hx10n hx12n ((hregn .x19 (by decide) (by decide)).trans hx19_1) hdign hzr_n
      refine ⟨sm, ?_, hpcm, fun r h10 h12 => (hreg1 r h10 h12).trans (hregn r h10 h12),
        hx10m, hx12m, hdigm,
        (hpresn.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (le_refl _))⟩
      have h := hrunn.trans hrun1
      rw [show 769 * n + 769 = 769 * (n + 1) by omega,
          show 2561 * n + 2561 = 2561 * (n + 1) by omega,
          show 256 * n + 256 = 256 * (n + 1) by omega] at h
      exact h
  obtain ⟨s2, hrun2, hpc2, hreg2, _, hx12_2, hdig2, hpres2⟩ := hloop 32768 (le_refl _)
  have hpc2' : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 4150) := by
    simpa only [Nat.lt_irrefl, ite_false] using hpc2
  have hx12_2' : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * ROOT_NODE) := hx12_2
  have hx26_2 : s2.getReg .x26 = BitVec.ofNat 64 C_CMT :=
    (hreg2 .x26 (by decide) (by decide)).trans hx26_1
  have hroot2 : readBuffer s2 (C_TD + 32 * ROOT_NODE) 32 = rootVal c96 msg salts :=
    hdig2 ROOT_NODE (by rw [hLEN, hRN]; omega)
  obtain ⟨sfin, hhalt, hcmt_fin, hpres_fin⟩ :=
    commit_copy_root_halt oracle (rootVal c96 msg salts) s2 hpc2' hx12_2' hx26_2 hroot2
  have hpre_tot : DetRun oracle (submission.image .commit) s0 25198599 s2 83918855 8388608 := by
    have h := hr1.trans hrun2
    rw [show 7 + 769 * 32768 = 25198599 by omega,
        show 7 + 2561 * 32768 = 83918855 by omega,
        show 0 + 256 * 32768 = 8388608 by omega] at h
    exact h
  refine ⟨sfin, ?_, hcmt_fin, ?_, ?_⟩
  · intro extra
    have hsp : 25198610 + extra = 25198599 + (11 + extra) := by omega
    rw [hsp, hpre_tot (11 + extra), hhalt extra, map_pure]
    rfl
  · intro v hv
    have hlt2 : v < LENGTH + 256 * 32768 := by rw [hTN] at hv; rw [hLEN]; omega
    rw [hpres_fin.readBuffer_eq (by rw [hTN] at hv; omega) (by omega)]
    exact hdig2 v hlt2
  · intro q hq hreg
    have h3 := hpres_fin q hq (by omega)
    have h2 := hpres2 q hq (by omega)
    rw [h3, h2, getByte_of_mem_eq hmem1]

end CommitGolfCandidate
