import CommitGolfCandidate.R4CommitBase

set_option Elab.async false

/-! Exact RV64IM execution proof for Phase 1 of the R4a `commit` image (zero-rebase 3-subpass
late-salt leaf pipeline, words 32797..180277):
- Phase 1A (`leaf0_loop`, words 32797..81959): `u_i = C(M_i[0..96)) -> M_i[64..96)` (`1,024 × 16,384`)
- Phase 1B (`leaf12_loop`, words 81960..131122): `(a_i, b_i)` written into paired rows (`2,048 × 4,096`)
- Phase 1C (`leaf3_loop`, words 131123..180277): late-salted `leafDigest` into `L0` (`1,024 × 8,192`). -/
namespace CommitGolfCandidate.R4
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 2. Phase 1A: `leaf0_loop` + Mid1A Setup (words `32797..81959`) -/

private def commitMid1AInstrs : List Instr :=
  [.ADDI .x10 .x8 (4000#12), .ADDI .x12 .x18 (4064#12),
   .ADDI .x6 .x0 (1023#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (2047#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (1952#12), .ADD .x19 .x8 .x6]

private theorem commit_mid1A_run (oracle : Oracle) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 81952)) :
    DetRun oracle (submission.image .commit) s0 8 (commitMid1AInstrs.foldl execInstrBr s0) 8 0 := by
  have hall : ∀ ins ∈ commitMid1AInstrs, isPureAlu ins = true := by decide
  apply exec_alu_list commitMid1AInstrs s0
  intro i hi
  have hi' : i < 8 := hi
  have hpc_i : ((commitMid1AInstrs.take i).foldl execInstrBr s0).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (81952 + i)) := by
    have h := foldl_pureAlu_pc (commitMid1AInstrs.take i) s0 (0x1000 + 4 * 81952)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitMid1AInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem commit_mid1A_spec (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 81952))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64)
    (hx8 : s0.getReg .x8 = BitVec.ofNat 64 C_MSG)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64)
    (hx13 : s0.getReg .x13 = 0#64)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s1 := commitMid1AInstrs.foldl execInstrBr s0
    s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 81960) ∧
    s1.mem = s0.mem ∧
    s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
    s1.getReg .x5 = 0#64 ∧
    s1.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
    s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s1.getReg .x10 = BitVec.ofNat 64 (C_MSG - 96) ∧
    s1.getReg .x11 = 96#64 ∧
    s1.getReg .x12 = BitVec.ofNat 64 (C_ROW - 32) ∧
    s1.getReg .x13 = 0#64 ∧
    s1.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
    s1.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 96) ∧
    s1.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ commitMid1AInstrs, isPureAlu ins = true := by decide
  refine ⟨?_, foldl_pureAlu_mem commitMid1AInstrs s0 hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (foldl_pureAlu_pc commitMid1AInstrs s0 (0x1000 + 4 * 81952) hall hpc).trans (by decide)
  all_goals (
    simp only [commitMid1AInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx2, hx5, hx8, hx9, hx11, hx13, hx18, hx26]
    try decide)

/-- One leaf step of Phase 1A (`leaf0Instr`: `3` steps, `10` cycles, `1` call). -/
private theorem commit_leaf0_step (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (k idx : Nat) (hk : k < 16384) (hidx : idx < LENGTH)
    (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (32797 + 3 * k)))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * idx - 256))
    (hmsg : ∀ j < 256, s.getByte (BitVec.ofNat 64 (C_MSG + 256 * idx + j)) =
      (msg ⟨idx, hidx⟩).extractLsb' (8 * j) 8) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s',
      DetRun oracle (submission.image .commit) s 3 s' 10 1 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (32797 + 3 * (k + 1))) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * idx) ∧
      readBuffer s' (C_MSG + 256 * idx + 64) 96 =
        leafAInput (c96 (leafUInput (msg ⟨idx, hidx⟩))) (msg ⟨idx, hidx⟩) ∧
      readBuffer s' (C_MSG + 256 * idx + 160) 96 = leafBInput (msg ⟨idx, hidx⟩) ∧
      MemPreservedOutside s s' (C_MSG + 256 * idx + 64) (C_MSG + 256 * idx + 96) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let M : Nat := C_MSG + 256 * idx
  let s1 := execInstrBr s (.ADDI .x10 .x10 (256#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x10 (64#12))
  let u := c96 (leafUInput (msg ⟨idx, hidx⟩))
  let s3 := writeBits s2 (BitVec.ofNat 64 (M + 64)) u
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (32797 + 3 * k + 1)) := pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (32797 + 3 * k + 2)) := pc_step_idx s1 _ hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (32797 + 3 * (k + 1))) :=
    (pc_step_idx s2 _ hs2_pc).trans (congrArg (BitVec.ofNat 64) (by omega))
  have hm2 : s2.mem = s.mem := (mem_exec_ADDI s1 _ _ _).trans (mem_exec_ADDI s _ _ _)
  have hs2_reg : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s2.getReg r = s.getReg r := fun r h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
  have hs1_a0 : s1.getReg .x10 = BitVec.ofNat 64 M := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ 256 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_a0 : s2.getReg .x10 = BitVec.ofNat 64 M := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs1_a0]
  have hs2_a2 : s2.getReg .x12 = BitVec.ofNat 64 (M + 64) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs1_a0,
      add_signExtend12_ofNat_small _ 64 (by omega)]
  have hs2_in : readBuffer s2 M 96 = leafUInput (msg ⟨idx, hidx⟩) := by
    rw [readBuffer_of_mem_eq hm2]
    have hr := read_serialized_slice s (msg ⟨idx, hidx⟩) M 0 96 (fun j hj => by
      simpa only [Nat.zero_add] using hmsg j (by omega))
    simpa [leafUInput] using hr
  have hst0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_leaf0 s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc)) rfl
  have hst1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_leaf0 s1 k 1 hk (by omega) hs1_pc) rfl
  have hst2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s2)
      (commit_fetch_leaf0 s2 k 2 hk (by omega) hs2_pc)
      ((hs2_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg .x13 (by decide) (by decide)).trans hx13)
      M (M + 64) hs2_a0 hs2_a2 (by omega) (by omega) (by omega) (by omega) u (by rw [hs2_in])
  have hpres : MemPreservedOutside s s3 (M + 64) (M + 96) :=
    (MemPreservedOutside.of_mem_eq hm2 _ _).trans (memPreserved_writeBits s2 (M + 64) u (by omega))
  refine ⟨s3, (hst0.trans hst1).trans hst2, hs3_pc,
    fun r h10 h12 => (writeBits_register s2 _ u r).trans (hs2_reg r h10 h12),
    (writeBits_register s2 _ u .x10).trans hs2_a0, ?_, ?_, hpres⟩
  · rw [readBuffer_leafA, writeBits_readBuffer_digest s2 (M + 64) u]
    have hmid : readBuffer s3 (M + 64 + 32) 64 = (msg ⟨idx, hidx⟩).extractLsb' 768 512 := by
      have ha : M + 64 + 32 = M + 96 := by omega
      rw [ha]
      have hr := read_serialized_slice s3 (msg ⟨idx, hidx⟩) (M + 96) 96 64 (fun j hj => by
        rw [hpres (M + 96 + j) (by omega) (by omega), show M + 96 + j = M + (96 + j) by omega]
        exact hmsg (96 + j) (by omega))
      simpa using hr
    rw [hmid]; rfl
  · have hr := read_serialized_slice s3 (msg ⟨idx, hidx⟩) (M + 160) 160 96 (fun j hj => by
      rw [hpres (M + 160 + j) (by omega) (by omega), show M + 160 + j = M + (160 + j) by omega]
      exact hmsg (160 + j) (by omega))
    simpa [leafBInput] using hr

/-- One 16,384-leaf chunk of Phase 1A (`words 32797..81951`: `49154` steps, `163842` cycles, `16,384` calls). -/
private theorem commit_phase1A_chunk (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (c : Nat) (hc : c < 1024) (sc : MachineState)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 32797))
    (hx5 : sc.getReg .x5 = 0#64) (hx11 : sc.getReg .x11 = 96#64) (hx13 : sc.getReg .x13 = 0#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (16384 * c) - 256))
    (hx19 : sc.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256))
    (hmsg : ∀ (k : Nat) (hk : k < 16384), ∀ j < 256,
      sc.getByte (BitVec.ofNat 64 (C_MSG + 256 * (16384 * c + k) + j)) =
        (msg ⟨16384 * c + k, by unfold LENGTH LOG_LENGTH; omega⟩).extractLsb' (8 * j) 8) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ sbne,
      DetRun oracle (submission.image .commit) sc 49154 sbne 163842 16384 ∧
      sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < 1024 then 32797 else 81952)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sbne.getReg r = sc.getReg r) ∧
      sbne.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (16384 * (c + 1)) - 256) ∧
      (∀ (k : Nat) (hk : k < 16384),
        let idx : Index := ⟨16384 * c + k, by unfold LENGTH LOG_LENGTH; omega⟩
        readBuffer sbne (C_MSG + 256 * idx.val + 64) 96 =
          leafAInput (c96 (leafUInput (msg idx))) (msg idx) ∧
        readBuffer sbne (C_MSG + 256 * idx.val + 160) 96 = leafBInput (msg idx)) ∧
      MemPreservedOutside sc sbne (C_MSG + 256 * (16384 * c)) (C_MSG + 256 * (16384 * (c + 1))) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hind : ∀ (m : Nat) (hm : m ≤ 16384),
      ∃ sm,
        DetRun oracle (submission.image .commit) sc (3 * m) sm (10 * m) m ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (32797 + 3 * m)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sm.getReg r = sc.getReg r) ∧
        sm.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (16384 * c + m) - 256) ∧
        (∀ (k : Nat) (hk : k < m),
          let idx : Index := ⟨16384 * c + k, by omega⟩
          readBuffer sm (C_MSG + 256 * idx.val + 64) 96 =
            leafAInput (c96 (leafUInput (msg idx))) (msg idx) ∧
          readBuffer sm (C_MSG + 256 * idx.val + 160) 96 = leafBInput (msg idx)) ∧
        MemPreservedOutside sc sm (C_MSG + 256 * (16384 * c)) (C_MSG + 256 * (16384 * c + m)) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, fun _ h => (Nat.not_lt_zero _ h).elim, MemPreservedOutside.refl _ _ _⟩
    | succ m ih =>
      obtain ⟨sm, hrunm, hpcm, hregm, hx10m, hresm, hpresm⟩ := ih (by omega)
      obtain ⟨sn, hrun1, hpcn, hregn, hx10n, ha1, hb1, hpres1⟩ :=
        commit_leaf0_step h768 oracle msg m (16384 * c + m) (by omega) (by omega) sm hpcm
          ((hregm .x5 (by decide) (by decide)).trans hx5)
          ((hregm .x11 (by decide) (by decide)).trans hx11)
          ((hregm .x13 (by decide) (by decide)).trans hx13) hx10m
          (fun j hj => by
            rw [hpresm (C_MSG + 256 * (16384 * c + m) + j) (by omega) (by omega)]
            exact hmsg m (by omega) j hj)
      have hrun_next : DetRun oracle (submission.image .commit) sc (3 * (m + 1)) sn (10 * (m + 1)) (m + 1) := by
        have h := hrunm.trans hrun1
        rw [show 3 * m + 3 = 3 * (m + 1) by omega, show 10 * m + 10 = 10 * (m + 1) by omega] at h
        exact h
      refine ⟨sn, hrun_next, hpcn, fun r h10 h12 => (hregn r h10 h12).trans (hregm r h10 h12),
        by rw [hx10n]; exact congrArg (BitVec.ofNat 64) (by omega), ?_,
        (hpresm.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (by omega))⟩
      intro k hk
      dsimp only
      by_cases hkm : k = m
      · subst hkm; exact ⟨ha1, hb1⟩
      · obtain ⟨hak, hbk⟩ := hresm k (by omega)
        dsimp only at hak hbk
        exact ⟨(hpres1.readBuffer_eq (by omega) (by omega)).trans hak,
               (hpres1.readBuffer_eq (by omega) (by omega)).trans hbk⟩
  obtain ⟨sm, hrun256, hpc256, hreg256, hx10_256, hres256, hpres256⟩ := hind 16384 (le_refl _)
  let sbne := latchResult sm 32797 81952
  have hbne : DetRun oracle (submission.image .commit) sm 2 sbne 2 0 :=
    longRun oracle sm 81949 32797 (by decide +kernel) hpc256
  have hmem_bne : sbne.mem = sm.mem := rfl
  have hreg_bne : ∀ r, sbne.getReg r = sm.getReg r := fun _ => rfl
  have hpc_end : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < 1024 then 32797 else 81952)) := by
    have hx19m : sm.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256) :=
      (hreg256 .x19 (by decide) (by decide)).trans hx19
    by_cases hlt : c + 1 < 1024
    · have hne : (sm.getReg .x10 != sm.getReg .x19) = true := by
        rw [hx10_256, hx19m, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp [latchResult,sbne,hlt,hne,lpc,pc_setPC]
    · have heq : (sm.getReg .x10 != sm.getReg .x19) = false := by
        rw [hx10_256, hx19m, show C_MSG + 256 * (16384 * c + 16384) - 256 = C_MSG + 2 ^ 32 - 256 by omega]
        exact bne_self_eq_false _
      simp [latchResult,sbne,hlt,heq,lpc,pc_setPC]
  refine ⟨sbne, hrun256.trans hbne, hpc_end,
    fun r h10 h12 => (hreg_bne r).trans (hreg256 r h10 h12),
    by rw [hreg_bne, hx10_256]; exact congrArg (BitVec.ofNat 64) (by omega),
    fun k hk =>
      let ⟨ha, hb⟩ := hres256 k hk
      ⟨(readBuffer_of_mem_eq hmem_bne _ _).trans ha,
       (readBuffer_of_mem_eq hmem_bne _ _).trans hb⟩,
    (hpres256.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmem_bne _ _)⟩

/-- Full Phase 1A (`words 32797..81959`): `50,333,704` steps, `167,774,216` cycles, `16,777,216` calls. -/
private theorem commit_phase1A (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 32797))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx8 : s0.getReg .x8 = BitVec.ofNat 64 C_MSG)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 (C_MSG - 256))
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx19 : s0.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hmsg0 : ∀ (i : Index) (j : Nat), j < 256 →
      s0.getByte (BitVec.ofNat 64 (C_MSG + 256 * i.val + j)) = (msg i).extractLsb' (8 * j) 8) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 50333704 s1 167774216 16777216 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 81960) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧ s1.getReg .x5 = 0#64 ∧
      s1.getReg .x8 = BitVec.ofNat 64 C_MSG ∧ s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x10 = BitVec.ofNat 64 (C_MSG - 96) ∧ s1.getReg .x11 = 96#64 ∧
      s1.getReg .x12 = BitVec.ofNat 64 (C_ROW - 32) ∧ s1.getReg .x13 = 0#64 ∧
      s1.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
      s1.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 96) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ i : Index,
        readBuffer s1 (C_MSG + 256 * i.val + 64) 96 =
          leafAInput (c96 (leafUInput (msg i))) (msg i) ∧
        readBuffer s1 (C_MSG + 256 * i.val + 160) 96 = leafBInput (msg i)) ∧
      MemPreservedOutside s0 s1 C_MSG (C_MSG + 2 ^ 32) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hloop : ∀ (n : Nat) (hn : n ≤ 1024),
      ∃ sn,
        DetRun oracle (submission.image .commit) s0 (49154 * n) sn (163842 * n) (16384 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 1024 then 32797 else 81952)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sn.getReg r = s0.getReg r) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (16384 * n) - 256) ∧
        (∀ idx : Nat, ∀ hlt : idx < 16384 * n,
          let i : Index := ⟨idx, by omega⟩
          readBuffer sn (C_MSG + 256 * idx + 64) 96 =
            leafAInput (c96 (leafUInput (msg i))) (msg i) ∧
          readBuffer sn (C_MSG + 256 * idx + 160) 96 = leafBInput (msg i)) ∧
        MemPreservedOutside s0 sn C_MSG (C_MSG + 256 * (16384 * n)) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨s0, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, fun _ h => (Nat.not_lt_zero _ h).elim, MemPreservedOutside.refl _ _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hregn, hx10n, hresn, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 32797) := by
        simpa only [show n < 1024 by omega, ite_true] using hpcn
      obtain ⟨sm, hrunC, hpcm, hregC, hx10m, hresC, hpresC⟩ :=
        commit_phase1A_chunk h768 oracle msg n (by omega) sn hpc_in
          ((hregn .x5 (by decide) (by decide)).trans hx5)
          ((hregn .x11 (by decide) (by decide)).trans hx11)
          ((hregn .x13 (by decide) (by decide)).trans hx13) hx10n
          ((hregn .x19 (by decide) (by decide)).trans hx19)
          (fun k hk j hj => by
            rw [hpresn (C_MSG + 256 * (16384 * n + k) + j) (by omega) (by omega)]
            exact hmsg0 ⟨16384 * n + k, by omega⟩ j hj)
      have hrun_n1 : DetRun oracle (submission.image .commit) s0 (49154 * (n + 1)) sm
          (163842 * (n + 1)) (16384 * (n + 1)) := by
        have h := hrunn.trans hrunC
        rw [show 49154 * n + 49154 = 49154 * (n + 1) by omega,
            show 163842 * n + 163842 = 163842 * (n + 1) by omega,
            show 16384 * n + 16384 = 16384 * (n + 1) by omega] at h
        exact h
      refine ⟨sm, hrun_n1, hpcm, fun r h10 h12 => (hregC r h10 h12).trans (hregn r h10 h12),
        hx10m, ?_, (hpresn.mono (le_refl _) (by omega)).trans (hpresC.mono (by omega) (le_refl _))⟩
      intro idx hlt
      by_cases hold : idx < 16384 * n
      · obtain ⟨ha, hb⟩ := hresn idx hold
        exact ⟨(hpresC.readBuffer_eq (by omega) (by omega)).trans ha,
               (hpresC.readBuffer_eq (by omega) (by omega)).trans hb⟩
      · have hk : idx - 16384 * n < 16384 := by omega
        have heq : 16384 * n + (idx - 16384 * n) = idx := by omega
        have hc := hresC (idx - 16384 * n) hk
        simpa only [heq] using hc
  obtain ⟨sb, hrun_loop, hpc_b, hreg_b, _, hres_b, hpres_b⟩ := hloop 1024 (le_refl _)
  have hpc_b' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 81952) := by
    simpa only [Nat.lt_irrefl, ite_false] using hpc_b
  let s1 := commitMid1AInstrs.foldl execInstrBr sb
  have hmid_run : DetRun oracle (submission.image .commit) sb 8 s1 8 0 :=
    commit_mid1A_run oracle sb hpc_b'
  obtain ⟨hs1_pc, hs1_mem, hs1_x2, hs1_x5, hs1_x8, hs1_x9, hs1_x10, hs1_x11, hs1_x12,
    hs1_x13, hs1_x18, hs1_x19, hs1_x26⟩ := commit_mid1A_spec sb hpc_b'
      ((hreg_b .x2 (by decide) (by decide)).trans hx2)
      ((hreg_b .x5 (by decide) (by decide)).trans hx5)
      ((hreg_b .x8 (by decide) (by decide)).trans hx8)
      ((hreg_b .x9 (by decide) (by decide)).trans hx9)
      ((hreg_b .x11 (by decide) (by decide)).trans hx11)
      ((hreg_b .x13 (by decide) (by decide)).trans hx13)
      ((hreg_b .x18 (by decide) (by decide)).trans hx18)
      ((hreg_b .x26 (by decide) (by decide)).trans hx26)
  refine ⟨s1, by simpa using hrun_loop.trans hmid_run,
    hs1_pc, hs1_x2, hs1_x5, hs1_x8, hs1_x9, hs1_x10, hs1_x11, hs1_x12, hs1_x13, hs1_x18, hs1_x19, hs1_x26,
    ?_, (hpres_b.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hs1_mem _ _)⟩
  intro ⟨idx, hidx⟩
  obtain ⟨ha, hb⟩ := hres_b idx (by omega)
  exact ⟨(readBuffer_of_mem_eq hs1_mem _ _).trans ha, (readBuffer_of_mem_eq hs1_mem _ _).trans hb⟩

/-! ### 3. Phase 1B: `leaf12_loop` + Mid1B Setup (words `81960..131122`) -/

private def commitMid1BInstrs : List Instr :=
  [.ADDI .x10 .x18 (4000#12), .ADDI .x12 .x9 (4064#12),
   .ADDI .x6 .x0 (367#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (2047#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (1952#12), .ADD .x19 .x18 .x6]

private theorem commit_mid1B_run (oracle : Oracle) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 131115)) :
    DetRun oracle (submission.image .commit) s0 8 (commitMid1BInstrs.foldl execInstrBr s0) 8 0 := by
  have hall : ∀ ins ∈ commitMid1BInstrs, isPureAlu ins = true := by decide
  apply exec_alu_list commitMid1BInstrs s0
  intro i hi
  have hi' : i < 8 := hi
  have hpc_i : ((commitMid1BInstrs.take i).foldl execInstrBr s0).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (131115 + i)) := by
    have h := foldl_pureAlu_pc (commitMid1BInstrs.take i) s0 (0x1000 + 4 * 131115)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitMid1BInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem commit_mid1B_spec (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 131115))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64)
    (hx13 : s0.getReg .x13 = 0#64)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s1 := commitMid1BInstrs.foldl execInstrBr s0
    s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 131123) ∧
    s1.mem = s0.mem ∧
    s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
    s1.getReg .x5 = 0#64 ∧
    s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s1.getReg .x10 = BitVec.ofNat 64 (C_ROW - 96) ∧
    s1.getReg .x11 = 96#64 ∧
    s1.getReg .x12 = BitVec.ofNat 64 (C_TD - 32) ∧
    s1.getReg .x13 = 0#64 ∧
    s1.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
    s1.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes - 96) ∧
    s1.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ commitMid1BInstrs, isPureAlu ins = true := by decide
  refine ⟨?_, foldl_pureAlu_mem commitMid1BInstrs s0 hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (foldl_pureAlu_pc commitMid1BInstrs s0 (0x1000 + 4 * 131115) hall hpc).trans (by decide)
  all_goals (
    simp only [commitMid1BInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx2, hx5, hx9, hx11, hx13, hx18, hx26, rowBytes_eq]
    try decide)

/-- One 3-instruction compression step (`ADDI x10, x10, d10; ADDI x12, x12, d12; ECALL`). -/
private theorem commit_inc_compress (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (s : MachineState)
    (basePc src0 dst0 d10 d12 : Nat) (hd10 : d10 < 2048) (hd12 : d12 < 2048)
    (hsrc_al : (src0 + d10) % 8 = 0) (hdst_al : (dst0 + d12) % 8 = 0)
    (hsrc_bd : src0 + d10 + 96 ≤ MEMORY_BYTES) (hdst_bd : dst0 + d12 + 32 ≤ MEMORY_BYTES)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src0)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst0)
    (hfetch0 : fetch (submission.image .commit) s = some (.base (.ADDI .x10 .x10 (BitVec.ofNat 12 d10))))
    (hfetch1 : ∀ st : MachineState, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) →
      fetch (submission.image .commit) st = some (.base (.ADDI .x12 .x12 (BitVec.ofNat 12 d12))))
    (hfetch2 : ∀ st : MachineState, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) →
      fetch (submission.image .commit) st = some (.base .ECALL))
    (out : Digest)
    (hout : oracle.compression ((readBuffer s (src0 + d10) 96).cast h768.symm) = out) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 3 s' 10 1 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (src0 + d10) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (dst0 + d12) ∧
      readBuffer s' (dst0 + d12) 32 = out ∧
      MemPreservedOutside s s' (dst0 + d12) (dst0 + d12 + 32) := by
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let s1 := execInstrBr s (.ADDI .x10 .x10 (BitVec.ofNat 12 d10))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (BitVec.ofNat 12 d12))
  let s3 := writeBits s2 (BitVec.ofNat 64 (dst0 + d12)) out
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) := pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) := pc_step_idx s1 _ hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) := pc_step_idx s2 _ hs2_pc
  have hm2 : s2.mem = s.mem := (mem_exec_ADDI s1 _ _ _).trans (mem_exec_ADDI s _ _ _)
  have hs2_reg : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s2.getReg r = s.getReg r := fun r h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
  have hs1_a0 : s1.getReg .x10 = BitVec.ofNat 64 (src0 + d10) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ d10 hd10]
  have hs2_a0 : s2.getReg .x10 = BitVec.ofNat 64 (src0 + d10) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs1_a0]
  have hs2_a2 : s2.getReg .x12 = BitVec.ofNat 64 (dst0 + d12) := by
    have h1x12 : s1.getReg .x12 = BitVec.ofNat 64 dst0 := by
      simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hx12]
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h1x12,
      add_signExtend12_ofNat_small _ d12 hd12]
  have hst0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 := DetRun.step1 hfetch0 rfl
  have hst1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 := DetRun.step1 (hfetch1 s1 hs1_pc) rfl
  have hst2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s2)
      (hfetch2 s2 hs2_pc)
      ((hs2_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg .x13 (by decide) (by decide)).trans hx13)
      (src0 + d10) (dst0 + d12) hs2_a0 hs2_a2 hsrc_al hdst_al hsrc_bd hdst_bd out
      (by rw [readBuffer_of_mem_eq hm2]; exact hout)
  refine ⟨s3, (hst0.trans hst1).trans hst2, hs3_pc,
    fun r h10 h12 => (writeBits_register s2 _ out r).trans (hs2_reg r h10 h12),
    (writeBits_register s2 _ out .x10).trans hs2_a0,
    (writeBits_register s2 _ out .x12).trans hs2_a2,
    writeBits_readBuffer_digest s2 _ out,
    (MemPreservedOutside.of_mem_eq hm2 _ _).trans (memPreserved_writeBits s2 _ out (by omega))⟩

/-- One pair of Phase 1B (`leaf12PairInstr`: `12` steps, `40` cycles, `4` calls). -/
private theorem commit_leaf12_pair (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (k p : Nat) (hk : k < 4096) (hp : p < LENGTH / 2)
    (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (81960 + 12 * k)))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * p - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_ROW + 184 * p - 32))
    (hinEvA : readBuffer s (C_MSG + 256 * (2 * p) + 64) 96 =
      leafAInput ((fun x => oracle.compression (x.cast h768.symm))
        (leafUInput (msg ⟨2 * p, by unfold LENGTH LOG_LENGTH at *; omega⟩)))
        (msg ⟨2 * p, by unfold LENGTH LOG_LENGTH at *; omega⟩))
    (hinEvB : readBuffer s (C_MSG + 256 * (2 * p) + 160) 96 =
      leafBInput (msg ⟨2 * p, by unfold LENGTH LOG_LENGTH at *; omega⟩))
    (hinOdA : readBuffer s (C_MSG + 256 * (2 * p + 1) + 64) 96 =
      leafAInput ((fun x => oracle.compression (x.cast h768.symm))
        (leafUInput (msg ⟨2 * p + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩)))
        (msg ⟨2 * p + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩))
    (hinOdB : readBuffer s (C_MSG + 256 * (2 * p + 1) + 160) 96 =
      leafBInput (msg ⟨2 * p + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩)) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s',
      DetRun oracle (submission.image .commit) s 12 s' 40 4 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (81960 + 12 * (k + 1))) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (p + 1) - 96) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_ROW + 184 * (p + 1) - 32) ∧
      readBuffer s' (C_ROW + 184 * p) 32 =
        leafA c96 (msg ⟨2 * p, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer s' (C_ROW + 184 * p + 32) 32 =
        leafB c96 (msg ⟨2 * p, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer s' (C_ROW + 184 * p + 120) 32 =
        leafA c96 (msg ⟨2 * p + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer s' (C_ROW + 184 * p + 152) 32 =
        leafB c96 (msg ⟨2 * p + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < C_ROW + 184 * p ∨ (C_ROW + 184 * p + 64 ≤ q ∧ q < C_ROW + 184 * p + 120) ∨
          C_ROW + 184 * (p + 1) ≤ q) →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5905584160 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let iEv : Index := ⟨2 * p, by omega⟩
  let iOd : Index := ⟨2 * p + 1, by omega⟩
  -- Call 0: even leafA -> C_ROW + 184*p
  obtain ⟨s1, hr1, hpc1, hreg1, hx10_1, hx12_1, hd0, hp1⟩ :=
    commit_inc_compress h768 oracle s (81960 + 12 * k) (C_MSG + 512 * p - 96) (C_ROW + 184 * p - 32) 160 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hpc hx5 hx11 hx13 hx10 hx12
      (commit_fetch_leaf12 s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc))
      (fun st hst => commit_fetch_leaf12 st k 1 hk (by omega) hst)
      (fun st hst => commit_fetch_leaf12 st k 2 hk (by omega) hst)
      (leafA c96 (msg iEv))
      (by rw [show C_MSG + 512 * p - 96 + 160 = C_MSG + 256 * (2 * p) + 64 by omega, hinEvA]; rfl)
  -- Call 1: even leafB -> C_ROW + 184*p + 32
  obtain ⟨s2, hr2, hpc2, hreg2, hx10_2, hx12_2, hd1, hp2⟩ :=
    commit_inc_compress h768 oracle s1 (81960 + 12 * k + 3) (C_MSG + 512 * p - 96 + 160) (C_ROW + 184 * p - 32 + 32) 96 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hpc1
      ((hreg1 .x5 (by decide) (by decide)).trans hx5)
      ((hreg1 .x11 (by decide) (by decide)).trans hx11)
      ((hreg1 .x13 (by decide) (by decide)).trans hx13) hx10_1 hx12_1
      (commit_fetch_leaf12 s1 k 3 hk (by omega) hpc1)
      (fun st hst => commit_fetch_leaf12 st k 4 hk (by omega) (by simpa only [Nat.add_assoc] using hst))
      (fun st hst => commit_fetch_leaf12 st k 5 hk (by omega) (by simpa only [Nat.add_assoc] using hst))
      (leafB c96 (msg iEv))
      (by
        rw [show C_MSG + 512 * p - 96 + 160 + 96 = C_MSG + 256 * (2 * p) + 160 by omega,
            hp1.readBuffer_eq (by omega) (by omega), hinEvB]; rfl)
  -- Call 2: odd leafA -> C_ROW + 184*p + 120
  obtain ⟨s3, hr3, hpc3, hreg3, hx10_3, hx12_3, hd2, hp3⟩ :=
    commit_inc_compress h768 oracle s2 (81960 + 12 * k + 6)
      (C_MSG + 512 * p - 96 + 160 + 96) (C_ROW + 184 * p - 32 + 32 + 32) 160 88
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simpa only [Nat.add_assoc] using hpc2)
      ((hreg2 .x5 (by decide) (by decide)).trans ((hreg1 .x5 (by decide) (by decide)).trans hx5))
      ((hreg2 .x11 (by decide) (by decide)).trans ((hreg1 .x11 (by decide) (by decide)).trans hx11))
      ((hreg2 .x13 (by decide) (by decide)).trans ((hreg1 .x13 (by decide) (by decide)).trans hx13))
      hx10_2 hx12_2
      (commit_fetch_leaf12 s2 k 6 hk (by omega) (by simpa only [Nat.add_assoc] using hpc2))
      (fun st hst => commit_fetch_leaf12 st k 7 hk (by omega) (by simpa only [Nat.add_assoc] using hst))
      (fun st hst => commit_fetch_leaf12 st k 8 hk (by omega) (by simpa only [Nat.add_assoc] using hst))
      (leafA c96 (msg iOd))
      (by
        rw [show C_MSG + 512 * p - 96 + 160 + 96 + 160 = C_MSG + 256 * (2 * p + 1) + 64 by omega,
            hp2.readBuffer_eq (by omega) (by omega), hp1.readBuffer_eq (by omega) (by omega), hinOdA]; rfl)
  -- Call 3: odd leafB -> C_ROW + 184*p + 152
  obtain ⟨s4, hr4, hpc4, hreg4, hx10_4, hx12_4, hd3, hp4⟩ :=
    commit_inc_compress h768 oracle s3 (81960 + 12 * k + 9)
      (C_MSG + 512 * p - 96 + 160 + 96 + 160) (C_ROW + 184 * p - 32 + 32 + 32 + 88) 96 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simpa only [Nat.add_assoc] using hpc3)
      ((hreg3 .x5 (by decide) (by decide)).trans ((hreg2 .x5 (by decide) (by decide)).trans ((hreg1 .x5 (by decide) (by decide)).trans hx5)))
      ((hreg3 .x11 (by decide) (by decide)).trans ((hreg2 .x11 (by decide) (by decide)).trans ((hreg1 .x11 (by decide) (by decide)).trans hx11)))
      ((hreg3 .x13 (by decide) (by decide)).trans ((hreg2 .x13 (by decide) (by decide)).trans ((hreg1 .x13 (by decide) (by decide)).trans hx13)))
      hx10_3 hx12_3
      (commit_fetch_leaf12 s3 k 9 hk (by omega) (by simpa only [Nat.add_assoc] using hpc3))
      (fun st hst => commit_fetch_leaf12 st k 10 hk (by omega) (by simpa only [Nat.add_assoc] using hst))
      (fun st hst => commit_fetch_leaf12 st k 11 hk (by omega) (by simpa only [Nat.add_assoc] using hst))
      (leafB c96 (msg iOd))
      (by
        rw [show C_MSG + 512 * p - 96 + 160 + 96 + 160 + 96 = C_MSG + 256 * (2 * p + 1) + 160 by omega,
            hp3.readBuffer_eq (by omega) (by omega), hp2.readBuffer_eq (by omega) (by omega),
            hp1.readBuffer_eq (by omega) (by omega), hinOdB]; rfl)
  refine ⟨s4, by simpa using ((hr1.trans hr2).trans hr3).trans hr4,
    by rw [hpc4]; exact congrArg (BitVec.ofNat 64) (by omega),
    fun r h10 h12 => (((hreg4 r h10 h12).trans (hreg3 r h10 h12)).trans (hreg2 r h10 h12)).trans (hreg1 r h10 h12),
    by rw [hx10_4]; exact congrArg (BitVec.ofNat 64) (by omega),
    by rw [hx12_4]; exact congrArg (BitVec.ofNat 64) (by omega), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp4.readBuffer_eq (by omega) (by omega), hp3.readBuffer_eq (by omega) (by omega),
        hp2.readBuffer_eq (by omega) (by omega)]
    simpa [show C_ROW + 184 * p - 32 + 32 = C_ROW + 184 * p by omega] using hd0
  · rw [hp4.readBuffer_eq (by omega) (by omega), hp3.readBuffer_eq (by omega) (by omega)]
    simpa [show C_ROW + 184 * p - 32 + 32 + 32 = C_ROW + 184 * p + 32 by omega] using hd1
  · rw [hp4.readBuffer_eq (by omega) (by omega)]
    simpa [show C_ROW + 184 * p - 32 + 32 + 32 + 88 = C_ROW + 184 * p + 120 by omega] using hd2
  · simpa [show C_ROW + 184 * p - 32 + 32 + 32 + 88 + 32 = C_ROW + 184 * p + 152 by omega] using hd3
  · intro q hq hout
    have h4 := hp4 q hq (by omega)
    have h3 := hp3 q hq (by omega)
    have h2 := hp2 q hq (by omega)
    have h1 := hp1 q hq (by omega)
    exact ((h4.trans h3).trans h2).trans h1

/-- One 4,096-pair chunk of Phase 1B (`words 81960..131114`: `49154` steps, `163842` cycles, `16,384` calls). -/
private theorem commit_phase1B_chunk (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (c : Nat) (hc : c < 2048) (sc : MachineState)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 81960))
    (hx5 : sc.getReg .x5 = 0#64) (hx11 : sc.getReg .x11 = 96#64) (hx13 : sc.getReg .x13 = 0#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (4096 * c) - 96))
    (hx12 : sc.getReg .x12 = BitVec.ofNat 64 (C_ROW + 184 * (4096 * c) - 32))
    (hx19 : sc.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 96))
    (h1A : ∀ i : Index,
      readBuffer sc (C_MSG + 256 * i.val + 64) 96 =
        leafAInput ((fun x => oracle.compression (x.cast h768.symm)) (leafUInput (msg i))) (msg i) ∧
      readBuffer sc (C_MSG + 256 * i.val + 160) 96 = leafBInput (msg i)) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ sbne,
      DetRun oracle (submission.image .commit) sc 49154 sbne 163842 16384 ∧
      sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < 2048 then 81960 else 131115)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sbne.getReg r = sc.getReg r) ∧
      sbne.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (4096 * (c + 1)) - 96) ∧
      sbne.getReg .x12 = BitVec.ofNat 64 (C_ROW + 184 * (4096 * (c + 1)) - 32) ∧
      (∀ (k : Nat) (hk : k < 4096),
        let p := 4096 * c + k
        readBuffer sbne (C_ROW + 184 * p) 32 =
          leafA c96 (msg ⟨2 * p, by unfold LENGTH LOG_LENGTH; omega⟩) ∧
        readBuffer sbne (C_ROW + 184 * p + 32) 32 =
          leafB c96 (msg ⟨2 * p, by unfold LENGTH LOG_LENGTH; omega⟩) ∧
        readBuffer sbne (C_ROW + 184 * p + 120) 32 =
          leafA c96 (msg ⟨2 * p + 1, by unfold LENGTH LOG_LENGTH; omega⟩) ∧
        readBuffer sbne (C_ROW + 184 * p + 152) 32 =
          leafB c96 (msg ⟨2 * p + 1, by unfold LENGTH LOG_LENGTH; omega⟩)) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (∀ k < 4096, q < C_ROW + 184 * (4096 * c + k) ∨
          (C_ROW + 184 * (4096 * c + k) + 64 ≤ q ∧ q < C_ROW + 184 * (4096 * c + k) + 120) ∨
          C_ROW + 184 * (4096 * c + k + 1) ≤ q) →
        sbne.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5905584160 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hind : ∀ (m : Nat) (hm : m ≤ 4096),
      ∃ sm,
        DetRun oracle (submission.image .commit) sc (12 * m) sm (40 * m) (4 * m) ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (81960 + 12 * m)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sm.getReg r = sc.getReg r) ∧
        sm.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (4096 * c + m) - 96) ∧
        sm.getReg .x12 = BitVec.ofNat 64 (C_ROW + 184 * (4096 * c + m) - 32) ∧
        (∀ (k : Nat) (hk : k < m),
          let p := 4096 * c + k
          readBuffer sm (C_ROW + 184 * p) 32 = leafA c96 (msg ⟨2 * p, by omega⟩) ∧
          readBuffer sm (C_ROW + 184 * p + 32) 32 = leafB c96 (msg ⟨2 * p, by omega⟩) ∧
          readBuffer sm (C_ROW + 184 * p + 120) 32 = leafA c96 (msg ⟨2 * p + 1, by omega⟩) ∧
          readBuffer sm (C_ROW + 184 * p + 152) 32 = leafB c96 (msg ⟨2 * p + 1, by omega⟩)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ k < m, q < C_ROW + 184 * (4096 * c + k) ∨
            (C_ROW + 184 * (4096 * c + k) + 64 ≤ q ∧ q < C_ROW + 184 * (4096 * c + k) + 120) ∨
            C_ROW + 184 * (4096 * c + k + 1) ≤ q) →
          sm.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩
    | succ m ih =>
      obtain ⟨sm, hrunm, hpcm, hregm, hx10m, hx12m, hresm, hpresm⟩ := ih (by omega)
      have hpres_msg : ∀ (i : Index) (off : Nat), off + 96 ≤ 256 →
          readBuffer sm (C_MSG + 256 * i.val + off) 96 = readBuffer sc (C_MSG + 256 * i.val + off) 96 := by
        intro i off hoff
        have hi := i.isLt
        exact readBuffer_congr _ _ _ _ (fun j hj => hpresm (C_MSG + 256 * i.val + off + j) (by omega)
          (fun _ _ => by omega))
      obtain ⟨sn, hrun1, hpcn, hregn, hx10n, hx12n, ha0, hb0, ha1, hb1, hpres1⟩ :=
        commit_leaf12_pair h768 oracle msg m (4096 * c + m) (by omega) (by omega) sm hpcm
          ((hregm .x5 (by decide) (by decide)).trans hx5)
          ((hregm .x11 (by decide) (by decide)).trans hx11)
          ((hregm .x13 (by decide) (by decide)).trans hx13) hx10m hx12m
          ((hpres_msg ⟨2 * (4096 * c + m), by omega⟩ 64 (by omega)).trans (h1A ⟨2 * (4096 * c + m), by omega⟩).1)
          ((hpres_msg ⟨2 * (4096 * c + m), by omega⟩ 160 (by omega)).trans (h1A ⟨2 * (4096 * c + m), by omega⟩).2)
          ((hpres_msg ⟨2 * (4096 * c + m) + 1, by omega⟩ 64 (by omega)).trans (h1A ⟨2 * (4096 * c + m) + 1, by omega⟩).1)
          ((hpres_msg ⟨2 * (4096 * c + m) + 1, by omega⟩ 160 (by omega)).trans (h1A ⟨2 * (4096 * c + m) + 1, by omega⟩).2)
      have hrun_next : DetRun oracle (submission.image .commit) sc (12 * (m + 1)) sn
          (40 * (m + 1)) (4 * (m + 1)) := by
        have h := hrunm.trans hrun1
        rw [show 12 * m + 12 = 12 * (m + 1) by omega, show 40 * m + 40 = 40 * (m + 1) by omega,
            show 4 * m + 4 = 4 * (m + 1) by omega] at h
        exact h
      refine ⟨sn, hrun_next, hpcn, fun r h10 h12 => (hregn r h10 h12).trans (hregm r h10 h12),
        by rw [hx10n]; exact congrArg (BitVec.ofNat 64) (by omega),
        by rw [hx12n]; exact congrArg (BitVec.ofNat 64) (by omega), ?_, ?_⟩
      · intro k hk
        by_cases hkm : k = m
        · subst hkm; exact ⟨ha0, hb0, ha1, hb1⟩
        · obtain ⟨h0, h1, h2, h3⟩ := hresm k (by omega)
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact (readBuffer_congr _ _ _ _ (fun j hj => hpres1 _ (by omega) (by omega))).trans h0
          · exact (readBuffer_congr _ _ _ _ (fun j hj => hpres1 _ (by omega) (by omega))).trans h1
          · exact (readBuffer_congr _ _ _ _ (fun j hj => hpres1 _ (by omega) (by omega))).trans h2
          · exact (readBuffer_congr _ _ _ _ (fun j hj => hpres1 _ (by omega) (by omega))).trans h3
      · intro q hq hout
        have h1 := hpres1 q hq (hout m (by omega))
        have h2 := hpresm q hq (fun k hk => hout k (by omega))
        exact h1.trans h2
  obtain ⟨sm, hrun64, hpc64, hreg64, hx10_64, hx12_64, hres64, hpres64⟩ := hind 4096 (le_refl _)
  let sbne := latchResult sm 81960 131115
  have hbne : DetRun oracle (submission.image .commit) sm 2 sbne 2 0 :=
    longRun oracle sm 131112 81960 (by decide +kernel) hpc64
  have hmem_bne : sbne.mem = sm.mem := rfl
  have hreg_bne : ∀ r, sbne.getReg r = sm.getReg r := fun _ => rfl
  have hpc_end : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < 2048 then 81960 else 131115)) := by
    have hx19m : sm.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 96) :=
      (hreg64 .x19 (by decide) (by decide)).trans hx19
    by_cases hlt : c + 1 < 2048
    · have hne : (sm.getReg .x10 != sm.getReg .x19) = true := by
        rw [hx10_64, hx19m, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp [latchResult,sbne,hlt,hne,lpc,pc_setPC]
    · have heq : (sm.getReg .x10 != sm.getReg .x19) = false := by
        rw [hx10_64, hx19m, show C_MSG + 512 * (4096 * c + 4096) - 96 = C_MSG + 2 ^ 32 - 96 by omega]
        exact bne_self_eq_false _
      simp [latchResult,sbne,hlt,heq,lpc,pc_setPC]
  refine ⟨sbne, hrun64.trans hbne, hpc_end,
    fun r h10 h12 => (hreg_bne r).trans (hreg64 r h10 h12),
    by rw [hreg_bne, hx10_64]; exact congrArg (BitVec.ofNat 64) (by omega),
    by rw [hreg_bne, hx12_64]; exact congrArg (BitVec.ofNat 64) (by omega),
    fun k hk =>
      let ⟨h0, h1, h2, h3⟩ := hres64 k hk
      ⟨(readBuffer_of_mem_eq hmem_bne _ _).trans h0,
       (readBuffer_of_mem_eq hmem_bne _ _).trans h1,
       (readBuffer_of_mem_eq hmem_bne _ _).trans h2,
       (readBuffer_of_mem_eq hmem_bne _ _).trans h3⟩,
    fun q hq hout => (getByte_of_mem_eq hmem_bne _).trans (hpres64 q hq hout)⟩

/-- Full Phase 1B (`words 81960..131122`): `100,667,400` steps, `335,548,424` cycles, `33,554,432` calls. -/
private theorem commit_phase1B (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (s1 : MachineState)
    (hpc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 81960))
    (hx2 : s1.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s1.getReg .x5 = 0#64) (hx9 : s1.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s1.getReg .x10 = BitVec.ofNat 64 (C_MSG - 96))
    (hx11 : s1.getReg .x11 = 96#64)
    (hx12 : s1.getReg .x12 = BitVec.ofNat 64 (C_ROW - 32))
    (hx13 : s1.getReg .x13 = 0#64)
    (hx18 : s1.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx19 : s1.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 96))
    (hx26 : s1.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (h1A : ∀ i : Index,
      readBuffer s1 (C_MSG + 256 * i.val + 64) 96 =
        leafAInput ((fun x => oracle.compression (x.cast h768.symm)) (leafUInput (msg i))) (msg i) ∧
      readBuffer s1 (C_MSG + 256 * i.val + 160) 96 = leafBInput (msg i)) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s2,
      DetRun oracle (submission.image .commit) s1 100667400 s2 335548424 33554432 ∧
      s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 131123) ∧
      s2.getReg .x2 = BitVec.ofNat 64 C_DB ∧ s2.getReg .x5 = 0#64 ∧
      s2.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s2.getReg .x10 = BitVec.ofNat 64 (C_ROW - 96) ∧ s2.getReg .x11 = 96#64 ∧
      s2.getReg .x12 = BitVec.ofNat 64 (C_TD - 32) ∧ s2.getReg .x13 = 0#64 ∧
      s2.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
      s2.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes - 96) ∧
      s2.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ p : Fin (LENGTH / 2),
        readBuffer s2 (C_ROW + 184 * p.val) 32 =
          leafA c96 (msg ⟨2 * p.val, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
        readBuffer s2 (C_ROW + 184 * p.val + 32) 32 =
          leafB c96 (msg ⟨2 * p.val, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
        readBuffer s2 (C_ROW + 184 * p.val + 120) 32 =
          leafA c96 (msg ⟨2 * p.val + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
        readBuffer s2 (C_ROW + 184 * p.val + 152) 32 =
          leafB c96 (msg ⟨2 * p.val + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩)) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (∀ p < LENGTH / 2, q < C_ROW + 184 * p ∨
          (C_ROW + 184 * p + 64 ≤ q ∧ q < C_ROW + 184 * p + 120) ∨
          C_ROW + 184 * (p + 1) ≤ q) →
        s2.getByte (BitVec.ofNat 64 q) = s1.getByte (BitVec.ofNat 64 q)) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5905584160 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hloop : ∀ (n : Nat) (hn : n ≤ 2048),
      ∃ sn,
        DetRun oracle (submission.image .commit) s1 (49154 * n) sn (163842 * n) (16384 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 2048 then 81960 else 131115)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sn.getReg r = s1.getReg r) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (4096 * n) - 96) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_ROW + 184 * (4096 * n) - 32) ∧
        (∀ (p : Nat) (hp : p < 4096 * n),
          readBuffer sn (C_ROW + 184 * p) 32 = leafA c96 (msg ⟨2 * p, by omega⟩) ∧
          readBuffer sn (C_ROW + 184 * p + 32) 32 = leafB c96 (msg ⟨2 * p, by omega⟩) ∧
          readBuffer sn (C_ROW + 184 * p + 120) 32 = leafA c96 (msg ⟨2 * p + 1, by omega⟩) ∧
          readBuffer sn (C_ROW + 184 * p + 152) 32 = leafB c96 (msg ⟨2 * p + 1, by omega⟩)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ p < 4096 * n, q < C_ROW + 184 * p ∨
            (C_ROW + 184 * p + 64 ≤ q ∧ q < C_ROW + 184 * p + 120) ∨
            C_ROW + 184 * (p + 1) ≤ q) →
          sn.getByte (BitVec.ofNat 64 q) = s1.getByte (BitVec.ofNat 64 q)) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨s1, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hregn, hx10n, hx12n, hresn, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 81960) := by
        simpa only [show n < 2048 by omega, ite_true] using hpcn
      have h1An : ∀ i : Index,
          readBuffer sn (C_MSG + 256 * i.val + 64) 96 = leafAInput (c96 (leafUInput (msg i))) (msg i) ∧
          readBuffer sn (C_MSG + 256 * i.val + 160) 96 = leafBInput (msg i) := by
        intro i; have hi := i.isLt
        exact ⟨(readBuffer_congr _ _ _ _ (fun j hj => hpresn _ (by omega) (fun _ _ => by omega))).trans (h1A i).1,
               (readBuffer_congr _ _ _ _ (fun j hj => hpresn _ (by omega) (fun _ _ => by omega))).trans (h1A i).2⟩
      obtain ⟨sm, hrunC, hpcm, hregC, hx10m, hx12m, hresC, hpresC⟩ :=
        commit_phase1B_chunk h768 oracle msg n (by omega) sn hpc_in
          ((hregn .x5 (by decide) (by decide)).trans hx5)
          ((hregn .x11 (by decide) (by decide)).trans hx11)
          ((hregn .x13 (by decide) (by decide)).trans hx13) hx10n hx12n
          ((hregn .x19 (by decide) (by decide)).trans hx19) h1An
      have hrun_n1 : DetRun oracle (submission.image .commit) s1 (49154 * (n + 1)) sm
          (163842 * (n + 1)) (16384 * (n + 1)) := by
        have h := hrunn.trans hrunC
        rw [show 49154 * n + 49154 = 49154 * (n + 1) by omega,
            show 163842 * n + 163842 = 163842 * (n + 1) by omega,
            show 16384 * n + 16384 = 16384 * (n + 1) by omega] at h
        exact h
      refine ⟨sm, hrun_n1, hpcm, fun r h10 h12 => (hregC r h10 h12).trans (hregn r h10 h12),
        hx10m, hx12m, ?_, ?_⟩
      · intro p hp
        by_cases hold : p < 4096 * n
        · obtain ⟨h0, h1, h2, h3⟩ := hresn p hold
          refine ⟨?_, ?_, ?_, ?_⟩
          · exact (readBuffer_congr _ _ _ _ (fun j hj => hpresC _ (by omega) (fun _ _ => by omega))).trans h0
          · exact (readBuffer_congr _ _ _ _ (fun j hj => hpresC _ (by omega) (fun _ _ => by omega))).trans h1
          · exact (readBuffer_congr _ _ _ _ (fun j hj => hpresC _ (by omega) (fun _ _ => by omega))).trans h2
          · exact (readBuffer_congr _ _ _ _ (fun j hj => hpresC _ (by omega) (fun _ _ => by omega))).trans h3
        · have hk : p - 4096 * n < 4096 := by omega
          have heq : 4096 * n + (p - 4096 * n) = p := by omega
          simpa only [heq] using hresC (p - 4096 * n) hk
      · intro q hq hout
        have h1 := hpresC q hq (fun k hk => hout (4096 * n + k) (by omega))
        have h2 := hpresn q hq (fun p hp => hout p (by omega))
        exact h1.trans h2
  obtain ⟨sb, hrun_loop, hpc_b, hreg_b, _, _, hres_b, hpres_b⟩ := hloop 2048 (le_refl _)
  have hpc_b' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 131115) := by
    simpa only [Nat.lt_irrefl, ite_false] using hpc_b
  let s2 := commitMid1BInstrs.foldl execInstrBr sb
  have hmid_run : DetRun oracle (submission.image .commit) sb 8 s2 8 0 :=
    commit_mid1B_run oracle sb hpc_b'
  obtain ⟨hs2_pc, hs2_mem, hs2_x2, hs2_x5, hs2_x9, hs2_x10, hs2_x11, hs2_x12,
    hs2_x13, hs2_x18, hs2_x19, hs2_x26⟩ := commit_mid1B_spec sb hpc_b'
      ((hreg_b .x2 (by decide) (by decide)).trans hx2)
      ((hreg_b .x5 (by decide) (by decide)).trans hx5)
      ((hreg_b .x9 (by decide) (by decide)).trans hx9)
      ((hreg_b .x11 (by decide) (by decide)).trans hx11)
      ((hreg_b .x13 (by decide) (by decide)).trans hx13)
      ((hreg_b .x18 (by decide) (by decide)).trans hx18)
      ((hreg_b .x26 (by decide) (by decide)).trans hx26)
  refine ⟨s2, by simpa using hrun_loop.trans hmid_run,
    hs2_pc, hs2_x2, hs2_x5, hs2_x9, hs2_x10, hs2_x11, hs2_x12, hs2_x13, hs2_x18, hs2_x19, hs2_x26, ?_, ?_⟩
  · intro ⟨p, hp⟩
    obtain ⟨h0, h1, h2, h3⟩ := hres_b p (by omega)
    exact ⟨(readBuffer_of_mem_eq hs2_mem _ _).trans h0,
           (readBuffer_of_mem_eq hs2_mem _ _).trans h1,
           (readBuffer_of_mem_eq hs2_mem _ _).trans h2,
           (readBuffer_of_mem_eq hs2_mem _ _).trans h3⟩
  · intro q hq hout
    exact (getByte_of_mem_eq hs2_mem _).trans (hpres_b q hq (fun p hp => hout p (by omega)))

/-! ### 4. Phase 1C: `leaf3_loop` (words `131123..180277`) -/

private theorem pairSalts_even (rand : Fin (LENGTH / 2) → PairRand) (p : Nat) (hp : p < LENGTH / 2) :
    pairSalts rand ⟨2 * p, by unfold LENGTH LOG_LENGTH at *; omega⟩ = pairSaltEven (rand ⟨p, hp⟩) := by
  unfold pairSalts
  simp only [show 2 * p / 2 = p by omega, show 2 * p % 2 = 0 by omega, ite_true]

private theorem pairSalts_odd (rand : Fin (LENGTH / 2) → PairRand) (p : Nat) (hp : p < LENGTH / 2) :
    pairSalts rand ⟨2 * p + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩ = pairSaltOdd (rand ⟨p, hp⟩) := by
  unfold pairSalts
  simp only [show (2 * p + 1) / 2 = p by omega, show (2 * p + 1) % 2 = 1 by omega,
    show (1 : Nat) ≠ 0 by decide, ite_false]

/-- One pair of Phase 1C (`leaf3PairInstr`: `6` steps, `20` cycles, `2` calls). -/
private theorem commit_leaf3_pair (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (rand : Fin (LENGTH / 2) → PairRand)
    (k p : Nat) (hk : k < 8192) (hp : p < LENGTH / 2) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (131123 + 6 * k)))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * p - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + 64 * p - 32))
    (ha0 : readBuffer s (C_ROW + 184 * p) 32 =
      leafA (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p, by unfold LENGTH LOG_LENGTH at *; omega⟩))
    (hb0 : readBuffer s (C_ROW + 184 * p + 32) 32 =
      leafB (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p, by unfold LENGTH LOG_LENGTH at *; omega⟩))
    (hgap0 : readBuffer s (C_ROW + 184 * p + 64) 8 = 0)
    (hsaltEv : readBuffer s (C_ROW + 184 * p + 72) 24 = pairSaltEven (rand ⟨p, hp⟩))
    (hsaltOd : readBuffer s (C_ROW + 184 * p + 88) 24 = pairSaltOdd (rand ⟨p, hp⟩))
    (hgap1 : readBuffer s (C_ROW + 184 * p + 112) 8 = 0)
    (ha1 : readBuffer s (C_ROW + 184 * p + 120) 32 =
      leafA (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩))
    (hb1 : readBuffer s (C_ROW + 184 * p + 152) 32 =
      leafB (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩)) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s',
      DetRun oracle (submission.image .commit) s 6 s' 20 2 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (131123 + 6 * (k + 1))) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (p + 1) - 96) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + 64 * (p + 1) - 32) ∧
      readBuffer s' (C_TD + 32 * (2 * p)) 32 = nodeVal c96 msg (pairSalts rand) 0 (2 * p) ∧
      readBuffer s' (C_TD + 32 * (2 * p + 1)) 32 = nodeVal c96 msg (pairSalts rand) 0 (2 * p + 1) ∧
      MemPreservedOutside s s' (C_TD + 64 * p) (C_TD + 64 * (p + 1)) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5905584160 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let d0 := nodeVal c96 msg (pairSalts rand) 0 (2 * p)
  let d1 := nodeVal c96 msg (pairSalts rand) 0 (2 * p + 1)
  have hd0_eq : oracle.compression ((readBuffer s (C_ROW + 184 * p) 96).cast h768.symm) = d0 := by
    rw [readBuffer_lateEven s (C_ROW + 184 * p) hgap0, ha0, hb0, hsaltEv]
    unfold d0 nodeVal nodeValFromLeaves leafDigest leafFinalInput
    simp only [show 2 * p < LENGTH by omega, dite_true, show 2 * p % 2 = 0 by omega, ite_true,
      pairSalts_even rand p hp]
    rfl
  obtain ⟨s1, hr1, hpc1, hreg1, hx10_1, hx12_1, hdig0, hp1⟩ :=
    commit_inc_compress h768 oracle s (131123 + 6 * k) (C_ROW + 184 * p - 96) (C_TD + 64 * p - 32) 96 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hpc hx5 hx11 hx13 hx10 hx12
      (commit_fetch_leaf3 s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc))
      (fun st hst => commit_fetch_leaf3 st k 1 hk (by omega) hst)
      (fun st hst => commit_fetch_leaf3 st k 2 hk (by omega) hst) d0
      (by rw [show C_ROW + 184 * p - 96 + 96 = C_ROW + 184 * p by omega]; exact hd0_eq)
  have hd1_eq : oracle.compression ((readBuffer s1 (C_ROW + 184 * p + 88) 96).cast h768.symm) = d1 := by
    rw [hp1.readBuffer_eq (by omega) (by omega),
        readBuffer_lateOdd s (C_ROW + 184 * p + 88)
          (by simpa only [show C_ROW + 184 * p + 88 + 24 = C_ROW + 184 * p + 112 by omega] using hgap1),
        show C_ROW + 184 * p + 88 + 32 = C_ROW + 184 * p + 120 by omega,
        show C_ROW + 184 * p + 88 + 64 = C_ROW + 184 * p + 152 by omega,
        ha1, hb1, hsaltOd]
    unfold d1 nodeVal nodeValFromLeaves leafDigest leafFinalInput
    simp only [show 2 * p + 1 < LENGTH by omega, dite_true, show (2 * p + 1) % 2 = 1 by omega,
      show (1 : Nat) ≠ 0 by decide, ite_false, pairSalts_odd rand p hp]
    rfl
  obtain ⟨s2, hr2, hpc2, hreg2, hx10_2, hx12_2, hdig1, hp2⟩ :=
    commit_inc_compress h768 oracle s1 (131123 + 6 * k + 3)
      (C_ROW + 184 * p - 96 + 96) (C_TD + 64 * p - 32 + 32) 88 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hpc1
      ((hreg1 .x5 (by decide) (by decide)).trans hx5)
      ((hreg1 .x11 (by decide) (by decide)).trans hx11)
      ((hreg1 .x13 (by decide) (by decide)).trans hx13) hx10_1 hx12_1
      (commit_fetch_leaf3 s1 k 3 hk (by omega) hpc1)
      (fun st hst => commit_fetch_leaf3 st k 4 hk (by omega) (by simpa only [Nat.add_assoc] using hst))
      (fun st hst => commit_fetch_leaf3 st k 5 hk (by omega) (by simpa only [Nat.add_assoc] using hst)) d1
      (by rw [show C_ROW + 184 * p - 96 + 96 + 88 = C_ROW + 184 * p + 88 by omega]; exact hd1_eq)
  refine ⟨s2, by simpa using hr1.trans hr2,
    by rw [hpc2]; exact congrArg (BitVec.ofNat 64) (by omega),
    fun r h10 h12 => (hreg2 r h10 h12).trans (hreg1 r h10 h12),
    by rw [hx10_2]; exact congrArg (BitVec.ofNat 64) (by omega),
    by rw [hx12_2]; exact congrArg (BitVec.ofNat 64) (by omega), ?_, ?_, ?_⟩
  · rw [hp2.readBuffer_eq (by omega) (by omega)]
    simpa [show C_TD + 64 * p - 32 + 32 = C_TD + 32 * (2 * p) by omega] using hdig0
  · simpa [show C_TD + 64 * p - 32 + 32 + 32 = C_TD + 32 * (2 * p + 1) by omega] using hdig1
  · exact (hp1.mono (by omega) (by omega)).trans (hp2.mono (by omega) (by omega))

/-- One 8,192-pair chunk of Phase 1C (`words 131123..180277`: `49154` steps, `163842` cycles, `16,384` calls). -/
private theorem commit_phase1C_chunk (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (rand : Fin (LENGTH / 2) → PairRand)
    (c : Nat) (hc : c < 1024) (sc : MachineState)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 131123))
    (hx5 : sc.getReg .x5 = 0#64) (hx11 : sc.getReg .x11 = 96#64) (hx13 : sc.getReg .x13 = 0#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (8192 * c) - 96))
    (hx12 : sc.getReg .x12 = BitVec.ofNat 64 (C_TD + 64 * (8192 * c) - 32))
    (hx19 : sc.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes - 96))
    (hrow : ∀ p : Fin (LENGTH / 2),
      readBuffer sc (C_ROW + 184 * p.val) 32 =
        leafA (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer sc (C_ROW + 184 * p.val + 32) 32 =
        leafB (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer sc (C_ROW + 184 * p.val + 64) 8 = 0 ∧
      readBuffer sc (C_ROW + 184 * p.val + 72) 24 = pairSaltEven (rand p) ∧
      readBuffer sc (C_ROW + 184 * p.val + 88) 24 = pairSaltOdd (rand p) ∧
      readBuffer sc (C_ROW + 184 * p.val + 112) 8 = 0 ∧
      readBuffer sc (C_ROW + 184 * p.val + 120) 32 =
        leafA (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer sc (C_ROW + 184 * p.val + 152) 32 =
        leafB (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩)) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ sbne,
      DetRun oracle (submission.image .commit) sc 49154 sbne 163842 16384 ∧
      sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < 1024 then 131123 else 180278)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sbne.getReg r = sc.getReg r) ∧
      sbne.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (8192 * (c + 1)) - 96) ∧
      sbne.getReg .x12 = BitVec.ofNat 64 (C_TD + 64 * (8192 * (c + 1)) - 32) ∧
      (∀ idx, 16384 * c ≤ idx → idx < 16384 * (c + 1) →
        readBuffer sbne (C_TD + 32 * idx) 32 = nodeVal c96 msg (pairSalts rand) 0 idx) ∧
      MemPreservedOutside sc sbne (C_TD + 64 * (8192 * c)) (C_TD + 64 * (8192 * (c + 1))) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5905584160 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hrb := rowBytes_eq
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hind : ∀ m ≤ 8192,
      ∃ sm,
        DetRun oracle (submission.image .commit) sc (6 * m) sm (20 * m) (2 * m) ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (131123 + 6 * m)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sm.getReg r = sc.getReg r) ∧
        sm.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (8192 * c + m) - 96) ∧
        sm.getReg .x12 = BitVec.ofNat 64 (C_TD + 64 * (8192 * c + m) - 32) ∧
        (∀ idx, 16384 * c ≤ idx → idx < 16384 * c + 2 * m →
          readBuffer sm (C_TD + 32 * idx) 32 = nodeVal c96 msg (pairSalts rand) 0 idx) ∧
        MemPreservedOutside sc sm (C_TD + 64 * (8192 * c)) (C_TD + 64 * (8192 * c + m)) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12, fun _ h1 h2 => by omega, MemPreservedOutside.refl _ _ _⟩
    | succ m ih =>
      obtain ⟨sm, hrunm, hpcm, hregm, hx10m, hx12m, hdigm, hpresm⟩ := ih (by omega)
      have hpres_row : ∀ (addr n : Nat), C_ROW ≤ addr → addr + n ≤ 2 ^ 64 →
          readBuffer sm addr n = readBuffer sc addr n := fun addr n hge hbd =>
        hpresm.readBuffer_eq hbd (by omega)
      obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hrow ⟨8192 * c + m, by omega⟩
      obtain ⟨sn, hrun1, hpcn, hregn, hx10n, hx12n, hd0, hd1, hpres1⟩ :=
        commit_leaf3_pair h768 oracle msg rand m (8192 * c + m) (by omega) (by omega) sm hpcm
          ((hregm .x5 (by decide) (by decide)).trans hx5)
          ((hregm .x11 (by decide) (by decide)).trans hx11)
          ((hregm .x13 (by decide) (by decide)).trans hx13) hx10m hx12m
          ((hpres_row _ 32 (by omega) (by omega)).trans r0)
          ((hpres_row _ 32 (by omega) (by omega)).trans r1)
          ((hpres_row _ 8 (by omega) (by omega)).trans r2)
          ((hpres_row _ 24 (by omega) (by omega)).trans r3)
          ((hpres_row _ 24 (by omega) (by omega)).trans r4)
          ((hpres_row _ 8 (by omega) (by omega)).trans r5)
          ((hpres_row _ 32 (by omega) (by omega)).trans r6)
          ((hpres_row _ 32 (by omega) (by omega)).trans r7)
      have hrun_next : DetRun oracle (submission.image .commit) sc (6 * (m + 1)) sn
          (20 * (m + 1)) (2 * (m + 1)) := by
        have h := hrunm.trans hrun1
        rw [show 6 * m + 6 = 6 * (m + 1) by omega, show 20 * m + 20 = 20 * (m + 1) by omega,
            show 2 * m + 2 = 2 * (m + 1) by omega] at h
        exact h
      refine ⟨sn, hrun_next, hpcn, fun r h10 h12 => (hregn r h10 h12).trans (hregm r h10 h12),
        by rw [hx10n]; exact congrArg (BitVec.ofNat 64) (by omega),
        by rw [hx12n]; exact congrArg (BitVec.ofNat 64) (by omega), ?_,
        (hpresm.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (by omega))⟩
      intro idx hlo hhi
      by_cases hold : idx < 16384 * c + 2 * m
      · exact (hpres1.readBuffer_eq (by omega) (by omega)).trans (hdigm idx hlo hold)
      · by_cases hev : idx = 2 * (8192 * c + m)
        · subst hev; exact hd0
        · have hodd : idx = 2 * (8192 * c + m) + 1 := by omega
          subst hodd; exact hd1
  obtain ⟨sm, hrun128, hpc128, hreg128, hx10_128, hx12_128, hdig128, hpres128⟩ := hind 8192 (le_refl _)
  let sbne := latchResult sm 131123 180278
  have hbne : DetRun oracle (submission.image .commit) sm 2 sbne 2 0 :=
    longRun oracle sm 180275 131123 (by decide +kernel) hpc128
  have hmem_bne : sbne.mem = sm.mem := rfl
  have hreg_bne : ∀ r, sbne.getReg r = sm.getReg r := fun _ => rfl
  have hpc_end : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < 1024 then 131123 else 180278)) := by
    have hx19m : sm.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes - 96) :=
      (hreg128 .x19 (by decide) (by decide)).trans hx19
    by_cases hlt : c + 1 < 1024
    · have hne : (sm.getReg .x10 != sm.getReg .x19) = true := by
        rw [hx10_128, hx19m, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp [latchResult,sbne,hlt,hne,lpc,pc_setPC]
    · have heq : (sm.getReg .x10 != sm.getReg .x19) = false := by
        rw [hx10_128, hx19m, show C_ROW + 184 * (8192 * c + 8192) - 96 = C_ROW + rowBytes - 96 by omega]
        exact bne_self_eq_false _
      simp [latchResult,sbne,hlt,heq,lpc,pc_setPC]
  refine ⟨sbne, hrun128.trans hbne, hpc_end,
    fun r h10 h12 => (hreg_bne r).trans (hreg128 r h10 h12),
    by rw [hreg_bne, hx10_128]; exact congrArg (BitVec.ofNat 64) (by omega),
    by rw [hreg_bne, hx12_128]; exact congrArg (BitVec.ofNat 64) (by omega),
    fun idx hlo hhi => (readBuffer_of_mem_eq hmem_bne _ _).trans (hdig128 idx hlo (by omega)),
    (hpres128.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmem_bne _ _)⟩

/-- Full Phase 1C (`words 131123..180277`): `50,333,696` steps, `167,774,208` cycles, `16,777,216` calls. -/
private theorem commit_phase1C (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (rand : Fin (LENGTH / 2) → PairRand) (s2 : MachineState)
    (hpc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 131123))
    (hx2 : s2.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s2.getReg .x5 = 0#64) (hx9 : s2.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s2.getReg .x10 = BitVec.ofNat 64 (C_ROW - 96))
    (hx11 : s2.getReg .x11 = 96#64)
    (hx12 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD - 32))
    (hx13 : s2.getReg .x13 = 0#64)
    (hx19 : s2.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes - 96))
    (hx26 : s2.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hrow : ∀ p : Fin (LENGTH / 2),
      readBuffer s2 (C_ROW + 184 * p.val) 32 =
        leafA (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 32) 32 =
        leafB (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 64) 8 = 0 ∧
      readBuffer s2 (C_ROW + 184 * p.val + 72) 24 = pairSaltEven (rand p) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 88) 24 = pairSaltOdd (rand p) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 112) 8 = 0 ∧
      readBuffer s2 (C_ROW + 184 * p.val + 120) 32 =
        leafA (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 152) 32 =
        leafB (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩)) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s3,
      DetRun oracle (submission.image .commit) s2 50333696 s3 167774208 16777216 ∧
      s3.pc = BitVec.ofNat 64 (0x1000 + 4 * 180278) ∧
      s3.getReg .x2 = BitVec.ofNat 64 C_DB ∧ s3.getReg .x5 = 0#64 ∧
      s3.getReg .x9 = BitVec.ofNat 64 C_TD ∧ s3.getReg .x11 = 96#64 ∧
      s3.getReg .x13 = 0#64 ∧ s3.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ idx < LENGTH, readBuffer s3 (C_TD + 32 * idx) 32 = nodeVal c96 msg (pairSalts rand) 0 idx) ∧
      MemPreservedOutside s2 s3 C_TD (C_TD + levelBase 1) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5905584160 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hlb1 : levelBase 1 = 536870912 := by decide
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hloop : ∀ n ≤ 1024,
      ∃ sn,
        DetRun oracle (submission.image .commit) s2 (49154 * n) sn (163842 * n) (16384 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 1024 then 131123 else 180278)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sn.getReg r = s2.getReg r) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (8192 * n) - 96) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_TD + 64 * (8192 * n) - 32) ∧
        (∀ idx < 16384 * n, readBuffer sn (C_TD + 32 * idx) 32 = nodeVal c96 msg (pairSalts rand) 0 idx) ∧
        MemPreservedOutside s2 sn C_TD (C_TD + 64 * (8192 * n)) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨s2, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12, fun _ h => (Nat.not_lt_zero _ h).elim,
        MemPreservedOutside.refl _ _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hregn, hx10n, hx12n, hdign, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 131123) := by
        simpa only [show n < 1024 by omega, ite_true] using hpcn
      have hrown : ∀ p : Fin (LENGTH / 2),
          readBuffer sn (C_ROW + 184 * p.val) 32 = leafA c96 (msg ⟨2 * p.val, by omega⟩) ∧
          readBuffer sn (C_ROW + 184 * p.val + 32) 32 = leafB c96 (msg ⟨2 * p.val, by omega⟩) ∧
          readBuffer sn (C_ROW + 184 * p.val + 64) 8 = 0 ∧
          readBuffer sn (C_ROW + 184 * p.val + 72) 24 = pairSaltEven (rand p) ∧
          readBuffer sn (C_ROW + 184 * p.val + 88) 24 = pairSaltOdd (rand p) ∧
          readBuffer sn (C_ROW + 184 * p.val + 112) 8 = 0 ∧
          readBuffer sn (C_ROW + 184 * p.val + 120) 32 = leafA c96 (msg ⟨2 * p.val + 1, by omega⟩) ∧
          readBuffer sn (C_ROW + 184 * p.val + 152) 32 = leafB c96 (msg ⟨2 * p.val + 1, by omega⟩) := by
        intro p; have hp := p.isLt
        obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hrow p
        exact ⟨(hpresn.readBuffer_eq (by omega) (by omega)).trans r0,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans r1,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans r2,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans r3,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans r4,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans r5,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans r6,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans r7⟩
      obtain ⟨sm, hrunC, hpcm, hregC, hx10m, hx12m, hdigC, hpresC⟩ :=
        commit_phase1C_chunk h768 oracle msg rand n (by omega) sn hpc_in
          ((hregn .x5 (by decide) (by decide)).trans hx5)
          ((hregn .x11 (by decide) (by decide)).trans hx11)
          ((hregn .x13 (by decide) (by decide)).trans hx13) hx10n hx12n
          ((hregn .x19 (by decide) (by decide)).trans hx19) hrown
      have hrun_n1 : DetRun oracle (submission.image .commit) s2 (49154 * (n + 1)) sm
          (163842 * (n + 1)) (16384 * (n + 1)) := by
        have h := hrunn.trans hrunC
        rw [show 49154 * n + 49154 = 49154 * (n + 1) by omega,
            show 163842 * n + 163842 = 163842 * (n + 1) by omega,
            show 16384 * n + 16384 = 16384 * (n + 1) by omega] at h
        exact h
      refine ⟨sm, hrun_n1, hpcm, fun r h10 h12 => (hregC r h10 h12).trans (hregn r h10 h12),
        hx10m, hx12m, ?_, (hpresn.mono (le_refl _) (by omega)).trans (hpresC.mono (by omega) (le_refl _))⟩
      intro idx hidx
      by_cases hold : idx < 16384 * n
      · exact (hpresC.readBuffer_eq (by omega) (by omega)).trans (hdign idx hold)
      · exact hdigC idx (by omega) hidx
  obtain ⟨s3, hrun, hpc3, hreg3, _, _, hdig3, hpres3⟩ := hloop 1024 (le_refl _)
  refine ⟨s3, hrun, by simpa only [Nat.lt_irrefl, ite_false] using hpc3,
    (hreg3 .x2 (by decide) (by decide)).trans hx2,
    (hreg3 .x5 (by decide) (by decide)).trans hx5,
    (hreg3 .x9 (by decide) (by decide)).trans hx9,
    (hreg3 .x11 (by decide) (by decide)).trans hx11,
    (hreg3 .x13 (by decide) (by decide)).trans hx13,
    (hreg3 .x26 (by decide) (by decide)).trans hx26,
    fun idx hidx => hdig3 idx (by omega),
    hpres3.mono (le_refl _) (by omega)⟩

/-! ### 5. Complete Phase 1 Composition (1A + 1B + 1C, words `32797..180277`) -/

/-- Complete Phase 1 (`words 32797..180277`): `201,334,800` steps, `671,096,848` cycles,
`67,108,864` compression calls. Writes all `16,777,216` leaves to `L0` while preserving all
salts in `C_ROW` and all memory in `[C_TD + levelBase 1, C_ROW) ∪ [C_TD + trapdoorBytes, 2^64)`. -/
theorem commit_phase1 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (rand : Fin (LENGTH / 2) → PairRand) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 32797))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx8 : s0.getReg .x8 = BitVec.ofNat 64 C_MSG)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 (C_MSG - 256))
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx19 : s0.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hmsg0 : ∀ (i : Index) (j : Nat), j < 256 →
      s0.getByte (BitVec.ofNat 64 (C_MSG + 256 * i.val + j)) = (msg i).extractLsb' (8 * j) 8)
    (hsalt0 : ∀ j : Fin (LENGTH / 2),
      readBuffer s0 (C_ROW + 184 * j.val + 72) 24 = pairSaltEven (rand j) ∧
      readBuffer s0 (C_ROW + 184 * j.val + 88) 24 = pairSaltOdd (rand j))
    (hgap0 : ∀ j : Fin (LENGTH / 2),
      readBuffer s0 (C_ROW + 184 * j.val + 64) 8 = 0 ∧
      readBuffer s0 (C_ROW + 184 * j.val + 112) 8 = 0) :
    ∃ s3,
      DetRun oracle (submission.image .commit) s0 201334800 s3 671096848 67108864 ∧
      s3.pc = BitVec.ofNat 64 (0x1000 + 4 * 180278) ∧
      s3.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s3.getReg .x5 = 0#64 ∧
      s3.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s3.getReg .x11 = 96#64 ∧
      s3.getReg .x13 = 0#64 ∧
      s3.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ idx < LENGTH,
        readBuffer s3 (C_TD + 32 * idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg (pairSalts rand) 0 idx) ∧
      (∀ i : Index, readBuffer s3 (C_TD + saltOff i) 24 = pairSalts rand i) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        ((C_TD + levelBase 1 ≤ q ∧ q < C_ROW) ∨ C_TD + trapdoorBytes ≤ q) →
        s3.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_ROW : C_ROW = 5905584160 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hlb1 : levelBase 1 = 536870912 := by decide
  have htd := trapdoorBytes_eq
  have hro := rowOff_eq
  obtain ⟨s1, hr1A, hpc1, hx2_1, hx5_1, _, hx9_1, hx10_1, hx11_1, hx12_1, hx13_1,
    hx18_1, hx19_1, hx26_1, h1A, hp1A⟩ :=
    commit_phase1A h768 oracle msg s0 hpc hx2 hx5 hx8 hx9 hx10 hx11 hx13 hx18 hx19 hx26 hmsg0
  obtain ⟨s2, hr1B, hpc2, hx2_2, hx5_2, hx9_2, hx10_2, hx11_2, hx12_2, hx13_2,
    _, hx19_2, hx26_2, h1B, hp1B⟩ :=
    commit_phase1B h768 oracle msg s1 hpc1 hx2_1 hx5_1 hx9_1 hx10_1 hx11_1 hx12_1 hx13_1
      hx18_1 hx19_1 hx26_1 h1A
  have hrow2 : ∀ p : Fin (LENGTH / 2),
      readBuffer s2 (C_ROW + 184 * p.val) 32 =
        leafA (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val, by omega⟩) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 32) 32 =
        leafB (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val, by omega⟩) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 64) 8 = 0 ∧
      readBuffer s2 (C_ROW + 184 * p.val + 72) 24 = pairSaltEven (rand p) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 88) 24 = pairSaltOdd (rand p) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 112) 8 = 0 ∧
      readBuffer s2 (C_ROW + 184 * p.val + 120) 32 =
        leafA (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val + 1, by omega⟩) ∧
      readBuffer s2 (C_ROW + 184 * p.val + 152) 32 =
        leafB (fun x => oracle.compression (x.cast h768.symm)) (msg ⟨2 * p.val + 1, by omega⟩) := by
    intro p; have hp := p.isLt
    obtain ⟨ha0, hb0, ha1, hb1⟩ := h1B p
    have hmid_pres : ∀ off n, 64 ≤ off → off + n ≤ 120 →
        readBuffer s2 (C_ROW + 184 * p.val + off) n = readBuffer s0 (C_ROW + 184 * p.val + off) n := by
      intro off n hlo hhi
      apply readBuffer_congr; intro j hj
      have h1 := hp1B (C_ROW + 184 * p.val + off + j) (by omega) (fun p' _ => by
        by_cases heq : p' = p.val
        · subst heq; omega
        · omega)
      have h0 := hp1A (C_ROW + 184 * p.val + off + j) (by omega) (by omega)
      exact h1.trans h0
    exact ⟨ha0, hb0,
      (hmid_pres 64 8 (by omega) (by omega)).trans (hgap0 p).1,
      (hmid_pres 72 24 (by omega) (by omega)).trans (hsalt0 p).1,
      (hmid_pres 88 24 (by omega) (by omega)).trans (hsalt0 p).2,
      (hmid_pres 112 8 (by omega) (by omega)).trans (hgap0 p).2,
      ha1, hb1⟩
  obtain ⟨s3, hr1C, hpc3, hx2_3, hx5_3, hx9_3, hx11_3, hx13_3, hx26_3, hl0_3, hp1C⟩ :=
    commit_phase1C h768 oracle msg rand s2 hpc2 hx2_2 hx5_2 hx9_2 hx10_2 hx11_2 hx12_2 hx13_2
      hx19_2 hx26_2 hrow2
  refine ⟨s3, by simpa using (hr1A.trans hr1B).trans hr1C,
    hpc3, hx2_3, hx5_3, hx9_3, hx11_3, hx13_3, hx26_3, hl0_3, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    let p : Fin (LENGTH / 2) := ⟨i.val / 2, by omega⟩
    by_cases hev : i.val % 2 = 0
    · have hso : C_TD + saltOff i = C_ROW + 184 * p.val + 72 := by
        unfold saltOff PAIR_STRIDE; simp only [hev, ite_true, p]; omega
      have hps : pairSalts rand i = pairSaltEven (rand p) := by
        unfold pairSalts; simp only [hev, ite_true]; rfl
      rw [hso, hps, hp1C.readBuffer_eq (by omega) (by omega)]
      exact (hrow2 p).2.2.2.1
    · have hso : C_TD + saltOff i = C_ROW + 184 * p.val + 88 := by
        unfold saltOff PAIR_STRIDE; simp only [hev, ite_false, p]; omega
      have hps : pairSalts rand i = pairSaltOdd (rand p) := by
        unfold pairSalts; simp only [hev, ite_false]; rfl
      rw [hso, hps, hp1C.readBuffer_eq (by omega) (by omega)]
      exact (hrow2 p).2.2.2.2.1
  · intro q hq hreg
    have h3 := hp1C q hq (by omega)
    have h2 := hp1B q hq (fun p hp => by omega)
    have h1 := hp1A q hq (by omega)
    exact (h3.trans h2).trans h1

end CommitGolfCandidate.R4
