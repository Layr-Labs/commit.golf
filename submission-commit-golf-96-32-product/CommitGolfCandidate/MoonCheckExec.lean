import CommitGolfCandidate.MoonCheckCapPair

/-! Symbolic execution of cap-level composition, full bottom-up cap walk, and epilogue (`pc[243..332]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem pc_286_branch : pcWord 286 + signExtend13 92#13 = pcWord 309 := by decide
private theorem pc_290_branch : pcWord 290 + signExtend13 76#13 = pcWord 309 := by decide
private theorem pc_310_branch : pcWord 310 + signExtend13 7932#13 = pcWord 245 := by decide
private theorem pc_311_branch : pcWord 311 + signExtend13 76#13 = pcWord 330 := by decide
private theorem pc_312_branch : pcWord 312 + signExtend13 72#13 = pcWord 330 := by decide

private def capOddAddrInstrs : List Instr :=
  [.SLLI .x6 .x22 6#6, .SLLI .x7 .x22 5#6, .ADD .x10 .x6 .x7, .ADD .x10 .x16 .x10,
   .SRLI .x6 .x22 1#6, .ADD .x6 .x22 .x6, .SLLI .x6 .x6 5#6, .ADD .x12 .x17 .x6]

/-- Complete cap-level step `l = 15 + step` (`step < 9`, `pc[245..310]`). -/
theorem step_cap_level (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (sPos : MachineState) (step : Nat) (hstep : step < 9)
    (s : MachineState) (trPrev : CompressionReplies)
    (hinv : CapWalkInv h768 oracle input sPos step s trPrev) :
    let l := 15 + step
    let pBase := posRecordOff input.positions input.positions.card
    let tBase := posTailOff input.positions input.positions.card
    PhaseOutcome oracle s (37 + 225 * (levelSize l / 2)) input.positions.card
      (input.proof.length <
        pBase + 29 * capFrontierPrefix input.positions (step + 1) +
        tailBytes (tBase + capFrontierPrefix input.positions (step + 1)))
      (fun s' calls tr =>
        calls ≤ input.positions.card ∧
        CapWalkInv h768 oracle input sPos (step + 1) s' (trPrev ++ tr)) := by
  intro l pBase tBase
  have hl1 : 15 ≤ l := by omega
  have hl2 : l < 24 := by omega
  have hplen_bd : input.proof.length ≤ 8556390424 := hvalid
  have hpc_s : s.pc = pcWord 245 := by have := hinv.pc; rwa [if_neg (by omega : step ≠ 9)] at this
  have hls_le : levelSize l ≤ 342 := levelSize_cap_le342 l hl1 hl2
  have hpairs_pos : 0 < levelSize l / 2 := levelSize_cap_pairs_pos l hl1 hl2
  have hmo_l_bd := capMarkOff_lt_4824 l hl1 (by omega)
  have hmo_n_bd := capMarkOff_lt_4824 (l + 1) (by omega) (by omega)
  have hvo_l_bd := capValOff_lt_33152 l hl1 (by omega)
  have hvo_n_bd := capValOff_lt_33152 (l + 1) (by omega) (by omega)
  have hvo_step := capValOff_step_eq l hl1 hl2
  have hvo_l_al := capValOff_mod8 l hl1 (by omega)
  have hvo_n_al := capValOff_mod8 (l + 1) (by omega) (by omega)
  have hmo_step := capMarkOff_step_le l hl1 hl2
  -- pc[245..255]: load level table fields (11 steps)
  let s0 := submission.initialState .check input
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hmem_data : ∀ (off : Nat) (hoff : off + 8 ≤ 800), off % 8 = 0 →
      s.getMem (BitVec.ofNat 64 (68719475936 + off)) =
        packedDword MoonArtifact.openingData off hoff := by
    intro off hoff hal
    rw [hinv.high.getMem_eq (by omega) (by omega) (by omega)]
    exact check_initial_data_dword input hvalid off hoff
  -- pc[245]: LD x20, 8(x29)
  have ha245 : s.getReg .x29 + signExtend12 8#12 = BitVec.ofNat 64 (68719475936 + (32 * l + 8)) := by
    rw [hinv.x29, se12_8]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 8 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv245 : memoryArgumentsValid s (.LD .x20 .x29 8#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha245]
    exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst245 := step_ordinary oracle s 245 (.LD .x20 .x29 8#12) (by decide) hpc_s rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv245])
  let s1 := execInstrBr s (.LD .x20 .x29 8#12)
  have hpc1 : s1.pc = pcWord 246 := by simp only [s1, execInstrBr, MachineState.setPC, hpc_s, pcWord_add_four]
  have hx20_1 : s1.getReg .x20 = BitVec.ofNat 64 (levelSize l) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, ha245]
    rw [MachineState.getReg_setReg_eq (by decide), hmem_data (32 * l + 8) (by omega) (by omega)]
    exact openingData_dword_1 ⟨l, by omega⟩
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  -- pc[246..247]: LD x14, 16(x29); ADD x14, x18, x14
  have hx29_1 : s1.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x29), hinv.x29]
  have ha246 : s1.getReg .x29 + signExtend12 16#12 = BitVec.ofNat 64 (68719475936 + (32 * l + 16)) := by
    rw [hx29_1, se12_16]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 16 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv246 : memoryArgumentsValid s1 (.LD .x14 .x29 16#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha246]
    exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst246 := step_ordinary oracle s1 246 (.LD .x14 .x29 16#12) (by decide) hpc1 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv246])
  let s2 := execInstrBr s1 (.LD .x14 .x29 16#12)
  have hpc2 : s2.pc = pcWord 247 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hst247 := step_ordinary oracle s2 247 (.ADD .x14 .x18 .x14) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.ADD .x14 .x18 .x14)
  have hpc3 : s3.pc = pcWord 248 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hmem3 : s3.mem = s.mem := by simpa [s3, s2, execInstrBr, mem_setPC, mem_setReg] using hmem1
  have hx14_3 : s3.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) := by
    have h14_2 : s2.getReg .x14 = BitVec.ofNat 64 (capMarkOff l) := by
      simp only [s2, execInstrBr, MachineState.getReg_setPC, ha246]
      rw [MachineState.getReg_setReg_eq (by decide)]
      have hm : s1.getMem (BitVec.ofNat 64 (68719475936 + (32 * l + 16))) =
          s.getMem (BitVec.ofNat 64 (68719475936 + (32 * l + 16))) := by simp [MachineState.getMem, hmem1]
      rw [hm, hmem_data (32 * l + 16) (by omega) (by omega)]
      exact openingData_dword_2 ⟨l, by omega⟩
    have h18_2 : s2.getReg .x18 = 4096#64 := by
      simp only [s2, s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        ne_eq, not_false_eq_true, reduceCtorEq, hinv.fixed.x18]
    simp only [s3, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), h18_2, h14_2]
    change BitVec.ofNat 64 4096 + _ = _; exact bv64_add 4096 _
  -- pc[248..249]: LD x15, 48(x29); ADD x15, x18, x15
  have hx29_3 : s3.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    simp only [s3, s2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, hx29_1]
  have ha248 : s3.getReg .x29 + signExtend12 48#12 = BitVec.ofNat 64 (68719475936 + (32 * (l + 1) + 16)) := by
    rw [hx29_3, se12_48]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 48 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv248 : memoryArgumentsValid s3 (.LD .x15 .x29 48#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha248]
    exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst248 := step_ordinary oracle s3 248 (.LD .x15 .x29 48#12) (by decide) hpc3 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv248])
  let s4 := execInstrBr s3 (.LD .x15 .x29 48#12)
  have hpc4 : s4.pc = pcWord 249 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hst249 := step_ordinary oracle s4 249 (.ADD .x15 .x18 .x15) (by decide) hpc4 rfl (by intro h; cases h) rfl
  let s5 := execInstrBr s4 (.ADD .x15 .x18 .x15)
  have hpc5 : s5.pc = pcWord 250 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem5 : s5.mem = s.mem := by simpa [s5, s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
  have hx15_5 : s5.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) := by
    have h15_4 : s4.getReg .x15 = BitVec.ofNat 64 (capMarkOff (l + 1)) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC, ha248]
      rw [MachineState.getReg_setReg_eq (by decide)]
      have hm : s3.getMem (BitVec.ofNat 64 (68719475936 + (32 * (l + 1) + 16))) =
          s.getMem (BitVec.ofNat 64 (68719475936 + (32 * (l + 1) + 16))) := by simp [MachineState.getMem, hmem3]
      rw [hm, hmem_data (32 * (l + 1) + 16) (by omega) (by omega)]
      exact openingData_dword_2 ⟨l + 1, by omega⟩
    have h18_4 : s4.getReg .x18 = 4096#64 := by
      simp only [s4, s3, s2, s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        ne_eq, not_false_eq_true, reduceCtorEq, hinv.fixed.x18]
    simp only [s5, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), h18_4, h15_4]
    change BitVec.ofNat 64 4096 + _ = _; exact bv64_add 4096 _
  -- pc[250..251]: LD x16, 24(x29); ADD x16, x19, x16
  have hx29_5 : s5.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    simp only [s5, s4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, hx29_3]
  have ha250 : s5.getReg .x29 + signExtend12 24#12 = BitVec.ofNat 64 (68719475936 + (32 * l + 24)) := by
    rw [hx29_5, se12_24]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 24 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv250 : memoryArgumentsValid s5 (.LD .x16 .x29 24#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha250]
    exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst250 := step_ordinary oracle s5 250 (.LD .x16 .x29 24#12) (by decide) hpc5 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv250])
  let s6 := execInstrBr s5 (.LD .x16 .x29 24#12)
  have hpc6 : s6.pc = pcWord 251 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
  have hst251 := step_ordinary oracle s6 251 (.ADD .x16 .x19 .x16) (by decide) hpc6 rfl (by intro h; cases h) rfl
  let s7 := execInstrBr s6 (.ADD .x16 .x19 .x16)
  have hpc7 : s7.pc = pcWord 252 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
  have hmem7 : s7.mem = s.mem := by simpa [s7, s6, execInstrBr, mem_setPC, mem_setReg] using hmem5
  have hx16_7 : s7.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) := by
    have h16_6 : s6.getReg .x16 = BitVec.ofNat 64 (capValOff l) := by
      simp only [s6, execInstrBr, MachineState.getReg_setPC, ha250]
      rw [MachineState.getReg_setReg_eq (by decide)]
      have hm : s5.getMem (BitVec.ofNat 64 (68719475936 + (32 * l + 24))) =
          s.getMem (BitVec.ofNat 64 (68719475936 + (32 * l + 24))) := by simp [MachineState.getMem, hmem5]
      rw [hm, hmem_data (32 * l + 24) (by omega) (by omega)]
      exact openingData_dword_3 ⟨l, by omega⟩
    have h19_6 : s6.getReg .x19 = 8192#64 := by
      simp only [s6, s5, s4, s3, s2, s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        ne_eq, not_false_eq_true, reduceCtorEq, hinv.fixed.x19]
    simp only [s7, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), h19_6, h16_6]
    change BitVec.ofNat 64 8192 + _ = _; exact bv64_add 8192 _
  -- pc[252..255]: LD x17, 56(x29); ADD x17, x19, x17; SRLI x22, x20, 1; ADDI x23, x0, 0
  have hx29_7 : s7.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    simp only [s7, s6, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, hx29_5]
  have ha252 : s7.getReg .x29 + signExtend12 56#12 = BitVec.ofNat 64 (68719475936 + (32 * (l + 1) + 24)) := by
    rw [hx29_7, se12_56]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 56 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv252 : memoryArgumentsValid s7 (.LD .x17 .x29 56#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha252]
    exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst252 := step_ordinary oracle s7 252 (.LD .x17 .x29 56#12) (by decide) hpc7 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv252])
  let s8 := execInstrBr s7 (.LD .x17 .x29 56#12)
  have hpc8 : s8.pc = pcWord 253 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
  have hst253 := step_ordinary oracle s8 253 (.ADD .x17 .x19 .x17) (by decide) hpc8 rfl (by intro h; cases h) rfl
  let s9 := execInstrBr s8 (.ADD .x17 .x19 .x17)
  have hpc9 : s9.pc = pcWord 254 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
  have hst254 := step_ordinary oracle s9 254 (.SRLI .x22 .x20 1#6) (by decide) hpc9 rfl (by intro h; cases h) rfl
  let s10 := execInstrBr s9 (.SRLI .x22 .x20 1#6)
  have hpc10 : s10.pc = pcWord 255 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9, pcWord_add_four]
  have hst255 := step_ordinary oracle s10 255 (.ADDI .x23 .x0 0#12) (by decide) hpc10 rfl (by intro h; cases h) rfl
  let s11 := execInstrBr s10 (.ADDI .x23 .x0 0#12)
  have hpc11 : s11.pc = pcWord 256 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10, pcWord_add_four]
  have hmem11 : s11.mem = s.mem := by
    simpa [s11, s10, s9, s8, execInstrBr, mem_setPC, mem_setReg] using hmem7
  have hs_hdr : StepsTo oracle s s11 11 0 [] := by
    simpa using (((hst245.trans (hst246.trans hst247)).trans (hst248.trans hst249)).trans
      (hst250.trans hst251)).trans ((hst252.trans hst253).trans (hst254.trans hst255))
  have hreg11 : ∀ r, r ≠ .x20 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x22 → r ≠ .x23 →
      s11.getReg r = s.getReg r := fun r h20r h14r h15r h16r h17r h22r h23r => by
    simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h23r.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h22r.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h17r.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h17r.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h16r.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h16r.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h15r.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h15r.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h14r.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h14r.symm, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ h20r.symm]
  have hx20_11 : s11.getReg .x20 = BitVec.ofNat 64 (levelSize l) := by
    simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx20_1]
  have hx14_11 : s11.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) := by
    simp only [s11, s10, s9, s8, s7, s6, s5, s4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx14_3]
  have hx15_11 : s11.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) := by
    simp only [s11, s10, s9, s8, s7, s6, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx15_5]
  have hx16_11 : s11.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) := by
    simp only [s11, s10, s9, s8, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx16_7]
  have hx17_11 : s11.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) := by
    have h17_8 : s8.getReg .x17 = BitVec.ofNat 64 (capValOff (l + 1)) := by
      simp only [s8, execInstrBr, MachineState.getReg_setPC, ha252]
      rw [MachineState.getReg_setReg_eq (by decide)]
      have hm : s7.getMem (BitVec.ofNat 64 (68719475936 + (32 * (l + 1) + 24))) =
          s.getMem (BitVec.ofNat 64 (68719475936 + (32 * (l + 1) + 24))) := by simp [MachineState.getMem, hmem7]
      rw [hm, hmem_data (32 * (l + 1) + 24) (by omega) (by omega)]
      exact openingData_dword_3 ⟨l + 1, by omega⟩
    have h19_8 : s8.getReg .x19 = 8192#64 := by
      simp only [s8, s7, s6, s5, s4, s3, s2, s1, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hinv.fixed.x19]
    have h17_9 : s9.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) := by
      simp only [s9, execInstrBr, MachineState.getReg_setPC]
      rw [MachineState.getReg_setReg_eq (by decide), h19_8, h17_8]
      change BitVec.ofNat 64 8192 + _ = _; exact bv64_add 8192 _
    simp only [s11, s10, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, h17_9]
  have hx22_11 : s11.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) := by
    have h20_9 : s9.getReg .x20 = BitVec.ofNat 64 (levelSize l) := by
      simp only [s9, s8, s7, s6, s5, s4, s3, s2, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx20_1]
    simp only [s11, s10, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, h20_9,
      show (1#6 : BitVec 6).toNat = 1 by decide]
    rw [bv64_shr _ 1 (by omega), Nat.pow_one]
  have hx23_11 : s11.getReg .x23 = BitVec.ofNat 64 0 := by
    simp only [s11, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      ne_eq, not_false_eq_true, reduceCtorEq, getReg_x0]; decide
  -- Pair loop induction over n ≤ levelSize l / 2
  let pLvl := pBase + 29 * capFrontierPrefix input.positions step
  let tLvl := tBase + capFrontierPrefix input.positions step
  have hpair_loop : ∀ n ≤ levelSize l / 2,
      PhaseOutcome oracle s11 (225 * n) (pairMarkedNextCount input.positions l n)
        (input.proof.length <
          pLvl + 29 * pairFrontierCount input.positions l n +
          tailBytes (tLvl + pairFrontierCount input.positions l n))
        (fun sn calls tr =>
          calls ≤ pairMarkedNextCount input.positions l n ∧
          sn.pc = (if n = levelSize l / 2 then pcWord 285 else pcWord 256) ∧
          CheckFixedRegs sn ∧
          ProofCursor s0 input.proof.length
            (pLvl + 29 * pairFrontierCount input.positions l n)
            (tLvl + pairFrontierCount input.positions l n) sn ∧
          HighMemPreserved s0 sn ∧
          sn.getReg .x20 = BitVec.ofNat 64 (levelSize l) ∧
          sn.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
          sn.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
          sn.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) ∧
          sn.getReg .x17 = BitVec.ofNat 64 (8192 + capValOff (l + 1)) ∧
          sn.getReg .x22 = BitVec.ofNat 64 (levelSize l / 2) ∧
          sn.getReg .x23 = BitVec.ofNat 64 n ∧
          sn.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) ∧
          sn.getReg .x30 = BitVec.ofNat 64 (68719475936 + 768) ∧
          (∀ idx < levelSize l, sn.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + idx)) =
            if capMark input.positions l idx then 1#8 else 0#8) ∧
          (∀ q < n, sn.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) =
            if capMark input.positions (l + 1) q then 1#8 else 0#8) ∧
          (∀ a, 4096 + capMarkOff (l + 1) + n ≤ a → a < 4824 → sn.getByte (BitVec.ofNat 64 a) = 0#8) ∧
          (∀ q, n ≤ q → q < levelSize l / 2 →
            ∀ b < 32, sn.getByte (BitVec.ofNat 64 (8192 + capValOff l + 96 * q + 64 + b)) = 0#8) ∧
          (∀ a : Nat, a < 2 ^ 64 →
            (a < 4096 + capMarkOff (l + 1) ∨ 4096 + capMarkOff (l + 1) + n ≤ a) →
            (∀ q < n, ∀ idx, (idx = 2 * q ∨ idx = 2 * q + 1) → capMark input.positions l idx = false →
              a < 8192 + capValOff l + gapOffset idx ∨ 8192 + capValOff l + gapOffset idx + 32 ≤ a) →
            (∀ q < n, capMark input.positions (l + 1) q = true →
              a < 8192 + capValOff (l + 1) + gapOffset q ∨ 8192 + capValOff (l + 1) + gapOffset q + 32 ≤ a) →
            sn.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) ∧
          (∀ q < n, capMark input.positions (l + 1) q = true →
            let dL := readBuffer sn (8192 + capValOff l + gapOffset (2 * q)) 32
            let dR := readBuffer sn (8192 + capValOff l + gapOffset (2 * q + 1)) 32
            let pAt := pLvl + 29 * pairFrontierCount input.positions l q
            let tAt := tLvl + pairFrontierCount input.positions l q
            readBuffer sn (8192 + capValOff (l + 1) + gapOffset q) 32 =
              (if l = 23 then c96 (binaryInput dL dR) else mask238 (c96 (binaryInput dL dR))) ∧
            InTrace h768 oracle tr (binaryInput dL dR) ∧
            (capMark input.positions l (2 * q) = false → dL = proofDigest238 s0 input.proof.length (11341403200 + pAt) tAt) ∧
            (capMark input.positions l (2 * q + 1) = false → dR = proofDigest238 s0 input.proof.length (11341403200 + pAt) tAt))) := by
    intro n hn
    induction n with
    | zero =>
      refine .continued s11 0 0 [] (Nat.zero_le _) (Nat.zero_le _) (StepsTo.refl oracle s11) ?_
      refine ⟨Nat.zero_le _,
        by simp [Nat.ne_of_lt hpairs_pos, hpc11],
        hinv.fixed.of_agree (fun r hr => hreg11 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
          (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
        by simpa [pairFrontierCount_zero, pLvl, tLvl] using
          hinv.cursor.of_agree (fun r hr => hreg11 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
            (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
            (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
        hinv.high.trans (MemEqOutside.of_mem_eq hmem11 0 4294971392),
        hx20_11, hx14_11, hx15_11, hx16_11, hx17_11, hx22_11, hx23_11,
        (hreg11 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hinv.x29,
        (hreg11 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hinv.x30,
        fun idx hidx => by simp [MachineState.getByte, MachineState.getMem, hmem11]; exact hinv.mark_cur hstep idx hidx,
        fun _ h => (Nat.not_lt_zero _ h).elim,
        fun a ha1 ha2 => by simp [MachineState.getByte, MachineState.getMem, hmem11]; exact hinv.mark_hi_zero hstep a (by omega) ha2,
        fun q _ hq b hb => by simp [MachineState.getByte, MachineState.getMem, hmem11]; exact hinv.val_cur_gap_zero hstep q hq b hb,
        fun a _ _ _ _ => by simp [MachineState.getByte, MachineState.getMem, hmem11],
        fun _ h => (Nat.not_lt_zero _ h).elim⟩
    | succ q ih =>
      have hq_lt : q < levelSize l / 2 := by omega
      have hcm_succ : capMark input.positions (l + 1) q =
          (capMark input.positions l (2 * q) || capMark input.positions l (2 * q + 1)) := by
        rw [capMark_succ input.positions l q hl1, if_pos (by omega)]
      have hrej_mono : input.proof.length <
            pLvl + 29 * pairFrontierCount input.positions l q +
            tailBytes (tLvl + pairFrontierCount input.positions l q) →
          input.proof.length <
            pLvl + 29 * pairFrontierCount input.positions l (q + 1) +
            tailBytes (tLvl + pairFrontierCount input.positions l (q + 1)) := by
        have hfm := pairFrontierCount_mono input.positions l (show q ≤ q + 1 by omega)
        have htm := tailBytes_mono (show tLvl + pairFrontierCount input.positions l q ≤
          tLvl + pairFrontierCount input.positions l (q + 1) by omega)
        omega
      rw [show 225 * (q + 1) = 225 * q + 225 by omega, pairMarkedNextCount_succ]
      refine (ih (by omega)).bind_dep hrej_mono (fun sq calls1 tr1 ⟨hcalls1, hpc1, hfix1, hcur1, hhigh1,
          h20, h14, h15, h16, h17, h22, h23, h29, h30, hmkL, hmkN, hmkHi, hremG, hpres1, hdone1⟩ => by
        have hpc_q : sq.pc = pcWord 256 := by rwa [if_neg (by omega : q ≠ levelSize l / 2)] at hpc1
        let pCur := pLvl + 29 * pairFrontierCount input.positions l q
        let tCur := tLvl + pairFrontierCount input.positions l q
        have hp_pair := step_cap_pair h768 oracle input hvalid l q pCur tCur hl1 hl2 hq_lt
          sq hpc_q hfix1 hcur1 hhigh1 h20 h14 h15 h16 h17 h22 h23 h29 h30
          (hmkL (2 * q) (by omega)) (hmkL (2 * q + 1) (by omega))
          (hmkHi (4096 + capMarkOff (l + 1) + q) (by omega) (by have := levelSize_step l (by omega); omega))
          (hremG q (le_refl q) hq_lt)
        have hcan_q : ((capMark input.positions l (2 * q) != capMark input.positions l (2 * q + 1)) = true ∧
            input.proof.length < pCur + 29 + tailBytes (tCur + 1)) →
            input.proof.length <
              pLvl + 29 * pairFrontierCount input.positions l (q + 1) +
              tailBytes (tLvl + pairFrontierCount input.positions l (q + 1)) := by
          rintro ⟨hbne, hlt⟩
          dsimp only [pCur, tCur] at hlt
          rw [pairFrontierCount_succ, if_pos hbne]
          simpa only [Nat.mul_add, Nat.add_assoc] using hlt
        have hpNext_eq : pCur + (if (capMark input.positions l (2 * q) != capMark input.positions l (2 * q + 1)) then 29 else 0) =
            pLvl + 29 * pairFrontierCount input.positions l (q + 1) := by
          dsimp only [pCur]
          rw [pairFrontierCount_succ]; split <;> omega
        have htNext_eq : tCur + (if (capMark input.positions l (2 * q) != capMark input.positions l (2 * q + 1)) then 1 else 0) =
            tLvl + pairFrontierCount input.positions l (q + 1) := by
          dsimp only [tCur]
          rw [pairFrontierCount_succ]; split <;> omega
        refine hp_pair.weaken (le_refl _) (by rw [hcm_succ]) hcan_q ?_
        rintro sq1 calls2 tr2 ⟨hcalls2, hpc2, hfix2, hcur2, h20_2, h14_2, h15_2, h16_2, h17_2, h22_2, h23_2,
          h29_2, h30_2, hmk_q, hval_q, hmeq_00, hout_q⟩
        rw [hpNext_eq, htNext_eq] at hcur2
        have hhigh2 : HighMemPreserved s0 sq1 := by
          intro a ha hge
          have hu_le : (if !capMark input.positions l (2 * q) then 2 * q else 2 * q + 1) ≤ 2 * q + 1 := by
            split <;> omega
          have hq_go : gapOffset (if !capMark input.positions l (2 * q) then 2 * q else 2 * q + 1) + 32 ≤ 96 * q + 64 := by
            unfold gapOffset; omega
          have hq_next : gapOffset q + 32 ≤ 96 * q + 64 := by unfold gapOffset; omega
          have : sq1.getByte (BitVec.ofNat 64 a) = sq.getByte (BitVec.ofNat 64 a) :=
            hout_q a ha (by omega) (Or.inr (Or.inr (by omega))) (Or.inr (by omega))
          exact this.trans (hhigh1 a ha hge)
        have hpres_step : ∀ a : Nat, a < 2 ^ 64 →
            a ≠ 4096 + capMarkOff (l + 1) + q →
            (∀ idx, (idx = 2 * q ∨ idx = 2 * q + 1) → capMark input.positions l idx = false →
              a < 8192 + capValOff l + gapOffset idx ∨ 8192 + capValOff l + gapOffset idx + 32 ≤ a) →
            (capMark input.positions (l + 1) q = true →
              a < 8192 + capValOff (l + 1) + gapOffset q ∨ 8192 + capValOff (l + 1) + gapOffset q + 32 ≤ a) →
            sq1.getByte (BitVec.ofNat 64 a) = sq.getByte (BitVec.ofNat 64 a) := fun a ha hne hunm_d hdst_d => by
          by_cases h00 : capMark input.positions l (2 * q) = false ∧ capMark input.positions l (2 * q + 1) = false
          · simp [MachineState.getByte, MachineState.getMem, hmeq_00 h00.1 h00.2]
          · have hcm_t : capMark input.positions (l + 1) q = true := by
              rw [hcm_succ]
              cases h1 : capMark input.positions l (2 * q) <;>
                cases h2 : capMark input.positions l (2 * q + 1) <;>
                  first | rfl | exact (h00 ⟨h1, h2⟩).elim
            refine hout_q a ha hne ?_ (hdst_d hcm_t)
            by_cases heq : capMark input.positions l (2 * q) = capMark input.positions l (2 * q + 1)
            · exact Or.inl heq
            · right
              cases h1 : capMark input.positions l (2 * q) with
              | false => simpa [h1] using hunm_d (2 * q) (Or.inl rfl) h1
              | true =>
                have h2 : capMark input.positions l (2 * q + 1) = false := by
                  cases h2' : capMark input.positions l (2 * q + 1)
                  · rfl
                  · exfalso; apply heq; rw [h1, h2']
                simpa [h1] using hunm_d (2 * q + 1) (Or.inr rfl) h2
        refine ⟨by rw [← hcm_succ] at hcalls2; omega,
          hpc2, hfix2, hcur2, hhigh2, h20_2, h14_2, h15_2, h16_2, h17_2, h22_2, h23_2, h29_2, h30_2,
          ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro idx hidx
          exact (hpres_step _ (by omega) (by omega) (fun _ _ _ => Or.inl (by unfold gapOffset; omega))
            (fun _ => Or.inl (by unfold gapOffset; omega))).trans (hmkL idx hidx)
        · intro q' hq'
          by_cases hlt : q' < q
          · exact (hpres_step _ (by omega) (by omega) (fun _ _ _ => Or.inl (by unfold gapOffset; omega))
              (fun _ => Or.inl (by unfold gapOffset; omega))).trans (hmkN q' hlt)
          · have : q' = q := by omega
            subst this; rwa [hcm_succ]
        · intro a ha1 ha2
          exact (hpres_step a (by omega) (by omega) (fun _ _ _ => Or.inl (by unfold gapOffset; omega))
            (fun _ => Or.inl (by unfold gapOffset; omega))).trans (hmkHi a (by omega) ha2)
        · intro q' hq'1 hq'2 b hb
          have hdisj_g : ∀ idx, (idx = 2 * q ∨ idx = 2 * q + 1) →
              8192 + capValOff l + 96 * q' + 64 + b < 8192 + capValOff l + gapOffset idx ∨
                8192 + capValOff l + gapOffset idx + 32 ≤ 8192 + capValOff l + 96 * q' + 64 + b := by
            intro idx hidx
            rcases hidx with rfl | rfl
            · rw [gapOffset_even]; omega
            · rw [gapOffset_odd]; omega
          exact (hpres_step _ (by omega) (by omega) (fun idx hi _ => hdisj_g idx hi)
            (fun _ => Or.inl (by unfold gapOffset; omega))).trans (hremG q' (by omega) hq'2 b hb)
        · intro a ha hmk_out hunm_out hdst_out
          have h1 := hpres_step a ha (by omega)
            (fun idx hi hm => hunm_out q (by omega) idx hi hm)
            (fun hcm => hdst_out q (by omega) hcm)
          have h2 := hpres1 a ha (by omega)
            (fun q' hq' idx hi hm => hunm_out q' (by omega) idx hi hm)
            (fun q' hq' hcm => hdst_out q' (by omega) hcm)
          exact h1.trans h2
        · intro q' hq' hcm'
          by_cases hlt : q' < q
          · obtain ⟨hv, htr, hfrL, hfrR⟩ := hdone1 q' hlt hcm'
            have hpres_slot : ∀ idx, (idx = 2 * q' ∨ idx = 2 * q' + 1) →
                readBuffer sq1 (8192 + capValOff l + gapOffset idx) 32 =
                readBuffer sq (8192 + capValOff l + gapOffset idx) 32 := fun idx hi => by
              apply readBuffer_congr2; intro b hb
              refine hpres_step _ (by unfold gapOffset; omega) (by unfold gapOffset; omega) ?_
                (fun _ => Or.inl (by rcases hi with rfl | rfl <;> [rw [gapOffset_even]; rw [gapOffset_odd]] <;> unfold gapOffset <;> omega))
              intro idx2 hi2 _
              have := gapOffset_disjoint (show idx ≠ idx2 by omega); omega
            have hpres_dst : readBuffer sq1 (8192 + capValOff (l + 1) + gapOffset q') 32 =
                readBuffer sq (8192 + capValOff (l + 1) + gapOffset q') 32 := by
              apply readBuffer_congr2; intro b hb
              refine hpres_step _ (by unfold gapOffset; omega) (by unfold gapOffset; omega)
                (fun idx2 hi2 _ => Or.inr (by rcases hi2 with rfl | rfl <;> [rw [gapOffset_even]; rw [gapOffset_odd]] <;> omega))
                (fun _ => by have := gapOffset_disjoint (show q' ≠ q by omega); omega)
            rw [hpres_slot (2 * q') (Or.inl rfl), hpres_slot (2 * q' + 1) (Or.inr rfl), hpres_dst]
            exact ⟨hv, htr.append_left, hfrL, hfrR⟩
          · have : q' = q := by omega
            subst this
            rw [hcm_succ] at hcm'
            obtain ⟨hv, htr, hfrL, hfrR⟩ := hval_q hcm'
            exact ⟨hv, htr.append_right, hfrL, hfrR⟩)
  -- Now chain header (11 steps) + pair loop (225 * pairs) + odd tail (≤ 24) + loop end (2)
  have hpairs_res := hpair_loop (levelSize l / 2) (le_refl _)
  have hpoff_next : pLvl + 29 * pairFrontierCount input.positions l (levelSize l / 2) =
      pBase + 29 * capFrontierPrefix input.positions (step + 1) := by
    dsimp only [pLvl, l]
    rw [pairFrontierCount_full, capFrontierPrefix_succ]; omega
  have htoff_next : tLvl + pairFrontierCount input.positions l (levelSize l / 2) =
      tBase + capFrontierPrefix input.positions (step + 1) := by
    dsimp only [tLvl, l]
    rw [pairFrontierCount_full, capFrontierPrefix_succ]; omega
  have hcan_lvl : input.proof.length <
        pLvl + 29 * pairFrontierCount input.positions l (levelSize l / 2) +
        tailBytes (tLvl + pairFrontierCount input.positions l (levelSize l / 2)) →
      input.proof.length <
        pBase + 29 * capFrontierPrefix input.positions (step + 1) +
        tailBytes (tBase + capFrontierPrefix input.positions (step + 1)) := by
    rw [hpoff_next, htoff_next]; exact id
  refine PhaseOutcome.weaken
    (K1 := 11 + (225 * (levelSize l / 2) + 26))
    (Q1 := pairMarkedNextCount input.positions l (levelSize l / 2) + 0)
    ?_ (by omega) (by have := pairMarkedNextCount_le_card input.positions l hl1; omega) id (fun _ _ _ h => h)
  refine hs_hdr.prepend_pure ?_
  refine hpairs_res.bind_dep hcan_lvl (fun sP qP trP ⟨hqP, hpcP, hfixP, hcurP, hhighP,
          h20, h14, h15, h16, h17, h22, h23, h29, h30, hmkL, hmkN, hmkHi, _, hpresP, hdoneP⟩ => by
        rw [if_pos rfl] at hpcP
        rw [hpoff_next, htoff_next] at hcurP
        -- Odd tail pc[285..308] -> pc[309] (≤ 24 steps, 0 calls)
        let pairs := levelSize l / 2
        have hodd_tail : ∃ s309 kOdd, kOdd ≤ 24 ∧ StepsTo oracle sP s309 kOdd 0 [] ∧
            s309.pc = pcWord 309 ∧
            CheckFixedRegs s309 ∧
            ProofCursor s0 input.proof.length
              (pBase + 29 * capFrontierPrefix input.positions (step + 1))
              (tBase + capFrontierPrefix input.positions (step + 1)) s309 ∧
            s309.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) ∧
            s309.getReg .x30 = BitVec.ofNat 64 (68719475936 + 768) ∧
            (levelSize l % 2 = 1 →
              s309.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + pairs)) =
                (if capMark input.positions l (2 * pairs) then 1#8 else 0#8) ∧
              (capMark input.positions l (2 * pairs) = true →
                readBuffer s309 (8192 + capValOff (l + 1) + gapOffset pairs) 32 =
                  readBuffer sP (8192 + capValOff l + gapOffset (2 * pairs)) 32)) ∧
            (∀ a : Nat, a < 2 ^ 64 →
              (levelSize l % 2 = 0 ∨ a ≠ 4096 + capMarkOff (l + 1) + pairs) →
              (levelSize l % 2 = 0 ∨ capMark input.positions l (2 * pairs) = false ∨
                a < 8192 + capValOff (l + 1) + gapOffset pairs ∨
                8192 + capValOff (l + 1) + gapOffset pairs + 32 ≤ a) →
              s309.getByte (BitVec.ofNat 64 a) = sP.getByte (BitVec.ofNat 64 a)) := by
          have hst285 := step_ordinary oracle sP 285 (.ANDI .x6 .x20 1#12) (by decide) hpcP rfl (by intro h; cases h) rfl
          let t1 := execInstrBr sP (.ANDI .x6 .x20 1#12)
          have hpc_t1 : t1.pc = pcWord 286 := by simp only [t1, execInstrBr, MachineState.setPC, hpcP, pcWord_add_four]
          have hx6_t1 : t1.getReg .x6 = BitVec.ofNat 64 (levelSize l % 2) := by
            simp only [t1, execInstrBr, MachineState.getReg_setPC]
            rw [MachineState.getReg_setReg_eq (by decide), h20, se12_1, bv64_and_one _ (by omega)]
          have hst286 := step_ordinary oracle t1 286 (.BEQ .x6 .x0 92#13) (by decide) hpc_t1 rfl (by intro h; cases h) rfl
          let t2 := execInstrBr t1 (.BEQ .x6 .x0 92#13)
          by_cases heven : levelSize l % 2 = 0
          · have hx6z : t1.getReg .x6 = 0#64 := by rw [hx6_t1, heven]
            have hpc_t2 : t2.pc = pcWord 309 := by
              simp only [t2, execInstrBr, hx6z, getReg_x0, beq_self_eq_true, ite_true,
                MachineState.setPC, hpc_t1]; exact pc_286_branch
            have hmem_t2 : t2.mem = sP.mem := by
              have h21 : t2.mem = t1.mem := by
                simp only [t2, execInstrBr, hx6z, getReg_x0, beq_self_eq_true, ite_true, mem_setPC]
              rw [h21]
              simp only [t1, execInstrBr, mem_setPC, mem_setReg]
            have hreg_t2 : ∀ r, r ≠ .x6 → t2.getReg r = sP.getReg r := fun r h6 => by
              have h21 : t2.getReg r = t1.getReg r := by
                simp only [t2, execInstrBr, hx6z, getReg_x0, beq_self_eq_true, ite_true, MachineState.getReg_setPC]
              rw [h21]
              simp only [t1, execInstrBr, MachineState.getReg_setPC]
              exact MachineState.getReg_setReg_ne _ _ _ _ h6.symm
            exact ⟨t2, 2, by decide, by simpa using hst285.trans hst286, hpc_t2,
              hfixP.of_agree (fun r hr => hreg_t2 r (isFixedReg_ne_of_false hr rfl)),
              hcurP.of_agree (fun r hr => hreg_t2 r (isCursorReg_ne_of_false hr rfl)),
              (hreg_t2 .x29 (by decide)).trans h29, (hreg_t2 .x30 (by decide)).trans h30,
              fun hodd => by omega,
              fun a _ _ _ => by simp [MachineState.getByte, MachineState.getMem, hmem_t2]⟩
          · have hodd : levelSize l % 2 = 1 := by omega
            have hl_lt23 : l < 23 := cap_lt23_of_odd l hl1 hl2 hodd
            have hpairs_lt_next : pairs < levelSize (l + 1) := by rw [levelSize_step l (by omega)]; omega
            have hx6o : t1.getReg .x6 = 1#64 := by rw [hx6_t1, hodd]
            have hpc_t2 : t2.pc = pcWord 287 := by
              simp only [t2, execInstrBr, hx6o, getReg_x0, show (1#64 == 0#64) = false by decide,
                Bool.false_eq_true, ite_false, MachineState.setPC, hpc_t1, pcWord_add_four]
            have hmem_t2 : t2.mem = sP.mem := by
              have h21 : t2.mem = t1.mem := by
                simp only [t2, execInstrBr, hx6o, getReg_x0, show (1#64 == 0#64) = false by decide,
                  Bool.false_eq_true, ite_false, mem_setPC]
              rw [h21]
              simp only [t1, execInstrBr, mem_setPC, mem_setReg]
            have hreg_t2 : ∀ r, r ≠ .x6 → t2.getReg r = sP.getReg r := fun r h6 => by
              have h21 : t2.getReg r = t1.getReg r := by
                simp only [t2, execInstrBr, hx6o, getReg_x0, show (1#64 == 0#64) = false by decide,
                  Bool.false_eq_true, ite_false, MachineState.getReg_setPC]
              rw [h21]
              simp only [t1, execInstrBr, MachineState.getReg_setPC]
              exact MachineState.getReg_setReg_ne _ _ _ _ h6.symm
            -- pc[287..290]: load capMark[l][2 * pairs], branch to pc[309] if 0
            have hst287 := step_ordinary oracle t2 287 (.SLLI .x7 .x22 1#6) (by decide) hpc_t2 rfl (by intro h; cases h) rfl
            let t3 := execInstrBr t2 (.SLLI .x7 .x22 1#6)
            have hpc_t3 : t3.pc = pcWord 288 := by simp only [t3, execInstrBr, MachineState.setPC, hpc_t2, pcWord_add_four]
            have hst288 := step_ordinary oracle t3 288 (.ADD .x7 .x14 .x7) (by decide) hpc_t3 rfl (by intro h; cases h) rfl
            let t4 := execInstrBr t3 (.ADD .x7 .x14 .x7)
            have hpc_t4 : t4.pc = pcWord 289 := by simp only [t4, execInstrBr, MachineState.setPC, hpc_t3, pcWord_add_four]
            have hx7_t4 : t4.getReg .x7 = BitVec.ofNat 64 (4096 + capMarkOff l + 2 * pairs) := by
              have h22_2 := (hreg_t2 .x22 (by decide)).trans h22
              have h14_2 := (hreg_t2 .x14 (by decide)).trans h14
              simp only [t4, t3, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
                MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, h22_2, h14_2,
                show (1#6 : BitVec 6).toNat = 1 by decide]
              rw [bv64_shl pairs 1 (by omega), bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
            have hmem_t4 : t4.mem = sP.mem := by
              simpa [t4, t3, execInstrBr, mem_setPC, mem_setReg] using hmem_t2
            have ha289 : t4.getReg .x7 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + capMarkOff l + 2 * pairs) := by
              rw [hx7_t4, se12_0, BitVec.add_zero]
            have hv289 : memoryArgumentsValid t4 (.LBU .x8 .x7 0#12) = true := by
              simp only [memoryArgumentsValid, memAccess, ha289]
              exact accessValid_ofNat _ 1 (by unfold MEMORY_BYTES; omega) (by omega)
            have hst289 := step_ordinary oracle t4 289 (.LBU .x8 .x7 0#12) (by decide) hpc_t4 rfl (by intro h; cases h)
              (by simp [ordinaryStep, hv289])
            let t5 := execInstrBr t4 (.LBU .x8 .x7 0#12)
            have hpc_t5 : t5.pc = pcWord 290 := by simp only [t5, execInstrBr, MachineState.setPC, hpc_t4, pcWord_add_four]
            have hx8_t5 : t5.getReg .x8 = if capMark input.positions l (2 * pairs) then 1#64 else 0#64 := by
              simp only [t5, execInstrBr, MachineState.getReg_setPC, ha289]
              rw [MachineState.getReg_setReg_eq (by decide)]
              have hb : t4.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * pairs)) =
                  if capMark input.positions l (2 * pairs) then 1#8 else 0#8 := by
                simpa only [MachineState.getByte, MachineState.getMem, hmem_t4] using hmkL (2 * pairs) (by omega)
              rw [hb, bool_byte_zeroExtend]
            have hmem_t5 : t5.mem = sP.mem := by
              simpa [t5, execInstrBr, mem_setPC, mem_setReg] using hmem_t4
            have hreg_t5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → t5.getReg r = sP.getReg r := fun r h6 h7 h8 => by
              simp only [t5, t4, t3, execInstrBr, MachineState.getReg_setPC]
              rw [MachineState.getReg_setReg_ne _ _ _ _ h8.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h7.symm, MachineState.getReg_setPC,
                MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
              exact hreg_t2 r h6
            have hst290 := step_ordinary oracle t5 290 (.BEQ .x8 .x0 76#13) (by decide) hpc_t5 rfl (by intro h; cases h) rfl
            let t6 := execInstrBr t5 (.BEQ .x8 .x0 76#13)
            cases hm_odd : capMark input.positions l (2 * pairs) with
            | false =>
              have hx8z : t5.getReg .x8 = 0#64 := by simp only [hx8_t5, hm_odd, Bool.false_eq_true, ite_false]
              have hpc_t6 : t6.pc = pcWord 309 := by
                simp only [t6, execInstrBr, hx8z, getReg_x0, beq_self_eq_true, ite_true,
                  MachineState.setPC, hpc_t5]; exact pc_290_branch
              have hmem_t6 : t6.mem = sP.mem := by
                simpa [t6, execInstrBr, hx8z, getReg_x0, MachineState.setPC] using hmem_t5
              have hreg_t6 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → t6.getReg r = sP.getReg r := fun r h6 h7 h8 => by
                have : t6.getReg r = t5.getReg r := by simp [t6, execInstrBr, hx8z, getReg_x0, MachineState.getReg_setPC]
                exact this.trans (hreg_t5 r h6 h7 h8)
              refine ⟨t6, 6, by decide,
                by simpa using (hst285.trans hst286).trans ((hst287.trans hst288).trans (hst289.trans hst290)),
                hpc_t6,
                hfixP.of_agree (fun r hr => hreg_t6 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
                hcurP.of_agree (fun r hr => hreg_t6 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
                (hreg_t6 .x29 (by decide) (by decide) (by decide)).trans h29,
                (hreg_t6 .x30 (by decide) (by decide) (by decide)).trans h30,
                fun _ => ⟨by simp [MachineState.getByte, MachineState.getMem, hmem_t6]
                             exact hmkHi (4096 + capMarkOff (l + 1) + pairs) (le_refl _) (by omega),
                  fun hc => by cases hc⟩,
                fun a _ _ _ => by simp [MachineState.getByte, MachineState.getMem, hmem_t6]⟩
            | true =>
              have hx8o : t5.getReg .x8 = 1#64 := by simp only [hx8_t5, hm_odd, ite_true]
              have hpc_t6 : t6.pc = pcWord 291 := by
                simp only [t6, execInstrBr, hx8o, getReg_x0, show (1#64 == 0#64) = false by decide,
                  Bool.false_eq_true, ite_false, MachineState.setPC, hpc_t5, pcWord_add_four]
              have hmem_t6 : t6.mem = sP.mem := by
                simpa [t6, execInstrBr, hx8o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.setPC] using hmem_t5
              have hreg_t6 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → t6.getReg r = sP.getReg r := fun r h6 h7 h8 => by
                have : t6.getReg r = t5.getReg r := by
                  simp [t6, execInstrBr, hx8o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
                exact this.trans (hreg_t5 r h6 h7 h8)
              have hx8_t6 : t6.getReg .x8 = 1#64 := by
                have : t6.getReg .x8 = t5.getReg .x8 := by
                  simp [t6, execInstrBr, hx8o, getReg_x0, show (1#64 == 0#64) = false by decide, MachineState.getReg_setPC]
                exact this.trans hx8o
              -- pc[291..292]: SB capMark[l+1][pairs] = 1
              have hst291 := step_ordinary oracle t6 291 (.ADD .x7 .x15 .x22) (by decide) hpc_t6 rfl (by intro h; cases h) rfl
              let t7 := execInstrBr t6 (.ADD .x7 .x15 .x22)
              have hpc_t7 : t7.pc = pcWord 292 := by simp only [t7, execInstrBr, MachineState.setPC, hpc_t6, pcWord_add_four]
              have hx7_t7 : t7.getReg .x7 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + pairs) := by
                simp only [t7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_eq (by decide),
                  hreg_t6 .x15 (by decide) (by decide) (by decide), h15,
                  hreg_t6 .x22 (by decide) (by decide) (by decide), h22, bv64_add]
              have hx8_t7 : t7.getReg .x8 = 1#64 := by
                simp only [t7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x8), hx8_t6]
              have ha292 : t7.getReg .x7 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + pairs) := by
                rw [hx7_t7, se12_0, BitVec.add_zero]
              have hv292 : memoryArgumentsValid t7 (.SB .x7 .x8 0#12) = true := by
                simp only [memoryArgumentsValid, memAccess, ha292]
                exact accessValid_ofNat _ 1 (by unfold MEMORY_BYTES; omega) (by omega)
              have hst292 := step_ordinary oracle t7 292 (.SB .x7 .x8 0#12) (by decide) hpc_t7 rfl (by intro h; cases h)
                (by simp [ordinaryStep, hv292])
              let t8 := execInstrBr t7 (.SB .x7 .x8 0#12)
              have hpc_t8 : t8.pc = pcWord 293 := by simp only [t8, execInstrBr, MachineState.setPC, hpc_t7, pcWord_add_four]
              have hmem_t7 : t7.mem = sP.mem := by simpa [t7, execInstrBr, mem_setPC, mem_setReg] using hmem_t6
              have hbyte_t8 : ∀ a, t8.getByte a =
                  (sP.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + pairs)) 1#8).getByte a := fun a => by
                simp only [t8, execInstrBr, ha292, hx8_t7, show (1#64 : Word).truncate 8 = 1#8 by decide,
                  MachineState.getByte, MachineState.setByte, MachineState.getMem,
                  MachineState.setMem, mem_setPC, hmem_t7]
              have hout_t8 : MemEqOutside sP t8 (4096 + capMarkOff (l + 1) + pairs)
                  (4096 + capMarkOff (l + 1) + pairs + 1) := by
                intro a ha hout; rw [hbyte_t8]; exact MemEqOutside_setByte sP _ 1#8 (by omega) a ha hout
              have hreg_t8 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → t8.getReg r = sP.getReg r := fun r h6 h7 h8 => by
                have : t8.getReg r = t7.getReg r := by
                  simp [t8, execInstrBr, MachineState.setByte, MachineState.setMem, MachineState.setPC, MachineState.getReg]
                rw [this]; simp only [t7, execInstrBr, MachineState.getReg_setPC]
                rw [MachineState.getReg_setReg_ne _ _ _ _ h7.symm]
                exact hreg_t6 r h6 h7 h8
              -- pc[293..300]: compute x10 = 8192 + capValOff l + 96 * pairs, x12 = 8192 + capValOff (l+1) + gapOffset pairs
              have hcodeO : ∀ j (hj : j < capOddAddrInstrs.length), checkInstr (293 + j) = .base (capOddAddrInstrs[j]'hj) := by
                intro j hj; have hj' : j < 8 := hj; interval_cases j <;> rfl
              have hpureO : ∀ j (hj : j < capOddAddrInstrs.length),
                  Instruction.base (capOddAddrInstrs[j]'hj) ≠ .base .ECALL ∧
                  ∀ st, ordinaryStep st (.base (capOddAddrInstrs[j]'hj)) = some (execInstrBr st (capOddAddrInstrs[j]'hj)) ∧
                        (execInstrBr st (capOddAddrInstrs[j]'hj)).pc = st.pc + (4 : Word) ∧
                        (execInstrBr st (capOddAddrInstrs[j]'hj)).mem = st.mem := by
                intro j hj; have hj' : j < 8 := hj; interval_cases j <;> exact ⟨(by intro h; cases h), fun _ => ⟨rfl, rfl, rfl⟩⟩
              obtain ⟨hs_t9, hpc_t9, hmem_t9⟩ := step_pure_list oracle 293 capOddAddrInstrs t8 (by decide) hcodeO hpureO hpc_t8
              let t9 := runInstrs t8 capOddAddrInstrs
              have hs_t9 : StepsTo oracle t8 t9 8 0 [] := hs_t9
              have hpc_t9 : t9.pc = pcWord 301 := hpc_t9
              have hmem_t9 : t9.mem = t8.mem := hmem_t9
              have hreg_t9 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → t9.getReg r = t8.getReg r :=
                fun r h6 h7 h10 h12 => by
                  simp only [t9, runInstrs, capOddAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC]
                  rw [MachineState.getReg_setReg_ne _ _ _ _ h12.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
                    MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm, MachineState.getReg_setPC,
                    MachineState.getReg_setReg_ne _ _ _ _ h10.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h10.symm, MachineState.getReg_setPC,
                    MachineState.getReg_setReg_ne _ _ _ _ h7.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h6.symm]
              have hx10_t9 : t9.getReg .x10 = BitVec.ofNat 64 (8192 + capValOff l + gapOffset (2 * pairs)) := by
                have h22_8 := (hreg_t8 .x22 (by decide) (by decide) (by decide)).trans h22
                have h16_8 := (hreg_t8 .x16 (by decide) (by decide) (by decide)).trans h16
                simp only [t9, runInstrs, capOddAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
                  MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq,
                  h22_8, h16_8, show (6#6 : BitVec 6).toNat = 6 by decide, show (5#6 : BitVec 6).toNat = 5 by decide]
                rw [bv64_shl pairs 6 (by omega), bv64_shl pairs 5 (by omega), bv64_add, bv64_add, gapOffset_even]; exact congrArg (BitVec.ofNat 64) (by omega)
              have hx12_t9 : t9.getReg .x12 = BitVec.ofNat 64 (8192 + capValOff (l + 1) + gapOffset pairs) := by
                have h22_8 := (hreg_t8 .x22 (by decide) (by decide) (by decide)).trans h22
                have h17_8 := (hreg_t8 .x17 (by decide) (by decide) (by decide)).trans h17
                simp only [t9, runInstrs, capOddAddrInstrs, List.foldl, execInstrBr, MachineState.getReg_setPC,
                  MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq,
                  h22_8, h17_8, show (1#6 : BitVec 6).toNat = 1 by decide, show (5#6 : BitVec 6).toNat = 5 by decide]
                rw [bv64_shr pairs 1 (by omega), Nat.pow_one, bv64_add, bv64_shl _ 5 (by omega), bv64_add]
                exact congrArg (BitVec.ofNat 64) (by unfold gapOffset; omega)
              -- pc[301..308]: copy 4 dwords x10 -> x12
              have hcp_odd : ∀ j < 4,
                  checkInstr (301 + 2 * j) = .base (.LD .x6 .x10 (BitVec.ofNat 12 (0 + 8 * j))) ∧
                  checkInstr (301 + 2 * j + 1) = .base (.SD .x12 .x6 (BitVec.ofNat 12 (0 + 8 * j))) := by
                intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩
              have hsrc_bd_o : 8192 + capValOff l + gapOffset (2 * pairs) + 32 ≤ 8192 + capValOff (l + 1) := by
                rw [gapOffset_even, hvo_step]; omega
              have hdst_bd_o : capValOff (l + 1) + gapOffset pairs + 32 ≤ 33152 :=
                cap_val_next_bound l pairs hl1 hl2 hpairs_lt_next
              obtain ⟨t10, hs_t10, hpc_t10, hreg_t10, hcopy_t10, hout_t10⟩ :=
                step_copy_dwords oracle 301 4 .x10 .x12 0 0 t9
                  (8192 + capValOff l + gapOffset (2 * pairs)) (8192 + capValOff (l + 1) + gapOffset pairs)
                  (by decide) (by decide) (by decide) (by decide) (by decide) hcp_odd hpc_t9 hx10_t9 hx12_t9
                  (by unfold gapOffset; omega) (by unfold gapOffset; omega)
                  (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega) (by omega)
              have hreg_all_o : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x12 → t10.getReg r = sP.getReg r :=
                fun r h6 h7 h8 h10 h12 => (hreg_t10 r h6).trans ((hreg_t9 r h6 h7 h10 h12).trans (hreg_t8 r h6 h7 h8))
              refine ⟨t10, 24, by decide,
                by simpa using (((hst285.trans hst286).trans ((hst287.trans hst288).trans (hst289.trans hst290))).trans
                  (hst291.trans hst292)).trans (hs_t9.trans hs_t10),
                hpc_t10,
                hfixP.of_agree (fun r hr => hreg_all_o r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)
                  (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
                hcurP.of_agree (fun r hr => hreg_all_o r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)
                  (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
                (hreg_all_o .x29 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h29,
                (hreg_all_o .x30 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h30,
                fun _ => ⟨by
                    rw [hout_t10 _ (by omega) (by simp only [Nat.add_zero]; omega)]
                    have : t9.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + pairs)) =
                        t8.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + pairs)) := by
                      simp [MachineState.getByte, MachineState.getMem, hmem_t9]
                    rw [this, hbyte_t8, set_byte_read]; simp only [ite_true],
                  fun _ => by
                    apply readBuffer_congr2; intro b hb
                    have hc := hcopy_t10 b hb; simp only [Nat.add_zero] at hc
                    rw [hc]
                    have : t9.getByte (BitVec.ofNat 64 (8192 + capValOff l + gapOffset (2 * pairs) + b)) =
                        t8.getByte (BitVec.ofNat 64 (8192 + capValOff l + gapOffset (2 * pairs) + b)) := by
                      simp [MachineState.getByte, MachineState.getMem, hmem_t9]
                    rw [this, hout_t8 _ (by omega) (by omega)]⟩,
                fun a ha hmk_o hval_o => by
                  have hno_v : a < 8192 + capValOff (l + 1) + gapOffset pairs + 0 ∨
                      8192 + capValOff (l + 1) + gapOffset pairs + 0 + 32 ≤ a := by
                    rcases hval_o with h0 | h0 | h1 | h2 <;> [omega; cases h0; omega; omega]
                  have hno_m : a ≠ 4096 + capMarkOff (l + 1) + pairs := by
                    rcases hmk_o with h0 | h1 <;> [omega; exact h1]
                  rw [hout_t10 a ha hno_v]
                  have : t9.getByte (BitVec.ofNat 64 a) = t8.getByte (BitVec.ofNat 64 a) := by
                    simp [MachineState.getByte, MachineState.getMem, hmem_t9]
                  rw [this, hout_t8 a ha (by omega)]⟩
        obtain ⟨s309, kOdd, hkOdd, hsOdd, hpc309, hfix309, hcur309, hx29_309, hx30_309, hodd_res, hout_odd⟩ := hodd_tail
        -- pc[309..310]: ADDI x29, x29, 32; BNE x29, x30, pc[245]
        have hst309 := step_ordinary oracle s309 309 (.ADDI .x29 .x29 32#12) (by decide) hpc309 rfl (by intro h; cases h) rfl
        let s310 := execInstrBr s309 (.ADDI .x29 .x29 32#12)
        have hpc310 : s310.pc = pcWord 310 := by simp only [s310, execInstrBr, MachineState.setPC, hpc309, pcWord_add_four]
        have hx29_310 : s310.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (15 + (step + 1))) := by
          simp only [s310, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide), hx29_309, se12_32]
          change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
        have hx30_310 : s310.getReg .x30 = BitVec.ofNat 64 (68719475936 + 768) := by
          simp only [s310, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), hx30_309]
        have hst310 := step_ordinary oracle s310 310 (.BNE .x29 .x30 7932#13) (by decide) hpc310 rfl (by intro h; cases h) rfl
        let sFin := execInstrBr s310 (.BNE .x29 .x30 7932#13)
        have hmemFin : sFin.mem = s309.mem := by
          simp only [sFin, execInstrBr]; split <;> simp [s310, execInstrBr, mem_setPC, mem_setReg]
        have hregFin : ∀ r, r ≠ .x29 → sFin.getReg r = s309.getReg r := fun r h29r => by
          have : sFin.getReg r = s310.getReg r := by simp only [sFin, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
          rw [this]; simp only [s310, execInstrBr, MachineState.getReg_setPC]
          exact MachineState.getReg_setReg_ne _ _ _ _ h29r.symm
        have hx29Fin : sFin.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (15 + (step + 1))) := by
          have : sFin.getReg .x29 = s310.getReg .x29 := by simp only [sFin, execInstrBr]; split <;> simp [MachineState.getReg_setPC]
          exact this.trans hx29_310
        have hne_iff : (s310.getReg .x29 != s310.getReg .x30) = decide (step + 1 ≠ 9) := by
          rw [hx29_310, hx30_310, bv64_bne_eq _ _ (by omega) (by omega)]
          exact decide_eq_decide.mpr (by omega)
        have hpcFin : sFin.pc = if step + 1 = 9 then pcWord 311 else pcWord 245 := by
          by_cases h9 : step + 1 = 9
          · simp only [sFin, execInstrBr, hne_iff, h9, ne_eq, not_true_eq_false, decide_false,
              Bool.false_eq_true, ite_false, ite_true, MachineState.setPC, hpc310, pcWord_add_four]
          · simp only [sFin, execInstrBr, hne_iff, h9, ne_eq, not_false_eq_true, decide_true,
              ite_true, ite_false, MachineState.setPC, hpc310]; exact pc_310_branch
        have hfin_sP : ∀ a : Nat, a < 2 ^ 64 →
            (levelSize l % 2 = 0 ∨ a ≠ 4096 + capMarkOff (l + 1) + pairs) →
            (levelSize l % 2 = 0 ∨ capMark input.positions l (2 * pairs) = false ∨
              a < 8192 + capValOff (l + 1) + gapOffset pairs ∨
              8192 + capValOff (l + 1) + gapOffset pairs + 32 ≤ a) →
            sFin.getByte (BitVec.ofNat 64 a) = sP.getByte (BitVec.ofNat 64 a) := fun a ha h1 h2 => by
          have : sFin.getByte (BitVec.ofNat 64 a) = s309.getByte (BitVec.ofNat 64 a) := by
            simp [MachineState.getByte, MachineState.getMem, hmemFin]
          exact this.trans (hout_odd a ha h1 h2)
        have hfin_s : ∀ a : Nat, a < 2 ^ 64 →
            (a < 4096 + capMarkOff (l + 1) ∨ 4096 + capMarkOff (l + 1) + levelSize (l + 1) ≤ a) →
            (∀ idx < levelSize l, capMark input.positions l idx = false →
              a < 8192 + capValOff l + gapOffset idx ∨ 8192 + capValOff l + gapOffset idx + 32 ≤ a) →
            (∀ idx < levelSize (l + 1), capMark input.positions (l + 1) idx = true →
              a < 8192 + capValOff (l + 1) + gapOffset idx ∨ 8192 + capValOff (l + 1) + gapOffset idx + 32 ≤ a) →
            sFin.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a) := fun a ha hmk hunm hdst => by
          have hls_next : levelSize (l + 1) = pairs + levelSize l % 2 := by
            rw [levelSize_step l (by omega)]; omega
          have h1 : sFin.getByte (BitVec.ofNat 64 a) = sP.getByte (BitVec.ofNat 64 a) := by
            refine hfin_sP a ha ?_ ?_
            · by_cases he : levelSize l % 2 = 0
              · exact Or.inl he
              · exact Or.inr (by omega)
            · by_cases he : levelSize l % 2 = 0
              · exact Or.inl he
              · by_cases hm : capMark input.positions l (2 * pairs) = false
                · exact Or.inr (Or.inl hm)
                · have hmt : capMark input.positions l (2 * pairs) = true :=
                    Bool.eq_true_of_not_eq_false hm
                  have hcm_p : capMark input.positions (l + 1) pairs = true := by
                    rw [capMark_succ input.positions l pairs hl1, if_neg (by omega), if_pos (by omega), hmt]
                  exact Or.inr (Or.inr (hdst pairs (by omega) hcm_p))
          have h2 : sP.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a) :=
            hpresP a ha (by omega)
              (fun q hq idx hi hm => hunm idx (by omega) hm)
              (fun q hq hcm => hdst q (by omega) hcm)
          exact h1.trans h2
        have hcalls_le : qP ≤ input.positions.card :=
          hqP.trans (pairMarkedNextCount_le_card input.positions l hl1)
        refine PhaseOutcome.continued sFin (kOdd + 2) 0 [] (by omega) (by decide)
          (by simpa [Nat.add_assoc] using hsOdd.trans (hst309.trans hst310)) ?_
        refine ⟨by simpa using hcalls_le, ?_⟩
        refine ⟨hfix309.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)),
          hcur309.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)),
          ?_, hpcFin, hx29Fin,
          (hregFin .x30 (by decide)).trans hx30_309, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- HighMemPreserved
          intro a ha hge
          exact (hfin_s a ha (Or.inr (by omega))
            (fun idx hidx _ => Or.inr (by have := cap_gapOffset_bound l idx hl1 (by omega) hidx; omega))
            (fun idx hidx _ => Or.inr (by have := cap_val_next_bound l idx hl1 hl2 hidx; omega))).trans
            (hinv.high a ha hge)
        · -- mark_cur for step + 1
          intro hstep1 idx hidx
          have hl1_eq : 15 + (step + 1) = l + 1 := by omega
          rw [hl1_eq] at hidx ⊢
          have hls_next : levelSize (l + 1) = pairs + levelSize l % 2 := by
            rw [levelSize_step l (by omega)]; omega
          by_cases hlt : idx < pairs
          · exact (hfin_sP _ (by omega) (Or.inr (by omega))
              (Or.inr (Or.inr (Or.inl (by unfold gapOffset; omega))))).trans (hmkN idx hlt)
          · have hodd : levelSize l % 2 = 1 := by omega
            have heq : idx = pairs := by omega
            subst heq
            have hcm_p : capMark input.positions (l + 1) pairs = capMark input.positions l (2 * pairs) := by
              rw [capMark_succ input.positions l pairs hl1, if_neg (by omega), if_pos (by omega)]
            rw [hcm_p]
            have : sFin.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + pairs)) =
                s309.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + pairs)) := by
              simp [MachineState.getByte, MachineState.getMem, hmemFin]
            exact this.trans (hodd_res hodd).1
        · -- mark_hi_zero for step + 1
          intro hstep1 a ha1 ha2
          have hl2_eq : 15 + (step + 1) + 1 = l + 2 := by omega
          rw [hl2_eq] at ha1
          have hmo_n2 : capMarkOff (l + 1) + levelSize (l + 1) ≤ capMarkOff (l + 2) :=
            capMarkOff_step_le (l + 1) (by omega) (by omega)
          have h1 := hfin_s a (by omega) (Or.inr (by omega))
            (fun _ _ _ => Or.inl (by unfold gapOffset; omega))
            (fun _ _ _ => Or.inl (by unfold gapOffset; omega))
          have h2 := hinv.mark_hi_zero hstep a (by change 4096 + capMarkOff (l + 1) ≤ a; omega) ha2
          exact h1.trans h2
        · -- val_cur_gap_zero for step + 1
          intro hstep1 q' hq' b hb
          have hl1_eq : 15 + (step + 1) = l + 1 := by omega
          rw [hl1_eq] at hq' ⊢
          have hgap_bd : capValOff (l + 1) + 96 * q' + 64 + b < 33152 := by
            have hlt : 96 * q' + 96 ≤ levelBytes (l + 1) := by
              unfold levelBytes
              have hne0 : l + 1 ≠ 0 := by omega
              have hlt24 : l + 1 < 24 := by omega
              simp only [hne0, ite_false, hlt24, ite_true]; omega
            omega
          have h1 := hfin_s (8192 + capValOff (l + 1) + 96 * q' + 64 + b) (by omega) (Or.inr (by omega))
            (fun idx0 hidx0 _ => Or.inr (by
              have := cap_gapOffset_bound l idx0 hl1 (by omega) hidx0
              have : capValOff l + levelBytes l = capValOff (l + 1) := capValOff_add_levelBytes_eq l hl1 hl2
              omega))
            (fun idx1 _ _ => by have := gapOffset_disjoint_gap idx1 q'; omega)
          exact h1.trans (hinv.val_hi_zero hstep _ (by change 8192 + capValOff (l + 1) ≤ _; omega) (by omega))
        · -- val_hi_zero for step + 1
          intro hstep1 a ha1 ha2
          have hl2_eq : 15 + (step + 1) + 1 = l + 2 := by omega
          rw [hl2_eq] at ha1
          have hl23 : l < 23 := by omega
          have h1 := hfin_s a (by omega) (Or.inr (by omega))
            (fun idx0 hidx0 _ => Or.inr (by
              have := cap_gapOffset_bound l idx0 hl1 (by omega) hidx0
              have : capValOff l + levelBytes l ≤ capValOff (l + 2) := capValOff_add_levelBytes_le hl1 (by omega) (by omega)
              omega))
            (fun idx1 hidx1 _ => Or.inr (by have := cap_val_next_lt_next l idx1 hl1 hl23 hidx1; omega))
          have hvo_m := capValOff_mono (by omega) (show l + 1 ≤ l + 2 by omega) (by omega)
          exact h1.trans (hinv.val_hi_zero hstep a (by change 8192 + capValOff (l + 1) ≤ a; omega) ha2)
        · -- val15_marked preserved
          intro c hc hcm15
          have hpres_15 : readBuffer sFin (8192 + capValOff 15 + gapOffset c) 32 =
              readBuffer s (8192 + capValOff 15 + gapOffset c) 32 := by
            have h15 : capValOff 15 = 0 := by decide
            have h16 : capValOff 16 = 16416 := by decide
            apply readBuffer_congr2; intro b hb
            have hc_bd : gapOffset c + 32 ≤ 16416 := by unfold gapOffset; omega
            refine hfin_s (8192 + capValOff 15 + gapOffset c + b) (by omega) (Or.inr (by omega)) ?_ ?_
            · intro idx0 hidx0 hunm0
              by_cases hs0 : step = 0
              · have hl15 : l = 15 := by omega
                rw [hl15] at hunm0 ⊢
                have hne : c ≠ idx0 := fun h => by rw [h, hunm0] at hcm15; cases hcm15
                have := gapOffset_disjoint hne; omega
              · left
                have hm := capValOff_mono (by decide) (show 16 ≤ l by omega) (by omega)
                omega
            · intro idx1 _ _
              left
              have hm := capValOff_mono (by decide) (show 16 ≤ l + 1 by omega) (by omega)
              omega
          exact hpres_15.trans (hinv.val15_marked c hc hcm15)
        · -- levels_done for d < step + 1
          intro d hd
          by_cases hd_lt : d < step
          · -- Earlier level d < step: preserve all reads from s
            obtain ⟨hprev_p, hprev_o⟩ := hinv.levels_done d hd_lt
            let ld := 15 + d
            have hld_lt : ld < l := by omega
            have hpres_low : ∀ idx < levelSize ld,
                readBuffer sFin (8192 + capValOff ld + gapOffset idx) 32 =
                readBuffer s (8192 + capValOff ld + gapOffset idx) 32 := fun idx hidx => by
              have hb1 := cap_gapOffset_bound ld idx (by omega) (by omega) hidx
              have hb2 : capValOff ld + levelBytes ld ≤ capValOff l := capValOff_add_levelBytes_le (by omega) hld_lt (by omega)
              apply readBuffer_congr2; intro b hb
              exact hfin_s (8192 + capValOff ld + gapOffset idx + b) (by omega) (Or.inr (by omega))
                (fun _ _ _ => Or.inl (by omega)) (fun _ _ _ => Or.inl (by omega))
            have hpres_hi : ∀ idx < levelSize (ld + 1), capMark input.positions (ld + 1) idx = true →
                readBuffer sFin (8192 + capValOff (ld + 1) + gapOffset idx) 32 =
                readBuffer s (8192 + capValOff (ld + 1) + gapOffset idx) 32 := fun idx hidx hcm => by
              have hb1 := cap_gapOffset_bound (ld + 1) idx (by omega) (by omega) hidx
              have hb2_hi : capValOff (ld + 1) + levelBytes (ld + 1) ≤ capValOff (l + 1) :=
                capValOff_add_levelBytes_le (by omega) (by omega) (by omega)
              apply readBuffer_congr2; intro b hb
              refine hfin_s (8192 + capValOff (ld + 1) + gapOffset idx + b) (by omega) (Or.inr (by omega)) ?_ ?_
              · intro idx0 hidx0 hunm0
                by_cases hnext : ld + 1 = l
                · rw [hnext] at hcm ⊢
                  have hne : idx ≠ idx0 := fun h => by rw [h, hunm0] at hcm; cases hcm
                  have := gapOffset_disjoint hne; omega
                · left
                  have hb2 : capValOff (ld + 1) + levelBytes (ld + 1) ≤ capValOff l := capValOff_add_levelBytes_le (by omega) (by omega) (by omega)
                  omega
              · intro _ _ _
                left
                have hb2 : capValOff (ld + 1) + levelBytes (ld + 1) ≤ capValOff (l + 1) := capValOff_add_levelBytes_le (by omega) (by omega) (by omega)
                omega
            constructor
            · intro q hq hcm
              change q < levelSize ld / 2 at hq
              obtain ⟨hv, htr, hfL, hfR⟩ := hprev_p q hq hcm
              have hq_next : q < levelSize (ld + 1) := by rw [levelSize_step ld (by omega)]; omega
              rw [hpres_low (2 * q) (by omega), hpres_low (2 * q + 1) (by omega), hpres_hi q hq_next hcm]
              exact ⟨hv, htr.append_left, hfL, hfR⟩
            · intro hodd hcm
              change levelSize ld % 2 = 1 at hodd
              have hp_next : levelSize ld / 2 < levelSize (ld + 1) := by rw [levelSize_step ld (by omega)]; omega
              have hcm_n : capMark input.positions (ld + 1) (levelSize ld / 2) = true := by
                rw [capMark_succ input.positions ld (levelSize ld / 2) (by omega),
                  if_neg (by omega), if_pos (by omega), hcm]
              rw [hpres_low (2 * (levelSize ld / 2)) (by omega), hpres_hi (levelSize ld / 2) hp_next hcm_n]
              exact hprev_o hodd hcm
          · -- Current level d = step
            have hdeq : d = step := by omega
            subst hdeq
            constructor
            · intro q hq hcm
              change q < levelSize l / 2 at hq
              obtain ⟨hv, htr, hfL, hfR⟩ := hdoneP q hq hcm
              have hpres_cur : ∀ idx < levelSize l,
                  readBuffer sFin (8192 + capValOff l + gapOffset idx) 32 =
                  readBuffer sP (8192 + capValOff l + gapOffset idx) 32 := fun idx hidx => by
                have hb1 := cap_gapOffset_bound l idx hl1 (by omega) hidx
                have hb2 : capValOff l + levelBytes l = capValOff (l + 1) := capValOff_add_levelBytes_eq l hl1 hl2
                apply readBuffer_congr2; intro b hb
                exact hfin_sP (8192 + capValOff l + gapOffset idx + b) (by omega) (Or.inr (by omega))
                  (Or.inr (Or.inr (Or.inl (by omega))))
              have hpres_next : readBuffer sFin (8192 + capValOff (l + 1) + gapOffset q) 32 =
                  readBuffer sP (8192 + capValOff (l + 1) + gapOffset q) 32 := by
                have hne : q ≠ pairs := by omega
                have hdisj := gapOffset_disjoint hne
                apply readBuffer_congr2; intro b hb
                exact hfin_sP (8192 + capValOff (l + 1) + gapOffset q + b)
                  (by have := cap_val_next_bound l q hl1 hl2 (by rw [levelSize_step l (by omega)]; omega); omega)
                  (Or.inr (by omega)) (Or.inr (Or.inr (by omega)))
              rw [hpres_cur (2 * q) (by omega), hpres_cur (2 * q + 1) (by omega), hpres_next]
              exact ⟨hv, by simpa only [List.append_nil] using htr.append_right,
                by simpa only [pLvl, tLvl, Nat.mul_add, Nat.add_assoc] using hfL,
                by simpa only [pLvl, tLvl, Nat.mul_add, Nat.add_assoc] using hfR⟩
            · intro hodd hcm
              change levelSize l % 2 = 1 at hodd
              have h1 : readBuffer sFin (8192 + capValOff (l + 1) + gapOffset pairs) 32 =
                  readBuffer s309 (8192 + capValOff (l + 1) + gapOffset pairs) 32 := by
                apply readBuffer_congr2; intro b _; simp [MachineState.getByte, MachineState.getMem, hmemFin]
              have h2 : readBuffer sFin (8192 + capValOff l + gapOffset (2 * pairs)) 32 =
                  readBuffer sP (8192 + capValOff l + gapOffset (2 * pairs)) 32 := by
                have hb1 := cap_gapOffset_bound l (2 * pairs) hl1 (by omega) (by omega)
                have hb2 : capValOff l + levelBytes l = capValOff (l + 1) := capValOff_add_levelBytes_eq l hl1 hl2
                apply readBuffer_congr2; intro b hb
                exact hfin_sP (8192 + capValOff l + gapOffset (2 * pairs) + b) (by omega) (Or.inr (by omega))
                  (Or.inr (Or.inr (Or.inl (by omega))))
              rw [h1, h2]
              exact (hodd_res hodd).2 hcm)

/-- Complete bottom-up cap walk from `pc[243]` to `pc[311]` (`≤ 80000` steps, `≤ 9 * k` calls). -/
theorem step_cap_walk (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (sPos : MachineState) (trPos : CompressionReplies)
    (hpos : PosLoopInv h768 oracle input input.positions.card sPos trPos) :
    let pBase := posRecordOff input.positions input.positions.card
    let tBase := posTailOff input.positions input.positions.card
    PhaseOutcome oracle sPos 80000 (9 * input.positions.card)
      (input.proof.length <
        pBase + 29 * capFrontierCount input.positions +
        tailBytes (tBase + capFrontierCount input.positions))
      (fun sCap calls trCap =>
        calls ≤ 9 * input.positions.card ∧
        CapWalkInv h768 oracle input sPos 9 sCap trCap) := by
  intro pBase tBase
  -- pc[243..244]: ADDI x29, x2, 480; ADDI x30, x2, 768
  have hpc243 : sPos.pc = pcWord 243 := by have := hpos.pc; rwa [if_pos rfl] at this
  have hst243 := step_ordinary oracle sPos 243 (.ADDI .x29 .x2 480#12) (by decide) hpc243 rfl (by intro h; cases h) rfl
  let s1 := execInstrBr sPos (.ADDI .x29 .x2 480#12)
  have hpc1 : s1.pc = pcWord 244 := by simp only [s1, execInstrBr, MachineState.setPC, hpc243, pcWord_add_four]
  have hst244 := step_ordinary oracle s1 244 (.ADDI .x30 .x2 768#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADDI .x30 .x2 768#12)
  have hpc2 : s2.pc = pcWord 245 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = sPos.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg2 : ∀ r, r ≠ .x29 → r ≠ .x30 → s2.getReg r = sPos.getReg r := fun r h29 h30 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h30.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h29.symm]
  have hx29_2 : s2.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 15) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hpos.fixed.x2, se12_480]
    rw [bv64_add]
  have hx30_2 : s2.getReg .x30 = BitVec.ofNat 64 (68719475936 + 768) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hpos.fixed.x2, se12_768]
    rw [bv64_add]
  have hinit0 : CapWalkInv h768 oracle input sPos 0 s2 [] := by
    refine ⟨hpos.fixed.of_agree (fun r hr => hreg2 r (isFixedReg_ne_of_false hr rfl) (isFixedReg_ne_of_false hr rfl)),
      by simpa [capFrontierPrefix_zero, pBase, tBase] using
        hpos.cursor.of_agree (fun r hr => hreg2 r (isCursorReg_ne_of_false hr rfl) (isCursorReg_ne_of_false hr rfl)),
      hpos.high.trans (MemEqOutside.of_mem_eq hmem2 0 4294971392),
      by simpa using hpc2,
      hx29_2, hx30_2,
      fun _ idx hidx => by
        rw [show capMarkOff 15 = 0 by decide, Nat.add_zero]
        rw [levelSize_15] at hidx
        have hb : s2.getByte (BitVec.ofNat 64 (4096 + idx)) = sPos.getByte (BitVec.ofNat 64 (4096 + idx)) := by
          simp only [MachineState.getByte, MachineState.getMem, hmem2]
        rw [hb]
        simpa only [posMarked15_card_eq_capMark] using hpos.mark15 idx hidx,
      fun _ a ha1 ha2 => by
        rw [show capMarkOff 16 = 344 by decide] at ha1
        simp only [MachineState.getByte, MachineState.getMem, hmem2]
        exact hpos.mark_hi_zero a (by omega) ha2,
      fun _ q hq b hb => by
        rw [show capValOff 15 = 0 by decide, Nat.add_zero]
        rw [show levelSize 15 / 2 = 171 by decide] at hq
        simp only [MachineState.getByte, MachineState.getMem, hmem2]
        exact hpos.val15_gap_zero q hq b hb,
      fun _ a ha1 ha2 => by
        simp only [MachineState.getByte, MachineState.getMem, hmem2]
        exact hpos.val_hi_zero a ha1 ha2,
      fun c _ _ => by
        rw [show capValOff 15 = 0 by decide, Nat.add_zero]
        apply readBuffer_congr2; intro b _; simp [MachineState.getByte, MachineState.getMem, hmem2],
      fun _ h => (Nat.not_lt_zero _ h).elim⟩
  have hind : ∀ n ≤ 9,
      PhaseOutcome oracle s2 (∑ d ∈ Finset.range n, (37 + 225 * (levelSize (15 + d) / 2)))
        (n * input.positions.card)
        (input.proof.length <
          pBase + 29 * capFrontierPrefix input.positions n +
          tailBytes (tBase + capFrontierPrefix input.positions n))
        (fun s' calls tr => calls ≤ n * input.positions.card ∧ CapWalkInv h768 oracle input sPos n s' tr) := by
    intro n hn
    induction n with
    | zero =>
      exact .continued s2 0 0 [] (by simp) (by simp) (StepsTo.refl oracle s2) ⟨by simp, hinit0⟩
    | succ d ih =>
      have hmono : input.proof.length <
            pBase + 29 * capFrontierPrefix input.positions d +
            tailBytes (tBase + capFrontierPrefix input.positions d) →
          input.proof.length <
            pBase + 29 * capFrontierPrefix input.positions (d + 1) +
            tailBytes (tBase + capFrontierPrefix input.positions (d + 1)) := by
        have hfm := capFrontierPrefix_mono input.positions (show d ≤ d + 1 by omega)
        have htm := tailBytes_mono (show tBase + capFrontierPrefix input.positions d ≤
          tBase + capFrontierPrefix input.positions (d + 1) by omega)
        omega
      rw [Finset.sum_range_succ, Nat.succ_mul d input.positions.card]
      refine PhaseOutcome.bind_dep
        (P2 := fun s' calls tr => calls ≤ d * input.positions.card + input.positions.card ∧
          CapWalkInv h768 oracle input sPos (d + 1) s' tr)
        (ih (by omega)) hmono (fun sd q1 tr1 ⟨hq1, hinv_d⟩ => by
          have hstep_d := step_cap_level h768 oracle input hvalid sPos d (by omega) sd tr1 hinv_d
          dsimp only at hstep_d
          exact hstep_d.weaken (le_refl _) (le_refl _) id
            (fun sd1 q2 tr2 ⟨hq2, hinv_d1⟩ => ⟨by omega, hinv_d1⟩))
  have h9 := hind 9 (le_refl 9)
  have hpre2 : StepsTo oracle sPos s2 2 0 [] := by simpa using hst243.trans hst244
  refine (hpre2.prepend_pure h9).weaken (by have := cap_level_steps_sum; omega) (by omega)
    (fun h => by rwa [capFrontierPrefix_9] at h) (fun _ _ _ h => h)

/-- Epilogue (`pc[311..332]`): exact two-end exhaustion (`x25 == x31`, `x3 == 0`) and 4-dword root
comparison, `≤ 25` steps, `0` calls. -/
theorem step_epilogue (oracle : Oracle) (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (pFinal tFinal : Nat)
    (s : MachineState) (hpc : s.pc = pcWord 311)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pFinal tFinal s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s) :
    HaltsWith oracle s 25 0
      (if pFinal + tailBytes tFinal == input.proof.length &&
          tailBuf (submission.initialState .check input) input.proof.length tFinal == 0 &&
          readBuffer s (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))
       then Exit.success else Exit.failure) [] := by
  let s0 := submission.initialState .check input
  have hplen_bd : input.proof.length ≤ 8556390424 := hvalid
  have hple : pFinal + tailBytes tFinal ≤ input.proof.length := hcur.le
  -- pc[311]: BNE x25, x31, pc[330]
  have hst311 := step_ordinary oracle s 311 (.BNE .x25 .x31 76#13) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.BNE .x25 .x31 76#13)
  have hne_ptr : (s.getReg .x25 != s.getReg .x31) = decide (pFinal + tailBytes tFinal ≠ input.proof.length) := by
    rw [hcur.x25, hcur.x31, bv64_bne_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hpeq : pFinal + tailBytes tFinal = input.proof.length
  · have hpc1 : s1.pc = pcWord 312 := by
      simp only [s1, execInstrBr, hne_ptr, hpeq, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false, MachineState.setPC, hpc, pcWord_add_four]
    have hmem1 : s1.mem = s.mem := by
      simp [s1, execInstrBr, hne_ptr, hpeq, MachineState.setPC]
    have hreg1 : ∀ r, s1.getReg r = s.getReg r := fun r => by
      simp [s1, execInstrBr, hne_ptr, hpeq, MachineState.getReg_setPC]
    -- pc[312]: BNE x3, x0, pc[330]
    have hst312 := step_ordinary oracle s1 312 (.BNE .x3 .x0 72#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
    let s1b := execInstrBr s1 (.BNE .x3 .x0 72#13)
    have htb_lt : tailBuf s0 input.proof.length tFinal < 2 ^ 64 := by
      have h1 := tailBuf_lt s0 input.proof.length tFinal
      have h2 := tailCnt_lt8 tFinal
      have h3 : 2 ^ tailCnt tFinal ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      have h4 : 2 ^ 7 = 128 := by decide
      omega
    have hne_buf : (s1.getReg .x3 != s1.getReg .x0) = decide (tailBuf s0 input.proof.length tFinal ≠ 0) := by
      rw [hreg1 .x3, hcur.x3, getReg_x0, show (0#64 : Word) = BitVec.ofNat 64 0 from rfl,
        bv64_bne_eq _ 0 htb_lt (by omega)]
    by_cases hbuf0 : tailBuf s0 input.proof.length tFinal = 0
    · have hpc1b : s1b.pc = pcWord 313 := by
        simp only [s1b, execInstrBr, hne_buf, hbuf0, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ite_false, MachineState.setPC, hpc1, pcWord_add_four]
      have hmem1b : s1b.mem = s.mem := by
        simpa [s1b, execInstrBr, hne_buf, hbuf0, MachineState.setPC] using hmem1
      have hreg1b : ∀ r, s1b.getReg r = s.getReg r := fun r => by
        simpa [s1b, execInstrBr, hne_buf, hbuf0, MachineState.getReg_setPC] using hreg1 r
      -- pc[313]: LD x6, 792(x2); pc[314]: ADD x10, x19, x6
      have ha313 : s1b.getReg .x2 + signExtend12 792#12 = BitVec.ofNat 64 (68719475936 + (32 * 24 + 24)) := by
        rw [hreg1b .x2, hfix.x2, se12_792, bv64_add]
      have hv313 : memoryArgumentsValid s1b (.LD .x6 .x2 792#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha313]
        exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; decide) (by decide)
      have hst313 := step_ordinary oracle s1b 313 (.LD .x6 .x2 792#12) (by decide) hpc1b rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv313])
      let s2 := execInstrBr s1b (.LD .x6 .x2 792#12)
      have hpc2 : s2.pc = pcWord 314 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1b, pcWord_add_four]
      have hx6_2 : s2.getReg .x6 = BitVec.ofNat 64 (capValOff 24) := by
        simp only [s2, execInstrBr, MachineState.getReg_setPC, ha313]
        rw [MachineState.getReg_setReg_eq (by decide)]
        have hm : s1b.getMem (BitVec.ofNat 64 (68719475936 + (32 * 24 + 24))) =
            s.getMem (BitVec.ofNat 64 (68719475936 + (32 * 24 + 24))) := by simp [MachineState.getMem, hmem1b]
        rw [hm, hhigh.getMem_eq (by decide) (by decide) (by decide),
          check_initial_data_dword input hvalid (32 * 24 + 24) (by decide)]
        exact openingData_dword_3 ⟨24, by decide⟩
      have hst314 := step_ordinary oracle s2 314 (.ADD .x10 .x19 .x6) (by decide) hpc2 rfl (by intro h; cases h) rfl
      let s3 := execInstrBr s2 (.ADD .x10 .x19 .x6)
      have hpc3 : s3.pc = pcWord 315 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
      have hmem3 : s3.mem = s.mem := by simpa [s3, s2, execInstrBr, mem_setPC, mem_setReg] using hmem1b
      have hx10_3 : s3.getReg .x10 = BitVec.ofNat 64 (8192 + capValOff 24) := by
        simp only [s3, execInstrBr, MachineState.getReg_setPC]
        rw [MachineState.getReg_setReg_eq (by decide)]
        have h19_2 : s2.getReg .x19 = 8192#64 := by
          simp only [s2, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x19), hreg1b, hfix.x19]
        rw [h19_2, hx6_2]; change BitVec.ofNat 64 8192 + _ = _; exact bv64_add 8192 _
      have hx26_3 : s3.getReg .x26 = BitVec.ofNat 64 4294971392 := by
        simp only [s3, s2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
          ne_eq, not_false_eq_true, reduceCtorEq, hreg1b, hfix.x26]
      have hcmp_code : ∀ j < 4,
          checkInstr (315 + 3 * j) = .base (.LD .x6 .x10 (BitVec.ofNat 12 (8 * j))) ∧
          checkInstr (315 + 3 * j + 1) = .base (.LD .x7 .x26 (BitVec.ofNat 12 (8 * j))) ∧
          checkInstr (315 + 3 * j + 2) = .base (.BNE .x6 .x7 (BitVec.ofNat 13 (4 * (330 - (315 + 3 * j + 2))))) := by
        intro j hj; interval_cases j <;> exact ⟨rfl, rfl, rfl⟩
      have hcmp := step_compare4 oracle 315 .x10 .x26 s3 (8192 + capValOff 24) 4294971392
        (by decide) (by decide) (by decide) (by decide) (by decide) hcmp_code hpc3 hx10_3 hx26_3
        (by decide) (by decide) (by unfold MEMORY_BYTES; decide) (by unfold MEMORY_BYTES; decide)
      have hrb_root : readBuffer s3 (8192 + capValOff 24) 32 = readBuffer s (8192 + capValOff 24) 32 :=
        (MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by decide) (by omega)
      have hrb_cmt : readBuffer s3 4294971392 32 = input.commitment := by
        rw [(MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by decide) (by omega),
          hhigh.readBuffer_eq (by decide) (by omega), check_initial_commitment]
      have hs13 : StepsTo oracle s s3 4 0 [] := by simpa using ((hst311.trans hst312).trans hst313).trans hst314
      cases hcmp with
      | rejected k q tr hr hk hq hh =>
        rw [hrb_root, hrb_cmt] at hr
        have hbeq : (readBuffer s (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))) = false :=
          beq_eq_false_iff_ne.mpr hr
        have hif : (if pFinal + tailBytes tFinal == input.proof.length &&
            tailBuf s0 input.proof.length tFinal == 0 &&
            readBuffer s (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))
            then Exit.success else Exit.failure) = Exit.failure := by simp [hpeq, hbuf0, hbeq]
        rw [hif]
        have hqz : q = 0 := by omega
        subst hqz
        have htr_nil : tr = [] := by
          have h0 := hh.2 0
          have hnil := detExec_trace_nil_of_zero_calls oracle (submission.image .check) (k + 0) s3 h0.2.1
          rw [← h0.2.2, hnil]
        subst htr_nil
        exact (by simpa using hs13.halt hh : HaltsWith oracle s (4 + k) 0 .failure []).mono (by omega)
      | continued s4 k q tr hk hq hs4 hp4 =>
        obtain ⟨rfl, rfl, heq_dig, hpc4, _, _⟩ := hp4
        rw [hrb_root, hrb_cmt] at heq_dig
        have hbeq : (readBuffer s (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))) = true :=
          beq_iff_eq.mpr heq_dig
        have hif : (if pFinal + tailBytes tFinal == input.proof.length &&
            tailBuf s0 input.proof.length tFinal == 0 &&
            readBuffer s (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))
            then Exit.success else Exit.failure) = Exit.success := by simp [hpeq, hbuf0, hbeq]
        rw [hif]
        have htot := (hs13.trans hs4).halt (halt_accept oracle s4 hpc4)
        exact (by simpa using htot : HaltsWith oracle s (4 + k + 3) 0 .success []).mono (by omega)
    · have hbeq : (tailBuf s0 input.proof.length tFinal == 0) = false := beq_eq_false_iff_ne.mpr hbuf0
      have hif : (if pFinal + tailBytes tFinal == input.proof.length &&
          tailBuf s0 input.proof.length tFinal == 0 &&
          readBuffer s (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))
          then Exit.success else Exit.failure) = Exit.failure := by simp [hbeq]
      rw [hif]
      have hpc1b : s1b.pc = pcWord 330 := by
        simp only [s1b, execInstrBr, hne_buf, hbuf0, ne_eq, not_false_eq_true, decide_true,
          ite_true, MachineState.setPC, hpc1]; exact pc_312_branch
      exact (by simpa using (hst311.trans hst312).halt (halt_reject oracle s1b hpc1b) :
        HaltsWith oracle s 5 0 .failure []).mono (by decide)
  · have hbeq : (pFinal + tailBytes tFinal == input.proof.length) = false := beq_eq_false_iff_ne.mpr hpeq
    have hif : (if pFinal + tailBytes tFinal == input.proof.length &&
        tailBuf s0 input.proof.length tFinal == 0 &&
        readBuffer s (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))
        then Exit.success else Exit.failure) = Exit.failure := by simp [hbeq]
    rw [hif]
    have hpc1 : s1.pc = pcWord 330 := by
      simp only [s1, execInstrBr, hne_ptr, hpeq, ne_eq, not_false_eq_true, decide_true,
        ite_true, MachineState.setPC, hpc]; exact pc_311_branch
    exact (by simpa using hst311.halt (halt_reject oracle s1 hpc1) : HaltsWith oracle s 4 0 .failure []).mono (by decide)

end CommitGolfCandidate
