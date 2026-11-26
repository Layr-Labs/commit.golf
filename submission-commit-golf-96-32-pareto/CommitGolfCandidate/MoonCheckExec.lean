import CommitGolfCandidate.MoonCheckCapPair

/-! Symbolic execution of pure-binary cap-level composition, full bottom-up cap walk, and epilogue
(`pc[198..263]`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem pc_211_branch : pcWord 241 + signExtend13 8028#13 = pcWord 200 := by decide
private theorem pc_212_branch : pcWord 242 + signExtend13 76#13 = pcWord 261 := by decide
private theorem pc_213_branch : pcWord 243 + signExtend13 72#13 = pcWord 261 := by decide

/-- Complete cap-level step `l = 16 + step` (`step < 8`, `pc[200..241]`). -/
theorem step_cap_level (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (sPos : MachineState) (step : Nat) (hstep : step < 8)
    (s : MachineState) (trPrev : CompressionReplies)
    (hinv : CapWalkInv h768 oracle input sPos step s trPrev) :
    let l := 16 + step
    let pBase := posRecordOff input.positions.card input.positions.card
    let tBase := posTailOff input.positions.card
    PhaseOutcome oracle s (13 + 225 * (levelSize l / 2)) input.positions.card
      (input.proof.length <
        pBase + 29 * capFrontierPrefix input.positions (step + 1) +
        tailBytes (tBase + capFrontierPrefix input.positions (step + 1)))
      (fun s' calls tr =>
        calls ≤ input.positions.card ∧
        CapWalkInv h768 oracle input sPos (step + 1) s' (trPrev ++ tr)) := by
  intro l pBase tBase
  have hl1 : 16 ≤ l := by omega
  have hl2 : l < 24 := by omega
  have hplen_bd : input.proof.length ≤ 8239714016 := hvalid
  have hpc_s : s.pc = pcWord 200 := by have := hinv.pc; rwa [if_neg (by omega : step ≠ 8)] at this
  have hls_le : levelSize l ≤ 256 := levelSize_cap_le256 l hl1 hl2
  have hls_even : levelSize l % 2 = 0 := levelSize_even l hl2
  have hpairs_pos : 0 < levelSize l / 2 := levelSize_cap_pairs_pos l hl1 hl2
  have hmo_l_bd := capMarkOff_lt_4696 l hl1 (by omega)
  have hmo_n_bd := capMarkOff_lt_4696 (l + 1) (by omega) (by omega)
  have hvo_l_bd := capValOff_lt_25000 l hl1 (by omega)
  have hvo_n_bd := capValOff_lt_25000 (l + 1) (by omega) (by omega)
  have hvo_step := capValOff_step_eq l hl1 hl2
  have hvo_l_al := capValOff_mod8 l hl1 (by omega)
  have hvo_n_al := capValOff_mod8 (l + 1) (by omega) (by omega)
  have hmo_step := capMarkOff_step_le l hl1 hl2
  -- pc[200..210]: load level table fields (11 steps)
  let s0 := submission.initialState .check input
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hmem_data : ∀ (off : Nat) (hoff : off + 8 ≤ 800), off % 8 = 0 →
      s.getMem (BitVec.ofNat 64 (68719475936 + off)) =
        packedDword MoonArtifact.openingData off hoff := by
    intro off hoff hal
    rw [hinv.high.getMem_eq (by omega) (by omega) (by omega)]
    exact check_initial_data_dword input hvalid off hoff
  -- pc[200]: LD x20, 8(x29)
  have ha170 : s.getReg .x29 + signExtend12 8#12 = BitVec.ofNat 64 (68719475936 + (32 * l + 8)) := by
    rw [hinv.x29, se12_8]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 8 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv170 : memoryArgumentsValid s (.LD .x20 .x29 8#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha170]
    exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst170 := step_ordinary oracle s 200 (.LD .x20 .x29 8#12) (by decide) hpc_s rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv170])
  let s1 := execInstrBr s (.LD .x20 .x29 8#12)
  have hpc1 : s1.pc = pcWord 201 := by simp only [s1, execInstrBr, MachineState.setPC, hpc_s, pcWord_add_four]
  have hx20_1 : s1.getReg .x20 = BitVec.ofNat 64 (levelSize l) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, ha170]
    rw [MachineState.getReg_setReg_eq (by decide), hmem_data (32 * l + 8) (by omega) (by omega)]
    exact openingData_dword_1 ⟨l, by omega⟩
  have hmem1 : s1.mem = s.mem := by simp [s1, execInstrBr, mem_setPC, mem_setReg]
  -- pc[201..202]: LD x14, 16(x29); ADD x14, x18, x14
  have hx29_1 : s1.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x29), hinv.x29]
  have ha171 : s1.getReg .x29 + signExtend12 16#12 = BitVec.ofNat 64 (68719475936 + (32 * l + 16)) := by
    rw [hx29_1, se12_16]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 16 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv171 : memoryArgumentsValid s1 (.LD .x14 .x29 16#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha171]
    exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst171 := step_ordinary oracle s1 201 (.LD .x14 .x29 16#12) (by decide) hpc1 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv171])
  let s2 := execInstrBr s1 (.LD .x14 .x29 16#12)
  have hpc2 : s2.pc = pcWord 202 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hst172 := step_ordinary oracle s2 202 (.ADD .x14 .x18 .x14) (by decide) hpc2 rfl (by intro h; cases h) rfl
  let s3 := execInstrBr s2 (.ADD .x14 .x18 .x14)
  have hpc3 : s3.pc = pcWord 203 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
  have hmem3 : s3.mem = s.mem := by simpa [s3, s2, execInstrBr, mem_setPC, mem_setReg] using hmem1
  have hx14_3 : s3.getReg .x14 = BitVec.ofNat 64 (4096 + capMarkOff l) := by
    have h14_2 : s2.getReg .x14 = BitVec.ofNat 64 (capMarkOff l) := by
      simp only [s2, execInstrBr, MachineState.getReg_setPC, ha171]
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
  -- pc[203..204]: LD x15, 48(x29); ADD x15, x18, x15
  have hx29_3 : s3.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    simp only [s3, s2, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, hx29_1]
  have ha173 : s3.getReg .x29 + signExtend12 48#12 = BitVec.ofNat 64 (68719475936 + (32 * (l + 1) + 16)) := by
    rw [hx29_3, se12_48]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 48 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv173 : memoryArgumentsValid s3 (.LD .x15 .x29 48#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha173]
    exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst173 := step_ordinary oracle s3 203 (.LD .x15 .x29 48#12) (by decide) hpc3 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv173])
  let s4 := execInstrBr s3 (.LD .x15 .x29 48#12)
  have hpc4 : s4.pc = pcWord 204 := by simp only [s4, execInstrBr, MachineState.setPC, hpc3, pcWord_add_four]
  have hst174 := step_ordinary oracle s4 204 (.ADD .x15 .x18 .x15) (by decide) hpc4 rfl (by intro h; cases h) rfl
  let s5 := execInstrBr s4 (.ADD .x15 .x18 .x15)
  have hpc5 : s5.pc = pcWord 205 := by simp only [s5, execInstrBr, MachineState.setPC, hpc4, pcWord_add_four]
  have hmem5 : s5.mem = s.mem := by simpa [s5, s4, execInstrBr, mem_setPC, mem_setReg] using hmem3
  have hx15_5 : s5.getReg .x15 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) := by
    have h15_4 : s4.getReg .x15 = BitVec.ofNat 64 (capMarkOff (l + 1)) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC, ha173]
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
  -- pc[205..206]: LD x16, 24(x29); ADD x16, x19, x16
  have hx29_5 : s5.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    simp only [s5, s4, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, hx29_3]
  have ha175 : s5.getReg .x29 + signExtend12 24#12 = BitVec.ofNat 64 (68719475936 + (32 * l + 24)) := by
    rw [hx29_5, se12_24]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 24 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv175 : memoryArgumentsValid s5 (.LD .x16 .x29 24#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha175]
    exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst175 := step_ordinary oracle s5 205 (.LD .x16 .x29 24#12) (by decide) hpc5 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv175])
  let s6 := execInstrBr s5 (.LD .x16 .x29 24#12)
  have hpc6 : s6.pc = pcWord 206 := by simp only [s6, execInstrBr, MachineState.setPC, hpc5, pcWord_add_four]
  have hst176 := step_ordinary oracle s6 206 (.ADD .x16 .x19 .x16) (by decide) hpc6 rfl (by intro h; cases h) rfl
  let s7 := execInstrBr s6 (.ADD .x16 .x19 .x16)
  have hpc7 : s7.pc = pcWord 207 := by simp only [s7, execInstrBr, MachineState.setPC, hpc6, pcWord_add_four]
  have hmem7 : s7.mem = s.mem := by simpa [s7, s6, execInstrBr, mem_setPC, mem_setReg] using hmem5
  have hx16_7 : s7.getReg .x16 = BitVec.ofNat 64 (8192 + capValOff l) := by
    have h16_6 : s6.getReg .x16 = BitVec.ofNat 64 (capValOff l) := by
      simp only [s6, execInstrBr, MachineState.getReg_setPC, ha175]
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
  -- pc[207..210]: LD x17, 56(x29); ADD x17, x19, x17; SRLI x22, x20, 1; ADDI x23, x0, 0
  have hx29_7 : s7.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    simp only [s7, s6, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, hx29_5]
  have ha177 : s7.getReg .x29 + signExtend12 56#12 = BitVec.ofNat 64 (68719475936 + (32 * (l + 1) + 24)) := by
    rw [hx29_7, se12_56]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 56 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  have hv177 : memoryArgumentsValid s7 (.LD .x17 .x29 56#12) = true := by
    simp only [memoryArgumentsValid, memAccess, ha177]
    exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; omega) (by omega)
  have hst177 := step_ordinary oracle s7 207 (.LD .x17 .x29 56#12) (by decide) hpc7 rfl (by intro h; cases h)
    (by simp [ordinaryStep, hv177])
  let s8 := execInstrBr s7 (.LD .x17 .x29 56#12)
  have hpc8 : s8.pc = pcWord 208 := by simp only [s8, execInstrBr, MachineState.setPC, hpc7, pcWord_add_four]
  have hst178 := step_ordinary oracle s8 208 (.ADD .x17 .x19 .x17) (by decide) hpc8 rfl (by intro h; cases h) rfl
  let s9 := execInstrBr s8 (.ADD .x17 .x19 .x17)
  have hpc9 : s9.pc = pcWord 209 := by simp only [s9, execInstrBr, MachineState.setPC, hpc8, pcWord_add_four]
  have hst179 := step_ordinary oracle s9 209 (.SRLI .x22 .x20 1#6) (by decide) hpc9 rfl (by intro h; cases h) rfl
  let s10 := execInstrBr s9 (.SRLI .x22 .x20 1#6)
  have hpc10 : s10.pc = pcWord 210 := by simp only [s10, execInstrBr, MachineState.setPC, hpc9, pcWord_add_four]
  have hst180 := step_ordinary oracle s10 210 (.ADDI .x23 .x0 0#12) (by decide) hpc10 rfl (by intro h; cases h) rfl
  let s11 := execInstrBr s10 (.ADDI .x23 .x0 0#12)
  have hpc11 : s11.pc = pcWord 211 := by simp only [s11, execInstrBr, MachineState.setPC, hpc10, pcWord_add_four]
  have hmem11 : s11.mem = s.mem := by
    simpa [s11, s10, s9, s8, execInstrBr, mem_setPC, mem_setReg] using hmem7
  have hs_hdr : StepsTo oracle s s11 11 0 [] := by
    simpa using (((hst170.trans (hst171.trans hst172)).trans (hst173.trans hst174)).trans
      (hst175.trans hst176)).trans ((hst177.trans hst178).trans (hst179.trans hst180))
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
      simp only [s8, execInstrBr, MachineState.getReg_setPC, ha177]
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
          sn.pc = (if n = levelSize l / 2 then pcWord 240 else pcWord 211) ∧
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
          (∀ a, 4096 + capMarkOff (l + 1) + n ≤ a → a < 4696 → sn.getByte (BitVec.ofNat 64 a) = 0#8) ∧
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
            (capMark input.positions l (2 * q) = false → dL = proofDigest238 s0 input.proof.length (10603204576 + pAt) tAt) ∧
            (capMark input.positions l (2 * q + 1) = false → dR = proofDigest238 s0 input.proof.length (10603204576 + pAt) tAt))) := by
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
        have hpc_q : sq.pc = pcWord 211 := by rwa [if_neg (by omega : q ≠ levelSize l / 2)] at hpc1
        let pCur := pLvl + 29 * pairFrontierCount input.positions l q
        let tCur := tLvl + pairFrontierCount input.positions l q
        have hp_pair := step_cap_pair h768 oracle input hvalid l q pCur tCur hl1 hl2 hq_lt
          sq hpc_q hfix1 hcur1 hhigh1 h20 h14 h15 h16 h17 h22 h23 h29 h30
          (hmkL (2 * q) (by omega)) (hmkL (2 * q + 1) (by omega))
          (hmkHi (4096 + capMarkOff (l + 1) + q) (by omega) (by have := levelSize_step l hl2; omega))
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
  -- Chain header (11 steps) + pair loop (225 * pairs) + loop end (2 steps)
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
    (K1 := 11 + (225 * (levelSize l / 2) + 2))
    (Q1 := pairMarkedNextCount input.positions l (levelSize l / 2) + 0)
    ?_ (by omega) (by have := pairMarkedNextCount_le_card input.positions l hl1 hl2; omega) id (fun _ _ _ h => h)
  refine hs_hdr.prepend_pure ?_
  refine hpairs_res.bind_dep hcan_lvl (fun sP qP trP ⟨hqP, hpcP, hfixP, hcurP, hhighP,
          h20, h14, h15, h16, h17, h22, h23, h29, h30, hmkL, hmkN, hmkHi, _, hpresP, hdoneP⟩ => by
        rw [if_pos rfl] at hpcP
        rw [hpoff_next, htoff_next] at hcurP
        -- pc[240..241]: ADDI x29, x29, 32; BNE x29, x30, pc[200]
        have hst210 := step_ordinary oracle sP 240 (.ADDI .x29 .x29 32#12) (by decide) hpcP rfl (by intro h; cases h) rfl
        let s211 := execInstrBr sP (.ADDI .x29 .x29 32#12)
        have hpc211 : s211.pc = pcWord 241 := by simp only [s211, execInstrBr, MachineState.setPC, hpcP, pcWord_add_four]
        have hmem211 : s211.mem = sP.mem := by simp [s211, execInstrBr, mem_setPC, mem_setReg]
        have hx29_211 : s211.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (16 + (step + 1))) := by
          simp only [s211, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide), h29, se12_32]
          change BitVec.ofNat 64 _ + BitVec.ofNat 64 32 = _; rw [bv64_add]; exact congrArg (BitVec.ofNat 64) (by omega)
        have hx30_211 : s211.getReg .x30 = BitVec.ofNat 64 (68719475936 + 768) := by
          simp only [s211, execInstrBr, MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x30), h30]
        obtain ⟨sFin, hst211, hpcFin_raw, hregFin_211, hmemFin_211⟩ :=
          step_bne_reg oracle 241 200 .x29 .x30 8028#13 (by decide) rfl pc_211_branch s211
            (68719475936 + 32 * (16 + (step + 1))) (68719475936 + 768) (by omega) (by omega) hpc211 hx29_211 hx30_211
        have hpcFin : sFin.pc = if step + 1 = 8 then pcWord 242 else pcWord 200 := by
          rw [hpcFin_raw]; congr 1; exact propext (by omega)
        have hmemFin : sFin.mem = sP.mem := hmemFin_211.trans hmem211
        have hregFin : ∀ r, r ≠ .x29 → sFin.getReg r = sP.getReg r := fun r h29r => by
          rw [hregFin_211 r]; simp only [s211, execInstrBr, MachineState.getReg_setPC]
          exact MachineState.getReg_setReg_ne _ _ _ _ h29r.symm
        have hls_next : levelSize (l + 1) = levelSize l / 2 := levelSize_step l hl2
        have hfin_s : ∀ a : Nat, a < 2 ^ 64 →
            (a < 4096 + capMarkOff (l + 1) ∨ 4096 + capMarkOff (l + 1) + levelSize (l + 1) ≤ a) →
            (∀ idx < levelSize l, capMark input.positions l idx = false →
              a < 8192 + capValOff l + gapOffset idx ∨ 8192 + capValOff l + gapOffset idx + 32 ≤ a) →
            (∀ idx < levelSize (l + 1), capMark input.positions (l + 1) idx = true →
              a < 8192 + capValOff (l + 1) + gapOffset idx ∨ 8192 + capValOff (l + 1) + gapOffset idx + 32 ≤ a) →
            sFin.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a) := fun a ha hmk hunm hdst => by
          have h1 : sFin.getByte (BitVec.ofNat 64 a) = sP.getByte (BitVec.ofNat 64 a) := by
            simp [MachineState.getByte, MachineState.getMem, hmemFin]
          rw [h1]
          exact hpresP a ha (by omega)
            (fun q hq idx hi hm => hunm idx (by omega) hm)
            (fun q hq hcm => hdst q (by omega) hcm)
        have hcalls_le : qP ≤ input.positions.card :=
          hqP.trans (pairMarkedNextCount_le_card input.positions l hl1 hl2)
        refine PhaseOutcome.continued sFin 2 0 [] (by decide) (by decide)
          (by simpa [Nat.add_assoc] using hst210.trans hst211) ?_
        refine ⟨by simpa using hcalls_le, ?_⟩
        refine ⟨hfixP.of_agree (fun r hr => hregFin r (isFixedReg_ne_of_false hr rfl)),
          hcurP.of_agree (fun r hr => hregFin r (isCursorReg_ne_of_false hr rfl)),
          ?_, hpcFin, (hregFin_211 .x29).trans hx29_211,
          (hregFin .x30 (by decide)).trans h30, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · -- HighMemPreserved
          intro a ha hge
          exact (hfin_s a ha (Or.inr (by omega))
            (fun idx hidx _ => Or.inr (by have := cap_gapOffset_bound l idx hl1 (by omega) hidx; omega))
            (fun idx hidx _ => Or.inr (by have := cap_val_next_bound l idx hl1 hl2 hidx; omega))).trans
            (hinv.high a ha hge)
        · -- mark_cur for step + 1
          intro hstep1 idx hidx
          have hl1_eq : 16 + (step + 1) = l + 1 := by omega
          rw [hl1_eq] at hidx ⊢
          have : sFin.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + idx)) =
              sP.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + idx)) := by
            simp [MachineState.getByte, MachineState.getMem, hmemFin]
          rw [this]
          exact hmkN idx (by omega)
        · -- mark_hi_zero for step + 1
          intro hstep1 a ha1 ha2
          have hl2_eq : 16 + (step + 1) + 1 = l + 2 := by omega
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
          have hl1_eq : 16 + (step + 1) = l + 1 := by omega
          rw [hl1_eq] at hq' ⊢
          have hgap_bd : capValOff (l + 1) + 96 * q' + 64 + b < 25000 := by
            have hlt : 96 * q' + 96 ≤ levelBytes (l + 1) := by
              unfold levelBytes
              have hlt24 : l + 1 < 24 := by omega
              simp only [hlt24, ite_true]; omega
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
          have hl2_eq : 16 + (step + 1) + 1 = l + 2 := by omega
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
        · -- val16_marked preserved
          intro c hc hcm16
          have hpres_16 : readBuffer sFin (8192 + capValOff 16 + gapOffset c) 32 =
              readBuffer s (8192 + capValOff 16 + gapOffset c) 32 := by
            have h16 : capValOff 16 = 0 := by decide
            have h17 : capValOff 17 = 12288 := by decide
            apply readBuffer_congr2; intro b hb
            have hc_bd : gapOffset c + 32 ≤ 12288 := by unfold gapOffset; omega
            refine hfin_s (8192 + capValOff 16 + gapOffset c + b) (by omega) (Or.inr (by omega)) ?_ ?_
            · intro idx0 hidx0 hunm0
              by_cases hs0 : step = 0
              · have hl16 : l = 16 := by omega
                rw [hl16] at hunm0 ⊢
                have hne : c ≠ idx0 := fun h => by rw [h, hunm0] at hcm16; cases hcm16
                have := gapOffset_disjoint hne; omega
              · left
                have hm := capValOff_mono (by decide) (show 17 ≤ l by omega) (by omega)
                omega
            · intro idx1 _ _
              left
              have hm := capValOff_mono (by decide) (show 17 ≤ l + 1 by omega) (by omega)
              omega
          exact hpres_16.trans (hinv.val16_marked c hc hcm16)
        · -- levels_done for d < step + 1
          intro d hd
          by_cases hd_lt : d < step
          · -- Earlier level d < step: preserve all reads from s
            have hprev_p := hinv.levels_done d hd_lt
            let ld := 16 + d
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
            dsimp only
            intro q hq hcm
            change q < levelSize ld / 2 at hq
            obtain ⟨hv, htr, hfL, hfR⟩ := hprev_p q hq hcm
            have hq_next : q < levelSize (ld + 1) := by rw [levelSize_step ld (by omega)]; omega
            have hld_even := levelSize_even ld (by omega)
            rw [hpres_low (2 * q) (by omega), hpres_low (2 * q + 1) (by omega), hpres_hi q hq_next hcm]
            exact ⟨hv, htr.append_left, hfL, hfR⟩
          · -- Current level d = step
            have hdeq : d = step := by omega
            subst hdeq
            dsimp only
            intro q hq hcm
            obtain ⟨hv, htr, hfL, hfR⟩ := hdoneP q hq hcm
            have hrb_eq : ∀ addr n, readBuffer sFin addr n = readBuffer sP addr n := fun addr n => by
              apply readBuffer_congr2; intro b _; simp [MachineState.getByte, MachineState.getMem, hmemFin]
            rw [hrb_eq, hrb_eq, hrb_eq]
            exact ⟨hv, by simpa only [List.append_nil] using htr.append_right,
              by simpa only [pLvl, tLvl, Nat.mul_add, Nat.add_assoc] using hfL,
              by simpa only [pLvl, tLvl, Nat.mul_add, Nat.add_assoc] using hfR⟩)

/-- Complete bottom-up cap walk from `pc[198]` to `pc[242]` (`≤ 60000` steps, `≤ 8 * k` calls). -/
theorem step_cap_walk (h768 : COMPRESSION_INPUT_LENGTH = 768) (oracle : Oracle)
    (input : CheckInput) (hvalid : input.proof.length ≤ submission.sizes.proof)
    (sPos : MachineState) (trPos : CompressionReplies)
    (hpos : PosLoopInv h768 oracle input input.positions.card sPos trPos) :
    let pBase := posRecordOff input.positions.card input.positions.card
    let tBase := posTailOff input.positions.card
    PhaseOutcome oracle sPos 60000 (8 * input.positions.card)
      (input.proof.length <
        pBase + 29 * capFrontierCount input.positions +
        tailBytes (tBase + capFrontierCount input.positions))
      (fun sCap calls trCap =>
        calls ≤ 8 * input.positions.card ∧
        CapWalkInv h768 oracle input sPos 8 sCap trCap) := by
  intro pBase tBase
  -- pc[198..199]: ADDI x29, x2, 512; ADDI x30, x2, 768
  have hpc168 : sPos.pc = pcWord 198 := by have := hpos.pc; rwa [if_pos rfl] at this
  have hst168 := step_ordinary oracle sPos 198 (.ADDI .x29 .x2 512#12) (by decide) hpc168 rfl (by intro h; cases h) rfl
  let s1 := execInstrBr sPos (.ADDI .x29 .x2 512#12)
  have hpc1 : s1.pc = pcWord 199 := by simp only [s1, execInstrBr, MachineState.setPC, hpc168, pcWord_add_four]
  have hst169 := step_ordinary oracle s1 199 (.ADDI .x30 .x2 768#12) (by decide) hpc1 rfl (by intro h; cases h) rfl
  let s2 := execInstrBr s1 (.ADDI .x30 .x2 768#12)
  have hpc2 : s2.pc = pcWord 200 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1, pcWord_add_four]
  have hmem2 : s2.mem = sPos.mem := by simp [s2, s1, execInstrBr, mem_setPC, mem_setReg]
  have hreg2 : ∀ r, r ≠ .x29 → r ≠ .x30 → s2.getReg r = sPos.getReg r := fun r h29 h30 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ h30.symm, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ h29.symm]
  have hx29_2 : s2.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 16) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hpos.fixed.x2, se12_512]
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
        rw [show capMarkOff 16 = 0 by decide, Nat.add_zero]
        rw [levelSize_16] at hidx
        have hb : s2.getByte (BitVec.ofNat 64 (4096 + idx)) = sPos.getByte (BitVec.ofNat 64 (4096 + idx)) := by
          simp only [MachineState.getByte, MachineState.getMem, hmem2]
        rw [hb]
        simpa only [posMarked16_card_eq_capMark] using hpos.mark16 idx hidx,
      fun _ a ha1 ha2 => by
        rw [show capMarkOff 17 = 256 by decide] at ha1
        simp only [MachineState.getByte, MachineState.getMem, hmem2]
        exact hpos.mark_hi_zero a (by omega) ha2,
      fun _ q hq b hb => by
        rw [show capValOff 16 = 0 by decide, Nat.add_zero]
        rw [show levelSize 16 / 2 = 128 by decide] at hq
        simp only [MachineState.getByte, MachineState.getMem, hmem2]
        exact hpos.val16_gap_zero q hq b hb,
      fun _ a ha1 ha2 => by
        simp only [MachineState.getByte, MachineState.getMem, hmem2]
        exact hpos.val_hi_zero a ha1 ha2,
      fun c _ _ => by
        rw [show capValOff 16 = 0 by decide, Nat.add_zero]
        apply readBuffer_congr2; intro b _; simp [MachineState.getByte, MachineState.getMem, hmem2],
      fun _ h => (Nat.not_lt_zero _ h).elim⟩
  have hind : ∀ n ≤ 8,
      PhaseOutcome oracle s2 (∑ d ∈ Finset.range n, (13 + 225 * (levelSize (16 + d) / 2)))
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
  have h8 := hind 8 (le_refl 8)
  have hpre2 : StepsTo oracle sPos s2 2 0 [] := by simpa using hst168.trans hst169
  refine (hpre2.prepend_pure h8).weaken (by have := cap_level_steps_sum; omega) (by omega)
    (fun h => by rwa [capFrontierPrefix_8] at h) (fun _ _ _ h => h)

/-- Epilogue (`pc[242..263]`): exact two-end exhaustion (`x25 == x31`, `x3 == 0`) and 4-dword root
comparison, `≤ 25` steps, `0` calls. -/
theorem step_epilogue (oracle : Oracle) (input : CheckInput)
    (hvalid : input.proof.length ≤ submission.sizes.proof)
    (pFinal tFinal : Nat)
    (s : MachineState) (hpc : s.pc = pcWord 242)
    (hfix : CheckFixedRegs s)
    (hcur : ProofCursor (submission.initialState .check input) input.proof.length pFinal tFinal s)
    (hhigh : HighMemPreserved (submission.initialState .check input) s) :
    HaltsWith oracle s 25 0
      (if pFinal + tailBytes tFinal == input.proof.length &&
          tailBuf (submission.initialState .check input) input.proof.length tFinal == 0 &&
          readBuffer s (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))
       then Exit.success else Exit.failure) [] := by
  let s0 := submission.initialState .check input
  have hplen_bd : input.proof.length ≤ 8239714016 := hvalid
  have hple : pFinal + tailBytes tFinal ≤ input.proof.length := hcur.le
  -- pc[242]: BNE x25, x31, pc[261]
  have hst212 := step_ordinary oracle s 242 (.BNE .x25 .x31 76#13) (by decide) hpc rfl (by intro h; cases h) rfl
  let s1 := execInstrBr s (.BNE .x25 .x31 76#13)
  have hne_ptr : (s.getReg .x25 != s.getReg .x31) = decide (pFinal + tailBytes tFinal ≠ input.proof.length) := by
    rw [hcur.x25, hcur.x31, bv64_bne_eq _ _ (by omega) (by omega)]
    exact decide_eq_decide.mpr (by omega)
  by_cases hpeq : pFinal + tailBytes tFinal = input.proof.length
  · have hpc1 : s1.pc = pcWord 243 := by
      simp only [s1, execInstrBr, hne_ptr, hpeq, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false, MachineState.setPC, hpc, pcWord_add_four]
    have hmem1 : s1.mem = s.mem := by
      simp [s1, execInstrBr, hne_ptr, hpeq, MachineState.setPC]
    have hreg1 : ∀ r, s1.getReg r = s.getReg r := fun r => by
      simp [s1, execInstrBr, hne_ptr, hpeq, MachineState.getReg_setPC]
    -- pc[243]: BNE x3, x0, pc[261]
    have hst213 := step_ordinary oracle s1 243 (.BNE .x3 .x0 72#13) (by decide) hpc1 rfl (by intro h; cases h) rfl
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
    · have hpc1b : s1b.pc = pcWord 244 := by
        simp only [s1b, execInstrBr, hne_buf, hbuf0, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ite_false, MachineState.setPC, hpc1, pcWord_add_four]
      have hmem1b : s1b.mem = s.mem := by
        simpa [s1b, execInstrBr, hne_buf, hbuf0, MachineState.setPC] using hmem1
      have hreg1b : ∀ r, s1b.getReg r = s.getReg r := fun r => by
        simpa [s1b, execInstrBr, hne_buf, hbuf0, MachineState.getReg_setPC] using hreg1 r
      -- pc[244]: LD x6, 792(x2); pc[245]: ADD x10, x19, x6
      have ha214 : s1b.getReg .x2 + signExtend12 792#12 = BitVec.ofNat 64 (68719475936 + (32 * 24 + 24)) := by
        rw [hreg1b .x2, hfix.x2, se12_792, bv64_add]
      have hv214 : memoryArgumentsValid s1b (.LD .x6 .x2 792#12) = true := by
        simp only [memoryArgumentsValid, memAccess, ha214]
        exact accessValid_ofNat _ 8 (by unfold MEMORY_BYTES; omega) (by decide)
      have hst214 := step_ordinary oracle s1b 244 (.LD .x6 .x2 792#12) (by decide) hpc1b rfl (by intro h; cases h)
        (by simp [ordinaryStep, hv214])
      let s2 := execInstrBr s1b (.LD .x6 .x2 792#12)
      have hpc2 : s2.pc = pcWord 245 := by simp only [s2, execInstrBr, MachineState.setPC, hpc1b, pcWord_add_four]
      have hx6_2 : s2.getReg .x6 = BitVec.ofNat 64 (capValOff 24) := by
        simp only [s2, execInstrBr, MachineState.getReg_setPC, ha214]
        rw [MachineState.getReg_setReg_eq (by decide)]
        have hm : s1b.getMem (BitVec.ofNat 64 (68719475936 + (32 * 24 + 24))) =
            s.getMem (BitVec.ofNat 64 (68719475936 + (32 * 24 + 24))) := by simp [MachineState.getMem, hmem1b]
        rw [hm, hhigh.getMem_eq (by decide) (by omega) (by omega),
          check_initial_data_dword input hvalid (32 * 24 + 24) (by decide)]
        exact openingData_dword_3 ⟨24, by decide⟩
      have hst215 := step_ordinary oracle s2 245 (.ADD .x10 .x19 .x6) (by decide) hpc2 rfl (by intro h; cases h) rfl
      let s3 := execInstrBr s2 (.ADD .x10 .x19 .x6)
      have hpc3 : s3.pc = pcWord 246 := by simp only [s3, execInstrBr, MachineState.setPC, hpc2, pcWord_add_four]
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
          checkInstr (246 + 3 * j) = .base (.LD .x6 .x10 (BitVec.ofNat 12 (8 * j))) ∧
          checkInstr (246 + 3 * j + 1) = .base (.LD .x7 .x26 (BitVec.ofNat 12 (8 * j))) ∧
          checkInstr (246 + 3 * j + 2) = .base (.BNE .x6 .x7 (BitVec.ofNat 13 (4 * (261 - (246 + 3 * j + 2))))) := by
        intro j hj; interval_cases j <;> exact ⟨rfl, rfl, rfl⟩
      have hcap24_bd := capValOff_lt_25000 24 (by decide) (by decide)
      have hcap24_al := capValOff_mod8 24 (by decide) (by decide)
      have hcmp := step_compare4 oracle 246 .x10 .x26 s3 (8192 + capValOff 24) 4294971392
        (by decide) (by decide) (by decide) (by decide) (by decide) hcmp_code hpc3 hx10_3 hx26_3
        (by omega) (by decide) (by unfold MEMORY_BYTES; omega) (by unfold MEMORY_BYTES; omega)
      have hrb_root : readBuffer s3 (8192 + capValOff 24) 32 = readBuffer s (8192 + capValOff 24) 32 :=
        (MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by omega) (by omega)
      have hrb_cmt : readBuffer s3 4294971392 32 = input.commitment := by
        rw [(MemEqOutside.of_mem_eq hmem3 0 0).readBuffer_eq (by omega) (by omega),
          hhigh.readBuffer_eq (by omega) (by omega), check_initial_commitment]
      have hs13 : StepsTo oracle s s3 4 0 [] := by simpa using ((hst212.trans hst213).trans hst214).trans hst215
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
      have hpc1b : s1b.pc = pcWord 261 := by
        simp only [s1b, execInstrBr, hne_buf, hbuf0, ne_eq, not_false_eq_true, decide_true,
          ite_true, MachineState.setPC, hpc1]; exact pc_213_branch
      exact (by simpa using (hst212.trans hst213).halt (halt_reject oracle s1b hpc1b) :
        HaltsWith oracle s 5 0 .failure []).mono (by decide)
  · have hbeq : (pFinal + tailBytes tFinal == input.proof.length) = false := beq_eq_false_iff_ne.mpr hpeq
    have hif : (if pFinal + tailBytes tFinal == input.proof.length &&
        tailBuf s0 input.proof.length tFinal == 0 &&
        readBuffer s (8192 + capValOff 24) 32 == (input.commitment : BitVec (8 * 32))
        then Exit.success else Exit.failure) = Exit.failure := by simp [hbeq]
    rw [hif]
    have hpc1 : s1.pc = pcWord 261 := by
      simp only [s1, execInstrBr, hne_ptr, hpeq, ne_eq, not_false_eq_true, decide_true,
        ite_true, MachineState.setPC, hpc]; exact pc_212_branch
    exact (by simpa using hst212.halt (halt_reject oracle s1 hpc1) : HaltsWith oracle s 4 0 .failure []).mono (by decide)

end CommitGolfCandidate
