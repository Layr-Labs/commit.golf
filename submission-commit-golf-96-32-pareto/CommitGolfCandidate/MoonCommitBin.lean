import CommitGolfCandidate.MoonCommitBinA

/-! Header, Tail, and top-level level-driver proofs for both binary phases of the pure-binary
`commit` image (zero odd-node promotion edge cases):
- `commit_bin_level` (Phase 3A, 240-bit masked, `L0 -> L1`, words `3624..4163`)
- `commit_bin238_level` (Phase 3B, 238-bit masked, `L1..L22 -> L2..L23`, words `4168..4967`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Isolated Branch Targets -/

private theorem pc_beq_3632 :
    BitVec.ofNat 64 (0x1000 + 4 * 3632) + signExtend13 (2072#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 4150) := by decide

private theorem pc_bne_4163 :
    BitVec.ofNat 64 (0x1000 + 4 * 4163) + signExtend13 (6036#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 3624) := by decide

private theorem pc_beq_4176 :
    BitVec.ofNat 64 (0x1000 + 4 * 4176) + signExtend13 (3096#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 4950) := by decide

private theorem pc_bne_4967 :
    BitVec.ofNat 64 (0x1000 + 4 * 4967) + signExtend13 (4996#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 4168) := by decide

/-! ### 2. Parameterized Header (9 instructions) and Loop Tail (2 instructions) -/

private theorem commit_bin_header_ptrs_gen (oracle : Oracle) (pcHdr lvlIdx : Nat) (hlvl : lvlIdx < 23)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * pcHdr))
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * lvlIdx))
    (hd0 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx)) = BitVec.ofNat 64 (levelBase lvlIdx))
    (hd1 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + 8)) = BitVec.ofNat 64 (levelBase (lvlIdx + 1)))
    (hf0 : fetch (submission.image .commit) s0 = some (.base (.LD .x6 .x24 (0#12))))
    (hf1 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 1)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x10 .x9 .x6)))
    (hf2 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 2)) →
      fetch (submission.image .commit) st = some (.base (.ADDI .x10 .x10 (4000#12))))
    (hf3 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 3)) →
      fetch (submission.image .commit) st = some (.base (.LD .x6 .x24 (8#12))))
    (hf4 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 4)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x12 .x9 .x6)))
    (hf5 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 5)) →
      fetch (submission.image .commit) st = some (.base (.ADDI .x12 .x12 (4032#12)))) :
    ∃ h5,
      DetRun oracle (submission.image .commit) s0 6 h5 6 0 ∧
      h5.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 6)) ∧
      h5.mem = s0.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → h5.getReg r = s0.getReg r) ∧
      h5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase lvlIdx - 96) ∧
      h5.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 64) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let h0 := execInstrBr s0 (.LD .x6 .x24 (0#12))
  let h1 := execInstrBr h0 (.ADD .x10 .x9 .x6)
  let h2 := execInstrBr h1 (.ADDI .x10 .x10 (4000#12))
  let h3 := execInstrBr h2 (.LD .x6 .x24 (8#12))
  let h4 := execInstrBr h3 (.ADD .x12 .x9 .x6)
  let h5 := execInstrBr h4 (.ADDI .x12 .x12 (4032#12))
  have hh0_pc : h0.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 1)) := pc_step_idx s0 pcHdr hpc
  have hh1_pc : h1.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 2)) := pc_step_idx h0 (pcHdr + 1) hh0_pc
  have hh2_pc : h2.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 3)) := pc_step_idx h1 (pcHdr + 2) hh1_pc
  have hh3_pc : h3.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 4)) := pc_step_idx h2 (pcHdr + 3) hh2_pc
  have hh4_pc : h4.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 5)) := pc_step_idx h3 (pcHdr + 4) hh3_pc
  have hh5_pc : h5.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 6)) := pc_step_idx h4 (pcHdr + 5) hh4_pc
  have hh2_mem : h2.mem = s0.mem :=
    ((mem_exec_ADDI h1 _ _ _).trans (mem_exec_ADD h0 _ _ _)).trans (mem_exec_LD s0 _ _ _)
  have hh5_mem : h5.mem = s0.mem :=
    (((mem_exec_ADDI h4 _ _ _).trans (mem_exec_ADD h3 _ _ _)).trans (mem_exec_LD h2 _ _ _)).trans hh2_mem
  have hh2_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → h2.getReg r = s0.getReg r := fun r h6r h10r => by
    simp only [h2, h1, h0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x10 r (Ne.symm h10r), getReg_setReg_ne' .x6 r (Ne.symm h6r)]
  have hh5_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → h5.getReg r = s0.getReg r :=
    fun r h6r h10r h12r => by
      have h52 : h5.getReg r = h2.getReg r := by
        simp only [h5, h4, h3, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x12 r (Ne.symm h12r), getReg_setReg_ne' .x6 r (Ne.symm h6r)]
      exact h52.trans (hh2_reg_other r h6r h10r)
  have hh0_addr : s0.getReg .x24 + signExtend12 (0#12) = BitVec.ofNat 64 (C_DB + 32 * lvlIdx) := by
    rw [hx24, add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
  have hh3_addr : h2.getReg .x24 + signExtend12 (8#12) = BitVec.ofNat 64 (C_DB + 32 * lvlIdx + 8) := by
    rw [hh2_reg_other .x24 (by decide) (by decide), hx24, add_signExtend12_ofNat_small _ 8 (by omega)]
  have hrun : DetRun oracle (submission.image .commit) s0 6 h5 6 0 := by
    have r0 : DetRun oracle (submission.image .commit) s0 1 h0 1 0 :=
      DetRun.step1 hf0 (ordinaryStep_LD s0 .x6 .x24 (0#12) (by rw [hh0_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have r1 : DetRun oracle (submission.image .commit) h0 1 h1 1 0 := DetRun.step1 (hf1 h0 hh0_pc) rfl
    have r2 : DetRun oracle (submission.image .commit) h1 1 h2 1 0 := DetRun.step1 (hf2 h1 hh1_pc) rfl
    have r3 : DetRun oracle (submission.image .commit) h2 1 h3 1 0 :=
      DetRun.step1 (hf3 h2 hh2_pc) (ordinaryStep_LD h2 .x6 .x24 (8#12) (by rw [hh3_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have r4 : DetRun oracle (submission.image .commit) h3 1 h4 1 0 := DetRun.step1 (hf4 h3 hh3_pc) rfl
    have r5 : DetRun oracle (submission.image .commit) h4 1 h5 1 0 := DetRun.step1 (hf5 h4 hh4_pc) rfl
    exact ((((r0.trans r1).trans r2).trans r3).trans r4).trans r5
  have hh5_x10 : h5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase lvlIdx - 96) := by
    have h06 : h0.getReg .x6 = BitVec.ofNat 64 (levelBase lvlIdx) := by
      simp only [h0, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hh0_addr, hd0]
    have h110 : h1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase lvlIdx) := by
      have : h0.getReg .x9 = BitVec.ofNat 64 C_TD := by
        simp only [h0, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x9 (by decide), hx9]
      simp only [h1, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), this, h06, ← BitVec.ofNat_add]
    have h210 : h2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase lvlIdx - 96) := by
      simp only [h2, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), h110]
      exact bv64_add_neg96 (C_TD + levelBase lvlIdx) (by omega)
    simp only [h5, h4, h3, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 .x10 (by decide), getReg_setReg_ne' .x6 .x10 (by decide), h210]
  have hh5_x12 : h5.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 64) := by
    have h2mem : ∀ a, h2.getMem a = s0.getMem a := fun a => by simp only [MachineState.getMem, hh2_mem]
    have h36 : h3.getReg .x6 = BitVec.ofNat 64 (levelBase (lvlIdx + 1)) := by
      simp only [h3, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hh3_addr, h2mem, hd1]
    have h412 : h4.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1)) := by
      have h39 : h3.getReg .x9 = BitVec.ofNat 64 C_TD := by
        simp only [h3, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x9 (by decide),
          hh2_reg_other .x9 (by decide) (by decide), hx9]
      simp only [h4, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h39, h36, ← BitVec.ofNat_add]
    simp only [h5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h412]
    exact bv64_add_neg64 (C_TD + levelBase (lvlIdx + 1)) (by omega)
  exact ⟨h5, hrun, hh5_pc, hh5_mem, hh5_reg_other, hh5_x10, hh5_x12⟩

private theorem commit_bin_header_gen (oracle : Oracle) (msg : Message)
    (pcHdr pcA pcB : Nat) (beqImm : BitVec 13)
    (hpc_A : pcHdr + 9 = pcA)
    (hbeq_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 8)) + signExtend13 beqImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcB))
    (lvlIdx outPairs chunks : Nat) (hlvl : lvlIdx < 23)
    (hout : outPairs = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = outPairs / 64)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * pcHdr))
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * lvlIdx))
    (hdata : ∀ off < 32, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + off)) =
        (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + off)))
    (hf0 : fetch (submission.image .commit) s0 = some (.base (.LD .x6 .x24 (0#12))))
    (hf1 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 1)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x10 .x9 .x6)))
    (hf2 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 2)) →
      fetch (submission.image .commit) st = some (.base (.ADDI .x10 .x10 (4000#12))))
    (hf3 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 3)) →
      fetch (submission.image .commit) st = some (.base (.LD .x6 .x24 (8#12))))
    (hf4 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 4)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x12 .x9 .x6)))
    (hf5 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 5)) →
      fetch (submission.image .commit) st = some (.base (.ADDI .x12 .x12 (4032#12))))
    (hf6 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 6)) →
      fetch (submission.image .commit) st = some (.base (.LD .x20 .x24 (16#12))))
    (hf7 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 7)) →
      fetch (submission.image .commit) st = some (.base (.SRLI .x22 .x20 (6#6))))
    (hf8 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 8)) →
      fetch (submission.image .commit) st = some (.base (.BEQ .x22 .x0 beqImm))) :
    ∃ h8,
      DetRun oracle (submission.image .commit) s0 9 h8 9 0 ∧
      h8.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then pcA else pcB)) ∧
      h8.mem = s0.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x20 → r ≠ .x22 →
        h8.getReg r = s0.getReg r) ∧
      h8.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase lvlIdx - 96) ∧
      h8.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 64) ∧
      h8.getReg .x20 = BitVec.ofNat 64 outPairs ∧
      h8.getReg .x22 = BitVec.ofNat 64 chunks := by
  have hC_DB : C_DB = 68719476000 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hdstSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  have hd0 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx)) = BitVec.ofNat 64 (levelBase lvlIdx) := by
    have h := hdata 0 (by omega) (by omega); simp only [Nat.add_zero] at h
    rw [h, commit_initial_data_dword msg (32 * lvlIdx) (by omega)]; exact commitData_dword_0 ⟨lvlIdx, hlvl⟩
  have hd1 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + 8)) = BitVec.ofNat 64 (levelBase (lvlIdx + 1)) := by
    rw [hdata 8 (by omega) (by omega), Nat.add_assoc, commit_initial_data_dword msg (32 * lvlIdx + 8) (by omega)]
    exact commitData_dword_1 ⟨lvlIdx, hlvl⟩
  have hd2 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + 16)) = BitVec.ofNat 64 outPairs := by
    rw [hdata 16 (by omega) (by omega), Nat.add_assoc, commit_initial_data_dword msg (32 * lvlIdx + 16) (by omega), hout]
    exact commitData_dword_2 ⟨lvlIdx, hlvl⟩
  obtain ⟨h5, hrun1, hh5_pc, hh5_mem, hh5_reg, hh5_x10, hh5_x12⟩ :=
    commit_bin_header_ptrs_gen oracle pcHdr lvlIdx hlvl s0 hpc hx9 hx24 hd0 hd1 hf0 hf1 hf2 hf3 hf4 hf5
  let h6 := execInstrBr h5 (.LD .x20 .x24 (16#12))
  let h7 := execInstrBr h6 (.SRLI .x22 .x20 (6#6))
  let h8 := execInstrBr h7 (.BEQ .x22 .x0 beqImm)
  have hh6_pc : h6.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 7)) := pc_step_idx h5 (pcHdr + 6) hh5_pc
  have hh7_pc : h7.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcHdr + 8)) := pc_step_idx h6 (pcHdr + 7) hh6_pc
  have hh6_mem : h6.mem = s0.mem := (mem_exec_LD h5 _ _ _).trans hh5_mem
  have hh_mem : h8.mem = s0.mem :=
    ((mem_exec_BEQ h7 _ _ _).trans (mem_exec_SRLI h6 _ _ _)).trans hh6_mem
  have hh7_reg_h5 : ∀ r : Reg, r ≠ .x20 → r ≠ .x22 → h7.getReg r = h5.getReg r :=
    fun r h20r h22r => by
      simp only [h7, h6, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x22 r (Ne.symm h22r), getReg_setReg_ne' .x20 r (Ne.symm h20r)]
  have hh6_addr : h5.getReg .x24 + signExtend12 (16#12) = BitVec.ofNat 64 (C_DB + 32 * lvlIdx + 16) := by
    rw [hh5_reg .x24 (by decide) (by decide) (by decide), hx24, add_signExtend12_ofNat_small _ 16 (by omega)]
  have hrun2 : DetRun oracle (submission.image .commit) h5 3 h8 3 0 := by
    have r6 : DetRun oracle (submission.image .commit) h5 1 h6 1 0 :=
      DetRun.step1 (hf6 h5 hh5_pc) (ordinaryStep_LD h5 .x20 .x24 (16#12) (by rw [hh6_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have r7 : DetRun oracle (submission.image .commit) h6 1 h7 1 0 := DetRun.step1 (hf7 h6 hh6_pc) rfl
    have r8 : DetRun oracle (submission.image .commit) h7 1 h8 1 0 := DetRun.step1 (hf8 h7 hh7_pc) rfl
    exact (r6.trans r7).trans r8
  have h5mem : ∀ a, h5.getMem a = s0.getMem a := fun a => by simp only [MachineState.getMem, hh5_mem]
  have hh6_x20 : h6.getReg .x20 = BitVec.ofNat 64 outPairs := by
    simp only [h6, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0), hh6_addr, h5mem, hd2]
  have hh7_x20 : h7.getReg .x20 = BitVec.ofNat 64 outPairs := by
    simp only [h7, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 .x20 (by decide), hh6_x20]
  have hh7_x22 : h7.getReg .x22 = BitVec.ofNat 64 chunks := by
    simp only [h7, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), hh6_x20]
    exact (bv64_ushiftRight_ofNat outPairs 6 (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have hh8_reg : ∀ r : Reg, h8.getReg r = h7.getReg r := reg_exec_BEQ h7 .x22 .x0 beqImm
  have hh8_pc : h8.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then pcA else pcB)) := by
    by_cases hch : 0 < chunks
    · have hne0 : (h7.getReg .x22 == h7.getReg .x0) = false := by
        rw [hh7_x22, c_getReg_x0, beq_eq_false_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hch, ite_true, h8, execInstrBr, hne0, Bool.false_eq_true, ite_false, pc_setPC]
      rw [← hpc_A]
      exact pc_step_idx h7 (pcHdr + 8) hh7_pc
    · have hch0 : chunks = 0 := by omega
      have heq0 : (h7.getReg .x22 == h7.getReg .x0) = true := by
        rw [hh7_x22, hch0, c_getReg_x0]; exact beq_self_eq_true _
      simp only [hch, ite_false, h8, execInstrBr, heq0, ite_true, pc_setPC, hh7_pc]
      exact hbeq_pc
  exact ⟨h8, hrun1.trans hrun2, hh8_pc, hh_mem,
    fun r h6 h10 h12 h20 h22 => ((hh8_reg r).trans (hh7_reg_h5 r h20 h22)).trans (hh5_reg r h6 h10 h12),
    ((hh8_reg .x10).trans (hh7_reg_h5 .x10 (by decide) (by decide))).trans hh5_x10,
    ((hh8_reg .x12).trans (hh7_reg_h5 .x12 (by decide) (by decide))).trans hh5_x12,
    (hh8_reg .x20).trans hh7_x20, (hh8_reg .x22).trans hh7_x22⟩

private theorem commit_bin_tail_gen (oracle : Oracle)
    (pcNext pcLoop pcExit endLvl : Nat) (bneImm : BitVec 13)
    (hpc_exit : pcNext + 2 = pcExit)
    (hbne_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcNext + 1)) + signExtend13 bneImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcLoop))
    (lvlIdx : Nat) (hlvl : lvlIdx < endLvl) (hend : endLvl ≤ 23)
    (sc : MachineState)
    (hpcC : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * pcNext))
    (hx24 : sc.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * lvlIdx))
    (hx25 : sc.getReg .x25 = BitVec.ofNat 64 (C_DB + 32 * endLvl))
    (hf0 : fetch (submission.image .commit) sc = some (.base (.ADDI .x24 .x24 (32#12))))
    (hf1 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcNext + 1)) →
      fetch (submission.image .commit) st = some (.base (.BNE .x24 .x25 bneImm))) :
    ∃ e2,
      DetRun oracle (submission.image .commit) sc 2 e2 2 0 ∧
      e2.pc = BitVec.ofNat 64 (0x1000 + 4 * (if lvlIdx + 1 < endLvl then pcLoop else pcExit)) ∧
      e2.mem = sc.mem ∧
      e2.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (lvlIdx + 1)) ∧
      (∀ r : Reg, r ≠ .x24 → e2.getReg r = sc.getReg r) := by
  have hC_DB : C_DB = 68719476000 := rfl
  let e1 := execInstrBr sc (.ADDI .x24 .x24 (32#12))
  let e2 := execInstrBr e1 (.BNE .x24 .x25 bneImm)
  have he1_pc : e1.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcNext + 1)) := pc_step_idx sc pcNext hpcC
  have he_run : DetRun oracle (submission.image .commit) sc 2 e2 2 0 :=
    (DetRun.step1 hf0 rfl).trans (DetRun.step1 (hf1 e1 he1_pc) rfl)
  have he1_x24 : e1.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (lvlIdx + 1)) := by
    simp only [e1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x24 ≠ .x0), hx24,
      add_signExtend12_ofNat_small _ 32 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have he1_x25 : e1.getReg .x25 = BitVec.ofNat 64 (C_DB + 32 * endLvl) := by
    simp only [e1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x24 .x25 (by decide), hx25]
  have he2_pc : e2.pc = BitVec.ofNat 64 (0x1000 + 4 * (if lvlIdx + 1 < endLvl then pcLoop else pcExit)) := by
    by_cases hlt : lvlIdx + 1 < endLvl
    · have hne : (e1.getReg .x24 != e1.getReg .x25) = true := by
        rw [he1_x24, he1_x25, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hlt, ite_true, e2, execInstrBr, hne, pc_setPC, he1_pc]
      exact hbne_pc
    · have heq : (e1.getReg .x24 != e1.getReg .x25) = false := by
        rw [he1_x24, he1_x25, show lvlIdx + 1 = endLvl by omega]
        exact bne_self_eq_false _
      simp only [hlt, ite_false, e2, execInstrBr, heq, Bool.false_eq_true, pc_setPC]
      rw [← hpc_exit]
      exact pc_step_idx e1 (pcNext + 1) he1_pc
  have he2_mem : e2.mem = sc.mem := (mem_exec_BNE e1 _ _ _).trans (mem_exec_ADDI sc _ _ _)
  have he2_reg : ∀ r : Reg, r ≠ .x24 → e2.getReg r = sc.getReg r := fun r hr => by
    rw [reg_exec_BNE e1 _ _ _ r]
    simp only [e1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x24 r (Ne.symm hr)]
  exact ⟨e2, he_run, he2_pc, he2_mem, (reg_exec_BNE e1 _ _ _ .x24).trans he1_x24, he2_reg⟩

/-! ### 3. Exported Level Drivers: Phase 3A (`commit_bin_level`) and Phase 3B (`commit_bin238_level`) -/

/-- One full iteration of Phase 3A `bin_driver` (words `3624..4163`) for `lvlIdx < 1`
building 240-bit masked `L_{lvlIdx+1}` (`L1`). -/
theorem commit_bin_level (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx : Nat) (hlvl : lvlIdx < 1) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 3624))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * lvlIdx))
    (hx25 : s0.getReg .x25 = BitVec.ofNat 64 (C_DB + 32))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 32, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + off)) =
        (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + off)))
    (hsrc : ∀ idx < levelSize lvlIdx,
      readBuffer s0 (C_TD + levelBase lvlIdx + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts lvlIdx idx)
    (hsrcGap : ∀ q < levelSize lvlIdx / 2,
      readBuffer s0 (C_TD + levelBase lvlIdx + 96 * q + 64) 32 = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0
        (binLevelSteps lvlIdx) s1 (binLevelCycles lvlIdx) (binLevelCalls lvlIdx) ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (if lvlIdx + 1 < 1 then 3624 else 4164)) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (lvlIdx + 1)) ∧
      s1.getReg .x25 = BitVec.ofNat 64 (C_DB + 32) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ idx < levelSize (lvlIdx + 1),
        readBuffer s1 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx) ∧
      (∀ q < levelSize (lvlIdx + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase (lvlIdx + 1)) (C_TD + levelBase (lvlIdx + 2)) := by
  let outPairs := levelSize (lvlIdx + 1) / 2
  let chunks := outPairs / 64
  let remPairs := outPairs % 64
  have hdstEven := levelSize_even (lvlIdx + 1) (by omega)
  obtain ⟨h8, hh_run, hh8_pc, hh_mem, hh8_reg, hh8_x10, hh8_x12, hh8_x20, hh8_x22⟩ :=
    commit_bin_header_gen oracle msg 3624 3633 4150 (2072#13) rfl pc_beq_3632
      lvlIdx outPairs chunks (by omega) rfl rfl s0 hpc hx9 hx24 hdata
      (commit_fetch_commitMid3Instr s0 3624 (by omega) (by omega) hpc)
      (fun st hst => commit_fetch_commitMid3Instr st 3625 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid3Instr st 3626 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid3Instr st 3627 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid3Instr st 3628 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid3Instr st 3629 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid3Instr st 3630 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid3Instr st 3631 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid3Instr st 3632 (by omega) (by omega) hst)
  obtain ⟨sb, hrunA, hpcB, hregA, hx10B, hx12B, hdigB, hgapB, hpresB⟩ :=
    commit_bin_level_stageA h768 oracle msg salts lvlIdx outPairs chunks hlvl rfl rfl s0 h8 hh_mem hh8_pc
      ((hh8_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5)
      ((hh8_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11)
      ((hh8_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13)
      hh8_x10 hh8_x12 hh8_x22 hsrc hsrcGap
  obtain ⟨st, hrunB, hpcT, hregB, _, _, hdigT, hgapT, hpresT⟩ :=
    commit_bin_level_stageB h768 oracle msg salts lvlIdx outPairs chunks remPairs hlvl rfl rfl rfl s0 sb hpcB
      ((hregA .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh8_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5))
      ((hregA .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh8_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11))
      ((hregA .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh8_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13))
      ((hregA .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh8_x20)
      hx10B hx12B hsrc hsrcGap hdigB hgapB hpresB
  have hst_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → r ≠ .x20 → r ≠ .x22 →
      st.getReg r = s0.getReg r := fun r h6 h7 h10 h12 h19 h20 h22 =>
    ((hregB r h6 h10 h12 h22).trans (hregA r h6 h7 h10 h12 h19)).trans (hh8_reg r h6 h10 h12 h20 h22)
  obtain ⟨e2, he_run, he2_pc, he2_mem, he2_x24, he2_reg⟩ :=
    commit_bin_tail_gen oracle 4162 3624 4164 1 (6036#13) rfl pc_bne_4163 lvlIdx hlvl (by omega) st hpcT
      ((hst_reg .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
      ((hst_reg .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25)
      (commit_fetch_commitMid4Instr st 4162 (by omega) (by omega) hpcT)
      (fun s' hs' => commit_fetch_commitMid4Instr s' 4163 (by omega) (by omega) hs')
  have hrun_all : DetRun oracle (submission.image .commit) s0
      (binLevelSteps lvlIdx) e2 (binLevelCycles lvlIdx) (binLevelCalls lvlIdx) := by
    have h := ((hh_run.trans hrunA).trans hrunB).trans he_run
    have hs : 9 + (if 0 < chunks then 4 + 513 * chunks else 0) + (2 + 10 * remPairs) + 2 =
        binLevelSteps lvlIdx := rfl
    have hc : 9 + (if 0 < chunks then 4 + 1409 * chunks else 0) + (2 + 24 * remPairs) + 2 =
        binLevelCycles lvlIdx := rfl
    have hq : 0 + 128 * chunks + 2 * remPairs + 0 = binLevelCalls lvlIdx := by
      unfold binLevelCalls; omega
    rw [hs, hc, hq] at h
    exact h
  refine ⟨e2, hrun_all, he2_pc,
    (he2_reg .x2 (by decide)).trans ((hst_reg .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx2),
    (he2_reg .x5 (by decide)).trans ((hst_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5),
    (he2_reg .x9 (by decide)).trans ((hst_reg .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx9),
    (he2_reg .x11 (by decide)).trans ((hst_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11),
    (he2_reg .x13 (by decide)).trans ((hst_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13),
    he2_x24,
    (he2_reg .x25 (by decide)).trans ((hst_reg .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25),
    (he2_reg .x26 (by decide)).trans ((hst_reg .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26),
    fun idx hidx => (readBuffer_of_mem_eq he2_mem _ _).trans (hdigT idx hidx),
    fun q hq j hj => (getByte_of_mem_eq he2_mem _).trans (hgapT q hq j hj),
    hpresT.trans (MemPreservedOutside.of_mem_eq he2_mem _ _)⟩

/-- One full iteration of Phase 3B `bin238_driver` (words `4168..4967`) for `1 ≤ lvlIdx < 23`
building 238-bit masked `L_{lvlIdx+1}` (`L2..L23`). -/
theorem commit_bin238_level (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx : Nat) (hlo : 1 ≤ lvlIdx) (hhi : lvlIdx < 23) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 4168))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * lvlIdx))
    (hx25 : s0.getReg .x25 = BitVec.ofNat 64 (C_DB + 736))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hx27 : s0.getReg .x27 = mask238Word)
    (hdata : ∀ off < 32, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + off)) =
        (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + off)))
    (hsrc : ∀ idx < levelSize lvlIdx,
      readBuffer s0 (C_TD + levelBase lvlIdx + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts lvlIdx idx)
    (hsrcGap : ∀ q < levelSize lvlIdx / 2,
      readBuffer s0 (C_TD + levelBase lvlIdx + 96 * q + 64) 32 = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0
        (bin238LevelSteps lvlIdx) s1 (bin238LevelCycles lvlIdx) (bin238LevelCalls lvlIdx) ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (if lvlIdx + 1 < 23 then 4168 else 4968)) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (lvlIdx + 1)) ∧
      s1.getReg .x25 = BitVec.ofNat 64 (C_DB + 736) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      s1.getReg .x27 = mask238Word ∧
      (∀ idx < levelSize (lvlIdx + 1),
        readBuffer s1 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx) ∧
      (∀ q < levelSize (lvlIdx + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase (lvlIdx + 1)) (C_TD + levelBase (lvlIdx + 2)) := by
  let outPairs := levelSize (lvlIdx + 1) / 2
  let chunks := outPairs / 64
  let remPairs := outPairs % 64
  have hdstEven := levelSize_even (lvlIdx + 1) (by omega)
  obtain ⟨h8, hh_run, hh8_pc, hh_mem, hh8_reg, hh8_x10, hh8_x12, hh8_x20, hh8_x22⟩ :=
    commit_bin_header_gen oracle msg 4168 4177 4950 (3096#13) rfl pc_beq_4176
      lvlIdx outPairs chunks hhi rfl rfl s0 hpc hx9 hx24 hdata
      (commit_fetch_commitMid4Instr s0 4168 (by omega) (by omega) hpc)
      (fun st hst => commit_fetch_commitMid4Instr st 4169 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid4Instr st 4170 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid4Instr st 4171 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid4Instr st 4172 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid4Instr st 4173 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid4Instr st 4174 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid4Instr st 4175 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid4Instr st 4176 (by omega) (by omega) hst)
  have hh8_x27 : h8.getReg .x27 = mask238Word :=
    (hh8_reg .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27
  obtain ⟨sb, hrunA, hpcB, hregA, hx10B, hx12B, hdigB, hgapB, hpresB⟩ :=
    commit_bin238_level_stageA h768 oracle msg salts lvlIdx outPairs chunks hlo hhi rfl rfl s0 h8 hh_mem hh8_pc
      ((hh8_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5)
      ((hh8_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11)
      ((hh8_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13)
      hh8_x27 hh8_x10 hh8_x12 hh8_x22 hsrc hsrcGap
  have hsb_x27 : sb.getReg .x27 = mask238Word :=
    (hregA .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh8_x27
  obtain ⟨st, hrunB, hpcT, hregB, _, _, hdigT, hgapT, hpresT⟩ :=
    commit_bin238_level_stageB h768 oracle msg salts lvlIdx outPairs chunks remPairs hlo hhi rfl rfl rfl s0 sb hpcB
      ((hregA .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh8_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5))
      ((hregA .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh8_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11))
      ((hregA .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh8_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13))
      hsb_x27
      ((hregA .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh8_x20)
      hx10B hx12B hsrc hsrcGap hdigB hgapB hpresB
  have hst_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → r ≠ .x20 → r ≠ .x22 →
      st.getReg r = s0.getReg r := fun r h6 h7 h10 h12 h19 h20 h22 =>
    ((hregB r h6 h10 h12 h22).trans (hregA r h6 h7 h10 h12 h19)).trans (hh8_reg r h6 h10 h12 h20 h22)
  obtain ⟨e2, he_run, he2_pc, he2_mem, he2_x24, he2_reg⟩ :=
    commit_bin_tail_gen oracle 4966 4168 4968 23 (4996#13) rfl pc_bne_4967 lvlIdx hhi (le_refl _) st hpcT
      ((hst_reg .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
      ((hst_reg .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25)
      (commit_fetch_commitTailInstr st 4966 (by omega) (by omega) hpcT)
      (fun s' hs' => commit_fetch_commitTailInstr s' 4967 (by omega) (by omega) hs')
  have hrun_all : DetRun oracle (submission.image .commit) s0
      (bin238LevelSteps lvlIdx) e2 (bin238LevelCycles lvlIdx) (bin238LevelCalls lvlIdx) := by
    have h := ((hh_run.trans hrunA).trans hrunB).trans he_run
    have hs : 9 + (if 0 < chunks then 4 + 769 * chunks else 0) + (2 + 14 * remPairs) + 2 =
        bin238LevelSteps lvlIdx := rfl
    have hc : 9 + (if 0 < chunks then 4 + 1665 * chunks else 0) + (2 + 28 * remPairs) + 2 =
        bin238LevelCycles lvlIdx := rfl
    have hq : 0 + 128 * chunks + 2 * remPairs + 0 = bin238LevelCalls lvlIdx := by
      unfold bin238LevelCalls; omega
    rw [hs, hc, hq] at h
    exact h
  refine ⟨e2, hrun_all, he2_pc,
    (he2_reg .x2 (by decide)).trans ((hst_reg .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx2),
    (he2_reg .x5 (by decide)).trans ((hst_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5),
    (he2_reg .x9 (by decide)).trans ((hst_reg .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx9),
    (he2_reg .x11 (by decide)).trans ((hst_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11),
    (he2_reg .x13 (by decide)).trans ((hst_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13),
    he2_x24,
    (he2_reg .x25 (by decide)).trans ((hst_reg .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25),
    (he2_reg .x26 (by decide)).trans ((hst_reg .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26),
    (he2_reg .x27 (by decide)).trans ((hst_reg .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27),
    fun idx hidx => (readBuffer_of_mem_eq he2_mem _ _).trans (hdigT idx hidx),
    fun q hq j hj => (getByte_of_mem_eq he2_mem _).trans (hgapT q hq j hj),
    hpresT.trans (MemPreservedOutside.of_mem_eq he2_mem _ _)⟩

end CommitGolfCandidate
