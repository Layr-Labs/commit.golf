import CommitGolfCandidate.MoonCommitBin
import CommitGolfCandidate.CompressionSampling

/-! Exact RV64IM execution proofs for Phases 3A, 3B, 3C, and 4 of the v5 (`148,474`-word) `commit` image,
plus full-commit composition proving `commit_run_exact`, `commit_oracle_run_exact`, and `commit_termination`:
- Phase 3A: 4-level 240-bit binary driver (`L2..L5`, `U_BIN=2048`, words `139327..147578`)
- Phase 3B: 3-level 238-bit binary driver (`L6..L8`, `U_BIN238=128`, words `147579..148411`)
- Phase 3C: 15-level variable-width / hash-chained binary driver (`L9..L23`, words `148412..148459`)
- Phase 4: unmasked 256-bit `L24` root + copy to commitment + `HALT(0)` (words `148460..148473`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Exact Step / Cycle / Call Cost Formulas -/

private def p3cNodeSteps (l : Nat) : Nat :=
  if levelChain l ≤ 1 then 15 else 22 + 4 * (levelChain l - 2)

private def p3cNodeCycles (l : Nat) : Nat :=
  if levelChain l ≤ 1 then 22 else 36 + 11 * (levelChain l - 2)

private def p3cLevelSteps (l : Nat) : Nat := 16 + levelSize l * p3cNodeSteps l
private def p3cLevelCycles (l : Nat) : Nat := 16 + levelSize l * p3cNodeCycles l
private def p3cLevelCalls (l : Nat) : Nat := levelSize l * levelChain l

private theorem phase3A_steps_sum :
    2 + ∑ i ∈ Finset.range 4, binLevelSteps i = 20980835 := by decide

private theorem phase3A_cycles_sum :
    2 + ∑ i ∈ Finset.range 4, binLevelCycles i = 57680995 := by decide

private theorem phase3A_calls_sum :
    ∑ i ∈ Finset.range 4, binLevelCalls i = 5242880 := by decide

private theorem phase3B_steps_sum :
    4 + ∑ k ∈ Finset.range 3, bin238LevelSteps (4 + k) = 1837645 := by decide

private theorem phase3B_cycles_sum :
    4 + ∑ k ∈ Finset.range 3, bin238LevelCycles (4 + k) = 3978490 := by decide

private theorem phase3B_calls_sum :
    ∑ k ∈ Finset.range 3, bin238LevelCalls (4 + k) = 305835 := by decide

private theorem phase3C_steps_sum :
    3 + ∑ k ∈ Finset.range 15, p3cLevelSteps (9 + k) = 1424710 := by decide

private theorem phase3C_cycles_sum :
    3 + ∑ k ∈ Finset.range 15, p3cLevelCycles (9 + k) = 2847859 := by decide

private theorem phase3C_calls_sum :
    ∑ k ∈ Finset.range 15, p3cLevelCalls (9 + k) = 203307 := by decide

private theorem levelBase_mono : ∀ a b, a ≤ b → b ≤ 24 → levelBase a ≤ levelBase b := by
  intro a b hab hb
  induction b with
  | zero =>
    have h0 : a = 0 := by omega
    rw [h0]
  | succ b ih =>
    by_cases h : a ≤ b
    · have hstep : levelBase (b + 1) = levelBase b + levelBytes b := rfl
      have hle : levelBase b ≤ levelBase (b + 1) := by rw [hstep]; omega
      exact (ih h (by omega)).trans hle
    · have heq : a = b + 1 := by omega
      rw [heq]

/-! ### 2. Phase 3A (`L2..L5`, 240-bit) and Phase 3B (`L6..L8`, 238-bit) -/

/-- Phase 3A (`L2..L5`, 240-bit masked, words `139327..147578`):
`20,980,835` steps, `57,680,995` cycles, `5,242,880` calls. -/
private theorem commit_phase3A (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 139327))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 704, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl1 : ∀ idx < levelSize 1, readBuffer s0 (C_TD + levelBase 1 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 idx)
    (hzero : ∀ l, 1 ≤ l → l < 24 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 20980835 s1 57680995 5242880 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 147579) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x24 = BitVec.ofNat 64 (C_DB + 128) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l, 1 ≤ l → l ≤ 5 → ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l, 1 ≤ l → l < 24 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 2) (C_TD + levelBase 6) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476032 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have htb := treeBytes_eq
  let sa0 := execInstrBr s0 (.ADDI .x24 .x2 (0#12))
  let sa := execInstrBr sa0 (.ADDI .x25 .x2 (128#12))
  have hsa0_pc : sa0.pc = BitVec.ofNat 64 (0x1000 + 4 * 139328) := pc_step_idx s0 139327 hpc
  have hsa_pc : sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 139329) := pc_step_idx sa0 139328 hsa0_pc
  have hsetup : DetRun oracle (submission.image .commit) s0 2 sa 2 0 := by
    have r0 : DetRun oracle (submission.image .commit) s0 1 sa0 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hpc (by simp only [commitMid2Instr])
    have r1 : DetRun oracle (submission.image .commit) sa0 1 sa 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hsa0_pc (by simp only [commitMid2Instr])
    exact r0.trans r1
  have hsa_mem : sa.mem = s0.mem := (mem_exec_ADDI sa0 _ _ _).trans (mem_exec_ADDI s0 _ _ _)
  have hsa_reg_other : ∀ r : Reg, r ≠ .x24 → r ≠ .x25 → sa.getReg r = s0.getReg r := fun r h24 h25 => by
    simp only [sa, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x25 r (Ne.symm h25), getReg_setReg_ne' .x24 r (Ne.symm h24)]
  have hind : ∀ n ≤ 4,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa (∑ i ∈ Finset.range n, binLevelSteps i) sn
          (∑ i ∈ Finset.range n, binLevelCycles i) (∑ i ∈ Finset.range n, binLevelCalls i) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 4 then 139329 else 147579)) ∧
        sn.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sn.getReg .x5 = 0#64 ∧
        sn.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sn.getReg .x11 = 96#64 ∧
        sn.getReg .x13 = 0#64 ∧ sn.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * n) ∧
        sn.getReg .x25 = BitVec.ofNat 64 (C_DB + 128) ∧ sn.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        (∀ l, 1 ≤ l → l ≤ n + 1 → ∀ idx < levelSize l,
          readBuffer sn (C_TD + levelBase l + gapOffset idx) 32 = nodeVal c96 msg salts l idx) ∧
        (∀ l, 1 ≤ l → l < 24 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
        MemPreservedOutside s0 sn (C_TD + levelBase 2) (C_TD + levelBase (n + 2)) := by
    intro n hn; induction n with
    | zero =>
      refine ⟨sa, by simpa only [Finset.sum_range_zero] using DetRun.refl oracle (submission.image .commit) sa,
        by simpa only [show (0 : Nat) < 4 by decide, ite_true] using hsa_pc,
        (hsa_reg_other .x2 (by decide) (by decide)).trans hx2,
        (hsa_reg_other .x5 (by decide) (by decide)).trans hx5,
        (hsa_reg_other .x9 (by decide) (by decide)).trans hx9,
        (hsa_reg_other .x11 (by decide) (by decide)).trans hx11,
        (hsa_reg_other .x13 (by decide) (by decide)).trans hx13,
        by simp only [sa, sa0, execInstrBr, MachineState.getReg_setPC,
            getReg_setReg_ne' .x25 .x24 (by decide),
            MachineState.getReg_setReg_eq (by decide : Reg.x24 ≠ .x0), hx2]; decide,
        by simp only [sa, sa0, execInstrBr, MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0),
            getReg_setReg_ne' .x24 .x2 (by decide), hx2]; decide,
        (hsa_reg_other .x26 (by decide) (by decide)).trans hx26,
        fun l hl_lo hl_hi idx hidx => by
          have : l = 1 := by omega
          subst this
          rw [readBuffer_of_mem_eq hsa_mem]
          exact hl1 idx hidx,
        fun l hl1 hl2 q hq j hj => by
          rw [getByte_of_mem_eq hsa_mem]
          exact hzero l hl1 hl2 q hq j hj,
        MemPreservedOutside.of_mem_eq hsa_mem _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hx2n, hx5n, hx9n, hx11n, hx13n, hx24n, hx25n, hx26n, hdign, hgapn, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 139329) := by
        simpa only [show n < 4 by omega, ite_true] using hpcn
      have hlb_bd := levelBase_bound (n + 2) (by omega)
      obtain ⟨sm, hrun1, hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx24m, hx25m, hx26m, hdig1, hgap1, hpres1⟩ :=
        commit_bin_level h768 oracle msg salts n (by omega) sn hpc_in hx2n hx5n hx9n hx11n hx13n hx24n hx25n hx26n
          (fun off hoff hal => by
            have heq : C_DB + 32 * n + off = C_DB + (32 * n + off) := by omega
            rw [heq, hpresn.getMem_eq (by omega) (by omega) (by omega)]
            exact hdata (32 * n + off) (by omega) (by omega))
          (fun idx hidx => hdign (n + 1) (by omega) (by omega) idx hidx)
          (fun q hq => readBuffer_zero_of_bytes sn _ 32 (fun j hj => by
            simpa only [Nat.add_assoc] using hgapn (n + 1) (by omega) (by omega) q hq j hj))
      have hlb_n2_n3 : levelBase (n + 2) ≤ levelBase (n + 3) := levelBase_mono _ _ (by omega) (by omega)
      have hlb_2_n2 : levelBase 2 ≤ levelBase (n + 2) := levelBase_mono _ _ (by omega) (by omega)
      refine ⟨sm, by simpa only [Finset.sum_range_succ] using hrunn.trans hrun1,
        hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx24m, hx25m, hx26m, ?_, ?_, ?_⟩
      · intro l hl1 hl2 idx hidx
        by_cases hcur : l = n + 2
        · subst hcur; exact hdig1 idx hidx
        · have hlt : l ≤ n + 1 := by omega
          have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
          have hlb_l : levelBase l + levelBytes l ≤ levelBase (n + 2) := by
            have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
            rw [h1]; exact levelBase_mono (l + 1) (n + 2) (by omega) (by omega)
          have hlb_bd_l := levelBase_bound l (by omega)
          rw [hpres1.readBuffer_eq (by omega) (by omega)]
          exact hdign l hl1 hlt idx hidx
      · intro l hl1 hl2 q hq j hj
        by_cases hcur : l = n + 2
        · subst hcur
          exact (hgap1 q hq j hj).trans (hgapn (n + 2) (by omega) (by omega) q hq j hj)
        · have hbytes := levelBytes_eq_gap l hl1 hl2
          have hbd := levelBase_bound l (by omega)
          have hout : C_TD + levelBase l + 96 * q + 64 + j < C_TD + levelBase (n + 2) ∨
              C_TD + levelBase (n + 3) ≤ C_TD + levelBase l + 96 * q + 64 + j := by
            by_cases hlt : l < n + 2
            · left
              have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
              have h2 := levelBase_mono (l + 1) (n + 2) (by omega) (by omega)
              omega
            · right
              have h2 := levelBase_mono (n + 3) l (by omega) (by omega)
              omega
          exact (hpres1 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) hout).trans (hgapn l hl1 hl2 q hq j hj)
      · have hne_n : n + 1 + 2 = n + 3 := by omega
        rw [hne_n]
        exact (hpresn.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (le_refl _))
  obtain ⟨sfin, hrun4, hpc4, hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, _, hx26f, hdigf, hgapf, hpresf⟩ :=
    hind 4 (le_refl _)
  have hrun_tot : DetRun oracle (submission.image .commit) s0 20980835 sfin 57680995 5242880 := by
    have h := hsetup.trans hrun4
    rw [phase3A_steps_sum, phase3A_cycles_sum, Nat.zero_add, phase3A_calls_sum] at h
    exact h
  exact ⟨sfin, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpc4,
    hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, hx26f, hdigf, hgapf, hpresf⟩

/-- Phase 3B (`L6..L8`, 238-bit masked, words `147579..148411`):
`1,837,645` steps, `3,978,490` cycles, `305,835` calls. -/
private theorem commit_phase3B (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 147579))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 128))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 704, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl5 : ∀ idx < levelSize 5, readBuffer s0 (C_TD + levelBase 5 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 5 idx)
    (hzero : ∀ l, 5 ≤ l → l < 24 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0)
    (hodd8 : ∀ j < 32, s0.getByte (BitVec.ofNat 64 (C_TD + levelBase 8 + 96 * 21845 + 32 + j)) = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 1837645 s1 3978490 305835 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148412) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x24 = BitVec.ofNat 64 (C_DB + 224) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l, 6 ≤ l → l ≤ 8 → ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l, 5 ≤ l → l < 24 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
      (∀ j < 32, s1.getByte (BitVec.ofNat 64 (C_TD + levelBase 8 + 96 * 21845 + 32 + j)) = 0) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 6) (C_TD + levelBase 9) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476032 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have htb := treeBytes_eq
  -- Setup words 147579..147582: x25 = C_DB + 224, x27 = mask238Word
  let sa0 := execInstrBr s0 (.ADDI .x25 .x2 (224#12))
  let sa1 := execInstrBr sa0 (.ADDI .x27 .x0 (1#12))
  let sa2 := execInstrBr sa1 (.SLLI .x27 .x27 (46#6))
  let sa := execInstrBr sa2 (.ADDI .x27 .x27 (4095#12))
  have hsa0_pc : sa0.pc = BitVec.ofNat 64 (0x1000 + 4 * 147580) := pc_step_idx s0 147579 hpc
  have hsa1_pc : sa1.pc = BitVec.ofNat 64 (0x1000 + 4 * 147581) := pc_step_idx sa0 147580 hsa0_pc
  have hsa2_pc : sa2.pc = BitVec.ofNat 64 (0x1000 + 4 * 147582) := pc_step_idx sa1 147581 hsa1_pc
  have hsa_pc : sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 147583) := pc_step_idx sa2 147582 hsa2_pc
  have hsetup : DetRun oracle (submission.image .commit) s0 4 sa 4 0 := by
    have r0 : DetRun oracle (submission.image .commit) s0 1 sa0 1 0 :=
      commit_step1_mid3 (by omega) (by omega) hpc (by simp only [commitMid3Instr])
    have r1 : DetRun oracle (submission.image .commit) sa0 1 sa1 1 0 :=
      commit_step1_mid3 (by omega) (by omega) hsa0_pc (by simp only [commitMid3Instr])
    have r2 : DetRun oracle (submission.image .commit) sa1 1 sa2 1 0 :=
      commit_step1_mid3 (by omega) (by omega) hsa1_pc (by simp only [commitMid3Instr])
    have r3 : DetRun oracle (submission.image .commit) sa2 1 sa 1 0 :=
      commit_step1_mid3 (by omega) (by omega) hsa2_pc (by simp only [commitMid3Instr])
    exact ((r0.trans r1).trans r2).trans r3
  have hsa_mem : sa.mem = s0.mem :=
    (((mem_exec_ADDI sa2 _ _ _).trans (mem_exec_SLLI sa1 _ _ _)).trans
      (mem_exec_ADDI sa0 _ _ _)).trans (mem_exec_ADDI s0 _ _ _)
  have hsa_reg_other : ∀ r : Reg, r ≠ .x25 → r ≠ .x27 → sa.getReg r = s0.getReg r := fun r h25 h27 => by
    simp only [sa, sa2, sa1, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x27 r (Ne.symm h27), getReg_setReg_ne' .x25 r (Ne.symm h25)]
  have hsa_x25 : sa.getReg .x25 = BitVec.ofNat 64 (C_DB + 224) := by
    simp only [sa, sa2, sa1, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x27 .x25 (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0), hx2]; decide
  have hsa_x27 : sa.getReg .x27 = mask238Word := by
    simp only [sa, sa2, sa1, sa0, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x27 ≠ .x0), c_getReg_x0]; decide
  have hind : ∀ k ≤ 3,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa (∑ i ∈ Finset.range k, bin238LevelSteps (4 + i)) sn
          (∑ i ∈ Finset.range k, bin238LevelCycles (4 + i)) (∑ i ∈ Finset.range k, bin238LevelCalls (4 + i)) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k < 3 then 147583 else 148412)) ∧
        sn.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sn.getReg .x5 = 0#64 ∧
        sn.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sn.getReg .x11 = 96#64 ∧
        sn.getReg .x13 = 0#64 ∧ sn.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (4 + k)) ∧
        sn.getReg .x25 = BitVec.ofNat 64 (C_DB + 224) ∧ sn.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        sn.getReg .x27 = mask238Word ∧
        (∀ l, 5 ≤ l → l ≤ k + 5 → ∀ idx < levelSize l,
          readBuffer sn (C_TD + levelBase l + gapOffset idx) 32 = nodeVal c96 msg salts l idx) ∧
        (∀ l, 5 ≤ l → l < 24 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
        (∀ j < 32, sn.getByte (BitVec.ofNat 64 (C_TD + levelBase 8 + 96 * 21845 + 32 + j)) = 0) ∧
        MemPreservedOutside s0 sn (C_TD + levelBase 6) (C_TD + levelBase (k + 6)) := by
    intro k hk; induction k with
    | zero =>
      refine ⟨sa, by simpa only [Finset.sum_range_zero] using DetRun.refl oracle (submission.image .commit) sa,
        by simpa only [show (0 : Nat) < 3 by decide, ite_true] using hsa_pc,
        (hsa_reg_other .x2 (by decide) (by decide)).trans hx2,
        (hsa_reg_other .x5 (by decide) (by decide)).trans hx5,
        (hsa_reg_other .x9 (by decide) (by decide)).trans hx9,
        (hsa_reg_other .x11 (by decide) (by decide)).trans hx11,
        (hsa_reg_other .x13 (by decide) (by decide)).trans hx13,
        (hsa_reg_other .x24 (by decide) (by decide)).trans hx24,
        hsa_x25,
        (hsa_reg_other .x26 (by decide) (by decide)).trans hx26,
        hsa_x27,
        fun l hl_lo hl_hi idx hidx => by
          have : l = 5 := by omega
          subst this
          rw [readBuffer_of_mem_eq hsa_mem]
          exact hl5 idx hidx,
        fun l hl1 hl2 q hq j hj => by
          rw [getByte_of_mem_eq hsa_mem]
          exact hzero l hl1 hl2 q hq j hj,
        fun j hj => by
          rw [getByte_of_mem_eq hsa_mem]
          exact hodd8 j hj,
        MemPreservedOutside.of_mem_eq hsa_mem _ _⟩
    | succ k ih =>
      obtain ⟨sn, hrunn, hpcn, hx2n, hx5n, hx9n, hx11n, hx13n, hx24n, hx25n, hx26n, hx27n,
        hdign, hgapn, hodd8n, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 147583) := by
        simpa only [show k < 3 by omega, ite_true] using hpcn
      have hlb_bd := levelBase_bound (k + 6) (by omega)
      obtain ⟨sm, hrun1, hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx24m, hx25m, hx26m, hx27m,
        hdig1, hgap1, hoddSlot1, hpres1⟩ :=
        commit_bin238_level h768 oracle msg salts (4 + k) (by omega) (by omega) sn hpc_in
          hx2n hx5n hx9n hx11n hx13n hx24n hx25n hx26n hx27n
          (fun off hoff hal => by
            have heq : C_DB + 32 * (4 + k) + off = C_DB + (32 * (4 + k) + off) := by omega
            rw [heq, hpresn.getMem_eq (by omega) (by omega) (by omega)]
            exact hdata (32 * (4 + k) + off) (by omega) (by omega))
          (fun idx hidx => hdign (4 + k + 1) (by omega) (by omega) idx hidx)
          (fun q hq => readBuffer_zero_of_bytes sn _ 32 (fun j hj => by
            simpa only [Nat.add_assoc] using hgapn (4 + k + 1) (by omega) (by omega) q hq j hj))
      have hpc_eq : sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k + 1 < 3 then 147583 else 148412)) := by
        simpa only [show (4 + k + 1 < 7) ↔ (k + 1 < 3) by omega] using hpcm
      have hx24_eq : sm.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (4 + (k + 1))) := by
        simpa only [show 4 + k + 1 = 4 + (k + 1) by omega] using hx24m
      have hlb_k6_k7 : levelBase (k + 6) ≤ levelBase (k + 7) := levelBase_mono _ _ (by omega) (by omega)
      have hlb_6_k6 : levelBase 6 ≤ levelBase (k + 6) := levelBase_mono _ _ (by omega) (by omega)
      have h4k2 : 4 + k + 2 = k + 6 := by omega
      have h4k3 : 4 + k + 3 = k + 7 := by omega
      rw [h4k2, h4k3] at hpres1
      refine ⟨sm, by simpa only [Finset.sum_range_succ] using hrunn.trans hrun1,
        hpc_eq, hx2m, hx5m, hx9m, hx11m, hx13m, hx24_eq, hx25m, hx26m, hx27m, ?_, ?_, ?_, ?_⟩
      · intro l hl1 hl2 idx hidx
        by_cases hcur : l = k + 6
        · subst hcur; simpa only [h4k2] using hdig1 idx (by simpa only [h4k2] using hidx)
        · have hlt : l ≤ k + 5 := by omega
          have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
          have hlb_l : levelBase l + levelBytes l ≤ levelBase (k + 6) := by
            have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
            rw [h1]; exact levelBase_mono (l + 1) (k + 6) (by omega) (by omega)
          have hlb_bd_l := levelBase_bound l (by omega)
          rw [hpres1.readBuffer_eq (by omega) (by omega)]
          exact hdign l hl1 hlt idx hidx
      · intro l hl1 hl2 q hq j hj
        by_cases hcur : l = k + 6
        · subst hcur
          have hg1 := hgap1 q (by simpa only [h4k2] using hq) j hj
          rw [h4k2] at hg1
          exact hg1.trans (hgapn (k + 6) (by omega) (by omega) q hq j hj)
        · have hbytes := levelBytes_eq_gap l (by omega) hl2
          have hbd := levelBase_bound l (by omega)
          have hout : C_TD + levelBase l + 96 * q + 64 + j < C_TD + levelBase (k + 6) ∨
              C_TD + levelBase (k + 7) ≤ C_TD + levelBase l + 96 * q + 64 + j := by
            by_cases hlt : l < k + 6
            · left
              have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
              have h2 := levelBase_mono (l + 1) (k + 6) (by omega) (by omega)
              omega
            · right
              have h2 := levelBase_mono (k + 7) l (by omega) (by omega)
              omega
          exact (hpres1 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) hout).trans (hgapn l hl1 hl2 q hq j hj)
      · intro j hj
        by_cases hk2 : k = 2
        · subst hk2
          have hmod : levelSize (4 + 2 + 2) % 2 = 1 := by decide
          have hdiv : levelSize (4 + 2 + 2) / 2 = 21845 := by decide
          have h := hoddSlot1 hmod j hj
          rw [hdiv] at h
          exact h.trans (hodd8n j hj)
        · have hlb8 : levelBase (k + 7) ≤ levelBase 8 := levelBase_mono (k + 7) 8 (by omega) (by omega)
          have hbd8 := levelBase_bound 8 (by omega)
          have hbytes8 : levelBytes 8 = 21846 * 96 := by decide
          exact (hpres1 (C_TD + levelBase 8 + 96 * 21845 + 32 + j) (by omega) (Or.inr (by omega))).trans (hodd8n j hj)
      · have hne_k : k + 1 + 6 = k + 7 := by omega
        rw [hne_k]
        exact (hpresn.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (le_refl _))
  obtain ⟨sfin, hrun3, hpc3, hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, _, hx26f, _, hdigf, hgapf, hodd8f, hpresf⟩ :=
    hind 3 (le_refl _)
  have hrun_tot : DetRun oracle (submission.image .commit) s0 1837645 sfin 3978490 305835 := by
    have h := hsetup.trans hrun3
    rw [phase3B_steps_sum, phase3B_cycles_sum, Nat.zero_add, phase3B_calls_sum] at h
    exact h
  exact ⟨sfin, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpc3,
    hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, hx26f,
    fun l hl1 hl2 idx hidx => hdigf l (by omega) (by omega) idx hidx,
    hgapf, hodd8f, hpresf⟩

/-! ### 3. Phase 3C (`L9..L23`, Variable-Width & Hash-Chained Driver, words `148412..148459`) -/

private theorem pc_bne_148434 :
    BitVec.ofNat 64 (0x1000 + 4 * 148434) + signExtend13 (16#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 148438) := by decide

private theorem pc_jal_148437 :
    BitVec.ofNat 64 (0x1000 + 4 * 148437) + signExtend21 (60#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 148452) := by decide

private theorem pc_beq_148444 :
    BitVec.ofNat 64 (0x1000 + 4 * 148444) + signExtend13 (20#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 148449) := by decide

private theorem pc_bne_148448 :
    BitVec.ofNat 64 (0x1000 + 4 * 148448) + signExtend13 (8180#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 148445) := by decide

private theorem pc_bne_148457 :
    BitVec.ofNat 64 (0x1000 + 4 * 148457) + signExtend13 (8080#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 148429) := by decide

private theorem pc_bne_148459 :
    BitVec.ofNat 64 (0x1000 + 4 * 148459) + signExtend13 (8016#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 148415) := by decide

private theorem mem_exec_SRL (s : MachineState) (rd rs1 rs2 : Reg) :
    (execInstrBr s (.SRL rd rs1 rs2)).mem = s.mem := by cases rd <;> rfl

private theorem p3c_meta_x19 (k : Nat) (hk : k < 15) :
    (BitVec.ofNat 64 (commitMeta3C (9 + k))) &&& signExtend12 (255#12) =
      BitVec.ofNat 64 (levelChain (9 + k) - 1) := by
  interval_cases k <;> decide

private theorem p3c_meta_x27 (k : Nat) (hk : k < 15) :
    signExtend12 (4095#12) >>>
      ((((BitVec.ofNat 64 (commitMeta3C (9 + k))) >>> 8) &&& signExtend12 (255#12)).toNat % 64) =
      maskTopWord (levelWidth (9 + k)) := by
  interval_cases k <;> decide

private theorem p3c_meta_x28 (k : Nat) (hk : k < 15) :
    (BitVec.ofNat 64 (commitMeta3C (9 + k))) >>> 32 =
      BitVec.ofNat 64 (levelTagStart (9 + k)) := by
  interval_cases k <;> decide

private theorem p3c_meta_x30 (k : Nat) (hk : k < 15) :
    BitVec.ofNat 64 (levelTagStart (9 + k)) + BitVec.ofNat 64 (levelChain (9 + k) - 1) =
      BitVec.ofNat 64 (levelTagStart (9 + k) + (levelChain (9 + k) - 1)) := by
  interval_cases k <;> decide

private theorem p3c_tagStart_eq (k : Nat) (hk : k < 15) (hch : ¬ levelChain (9 + k) ≤ 1) :
    levelTagStart (9 + k) = 256 * (9 + k) + 1 := by
  interval_cases k <;> simp_all [levelChain, levelTagStart]

private theorem p3c_chain_le_16 (k : Nat) (hk : k < 15) : levelChain (9 + k) ≤ 16 := by
  interval_cases k <;> decide

private theorem p3c_nodeVal_eq (c96 : Comp96) (msg : Message) (salts : Index → Salt192)
    (l idx : Nat) (hl1 : 9 ≤ l) (hl2 : l ≤ 23) (hidx : idx < levelSize l) :
    chainHash c96 l
      (nodeVal c96 msg salts (l - 1) (2 * idx))
      (if 2 * idx + 1 < levelSize (l - 1) then nodeVal c96 msg salts (l - 1) (2 * idx + 1) else 0) =
    nodeVal c96 msg salts l idx := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by omega⟩
  have hprev : m + 2 - 1 = m + 1 := by omega
  rw [hprev]
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (m + 2) idx = _
  rw [nodeValFromLeaves]
  have hstep : levelSize (m + 2) = (levelSize (m + 1) + 1) / 2 := levelSize_step (m + 1) (by omega)
  have h2idx : 2 * idx < levelSize (m + 1) := by omega
  have hge9 : ¬ (m + 2 < 9) := by omega
  by_cases hodd : 2 * idx + 1 < levelSize (m + 1)
  · simp only [hodd, ite_true]; rfl
  · simp only [hodd, ite_false, h2idx, ite_true, hge9]; rfl

private theorem p3c_gapOffset_bv (idx : Nat) (hidx : idx < 2 ^ 30) :
    ((BitVec.ofNat 64 idx + BitVec.ofNat 64 idx >>> 1) <<< 5) = BitVec.ofNat 64 (gapOffset idx) := by
  apply BitVec.eq_of_toNat_eq
  unfold gapOffset
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  have h1 : idx % 2 ^ 64 = idx := Nat.mod_eq_of_lt (by omega)
  have h2 : (idx + idx / 2) % 2 ^ 64 = idx + idx / 2 := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2]
  have h3 : (idx + idx / 2) * 2 ^ 5 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Mid-chain loop (words `148445..148448`) executing `m` iterations of stages `2..m+1`. -/
private theorem p3c_mid_loop (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (l : Nat) (hl : 9 ≤ l) (hl2 : l ≤ 23)
    (hch : 2 ≤ levelChain l) (d1 : Digest)
    (s0 : MachineState) (m : Nat) (hm : m ≤ levelChain l - 2)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * (if m < levelChain l - 2 then 148445 else 148449)))
    (hx5 : s0.getReg .x5 = 0#64) (hx10 : s0.getReg .x10 = BitVec.ofNat 64 commitChainScratch)
    (hx11 : s0.getReg .x11 = 96#64) (hx12 : s0.getReg .x12 = BitVec.ofNat 64 commitChainScratch)
    (hx13 : s0.getReg .x13 = 0#64) (hx18 : s0.getReg .x18 = BitVec.ofNat 64 commitChainScratch)
    (hx23 : s0.getReg .x23 = BitVec.ofNat 64 (256 * l + 2 + m))
    (hx30 : s0.getReg .x30 = BitVec.ofNat 64 (256 * l + levelChain l))
    (hcur : readBuffer s0 commitChainScratch 32 =
      chainIter (fun x => oracle.compression (x.cast h768.symm)) l m d1)
    (hmid0 : readBuffer s0 (commitChainScratch + 32) 32 = 0)
    (hhi0 : readBuffer s0 (commitChainScratch + 72) 24 = 0) :
    let rem := levelChain l - 2 - m
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 (4 * rem) s1 (11 * rem) rem ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148449) ∧
      (∀ r : Reg, r ≠ .x23 → s1.getReg r = s0.getReg r) ∧
      readBuffer s1 commitChainScratch 32 =
        chainIter (fun x => oracle.compression (x.cast h768.symm)) l (levelChain l - 2) d1 ∧
      readBuffer s1 (commitChainScratch + 32) 32 = 0 ∧
      readBuffer s1 (commitChainScratch + 72) 24 = 0 ∧
      MemPreservedOutside s0 s1 commitChainScratch (commitChainScratch + 72) := by
  have hCS : commitChainScratch = 8589934592 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hcl16 : levelChain l ≤ 16 := by
    simpa only [show 9 + (l - 9) = l by omega] using p3c_chain_le_16 (l - 9) (by omega)
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  -- Induction on remaining iterations `rem = levelChain l - 2 - m`
  suffices hgen : ∀ rem : Nat, ∀ m : Nat, m + rem = levelChain l - 2 → ∀ s : MachineState,
      s.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < rem then 148445 else 148449)) →
      s.getReg .x5 = 0#64 → s.getReg .x10 = BitVec.ofNat 64 commitChainScratch →
      s.getReg .x11 = 96#64 → s.getReg .x12 = BitVec.ofNat 64 commitChainScratch →
      s.getReg .x13 = 0#64 → s.getReg .x18 = BitVec.ofNat 64 commitChainScratch →
      s.getReg .x23 = BitVec.ofNat 64 (256 * l + 2 + m) →
      s.getReg .x30 = BitVec.ofNat 64 (256 * l + levelChain l) →
      readBuffer s commitChainScratch 32 = chainIter c96 l m d1 →
      readBuffer s (commitChainScratch + 32) 32 = 0 →
      readBuffer s (commitChainScratch + 72) 24 = 0 →
      ∃ s1,
        DetRun oracle (submission.image .commit) s (4 * rem) s1 (11 * rem) rem ∧
        s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148449) ∧
        (∀ r : Reg, r ≠ .x23 → s1.getReg r = s.getReg r) ∧
        readBuffer s1 commitChainScratch 32 = chainIter c96 l (levelChain l - 2) d1 ∧
        readBuffer s1 (commitChainScratch + 32) 32 = 0 ∧
        readBuffer s1 (commitChainScratch + 72) 24 = 0 ∧
        MemPreservedOutside s s1 commitChainScratch (commitChainScratch + 72) by
    have hrem : m + (levelChain l - 2 - m) = levelChain l - 2 := by omega
    have hpc' : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < levelChain l - 2 - m then 148445 else 148449)) := by
      simpa only [show (0 < levelChain l - 2 - m) ↔ (m < levelChain l - 2) by omega] using hpc
    exact hgen (levelChain l - 2 - m) m hrem s0 hpc' hx5 hx10 hx11 hx12 hx13 hx18 hx23 hx30 hcur hmid0 hhi0
  intro rem
  induction rem with
  | zero =>
    intro m hm s hpc _ _ _ _ _ _ _ _ hcur hmid0 hhi0
    have hm_eq : m = levelChain l - 2 := by omega
    subst hm_eq
    refine ⟨s, DetRun.refl oracle (submission.image .commit) s,
      by simpa only [Nat.lt_irrefl, ite_false] using hpc,
      fun _ _ => rfl, hcur, hmid0, hhi0, MemPreservedOutside.refl s _ _⟩
  | succ rem ih =>
    intro m hm s hpc hx5 hx10 hx11 hx12 hx13 hx18 hx23 hx30 hcur hmid0 hhi0
    have hpc0 : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 148445) := by
      simpa only [show 0 < rem + 1 by omega, ite_true] using hpc
    -- 148445: SD x18, x23, 64
    let t1 := execInstrBr s (.SD .x18 .x23 (64#12))
    have ht1_addr : s.getReg .x18 + signExtend12 (64#12) = BitVec.ofNat 64 (commitChainScratch + 64) := by
      rw [hx18, add_signExtend12_ofNat_small _ 64 (by omega)]
    have hr1 : DetRun oracle (submission.image .commit) s 1 t1 1 0 :=
      commit_step1_tail (by omega) (by omega) hpc0 (by simp only [commitTailInstr])
        (ordinaryStep_SD s .x18 .x23 (64#12) (by rw [ht1_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have ht1_pc : t1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148446) := pc_step_idx s 148445 hpc0
    have ht1_reg : ∀ r : Reg, t1.getReg r = s.getReg r := reg_exec_SD s .x18 .x23 (64#12)
    have ht1_mem : t1.mem = (s.setMem (BitVec.ofNat 64 (commitChainScratch + 64))
        (BitVec.ofNat 64 (256 * l + 2 + m))).mem := by
      simp only [t1, execInstrBr, ht1_addr, hx23, c_mem_setPC]
    have ht1_pres : MemPreservedOutside s t1 (commitChainScratch + 64) (commitChainScratch + 72) := by
      intro q hq hout
      rw [getByte_of_mem_eq ht1_mem]
      exact setMem_getByte_ofNat s (commitChainScratch + 64) q _ (by omega) (by omega) hq hout
    have ht1_cur : readBuffer t1 commitChainScratch 32 = chainIter c96 l m d1 := by
      rw [ht1_pres.readBuffer_eq (by omega) (by omega)]; exact hcur
    have ht1_mid : readBuffer t1 (commitChainScratch + 32) 32 = 0 := by
      rw [ht1_pres.readBuffer_eq (by omega) (by omega)]; exact hmid0
    have ht1_hi : readBuffer t1 (commitChainScratch + 72) 24 = 0 := by
      rw [ht1_pres.readBuffer_eq (by omega) (by omega)]; exact hhi0
    have ht1_tag : readBuffer t1 (commitChainScratch + 64) 8 = levelTag l (m + 2) := by
      rw [readBuffer_word t1 (commitChainScratch + 64) (by omega)]
      have hgm : t1.getMem (BitVec.ofNat 64 (commitChainScratch + 64)) =
          BitVec.ofNat 64 (256 * l + 2 + m) := by
        change t1.mem (BitVec.ofNat 64 (commitChainScratch + 64)) = _
        rw [ht1_mem]
        exact MachineState.getMem_setMem_eq (s := s) (a := BitVec.ofNat 64 (commitChainScratch + 64))
      rw [hgm]
      unfold levelTag; exact congrArg (BitVec.ofNat 64) (by omega)
    have ht1_in : readBuffer t1 commitChainScratch 96 =
        chainStepInput (chainIter c96 l m d1) (levelTag l (m + 2)) := by
      rw [readBuffer_chainStep t1 commitChainScratch (levelTag l (m + 2)) ht1_mid ht1_tag ht1_hi, ht1_cur]
    -- 148446: ECALL -> write next = chainIter c96 l (m+1) d1 to commitChainScratch
    let nxt := chainIter c96 l (m + 1) d1
    let t2 := writeBits t1 (BitVec.ofNat 64 commitChainScratch) nxt
    have hf46 : fetch (submission.image .commit) t1 = some (.base .ECALL) := by
      have h := commit_fetch_commitTailInstr t1 148446 (by omega) (by omega) ht1_pc
      simp only [commitTailInstr] at h; exact h
    have hr2 : DetRun oracle (submission.image .commit) t1 1 t2 8 1 :=
      DetRun.compress_eq h768 hf46 ((ht1_reg .x5).trans hx5) ((ht1_reg .x11).trans hx11)
        ((ht1_reg .x13).trans hx13) commitChainScratch commitChainScratch
        ((ht1_reg .x10).trans hx10) ((ht1_reg .x12).trans hx12)
        (by omega) (by omega) (by omega) (by omega) nxt (by rw [ht1_in]; rfl)
    have ht2_pc : t2.pc = BitVec.ofNat 64 (0x1000 + 4 * 148447) := pc_step_idx t1 148446 ht1_pc
    have ht2_reg : ∀ r : Reg, t2.getReg r = s.getReg r := fun r => (writeBits_register t1 _ nxt r).trans (ht1_reg r)
    have ht2_pres : MemPreservedOutside t1 t2 commitChainScratch (commitChainScratch + 32) :=
      memPreserved_writeBits t1 commitChainScratch nxt (by omega)
    -- 148447: ADDI x23, x23, 1; 148448: BNE x23, x30, 8180#13
    let t3 := execInstrBr t2 (.ADDI .x23 .x23 (1#12))
    let t4 := execInstrBr t3 (.BNE .x23 .x30 (8180#13))
    have ht3_pc : t3.pc = BitVec.ofNat 64 (0x1000 + 4 * 148448) := pc_step_idx t2 148447 ht2_pc
    have hr3 : DetRun oracle (submission.image .commit) t2 1 t3 1 0 :=
      commit_step1_tail (by omega) (by omega) ht2_pc (by simp only [commitTailInstr])
    have hr4 : DetRun oracle (submission.image .commit) t3 1 t4 1 0 :=
      commit_step1_tail (by omega) (by omega) ht3_pc (by simp only [commitTailInstr])
    have ht4_mem : t4.mem = t2.mem := (mem_exec_BNE t3 _ _ _).trans (mem_exec_ADDI t2 _ _ _)
    have ht3_x23 : t3.getReg .x23 = BitVec.ofNat 64 (256 * l + 2 + (m + 1)) := by
      simp only [t3, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x23 ≠ .x0), ht2_reg .x23, hx23,
        add_signExtend12_ofNat_small _ 1 (by omega)]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have ht3_x30 : t3.getReg .x30 = BitVec.ofNat 64 (256 * l + levelChain l) := by
      simp only [t3, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x23 .x30 (by decide), ht2_reg .x30, hx30]
    have ht4_reg_other : ∀ r : Reg, r ≠ .x23 → t4.getReg r = s.getReg r := fun r h23 => by
      rw [reg_exec_BNE t3 _ _ _ r]
      simp only [t3, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x23 r (Ne.symm h23), ht2_reg r]
    have ht4_pc : t4.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < rem then 148445 else 148449)) := by
      by_cases hrem' : 0 < rem
      · have hne : (t3.getReg .x23 != t3.getReg .x30) = true := by
          rw [ht3_x23, ht3_x30, bne_iff_ne]
          exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
        simp only [hrem', ite_true, t4, execInstrBr, hne, pc_setPC, ht3_pc]
        exact pc_bne_148448
      · have heq : (t3.getReg .x23 != t3.getReg .x30) = false := by
          rw [ht3_x23, ht3_x30, show 256 * l + 2 + (m + 1) = 256 * l + levelChain l by omega]
          exact bne_self_eq_false _
        simp only [hrem', ite_false, t4, execInstrBr, heq, Bool.false_eq_true, pc_setPC]
        exact pc_step_idx t3 148448 ht3_pc
    have ht4_pres : MemPreservedOutside s t4 commitChainScratch (commitChainScratch + 72) :=
      ((ht1_pres.mono (by omega) (le_refl _)).trans (ht2_pres.mono (le_refl _) (by omega))).trans
        (MemPreservedOutside.of_mem_eq ht4_mem _ _)
    obtain ⟨s1, hrun_rest, hs1_pc, hs1_reg, hs1_cur, hs1_mid, hs1_hi, hs1_pres⟩ :=
      ih (m + 1) (by omega) t4 ht4_pc
        ((ht4_reg_other .x5 (by decide)).trans hx5) ((ht4_reg_other .x10 (by decide)).trans hx10)
        ((ht4_reg_other .x11 (by decide)).trans hx11) ((ht4_reg_other .x12 (by decide)).trans hx12)
        ((ht4_reg_other .x13 (by decide)).trans hx13) ((ht4_reg_other .x18 (by decide)).trans hx18)
        ((reg_exec_BNE t3 _ _ _ .x23).trans ht3_x23) ((ht4_reg_other .x30 (by decide)).trans hx30)
        ((readBuffer_of_mem_eq ht4_mem _ _).trans (writeBits_readBuffer_digest t1 commitChainScratch nxt))
        ((readBuffer_of_mem_eq ht4_mem _ _).trans ((ht2_pres.readBuffer_eq (by omega) (by omega)).trans ht1_mid))
        ((readBuffer_of_mem_eq ht4_mem _ _).trans ((ht2_pres.readBuffer_eq (by omega) (by omega)).trans ht1_hi))
    have hrun_tot : DetRun oracle (submission.image .commit) s (4 * (rem + 1)) s1 (11 * (rem + 1)) (rem + 1) := by
      have h := (((hr1.trans hr2).trans hr3).trans hr4).trans hrun_rest
      rw [show 1 + 1 + 1 + 1 + 4 * rem = 4 * (rem + 1) by omega,
          show 1 + 8 + 1 + 1 + 11 * rem = 11 * (rem + 1) by omega,
          show 0 + 1 + 0 + 0 + rem = rem + 1 by omega] at h
      exact h
    exact ⟨s1, hrun_tot, hs1_pc, fun r h23 => (hs1_reg r h23).trans (ht4_reg_other r h23),
      hs1_cur, hs1_mid, hs1_hi, ht4_pres.trans hs1_pres⟩

/-- One node step of Phase 3C (words `148429..148457`) computing `nodeVal l idx` for `9 ≤ l ≤ 23`. -/
private theorem levelChain_eq_one_of_le (l : Nat) (hl1 : 9 ≤ l) (hl2 : l ≤ 23) (h : levelChain l ≤ 1) :
    levelChain l = 1 := by
  interval_cases l <;> simp [levelChain] at h ⊢

private theorem p3c_node_chain_branch (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (l : Nat) (hl1 : 9 ≤ l) (hl2 : l ≤ 23) (hch1 : ¬ levelChain l ≤ 1)
    (srcAddr dstAddr : Nat)
    (hsrc_lo : C_TD ≤ srcAddr) (hsrc_hi : srcAddr + 96 ≤ C_TD + treeBytes) (hsrc_al : srcAddr % 8 = 0)
    (hdst_lo : C_TD ≤ dstAddr) (hdst_hi : dstAddr + 32 ≤ C_TD + treeBytes) (hdst_al : dstAddr % 8 = 0)
    (hdisj : srcAddr + 96 ≤ dstAddr)
    (leftD rightD : Digest) (s0 p6 : MachineState)
    (hp6_pc : p6.pc = BitVec.ofNat 64 (0x1000 + 4 * 148438))
    (hp6_mem : p6.mem = s0.mem)
    (hp6_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x22 → p6.getReg r = s0.getReg r)
    (hp6_x10 : p6.getReg .x10 = BitVec.ofNat 64 srcAddr)
    (hp6_x22 : p6.getReg .x22 = BitVec.ofNat 64 dstAddr)
    (hx5 : s0.getReg .x5 = 0#64) (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx14 : s0.getReg .x14 = BitVec.ofNat 64 srcAddr)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 commitChainScratch)
    (hx28 : s0.getReg .x28 = BitVec.ofNat 64 (levelTagStart l))
    (hx30 : s0.getReg .x30 = BitVec.ofNat 64 (levelTagStart l + (levelChain l - 1)))
    (hleft : readBuffer s0 srcAddr 32 = leftD)
    (hright : readBuffer s0 (srcAddr + 32) 32 = rightD)
    (hgap : ∀ j < 32, s0.getByte (BitVec.ofNat 64 (srcAddr + 64 + j)) = 0)
    (hscrMid : readBuffer s0 (commitChainScratch + 32) 32 = 0)
    (hscrHi : readBuffer s0 (commitChainScratch + 72) 24 = 0) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ sm,
      DetRun oracle (submission.image .commit) p6
        (10 + 4 * (levelChain l - 2)) sm (24 + 11 * (levelChain l - 2)) (levelChain l) ∧
      sm.pc = BitVec.ofNat 64 (0x1000 + 4 * 148452) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x23 → sm.getReg r = s0.getReg r) ∧
      sm.getReg .x22 = BitVec.ofNat 64 dstAddr ∧
      readBuffer sm dstAddr 32 = chainEval c96 l leftD rightD ∧
      readBuffer sm (commitChainScratch + 32) 32 = 0 ∧
      readBuffer sm (commitChainScratch + 72) 24 = 0 ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < dstAddr ∨ dstAddr + 32 ≤ q) →
        (q < commitChainScratch ∨ commitChainScratch + 72 ≤ q) →
        sm.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hCS : commitChainScratch = 8589934592 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have htb := treeBytes_eq
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hch2 : 2 ≤ levelChain l := by omega
  have hcl16 : levelChain l ≤ 16 := by
    simpa only [show 9 + (l - 9) = l by omega] using p3c_chain_le_16 (l - 9) (by omega)
  have hts : levelTagStart l = 256 * l + 1 := by
    simpa only [show 9 + (l - 9) = l by omega] using
      p3c_tagStart_eq (l - 9) (by omega) (by simpa only [show 9 + (l - 9) = l by omega] using hch1)
  let d1 := c96 (binaryTaggedInput leftD rightD (levelTag l 1))
  have hst1 : ∃ c4,
      DetRun oracle (submission.image .commit) p6 4 c4 11 1 ∧
      c4.pc = BitVec.ofNat 64 (0x1000 + 4 * 148442) ∧
      (∀ r : Reg, r ≠ .x12 → c4.getReg r = p6.getReg r) ∧
      c4.getReg .x12 = BitVec.ofNat 64 commitChainScratch ∧
      readBuffer c4 commitChainScratch 32 = chainIter c96 l 0 d1 ∧
      MemPreservedOutside s0 c4 commitChainScratch (commitChainScratch + 32) := by
    let c1 := execInstrBr p6 (.SD .x14 .x28 (64#12))
    let c2 := execInstrBr c1 (.ADDI .x12 .x18 (0#12))
    let c3 := writeBits c2 (BitVec.ofNat 64 commitChainScratch) d1
    let c4 := execInstrBr c3 (.SD .x14 .x0 (64#12))
    have hc1_addr : p6.getReg .x14 + signExtend12 (64#12) = BitVec.ofNat 64 (srcAddr + 64) := by
      rw [hp6_reg_other .x14 (by decide) (by decide) (by decide), hx14, add_signExtend12_ofNat_small _ 64 (by omega)]
    have hrc1 : DetRun oracle (submission.image .commit) p6 1 c1 1 0 :=
      commit_step1_tail (by omega) (by omega) hp6_pc (by simp only [commitTailInstr])
        (ordinaryStep_SD p6 .x14 .x28 (64#12) (by rw [hc1_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have hc1_pc : c1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148439) := pc_step_idx p6 148438 hp6_pc
    have hc2_pc : c2.pc = BitVec.ofNat 64 (0x1000 + 4 * 148440) := pc_step_idx c1 148439 hc1_pc
    have hc3_pc : c3.pc = BitVec.ofNat 64 (0x1000 + 4 * 148441) := pc_step_idx c2 148440 hc2_pc
    have hc4_pc : c4.pc = BitVec.ofNat 64 (0x1000 + 4 * 148442) := pc_step_idx c3 148441 hc3_pc
    have hrc2 : DetRun oracle (submission.image .commit) c1 1 c2 1 0 :=
      commit_step1_tail (by omega) (by omega) hc1_pc (by simp only [commitTailInstr])
    have hc1_reg : ∀ r : Reg, c1.getReg r = p6.getReg r := reg_exec_SD p6 .x14 .x28 (64#12)
    have hc2_reg : ∀ r : Reg, r ≠ .x12 → c2.getReg r = p6.getReg r := fun r h12 => by
      simp only [c2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12), hc1_reg r]
    have hc2_x12 : c2.getReg .x12 = BitVec.ofNat 64 commitChainScratch := by
      simp only [c2, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hc1_reg .x18,
        hp6_reg_other .x18 (by decide) (by decide) (by decide), hx18,
        add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
    have hc2_mem : c2.mem = (s0.setMem (BitVec.ofNat 64 (srcAddr + 64)) (levelTag l 1)).mem := by
      have h28 : p6.getReg .x28 = levelTag l 1 := by
        rw [hp6_reg_other .x28 (by decide) (by decide) (by decide), hx28, hts]; rfl
      have h1 : c1.mem = (p6.setMem (BitVec.ofNat 64 (srcAddr + 64)) (levelTag l 1)).mem := by
        simp only [c1, execInstrBr, hc1_addr, h28, c_mem_setPC]
      rw [mem_exec_ADDI c1 _ _ _, h1]
      simp only [MachineState.setMem, hp6_mem]
    have hc2_pres : MemPreservedOutside s0 c2 (srcAddr + 64) (srcAddr + 72) := by
      intro q hq hout
      rw [getByte_of_mem_eq hc2_mem]
      exact setMem_getByte_ofNat s0 (srcAddr + 64) q _ (by omega) (by omega) hq hout
    have hc2_in : readBuffer c2 srcAddr 96 = binaryTaggedInput leftD rightD (levelTag l 1) := by
      have htag : readBuffer c2 (srcAddr + 64) 8 = levelTag l 1 := by
        rw [readBuffer_word c2 (srcAddr + 64) (by omega)]
        change c2.mem (BitVec.ofNat 64 (srcAddr + 64)) = levelTag l 1
        rw [hc2_mem]
        exact MachineState.getMem_setMem_eq (s := s0)
      have hhi : readBuffer c2 (srcAddr + 72) 24 = 0 := by
        apply readBuffer_zero_of_bytes; intro j hj
        rw [hc2_pres (srcAddr + 72 + j) (by omega) (Or.inr (by omega))]
        have : srcAddr + 72 + j = srcAddr + 64 + (8 + j) := by omega
        rw [this]; exact hgap (8 + j) (by omega)
      rw [readBuffer_binaryTagged c2 srcAddr (levelTag l 1) htag hhi,
        hc2_pres.readBuffer_eq (by omega) (by omega), hc2_pres.readBuffer_eq (by omega) (by omega),
        hleft, hright]
    have hf40 : fetch (submission.image .commit) c2 = some (.base .ECALL) := by
      have h := commit_fetch_commitTailInstr c2 148440 (by omega) (by omega) hc2_pc
      simp only [commitTailInstr] at h; exact h
    have hrc3 : DetRun oracle (submission.image .commit) c2 1 c3 8 1 :=
      DetRun.compress_eq h768 hf40
        ((hc2_reg .x5 (by decide)).trans ((hp6_reg_other .x5 (by decide) (by decide) (by decide)).trans hx5))
        ((hc2_reg .x11 (by decide)).trans ((hp6_reg_other .x11 (by decide) (by decide) (by decide)).trans hx11))
        ((hc2_reg .x13 (by decide)).trans ((hp6_reg_other .x13 (by decide) (by decide) (by decide)).trans hx13))
        srcAddr commitChainScratch ((hc2_reg .x10 (by decide)).trans hp6_x10) hc2_x12
        (by omega) (by omega) (by omega) (by omega) d1 (by rw [hc2_in])
    have hc3_reg : ∀ r : Reg, c3.getReg r = c2.getReg r := writeBits_register c2 _ d1
    have hc3_addr : c3.getReg .x14 + signExtend12 (64#12) = BitVec.ofNat 64 (srcAddr + 64) := by
      rw [hc3_reg .x14, hc2_reg .x14 (by decide), hp6_reg_other .x14 (by decide) (by decide) (by decide),
        hx14, add_signExtend12_ofNat_small _ 64 (by omega)]
    have hrc4 : DetRun oracle (submission.image .commit) c3 1 c4 1 0 :=
      commit_step1_tail (by omega) (by omega) hc3_pc (by simp only [commitTailInstr])
        (ordinaryStep_SD c3 .x14 .x0 (64#12) (by rw [hc3_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have hc3_pres : MemPreservedOutside c2 c3 commitChainScratch (commitChainScratch + 32) :=
      memPreserved_writeBits c2 commitChainScratch d1 (by omega)
    have hc4_mem : c4.mem = (c3.setMem (BitVec.ofNat 64 (srcAddr + 64)) 0#64).mem := by
      simp only [c4, execInstrBr, hc3_addr, c_getReg_x0, c_mem_setPC]
    have hc4_pres : MemPreservedOutside s0 c4 commitChainScratch (commitChainScratch + 32) := by
      intro q hq hout
      rw [getByte_of_mem_eq hc4_mem]
      by_cases hgap8 : srcAddr + 64 ≤ q ∧ q < srcAddr + 72
      · have hj : q - (srcAddr + 64) < 8 := by omega
        have hqeq : srcAddr + 64 + (q - (srcAddr + 64)) = q := by omega
        rw [← hqeq, setMem_getByte_inside c3 (srcAddr + 64) (q - (srcAddr + 64)) 0#64 (by omega) hj]
        rw [hgap (q - (srcAddr + 64)) (by omega)]; exact BitVec.extractLsb'_zero
      · rw [setMem_getByte_ofNat c3 (srcAddr + 64) q 0#64 (by omega) (by omega) hq (by omega)]
        exact (hc3_pres q hq hout).trans (hc2_pres q hq (by omega))
    have hc4_cur : readBuffer c4 commitChainScratch 32 = chainIter c96 l 0 d1 := by
      rw [readBuffer_congr c4 c3 commitChainScratch 32 (fun j hj => by
        rw [getByte_of_mem_eq hc4_mem]
        exact setMem_getByte_ofNat c3 (srcAddr + 64) (commitChainScratch + j) 0#64
          (by omega) (by omega) (by omega) (Or.inr (by omega)))]
      exact writeBits_readBuffer_digest c2 commitChainScratch d1
    exact ⟨c4, ((hrc1.trans hrc2).trans hrc3).trans hrc4, hc4_pc,
      fun r h12 => ((reg_exec_SD c3 _ _ _ r).trans (hc3_reg r)).trans (hc2_reg r h12),
      ((reg_exec_SD c3 _ _ _ .x12).trans (hc3_reg .x12)).trans hc2_x12,
      hc4_cur, hc4_pres⟩
  obtain ⟨c4, hrc14, hc4_pc, hc4_reg, hc4_x12, hc4_cur, hc4_pres⟩ := hst1
  have hst2 : ∃ c7,
      DetRun oracle (submission.image .commit) c4 3 c7 3 0 ∧
      c7.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < levelChain l - 2 then 148445 else 148449)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → r ≠ .x23 → c7.getReg r = p6.getReg r) ∧
      c7.getReg .x10 = BitVec.ofNat 64 commitChainScratch ∧
      c7.getReg .x12 = BitVec.ofNat 64 commitChainScratch ∧
      c7.getReg .x23 = BitVec.ofNat 64 (256 * l + 2 + 0) ∧
      c7.getReg .x30 = BitVec.ofNat 64 (256 * l + levelChain l) ∧
      c7.mem = c4.mem := by
    let c5 := execInstrBr c4 (.ADDI .x23 .x28 (1#12))
    let c6 := execInstrBr c5 (.ADDI .x10 .x18 (0#12))
    let c7 := execInstrBr c6 (.BEQ .x23 .x30 (20#13))
    have hc5_pc : c5.pc = BitVec.ofNat 64 (0x1000 + 4 * 148443) := pc_step_idx c4 148442 hc4_pc
    have hc6_pc : c6.pc = BitVec.ofNat 64 (0x1000 + 4 * 148444) := pc_step_idx c5 148443 hc5_pc
    have hrc5 : DetRun oracle (submission.image .commit) c4 1 c5 1 0 :=
      commit_step1_tail (by omega) (by omega) hc4_pc (by simp only [commitTailInstr])
    have hrc6 : DetRun oracle (submission.image .commit) c5 1 c6 1 0 :=
      commit_step1_tail (by omega) (by omega) hc5_pc (by simp only [commitTailInstr])
    have hrc7 : DetRun oracle (submission.image .commit) c6 1 c7 1 0 :=
      commit_step1_tail (by omega) (by omega) hc6_pc (by simp only [commitTailInstr])
    have hc7_mem : c7.mem = c4.mem :=
      ((mem_exec_BEQ c6 _ _ _).trans (mem_exec_ADDI c5 _ _ _)).trans (mem_exec_ADDI c4 _ _ _)
    have hc6_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → r ≠ .x23 → c6.getReg r = p6.getReg r :=
      fun r h10 h12 h23 => by
        simp only [c6, c5, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 r (Ne.symm h10), getReg_setReg_ne' .x23 r (Ne.symm h23), hc4_reg r h12]
    have hc6_x23 : c6.getReg .x23 = BitVec.ofNat 64 (256 * l + 2 + 0) := by
      simp only [c6, c5, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x10 .x23 (by decide),
        MachineState.getReg_setReg_eq (by decide : Reg.x23 ≠ .x0), hc4_reg .x28 (by decide),
        hp6_reg_other .x28 (by decide) (by decide) (by decide), hx28, hts,
        add_signExtend12_ofNat_small _ 1 (by omega)]
    have hc6_x30 : c6.getReg .x30 = BitVec.ofNat 64 (256 * l + levelChain l) := by
      rw [hc6_reg_other .x30 (by decide) (by decide) (by decide),
        hp6_reg_other .x30 (by decide) (by decide) (by decide), hx30, hts]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hc7_x10 : c7.getReg .x10 = BitVec.ofNat 64 commitChainScratch := by
      rw [reg_exec_BEQ c6 _ _ _ .x10]
      simp only [c6, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
        show c5.getReg .x18 = p6.getReg .x18 by
          simp only [c5, execInstrBr, MachineState.getReg_setPC,
            getReg_setReg_ne' .x23 .x18 (by decide), hc4_reg .x18 (by decide)],
        hp6_reg_other .x18 (by decide) (by decide) (by decide), hx18,
        add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
    have hc7_x12 : c7.getReg .x12 = BitVec.ofNat 64 commitChainScratch := by
      rw [reg_exec_BEQ c6 _ _ _ .x12]
      simp only [c6, c5, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x10 .x12 (by decide), getReg_setReg_ne' .x23 .x12 (by decide), hc4_x12]
    have hc7_pc : c7.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < levelChain l - 2 then 148445 else 148449)) := by
      by_cases hm : 0 < levelChain l - 2
      · have hne : (c6.getReg .x23 == c6.getReg .x30) = false := by
          rw [hc6_x23, hc6_x30, beq_eq_false_iff_ne]
          exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
        simp only [hm, ite_true, c7, execInstrBr, hne, Bool.false_eq_true, ite_false, pc_setPC]
        exact pc_step_idx c6 148444 hc6_pc
      · have heq : (c6.getReg .x23 == c6.getReg .x30) = true := by
          rw [hc6_x23, hc6_x30, show 256 * l + 2 + 0 = 256 * l + levelChain l by omega]
          exact beq_self_eq_true _
        simp only [hm, ite_false, c7, execInstrBr, heq, ite_true, pc_setPC, hc6_pc]
        exact pc_beq_148444
    exact ⟨c7, (hrc5.trans hrc6).trans hrc7, hc7_pc,
      fun r h10 h12 h23 => (reg_exec_BEQ c6 _ _ _ r).trans (hc6_reg_other r h10 h12 h23),
      hc7_x10, hc7_x12, (reg_exec_BEQ c6 _ _ _ .x23).trans hc6_x23,
      (reg_exec_BEQ c6 _ _ _ .x30).trans hc6_x30, hc7_mem⟩
  obtain ⟨c7, hrc57, hc7_pc, hc7_reg_other, hc7_x10, hc7_x12, hc7_x23, hc7_x30, hc7_mem⟩ := hst2
  have hc7_cur : readBuffer c7 commitChainScratch 32 = chainIter c96 l 0 d1 :=
    (readBuffer_of_mem_eq hc7_mem _ _).trans hc4_cur
  have hc7_pres : MemPreservedOutside s0 c7 commitChainScratch (commitChainScratch + 32) :=
    hc4_pres.trans (MemPreservedOutside.of_mem_eq hc7_mem _ _)
  obtain ⟨cm, hmid_run, hcm_pc, hcm_reg, hcm_cur, hcm_mid, hcm_hi, hcm_pres⟩ :=
    p3c_mid_loop h768 oracle l hl1 hl2 hch2 d1 c7 0 (by omega) hc7_pc
      ((hc7_reg_other .x5 (by decide) (by decide) (by decide)).trans ((hp6_reg_other .x5 (by decide) (by decide) (by decide)).trans hx5))
      hc7_x10
      ((hc7_reg_other .x11 (by decide) (by decide) (by decide)).trans ((hp6_reg_other .x11 (by decide) (by decide) (by decide)).trans hx11))
      hc7_x12
      ((hc7_reg_other .x13 (by decide) (by decide) (by decide)).trans ((hp6_reg_other .x13 (by decide) (by decide) (by decide)).trans hx13))
      ((hc7_reg_other .x18 (by decide) (by decide) (by decide)).trans ((hp6_reg_other .x18 (by decide) (by decide) (by decide)).trans hx18))
      hc7_x23 hc7_x30
      hc7_cur
      ((hc7_pres.readBuffer_eq (by omega) (by omega)).trans hscrMid)
      ((hc7_pres.readBuffer_eq (by omega) (by omega)).trans hscrHi)
  let f1 := execInstrBr cm (.SD .x18 .x30 (64#12))
  let f2 := execInstrBr f1 (.ADDI .x12 .x22 (0#12))
  let res := chainEval c96 l leftD rightD
  let f3 := writeBits f2 (BitVec.ofNat 64 dstAddr) res
  have hf1_addr : cm.getReg .x18 + signExtend12 (64#12) = BitVec.ofNat 64 (commitChainScratch + 64) := by
    rw [hcm_reg .x18 (by decide), hc7_reg_other .x18 (by decide) (by decide) (by decide),
      hp6_reg_other .x18 (by decide) (by decide) (by decide), hx18, add_signExtend12_ofNat_small _ 64 (by omega)]
  have hrf1 : DetRun oracle (submission.image .commit) cm 1 f1 1 0 :=
    commit_step1_tail (by omega) (by omega) hcm_pc (by simp only [commitTailInstr])
      (ordinaryStep_SD cm .x18 .x30 (64#12) (by rw [hf1_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hf1_pc : f1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148450) := pc_step_idx cm 148449 hcm_pc
  have hf2_pc : f2.pc = BitVec.ofNat 64 (0x1000 + 4 * 148451) := pc_step_idx f1 148450 hf1_pc
  have hf3_pc : f3.pc = BitVec.ofNat 64 (0x1000 + 4 * 148452) := pc_step_idx f2 148451 hf2_pc
  have hrf2 : DetRun oracle (submission.image .commit) f1 1 f2 1 0 :=
    commit_step1_tail (by omega) (by omega) hf1_pc (by simp only [commitTailInstr])
  have hf1_reg : ∀ r : Reg, f1.getReg r = cm.getReg r := reg_exec_SD cm .x18 .x30 (64#12)
  have hf2_reg : ∀ r : Reg, r ≠ .x12 → f2.getReg r = cm.getReg r := fun r h12 => by
    simp only [f2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12), hf1_reg r]
  have hf2_x22 : f2.getReg .x22 = BitVec.ofNat 64 dstAddr :=
    (hf2_reg .x22 (by decide)).trans ((hcm_reg .x22 (by decide)).trans
      ((hc7_reg_other .x22 (by decide) (by decide) (by decide)).trans hp6_x22))
  have hf2_x12 : f2.getReg .x12 = BitVec.ofNat 64 dstAddr := by
    simp only [f2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hf1_reg .x22,
      hcm_reg .x22 (by decide), hc7_reg_other .x22 (by decide) (by decide) (by decide), hp6_x22,
      add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
  have hf2_mem : f2.mem = (cm.setMem (BitVec.ofNat 64 (commitChainScratch + 64)) (levelTag l (levelChain l))).mem := by
    have h30 : cm.getReg .x30 = levelTag l (levelChain l) := by
      rw [hcm_reg .x30 (by decide), hc7_x30]; rfl
    rw [mem_exec_ADDI f1 _ _ _]
    simp only [f1, execInstrBr, hf1_addr, h30, c_mem_setPC]
  have hf2_pres : MemPreservedOutside cm f2 (commitChainScratch + 64) (commitChainScratch + 72) := by
    intro q hq hout
    rw [getByte_of_mem_eq hf2_mem]
    exact setMem_getByte_ofNat cm (commitChainScratch + 64) q _ (by omega) (by omega) hq hout
  have hf2_in : readBuffer f2 commitChainScratch 96 =
      chainStepInput (chainIter c96 l (levelChain l - 2) d1) (levelTag l (levelChain l)) := by
    have htag : readBuffer f2 (commitChainScratch + 64) 8 = levelTag l (levelChain l) := by
      rw [readBuffer_word f2 (commitChainScratch + 64) (by omega)]
      change f2.mem (BitVec.ofNat 64 (commitChainScratch + 64)) = levelTag l (levelChain l)
      rw [hf2_mem]
      exact MachineState.getMem_setMem_eq (s := cm)
    rw [readBuffer_chainStep f2 commitChainScratch (levelTag l (levelChain l))
      ((hf2_pres.readBuffer_eq (by omega) (by omega)).trans hcm_mid)
      htag
      ((hf2_pres.readBuffer_eq (by omega) (by omega)).trans hcm_hi),
      hf2_pres.readBuffer_eq (by omega) (by omega), hcm_cur]
  have hres_eq : c96 (chainStepInput (chainIter c96 l (levelChain l - 2) d1) (levelTag l (levelChain l))) = res := by
    have hsub : levelChain l - 1 = (levelChain l - 2) + 1 := by omega
    have hadd : (levelChain l - 2) + 2 = levelChain l := by omega
    simp only [res, chainEval, hch1, ite_false]
    rw [hsub, chainIter, hadd]
  have hf51 : fetch (submission.image .commit) f2 = some (.base .ECALL) := by
    have h := commit_fetch_commitTailInstr f2 148451 (by omega) (by omega) hf2_pc
    simp only [commitTailInstr] at h; exact h
  have hrf3 : DetRun oracle (submission.image .commit) f2 1 f3 8 1 :=
    DetRun.compress_eq h768 hf51
      ((hf2_reg .x5 (by decide)).trans ((hcm_reg .x5 (by decide)).trans
        ((hc7_reg_other .x5 (by decide) (by decide) (by decide)).trans
          ((hp6_reg_other .x5 (by decide) (by decide) (by decide)).trans hx5))))
      ((hf2_reg .x11 (by decide)).trans ((hcm_reg .x11 (by decide)).trans
        ((hc7_reg_other .x11 (by decide) (by decide) (by decide)).trans
          ((hp6_reg_other .x11 (by decide) (by decide) (by decide)).trans hx11))))
      ((hf2_reg .x13 (by decide)).trans ((hcm_reg .x13 (by decide)).trans
        ((hc7_reg_other .x13 (by decide) (by decide) (by decide)).trans
          ((hp6_reg_other .x13 (by decide) (by decide) (by decide)).trans hx13))))
      commitChainScratch dstAddr
      ((hf2_reg .x10 (by decide)).trans ((hcm_reg .x10 (by decide)).trans hc7_x10))
      hf2_x12 (by omega) (by omega) (by omega) (by omega) res (by rw [hf2_in]; exact hres_eq)
  have hf3_pres : MemPreservedOutside f2 f3 dstAddr (dstAddr + 32) :=
    memPreserved_writeBits f2 dstAddr res (by omega)
  have hrun_ch : DetRun oracle (submission.image .commit) p6
      (10 + 4 * (levelChain l - 2)) f3 (24 + 11 * (levelChain l - 2)) (levelChain l) := by
    have h := (((hrc14.trans hrc57).trans hmid_run).trans ((hrf1.trans hrf2).trans hrf3))
    rw [show 4 + 3 + 4 * (levelChain l - 2 - 0) + (1 + 1 + 1) =
          10 + 4 * (levelChain l - 2) by omega,
        show 11 + 3 + 11 * (levelChain l - 2 - 0) + (1 + 1 + 8) =
          24 + 11 * (levelChain l - 2) by omega,
        show 1 + 0 + (levelChain l - 2 - 0) + (0 + 0 + 1) =
          levelChain l by omega] at h
    exact h
  refine ⟨f3, hrun_ch, hf3_pc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h6 h10 h12 h22 h23
    rw [writeBits_register, hf2_reg r h12, hcm_reg r h23, hc7_reg_other r h10 h12 h23, hp6_reg_other r h6 h10 h22]
  · rw [writeBits_register, hf2_x22]
  · exact writeBits_readBuffer_digest f2 dstAddr res
  · rw [hf3_pres.readBuffer_eq (by omega) (by omega), hf2_pres.readBuffer_eq (by omega) (by omega)]; exact hcm_mid
  · rw [hf3_pres.readBuffer_eq (by omega) (by omega), hf2_pres.readBuffer_eq (by omega) (by omega)]; exact hcm_hi
  · intro q hq houtD houtS
    exact (((hf3_pres q hq houtD).trans (hf2_pres q hq (by omega))).trans (hcm_pres q hq houtS)).trans
      (hc7_pres q hq (by omega))

private theorem p3c_node_step (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (l idx : Nat) (hl1 : 9 ≤ l) (hl2 : l ≤ 23) (hidx : idx < levelSize l)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 148429))
    (hx5 : s0.getReg .x5 = 0#64) (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx14 : s0.getReg .x14 = BitVec.ofNat 64 (C_TD + levelBase (l - 1) + 96 * idx))
    (hx15 : s0.getReg .x15 = BitVec.ofNat 64 (C_TD + levelBase l))
    (hx16 : s0.getReg .x16 = BitVec.ofNat 64 (levelSize l))
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 commitChainScratch)
    (hx19 : s0.getReg .x19 = BitVec.ofNat 64 (levelChain l - 1))
    (hx20 : s0.getReg .x20 = BitVec.ofNat 64 idx)
    (hx27 : s0.getReg .x27 = maskTopWord (levelWidth l))
    (hx28 : s0.getReg .x28 = BitVec.ofNat 64 (levelTagStart l))
    (hx30 : s0.getReg .x30 = BitVec.ofNat 64 (levelTagStart l + (levelChain l - 1)))
    (hleft : readBuffer s0 (C_TD + levelBase (l - 1) + 96 * idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (l - 1) (2 * idx))
    (hright : readBuffer s0 (C_TD + levelBase (l - 1) + 96 * idx + 32) 32 =
      if 2 * idx + 1 < levelSize (l - 1) then
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (l - 1) (2 * idx + 1)
      else 0)
    (hgap : ∀ j < 32, s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (l - 1) + 96 * idx + 64 + j)) = 0)
    (hscrMid : readBuffer s0 (commitChainScratch + 32) 32 = 0)
    (hscrHi : readBuffer s0 (commitChainScratch + 72) 24 = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 (p3cNodeSteps l) s1 (p3cNodeCycles l) (levelChain l) ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (if idx + 1 < levelSize l then 148429 else 148458)) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x14 → r ≠ .x20 → r ≠ .x22 → r ≠ .x23 →
        s1.getReg r = s0.getReg r) ∧
      s1.getReg .x14 = BitVec.ofNat 64 (C_TD + levelBase (l - 1) + 96 * (idx + 1)) ∧
      s1.getReg .x20 = BitVec.ofNat 64 (idx + 1) ∧
      readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx ∧
      readBuffer s1 (commitChainScratch + 32) 32 = 0 ∧
      readBuffer s1 (commitChainScratch + 72) 24 = 0 ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < C_TD + levelBase l + gapOffset idx ∨ C_TD + levelBase l + gapOffset idx + 32 ≤ q) →
        (q < commitChainScratch ∨ commitChainScratch + 72 ≤ q) →
        s1.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hCS : commitChainScratch = 8589934592 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have htb := treeBytes_eq
  have hsrcB := levelBase_bound (l - 1) (by omega)
  have hdstB := levelBase_bound l (by omega)
  have hsrcAl := levelBase_mod8 (l - 1) (by omega)
  have hdstAl := levelBase_mod8 l (by omega)
  have hsrcBytes := levelBytes_eq_gap (l - 1) (by omega) (by omega)
  have hdstBytes := levelBytes_eq_gap l (by omega) (by omega)
  have hlsStep : levelSize l = (levelSize (l - 1) + 1) / 2 := by
    have h := levelSize_step (l - 1) (by omega)
    simpa only [show l - 1 + 1 = l by omega] using h
  have hbase_step : levelBase l = levelBase (l - 1) + levelBytes (l - 1) := by
    have h : levelBase (l - 1 + 1) = levelBase (l - 1) + levelBytes (l - 1) := rfl
    simpa only [show l - 1 + 1 = l by omega] using h
  have hgo_bd := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
  have hgo_al : gapOffset idx % 8 = 0 := by unfold gapOffset; omega
  have hls_lt : levelSize l < 2 ^ 30 := by
    have := levelSize_le_max l (by omega); omega
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let leftD := nodeVal c96 msg salts (l - 1) (2 * idx)
  let rightD := if 2 * idx + 1 < levelSize (l - 1) then nodeVal c96 msg salts (l - 1) (2 * idx + 1) else 0
  let srcAddr := C_TD + levelBase (l - 1) + 96 * idx
  let dstAddr := C_TD + levelBase l + gapOffset idx
  -- Prefix 148429..148434 (6 steps, 6 cycles), opaque via `obtain`
  have hpre : ∃ p6,
      DetRun oracle (submission.image .commit) s0 6 p6 6 0 ∧
      p6.pc = BitVec.ofNat 64 (0x1000 + 4 * (if levelChain l ≤ 1 then 148435 else 148438)) ∧
      p6.mem = s0.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x22 → p6.getReg r = s0.getReg r) ∧
      p6.getReg .x10 = BitVec.ofNat 64 srcAddr ∧
      p6.getReg .x22 = BitVec.ofNat 64 dstAddr := by
    let p1 := execInstrBr s0 (.SRLI .x6 .x20 (1#6))
    let p2 := execInstrBr p1 (.ADD .x6 .x20 .x6)
    let p3 := execInstrBr p2 (.SLLI .x6 .x6 (5#6))
    let p4 := execInstrBr p3 (.ADD .x22 .x15 .x6)
    let p5 := execInstrBr p4 (.ADDI .x10 .x14 (0#12))
    let p6 := execInstrBr p5 (.BNE .x19 .x0 (16#13))
    have hp1_pc : p1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148430) := pc_step_idx s0 148429 hpc
    have hp2_pc : p2.pc = BitVec.ofNat 64 (0x1000 + 4 * 148431) := pc_step_idx p1 148430 hp1_pc
    have hp3_pc : p3.pc = BitVec.ofNat 64 (0x1000 + 4 * 148432) := pc_step_idx p2 148431 hp2_pc
    have hp4_pc : p4.pc = BitVec.ofNat 64 (0x1000 + 4 * 148433) := pc_step_idx p3 148432 hp3_pc
    have hp5_pc : p5.pc = BitVec.ofNat 64 (0x1000 + 4 * 148434) := pc_step_idx p4 148433 hp4_pc
    have hpre_run : DetRun oracle (submission.image .commit) s0 6 p6 6 0 := by
      have r1 : DetRun oracle (submission.image .commit) s0 1 p1 1 0 :=
        commit_step1_tail (by omega) (by omega) hpc (by simp only [commitTailInstr])
      have r2 : DetRun oracle (submission.image .commit) p1 1 p2 1 0 :=
        commit_step1_tail (by omega) (by omega) hp1_pc (by simp only [commitTailInstr])
      have r3 : DetRun oracle (submission.image .commit) p2 1 p3 1 0 :=
        commit_step1_tail (by omega) (by omega) hp2_pc (by simp only [commitTailInstr])
      have r4 : DetRun oracle (submission.image .commit) p3 1 p4 1 0 :=
        commit_step1_tail (by omega) (by omega) hp3_pc (by simp only [commitTailInstr])
      have r5 : DetRun oracle (submission.image .commit) p4 1 p5 1 0 :=
        commit_step1_tail (by omega) (by omega) hp4_pc (by simp only [commitTailInstr])
      have r6 : DetRun oracle (submission.image .commit) p5 1 p6 1 0 :=
        commit_step1_tail (by omega) (by omega) hp5_pc (by simp only [commitTailInstr])
      exact ((((r1.trans r2).trans r3).trans r4).trans r5).trans r6
    have hp6_mem : p6.mem = s0.mem :=
      (((((mem_exec_BNE p5 _ _ _).trans (mem_exec_ADDI p4 _ _ _)).trans
        (mem_exec_ADD p3 _ _ _)).trans (mem_exec_SLLI p2 _ _ _)).trans
        (mem_exec_ADD p1 _ _ _)).trans (mem_exec_SRLI s0 _ _ _)
    have hp5_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x22 → p5.getReg r = s0.getReg r :=
      fun r h6 h10 h22 => by
        simp only [p5, p4, p3, p2, p1, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 r (Ne.symm h10), getReg_setReg_ne' .x22 r (Ne.symm h22),
          getReg_setReg_ne' .x6 r (Ne.symm h6)]
    have hp5_x19 : p5.getReg .x19 = BitVec.ofNat 64 (levelChain l - 1) :=
      (hp5_reg_other .x19 (by decide) (by decide) (by decide)).trans hx19
    have hp6_pc : p6.pc = BitVec.ofNat 64 (0x1000 + 4 * (if levelChain l ≤ 1 then 148435 else 148438)) := by
      by_cases hch1 : levelChain l ≤ 1
      · have hch_eq1 : levelChain l = 1 := levelChain_eq_one_of_le l hl1 hl2 hch1
        have heq0 : (p5.getReg .x19 != p5.getReg .x0) = false := by
          rw [hp5_x19, hch_eq1, c_getReg_x0]; decide
        simp only [hch1, ite_true, p6, execInstrBr, heq0, Bool.false_eq_true, ite_false, pc_setPC]
        exact pc_step_idx p5 148434 hp5_pc
      · have hcl16 : levelChain l ≤ 16 := by
          simpa only [show 9 + (l - 9) = l by omega] using p3c_chain_le_16 (l - 9) (by omega)
        have hne0 : (p5.getReg .x19 != p5.getReg .x0) = true := by
          rw [hp5_x19, c_getReg_x0, bne_iff_ne]
          exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
        simp only [hch1, ite_false, p6, execInstrBr, hne0, ite_true, pc_setPC, hp5_pc]
        exact pc_bne_148434
    refine ⟨p6, hpre_run, hp6_pc, hp6_mem,
      fun r h6 h10 h22 => (reg_exec_BNE p5 _ _ _ r).trans (hp5_reg_other r h6 h10 h22), ?_, ?_⟩
    · rw [reg_exec_BNE p5 _ _ _ .x10]
      simp only [p5, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
        show p4.getReg .x14 = s0.getReg .x14 by
          simp only [p4, p3, p2, p1, execInstrBr, MachineState.getReg_setPC,
            getReg_setReg_ne' .x22 .x14 (by decide), getReg_setReg_ne' .x6 .x14 (by decide)],
        hx14, add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
      rfl
    · have hp3_x6 : p3.getReg .x6 = BitVec.ofNat 64 (gapOffset idx) := by
        simp only [p3, p2, p1, execInstrBr, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0),
          getReg_setReg_ne' .x6 .x20 (by decide), hx20]
        exact p3c_gapOffset_bv idx (by omega)
      have hp3_x15 : p3.getReg .x15 = BitVec.ofNat 64 (C_TD + levelBase l) := by
        simp only [p3, p2, p1, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x6 .x15 (by decide), hx15]
      rw [reg_exec_BNE p5 _ _ _ .x22]
      simp only [p5, p4, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x10 .x22 (by decide),
        MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), hp3_x15, hp3_x6, ← BitVec.ofNat_add]
      rfl
  obtain ⟨p6, hpre_run, hp6_pc_if, hp6_mem, hp6_reg_other, hp6_x10, hp6_x22⟩ := hpre
  -- Middle section (`p6` -> `sm` at PC 148452) writing unmasked `chainEval c96 l leftD rightD` to `dstAddr`
  have hmid : ∃ sm,
      DetRun oracle (submission.image .commit) p6
        (if levelChain l ≤ 1 then 3 else 10 + 4 * (levelChain l - 2)) sm
        (if levelChain l ≤ 1 then 10 else 24 + 11 * (levelChain l - 2)) (levelChain l) ∧
      sm.pc = BitVec.ofNat 64 (0x1000 + 4 * 148452) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → r ≠ .x23 → sm.getReg r = s0.getReg r) ∧
      sm.getReg .x22 = BitVec.ofNat 64 dstAddr ∧
      readBuffer sm dstAddr 32 = chainEval c96 l leftD rightD ∧
      readBuffer sm (commitChainScratch + 32) 32 = 0 ∧
      readBuffer sm (commitChainScratch + 72) 24 = 0 ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < dstAddr ∨ dstAddr + 32 ≤ q) →
        (q < commitChainScratch ∨ commitChainScratch + 72 ≤ q) →
        sm.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
    by_cases hch1 : levelChain l ≤ 1
    · have hch_eq1 : levelChain l = 1 := levelChain_eq_one_of_le l hl1 hl2 hch1
      have hp6_pc : p6.pc = BitVec.ofNat 64 (0x1000 + 4 * 148435) := by
        simpa only [hch1, ite_true] using hp6_pc_if
      let u1 := execInstrBr p6 (.ADDI .x12 .x22 (0#12))
      let raw := chainEval c96 l leftD rightD
      let u2 := writeBits u1 (BitVec.ofNat 64 dstAddr) raw
      let u3 := execInstrBr u2 (.JAL .x0 (60#21))
      have hu1_pc : u1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148436) := pc_step_idx p6 148435 hp6_pc
      have hu2_pc : u2.pc = BitVec.ofNat 64 (0x1000 + 4 * 148437) := pc_step_idx u1 148436 hu1_pc
      have hu1_mem : u1.mem = s0.mem := (mem_exec_ADDI p6 _ _ _).trans hp6_mem
      have hu1_x12 : u1.getReg .x12 = BitVec.ofNat 64 dstAddr := by
        simp only [u1, execInstrBr, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hp6_x22,
          add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
      have hu1_reg : ∀ r : Reg, r ≠ .x12 → u1.getReg r = p6.getReg r := fun r h12 => by
        simp only [u1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
      have hru1 : DetRun oracle (submission.image .commit) p6 1 u1 1 0 :=
        commit_step1_tail (by omega) (by omega) hp6_pc (by simp only [commitTailInstr])
      have hu1_in : readBuffer u1 srcAddr 96 = binaryInput leftD rightD := by
        rw [readBuffer_of_mem_eq hu1_mem, readBuffer_binary_of_zero_gap s0 srcAddr
          (readBuffer_zero_of_bytes s0 (srcAddr + 64) 32 (fun j hj => by
            simpa only [srcAddr, Nat.add_assoc] using hgap j hj)), hleft, hright]
      have hf36 : fetch (submission.image .commit) u1 = some (.base .ECALL) := by
        have h := commit_fetch_commitTailInstr u1 148436 (by omega) (by omega) hu1_pc
        simp only [commitTailInstr] at h; exact h
      have hru2 : DetRun oracle (submission.image .commit) u1 1 u2 8 1 :=
        DetRun.compress_eq h768 hf36 ((hu1_reg .x5 (by decide)).trans ((hp6_reg_other .x5 (by decide) (by decide) (by decide)).trans hx5))
          ((hu1_reg .x11 (by decide)).trans ((hp6_reg_other .x11 (by decide) (by decide) (by decide)).trans hx11))
          ((hu1_reg .x13 (by decide)).trans ((hp6_reg_other .x13 (by decide) (by decide) (by decide)).trans hx13))
          srcAddr dstAddr ((hu1_reg .x10 (by decide)).trans hp6_x10) hu1_x12
          (by omega) (by omega) (by omega) (by omega) raw (by rw [hu1_in]; simp [raw, chainEval, hch1]; rfl)
      have hru3 : DetRun oracle (submission.image .commit) u2 1 u3 1 0 :=
        commit_step1_tail (by omega) (by omega) hu2_pc (by simp only [commitTailInstr])
      have hu3_mem : u3.mem = u2.mem := mem_exec_JAL u2 .x0 (60#21)
      have hu2_pres : MemPreservedOutside s0 u2 dstAddr (dstAddr + 32) :=
        (MemPreservedOutside.of_mem_eq hu1_mem _ _).trans (memPreserved_writeBits u1 dstAddr raw (by omega))
      refine ⟨u3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have h := (hru1.trans hru2).trans hru3
        simp only [hch_eq1]; exact h
      · simp only [u3, execInstrBr, pc_setPC, hu2_pc]; exact pc_jal_148437
      · intro r h6 h10 h12 h22 _
        rw [reg_exec_JAL0 u2 _ r, writeBits_register, hu1_reg r h12, hp6_reg_other r h6 h10 h22]
      · rw [reg_exec_JAL0 u2 _ .x22, writeBits_register, hu1_reg .x22 (by decide), hp6_x22]
      · rw [readBuffer_of_mem_eq hu3_mem]; exact writeBits_readBuffer_digest u1 dstAddr raw
      · rw [readBuffer_of_mem_eq hu3_mem, hu2_pres.readBuffer_eq (by omega) (by omega)]; exact hscrMid
      · rw [readBuffer_of_mem_eq hu3_mem, hu2_pres.readBuffer_eq (by omega) (by omega)]; exact hscrHi
      · intro q hq houtD _
        rw [getByte_of_mem_eq hu3_mem]; exact hu2_pres q hq houtD
    · -- Chained branch (`2 ≤ levelChain l`, words `148438..148451`)
      have hp6_pc : p6.pc = BitVec.ofNat 64 (0x1000 + 4 * 148438) := by
        simpa only [hch1, ite_false] using hp6_pc_if
      obtain ⟨sm, hrun_ch, hsm_pc, hsm_reg, hsm_x22, hsm_dig, hsm_mid, hsm_hi, hsm_pres⟩ :=
        p3c_node_chain_branch h768 oracle l hl1 hl2 hch1 srcAddr dstAddr
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          leftD rightD s0 p6 hp6_pc hp6_mem hp6_reg_other hp6_x10 hp6_x22
          hx5 hx11 hx13 hx14 hx18 hx28 hx30 hleft hright hgap hscrMid hscrHi
      exact ⟨sm, by simpa only [hch1, ite_false] using hrun_ch, hsm_pc, hsm_reg, hsm_x22,
        hsm_dig, hsm_mid, hsm_hi, hsm_pres⟩
  -- Suffix 148452..148457: mask (LD/AND/SD) + ADDI x14,96 + ADDI x20,1 + BNE x20,x16
  obtain ⟨sm, hmid_run, hsm_pc, hsm_reg, hsm_x22, hsm_dig, hsm_mid, hsm_hi, hsm_pres⟩ := hmid
  let m1 := execInstrBr sm (.LD .x6 .x22 (24#12))
  let m2 := execInstrBr m1 (.AND .x6 .x6 .x27)
  let m3 := execInstrBr m2 (.SD .x22 .x6 (24#12))
  let m4 := execInstrBr m3 (.ADDI .x14 .x14 (96#12))
  let m5 := execInstrBr m4 (.ADDI .x20 .x20 (1#12))
  let m6 := execInstrBr m5 (.BNE .x20 .x16 (8080#13))
  have hm1_pc : m1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148453) := pc_step_idx sm 148452 hsm_pc
  have hm2_pc : m2.pc = BitVec.ofNat 64 (0x1000 + 4 * 148454) := pc_step_idx m1 148453 hm1_pc
  have hm3_pc : m3.pc = BitVec.ofNat 64 (0x1000 + 4 * 148455) := pc_step_idx m2 148454 hm2_pc
  have hm4_pc : m4.pc = BitVec.ofNat 64 (0x1000 + 4 * 148456) := pc_step_idx m3 148455 hm3_pc
  have hm5_pc : m5.pc = BitVec.ofNat 64 (0x1000 + 4 * 148457) := pc_step_idx m4 148456 hm4_pc
  have hm1_addr : sm.getReg .x22 + signExtend12 (24#12) = BitVec.ofNat 64 (dstAddr + 24) := by
    rw [hsm_x22, add_signExtend12_ofNat_small _ 24 (by omega)]
  have hm2_x22 : m2.getReg .x22 = BitVec.ofNat 64 dstAddr := by
    simp only [m2, m1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x6 .x22 (by decide), hsm_x22]
  have hm3_addr : m2.getReg .x22 + signExtend12 (24#12) = BitVec.ofNat 64 (dstAddr + 24) := by
    rw [hm2_x22, add_signExtend12_ofNat_small _ 24 (by omega)]
  have hrm_run : DetRun oracle (submission.image .commit) sm 6 m6 6 0 := by
    have r1 : DetRun oracle (submission.image .commit) sm 1 m1 1 0 :=
      commit_step1_tail (by omega) (by omega) hsm_pc (by simp only [commitTailInstr])
        (ordinaryStep_LD sm .x6 .x22 (24#12) (by rw [hm1_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have r2 : DetRun oracle (submission.image .commit) m1 1 m2 1 0 :=
      commit_step1_tail (by omega) (by omega) hm1_pc (by simp only [commitTailInstr])
    have r3 : DetRun oracle (submission.image .commit) m2 1 m3 1 0 :=
      commit_step1_tail (by omega) (by omega) hm2_pc (by simp only [commitTailInstr])
        (ordinaryStep_SD m2 .x22 .x6 (24#12) (by rw [hm3_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have r4 : DetRun oracle (submission.image .commit) m3 1 m4 1 0 :=
      commit_step1_tail (by omega) (by omega) hm3_pc (by simp only [commitTailInstr])
    have r5 : DetRun oracle (submission.image .commit) m4 1 m5 1 0 :=
      commit_step1_tail (by omega) (by omega) hm4_pc (by simp only [commitTailInstr])
    have r6 : DetRun oracle (submission.image .commit) m5 1 m6 1 0 :=
      commit_step1_tail (by omega) (by omega) hm5_pc (by simp only [commitTailInstr])
    exact ((((r1.trans r2).trans r3).trans r4).trans r5).trans r6
  have hm2_x6 : m2.getReg .x6 = sm.getMem (BitVec.ofNat 64 (dstAddr + 24)) &&& maskTopWord (levelWidth l) := by
    have h1 : m1.getReg .x27 = maskTopWord (levelWidth l) := by
      simp only [m1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x27 (by decide),
        hsm_reg .x27 (by decide) (by decide) (by decide) (by decide) (by decide), hx27]
    simp only [m2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), h1]
    simp only [m1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hm1_addr]
  have hm6_mem : m6.mem = (sm.setMem (BitVec.ofNat 64 (dstAddr + 24))
      (sm.getMem (BitVec.ofNat 64 (dstAddr + 24)) &&& maskTopWord (levelWidth l))).mem := by
    have hm2_mem : m2.mem = sm.mem := (c_mem_exec_AND m1 _ _ _).trans (mem_exec_LD sm _ _ _)
    rw [mem_exec_BNE m5 _ _ _, mem_exec_ADDI m4 _ _ _, mem_exec_ADDI m3 _ _ _]
    simp only [m3, execInstrBr, hm3_addr, hm2_x6, c_mem_setPC, MachineState.setMem, hm2_mem]
  have hm6_pres : MemPreservedOutside sm m6 (dstAddr + 24) (dstAddr + 32) := by
    intro q hq hout
    rw [getByte_of_mem_eq hm6_mem]
    exact setMem_getByte_ofNat sm (dstAddr + 24) q _ (by omega) (by omega) hq hout
  have hm3_reg : ∀ r : Reg, r ≠ .x6 → m3.getReg r = sm.getReg r := fun r h6 => by
    rw [reg_exec_SD m2 _ _ _ r]
    simp only [m2, m1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm h6)]
  have hm5_x14 : m5.getReg .x14 = BitVec.ofNat 64 (C_TD + levelBase (l - 1) + 96 * (idx + 1)) := by
    simp only [m5, m4, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x20 .x14 (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x14 ≠ .x0), hm3_reg .x14 (by decide),
      hsm_reg .x14 (by decide) (by decide) (by decide) (by decide) (by decide), hx14,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hm5_x20 : m5.getReg .x20 = BitVec.ofNat 64 (idx + 1) := by
    simp only [m5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0),
      show m4.getReg .x20 = BitVec.ofNat 64 idx by
        simp only [m4, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x14 .x20 (by decide), hm3_reg .x20 (by decide),
          hsm_reg .x20 (by decide) (by decide) (by decide) (by decide) (by decide), hx20],
      add_signExtend12_ofNat_small _ 1 (by omega)]
  have hm5_x16 : m5.getReg .x16 = BitVec.ofNat 64 (levelSize l) := by
    simp only [m5, m4, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x20 .x16 (by decide), getReg_setReg_ne' .x14 .x16 (by decide),
      hm3_reg .x16 (by decide), hsm_reg .x16 (by decide) (by decide) (by decide) (by decide) (by decide), hx16]
  have hm6_pc : m6.pc = BitVec.ofNat 64 (0x1000 + 4 * (if idx + 1 < levelSize l then 148429 else 148458)) := by
    by_cases hlt : idx + 1 < levelSize l
    · have hne : (m5.getReg .x20 != m5.getReg .x16) = true := by
        rw [hm5_x20, hm5_x16, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hlt, ite_true, m6, execInstrBr, hne, pc_setPC, hm5_pc]; exact pc_bne_148457
    · have heq : (m5.getReg .x20 != m5.getReg .x16) = false := by
        rw [hm5_x20, hm5_x16, show idx + 1 = levelSize l by omega]
        exact bne_self_eq_false _
      simp only [hlt, ite_false, m6, execInstrBr, heq, Bool.false_eq_true, pc_setPC]
      exact pc_step_idx m5 148457 hm5_pc
  have hrun_all : DetRun oracle (submission.image .commit) s0 (p3cNodeSteps l) m6 (p3cNodeCycles l) (levelChain l) := by
    have h := (hpre_run.trans hmid_run).trans hrm_run
    by_cases hch1 : levelChain l ≤ 1
    · simp only [hch1, ite_true, p3cNodeSteps, p3cNodeCycles] at h ⊢
      rw [show 6 + 3 + 6 = 15 by omega, show 6 + 10 + 6 = 22 by omega, Nat.zero_add, Nat.add_zero] at h
      exact h
    · simp only [hch1, ite_false, p3cNodeSteps, p3cNodeCycles] at h ⊢
      rw [show 6 + (10 + 4 * (levelChain l - 2)) + 6 = 22 + 4 * (levelChain l - 2) by omega,
          show 6 + (24 + 11 * (levelChain l - 2)) + 6 = 36 + 11 * (levelChain l - 2) by omega,
          Nat.zero_add, Nat.add_zero] at h
      exact h
  refine ⟨m6, hrun_all, hm6_pc, ?_, (reg_exec_BNE m5 _ _ _ .x14).trans hm5_x14,
    (reg_exec_BNE m5 _ _ _ .x20).trans hm5_x20, ?_, ?_, ?_, ?_⟩
  · intro r h6 h10 h12 h14 h20 h22 h23
    rw [reg_exec_BNE m5 _ _ _ r]
    simp only [m5, m4, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x20 r (Ne.symm h20), getReg_setReg_ne' .x14 r (Ne.symm h14),
      hm3_reg r h6, hsm_reg r h6 h10 h12 h22 h23]
  · rw [readBuffer_of_mem_eq hm6_mem,
      sd_and_maskWidth sm dstAddr (levelWidth l) (levelWidth_ge_192 l) (levelWidth_le_256 l) (by omega) (by omega),
      hsm_dig]
    exact p3c_nodeVal_eq c96 msg salts l idx hl1 hl2 hidx
  · rw [hm6_pres.readBuffer_eq (by omega) (by omega)]; exact hsm_mid
  · rw [hm6_pres.readBuffer_eq (by omega) (by omega)]; exact hsm_hi
  · intro q hq houtD houtS
    exact (hm6_pres q hq (by omega)).trans (hsm_pres q hq houtD houtS)

/-- One full level `l = 9 + k` (`k < 15`) of Phase 3C (words `148415..148459`). -/
private theorem p3c_level (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (k : Nat) (hk : k < 15) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 148415))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 commitChainScratch)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (7 + k)))
    (hx25 : s0.getReg .x25 = BitVec.ofNat 64 (C_DB + 704))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 32, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + 32 * (7 + k) + off)) =
        (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + 32 * (7 + k) + off)))
    (hsrc : ∀ idx < levelSize (8 + k),
      readBuffer s0 (C_TD + levelBase (8 + k) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (8 + k) idx)
    (hsrcOdd : levelSize (8 + k) % 2 = 1 →
      readBuffer s0 (C_TD + levelBase (8 + k) + 96 * (levelSize (8 + k) / 2) + 32) 32 = 0)
    (hsrcGap : ∀ q < (levelSize (8 + k) + 1) / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (8 + k) + 96 * q + 64 + j)) = 0)
    (hdstZero : ∀ idx < levelBytes (9 + k),
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (9 + k) + idx)) = 0)
    (hscrMid : readBuffer s0 (commitChainScratch + 32) 32 = 0)
    (hscrHi : readBuffer s0 (commitChainScratch + 72) 24 = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0
        (p3cLevelSteps (9 + k)) s1 (p3cLevelCycles (9 + k)) (p3cLevelCalls (9 + k)) ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k + 1 < 15 then 148415 else 148460)) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x15 = BitVec.ofNat 64 (C_TD + levelBase (9 + k)) ∧
      s1.getReg .x18 = BitVec.ofNat 64 commitChainScratch ∧
      s1.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (7 + (k + 1))) ∧
      s1.getReg .x25 = BitVec.ofNat 64 (C_DB + 704) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ idx < levelSize (9 + k),
        readBuffer s1 (C_TD + levelBase (9 + k) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (9 + k) idx) ∧
      (levelSize (9 + k) % 2 = 1 →
        readBuffer s1 (C_TD + levelBase (9 + k) + 96 * (levelSize (9 + k) / 2) + 32) 32 = 0) ∧
      (∀ q < (levelSize (9 + k) + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase (9 + k) + 96 * q + 64 + j)) = 0) ∧
      readBuffer s1 (commitChainScratch + 32) 32 = 0 ∧
      readBuffer s1 (commitChainScratch + 72) 24 = 0 ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < C_TD + levelBase (9 + k) ∨ C_TD + levelBase (10 + k) ≤ q) →
        (q < commitChainScratch ∨ commitChainScratch + 72 ≤ q) →
        s1.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476032 := rfl
  have hCS : commitChainScratch = 8589934592 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have htb := treeBytes_eq
  have hsrcB := levelBase_bound (8 + k) (by omega)
  have hdstB := levelBase_bound (9 + k) (by omega)
  have hsrcBytes := levelBytes_eq_gap (8 + k) (by omega) (by omega)
  have hdstBytes := levelBytes_eq_gap (9 + k) (by omega) (by omega)
  have hbase_step : levelBase (9 + k) = levelBase (8 + k) + levelBytes (8 + k) := by
    rw [show 9 + k = (8 + k) + 1 by omega]; rfl
  have hbase_next : levelBase (10 + k) = levelBase (9 + k) + levelBytes (9 + k) := by
    rw [show 10 + k = (9 + k) + 1 by omega]; rfl
  have hlsStep : levelSize (9 + k) = (levelSize (8 + k) + 1) / 2 := by
    rw [show 9 + k = (8 + k) + 1 by omega]; exact levelSize_step (8 + k) (by omega)
  have hlsPos : 0 < levelSize (9 + k) := levelSize_pos (9 + k) (by omega)
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  -- Data reads
  have hd0 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * (7 + k))) = BitVec.ofNat 64 (levelBase (8 + k)) := by
    have h := hdata 0 (by omega) (by omega); simp only [Nat.add_zero] at h
    rw [h, commit_initial_data_dword msg (32 * (7 + k)) (by omega)]
    simpa only [show 7 + k + 1 = 8 + k by omega] using commitData_dword_0 ⟨7 + k, by omega⟩
  have hd1 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * (7 + k) + 8)) = BitVec.ofNat 64 (levelBase (9 + k)) := by
    rw [hdata 8 (by omega) (by omega), Nat.add_assoc, commit_initial_data_dword msg (32 * (7 + k) + 8) (by omega)]
    simpa only [show 7 + k + 2 = 9 + k by omega] using commitData_dword_1 ⟨7 + k, by omega⟩
  have hd2 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * (7 + k) + 16)) = BitVec.ofNat 64 (levelSize (9 + k)) := by
    rw [hdata 16 (by omega) (by omega), Nat.add_assoc, commit_initial_data_dword msg (32 * (7 + k) + 16) (by omega)]
    exact commitData_dword_2_hi ⟨k, hk⟩
  have hd3 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * (7 + k) + 24)) = BitVec.ofNat 64 (commitMeta3C (9 + k)) := by
    rw [hdata 24 (by omega) (by omega), Nat.add_assoc, commit_initial_data_dword msg (32 * (7 + k) + 24) (by omega)]
    exact commitData_dword_3_hi ⟨k, hk⟩
  -- Header part 1 (words 148415..148420, 6 steps), opaque via `obtain`
  have hhdr1 : ∃ h6,
      DetRun oracle (submission.image .commit) s0 6 h6 6 0 ∧
      h6.pc = BitVec.ofNat 64 (0x1000 + 4 * 148421) ∧
      h6.mem = s0.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x21 → h6.getReg r = s0.getReg r) ∧
      h6.getReg .x14 = BitVec.ofNat 64 (C_TD + levelBase (8 + k)) ∧
      h6.getReg .x15 = BitVec.ofNat 64 (C_TD + levelBase (9 + k)) ∧
      h6.getReg .x16 = BitVec.ofNat 64 (levelSize (9 + k)) ∧
      h6.getReg .x21 = BitVec.ofNat 64 (commitMeta3C (9 + k)) := by
    let h1 := execInstrBr s0 (.LD .x6 .x24 (0#12))
    let h2 := execInstrBr h1 (.ADD .x14 .x9 .x6)
    let h3 := execInstrBr h2 (.LD .x6 .x24 (8#12))
    let h4 := execInstrBr h3 (.ADD .x15 .x9 .x6)
    let h5 := execInstrBr h4 (.LD .x16 .x24 (16#12))
    let h6 := execInstrBr h5 (.LD .x21 .x24 (24#12))
    have hh1_pc : h1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148416) := pc_step_idx s0 148415 hpc
    have hh2_pc : h2.pc = BitVec.ofNat 64 (0x1000 + 4 * 148417) := pc_step_idx h1 148416 hh1_pc
    have hh3_pc : h3.pc = BitVec.ofNat 64 (0x1000 + 4 * 148418) := pc_step_idx h2 148417 hh2_pc
    have hh4_pc : h4.pc = BitVec.ofNat 64 (0x1000 + 4 * 148419) := pc_step_idx h3 148418 hh3_pc
    have hh5_pc : h5.pc = BitVec.ofNat 64 (0x1000 + 4 * 148420) := pc_step_idx h4 148419 hh4_pc
    have hh6_pc : h6.pc = BitVec.ofNat 64 (0x1000 + 4 * 148421) := pc_step_idx h5 148420 hh5_pc
    have hh2_mem : h2.mem = s0.mem := (mem_exec_ADD h1 _ _ _).trans (mem_exec_LD s0 _ _ _)
    have hh4_mem : h4.mem = s0.mem := ((mem_exec_ADD h3 _ _ _).trans (mem_exec_LD h2 _ _ _)).trans hh2_mem
    have hh5_mem : h5.mem = s0.mem := (mem_exec_LD h4 _ _ _).trans hh4_mem
    have hh6_mem : h6.mem = s0.mem := (mem_exec_LD h5 _ _ _).trans hh5_mem
    have hh0_addr : s0.getReg .x24 + signExtend12 (0#12) = BitVec.ofNat 64 (C_DB + 32 * (7 + k)) := by
      rw [hx24, add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
    have hh2_x24 : h2.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (7 + k)) := by
      simp only [h2, h1, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x14 .x24 (by decide), getReg_setReg_ne' .x6 .x24 (by decide), hx24]
    have hh2_addr : h2.getReg .x24 + signExtend12 (8#12) = BitVec.ofNat 64 (C_DB + 32 * (7 + k) + 8) := by
      rw [hh2_x24, add_signExtend12_ofNat_small _ 8 (by omega)]
    have hh4_x24 : h4.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (7 + k)) := by
      simp only [h4, h3, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x15 .x24 (by decide), getReg_setReg_ne' .x6 .x24 (by decide), hh2_x24]
    have hh4_addr : h4.getReg .x24 + signExtend12 (16#12) = BitVec.ofNat 64 (C_DB + 32 * (7 + k) + 16) := by
      rw [hh4_x24, add_signExtend12_ofNat_small _ 16 (by omega)]
    have hh5_x24 : h5.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (7 + k)) := by
      simp only [h5, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x16 .x24 (by decide), hh4_x24]
    have hh5_addr : h5.getReg .x24 + signExtend12 (24#12) = BitVec.ofNat 64 (C_DB + 32 * (7 + k) + 24) := by
      rw [hh5_x24, add_signExtend12_ofNat_small _ 24 (by omega)]
    have hr16 : DetRun oracle (submission.image .commit) s0 6 h6 6 0 := by
      have r1 : DetRun oracle (submission.image .commit) s0 1 h1 1 0 :=
        commit_step1_tail (by omega) (by omega) hpc (by simp only [commitTailInstr])
          (ordinaryStep_LD s0 .x6 .x24 (0#12) (by rw [hh0_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
      have r2 : DetRun oracle (submission.image .commit) h1 1 h2 1 0 :=
        commit_step1_tail (by omega) (by omega) hh1_pc (by simp only [commitTailInstr])
      have r3 : DetRun oracle (submission.image .commit) h2 1 h3 1 0 :=
        commit_step1_tail (by omega) (by omega) hh2_pc (by simp only [commitTailInstr])
          (ordinaryStep_LD h2 .x6 .x24 (8#12) (by rw [hh2_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
      have r4 : DetRun oracle (submission.image .commit) h3 1 h4 1 0 :=
        commit_step1_tail (by omega) (by omega) hh3_pc (by simp only [commitTailInstr])
      have r5 : DetRun oracle (submission.image .commit) h4 1 h5 1 0 :=
        commit_step1_tail (by omega) (by omega) hh4_pc (by simp only [commitTailInstr])
          (ordinaryStep_LD h4 .x16 .x24 (16#12) (by rw [hh4_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
      have r6 : DetRun oracle (submission.image .commit) h5 1 h6 1 0 :=
        commit_step1_tail (by omega) (by omega) hh5_pc (by simp only [commitTailInstr])
          (ordinaryStep_LD h5 .x21 .x24 (24#12) (by rw [hh5_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
      exact ((((r1.trans r2).trans r3).trans r4).trans r5).trans r6
    refine ⟨h6, hr16, hh6_pc, hh6_mem,
      fun r h6r h14r h15r h16r h21r => by
        simp only [h6, h5, h4, h3, h2, h1, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x21 r (Ne.symm h21r), getReg_setReg_ne' .x16 r (Ne.symm h16r),
          getReg_setReg_ne' .x15 r (Ne.symm h15r), getReg_setReg_ne' .x14 r (Ne.symm h14r),
          getReg_setReg_ne' .x6 r (Ne.symm h6r)],
      ?_, ?_, ?_, ?_⟩
    · simp only [h6, h5, h4, h3, h2, h1, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x21 .x14 (by decide), getReg_setReg_ne' .x16 .x14 (by decide),
        getReg_setReg_ne' .x15 .x14 (by decide), getReg_setReg_ne' .x6 .x14 (by decide),
        MachineState.getReg_setReg_eq (by decide : Reg.x14 ≠ .x0),
        getReg_setReg_ne' .x6 .x9 (by decide), MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0),
        hx9, hh0_addr, hd0, ← BitVec.ofNat_add]
    · have h2mem : ∀ a, h2.getMem a = s0.getMem a := fun a => by simp only [MachineState.getMem, hh2_mem]
      have h29 : h2.getReg .x9 = BitVec.ofNat 64 C_TD := by
        simp only [h2, h1, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x14 .x9 (by decide), getReg_setReg_ne' .x6 .x9 (by decide), hx9]
      simp only [h6, h5, h4, h3, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x21 .x15 (by decide), getReg_setReg_ne' .x16 .x15 (by decide),
        MachineState.getReg_setReg_eq (by decide : Reg.x15 ≠ .x0),
        getReg_setReg_ne' .x6 .x9 (by decide), MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0),
        h29, hh2_addr, h2mem, hd1, ← BitVec.ofNat_add]
    · have h4mem : ∀ a, h4.getMem a = s0.getMem a := fun a => by simp only [MachineState.getMem, hh4_mem]
      simp only [h6, h5, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x21 .x16 (by decide),
        MachineState.getReg_setReg_eq (by decide : Reg.x16 ≠ .x0), hh4_addr, h4mem, hd2]
    · have h5mem : ∀ a, h5.getMem a = s0.getMem a := fun a => by simp only [MachineState.getMem, hh5_mem]
      simp only [h6, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x21 ≠ .x0), hh5_addr, h5mem, hd3]
  obtain ⟨h6, hr16, hh6_pc, hh6_mem, hh6_reg_other, hh6_x14, hh6_x15, hh6_x16, hh6_x21⟩ := hhdr1
  -- Header part 2 (words 148421..148428, 8 steps), opaque via `obtain`
  have hhdr2 : ∃ h14,
      DetRun oracle (submission.image .commit) h6 8 h14 8 0 ∧
      h14.pc = BitVec.ofNat 64 (0x1000 + 4 * 148429) ∧
      h14.mem = s0.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x19 → r ≠ .x20 → r ≠ .x27 → r ≠ .x28 → r ≠ .x30 → h14.getReg r = h6.getReg r) ∧
      h14.getReg .x19 = BitVec.ofNat 64 (levelChain (9 + k) - 1) ∧
      h14.getReg .x20 = BitVec.ofNat 64 0 ∧
      h14.getReg .x27 = maskTopWord (levelWidth (9 + k)) ∧
      h14.getReg .x28 = BitVec.ofNat 64 (levelTagStart (9 + k)) ∧
      h14.getReg .x30 = BitVec.ofNat 64 (levelTagStart (9 + k) + (levelChain (9 + k) - 1)) := by
    let h7 := execInstrBr h6 (.ANDI .x19 .x21 (255#12))
    let h8 := execInstrBr h7 (.SRLI .x6 .x21 (8#6))
    let h9 := execInstrBr h8 (.ANDI .x6 .x6 (255#12))
    let h10 := execInstrBr h9 (.ADDI .x27 .x0 (4095#12))
    let h11 := execInstrBr h10 (.SRL .x27 .x27 .x6)
    let h12 := execInstrBr h11 (.SRLI .x28 .x21 (32#6))
    let h13 := execInstrBr h12 (.ADD .x30 .x28 .x19)
    let h14 := execInstrBr h13 (.ADDI .x20 .x0 (0#12))
    have hh7_pc : h7.pc = BitVec.ofNat 64 (0x1000 + 4 * 148422) := pc_step_idx h6 148421 hh6_pc
    have hh8_pc : h8.pc = BitVec.ofNat 64 (0x1000 + 4 * 148423) := pc_step_idx h7 148422 hh7_pc
    have hh9_pc : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * 148424) := pc_step_idx h8 148423 hh8_pc
    have hh10_pc : h10.pc = BitVec.ofNat 64 (0x1000 + 4 * 148425) := pc_step_idx h9 148424 hh9_pc
    have hh11_pc : h11.pc = BitVec.ofNat 64 (0x1000 + 4 * 148426) := pc_step_idx h10 148425 hh10_pc
    have hh12_pc : h12.pc = BitVec.ofNat 64 (0x1000 + 4 * 148427) := pc_step_idx h11 148426 hh11_pc
    have hh13_pc : h13.pc = BitVec.ofNat 64 (0x1000 + 4 * 148428) := pc_step_idx h12 148427 hh12_pc
    have hh14_pc : h14.pc = BitVec.ofNat 64 (0x1000 + 4 * 148429) := pc_step_idx h13 148428 hh13_pc
    have hh14_mem : h14.mem = s0.mem :=
      ((((((((mem_exec_ADDI h13 _ _ _).trans (mem_exec_ADD h12 _ _ _)).trans
        (mem_exec_SRLI h11 _ _ _)).trans (mem_exec_SRL h10 _ _ _)).trans
        (mem_exec_ADDI h9 _ _ _)).trans (mem_exec_ANDI h8 _ _ _)).trans
        (mem_exec_SRLI h7 _ _ _)).trans (mem_exec_ANDI h6 _ _ _)).trans hh6_mem
    have hr714 : DetRun oracle (submission.image .commit) h6 8 h14 8 0 := by
      have r7 : DetRun oracle (submission.image .commit) h6 1 h7 1 0 :=
        commit_step1_tail (by omega) (by omega) hh6_pc (by simp only [commitTailInstr])
      have r8 : DetRun oracle (submission.image .commit) h7 1 h8 1 0 :=
        commit_step1_tail (by omega) (by omega) hh7_pc (by simp only [commitTailInstr])
      have r9 : DetRun oracle (submission.image .commit) h8 1 h9 1 0 :=
        commit_step1_tail (by omega) (by omega) hh8_pc (by simp only [commitTailInstr])
      have r10 : DetRun oracle (submission.image .commit) h9 1 h10 1 0 :=
        commit_step1_tail (by omega) (by omega) hh9_pc (by simp only [commitTailInstr])
      have r11 : DetRun oracle (submission.image .commit) h10 1 h11 1 0 :=
        commit_step1_tail (by omega) (by omega) hh10_pc (by simp only [commitTailInstr])
      have r12 : DetRun oracle (submission.image .commit) h11 1 h12 1 0 :=
        commit_step1_tail (by omega) (by omega) hh11_pc (by simp only [commitTailInstr])
      have r13 : DetRun oracle (submission.image .commit) h12 1 h13 1 0 :=
        commit_step1_tail (by omega) (by omega) hh12_pc (by simp only [commitTailInstr])
      have r14 : DetRun oracle (submission.image .commit) h13 1 h14 1 0 :=
        commit_step1_tail (by omega) (by omega) hh13_pc (by simp only [commitTailInstr])
      exact ((((((r7.trans r8).trans r9).trans r10).trans r11).trans r12).trans r13).trans r14
    have hh7_x19 : h7.getReg .x19 = BitVec.ofNat 64 (levelChain (9 + k) - 1) := by
      simp only [h7, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x19 ≠ .x0), hh6_x21]
      exact p3c_meta_x19 k hk
    have hh12_x28 : h12.getReg .x28 = BitVec.ofNat 64 (levelTagStart (9 + k)) := by
      have h11_21 : h11.getReg .x21 = BitVec.ofNat 64 (commitMeta3C (9 + k)) := by
        simp only [h11, h10, h9, h8, h7, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x27 .x21 (by decide), getReg_setReg_ne' .x6 .x21 (by decide),
          getReg_setReg_ne' .x19 .x21 (by decide), hh6_x21]
      simp only [h12, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ .x0), h11_21]
      exact p3c_meta_x28 k hk
    refine ⟨h14, hr714, hh14_pc, hh14_mem,
      fun r h6r h19r h20r h27r h28r h30r => by
        simp only [h14, h13, h12, h11, h10, h9, h8, h7, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x20 r (Ne.symm h20r), getReg_setReg_ne' .x30 r (Ne.symm h30r),
          getReg_setReg_ne' .x28 r (Ne.symm h28r), getReg_setReg_ne' .x27 r (Ne.symm h27r),
          getReg_setReg_ne' .x6 r (Ne.symm h6r), getReg_setReg_ne' .x19 r (Ne.symm h19r)],
      by simp only [h14, h13, h12, h11, h10, h9, h8, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x20 .x19 (by decide), getReg_setReg_ne' .x30 .x19 (by decide),
          getReg_setReg_ne' .x28 .x19 (by decide), getReg_setReg_ne' .x27 .x19 (by decide),
          getReg_setReg_ne' .x6 .x19 (by decide), hh7_x19],
      by simp only [h14, execInstrBr, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0), c_getReg_x0]; decide,
      ?_,
      by simp only [h14, h13, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x20 .x28 (by decide), getReg_setReg_ne' .x30 .x28 (by decide), hh12_x28],
      ?_⟩
    · have h96 : h9.getReg .x6 = ((BitVec.ofNat 64 (commitMeta3C (9 + k))) >>> 8) &&& signExtend12 (255#12) := by
        simp only [h9, h8, h7, execInstrBr, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0),
          getReg_setReg_ne' .x19 .x21 (by decide), hh6_x21]
        rfl
      have h11_27 : h11.getReg .x27 = maskTopWord (levelWidth (9 + k)) := by
        simp only [h11, h10, execInstrBr, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide : Reg.x27 ≠ .x0),
          getReg_setReg_ne' .x27 .x6 (by decide), c_getReg_x0, h96, BitVec.zero_add]
        exact p3c_meta_x27 k hk
      simp only [h14, h13, h12, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x20 .x27 (by decide), getReg_setReg_ne' .x30 .x27 (by decide),
        getReg_setReg_ne' .x28 .x27 (by decide), h11_27]
    · have h12_19 : h12.getReg .x19 = BitVec.ofNat 64 (levelChain (9 + k) - 1) := by
        simp only [h12, h11, h10, h9, h8, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x28 .x19 (by decide), getReg_setReg_ne' .x27 .x19 (by decide),
          getReg_setReg_ne' .x6 .x19 (by decide), hh7_x19]
      simp only [h14, h13, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x20 .x30 (by decide),
        MachineState.getReg_setReg_eq (by decide : Reg.x30 ≠ .x0), hh12_x28, h12_19]
      exact p3c_meta_x30 k hk
  obtain ⟨h14, hr714, hh14_pc, hh14_mem, hh14_reg_h6, hh14_x19, hh14_x20, hh14_x27, hh14_x28, hh14_x30⟩ := hhdr2
  have hhdr_run : DetRun oracle (submission.image .commit) s0 14 h14 14 0 := hr16.trans hr714
  have hh14_x14 : h14.getReg .x14 = BitVec.ofNat 64 (C_TD + levelBase (8 + k)) :=
    (hh14_reg_h6 .x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh6_x14
  have hh14_x15 : h14.getReg .x15 = BitVec.ofNat 64 (C_TD + levelBase (9 + k)) :=
    (hh14_reg_h6 .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh6_x15
  have hh14_x16 : h14.getReg .x16 = BitVec.ofNat 64 (levelSize (9 + k)) :=
    (hh14_reg_h6 .x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh6_x16
  -- Induction over `n ≤ levelSize (9 + k)` nodes
  have hnodes : ∀ n ≤ levelSize (9 + k),
      ∃ sn,
        DetRun oracle (submission.image .commit) h14
          (n * p3cNodeSteps (9 + k)) sn (n * p3cNodeCycles (9 + k)) (n * levelChain (9 + k)) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < levelSize (9 + k) then 148429 else 148458)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x14 → r ≠ .x20 → r ≠ .x22 → r ≠ .x23 →
          sn.getReg r = h14.getReg r) ∧
        sn.getReg .x14 = BitVec.ofNat 64 (C_TD + levelBase (8 + k) + 96 * n) ∧
        sn.getReg .x20 = BitVec.ofNat 64 n ∧
        (∀ idx < n, readBuffer sn (C_TD + levelBase (9 + k) + gapOffset idx) 32 = nodeVal c96 msg salts (9 + k) idx) ∧
        (∀ q < (levelSize (9 + k) + 1) / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase (9 + k) + 96 * q + 64 + j)) = 0) ∧
        readBuffer sn (commitChainScratch + 32) 32 = 0 ∧
        readBuffer sn (commitChainScratch + 72) 24 = 0 ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (q < C_TD + levelBase (9 + k) ∨ C_TD + levelBase (9 + k) + gapOffset n ≤ q) →
          (q < commitChainScratch ∨ commitChainScratch + 72 ≤ q) →
          sn.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
    intro n hn; induction n with
    | zero =>
      refine ⟨h14, by simpa only [Nat.zero_mul] using DetRun.refl oracle (submission.image .commit) h14,
        by simpa only [hlsPos, ite_true] using hh14_pc,
        fun _ _ _ _ _ _ _ _ => rfl,
        by simpa only [Nat.mul_zero, Nat.add_zero] using hh14_x14, hh14_x20,
        fun idx hidx => by omega,
        fun q hq j hj => by
          rw [getByte_of_mem_eq hh14_mem]
          have hadd : C_TD + levelBase (9 + k) + 96 * q + 64 + j = C_TD + levelBase (9 + k) + (96 * q + 64 + j) := by omega
          rw [hadd]; exact hdstZero (96 * q + 64 + j) (by rw [hdstBytes]; omega),
        by rw [readBuffer_of_mem_eq hh14_mem]; exact hscrMid,
        by rw [readBuffer_of_mem_eq hh14_mem]; exact hscrHi,
        fun q _ _ _ => getByte_of_mem_eq hh14_mem _⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hregn, hx14n, hx20n, hdign, hgapn, hmidn, hhin, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 148429) := by
        simpa only [show n < levelSize (9 + k) by omega, ite_true] using hpcn
      have hprev_eq : 9 + k - 1 = 8 + k := by omega
      have hsrcL : readBuffer sn (C_TD + levelBase (9 + k - 1) + 96 * n) 32 =
          nodeVal c96 msg salts (9 + k - 1) (2 * n) := by
        rw [hprev_eq]
        have h1 : readBuffer sn (C_TD + levelBase (8 + k) + 96 * n) 32 =
            readBuffer s0 (C_TD + levelBase (8 + k) + 96 * n) 32 :=
          readBuffer_congr _ _ _ _ (fun j hj => hpresn _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
        rw [h1, ← gapOffset_even n]
        exact hsrc (2 * n) (by omega)
      have hsrcR : readBuffer sn (C_TD + levelBase (9 + k - 1) + 96 * n + 32) 32 =
          if 2 * n + 1 < levelSize (9 + k - 1) then nodeVal c96 msg salts (9 + k - 1) (2 * n + 1) else 0 := by
        rw [hprev_eq]
        have h1 : readBuffer sn (C_TD + levelBase (8 + k) + 96 * n + 32) 32 =
            readBuffer s0 (C_TD + levelBase (8 + k) + 96 * n + 32) 32 :=
          readBuffer_congr _ _ _ _ (fun j hj => hpresn _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
        rw [h1]
        by_cases hodd : 2 * n + 1 < levelSize (8 + k)
        · simp only [hodd, ite_true]
          have hgo : gapOffset (2 * n + 1) = 96 * n + 32 := gapOffset_odd n
          rw [Nat.add_assoc, ← hgo]
          exact hsrc (2 * n + 1) hodd
        · simp only [hodd, ite_false]
          have hmod : levelSize (8 + k) % 2 = 1 := by omega
          have hdiv : levelSize (8 + k) / 2 = n := by omega
          rw [← hdiv]; exact hsrcOdd hmod
      have hsrcG : ∀ j < 32, sn.getByte (BitVec.ofNat 64 (C_TD + levelBase (9 + k - 1) + 96 * n + 64 + j)) = 0 := by
        intro j hj; rw [hprev_eq]
        rw [hpresn _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
        exact hsrcGap n (by omega) j hj
      obtain ⟨sm, hstep_run, hpcm, hregm, hx14m, hx20m, hdigm, hmidm, hhim, hpresm⟩ :=
        p3c_node_step h768 oracle msg salts (9 + k) n (by omega) (by omega) (by omega) sn hpc_in
          ((hregn .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hh14_reg_h6 .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              ((hh6_reg_other .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5)))
          ((hregn .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hh14_reg_h6 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              ((hh6_reg_other .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11)))
          ((hregn .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hh14_reg_h6 .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              ((hh6_reg_other .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13)))
          (by rw [hprev_eq]; exact hx14n)
          ((hregn .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh14_x15)
          ((hregn .x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh14_x16)
          ((hregn .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
            ((hh14_reg_h6 .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              ((hh6_reg_other .x18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx18)))
          ((hregn .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh14_x19)
          hx20n
          ((hregn .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh14_x27)
          ((hregn .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh14_x28)
          ((hregn .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh14_x30)
          hsrcL hsrcR hsrcG hmidn hhin
      have hrun_tot : DetRun oracle (submission.image .commit) h14
          ((n + 1) * p3cNodeSteps (9 + k)) sm ((n + 1) * p3cNodeCycles (9 + k)) ((n + 1) * levelChain (9 + k)) := by
        have h := hrunn.trans hstep_run
        rw [Nat.succ_mul, Nat.succ_mul, Nat.succ_mul]; exact h
      refine ⟨sm, hrun_tot, hpcm,
        fun r h6 h10 h12 h14r h20 h22 h23 =>
          (hregm r h6 h10 h12 h14r h20 h22 h23).trans (hregn r h6 h10 h12 h14r h20 h22 h23),
        by rw [hprev_eq] at hx14m; exact hx14m, hx20m, ?_, ?_, hmidm, hhim, ?_⟩
      · intro idx hidx
        by_cases hlt : idx < n
        · have hgo_lt : gapOffset idx + 32 ≤ gapOffset n := by unfold gapOffset; omega
          have hgo_n := gapOffset_lt_levelBytes (9 + k) n (by omega) (by omega) (by omega)
          have hrb : readBuffer sm (C_TD + levelBase (9 + k) + gapOffset idx) 32 =
              readBuffer sn (C_TD + levelBase (9 + k) + gapOffset idx) 32 :=
            readBuffer_congr _ _ _ _ (fun j hj => hpresm _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
          rw [hrb]; exact hdign idx hlt
        · have heq : idx = n := by omega
          subst heq; exact hdigm
      · intro q hq j hj
        have hsep : C_TD + levelBase (9 + k) + 96 * q + 64 + j < C_TD + levelBase (9 + k) + gapOffset n ∨
            C_TD + levelBase (9 + k) + gapOffset n + 32 ≤ C_TD + levelBase (9 + k) + 96 * q + 64 + j := by
          unfold gapOffset; omega
        rw [hpresm _ (by rw [hdstBytes] at hdstB; omega) hsep (Or.inl (by rw [hdstBytes] at hdstB; omega))]
        exact hgapn q hq j hj
      · intro q hq houtD houtS
        have hgo_le : gapOffset n + 32 ≤ gapOffset (n + 1) := by unfold gapOffset; omega
        have hgo_le0 : gapOffset n ≤ gapOffset (n + 1) := by omega
        exact (hpresm q hq (by omega) houtS).trans (hpresn q hq (by omega) houtS)
  obtain ⟨sn, hnodes_run, hsn_pc, hsn_reg, _, _, hsn_dig, hsn_gap, hsn_mid, hsn_hi, hsn_pres⟩ :=
    hnodes (levelSize (9 + k)) (le_refl _)
  have hsn_pc' : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 148458) := by
    simpa only [Nat.lt_irrefl, ite_false] using hsn_pc
  -- Level tail 148458..148459: ADDI x24, x24, 32; BNE x24, x25, 8016#13
  let e1 := execInstrBr sn (.ADDI .x24 .x24 (32#12))
  let e2 := execInstrBr e1 (.BNE .x24 .x25 (8016#13))
  have he1_pc : e1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148459) := pc_step_idx sn 148458 hsn_pc'
  have htail_run : DetRun oracle (submission.image .commit) sn 2 e2 2 0 :=
    (commit_step1_tail (by omega) (by omega) hsn_pc' (by simp only [commitTailInstr])).trans
      (commit_step1_tail (by omega) (by omega) he1_pc (by simp only [commitTailInstr]))
  have he2_mem : e2.mem = sn.mem := (mem_exec_BNE e1 _ _ _).trans (mem_exec_ADDI sn _ _ _)
  have hsn_x24 : sn.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (7 + k)) :=
    (hsn_reg .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hh14_reg_h6 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh6_reg_other .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24))
  have hsn_x25 : sn.getReg .x25 = BitVec.ofNat 64 (C_DB + 704) :=
    (hsn_reg .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hh14_reg_h6 .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh6_reg_other .x25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25))
  have he1_x24 : e1.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (7 + (k + 1))) := by
    simp only [e1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x24 ≠ .x0), hsn_x24,
      add_signExtend12_ofNat_small _ 32 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have he1_x25 : e1.getReg .x25 = BitVec.ofNat 64 (C_DB + 704) := by
    simp only [e1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x24 .x25 (by decide), hsn_x25]
  have he2_pc : e2.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k + 1 < 15 then 148415 else 148460)) := by
    by_cases hlt : k + 1 < 15
    · have hne : (e1.getReg .x24 != e1.getReg .x25) = true := by
        rw [he1_x24, he1_x25, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hlt, ite_true, e2, execInstrBr, hne, pc_setPC, he1_pc]; exact pc_bne_148459
    · have heq : (e1.getReg .x24 != e1.getReg .x25) = false := by
        rw [he1_x24, he1_x25, show 32 * (7 + (k + 1)) = 704 by omega]
        exact bne_self_eq_false _
      simp only [hlt, ite_false, e2, execInstrBr, heq, Bool.false_eq_true, pc_setPC]
      exact pc_step_idx e1 148459 he1_pc
  have he2_reg_sn : ∀ r : Reg, r ≠ .x24 → e2.getReg r = sn.getReg r := fun r h24 => by
    rw [reg_exec_BNE e1 _ _ _ r]
    simp only [e1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x24 r (Ne.symm h24)]
  have hrun_tot : DetRun oracle (submission.image .commit) s0
      (p3cLevelSteps (9 + k)) e2 (p3cLevelCycles (9 + k)) (p3cLevelCalls (9 + k)) := by
    have h := (hhdr_run.trans hnodes_run).trans htail_run
    unfold p3cLevelSteps p3cLevelCycles p3cLevelCalls
    rw [show 14 + levelSize (9 + k) * p3cNodeSteps (9 + k) + 2 = 16 + levelSize (9 + k) * p3cNodeSteps (9 + k) by omega,
        show 14 + levelSize (9 + k) * p3cNodeCycles (9 + k) + 2 = 16 + levelSize (9 + k) * p3cNodeCycles (9 + k) by omega,
        Nat.zero_add, Nat.add_zero] at h
    exact h
  have hgo_end_le : gapOffset (levelSize (9 + k)) ≤ levelBytes (9 + k) := by
    unfold gapOffset; rw [hdstBytes]; omega
  refine ⟨e2, hrun_tot, he2_pc,
    (he2_reg_sn .x2 (by decide)).trans ((hsn_reg .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hh14_reg_h6 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh6_reg_other .x2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx2))),
    (he2_reg_sn .x5 (by decide)).trans ((hsn_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hh14_reg_h6 .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh6_reg_other .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5))),
    (he2_reg_sn .x9 (by decide)).trans ((hsn_reg .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hh14_reg_h6 .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh6_reg_other .x9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx9))),
    (he2_reg_sn .x11 (by decide)).trans ((hsn_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hh14_reg_h6 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh6_reg_other .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11))),
    (he2_reg_sn .x13 (by decide)).trans ((hsn_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hh14_reg_h6 .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh6_reg_other .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13))),
    (he2_reg_sn .x15 (by decide)).trans ((hsn_reg .x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh14_x15),
    (he2_reg_sn .x18 (by decide)).trans ((hsn_reg .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hh14_reg_h6 .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh6_reg_other .x18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx18))),
    (reg_exec_BNE e1 _ _ _ .x24).trans he1_x24,
    (he2_reg_sn .x25 (by decide)).trans hsn_x25,
    (he2_reg_sn .x26 (by decide)).trans ((hsn_reg .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hh14_reg_h6 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh6_reg_other .x26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26))),
    fun idx hidx => (readBuffer_of_mem_eq he2_mem _ _).trans (hsn_dig idx hidx),
    fun hmod => by
      rw [readBuffer_of_mem_eq he2_mem]
      apply readBuffer_zero_of_bytes; intro j hj
      have hgo_eq : gapOffset (levelSize (9 + k)) = 96 * (levelSize (9 + k) / 2) + 32 := by
        unfold gapOffset; omega
      have haddr : C_TD + levelBase (9 + k) + 96 * (levelSize (9 + k) / 2) + 32 + j =
          C_TD + levelBase (9 + k) + (96 * (levelSize (9 + k) / 2) + 32 + j) := by omega
      rw [hsn_pres _ (by rw [hdstBytes] at hdstB; omega) (Or.inr (by omega)) (Or.inl (by rw [hdstBytes] at hdstB; omega)),
        haddr]
      exact hdstZero _ (by rw [hdstBytes]; omega),
    fun q hq j hj => (getByte_of_mem_eq he2_mem _).trans (hsn_gap q hq j hj),
    (readBuffer_of_mem_eq he2_mem _ _).trans hsn_mid,
    (readBuffer_of_mem_eq he2_mem _ _).trans hsn_hi,
    fun q hq houtD houtS => (getByte_of_mem_eq he2_mem _).trans (hsn_pres q hq (by omega) houtS)⟩

/-- Phase 3C (`L9..L23`, words `148412..148459`): `1,424,710` steps, `2,847,859` cycles, `203,307` calls. -/
private theorem commit_phase3C (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 148412))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 224))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 704, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl8 : ∀ idx < levelSize 8, readBuffer s0 (C_TD + levelBase 8 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 8 idx)
    (hodd8 : ∀ j < 32, s0.getByte (BitVec.ofNat 64 (C_TD + levelBase 8 + 96 * 21845 + 32 + j)) = 0)
    (hgap8 : ∀ q < (levelSize 8 + 1) / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase 8 + 96 * q + 64 + j)) = 0)
    (hzero9 : ∀ addr, C_TD + levelBase 9 ≤ addr → addr < C_TD + levelBase 24 →
      s0.getByte (BitVec.ofNat 64 addr) = 0)
    (hscrMid : readBuffer s0 (commitChainScratch + 32) 32 = 0)
    (hscrHi : readBuffer s0 (commitChainScratch + 72) 24 = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 1424710 s1 2847859 203307 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148460) ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x15 = BitVec.ofNat 64 (C_TD + levelBase 23) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l, 9 ≤ l → l ≤ 23 → ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l, 9 ≤ l → l ≤ 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < C_TD + levelBase 9 ∨ C_TD + levelBase 24 ≤ q) →
        (q < commitChainScratch ∨ commitChainScratch + 72 ≤ q) →
        s1.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476032 := rfl
  have hCS : commitChainScratch = 8589934592 := rfl
  have htb := treeBytes_eq
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  -- Setup words 148412..148414
  let sa0 := execInstrBr s0 (.ADDI .x25 .x2 (704#12))
  let sa1 := execInstrBr sa0 (.ADDI .x18 .x0 (1#12))
  let sa := execInstrBr sa1 (.SLLI .x18 .x18 (33#6))
  have hsa0_pc : sa0.pc = BitVec.ofNat 64 (0x1000 + 4 * 148413) := pc_step_idx s0 148412 hpc
  have hsa1_pc : sa1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148414) := pc_step_idx sa0 148413 hsa0_pc
  have hsa_pc : sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 148415) := pc_step_idx sa1 148414 hsa1_pc
  have hsetup : DetRun oracle (submission.image .commit) s0 3 sa 3 0 :=
    ((commit_step1_tail (by omega) (by omega) hpc (by simp only [commitTailInstr])).trans
      (commit_step1_tail (by omega) (by omega) hsa0_pc (by simp only [commitTailInstr]))).trans
      (commit_step1_tail (by omega) (by omega) hsa1_pc (by simp only [commitTailInstr]))
  have hsa_mem : sa.mem = s0.mem :=
    ((mem_exec_SLLI sa1 _ _ _).trans (mem_exec_ADDI sa0 _ _ _)).trans (mem_exec_ADDI s0 _ _ _)
  have hsa_reg_other : ∀ r : Reg, r ≠ .x18 → r ≠ .x25 → sa.getReg r = s0.getReg r := fun r h18 h25 => by
    simp only [sa, sa1, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x18 r (Ne.symm h18), getReg_setReg_ne' .x25 r (Ne.symm h25)]
  have hsa_x25 : sa.getReg .x25 = BitVec.ofNat 64 (C_DB + 704) := by
    simp only [sa, sa1, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x18 .x25 (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0), hx2]; decide
  have hsa_x18 : sa.getReg .x18 = BitVec.ofNat 64 commitChainScratch := by
    simp only [sa, sa1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x18 ≠ .x0), c_getReg_x0]; decide
  have hind : ∀ n ≤ 15,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa
          (∑ k ∈ Finset.range n, p3cLevelSteps (9 + k)) sn
          (∑ k ∈ Finset.range n, p3cLevelCycles (9 + k))
          (∑ k ∈ Finset.range n, p3cLevelCalls (9 + k)) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 15 then 148415 else 148460)) ∧
        sn.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sn.getReg .x5 = 0#64 ∧
        sn.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sn.getReg .x11 = 96#64 ∧
        sn.getReg .x13 = 0#64 ∧
        (n ≠ 0 → sn.getReg .x15 = BitVec.ofNat 64 (C_TD + levelBase (8 + n))) ∧
        sn.getReg .x18 = BitVec.ofNat 64 commitChainScratch ∧
        sn.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (7 + n)) ∧
        sn.getReg .x25 = BitVec.ofNat 64 (C_DB + 704) ∧
        sn.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        (∀ l, 8 ≤ l → l ≤ 8 + n → ∀ idx < levelSize l,
          readBuffer sn (C_TD + levelBase l + gapOffset idx) 32 = nodeVal c96 msg salts l idx) ∧
        (levelSize (8 + n) % 2 = 1 →
          readBuffer sn (C_TD + levelBase (8 + n) + 96 * (levelSize (8 + n) / 2) + 32) 32 = 0) ∧
        (∀ l, 8 ≤ l → l ≤ 8 + n → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
        readBuffer sn (commitChainScratch + 32) 32 = 0 ∧
        readBuffer sn (commitChainScratch + 72) 24 = 0 ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (q < C_TD + levelBase 9 ∨ C_TD + levelBase (9 + n) ≤ q) →
          (q < commitChainScratch ∨ commitChainScratch + 72 ≤ q) →
          sn.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
    intro n hn; induction n with
    | zero =>
      refine ⟨sa, by simpa only [Finset.sum_range_zero] using DetRun.refl oracle (submission.image .commit) sa,
        by simpa only [show (0 : Nat) < 15 by decide, ite_true] using hsa_pc,
        (hsa_reg_other .x2 (by decide) (by decide)).trans hx2,
        (hsa_reg_other .x5 (by decide) (by decide)).trans hx5,
        (hsa_reg_other .x9 (by decide) (by decide)).trans hx9,
        (hsa_reg_other .x11 (by decide) (by decide)).trans hx11,
        (hsa_reg_other .x13 (by decide) (by decide)).trans hx13,
        fun h => (h rfl).elim, hsa_x18,
        (hsa_reg_other .x24 (by decide) (by decide)).trans hx24, hsa_x25,
        (hsa_reg_other .x26 (by decide) (by decide)).trans hx26,
        fun l hl1 hl2 idx hidx => by
          have : l = 8 := by omega
          subst this; rw [readBuffer_of_mem_eq hsa_mem]; exact hl8 idx hidx,
        fun _ => by
          rw [readBuffer_of_mem_eq hsa_mem]
          apply readBuffer_zero_of_bytes; intro j hj
          have hdiv : levelSize (8 + 0) / 2 = 21845 := by decide
          rw [hdiv]; exact hodd8 j hj,
        fun l hl1 hl2 q hq j hj => by
          have : l = 8 := by omega
          subst this; rw [getByte_of_mem_eq hsa_mem]; exact hgap8 q hq j hj,
        by rw [readBuffer_of_mem_eq hsa_mem]; exact hscrMid,
        by rw [readBuffer_of_mem_eq hsa_mem]; exact hscrHi,
        fun q _ _ _ => getByte_of_mem_eq hsa_mem _⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hx2n, hx5n, hx9n, hx11n, hx13n, _, hx18n, hx24n, hx25n, hx26n,
        hdign, hoddn, hgapn, hmidn, hhin, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 148415) := by
        simpa only [show n < 15 by omega, ite_true] using hpcn
      have hlb_9_9n : levelBase 9 ≤ levelBase (9 + n) := levelBase_mono 9 (9 + n) (by omega) (by omega)
      have hlb_9n_10n : levelBase (9 + n) ≤ levelBase (10 + n) := levelBase_mono (9 + n) (10 + n) (by omega) (by omega)
      have hlb_bd_9n := levelBase_bound (9 + n) (by omega)
      have hlb_10n_24 : levelBase (10 + n) ≤ levelBase 24 := levelBase_mono (10 + n) 24 (by omega) (le_refl _)
      have hbase_next : levelBase (10 + n) = levelBase (9 + n) + levelBytes (9 + n) := by
        rw [show 10 + n = (9 + n) + 1 by omega]; rfl
      obtain ⟨sm, hrun1, hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx15m, hx18m, hx24m, hx25m, hx26m,
        hdig1, hodd1, hgap1, hmid1, hhi1, hpres1⟩ :=
        p3c_level h768 oracle msg salts n (by omega) sn hpc_in hx2n hx5n hx9n hx11n hx13n hx18n hx24n hx25n hx26n
          (fun off hoff hal => by
            have heq : C_DB + 32 * (7 + n) + off = C_DB + (32 * (7 + n) + off) := by omega
            rw [heq, ← readBuffer_word sn _ (by omega)]
            have hrb : readBuffer sn (C_DB + (32 * (7 + n) + off)) 8 = readBuffer s0 (C_DB + (32 * (7 + n) + off)) 8 :=
              readBuffer_congr _ _ _ _ (fun j hj => hpresn _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))
            rw [hrb, readBuffer_word s0 _ (by omega)]
            exact hdata (32 * (7 + n) + off) (by omega) (by omega))
          (fun idx hidx => hdign (8 + n) (by omega) (le_refl _) idx hidx)
          hoddn
          (fun q hq j hj => hgapn (8 + n) (by omega) (le_refl _) q hq j hj)
          (fun off hoff => by
            rw [hpresn _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
            exact hzero9 _ (by omega) (by omega))
          hmidn hhin
      refine ⟨sm, by simpa only [Finset.sum_range_succ] using hrunn.trans hrun1,
        hpcm, hx2m, hx5m, hx9m, hx11m, hx13m,
        fun _ => by simpa only [show 8 + (n + 1) = 9 + n by omega] using hx15m,
        hx18m, hx24m, hx25m, hx26m, ?_,
        by simpa only [show 8 + (n + 1) = 9 + n by omega] using hodd1, ?_, hmid1, hhi1, ?_⟩
      · intro l hl1 hl2 idx hidx
        by_cases hcur : l = 9 + n
        · subst hcur; exact hdig1 idx hidx
        · have hlt : l ≤ 8 + n := by omega
          have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
          have hlb_l : levelBase l + levelBytes l ≤ levelBase (9 + n) := by
            have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
            rw [h1]; exact levelBase_mono (l + 1) (9 + n) (by omega) (by omega)
          have hbd_l := levelBase_bound l (by omega)
          have hrb : readBuffer sm (C_TD + levelBase l + gapOffset idx) 32 =
              readBuffer sn (C_TD + levelBase l + gapOffset idx) 32 :=
            readBuffer_congr _ _ _ _ (fun j hj => hpres1 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
          rw [hrb]; exact hdign l hl1 hlt idx hidx
      · intro l hl1 hl2 q hq j hj
        by_cases hcur : l = 9 + n
        · subst hcur; exact hgap1 q hq j hj
        · have hlt : l ≤ 8 + n := by omega
          have hbytes := levelBytes_eq_gap l (by omega) (by omega)
          have hlb_l : levelBase l + levelBytes l ≤ levelBase (9 + n) := by
            have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
            rw [h1]; exact levelBase_mono (l + 1) (9 + n) (by omega) (by omega)
          have hbd_l := levelBase_bound l (by omega)
          rw [hpres1 _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
          exact hgapn l hl1 hlt q hq j hj
      · intro q hq houtD houtS
        have h10 : 9 + (n + 1) = 10 + n := by omega
        rw [h10] at houtD
        exact (hpres1 q hq (by omega) houtS).trans (hpresn q hq (by omega) houtS)
  obtain ⟨sfin, hrun15, hpc15, _, hx5f, hx9f, hx11f, hx13f, hx15f, _, _, _, hx26f, hdigf, _, hgapf, _, _, hpresf⟩ :=
    hind 15 (le_refl _)
  have hrun_tot : DetRun oracle (submission.image .commit) s0 1424710 sfin 2847859 203307 := by
    have h := hsetup.trans hrun15
    rw [phase3C_steps_sum, phase3C_cycles_sum, Nat.zero_add, phase3C_calls_sum] at h
    exact h
  exact ⟨sfin, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpc15,
    hx5f, hx9f, hx11f, hx13f, hx15f (by decide), hx26f,
    fun l hl1 hl2 idx hidx => hdigf l (by omega) (by omega) idx hidx,
    fun l hl1 hl2 q hq j hj => hgapf l (by omega) (by omega) q hq j hj,
    hpresf⟩

/-- Full Phase 3 (`3A + 3B + 3C`, `L2..L23`, words `139327..148459`):
exact `24,243,190` steps, `64,507,344` cycles, `5,752,022` compression calls. -/
theorem commit_phase3 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 139327))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 704, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl1 : ∀ idx < levelSize 1, readBuffer s0 (C_TD + levelBase 1 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 idx)
    (hzero : ∀ l, 1 ≤ l → l < 24 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0)
    (hzero8 : ∀ addr, C_TD + levelBase 8 ≤ addr → addr < C_TD + levelBase 24 →
      s0.getByte (BitVec.ofNat 64 addr) = 0)
    (hscr0 : ∀ j < 96, s0.getByte (BitVec.ofNat 64 (commitChainScratch + j)) = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 24243190 s1 64507344 5752022 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148460) ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x15 = BitVec.ofNat 64 (C_TD + levelBase 23) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l, 2 ≤ l → l ≤ 23 → ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l, 2 ≤ l → l ≤ 23 → ∀ q < (levelSize l + 1) / 2,
        readBuffer s1 (C_TD + levelBase l + 96 * q + 64) 32 = 0) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < C_TD + levelBase 2 ∨ C_TD + levelBase 24 ≤ q) →
        (q < commitChainScratch ∨ commitChainScratch + 72 ≤ q) →
        s1.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476032 := rfl
  have hCS : commitChainScratch = 8589934592 := rfl
  have htb := treeBytes_eq
  have hlb2_6 : levelBase 2 ≤ levelBase 6 := levelBase_mono 2 6 (by omega) (by omega)
  have hlb6_8 : levelBase 6 ≤ levelBase 8 := levelBase_mono 6 8 (by omega) (by omega)
  have hlb8_9 : levelBase 8 ≤ levelBase 9 := levelBase_mono 8 9 (by omega) (by omega)
  have hlb9_24 : levelBase 9 ≤ levelBase 24 := levelBase_mono 9 24 (by omega) (by omega)
  have hlb6_bd := levelBase_bound 6 (by omega)
  have hlb8_bd := levelBase_bound 8 (by omega)
  have hlb9_bd := levelBase_bound 9 (by omega)
  have hlb24_bd := levelBase_bound 24 (by omega)
  have hbytes8 : levelBytes 8 = 21846 * 96 := by decide
  have hlb8_next : levelBase 8 + levelBytes 8 = levelBase 9 := rfl
  obtain ⟨sA, hrunA, hpcA, hx2A, hx5A, hx9A, hx11A, hx13A, hx24A, hx26A, hdigA, hgapA, hpresA⟩ :=
    commit_phase3A h768 oracle msg salts s0 hpc hx2 hx5 hx9 hx11 hx13 hx26 hdata hl1 hzero
  obtain ⟨sB, hrunB, hpcB, hx2B, hx5B, hx9B, hx11B, hx13B, hx24B, hx26B, hdigB, hgapB, hodd8B, hpresB⟩ :=
    commit_phase3B h768 oracle msg salts sA hpcA hx2A hx5A hx9A hx11A hx13A hx24A hx26A
      (fun off hoff hal => by
        rw [hpresA.getMem_eq (by omega) (by omega) (by omega)]; exact hdata off hoff hal)
      (fun idx hidx => hdigA 5 (by omega) (by omega) idx hidx)
      (fun l hl1 hl2 q hq j hj => hgapA l (by omega) hl2 q hq j hj)
      (fun j hj => by
        rw [hpresA _ (by omega) (Or.inr (by omega))]
        exact hzero8 _ (by omega) (by omega))
  obtain ⟨sC, hrunC, hpcC, hx5C, hx9C, hx11C, hx13C, hx15C, hx26C, hdigC, hgapC, hpresC⟩ :=
    commit_phase3C h768 oracle msg salts sB hpcB hx2B hx5B hx9B hx11B hx13B hx24B hx26B
      (fun off hoff hal => by
        rw [hpresB.getMem_eq (by omega) (by omega) (by omega),
            hpresA.getMem_eq (by omega) (by omega) (by omega)]
        exact hdata off hoff hal)
      (fun idx hidx => hdigB 8 (by omega) (by omega) idx hidx)
      hodd8B
      (fun q hq j hj => hgapB 8 (by omega) (by omega) q hq j hj)
      (fun addr ha1 ha2 => by
        rw [hpresB addr (by omega) (Or.inr (by omega)), hpresA addr (by omega) (Or.inr (by omega))]
        exact hzero8 addr (by omega) ha2)
      (readBuffer_zero_of_bytes sB (commitChainScratch + 32) 32 (fun j hj => by
        rw [hpresB _ (by omega) (Or.inr (by omega)), hpresA _ (by omega) (Or.inr (by omega))]
        have : commitChainScratch + 32 + j = commitChainScratch + (32 + j) := by omega
        rw [this]; exact hscr0 (32 + j) (by omega)))
      (readBuffer_zero_of_bytes sB (commitChainScratch + 72) 24 (fun j hj => by
        rw [hpresB _ (by omega) (Or.inr (by omega)), hpresA _ (by omega) (Or.inr (by omega))]
        have : commitChainScratch + 72 + j = commitChainScratch + (72 + j) := by omega
        rw [this]; exact hscr0 (72 + j) (by omega)))
  refine ⟨sC, (hrunA.trans hrunB).trans hrunC, hpcC, hx5C, hx9C, hx11C, hx13C, hx15C, hx26C, ?_, ?_, ?_⟩
  · intro l hl1 hl2 idx hidx
    by_cases hlt6 : l < 6
    · have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
      have hlb_l : levelBase l + levelBytes l ≤ levelBase 6 := by
        have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
        rw [h1]; exact levelBase_mono (l + 1) 6 (by omega) (by omega)
      have hbd_l := levelBase_bound l (by omega)
      have hrbC : readBuffer sC (C_TD + levelBase l + gapOffset idx) 32 =
          readBuffer sB (C_TD + levelBase l + gapOffset idx) 32 :=
        readBuffer_congr _ _ _ _ (fun j hj => hpresC _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
      rw [hrbC, hpresB.readBuffer_eq (by omega) (by omega)]
      exact hdigA l (by omega) (by omega) idx hidx
    · by_cases hlt9 : l < 9
      · have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
        have hlb_l : levelBase l + levelBytes l ≤ levelBase 9 := by
          have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
          rw [h1]; exact levelBase_mono (l + 1) 9 (by omega) (by omega)
        have hbd_l := levelBase_bound l (by omega)
        have hrbC : readBuffer sC (C_TD + levelBase l + gapOffset idx) 32 =
            readBuffer sB (C_TD + levelBase l + gapOffset idx) 32 :=
          readBuffer_congr _ _ _ _ (fun j hj => hpresC _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
        rw [hrbC]; exact hdigB l (by omega) (by omega) idx hidx
      · exact hdigC l (by omega) hl2 idx hidx
  · intro l hl1 hl2 q hq
    apply readBuffer_zero_of_bytes sC _ 32; intro j hj
    by_cases hlt9 : l < 9
    · have hbytes := levelBytes_eq_gap l (by omega) (by omega)
      have hbd := levelBase_bound l (by omega)
      have hlb_l : levelBase l + levelBytes l ≤ levelBase 9 := by
        have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
        rw [h1]; exact levelBase_mono (l + 1) 9 (by omega) (by omega)
      rw [hpresC _ (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
      by_cases hlt6 : l < 6
      · have hlb_l6 : levelBase l + levelBytes l ≤ levelBase 6 := by
          have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
          rw [h1]; exact levelBase_mono (l + 1) 6 (by omega) (by omega)
        rw [hpresB _ (by omega) (Or.inl (by omega))]
        exact hgapA l (by omega) (by omega) q hq j hj
      · exact hgapB l (by omega) (by omega) q hq j hj
    · exact hgapC l (by omega) hl2 q hq j hj
  · intro q hq houtD houtS
    exact ((hpresC q hq (by omega) houtS).trans (hpresB q hq (by omega))).trans (hpresA q hq (by omega))

/-! ### 4. Phase 4 (`L24` Root, Copy to Commitment, and `HALT(0)`, words `148460..148473`) -/

private theorem commit_fetch_copy32_phase4 (k : Nat) (hk : k < 4) (st : MachineState) :
    (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (148463 + 2 * k)) →
      fetch (submission.image .commit) st = some (.base (.LD .x6 .x12 (BitVec.ofNat 12 (0 + 8 * k))))) ∧
    (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (148463 + 2 * k + 1)) →
      fetch (submission.image .commit) st = some (.base (.SD .x26 .x6 (BitVec.ofNat 12 (0 + 8 * k))))) := by
  constructor
  · intro hpc'
    have h := commit_fetch_commitTailInstr st (148463 + 2 * k) (by omega) (by omega) hpc'
    interval_cases k <;> simpa only [commitTailInstr] using h
  · intro hpc'
    have h := commit_fetch_commitTailInstr st (148463 + 2 * k + 1) (by omega) (by omega) hpc'
    interval_cases k <;> simpa only [commitTailInstr] using h

/-- Phase 4 pre-halt (words `148460..148472`: `13` steps, `20` cycles, `1` compression call),
landing at `148473` (`ECALL HALT(0)`) with `rootVal` in both `C_TD + levelBase 24` and `C_CMT`. -/
theorem commit_phase4 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 148460))
    (hx5 : s0.getReg .x5 = 0#64) (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx15 : s0.getReg .x15 = BitVec.ofNat 64 (C_TD + levelBase 23))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hl23 : ∀ idx < 2, readBuffer s0 (C_TD + levelBase 23 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 23 idx)
    (hgap23 : readBuffer s0 (C_TD + levelBase 23 + 64) 32 = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 13 s1 20 1 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148473) ∧
      s1.getReg .x5 = 1#64 ∧
      s1.getReg .x10 = 0#64 ∧
      readBuffer s1 C_CMT 32 = rootVal (fun x => oracle.compression (x.cast h768.symm)) msg salts ∧
      readBuffer s1 (C_TD + levelBase 24) 32 =
        rootVal (fun x => oracle.compression (x.cast h768.symm)) msg salts ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < C_CMT ∨ C_CMT + 32 ≤ q) →
        (q < C_TD + levelBase 24 ∨ C_TD + levelBase 24 + 32 ≤ q) →
        s1.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_CMT : C_CMT = 4294971392 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hlb23 : levelBase 23 = 1073742752 := by decide
  have hlb24 : levelBase 24 = 1073742848 := by decide
  let r1 := execInstrBr s0 (.ADDI .x10 .x15 (0#12))
  let r2 := execInstrBr r1 (.ADDI .x12 .x15 (96#12))
  have hr1_pc : r1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148461) := pc_step_idx s0 148460 hpc
  have hr2_pc : r2.pc = BitVec.ofNat 64 (0x1000 + 4 * 148462) := pc_step_idx r1 148461 hr1_pc
  have hprep_run : DetRun oracle (submission.image .commit) s0 2 r2 2 0 :=
    (commit_step1_tail (by omega) (by omega) hpc (by simp only [commitTailInstr])).trans
      (commit_step1_tail (by omega) (by omega) hr1_pc (by simp only [commitTailInstr]))
  have hr2_mem : r2.mem = s0.mem := (mem_exec_ADDI r1 _ _ _).trans (mem_exec_ADDI s0 _ _ _)
  have hr2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → r2.getReg r = s0.getReg r := fun r h10 h12 => by
    simp only [r2, r1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
  have hr2_x10 : r2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 23) := by
    simp only [r2, r1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 .x10 (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx15,
      add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
  have hr2_x12 : r2.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 24) := by
    simp only [r2, r1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      getReg_setReg_ne' .x10 .x15 (by decide), hx15,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  let root := rootVal c96 msg salts
  let r3 := writeBits r2 (BitVec.ofNat 64 (C_TD + levelBase 24)) root
  have hr2_in : readBuffer r2 (C_TD + levelBase 23) 96 =
      binaryInput (nodeVal c96 msg salts 23 0) (nodeVal c96 msg salts 23 1) := by
    rw [readBuffer_of_mem_eq hr2_mem, readBuffer_binary_of_zero_gap s0 _ hgap23]
    have h0 := hl23 0 (by omega); have h1 := hl23 1 (by omega)
    rw [show gapOffset 0 = 0 from rfl, Nat.add_zero] at h0
    rw [show gapOffset 1 = 32 from rfl] at h1
    rw [h0, h1]
  have hroot_eq : oracle.compression ((readBuffer r2 (C_TD + levelBase 23) 96).cast h768.symm) = root := by
    rw [hr2_in]; exact nodeVal_root_eq c96 msg salts
  have hf62 : fetch (submission.image .commit) r2 = some (.base .ECALL) := by
    have h := commit_fetch_commitTailInstr r2 148462 (by omega) (by omega) hr2_pc
    simp only [commitTailInstr] at h; exact h
  have hcall_run : DetRun oracle (submission.image .commit) r2 1 r3 8 1 :=
    DetRun.compress_eq h768 hf62
      ((hr2_reg_other .x5 (by decide) (by decide)).trans hx5)
      ((hr2_reg_other .x11 (by decide) (by decide)).trans hx11)
      ((hr2_reg_other .x13 (by decide) (by decide)).trans hx13)
      (C_TD + levelBase 23) (C_TD + levelBase 24) hr2_x10 hr2_x12
      (by omega) (by omega) (by omega) (by omega) root hroot_eq
  have hr3_pc : r3.pc = BitVec.ofNat 64 (0x1000 + 4 * 148463) := pc_step_idx r2 148462 hr2_pc
  obtain ⟨rc, hcopy_run, hrc_pc, _, hrc_dig, hrc_pres⟩ :=
    commit_copy32 oracle r3 148463 .x12 .x26 (C_TD + levelBase 24) C_CMT 0 0
      (by decide) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hr3_pc
      ((writeBits_register r2 _ root .x12).trans hr2_x12)
      ((writeBits_register r2 _ root .x26).trans ((hr2_reg_other .x26 (by decide) (by decide)).trans hx26))
      commit_fetch_copy32_phase4
  let s1 := execInstrBr rc (.ADDI .x5 .x0 (1#12))
  let s2 := execInstrBr s1 (.ADDI .x10 .x0 (0#12))
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 148472) := pc_step_idx rc 148471 hrc_pc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 148473) := pc_step_idx s1 148472 hs1_pc
  have hs1_run : DetRun oracle (submission.image .commit) rc 1 s1 1 0 :=
    commit_step1_tail (by omega) (by omega) hrc_pc (by simp only [commitTailInstr])
  have hs2_run : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    commit_step1_tail (by omega) (by omega) hs1_pc (by simp only [commitTailInstr])
  have hs2_mem : s2.mem = rc.mem := (mem_exec_ADDI s1 _ _ _).trans (mem_exec_ADDI rc _ _ _)
  refine ⟨s2, ((hprep_run.trans hcall_run).trans hcopy_run).trans (hs1_run.trans hs2_run),
    hs2_pc,
    by simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x10 .x5 (by decide), MachineState.getReg_setReg_eq (by decide : Reg.x5 ≠ .x0),
        c_getReg_x0]; decide,
    by simp only [s2, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), c_getReg_x0]; decide, ?_, ?_, ?_⟩
  · rw [readBuffer_of_mem_eq hs2_mem]
    simpa only [Nat.add_zero] using hrc_dig.trans (writeBits_readBuffer_digest r2 (C_TD + levelBase 24) root)
  · rw [readBuffer_of_mem_eq hs2_mem, hrc_pres.readBuffer_eq (by omega) (by omega)]
    exact writeBits_readBuffer_digest r2 (C_TD + levelBase 24) root
  · intro q hq houtCmt houtRoot
    have h1 := getByte_of_mem_eq hs2_mem (BitVec.ofNat 64 q)
    have h2 := hrc_pres q hq (by simpa only [Nat.add_zero] using houtCmt)
    have h3 := memPreserved_writeBits r2 (C_TD + levelBase 24) root (by omega) q hq houtRoot
    have h4 := getByte_of_mem_eq hr2_mem (BitVec.ofNat 64 q)
    exact ((h1.trans h2).trans h3).trans h4

/-! ### 5. Top-Level Commit Exactness, Oracle Refinement, and Termination -/

private theorem commit_det_phases (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (s0 : MachineState) (rand : Fin (LENGTH / 2) → PairRand)
    (hinv :
      s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 16412) ∧
      s0.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s0.getReg .x5 = 0#64 ∧
      s0.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
      s0.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s0.getReg .x10 = BitVec.ofNat 64 (C_MSG - 256) ∧
      s0.getReg .x11 = 96#64 ∧
      s0.getReg .x13 = 0#64 ∧
      s0.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
      s0.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256) ∧
      s0.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ j : Fin (LENGTH / 2),
        readBuffer s0 (C_ROW + 184 * j.val + 72) 24 = pairSaltEven (rand j) ∧
        readBuffer s0 (C_ROW + 184 * j.val + 88) 24 = pairSaltOdd (rand j)) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (∀ j < LENGTH / 2, q < C_ROW + 184 * j + 72 ∨ C_ROW + 184 * j + 112 ≤ q) →
        s0.getByte (BitVec.ofNat 64 q) = (submission.initialState .commit message).getByte (BitVec.ofNat 64 q))) :
    ∃ sfin : MachineState,
      oracle.run (execute (submission.image .commit) (submission.steps .commit - 16779289) s0 true) =
        pure (⟨.success, sfin, 791533741, 78453292⟩, 78453292) ∧
      readBuffer sfin C_CMT 32 =
        rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) ∧
      CommittedTrapdoor h768 oracle.compression message (pairSalts rand)
        (readBuffer sfin C_TD submission.sizes.trapdoor) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_CMT : C_CMT = 4294971392 := rfl
  have hC_ROW : C_ROW = 5368714304 := rfl
  have hC_DB : C_DB = 68719476032 := rfl
  have hCS : commitChainScratch = 8589934592 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hsteps_ge : 16779289 + 242360697 ≤ submission.steps .commit := by decide
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let salts := pairSalts rand
  obtain ⟨hpc0, hx2_0, hx5_0, hx8_0, hx9_0, hx10_0, hx11_0, hx13_0, hx18_0, hx19_0, hx26_0,
    hsalts0, hpres0⟩ := hinv
  have hmsg0 : ∀ (i : Index) (j : Nat), j < 256 →
      s0.getByte (BitVec.ofNat 64 (C_MSG + 256 * i.val + j)) = (message i).extractLsb' (8 * j) 8 := by
    intro i j hj
    have hi := i.isLt
    rw [hpres0 (C_MSG + 256 * i.val + j) (by omega) (fun _ _ => by omega)]
    exact commit_initial_msg_byte message i j hj
  have hgap0 : ∀ p : Fin (LENGTH / 2),
      readBuffer s0 (C_ROW + 184 * p.val + 64) 8 = 0 ∧
      readBuffer s0 (C_ROW + 184 * p.val + 112) 8 = 0 := by
    intro p; have hp := p.isLt
    constructor
    · apply readBuffer_zero_of_bytes; intro b hb
      rw [hpres0 (C_ROW + 184 * p.val + 64 + b) (by omega) (fun j _ => by
        by_cases hjp : j = p.val
        · subst hjp; omega
        · omega)]
      exact commit_initial_zero_byte message _ (by omega)
    · apply readBuffer_zero_of_bytes; intro b hb
      rw [hpres0 (C_ROW + 184 * p.val + 112 + b) (by omega) (fun j _ => by
        by_cases hjp : j = p.val
        · subst hjp; omega
        · omega)]
      exact commit_initial_zero_byte message _ (by omega)
  obtain ⟨s1, hrun1, hpc1, hx2_1, hx5_1, hx9_1, hx11_1, hx13_1, hx26_1, hl0_1, hsalt1, hpres1⟩ :=
    commit_phase1 h768 oracle message rand s0 hpc0 hx2_0 hx5_0 hx8_0 hx9_0 hx10_0 hx11_0 hx13_0
      hx18_0 hx19_0 hx26_0 hmsg0 hsalts0 hgap0
  obtain ⟨s2, hrun2, hpc2, hx2_2, hx5_2, hx9_2, hx11_2, hx13_2, hx26_2, hl1_2, hgap1_2, hpres2⟩ :=
    commit_phase2 h768 oracle message salts s1 hpc1 hx2_1 hx5_1 hx9_1 hx11_1 hx13_1 hx26_1 hl0_1
  have hls0 := levelSize_0
  have hlb1 : levelBase 1 = 536870912 := by decide
  have hlb2 : levelBase 2 = 805306400 := by decide
  have hlb2_8 : levelBase 2 ≤ levelBase 8 := levelBase_mono 2 8 (by omega) (by omega)
  have hlb8_24 : levelBase 8 ≤ levelBase 24 := levelBase_mono 8 24 (by omega) (by omega)
  have hlb24 : levelBase 24 = 1073742848 := by decide
  have htb := treeBytes_eq
  have hro := rowOff_eq
  have htd := trapdoorBytes_eq
  have hdata2 : ∀ off < 704, off % 8 = 0 →
      s2.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit message).getMem (BitVec.ofNat 64 (C_DB + off)) := by
    intro off hoff hal
    rw [hpres2.getMem_eq (by omega) (by omega) (by omega),
      ← readBuffer_word s1 (C_DB + off) (by omega),
      ← readBuffer_word (submission.initialState .commit message) (C_DB + off) (by omega)]
    apply readBuffer_congr; intro j hj
    exact (hpres1 (C_DB + off + j) (by omega) (by omega)).trans
      (hpres0 (C_DB + off + j) (by omega) (fun _ _ => by omega))
  have hzero2 : ∀ l, 1 ≤ l → l < 24 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
      s2.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0 := by
    intro l hl1 hl2 q hq j hj
    have hbytes := levelBytes_eq_gap l hl1 hl2
    have hbd := levelBase_bound l (by omega)
    have hinit0 : (submission.initialState .commit message).getByte
        (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0 :=
      commit_initial_zero_byte message _ (by omega)
    have hp0 := hpres0 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (fun _ _ => by omega)
    have hlb_ge1 : levelBase 1 ≤ levelBase l := levelBase_mono 1 l hl1 (by omega)
    have hp1 := hpres1 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (by omega)
    by_cases hl1_eq : l = 1
    · subst hl1_eq
      exact ((hgap1_2 q hq j hj).trans hp1).trans (hp0.trans hinit0)
    · have hlb_ge2 : levelBase 2 ≤ levelBase l := levelBase_mono 2 l (by omega) (by omega)
      have hp2 := hpres2 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (by omega)
      exact ((hp2.trans hp1).trans hp0).trans hinit0
  have hzero8_2 : ∀ addr, C_TD + levelBase 8 ≤ addr → addr < C_TD + levelBase 24 →
      s2.getByte (BitVec.ofNat 64 addr) = 0 := by
    intro addr ha1 ha2
    rw [hpres2 addr (by omega) (Or.inr (by omega)), hpres1 addr (by omega) (by omega),
      hpres0 addr (by omega) (fun _ _ => by omega)]
    exact commit_initial_zero_byte message addr (by omega)
  have hscr0_2 : ∀ j < 96, s2.getByte (BitVec.ofNat 64 (commitChainScratch + j)) = 0 := by
    intro j hj
    rw [hpres2 _ (by omega) (Or.inr (by omega)), hpres1 _ (by omega) (by omega),
      hpres0 _ (by omega) (fun _ _ => by omega)]
    exact commit_initial_zero_byte message _ (by omega)
  obtain ⟨s3, hrun3, hpc3, hx5_3, hx9_3, hx11_3, hx13_3, hx15_3, hx26_3, hbin3, hgap3, hpres3⟩ :=
    commit_phase3 h768 oracle message salts s2 hpc2 hx2_2 hx5_2 hx9_2 hx11_2 hx13_2 hx26_2 hdata2 hl1_2 hzero2 hzero8_2 hscr0_2
  obtain ⟨s4, hrun4, hpc4, hx5_4, hx10_4, hcmt4, hroot4, hpres4⟩ :=
    commit_phase4 h768 oracle message salts s3 hpc3 hx5_3 hx11_3 hx13_3 hx15_3 hx26_3
      (fun idx hidx => hbin3 23 (by omega) (by omega) idx (by rw [levelSize_23]; exact hidx))
      (by simpa only [Nat.mul_zero, Nat.add_zero] using hgap3 23 (by omega) (by omega) 0 (by rw [levelSize_23]; omega))
  have hrun14 : DetRun oracle (submission.image .commit) s0 242360696 s4 791533740 78453292 :=
    ((hrun1.trans hrun2).trans hrun3).trans hrun4
  have hf148473 : fetch (submission.image .commit) s4 = some (.base .ECALL) := by
    have h := commit_fetch_commitTailInstr s4 148473 (by omega) (by omega) hpc4
    simp only [commitTailInstr] at h; exact h
  have hfin := hrun14.finish hf148473
    hx5_4 hx10_4 (submission.steps .commit - 16779289) (by omega)
  refine ⟨s4, hfin, ?_, ?_⟩
  · dsimp only [salts] at hcmt4; exact hcmt4
  · have htd_sz : submission.sizes.trapdoor = trapdoorBytes := trapdoorBytes_eq.symm
    refine ⟨?_, ?_, ?_⟩
    · intro l hl idx hidx
      have hoff_bd : levelBase l + nodeOffset l idx + 32 ≤ submission.sizes.trapdoor := by
        rw [htd_sz]
        have hbd := levelBase_bound l hl
        unfold nodeOffset
        by_cases h0 : l = 0
        · subst h0; simp only [ite_true]; unfold levelBase; omega
        · simp only [h0, ite_false]
          by_cases h24 : l = 24
          · subst h24; rw [levelSize_24] at hidx
            have : idx = 0 := by omega
            subst this; unfold gapOffset; rw [hlb24, htd]; decide
          · have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
            omega
      have hsl : BitVec.extractLsb' (8 * (levelBase l + nodeOffset l idx)) 256
          (readBuffer s4 C_TD submission.sizes.trapdoor) =
          readBuffer s4 (C_TD + (levelBase l + nodeOffset l idx)) 32 :=
        read_buffer_slice s4 C_TD submission.sizes.trapdoor (levelBase l + nodeOffset l idx) 32 hoff_bd
      rw [hsl]
      by_cases h0 : l = 0
      · subst h0
        have hnoff : levelBase 0 + nodeOffset 0 idx = 32 * idx := by
          unfold levelBase nodeOffset; simp only [ite_true]; omega
        rw [hnoff]
        have hp4 : readBuffer s4 (C_TD + 32 * idx) 32 = readBuffer s3 (C_TD + 32 * idx) 32 :=
          readBuffer_congr _ _ _ _ (fun j hj => hpres4 (C_TD + 32 * idx + j) (by omega) (by omega) (by omega))
        have hp3 : readBuffer s3 (C_TD + 32 * idx) 32 = readBuffer s2 (C_TD + 32 * idx) 32 :=
          readBuffer_congr _ _ _ _ (fun j hj => hpres3 (C_TD + 32 * idx + j) (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
        rw [hp4, hp3, hpres2.readBuffer_eq (by omega) (by omega)]
        exact hl0_1 idx hidx
      · by_cases h1 : l = 1
        · subst h1
          have hnoff : nodeOffset 1 idx = gapOffset idx := rfl
          rw [hnoff, ← Nat.add_assoc]
          have hgo := gapOffset_lt_levelBytes 1 idx (by omega) (by omega) hidx
          have hlb1_bytes : levelBase 1 + levelBytes 1 = levelBase 2 := rfl
          have hp4 : readBuffer s4 (C_TD + levelBase 1 + gapOffset idx) 32 =
              readBuffer s3 (C_TD + levelBase 1 + gapOffset idx) 32 :=
            readBuffer_congr _ _ _ _ (fun j hj => hpres4 (C_TD + levelBase 1 + gapOffset idx + j)
              (by omega) (by omega) (by omega))
          have hp3 : readBuffer s3 (C_TD + levelBase 1 + gapOffset idx) 32 =
              readBuffer s2 (C_TD + levelBase 1 + gapOffset idx) 32 :=
            readBuffer_congr _ _ _ _ (fun j hj => hpres3 (C_TD + levelBase 1 + gapOffset idx + j)
              (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
          rw [hp4, hp3]
          exact hl1_2 idx hidx
        · by_cases h24 : l = 24
          · subst h24
            rw [levelSize_24] at hidx
            have : idx = 0 := by omega
            subst this
            have hnoff : nodeOffset 24 0 = 0 := by decide
            rw [hnoff, Nat.add_zero]
            dsimp only [salts] at hroot4
            have hrt24 : rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) =
                nodeVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) 24 0 := rfl
            exact hroot4.trans hrt24
          · have hnoff : nodeOffset l idx = gapOffset idx := by unfold nodeOffset; simp only [h0, ite_false]
            rw [hnoff, ← Nat.add_assoc]
            have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
            have hlb_l : levelBase l + levelBytes l ≤ levelBase 24 := by
              have h1' : levelBase l + levelBytes l = levelBase (l + 1) := rfl
              rw [h1']; exact levelBase_mono (l + 1) 24 (by omega) (le_refl _)
            have hp4 : readBuffer s4 (C_TD + levelBase l + gapOffset idx) 32 =
                readBuffer s3 (C_TD + levelBase l + gapOffset idx) 32 :=
              readBuffer_congr _ _ _ _ (fun j hj => hpres4 (C_TD + levelBase l + gapOffset idx + j)
                (by omega) (by omega) (by omega))
            rw [hp4]
            exact hbin3 l (by omega) (by omega) idx hidx
    · intro l hl1 hl2 q hq
      have hbytes := levelBytes_eq_gap l hl1 hl2
      have hbd := levelBase_bound l (by omega)
      have hoff_bd : levelBase l + 96 * q + 64 + 32 ≤ submission.sizes.trapdoor := by
        rw [htd_sz]; omega
      have hsl : BitVec.extractLsb' (8 * (levelBase l + 96 * q + 64)) 256
          (readBuffer s4 C_TD submission.sizes.trapdoor) =
          readBuffer s4 (C_TD + (levelBase l + 96 * q + 64)) 32 :=
        read_buffer_slice s4 C_TD submission.sizes.trapdoor (levelBase l + 96 * q + 64) 32 hoff_bd
      rw [hsl]
      have hlb_l : levelBase l + levelBytes l ≤ levelBase 24 := by
        have h1' : levelBase l + levelBytes l = levelBase (l + 1) := rfl
        rw [h1']; exact levelBase_mono (l + 1) 24 (by omega) (le_refl _)
      have haddr : C_TD + (levelBase l + 96 * q + 64) = C_TD + levelBase l + 96 * q + 64 := by omega
      rw [haddr]
      have hp4 : readBuffer s4 (C_TD + levelBase l + 96 * q + 64) 32 =
          readBuffer s3 (C_TD + levelBase l + 96 * q + 64) 32 :=
        readBuffer_congr _ _ _ _ (fun j hj => hpres4 (C_TD + levelBase l + 96 * q + 64 + j)
          (by omega) (by omega) (by omega))
      rw [hp4]
      by_cases h1 : l = 1
      · subst h1
        have hlb1_bytes : levelBase 1 + levelBytes 1 = levelBase 2 := rfl
        have hp3 : readBuffer s3 (C_TD + levelBase 1 + 96 * q + 64) 32 =
            readBuffer s2 (C_TD + levelBase 1 + 96 * q + 64) 32 :=
          readBuffer_congr _ _ _ _ (fun j hj => hpres3 (C_TD + levelBase 1 + 96 * q + 64 + j)
            (by omega) (Or.inl (by omega)) (Or.inl (by omega)))
        rw [hp3]
        exact readBuffer_zero_of_bytes s2 _ 32 (fun j hj => by
          simpa only [Nat.add_assoc] using hzero2 1 (by omega) (by omega) q hq j hj)
      · exact hgap3 l (by omega) (by omega) q hq
    · intro i
      have hso_ge : rowOff ≤ saltOff i := by unfold saltOff; split_ifs <;> omega
      have hso_bd : saltOff i + 24 ≤ submission.sizes.trapdoor := by
        rw [htd_sz]; exact saltOff_add_24_le i
      have hsl : BitVec.extractLsb' (8 * saltOff i) 192
          (readBuffer s4 C_TD submission.sizes.trapdoor) =
          readBuffer s4 (C_TD + saltOff i) 24 :=
        read_buffer_slice s4 C_TD submission.sizes.trapdoor (saltOff i) 24 hso_bd
      rw [hsl]
      have hp4 : readBuffer s4 (C_TD + saltOff i) 24 = readBuffer s3 (C_TD + saltOff i) 24 :=
        readBuffer_congr _ _ _ _ (fun j hj => hpres4 (C_TD + saltOff i + j)
          (by omega) (by omega) (by omega))
      have hp3 : readBuffer s3 (C_TD + saltOff i) 24 = readBuffer s2 (C_TD + saltOff i) 24 :=
        readBuffer_congr _ _ _ _ (fun j hj => hpres3 (C_TD + saltOff i + j)
          (by omega) (Or.inr (by omega)) (Or.inl (by omega)))
      rw [hp4, hp3, hpres2.readBuffer_eq (by omega) (by omega)]
      exact hsalt1 i

private theorem readBuffer_digest_eq (s : MachineState) (a : Nat) (v : Commitment)
    (h : readBuffer s a 32 = v) : readBuffer s a DIGEST_BYTES = v := by
  have hgen : ∀ (n : Nat) (hn : n = 32) (w : BitVec (8 * n)),
      readBuffer s a 32 = w.cast (by rw [hn]) → readBuffer s a n = w := by
    intro n hn; subst hn; intro w hw; exact hw
  exact hgen DIGEST_BYTES rfl v h

private theorem commit_run_eq_helper (oracle : Oracle) (message : Message)
    (post0 finalState : (Fin (LENGTH / 2) → PairRand) → MachineState)
    (hrun0 : oracle.run (execute (submission.image .commit) (16779289 + (submission.steps .commit - 16779289))
        (submission.initialState .commit message) true) =ᵈ
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        (fun p : Execution × Nat => (p.1.charge 58722329 0, p.2)) <$>
          oracle.run (execute (submission.image .commit) (submission.steps .commit - 16779289) (post0 rand) true)))
    (hs : ∀ rand, oracle.run (execute (submission.image .commit) (submission.steps .commit - 16779289) (post0 rand) true) =
      pure (⟨.success, finalState rand, 791533741, 78453292⟩, 78453292)) :
    oracle.run (submission.run .commit message) =ᵈ
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        pure (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 850256070, oracleCalls := 78453292 } : Execution), 78453292)) := by
  have hsteps_commit : submission.steps .commit = 16779289 + (submission.steps .commit - 16779289) := by
    have hge : 16779289 ≤ submission.steps .commit := by decide
    omega
  rw [submission_run_commit submission message, hsteps_commit]
  refine hrun0.trans ?_
  apply EvalDistEq.bind_right; intro rand
  rw [hs rand, map_pure]
  have heq : (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 791533741, oracleCalls := 78453292 } : Execution).charge 58722329 0, 78453292) =
      (({ exit := Riscv.Exit.success, state := finalState rand,
          cycles := 850256070, oracleCalls := 78453292 } : Execution), 78453292) := by
    unfold Execution.charge; dsimp only
  rw [heq]

private theorem commit_read_spec_helper (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (sfin : MachineState) (salts : Index → Salt192)
    (hcmt : readBuffer sfin C_CMT 32 = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts)
    (htd : CommittedTrapdoor h768 oracle.compression message salts (readBuffer sfin C_TD submission.sizes.trapdoor)) :
    let (cmt, td) := submission.readCommit ⟨.success, sfin, 850256070, 78453292⟩
    cmt = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts ∧
    CommittedTrapdoor h768 oracle.compression message salts td := by
  have hC_CMT_eq : submission.layout.commitment = C_CMT := rfl
  have hC_TD_eq : submission.layout.trapdoor = C_TD := rfl
  dsimp only
  unfold Submission.readCommit
  dsimp only
  rw [hC_CMT_eq, hC_TD_eq]
  exact ⟨readBuffer_digest_eq sfin C_CMT _ hcmt, htd⟩

/-- Full exact execution of `submission.run .commit message` for any fixed oracle and message:
always halts with `.success`, exactly `850,256,070` cycles and `78,453,292` compression calls,
writing `rootVal` to the commitment buffer and a valid `CommittedTrapdoor` to the trapdoor buffer. -/
theorem commit_run_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    ∃ finalState : (Fin (LENGTH / 2) → PairRand) → MachineState,
      oracle.run (submission.run .commit message) =ᵈ
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (({ exit := Riscv.Exit.success, state := finalState rand,
                   cycles := 850256070, oracleCalls := 78453292 } : Execution), 78453292)) ∧
      ∀ rand,
        let salts := pairSalts rand
        let (cmt, td) := submission.readCommit
          ⟨Riscv.Exit.success, finalState rand, 850256070, 78453292⟩
        cmt = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts ∧
        CommittedTrapdoor h768 oracle.compression message salts td := by
  obtain ⟨post0, hrun0, hinv0⟩ := commit_phase0 oracle message (submission.steps .commit - 16779289)
  have hdet : ∀ rand : Fin (LENGTH / 2) → PairRand,
      ∃ sfin : MachineState,
        oracle.run (execute (submission.image .commit) (submission.steps .commit - 16779289) (post0 rand) true) =
          pure (⟨.success, sfin, 791533741, 78453292⟩, 78453292) ∧
        readBuffer sfin C_CMT 32 =
          rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) ∧
        CommittedTrapdoor h768 oracle.compression message (pairSalts rand)
          (readBuffer sfin C_TD submission.sizes.trapdoor) :=
    fun rand => commit_det_phases h768 oracle message (post0 rand) rand (hinv0 rand)
  let finalState (rand : Fin (LENGTH / 2) → PairRand) : MachineState := Classical.choose (hdet rand)
  exact ⟨finalState,
    commit_run_eq_helper oracle message post0 finalState hrun0 (fun rand => (Classical.choose_spec (hdet rand)).1),
    fun rand => commit_read_spec_helper h768 oracle message (finalState rand) (pairSalts rand)
      (Classical.choose_spec (hdet rand)).2.1 (Classical.choose_spec (hdet rand)).2.2⟩

/-- Exact `fixedOracleRun` refinement of `submission.scheme.commit message` for `MoonHiding`. -/
theorem commit_oracle_run_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    ∃ trapdoorOf : (Fin (LENGTH / 2) → PairRand) → BitVec (8 * submission.sizes.trapdoor),
      fixedOracleRun oracle (submission.scheme.commit message) =ᵈ
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (rootVal (fun x => oracle.compression (x.cast h768.symm)) message
            (pairSalts rand), trapdoorOf rand)) ∧
      ∀ rand,
        CommittedTrapdoor h768 oracle.compression message (pairSalts rand) (trapdoorOf rand) := by
  obtain ⟨finalState, hrun, hspec⟩ := commit_run_exact h768 oracle message
  refine ⟨fun rand => (submission.readCommit ⟨.success, finalState rand, 850256070, 78453292⟩).2, ?_, ?_⟩
  · let f : Execution × Nat → Commitment × BitVec (8 * submission.sizes.trapdoor) :=
      fun p => submission.readCommit p.1
    have hmap : (fixedOracleRun oracle (submission.scheme.commit message) :
          ProbComp (Commitment × BitVec (8 * submission.sizes.trapdoor))) =
        f <$> oracle.run (submission.run .commit message) := by
      simp only [fixedOracleRun, Submission.scheme, oracle_run_map, Functor.map_map, f]
    have hstep : f <$> (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (({ exit := Riscv.Exit.success, state := finalState rand,
                   cycles := 850256070, oracleCalls := 78453292 } : Execution), 78453292)) =
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand),
                (submission.readCommit ⟨.success, finalState rand, 850256070, 78453292⟩).2)) := by
      rw [map_bind]
      apply bind_congr; intro rand
      rw [map_pure]
      exact congrArg pure (Prod.ext (hspec rand).1 rfl)
    exact hmap.symm ▸ (hstep ▸ (hrun.map f))
  · intro rand; exact (hspec rand).2

private theorem commit_prEvent_uniform_bind_pure_eq_one {α β : Type} [SampleableType α]
    (f : α → β) (p : β → Prop) (h : ∀ a, p (f a)) :
    Pr{let y ← (($ᵗ α) >>= fun a => pure (f a))}[p y] = 1 := by
  have h1 : Pr{let y ← (($ᵗ α) >>= fun a => pure (f a))}[p y] =
      Pr{let y ← (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit))}[True] := by
    apply prEvent_bind_congr ($ᵗ α) (fun a => pure (f a)) (fun _ => pure ()) p (fun _ => True)
    intro a
    classical
    rw [prEvent_pure, prEvent_pure, ite_eq_left (h a), ite_eq_left trivial]
  rw [h1]
  have h2 : (fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit)) =
      (($ᵗ α) >>= fun _ => (pure True : ProbComp Prop)) := by
    simp only [map_bind, map_pure]
  change prEvent ((fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit))) = 1
  rw [h2, prEvent_def, OracleComp.evalDist_bind_const]
  change prEvent (pure True : ProbComp Prop) = 1
  rw [prEvent_pure_prop, ite_eq_left trivial]

/-- `submission.run .commit` always terminates with probability 1 for every oracle and message. -/
theorem commit_termination (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    Pr{let result ← oracle.run (submission.run .commit message)}[
      result.1.exit ≠ Riscv.Exit.unfinished] = 1 := by
  obtain ⟨finalState, hrun, _⟩ := commit_run_exact h768 oracle message
  rw [hrun.prEvent_eq _]
  exact commit_prEvent_uniform_bind_pure_eq_one
    (fun rand => ((⟨.success, finalState rand, 850256070, 78453292⟩ : Execution), 78453292))
    (fun result => result.1.exit ≠ Riscv.Exit.unfinished)
    (fun _ => by dsimp only; decide)

end CommitGolfCandidate
