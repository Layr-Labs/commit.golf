import CommitGolfCandidate.MoonCommitBin
import CommitGolfCandidate.CompressionSampling

/-! Exact RV64IM execution proofs for Phases 3U, 3A, 3B, and 4 of the r=2 `commit` image, plus full-commit
composition proving `commit_run_exact`, `commit_oracle_run_exact`, and `commit_termination`:
- Phase 3U: 2-level unmasked 256-bit binary driver (`L3..L4`, words `59445..60241`)
- Phase 3A: 4-level 240-bit binary driver (`L5..L8`, words `60242..60809`)
- Phase 3B: 14-level 238-bit binary driver (`L9..L22`, words `60810..61642`)
- Phase 4: unmasked 256-bit `L23` root + copy to commitment + `HALT(0)` (words `61643..61666`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Phase 3: Split 256-Bit (`L3..L4`) + 240-Bit (`L5..L8`) + 238-Bit (`L9..L22`) Binary Drivers -/

private theorem phase3U_steps_sum :
    2 + ∑ i ∈ Finset.range 2, binULevelSteps i = 4200146 := by decide

private theorem phase3U_cycles_sum :
    2 + ∑ i ∈ Finset.range 2, binULevelCycles i = 13986860 := by decide

private theorem phase3U_calls_sum :
    ∑ i ∈ Finset.range 2, binULevelCalls i = 1398102 := by decide

private theorem phase3A_steps_sum :
    1 + ∑ k ∈ Finset.range 4, binLevelSteps (2 + k) = 1751318 := by decide

private theorem phase3A_cycles_sum :
    1 + ∑ k ∈ Finset.range 4, binLevelCycles (2 + k) = 4809660 := by decide

private theorem phase3A_calls_sum :
    ∑ k ∈ Finset.range 4, binLevelCalls (2 + k) = 436906 := by decide

private theorem phase3B_steps_sum :
    4 + ∑ k ∈ Finset.range 14, bin238LevelSteps (6 + k) = 176018 := by decide

private theorem phase3B_cycles_sum :
    4 + ∑ k ∈ Finset.range 14, bin238LevelCycles (6 + k) = 379900 := by decide

private theorem phase3B_calls_sum :
    ∑ k ∈ Finset.range 14, bin238LevelCalls (6 + k) = 29126 := by decide

private theorem levelBase_mono : ∀ a b, a ≤ b → b ≤ 23 → levelBase a ≤ levelBase b := by
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

/-- Phase 3U (`L3..L4`, unmasked 256-bit, words `59445..60241`):
`4,200,146` steps, `13,986,860` cycles, `1,398,102` calls. -/
private theorem commit_phase3U (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 59445))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 640, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl2 : ∀ idx < levelSize 2, readBuffer s0 (C_TD + levelBase 2 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 2 idx)
    (hzero : ∀ l, 2 ≤ l → l < 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 4200146 s1 13986860 1398102 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 60242) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x24 = BitVec.ofNat 64 (C_DB + 64) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l, 2 ≤ l → l ≤ 4 → ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l, 2 ≤ l → l < 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 3) (C_TD + levelBase 5) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476096 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have htb := treeBytes_eq
  let sa0 := execInstrBr s0 (.ADDI .x24 .x2 (0#12))
  let sa := execInstrBr sa0 (.ADDI .x25 .x2 (64#12))
  have hsa0_pc : sa0.pc = BitVec.ofNat 64 (0x1000 + 4 * 59446) := pc_step_idx s0 59445 hpc
  have hsa_pc : sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 59447) := pc_step_idx sa0 59446 hsa0_pc
  have hsetup : DetRun oracle (submission.image .commit) s0 2 sa 2 0 := by
    have r0 : DetRun oracle (submission.image .commit) s0 1 sa0 1 0 :=
      commit_step1_mid2B (by omega) (by omega) hpc (by simp only [commitMid2BInstr])
    have r1 : DetRun oracle (submission.image .commit) sa0 1 sa 1 0 :=
      commit_step1_mid2B (by omega) (by omega) hsa0_pc (by simp only [commitMid2BInstr])
    exact r0.trans r1
  have hsa_mem : sa.mem = s0.mem := (mem_exec_ADDI sa0 _ _ _).trans (mem_exec_ADDI s0 _ _ _)
  have hsa_reg_other : ∀ r : Reg, r ≠ .x24 → r ≠ .x25 → sa.getReg r = s0.getReg r := fun r h24 h25 => by
    simp only [sa, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x25 r (Ne.symm h25), getReg_setReg_ne' .x24 r (Ne.symm h24)]
  have hind : ∀ n ≤ 2,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa (∑ i ∈ Finset.range n, binULevelSteps i) sn
          (∑ i ∈ Finset.range n, binULevelCycles i) (∑ i ∈ Finset.range n, binULevelCalls i) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 2 then 59447 else 60242)) ∧
        sn.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sn.getReg .x5 = 0#64 ∧
        sn.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sn.getReg .x11 = 96#64 ∧
        sn.getReg .x13 = 0#64 ∧ sn.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * n) ∧
        sn.getReg .x25 = BitVec.ofNat 64 (C_DB + 64) ∧ sn.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        (∀ l, 2 ≤ l → l ≤ n + 2 → ∀ idx < levelSize l,
          readBuffer sn (C_TD + levelBase l + gapOffset idx) 32 = nodeVal c96 msg salts l idx) ∧
        (∀ l, 2 ≤ l → l < 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
        MemPreservedOutside s0 sn (C_TD + levelBase 3) (C_TD + levelBase (n + 3)) := by
    intro n hn; induction n with
    | zero =>
      refine ⟨sa, by simpa only [Finset.sum_range_zero] using DetRun.refl oracle (submission.image .commit) sa,
        by simpa only [show (0 : Nat) < 2 by decide, ite_true] using hsa_pc,
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
          have : l = 2 := by omega
          subst this
          rw [readBuffer_of_mem_eq hsa_mem]
          exact hl2 idx hidx,
        fun l hl1 hl2 q hq j hj => by
          rw [getByte_of_mem_eq hsa_mem]
          exact hzero l hl1 hl2 q hq j hj,
        MemPreservedOutside.of_mem_eq hsa_mem _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hx2n, hx5n, hx9n, hx11n, hx13n, hx24n, hx25n, hx26n, hdign, hgapn, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 59447) := by
        simpa only [show n < 2 by omega, ite_true] using hpcn
      have hlb_bd := levelBase_bound (n + 3) (by omega)
      obtain ⟨sm, hrun1, hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx24m, hx25m, hx26m, hdig1, hgap1, hpres1⟩ :=
        commit_binU_level h768 oracle msg salts n (by omega) sn hpc_in hx2n hx5n hx9n hx11n hx13n hx24n hx25n hx26n
          (fun off hoff hal => by
            have heq : C_DB + 32 * n + off = C_DB + (32 * n + off) := by omega
            rw [heq, hpresn.getMem_eq (by omega) (by omega) (by omega)]
            exact hdata (32 * n + off) (by omega) (by omega))
          (fun idx hidx => hdign (n + 2) (by omega) (by omega) idx hidx)
          (fun q hq => readBuffer_zero_of_bytes sn _ 32 (fun j hj => by
            simpa only [Nat.add_assoc] using hgapn (n + 2) (by omega) (by omega) q hq j hj))
      have hlb_n3_n4 : levelBase (n + 3) ≤ levelBase (n + 4) := levelBase_mono _ _ (by omega) (by omega)
      have hlb_3_n3 : levelBase 3 ≤ levelBase (n + 3) := levelBase_mono _ _ (by omega) (by omega)
      refine ⟨sm, by simpa only [Finset.sum_range_succ] using hrunn.trans hrun1,
        hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx24m, hx25m, hx26m, ?_, ?_, ?_⟩
      · intro l hl1 hl2 idx hidx
        by_cases hcur : l = n + 3
        · subst hcur; exact hdig1 idx hidx
        · have hlt : l ≤ n + 2 := by omega
          have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
          have hlb_l : levelBase l + levelBytes l ≤ levelBase (n + 3) := by
            have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
            rw [h1]; exact levelBase_mono (l + 1) (n + 3) (by omega) (by omega)
          have hlb_bd_l := levelBase_bound l (by omega)
          rw [hpres1.readBuffer_eq (by omega) (by omega)]
          exact hdign l hl1 hlt idx hidx
      · intro l hl1 hl2 q hq j hj
        by_cases hcur : l = n + 3
        · subst hcur
          exact (hgap1 q hq j hj).trans (hgapn (n + 3) (by omega) (by omega) q hq j hj)
        · have hbytes := levelBytes_eq_gap l hl1 hl2
          have hbd := levelBase_bound l (by omega)
          have hout : C_TD + levelBase l + 96 * q + 64 + j < C_TD + levelBase (n + 3) ∨
              C_TD + levelBase (n + 4) ≤ C_TD + levelBase l + 96 * q + 64 + j := by
            by_cases hlt : l < n + 3
            · left
              have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
              have h2 := levelBase_mono (l + 1) (n + 3) (by omega) (by omega)
              omega
            · right
              have h2 := levelBase_mono (n + 4) l (by omega) (by omega)
              omega
          exact (hpres1 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) hout).trans (hgapn l hl1 hl2 q hq j hj)
      · have hne_n : n + 1 + 3 = n + 4 := by omega
        rw [hne_n]
        exact (hpresn.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (le_refl _))
  obtain ⟨sfin, hrun2, hpc2, hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, _, hx26f, hdigf, hgapf, hpresf⟩ :=
    hind 2 (le_refl _)
  have hrun_tot : DetRun oracle (submission.image .commit) s0 4200146 sfin 13986860 1398102 := by
    have h := hsetup.trans hrun2
    rw [phase3U_steps_sum, phase3U_cycles_sum, Nat.zero_add, phase3U_calls_sum] at h
    exact h
  exact ⟨sfin, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpc2,
    hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, hx26f, hdigf, hgapf, hpresf⟩

/-- Phase 3A (`L5..L8`, 240-bit masked, words `60242..60809`):
`1,751,318` steps, `4,809,660` cycles, `436,906` calls. -/
private theorem commit_phase3A (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 60242))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 64))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 640, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl4 : ∀ idx < levelSize 4, readBuffer s0 (C_TD + levelBase 4 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 4 idx)
    (hzero : ∀ l, 4 ≤ l → l < 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 1751318 s1 4809660 436906 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 60810) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x24 = BitVec.ofNat 64 (C_DB + 192) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l, 5 ≤ l → l ≤ 8 → ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l, 4 ≤ l → l < 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 5) (C_TD + levelBase 9) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476096 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have htb := treeBytes_eq
  let sa := execInstrBr s0 (.ADDI .x25 .x2 (192#12))
  have hsa_pc : sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 60243) := pc_step_idx s0 60242 hpc
  have hsetup : DetRun oracle (submission.image .commit) s0 1 sa 1 0 :=
    commit_step1_mid3U (by omega) (by omega) hpc (by simp only [commitMid3UInstr])
  have hsa_mem : sa.mem = s0.mem := mem_exec_ADDI s0 _ _ _
  have hsa_reg_other : ∀ r : Reg, r ≠ .x25 → sa.getReg r = s0.getReg r := fun r h25 => by
    simp only [sa, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x25 r (Ne.symm h25)]
  have hsa_x25 : sa.getReg .x25 = BitVec.ofNat 64 (C_DB + 192) := by
    simp only [sa, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0), hx2]; decide
  have hind : ∀ k ≤ 4,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa (∑ i ∈ Finset.range k, binLevelSteps (2 + i)) sn
          (∑ i ∈ Finset.range k, binLevelCycles (2 + i)) (∑ i ∈ Finset.range k, binLevelCalls (2 + i)) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k < 4 then 60243 else 60810)) ∧
        sn.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sn.getReg .x5 = 0#64 ∧
        sn.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sn.getReg .x11 = 96#64 ∧
        sn.getReg .x13 = 0#64 ∧ sn.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (2 + k)) ∧
        sn.getReg .x25 = BitVec.ofNat 64 (C_DB + 192) ∧ sn.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        (∀ l, 4 ≤ l → l ≤ k + 4 → ∀ idx < levelSize l,
          readBuffer sn (C_TD + levelBase l + gapOffset idx) 32 = nodeVal c96 msg salts l idx) ∧
        (∀ l, 4 ≤ l → l < 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
        MemPreservedOutside s0 sn (C_TD + levelBase 5) (C_TD + levelBase (k + 5)) := by
    intro k hk; induction k with
    | zero =>
      refine ⟨sa, by simpa only [Finset.sum_range_zero] using DetRun.refl oracle (submission.image .commit) sa,
        by simpa only [show (0 : Nat) < 4 by decide, ite_true] using hsa_pc,
        (hsa_reg_other .x2 (by decide)).trans hx2,
        (hsa_reg_other .x5 (by decide)).trans hx5,
        (hsa_reg_other .x9 (by decide)).trans hx9,
        (hsa_reg_other .x11 (by decide)).trans hx11,
        (hsa_reg_other .x13 (by decide)).trans hx13,
        (hsa_reg_other .x24 (by decide)).trans hx24,
        hsa_x25,
        (hsa_reg_other .x26 (by decide)).trans hx26,
        fun l hl_lo hl_hi idx hidx => by
          have : l = 4 := by omega
          subst this
          rw [readBuffer_of_mem_eq hsa_mem]
          exact hl4 idx hidx,
        fun l hl1 hl2 q hq j hj => by
          rw [getByte_of_mem_eq hsa_mem]
          exact hzero l hl1 hl2 q hq j hj,
        MemPreservedOutside.of_mem_eq hsa_mem _ _⟩
    | succ k ih =>
      obtain ⟨sn, hrunn, hpcn, hx2n, hx5n, hx9n, hx11n, hx13n, hx24n, hx25n, hx26n, hdign, hgapn, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 60243) := by
        simpa only [show k < 4 by omega, ite_true] using hpcn
      have hlb_bd := levelBase_bound (k + 5) (by omega)
      obtain ⟨sm, hrun1, hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx24m, hx25m, hx26m, hdig1, hgap1, hpres1⟩ :=
        commit_bin_level h768 oracle msg salts (2 + k) (by omega) (by omega) sn hpc_in
          hx2n hx5n hx9n hx11n hx13n hx24n hx25n hx26n
          (fun off hoff hal => by
            have heq : C_DB + 32 * (2 + k) + off = C_DB + (32 * (2 + k) + off) := by omega
            rw [heq, hpresn.getMem_eq (by omega) (by omega) (by omega)]
            exact hdata (32 * (2 + k) + off) (by omega) (by omega))
          (fun idx hidx => hdign (2 + k + 2) (by omega) (by omega) idx hidx)
          (fun q hq => readBuffer_zero_of_bytes sn _ 32 (fun j hj => by
            simpa only [Nat.add_assoc] using hgapn (2 + k + 2) (by omega) (by omega) q hq j hj))
      have hpc_eq : sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k + 1 < 4 then 60243 else 60810)) := by
        simpa only [show (2 + k + 1 < 6) ↔ (k + 1 < 4) by omega] using hpcm
      have hx24_eq : sm.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (2 + (k + 1))) := by
        simpa only [show 2 + k + 1 = 2 + (k + 1) by omega] using hx24m
      have hlb_k5_k6 : levelBase (k + 5) ≤ levelBase (k + 6) := levelBase_mono _ _ (by omega) (by omega)
      have hlb_5_k5 : levelBase 5 ≤ levelBase (k + 5) := levelBase_mono _ _ (by omega) (by omega)
      have h2k3 : 2 + k + 3 = k + 5 := by omega
      have h2k4 : 2 + k + 4 = k + 6 := by omega
      rw [h2k3, h2k4] at hpres1
      refine ⟨sm, by simpa only [Finset.sum_range_succ] using hrunn.trans hrun1,
        hpc_eq, hx2m, hx5m, hx9m, hx11m, hx13m, hx24_eq, hx25m, hx26m, ?_, ?_, ?_⟩
      · intro l hl1 hl2 idx hidx
        by_cases hcur : l = k + 5
        · subst hcur; simpa only [h2k3] using hdig1 idx (by simpa only [h2k3] using hidx)
        · have hlt : l ≤ k + 4 := by omega
          have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
          have hlb_l : levelBase l + levelBytes l ≤ levelBase (k + 5) := by
            have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
            rw [h1]; exact levelBase_mono (l + 1) (k + 5) (by omega) (by omega)
          have hlb_bd_l := levelBase_bound l (by omega)
          rw [hpres1.readBuffer_eq (by omega) (by omega)]
          exact hdign l hl1 hlt idx hidx
      · intro l hl1 hl2 q hq j hj
        by_cases hcur : l = k + 5
        · subst hcur
          have hg1 := hgap1 q (by simpa only [h2k3] using hq) j hj
          rw [h2k3] at hg1
          exact hg1.trans (hgapn (k + 5) (by omega) (by omega) q hq j hj)
        · have hbytes := levelBytes_eq_gap l (by omega) hl2
          have hbd := levelBase_bound l (by omega)
          have hout : C_TD + levelBase l + 96 * q + 64 + j < C_TD + levelBase (k + 5) ∨
              C_TD + levelBase (k + 6) ≤ C_TD + levelBase l + 96 * q + 64 + j := by
            by_cases hlt : l < k + 5
            · left
              have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
              have h2 := levelBase_mono (l + 1) (k + 5) (by omega) (by omega)
              omega
            · right
              have h2 := levelBase_mono (k + 6) l (by omega) (by omega)
              omega
          exact (hpres1 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) hout).trans (hgapn l hl1 hl2 q hq j hj)
      · have hne_k : k + 1 + 5 = k + 6 := by omega
        rw [hne_k]
        exact (hpresn.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (le_refl _))
  obtain ⟨sfin, hrun4, hpc4, hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, _, hx26f, hdigf, hgapf, hpresf⟩ :=
    hind 4 (le_refl _)
  have hrun_tot : DetRun oracle (submission.image .commit) s0 1751318 sfin 4809660 436906 := by
    have h := hsetup.trans hrun4
    rw [phase3A_steps_sum, phase3A_cycles_sum, Nat.zero_add, phase3A_calls_sum] at h
    exact h
  exact ⟨sfin, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpc4,
    hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, hx26f,
    fun l hl1 hl2 idx hidx => hdigf l (by omega) (by omega) idx hidx,
    hgapf, hpresf⟩

/-- Phase 3B (`L9..L22`, 238-bit masked, words `60810..61642`):
`176,018` steps, `379,900` cycles, `29,126` calls. -/
private theorem commit_phase3B (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 60810))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 192))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 640, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl8 : ∀ idx < levelSize 8, readBuffer s0 (C_TD + levelBase 8 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 8 idx)
    (hzero : ∀ l, 8 ≤ l → l < 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 176018 s1 379900 29126 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 61643) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l, 9 ≤ l → l ≤ 22 → ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l, 8 ≤ l → l < 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 9) (C_TD + levelBase 23) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476096 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have htb := treeBytes_eq
  -- Setup words 60810..60813: x25 = C_DB + 640, x27 = mask238Word
  let sa0 := execInstrBr s0 (.ADDI .x25 .x2 (640#12))
  let sa1 := execInstrBr sa0 (.ADDI .x27 .x0 (1#12))
  let sa2 := execInstrBr sa1 (.SLLI .x27 .x27 (46#6))
  let sa := execInstrBr sa2 (.ADDI .x27 .x27 (4095#12))
  have hsa0_pc : sa0.pc = BitVec.ofNat 64 (0x1000 + 4 * 60811) := pc_step_idx s0 60810 hpc
  have hsa1_pc : sa1.pc = BitVec.ofNat 64 (0x1000 + 4 * 60812) := pc_step_idx sa0 60811 hsa0_pc
  have hsa2_pc : sa2.pc = BitVec.ofNat 64 (0x1000 + 4 * 60813) := pc_step_idx sa1 60812 hsa1_pc
  have hsa_pc : sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 60814) := pc_step_idx sa2 60813 hsa2_pc
  have hsetup : DetRun oracle (submission.image .commit) s0 4 sa 4 0 := by
    have r0 : DetRun oracle (submission.image .commit) s0 1 sa0 1 0 :=
      commit_step1_mid3A (by omega) (by omega) hpc (by simp only [commitMid3AInstr])
    have r1 : DetRun oracle (submission.image .commit) sa0 1 sa1 1 0 :=
      commit_step1_mid3A (by omega) (by omega) hsa0_pc (by simp only [commitMid3AInstr])
    have r2 : DetRun oracle (submission.image .commit) sa1 1 sa2 1 0 :=
      commit_step1_mid3A (by omega) (by omega) hsa1_pc (by simp only [commitMid3AInstr])
    have r3 : DetRun oracle (submission.image .commit) sa2 1 sa 1 0 :=
      commit_step1_mid3A (by omega) (by omega) hsa2_pc (by simp only [commitMid3AInstr])
    exact ((r0.trans r1).trans r2).trans r3
  have hsa_mem : sa.mem = s0.mem :=
    (((mem_exec_ADDI sa2 _ _ _).trans (mem_exec_SLLI sa1 _ _ _)).trans
      (mem_exec_ADDI sa0 _ _ _)).trans (mem_exec_ADDI s0 _ _ _)
  have hsa_reg_other : ∀ r : Reg, r ≠ .x25 → r ≠ .x27 → sa.getReg r = s0.getReg r := fun r h25 h27 => by
    simp only [sa, sa2, sa1, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x27 r (Ne.symm h27), getReg_setReg_ne' .x25 r (Ne.symm h25)]
  have hsa_x25 : sa.getReg .x25 = BitVec.ofNat 64 (C_DB + 640) := by
    simp only [sa, sa2, sa1, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x27 .x25 (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0), hx2]; decide
  have hsa_x27 : sa.getReg .x27 = mask238Word := by
    simp only [sa, sa2, sa1, sa0, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x27 ≠ .x0), c_getReg_x0]; decide
  -- Induction over `k ≤ 14` levels (`lvlIdx = 6 + k`, building `L_{9+k}`)
  have hind : ∀ k ≤ 14,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa (∑ i ∈ Finset.range k, bin238LevelSteps (6 + i)) sn
          (∑ i ∈ Finset.range k, bin238LevelCycles (6 + i)) (∑ i ∈ Finset.range k, bin238LevelCalls (6 + i)) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k < 14 then 60814 else 61643)) ∧
        sn.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sn.getReg .x5 = 0#64 ∧
        sn.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sn.getReg .x11 = 96#64 ∧
        sn.getReg .x13 = 0#64 ∧ sn.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (6 + k)) ∧
        sn.getReg .x25 = BitVec.ofNat 64 (C_DB + 640) ∧ sn.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        sn.getReg .x27 = mask238Word ∧
        (∀ l, 8 ≤ l → l ≤ k + 8 → ∀ idx < levelSize l,
          readBuffer sn (C_TD + levelBase l + gapOffset idx) 32 = nodeVal c96 msg salts l idx) ∧
        (∀ l, 8 ≤ l → l < 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
        MemPreservedOutside s0 sn (C_TD + levelBase 9) (C_TD + levelBase (k + 9)) := by
    intro k hk; induction k with
    | zero =>
      refine ⟨sa, by simpa only [Finset.sum_range_zero] using DetRun.refl oracle (submission.image .commit) sa,
        by simpa only [show (0 : Nat) < 14 by decide, ite_true] using hsa_pc,
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
          have : l = 8 := by omega
          subst this
          rw [readBuffer_of_mem_eq hsa_mem]
          exact hl8 idx hidx,
        fun l hl1 hl2 q hq j hj => by
          rw [getByte_of_mem_eq hsa_mem]
          exact hzero l hl1 hl2 q hq j hj,
        MemPreservedOutside.of_mem_eq hsa_mem _ _⟩
    | succ k ih =>
      obtain ⟨sn, hrunn, hpcn, hx2n, hx5n, hx9n, hx11n, hx13n, hx24n, hx25n, hx26n, hx27n,
        hdign, hgapn, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 60814) := by
        simpa only [show k < 14 by omega, ite_true] using hpcn
      have hlb_bd := levelBase_bound (k + 9) (by omega)
      obtain ⟨sm, hrun1, hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx24m, hx25m, hx26m, hx27m,
        hdig1, hgap1, hpres1⟩ :=
        commit_bin238_level h768 oracle msg salts (6 + k) (by omega) (by omega) sn hpc_in
          hx2n hx5n hx9n hx11n hx13n hx24n hx25n hx26n hx27n
          (fun off hoff hal => by
            have heq : C_DB + 32 * (6 + k) + off = C_DB + (32 * (6 + k) + off) := by omega
            rw [heq, hpresn.getMem_eq (by omega) (by omega) (by omega)]
            exact hdata (32 * (6 + k) + off) (by omega) (by omega))
          (fun idx hidx => hdign (6 + k + 2) (by omega) (by omega) idx hidx)
          (fun q hq => readBuffer_zero_of_bytes sn _ 32 (fun j hj => by
            simpa only [Nat.add_assoc] using hgapn (6 + k + 2) (by omega) (by omega) q hq j hj))
      have hpc_eq : sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k + 1 < 14 then 60814 else 61643)) := by
        simpa only [show (6 + k + 1 < 20) ↔ (k + 1 < 14) by omega] using hpcm
      have hx24_eq : sm.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (6 + (k + 1))) := by
        simpa only [show 6 + k + 1 = 6 + (k + 1) by omega] using hx24m
      have hlb_k9_k10 : levelBase (k + 9) ≤ levelBase (k + 10) := levelBase_mono _ _ (by omega) (by omega)
      have hlb_9_k9 : levelBase 9 ≤ levelBase (k + 9) := levelBase_mono _ _ (by omega) (by omega)
      have h6k3 : 6 + k + 3 = k + 9 := by omega
      have h6k4 : 6 + k + 4 = k + 10 := by omega
      rw [h6k3, h6k4] at hpres1
      refine ⟨sm, by simpa only [Finset.sum_range_succ] using hrunn.trans hrun1,
        hpc_eq, hx2m, hx5m, hx9m, hx11m, hx13m, hx24_eq, hx25m, hx26m, hx27m, ?_, ?_, ?_⟩
      · intro l hl1 hl2 idx hidx
        by_cases hcur : l = k + 9
        · subst hcur; simpa only [h6k3] using hdig1 idx (by simpa only [h6k3] using hidx)
        · have hlt : l ≤ k + 8 := by omega
          have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
          have hlb_l : levelBase l + levelBytes l ≤ levelBase (k + 9) := by
            have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
            rw [h1]; exact levelBase_mono (l + 1) (k + 9) (by omega) (by omega)
          have hlb_bd_l := levelBase_bound l (by omega)
          rw [hpres1.readBuffer_eq (by omega) (by omega)]
          exact hdign l hl1 hlt idx hidx
      · intro l hl1 hl2 q hq j hj
        by_cases hcur : l = k + 9
        · subst hcur
          have hg1 := hgap1 q (by simpa only [h6k3] using hq) j hj
          rw [h6k3] at hg1
          exact hg1.trans (hgapn (k + 9) (by omega) (by omega) q hq j hj)
        · have hbytes := levelBytes_eq_gap l (by omega) hl2
          have hbd := levelBase_bound l (by omega)
          have hout : C_TD + levelBase l + 96 * q + 64 + j < C_TD + levelBase (k + 9) ∨
              C_TD + levelBase (k + 10) ≤ C_TD + levelBase l + 96 * q + 64 + j := by
            by_cases hlt : l < k + 9
            · left
              have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
              have h2 := levelBase_mono (l + 1) (k + 9) (by omega) (by omega)
              omega
            · right
              have h2 := levelBase_mono (k + 10) l (by omega) (by omega)
              omega
          exact (hpres1 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) hout).trans (hgapn l hl1 hl2 q hq j hj)
      · have hne_k : k + 1 + 9 = k + 10 := by omega
        rw [hne_k]
        exact (hpresn.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (le_refl _))
  obtain ⟨sfin, hrun14, hpc14, hx2f, hx5f, hx9f, hx11f, hx13f, _, _, hx26f, _, hdigf, hgapf, hpresf⟩ :=
    hind 14 (le_refl _)
  have hrun_tot : DetRun oracle (submission.image .commit) s0 176018 sfin 379900 29126 := by
    have h := hsetup.trans hrun14
    rw [phase3B_steps_sum, phase3B_cycles_sum, Nat.zero_add, phase3B_calls_sum] at h
    exact h
  exact ⟨sfin, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpc14,
    hx2f, hx5f, hx9f, hx11f, hx13f, hx26f,
    fun l hl1 hl2 idx hidx => hdigf l (by omega) (by omega) idx hidx,
    hgapf, hpresf⟩

/-- Full Phase 3 (Phase 3U `L3..L4` + Phase 3A `L5..L8` + Phase 3B `L9..L22`, words `59445..61642`):
exact `6,127,482` steps, `19,176,420` cycles, `1,864,134` compression calls. -/
theorem commit_phase3 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 59445))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 640, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl2 : ∀ idx < levelSize 2, readBuffer s0 (C_TD + levelBase 2 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 2 idx)
    (hzero : ∀ l, 2 ≤ l → l < 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 6127482 s1 19176420 1864134 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 61643) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l, 3 ≤ l → l ≤ 22 → ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l, 3 ≤ l → l ≤ 22 → ∀ q < (levelSize l + 1) / 2,
        readBuffer s1 (C_TD + levelBase l + 96 * q + 64) 32 = 0) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 3) (C_TD + levelBase 23) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476096 := rfl
  have htb := treeBytes_eq
  have hlb3_5 : levelBase 3 ≤ levelBase 5 := levelBase_mono 3 5 (by omega) (by omega)
  have hlb5_9 : levelBase 5 ≤ levelBase 9 := levelBase_mono 5 9 (by omega) (by omega)
  have hlb9_23 : levelBase 9 ≤ levelBase 23 := levelBase_mono 9 23 (by omega) (by omega)
  have hlb5_bd := levelBase_bound 5 (by omega)
  have hlb9_bd := levelBase_bound 9 (by omega)
  obtain ⟨sU, hrunU, hpcU, hx2U, hx5U, hx9U, hx11U, hx13U, hx24U, hx26U, hdigU, hgapU, hpresU⟩ :=
    commit_phase3U h768 oracle msg salts s0 hpc hx2 hx5 hx9 hx11 hx13 hx26 hdata hl2 hzero
  obtain ⟨sA, hrunA, hpcA, hx2A, hx5A, hx9A, hx11A, hx13A, hx24A, hx26A, hdigA, hgapA, hpresA⟩ :=
    commit_phase3A h768 oracle msg salts sU hpcU hx2U hx5U hx9U hx11U hx13U hx24U hx26U
      (fun off hoff hal => by
        rw [hpresU.getMem_eq (by omega) (by omega) (by omega)]
        exact hdata off hoff hal)
      (fun idx hidx => hdigU 4 (by omega) (by omega) idx hidx)
      (fun l hl1 hl2 q hq j hj => hgapU l (by omega) hl2 q hq j hj)
  obtain ⟨sB, hrunB, hpcB, hx2B, hx5B, hx9B, hx11B, hx13B, hx26B, hdigB, hgapB, hpresB⟩ :=
    commit_phase3B h768 oracle msg salts sA hpcA hx2A hx5A hx9A hx11A hx13A hx24A hx26A
      (fun off hoff hal => by
        rw [hpresA.getMem_eq (by omega) (by omega) (by omega),
            hpresU.getMem_eq (by omega) (by omega) (by omega)]
        exact hdata off hoff hal)
      (fun idx hidx => hdigA 8 (by omega) (by omega) idx hidx)
      (fun l hl1 hl2 q hq j hj => hgapA l (by omega) hl2 q hq j hj)
  have hpresUA : MemPreservedOutside s0 sA (C_TD + levelBase 3) (C_TD + levelBase 9) :=
    (hpresU.mono (le_refl _) (by omega)).trans (hpresA.mono (by omega) (le_refl _))
  refine ⟨sB, (hrunU.trans hrunA).trans hrunB, hpcB, hx2B, hx5B, hx9B, hx11B, hx13B, hx26B, ?_, ?_,
    (hpresUA.mono (le_refl _) (by omega)).trans (hpresB.mono (by omega) (le_refl _))⟩
  · intro l hl1 hl2 idx hidx
    by_cases hlt5 : l < 5
    · have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
      have hlb_l : levelBase l + levelBytes l ≤ levelBase 5 := by
        have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
        rw [h1]; exact levelBase_mono (l + 1) 5 (by omega) (by omega)
      have hlb_bd_l := levelBase_bound l (by omega)
      rw [hpresB.readBuffer_eq (by omega) (by omega), hpresA.readBuffer_eq (by omega) (by omega)]
      exact hdigU l (by omega) (by omega) idx hidx
    · by_cases hlt9 : l < 9
      · have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
        have hlb_l : levelBase l + levelBytes l ≤ levelBase 9 := by
          have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
          rw [h1]; exact levelBase_mono (l + 1) 9 (by omega) (by omega)
        have hlb_bd_l := levelBase_bound l (by omega)
        rw [hpresB.readBuffer_eq (by omega) (by omega)]
        exact hdigA l (by omega) (by omega) idx hidx
      · exact hdigB l (by omega) hl2 idx hidx
  · intro l hl1 hl2 q hq
    apply readBuffer_zero_of_bytes sB _ 32; intro j hj
    by_cases hlt5 : l < 5
    · have hbytes := levelBytes_eq_gap l (by omega) (by omega)
      have hbd := levelBase_bound l (by omega)
      have hlb_l : levelBase l + levelBytes l ≤ levelBase 5 := by
        have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
        rw [h1]; exact levelBase_mono (l + 1) 5 (by omega) (by omega)
      rw [hpresB (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (Or.inl (by omega)),
          hpresA (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (Or.inl (by omega))]
      exact hgapU l (by omega) (by omega) q hq j hj
    · by_cases hlt9 : l < 9
      · have hbytes := levelBytes_eq_gap l (by omega) (by omega)
        have hbd := levelBase_bound l (by omega)
        have hlb_l : levelBase l + levelBytes l ≤ levelBase 9 := by
          have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
          rw [h1]; exact levelBase_mono (l + 1) 9 (by omega) (by omega)
        rw [hpresB (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (Or.inl (by omega))]
        exact hgapA l (by omega) (by omega) q hq j hj
      · exact hgapB l (by omega) (by omega) q hq j hj

/-! ### 2. Phase 4: Unmasked Root (`L23`), Commitment Copy, and `HALT(0)` (words 61643..61666) -/

private theorem commit_fetch_copy32_phase4 (k : Nat) (hk : k < 4) (st : MachineState) :
    (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (61656 + 2 * k)) →
      fetch (submission.image .commit) st = some (.base (.LD .x6 .x12 (BitVec.ofNat 12 (0 + 8 * k))))) ∧
    (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (61656 + 2 * k + 1)) →
      fetch (submission.image .commit) st = some (.base (.SD .x26 .x6 (BitVec.ofNat 12 (0 + 8 * k))))) := by
  constructor
  · intro hpc'
    have h := commit_fetch_commitTailInstr st (61656 + 2 * k) (by omega) (by omega) hpc'
    interval_cases k <;> simpa only [commitTailInstr] using h
  · intro hpc'
    have h := commit_fetch_commitTailInstr st (61656 + 2 * k + 1) (by omega) (by omega) hpc'
    interval_cases k <;> simpa only [commitTailInstr] using h

/-- Phase 4 pointer setup part 1 (words `61643..61648`: `6` steps): sets `x10 = C_TD + levelBase 22`. -/
private theorem commit_phase4_prep_x10 (oracle : Oracle) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 61643))
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD) :
    ∃ r5,
      DetRun oracle (submission.image .commit) s0 6 r5 6 0 ∧
      r5.pc = BitVec.ofNat 64 (0x1000 + 4 * 61649) ∧
      r5.mem = s0.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r5.getReg r = s0.getReg r) ∧
      r5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 22) := by
  have hlb22 : levelBase 22 = 894785632 := by decide
  let r0 := execInstrBr s0 (.ADDI .x6 .x0 (213#12))
  let r1 := execInstrBr r0 (.SLLI .x6 .x6 (11#6))
  let r2 := execInstrBr r1 (.ADDI .x6 .x6 (683#12))
  let r3 := execInstrBr r2 (.SLLI .x6 .x6 (11#6))
  let r4 := execInstrBr r3 (.ADDI .x6 .x6 (96#12))
  let r5 := execInstrBr r4 (.ADD .x10 .x9 .x6)
  have hr0_pc : r0.pc = BitVec.ofNat 64 (0x1000 + 4 * 61644) := pc_step_idx s0 61643 hpc
  have hr1_pc : r1.pc = BitVec.ofNat 64 (0x1000 + 4 * 61645) := pc_step_idx r0 61644 hr0_pc
  have hr2_pc : r2.pc = BitVec.ofNat 64 (0x1000 + 4 * 61646) := pc_step_idx r1 61645 hr1_pc
  have hr3_pc : r3.pc = BitVec.ofNat 64 (0x1000 + 4 * 61647) := pc_step_idx r2 61646 hr2_pc
  have hr4_pc : r4.pc = BitVec.ofNat 64 (0x1000 + 4 * 61648) := pc_step_idx r3 61647 hr3_pc
  have hr5_pc : r5.pc = BitVec.ofNat 64 (0x1000 + 4 * 61649) := pc_step_idx r4 61648 hr4_pc
  have hrun : DetRun oracle (submission.image .commit) s0 6 r5 6 0 := by
    have p0 : DetRun oracle (submission.image .commit) s0 1 r0 1 0 :=
      commit_step1_tail (by omega) (by omega) hpc (by simp only [commitTailInstr])
    have p1 : DetRun oracle (submission.image .commit) r0 1 r1 1 0 :=
      commit_step1_tail (by omega) (by omega) hr0_pc (by simp only [commitTailInstr])
    have p2 : DetRun oracle (submission.image .commit) r1 1 r2 1 0 :=
      commit_step1_tail (by omega) (by omega) hr1_pc (by simp only [commitTailInstr])
    have p3 : DetRun oracle (submission.image .commit) r2 1 r3 1 0 :=
      commit_step1_tail (by omega) (by omega) hr2_pc (by simp only [commitTailInstr])
    have p4 : DetRun oracle (submission.image .commit) r3 1 r4 1 0 :=
      commit_step1_tail (by omega) (by omega) hr3_pc (by simp only [commitTailInstr])
    have p5 : DetRun oracle (submission.image .commit) r4 1 r5 1 0 :=
      commit_step1_tail (by omega) (by omega) hr4_pc (by simp only [commitTailInstr])
    exact ((((p0.trans p1).trans p2).trans p3).trans p4).trans p5
  have hmem : r5.mem = s0.mem :=
    (((((mem_exec_ADD r4 _ _ _).trans (mem_exec_ADDI r3 _ _ _)).trans (mem_exec_SLLI r2 _ _ _)).trans
      (mem_exec_ADDI r1 _ _ _)).trans (mem_exec_SLLI r0 _ _ _)).trans (mem_exec_ADDI s0 _ _ _)
  have hreg : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r5.getReg r = s0.getReg r := fun r h6r h10r => by
    simp only [r5, r4, r3, r2, r1, r0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x10 r (Ne.symm h10r), getReg_setReg_ne' .x6 r (Ne.symm h6r)]
  have hx10 : r5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 22) := by
    simp only [r5, r4, r3, r2, r1, r0, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq, hx9, hlb22]
    decide
  exact ⟨r5, hrun, hr5_pc, hmem, hreg, hx10⟩

/-- Phase 4 pointer setup part 2 (words `61649..61654`: `6` steps): sets `x12 = C_TD + levelBase 23`. -/
private theorem commit_phase4_prep_x12 (oracle : Oracle) (r5 : MachineState)
    (hpc : r5.pc = BitVec.ofNat 64 (0x1000 + 4 * 61649))
    (hx9 : r5.getReg .x9 = BitVec.ofNat 64 C_TD) :
    ∃ r11,
      DetRun oracle (submission.image .commit) r5 6 r11 6 0 ∧
      r11.pc = BitVec.ofNat 64 (0x1000 + 4 * 61655) ∧
      r11.mem = r5.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x12 → r11.getReg r = r5.getReg r) ∧
      r11.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 23) := by
  have hlb23 : levelBase 23 = 894785728 := by decide
  let r6 := execInstrBr r5 (.ADDI .x6 .x0 (213#12))
  let r7 := execInstrBr r6 (.SLLI .x6 .x6 (11#6))
  let r8 := execInstrBr r7 (.ADDI .x6 .x6 (683#12))
  let r9 := execInstrBr r8 (.SLLI .x6 .x6 (11#6))
  let r10 := execInstrBr r9 (.ADDI .x6 .x6 (192#12))
  let r11 := execInstrBr r10 (.ADD .x12 .x9 .x6)
  have hr6_pc : r6.pc = BitVec.ofNat 64 (0x1000 + 4 * 61650) := pc_step_idx r5 61649 hpc
  have hr7_pc : r7.pc = BitVec.ofNat 64 (0x1000 + 4 * 61651) := pc_step_idx r6 61650 hr6_pc
  have hr8_pc : r8.pc = BitVec.ofNat 64 (0x1000 + 4 * 61652) := pc_step_idx r7 61651 hr7_pc
  have hr9_pc : r9.pc = BitVec.ofNat 64 (0x1000 + 4 * 61653) := pc_step_idx r8 61652 hr8_pc
  have hr10_pc : r10.pc = BitVec.ofNat 64 (0x1000 + 4 * 61654) := pc_step_idx r9 61653 hr9_pc
  have hr11_pc : r11.pc = BitVec.ofNat 64 (0x1000 + 4 * 61655) := pc_step_idx r10 61654 hr10_pc
  have hrun : DetRun oracle (submission.image .commit) r5 6 r11 6 0 := by
    have p6 : DetRun oracle (submission.image .commit) r5 1 r6 1 0 :=
      commit_step1_tail (by omega) (by omega) hpc (by simp only [commitTailInstr])
    have p7 : DetRun oracle (submission.image .commit) r6 1 r7 1 0 :=
      commit_step1_tail (by omega) (by omega) hr6_pc (by simp only [commitTailInstr])
    have p8 : DetRun oracle (submission.image .commit) r7 1 r8 1 0 :=
      commit_step1_tail (by omega) (by omega) hr7_pc (by simp only [commitTailInstr])
    have p9 : DetRun oracle (submission.image .commit) r8 1 r9 1 0 :=
      commit_step1_tail (by omega) (by omega) hr8_pc (by simp only [commitTailInstr])
    have p10 : DetRun oracle (submission.image .commit) r9 1 r10 1 0 :=
      commit_step1_tail (by omega) (by omega) hr9_pc (by simp only [commitTailInstr])
    have p11 : DetRun oracle (submission.image .commit) r10 1 r11 1 0 :=
      commit_step1_tail (by omega) (by omega) hr10_pc (by simp only [commitTailInstr])
    exact ((((p6.trans p7).trans p8).trans p9).trans p10).trans p11
  have hmem : r11.mem = r5.mem :=
    (((((mem_exec_ADD r10 _ _ _).trans (mem_exec_ADDI r9 _ _ _)).trans (mem_exec_SLLI r8 _ _ _)).trans
      (mem_exec_ADDI r7 _ _ _)).trans (mem_exec_SLLI r6 _ _ _)).trans (mem_exec_ADDI r5 _ _ _)
  have hreg : ∀ r : Reg, r ≠ .x6 → r ≠ .x12 → r11.getReg r = r5.getReg r := fun r h6r h12r => by
    simp only [r11, r10, r9, r8, r7, r6, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12r), getReg_setReg_ne' .x6 r (Ne.symm h6r)]
  have hx12 : r11.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 23) := by
    simp only [r11, r10, r9, r8, r7, r6, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq, hx9, hlb23]
    decide
  exact ⟨r11, hrun, hr11_pc, hmem, hreg, hx12⟩

/-- Phase 4 pre-halt (words `61643..61665`: `23` steps, `30` cycles, `1` compression call),
landing at `61666` (`ECALL HALT(0)`) with `rootVal` in both `C_TD + levelBase 23` and `C_CMT`. -/
theorem commit_phase4 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 61643))
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hl22 : ∀ idx < 2, readBuffer s0 (C_TD + levelBase 22 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 22 idx)
    (hgap22 : readBuffer s0 (C_TD + levelBase 22 + 64) 32 = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 23 s1 30 1 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 61666) ∧
      s1.getReg .x5 = 1#64 ∧
      s1.getReg .x10 = 0#64 ∧
      readBuffer s1 C_CMT 32 = rootVal (fun x => oracle.compression (x.cast h768.symm)) msg salts ∧
      readBuffer s1 (C_TD + levelBase 23) 32 =
        rootVal (fun x => oracle.compression (x.cast h768.symm)) msg salts ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < C_CMT ∨ C_CMT + 32 ≤ q) →
        (q < C_TD + levelBase 23 ∨ C_TD + levelBase 23 + 32 ≤ q) →
        s1.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_CMT : C_CMT = 4294971392 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hlb22 : levelBase 22 = 894785632 := by decide
  have hlb23 : levelBase 23 = 894785728 := by decide
  obtain ⟨r5, hprep1, hr5_pc, hr5_mem, hr5_reg_other, hr5_x10⟩ :=
    commit_phase4_prep_x10 oracle s0 hpc hx9
  obtain ⟨r11, hprep2, hr11_pc, hr11_mem5, hr11_reg_r5, hr11_x12⟩ :=
    commit_phase4_prep_x12 oracle r5 hr5_pc ((hr5_reg_other .x9 (by decide) (by decide)).trans hx9)
  have hprep_run : DetRun oracle (submission.image .commit) s0 12 r11 12 0 := hprep1.trans hprep2
  have hr11_mem : r11.mem = s0.mem := hr11_mem5.trans hr5_mem
  have hr11_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r11.getReg r = s0.getReg r :=
    fun r h6r h10r h12r => (hr11_reg_r5 r h6r h12r).trans (hr5_reg_other r h6r h10r)
  have hr11_x10 : r11.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 22) :=
    (hr11_reg_r5 .x10 (by decide) (by decide)).trans hr5_x10
  let root := rootVal c96 msg salts
  let r12 := writeBits r11 (BitVec.ofNat 64 (C_TD + levelBase 23)) root
  have hr11_in : readBuffer r11 (C_TD + levelBase 22) 96 =
      binaryInput (nodeVal c96 msg salts 22 0) (nodeVal c96 msg salts 22 1) := by
    rw [readBuffer_of_mem_eq hr11_mem, readBuffer_binary_of_zero_gap s0 _ hgap22]
    have h0 := hl22 0 (by omega); have h1 := hl22 1 (by omega)
    rw [show gapOffset 0 = 0 from rfl, Nat.add_zero] at h0
    rw [show gapOffset 1 = 32 from rfl] at h1
    rw [h0, h1]
  have hroot_eq : oracle.compression ((readBuffer r11 (C_TD + levelBase 22) 96).cast h768.symm) = root := by
    rw [hr11_in]
    exact nodeVal_root_eq c96 msg salts
  have hf61655 : fetch (submission.image .commit) r11 = some (.base .ECALL) := by
    have h := commit_fetch_commitTailInstr r11 61655 (by omega) (by omega) hr11_pc
    simp only [commitTailInstr] at h
    exact h
  have hcall_run : DetRun oracle (submission.image .commit) r11 1 r12 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := r11) hf61655
      ((hr11_reg_other .x5 (by decide) (by decide) (by decide)).trans hx5)
      ((hr11_reg_other .x11 (by decide) (by decide) (by decide)).trans hx11)
      ((hr11_reg_other .x13 (by decide) (by decide) (by decide)).trans hx13)
      (C_TD + levelBase 22) (C_TD + levelBase 23) hr11_x10 hr11_x12
      (by omega) (by omega) (by omega) (by omega) root hroot_eq
  have hr12_pc : r12.pc = BitVec.ofNat 64 (0x1000 + 4 * 61656) := pc_step_idx r11 61655 hr11_pc
  obtain ⟨rc, hcopy_run, hrc_pc, _, hrc_dig, hrc_pres⟩ :=
    commit_copy32 oracle r12 61656 .x12 .x26 (C_TD + levelBase 23) C_CMT 0 0
      (by decide) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hr12_pc
      ((writeBits_register r11 _ root .x12).trans hr11_x12)
      ((writeBits_register r11 _ root .x26).trans ((hr11_reg_other .x26 (by decide) (by decide) (by decide)).trans hx26))
      commit_fetch_copy32_phase4
  let s1 := execInstrBr rc (.ADDI .x5 .x0 (1#12))
  let s2 := execInstrBr s1 (.ADDI .x10 .x0 (0#12))
  have hrc_pc' : rc.pc = BitVec.ofNat 64 (0x1000 + 4 * 61664) := hrc_pc
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 61665) := pc_step_idx rc 61664 hrc_pc'
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 61666) := pc_step_idx s1 61665 hs1_pc
  have hs1_run : DetRun oracle (submission.image .commit) rc 1 s1 1 0 :=
    commit_step1_tail (by omega) (by omega) hrc_pc' (by simp only [commitTailInstr])
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
    simpa only [Nat.add_zero] using hrc_dig.trans (writeBits_readBuffer_digest r11 (C_TD + levelBase 23) root)
  · rw [readBuffer_of_mem_eq hs2_mem, hrc_pres.readBuffer_eq (by omega) (by omega)]
    exact writeBits_readBuffer_digest r11 (C_TD + levelBase 23) root
  · intro q hq houtCmt houtRoot
    have h1 := getByte_of_mem_eq hs2_mem (BitVec.ofNat 64 q)
    have h2 := hrc_pres q hq (by simpa only [Nat.add_zero] using houtCmt)
    have h3 := memPreserved_writeBits r11 (C_TD + levelBase 23) root (by omega) q hq houtRoot
    have h4 := getByte_of_mem_eq hr11_mem (BitVec.ofNat 64 q)
    exact ((h1.trans h2).trans h3).trans h4

/-! ### 3. Top-Level Commit Exactness, Oracle Refinement, and Termination -/

private theorem commit_det_phases (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (s0 : MachineState) (rand : Fin (LENGTH / 2) → PairRand)
    (hinv :
      s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 4125) ∧
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
      oracle.run (execute (submission.image .commit) (submission.steps .commit - 16785434) s0 true) =
        pure (⟨.success, sfin, 764868916, 76429539⟩, 76429539) ∧
      readBuffer sfin C_CMT 32 =
        rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) ∧
      CommittedTrapdoor h768 oracle.compression message (pairSalts rand)
        (readBuffer sfin C_TD submission.sizes.trapdoor) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_CMT : C_CMT = 4294971392 := rfl
  have hC_ROW : C_ROW = 5189757184 := rfl
  have hC_DB : C_DB = 68719476096 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hsteps_ge : 16785434 + 229862143 ≤ submission.steps .commit := by decide
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
  obtain ⟨s2A, hrun2A, hpc2A, hx2_2A, hx5_2A, hx9_2A, hx11_2A, hx13_2A, hx26_2A, hl1_2A, hpres2A⟩ :=
    commit_phase2A h768 oracle message salts s1 hpc1 hx2_1 hx5_1 hx9_1 hx11_1 hx13_1 hx26_1 hl0_1
  obtain ⟨s2, hrun2B, hpc2, hx2_2, hx5_2, hx9_2, hx11_2, hx13_2, hx26_2, hl2_2, hgap2_2, hpres2B⟩ :=
    commit_phase2B h768 oracle message salts s2A hpc2A hx2_2A hx5_2A hx9_2A hx11_2A hx13_2A hx26_2A hl1_2A
  have hls0 := levelSize_0
  have hls1 := levelSize_1
  have hlb1 : levelBase 1 = 536870912 := by decide
  have hlb2 : levelBase 2 = 715827904 := by decide
  have hlb3 : levelBase 3 = 805306432 := by decide
  have hlb23 : levelBase 23 = 894785728 := by decide
  have htb := treeBytes_eq
  have hro := rowOff_eq
  have htd := trapdoorBytes_eq
  have hdata2 : ∀ off < 640, off % 8 = 0 →
      s2.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit message).getMem (BitVec.ofNat 64 (C_DB + off)) := by
    intro off hoff hal
    rw [hpres2B.getMem_eq (by omega) (by omega) (by omega),
      hpres2A.getMem_eq (by omega) (by omega) (by omega),
      ← readBuffer_word s1 (C_DB + off) (by omega),
      ← readBuffer_word (submission.initialState .commit message) (C_DB + off) (by omega)]
    apply readBuffer_congr; intro j hj
    exact (hpres1 (C_DB + off + j) (by omega) (by omega)).trans
      (hpres0 (C_DB + off + j) (by omega) (fun _ _ => by omega))
  have hzero2 : ∀ l, 2 ≤ l → l < 23 → ∀ q < (levelSize l + 1) / 2, ∀ j < 32,
      s2.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0 := by
    intro l hl1 hl2 q hq j hj
    have hbytes := levelBytes_eq_gap l hl1 hl2
    have hbd := levelBase_bound l (by omega)
    have hinit0 : (submission.initialState .commit message).getByte
        (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0 :=
      commit_initial_zero_byte message _ (by omega)
    have hp0 := hpres0 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (fun _ _ => by omega)
    have hlb_ge2 : levelBase 2 ≤ levelBase l := levelBase_mono 2 l hl1 (by omega)
    have hp1 := hpres1 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (by omega)
    have hp2A := hpres2A (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (by omega)
    by_cases hl2_eq : l = 2
    · subst hl2_eq
      exact (((hgap2_2 q hq j hj).trans hp2A).trans hp1).trans (hp0.trans hinit0)
    · have hlb_ge3 : levelBase 3 ≤ levelBase l := levelBase_mono 3 l (by omega) (by omega)
      have hp2B := hpres2B (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (by omega)
      exact (((hp2B.trans hp2A).trans hp1).trans hp0).trans hinit0
  obtain ⟨s3, hrun3, hpc3, _, hx5_3, hx9_3, hx11_3, hx13_3, hx26_3, hbin3, hgap3, hpres3⟩ :=
    commit_phase3 h768 oracle message salts s2 hpc2 hx2_2 hx5_2 hx9_2 hx11_2 hx13_2 hx26_2 hdata2 hl2_2 hzero2
  obtain ⟨s4, hrun4, hpc4, hx5_4, hx10_4, hcmt4, hroot4, hpres4⟩ :=
    commit_phase4 h768 oracle message salts s3 hpc3 hx5_3 hx9_3 hx11_3 hx13_3 hx26_3
      (fun idx hidx => hbin3 22 (by omega) (by omega) idx (by rw [levelSize_22]; exact hidx))
      (by simpa only [Nat.mul_zero, Nat.add_zero] using hgap3 22 (by omega) (by omega) 0 (by rw [levelSize_22]; omega))
  have hrun14 : DetRun oracle (submission.image .commit) s0 229862142 s4 764868915 76429539 :=
    (((hrun1.trans hrun2A).trans hrun2B).trans hrun3).trans hrun4
  have hf61666 : fetch (submission.image .commit) s4 = some (.base .ECALL) := by
    have h := commit_fetch_commitTailInstr s4 61666 (by omega) (by omega) hpc4
    simp only [commitTailInstr] at h
    exact h
  have hfin := hrun14.finish hf61666
    hx5_4 hx10_4 (submission.steps .commit - 16785434) (by omega)
  refine ⟨s4, hfin, ?_, ?_⟩
  · dsimp only [salts] at hcmt4; exact hcmt4
  · have htd_sz : submission.sizes.trapdoor = trapdoorBytes := trapdoorBytes_eq.symm
    refine ⟨?_, ?_, ?_⟩
    · intro l hl idx hidx
      have hoff_bd : levelBase l + nodeOffset l idx + 32 ≤ submission.sizes.trapdoor := by
        rw [htd_sz]
        have hbd := levelBase_bound l hl
        unfold nodeOffset
        by_cases hlt2 : l < 2
        · simp only [hlt2, ite_true]
          have hlb_bytes : levelBytes l = levelSize l * 32 := by unfold levelBytes; simp only [hlt2, ite_true]
          omega
        · simp only [hlt2, ite_false]
          by_cases h23 : l = 23
          · subst h23; rw [levelSize_23] at hidx
            have : idx = 0 := by omega
            subst this; unfold gapOffset; rw [hlb23, htd]; decide
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
          unfold levelBase nodeOffset; simp only [show (0 : Nat) < 2 by decide, ite_true]; omega
        rw [hnoff]
        have hp4 : readBuffer s4 (C_TD + 32 * idx) 32 = readBuffer s3 (C_TD + 32 * idx) 32 :=
          readBuffer_congr _ _ _ _ (fun j hj => hpres4 (C_TD + 32 * idx + j) (by omega) (by omega) (by omega))
        rw [hp4, hpres3.readBuffer_eq (by omega) (by omega),
            hpres2B.readBuffer_eq (by omega) (by omega), hpres2A.readBuffer_eq (by omega) (by omega)]
        exact hl0_1 idx hidx
      · by_cases h1 : l = 1
        · subst h1
          have hnoff : nodeOffset 1 idx = 32 * idx := by
            unfold nodeOffset; simp only [show (1 : Nat) < 2 by decide, ite_true]
          rw [hnoff, ← Nat.add_assoc]
          have hp4 : readBuffer s4 (C_TD + levelBase 1 + 32 * idx) 32 =
              readBuffer s3 (C_TD + levelBase 1 + 32 * idx) 32 :=
            readBuffer_congr _ _ _ _ (fun j hj => hpres4 (C_TD + levelBase 1 + 32 * idx + j)
              (by omega) (by omega) (by omega))
          rw [hp4, hpres3.readBuffer_eq (by omega) (by omega), hpres2B.readBuffer_eq (by omega) (by omega)]
          exact hl1_2A idx hidx
        · by_cases h2 : l = 2
          · subst h2
            have hnoff : nodeOffset 2 idx = gapOffset idx := rfl
            rw [hnoff, ← Nat.add_assoc]
            have hgo := gapOffset_lt_levelBytes 2 idx (by omega) (by omega) hidx
            have hlb2_bytes : levelBase 2 + levelBytes 2 = levelBase 3 := rfl
            have hp4 : readBuffer s4 (C_TD + levelBase 2 + gapOffset idx) 32 =
                readBuffer s3 (C_TD + levelBase 2 + gapOffset idx) 32 :=
              readBuffer_congr _ _ _ _ (fun j hj => hpres4 (C_TD + levelBase 2 + gapOffset idx + j)
                (by omega) (by omega) (by omega))
            rw [hp4, hpres3.readBuffer_eq (by omega) (by omega)]
            exact hl2_2 idx hidx
          · by_cases h23 : l = 23
            · subst h23
              rw [levelSize_23] at hidx
              have : idx = 0 := by omega
              subst this
              have hnoff : nodeOffset 23 0 = 0 := by decide
              rw [hnoff, Nat.add_zero]
              dsimp only [salts] at hroot4
              have hrt23 : rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) =
                  nodeVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) 23 0 := rfl
              exact hroot4.trans hrt23
            · have hnoff : nodeOffset l idx = gapOffset idx := by
                unfold nodeOffset; simp only [show ¬ (l < 2) by omega, ite_false]
              rw [hnoff, ← Nat.add_assoc]
              have hgo := gapOffset_lt_levelBytes l idx (by omega) (by omega) hidx
              have hlb_l : levelBase l + levelBytes l ≤ levelBase 23 := by
                have h1' : levelBase l + levelBytes l = levelBase (l + 1) := rfl
                rw [h1']; exact levelBase_mono (l + 1) 23 (by omega) (le_refl _)
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
      have hlb_l : levelBase l + levelBytes l ≤ levelBase 23 := by
        have h1' : levelBase l + levelBytes l = levelBase (l + 1) := rfl
        rw [h1']; exact levelBase_mono (l + 1) 23 (by omega) (le_refl _)
      have haddr : C_TD + (levelBase l + 96 * q + 64) = C_TD + levelBase l + 96 * q + 64 := by omega
      rw [haddr]
      have hp4 : readBuffer s4 (C_TD + levelBase l + 96 * q + 64) 32 =
          readBuffer s3 (C_TD + levelBase l + 96 * q + 64) 32 :=
        readBuffer_congr _ _ _ _ (fun j hj => hpres4 (C_TD + levelBase l + 96 * q + 64 + j)
          (by omega) (by omega) (by omega))
      rw [hp4]
      by_cases h2 : l = 2
      · subst h2
        have hlb2_bytes : levelBase 2 + levelBytes 2 = levelBase 3 := rfl
        rw [hpres3.readBuffer_eq (by omega) (by omega)]
        exact readBuffer_zero_of_bytes s2 _ 32 (fun j hj => by
          simpa only [Nat.add_assoc] using hzero2 2 (by omega) (by omega) q hq j hj)
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
      rw [hp4, hpres3.readBuffer_eq (by omega) (by omega),
          hpres2B.readBuffer_eq (by omega) (by omega), hpres2A.readBuffer_eq (by omega) (by omega)]
      exact hsalt1 i

private theorem readBuffer_digest_eq (s : MachineState) (a : Nat) (v : Commitment)
    (h : readBuffer s a 32 = v) : readBuffer s a DIGEST_BYTES = v := by
  have hgen : ∀ (n : Nat) (hn : n = 32) (w : BitVec (8 * n)),
      readBuffer s a 32 = w.cast (by rw [hn]) → readBuffer s a n = w := by
    intro n hn; subst hn; intro w hw; exact hw
  exact hgen DIGEST_BYTES rfl v h

private theorem commit_run_eq_helper (oracle : Oracle) (message : Message)
    (post0 finalState : (Fin (LENGTH / 2) → PairRand) → MachineState)
    (hrun0 : oracle.run (execute (submission.image .commit) (16785434 + (submission.steps .commit - 16785434))
        (submission.initialState .commit message) true) =ᵈ
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        (fun p : Execution × Nat => (p.1.charge 58728474 0, p.2)) <$>
          oracle.run (execute (submission.image .commit) (submission.steps .commit - 16785434) (post0 rand) true)))
    (hs : ∀ rand, oracle.run (execute (submission.image .commit) (submission.steps .commit - 16785434) (post0 rand) true) =
      pure (⟨.success, finalState rand, 764868916, 76429539⟩, 76429539)) :
    oracle.run (submission.run .commit message) =ᵈ
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        pure (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 823597390, oracleCalls := 76429539 } : Execution), 76429539)) := by
  have hsteps_commit : submission.steps .commit = 16785434 + (submission.steps .commit - 16785434) := by
    have hge : 16785434 ≤ submission.steps .commit := by decide
    omega
  rw [submission_run_commit submission message, hsteps_commit]
  refine hrun0.trans ?_
  apply EvalDistEq.bind_right; intro rand
  rw [hs rand, map_pure]
  have heq : (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 764868916, oracleCalls := 76429539 } : Execution).charge 58728474 0, 76429539) =
      (({ exit := Riscv.Exit.success, state := finalState rand,
          cycles := 823597390, oracleCalls := 76429539 } : Execution), 76429539) := by
    unfold Execution.charge; dsimp only
  rw [heq]

private theorem commit_read_spec_helper (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (sfin : MachineState) (salts : Index → Salt192)
    (hcmt : readBuffer sfin C_CMT 32 = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts)
    (htd : CommittedTrapdoor h768 oracle.compression message salts (readBuffer sfin C_TD submission.sizes.trapdoor)) :
    let (cmt, td) := submission.readCommit ⟨.success, sfin, 823597390, 76429539⟩
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
always halts with `.success`, exactly `823,597,390` cycles and `76,429,539` compression calls,
writing `rootVal` to the commitment buffer and a valid `CommittedTrapdoor` to the trapdoor buffer. -/
theorem commit_run_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    ∃ finalState : (Fin (LENGTH / 2) → PairRand) → MachineState,
      oracle.run (submission.run .commit message) =ᵈ
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (({ exit := Riscv.Exit.success, state := finalState rand,
                   cycles := 823597390, oracleCalls := 76429539 } : Execution), 76429539)) ∧
      ∀ rand,
        let salts := pairSalts rand
        let (cmt, td) := submission.readCommit
          ⟨Riscv.Exit.success, finalState rand, 823597390, 76429539⟩
        cmt = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts ∧
        CommittedTrapdoor h768 oracle.compression message salts td := by
  obtain ⟨post0, hrun0, hinv0⟩ := commit_phase0 oracle message (submission.steps .commit - 16785434)
  have hdet : ∀ rand : Fin (LENGTH / 2) → PairRand,
      ∃ sfin : MachineState,
        oracle.run (execute (submission.image .commit) (submission.steps .commit - 16785434) (post0 rand) true) =
          pure (⟨.success, sfin, 764868916, 76429539⟩, 76429539) ∧
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
  refine ⟨fun rand => (submission.readCommit ⟨.success, finalState rand, 823597390, 76429539⟩).2, ?_, ?_⟩
  · let f : Execution × Nat → Commitment × BitVec (8 * submission.sizes.trapdoor) :=
      fun p => submission.readCommit p.1
    have hmap : (fixedOracleRun oracle (submission.scheme.commit message) :
          ProbComp (Commitment × BitVec (8 * submission.sizes.trapdoor))) =
        f <$> oracle.run (submission.run .commit message) := by
      simp only [fixedOracleRun, Submission.scheme, oracle_run_map, Functor.map_map, f]
    have hstep : f <$> (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (({ exit := Riscv.Exit.success, state := finalState rand,
                   cycles := 823597390, oracleCalls := 76429539 } : Execution), 76429539)) =
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand),
                (submission.readCommit ⟨.success, finalState rand, 823597390, 76429539⟩).2)) := by
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
    rw [prEvent_pure, prEvent_pure, if_pos (h a), if_pos trivial]
  rw [h1]
  have h2 : (fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit)) =
      (($ᵗ α) >>= fun _ => (pure True : ProbComp Prop)) := by
    simp only [map_bind, map_pure]
  change prEvent ((fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit))) = 1
  rw [h2, prEvent_def, OracleComp.evalDist_bind_const]
  change prEvent (pure True : ProbComp Prop) = 1
  rw [prEvent_pure_prop, if_pos trivial]

/-- `submission.run .commit` always terminates with probability 1 for every oracle and message. -/
theorem commit_termination (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    Pr{let result ← oracle.run (submission.run .commit message)}[
      result.1.exit ≠ Riscv.Exit.unfinished] = 1 := by
  obtain ⟨finalState, hrun, _⟩ := commit_run_exact h768 oracle message
  rw [hrun.prEvent_eq _]
  exact commit_prEvent_uniform_bind_pure_eq_one
    (fun rand => ((⟨.success, finalState rand, 823597390, 76429539⟩ : Execution), 76429539))
    (fun result => result.1.exit ≠ Riscv.Exit.unfinished)
    (fun _ => by dsimp only; decide)

end CommitGolfCandidate
