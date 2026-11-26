import CommitGolfCandidate.MoonCommitBin
import CommitGolfCandidate.CompressionSampling

/-! Exact RV64IM execution proofs for Phases 3Z, 3A, 3B, and 4 of the pure-binary `commit` image,
plus full-commit composition proving `commit_run_exact`, `commit_oracle_run_exact`, and
`commit_termination`:
- Phase 3Z: 1-level 256-bit unmasked binary driver (`L0 -> L1`, words `3366..3777`)
- Phase 3A: 3-level 240-bit masked binary driver (`L1..L3 -> L2..L4`, words `3778..4318`)
- Phase 3B: 19-level 238-bit masked binary driver (`L4..L22 -> L5..L23`, words `4319..5122`)
- Phase 4: unmasked 256-bit `L24` root + copy to commitment + `HALT(0)` (words `5123..5142`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Phase 3: Split 256-Bit (`L1`) + 240-Bit (`L2..L4`) + 238-Bit (`L5..L23`) Binary Drivers -/

private theorem phase3Z_steps_sum :
    2 + ∑ i ∈ Finset.range 1, bin256LevelSteps i = 25231379 := by decide

private theorem phase3Z_cycles_sum :
    2 + ∑ i ∈ Finset.range 1, bin256LevelCycles i = 83951635 := by decide

private theorem phase3Z_calls_sum :
    ∑ i ∈ Finset.range 1, bin256LevelCalls i = 8388608 := by decide

private theorem phase3A_steps_sum :
    1 + ∑ k ∈ Finset.range 3, binLevelSteps (1 + k) = 29417524 := by decide

private theorem phase3A_cycles_sum :
    1 + ∑ k ∈ Finset.range 3, binLevelCycles (1 + k) = 80797748 := by decide

private theorem phase3A_calls_sum :
    ∑ k ∈ Finset.range 3, binLevelCalls (1 + k) = 7340032 := by decide

private theorem phase3B_steps_sum :
    4 + ∑ k ∈ Finset.range 19, bin238LevelSteps (4 + k) = 6300064 := by decide

private theorem phase3B_cycles_sum :
    4 + ∑ k ∈ Finset.range 19, bin238LevelCycles (4 + k) = 13640082 := by decide

private theorem phase3B_calls_sum :
    ∑ k ∈ Finset.range 19, bin238LevelCalls (4 + k) = 1048574 := by decide

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

/-- Phase 3Z (`L0 -> L1`, 256-bit unmasked, words `3366..3777`):
`25,231,379` steps, `83,951,635` cycles, `8,388,608` calls. -/
private theorem commit_phase3Z (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 3366))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 736, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl0 : ∀ idx < levelSize 0, readBuffer s0 (C_TD + levelBase 0 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 0 idx)
    (hzero : ∀ l < 24, ∀ q < levelSize l / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 25231379 s1 83951635 8388608 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 3778) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x24 = BitVec.ofNat 64 (C_DB + 32) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l ≤ 1, ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l < 24, ∀ q < levelSize l / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 1) (C_TD + levelBase 2) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have htb := treeBytes_eq
  let sa0 := execInstrBr s0 (.ADDI .x24 .x2 (0#12))
  let sa := execInstrBr sa0 (.ADDI .x25 .x2 (32#12))
  have hsa0_pc : sa0.pc = BitVec.ofNat 64 (0x1000 + 4 * 3367) := pc_step_idx s0 3366 hpc
  have hsa_pc : sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 3368) := pc_step_idx sa0 3367 hsa0_pc
  have hsetup : DetRun oracle (submission.image .commit) s0 2 sa 2 0 := by
    have r0 : DetRun oracle (submission.image .commit) s0 1 sa0 1 0 :=
      commit_step1_mid3 (by omega) (by omega) hpc (by simp only [commitMid3Instr])
    have r1 : DetRun oracle (submission.image .commit) sa0 1 sa 1 0 :=
      commit_step1_mid3 (by omega) (by omega) hsa0_pc (by simp only [commitMid3Instr])
    exact r0.trans r1
  have hsa_mem : sa.mem = s0.mem := (mem_exec_ADDI sa0 _ _ _).trans (mem_exec_ADDI s0 _ _ _)
  have hsa_reg_other : ∀ r : Reg, r ≠ .x24 → r ≠ .x25 → sa.getReg r = s0.getReg r := fun r h24 h25 => by
    simp only [sa, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x25 r (Ne.symm h25), getReg_setReg_ne' .x24 r (Ne.symm h24)]
  have hind : ∀ n ≤ 1,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa (∑ i ∈ Finset.range n, bin256LevelSteps i) sn
          (∑ i ∈ Finset.range n, bin256LevelCycles i) (∑ i ∈ Finset.range n, bin256LevelCalls i) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 1 then 3368 else 3778)) ∧
        sn.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sn.getReg .x5 = 0#64 ∧
        sn.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sn.getReg .x11 = 96#64 ∧
        sn.getReg .x13 = 0#64 ∧ sn.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * n) ∧
        sn.getReg .x25 = BitVec.ofNat 64 (C_DB + 32) ∧ sn.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        (∀ l ≤ n, ∀ idx < levelSize l,
          readBuffer sn (C_TD + levelBase l + gapOffset idx) 32 = nodeVal c96 msg salts l idx) ∧
        (∀ l < 24, ∀ q < levelSize l / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
        MemPreservedOutside s0 sn (C_TD + levelBase 1) (C_TD + levelBase (n + 1)) := by
    intro n hn; induction n with
    | zero =>
      refine ⟨sa, by simpa only [Finset.sum_range_zero] using DetRun.refl oracle (submission.image .commit) sa,
        by simpa only [show (0 : Nat) < 1 by decide, ite_true] using hsa_pc,
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
        fun l hl_hi idx hidx => by
          have : l = 0 := by omega
          subst this
          rw [readBuffer_of_mem_eq hsa_mem]
          exact hl0 idx hidx,
        fun l hl q hq j hj => by
          rw [getByte_of_mem_eq hsa_mem]
          exact hzero l hl q hq j hj,
        MemPreservedOutside.of_mem_eq hsa_mem _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hx2n, hx5n, hx9n, hx11n, hx13n, hx24n, hx25n, hx26n, hdign, hgapn, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 3368) := by
        simpa only [show n < 1 by omega, ite_true] using hpcn
      have hlb_bd := levelBase_bound (n + 1) (by omega)
      obtain ⟨sm, hrun1, hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx24m, hx25m, hx26m, hdig1, hgap1, hpres1⟩ :=
        commit_bin256_level h768 oracle msg salts n (by omega) sn hpc_in hx2n hx5n hx9n hx11n hx13n hx24n hx25n hx26n
          (fun off hoff hal => by
            have heq : C_DB + 32 * n + off = C_DB + (32 * n + off) := by omega
            rw [heq, hpresn.getMem_eq (by omega) (by omega) (by omega)]
            exact hdata (32 * n + off) (by omega) (by omega))
          (fun idx hidx => hdign n (by omega) idx hidx)
          (fun q hq => readBuffer_zero_of_bytes sn _ 32 (fun j hj => by
            simpa only [Nat.add_assoc] using hgapn n (by omega) q hq j hj))
      have hlb_n1_n2 : levelBase (n + 1) ≤ levelBase (n + 2) := levelBase_mono _ _ (by omega) (by omega)
      have hlb_1_n1 : levelBase 1 ≤ levelBase (n + 1) := levelBase_mono _ _ (by omega) (by omega)
      refine ⟨sm, by simpa only [Finset.sum_range_succ] using hrunn.trans hrun1,
        hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx24m, hx25m, hx26m, ?_, ?_, ?_⟩
      · intro l hl2 idx hidx
        by_cases hcur : l = n + 1
        · subst hcur; exact hdig1 idx hidx
        · have hlt : l ≤ n := by omega
          have hgo := gapOffset_lt_levelBytes l idx (by omega) hidx
          have hlb_l : levelBase l + levelBytes l ≤ levelBase (n + 1) := by
            have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
            rw [h1]; exact levelBase_mono (l + 1) (n + 1) (by omega) (by omega)
          have hlb_bd_l := levelBase_bound l (by omega)
          rw [hpres1.readBuffer_eq (by omega) (by omega)]
          exact hdign l hlt idx hidx
      · intro l hl2 q hq j hj
        by_cases hcur : l = n + 1
        · subst hcur
          exact (hgap1 q hq j hj).trans (hgapn (n + 1) (by omega) q hq j hj)
        · have hbytes := levelBytes_eq_gap l hl2
          have hbd := levelBase_bound l (by omega)
          have hout : C_TD + levelBase l + 96 * q + 64 + j < C_TD + levelBase (n + 1) ∨
              C_TD + levelBase (n + 2) ≤ C_TD + levelBase l + 96 * q + 64 + j := by
            by_cases hlt : l < n + 1
            · left
              have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
              have h2 := levelBase_mono (l + 1) (n + 1) (by omega) (by omega)
              omega
            · right
              have h2 := levelBase_mono (n + 2) l (by omega) (by omega)
              omega
          exact (hpres1 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) hout).trans (hgapn l hl2 q hq j hj)
      · have hne_n : n + 1 + 1 = n + 2 := by omega
        rw [hne_n]
        exact (hpresn.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (le_refl _))
  obtain ⟨sfin, hrun1, hpc1, hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, _, hx26f, hdigf, hgapf, hpresf⟩ :=
    hind 1 (le_refl _)
  have hrun_tot : DetRun oracle (submission.image .commit) s0 25231379 sfin 83951635 8388608 := by
    have h := hsetup.trans hrun1
    rw [phase3Z_steps_sum, phase3Z_cycles_sum, Nat.zero_add, phase3Z_calls_sum] at h
    exact h
  exact ⟨sfin, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpc1,
    hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, hx26f, hdigf, hgapf, hpresf⟩

/-- Phase 3A (`L1..L3 -> L2..L4`, 240-bit masked, words `3778..4318`):
`29,417,524` steps, `80,797,748` cycles, `7,340,032` calls. -/
private theorem commit_phase3A (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 3778))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 32))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 736, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl1 : ∀ idx < levelSize 1, readBuffer s0 (C_TD + levelBase 1 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 idx)
    (hzero : ∀ l, 1 ≤ l → l < 24 → ∀ q < levelSize l / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 29417524 s1 80797748 7340032 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 4319) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x24 = BitVec.ofNat 64 (C_DB + 128) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l, 2 ≤ l → l ≤ 4 → ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l, 1 ≤ l → l < 24 → ∀ q < levelSize l / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 2) (C_TD + levelBase 5) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have htb := treeBytes_eq
  -- Setup word 3778: ADDI x25, x2, 128
  let sa := execInstrBr s0 (.ADDI .x25 .x2 (128#12))
  have hsa_pc : sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 3779) := pc_step_idx s0 3778 hpc
  have hsetup : DetRun oracle (submission.image .commit) s0 1 sa 1 0 :=
    commit_step1_mid4 (by omega) (by omega) hpc (by simp only [commitMid4Instr])
  have hsa_mem : sa.mem = s0.mem := mem_exec_ADDI s0 _ _ _
  have hsa_reg_other : ∀ r : Reg, r ≠ .x25 → sa.getReg r = s0.getReg r := fun r h25 => by
    simp only [sa, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x25 r (Ne.symm h25)]
  have hsa_x25 : sa.getReg .x25 = BitVec.ofNat 64 (C_DB + 128) := by
    simp only [sa, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0), hx2]; decide
  have hind : ∀ k ≤ 3,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa (∑ i ∈ Finset.range k, binLevelSteps (1 + i)) sn
          (∑ i ∈ Finset.range k, binLevelCycles (1 + i)) (∑ i ∈ Finset.range k, binLevelCalls (1 + i)) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k < 3 then 3779 else 4319)) ∧
        sn.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sn.getReg .x5 = 0#64 ∧
        sn.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sn.getReg .x11 = 96#64 ∧
        sn.getReg .x13 = 0#64 ∧ sn.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (1 + k)) ∧
        sn.getReg .x25 = BitVec.ofNat 64 (C_DB + 128) ∧ sn.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        (∀ l, 1 ≤ l → l ≤ k + 1 → ∀ idx < levelSize l,
          readBuffer sn (C_TD + levelBase l + gapOffset idx) 32 = nodeVal c96 msg salts l idx) ∧
        (∀ l, 1 ≤ l → l < 24 → ∀ q < levelSize l / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
        MemPreservedOutside s0 sn (C_TD + levelBase 2) (C_TD + levelBase (k + 2)) := by
    intro k hk; induction k with
    | zero =>
      refine ⟨sa, by simpa only [Finset.sum_range_zero] using DetRun.refl oracle (submission.image .commit) sa,
        by simpa only [show (0 : Nat) < 3 by decide, ite_true] using hsa_pc,
        (hsa_reg_other .x2 (by decide)).trans hx2,
        (hsa_reg_other .x5 (by decide)).trans hx5,
        (hsa_reg_other .x9 (by decide)).trans hx9,
        (hsa_reg_other .x11 (by decide)).trans hx11,
        (hsa_reg_other .x13 (by decide)).trans hx13,
        (hsa_reg_other .x24 (by decide)).trans hx24,
        hsa_x25,
        (hsa_reg_other .x26 (by decide)).trans hx26,
        fun l hl_lo hl_hi idx hidx => by
          have : l = 1 := by omega
          subst this
          rw [readBuffer_of_mem_eq hsa_mem]
          exact hl1 idx hidx,
        fun l hl1 hl2 q hq j hj => by
          rw [getByte_of_mem_eq hsa_mem]
          exact hzero l hl1 hl2 q hq j hj,
        MemPreservedOutside.of_mem_eq hsa_mem _ _⟩
    | succ k ih =>
      obtain ⟨sn, hrunn, hpcn, hx2n, hx5n, hx9n, hx11n, hx13n, hx24n, hx25n, hx26n, hdign, hgapn, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 3779) := by
        simpa only [show k < 3 by omega, ite_true] using hpcn
      have hlb_bd := levelBase_bound (k + 2) (by omega)
      obtain ⟨sm, hrun1, hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx24m, hx25m, hx26m, hdig1, hgap1, hpres1⟩ :=
        commit_bin_level h768 oracle msg salts (1 + k) (by omega) (by omega) sn hpc_in
          hx2n hx5n hx9n hx11n hx13n hx24n hx25n hx26n
          (fun off hoff hal => by
            have heq : C_DB + 32 * (1 + k) + off = C_DB + (32 * (1 + k) + off) := by omega
            rw [heq, hpresn.getMem_eq (by omega) (by omega) (by omega)]
            exact hdata (32 * (1 + k) + off) (by omega) (by omega))
          (fun idx hidx => hdign (1 + k) (by omega) (by omega) idx hidx)
          (fun q hq => readBuffer_zero_of_bytes sn _ 32 (fun j hj => by
            simpa only [Nat.add_assoc] using hgapn (1 + k) (by omega) (by omega) q hq j hj))
      have hpc_eq : sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k + 1 < 3 then 3779 else 4319)) := by
        simpa only [show (1 + k + 1 < 4) ↔ (k + 1 < 3) by omega] using hpcm
      have hx24_eq : sm.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (1 + (k + 1))) := by
        simpa only [show 1 + k + 1 = 1 + (k + 1) by omega] using hx24m
      have hlb_k2_k3 : levelBase (k + 2) ≤ levelBase (k + 3) := levelBase_mono _ _ (by omega) (by omega)
      have hlb_2_k2 : levelBase 2 ≤ levelBase (k + 2) := levelBase_mono _ _ (by omega) (by omega)
      have h1k1 : 1 + k + 1 = k + 2 := by omega
      have h1k2 : 1 + k + 2 = k + 3 := by omega
      rw [h1k1, h1k2] at hpres1
      refine ⟨sm, by simpa only [Finset.sum_range_succ] using hrunn.trans hrun1,
        hpc_eq, hx2m, hx5m, hx9m, hx11m, hx13m, hx24_eq, hx25m, hx26m, ?_, ?_, ?_⟩
      · intro l hl1 hl2 idx hidx
        by_cases hcur : l = k + 2
        · subst hcur; simpa only [h1k1] using hdig1 idx (by simpa only [h1k1] using hidx)
        · have hlt : l ≤ k + 1 := by omega
          have hgo := gapOffset_lt_levelBytes l idx (by omega) hidx
          have hlb_l : levelBase l + levelBytes l ≤ levelBase (k + 2) := by
            have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
            rw [h1]; exact levelBase_mono (l + 1) (k + 2) (by omega) (by omega)
          have hlb_bd_l := levelBase_bound l (by omega)
          rw [hpres1.readBuffer_eq (by omega) (by omega)]
          exact hdign l hl1 hlt idx hidx
      · intro l hl1 hl2 q hq j hj
        by_cases hcur : l = k + 2
        · subst hcur
          have hg1 := hgap1 q (by simpa only [h1k1] using hq) j hj
          rw [h1k1] at hg1
          exact hg1.trans (hgapn (k + 2) (by omega) (by omega) q hq j hj)
        · have hbytes := levelBytes_eq_gap l hl2
          have hbd := levelBase_bound l (by omega)
          have hout : C_TD + levelBase l + 96 * q + 64 + j < C_TD + levelBase (k + 2) ∨
              C_TD + levelBase (k + 3) ≤ C_TD + levelBase l + 96 * q + 64 + j := by
            by_cases hlt : l < k + 2
            · left
              have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
              have h2 := levelBase_mono (l + 1) (k + 2) (by omega) (by omega)
              omega
            · right
              have h2 := levelBase_mono (k + 3) l (by omega) (by omega)
              omega
          exact (hpres1 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) hout).trans (hgapn l hl1 hl2 q hq j hj)
      · have hne_k : k + 1 + 2 = k + 3 := by omega
        rw [hne_k]
        exact (hpresn.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (le_refl _))
  obtain ⟨sfin, hrun3, hpc3, hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, _, hx26f, hdigf, hgapf, hpresf⟩ :=
    hind 3 (le_refl _)
  have hrun_tot : DetRun oracle (submission.image .commit) s0 29417524 sfin 80797748 7340032 := by
    have h := hsetup.trans hrun3
    rw [phase3A_steps_sum, phase3A_cycles_sum, Nat.zero_add, phase3A_calls_sum] at h
    exact h
  exact ⟨sfin, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpc3,
    hx2f, hx5f, hx9f, hx11f, hx13f, hx24f, hx26f,
    fun l hl1 hl2 idx hidx => hdigf l (by omega) (by omega) idx hidx,
    hgapf, hpresf⟩

/-- Phase 3B (`L4..L22 -> L5..L23`, 238-bit masked, words `4319..5122`):
`6,300,064` steps, `13,640,082` cycles, `1,048,574` calls. -/
private theorem commit_phase3B (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 4319))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 128))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 736, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl4 : ∀ idx < levelSize 4, readBuffer s0 (C_TD + levelBase 4 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 4 idx)
    (hzero : ∀ l, 4 ≤ l → l < 24 → ∀ q < levelSize l / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 6300064 s1 13640082 1048574 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 5123) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l, 5 ≤ l → l ≤ 23 → ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l, 4 ≤ l → l < 24 → ∀ q < levelSize l / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 5) (C_TD + levelBase 24) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have htb := treeBytes_eq
  -- Setup words 4319..4322: x27 = mask238Word, x25 = C_DB + 736
  let sa0 := execInstrBr s0 (.ADDI .x27 .x0 (1#12))
  let sa1 := execInstrBr sa0 (.SLLI .x27 .x27 (46#6))
  let sa2 := execInstrBr sa1 (.ADDI .x27 .x27 (4095#12))
  let sa := execInstrBr sa2 (.ADDI .x25 .x2 (736#12))
  have hsa0_pc : sa0.pc = BitVec.ofNat 64 (0x1000 + 4 * 4320) := pc_step_idx s0 4319 hpc
  have hsa1_pc : sa1.pc = BitVec.ofNat 64 (0x1000 + 4 * 4321) := pc_step_idx sa0 4320 hsa0_pc
  have hsa2_pc : sa2.pc = BitVec.ofNat 64 (0x1000 + 4 * 4322) := pc_step_idx sa1 4321 hsa1_pc
  have hsa_pc : sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 4323) := pc_step_idx sa2 4322 hsa2_pc
  have hsetup : DetRun oracle (submission.image .commit) s0 4 sa 4 0 := by
    have r0 : DetRun oracle (submission.image .commit) s0 1 sa0 1 0 :=
      commit_step1_mid5 (by omega) (by omega) hpc (by simp only [commitMid5Instr])
    have r1 : DetRun oracle (submission.image .commit) sa0 1 sa1 1 0 :=
      commit_step1_mid5 (by omega) (by omega) hsa0_pc (by simp only [commitMid5Instr])
    have r2 : DetRun oracle (submission.image .commit) sa1 1 sa2 1 0 :=
      commit_step1_mid5 (by omega) (by omega) hsa1_pc (by simp only [commitMid5Instr])
    have r3 : DetRun oracle (submission.image .commit) sa2 1 sa 1 0 :=
      commit_step1_mid5 (by omega) (by omega) hsa2_pc (by simp only [commitMid5Instr])
    exact ((r0.trans r1).trans r2).trans r3
  have hsa_mem : sa.mem = s0.mem :=
    (((mem_exec_ADDI sa2 _ _ _).trans (mem_exec_ADDI sa1 _ _ _)).trans
      (mem_exec_SLLI sa0 _ _ _)).trans (mem_exec_ADDI s0 _ _ _)
  have hsa_reg_other : ∀ r : Reg, r ≠ .x25 → r ≠ .x27 → sa.getReg r = s0.getReg r := fun r h25 h27 => by
    simp only [sa, sa2, sa1, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x25 r (Ne.symm h25), getReg_setReg_ne' .x27 r (Ne.symm h27)]
  have hsa_x25 : sa.getReg .x25 = BitVec.ofNat 64 (C_DB + 736) := by
    simp only [sa, sa2, sa1, sa0, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0),
      getReg_setReg_ne' .x27 .x2 (by decide), hx2]; decide
  have hsa_x27 : sa.getReg .x27 = mask238Word := by
    simp only [sa, sa2, sa1, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x25 .x27 (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x27 ≠ .x0), c_getReg_x0]; decide
  -- Induction over `k ≤ 19` levels (`lvlIdx = 4 + k`, building `L_{5+k}`)
  have hind : ∀ k ≤ 19,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa (∑ i ∈ Finset.range k, bin238LevelSteps (4 + i)) sn
          (∑ i ∈ Finset.range k, bin238LevelCycles (4 + i)) (∑ i ∈ Finset.range k, bin238LevelCalls (4 + i)) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k < 19 then 4323 else 5123)) ∧
        sn.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sn.getReg .x5 = 0#64 ∧
        sn.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sn.getReg .x11 = 96#64 ∧
        sn.getReg .x13 = 0#64 ∧ sn.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (4 + k)) ∧
        sn.getReg .x25 = BitVec.ofNat 64 (C_DB + 736) ∧ sn.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        sn.getReg .x27 = mask238Word ∧
        (∀ l, 4 ≤ l → l ≤ k + 4 → ∀ idx < levelSize l,
          readBuffer sn (C_TD + levelBase l + gapOffset idx) 32 = nodeVal c96 msg salts l idx) ∧
        (∀ l, 4 ≤ l → l < 24 → ∀ q < levelSize l / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
        MemPreservedOutside s0 sn (C_TD + levelBase 5) (C_TD + levelBase (k + 5)) := by
    intro k hk; induction k with
    | zero =>
      refine ⟨sa, by simpa only [Finset.sum_range_zero] using DetRun.refl oracle (submission.image .commit) sa,
        by simpa only [show (0 : Nat) < 19 by decide, ite_true] using hsa_pc,
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
          have : l = 4 := by omega
          subst this
          rw [readBuffer_of_mem_eq hsa_mem]
          exact hl4 idx hidx,
        fun l hl1 hl2 q hq j hj => by
          rw [getByte_of_mem_eq hsa_mem]
          exact hzero l hl1 hl2 q hq j hj,
        MemPreservedOutside.of_mem_eq hsa_mem _ _⟩
    | succ k ih =>
      obtain ⟨sn, hrunn, hpcn, hx2n, hx5n, hx9n, hx11n, hx13n, hx24n, hx25n, hx26n, hx27n,
        hdign, hgapn, hpresn⟩ := ih (by omega)
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 4323) := by
        simpa only [show k < 19 by omega, ite_true] using hpcn
      have hlb_bd := levelBase_bound (k + 5) (by omega)
      obtain ⟨sm, hrun1, hpcm, hx2m, hx5m, hx9m, hx11m, hx13m, hx24m, hx25m, hx26m, hx27m,
        hdig1, hgap1, hpres1⟩ :=
        commit_bin238_level h768 oracle msg salts (4 + k) (by omega) (by omega) sn hpc_in
          hx2n hx5n hx9n hx11n hx13n hx24n hx25n hx26n hx27n
          (fun off hoff hal => by
            have heq : C_DB + 32 * (4 + k) + off = C_DB + (32 * (4 + k) + off) := by omega
            rw [heq, hpresn.getMem_eq (by omega) (by omega) (by omega)]
            exact hdata (32 * (4 + k) + off) (by omega) (by omega))
          (fun idx hidx => hdign (4 + k) (by omega) (by omega) idx hidx)
          (fun q hq => readBuffer_zero_of_bytes sn _ 32 (fun j hj => by
            simpa only [Nat.add_assoc] using hgapn (4 + k) (by omega) (by omega) q hq j hj))
      have hpc_eq : sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k + 1 < 19 then 4323 else 5123)) := by
        simpa only [show (4 + k + 1 < 23) ↔ (k + 1 < 19) by omega] using hpcm
      have hx24_eq : sm.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (4 + (k + 1))) := by
        simpa only [show 4 + k + 1 = 4 + (k + 1) by omega] using hx24m
      have hlb_k5_k6 : levelBase (k + 5) ≤ levelBase (k + 6) := levelBase_mono _ _ (by omega) (by omega)
      have hlb_5_k5 : levelBase 5 ≤ levelBase (k + 5) := levelBase_mono _ _ (by omega) (by omega)
      have h4k1 : 4 + k + 1 = k + 5 := by omega
      have h4k2 : 4 + k + 2 = k + 6 := by omega
      rw [h4k1, h4k2] at hpres1
      refine ⟨sm, by simpa only [Finset.sum_range_succ] using hrunn.trans hrun1,
        hpc_eq, hx2m, hx5m, hx9m, hx11m, hx13m, hx24_eq, hx25m, hx26m, hx27m, ?_, ?_, ?_⟩
      · intro l hl1 hl2 idx hidx
        by_cases hcur : l = k + 5
        · subst hcur; simpa only [h4k1] using hdig1 idx (by simpa only [h4k1] using hidx)
        · have hlt : l ≤ k + 4 := by omega
          have hgo := gapOffset_lt_levelBytes l idx (by omega) hidx
          have hlb_l : levelBase l + levelBytes l ≤ levelBase (k + 5) := by
            have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
            rw [h1]; exact levelBase_mono (l + 1) (k + 5) (by omega) (by omega)
          have hlb_bd_l := levelBase_bound l (by omega)
          rw [hpres1.readBuffer_eq (by omega) (by omega)]
          exact hdign l hl1 hlt idx hidx
      · intro l hl1 hl2 q hq j hj
        by_cases hcur : l = k + 5
        · subst hcur
          have hg1 := hgap1 q (by simpa only [h4k1] using hq) j hj
          rw [h4k1] at hg1
          exact hg1.trans (hgapn (k + 5) (by omega) (by omega) q hq j hj)
        · have hbytes := levelBytes_eq_gap l hl2
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
  obtain ⟨sfin, hrun19, hpc19, hx2f, hx5f, hx9f, hx11f, hx13f, _, _, hx26f, _, hdigf, hgapf, hpresf⟩ :=
    hind 19 (le_refl _)
  have hrun_tot : DetRun oracle (submission.image .commit) s0 6300064 sfin 13640082 1048574 := by
    have h := hsetup.trans hrun19
    rw [phase3B_steps_sum, phase3B_cycles_sum, Nat.zero_add, phase3B_calls_sum] at h
    exact h
  exact ⟨sfin, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpc19,
    hx2f, hx5f, hx9f, hx11f, hx13f, hx26f,
    fun l hl1 hl2 idx hidx => hdigf l (by omega) (by omega) idx hidx,
    hgapf, hpresf⟩

/-- Full Phase 3 (Phase 3Z `L1` + Phase 3A `L2..L4` + Phase 3B `L5..L23`, words `3366..5122`):
exact `60,948,967` steps, `178,389,465` cycles, `16,777,214` compression calls. -/
theorem commit_phase3 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 3366))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 736, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl0 : ∀ idx < levelSize 0, readBuffer s0 (C_TD + levelBase 0 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 0 idx)
    (hzero : ∀ l < 24, ∀ q < levelSize l / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 60948967 s1 178389465 16777214 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 5123) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l, 1 ≤ l → l ≤ 23 → ∀ idx < levelSize l,
        readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts l idx) ∧
      (∀ l, 1 ≤ l → l ≤ 23 → ∀ q < levelSize l / 2,
        readBuffer s1 (C_TD + levelBase l + 96 * q + 64) 32 = 0) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 1) (C_TD + levelBase 24) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  have htb := treeBytes_eq
  have hlb1_2 : levelBase 1 ≤ levelBase 2 := levelBase_mono 1 2 (by omega) (by omega)
  have hlb2_5 : levelBase 2 ≤ levelBase 5 := levelBase_mono 2 5 (by omega) (by omega)
  have hlb5_24 : levelBase 5 ≤ levelBase 24 := levelBase_mono 5 24 (by omega) (by omega)
  have hlb2_bd := levelBase_bound 2 (by omega)
  have hlb5_bd := levelBase_bound 5 (by omega)
  obtain ⟨sZ, hrunZ, hpcZ, hx2Z, hx5Z, hx9Z, hx11Z, hx13Z, hx24Z, hx26Z, hdigZ, hgapZ, hpresZ⟩ :=
    commit_phase3Z h768 oracle msg salts s0 hpc hx2 hx5 hx9 hx11 hx13 hx26 hdata hl0 hzero
  obtain ⟨sA, hrunA, hpcA, hx2A, hx5A, hx9A, hx11A, hx13A, hx24A, hx26A, hdigA, hgapA, hpresA⟩ :=
    commit_phase3A h768 oracle msg salts sZ hpcZ hx2Z hx5Z hx9Z hx11Z hx13Z hx24Z hx26Z
      (fun off hoff hal => by
        rw [hpresZ.getMem_eq (by omega) (by omega) (by omega)]
        exact hdata off hoff hal)
      (fun idx hidx => hdigZ 1 (by omega) idx hidx)
      (fun l _ hl2 q hq j hj => hgapZ l hl2 q hq j hj)
  obtain ⟨sB, hrunB, hpcB, hx2B, hx5B, hx9B, hx11B, hx13B, hx26B, hdigB, hgapB, hpresB⟩ :=
    commit_phase3B h768 oracle msg salts sA hpcA hx2A hx5A hx9A hx11A hx13A hx24A hx26A
      (fun off hoff hal => by
        rw [hpresA.getMem_eq (by omega) (by omega) (by omega),
            hpresZ.getMem_eq (by omega) (by omega) (by omega)]
        exact hdata off hoff hal)
      (fun idx hidx => hdigA 4 (by omega) (by omega) idx hidx)
      (fun l hl1 hl2 q hq j hj => hgapA l (by omega) hl2 q hq j hj)
  have hpresAB : MemPreservedOutside sZ sB (C_TD + levelBase 2) (C_TD + levelBase 24) :=
    (hpresA.mono (le_refl _) (by omega)).trans (hpresB.mono (by omega) (le_refl _))
  refine ⟨sB, (hrunZ.trans hrunA).trans hrunB, hpcB, hx2B, hx5B, hx9B, hx11B, hx13B, hx26B, ?_, ?_,
    (hpresZ.mono (le_refl _) (by omega)).trans (hpresAB.mono (by omega) (le_refl _))⟩
  · intro l hl1 hl2 idx hidx
    by_cases hlt2 : l < 2
    · have hgo := gapOffset_lt_levelBytes l idx (by omega) hidx
      have hlb_l : levelBase l + levelBytes l ≤ levelBase 2 := by
        have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
        rw [h1]; exact levelBase_mono (l + 1) 2 (by omega) (by omega)
      have hlb_bd_l := levelBase_bound l (by omega)
      rw [hpresAB.readBuffer_eq (by omega) (by omega)]
      exact hdigZ l (by omega) idx hidx
    · by_cases hlt5 : l < 5
      · have hgo := gapOffset_lt_levelBytes l idx (by omega) hidx
        have hlb_l : levelBase l + levelBytes l ≤ levelBase 5 := by
          have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
          rw [h1]; exact levelBase_mono (l + 1) 5 (by omega) (by omega)
        have hlb_bd_l := levelBase_bound l (by omega)
        rw [hpresB.readBuffer_eq (by omega) (by omega)]
        exact hdigA l (by omega) (by omega) idx hidx
      · exact hdigB l (by omega) hl2 idx hidx
  · intro l hl1 hl2 q hq
    apply readBuffer_zero_of_bytes sB _ 32; intro j hj
    by_cases hlt2 : l < 2
    · have hbytes := levelBytes_eq_gap l (by omega)
      have hbd := levelBase_bound l (by omega)
      have hlb_l : levelBase l + levelBytes l ≤ levelBase 2 := by
        have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
        rw [h1]; exact levelBase_mono (l + 1) 2 (by omega) (by omega)
      rw [hpresAB (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (Or.inl (by omega))]
      exact hgapZ l (by omega) q hq j hj
    · by_cases hlt5 : l < 5
      · have hbytes := levelBytes_eq_gap l (by omega)
        have hbd := levelBase_bound l (by omega)
        have hlb_l : levelBase l + levelBytes l ≤ levelBase 5 := by
          have h1 : levelBase l + levelBytes l = levelBase (l + 1) := rfl
          rw [h1]; exact levelBase_mono (l + 1) 5 (by omega) (by omega)
        rw [hpresB (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (Or.inl (by omega))]
        exact hgapA l (by omega) (by omega) q hq j hj
      · exact hgapB l (by omega) (by omega) q hq j hj

/-! ### 2. Phase 4: Unmasked Root (`L24`), Commitment Copy, and `HALT(0)` (words 5123..5142) -/

private theorem commit_fetch_copy32_phase4 (k : Nat) (hk : k < 4) (st : MachineState) :
    (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (5132 + 2 * k)) →
      fetch (submission.image .commit) st = some (.base (.LD .x6 .x12 (BitVec.ofNat 12 (0 + 8 * k))))) ∧
    (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (5132 + 2 * k + 1)) →
      fetch (submission.image .commit) st = some (.base (.SD .x26 .x6 (BitVec.ofNat 12 (0 + 8 * k))))) := by
  constructor
  · intro hpc'
    have h := commit_fetch_commitTailInstr st (5132 + 2 * k) (by omega) (by omega) hpc'
    interval_cases k <;> simpa only [commitTailInstr] using h
  · intro hpc'
    have h := commit_fetch_commitTailInstr st (5132 + 2 * k + 1) (by omega) (by omega) hpc'
    interval_cases k <;> simpa only [commitTailInstr] using h

/-- Phase 4 pointer setup part 1 (words `5123..5126`: `4` steps): sets `x10 = C_TD + levelBase 23`. -/
private theorem commit_phase4_prep_x10 (oracle : Oracle) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 5123))
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD) :
    ∃ r3,
      DetRun oracle (submission.image .commit) s0 4 r3 4 0 ∧
      r3.pc = BitVec.ofNat 64 (0x1000 + 4 * 5127) ∧
      r3.mem = s0.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r3.getReg r = s0.getReg r) ∧
      r3.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 23) := by
  have hlb23 : levelBase 23 = 1610612544 := by decide
  let r0 := execInstrBr s0 (.ADDI .x6 .x0 (1536#12))
  let r1 := execInstrBr r0 (.SLLI .x6 .x6 (20#6))
  let r2 := execInstrBr r1 (.ADDI .x6 .x6 (3904#12))
  let r3 := execInstrBr r2 (.ADD .x10 .x9 .x6)
  have hr0_pc : r0.pc = BitVec.ofNat 64 (0x1000 + 4 * 5124) := pc_step_idx s0 5123 hpc
  have hr1_pc : r1.pc = BitVec.ofNat 64 (0x1000 + 4 * 5125) := pc_step_idx r0 5124 hr0_pc
  have hr2_pc : r2.pc = BitVec.ofNat 64 (0x1000 + 4 * 5126) := pc_step_idx r1 5125 hr1_pc
  have hr3_pc : r3.pc = BitVec.ofNat 64 (0x1000 + 4 * 5127) := pc_step_idx r2 5126 hr2_pc
  have hrun : DetRun oracle (submission.image .commit) s0 4 r3 4 0 := by
    have p0 : DetRun oracle (submission.image .commit) s0 1 r0 1 0 :=
      commit_step1_tail (by omega) (by omega) hpc (by simp only [commitTailInstr])
    have p1 : DetRun oracle (submission.image .commit) r0 1 r1 1 0 :=
      commit_step1_tail (by omega) (by omega) hr0_pc (by simp only [commitTailInstr])
    have p2 : DetRun oracle (submission.image .commit) r1 1 r2 1 0 :=
      commit_step1_tail (by omega) (by omega) hr1_pc (by simp only [commitTailInstr])
    have p3 : DetRun oracle (submission.image .commit) r2 1 r3 1 0 :=
      commit_step1_tail (by omega) (by omega) hr2_pc (by simp only [commitTailInstr])
    exact ((p0.trans p1).trans p2).trans p3
  have hmem : r3.mem = s0.mem :=
    (((mem_exec_ADD r2 _ _ _).trans (mem_exec_ADDI r1 _ _ _)).trans
      (mem_exec_SLLI r0 _ _ _)).trans (mem_exec_ADDI s0 _ _ _)
  have hreg : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r3.getReg r = s0.getReg r := fun r h6r h10r => by
    simp only [r3, r2, r1, r0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x10 r (Ne.symm h10r), getReg_setReg_ne' .x6 r (Ne.symm h6r)]
  have hx10 : r3.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 23) := by
    simp only [r3, r2, r1, r0, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq, hx9, hlb23]
    decide
  exact ⟨r3, hrun, hr3_pc, hmem, hreg, hx10⟩

/-- Phase 4 pointer setup part 2 (words `5127..5130`: `4` steps): sets `x12 = C_TD + levelBase 24`. -/
private theorem commit_phase4_prep_x12 (oracle : Oracle) (r3 : MachineState)
    (hpc : r3.pc = BitVec.ofNat 64 (0x1000 + 4 * 5127))
    (hx9 : r3.getReg .x9 = BitVec.ofNat 64 C_TD) :
    ∃ r7,
      DetRun oracle (submission.image .commit) r3 4 r7 4 0 ∧
      r7.pc = BitVec.ofNat 64 (0x1000 + 4 * 5131) ∧
      r7.mem = r3.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x12 → r7.getReg r = r3.getReg r) ∧
      r7.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 24) := by
  have hlb24 : levelBase 24 = 1610612640 := by decide
  let r4 := execInstrBr r3 (.ADDI .x6 .x0 (1536#12))
  let r5 := execInstrBr r4 (.SLLI .x6 .x6 (20#6))
  let r6 := execInstrBr r5 (.ADDI .x6 .x6 (4000#12))
  let r7 := execInstrBr r6 (.ADD .x12 .x9 .x6)
  have hr4_pc : r4.pc = BitVec.ofNat 64 (0x1000 + 4 * 5128) := pc_step_idx r3 5127 hpc
  have hr5_pc : r5.pc = BitVec.ofNat 64 (0x1000 + 4 * 5129) := pc_step_idx r4 5128 hr4_pc
  have hr6_pc : r6.pc = BitVec.ofNat 64 (0x1000 + 4 * 5130) := pc_step_idx r5 5129 hr5_pc
  have hr7_pc : r7.pc = BitVec.ofNat 64 (0x1000 + 4 * 5131) := pc_step_idx r6 5130 hr6_pc
  have hrun : DetRun oracle (submission.image .commit) r3 4 r7 4 0 := by
    have p4 : DetRun oracle (submission.image .commit) r3 1 r4 1 0 :=
      commit_step1_tail (by omega) (by omega) hpc (by simp only [commitTailInstr])
    have p5 : DetRun oracle (submission.image .commit) r4 1 r5 1 0 :=
      commit_step1_tail (by omega) (by omega) hr4_pc (by simp only [commitTailInstr])
    have p6 : DetRun oracle (submission.image .commit) r5 1 r6 1 0 :=
      commit_step1_tail (by omega) (by omega) hr5_pc (by simp only [commitTailInstr])
    have p7 : DetRun oracle (submission.image .commit) r6 1 r7 1 0 :=
      commit_step1_tail (by omega) (by omega) hr6_pc (by simp only [commitTailInstr])
    exact ((p4.trans p5).trans p6).trans p7
  have hmem : r7.mem = r3.mem :=
    (((mem_exec_ADD r6 _ _ _).trans (mem_exec_ADDI r5 _ _ _)).trans
      (mem_exec_SLLI r4 _ _ _)).trans (mem_exec_ADDI r3 _ _ _)
  have hreg : ∀ r : Reg, r ≠ .x6 → r ≠ .x12 → r7.getReg r = r3.getReg r := fun r h6r h12r => by
    simp only [r7, r6, r5, r4, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12r), getReg_setReg_ne' .x6 r (Ne.symm h6r)]
  have hx12 : r7.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 24) := by
    simp only [r7, r6, r5, r4, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne,
      c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq, hx9, hlb24]
    decide
  exact ⟨r7, hrun, hr7_pc, hmem, hreg, hx12⟩

/-- Phase 4 pre-halt (words `5123..5141`: `19` steps, `26` cycles, `1` compression call),
landing at `5142` (`ECALL HALT(0)`) with `rootVal` in both `C_TD + levelBase 24` and `C_CMT`. -/
theorem commit_phase4 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 5123))
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hl23 : ∀ idx < 2, readBuffer s0 (C_TD + levelBase 23 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 23 idx)
    (hgap23 : readBuffer s0 (C_TD + levelBase 23 + 64) 32 = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 19 s1 26 1 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 5142) ∧
      s1.getReg .x5 = 1#64 ∧
      s1.getReg .x10 = 0#64 ∧
      readBuffer s1 C_CMT 32 = rootVal (fun x => oracle.compression (x.cast h768.symm)) msg salts ∧
      readBuffer s1 (C_TD + levelBase 24) 32 =
        rootVal (fun x => oracle.compression (x.cast h768.symm)) msg salts ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < C_CMT ∨ C_CMT + 32 ≤ q) →
        (q < C_TD + levelBase 24 ∨ C_TD + levelBase 24 + 32 ≤ q) →
        s1.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_CMT : C_CMT = 4294971392 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hlb23 : levelBase 23 = 1610612544 := by decide
  have hlb24 : levelBase 24 = 1610612640 := by decide
  obtain ⟨r3, hprep1, hr3_pc, hr3_mem, hr3_reg_other, hr3_x10⟩ :=
    commit_phase4_prep_x10 oracle s0 hpc hx9
  obtain ⟨r7, hprep2, hr7_pc, hr7_mem3, hr7_reg_r3, hr7_x12⟩ :=
    commit_phase4_prep_x12 oracle r3 hr3_pc ((hr3_reg_other .x9 (by decide) (by decide)).trans hx9)
  have hprep_run : DetRun oracle (submission.image .commit) s0 8 r7 8 0 := hprep1.trans hprep2
  have hr7_mem : r7.mem = s0.mem := hr7_mem3.trans hr3_mem
  have hr7_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r7.getReg r = s0.getReg r :=
    fun r h6r h10r h12r => (hr7_reg_r3 r h6r h12r).trans (hr3_reg_other r h6r h10r)
  have hr7_x10 : r7.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 23) :=
    (hr7_reg_r3 .x10 (by decide) (by decide)).trans hr3_x10
  let root := rootVal c96 msg salts
  let r8 := writeBits r7 (BitVec.ofNat 64 (C_TD + levelBase 24)) root
  have hr7_in : readBuffer r7 (C_TD + levelBase 23) 96 =
      binaryInput (nodeVal c96 msg salts 23 0) (nodeVal c96 msg salts 23 1) := by
    rw [readBuffer_of_mem_eq hr7_mem, readBuffer_binary_of_zero_gap s0 _ hgap23]
    have h0 := hl23 0 (by omega); have h1 := hl23 1 (by omega)
    rw [show gapOffset 0 = 0 from rfl, Nat.add_zero] at h0
    rw [show gapOffset 1 = 32 from rfl] at h1
    rw [h0, h1]
  have hroot_eq : oracle.compression ((readBuffer r7 (C_TD + levelBase 23) 96).cast h768.symm) = root := by
    rw [hr7_in]
    exact nodeVal_root_eq c96 msg salts
  have hf5131 : fetch (submission.image .commit) r7 = some (.base .ECALL) := by
    have h := commit_fetch_commitTailInstr r7 5131 (by omega) (by omega) hr7_pc
    simp only [commitTailInstr] at h
    exact h
  have hcall_run : DetRun oracle (submission.image .commit) r7 1 r8 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := r7) hf5131
      ((hr7_reg_other .x5 (by decide) (by decide) (by decide)).trans hx5)
      ((hr7_reg_other .x11 (by decide) (by decide) (by decide)).trans hx11)
      ((hr7_reg_other .x13 (by decide) (by decide) (by decide)).trans hx13)
      (C_TD + levelBase 23) (C_TD + levelBase 24) hr7_x10 hr7_x12
      (by omega) (by omega) (by omega) (by omega) root hroot_eq
  have hr8_pc : r8.pc = BitVec.ofNat 64 (0x1000 + 4 * 5132) := pc_step_idx r7 5131 hr7_pc
  obtain ⟨rc, hcopy_run, hrc_pc, _, hrc_dig, hrc_pres⟩ :=
    commit_copy32 oracle r8 5132 .x12 .x26 (C_TD + levelBase 24) C_CMT 0 0
      (by decide) (by decide) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hr8_pc
      ((writeBits_register r7 _ root .x12).trans hr7_x12)
      ((writeBits_register r7 _ root .x26).trans ((hr7_reg_other .x26 (by decide) (by decide) (by decide)).trans hx26))
      commit_fetch_copy32_phase4
  let s1 := execInstrBr rc (.ADDI .x5 .x0 (1#12))
  let s2 := execInstrBr s1 (.ADDI .x10 .x0 (0#12))
  have hrc_pc' : rc.pc = BitVec.ofNat 64 (0x1000 + 4 * 5140) := hrc_pc
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 5141) := pc_step_idx rc 5140 hrc_pc'
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 5142) := pc_step_idx s1 5141 hs1_pc
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
    simpa only [Nat.add_zero] using hrc_dig.trans (writeBits_readBuffer_digest r7 (C_TD + levelBase 24) root)
  · rw [readBuffer_of_mem_eq hs2_mem, hrc_pres.readBuffer_eq (by omega) (by omega)]
    exact writeBits_readBuffer_digest r7 (C_TD + levelBase 24) root
  · intro q hq houtCmt houtRoot
    have h1 := getByte_of_mem_eq hs2_mem (BitVec.ofNat 64 q)
    have h2 := hrc_pres q hq (by simpa only [Nat.add_zero] using houtCmt)
    have h3 := memPreserved_writeBits r7 (C_TD + levelBase 24) root (by omega) q hq houtRoot
    have h4 := getByte_of_mem_eq hr7_mem (BitVec.ofNat 64 q)
    exact ((h1.trans h2).trans h3).trans h4

/-! ### 3. Top-Level Commit Exactness, Oracle Refinement, and Termination -/

private theorem commit_det_phases (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (s0 : MachineState) (rand : Fin (LENGTH / 2) → PairRand)
    (hinv :
      s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 1047) ∧
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
      oracle.run (execute (submission.image .commit) (submission.steps .commit - 16793622) s0 true) =
        pure (⟨.success, sfin, 849740288, 83886079⟩, 83886079) ∧
      readBuffer sfin C_CMT 32 =
        rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) ∧
      CommittedTrapdoor h768 oracle.compression message (pairSalts rand)
        (readBuffer sfin C_TD submission.sizes.trapdoor) := by
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_CMT : C_CMT = 4294971392 := rfl
  have hC_ROW : C_ROW = 5905584096 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hsteps_ge : 16793622 + 262537735 ≤ submission.steps .commit := by decide
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
  obtain ⟨s1, hrun1, hpc1, hx2_1, hx5_1, hx9_1, hx11_1, hx13_1, hx26_1, hl0_1, hgap0_1, hsalt1, hpres1⟩ :=
    commit_phase1 h768 oracle message rand s0 hpc0 hx2_0 hx5_0 hx8_0 hx9_0 hx10_0 hx11_0 hx13_0
      hx18_0 hx19_0 hx26_0 hmsg0 hsalts0 hgap0
  have hls0 := levelSize_0
  have hlb0 : levelBase 0 = 0 := rfl
  have hlb1 : levelBase 1 = 805306368 := by decide
  have hlb24 : levelBase 24 = 1610612640 := by decide
  have htb := treeBytes_eq
  have hro := rowOff_eq
  have htd := trapdoorBytes_eq
  have hdata1 : ∀ off < 736, off % 8 = 0 →
      s1.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit message).getMem (BitVec.ofNat 64 (C_DB + off)) := by
    intro off hoff hal
    rw [← readBuffer_word s1 (C_DB + off) (by omega),
      ← readBuffer_word (submission.initialState .commit message) (C_DB + off) (by omega)]
    apply readBuffer_congr; intro j hj
    exact (hpres1 (C_DB + off + j) (by omega) (by omega)).trans
      (hpres0 (C_DB + off + j) (by omega) (fun _ _ => by omega))
  have hl0_1' : ∀ idx < levelSize 0,
      readBuffer s1 (C_TD + levelBase 0 + gapOffset idx) 32 = nodeVal c96 message salts 0 idx := by
    intro idx hidx
    rw [hlb0, Nat.add_zero]
    exact hl0_1 idx (by omega)
  have hzero1 : ∀ l < 24, ∀ q < levelSize l / 2, ∀ j < 32,
      s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0 := by
    intro l hl q hq j hj
    have hbytes := levelBytes_eq_gap l hl
    have hbd := levelBase_bound l (by omega)
    have hinit0 : (submission.initialState .commit message).getByte
        (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0 :=
      commit_initial_zero_byte message _ (by omega)
    have hp0 := hpres0 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (fun _ _ => by omega)
    by_cases hl0_eq : l = 0
    · subst hl0_eq
      rw [hlb0, Nat.add_zero] at hp0 hinit0 ⊢
      exact ((hgap0_1 q (by omega) j hj).trans hp0).trans hinit0
    · have hlb_ge1 : levelBase 1 ≤ levelBase l := levelBase_mono 1 l (by omega) (by omega)
      have hp1 := hpres1 (C_TD + levelBase l + 96 * q + 64 + j) (by omega) (by omega)
      exact (hp1.trans hp0).trans hinit0
  obtain ⟨s3, hrun3, hpc3, _, hx5_3, hx9_3, hx11_3, hx13_3, hx26_3, hbin3, hgap3, hpres3⟩ :=
    commit_phase3 h768 oracle message salts s1 hpc1 hx2_1 hx5_1 hx9_1 hx11_1 hx13_1 hx26_1 hdata1 hl0_1' hzero1
  obtain ⟨s4, hrun4, hpc4, hx5_4, hx10_4, hcmt4, hroot4, hpres4⟩ :=
    commit_phase4 h768 oracle message salts s3 hpc3 hx5_3 hx9_3 hx11_3 hx13_3 hx26_3
      (fun idx hidx => hbin3 23 (by omega) (by omega) idx (by rw [levelSize_23]; exact hidx))
      (by simpa only [Nat.mul_zero, Nat.add_zero] using hgap3 23 (by omega) (by omega) 0 (by rw [levelSize_23]; omega))
  have hrun14 : DetRun oracle (submission.image .commit) s0 262537734 s4 849740287 83886079 :=
    (hrun1.trans hrun3).trans hrun4
  have hf5142 : fetch (submission.image .commit) s4 = some (.base .ECALL) := by
    have h := commit_fetch_commitTailInstr s4 5142 (by omega) (by omega) hpc4
    simp only [commitTailInstr] at h
    exact h
  have hfin := hrun14.finish hf5142
    hx5_4 hx10_4 (submission.steps .commit - 16793622) (by omega)
  refine ⟨s4, hfin, ?_, ?_⟩
  · dsimp only [salts] at hcmt4; exact hcmt4
  · have htd_sz : submission.sizes.trapdoor = trapdoorBytes := trapdoorBytes_eq.symm
    refine ⟨?_, ?_, ?_⟩
    · intro l hl idx hidx
      have hnoff : nodeOffset l idx = gapOffset idx := rfl
      have hoff_bd : levelBase l + nodeOffset l idx + 32 ≤ submission.sizes.trapdoor := by
        rw [htd_sz, hnoff]
        have hbd := levelBase_bound l hl
        by_cases h24 : l = 24
        · subst h24; rw [levelSize_24] at hidx
          have : idx = 0 := by omega
          subst this; unfold gapOffset; rw [hlb24, htd]; decide
        · have hgo := gapOffset_lt_levelBytes l idx (by omega) hidx
          omega
      have hsl : BitVec.extractLsb' (8 * (levelBase l + nodeOffset l idx)) 256
          (readBuffer s4 C_TD submission.sizes.trapdoor) =
          readBuffer s4 (C_TD + (levelBase l + nodeOffset l idx)) 32 :=
        read_buffer_slice s4 C_TD submission.sizes.trapdoor (levelBase l + nodeOffset l idx) 32 hoff_bd
      rw [hsl, hnoff]
      by_cases h0 : l = 0
      · subst h0
        rw [hlb0, Nat.zero_add]
        have hgo := gapOffset_lt_levelBytes 0 idx (by omega) hidx
        have hlb0_bytes : levelBytes 0 = levelBase 1 := by decide
        have hp4 : readBuffer s4 (C_TD + gapOffset idx) 32 = readBuffer s3 (C_TD + gapOffset idx) 32 :=
          readBuffer_congr _ _ _ _ (fun j hj => hpres4 (C_TD + gapOffset idx + j) (by omega) (by omega) (by omega))
        rw [hp4, hpres3.readBuffer_eq (by omega) (by omega)]
        exact hl0_1 idx (by omega)
      · by_cases h24 : l = 24
        · subst h24
          rw [levelSize_24] at hidx
          have : idx = 0 := by omega
          subst this
          have hgo0 : gapOffset 0 = 0 := rfl
          rw [hgo0, Nat.add_zero]
          dsimp only [salts] at hroot4
          have hrt24 : rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) =
              nodeVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand) 24 0 := rfl
          exact hroot4.trans hrt24
        · rw [← Nat.add_assoc]
          have hgo := gapOffset_lt_levelBytes l idx (by omega) hidx
          have hlb_l : levelBase l + levelBytes l ≤ levelBase 24 := by
            have h1' : levelBase l + levelBytes l = levelBase (l + 1) := rfl
            rw [h1']; exact levelBase_mono (l + 1) 24 (by omega) (le_refl _)
          have hp4 : readBuffer s4 (C_TD + levelBase l + gapOffset idx) 32 =
              readBuffer s3 (C_TD + levelBase l + gapOffset idx) 32 :=
            readBuffer_congr _ _ _ _ (fun j hj => hpres4 (C_TD + levelBase l + gapOffset idx + j)
              (by omega) (by omega) (by omega))
          rw [hp4]
          exact hbin3 l (by omega) (by omega) idx hidx
    · intro l hl q hq
      have hbytes := levelBytes_eq_gap l hl
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
      by_cases h0 : l = 0
      · subst h0
        have hlb0_bytes : levelBase 0 + levelBytes 0 = levelBase 1 := rfl
        rw [hpres3.readBuffer_eq (by omega) (by omega)]
        exact readBuffer_zero_of_bytes s1 _ 32 (fun j hj => by
          simpa only [Nat.add_assoc] using hzero1 0 (by omega) q hq j hj)
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
      rw [hp4, hpres3.readBuffer_eq (by omega) (by omega)]
      exact hsalt1 i

private theorem readBuffer_digest_eq (s : MachineState) (a : Nat) (v : Commitment)
    (h : readBuffer s a 32 = v) : readBuffer s a DIGEST_BYTES = v := by
  have hgen : ∀ (n : Nat) (hn : n = 32) (w : BitVec (8 * n)),
      readBuffer s a 32 = w.cast (by rw [hn]) → readBuffer s a n = w := by
    intro n hn; subst hn; intro w hw; exact hw
  exact hgen DIGEST_BYTES rfl v h

private theorem commit_run_eq_helper (oracle : Oracle) (message : Message)
    (post0 finalState : (Fin (LENGTH / 2) → PairRand) → MachineState)
    (hrun0 : oracle.run (execute (submission.image .commit) (16793622 + (submission.steps .commit - 16793622))
        (submission.initialState .commit message) true) =ᵈ
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        (fun p : Execution × Nat => (p.1.charge 58736662 0, p.2)) <$>
          oracle.run (execute (submission.image .commit) (submission.steps .commit - 16793622) (post0 rand) true)))
    (hs : ∀ rand, oracle.run (execute (submission.image .commit) (submission.steps .commit - 16793622) (post0 rand) true) =
      pure (⟨.success, finalState rand, 849740288, 83886079⟩, 83886079)) :
    oracle.run (submission.run .commit message) =ᵈ
      (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
        pure (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 908476950, oracleCalls := 83886079 } : Execution), 83886079)) := by
  have hsteps_commit : submission.steps .commit = 16793622 + (submission.steps .commit - 16793622) := by
    have hge : 16793622 ≤ submission.steps .commit := by decide
    omega
  rw [submission_run_commit submission message, hsteps_commit]
  refine hrun0.trans ?_
  apply EvalDistEq.bind_right; intro rand
  rw [hs rand, map_pure]
  have heq : (({ exit := Riscv.Exit.success, state := finalState rand,
                 cycles := 849740288, oracleCalls := 83886079 } : Execution).charge 58736662 0, 83886079) =
      (({ exit := Riscv.Exit.success, state := finalState rand,
          cycles := 908476950, oracleCalls := 83886079 } : Execution), 83886079) := by
    unfold Execution.charge; dsimp only
  rw [heq]

private theorem commit_read_spec_helper (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (sfin : MachineState) (salts : Index → Salt192)
    (hcmt : readBuffer sfin C_CMT 32 = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts)
    (htd : CommittedTrapdoor h768 oracle.compression message salts (readBuffer sfin C_TD submission.sizes.trapdoor)) :
    let (cmt, td) := submission.readCommit ⟨.success, sfin, 908476950, 83886079⟩
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
always halts with `.success`, exactly `908,476,950` cycles and `83,886,079` compression calls,
writing `rootVal` to the commitment buffer and a valid `CommittedTrapdoor` to the trapdoor buffer. -/
theorem commit_run_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    ∃ finalState : (Fin (LENGTH / 2) → PairRand) → MachineState,
      oracle.run (submission.run .commit message) =ᵈ
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (({ exit := Riscv.Exit.success, state := finalState rand,
                   cycles := 908476950, oracleCalls := 83886079 } : Execution), 83886079)) ∧
      ∀ rand,
        let salts := pairSalts rand
        let (cmt, td) := submission.readCommit
          ⟨Riscv.Exit.success, finalState rand, 908476950, 83886079⟩
        cmt = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts ∧
        CommittedTrapdoor h768 oracle.compression message salts td := by
  obtain ⟨post0, hrun0, hinv0⟩ := commit_phase0 oracle message (submission.steps .commit - 16793622)
  have hdet : ∀ rand : Fin (LENGTH / 2) → PairRand,
      ∃ sfin : MachineState,
        oracle.run (execute (submission.image .commit) (submission.steps .commit - 16793622) (post0 rand) true) =
          pure (⟨.success, sfin, 849740288, 83886079⟩, 83886079) ∧
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
  refine ⟨fun rand => (submission.readCommit ⟨.success, finalState rand, 908476950, 83886079⟩).2, ?_, ?_⟩
  · let f : Execution × Nat → Commitment × BitVec (8 * submission.sizes.trapdoor) :=
      fun p => submission.readCommit p.1
    have hmap : (fixedOracleRun oracle (submission.scheme.commit message) :
          ProbComp (Commitment × BitVec (8 * submission.sizes.trapdoor))) =
        f <$> oracle.run (submission.run .commit message) := by
      simp only [fixedOracleRun, Submission.scheme, oracle_run_map, Functor.map_map, f]
    have hstep : f <$> (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (({ exit := Riscv.Exit.success, state := finalState rand,
                   cycles := 908476950, oracleCalls := 83886079 } : Execution), 83886079)) =
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          pure (rootVal (fun x => oracle.compression (x.cast h768.symm)) message (pairSalts rand),
                (submission.readCommit ⟨.success, finalState rand, 908476950, 83886079⟩).2)) := by
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
    (fun rand => ((⟨.success, finalState rand, 908476950, 83886079⟩ : Execution), 83886079))
    (fun result => result.1.exit ≠ Riscv.Exit.unfinished)
    (fun _ => by dsimp only; decide)

end CommitGolfCandidate
