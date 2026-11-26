import CommitGolfCandidate.MoonCommitExec

/-! Exact RV64IM execution proofs for binary tree levels `L2..L23` of the `commit` image
(cost accounting, tree-node helpers, `commit_bin_pair`, and Stages A & B of `commit_bin_level`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-- Exact cost accounting for binary level `lvlIdx : Nat` (`0 ≤ lvlIdx < 22`, building `L_{lvlIdx+2}`
from `L_{lvlIdx+1}`). -/
def binLevelSteps (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 1) / 2
  let prom := levelSize (lvlIdx + 1) % 2
  let chunks := calls / 128
  let remPairs := (calls % 128) / 2
  let oddCall := calls % 2
  10 + (if 0 < chunks then 4 + 513 * chunks else 0) + (3 + 10 * remPairs) +
    (if oddCall = 1 then 7 + 9 * prom else 3 + 8 * prom) + 2

def binLevelCycles (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 1) / 2
  let prom := levelSize (lvlIdx + 1) % 2
  let chunks := calls / 128
  let remPairs := (calls % 128) / 2
  let oddCall := calls % 2
  10 + (if 0 < chunks then 4 + 1409 * chunks else 0) + (3 + 24 * remPairs) +
    (if oddCall = 1 then 14 + 9 * prom else 3 + 8 * prom) + 2

def binLevelCalls (lvlIdx : Nat) : Nat :=
  levelSize (lvlIdx + 1) / 2

theorem levelSize_le_max (l : Nat) (hl : l ≤ 24) : levelSize l ≤ 16777216 := by
  interval_cases l <;> decide

theorem levelBase_mod8 (l : Nat) (hl : l ≤ 24) : levelBase l % 8 = 0 := by
  interval_cases l <;> decide

theorem levelBytes_eq_gap (l : Nat) (hl1 : 1 ≤ l) (hl2 : l < 24) :
    levelBytes l = ((levelSize l + 1) / 2) * 96 := by
  unfold levelBytes
  have h0 : l ≠ 0 := by omega
  simp only [h0, ite_false, hl2, ite_true]

theorem nodeVal_bin_masked (c96 : Comp96) (msg : Message) (salts : Index → Salt192)
    (lvlIdx idx : Nat) (hlt : 2 * idx + 1 < levelSize (lvlIdx + 1)) (hne24 : lvlIdx + 2 ≠ 24) :
    mask240 (c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (2 * idx))
      (nodeVal c96 msg salts (lvlIdx + 1) (2 * idx + 1)))) =
      nodeVal c96 msg salts (lvlIdx + 2) idx := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (lvlIdx + 2) idx = _
  rw [nodeValFromLeaves]
  dsimp only
  simp only [hlt, ite_true, hne24, ite_false]
  rfl

theorem nodeVal_bin_promoted (c96 : Comp96) (msg : Message) (salts : Index → Salt192)
    (lvlIdx idx : Nat) (h1 : ¬ (2 * idx + 1 < levelSize (lvlIdx + 1)))
    (h2 : 2 * idx < levelSize (lvlIdx + 1)) :
    nodeVal c96 msg salts (lvlIdx + 1) (2 * idx) = nodeVal c96 msg salts (lvlIdx + 2) idx := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (lvlIdx + 2) idx = _
  rw [nodeValFromLeaves]
  dsimp only
  simp only [h1, ite_false, h2, ite_true]
  rfl

theorem nodeVal_root_eq (c96 : Comp96) (msg : Message) (salts : Index → Salt192) :
    c96 (binaryInput (nodeVal c96 msg salts 23 0) (nodeVal c96 msg salts 23 1)) =
      rootVal c96 msg salts := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (22 + 2) 0 = _
  rw [nodeValFromLeaves]
  dsimp only
  have hlt : 2 * 0 + 1 < levelSize (22 + 1) := by
    rw [show 22 + 1 = 23 from rfl, levelSize_23]; omega
  have h24 : (22 + 2 : Nat) = 24 := rfl
  simp only [hlt, h24, ite_true]
  rfl

/-- Single-step wrappers that discharge `commitMid2Instr`/`commitTailInstr` before `ordinaryStep`. -/
theorem commit_step1_mid2 {oracle : Oracle} {s : MachineState} {idx : Nat} {ins : Instr}
    (hlo : 4154 ≤ idx) (hhi : idx < 4195)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hins : commitMid2Instr idx = .base ins)
    (hstep : ordinaryStep s (.base ins) = some (execInstrBr s ins) := by rfl)
    (hcyc : instructionCycles (.base ins) = 1 := by rfl) :
    DetRun oracle (submission.image .commit) s 1 (execInstrBr s ins) 1 0 := by
  have hf := commit_fetch_commitMid2Instr s idx hlo hhi hpc
  rw [hins] at hf
  exact DetRun.step1 hf hstep hcyc

theorem commit_step1_tail {oracle : Oracle} {s : MachineState} {idx : Nat} {ins : Instr}
    (hlo : 4707 ≤ idx) (hhi : idx < 4770)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hins : commitTailInstr idx = .base ins)
    (hstep : ordinaryStep s (.base ins) = some (execInstrBr s ins) := by rfl)
    (hcyc : instructionCycles (.base ins) = 1 := by rfl) :
    DetRun oracle (submission.image .commit) s 1 (execInstrBr s ins) 1 0 := by
  have hf := commit_fetch_commitTailInstr s idx hlo hhi hpc
  rw [hins] at hf
  exact DetRun.step1 hf hstep hcyc

private theorem pc_bne_3158 :
    BitVec.ofNat 64 (0x1000 + 4 * 4707) + signExtend13 (6144#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 4195) := by decide

private theorem pc_beq_3161 :
    BitVec.ofNat 64 (0x1000 + 4 * 4710) + signExtend13 (44#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 4721) := by decide

private theorem pc_bne_3171 :
    BitVec.ofNat 64 (0x1000 + 4 * 4720) + signExtend13 (8156#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 4711) := by decide

/-- One 2-call pair of masked binary compressions (`binPairInstr`: 8 steps, 22 cycles, 2 calls).
Works identically for `bin_bulk` (`basePc = 4195 + 8 * p`) and `bin_tail` (`basePc = 4711`). -/
theorem commit_bin_pair (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx basePc q : Nat) (hlvl : lvlIdx < 22) (hq : 2 * q + 1 < levelSize (lvlIdx + 1) / 2)
    (s : MachineState)
    (hfetch : ∀ j < 8, ∀ st : MachineState,
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + j)) →
      fetch (submission.image .commit) st = some (binPairInstr j))
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q) - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q - 64))
    (hsrc : ∀ j < 4, readBuffer s (C_TD + levelBase (lvlIdx + 1) + gapOffset (4 * q + j)) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) (4 * q + j))
    (hsrcGap : ∀ p < 2, readBuffer s (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + p) + 64) 32 = 0) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 8 s' 22 2 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 8)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + 1)) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) ∧
      readBuffer s' (C_TD + levelBase (lvlIdx + 2) + 96 * q) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (2 * q) ∧
      readBuffer s' (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (2 * q + 1) ∧
      MemPreservedOutside s s' (C_TD + levelBase (lvlIdx + 2) + 96 * q)
        (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcB := levelBase_bound (lvlIdx + 1) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 2) (by omega)
  have htb := treeBytes_eq
  have hsrcAl := levelBase_mod8 (lvlIdx + 1) (by omega)
  have hdstAl := levelBase_mod8 (lvlIdx + 2) (by omega)
  have hsrcBytes := levelBytes_eq_gap (lvlIdx + 1) (by omega) (by omega)
  have hdstBytes := levelBytes_eq_gap (lvlIdx + 2) (by omega) (by omega)
  have hdstSize : levelSize (lvlIdx + 2) = (levelSize (lvlIdx + 1) + 1) / 2 :=
    levelSize_step (lvlIdx + 1) (by omega)
  have hbase_step : levelBase (lvlIdx + 2) = levelBase (lvlIdx + 1) + levelBytes (lvlIdx + 1) := rfl
  have hsrc_lt : 96 * (2 * q + 1) + 96 ≤ levelBytes (lvlIdx + 1) := by rw [hsrcBytes]; omega
  have hdst_lt : 96 * q + 64 ≤ levelBytes (lvlIdx + 2) := by rw [hdstBytes, hdstSize]; omega
  -- First call + mask240 (steps 0..3)
  let s1 := execInstrBr s (.ADDI .x10 .x10 (96#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (64#12))
  let raw0 := c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (4 * q))
    (nodeVal c96 msg salts (lvlIdx + 1) (4 * q + 1)))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q)) raw0
  let s4 := execInstrBr s3 (.SH .x12 .x0 (30#12))
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) := pc_step_idx s basePc hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) := pc_step_idx s1 (basePc + 1) hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) := pc_step_idx s2 (basePc + 2) hs2_pc
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 4)) := pc_step_idx s3 (basePc + 3) hs3_pc
  have hm2 : s2.mem = s.mem := (mem_exec_ADDI s1 .x12 .x12 (64#12)).trans (mem_exec_ADDI s .x10 .x10 (96#12))
  have hs2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s2.getReg r = s.getReg r := fun r h10 h12 => by
    have h2 : s2.getReg r = s1.getReg r := by
      simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
    have h1 : s1.getReg r = s.getReg r := by
      simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm h10)]
    exact h2.trans h1
  have hs4_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s4.getReg r = s.getReg r := fun r h10 h12 =>
    ((reg_exec_SH s3 _ _ _ r).trans (writeBits_register s2 _ raw0 r)).trans (hs2_reg_other r h10 h12)
  have hs1_a0 : s1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_a0 : s2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q)) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs1_a0]
  have hs2_a2 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q) := by
    have h1x12 : s1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q - 64) := by
      simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hx12]
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h1x12,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_in : readBuffer s2 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q)) 96 =
      binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (4 * q))
        (nodeVal c96 msg salts (lvlIdx + 1) (4 * q + 1)) := by
    rw [readBuffer_of_mem_eq hm2,
      readBuffer_binary_of_zero_gap s _ (by simpa only [Nat.add_zero] using hsrcGap 0 (by omega))]
    have h0 := hsrc 0 (by omega); have h1 := hsrc 1 (by omega)
    rw [show 4 * q + 0 = 4 * q from Nat.add_zero _,
        show gapOffset (4 * q) = 96 * (2 * q) by rw [show 4 * q = 2 * (2 * q) by omega, gapOffset_even]] at h0
    rw [show gapOffset (4 * q + 1) = 96 * (2 * q) + 32 by rw [show 4 * q + 1 = 2 * (2 * q) + 1 by omega, gapOffset_odd],
        ← Nat.add_assoc] at h1
    rw [h0, h1]
  have hst0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (hfetch 0 (by omega) s (by simpa only [Nat.add_zero] using hpc)) rfl
  have hst1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (hfetch 1 (by omega) s1 hs1_pc) rfl
  have hst2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s2)
      (hfetch 2 (by omega) s2 hs2_pc)
      (by rw [hs2_reg_other .x5 (by decide) (by decide)]; exact hx5)
      (by rw [hs2_reg_other .x11 (by decide) (by decide)]; exact hx11)
      (by rw [hs2_reg_other .x13 (by decide) (by decide)]; exact hx13)
      (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q)) (C_TD + levelBase (lvlIdx + 2) + 96 * q) hs2_a0 hs2_a2
      (by omega) (by omega) (by omega) (by omega) raw0 (by rw [hs2_in])
  have hs3_a2 : s3.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q) :=
    (writeBits_register s2 _ raw0 .x12).trans hs2_a2
  have hsh0_addr : s3.getReg .x12 + signExtend12 (30#12) =
      BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 30) := by
    rw [hs3_a2, add_signExtend12_ofNat_small _ 30 (by omega)]
  have hst3 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (hfetch 3 (by omega) s3 hs3_pc)
      (ordinaryStep_SH s3 .x12 .x0 (30#12) (by
        rw [hsh0_addr]; exact c_accessValid_ofNat _ 2 (by omega) (by omega)))
  have hs4_mem : s4.mem =
      (s3.setHalfword (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 30)) 0#16).mem := by
    simp only [s4, execInstrBr, hsh0_addr, c_getReg_x0, c_mem_setPC]; rfl
  have hs4_pres : MemPreservedOutside s s4 (C_TD + levelBase (lvlIdx + 2) + 96 * q)
      (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) := by
    have h02 : MemPreservedOutside s s2 (C_TD + levelBase (lvlIdx + 2) + 96 * q)
        (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) :=
      MemPreservedOutside.of_mem_eq hm2 _ _
    have h23 : MemPreservedOutside s2 s3 (C_TD + levelBase (lvlIdx + 2) + 96 * q)
        (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) :=
      memPreserved_writeBits s2 _ raw0 (by omega)
    have h34 : MemPreservedOutside s3 s4 (C_TD + levelBase (lvlIdx + 2) + 96 * q)
        (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) :=
      ((memPreserved_setHalfword s3 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 30) 0#16
        (by omega) (by omega)).mono (by omega) (by omega)).trans (MemPreservedOutside.of_mem_eq hs4_mem _ _)
    exact (h02.trans h23).trans h34
  have hs4_dig0 : readBuffer s4 (C_TD + levelBase (lvlIdx + 2) + 96 * q) 32 =
      nodeVal c96 msg salts (lvlIdx + 2) (2 * q) := by
    rw [readBuffer_of_mem_eq hs4_mem, sh_zero_mask240 s3 _ (by omega) (by omega), writeBits_readBuffer_digest]
    have h4 : 2 * (2 * q) = 4 * q := by omega
    rw [show raw0 = c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (2 * (2 * q)))
      (nodeVal c96 msg salts (lvlIdx + 1) (2 * (2 * q) + 1))) by rw [h4]]
    exact nodeVal_bin_masked c96 msg salts lvlIdx (2 * q) (by omega) (by omega)
  -- Second call + mask240 (steps 4..7)
  let s5 := execInstrBr s4 (.ADDI .x10 .x10 (96#12))
  let s6 := execInstrBr s5 (.ADDI .x12 .x12 (32#12))
  let raw1 := c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (4 * q + 2))
    (nodeVal c96 msg salts (lvlIdx + 1) (4 * q + 3)))
  let s7 := writeBits s6 (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32)) raw1
  let s8 := execInstrBr s7 (.SH .x12 .x0 (30#12))
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 5)) := pc_step_idx s4 (basePc + 4) hs4_pc
  have hs6_pc : s6.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 6)) := pc_step_idx s5 (basePc + 5) hs5_pc
  have hs7_pc : s7.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 7)) := pc_step_idx s6 (basePc + 6) hs6_pc
  have hs8_pc : s8.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 8)) := pc_step_idx s7 (basePc + 7) hs7_pc
  have hm6 : s6.mem = s4.mem := (mem_exec_ADDI s5 .x12 .x12 (32#12)).trans (mem_exec_ADDI s4 .x10 .x10 (96#12))
  have hs6_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s6.getReg r = s.getReg r := fun r h10 h12 => by
    have h6 : s6.getReg r = s5.getReg r := by
      simp only [s6, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
    have h5 : s5.getReg r = s4.getReg r := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm h10)]
    exact (h6.trans h5).trans (hs4_reg_other r h10 h12)
  have hs8_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s8.getReg r = s.getReg r := fun r h10 h12 =>
    ((reg_exec_SH s7 _ _ _ r).trans (writeBits_register s6 _ raw1 r)).trans (hs6_reg_other r h10 h12)
  have hs5_a0 : s5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + 1)) := by
    have hs4_a0 : s4.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q)) :=
      ((reg_exec_SH s3 _ _ _ .x10).trans (writeBits_register s2 _ raw0 .x10)).trans hs2_a0
    simp only [s5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs4_a0,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs6_a0 : s6.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + 1)) := by
    simp only [s6, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs5_a0]
  have hs6_a2 : s6.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) := by
    have hs5_a2 : s5.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q) := by
      have h54 : s5.getReg .x12 = s4.getReg .x12 := by
        simp only [s5, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide)]
      exact h54.trans ((reg_exec_SH s3 _ _ _ .x12).trans hs3_a2)
    simp only [s6, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs5_a2,
      add_signExtend12_ofNat_small _ 32 (by omega)]
  have hs6_in : readBuffer s6 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + 1)) 96 =
      binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (4 * q + 2))
        (nodeVal c96 msg salts (lvlIdx + 1) (4 * q + 3)) := by
    rw [readBuffer_of_mem_eq hm6, hs4_pres.readBuffer_eq (by omega) (by omega),
      readBuffer_binary_of_zero_gap s _ (hsrcGap 1 (by omega))]
    have h2 := hsrc 2 (by omega); have h3 := hsrc 3 (by omega)
    rw [show gapOffset (4 * q + 2) = 96 * (2 * q + 1) by rw [show 4 * q + 2 = 2 * (2 * q + 1) by omega, gapOffset_even]] at h2
    rw [show gapOffset (4 * q + 3) = 96 * (2 * q + 1) + 32 by rw [show 4 * q + 3 = 2 * (2 * q + 1) + 1 by omega, gapOffset_odd],
        ← Nat.add_assoc] at h3
    rw [h2, h3]
  have hst4 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (hfetch 4 (by omega) s4 hs4_pc) rfl
  have hst5 : DetRun oracle (submission.image .commit) s5 1 s6 1 0 :=
    DetRun.step1 (hfetch 5 (by omega) s5 hs5_pc) rfl
  have hst6 : DetRun oracle (submission.image .commit) s6 1 s7 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s6)
      (hfetch 6 (by omega) s6 hs6_pc)
      (by rw [hs6_reg_other .x5 (by decide) (by decide)]; exact hx5)
      (by rw [hs6_reg_other .x11 (by decide) (by decide)]; exact hx11)
      (by rw [hs6_reg_other .x13 (by decide) (by decide)]; exact hx13)
      (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + 1)) (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32)
      hs6_a0 hs6_a2 (by omega) (by omega) (by omega) (by omega) raw1 (by rw [hs6_in])
  have hs7_a2 : s7.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) :=
    (writeBits_register s6 _ raw1 .x12).trans hs6_a2
  have hsh1_addr : s7.getReg .x12 + signExtend12 (30#12) =
      BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 62) := by
    rw [hs7_a2, add_signExtend12_ofNat_small _ 30 (by omega)]
  have hst7 : DetRun oracle (submission.image .commit) s7 1 s8 1 0 :=
    DetRun.step1 (hfetch 7 (by omega) s7 hs7_pc)
      (ordinaryStep_SH s7 .x12 .x0 (30#12) (by
        rw [hsh1_addr]; exact c_accessValid_ofNat _ 2 (by omega) (by omega)))
  have hs8_mem : s8.mem =
      (s7.setHalfword (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 62)) 0#16).mem := by
    simp only [s8, execInstrBr, hsh1_addr, c_getReg_x0, c_mem_setPC]; rfl
  have hs48_pres : MemPreservedOutside s4 s8 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32)
      (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) := by
    have h46 : MemPreservedOutside s4 s6 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32)
        (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) :=
      MemPreservedOutside.of_mem_eq hm6 _ _
    have h67 : MemPreservedOutside s6 s7 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32)
        (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) :=
      memPreserved_writeBits s6 _ raw1 (by omega)
    have h78 : MemPreservedOutside s7 s8 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32)
        (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) :=
      ((memPreserved_setHalfword s7 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 62) 0#16
        (by omega) (by omega)).mono (by omega) (by omega)).trans (MemPreservedOutside.of_mem_eq hs8_mem _ _)
    exact (h46.trans h67).trans h78
  refine ⟨s8,
    ((((((hst0.trans hst1).trans hst2).trans hst3).trans hst4).trans hst5).trans hst6).trans hst7,
    hs8_pc, hs8_reg_other,
    ((reg_exec_SH s7 _ _ _ .x10).trans (writeBits_register s6 _ raw1 .x10)).trans hs6_a0,
    (reg_exec_SH s7 _ _ _ .x12).trans hs7_a2, ?_, ?_, ?_⟩
  · rw [hs48_pres.readBuffer_eq (by omega) (by omega)]; exact hs4_dig0
  · have hm : s8.mem =
        (s7.setHalfword (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32 + 30)) 0#16).mem := by
      have : C_TD + levelBase (lvlIdx + 2) + 96 * q + 62 = C_TD + levelBase (lvlIdx + 2) + 96 * q + 32 + 30 := by omega
      rw [← this]; exact hs8_mem
    rw [readBuffer_of_mem_eq hm, sh_zero_mask240 s7 _ (by omega) (by omega), writeBits_readBuffer_digest]
    have h4a : 2 * (2 * q + 1) = 4 * q + 2 := by omega
    have h4b : 2 * (2 * q + 1) + 1 = 4 * q + 3 := by omega
    rw [show raw1 = c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (2 * (2 * q + 1)))
      (nodeVal c96 msg salts (lvlIdx + 1) (2 * (2 * q + 1) + 1))) by rw [h4b, h4a]]
    exact nodeVal_bin_masked c96 msg salts lvlIdx (2 * q + 1) (by omega) (by omega)
  · exact (hs4_pres.mono (le_refl _) (by omega)).trans (hs48_pres.mono (by omega) (le_refl _))

/-- Stage A setup (words `4191..4194`): computes bulk end pointer `x19`. -/
private theorem commit_bin_stageA_setup (oracle : Oracle)
    (lvlIdx calls chunks : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 128)
    (h9 : MachineState)
    (hpc2642 : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * 4191))
    (hx10 : h9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 96))
    (hx22 : h9.getReg .x22 = BitVec.ofNat 64 chunks) :
    ∃ b3,
      DetRun oracle (submission.image .commit) h9 4 b3 4 0 ∧
      b3.pc = BitVec.ofNat 64 (0x1000 + 4 * 4195) ∧
      b3.mem = h9.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x19 → b3.getReg r = h9.getReg r) ∧
      b3.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks) - 96) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  let b0 := execInstrBr h9 (.SLLI .x6 .x22 (12#6))
  let b1 := execInstrBr b0 (.SLLI .x7 .x22 (13#6))
  let b2 := execInstrBr b1 (.ADD .x6 .x6 .x7)
  let b3 := execInstrBr b2 (.ADD .x19 .x10 .x6)
  have hb0_pc : b0.pc = BitVec.ofNat 64 (0x1000 + 4 * 4192) := pc_step_idx h9 4191 hpc2642
  have hb1_pc : b1.pc = BitVec.ofNat 64 (0x1000 + 4 * 4193) := pc_step_idx b0 4192 hb0_pc
  have hb2_pc : b2.pc = BitVec.ofNat 64 (0x1000 + 4 * 4194) := pc_step_idx b1 4193 hb1_pc
  have hb3_pc : b3.pc = BitVec.ofNat 64 (0x1000 + 4 * 4195) := pc_step_idx b2 4194 hb2_pc
  have hb_run : DetRun oracle (submission.image .commit) h9 4 b3 4 0 := by
    have sA0 : DetRun oracle (submission.image .commit) h9 1 b0 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hpc2642 rfl
    have sA1 : DetRun oracle (submission.image .commit) b0 1 b1 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hb0_pc rfl
    have sA2 : DetRun oracle (submission.image .commit) b1 1 b2 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hb1_pc rfl
    have sA3 : DetRun oracle (submission.image .commit) b2 1 b3 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hb2_pc rfl
    exact ((sA0.trans sA1).trans sA2).trans sA3
  have hb3_mem : b3.mem = h9.mem :=
    (((mem_exec_ADD b2 _ _ _).trans (mem_exec_ADD b1 _ _ _)).trans (mem_exec_SLLI b0 _ _ _)).trans
      (mem_exec_SLLI h9 _ _ _)
  have hb3_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x19 → b3.getReg r = h9.getReg r := fun r h6 h7 h19 => by
    simp only [b3, b2, b1, b0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x19 r (Ne.symm h19), getReg_setReg_ne' .x6 r (Ne.symm h6),
      getReg_setReg_ne' .x7 r (Ne.symm h7)]
  have hb3_x19 : b3.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks) - 96) := by
    have hb0_x6 : b0.getReg .x6 = BitVec.ofNat 64 (chunks * 2 ^ 12) := by
      simp only [b0, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hx22]
      exact bv64_shiftLeft_ofNat chunks 12 (by omega)
    have hb1_x7 : b1.getReg .x7 = BitVec.ofNat 64 (chunks * 2 ^ 13) := by
      have : b0.getReg .x22 = BitVec.ofNat 64 chunks := by
        simp only [b0, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x22 (by decide), hx22]
      simp only [b1, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x7 ≠ .x0), this]
      exact bv64_shiftLeft_ofNat chunks 13 (by omega)
    have hb2_x6 : b2.getReg .x6 = BitVec.ofNat 64 (12288 * chunks) := by
      have : b1.getReg .x6 = BitVec.ofNat 64 (chunks * 2 ^ 12) := by
        simp only [b1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x7 .x6 (by decide), hb0_x6]
      simp only [b2, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), this, hb1_x7, ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hb2_x10 : b2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 96) := by
      simp only [b2, b1, b0, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x6 .x10 (by decide), getReg_setReg_ne' .x7 .x10 (by decide), hx10]
    simp only [b3, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x19 ≠ .x0), hb2_x10, hb2_x6, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  exact ⟨b3, hb_run, hb3_pc, hb3_mem, hb3_reg, hb3_x19⟩

/-- One 64-pair bulk chunk (words `4195..4707`: `513` steps, `1409` cycles, `128` calls). -/
private theorem commit_bin_stageA_chunk (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks n : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 128) (hn : n < chunks)
    (s0 sn : MachineState)
    (hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 4195))
    (hx5 : sn.getReg .x5 = 0#64) (hx11 : sn.getReg .x11 = 96#64) (hx13 : sn.getReg .x13 = 0#64)
    (hx19 : sn.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks) - 96))
    (hx10n : sn.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * n) - 96))
    (hx12n : sn.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 1) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64) 32 = 0)
    (hpresn : MemPreservedOutside s0 sn (C_TD + levelBase (lvlIdx + 2))
      (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n))) :
    ∃ sbne,
      DetRun oracle (submission.image .commit) sn 513 sbne 1409 128 ∧
      sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n + 1 < chunks then 4195 else 4708)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sbne.getReg r = sn.getReg r) ∧
      sbne.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * (n + 1)) - 96) ∧
      sbne.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * (n + 1)) - 64) ∧
      (∀ idx, 128 * n ≤ idx → idx < 128 * (n + 1) →
        readBuffer sbne (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx) ∧
      (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
        sbne.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
        sn.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
      MemPreservedOutside sn sbne (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n))
        (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * (n + 1))) := by
  have hC_TD : C_TD = 4294971424 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  have hdstSize_eq : levelSize (lvlIdx + 2) = (levelSize (lvlIdx + 1) + 1) / 2 :=
    levelSize_step (lvlIdx + 1) (by omega)
  have hsrcB := levelBase_bound (lvlIdx + 1) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 2) (by omega)
  have htb := treeBytes_eq
  have hsrcBytes := levelBytes_eq_gap (lvlIdx + 1) (by omega) (by omega)
  have hdstBytes := levelBytes_eq_gap (lvlIdx + 2) (by omega) (by omega)
  have hbase_step : levelBase (lvlIdx + 2) = levelBase (lvlIdx + 1) + levelBytes (lvlIdx + 1) := rfl
  have hpairs : ∀ m ≤ 64,
      ∃ sm,
        DetRun oracle (submission.image .commit) sn (8 * m) sm (22 * m) (2 * m) ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (4195 + 8 * m)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sm.getReg r = sn.getReg r) ∧
        sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * (64 * n + m)) - 96) ∧
        sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n + m) - 64) ∧
        (∀ idx, 128 * n ≤ idx → idx < 128 * n + 2 * m →
          readBuffer sm (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
            nodeVal c96 msg salts (lvlIdx + 2) idx) ∧
        (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
          sm.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
        MemPreservedOutside sn sm (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n))
          (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n + m)) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨sn, DetRun.refl _ _ _, hpc_in, fun _ _ _ => rfl,
        by rw [hx10n]; exact congrArg (BitVec.ofNat 64) (by omega),
        by rw [hx12n]; exact congrArg (BitVec.ofNat 64) (by omega),
        fun _ h1 h2 => by omega, fun _ _ _ _ => rfl, MemPreservedOutside.refl _ _ _⟩
    | succ m ihm =>
      obtain ⟨sm, hrunm, hpcm, hregm, hx10m, hx12m, hdigm, hgapm, hpresm⟩ := ihm (by omega)
      have hpres_s0 : MemPreservedOutside s0 sm (C_TD + levelBase (lvlIdx + 2))
          (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n + m)) :=
        (hpresn.mono (le_refl _) (by omega)).trans (hpresm.mono (by omega) (le_refl _))
      obtain ⟨sp, hrun1, hpcp, hregp, hx10p, hx12p, hd0p, hd1p, hpres1⟩ :=
        commit_bin_pair h768 oracle msg salts lvlIdx (4195 + 8 * m) (64 * n + m) hlvl (by omega) sm
          (fun j hj st hst => commit_fetch_bin_bulk st m j (by omega) hj hst)
          hpcm
          (by rw [hregm .x5 (by decide) (by decide)]; exact hx5)
          (by rw [hregm .x11 (by decide) (by decide)]; exact hx11)
          (by rw [hregm .x13 (by decide) (by decide)]; exact hx13)
          hx10m hx12m
          (fun j hj => by
            have hgo : gapOffset (4 * (64 * n + m) + j) + 32 ≤ levelBytes (lvlIdx + 1) :=
              gapOffset_lt_levelBytes (lvlIdx + 1) _ (by omega) (by omega) (by omega)
            rw [hpres_s0.readBuffer_eq (by omega) (by omega)]
            exact hsrc (4 * (64 * n + m) + j) (by omega))
          (fun p hp => by
            have hgap_bd : 96 * (2 * (64 * n + m) + p) + 64 + 32 ≤ levelBytes (lvlIdx + 1) := by
              rw [hsrcBytes]; omega
            rw [hpres_s0.readBuffer_eq (by omega) (by omega)]
            exact hsrcGap (2 * (64 * n + m) + p) (by omega))
      have hrun_m1 : DetRun oracle (submission.image .commit) sn (8 * (m + 1)) sp (22 * (m + 1)) (2 * (m + 1)) := by
        have h := hrunm.trans hrun1
        rw [show 8 * m + 8 = 8 * (m + 1) by omega,
            show 22 * m + 22 = 22 * (m + 1) by omega,
            show 2 * m + 2 = 2 * (m + 1) by omega] at h
        exact h
      refine ⟨sp, hrun_m1,
        by rw [hpcp]; exact congrArg (BitVec.ofNat 64) (by omega),
        fun r h10 h12 => (hregp r h10 h12).trans (hregm r h10 h12),
        by rw [hx10p]; exact congrArg (BitVec.ofNat 64) (by omega),
        by rw [hx12p]; exact congrArg (BitVec.ofNat 64) (by omega), ?_, ?_, ?_⟩
      · intro idx hlo hhi
        by_cases hold : idx < 128 * n + 2 * m
        · rw [← hdigm idx hlo hold]
          have hgo : gapOffset idx + 32 ≤ 96 * (64 * n + m) := by unfold gapOffset; omega
          exact hpres1.readBuffer_eq (by omega) (by omega)
        · by_cases hev : idx = 2 * (64 * n + m)
          · subst hev; simpa only [gapOffset_even] using hd0p
          · have hodd : idx = 2 * (64 * n + m) + 1 := by omega
            subst hodd; simpa only [gapOffset_odd, Nat.add_assoc] using hd1p
      · intro q hq j hj
        have hsep : C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j <
              C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n + m) ∨
            C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n + m) + 64 ≤
              C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j := by omega
        exact (hpres1 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)
          (by rw [hdstBytes] at hdstB; omega) hsep).trans (hgapm q hq j hj)
      · exact (hpresm.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (by omega))
  obtain ⟨sm, hrun64, hpc64, hreg64, hx10_64, hx12_64, hdig64, hgap64, hpres64⟩ := hpairs 64 (le_refl _)
  let sbne := execInstrBr sm (.BNE .x10 .x19 (6144#13))
  have hbne : DetRun oracle (submission.image .commit) sm 1 sbne 1 0 :=
    commit_step1_tail (by omega) (by omega) hpc64 rfl
  have hmem_bne : sbne.mem = sm.mem := mem_exec_BNE sm .x10 .x19 (6144#13)
  have hreg_bne : ∀ r, sbne.getReg r = sm.getReg r := reg_exec_BNE sm .x10 .x19 (6144#13)
  have hpc_end : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n + 1 < chunks then 4195 else 4708)) := by
    have hx19m : sm.getReg .x19 =
        BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks) - 96) :=
      (hreg64 .x19 (by decide) (by decide)).trans hx19
    by_cases hlt : n + 1 < chunks
    · have hne : (sm.getReg .x10 != sm.getReg .x19) = true := by
        rw [hx10_64, hx19m, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hlt, ite_true, sbne, execInstrBr, hne, pc_setPC, hpc64]
      exact pc_bne_3158
    · have heq : (sm.getReg .x10 != sm.getReg .x19) = false := by
        rw [hx10_64, hx19m, show 2 * (64 * n + 64) = 128 * chunks by omega]
        exact bne_self_eq_false _
      simp only [hlt, ite_false, sbne, execInstrBr, heq, Bool.false_eq_true, pc_setPC]
      exact pc_step_idx sm 4707 hpc64
  refine ⟨sbne, hrun64.trans hbne, hpc_end,
    fun r h10 h12 => (hreg_bne r).trans (hreg64 r h10 h12),
    by rw [hreg_bne, hx10_64]; exact congrArg (BitVec.ofNat 64) (by omega),
    by rw [hreg_bne, hx12_64]; exact congrArg (BitVec.ofNat 64) (by omega),
    fun idx hlo hhi => by rw [readBuffer_of_mem_eq hmem_bne]; exact hdig64 idx hlo (by omega),
    fun q hq j hj => by rw [getByte_of_mem_eq hmem_bne]; exact hgap64 q hq j hj,
    (hpres64.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmem_bne _ _)⟩

/-- Stage A of `commit_bin_level`: bulk 64-pair chunks (`words 4191..4707`). -/
theorem commit_bin_level_stageA (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 128)
    (s0 h9 : MachineState)
    (hh_mem : h9.mem = s0.mem)
    (hh9_pc : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then 4191 else 4708)))
    (hx5 : h9.getReg .x5 = 0#64) (hx11 : h9.getReg .x11 = 96#64) (hx13 : h9.getReg .x13 = 0#64)
    (hx10 : h9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 96))
    (hx12 : h9.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) - 64))
    (hx22 : h9.getReg .x22 = BitVec.ofNat 64 chunks)
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 1) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64) 32 = 0) :
    ∃ sb,
      DetRun oracle (submission.image .commit) h9
        (if 0 < chunks then 4 + 513 * chunks else 0) sb
        (if 0 < chunks then 4 + 1409 * chunks else 0) (128 * chunks) ∧
      sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 4708) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → sb.getReg r = h9.getReg r) ∧
      sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks) - 96) ∧
      sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks) - 64) ∧
      (∀ idx < 128 * chunks,
        readBuffer sb (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx) ∧
      (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
        sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 2))
        (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 2) (by omega)
  have htb := treeBytes_eq
  by_cases hch : 0 < chunks
  · have hpc2642 : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * 4191) := by
      simpa only [hch, ite_true] using hh9_pc
    obtain ⟨b3, hb_setup, hb3_pc, hb3_mem', hb3_reg, hb3_x19⟩ :=
      commit_bin_stageA_setup oracle lvlIdx calls chunks hlvl hcalls hchunks h9 hpc2642 hx10 hx22
    have hb3_mem : b3.mem = s0.mem := hb3_mem'.trans hh_mem
    have hbulk : ∀ n ≤ chunks,
        ∃ sn,
          DetRun oracle (submission.image .commit) b3 (513 * n) sn (1409 * n) (128 * n) ∧
          sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < chunks then 4195 else 4708)) ∧
          (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sn.getReg r = b3.getReg r) ∧
          sn.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * n) - 96) ∧
          sn.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n) - 64) ∧
          (∀ idx < 128 * n, readBuffer sn (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
            nodeVal c96 msg salts (lvlIdx + 2) idx) ∧
          (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
            sn.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
            s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
          MemPreservedOutside s0 sn (C_TD + levelBase (lvlIdx + 2))
            (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n)) := by
      intro n hn; induction n with
      | zero =>
        exact ⟨b3, DetRun.refl _ _ _, by simpa only [hch, ite_true] using hb3_pc, fun _ _ _ => rfl,
          by rw [hb3_reg .x10 (by decide) (by decide) (by decide), hx10]; exact congrArg (BitVec.ofNat 64) (by omega),
          by rw [hb3_reg .x12 (by decide) (by decide) (by decide), hx12]; exact congrArg (BitVec.ofNat 64) (by omega),
          fun _ h => (Nat.not_lt_zero _ h).elim,
          fun _ _ _ _ => getByte_of_mem_eq hb3_mem _,
          MemPreservedOutside.of_mem_eq hb3_mem _ _⟩
      | succ n ih =>
        obtain ⟨sn, hrunn, hpcn, hregn, hx10n, hx12n, hdign, hgapn, hpresn⟩ := ih (by omega)
        have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 4195) := by
          simpa only [show n < chunks by omega, ite_true] using hpcn
        obtain ⟨sbne, hrunC, hpc_end, hregC, hx10C, hx12C, hdigC, hgapC, hpresC⟩ :=
          commit_bin_stageA_chunk h768 oracle msg salts lvlIdx calls chunks n hlvl hcalls hchunks
            (by omega) s0 sn hpc_in
            ((hregn .x5 (by decide) (by decide)).trans ((hb3_reg .x5 (by decide) (by decide) (by decide)).trans hx5))
            ((hregn .x11 (by decide) (by decide)).trans ((hb3_reg .x11 (by decide) (by decide) (by decide)).trans hx11))
            ((hregn .x13 (by decide) (by decide)).trans ((hb3_reg .x13 (by decide) (by decide) (by decide)).trans hx13))
            ((hregn .x19 (by decide) (by decide)).trans hb3_x19)
            hx10n hx12n hsrc hsrcGap hpresn
        have hrun_n1 : DetRun oracle (submission.image .commit) b3 (513 * (n + 1)) sbne
            (1409 * (n + 1)) (128 * (n + 1)) := by
          have h := hrunn.trans hrunC
          rw [show 513 * n + 513 = 513 * (n + 1) by omega,
              show 1409 * n + 1409 = 1409 * (n + 1) by omega,
              show 128 * n + 128 = 128 * (n + 1) by omega] at h
          exact h
        refine ⟨sbne, hrun_n1, hpc_end, fun r h10 h12 => (hregC r h10 h12).trans (hregn r h10 h12),
          hx10C, hx12C, ?_, fun q hq j hj => (hgapC q hq j hj).trans (hgapn q hq j hj),
          (hpresn.mono (le_refl _) (by omega)).trans (hpresC.mono (by omega) (le_refl _))⟩
        intro idx hidx
        by_cases hold : idx < 128 * n
        · rw [← hdign idx hold]
          have hgo : gapOffset idx + 32 ≤ 96 * (64 * n) := by unfold gapOffset; omega
          exact hpresC.readBuffer_eq (by omega) (by omega)
        · exact hdigC idx (by omega) hidx
    obtain ⟨sb, hrunb, hpcb, hregb, hx10b, hx12b, hdigb, hgapb, hpresb⟩ := hbulk chunks (le_refl _)
    have hrun_tot : DetRun oracle (submission.image .commit) h9
        (if 0 < chunks then 4 + 513 * chunks else 0) sb
        (if 0 < chunks then 4 + 1409 * chunks else 0) (128 * chunks) := by
      have h := hb_setup.trans hrunb
      rw [Nat.zero_add] at h
      simpa only [hch, ite_true] using h
    exact ⟨sb, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpcb,
      fun r h6 h7 h10 h12 h19 => (hregb r h10 h12).trans (hb3_reg r h6 h7 h19),
      hx10b, hx12b, hdigb, hgapb, hpresb⟩
  · have hch0 : chunks = 0 := by omega
    have hpc3159 : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * 4708) := by
      simpa only [hch, ite_false] using hh9_pc
    have hrun0 : DetRun oracle (submission.image .commit) h9
        (if 0 < chunks then 4 + 513 * chunks else 0) h9
        (if 0 < chunks then 4 + 1409 * chunks else 0) (128 * chunks) := by
      rw [show (if 0 < chunks then 4 + 513 * chunks else 0) = 0 by simp only [hch, ite_false],
          show (if 0 < chunks then 4 + 1409 * chunks else 0) = 0 by simp only [hch, ite_false],
          show 128 * chunks = 0 by omega]
      exact DetRun.refl oracle (submission.image .commit) h9
    exact ⟨h9, hrun0, hpc3159, fun _ _ _ _ _ _ => rfl,
      by rw [hx10]; exact congrArg (BitVec.ofNat 64) (by omega),
      by rw [hx12]; exact congrArg (BitVec.ofNat 64) (by omega),
      fun _ h => by omega,
      fun _ _ _ _ => getByte_of_mem_eq hh_mem _,
      by rw [show C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks) =
            C_TD + levelBase (lvlIdx + 2) by omega]
         exact MemPreservedOutside.of_mem_eq hh_mem _ _⟩

private theorem commit_fetch_bin_tail_pair (st : MachineState) (j : Nat) (hj : j < 8)
    (hst : st.pc = BitVec.ofNat 64 (0x1000 + 4 * (4711 + j))) :
    fetch (submission.image .commit) st = some (binPairInstr j) := by
  have h := commit_fetch_commitTailInstr st (4711 + j) (by omega) (by omega) hst
  interval_cases j <;> simpa only [binPairInstr, commitTailInstr] using h

/-- Stage B setup (words `4708..4710`): computes `x22 = remPairs` and branches to `4711` or `4721`. -/
private theorem commit_bin_stageB_setup (oracle : Oracle)
    (lvlIdx calls remPairs : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hrem : remPairs = (calls % 128) / 2)
    (sb : MachineState)
    (hpcB : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 4708))
    (hx20B : sb.getReg .x20 = BitVec.ofNat 64 calls) :
    ∃ t2,
      DetRun oracle (submission.image .commit) sb 3 t2 3 0 ∧
      t2.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < remPairs then 4711 else 4721)) ∧
      t2.mem = sb.mem ∧
      t2.getReg .x22 = BitVec.ofNat 64 remPairs ∧
      (∀ r : Reg, r ≠ .x22 → t2.getReg r = sb.getReg r) := by
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  let t0 := execInstrBr sb (.ANDI .x22 .x20 (127#12))
  let t1 := execInstrBr t0 (.SRLI .x22 .x22 (1#6))
  let t2 := execInstrBr t1 (.BEQ .x22 .x0 (44#13))
  have ht0_pc : t0.pc = BitVec.ofNat 64 (0x1000 + 4 * 4709) := pc_step_idx sb 4708 hpcB
  have ht1_pc : t1.pc = BitVec.ofNat 64 (0x1000 + 4 * 4710) := pc_step_idx t0 4709 ht0_pc
  have ht_run3 : DetRun oracle (submission.image .commit) sb 3 t2 3 0 := by
    have rt0 : DetRun oracle (submission.image .commit) sb 1 t0 1 0 :=
      commit_step1_tail (by omega) (by omega) hpcB rfl
    have rt1 : DetRun oracle (submission.image .commit) t0 1 t1 1 0 :=
      commit_step1_tail (by omega) (by omega) ht0_pc rfl
    have rt2 : DetRun oracle (submission.image .commit) t1 1 t2 1 0 :=
      commit_step1_tail (by omega) (by omega) ht1_pc rfl
    exact (rt0.trans rt1).trans rt2
  have ht1_x22 : t1.getReg .x22 = BitVec.ofNat 64 remPairs := by
    have ht0_x22 : t0.getReg .x22 = BitVec.ofNat 64 (calls % 128) := by
      simp only [t0, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), hx20B]
      exact bv64_and_127 calls (by omega)
    simp only [t1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), ht0_x22]
    exact (bv64_ushiftRight_ofNat (calls % 128) 1 (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have ht2_mem : t2.mem = sb.mem :=
    ((mem_exec_BEQ t1 _ _ _).trans (mem_exec_SRLI t0 _ _ _)).trans (mem_exec_ANDI sb _ _ _)
  have ht2_reg : ∀ r : Reg, r ≠ .x22 → t2.getReg r = sb.getReg r := fun r hr => by
    rw [reg_exec_BEQ t1 _ _ _ r]
    simp only [t1, t0, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 r (Ne.symm hr)]
  have ht2_pc : t2.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < remPairs then 4711 else 4721)) := by
    by_cases hrp : 0 < remPairs
    · have hne0 : (t1.getReg .x22 == t1.getReg .x0) = false := by
        rw [ht1_x22, c_getReg_x0, beq_eq_false_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hrp, ite_true, t2, execInstrBr, hne0, Bool.false_eq_true, ite_false, pc_setPC]
      exact pc_step_idx t1 4710 ht1_pc
    · have hrp0 : remPairs = 0 := by omega
      have heq0 : (t1.getReg .x22 == t1.getReg .x0) = true := by
        rw [ht1_x22, hrp0, c_getReg_x0]; exact beq_self_eq_true _
      simp only [hrp, ite_false, t2, execInstrBr, heq0, ite_true, pc_setPC, ht1_pc]
      exact pc_beq_3161
  exact ⟨t2, ht_run3, ht2_pc, ht2_mem, (reg_exec_BEQ t1 _ _ _ .x22).trans ht1_x22, ht2_reg⟩

/-- Stage B decrement step (word `4719`: `ADDI x22, x22, -1`). -/
private theorem commit_bin_stageB_dec (oracle : Oracle) (remPairs m : Nat)
    (hm : m < remPairs) (sp : MachineState)
    (hsp_pc : sp.pc = BitVec.ofNat 64 (0x1000 + 4 * 4719))
    (hx22p : sp.getReg .x22 = BitVec.ofNat 64 (remPairs - m)) :
    ∃ sdec,
      DetRun oracle (submission.image .commit) sp 1 sdec 1 0 ∧
      sdec.pc = BitVec.ofNat 64 (0x1000 + 4 * 4720) ∧
      sdec.mem = sp.mem ∧
      sdec.getReg .x22 = BitVec.ofNat 64 (remPairs - (m + 1)) ∧
      (∀ r : Reg, r ≠ .x22 → sdec.getReg r = sp.getReg r) := by
  let sdec := execInstrBr sp (.ADDI .x22 .x22 (4095#12))
  have hsdec_pc : sdec.pc = BitVec.ofNat 64 (0x1000 + 4 * 4720) := by
    change (sp.setReg .x22 _ |>.setPC (sp.pc + 4)).pc = _
    rw [pc_setPC]
    exact pc_step_idx sp 4719 hsp_pc
  have hdec_run : DetRun oracle (submission.image .commit) sp 1 sdec 1 0 :=
    commit_step1_tail (by omega) (by omega) hsp_pc rfl
  have hsdec_x22 : sdec.getReg .x22 = BitVec.ofNat 64 (remPairs - (m + 1)) := by
    simp only [sdec, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), hx22p]
    exact (c_bv64_add_neg1 (remPairs - m) (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have hreg : ∀ r : Reg, r ≠ .x22 → sdec.getReg r = sp.getReg r := fun r hr => by
    simp only [sdec, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 r (Ne.symm hr)]
  exact ⟨sdec, hdec_run, hsdec_pc, mem_exec_ADDI sp _ _ _, hsdec_x22, hreg⟩

/-- Stage B branch step (word `4720`: `BNE x22, x0, -36`). -/
private theorem commit_bin_stageB_bne (oracle : Oracle) (remPairs m : Nat)
    (hrem_lt : remPairs < 2 ^ 64) (sdec : MachineState)
    (hsdec_pc : sdec.pc = BitVec.ofNat 64 (0x1000 + 4 * 4720))
    (hsdec_x22 : sdec.getReg .x22 = BitVec.ofNat 64 (remPairs - (m + 1))) :
    ∃ sbne,
      DetRun oracle (submission.image .commit) sdec 1 sbne 1 0 ∧
      sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if m + 1 < remPairs then 4711 else 4721)) ∧
      sbne.mem = sdec.mem ∧
      (∀ r : Reg, sbne.getReg r = sdec.getReg r) := by
  let sbne := execInstrBr sdec (.BNE .x22 .x0 (8156#13))
  have hbne_run : DetRun oracle (submission.image .commit) sdec 1 sbne 1 0 :=
    commit_step1_tail (by omega) (by omega) hsdec_pc rfl
  have hpc_end : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if m + 1 < remPairs then 4711 else 4721)) := by
    by_cases hlt : m + 1 < remPairs
    · have hne : (sdec.getReg .x22 != sdec.getReg .x0) = true := by
        rw [hsdec_x22, c_getReg_x0, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hlt, ite_true, sbne, execInstrBr, hne, pc_setPC, hsdec_pc]
      exact pc_bne_3171
    · have heq : (sdec.getReg .x22 != sdec.getReg .x0) = false := by
        rw [hsdec_x22, c_getReg_x0, show remPairs - (m + 1) = 0 by omega]
        exact bne_self_eq_false _
      simp only [hlt, ite_false, sbne, execInstrBr, heq, Bool.false_eq_true, pc_setPC]
      exact pc_step_idx sdec 4720 hsdec_pc
  exact ⟨sbne, hbne_run, hpc_end, mem_exec_BNE sdec _ _ _, reg_exec_BNE sdec _ _ _⟩

/-- Stage B decrement + branch latch (words `4719..4720`: `2` steps, `2` cycles, `0` calls). -/
private theorem commit_bin_stageB_latch (oracle : Oracle) (remPairs m : Nat)
    (hm : m < remPairs) (hrem_lt : remPairs < 2 ^ 64)
    (sp : MachineState)
    (hsp_pc : sp.pc = BitVec.ofNat 64 (0x1000 + 4 * 4719))
    (hx22p : sp.getReg .x22 = BitVec.ofNat 64 (remPairs - m)) :
    ∃ sbne,
      DetRun oracle (submission.image .commit) sp 2 sbne 2 0 ∧
      sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if m + 1 < remPairs then 4711 else 4721)) ∧
      sbne.mem = sp.mem ∧
      sbne.getReg .x22 = BitVec.ofNat 64 (remPairs - (m + 1)) ∧
      (∀ r : Reg, r ≠ .x22 → sbne.getReg r = sp.getReg r) := by
  obtain ⟨sdec, hdec_run, hsdec_pc, hsdec_mem, hsdec_x22, hsdec_reg⟩ :=
    commit_bin_stageB_dec oracle remPairs m hm sp hsp_pc hx22p
  obtain ⟨sbne, hbne_run, hpc_end, hmem_bne, hreg_bne⟩ :=
    commit_bin_stageB_bne oracle remPairs m hrem_lt sdec hsdec_pc hsdec_x22
  exact ⟨sbne, hdec_run.trans hbne_run, hpc_end, hmem_bne.trans hsdec_mem,
    (hreg_bne .x22).trans hsdec_x22, fun r hr => (hreg_bne r).trans (hsdec_reg r hr)⟩

/-- One iteration of the Stage B tail-pair loop (words `4711..4720`: `10` steps, `24` cycles, `2` calls). -/
private theorem commit_bin_stageB_iter (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks remPairs m : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 128)
    (hrem : remPairs = (calls % 128) / 2) (hm : m < remPairs)
    (s0 sm : MachineState)
    (hpc_in : sm.pc = BitVec.ofNat 64 (0x1000 + 4 * 4711))
    (hx5 : sm.getReg .x5 = 0#64) (hx11 : sm.getReg .x11 = 96#64) (hx13 : sm.getReg .x13 = 0#64)
    (hx22m : sm.getReg .x22 = BitVec.ofNat 64 (remPairs - m))
    (hx10m : sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks + 2 * m) - 96))
    (hx12m : sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + m) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 1) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64) 32 = 0)
    (hpresm : MemPreservedOutside s0 sm (C_TD + levelBase (lvlIdx + 2))
      (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + m))) :
    ∃ sbne,
      DetRun oracle (submission.image .commit) sm 10 sbne 24 2 ∧
      sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if m + 1 < remPairs then 4711 else 4721)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → sbne.getReg r = sm.getReg r) ∧
      sbne.getReg .x22 = BitVec.ofNat 64 (remPairs - (m + 1)) ∧
      sbne.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks + 2 * (m + 1)) - 96) ∧
      sbne.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + (m + 1)) - 64) ∧
      readBuffer sbne (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + m)) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (2 * (64 * chunks + m)) ∧
      readBuffer sbne (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + m) + 32) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (2 * (64 * chunks + m) + 1) ∧
      MemPreservedOutside sm sbne (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + m))
        (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + m) + 64) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  have hsrcB := levelBase_bound (lvlIdx + 1) (by omega)
  have htb := treeBytes_eq
  have hsrcBytes := levelBytes_eq_gap (lvlIdx + 1) (by omega) (by omega)
  have hbase_step : levelBase (lvlIdx + 2) = levelBase (lvlIdx + 1) + levelBytes (lvlIdx + 1) := rfl
  have hcalls_ge : 128 * chunks + 2 * remPairs ≤ calls := by omega
  obtain ⟨sp, hrun1, hpcp, hregp, hx10p, hx12p, hd0p, hd1p, hpres1⟩ :=
    commit_bin_pair h768 oracle msg salts lvlIdx 4711 (64 * chunks + m) hlvl (by omega) sm
      (fun j hj st hst => commit_fetch_bin_tail_pair st j hj hst)
      hpc_in hx5 hx11 hx13
      (by rw [hx10m]; exact congrArg (BitVec.ofNat 64) (by omega)) hx12m
      (fun j hj => by
        have hgo : gapOffset (4 * (64 * chunks + m) + j) + 32 ≤ levelBytes (lvlIdx + 1) :=
          gapOffset_lt_levelBytes (lvlIdx + 1) _ (by omega) (by omega) (by omega)
        rw [hpresm.readBuffer_eq (by omega) (by omega)]
        exact hsrc (4 * (64 * chunks + m) + j) (by omega))
      (fun p hp => by
        have hgap_bd : 96 * (2 * (64 * chunks + m) + p) + 64 + 32 ≤ levelBytes (lvlIdx + 1) := by
          rw [hsrcBytes]; omega
        rw [hpresm.readBuffer_eq (by omega) (by omega)]
        exact hsrcGap (2 * (64 * chunks + m) + p) (by omega))
  have hsp_pc : sp.pc = BitVec.ofNat 64 (0x1000 + 4 * 4719) := hpcp
  obtain ⟨sbne, hlatch, hpc_end, hmem_end, hx22_end, hreg_end⟩ :=
    commit_bin_stageB_latch oracle remPairs m hm (by omega) sp hsp_pc
      ((hregp .x22 (by decide) (by decide)).trans hx22m)
  refine ⟨sbne, hrun1.trans hlatch, hpc_end,
    fun r h10 h12 h22 => (hreg_end r h22).trans (hregp r h10 h12),
    hx22_end,
    by rw [hreg_end .x10 (by decide), hx10p]; exact congrArg (BitVec.ofNat 64) (by omega),
    by rw [hreg_end .x12 (by decide), hx12p]; exact congrArg (BitVec.ofNat 64) (by omega),
    by rw [readBuffer_of_mem_eq hmem_end]; exact hd0p,
    by rw [readBuffer_of_mem_eq hmem_end]; exact hd1p,
    hpres1.trans (MemPreservedOutside.of_mem_eq hmem_end _ _)⟩

/-- Stage B of `commit_bin_level`: tail pairs (`words 4708..4720`). -/
theorem commit_bin_level_stageB (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks remPairs : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 128)
    (hrem : remPairs = (calls % 128) / 2)
    (s0 sb : MachineState)
    (hpcB : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 4708))
    (hx5B : sb.getReg .x5 = 0#64) (hx11B : sb.getReg .x11 = 96#64) (hx13B : sb.getReg .x13 = 0#64)
    (hx20B : sb.getReg .x20 = BitVec.ofNat 64 calls)
    (hx10B : sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks) - 96))
    (hx12B : sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 1) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64) 32 = 0)
    (hdigB : ∀ idx < 128 * chunks,
      readBuffer sb (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hgapB : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
      sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)))
    (hpresB : MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 2))
      (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks))) :
    ∃ st,
      DetRun oracle (submission.image .commit) sb (3 + 10 * remPairs) st (3 + 24 * remPairs) (2 * remPairs) ∧
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * 4721) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → st.getReg r = sb.getReg r) ∧
      st.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks + 2 * remPairs) - 96) ∧
      st.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + remPairs) - 64) ∧
      (∀ idx < 128 * chunks + 2 * remPairs,
        readBuffer st (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx) ∧
      (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
        st.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 st (C_TD + levelBase (lvlIdx + 2))
        (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + remPairs)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  have hdstSize_eq : levelSize (lvlIdx + 2) = (levelSize (lvlIdx + 1) + 1) / 2 :=
    levelSize_step (lvlIdx + 1) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 2) (by omega)
  have htb := treeBytes_eq
  have hdstBytes := levelBytes_eq_gap (lvlIdx + 2) (by omega) (by omega)
  obtain ⟨t2, ht_run3, ht2_pc, ht2_mem, ht2_x22, ht2_reg⟩ :=
    commit_bin_stageB_setup oracle lvlIdx calls remPairs hlvl hcalls hrem sb hpcB hx20B
  by_cases hrp : 0 < remPairs
  · have htloop : ∀ m ≤ remPairs,
        ∃ sm,
          DetRun oracle (submission.image .commit) t2 (10 * m) sm (24 * m) (2 * m) ∧
          sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (if m < remPairs then 4711 else 4721)) ∧
          (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → sm.getReg r = sb.getReg r) ∧
          sm.getReg .x22 = BitVec.ofNat 64 (remPairs - m) ∧
          sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks + 2 * m) - 96) ∧
          sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + m) - 64) ∧
          (∀ idx < 128 * chunks + 2 * m, readBuffer sm (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
            nodeVal c96 msg salts (lvlIdx + 2) idx) ∧
          (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
            sm.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
            s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
          MemPreservedOutside s0 sm (C_TD + levelBase (lvlIdx + 2))
            (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + m)) := by
      intro m hm; induction m with
      | zero =>
        exact ⟨t2, DetRun.refl _ _ _, ht2_pc, fun r _ _ h22 => ht2_reg r h22,
          by rw [ht2_x22]; exact congrArg (BitVec.ofNat 64) (by omega),
          by rw [ht2_reg .x10 (by decide), hx10B]; exact congrArg (BitVec.ofNat 64) (by omega),
          by rw [ht2_reg .x12 (by decide), hx12B]; exact congrArg (BitVec.ofNat 64) (by omega),
          fun idx hidx => by rw [readBuffer_of_mem_eq ht2_mem]; exact hdigB idx (by omega),
          fun q hq j hj => by rw [getByte_of_mem_eq ht2_mem]; exact hgapB q hq j hj,
          by rw [show C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + 0) =
                C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks) by omega]
             exact hpresB.trans (MemPreservedOutside.of_mem_eq ht2_mem _ _)⟩
      | succ m ihm =>
        obtain ⟨sm, hrunm, hpcm, hregm, hx22m, hx10m, hx12m, hdigm, hgapm, hpresm⟩ := ihm (by omega)
        have hpc_in : sm.pc = BitVec.ofNat 64 (0x1000 + 4 * 4711) := by
          simpa only [show m < remPairs by omega, ite_true] using hpcm
        obtain ⟨sbne, hrunI, hpc_end, hregI, hx22I, hx10I, hx12I, hd0I, hd1I, hpresI⟩ :=
          commit_bin_stageB_iter h768 oracle msg salts lvlIdx calls chunks remPairs m hlvl hcalls hchunks hrem
            (by omega) s0 sm hpc_in
            ((hregm .x5 (by decide) (by decide) (by decide)).trans hx5B)
            ((hregm .x11 (by decide) (by decide) (by decide)).trans hx11B)
            ((hregm .x13 (by decide) (by decide) (by decide)).trans hx13B)
            hx22m hx10m hx12m hsrc hsrcGap hpresm
        have hrun_m1 : DetRun oracle (submission.image .commit) t2 (10 * (m + 1)) sbne
            (24 * (m + 1)) (2 * (m + 1)) := by
          have h := hrunm.trans hrunI
          rw [show 10 * m + 10 = 10 * (m + 1) by omega,
              show 24 * m + 24 = 24 * (m + 1) by omega,
              show 2 * m + 2 = 2 * (m + 1) by omega] at h
          exact h
        refine ⟨sbne, hrun_m1, hpc_end,
          fun r h10 h12 h22 => (hregI r h10 h12 h22).trans (hregm r h10 h12 h22),
          hx22I, hx10I, hx12I, ?_, ?_,
          (hpresm.mono (le_refl _) (by omega)).trans (hpresI.mono (by omega) (by omega))⟩
        · intro idx hidx
          by_cases hold : idx < 128 * chunks + 2 * m
          · rw [← hdigm idx hold]
            have hgo : gapOffset idx + 32 ≤ 96 * (64 * chunks + m) := by unfold gapOffset; omega
            have hdst_bd : 96 * (64 * chunks + m) ≤ levelBytes (lvlIdx + 2) := by
              rw [hdstBytes, hdstSize_eq]; omega
            exact hpresI.readBuffer_eq (by omega) (by omega)
          · by_cases hev : idx = 2 * (64 * chunks + m)
            · subst hev; simpa only [gapOffset_even] using hd0I
            · have hodd : idx = 2 * (64 * chunks + m) + 1 := by omega
              subst hodd; simpa only [gapOffset_odd, Nat.add_assoc] using hd1I
        · intro q hq j hj
          have hsep : C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j <
                C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + m) ∨
              C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + m) + 64 ≤
                C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j := by omega
          exact (hpresI (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)
            (by rw [hdstBytes] at hdstB; omega) hsep).trans (hgapm q hq j hj)
    obtain ⟨st, hrunT, hpcT, hregT, _, hx10T, hx12T, hdigT, hgapT, hpresT⟩ := htloop remPairs (le_refl _)
    have hrun_all : DetRun oracle (submission.image .commit) sb (3 + 10 * remPairs) st
        (3 + 24 * remPairs) (2 * remPairs) := by
      have h := ht_run3.trans hrunT
      rw [Nat.zero_add] at h
      exact h
    exact ⟨st, hrun_all, by simpa only [Nat.lt_irrefl, ite_false] using hpcT,
      hregT, hx10T, hx12T, hdigT, hgapT, hpresT⟩
  · have hrp0 : remPairs = 0 := by omega
    have hrun0 : DetRun oracle (submission.image .commit) sb (3 + 10 * remPairs) t2
        (3 + 24 * remPairs) (2 * remPairs) := by
      rw [show 3 + 10 * remPairs = 3 by omega,
          show 3 + 24 * remPairs = 3 by omega,
          show 2 * remPairs = 0 by omega]
      exact ht_run3
    refine ⟨t2, hrun0, by simpa only [hrp, ite_false] using ht2_pc, fun r _ _ h22 => ht2_reg r h22,
      by rw [ht2_reg .x10 (by decide), hx10B]; exact congrArg (BitVec.ofNat 64) (by omega),
      by rw [ht2_reg .x12 (by decide), hx12B]; exact congrArg (BitVec.ofNat 64) (by omega),
      fun idx hidx => by rw [readBuffer_of_mem_eq ht2_mem]; exact hdigB idx (by omega),
      fun q hq j hj => by rw [getByte_of_mem_eq ht2_mem]; exact hgapB q hq j hj,
      by rw [show C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + remPairs) =
            C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks) by omega]
         exact hpresB.trans (MemPreservedOutside.of_mem_eq ht2_mem _ _)⟩

end CommitGolfCandidate
