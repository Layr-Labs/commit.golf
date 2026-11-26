import CommitGolfCandidate.MoonCommitExec

/-! Exact RV64IM execution proofs for binary tree levels of the v4 (`148K`) `commit` image:
- Cost accounting & tree-node masking helpers for Phase 3A (`L2..L5`, 240-bit, `U_BIN=2048`)
  and Phase 3B (`L6..L23`, 238-bit, `U_BIN238=128`)
- `commit_bin_pair` (240-bit), `commit_mask238_step` + `commit_bin238_pair` (238-bit)
- Stage A (Phase 3A `1024`-pair chunks with 2-instr `BEQ+JAL` latch, Phase 3B `64`-pair chunks)
  and unified parameterized Stage B (tail pairs) instantiated for both phases. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-- Exact cost accounting for Phase 3A (240-bit masked, `U_BIN = 2048`) binary level `lvlIdx < 4`. -/
def binLevelSteps (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 1) / 2
  let prom := levelSize (lvlIdx + 1) % 2
  let chunks := calls / 2048
  let remPairs := (calls % 2048) / 2
  let oddCall := calls % 2
  (if 0 < chunks then 10 else 11) + (if 0 < chunks then 3 + 8194 * chunks else 0) +
    (3 + 10 * remPairs) + (if oddCall = 1 then 7 + 9 * prom else 3 + 8 * prom) +
    (if lvlIdx + 1 < 4 then 3 else 2)

def binLevelCycles (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 1) / 2
  let prom := levelSize (lvlIdx + 1) % 2
  let chunks := calls / 2048
  let remPairs := (calls % 2048) / 2
  let oddCall := calls % 2
  (if 0 < chunks then 10 else 11) + (if 0 < chunks then 3 + 22530 * chunks else 0) +
    (3 + 24 * remPairs) + (if oddCall = 1 then 14 + 9 * prom else 3 + 8 * prom) +
    (if lvlIdx + 1 < 4 then 3 else 2)

def binLevelCalls (lvlIdx : Nat) : Nat :=
  levelSize (lvlIdx + 1) / 2

/-- Exact cost accounting for Phase 3B (238-bit masked) binary level `4 ≤ lvlIdx < 22`. -/
def bin238LevelSteps (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 1) / 2
  let prom := levelSize (lvlIdx + 1) % 2
  let chunks := calls / 128
  let remPairs := (calls % 128) / 2
  let oddCall := calls % 2
  10 + (if 0 < chunks then 4 + 769 * chunks else 0) + (3 + 14 * remPairs) +
    (if oddCall = 1 then 9 + 9 * prom else 3 + 8 * prom) + 2

def bin238LevelCycles (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 1) / 2
  let prom := levelSize (lvlIdx + 1) % 2
  let chunks := calls / 128
  let remPairs := (calls % 128) / 2
  let oddCall := calls % 2
  10 + (if 0 < chunks then 4 + 1665 * chunks else 0) + (3 + 28 * remPairs) +
    (if oddCall = 1 then 16 + 9 * prom else 3 + 8 * prom) + 2

def bin238LevelCalls (lvlIdx : Nat) : Nat :=
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
    (lvlIdx idx : Nat) (hlt : 2 * idx + 1 < levelSize (lvlIdx + 1)) (hlvl4 : lvlIdx < 4) :
    mask240 (c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (2 * idx))
      (nodeVal c96 msg salts (lvlIdx + 1) (2 * idx + 1)))) =
      nodeVal c96 msg salts (lvlIdx + 2) idx := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (lvlIdx + 2) idx = _
  rw [nodeValFromLeaves]
  dsimp only
  unfold maskLevel
  have h1 : ¬ (lvlIdx + 2 < 2 ∨ lvlIdx + 2 = 24) := by omega
  have h2 : lvlIdx + 2 < 6 := by omega
  simp only [hlt, ite_true, h1, ite_false, h2]
  rfl

theorem nodeVal_bin_masked238 (c96 : Comp96) (msg : Message) (salts : Index → Salt192)
    (lvlIdx idx : Nat) (hlt : 2 * idx + 1 < levelSize (lvlIdx + 1))
    (hlo : 4 ≤ lvlIdx) (hhi : lvlIdx < 22) :
    mask238 (c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (2 * idx))
      (nodeVal c96 msg salts (lvlIdx + 1) (2 * idx + 1)))) =
      nodeVal c96 msg salts (lvlIdx + 2) idx := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (lvlIdx + 2) idx = _
  rw [nodeValFromLeaves]
  dsimp only
  unfold maskLevel
  have h1 : ¬ (lvlIdx + 2 < 2 ∨ lvlIdx + 2 = 24) := by omega
  have h2 : ¬ (lvlIdx + 2 < 6) := by omega
  simp only [hlt, ite_true, h1, ite_false, h2]
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
  unfold maskLevel
  have hlt : 2 * 0 + 1 < levelSize (22 + 1) := by
    rw [show 22 + 1 = 23 from rfl, levelSize_23]; omega
  have h24 : 22 + 2 < 2 ∨ (22 + 2 : Nat) = 24 := Or.inr rfl
  simp only [hlt, h24, ite_true]
  rfl

/-- Single-step wrappers for the non-parametric v4 slices (`commitMid2`, `commitMid3`, `commitTail`). -/
theorem commit_step1_mid2 {oracle : Oracle} {s : MachineState} {idx : Nat} {ins : Instr}
    (hlo : 139314 ≤ idx) (hhi : idx < 139344)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hins : commitMid2Instr idx = .base ins)
    (hstep : ordinaryStep s (.base ins) = some (execInstrBr s ins) := by rfl)
    (hcyc : instructionCycles (.base ins) = 1 := by rfl) :
    DetRun oracle (submission.image .commit) s 1 (execInstrBr s ins) 1 0 := by
  have hf := commit_fetch_commitMid2Instr s idx hlo hhi hpc
  rw [hins] at hf
  exact DetRun.step1 hf hstep hcyc

theorem commit_step1_mid3 {oracle : Oracle} {s : MachineState} {idx : Nat} {ins : Instr}
    (hlo : 147536 ≤ idx) (hhi : idx < 147597)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hins : commitMid3Instr idx = .base ins)
    (hstep : ordinaryStep s (.base ins) = some (execInstrBr s ins) := by rfl)
    (hcyc : instructionCycles (.base ins) = 1 := by rfl) :
    DetRun oracle (submission.image .commit) s 1 (execInstrBr s ins) 1 0 := by
  have hf := commit_fetch_commitMid3Instr s idx hlo hhi hpc
  rw [hins] at hf
  exact DetRun.step1 hf hstep hcyc

theorem commit_step1_tail {oracle : Oracle} {s : MachineState} {idx : Nat} {ins : Instr}
    (hlo : 148365 ≤ idx) (hhi : idx < 148434)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hins : commitTailInstr idx = .base ins)
    (hstep : ordinaryStep s (.base ins) = some (execInstrBr s ins) := by rfl)
    (hcyc : instructionCycles (.base ins) = 1 := by rfl) :
    DetRun oracle (submission.image .commit) s 1 (execInstrBr s ins) 1 0 := by
  have hf := commit_fetch_commitTailInstr s idx hlo hhi hpc
  rw [hins] at hf
  exact DetRun.step1 hf hstep hcyc

theorem c_mem_exec_AND (s : MachineState) (rd rs1 rs2 : Reg) :
    (execInstrBr s (.AND rd rs1 rs2)).mem = s.mem := by cases rd <;> rfl

/-! ### 1. Isolated Branch Targets for Stage A and Stage B (Phase 3A and Phase 3B) -/

private theorem pc_jal_147537 :
    BitVec.ofNat 64 (0x1000 + 4 * 147537) + signExtend21 (2064380#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 139344) := by decide

private theorem pc_beq_147540 :
    BitVec.ofNat 64 (0x1000 + 4 * 147540) + signExtend13 (44#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 147551) := by decide

private theorem pc_bne_147550 :
    BitVec.ofNat 64 (0x1000 + 4 * 147550) + signExtend13 (8156#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 147541) := by decide

private theorem pc_bne_148365 :
    BitVec.ofNat 64 (0x1000 + 4 * 148365) + signExtend13 (5120#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 147597) := by decide

private theorem pc_beq_148368 :
    BitVec.ofNat 64 (0x1000 + 4 * 148368) + signExtend13 (60#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 148383) := by decide

private theorem pc_bne_148382 :
    BitVec.ofNat 64 (0x1000 + 4 * 148382) + signExtend13 (8140#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 148369) := by decide

/-! ### 2. 240-Bit Masked Binary Pair (`binPairInstr`: 8 steps, 22 cycles, 2 calls) -/

theorem commit_bin_pair (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx basePc q : Nat) (hlvl : lvlIdx < 4) (hq : 2 * q + 1 < levelSize (lvlIdx + 1) / 2)
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
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
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
    exact nodeVal_bin_masked c96 msg salts lvlIdx (2 * q) (by omega) hlvl
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
  have hs8_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s8.getReg r = s.getReg r :=
    fun r _ h10 h12 => ((reg_exec_SH s7 _ _ _ r).trans (writeBits_register s6 _ raw1 r)).trans (hs6_reg_other r h10 h12)
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
    exact nodeVal_bin_masked c96 msg salts lvlIdx (2 * q + 1) (by omega) hlvl
  · exact (hs4_pres.mono (le_refl _) (by omega)).trans (hs48_pres.mono (by omega) (le_refl _))

/-! ### 3. 238-Bit Mask Step & Masked Binary Pair (`bin238PairInstr`: 12 steps, 26 cycles, 2 calls) -/

/-- Three-instruction 238-bit digest mask: `ld x6, 24(x12); and x6, x6, x27; sd x12, x6, 24`. -/
theorem commit_mask238_step (oracle : Oracle) (s : MachineState)
    (basePc addr : Nat) (halign : addr % 8 = 0) (hbd : addr + 32 ≤ MEMORY_BYTES)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 addr)
    (hx27 : s.getReg .x27 = mask238Word)
    (hfetch0 : fetch (submission.image .commit) s = some (.base (.LD .x6 .x12 (24#12))))
    (hfetch1 : ∀ st : MachineState, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) →
      fetch (submission.image .commit) st = some (.base (.AND .x6 .x6 .x27)))
    (hfetch2 : ∀ st : MachineState, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) →
      fetch (submission.image .commit) st = some (.base (.SD .x12 .x6 (24#12)))) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 3 s' 3 0 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) ∧
      (∀ r : Reg, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      readBuffer s' addr 32 = mask238 (readBuffer s addr 32) ∧
      MemPreservedOutside s s' (addr + 24) (addr + 32) := by
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let s1 := execInstrBr s (.LD .x6 .x12 (24#12))
  let s2 := execInstrBr s1 (.AND .x6 .x6 .x27)
  let s3 := execInstrBr s2 (.SD .x12 .x6 (24#12))
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) := pc_step_idx s basePc hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) := pc_step_idx s1 (basePc + 1) hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) := pc_step_idx s2 (basePc + 2) hs2_pc
  have haddr0 : s.getReg .x12 + signExtend12 (24#12) = BitVec.ofNat 64 (addr + 24) := by
    rw [hx12, add_signExtend12_ofNat_small _ 24 (by omega)]
  have hs2_reg : ∀ r : Reg, r ≠ .x6 → s2.getReg r = s.getReg r := fun r hr => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm hr)]
  have haddr2 : s2.getReg .x12 + signExtend12 (24#12) = BitVec.ofNat 64 (addr + 24) := by
    rw [hs2_reg .x12 (by decide), hx12, add_signExtend12_ofNat_small _ 24 (by omega)]
  have hst0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 hfetch0
      (ordinaryStep_LD s .x6 .x12 (24#12) (by rw [haddr0]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hst1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (hfetch1 s1 hs1_pc) rfl
  have hst2 : DetRun oracle (submission.image .commit) s2 1 s3 1 0 :=
    DetRun.step1 (hfetch2 s2 hs2_pc)
      (ordinaryStep_SD s2 .x12 .x6 (24#12) (by rw [haddr2]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hm2 : s2.mem = s.mem := (c_mem_exec_AND s1 _ _ _).trans (mem_exec_LD s _ _ _)
  have hs1_x6 : s1.getReg .x6 = s.getMem (BitVec.ofNat 64 (addr + 24)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), haddr0]
  have hs1_x27 : s1.getReg .x27 = mask238Word := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x6 .x27 (by decide), hx27]
  have hs2_x6 : s2.getReg .x6 = s.getMem (BitVec.ofNat 64 (addr + 24)) &&& mask238Word := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hs1_x6, hs1_x27]
  have hs3_mem : s3.mem =
      (s.setMem (BitVec.ofNat 64 (addr + 24)) (s.getMem (BitVec.ofNat 64 (addr + 24)) &&& mask238Word)).mem := by
    simp only [s3, execInstrBr, haddr2, hs2_x6, c_mem_setPC, MachineState.setMem, hm2]
  refine ⟨s3, (hst0.trans hst1).trans hst2, hs3_pc,
    fun r hr => (reg_exec_SD s2 _ _ _ r).trans (hs2_reg r hr), ?_, ?_⟩
  · rw [readBuffer_of_mem_eq hs3_mem]
    exact sd_and_mask238 s addr halign (by omega)
  · exact (memPreserved_setMem s (addr + 24) _ (by omega) (by omega)).trans
      (MemPreservedOutside.of_mem_eq hs3_mem _ _)

theorem commit_bin238_pair (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx basePc q : Nat) (hlo : 4 ≤ lvlIdx) (hhi : lvlIdx < 22)
    (hq : 2 * q + 1 < levelSize (lvlIdx + 1) / 2) (s : MachineState)
    (hfetch : ∀ j < 12, ∀ st : MachineState,
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + j)) →
      fetch (submission.image .commit) st = some (bin238PairInstr j))
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx27 : s.getReg .x27 = mask238Word)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q) - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q - 64))
    (hsrc : ∀ j < 4, readBuffer s (C_TD + levelBase (lvlIdx + 1) + gapOffset (4 * q + j)) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) (4 * q + j))
    (hsrcGap : ∀ p < 2, readBuffer s (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + p) + 64) 32 = 0) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 12 s' 26 2 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 12)) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
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
  -- Call 0 (steps 0..2) + mask238 (steps 3..5)
  let s1 := execInstrBr s (.ADDI .x10 .x10 (96#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (64#12))
  let raw0 := c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (4 * q))
    (nodeVal c96 msg salts (lvlIdx + 1) (4 * q + 1)))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q)) raw0
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) := pc_step_idx s basePc hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) := pc_step_idx s1 (basePc + 1) hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) := pc_step_idx s2 (basePc + 2) hs2_pc
  have hm2 : s2.mem = s.mem := (mem_exec_ADDI s1 .x12 .x12 (64#12)).trans (mem_exec_ADDI s .x10 .x10 (96#12))
  have hs2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s2.getReg r = s.getReg r := fun r h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
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
  have hs3_a0 : s3.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q)) :=
    (writeBits_register s2 _ raw0 .x10).trans hs2_a0
  have hs3_a2 : s3.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q) :=
    (writeBits_register s2 _ raw0 .x12).trans hs2_a2
  obtain ⟨s4, hm_run0, hs4_pc', hs4_reg3, hs4_mask0, hs4_mpres0⟩ :=
    commit_mask238_step oracle s3 (basePc + 3) (C_TD + levelBase (lvlIdx + 2) + 96 * q)
      (by omega) (by omega) hs3_pc hs3_a2
      ((writeBits_register s2 _ raw0 .x27).trans ((hs2_reg_other .x27 (by decide) (by decide)).trans hx27))
      (hfetch 3 (by omega) s3 hs3_pc)
      (fun st hst => hfetch 4 (by omega) st (by simpa only [Nat.add_assoc] using hst))
      (fun st hst => hfetch 5 (by omega) st (by simpa only [Nat.add_assoc] using hst))
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 6)) := by
    simpa only [Nat.add_assoc] using hs4_pc'
  have hs4_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s4.getReg r = s.getReg r :=
    fun r h6 h10 h12 => ((hs4_reg3 r h6).trans (writeBits_register s2 _ raw0 r)).trans (hs2_reg_other r h10 h12)
  have hs4_pres : MemPreservedOutside s s4 (C_TD + levelBase (lvlIdx + 2) + 96 * q)
      (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) :=
    ((MemPreservedOutside.of_mem_eq hm2 _ _).trans (memPreserved_writeBits s2 _ raw0 (by omega))).trans
      (hs4_mpres0.mono (by omega) (le_refl _))
  have hs4_dig0 : readBuffer s4 (C_TD + levelBase (lvlIdx + 2) + 96 * q) 32 =
      nodeVal c96 msg salts (lvlIdx + 2) (2 * q) := by
    rw [hs4_mask0, writeBits_readBuffer_digest]
    have h4 : 2 * (2 * q) = 4 * q := by omega
    rw [show raw0 = c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (2 * (2 * q)))
      (nodeVal c96 msg salts (lvlIdx + 1) (2 * (2 * q) + 1))) by rw [h4]]
    exact nodeVal_bin_masked238 c96 msg salts lvlIdx (2 * q) (by omega) hlo hhi
  -- Call 1 (steps 6..8) + mask238 (steps 9..11)
  let s5 := execInstrBr s4 (.ADDI .x10 .x10 (96#12))
  let s6 := execInstrBr s5 (.ADDI .x12 .x12 (32#12))
  let raw1 := c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (4 * q + 2))
    (nodeVal c96 msg salts (lvlIdx + 1) (4 * q + 3)))
  let s7 := writeBits s6 (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32)) raw1
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 7)) := pc_step_idx s4 (basePc + 6) hs4_pc
  have hs6_pc : s6.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 8)) := pc_step_idx s5 (basePc + 7) hs5_pc
  have hs7_pc : s7.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 9)) := pc_step_idx s6 (basePc + 8) hs6_pc
  have hm6 : s6.mem = s4.mem := (mem_exec_ADDI s5 .x12 .x12 (32#12)).trans (mem_exec_ADDI s4 .x10 .x10 (96#12))
  have hs6_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s6.getReg r = s.getReg r :=
    fun r h6 h10 h12 => by
      have h64 : s6.getReg r = s4.getReg r := by
        simp only [s6, s5, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
      exact h64.trans (hs4_reg_other r h6 h10 h12)
  have hs5_a0 : s5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + 1)) := by
    have hs4_a0 : s4.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q)) :=
      (hs4_reg3 .x10 (by decide)).trans hs3_a0
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
      exact h54.trans ((hs4_reg3 .x12 (by decide)).trans hs3_a2)
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
  have hst6 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (hfetch 6 (by omega) s4 hs4_pc) rfl
  have hst7 : DetRun oracle (submission.image .commit) s5 1 s6 1 0 :=
    DetRun.step1 (hfetch 7 (by omega) s5 hs5_pc) rfl
  have hst8 : DetRun oracle (submission.image .commit) s6 1 s7 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s6)
      (hfetch 8 (by omega) s6 hs6_pc)
      (by rw [hs6_reg_other .x5 (by decide) (by decide) (by decide)]; exact hx5)
      (by rw [hs6_reg_other .x11 (by decide) (by decide) (by decide)]; exact hx11)
      (by rw [hs6_reg_other .x13 (by decide) (by decide) (by decide)]; exact hx13)
      (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + 1)) (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32)
      hs6_a0 hs6_a2 (by omega) (by omega) (by omega) (by omega) raw1 (by rw [hs6_in])
  have hs7_a0 : s7.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + 1)) :=
    (writeBits_register s6 _ raw1 .x10).trans hs6_a0
  have hs7_a2 : s7.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) :=
    (writeBits_register s6 _ raw1 .x12).trans hs6_a2
  obtain ⟨s8, hm_run1, hs8_pc', hs8_reg7, hs8_mask1, hs8_mpres1⟩ :=
    commit_mask238_step oracle s7 (basePc + 9) (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32)
      (by omega) (by omega) hs7_pc hs7_a2
      ((writeBits_register s6 _ raw1 .x27).trans ((hs6_reg_other .x27 (by decide) (by decide) (by decide)).trans hx27))
      (hfetch 9 (by omega) s7 hs7_pc)
      (fun st hst => hfetch 10 (by omega) st (by simpa only [Nat.add_assoc] using hst))
      (fun st hst => hfetch 11 (by omega) st (by simpa only [Nat.add_assoc] using hst))
  have hs48_pres : MemPreservedOutside s4 s8 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32)
      (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) :=
    ((MemPreservedOutside.of_mem_eq hm6 _ _).trans (memPreserved_writeBits s6 _ raw1 (by omega))).trans
      (hs8_mpres1.mono (by omega) (by omega))
  refine ⟨s8,
    ((((((hst0.trans hst1).trans hst2).trans hm_run0).trans hst6).trans hst7).trans hst8).trans hm_run1,
    by simpa only [Nat.add_assoc] using hs8_pc',
    fun r h6 h10 h12 => ((hs8_reg7 r h6).trans (writeBits_register s6 _ raw1 r)).trans (hs6_reg_other r h6 h10 h12),
    (hs8_reg7 .x10 (by decide)).trans hs7_a0,
    (hs8_reg7 .x12 (by decide)).trans hs7_a2, ?_, ?_, ?_⟩
  · rw [hs48_pres.readBuffer_eq (by omega) (by omega)]; exact hs4_dig0
  · rw [hs8_mask1, writeBits_readBuffer_digest]
    have h4a : 2 * (2 * q + 1) = 4 * q + 2 := by omega
    have h4b : 2 * (2 * q + 1) + 1 = 4 * q + 3 := by omega
    rw [show raw1 = c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (2 * (2 * q + 1)))
      (nodeVal c96 msg salts (lvlIdx + 1) (2 * (2 * q + 1) + 1))) by rw [h4b, h4a]]
    exact nodeVal_bin_masked238 c96 msg salts lvlIdx (2 * q + 1) (by omega) hlo hhi
  · exact (hs4_pres.mono (le_refl _) (by omega)).trans (hs48_pres.mono (by omega) (le_refl _))

/-! ### 4. Parameterized Stage A (Bulk 64-Pair Chunks) -/

private theorem commit_bin_stageA_setup_gen (oracle : Oracle)
    (pcSetup lvlIdx calls chunks : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 128)
    (h9 : MachineState)
    (hpcS : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * pcSetup))
    (hx10 : h9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 96))
    (hx22 : h9.getReg .x22 = BitVec.ofNat 64 chunks)
    (hf0 : fetch (submission.image .commit) h9 = some (.base (.SLLI .x6 .x22 (12#6))))
    (hf1 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 1)) →
      fetch (submission.image .commit) st = some (.base (.SLLI .x7 .x22 (13#6))))
    (hf2 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 2)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x6 .x6 .x7)))
    (hf3 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 3)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x19 .x10 .x6))) :
    ∃ b3,
      DetRun oracle (submission.image .commit) h9 4 b3 4 0 ∧
      b3.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 4)) ∧
      b3.mem = h9.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x19 → b3.getReg r = h9.getReg r) ∧
      b3.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks) - 96) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  let b0 := execInstrBr h9 (.SLLI .x6 .x22 (12#6))
  let b1 := execInstrBr b0 (.SLLI .x7 .x22 (13#6))
  let b2 := execInstrBr b1 (.ADD .x6 .x6 .x7)
  let b3 := execInstrBr b2 (.ADD .x19 .x10 .x6)
  have hb0_pc : b0.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 1)) := pc_step_idx h9 pcSetup hpcS
  have hb1_pc : b1.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 2)) := pc_step_idx b0 (pcSetup + 1) hb0_pc
  have hb2_pc : b2.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 3)) := pc_step_idx b1 (pcSetup + 2) hb1_pc
  have hb3_pc : b3.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 4)) := pc_step_idx b2 (pcSetup + 3) hb2_pc
  have hb_run : DetRun oracle (submission.image .commit) h9 4 b3 4 0 :=
    (((DetRun.step1 hf0 rfl).trans (DetRun.step1 (hf1 b0 hb0_pc) rfl)).trans
      (DetRun.step1 (hf2 b1 hb1_pc) rfl)).trans (DetRun.step1 (hf3 b2 hb2_pc) rfl)
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

private theorem commit_bin_stageA_chunk_gen (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (pcBulk pcExit pairSteps pairCyc : Nat) (bneImm : BitVec 13)
    (hbne_exit : pcBulk + pairSteps * 64 + 1 = pcExit)
    (hbne_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * 64)) + signExtend13 bneImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcBulk))
    (lvlIdx calls chunks n : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 128) (hn : n < chunks)
    (s0 sn : MachineState)
    (hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * pcBulk))
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
      (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n)))
    (hpair : ∀ (m q : Nat), m < 64 → 2 * q + 1 < calls → ∀ (sm : MachineState),
      sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * m)) →
      sm.getReg .x5 = 0#64 → sm.getReg .x11 = 96#64 → sm.getReg .x13 = 0#64 →
      sm.getReg .x27 = sn.getReg .x27 →
      sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q) - 96) →
      sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q - 64) →
      (∀ j < 4, readBuffer sm (C_TD + levelBase (lvlIdx + 1) + gapOffset (4 * q + j)) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) (4 * q + j)) →
      (∀ p < 2, readBuffer sm (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + p) + 64) 32 = 0) →
      ∃ sp,
        DetRun oracle (submission.image .commit) sm pairSteps sp pairCyc 2 ∧
        sp.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * m + pairSteps)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sp.getReg r = sm.getReg r) ∧
        sp.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + 1)) ∧
        sp.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 2) + 96 * q) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (2 * q) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (2 * q + 1) ∧
        MemPreservedOutside sm sp (C_TD + levelBase (lvlIdx + 2) + 96 * q)
          (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64))
    (hbne_fetch : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * 64)) →
      fetch (submission.image .commit) st = some (.base (.BNE .x10 .x19 bneImm))) :
    ∃ sbne,
      DetRun oracle (submission.image .commit) sn (pairSteps * 64 + 1) sbne (pairCyc * 64 + 1) 128 ∧
      sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n + 1 < chunks then pcBulk else pcExit)) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sbne.getReg r = sn.getReg r) ∧
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
        DetRun oracle (submission.image .commit) sn (pairSteps * m) sm (pairCyc * m) (2 * m) ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * m)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sm.getReg r = sn.getReg r) ∧
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
      exact ⟨sn, DetRun.refl _ _ _, by simpa only [Nat.mul_zero, Nat.add_zero] using hpc_in,
        fun _ _ _ _ => rfl,
        by rw [hx10n]; exact congrArg (BitVec.ofNat 64) (by omega),
        by rw [hx12n]; exact congrArg (BitVec.ofNat 64) (by omega),
        fun _ h1 h2 => by omega, fun _ _ _ _ => rfl, MemPreservedOutside.refl _ _ _⟩
    | succ m ihm =>
      obtain ⟨sm, hrunm, hpcm, hregm, hx10m, hx12m, hdigm, hgapm, hpresm⟩ := ihm (by omega)
      have hpres_s0 : MemPreservedOutside s0 sm (C_TD + levelBase (lvlIdx + 2))
          (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * n + m)) :=
        (hpresn.mono (le_refl _) (by omega)).trans (hpresm.mono (by omega) (le_refl _))
      obtain ⟨sp, hrun1, hpcp, hregp, hx10p, hx12p, hd0p, hd1p, hpres1⟩ :=
        hpair m (64 * n + m) (by omega) (by omega) sm hpcm
          ((hregm .x5 (by decide) (by decide) (by decide)).trans hx5)
          ((hregm .x11 (by decide) (by decide) (by decide)).trans hx11)
          ((hregm .x13 (by decide) (by decide) (by decide)).trans hx13)
          (hregm .x27 (by decide) (by decide) (by decide))
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
      have hrun_m1 : DetRun oracle (submission.image .commit) sn (pairSteps * (m + 1)) sp
          (pairCyc * (m + 1)) (2 * (m + 1)) := by
        have h := hrunm.trans hrun1
        rw [← Nat.mul_succ pairSteps m, ← Nat.mul_succ pairCyc m,
            show 2 * m + 2 = 2 * (m + 1) by omega] at h
        exact h
      refine ⟨sp, hrun_m1,
        by rw [hpcp, Nat.add_assoc, ← Nat.mul_succ],
        fun r h6 h10 h12 => (hregp r h6 h10 h12).trans (hregm r h6 h10 h12),
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
  let sbne := execInstrBr sm (.BNE .x10 .x19 bneImm)
  have hbne : DetRun oracle (submission.image .commit) sm 1 sbne 1 0 :=
    DetRun.step1 (hbne_fetch sm hpc64) rfl
  have hmem_bne : sbne.mem = sm.mem := mem_exec_BNE sm .x10 .x19 bneImm
  have hreg_bne : ∀ r, sbne.getReg r = sm.getReg r := reg_exec_BNE sm .x10 .x19 bneImm
  have hpc_end : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n + 1 < chunks then pcBulk else pcExit)) := by
    have hx19m : sm.getReg .x19 =
        BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks) - 96) :=
      (hreg64 .x19 (by decide) (by decide) (by decide)).trans hx19
    by_cases hlt : n + 1 < chunks
    · have hne : (sm.getReg .x10 != sm.getReg .x19) = true := by
        rw [hx10_64, hx19m, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hlt, ite_true, sbne, execInstrBr, hne, pc_setPC, hpc64]
      exact hbne_pc
    · have heq : (sm.getReg .x10 != sm.getReg .x19) = false := by
        rw [hx10_64, hx19m, show 2 * (64 * n + 64) = 128 * chunks by omega]
        exact bne_self_eq_false _
      simp only [hlt, ite_false, sbne, execInstrBr, heq, Bool.false_eq_true, pc_setPC]
      rw [← hbne_exit]
      exact pc_step_idx sm (pcBulk + pairSteps * 64) hpc64
  refine ⟨sbne, hrun64.trans hbne, hpc_end,
    fun r h6 h10 h12 => (hreg_bne r).trans (hreg64 r h6 h10 h12),
    by rw [hreg_bne, hx10_64]; exact congrArg (BitVec.ofNat 64) (by omega),
    by rw [hreg_bne, hx12_64]; exact congrArg (BitVec.ofNat 64) (by omega),
    fun idx hlo hhi => (readBuffer_of_mem_eq hmem_bne _ _).trans (hdig64 idx hlo (by omega)),
    fun q hq j hj => (getByte_of_mem_eq hmem_bne _).trans (hgap64 q hq j hj),
    (hpres64.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmem_bne _ _)⟩

private theorem commit_bin_stageA_gen (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (pcSetup pcBulk pcExit pairSteps pairCyc : Nat) (bneImm : BitVec 13)
    (hsetup_bulk : pcSetup + 4 = pcBulk)
    (hbne_exit : pcBulk + pairSteps * 64 + 1 = pcExit)
    (hbne_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * 64)) + signExtend13 bneImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcBulk))
    (lvlIdx calls chunks : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 128)
    (s0 h9 : MachineState)
    (hh_mem : h9.mem = s0.mem)
    (hh9_pc : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then pcSetup else pcExit)))
    (hx5 : h9.getReg .x5 = 0#64) (hx11 : h9.getReg .x11 = 96#64) (hx13 : h9.getReg .x13 = 0#64)
    (hx10 : h9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 96))
    (hx12 : h9.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) - 64))
    (hx22 : h9.getReg .x22 = BitVec.ofNat 64 chunks)
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 1) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64) 32 = 0)
    (hfS0 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * pcSetup) →
      fetch (submission.image .commit) st = some (.base (.SLLI .x6 .x22 (12#6))))
    (hfS1 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 1)) →
      fetch (submission.image .commit) st = some (.base (.SLLI .x7 .x22 (13#6))))
    (hfS2 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 2)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x6 .x6 .x7)))
    (hfS3 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 3)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x19 .x10 .x6)))
    (hpair : ∀ (m q : Nat), m < 64 → 2 * q + 1 < calls → ∀ (sm : MachineState),
      sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * m)) →
      sm.getReg .x5 = 0#64 → sm.getReg .x11 = 96#64 → sm.getReg .x13 = 0#64 →
      sm.getReg .x27 = h9.getReg .x27 →
      sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q) - 96) →
      sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q - 64) →
      (∀ j < 4, readBuffer sm (C_TD + levelBase (lvlIdx + 1) + gapOffset (4 * q + j)) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) (4 * q + j)) →
      (∀ p < 2, readBuffer sm (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + p) + 64) 32 = 0) →
      ∃ sp,
        DetRun oracle (submission.image .commit) sm pairSteps sp pairCyc 2 ∧
        sp.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * m + pairSteps)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sp.getReg r = sm.getReg r) ∧
        sp.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + 1)) ∧
        sp.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 2) + 96 * q) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (2 * q) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (2 * q + 1) ∧
        MemPreservedOutside sm sp (C_TD + levelBase (lvlIdx + 2) + 96 * q)
          (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64))
    (hbne_fetch : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * 64)) →
      fetch (submission.image .commit) st = some (.base (.BNE .x10 .x19 bneImm))) :
    ∃ sb,
      DetRun oracle (submission.image .commit) h9
        (if 0 < chunks then 4 + (pairSteps * 64 + 1) * chunks else 0) sb
        (if 0 < chunks then 4 + (pairCyc * 64 + 1) * chunks else 0) (128 * chunks) ∧
      sb.pc = BitVec.ofNat 64 (0x1000 + 4 * pcExit) ∧
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
  · have hpcS : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * pcSetup) := by
      simpa only [hch, ite_true] using hh9_pc
    obtain ⟨b3, hb_setup, hb3_pc', hb3_mem', hb3_reg, hb3_x19⟩ :=
      commit_bin_stageA_setup_gen oracle pcSetup lvlIdx calls chunks hlvl hcalls hchunks h9 hpcS hx10 hx22
        (hfS0 h9 hpcS) hfS1 hfS2 hfS3
    have hb3_pc : b3.pc = BitVec.ofNat 64 (0x1000 + 4 * pcBulk) := by rw [← hsetup_bulk]; exact hb3_pc'
    have hb3_mem : b3.mem = s0.mem := hb3_mem'.trans hh_mem
    have hbulk : ∀ n ≤ chunks,
        ∃ sn,
          DetRun oracle (submission.image .commit) b3 ((pairSteps * 64 + 1) * n) sn
            ((pairCyc * 64 + 1) * n) (128 * n) ∧
          sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < chunks then pcBulk else pcExit)) ∧
          (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sn.getReg r = b3.getReg r) ∧
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
        exact ⟨b3, DetRun.refl _ _ _, by simpa only [hch, ite_true] using hb3_pc, fun _ _ _ _ => rfl,
          by rw [hb3_reg .x10 (by decide) (by decide) (by decide), hx10]; exact congrArg (BitVec.ofNat 64) (by omega),
          by rw [hb3_reg .x12 (by decide) (by decide) (by decide), hx12]; exact congrArg (BitVec.ofNat 64) (by omega),
          fun _ h => (Nat.not_lt_zero _ h).elim,
          fun _ _ _ _ => getByte_of_mem_eq hb3_mem _,
          MemPreservedOutside.of_mem_eq hb3_mem _ _⟩
      | succ n ih =>
        obtain ⟨sn, hrunn, hpcn, hregn, hx10n, hx12n, hdign, hgapn, hpresn⟩ := ih (by omega)
        have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * pcBulk) := by
          simpa only [show n < chunks by omega, ite_true] using hpcn
        have hsn_x27 : sn.getReg .x27 = h9.getReg .x27 :=
          (hregn .x27 (by decide) (by decide) (by decide)).trans (hb3_reg .x27 (by decide) (by decide) (by decide))
        obtain ⟨sbne, hrunC, hpc_end, hregC, hx10C, hx12C, hdigC, hgapC, hpresC⟩ :=
          commit_bin_stageA_chunk_gen h768 oracle msg salts pcBulk pcExit pairSteps pairCyc bneImm
            hbne_exit hbne_pc lvlIdx calls chunks n hlvl hcalls hchunks (by omega) s0 sn hpc_in
            ((hregn .x5 (by decide) (by decide) (by decide)).trans ((hb3_reg .x5 (by decide) (by decide) (by decide)).trans hx5))
            ((hregn .x11 (by decide) (by decide) (by decide)).trans ((hb3_reg .x11 (by decide) (by decide) (by decide)).trans hx11))
            ((hregn .x13 (by decide) (by decide) (by decide)).trans ((hb3_reg .x13 (by decide) (by decide) (by decide)).trans hx13))
            ((hregn .x19 (by decide) (by decide) (by decide)).trans hb3_x19)
            hx10n hx12n hsrc hsrcGap hpresn
            (fun m q hm hq sm hp h5 h11 h13 h27 => hpair m q hm hq sm hp h5 h11 h13 (h27.trans hsn_x27))
            hbne_fetch
        have hrun_n1 : DetRun oracle (submission.image .commit) b3 ((pairSteps * 64 + 1) * (n + 1)) sbne
            ((pairCyc * 64 + 1) * (n + 1)) (128 * (n + 1)) := by
          have h := hrunn.trans hrunC
          rw [← Nat.mul_succ (pairSteps * 64 + 1) n, ← Nat.mul_succ (pairCyc * 64 + 1) n,
              show 128 * n + 128 = 128 * (n + 1) by omega] at h
          exact h
        refine ⟨sbne, hrun_n1, hpc_end, fun r h6 h10 h12 => (hregC r h6 h10 h12).trans (hregn r h6 h10 h12),
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
        (if 0 < chunks then 4 + (pairSteps * 64 + 1) * chunks else 0) sb
        (if 0 < chunks then 4 + (pairCyc * 64 + 1) * chunks else 0) (128 * chunks) := by
      have h := hb_setup.trans hrunb
      rw [Nat.zero_add] at h
      simpa only [hch, ite_true] using h
    exact ⟨sb, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpcb,
      fun r h6 h7 h10 h12 h19 => (hregb r h6 h10 h12).trans (hb3_reg r h6 h7 h19),
      hx10b, hx12b, hdigb, hgapb, hpresb⟩
  · have hch0 : chunks = 0 := by omega
    have hpcE : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * pcExit) := by
      simpa only [hch, ite_false] using hh9_pc
    have hrun0 : DetRun oracle (submission.image .commit) h9
        (if 0 < chunks then 4 + (pairSteps * 64 + 1) * chunks else 0) h9
        (if 0 < chunks then 4 + (pairCyc * 64 + 1) * chunks else 0) (128 * chunks) := by
      rw [show (if 0 < chunks then 4 + (pairSteps * 64 + 1) * chunks else 0) = 0 by simp only [hch, ite_false],
          show (if 0 < chunks then 4 + (pairCyc * 64 + 1) * chunks else 0) = 0 by simp only [hch, ite_false],
          show 128 * chunks = 0 by omega]
      exact DetRun.refl oracle (submission.image .commit) h9
    exact ⟨h9, hrun0, hpcE, fun _ _ _ _ _ _ => rfl,
      by rw [hx10]; exact congrArg (BitVec.ofNat 64) (by omega),
      by rw [hx12]; exact congrArg (BitVec.ofNat 64) (by omega),
      fun _ h => by omega,
      fun _ _ _ _ => getByte_of_mem_eq hh_mem _,
      by rw [show C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks) =
            C_TD + levelBase (lvlIdx + 2) by omega]
         exact MemPreservedOutside.of_mem_eq hh_mem _ _⟩

/-! ### 5. Parameterized Stage B (Tail Pairs) -/

private theorem commit_bin_stageB_setup_gen (oracle : Oracle)
    (pcB pcBody pcExit modVal : Nat) (andiImm : BitVec 12) (beqImm : BitVec 13)
    (hstep_body : pcB + 3 = pcBody)
    (hbeq_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcB + 2)) + signExtend13 beqImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcExit))
    (handi : ∀ n < 2 ^ 64, BitVec.ofNat 64 n &&& signExtend12 andiImm = BitVec.ofNat 64 (n % modVal))
    (lvlIdx calls remPairs : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hrem : remPairs = (calls % modVal) / 2)
    (sb : MachineState)
    (hpcB : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * pcB))
    (hx20B : sb.getReg .x20 = BitVec.ofNat 64 calls)
    (hf0 : fetch (submission.image .commit) sb = some (.base (.ANDI .x22 .x20 andiImm)))
    (hf1 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcB + 1)) →
      fetch (submission.image .commit) st = some (.base (.SRLI .x22 .x22 (1#6))))
    (hf2 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcB + 2)) →
      fetch (submission.image .commit) st = some (.base (.BEQ .x22 .x0 beqImm))) :
    ∃ t2,
      DetRun oracle (submission.image .commit) sb 3 t2 3 0 ∧
      t2.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < remPairs then pcBody else pcExit)) ∧
      t2.mem = sb.mem ∧
      t2.getReg .x22 = BitVec.ofNat 64 remPairs ∧
      (∀ r : Reg, r ≠ .x22 → t2.getReg r = sb.getReg r) := by
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  have hmod_le : calls % modVal ≤ calls := Nat.mod_le calls modVal
  let t0 := execInstrBr sb (.ANDI .x22 .x20 andiImm)
  let t1 := execInstrBr t0 (.SRLI .x22 .x22 (1#6))
  let t2 := execInstrBr t1 (.BEQ .x22 .x0 beqImm)
  have ht0_pc : t0.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcB + 1)) := pc_step_idx sb pcB hpcB
  have ht1_pc : t1.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcB + 2)) := pc_step_idx t0 (pcB + 1) ht0_pc
  have ht_run3 : DetRun oracle (submission.image .commit) sb 3 t2 3 0 :=
    ((DetRun.step1 hf0 rfl).trans (DetRun.step1 (hf1 t0 ht0_pc) rfl)).trans (DetRun.step1 (hf2 t1 ht1_pc) rfl)
  have ht1_x22 : t1.getReg .x22 = BitVec.ofNat 64 remPairs := by
    have ht0_x22 : t0.getReg .x22 = BitVec.ofNat 64 (calls % modVal) := by
      simp only [t0, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), hx20B]
      exact handi calls (by omega)
    simp only [t1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), ht0_x22]
    exact (bv64_ushiftRight_ofNat (calls % modVal) 1 (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have ht2_mem : t2.mem = sb.mem :=
    ((mem_exec_BEQ t1 _ _ _).trans (mem_exec_SRLI t0 _ _ _)).trans (mem_exec_ANDI sb _ _ _)
  have ht2_reg : ∀ r : Reg, r ≠ .x22 → t2.getReg r = sb.getReg r := fun r hr => by
    rw [reg_exec_BEQ t1 _ _ _ r]
    simp only [t1, t0, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 r (Ne.symm hr)]
  have ht2_pc : t2.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < remPairs then pcBody else pcExit)) := by
    by_cases hrp : 0 < remPairs
    · have hne0 : (t1.getReg .x22 == t1.getReg .x0) = false := by
        rw [ht1_x22, c_getReg_x0, beq_eq_false_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hrp, ite_true, t2, execInstrBr, hne0, Bool.false_eq_true, ite_false, pc_setPC]
      rw [← hstep_body]
      exact pc_step_idx t1 (pcB + 2) ht1_pc
    · have hrp0 : remPairs = 0 := by omega
      have heq0 : (t1.getReg .x22 == t1.getReg .x0) = true := by
        rw [ht1_x22, hrp0, c_getReg_x0]; exact beq_self_eq_true _
      simp only [hrp, ite_false, t2, execInstrBr, heq0, ite_true, pc_setPC, ht1_pc]
      exact hbeq_pc
  exact ⟨t2, ht_run3, ht2_pc, ht2_mem, (reg_exec_BEQ t1 _ _ _ .x22).trans ht1_x22, ht2_reg⟩

private theorem commit_bin_stageB_dec_gen (oracle : Oracle) (pcDec remPairs m : Nat)
    (hm : m < remPairs) (sp : MachineState)
    (hsp_pc : sp.pc = BitVec.ofNat 64 (0x1000 + 4 * pcDec))
    (hx22p : sp.getReg .x22 = BitVec.ofNat 64 (remPairs - m))
    (hfDec : fetch (submission.image .commit) sp = some (.base (.ADDI .x22 .x22 (4095#12)))) :
    ∃ sdec,
      DetRun oracle (submission.image .commit) sp 1 sdec 1 0 ∧
      sdec.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcDec + 1)) ∧
      sdec.mem = sp.mem ∧
      sdec.getReg .x22 = BitVec.ofNat 64 (remPairs - (m + 1)) ∧
      (∀ r : Reg, r ≠ .x22 → sdec.getReg r = sp.getReg r) := by
  let sdec := execInstrBr sp (.ADDI .x22 .x22 (4095#12))
  have hsdec_pc : sdec.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcDec + 1)) := by
    change (sp.setReg .x22 _ |>.setPC (sp.pc + 4)).pc = _
    rw [pc_setPC]
    exact pc_step_idx sp pcDec hsp_pc
  have hsdec_x22 : sdec.getReg .x22 = BitVec.ofNat 64 (remPairs - (m + 1)) := by
    simp only [sdec, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), hx22p]
    exact (c_bv64_add_neg1 (remPairs - m) (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have hreg : ∀ r : Reg, r ≠ .x22 → sdec.getReg r = sp.getReg r := fun r hr => by
    simp only [sdec, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 r (Ne.symm hr)]
  exact ⟨sdec, DetRun.step1 hfDec rfl, hsdec_pc, mem_exec_ADDI sp _ _ _, hsdec_x22, hreg⟩

private theorem commit_bin_stageB_bne_gen (oracle : Oracle)
    (pcBne pcBody pcExit : Nat) (bneImm : BitVec 13)
    (hstep_exit : pcBne + 1 = pcExit)
    (hbne_pc : BitVec.ofNat 64 (0x1000 + 4 * pcBne) + signExtend13 bneImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcBody))
    (remPairs m : Nat) (hrem_lt : remPairs < 2 ^ 64) (sdec : MachineState)
    (hsdec_pc : sdec.pc = BitVec.ofNat 64 (0x1000 + 4 * pcBne))
    (hsdec_x22 : sdec.getReg .x22 = BitVec.ofNat 64 (remPairs - (m + 1)))
    (hfBne : fetch (submission.image .commit) sdec = some (.base (.BNE .x22 .x0 bneImm))) :
    ∃ sbne,
      DetRun oracle (submission.image .commit) sdec 1 sbne 1 0 ∧
      sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if m + 1 < remPairs then pcBody else pcExit)) ∧
      sbne.mem = sdec.mem ∧
      (∀ r : Reg, sbne.getReg r = sdec.getReg r) := by
  let sbne := execInstrBr sdec (.BNE .x22 .x0 bneImm)
  have hpc_end : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if m + 1 < remPairs then pcBody else pcExit)) := by
    by_cases hlt : m + 1 < remPairs
    · have hne : (sdec.getReg .x22 != sdec.getReg .x0) = true := by
        rw [hsdec_x22, c_getReg_x0, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hlt, ite_true, sbne, execInstrBr, hne, pc_setPC, hsdec_pc]
      exact hbne_pc
    · have heq : (sdec.getReg .x22 != sdec.getReg .x0) = false := by
        rw [hsdec_x22, c_getReg_x0, show remPairs - (m + 1) = 0 by omega]
        exact bne_self_eq_false _
      simp only [hlt, ite_false, sbne, execInstrBr, heq, Bool.false_eq_true, pc_setPC]
      rw [← hstep_exit]
      exact pc_step_idx sdec pcBne hsdec_pc
  exact ⟨sbne, DetRun.step1 hfBne rfl, hpc_end, mem_exec_BNE sdec _ _ _, reg_exec_BNE sdec _ _ _⟩

private theorem commit_bin_stageB_gen (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (pcB pcBody pcExit pairSteps pairCyc modVal : Nat) (andiImm : BitVec 12) (beqImm bneImm : BitVec 13)
    (hstep_body : pcB + 3 = pcBody)
    (hstep_exit : pcBody + pairSteps + 2 = pcExit)
    (hbeq_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcB + 2)) + signExtend13 beqImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcExit))
    (hbne_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcBody + pairSteps + 1)) + signExtend13 bneImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcBody))
    (handi : ∀ n < 2 ^ 64, BitVec.ofNat 64 n &&& signExtend12 andiImm = BitVec.ofNat 64 (n % modVal))
    (lvlIdx calls basePairs remPairs : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hrem : remPairs = (calls % modVal) / 2)
    (hbase : 2 * basePairs + 2 * remPairs ≤ calls)
    (s0 sb : MachineState)
    (hpcB : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * pcB))
    (hx5B : sb.getReg .x5 = 0#64) (hx11B : sb.getReg .x11 = 96#64) (hx13B : sb.getReg .x13 = 0#64)
    (hx20B : sb.getReg .x20 = BitVec.ofNat 64 calls)
    (hx10B : sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * basePairs) - 96))
    (hx12B : sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * basePairs - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 1) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64) 32 = 0)
    (hdigB : ∀ idx < 2 * basePairs,
      readBuffer sb (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hgapB : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
      sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)))
    (hpresB : MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 2))
      (C_TD + levelBase (lvlIdx + 2) + 96 * basePairs))
    (hfS0 : fetch (submission.image .commit) sb = some (.base (.ANDI .x22 .x20 andiImm)))
    (hfS1 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcB + 1)) →
      fetch (submission.image .commit) st = some (.base (.SRLI .x22 .x22 (1#6))))
    (hfS2 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcB + 2)) →
      fetch (submission.image .commit) st = some (.base (.BEQ .x22 .x0 beqImm)))
    (hpair : ∀ (q : Nat), 2 * q + 1 < calls → ∀ (sm : MachineState),
      sm.pc = BitVec.ofNat 64 (0x1000 + 4 * pcBody) →
      sm.getReg .x5 = 0#64 → sm.getReg .x11 = 96#64 → sm.getReg .x13 = 0#64 →
      sm.getReg .x27 = sb.getReg .x27 →
      sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q) - 96) →
      sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q - 64) →
      (∀ j < 4, readBuffer sm (C_TD + levelBase (lvlIdx + 1) + gapOffset (4 * q + j)) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) (4 * q + j)) →
      (∀ p < 2, readBuffer sm (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + p) + 64) 32 = 0) →
      ∃ sp,
        DetRun oracle (submission.image .commit) sm pairSteps sp pairCyc 2 ∧
        sp.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBody + pairSteps)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sp.getReg r = sm.getReg r) ∧
        sp.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * q + 1)) ∧
        sp.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 2) + 96 * q) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (2 * q) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 2) + 96 * q + 32) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (2 * q + 1) ∧
        MemPreservedOutside sm sp (C_TD + levelBase (lvlIdx + 2) + 96 * q)
          (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64))
    (hfDec : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBody + pairSteps)) →
      fetch (submission.image .commit) st = some (.base (.ADDI .x22 .x22 (4095#12))))
    (hfBne : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBody + pairSteps + 1)) →
      fetch (submission.image .commit) st = some (.base (.BNE .x22 .x0 bneImm))) :
    ∃ st,
      DetRun oracle (submission.image .commit) sb (3 + (pairSteps + 2) * remPairs) st
        (3 + (pairCyc + 2) * remPairs) (2 * remPairs) ∧
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * pcExit) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → st.getReg r = sb.getReg r) ∧
      st.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * basePairs + 2 * remPairs) - 96) ∧
      st.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (basePairs + remPairs) - 64) ∧
      (∀ idx < 2 * basePairs + 2 * remPairs,
        readBuffer st (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx) ∧
      (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
        st.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 st (C_TD + levelBase (lvlIdx + 2))
        (C_TD + levelBase (lvlIdx + 2) + 96 * (basePairs + remPairs)) := by
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
  obtain ⟨t2, ht_run3, ht2_pc, ht2_mem, ht2_x22, ht2_reg⟩ :=
    commit_bin_stageB_setup_gen oracle pcB pcBody pcExit modVal andiImm beqImm hstep_body hbeq_pc handi
      lvlIdx calls remPairs hlvl hcalls hrem sb hpcB hx20B hfS0 hfS1 hfS2
  by_cases hrp : 0 < remPairs
  · have htloop : ∀ m ≤ remPairs,
        ∃ sm,
          DetRun oracle (submission.image .commit) t2 ((pairSteps + 2) * m) sm ((pairCyc + 2) * m) (2 * m) ∧
          sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (if m < remPairs then pcBody else pcExit)) ∧
          (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → sm.getReg r = sb.getReg r) ∧
          sm.getReg .x22 = BitVec.ofNat 64 (remPairs - m) ∧
          sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * basePairs + 2 * m) - 96) ∧
          sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (basePairs + m) - 64) ∧
          (∀ idx < 2 * basePairs + 2 * m, readBuffer sm (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
            nodeVal c96 msg salts (lvlIdx + 2) idx) ∧
          (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
            sm.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
            s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
          MemPreservedOutside s0 sm (C_TD + levelBase (lvlIdx + 2))
            (C_TD + levelBase (lvlIdx + 2) + 96 * (basePairs + m)) := by
      intro m hm; induction m with
      | zero =>
        exact ⟨t2, DetRun.refl _ _ _, ht2_pc, fun r _ _ _ h22 => ht2_reg r h22,
          by rw [ht2_x22]; exact congrArg (BitVec.ofNat 64) (by omega),
          by rw [ht2_reg .x10 (by decide), hx10B]; exact congrArg (BitVec.ofNat 64) (by omega),
          by rw [ht2_reg .x12 (by decide), hx12B]; exact congrArg (BitVec.ofNat 64) (by omega),
          fun idx hidx => (readBuffer_of_mem_eq ht2_mem _ _).trans (hdigB idx (by omega)),
          fun q hq j hj => (getByte_of_mem_eq ht2_mem _).trans (hgapB q hq j hj),
          by rw [show C_TD + levelBase (lvlIdx + 2) + 96 * (basePairs + 0) =
                C_TD + levelBase (lvlIdx + 2) + 96 * basePairs by omega]
             exact hpresB.trans (MemPreservedOutside.of_mem_eq ht2_mem _ _)⟩
      | succ m ihm =>
        obtain ⟨sm, hrunm, hpcm, hregm, hx22m, hx10m, hx12m, hdigm, hgapm, hpresm⟩ := ihm (by omega)
        have hpc_in : sm.pc = BitVec.ofNat 64 (0x1000 + 4 * pcBody) := by
          simpa only [show m < remPairs by omega, ite_true] using hpcm
        obtain ⟨sp, hrun1, hpcp, hregp, hx10p, hx12p, hd0p, hd1p, hpres1⟩ :=
          hpair (basePairs + m) (by omega) sm hpc_in
            ((hregm .x5 (by decide) (by decide) (by decide) (by decide)).trans hx5B)
            ((hregm .x11 (by decide) (by decide) (by decide) (by decide)).trans hx11B)
            ((hregm .x13 (by decide) (by decide) (by decide) (by decide)).trans hx13B)
            (hregm .x27 (by decide) (by decide) (by decide) (by decide))
            (by rw [hx10m]; exact congrArg (BitVec.ofNat 64) (by omega)) hx12m
            (fun j hj => by
              have hgo : gapOffset (4 * (basePairs + m) + j) + 32 ≤ levelBytes (lvlIdx + 1) :=
                gapOffset_lt_levelBytes (lvlIdx + 1) _ (by omega) (by omega) (by omega)
              rw [hpresm.readBuffer_eq (by omega) (by omega)]
              exact hsrc (4 * (basePairs + m) + j) (by omega))
            (fun p hp => by
              have hgap_bd : 96 * (2 * (basePairs + m) + p) + 64 + 32 ≤ levelBytes (lvlIdx + 1) := by
                rw [hsrcBytes]; omega
              rw [hpresm.readBuffer_eq (by omega) (by omega)]
              exact hsrcGap (2 * (basePairs + m) + p) (by omega))
        obtain ⟨sdec, hdec_run, hsdec_pc, hsdec_mem, hsdec_x22, hsdec_reg⟩ :=
          commit_bin_stageB_dec_gen oracle (pcBody + pairSteps) remPairs m (by omega) sp hpcp
            ((hregp .x22 (by decide) (by decide) (by decide)).trans hx22m) (hfDec sp hpcp)
        obtain ⟨sbne, hbne_run, hpc_end, hmem_bne, hreg_bne⟩ :=
          commit_bin_stageB_bne_gen oracle (pcBody + pairSteps + 1) pcBody pcExit bneImm
            (by omega) hbne_pc remPairs m (by omega) sdec hsdec_pc hsdec_x22 (hfBne sdec hsdec_pc)
        have hmem_end : sbne.mem = sp.mem := hmem_bne.trans hsdec_mem
        have hpresI : MemPreservedOutside sm sbne (C_TD + levelBase (lvlIdx + 2) + 96 * (basePairs + m))
            (C_TD + levelBase (lvlIdx + 2) + 96 * (basePairs + m) + 64) :=
          hpres1.trans (MemPreservedOutside.of_mem_eq hmem_end _ _)
        have hrun_m1 : DetRun oracle (submission.image .commit) t2 ((pairSteps + 2) * (m + 1)) sbne
            ((pairCyc + 2) * (m + 1)) (2 * (m + 1)) := by
          have h := hrunm.trans (hrun1.trans (hdec_run.trans hbne_run))
          rw [← Nat.mul_succ (pairSteps + 2) m, ← Nat.mul_succ (pairCyc + 2) m,
              show 2 * m + (2 + (0 + 0)) = 2 * (m + 1) by omega] at h
          exact h
        refine ⟨sbne, hrun_m1, hpc_end,
          fun r h6 h10 h12 h22 => (((hreg_bne r).trans (hsdec_reg r h22)).trans (hregp r h6 h10 h12)).trans
            (hregm r h6 h10 h12 h22),
          (hreg_bne .x22).trans hsdec_x22,
          by rw [hreg_bne .x10, hsdec_reg .x10 (by decide), hx10p]; exact congrArg (BitVec.ofNat 64) (by omega),
          by rw [hreg_bne .x12, hsdec_reg .x12 (by decide), hx12p]; exact congrArg (BitVec.ofNat 64) (by omega),
          ?_, ?_, (hpresm.mono (le_refl _) (by omega)).trans (hpresI.mono (by omega) (by omega))⟩
        · intro idx hidx
          by_cases hold : idx < 2 * basePairs + 2 * m
          · rw [← hdigm idx hold]
            have hgo : gapOffset idx + 32 ≤ 96 * (basePairs + m) := by unfold gapOffset; omega
            have hdst_bd : 96 * (basePairs + m) ≤ levelBytes (lvlIdx + 2) := by
              rw [hdstBytes, hdstSize_eq]; omega
            exact hpresI.readBuffer_eq (by omega) (by omega)
          · by_cases hev : idx = 2 * (basePairs + m)
            · subst hev; simpa only [gapOffset_even] using (readBuffer_of_mem_eq hmem_end _ _).trans hd0p
            · have hodd : idx = 2 * (basePairs + m) + 1 := by omega
              subst hodd; simpa only [gapOffset_odd, Nat.add_assoc] using (readBuffer_of_mem_eq hmem_end _ _).trans hd1p
        · intro q hq j hj
          have hsep : C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j <
                C_TD + levelBase (lvlIdx + 2) + 96 * (basePairs + m) ∨
              C_TD + levelBase (lvlIdx + 2) + 96 * (basePairs + m) + 64 ≤
                C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j := by omega
          exact (hpresI (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)
            (by rw [hdstBytes] at hdstB; omega) hsep).trans (hgapm q hq j hj)
    obtain ⟨st, hrunT, hpcT, hregT, _, hx10T, hx12T, hdigT, hgapT, hpresT⟩ := htloop remPairs (le_refl _)
    have hrun_all : DetRun oracle (submission.image .commit) sb (3 + (pairSteps + 2) * remPairs) st
        (3 + (pairCyc + 2) * remPairs) (2 * remPairs) := by
      have h := ht_run3.trans hrunT
      rw [Nat.zero_add] at h
      exact h
    exact ⟨st, hrun_all, by simpa only [Nat.lt_irrefl, ite_false] using hpcT,
      hregT, hx10T, hx12T, hdigT, hgapT, hpresT⟩
  · have hrp0 : remPairs = 0 := by omega
    have hrun0 : DetRun oracle (submission.image .commit) sb (3 + (pairSteps + 2) * remPairs) t2
        (3 + (pairCyc + 2) * remPairs) (2 * remPairs) := by
      simp only [hrp0, Nat.mul_zero, Nat.add_zero]
      exact ht_run3
    refine ⟨t2, hrun0, by simpa only [hrp, ite_false] using ht2_pc, fun r _ _ _ h22 => ht2_reg r h22,
      by rw [ht2_reg .x10 (by decide), hx10B]; exact congrArg (BitVec.ofNat 64) (by omega),
      by rw [ht2_reg .x12 (by decide), hx12B]; exact congrArg (BitVec.ofNat 64) (by omega),
      fun idx hidx => (readBuffer_of_mem_eq ht2_mem _ _).trans (hdigB idx (by omega)),
      fun q hq j hj => (getByte_of_mem_eq ht2_mem _).trans (hgapB q hq j hj),
      by rw [show C_TD + levelBase (lvlIdx + 2) + 96 * (basePairs + remPairs) =
            C_TD + levelBase (lvlIdx + 2) + 96 * basePairs by omega]
         exact hpresB.trans (MemPreservedOutside.of_mem_eq ht2_mem _ _)⟩

/-! ### 6. Phase 3A Stage A (`U_BIN = 2048`, 1024-pair chunks with 2-instr `BEQ+JAL` latch)
and Concrete Stage A / Stage B Instantiations for Phase 3A (240b) and Phase 3B (238b) -/

private theorem commit_bin2048_stageA_setup (oracle : Oracle)
    (lvlIdx calls chunks : Nat) (hlvl : lvlIdx < 4)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 2048)
    (h9 : MachineState)
    (hpcS : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * 139340))
    (hx10 : h9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 96))
    (hx22 : h9.getReg .x22 = BitVec.ofNat 64 chunks) :
    ∃ b3,
      DetRun oracle (submission.image .commit) h9 4 b3 4 0 ∧
      b3.pc = BitVec.ofNat 64 (0x1000 + 4 * 139344) ∧
      b3.mem = h9.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x19 → b3.getReg r = h9.getReg r) ∧
      b3.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2048 * chunks) - 96) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  let b0 := execInstrBr h9 (.SLLI .x6 .x22 (16#6))
  let b1 := execInstrBr b0 (.SLLI .x7 .x22 (17#6))
  let b2 := execInstrBr b1 (.ADD .x6 .x6 .x7)
  let b3 := execInstrBr b2 (.ADD .x19 .x10 .x6)
  have hb0_pc : b0.pc = BitVec.ofNat 64 (0x1000 + 4 * 139341) := pc_step_idx h9 139340 hpcS
  have hb1_pc : b1.pc = BitVec.ofNat 64 (0x1000 + 4 * 139342) := pc_step_idx b0 139341 hb0_pc
  have hb2_pc : b2.pc = BitVec.ofNat 64 (0x1000 + 4 * 139343) := pc_step_idx b1 139342 hb1_pc
  have hb3_pc : b3.pc = BitVec.ofNat 64 (0x1000 + 4 * 139344) := pc_step_idx b2 139343 hb2_pc
  have hb_run : DetRun oracle (submission.image .commit) h9 4 b3 4 0 :=
    (((commit_step1_mid2 (by omega) (by omega) hpcS (by simp only [commitMid2Instr])).trans
      (commit_step1_mid2 (by omega) (by omega) hb0_pc (by simp only [commitMid2Instr]))).trans
      (commit_step1_mid2 (by omega) (by omega) hb1_pc (by simp only [commitMid2Instr]))).trans
      (commit_step1_mid2 (by omega) (by omega) hb2_pc (by simp only [commitMid2Instr]))
  have hb3_mem : b3.mem = h9.mem :=
    (((mem_exec_ADD b2 _ _ _).trans (mem_exec_ADD b1 _ _ _)).trans (mem_exec_SLLI b0 _ _ _)).trans
      (mem_exec_SLLI h9 _ _ _)
  have hb3_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x19 → b3.getReg r = h9.getReg r := fun r h6 h7 h19 => by
    simp only [b3, b2, b1, b0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x19 r (Ne.symm h19), getReg_setReg_ne' .x6 r (Ne.symm h6),
      getReg_setReg_ne' .x7 r (Ne.symm h7)]
  have hb3_x19 : b3.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2048 * chunks) - 96) := by
    have hb0_x6 : b0.getReg .x6 = BitVec.ofNat 64 (chunks * 2 ^ 16) := by
      simp only [b0, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hx22]
      exact bv64_shiftLeft_ofNat chunks 16 (by omega)
    have hb1_x7 : b1.getReg .x7 = BitVec.ofNat 64 (chunks * 2 ^ 17) := by
      have : b0.getReg .x22 = BitVec.ofNat 64 chunks := by
        simp only [b0, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x22 (by decide), hx22]
      simp only [b1, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x7 ≠ .x0), this]
      exact bv64_shiftLeft_ofNat chunks 17 (by omega)
    have hb2_x6 : b2.getReg .x6 = BitVec.ofNat 64 (196608 * chunks) := by
      have : b1.getReg .x6 = BitVec.ofNat 64 (chunks * 2 ^ 16) := by
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

private theorem commit_bin2048_stageA_chunk (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks n : Nat) (hlvl : lvlIdx < 4)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 2048) (hn : n < chunks)
    (s0 sn : MachineState)
    (hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 139344))
    (hx5 : sn.getReg .x5 = 0#64) (hx11 : sn.getReg .x11 = 96#64) (hx13 : sn.getReg .x13 = 0#64)
    (hx19 : sn.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2048 * chunks) - 96))
    (hx10n : sn.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2048 * n) - 96))
    (hx12n : sn.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * n) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 1) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64) 32 = 0)
    (hpresn : MemPreservedOutside s0 sn (C_TD + levelBase (lvlIdx + 2))
      (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * n))) :
    ∃ sfin,
      DetRun oracle (submission.image .commit) sn
        (if n + 1 < chunks then 8194 else 8193) sfin
        (if n + 1 < chunks then 22530 else 22529) 2048 ∧
      sfin.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n + 1 < chunks then 139344 else 147538)) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sfin.getReg r = sn.getReg r) ∧
      sfin.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2048 * (n + 1)) - 96) ∧
      sfin.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * (n + 1)) - 64) ∧
      (∀ idx, 2048 * n ≤ idx → idx < 2048 * (n + 1) →
        readBuffer sfin (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx) ∧
      (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
        sfin.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
        sn.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
      MemPreservedOutside sn sfin (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * n))
        (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * (n + 1))) := by
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
  have hpairs : ∀ m ≤ 1024,
      ∃ sm,
        DetRun oracle (submission.image .commit) sn (8 * m) sm (22 * m) (2 * m) ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (139344 + 8 * m)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sm.getReg r = sn.getReg r) ∧
        sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2 * (1024 * n + m)) - 96) ∧
        sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * n + m) - 64) ∧
        (∀ idx, 2048 * n ≤ idx → idx < 2048 * n + 2 * m →
          readBuffer sm (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
            nodeVal c96 msg salts (lvlIdx + 2) idx) ∧
        (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
          sm.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
        MemPreservedOutside sn sm (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * n))
          (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * n + m)) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨sn, DetRun.refl _ _ _, by simpa only [Nat.mul_zero, Nat.add_zero] using hpc_in,
        fun _ _ _ _ => rfl,
        by rw [hx10n]; exact congrArg (BitVec.ofNat 64) (by omega),
        by rw [hx12n]; exact congrArg (BitVec.ofNat 64) (by omega),
        fun _ h1 h2 => by omega, fun _ _ _ _ => rfl, MemPreservedOutside.refl _ _ _⟩
    | succ m ihm =>
      obtain ⟨sm, hrunm, hpcm, hregm, hx10m, hx12m, hdigm, hgapm, hpresm⟩ := ihm (by omega)
      have hpres_s0 : MemPreservedOutside s0 sm (C_TD + levelBase (lvlIdx + 2))
          (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * n + m)) :=
        (hpresn.mono (le_refl _) (by omega)).trans (hpresm.mono (by omega) (le_refl _))
      obtain ⟨sp, hrun1, hpcp, hregp, hx10p, hx12p, hd0p, hd1p, hpres1⟩ :=
        commit_bin_pair h768 oracle msg salts lvlIdx (139344 + 8 * m) (1024 * n + m) hlvl (by omega) sm
          (fun j hj st hst => commit_fetch_bin_bulk st m j (by omega) hj hst) hpcm
          ((hregm .x5 (by decide) (by decide) (by decide)).trans hx5)
          ((hregm .x11 (by decide) (by decide) (by decide)).trans hx11)
          ((hregm .x13 (by decide) (by decide) (by decide)).trans hx13)
          hx10m hx12m
          (fun j hj => by
            have hgo : gapOffset (4 * (1024 * n + m) + j) + 32 ≤ levelBytes (lvlIdx + 1) :=
              gapOffset_lt_levelBytes (lvlIdx + 1) _ (by omega) (by omega) (by omega)
            rw [hpres_s0.readBuffer_eq (by omega) (by omega)]
            exact hsrc (4 * (1024 * n + m) + j) (by omega))
          (fun p hp => by
            have hgap_bd : 96 * (2 * (1024 * n + m) + p) + 64 + 32 ≤ levelBytes (lvlIdx + 1) := by
              rw [hsrcBytes]; omega
            rw [hpres_s0.readBuffer_eq (by omega) (by omega)]
            exact hsrcGap (2 * (1024 * n + m) + p) (by omega))
      have hrun_m1 : DetRun oracle (submission.image .commit) sn (8 * (m + 1)) sp
          (22 * (m + 1)) (2 * (m + 1)) := by
        have h := hrunm.trans hrun1
        rw [show 8 * m + 8 = 8 * (m + 1) by omega,
            show 22 * m + 22 = 22 * (m + 1) by omega,
            show 2 * m + 2 = 2 * (m + 1) by omega] at h
        exact h
      refine ⟨sp, hrun_m1,
        by rw [hpcp, Nat.add_assoc, show 8 * m + 8 = 8 * (m + 1) by omega],
        fun r h6 h10 h12 => (hregp r h6 h10 h12).trans (hregm r h6 h10 h12),
        by rw [hx10p]; exact congrArg (BitVec.ofNat 64) (by omega),
        by rw [hx12p]; exact congrArg (BitVec.ofNat 64) (by omega), ?_, ?_, ?_⟩
      · intro idx hlo hhi
        by_cases hold : idx < 2048 * n + 2 * m
        · rw [← hdigm idx hlo hold]
          have hgo : gapOffset idx + 32 ≤ 96 * (1024 * n + m) := by unfold gapOffset; omega
          exact hpres1.readBuffer_eq (by omega) (by omega)
        · by_cases hev : idx = 2 * (1024 * n + m)
          · subst hev; simpa only [gapOffset_even] using hd0p
          · have hodd : idx = 2 * (1024 * n + m) + 1 := by omega
            subst hodd; simpa only [gapOffset_odd, Nat.add_assoc] using hd1p
      · intro q hq j hj
        have hsep : C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j <
              C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * n + m) ∨
            C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * n + m) + 64 ≤
              C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j := by omega
        exact (hpres1 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)
          (by rw [hdstBytes] at hdstB; omega) hsep).trans (hgapm q hq j hj)
      · exact (hpresm.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (by omega))
  obtain ⟨sm, hrun1024, hpc1024, hreg1024, hx10_1024, hx12_1024, hdig1024, hgap1024, hpres1024⟩ :=
    hpairs 1024 (le_refl _)
  have hx19m : sm.getReg .x19 =
      BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2048 * chunks) - 96) :=
    (hreg1024 .x19 (by decide) (by decide) (by decide)).trans hx19
  by_cases hlt : n + 1 < chunks
  · have hcmp : (sm.getReg .x10 == sm.getReg .x19) = false := by
      rw [hx10_1024, hx19m, beq_eq_false_iff_ne]
      exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
    have hl := c_beq_jal_latch oracle sm .x10 .x19 147536 139344 (2064380#21) false hpc1024 hcmp
      (commit_fetch_commitMid3Instr sm 147536 (by omega) (by omega) hpc1024)
      (fun st hst => commit_fetch_commitMid3Instr st 147537 (by omega) (by omega) hst)
      pc_jal_147537
    obtain ⟨hl_run, hl_pc, hl_mem, hl_reg⟩ := hl
    simp only [Bool.false_eq_true, ite_false] at hl_run hl_pc hl_mem hl_reg
    refine ⟨_, by simpa only [hlt, ite_true] using hrun1024.trans hl_run,
      by simpa only [hlt, ite_true] using hl_pc,
      fun r h6 h10 h12 => (hl_reg r).trans (hreg1024 r h6 h10 h12),
      by rw [hl_reg, hx10_1024]; exact congrArg (BitVec.ofNat 64) (by omega),
      by rw [hl_reg, hx12_1024]; exact congrArg (BitVec.ofNat 64) (by omega),
      fun idx hlo hhi => (readBuffer_of_mem_eq hl_mem _ _).trans (hdig1024 idx hlo (by omega)),
      fun q hq j hj => (getByte_of_mem_eq hl_mem _).trans (hgap1024 q hq j hj),
      (hpres1024.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hl_mem _ _)⟩
  · have hnc : n + 1 = chunks := Nat.le_antisymm hn (Nat.not_lt.mp hlt)
    have h2048 : 2 * (1024 * n + 1024) = 2048 * chunks := by rw [← hnc]; ring
    have hcmp : (sm.getReg .x10 == sm.getReg .x19) = true := by
      rw [hx10_1024, hx19m, h2048]
      exact beq_self_eq_true _
    have hl := c_beq_jal_latch oracle sm .x10 .x19 147536 139344 (2064380#21) true hpc1024 hcmp
      (commit_fetch_commitMid3Instr sm 147536 (by omega) (by omega) hpc1024)
      (fun st hst => commit_fetch_commitMid3Instr st 147537 (by omega) (by omega) hst)
      pc_jal_147537
    obtain ⟨hl_run, hl_pc, hl_mem, hl_reg⟩ := hl
    simp only [ite_true] at hl_run hl_pc hl_mem hl_reg
    refine ⟨_, by simpa only [hlt, ite_false] using hrun1024.trans hl_run,
      by simpa only [hlt, ite_false] using hl_pc,
      fun r h6 h10 h12 => (hl_reg r).trans (hreg1024 r h6 h10 h12),
      by rw [hl_reg, hx10_1024]; exact congrArg (BitVec.ofNat 64) (by omega),
      by rw [hl_reg, hx12_1024]; exact congrArg (BitVec.ofNat 64) (by omega),
      fun idx hlo hhi => (readBuffer_of_mem_eq hl_mem _ _).trans (hdig1024 idx hlo (by omega)),
      fun q hq j hj => (getByte_of_mem_eq hl_mem _).trans (hgap1024 q hq j hj),
      (hpres1024.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hl_mem _ _)⟩

private theorem commit_fetch_bin_tail_pair (st : MachineState) (j : Nat) (hj : j < 8)
    (hst : st.pc = BitVec.ofNat 64 (0x1000 + 4 * (147541 + j))) :
    fetch (submission.image .commit) st = some (binPairInstr j) := by
  have h := commit_fetch_commitMid3Instr st (147541 + j) (by omega) (by omega) hst
  interval_cases j <;> simpa only [binPairInstr, commitMid3Instr] using h

private theorem commit_fetch_bin238_tail_pair (st : MachineState) (j : Nat) (hj : j < 12)
    (hst : st.pc = BitVec.ofNat 64 (0x1000 + 4 * (148369 + j))) :
    fetch (submission.image .commit) st = some (bin238PairInstr j) := by
  have h := commit_fetch_commitTailInstr st (148369 + j) (by omega) (by omega) hst
  interval_cases j <;> simpa only [bin238PairInstr, commitTailInstr] using h

/-- Phase 3A Stage A (240-bit bulk `1024`-pair chunks, words `139340..147537`). -/
theorem commit_bin_level_stageA (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks : Nat) (hlvl : lvlIdx < 4)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 2048)
    (s0 h9 : MachineState)
    (hh_mem : h9.mem = s0.mem)
    (hh9_pc : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then 139340 else 147538)))
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
        (if 0 < chunks then 3 + 8194 * chunks else 0) sb
        (if 0 < chunks then 3 + 22530 * chunks else 0) (2048 * chunks) ∧
      sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 147538) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → sb.getReg r = h9.getReg r) ∧
      sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2048 * chunks) - 96) ∧
      sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * chunks) - 64) ∧
      (∀ idx < 2048 * chunks,
        readBuffer sb (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx) ∧
      (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
        sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 2))
        (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * chunks)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 2) (by omega)
  have htb := treeBytes_eq
  by_cases hch : 0 < chunks
  · have hpcS : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * 139340) := by
      simpa only [hch, ite_true] using hh9_pc
    obtain ⟨b3, hb_setup, hb3_pc, hb3_mem', hb3_reg, hb3_x19⟩ :=
      commit_bin2048_stageA_setup oracle lvlIdx calls chunks hlvl hcalls hchunks h9 hpcS hx10 hx22
    have hb3_mem : b3.mem = s0.mem := hb3_mem'.trans hh_mem
    have hbulk : ∀ n ≤ chunks,
        ∃ sn,
          DetRun oracle (submission.image .commit) b3
            (if n < chunks then 8194 * n else 8194 * n - 1) sn
            (if n < chunks then 22530 * n else 22530 * n - 1) (2048 * n) ∧
          sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < chunks then 139344 else 147538)) ∧
          (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sn.getReg r = b3.getReg r) ∧
          sn.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2048 * n) - 96) ∧
          sn.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * n) - 64) ∧
          (∀ idx < 2048 * n, readBuffer sn (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
            nodeVal c96 msg salts (lvlIdx + 2) idx) ∧
          (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
            sn.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
            s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
          MemPreservedOutside s0 sn (C_TD + levelBase (lvlIdx + 2))
            (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * n)) := by
      intro n hn; induction n with
      | zero =>
        exact ⟨b3, by simpa only [hch, ite_true, Nat.mul_zero] using DetRun.refl oracle (submission.image .commit) b3,
          by simpa only [hch, ite_true] using hb3_pc, fun _ _ _ _ => rfl,
          by rw [hb3_reg .x10 (by decide) (by decide) (by decide), hx10]; exact congrArg (BitVec.ofNat 64) (by omega),
          by rw [hb3_reg .x12 (by decide) (by decide) (by decide), hx12]; exact congrArg (BitVec.ofNat 64) (by omega),
          fun _ h => (Nat.not_lt_zero _ h).elim,
          fun _ _ _ _ => getByte_of_mem_eq hb3_mem _,
          MemPreservedOutside.of_mem_eq hb3_mem _ _⟩
      | succ n ih =>
        obtain ⟨sn, hrunn, hpcn, hregn, hx10n, hx12n, hdign, hgapn, hpresn⟩ := ih (by omega)
        have hlt_n : n < chunks := by omega
        have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 139344) := by
          simpa only [hlt_n, ite_true] using hpcn
        simp only [hlt_n, ite_true] at hrunn
        obtain ⟨sfin, hrunC, hpc_end, hregC, hx10C, hx12C, hdigC, hgapC, hpresC⟩ :=
          commit_bin2048_stageA_chunk h768 oracle msg salts lvlIdx calls chunks n hlvl hcalls hchunks hlt_n
            s0 sn hpc_in
            ((hregn .x5 (by decide) (by decide) (by decide)).trans ((hb3_reg .x5 (by decide) (by decide) (by decide)).trans hx5))
            ((hregn .x11 (by decide) (by decide) (by decide)).trans ((hb3_reg .x11 (by decide) (by decide) (by decide)).trans hx11))
            ((hregn .x13 (by decide) (by decide) (by decide)).trans ((hb3_reg .x13 (by decide) (by decide) (by decide)).trans hx13))
            ((hregn .x19 (by decide) (by decide) (by decide)).trans hb3_x19)
            hx10n hx12n hsrc hsrcGap hpresn
        have hrun_n1 : DetRun oracle (submission.image .commit) b3
            (if n + 1 < chunks then 8194 * (n + 1) else 8194 * (n + 1) - 1) sfin
            (if n + 1 < chunks then 22530 * (n + 1) else 22530 * (n + 1) - 1) (2048 * (n + 1)) := by
          have h := hrunn.trans hrunC
          have hs : 8194 * n + (if n + 1 < chunks then 8194 else 8193) =
              (if n + 1 < chunks then 8194 * (n + 1) else 8194 * (n + 1) - 1) := by split_ifs <;> omega
          have hc : 22530 * n + (if n + 1 < chunks then 22530 else 22529) =
              (if n + 1 < chunks then 22530 * (n + 1) else 22530 * (n + 1) - 1) := by split_ifs <;> omega
          rw [hs, hc, show 2048 * n + 2048 = 2048 * (n + 1) by omega] at h
          exact h
        refine ⟨sfin, hrun_n1, hpc_end, fun r h6 h10 h12 => (hregC r h6 h10 h12).trans (hregn r h6 h10 h12),
          hx10C, hx12C, ?_, fun q hq j hj => (hgapC q hq j hj).trans (hgapn q hq j hj),
          (hpresn.mono (le_refl _) (by omega)).trans (hpresC.mono (by omega) (le_refl _))⟩
        intro idx hidx
        by_cases hold : idx < 2048 * n
        · rw [← hdign idx hold]
          have hgo : gapOffset idx + 32 ≤ 96 * (1024 * n) := by unfold gapOffset; omega
          exact hpresC.readBuffer_eq (by omega) (by omega)
        · exact hdigC idx (by omega) hidx
    obtain ⟨sb, hrunb, hpcb, hregb, hx10b, hx12b, hdigb, hgapb, hpresb⟩ := hbulk chunks (le_refl _)
    simp only [Nat.lt_irrefl, ite_false] at hrunb
    have hrun_tot : DetRun oracle (submission.image .commit) h9
        (if 0 < chunks then 3 + 8194 * chunks else 0) sb
        (if 0 < chunks then 3 + 22530 * chunks else 0) (2048 * chunks) := by
      have h := hb_setup.trans hrunb
      rw [Nat.zero_add,
          show 4 + (8194 * chunks - 1) = (if 0 < chunks then 3 + 8194 * chunks else 0) by
            simp only [hch, ite_true]; omega,
          show 4 + (22530 * chunks - 1) = (if 0 < chunks then 3 + 22530 * chunks else 0) by
            simp only [hch, ite_true]; omega] at h
      exact h
    exact ⟨sb, hrun_tot, by simpa only [Nat.lt_irrefl, ite_false] using hpcb,
      fun r h6 h7 h10 h12 h19 => (hregb r h6 h10 h12).trans (hb3_reg r h6 h7 h19),
      hx10b, hx12b, hdigb, hgapb, hpresb⟩
  · have hch0 : chunks = 0 := by omega
    have hpcE : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * 147538) := by
      simpa only [hch, ite_false] using hh9_pc
    have hrun0 : DetRun oracle (submission.image .commit) h9
        (if 0 < chunks then 3 + 8194 * chunks else 0) h9
        (if 0 < chunks then 3 + 22530 * chunks else 0) (2048 * chunks) := by
      rw [show (if 0 < chunks then 3 + 8194 * chunks else 0) = 0 by simp only [hch, ite_false],
          show (if 0 < chunks then 3 + 22530 * chunks else 0) = 0 by simp only [hch, ite_false],
          show 2048 * chunks = 0 by omega]
      exact DetRun.refl oracle (submission.image .commit) h9
    exact ⟨h9, hrun0, hpcE, fun _ _ _ _ _ _ => rfl,
      by rw [hx10]; exact congrArg (BitVec.ofNat 64) (by omega),
      by rw [hx12]; exact congrArg (BitVec.ofNat 64) (by omega),
      fun _ h => by omega,
      fun _ _ _ _ => getByte_of_mem_eq hh_mem _,
      by rw [show C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * chunks) =
            C_TD + levelBase (lvlIdx + 2) by omega]
         exact MemPreservedOutside.of_mem_eq hh_mem _ _⟩

/-- Phase 3A Stage B (240-bit tail pairs, words `147538..147550`). -/
theorem commit_bin_level_stageB (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks remPairs : Nat) (hlvl : lvlIdx < 4)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 2048)
    (hrem : remPairs = (calls % 2048) / 2)
    (s0 sb : MachineState)
    (hpcB : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 147538))
    (hx5B : sb.getReg .x5 = 0#64) (hx11B : sb.getReg .x11 = 96#64) (hx13B : sb.getReg .x13 = 0#64)
    (hx20B : sb.getReg .x20 = BitVec.ofNat 64 calls)
    (hx10B : sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2048 * chunks) - 96))
    (hx12B : sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * chunks) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 1) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64) 32 = 0)
    (hdigB : ∀ idx < 2048 * chunks,
      readBuffer sb (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hgapB : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
      sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)))
    (hpresB : MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 2))
      (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * chunks))) :
    ∃ st,
      DetRun oracle (submission.image .commit) sb (3 + 10 * remPairs) st (3 + 24 * remPairs) (2 * remPairs) ∧
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * 147551) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → st.getReg r = sb.getReg r) ∧
      st.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (2048 * chunks + 2 * remPairs) - 96) ∧
      st.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * chunks + remPairs) - 64) ∧
      (∀ idx < 2048 * chunks + 2 * remPairs,
        readBuffer st (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx) ∧
      (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
        st.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 st (C_TD + levelBase (lvlIdx + 2))
        (C_TD + levelBase (lvlIdx + 2) + 96 * (1024 * chunks + remPairs)) := by
  have h2048 : 2 * (1024 * chunks) = 2048 * chunks := by omega
  simpa only [h2048] using
    commit_bin_stageB_gen h768 oracle msg salts 147538 147541 147551 8 22 2048 (2047#12) (44#13) (8156#13)
      rfl rfl pc_beq_147540 pc_bne_147550 c_bv64_and_2047 lvlIdx calls (1024 * chunks) remPairs (by omega)
      hcalls hrem (by omega) s0 sb hpcB hx5B hx11B hx13B hx20B
      (by rw [h2048]; exact hx10B) hx12B hsrc hsrcGap
      (by rw [h2048]; exact hdigB) hgapB hpresB
      (commit_fetch_commitMid3Instr sb 147538 (by omega) (by omega) hpcB)
      (fun st hst => commit_fetch_commitMid3Instr st 147539 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid3Instr st 147540 (by omega) (by omega) hst)
      (fun q hq sm hp h5 h11 h13 _ h10 h12 hs hsg =>
        commit_bin_pair h768 oracle msg salts lvlIdx 147541 q hlvl (by omega) sm
          (fun j hj st hst => commit_fetch_bin_tail_pair st j hj hst) hp h5 h11 h13 h10 h12 hs hsg)
      (fun st hst => commit_fetch_commitMid3Instr st 147549 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitMid3Instr st 147550 (by omega) (by omega) hst)

/-- Phase 3B Stage A (238-bit bulk chunks, words `147593..148365`). -/
theorem commit_bin238_level_stageA (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks : Nat) (hlo : 4 ≤ lvlIdx) (hhi : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 128)
    (s0 h9 : MachineState)
    (hh_mem : h9.mem = s0.mem)
    (hh9_pc : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then 147593 else 148366)))
    (hx5 : h9.getReg .x5 = 0#64) (hx11 : h9.getReg .x11 = 96#64) (hx13 : h9.getReg .x13 = 0#64)
    (hx27 : h9.getReg .x27 = mask238Word)
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
        (if 0 < chunks then 4 + 769 * chunks else 0) sb
        (if 0 < chunks then 4 + 1665 * chunks else 0) (128 * chunks) ∧
      sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 148366) ∧
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
        (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks)) :=
  commit_bin_stageA_gen h768 oracle msg salts 147593 147597 148366 12 26 (5120#13) rfl rfl pc_bne_148365
    lvlIdx calls chunks hhi hcalls hchunks s0 h9 hh_mem hh9_pc hx5 hx11 hx13 hx10 hx12 hx22
    hsrc hsrcGap
    (fun st hst => commit_fetch_commitMid3Instr st 147593 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3Instr st 147594 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3Instr st 147595 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3Instr st 147596 (by omega) (by omega) hst)
    (fun m q hm hq sm hp h5 h11 h13 h27 h10 h12 hs hsg =>
      commit_bin238_pair h768 oracle msg salts lvlIdx (147597 + 12 * m) q hlo hhi (by omega) sm
        (fun j hj st hst => commit_fetch_bin238_bulk st m j hm hj hst)
        hp h5 h11 h13 (h27.trans hx27) h10 h12 hs hsg)
    (fun st hst => commit_fetch_commitTailInstr st 148365 (by omega) (by omega) hst)

/-- Phase 3B Stage B (238-bit tail pairs, words `148366..148382`). -/
theorem commit_bin238_level_stageB (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks remPairs : Nat) (hlo : 4 ≤ lvlIdx) (hhi : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hchunks : chunks = calls / 128)
    (hrem : remPairs = (calls % 128) / 2)
    (s0 sb : MachineState)
    (hpcB : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 148366))
    (hx5B : sb.getReg .x5 = 0#64) (hx11B : sb.getReg .x11 = 96#64) (hx13B : sb.getReg .x13 = 0#64)
    (hx27B : sb.getReg .x27 = mask238Word)
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
      DetRun oracle (submission.image .commit) sb (3 + 14 * remPairs) st (3 + 28 * remPairs) (2 * remPairs) ∧
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * 148383) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → st.getReg r = sb.getReg r) ∧
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
  have h128 : 2 * (64 * chunks) = 128 * chunks := by omega
  simpa only [h128] using
    commit_bin_stageB_gen h768 oracle msg salts 148366 148369 148383 12 26 128 (127#12) (60#13) (8140#13)
      rfl rfl pc_beq_148368 pc_bne_148382 bv64_and_127 lvlIdx calls (64 * chunks) remPairs hhi
      hcalls hrem (by omega) s0 sb hpcB hx5B hx11B hx13B hx20B
      (by rw [h128]; exact hx10B) hx12B hsrc hsrcGap
      (by rw [h128]; exact hdigB) hgapB hpresB
      (commit_fetch_commitTailInstr sb 148366 (by omega) (by omega) hpcB)
      (fun st hst => commit_fetch_commitTailInstr st 148367 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitTailInstr st 148368 (by omega) (by omega) hst)
      (fun q hq sm hp h5 h11 h13 h27 h10 h12 hs hsg =>
        commit_bin238_pair h768 oracle msg salts lvlIdx 148369 q hlo hhi (by omega) sm
          (fun j hj st hst => commit_fetch_bin238_tail_pair st j hj hst)
          hp h5 h11 h13 (h27.trans hx27B) h10 h12 hs hsg)
      (fun st hst => commit_fetch_commitTailInstr st 148381 (by omega) (by omega) hst)
      (fun st hst => commit_fetch_commitTailInstr st 148382 (by omega) (by omega) hst)

end CommitGolfCandidate
