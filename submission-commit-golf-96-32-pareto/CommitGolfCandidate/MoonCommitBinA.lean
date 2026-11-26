import CommitGolfCandidate.MoonCommitExec

/-! Exact RV64IM execution proofs for binary tree levels of the r=2 `commit` image:
- Cost accounting & tree-node masking helpers for Phase 3U (`L3..L4`, unmasked 256-bit),
  Phase 3A (`L5..L8`, 240-bit), and Phase 3B (`L9..L22`, 238-bit)
- `commit_binU_pair` (256-bit), `commit_bin_pair` (240-bit), `commit_mask238_step` + `commit_bin238_pair` (238-bit)
- Unified parameterized Stage A (bulk chunks) and Stage B (tail pairs) instantiated for all three phases. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-- Exact cost accounting for Phase 3U (unmasked 256-bit) binary level `lvlIdx < 2` (`L2->L3`, `L3->L4`). -/
def binULevelSteps (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 2) / 2
  let chunks := calls / 256
  let remPairs := (calls % 256) / 2
  9 + (if 0 < chunks then 4 + 769 * chunks else 0) + (3 + 8 * remPairs) + 2

def binULevelCycles (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 2) / 2
  let chunks := calls / 256
  let remPairs := (calls % 256) / 2
  9 + (if 0 < chunks then 4 + 2561 * chunks else 0) + (3 + 22 * remPairs) + 2

def binULevelCalls (lvlIdx : Nat) : Nat :=
  levelSize (lvlIdx + 2) / 2

/-- Exact cost accounting for Phase 3A (240-bit masked) binary level `2 ≤ lvlIdx < 6` (`L4->L5` .. `L7->L8`). -/
def binLevelSteps (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 2) / 2
  let prom := levelSize (lvlIdx + 2) % 2
  let chunks := calls / 128
  let remPairs := (calls % 128) / 2
  let oddCall := calls % 2
  10 + (if 0 < chunks then 4 + 513 * chunks else 0) + (3 + 10 * remPairs) +
    (if oddCall = 1 then 7 + 9 * prom else 3 + 8 * prom) + 2

def binLevelCycles (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 2) / 2
  let prom := levelSize (lvlIdx + 2) % 2
  let chunks := calls / 128
  let remPairs := (calls % 128) / 2
  let oddCall := calls % 2
  10 + (if 0 < chunks then 4 + 1409 * chunks else 0) + (3 + 24 * remPairs) +
    (if oddCall = 1 then 14 + 9 * prom else 3 + 8 * prom) + 2

def binLevelCalls (lvlIdx : Nat) : Nat :=
  levelSize (lvlIdx + 2) / 2

/-- Exact cost accounting for Phase 3B (238-bit masked) binary level `6 ≤ lvlIdx < 20` (`L8->L9` .. `L21->L22`). -/
def bin238LevelSteps (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 2) / 2
  let prom := levelSize (lvlIdx + 2) % 2
  let chunks := calls / 128
  let remPairs := (calls % 128) / 2
  let oddCall := calls % 2
  10 + (if 0 < chunks then 4 + 769 * chunks else 0) + (3 + 14 * remPairs) +
    (if oddCall = 1 then 9 + 9 * prom else 3 + 8 * prom) + 2

def bin238LevelCycles (lvlIdx : Nat) : Nat :=
  let calls := levelSize (lvlIdx + 2) / 2
  let prom := levelSize (lvlIdx + 2) % 2
  let chunks := calls / 128
  let remPairs := (calls % 128) / 2
  let oddCall := calls % 2
  10 + (if 0 < chunks then 4 + 1665 * chunks else 0) + (3 + 28 * remPairs) +
    (if oddCall = 1 then 16 + 9 * prom else 3 + 8 * prom) + 2

def bin238LevelCalls (lvlIdx : Nat) : Nat :=
  levelSize (lvlIdx + 2) / 2

theorem levelSize_le_max (l : Nat) (hl : l ≤ 23) : levelSize l ≤ 16777216 := by
  interval_cases l <;> decide

theorem levelBase_mod8 (l : Nat) (hl : l ≤ 23) : levelBase l % 8 = 0 := by
  interval_cases l <;> decide

theorem levelBytes_eq_gap (l : Nat) (hl1 : 2 ≤ l) (hl2 : l < 23) :
    levelBytes l = ((levelSize l + 1) / 2) * 96 := by
  unfold levelBytes
  have h1 : ¬ (l < 2) := by omega
  simp only [h1, ite_false, hl2, ite_true]

theorem nodeVal_bin_unmasked (c96 : Comp96) (msg : Message) (salts : Index → Salt192)
    (lvlIdx idx : Nat) (hlt : 2 * idx + 1 < levelSize (lvlIdx + 2)) (hlvl2 : lvlIdx < 2) :
    c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (2 * idx))
      (nodeVal c96 msg salts (lvlIdx + 2) (2 * idx + 1))) =
      nodeVal c96 msg salts (lvlIdx + 3) idx := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (lvlIdx + 3) idx = _
  rw [nodeValFromLeaves]
  dsimp only
  unfold maskLevel
  have h1 : lvlIdx + 3 < 5 ∨ lvlIdx + 3 = 23 := Or.inl (by omega)
  simp only [hlt, ite_true, h1]
  rfl

theorem nodeVal_bin_masked (c96 : Comp96) (msg : Message) (salts : Index → Salt192)
    (lvlIdx idx : Nat) (hlt : 2 * idx + 1 < levelSize (lvlIdx + 2))
    (hlo : 2 ≤ lvlIdx) (hhi : lvlIdx < 6) :
    mask240 (c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (2 * idx))
      (nodeVal c96 msg salts (lvlIdx + 2) (2 * idx + 1)))) =
      nodeVal c96 msg salts (lvlIdx + 3) idx := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (lvlIdx + 3) idx = _
  rw [nodeValFromLeaves]
  dsimp only
  unfold maskLevel
  have h1 : ¬ (lvlIdx + 3 < 5 ∨ lvlIdx + 3 = 23) := by omega
  have h2 : lvlIdx + 3 < 9 := by omega
  simp only [hlt, ite_true, h1, ite_false, h2]
  rfl

theorem nodeVal_bin_masked238 (c96 : Comp96) (msg : Message) (salts : Index → Salt192)
    (lvlIdx idx : Nat) (hlt : 2 * idx + 1 < levelSize (lvlIdx + 2))
    (hlo : 6 ≤ lvlIdx) (hhi : lvlIdx < 20) :
    mask238 (c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (2 * idx))
      (nodeVal c96 msg salts (lvlIdx + 2) (2 * idx + 1)))) =
      nodeVal c96 msg salts (lvlIdx + 3) idx := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (lvlIdx + 3) idx = _
  rw [nodeValFromLeaves]
  dsimp only
  unfold maskLevel
  have h1 : ¬ (lvlIdx + 3 < 5 ∨ lvlIdx + 3 = 23) := by omega
  have h2 : ¬ (lvlIdx + 3 < 9) := by omega
  simp only [hlt, ite_true, h1, ite_false, h2]
  rfl

theorem nodeVal_bin_promoted (c96 : Comp96) (msg : Message) (salts : Index → Salt192)
    (lvlIdx idx : Nat) (h1 : ¬ (2 * idx + 1 < levelSize (lvlIdx + 2)))
    (h2 : 2 * idx < levelSize (lvlIdx + 2)) :
    nodeVal c96 msg salts (lvlIdx + 2) (2 * idx) = nodeVal c96 msg salts (lvlIdx + 3) idx := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (lvlIdx + 3) idx = _
  rw [nodeValFromLeaves]
  dsimp only
  simp only [h1, ite_false, h2, ite_true]
  rfl

theorem nodeVal_root_eq (c96 : Comp96) (msg : Message) (salts : Index → Salt192) :
    c96 (binaryInput (nodeVal c96 msg salts 22 0) (nodeVal c96 msg salts 22 1)) =
      rootVal c96 msg salts := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (20 + 3) 0 = _
  rw [nodeValFromLeaves]
  dsimp only
  unfold maskLevel
  have hlt : 2 * 0 + 1 < levelSize (20 + 2) := by
    rw [show 20 + 2 = 22 from rfl, levelSize_22]; omega
  have h23 : 20 + 3 < 5 ∨ (20 + 3 : Nat) = 23 := Or.inr rfl
  simp only [hlt, h23, ite_true]
  rfl

/-- Single-step wrappers for the non-parametric r=2 slices. -/
theorem commit_step1_mid2B {oracle : Oracle} {s : MachineState} {idx : Nat} {ins : Instr}
    (hlo : 59432 ≤ idx) (hhi : idx < 59460)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hins : commitMid2BInstr idx = .base ins)
    (hstep : ordinaryStep s (.base ins) = some (execInstrBr s ins) := by rfl)
    (hcyc : instructionCycles (.base ins) = 1 := by rfl) :
    DetRun oracle (submission.image .commit) s 1 (execInstrBr s ins) 1 0 := by
  have hf := commit_fetch_commitMid2BInstr s idx hlo hhi hpc
  rw [hins] at hf
  exact DetRun.step1 hf hstep hcyc

theorem commit_step1_mid3U {oracle : Oracle} {s : MachineState} {idx : Nat} {ins : Instr}
    (hlo : 60228 ≤ idx) (hhi : idx < 60257)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hins : commitMid3UInstr idx = .base ins)
    (hstep : ordinaryStep s (.base ins) = some (execInstrBr s ins) := by rfl)
    (hcyc : instructionCycles (.base ins) = 1 := by rfl) :
    DetRun oracle (submission.image .commit) s 1 (execInstrBr s ins) 1 0 := by
  have hf := commit_fetch_commitMid3UInstr s idx hlo hhi hpc
  rw [hins] at hf
  exact DetRun.step1 hf hstep hcyc

theorem commit_step1_mid3A {oracle : Oracle} {s : MachineState} {idx : Nat} {ins : Instr}
    (hlo : 60769 ≤ idx) (hhi : idx < 60828)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hins : commitMid3AInstr idx = .base ins)
    (hstep : ordinaryStep s (.base ins) = some (execInstrBr s ins) := by rfl)
    (hcyc : instructionCycles (.base ins) = 1 := by rfl) :
    DetRun oracle (submission.image .commit) s 1 (execInstrBr s ins) 1 0 := by
  have hf := commit_fetch_commitMid3AInstr s idx hlo hhi hpc
  rw [hins] at hf
  exact DetRun.step1 hf hstep hcyc

theorem commit_step1_tail {oracle : Oracle} {s : MachineState} {idx : Nat} {ins : Instr}
    (hlo : 61596 ≤ idx) (hhi : idx < 61667)
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

/-! ### 1. Isolated Branch Targets for Stage A and Stage B (Phases 3U, 3A, 3B) -/

private theorem pc_bne_60228 :
    BitVec.ofNat 64 (0x1000 + 4 * 60228) + signExtend13 (5120#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 59460) := by decide

private theorem pc_beq_60231 :
    BitVec.ofNat 64 (0x1000 + 4 * 60231) + signExtend13 (36#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 60240) := by decide

private theorem pc_bne_60239 :
    BitVec.ofNat 64 (0x1000 + 4 * 60239) + signExtend13 (8164#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 60232) := by decide

private theorem pc_bne_60769 :
    BitVec.ofNat 64 (0x1000 + 4 * 60769) + signExtend13 (6144#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 60257) := by decide

private theorem pc_beq_60772 :
    BitVec.ofNat 64 (0x1000 + 4 * 60772) + signExtend13 (44#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 60783) := by decide

private theorem pc_bne_60782 :
    BitVec.ofNat 64 (0x1000 + 4 * 60782) + signExtend13 (8156#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 60773) := by decide

private theorem pc_bne_61596 :
    BitVec.ofNat 64 (0x1000 + 4 * 61596) + signExtend13 (5120#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 60828) := by decide

private theorem pc_beq_61599 :
    BitVec.ofNat 64 (0x1000 + 4 * 61599) + signExtend13 (60#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 61614) := by decide

private theorem pc_bne_61613 :
    BitVec.ofNat 64 (0x1000 + 4 * 61613) + signExtend13 (8140#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 61600) := by decide

/-! ### 2. Unmasked 256-Bit Binary Pair (`binUPairInstr`: 6 steps, 20 cycles, 2 calls) -/

theorem commit_binU_pair (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx basePc q : Nat) (hlvl : lvlIdx < 2) (hq : 2 * q + 1 < levelSize (lvlIdx + 2) / 2)
    (s : MachineState)
    (hfetch : ∀ j < 6, ∀ st : MachineState,
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + j)) →
      fetch (submission.image .commit) st = some (binUPairInstr j))
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q) - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q - 64))
    (hsrc : ∀ j < 4, readBuffer s (C_TD + levelBase (lvlIdx + 2) + gapOffset (4 * q + j)) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (4 * q + j))
    (hsrcGap : ∀ p < 2, readBuffer s (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + p) + 64) 32 = 0) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 6 s' 20 2 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 6)) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) ∧
      readBuffer s' (C_TD + levelBase (lvlIdx + 3) + 96 * q) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q) ∧
      readBuffer s' (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q + 1) ∧
      MemPreservedOutside s s' (C_TD + levelBase (lvlIdx + 3) + 96 * q)
        (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcB := levelBase_bound (lvlIdx + 2) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 3) (by omega)
  have htb := treeBytes_eq
  have hsrcAl := levelBase_mod8 (lvlIdx + 2) (by omega)
  have hdstAl := levelBase_mod8 (lvlIdx + 3) (by omega)
  have hsrcBytes := levelBytes_eq_gap (lvlIdx + 2) (by omega) (by omega)
  have hdstBytes := levelBytes_eq_gap (lvlIdx + 3) (by omega) (by omega)
  have hdstSize : levelSize (lvlIdx + 3) = (levelSize (lvlIdx + 2) + 1) / 2 :=
    levelSize_step (lvlIdx + 2) (by omega)
  have hbase_step : levelBase (lvlIdx + 3) = levelBase (lvlIdx + 2) + levelBytes (lvlIdx + 2) := rfl
  have hsrc_lt : 96 * (2 * q + 1) + 96 ≤ levelBytes (lvlIdx + 2) := by rw [hsrcBytes]; omega
  have hdst_lt : 96 * q + 64 ≤ levelBytes (lvlIdx + 3) := by rw [hdstBytes, hdstSize]; omega
  let s1 := execInstrBr s (.ADDI .x10 .x10 (96#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (64#12))
  let raw0 := c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q))
    (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 1)))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q)) raw0
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) := pc_step_idx s basePc hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) := pc_step_idx s1 (basePc + 1) hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) := pc_step_idx s2 (basePc + 2) hs2_pc
  have hm2 : s2.mem = s.mem := (mem_exec_ADDI s1 .x12 .x12 (64#12)).trans (mem_exec_ADDI s .x10 .x10 (96#12))
  have hs2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s2.getReg r = s.getReg r := fun r h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
  have hs1_a0 : s1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_a0 : s2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs1_a0]
  have hs2_a2 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q) := by
    have h1x12 : s1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q - 64) := by
      simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hx12]
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h1x12,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_in : readBuffer s2 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) 96 =
      binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q))
        (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 1)) := by
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
      ((hs2_reg_other .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg_other .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg_other .x13 (by decide) (by decide)).trans hx13)
      (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) (C_TD + levelBase (lvlIdx + 3) + 96 * q) hs2_a0 hs2_a2
      (by omega) (by omega) (by omega) (by omega) raw0 (by rw [hs2_in])
  have hs3_pres : MemPreservedOutside s s3 (C_TD + levelBase (lvlIdx + 3) + 96 * q)
      (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) :=
    (MemPreservedOutside.of_mem_eq hm2 _ _).trans (memPreserved_writeBits s2 _ raw0 (by omega))
  have hs3_dig0 : readBuffer s3 (C_TD + levelBase (lvlIdx + 3) + 96 * q) 32 =
      nodeVal c96 msg salts (lvlIdx + 3) (2 * q) := by
    rw [writeBits_readBuffer_digest]
    have h4 : 2 * (2 * q) = 4 * q := by omega
    rw [show raw0 = c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q)))
      (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q) + 1))) by rw [h4]]
    exact nodeVal_bin_unmasked c96 msg salts lvlIdx (2 * q) (by omega) hlvl
  -- Second call (steps 3..5)
  let s4 := execInstrBr s3 (.ADDI .x10 .x10 (96#12))
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 (32#12))
  let raw1 := c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 2))
    (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 3)))
  let s6 := writeBits s5 (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32)) raw1
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 4)) := pc_step_idx s3 (basePc + 3) hs3_pc
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 5)) := pc_step_idx s4 (basePc + 4) hs4_pc
  have hs6_pc : s6.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 6)) := pc_step_idx s5 (basePc + 5) hs5_pc
  have hm5 : s5.mem = s3.mem := (mem_exec_ADDI s4 .x12 .x12 (32#12)).trans (mem_exec_ADDI s3 .x10 .x10 (96#12))
  have hs5_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s5.getReg r = s.getReg r := fun r h10 h12 => by
    have h53 : s5.getReg r = s3.getReg r := by
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
    exact (h53.trans (writeBits_register s2 _ raw0 r)).trans (hs2_reg_other r h10 h12)
  have hs3_a0 : s3.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) :=
    (writeBits_register s2 _ raw0 .x10).trans hs2_a0
  have hs3_a2 : s3.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q) :=
    (writeBits_register s2 _ raw0 .x12).trans hs2_a2
  have hs4_a0 : s4.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs3_a0,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs5_a0 : s5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs4_a0]
  have hs5_a2 : s5.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) := by
    have h4x12 : s4.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hs3_a2]
    simp only [s5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h4x12,
      add_signExtend12_ofNat_small _ 32 (by omega)]
  have hs5_in : readBuffer s5 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) 96 =
      binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 2))
        (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 3)) := by
    rw [readBuffer_of_mem_eq hm5, hs3_pres.readBuffer_eq (by omega) (by omega),
      readBuffer_binary_of_zero_gap s _ (hsrcGap 1 (by omega))]
    have h2 := hsrc 2 (by omega); have h3 := hsrc 3 (by omega)
    rw [show gapOffset (4 * q + 2) = 96 * (2 * q + 1) by rw [show 4 * q + 2 = 2 * (2 * q + 1) by omega, gapOffset_even]] at h2
    rw [show gapOffset (4 * q + 3) = 96 * (2 * q + 1) + 32 by rw [show 4 * q + 3 = 2 * (2 * q + 1) + 1 by omega, gapOffset_odd],
        ← Nat.add_assoc] at h3
    rw [h2, h3]
  have hst3 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (hfetch 3 (by omega) s3 hs3_pc) rfl
  have hst4 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (hfetch 4 (by omega) s4 hs4_pc) rfl
  have hst5 : DetRun oracle (submission.image .commit) s5 1 s6 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s5)
      (hfetch 5 (by omega) s5 hs5_pc)
      ((hs5_reg_other .x5 (by decide) (by decide)).trans hx5)
      ((hs5_reg_other .x11 (by decide) (by decide)).trans hx11)
      ((hs5_reg_other .x13 (by decide) (by decide)).trans hx13)
      (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32)
      hs5_a0 hs5_a2 (by omega) (by omega) (by omega) (by omega) raw1 (by rw [hs5_in])
  have hs36_pres : MemPreservedOutside s3 s6 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32)
      (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64) :=
    (MemPreservedOutside.of_mem_eq hm5 _ _).trans (memPreserved_writeBits s5 _ raw1 (by omega))
  refine ⟨s6, ((((hst0.trans hst1).trans hst2).trans hst3).trans hst4).trans hst5,
    hs6_pc, fun r _ h10 h12 => (writeBits_register s5 _ raw1 r).trans (hs5_reg_other r h10 h12),
    (writeBits_register s5 _ raw1 .x10).trans hs5_a0,
    (writeBits_register s5 _ raw1 .x12).trans hs5_a2, ?_, ?_, ?_⟩
  · rw [hs36_pres.readBuffer_eq (by omega) (by omega)]; exact hs3_dig0
  · rw [writeBits_readBuffer_digest]
    have h4a : 2 * (2 * q + 1) = 4 * q + 2 := by omega
    have h4b : 2 * (2 * q + 1) + 1 = 4 * q + 3 := by omega
    rw [show raw1 = c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q + 1)))
      (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q + 1) + 1))) by rw [h4b, h4a]]
    exact nodeVal_bin_unmasked c96 msg salts lvlIdx (2 * q + 1) (by omega) hlvl
  · exact (hs3_pres.mono (le_refl _) (by omega)).trans (hs36_pres.mono (by omega) (le_refl _))

/-! ### 3. 240-Bit Masked Binary Pair (`binPairInstr`: 8 steps, 22 cycles, 2 calls) -/

theorem commit_bin_pair (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx basePc q : Nat) (hlo : 2 ≤ lvlIdx) (hhi : lvlIdx < 6)
    (hq : 2 * q + 1 < levelSize (lvlIdx + 2) / 2) (s : MachineState)
    (hfetch : ∀ j < 8, ∀ st : MachineState,
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + j)) →
      fetch (submission.image .commit) st = some (binPairInstr j))
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q) - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q - 64))
    (hsrc : ∀ j < 4, readBuffer s (C_TD + levelBase (lvlIdx + 2) + gapOffset (4 * q + j)) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (4 * q + j))
    (hsrcGap : ∀ p < 2, readBuffer s (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + p) + 64) 32 = 0) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 8 s' 22 2 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 8)) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) ∧
      readBuffer s' (C_TD + levelBase (lvlIdx + 3) + 96 * q) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q) ∧
      readBuffer s' (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q + 1) ∧
      MemPreservedOutside s s' (C_TD + levelBase (lvlIdx + 3) + 96 * q)
        (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcB := levelBase_bound (lvlIdx + 2) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 3) (by omega)
  have htb := treeBytes_eq
  have hsrcAl := levelBase_mod8 (lvlIdx + 2) (by omega)
  have hdstAl := levelBase_mod8 (lvlIdx + 3) (by omega)
  have hsrcBytes := levelBytes_eq_gap (lvlIdx + 2) (by omega) (by omega)
  have hdstBytes := levelBytes_eq_gap (lvlIdx + 3) (by omega) (by omega)
  have hdstSize : levelSize (lvlIdx + 3) = (levelSize (lvlIdx + 2) + 1) / 2 :=
    levelSize_step (lvlIdx + 2) (by omega)
  have hbase_step : levelBase (lvlIdx + 3) = levelBase (lvlIdx + 2) + levelBytes (lvlIdx + 2) := rfl
  have hsrc_lt : 96 * (2 * q + 1) + 96 ≤ levelBytes (lvlIdx + 2) := by rw [hsrcBytes]; omega
  have hdst_lt : 96 * q + 64 ≤ levelBytes (lvlIdx + 3) := by rw [hdstBytes, hdstSize]; omega
  -- First call + mask240 (steps 0..3)
  let s1 := execInstrBr s (.ADDI .x10 .x10 (96#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (64#12))
  let raw0 := c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q))
    (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 1)))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q)) raw0
  let s4 := execInstrBr s3 (.SH .x12 .x0 (30#12))
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) := pc_step_idx s basePc hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) := pc_step_idx s1 (basePc + 1) hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) := pc_step_idx s2 (basePc + 2) hs2_pc
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 4)) := pc_step_idx s3 (basePc + 3) hs3_pc
  have hm2 : s2.mem = s.mem := (mem_exec_ADDI s1 .x12 .x12 (64#12)).trans (mem_exec_ADDI s .x10 .x10 (96#12))
  have hs2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s2.getReg r = s.getReg r := fun r h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
  have hs4_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s4.getReg r = s.getReg r := fun r h10 h12 =>
    ((reg_exec_SH s3 _ _ _ r).trans (writeBits_register s2 _ raw0 r)).trans (hs2_reg_other r h10 h12)
  have hs1_a0 : s1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_a0 : s2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs1_a0]
  have hs2_a2 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q) := by
    have h1x12 : s1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q - 64) := by
      simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hx12]
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h1x12,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_in : readBuffer s2 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) 96 =
      binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q))
        (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 1)) := by
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
      (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) (C_TD + levelBase (lvlIdx + 3) + 96 * q) hs2_a0 hs2_a2
      (by omega) (by omega) (by omega) (by omega) raw0 (by rw [hs2_in])
  have hs3_a2 : s3.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q) :=
    (writeBits_register s2 _ raw0 .x12).trans hs2_a2
  have hsh0_addr : s3.getReg .x12 + signExtend12 (30#12) =
      BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 30) := by
    rw [hs3_a2, add_signExtend12_ofNat_small _ 30 (by omega)]
  have hst3 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (hfetch 3 (by omega) s3 hs3_pc)
      (ordinaryStep_SH s3 .x12 .x0 (30#12) (by
        rw [hsh0_addr]; exact c_accessValid_ofNat _ 2 (by omega) (by omega)))
  have hs4_mem : s4.mem =
      (s3.setHalfword (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 30)) 0#16).mem := by
    simp only [s4, execInstrBr, hsh0_addr, c_getReg_x0, c_mem_setPC]; rfl
  have hs4_pres : MemPreservedOutside s s4 (C_TD + levelBase (lvlIdx + 3) + 96 * q)
      (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) :=
    ((MemPreservedOutside.of_mem_eq hm2 _ _).trans (memPreserved_writeBits s2 _ raw0 (by omega))).trans
      (((memPreserved_setHalfword s3 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 30) 0#16
        (by omega) (by omega)).mono (by omega) (by omega)).trans (MemPreservedOutside.of_mem_eq hs4_mem _ _))
  have hs4_dig0 : readBuffer s4 (C_TD + levelBase (lvlIdx + 3) + 96 * q) 32 =
      nodeVal c96 msg salts (lvlIdx + 3) (2 * q) := by
    rw [readBuffer_of_mem_eq hs4_mem, sh_zero_mask240 s3 _ (by omega) (by omega), writeBits_readBuffer_digest]
    have h4 : 2 * (2 * q) = 4 * q := by omega
    rw [show raw0 = c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q)))
      (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q) + 1))) by rw [h4]]
    exact nodeVal_bin_masked c96 msg salts lvlIdx (2 * q) (by omega) hlo hhi
  -- Second call + mask240 (steps 4..7)
  let s5 := execInstrBr s4 (.ADDI .x10 .x10 (96#12))
  let s6 := execInstrBr s5 (.ADDI .x12 .x12 (32#12))
  let raw1 := c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 2))
    (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 3)))
  let s7 := writeBits s6 (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32)) raw1
  let s8 := execInstrBr s7 (.SH .x12 .x0 (30#12))
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 5)) := pc_step_idx s4 (basePc + 4) hs4_pc
  have hs6_pc : s6.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 6)) := pc_step_idx s5 (basePc + 5) hs5_pc
  have hs7_pc : s7.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 7)) := pc_step_idx s6 (basePc + 6) hs6_pc
  have hs8_pc : s8.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 8)) := pc_step_idx s7 (basePc + 7) hs7_pc
  have hm6 : s6.mem = s4.mem := (mem_exec_ADDI s5 .x12 .x12 (32#12)).trans (mem_exec_ADDI s4 .x10 .x10 (96#12))
  have hs6_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s6.getReg r = s.getReg r := fun r h10 h12 => by
    have h64 : s6.getReg r = s4.getReg r := by
      simp only [s6, s5, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
    exact h64.trans (hs4_reg_other r h10 h12)
  have hs8_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s8.getReg r = s.getReg r :=
    fun r _ h10 h12 => ((reg_exec_SH s7 _ _ _ r).trans (writeBits_register s6 _ raw1 r)).trans (hs6_reg_other r h10 h12)
  have hs5_a0 : s5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) := by
    have hs4_a0 : s4.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) :=
      ((reg_exec_SH s3 _ _ _ .x10).trans (writeBits_register s2 _ raw0 .x10)).trans hs2_a0
    simp only [s5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs4_a0,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs6_a0 : s6.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) := by
    simp only [s6, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs5_a0]
  have hs6_a2 : s6.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) := by
    have hs5_a2 : s5.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q) := by
      have h54 : s5.getReg .x12 = s4.getReg .x12 := by
        simp only [s5, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide)]
      exact h54.trans ((reg_exec_SH s3 _ _ _ .x12).trans hs3_a2)
    simp only [s6, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs5_a2,
      add_signExtend12_ofNat_small _ 32 (by omega)]
  have hs6_in : readBuffer s6 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) 96 =
      binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 2))
        (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 3)) := by
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
      (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32)
      hs6_a0 hs6_a2 (by omega) (by omega) (by omega) (by omega) raw1 (by rw [hs6_in])
  have hs7_a2 : s7.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) :=
    (writeBits_register s6 _ raw1 .x12).trans hs6_a2
  have hsh1_addr : s7.getReg .x12 + signExtend12 (30#12) =
      BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 62) := by
    rw [hs7_a2, add_signExtend12_ofNat_small _ 30 (by omega)]
  have hst7 : DetRun oracle (submission.image .commit) s7 1 s8 1 0 :=
    DetRun.step1 (hfetch 7 (by omega) s7 hs7_pc)
      (ordinaryStep_SH s7 .x12 .x0 (30#12) (by
        rw [hsh1_addr]; exact c_accessValid_ofNat _ 2 (by omega) (by omega)))
  have hs8_mem : s8.mem =
      (s7.setHalfword (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 62)) 0#16).mem := by
    simp only [s8, execInstrBr, hsh1_addr, c_getReg_x0, c_mem_setPC]; rfl
  have hs48_pres : MemPreservedOutside s4 s8 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32)
      (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64) :=
    ((MemPreservedOutside.of_mem_eq hm6 _ _).trans (memPreserved_writeBits s6 _ raw1 (by omega))).trans
      (((memPreserved_setHalfword s7 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 62) 0#16
        (by omega) (by omega)).mono (by omega) (by omega)).trans (MemPreservedOutside.of_mem_eq hs8_mem _ _))
  refine ⟨s8,
    ((((((hst0.trans hst1).trans hst2).trans hst3).trans hst4).trans hst5).trans hst6).trans hst7,
    hs8_pc, hs8_reg_other,
    ((reg_exec_SH s7 _ _ _ .x10).trans (writeBits_register s6 _ raw1 .x10)).trans hs6_a0,
    (reg_exec_SH s7 _ _ _ .x12).trans hs7_a2, ?_, ?_, ?_⟩
  · rw [hs48_pres.readBuffer_eq (by omega) (by omega)]; exact hs4_dig0
  · have hm : s8.mem =
        (s7.setHalfword (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32 + 30)) 0#16).mem := by
      have : C_TD + levelBase (lvlIdx + 3) + 96 * q + 62 = C_TD + levelBase (lvlIdx + 3) + 96 * q + 32 + 30 := by omega
      rw [← this]; exact hs8_mem
    rw [readBuffer_of_mem_eq hm, sh_zero_mask240 s7 _ (by omega) (by omega), writeBits_readBuffer_digest]
    have h4a : 2 * (2 * q + 1) = 4 * q + 2 := by omega
    have h4b : 2 * (2 * q + 1) + 1 = 4 * q + 3 := by omega
    rw [show raw1 = c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q + 1)))
      (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q + 1) + 1))) by rw [h4b, h4a]]
    exact nodeVal_bin_masked c96 msg salts lvlIdx (2 * q + 1) (by omega) hlo hhi
  · exact (hs4_pres.mono (le_refl _) (by omega)).trans (hs48_pres.mono (by omega) (le_refl _))

/-! ### 4. 238-Bit Mask Step & Masked Binary Pair (`bin238PairInstr`: 12 steps, 26 cycles, 2 calls) -/

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
    (lvlIdx basePc q : Nat) (hlo : 6 ≤ lvlIdx) (hhi : lvlIdx < 20)
    (hq : 2 * q + 1 < levelSize (lvlIdx + 2) / 2) (s : MachineState)
    (hfetch : ∀ j < 12, ∀ st : MachineState,
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + j)) →
      fetch (submission.image .commit) st = some (bin238PairInstr j))
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx27 : s.getReg .x27 = mask238Word)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q) - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q - 64))
    (hsrc : ∀ j < 4, readBuffer s (C_TD + levelBase (lvlIdx + 2) + gapOffset (4 * q + j)) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (4 * q + j))
    (hsrcGap : ∀ p < 2, readBuffer s (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + p) + 64) 32 = 0) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 12 s' 26 2 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 12)) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) ∧
      readBuffer s' (C_TD + levelBase (lvlIdx + 3) + 96 * q) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q) ∧
      readBuffer s' (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q + 1) ∧
      MemPreservedOutside s s' (C_TD + levelBase (lvlIdx + 3) + 96 * q)
        (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcB := levelBase_bound (lvlIdx + 2) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 3) (by omega)
  have htb := treeBytes_eq
  have hsrcAl := levelBase_mod8 (lvlIdx + 2) (by omega)
  have hdstAl := levelBase_mod8 (lvlIdx + 3) (by omega)
  have hsrcBytes := levelBytes_eq_gap (lvlIdx + 2) (by omega) (by omega)
  have hdstBytes := levelBytes_eq_gap (lvlIdx + 3) (by omega) (by omega)
  have hdstSize : levelSize (lvlIdx + 3) = (levelSize (lvlIdx + 2) + 1) / 2 :=
    levelSize_step (lvlIdx + 2) (by omega)
  have hbase_step : levelBase (lvlIdx + 3) = levelBase (lvlIdx + 2) + levelBytes (lvlIdx + 2) := rfl
  have hsrc_lt : 96 * (2 * q + 1) + 96 ≤ levelBytes (lvlIdx + 2) := by rw [hsrcBytes]; omega
  have hdst_lt : 96 * q + 64 ≤ levelBytes (lvlIdx + 3) := by rw [hdstBytes, hdstSize]; omega
  -- Call 0 (steps 0..2) + mask238 (steps 3..5)
  let s1 := execInstrBr s (.ADDI .x10 .x10 (96#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (64#12))
  let raw0 := c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q))
    (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 1)))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q)) raw0
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) := pc_step_idx s basePc hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) := pc_step_idx s1 (basePc + 1) hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) := pc_step_idx s2 (basePc + 2) hs2_pc
  have hm2 : s2.mem = s.mem := (mem_exec_ADDI s1 .x12 .x12 (64#12)).trans (mem_exec_ADDI s .x10 .x10 (96#12))
  have hs2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s2.getReg r = s.getReg r := fun r h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
  have hs1_a0 : s1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_a0 : s2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs1_a0]
  have hs2_a2 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q) := by
    have h1x12 : s1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q - 64) := by
      simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hx12]
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h1x12,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_in : readBuffer s2 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) 96 =
      binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q))
        (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 1)) := by
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
      (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) (C_TD + levelBase (lvlIdx + 3) + 96 * q) hs2_a0 hs2_a2
      (by omega) (by omega) (by omega) (by omega) raw0 (by rw [hs2_in])
  have hs3_a0 : s3.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) :=
    (writeBits_register s2 _ raw0 .x10).trans hs2_a0
  have hs3_a2 : s3.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q) :=
    (writeBits_register s2 _ raw0 .x12).trans hs2_a2
  obtain ⟨s4, hm_run0, hs4_pc', hs4_reg3, hs4_mask0, hs4_mpres0⟩ :=
    commit_mask238_step oracle s3 (basePc + 3) (C_TD + levelBase (lvlIdx + 3) + 96 * q)
      (by omega) (by omega) hs3_pc hs3_a2
      ((writeBits_register s2 _ raw0 .x27).trans ((hs2_reg_other .x27 (by decide) (by decide)).trans hx27))
      (hfetch 3 (by omega) s3 hs3_pc)
      (fun st hst => hfetch 4 (by omega) st (by simpa only [Nat.add_assoc] using hst))
      (fun st hst => hfetch 5 (by omega) st (by simpa only [Nat.add_assoc] using hst))
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 6)) := by
    simpa only [Nat.add_assoc] using hs4_pc'
  have hs4_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s4.getReg r = s.getReg r :=
    fun r h6 h10 h12 => ((hs4_reg3 r h6).trans (writeBits_register s2 _ raw0 r)).trans (hs2_reg_other r h10 h12)
  have hs4_pres : MemPreservedOutside s s4 (C_TD + levelBase (lvlIdx + 3) + 96 * q)
      (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) :=
    ((MemPreservedOutside.of_mem_eq hm2 _ _).trans (memPreserved_writeBits s2 _ raw0 (by omega))).trans
      (hs4_mpres0.mono (by omega) (le_refl _))
  have hs4_dig0 : readBuffer s4 (C_TD + levelBase (lvlIdx + 3) + 96 * q) 32 =
      nodeVal c96 msg salts (lvlIdx + 3) (2 * q) := by
    rw [hs4_mask0, writeBits_readBuffer_digest]
    have h4 : 2 * (2 * q) = 4 * q := by omega
    rw [show raw0 = c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q)))
      (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q) + 1))) by rw [h4]]
    exact nodeVal_bin_masked238 c96 msg salts lvlIdx (2 * q) (by omega) hlo hhi
  -- Call 1 (steps 6..8) + mask238 (steps 9..11)
  let s5 := execInstrBr s4 (.ADDI .x10 .x10 (96#12))
  let s6 := execInstrBr s5 (.ADDI .x12 .x12 (32#12))
  let raw1 := c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 2))
    (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 3)))
  let s7 := writeBits s6 (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32)) raw1
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
  have hs5_a0 : s5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) := by
    have hs4_a0 : s4.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q)) :=
      (hs4_reg3 .x10 (by decide)).trans hs3_a0
    simp only [s5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs4_a0,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs6_a0 : s6.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) := by
    simp only [s6, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs5_a0]
  have hs6_a2 : s6.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) := by
    have hs5_a2 : s5.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q) := by
      have h54 : s5.getReg .x12 = s4.getReg .x12 := by
        simp only [s5, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide)]
      exact h54.trans ((hs4_reg3 .x12 (by decide)).trans hs3_a2)
    simp only [s6, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs5_a2,
      add_signExtend12_ofNat_small _ 32 (by omega)]
  have hs6_in : readBuffer s6 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) 96 =
      binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 2))
        (nodeVal c96 msg salts (lvlIdx + 2) (4 * q + 3)) := by
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
      (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32)
      hs6_a0 hs6_a2 (by omega) (by omega) (by omega) (by omega) raw1 (by rw [hs6_in])
  have hs7_a0 : s7.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) :=
    (writeBits_register s6 _ raw1 .x10).trans hs6_a0
  have hs7_a2 : s7.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) :=
    (writeBits_register s6 _ raw1 .x12).trans hs6_a2
  obtain ⟨s8, hm_run1, hs8_pc', hs8_reg7, hs8_mask1, hs8_mpres1⟩ :=
    commit_mask238_step oracle s7 (basePc + 9) (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32)
      (by omega) (by omega) hs7_pc hs7_a2
      ((writeBits_register s6 _ raw1 .x27).trans ((hs6_reg_other .x27 (by decide) (by decide) (by decide)).trans hx27))
      (hfetch 9 (by omega) s7 hs7_pc)
      (fun st hst => hfetch 10 (by omega) st (by simpa only [Nat.add_assoc] using hst))
      (fun st hst => hfetch 11 (by omega) st (by simpa only [Nat.add_assoc] using hst))
  have hs48_pres : MemPreservedOutside s4 s8 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32)
      (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64) :=
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
    rw [show raw1 = c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q + 1)))
      (nodeVal c96 msg salts (lvlIdx + 2) (2 * (2 * q + 1) + 1))) by rw [h4b, h4a]]
    exact nodeVal_bin_masked238 c96 msg salts lvlIdx (2 * q + 1) (by omega) hlo hhi
  · exact (hs4_pres.mono (le_refl _) (by omega)).trans (hs48_pres.mono (by omega) (le_refl _))

/-! ### 5. Parameterized Stage A (Bulk `chunkPairs`-Pair Chunks) -/

private theorem commit_bin_stageA_setup_gen (oracle : Oracle)
    (pcSetup chunkPairs sh1 sh2 lvlIdx calls chunks : Nat) (hlvl : lvlIdx < 20)
    (hsh1_lt : sh1 < 64) (hsh2_lt : sh2 < 64)
    (hsh1 : 2 ^ sh1 = 64 * chunkPairs) (hsh2 : 2 ^ sh2 = 128 * chunkPairs)
    (hcalls : calls = levelSize (lvlIdx + 2) / 2)
    (hchunks : chunks = calls / (2 * chunkPairs))
    (h9 : MachineState)
    (hpcS : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * pcSetup))
    (hx10 : h9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) - 96))
    (hx22 : h9.getReg .x22 = BitVec.ofNat 64 chunks)
    (hf0 : fetch (submission.image .commit) h9 = some (.base (.SLLI .x6 .x22 (BitVec.ofNat 6 sh1))))
    (hf1 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 1)) →
      fetch (submission.image .commit) st = some (.base (.SLLI .x7 .x22 (BitVec.ofNat 6 sh2))))
    (hf2 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 2)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x6 .x6 .x7)))
    (hf3 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 3)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x19 .x10 .x6))) :
    ∃ b3,
      DetRun oracle (submission.image .commit) h9 4 b3 4 0 ∧
      b3.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 4)) ∧
      b3.mem = h9.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x19 → b3.getReg r = h9.getReg r) ∧
      b3.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * chunkPairs * chunks) - 96) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hsrcSize_le := levelSize_le_max (lvlIdx + 2) (by omega)
  have hch_le : 2 * chunkPairs * chunks ≤ calls := by
    rw [hchunks]; exact Nat.mul_div_le calls (2 * chunkPairs)
  let b0 := execInstrBr h9 (.SLLI .x6 .x22 (BitVec.ofNat 6 sh1))
  let b1 := execInstrBr b0 (.SLLI .x7 .x22 (BitVec.ofNat 6 sh2))
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
  have hb3_x19 : b3.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * chunkPairs * chunks) - 96) := by
    have h1_lt : chunks * 2 ^ sh1 < 2 ^ 64 := by
      rw [hsh1]
      have : chunks * (64 * chunkPairs) = 32 * (2 * chunkPairs * chunks) := by ring
      omega
    have h2_lt : chunks * 2 ^ sh2 < 2 ^ 64 := by
      rw [hsh2]
      have : chunks * (128 * chunkPairs) = 64 * (2 * chunkPairs * chunks) := by ring
      omega
    have hb0_x6 : b0.getReg .x6 = BitVec.ofNat 64 (chunks * 2 ^ sh1) := by
      simp only [b0, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hx22]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsh1_lt]
      exact bv64_shiftLeft_ofNat chunks sh1 h1_lt
    have hb1_x7 : b1.getReg .x7 = BitVec.ofNat 64 (chunks * 2 ^ sh2) := by
      have : b0.getReg .x22 = BitVec.ofNat 64 chunks := by
        simp only [b0, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x22 (by decide), hx22]
      simp only [b1, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x7 ≠ .x0), this]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsh2_lt]
      exact bv64_shiftLeft_ofNat chunks sh2 h2_lt
    have hsum : chunks * 2 ^ sh1 + chunks * 2 ^ sh2 = 96 * (2 * chunkPairs * chunks) := by
      rw [hsh1, hsh2]; ring
    have hb2_x6 : b2.getReg .x6 = BitVec.ofNat 64 (96 * (2 * chunkPairs * chunks)) := by
      have : b1.getReg .x6 = BitVec.ofNat 64 (chunks * 2 ^ sh1) := by
        simp only [b1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x7 .x6 (by decide), hb0_x6]
      simp only [b2, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), this, hb1_x7, ← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) hsum
    have hb2_x10 : b2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) - 96) := by
      simp only [b2, b1, b0, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x6 .x10 (by decide), getReg_setReg_ne' .x7 .x10 (by decide), hx10]
    simp only [b3, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x19 ≠ .x0), hb2_x10, hb2_x6, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  exact ⟨b3, hb_run, hb3_pc, hb3_mem, hb3_reg, hb3_x19⟩

private theorem commit_bin_stageA_chunk_gen (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (pcBulk pcExit chunkPairs pairSteps pairCyc : Nat) (bneImm : BitVec 13)
    (hcp_pos : 0 < chunkPairs)
    (hbne_exit : pcBulk + pairSteps * chunkPairs + 1 = pcExit)
    (hbne_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * chunkPairs)) + signExtend13 bneImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcBulk))
    (lvlIdx calls chunks n : Nat) (hlvl : lvlIdx < 20)
    (hcalls : calls = levelSize (lvlIdx + 2) / 2)
    (hchunks : chunks = calls / (2 * chunkPairs)) (hn : n < chunks)
    (s0 sn : MachineState)
    (hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * pcBulk))
    (hx5 : sn.getReg .x5 = 0#64) (hx11 : sn.getReg .x11 = 96#64) (hx13 : sn.getReg .x13 = 0#64)
    (hx19 : sn.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * chunkPairs * chunks) - 96))
    (hx10n : sn.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * chunkPairs * n) - 96))
    (hx12n : sn.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * n) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 2),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) 32 = 0)
    (hpresn : MemPreservedOutside s0 sn (C_TD + levelBase (lvlIdx + 3))
      (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * n)))
    (hpair : ∀ (m q : Nat), m < chunkPairs → 2 * q + 1 < calls → ∀ (sm : MachineState),
      sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * m)) →
      sm.getReg .x5 = 0#64 → sm.getReg .x11 = 96#64 → sm.getReg .x13 = 0#64 →
      sm.getReg .x27 = sn.getReg .x27 →
      sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q) - 96) →
      sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q - 64) →
      (∀ j < 4, readBuffer sm (C_TD + levelBase (lvlIdx + 2) + gapOffset (4 * q + j)) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (4 * q + j)) →
      (∀ p < 2, readBuffer sm (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + p) + 64) 32 = 0) →
      ∃ sp,
        DetRun oracle (submission.image .commit) sm pairSteps sp pairCyc 2 ∧
        sp.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * m + pairSteps)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sp.getReg r = sm.getReg r) ∧
        sp.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) ∧
        sp.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 3) + 96 * q) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q + 1) ∧
        MemPreservedOutside sm sp (C_TD + levelBase (lvlIdx + 3) + 96 * q)
          (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64))
    (hbne_fetch : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * chunkPairs)) →
      fetch (submission.image .commit) st = some (.base (.BNE .x10 .x19 bneImm))) :
    ∃ sbne,
      DetRun oracle (submission.image .commit) sn (pairSteps * chunkPairs + 1) sbne
        (pairCyc * chunkPairs + 1) (2 * chunkPairs) ∧
      sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n + 1 < chunks then pcBulk else pcExit)) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sbne.getReg r = sn.getReg r) ∧
      sbne.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * chunkPairs * (n + 1)) - 96) ∧
      sbne.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * (n + 1)) - 64) ∧
      (∀ idx, 2 * chunkPairs * n ≤ idx → idx < 2 * chunkPairs * (n + 1) →
        readBuffer sbne (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx) ∧
      (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
        sbne.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
        sn.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
      MemPreservedOutside sn sbne (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * n))
        (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * (n + 1))) := by
  have hC_TD : C_TD = 4294971424 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcSize_le := levelSize_le_max (lvlIdx + 2) (by omega)
  have hdstSize_eq : levelSize (lvlIdx + 3) = (levelSize (lvlIdx + 2) + 1) / 2 :=
    levelSize_step (lvlIdx + 2) (by omega)
  have hsrcB := levelBase_bound (lvlIdx + 2) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 3) (by omega)
  have htb := treeBytes_eq
  have hsrcBytes := levelBytes_eq_gap (lvlIdx + 2) (by omega) (by omega)
  have hdstBytes := levelBytes_eq_gap (lvlIdx + 3) (by omega) (by omega)
  have hbase_step : levelBase (lvlIdx + 3) = levelBase (lvlIdx + 2) + levelBytes (lvlIdx + 2) := rfl
  have hch_le : 2 * chunkPairs * chunks ≤ calls := by
    rw [hchunks]; exact Nat.mul_div_le calls (2 * chunkPairs)
  have hn1_le : 2 * chunkPairs * (n + 1) ≤ calls :=
    (Nat.mul_le_mul_left (2 * chunkPairs) (by omega : n + 1 ≤ chunks)).trans hch_le
  have hpairs : ∀ m ≤ chunkPairs,
      ∃ sm,
        DetRun oracle (submission.image .commit) sn (pairSteps * m) sm (pairCyc * m) (2 * m) ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * m)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sm.getReg r = sn.getReg r) ∧
        sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * (chunkPairs * n + m)) - 96) ∧
        sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * n + m) - 64) ∧
        (∀ idx, 2 * chunkPairs * n ≤ idx → idx < 2 * chunkPairs * n + 2 * m →
          readBuffer sm (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
            nodeVal c96 msg salts (lvlIdx + 3) idx) ∧
        (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
          sm.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
        MemPreservedOutside sn sm (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * n))
          (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * n + m)) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨sn, DetRun.refl _ _ _, by simpa only [Nat.mul_zero, Nat.add_zero] using hpc_in,
        fun _ _ _ _ => rfl,
        by rw [hx10n]; exact congrArg (BitVec.ofNat 64) (by simp only [Nat.add_zero, Nat.mul_assoc]),
        by rw [hx12n]; exact congrArg (BitVec.ofNat 64) (by omega),
        fun _ h1 h2 => by omega, fun _ _ _ _ => rfl, MemPreservedOutside.refl _ _ _⟩
    | succ m ihm =>
      obtain ⟨sm, hrunm, hpcm, hregm, hx10m, hx12m, hdigm, hgapm, hpresm⟩ := ihm (by omega)
      have h2q1 : 2 * (chunkPairs * n + m) + 1 < calls := by
        have : 2 * (chunkPairs * n + m) + 1 < 2 * chunkPairs * (n + 1) := by
          rw [show 2 * chunkPairs * (n + 1) = 2 * (chunkPairs * n) + 2 * chunkPairs by ring]; omega
        omega
      have hpres_s0 : MemPreservedOutside s0 sm (C_TD + levelBase (lvlIdx + 3))
          (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * n + m)) :=
        (hpresn.mono (le_refl _) (by omega)).trans (hpresm.mono (by omega) (le_refl _))
      obtain ⟨sp, hrun1, hpcp, hregp, hx10p, hx12p, hd0p, hd1p, hpres1⟩ :=
        hpair m (chunkPairs * n + m) (by omega) h2q1 sm hpcm
          ((hregm .x5 (by decide) (by decide) (by decide)).trans hx5)
          ((hregm .x11 (by decide) (by decide) (by decide)).trans hx11)
          ((hregm .x13 (by decide) (by decide) (by decide)).trans hx13)
          (hregm .x27 (by decide) (by decide) (by decide))
          hx10m hx12m
          (fun j hj => by
            have hgo : gapOffset (4 * (chunkPairs * n + m) + j) + 32 ≤ levelBytes (lvlIdx + 2) :=
              gapOffset_lt_levelBytes (lvlIdx + 2) _ (by omega) (by omega) (by omega)
            rw [hpres_s0.readBuffer_eq (by omega) (by omega)]
            exact hsrc (4 * (chunkPairs * n + m) + j) (by omega))
          (fun p hp => by
            have hgap_bd : 96 * (2 * (chunkPairs * n + m) + p) + 64 + 32 ≤ levelBytes (lvlIdx + 2) := by
              rw [hsrcBytes]; omega
            rw [hpres_s0.readBuffer_eq (by omega) (by omega)]
            exact hsrcGap (2 * (chunkPairs * n + m) + p) (by omega))
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
        by_cases hold : idx < 2 * chunkPairs * n + 2 * m
        · rw [← hdigm idx hlo hold]
          have hgo : gapOffset idx + 32 ≤ 96 * (chunkPairs * n + m) := by
            unfold gapOffset; rw [Nat.mul_assoc 2 chunkPairs n] at hold; omega
          have hdst_bd : 96 * (chunkPairs * n + m) ≤ levelBytes (lvlIdx + 3) := by
            rw [hdstBytes, hdstSize_eq]; omega
          exact hpres1.readBuffer_eq (by omega) (by omega)
        · have heq_b : 2 * chunkPairs * n + 2 * m = 2 * (chunkPairs * n + m) := by ring
          by_cases hev : idx = 2 * (chunkPairs * n + m)
          · subst hev; simpa only [gapOffset_even] using hd0p
          · have hodd : idx = 2 * (chunkPairs * n + m) + 1 := by omega
            subst hodd; simpa only [gapOffset_odd, Nat.add_assoc] using hd1p
      · intro q hq j hj
        have hsep : C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j <
              C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * n + m) ∨
            C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * n + m) + 64 ≤
              C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j := by omega
        exact (hpres1 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)
          (by rw [hdstBytes] at hdstB; omega) hsep).trans (hgapm q hq j hj)
      · exact (hpresm.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (by omega))
  obtain ⟨sm, hrunP, hpcP, hregP, hx10_P, hx12_P, hdigP, hgapP, hpresP⟩ := hpairs chunkPairs (le_refl _)
  have h2cp : 2 * (chunkPairs * n + chunkPairs) = 2 * chunkPairs * (n + 1) := by ring
  have hcp1 : chunkPairs * n + chunkPairs = chunkPairs * (n + 1) := by ring
  let sbne := execInstrBr sm (.BNE .x10 .x19 bneImm)
  have hbne : DetRun oracle (submission.image .commit) sm 1 sbne 1 0 :=
    DetRun.step1 (hbne_fetch sm hpcP) rfl
  have hmem_bne : sbne.mem = sm.mem := mem_exec_BNE sm .x10 .x19 bneImm
  have hreg_bne : ∀ r, sbne.getReg r = sm.getReg r := reg_exec_BNE sm .x10 .x19 bneImm
  have hpc_end : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n + 1 < chunks then pcBulk else pcExit)) := by
    have hx19m : sm.getReg .x19 =
        BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * chunkPairs * chunks) - 96) :=
      (hregP .x19 (by decide) (by decide) (by decide)).trans hx19
    by_cases hlt : n + 1 < chunks
    · have hlt_m : 2 * chunkPairs * (n + 1) < 2 * chunkPairs * chunks :=
        Nat.mul_lt_mul_of_pos_left hlt (by omega)
      have hne : (sm.getReg .x10 != sm.getReg .x19) = true := by
        rw [hx10_P, hx19m, h2cp, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hlt, ite_true, sbne, execInstrBr, hne, pc_setPC, hpcP]
      exact hbne_pc
    · have heq : (sm.getReg .x10 != sm.getReg .x19) = false := by
        rw [hx10_P, hx19m, h2cp, show n + 1 = chunks by omega]
        exact bne_self_eq_false _
      simp only [hlt, ite_false, sbne, execInstrBr, heq, Bool.false_eq_true, pc_setPC]
      rw [← hbne_exit]
      exact pc_step_idx sm (pcBulk + pairSteps * chunkPairs) hpcP
  refine ⟨sbne, hrunP.trans hbne, hpc_end,
    fun r h6 h10 h12 => (hreg_bne r).trans (hregP r h6 h10 h12),
    by rw [hreg_bne, hx10_P, h2cp],
    by rw [hreg_bne, hx12_P, hcp1],
    fun idx hlo hhi => (readBuffer_of_mem_eq hmem_bne _ _).trans (hdigP idx hlo (by rw [show 2 * chunkPairs * n + 2 * chunkPairs = 2 * chunkPairs * (n + 1) by ring]; exact hhi)),
    fun q hq j hj => (getByte_of_mem_eq hmem_bne _).trans (hgapP q hq j hj),
    (hpresP.mono (le_refl _) (by rw [hcp1])).trans (MemPreservedOutside.of_mem_eq hmem_bne _ _)⟩

private theorem commit_bin_stageA_gen (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (pcSetup pcBulk pcExit chunkPairs sh1 sh2 pairSteps pairCyc : Nat) (bneImm : BitVec 13)
    (hcp_pos : 0 < chunkPairs) (hsh1_lt : sh1 < 64) (hsh2_lt : sh2 < 64)
    (hsh1 : 2 ^ sh1 = 64 * chunkPairs) (hsh2 : 2 ^ sh2 = 128 * chunkPairs)
    (hsetup_bulk : pcSetup + 4 = pcBulk)
    (hbne_exit : pcBulk + pairSteps * chunkPairs + 1 = pcExit)
    (hbne_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * chunkPairs)) + signExtend13 bneImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcBulk))
    (lvlIdx calls chunks : Nat) (hlvl : lvlIdx < 20)
    (hcalls : calls = levelSize (lvlIdx + 2) / 2)
    (hchunks : chunks = calls / (2 * chunkPairs))
    (s0 h9 : MachineState)
    (hh_mem : h9.mem = s0.mem)
    (hh9_pc : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then pcSetup else pcExit)))
    (hx5 : h9.getReg .x5 = 0#64) (hx11 : h9.getReg .x11 = 96#64) (hx13 : h9.getReg .x13 = 0#64)
    (hx10 : h9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) - 96))
    (hx12 : h9.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) - 64))
    (hx22 : h9.getReg .x22 = BitVec.ofNat 64 chunks)
    (hsrc : ∀ idx < levelSize (lvlIdx + 2),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) 32 = 0)
    (hfS0 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * pcSetup) →
      fetch (submission.image .commit) st = some (.base (.SLLI .x6 .x22 (BitVec.ofNat 6 sh1))))
    (hfS1 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 1)) →
      fetch (submission.image .commit) st = some (.base (.SLLI .x7 .x22 (BitVec.ofNat 6 sh2))))
    (hfS2 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 2)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x6 .x6 .x7)))
    (hfS3 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcSetup + 3)) →
      fetch (submission.image .commit) st = some (.base (.ADD .x19 .x10 .x6)))
    (hpair : ∀ (m q : Nat), m < chunkPairs → 2 * q + 1 < calls → ∀ (sm : MachineState),
      sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * m)) →
      sm.getReg .x5 = 0#64 → sm.getReg .x11 = 96#64 → sm.getReg .x13 = 0#64 →
      sm.getReg .x27 = h9.getReg .x27 →
      sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q) - 96) →
      sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q - 64) →
      (∀ j < 4, readBuffer sm (C_TD + levelBase (lvlIdx + 2) + gapOffset (4 * q + j)) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (4 * q + j)) →
      (∀ p < 2, readBuffer sm (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + p) + 64) 32 = 0) →
      ∃ sp,
        DetRun oracle (submission.image .commit) sm pairSteps sp pairCyc 2 ∧
        sp.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * m + pairSteps)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sp.getReg r = sm.getReg r) ∧
        sp.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) ∧
        sp.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 3) + 96 * q) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q + 1) ∧
        MemPreservedOutside sm sp (C_TD + levelBase (lvlIdx + 3) + 96 * q)
          (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64))
    (hbne_fetch : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBulk + pairSteps * chunkPairs)) →
      fetch (submission.image .commit) st = some (.base (.BNE .x10 .x19 bneImm))) :
    ∃ sb,
      DetRun oracle (submission.image .commit) h9
        (if 0 < chunks then 4 + (pairSteps * chunkPairs + 1) * chunks else 0) sb
        (if 0 < chunks then 4 + (pairCyc * chunkPairs + 1) * chunks else 0) (2 * chunkPairs * chunks) ∧
      sb.pc = BitVec.ofNat 64 (0x1000 + 4 * pcExit) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → sb.getReg r = h9.getReg r) ∧
      sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * chunkPairs * chunks) - 96) ∧
      sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks) - 64) ∧
      (∀ idx < 2 * chunkPairs * chunks,
        readBuffer sb (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx) ∧
      (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
        sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 3))
        (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcSize_le := levelSize_le_max (lvlIdx + 2) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 3) (by omega)
  have htb := treeBytes_eq
  by_cases hch : 0 < chunks
  · have hpcS : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * pcSetup) := by
      simpa only [hch, ite_true] using hh9_pc
    obtain ⟨b3, hb_setup, hb3_pc', hb3_mem', hb3_reg, hb3_x19⟩ :=
      commit_bin_stageA_setup_gen oracle pcSetup chunkPairs sh1 sh2 lvlIdx calls chunks hlvl
        hsh1_lt hsh2_lt hsh1 hsh2 hcalls hchunks h9 hpcS hx10 hx22 (hfS0 h9 hpcS) hfS1 hfS2 hfS3
    have hb3_pc : b3.pc = BitVec.ofNat 64 (0x1000 + 4 * pcBulk) := by rw [← hsetup_bulk]; exact hb3_pc'
    have hb3_mem : b3.mem = s0.mem := hb3_mem'.trans hh_mem
    have hbulk : ∀ n ≤ chunks,
        ∃ sn,
          DetRun oracle (submission.image .commit) b3 ((pairSteps * chunkPairs + 1) * n) sn
            ((pairCyc * chunkPairs + 1) * n) (2 * chunkPairs * n) ∧
          sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < chunks then pcBulk else pcExit)) ∧
          (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sn.getReg r = b3.getReg r) ∧
          sn.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * chunkPairs * n) - 96) ∧
          sn.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * n) - 64) ∧
          (∀ idx < 2 * chunkPairs * n, readBuffer sn (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
            nodeVal c96 msg salts (lvlIdx + 3) idx) ∧
          (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
            sn.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
            s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
          MemPreservedOutside s0 sn (C_TD + levelBase (lvlIdx + 3))
            (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * n)) := by
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
          commit_bin_stageA_chunk_gen h768 oracle msg salts pcBulk pcExit chunkPairs pairSteps pairCyc bneImm
            hcp_pos hbne_exit hbne_pc lvlIdx calls chunks n hlvl hcalls hchunks (by omega) s0 sn hpc_in
            ((hregn .x5 (by decide) (by decide) (by decide)).trans ((hb3_reg .x5 (by decide) (by decide) (by decide)).trans hx5))
            ((hregn .x11 (by decide) (by decide) (by decide)).trans ((hb3_reg .x11 (by decide) (by decide) (by decide)).trans hx11))
            ((hregn .x13 (by decide) (by decide) (by decide)).trans ((hb3_reg .x13 (by decide) (by decide) (by decide)).trans hx13))
            ((hregn .x19 (by decide) (by decide) (by decide)).trans hb3_x19)
            hx10n hx12n hsrc hsrcGap hpresn
            (fun m q hm hq sm hp h5 h11 h13 h27 => hpair m q hm hq sm hp h5 h11 h13 (h27.trans hsn_x27))
            hbne_fetch
        have hrun_n1 : DetRun oracle (submission.image .commit) b3 ((pairSteps * chunkPairs + 1) * (n + 1)) sbne
            ((pairCyc * chunkPairs + 1) * (n + 1)) (2 * chunkPairs * (n + 1)) := by
          have h := hrunn.trans hrunC
          rw [← Nat.mul_succ (pairSteps * chunkPairs + 1) n, ← Nat.mul_succ (pairCyc * chunkPairs + 1) n,
              ← Nat.mul_succ (2 * chunkPairs) n] at h
          exact h
        have hcp_le : chunkPairs * n ≤ chunkPairs * (n + 1) := Nat.mul_le_mul_left chunkPairs (by omega)
        refine ⟨sbne, hrun_n1, hpc_end, fun r h6 h10 h12 => (hregC r h6 h10 h12).trans (hregn r h6 h10 h12),
          hx10C, hx12C, ?_, fun q hq j hj => (hgapC q hq j hj).trans (hgapn q hq j hj),
          (hpresn.mono (le_refl _) (by omega)).trans (hpresC.mono (by omega) (le_refl _))⟩
        intro idx hidx
        by_cases hold : idx < 2 * chunkPairs * n
        · rw [← hdign idx hold]
          have hmul : 2 * chunkPairs * n = 2 * (chunkPairs * n) := Nat.mul_assoc 2 chunkPairs n
          have hgo : gapOffset idx + 32 ≤ 96 * (chunkPairs * n) := by
            unfold gapOffset; rw [hmul] at hold; omega
          have hch_le : 2 * chunkPairs * chunks ≤ calls := by
            rw [hchunks]; exact Nat.mul_div_le calls (2 * chunkPairs)
          have hle_calls : 2 * (chunkPairs * n) ≤ calls := by
            rw [← hmul]; exact (Nat.mul_le_mul_left (2 * chunkPairs) (by omega : n ≤ chunks)).trans hch_le
          have hds : levelSize (lvlIdx + 3) = (levelSize (lvlIdx + 2) + 1) / 2 := levelSize_step (lvlIdx + 2) (by omega)
          have hdstBytes : levelBytes (lvlIdx + 3) = ((levelSize (lvlIdx + 3) + 1) / 2) * 96 :=
            levelBytes_eq_gap (lvlIdx + 3) (by omega) (by omega)
          have hcpn_bd : 96 * (chunkPairs * n) ≤ levelBytes (lvlIdx + 3) := by
            rw [hdstBytes]; omega
          exact hpresC.readBuffer_eq (by omega) (by omega)
        · exact hdigC idx (by omega) hidx
    obtain ⟨sb, hrunb, hpcb, hregb, hx10b, hx12b, hdigb, hgapb, hpresb⟩ := hbulk chunks (le_refl _)
    have hrun_tot : DetRun oracle (submission.image .commit) h9
        (if 0 < chunks then 4 + (pairSteps * chunkPairs + 1) * chunks else 0) sb
        (if 0 < chunks then 4 + (pairCyc * chunkPairs + 1) * chunks else 0) (2 * chunkPairs * chunks) := by
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
        (if 0 < chunks then 4 + (pairSteps * chunkPairs + 1) * chunks else 0) h9
        (if 0 < chunks then 4 + (pairCyc * chunkPairs + 1) * chunks else 0) (2 * chunkPairs * chunks) := by
      rw [show (if 0 < chunks then 4 + (pairSteps * chunkPairs + 1) * chunks else 0) = 0 by simp only [hch, ite_false],
          show (if 0 < chunks then 4 + (pairCyc * chunkPairs + 1) * chunks else 0) = 0 by simp only [hch, ite_false],
          show 2 * chunkPairs * chunks = 0 by rw [hch0, Nat.mul_zero]]
      exact DetRun.refl oracle (submission.image .commit) h9
    exact ⟨h9, hrun0, hpcE, fun _ _ _ _ _ _ => rfl,
      by rw [hx10, hch0]; exact congrArg (BitVec.ofNat 64) (by omega),
      by rw [hx12, hch0]; exact congrArg (BitVec.ofNat 64) (by omega),
      fun _ h => by rw [hch0, Nat.mul_zero] at h; omega,
      fun _ _ _ _ => getByte_of_mem_eq hh_mem _,
      by rw [hch0, Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
         exact MemPreservedOutside.of_mem_eq hh_mem _ _⟩

/-! ### 6. Parameterized Stage B (Tail Pairs) -/

private theorem commit_bin_stageB_setup_gen (oracle : Oracle)
    (pcB pcBody pcExit chunkPairs : Nat) (maskImm : BitVec 12) (beqImm : BitVec 13)
    (hstep_body : pcB + 3 = pcBody)
    (hbeq_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcB + 2)) + signExtend13 beqImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcExit))
    (lvlIdx calls remPairs : Nat) (hlvl : lvlIdx < 20)
    (hcalls : calls = levelSize (lvlIdx + 2) / 2)
    (hrem : remPairs = (calls % (2 * chunkPairs)) / 2)
    (hmask : BitVec.ofNat 64 calls &&& signExtend12 maskImm = BitVec.ofNat 64 (calls % (2 * chunkPairs)))
    (sb : MachineState)
    (hpcB : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * pcB))
    (hx20B : sb.getReg .x20 = BitVec.ofNat 64 calls)
    (hf0 : fetch (submission.image .commit) sb = some (.base (.ANDI .x22 .x20 maskImm)))
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
  have hsrcSize_le := levelSize_le_max (lvlIdx + 2) (by omega)
  have hmod_le : calls % (2 * chunkPairs) ≤ calls := Nat.mod_le _ _
  let t0 := execInstrBr sb (.ANDI .x22 .x20 maskImm)
  let t1 := execInstrBr t0 (.SRLI .x22 .x22 (1#6))
  let t2 := execInstrBr t1 (.BEQ .x22 .x0 beqImm)
  have ht0_pc : t0.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcB + 1)) := pc_step_idx sb pcB hpcB
  have ht1_pc : t1.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcB + 2)) := pc_step_idx t0 (pcB + 1) ht0_pc
  have ht_run3 : DetRun oracle (submission.image .commit) sb 3 t2 3 0 :=
    ((DetRun.step1 hf0 rfl).trans (DetRun.step1 (hf1 t0 ht0_pc) rfl)).trans (DetRun.step1 (hf2 t1 ht1_pc) rfl)
  have ht1_x22 : t1.getReg .x22 = BitVec.ofNat 64 remPairs := by
    have ht0_x22 : t0.getReg .x22 = BitVec.ofNat 64 (calls % (2 * chunkPairs)) := by
      simp only [t0, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), hx20B]
      exact hmask
    simp only [t1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), ht0_x22]
    exact (bv64_ushiftRight_ofNat (calls % (2 * chunkPairs)) 1 (by omega)).trans
      (congrArg (BitVec.ofNat 64) (by omega))
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
    (pcB pcBody pcExit chunkPairs pairSteps pairCyc : Nat) (maskImm : BitVec 12) (beqImm bneImm : BitVec 13)
    (hstep_body : pcB + 3 = pcBody)
    (hstep_exit : pcBody + pairSteps + 2 = pcExit)
    (hbeq_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcB + 2)) + signExtend13 beqImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcExit))
    (hbne_pc : BitVec.ofNat 64 (0x1000 + 4 * (pcBody + pairSteps + 1)) + signExtend13 bneImm =
      BitVec.ofNat 64 (0x1000 + 4 * pcBody))
    (lvlIdx calls chunks remPairs : Nat) (hlvl : lvlIdx < 20)
    (hcalls : calls = levelSize (lvlIdx + 2) / 2)
    (hchunks : chunks = calls / (2 * chunkPairs))
    (hrem : remPairs = (calls % (2 * chunkPairs)) / 2)
    (hmask : BitVec.ofNat 64 calls &&& signExtend12 maskImm = BitVec.ofNat 64 (calls % (2 * chunkPairs)))
    (s0 sb : MachineState)
    (hpcB : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * pcB))
    (hx5B : sb.getReg .x5 = 0#64) (hx11B : sb.getReg .x11 = 96#64) (hx13B : sb.getReg .x13 = 0#64)
    (hx20B : sb.getReg .x20 = BitVec.ofNat 64 calls)
    (hx10B : sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * chunkPairs * chunks) - 96))
    (hx12B : sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 2),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) 32 = 0)
    (hdigB : ∀ idx < 2 * chunkPairs * chunks,
      readBuffer sb (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx)
    (hgapB : ∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
      sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)))
    (hpresB : MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 3))
      (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks)))
    (hfS0 : fetch (submission.image .commit) sb = some (.base (.ANDI .x22 .x20 maskImm)))
    (hfS1 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcB + 1)) →
      fetch (submission.image .commit) st = some (.base (.SRLI .x22 .x22 (1#6))))
    (hfS2 : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcB + 2)) →
      fetch (submission.image .commit) st = some (.base (.BEQ .x22 .x0 beqImm)))
    (hpair : ∀ (q : Nat), 2 * q + 1 < calls → ∀ (sm : MachineState),
      sm.pc = BitVec.ofNat 64 (0x1000 + 4 * pcBody) →
      sm.getReg .x5 = 0#64 → sm.getReg .x11 = 96#64 → sm.getReg .x13 = 0#64 →
      sm.getReg .x27 = sb.getReg .x27 →
      sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q) - 96) →
      sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q - 64) →
      (∀ j < 4, readBuffer sm (C_TD + levelBase (lvlIdx + 2) + gapOffset (4 * q + j)) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) (4 * q + j)) →
      (∀ p < 2, readBuffer sm (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + p) + 64) 32 = 0) →
      ∃ sp,
        DetRun oracle (submission.image .commit) sm pairSteps sp pairCyc 2 ∧
        sp.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBody + pairSteps)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sp.getReg r = sm.getReg r) ∧
        sp.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * q + 1)) ∧
        sp.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 3) + 96 * q) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q) ∧
        readBuffer sp (C_TD + levelBase (lvlIdx + 3) + 96 * q + 32) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) (2 * q + 1) ∧
        MemPreservedOutside sm sp (C_TD + levelBase (lvlIdx + 3) + 96 * q)
          (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64))
    (hfDec : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBody + pairSteps)) →
      fetch (submission.image .commit) st = some (.base (.ADDI .x22 .x22 (4095#12))))
    (hfBne : ∀ st, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcBody + pairSteps + 1)) →
      fetch (submission.image .commit) st = some (.base (.BNE .x22 .x0 bneImm))) :
    ∃ st,
      DetRun oracle (submission.image .commit) sb (3 + (pairSteps + 2) * remPairs) st
        (3 + (pairCyc + 2) * remPairs) (2 * remPairs) ∧
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * pcExit) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → st.getReg r = sb.getReg r) ∧
      st.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * chunkPairs * chunks + 2 * remPairs) - 96) ∧
      st.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks + remPairs) - 64) ∧
      (∀ idx < 2 * chunkPairs * chunks + 2 * remPairs,
        readBuffer st (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx) ∧
      (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
        st.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 st (C_TD + levelBase (lvlIdx + 3))
        (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks + remPairs)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcSize_le := levelSize_le_max (lvlIdx + 2) (by omega)
  have hdstSize_eq : levelSize (lvlIdx + 3) = (levelSize (lvlIdx + 2) + 1) / 2 :=
    levelSize_step (lvlIdx + 2) (by omega)
  have hsrcB := levelBase_bound (lvlIdx + 2) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 3) (by omega)
  have htb := treeBytes_eq
  have hsrcBytes := levelBytes_eq_gap (lvlIdx + 2) (by omega) (by omega)
  have hdstBytes := levelBytes_eq_gap (lvlIdx + 3) (by omega) (by omega)
  have hbase_step : levelBase (lvlIdx + 3) = levelBase (lvlIdx + 2) + levelBytes (lvlIdx + 2) := rfl
  have hdiv_mod : 2 * chunkPairs * chunks + 2 * remPairs ≤ calls := by
    have hdm := Nat.div_add_mod calls (2 * chunkPairs)
    rw [← hchunks] at hdm; omega
  obtain ⟨t2, ht_run3, ht2_pc, ht2_mem, ht2_x22, ht2_reg⟩ :=
    commit_bin_stageB_setup_gen oracle pcB pcBody pcExit chunkPairs maskImm beqImm hstep_body hbeq_pc
      lvlIdx calls remPairs hlvl hcalls hrem hmask sb hpcB hx20B hfS0 hfS1 hfS2
  by_cases hrp : 0 < remPairs
  · have htloop : ∀ m ≤ remPairs,
        ∃ sm,
          DetRun oracle (submission.image .commit) t2 ((pairSteps + 2) * m) sm ((pairCyc + 2) * m) (2 * m) ∧
          sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (if m < remPairs then pcBody else pcExit)) ∧
          (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → sm.getReg r = sb.getReg r) ∧
          sm.getReg .x22 = BitVec.ofNat 64 (remPairs - m) ∧
          sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (2 * chunkPairs * chunks + 2 * m) - 96) ∧
          sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks + m) - 64) ∧
          (∀ idx < 2 * chunkPairs * chunks + 2 * m, readBuffer sm (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
            nodeVal c96 msg salts (lvlIdx + 3) idx) ∧
          (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
            sm.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
            s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
          MemPreservedOutside s0 sm (C_TD + levelBase (lvlIdx + 3))
            (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks + m)) := by
      intro m hm; induction m with
      | zero =>
        exact ⟨t2, DetRun.refl _ _ _, ht2_pc, fun r _ _ _ h22 => ht2_reg r h22,
          by rw [ht2_x22]; exact congrArg (BitVec.ofNat 64) (by omega),
          by rw [ht2_reg .x10 (by decide), hx10B]; exact congrArg (BitVec.ofNat 64) (by omega),
          by rw [ht2_reg .x12 (by decide), hx12B]; exact congrArg (BitVec.ofNat 64) (by omega),
          fun idx hidx => (readBuffer_of_mem_eq ht2_mem _ _).trans (hdigB idx (by omega)),
          fun q hq j hj => (getByte_of_mem_eq ht2_mem _).trans (hgapB q hq j hj),
          by rw [show C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks + 0) =
                C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks) by omega]
             exact hpresB.trans (MemPreservedOutside.of_mem_eq ht2_mem _ _)⟩
      | succ m ihm =>
        obtain ⟨sm, hrunm, hpcm, hregm, hx22m, hx10m, hx12m, hdigm, hgapm, hpresm⟩ := ihm (by omega)
        have hpc_in : sm.pc = BitVec.ofNat 64 (0x1000 + 4 * pcBody) := by
          simpa only [show m < remPairs by omega, ite_true] using hpcm
        have h2q_eq : 2 * (chunkPairs * chunks + m) = 2 * chunkPairs * chunks + 2 * m := by ring
        obtain ⟨sp, hrun1, hpcp, hregp, hx10p, hx12p, hd0p, hd1p, hpres1⟩ :=
          hpair (chunkPairs * chunks + m) (by omega) sm hpc_in
            ((hregm .x5 (by decide) (by decide) (by decide) (by decide)).trans hx5B)
            ((hregm .x11 (by decide) (by decide) (by decide) (by decide)).trans hx11B)
            ((hregm .x13 (by decide) (by decide) (by decide) (by decide)).trans hx13B)
            (hregm .x27 (by decide) (by decide) (by decide) (by decide))
            (by rw [hx10m, h2q_eq]) hx12m
            (fun j hj => by
              have hgo : gapOffset (4 * (chunkPairs * chunks + m) + j) + 32 ≤ levelBytes (lvlIdx + 2) :=
                gapOffset_lt_levelBytes (lvlIdx + 2) _ (by omega) (by omega) (by omega)
              rw [hpresm.readBuffer_eq (by omega) (by omega)]
              exact hsrc (4 * (chunkPairs * chunks + m) + j) (by omega))
            (fun p hp => by
              have hgap_bd : 96 * (2 * (chunkPairs * chunks + m) + p) + 64 + 32 ≤ levelBytes (lvlIdx + 2) := by
                rw [hsrcBytes]; omega
              rw [hpresm.readBuffer_eq (by omega) (by omega)]
              exact hsrcGap (2 * (chunkPairs * chunks + m) + p) (by omega))
        obtain ⟨sdec, hdec_run, hsdec_pc, hsdec_mem, hsdec_x22, hsdec_reg⟩ :=
          commit_bin_stageB_dec_gen oracle (pcBody + pairSteps) remPairs m (by omega) sp hpcp
            ((hregp .x22 (by decide) (by decide) (by decide)).trans hx22m) (hfDec sp hpcp)
        obtain ⟨sbne, hbne_run, hpc_end, hmem_bne, hreg_bne⟩ :=
          commit_bin_stageB_bne_gen oracle (pcBody + pairSteps + 1) pcBody pcExit bneImm
            (by omega) hbne_pc remPairs m (by omega) sdec hsdec_pc hsdec_x22 (hfBne sdec hsdec_pc)
        have hmem_end : sbne.mem = sp.mem := hmem_bne.trans hsdec_mem
        have hpresI : MemPreservedOutside sm sbne (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks + m))
            (C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks + m) + 64) :=
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
          by_cases hold : idx < 2 * chunkPairs * chunks + 2 * m
          · rw [← hdigm idx hold]
            have hgo : gapOffset idx + 32 ≤ 96 * (chunkPairs * chunks + m) := by
              unfold gapOffset; omega
            have hdst_bd : 96 * (chunkPairs * chunks + m) ≤ levelBytes (lvlIdx + 3) := by
              rw [hdstBytes, hdstSize_eq]; omega
            exact hpresI.readBuffer_eq (by omega) (by omega)
          · by_cases hev : idx = 2 * (chunkPairs * chunks + m)
            · subst hev; simpa only [gapOffset_even] using (readBuffer_of_mem_eq hmem_end _ _).trans hd0p
            · have hodd : idx = 2 * (chunkPairs * chunks + m) + 1 := by omega
              subst hodd; simpa only [gapOffset_odd, Nat.add_assoc] using (readBuffer_of_mem_eq hmem_end _ _).trans hd1p
        · intro q hq j hj
          have hsep : C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j <
                C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks + m) ∨
              C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks + m) + 64 ≤
                C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j := by omega
          exact (hpresI (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)
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
      by rw [show C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks + remPairs) =
            C_TD + levelBase (lvlIdx + 3) + 96 * (chunkPairs * chunks) by omega]
         exact hpresB.trans (MemPreservedOutside.of_mem_eq ht2_mem _ _)⟩

/-! ### 7. Concrete Stage A & Stage B Instantiations for Phases 3U, 3A, 3B -/

private theorem commit_fetch_binu_tail_pair (st : MachineState) (j : Nat) (hj : j < 6)
    (hst : st.pc = BitVec.ofNat 64 (0x1000 + 4 * (60232 + j))) :
    fetch (submission.image .commit) st = some (binUPairInstr j) := by
  have h := commit_fetch_commitMid3UInstr st (60232 + j) (by omega) (by omega) hst
  interval_cases j <;> simpa only [binUPairInstr, commitMid3UInstr] using h

private theorem commit_fetch_bin_tail_pair (st : MachineState) (j : Nat) (hj : j < 8)
    (hst : st.pc = BitVec.ofNat 64 (0x1000 + 4 * (60773 + j))) :
    fetch (submission.image .commit) st = some (binPairInstr j) := by
  have h := commit_fetch_commitMid3AInstr st (60773 + j) (by omega) (by omega) hst
  interval_cases j <;> simpa only [binPairInstr, commitMid3AInstr] using h

private theorem commit_fetch_bin238_tail_pair (st : MachineState) (j : Nat) (hj : j < 12)
    (hst : st.pc = BitVec.ofNat 64 (0x1000 + 4 * (61600 + j))) :
    fetch (submission.image .commit) st = some (bin238PairInstr j) := by
  have h := commit_fetch_commitTailInstr st (61600 + j) (by omega) (by omega) hst
  interval_cases j <;> simpa only [bin238PairInstr, commitTailInstr] using h

/-- Phase 3U Stage A (unmasked 256-bit bulk chunks, words `59456..60228`). -/
theorem commit_binU_level_stageA (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks : Nat) (hlvl : lvlIdx < 2)
    (hcalls : calls = levelSize (lvlIdx + 2) / 2)
    (hchunks : chunks = calls / 256)
    (s0 h8 : MachineState)
    (hh_mem : h8.mem = s0.mem)
    (hh8_pc : h8.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then 59456 else 60229)))
    (hx5 : h8.getReg .x5 = 0#64) (hx11 : h8.getReg .x11 = 96#64) (hx13 : h8.getReg .x13 = 0#64)
    (hx10 : h8.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) - 96))
    (hx12 : h8.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) - 64))
    (hx22 : h8.getReg .x22 = BitVec.ofNat 64 chunks)
    (hsrc : ∀ idx < levelSize (lvlIdx + 2),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) 32 = 0) :
    ∃ sb,
      DetRun oracle (submission.image .commit) h8
        (if 0 < chunks then 4 + 769 * chunks else 0) sb
        (if 0 < chunks then 4 + 2561 * chunks else 0) (256 * chunks) ∧
      sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 60229) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → sb.getReg r = h8.getReg r) ∧
      sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (256 * chunks) - 96) ∧
      sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (128 * chunks) - 64) ∧
      (∀ idx < 256 * chunks,
        readBuffer sb (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx) ∧
      (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
        sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 3))
        (C_TD + levelBase (lvlIdx + 3) + 96 * (128 * chunks)) :=
  commit_bin_stageA_gen h768 oracle msg salts 59456 59460 60229 128 13 14 6 20 (5120#13)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl pc_bne_60228
    lvlIdx calls chunks (by omega) hcalls hchunks s0 h8 hh_mem hh8_pc hx5 hx11 hx13 hx10 hx12 hx22
    hsrc hsrcGap
    (fun st hst => commit_fetch_commitMid2BInstr st 59456 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid2BInstr st 59457 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid2BInstr st 59458 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid2BInstr st 59459 (by omega) (by omega) hst)
    (fun m q hm hq sm hp h5 h11 h13 _ h10 h12 hs hsg =>
      commit_binU_pair h768 oracle msg salts lvlIdx (59460 + 6 * m) q hlvl (by omega) sm
        (fun j hj st hst => commit_fetch_binu_bulk st m j hm hj hst) hp h5 h11 h13 h10 h12 hs hsg)
    (fun st hst => commit_fetch_commitMid3UInstr st 60228 (by omega) (by omega) hst)

/-- Phase 3U Stage B (unmasked 256-bit tail pairs, words `60229..60239`). -/
theorem commit_binU_level_stageB (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks remPairs : Nat) (hlvl : lvlIdx < 2)
    (hcalls : calls = levelSize (lvlIdx + 2) / 2)
    (hchunks : chunks = calls / 256)
    (hrem : remPairs = (calls % 256) / 2)
    (s0 sb : MachineState)
    (hpcB : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 60229))
    (hx5B : sb.getReg .x5 = 0#64) (hx11B : sb.getReg .x11 = 96#64) (hx13B : sb.getReg .x13 = 0#64)
    (hx20B : sb.getReg .x20 = BitVec.ofNat 64 calls)
    (hx10B : sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (256 * chunks) - 96))
    (hx12B : sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (128 * chunks) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 2),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) 32 = 0)
    (hdigB : ∀ idx < 256 * chunks,
      readBuffer sb (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx)
    (hgapB : ∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
      sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)))
    (hpresB : MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 3))
      (C_TD + levelBase (lvlIdx + 3) + 96 * (128 * chunks))) :
    ∃ st,
      DetRun oracle (submission.image .commit) sb (3 + 8 * remPairs) st (3 + 22 * remPairs) (2 * remPairs) ∧
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * 60240) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → st.getReg r = sb.getReg r) ∧
      st.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (256 * chunks + 2 * remPairs) - 96) ∧
      st.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (128 * chunks + remPairs) - 64) ∧
      (∀ idx < 256 * chunks + 2 * remPairs,
        readBuffer st (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx) ∧
      (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
        st.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 st (C_TD + levelBase (lvlIdx + 3))
        (C_TD + levelBase (lvlIdx + 3) + 96 * (128 * chunks + remPairs)) := by
  have hsrcSize_le := levelSize_le_max (lvlIdx + 2) (by omega)
  exact commit_bin_stageB_gen h768 oracle msg salts 60229 60232 60240 128 6 20 (255#12) (36#13) (8164#13)
    rfl rfl pc_beq_60231 pc_bne_60239 lvlIdx calls chunks remPairs (by omega) hcalls hchunks hrem
    (c_bv64_and_255 calls (by omega))
    s0 sb hpcB hx5B hx11B hx13B hx20B hx10B hx12B hsrc hsrcGap hdigB hgapB hpresB
    (commit_fetch_commitMid3UInstr sb 60229 (by omega) (by omega) hpcB)
    (fun st hst => commit_fetch_commitMid3UInstr st 60230 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3UInstr st 60231 (by omega) (by omega) hst)
    (fun q hq sm hp h5 h11 h13 _ h10 h12 hs hsg =>
      commit_binU_pair h768 oracle msg salts lvlIdx 60232 q hlvl (by omega) sm
        (fun j hj st hst => commit_fetch_binu_tail_pair st j hj hst) hp h5 h11 h13 h10 h12 hs hsg)
    (fun st hst => commit_fetch_commitMid3UInstr st 60238 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3UInstr st 60239 (by omega) (by omega) hst)

/-- Phase 3A Stage A (240-bit bulk chunks, words `60253..60769`). -/
theorem commit_bin_level_stageA (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks : Nat) (hlo : 2 ≤ lvlIdx) (hhi : lvlIdx < 6)
    (hcalls : calls = levelSize (lvlIdx + 2) / 2)
    (hchunks : chunks = calls / 128)
    (s0 h9 : MachineState)
    (hh_mem : h9.mem = s0.mem)
    (hh9_pc : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then 60253 else 60770)))
    (hx5 : h9.getReg .x5 = 0#64) (hx11 : h9.getReg .x11 = 96#64) (hx13 : h9.getReg .x13 = 0#64)
    (hx10 : h9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) - 96))
    (hx12 : h9.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) - 64))
    (hx22 : h9.getReg .x22 = BitVec.ofNat 64 chunks)
    (hsrc : ∀ idx < levelSize (lvlIdx + 2),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) 32 = 0) :
    ∃ sb,
      DetRun oracle (submission.image .commit) h9
        (if 0 < chunks then 4 + 513 * chunks else 0) sb
        (if 0 < chunks then 4 + 1409 * chunks else 0) (128 * chunks) ∧
      sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 60770) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → sb.getReg r = h9.getReg r) ∧
      sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (128 * chunks) - 96) ∧
      sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks) - 64) ∧
      (∀ idx < 128 * chunks,
        readBuffer sb (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx) ∧
      (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
        sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 3))
        (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks)) :=
  commit_bin_stageA_gen h768 oracle msg salts 60253 60257 60770 64 12 13 8 22 (6144#13)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl pc_bne_60769
    lvlIdx calls chunks (by omega) hcalls hchunks s0 h9 hh_mem hh9_pc hx5 hx11 hx13 hx10 hx12 hx22
    hsrc hsrcGap
    (fun st hst => commit_fetch_commitMid3UInstr st 60253 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3UInstr st 60254 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3UInstr st 60255 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3UInstr st 60256 (by omega) (by omega) hst)
    (fun m q hm hq sm hp h5 h11 h13 _ h10 h12 hs hsg =>
      commit_bin_pair h768 oracle msg salts lvlIdx (60257 + 8 * m) q hlo hhi (by omega) sm
        (fun j hj st hst => commit_fetch_bin_bulk st m j hm hj hst) hp h5 h11 h13 h10 h12 hs hsg)
    (fun st hst => commit_fetch_commitMid3AInstr st 60769 (by omega) (by omega) hst)

/-- Phase 3A Stage B (240-bit tail pairs, words `60770..60782`). -/
theorem commit_bin_level_stageB (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks remPairs : Nat) (hlo : 2 ≤ lvlIdx) (hhi : lvlIdx < 6)
    (hcalls : calls = levelSize (lvlIdx + 2) / 2)
    (hchunks : chunks = calls / 128)
    (hrem : remPairs = (calls % 128) / 2)
    (s0 sb : MachineState)
    (hpcB : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 60770))
    (hx5B : sb.getReg .x5 = 0#64) (hx11B : sb.getReg .x11 = 96#64) (hx13B : sb.getReg .x13 = 0#64)
    (hx20B : sb.getReg .x20 = BitVec.ofNat 64 calls)
    (hx10B : sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (128 * chunks) - 96))
    (hx12B : sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 2),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) 32 = 0)
    (hdigB : ∀ idx < 128 * chunks,
      readBuffer sb (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx)
    (hgapB : ∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
      sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)))
    (hpresB : MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 3))
      (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks))) :
    ∃ st,
      DetRun oracle (submission.image .commit) sb (3 + 10 * remPairs) st (3 + 24 * remPairs) (2 * remPairs) ∧
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * 60783) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → st.getReg r = sb.getReg r) ∧
      st.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (128 * chunks + 2 * remPairs) - 96) ∧
      st.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks + remPairs) - 64) ∧
      (∀ idx < 128 * chunks + 2 * remPairs,
        readBuffer st (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx) ∧
      (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
        st.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 st (C_TD + levelBase (lvlIdx + 3))
        (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks + remPairs)) := by
  have hsrcSize_le := levelSize_le_max (lvlIdx + 2) (by omega)
  exact commit_bin_stageB_gen h768 oracle msg salts 60770 60773 60783 64 8 22 (127#12) (44#13) (8156#13)
    rfl rfl pc_beq_60772 pc_bne_60782 lvlIdx calls chunks remPairs (by omega) hcalls hchunks hrem
    (bv64_and_127 calls (by omega))
    s0 sb hpcB hx5B hx11B hx13B hx20B hx10B hx12B hsrc hsrcGap hdigB hgapB hpresB
    (commit_fetch_commitMid3AInstr sb 60770 (by omega) (by omega) hpcB)
    (fun st hst => commit_fetch_commitMid3AInstr st 60771 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3AInstr st 60772 (by omega) (by omega) hst)
    (fun q hq sm hp h5 h11 h13 _ h10 h12 hs hsg =>
      commit_bin_pair h768 oracle msg salts lvlIdx 60773 q hlo hhi (by omega) sm
        (fun j hj st hst => commit_fetch_bin_tail_pair st j hj hst) hp h5 h11 h13 h10 h12 hs hsg)
    (fun st hst => commit_fetch_commitMid3AInstr st 60781 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3AInstr st 60782 (by omega) (by omega) hst)

/-- Phase 3B Stage A (238-bit bulk chunks, words `60824..61596`). -/
theorem commit_bin238_level_stageA (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks : Nat) (hlo : 6 ≤ lvlIdx) (hhi : lvlIdx < 20)
    (hcalls : calls = levelSize (lvlIdx + 2) / 2)
    (hchunks : chunks = calls / 128)
    (s0 h9 : MachineState)
    (hh_mem : h9.mem = s0.mem)
    (hh9_pc : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then 60824 else 61597)))
    (hx5 : h9.getReg .x5 = 0#64) (hx11 : h9.getReg .x11 = 96#64) (hx13 : h9.getReg .x13 = 0#64)
    (hx27 : h9.getReg .x27 = mask238Word)
    (hx10 : h9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) - 96))
    (hx12 : h9.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) - 64))
    (hx22 : h9.getReg .x22 = BitVec.ofNat 64 chunks)
    (hsrc : ∀ idx < levelSize (lvlIdx + 2),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) 32 = 0) :
    ∃ sb,
      DetRun oracle (submission.image .commit) h9
        (if 0 < chunks then 4 + 769 * chunks else 0) sb
        (if 0 < chunks then 4 + 1665 * chunks else 0) (128 * chunks) ∧
      sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 61597) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → sb.getReg r = h9.getReg r) ∧
      sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (128 * chunks) - 96) ∧
      sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks) - 64) ∧
      (∀ idx < 128 * chunks,
        readBuffer sb (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx) ∧
      (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
        sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 3))
        (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks)) :=
  commit_bin_stageA_gen h768 oracle msg salts 60824 60828 61597 64 12 13 12 26 (5120#13)
    (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl pc_bne_61596
    lvlIdx calls chunks hhi hcalls hchunks s0 h9 hh_mem hh9_pc hx5 hx11 hx13 hx10 hx12 hx22
    hsrc hsrcGap
    (fun st hst => commit_fetch_commitMid3AInstr st 60824 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3AInstr st 60825 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3AInstr st 60826 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitMid3AInstr st 60827 (by omega) (by omega) hst)
    (fun m q hm hq sm hp h5 h11 h13 h27 h10 h12 hs hsg =>
      commit_bin238_pair h768 oracle msg salts lvlIdx (60828 + 12 * m) q hlo hhi (by omega) sm
        (fun j hj st hst => commit_fetch_bin238_bulk st m j hm hj hst)
        hp h5 h11 h13 (h27.trans hx27) h10 h12 hs hsg)
    (fun st hst => commit_fetch_commitTailInstr st 61596 (by omega) (by omega) hst)

/-- Phase 3B Stage B (238-bit tail pairs, words `61597..61613`). -/
theorem commit_bin238_level_stageB (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (lvlIdx calls chunks remPairs : Nat) (hlo : 6 ≤ lvlIdx) (hhi : lvlIdx < 20)
    (hcalls : calls = levelSize (lvlIdx + 2) / 2)
    (hchunks : chunks = calls / 128)
    (hrem : remPairs = (calls % 128) / 2)
    (s0 sb : MachineState)
    (hpcB : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 61597))
    (hx5B : sb.getReg .x5 = 0#64) (hx11B : sb.getReg .x11 = 96#64) (hx13B : sb.getReg .x13 = 0#64)
    (hx27B : sb.getReg .x27 = mask238Word)
    (hx20B : sb.getReg .x20 = BitVec.ofNat 64 calls)
    (hx10B : sb.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (128 * chunks) - 96))
    (hx12B : sb.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 2),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64) 32 = 0)
    (hdigB : ∀ idx < 128 * chunks,
      readBuffer sb (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx)
    (hgapB : ∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
      sb.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)))
    (hpresB : MemPreservedOutside s0 sb (C_TD + levelBase (lvlIdx + 3))
      (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks))) :
    ∃ st,
      DetRun oracle (submission.image .commit) sb (3 + 14 * remPairs) st (3 + 28 * remPairs) (2 * remPairs) ∧
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * 61614) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → st.getReg r = sb.getReg r) ∧
      st.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (128 * chunks + 2 * remPairs) - 96) ∧
      st.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks + remPairs) - 64) ∧
      (∀ idx < 128 * chunks + 2 * remPairs,
        readBuffer st (C_TD + levelBase (lvlIdx + 3) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 3) idx) ∧
      (∀ q < (levelSize (lvlIdx + 3) + 1) / 2, ∀ j < 32,
        st.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 3) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 st (C_TD + levelBase (lvlIdx + 3))
        (C_TD + levelBase (lvlIdx + 3) + 96 * (64 * chunks + remPairs)) := by
  have hsrcSize_le := levelSize_le_max (lvlIdx + 2) (by omega)
  exact commit_bin_stageB_gen h768 oracle msg salts 61597 61600 61614 64 12 26 (127#12) (60#13) (8140#13)
    rfl rfl pc_beq_61599 pc_bne_61613 lvlIdx calls chunks remPairs hhi hcalls hchunks hrem
    (bv64_and_127 calls (by omega))
    s0 sb hpcB hx5B hx11B hx13B hx20B hx10B hx12B hsrc hsrcGap hdigB hgapB hpresB
    (commit_fetch_commitTailInstr sb 61597 (by omega) (by omega) hpcB)
    (fun st hst => commit_fetch_commitTailInstr st 61598 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitTailInstr st 61599 (by omega) (by omega) hst)
    (fun q hq sm hp h5 h11 h13 h27 h10 h12 hs hsg =>
      commit_bin238_pair h768 oracle msg salts lvlIdx 61600 q hlo hhi (by omega) sm
        (fun j hj st hst => commit_fetch_bin238_tail_pair st j hj hst)
        hp h5 h11 h13 (h27.trans hx27B) h10 h12 hs hsg)
    (fun st hst => commit_fetch_commitTailInstr st 61612 (by omega) (by omega) hst)
    (fun st hst => commit_fetch_commitTailInstr st 61613 (by omega) (by omega) hst)

end CommitGolfCandidate
