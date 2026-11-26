import CommitGolfCandidate.MoonCommitLeaf

/-! Exact RV64IM execution proof for Phase 2 of the B1-Ultra-121 `commit` image
(single unified 238-bit binary band covering all 23 internal levels `L1..L23`, words `701..1502`):
- Zero odd-sized levels, zero promotions (`levelSize (i + 1) = 2^(23 - i) ≥ 2` is always even)
- Exact `100,794,850` steps, `218,235,348` cycles, `16,777,214` compression calls
- Preserves `L0` and all lower computed levels, all zero gaps of `L0..L23`, all raw salts, and `commitData`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Exact Per-Level Cost Accounting & Tree Geometry Helpers -/

def bin238LevelSteps (i : Nat) : Nat :=
  let outPairs := levelSize (i + 1) / 2
  let chunks := outPairs / 64
  let rem := outPairs % 64
  9 + (if 0 < chunks then 4 + 769 * chunks else 0) + 2 + 14 * rem + 2

def bin238LevelCycles (i : Nat) : Nat :=
  let outPairs := levelSize (i + 1) / 2
  let chunks := outPairs / 64
  let rem := outPairs % 64
  9 + (if 0 < chunks then 4 + 1665 * chunks else 0) + 2 + 28 * rem + 2

def bin238LevelCalls (i : Nat) : Nat :=
  levelSize (i + 1)

theorem phase2_steps_sum :
    2 + ∑ i ∈ Finset.range 23, bin238LevelSteps i = 100794850 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; decide

theorem phase2_cycles_sum :
    2 + ∑ i ∈ Finset.range 23, bin238LevelCycles i = 218235348 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; decide

theorem phase2_calls_sum :
    ∑ i ∈ Finset.range 23, bin238LevelCalls i = 16777214 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; decide

private theorem levelSize_le_max (l : Nat) (hl : l ≤ 24) : levelSize l ≤ 16777216 := by
  interval_cases l <;> decide

private theorem levelBase_mod8 (l : Nat) (hl : l ≤ 24) : levelBase l % 8 = 0 := by
  interval_cases l <;> decide

theorem levelBase_mono : ∀ a b, a ≤ b → b ≤ 24 → levelBase a ≤ levelBase b := by
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

private theorem levelBytes_eq_gap (l : Nat) (hl : l < 24) :
    levelBytes l = (levelSize l / 2) * 96 := by
  unfold levelBytes; simp only [hl, ite_true]

private theorem nodeVal_bin_masked238 (c96 : Comp96) (msg : Message) (salts : Index → Salt121)
    (l idx : Nat) (hl : l < 23) (hidx : idx < levelSize (l + 1)) :
    mask238 (c96 (binaryInput (nodeVal c96 msg salts l (2 * idx))
      (nodeVal c96 msg salts l (2 * idx + 1)))) =
      nodeVal c96 msg salts (l + 1) idx := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) (l + 1) idx = _
  rw [nodeValFromLeaves]
  dsimp only
  unfold maskLevel
  have hlt : 2 * idx + 1 < levelSize l := by
    have hd := levelSize_double l (by omega)
    omega
  have hne24 : l + 1 ≠ 24 := by omega
  simp only [hlt, ite_true, hne24, ite_false]; rfl

/-! ### 2. Isolated Branch-Target Arithmetic & Single-Step Fetch Wrappers -/

private theorem pc_beq_711 :
    BitVec.ofNat 64 (0x1000 + 4 * 711) + signExtend13 (3096#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 1485) := by decide

private theorem pc_bne_1484 :
    BitVec.ofNat 64 (0x1000 + 4 * 1484) + signExtend13 (5120#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 716) := by decide

private theorem pc_beq_1486 :
    BitVec.ofNat 64 (0x1000 + 4 * 1486) + signExtend13 (60#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 1501) := by decide

private theorem pc_bne_1500 :
    BitVec.ofNat 64 (0x1000 + 4 * 1500) + signExtend13 (8140#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 1487) := by decide

private theorem pc_bne_1502 :
    BitVec.ofNat 64 (0x1000 + 4 * 1502) + signExtend13 (4996#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 703) := by decide

private theorem commit_step1_mid {oracle : Oracle} {s : MachineState} {idx : Nat} {ins : Instr}
    (hlo : 698 ≤ idx) (hhi : idx < 716)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hins : commitMidInstr idx = .base ins)
    (hstep : ordinaryStep s (.base ins) = some (execInstrBr s ins) := by rfl)
    (hcyc : instructionCycles (.base ins) = 1 := by rfl) :
    DetRun oracle (submission.image .commit) s 1 (execInstrBr s ins) 1 0 := by
  have hf := commit_fetch_commitMidInstr s idx hlo hhi hpc
  rw [hins] at hf
  exact DetRun.step1 hf hstep hcyc

private theorem commit_step1_tail {oracle : Oracle} {s : MachineState} {idx : Nat} {ins : Instr}
    (hlo : 1484 ≤ idx) (hhi : idx < 1523)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (hins : commitTailInstr idx = .base ins)
    (hstep : ordinaryStep s (.base ins) = some (execInstrBr s ins) := by rfl)
    (hcyc : instructionCycles (.base ins) = 1 := by rfl) :
    DetRun oracle (submission.image .commit) s 1 (execInstrBr s ins) 1 0 := by
  have hf := commit_fetch_commitTailInstr s idx hlo hhi hpc
  rw [hins] at hf
  exact DetRun.step1 hf hstep hcyc

/-! ### 3. Parameterized 238-Bit Binary Pair (`12` steps, `26` cycles, `2` calls) -/

private theorem commit_bin238_pair (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt121)
    (i p basePc : Nat) (hi : i < 23) (hp : p < levelSize (i + 1) / 2)
    (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx27 : s.getReg .x27 = mask238Word)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i + 192 * p - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * p - 64))
    (hfetch : ∀ j < 12, ∀ st : MachineState,
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + j)) →
      fetch (submission.image .commit) st = some (bin238Instr j))
    (hin0 : readBuffer s (C_TD + levelBase i + 192 * p) 32 = nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts i (4 * p))
    (hin1 : readBuffer s (C_TD + levelBase i + 192 * p + 32) 32 = nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts i (4 * p + 1))
    (hgap0 : readBuffer s (C_TD + levelBase i + 192 * p + 64) 32 = 0)
    (hin2 : readBuffer s (C_TD + levelBase i + 192 * p + 96) 32 = nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts i (4 * p + 2))
    (hin3 : readBuffer s (C_TD + levelBase i + 192 * p + 128) 32 = nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts i (4 * p + 3))
    (hgap1 : readBuffer s (C_TD + levelBase i + 192 * p + 160) 32 = 0) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s',
      DetRun oracle (submission.image .commit) s 12 s' 26 2 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 12)) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i + 192 * (p + 1) - 96) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * (p + 1) - 64) ∧
      readBuffer s' (C_TD + levelBase (i + 1) + 96 * p) 32 = nodeVal c96 msg salts (i + 1) (2 * p) ∧
      readBuffer s' (C_TD + levelBase (i + 1) + 96 * p + 32) 32 = nodeVal c96 msg salts (i + 1) (2 * p + 1) ∧
      MemPreservedOutside s s' (C_TD + levelBase (i + 1) + 96 * p) (C_TD + levelBase (i + 1) + 96 * p + 64) := by
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have htb := treeBytes_eq
  have hlb_i := levelBase_bound i (by omega)
  have hlb_o := levelBase_bound (i + 1) (by omega)
  have hmod_i := levelBase_mod8 i (by omega)
  have hmod_o := levelBase_mod8 (i + 1) (by omega)
  have hbytes_i := levelBytes_eq_gap i (by omega)
  have hbytes_o := levelBytes_eq_gap (i + 1) (by omega)
  have hd_i := levelSize_double i (by omega)
  have hev_o := levelSize_even (i + 1) (by omega)
  have hstep_b : levelBase (i + 1) = levelBase i + levelBytes i := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let src0 : Nat := C_TD + levelBase i + 192 * p
  let src1 : Nat := C_TD + levelBase i + 192 * p + 96
  let dst0 : Nat := C_TD + levelBase (i + 1) + 96 * p
  let dst1 : Nat := C_TD + levelBase (i + 1) + 96 * p + 32
  have hsrc_lt_dst : src1 + 96 ≤ dst0 := by omega
  have hdst_bd : dst1 + 32 ≤ MEMORY_BYTES := by omega
  -- First output node (2 * p) at `dst0`
  let s1 := execInstrBr s (.ADDI .x10 .x10 (96#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (64#12))
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) := pc_step_idx s basePc hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) := pc_step_idx s1 (basePc + 1) hs1_pc
  have hm2 : s2.mem = s.mem := by
    rw [show s2 = execInstrBr s1 (.ADDI .x12 .x12 (64#12)) from rfl, mem_exec_ADDI,
        show s1 = execInstrBr s (.ADDI .x10 .x10 (96#12)) from rfl, mem_exec_ADDI]
  have hs2_reg : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s2.getReg r = s.getReg r := fun r h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
  have hs2_x10 : s2.getReg .x10 = BitVec.ofNat 64 src0 := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_x12 : s2.getReg .x12 = BitVec.ofNat 64 dst0 := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), getReg_setReg_ne' .x10 .x12 (by decide), hx12,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hrb0 : readBuffer s2 src0 96 = binaryInput (nodeVal c96 msg salts i (2 * (2 * p)))
      (nodeVal c96 msg salts i (2 * (2 * p) + 1)) := by
    rw [readBuffer_of_mem_eq hm2, readBuffer_binary_of_zero_gap s src0 hgap0, hin0, hin1]
    simp only [show 2 * (2 * p) = 4 * p by omega]; rfl
  let raw0 : Digest := c96 (binaryInput (nodeVal c96 msg salts i (2 * (2 * p))) (nodeVal c96 msg salts i (2 * (2 * p) + 1)))
  let s3 := writeBits s2 (BitVec.ofNat 64 dst0) raw0
  have hr0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (hfetch 0 (by omega) s (by simpa using hpc)) rfl
  have hr1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (hfetch 1 (by omega) s1 hs1_pc) rfl
  have hr2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h768 (hfetch 2 (by omega) s2 hs2_pc)
      ((hs2_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg .x13 (by decide) (by decide)).trans hx13)
      src0 dst0 hs2_x10 hs2_x12 (by omega) (by omega) (by omega) (by omega) raw0 (by rw [hrb0])
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) := pc_step_idx s2 (basePc + 2) hs2_pc
  have hp03 : MemPreservedOutside s s3 dst0 (dst0 + 32) :=
    (MemPreservedOutside.of_mem_eq hm2 _ _).trans (memPreserved_writeBits s2 dst0 raw0 (by omega))
  obtain ⟨s6, hr35, hs6_pc, hs6_reg, hs6_val, hp36⟩ :=
    commit_mask238_step oracle s3 (basePc + 3) dst0 (by omega) (by omega)
      hs3_pc ((writeBits_register s2 _ raw0 .x12).trans hs2_x12)
      ((writeBits_register s2 _ raw0 .x27).trans ((hs2_reg .x27 (by decide) (by decide)).trans hx27))
      (fun st hst => hfetch 3 (by omega) st hst)
      (fun st hst => hfetch 4 (by omega) st hst)
      (fun st hst => hfetch 5 (by omega) st hst)
  have hp06 : MemPreservedOutside s s6 dst0 (dst0 + 32) :=
    hp03.trans (hp36.mono (by omega) (le_refl _))
  have hs6_node0 : readBuffer s6 dst0 32 = nodeVal c96 msg salts (i + 1) (2 * p) := by
    rw [hs6_val, writeBits_readBuffer_digest]
    exact nodeVal_bin_masked238 c96 msg salts i (2 * p) hi (by omega)
  -- Second output node (2 * p + 1) at `dst1`
  let s7 := execInstrBr s6 (.ADDI .x10 .x10 (96#12))
  let s8 := execInstrBr s7 (.ADDI .x12 .x12 (32#12))
  have hs7_pc : s7.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 7)) :=
    (pc_step_idx s6 (basePc + 6) (hs6_pc.trans (congrArg (BitVec.ofNat 64) (by omega)))).trans
      (congrArg (BitVec.ofNat 64) (by omega))
  have hs8_pc : s8.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 8)) := pc_step_idx s7 (basePc + 7) hs7_pc
  have hm68 : s8.mem = s6.mem := by
    rw [show s8 = execInstrBr s7 (.ADDI .x12 .x12 (32#12)) from rfl, mem_exec_ADDI,
        show s7 = execInstrBr s6 (.ADDI .x10 .x10 (96#12)) from rfl, mem_exec_ADDI]
  have hs8_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s8.getReg r = s.getReg r := fun r h6 h10 h12 => by
    simp only [s8, s7, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
    exact (hs6_reg r h6).trans ((writeBits_register s2 _ raw0 r).trans (hs2_reg r h10 h12))
  have hs8_x10 : s8.getReg .x10 = BitVec.ofNat 64 src1 := by
    simp only [s8, s7, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs6_reg .x10 (by decide),
      s3, writeBits_register, hs2_x10, add_signExtend12_ofNat_small _ 96 (by omega)]
    rfl
  have hs8_x12 : s8.getReg .x12 = BitVec.ofNat 64 dst1 := by
    simp only [s8, s7, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), getReg_setReg_ne' .x10 .x12 (by decide),
      hs6_reg .x12 (by decide), s3, writeBits_register, hs2_x12, add_signExtend12_ofNat_small _ 32 (by omega)]
    rfl
  have hrb1 : readBuffer s8 src1 96 = binaryInput (nodeVal c96 msg salts i (2 * (2 * p + 1)))
      (nodeVal c96 msg salts i (2 * (2 * p + 1) + 1)) := by
    rw [readBuffer_of_mem_eq hm68, hp06.readBuffer_eq (by omega) (Or.inl (by omega)),
      readBuffer_binary_of_zero_gap s src1 (by simpa only [show src1 + 64 = C_TD + levelBase i + 192 * p + 160 by omega] using hgap1)]
    rw [show src1 = C_TD + levelBase i + 192 * p + 96 from rfl,
      show C_TD + levelBase i + 192 * p + 96 + 32 = C_TD + levelBase i + 192 * p + 128 by omega, hin2, hin3]
    simp only [show 2 * (2 * p + 1) = 4 * p + 2 by omega]; rfl
  let raw1 : Digest := c96 (binaryInput (nodeVal c96 msg salts i (2 * (2 * p + 1)))
    (nodeVal c96 msg salts i (2 * (2 * p + 1) + 1)))
  let s9 := writeBits s8 (BitVec.ofNat 64 dst1) raw1
  have hr6 : DetRun oracle (submission.image .commit) s6 1 s7 1 0 :=
    DetRun.step1 (hfetch 6 (by omega) s6 (hs6_pc.trans (congrArg (BitVec.ofNat 64) (by omega)))) rfl
  have hr7 : DetRun oracle (submission.image .commit) s7 1 s8 1 0 :=
    DetRun.step1 (hfetch 7 (by omega) s7 hs7_pc) rfl
  have hr8 : DetRun oracle (submission.image .commit) s8 1 s9 8 1 :=
    DetRun.compress_eq h768 (hfetch 8 (by omega) s8 hs8_pc)
      ((hs8_reg .x5 (by decide) (by decide) (by decide)).trans hx5)
      ((hs8_reg .x11 (by decide) (by decide) (by decide)).trans hx11)
      ((hs8_reg .x13 (by decide) (by decide) (by decide)).trans hx13)
      src1 dst1 hs8_x10 hs8_x12 (by omega) (by omega) (by omega) (by omega) raw1 (by rw [hrb1])
  have hs9_pc : s9.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 9)) := pc_step_idx s8 (basePc + 8) hs8_pc
  have hp69 : MemPreservedOutside s6 s9 dst1 (dst1 + 32) :=
    (MemPreservedOutside.of_mem_eq hm68 _ _).trans (memPreserved_writeBits s8 dst1 raw1 (by omega))
  obtain ⟨s12, hr911, hs12_pc, hs12_reg, hs12_val, hp912⟩ :=
    commit_mask238_step oracle s9 (basePc + 9) dst1 (by omega) (by omega)
      hs9_pc ((writeBits_register s8 _ raw1 .x12).trans hs8_x12)
      ((writeBits_register s8 _ raw1 .x27).trans ((hs8_reg .x27 (by decide) (by decide) (by decide)).trans hx27))
      (fun st hst => hfetch 9 (by omega) st hst)
      (fun st hst => hfetch 10 (by omega) st hst)
      (fun st hst => hfetch 11 (by omega) st hst)
  have hp612 : MemPreservedOutside s6 s12 dst1 (dst1 + 32) :=
    hp69.trans (hp912.mono (by omega) (le_refl _))
  have hr_all : DetRun oracle (submission.image .commit) s 12 s12 26 2 := by
    have h1 := ((hr0.trans hr1).trans hr2).trans hr35
    have h2 := ((hr6.trans hr7).trans hr8).trans hr911
    exact h1.trans h2
  refine ⟨s12, hr_all, hs12_pc.trans (congrArg (BitVec.ofNat 64) (by omega)),
    fun r h6 h10 h12 => (hs12_reg r h6).trans ((writeBits_register s8 _ raw1 r).trans (hs8_reg r h6 h10 h12)),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs12_reg .x10 (by decide), writeBits_register, hs8_x10]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [hs12_reg .x12 (by decide), writeBits_register, hs8_x12]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [hp612.readBuffer_eq (by omega) (Or.inl (by omega))]
    exact hs6_node0
  · rw [hs12_val, writeBits_readBuffer_digest]
    exact nodeVal_bin_masked238 c96 msg salts i (2 * p + 1) hi (by omega)
  · exact (hp06.mono (le_refl _) (by omega)).trans (hp612.mono (by omega) (by omega))

/-! ### 4. Bulk Loop (`U = 64` pairs/chunk) and Remainder Loop -/

private theorem commit_bin238_bulk_chunk (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt121)
    (i chunks c : Nat) (hi : i < 23) (hch : chunks = (levelSize (i + 1) / 2) / 64) (hc : c < chunks)
    (sc : MachineState)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 716))
    (hx5 : sc.getReg .x5 = 0#64) (hx11 : sc.getReg .x11 = 96#64) (hx13 : sc.getReg .x13 = 0#64)
    (hx27 : sc.getReg .x27 = mask238Word)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i + 12288 * c - 96))
    (hx12 : sc.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 6144 * c - 64))
    (hx19 : sc.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase i - 96 + 12288 * chunks))
    (hin : ∀ idx < levelSize i, readBuffer sc (C_TD + levelBase i + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts i idx)
    (hgap : ∀ q < levelSize i / 2, readBuffer sc (C_TD + levelBase i + 96 * q + 64) 32 = 0) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s',
      DetRun oracle (submission.image .commit) sc 769 s' 1665 128 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < chunks then 716 else 1485)) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s'.getReg r = sc.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i + 12288 * (c + 1) - 96) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 6144 * (c + 1) - 64) ∧
      (∀ idx, 128 * c ≤ idx → idx < 128 * (c + 1) →
        readBuffer s' (C_TD + levelBase (i + 1) + gapOffset idx) 32 = nodeVal c96 msg salts (i + 1) idx) ∧
      MemPreservedOutside sc s' (C_TD + levelBase (i + 1) + 6144 * c) (C_TD + levelBase (i + 1) + 6144 * (c + 1)) ∧
      (∀ q < levelSize (i + 1) / 2, ∀ j < 32,
        s'.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j)) =
          sc.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j))) := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  have htb := treeBytes_eq
  have hlb_i := levelBase_bound i (by omega)
  have hlb_o := levelBase_bound (i + 1) (by omega)
  have hbytes_i := levelBytes_eq_gap i (by omega)
  have hbytes_o := levelBytes_eq_gap (i + 1) (by omega)
  have hd_i := levelSize_double i (by omega)
  have hstep_b : levelBase (i + 1) = levelBase i + levelBytes i := rfl
  have hind : ∀ k ≤ 64,
      ∃ sk,
        DetRun oracle (submission.image .commit) sc (12 * k) sk (26 * k) (2 * k) ∧
        sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (716 + 12 * k)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sk.getReg r = sc.getReg r) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i + 192 * (64 * c + k) - 96) ∧
        sk.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * (64 * c + k) - 64) ∧
        (∀ idx, 128 * c ≤ idx → idx < 128 * c + 2 * k →
          readBuffer sk (C_TD + levelBase (i + 1) + gapOffset idx) 32 = nodeVal c96 msg salts (i + 1) idx) ∧
        MemPreservedOutside sc sk (C_TD + levelBase (i + 1) + 6144 * c) (C_TD + levelBase (i + 1) + 6144 * c + 96 * k) ∧
        (∀ q < levelSize (i + 1) / 2, ∀ j < 32,
          sk.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j)) =
            sc.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j))) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ _ => rfl,
        by simpa only [Nat.add_zero, show 192 * (64 * c) = 12288 * c by omega] using hx10,
        by simpa only [Nat.add_zero, show 96 * (64 * c) = 6144 * c by omega] using hx12,
        fun _ h1 h2 => by omega, MemPreservedOutside.refl _ _ _, fun _ _ _ _ => rfl⟩
    | succ k ih =>
      obtain ⟨sk, hrunk, hpck, hregk, hx10k, hx12k, hnodek, hpresk, hgapk⟩ := ih (by omega)
      have hp_lt : 64 * c + k < levelSize (i + 1) / 2 := by omega
      have hsrc_le : C_TD + levelBase i + 192 * (64 * c + k) + 192 ≤ C_TD + levelBase (i + 1) + 6144 * c := by omega
      obtain ⟨sk', hpair, hpc', hreg', hx10', hx12', ho0, ho1, hpres'⟩ :=
        commit_bin238_pair h768 oracle msg salts i (64 * c + k) (716 + 12 * k) hi hp_lt sk hpck
          ((hregk .x5 (by decide) (by decide) (by decide)).trans hx5)
          ((hregk .x11 (by decide) (by decide) (by decide)).trans hx11)
          ((hregk .x13 (by decide) (by decide) (by decide)).trans hx13)
          ((hregk .x27 (by decide) (by decide) (by decide)).trans hx27)
          hx10k hx12k
          (fun j hj st hst => commit_fetch_bin238 st k j (by omega) hj hst)
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [gapOffset_even, show 4 * (64 * c + k) = 2 * (2 * (64 * c + k)) by omega,
                show 96 * (2 * (64 * c + k)) = 192 * (64 * c + k) by omega] using hin (4 * (64 * c + k)) (by omega))
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [gapOffset_odd, show 4 * (64 * c + k) + 1 = 2 * (2 * (64 * c + k)) + 1 by omega,
                show 96 * (2 * (64 * c + k)) + 32 = 192 * (64 * c + k) + 32 by omega, Nat.add_assoc] using
                hin (4 * (64 * c + k) + 1) (by omega))
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [show 96 * (2 * (64 * c + k)) = 192 * (64 * c + k) by omega] using hgap (2 * (64 * c + k)) (by omega))
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [gapOffset_even, show 4 * (64 * c + k) + 2 = 2 * (2 * (64 * c + k) + 1) by omega,
                show 96 * (2 * (64 * c + k) + 1) = 192 * (64 * c + k) + 96 by omega, Nat.add_assoc] using
                hin (4 * (64 * c + k) + 2) (by omega))
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [gapOffset_odd, show 4 * (64 * c + k) + 3 = 2 * (2 * (64 * c + k) + 1) + 1 by omega,
                show 96 * (2 * (64 * c + k) + 1) + 32 = 192 * (64 * c + k) + 128 by omega, Nat.add_assoc] using
                hin (4 * (64 * c + k) + 3) (by omega))
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [show 96 * (2 * (64 * c + k) + 1) + 64 = 192 * (64 * c + k) + 160 by omega, Nat.add_assoc] using
                hgap (2 * (64 * c + k) + 1) (by omega))
      refine ⟨sk', by simpa [Nat.mul_succ, Nat.add_assoc] using hrunk.trans hpair,
        hpc'.trans (congrArg (BitVec.ofNat 64) (by omega)),
        fun r h6 h10 h12 => (hreg' r h6 h10 h12).trans (hregk r h6 h10 h12),
        by simpa only [show 64 * c + k + 1 = 64 * c + (k + 1) by omega] using hx10',
        by simpa only [show 64 * c + k + 1 = 64 * c + (k + 1) by omega] using hx12', ?_, ?_, ?_⟩
      · intro idx hlo hhi
        by_cases hlt : idx < 128 * c + 2 * k
        · have hgo : gapOffset idx + 32 ≤ 96 * (64 * c + k) := by unfold gapOffset; omega
          rw [hpres'.readBuffer_eq (by omega) (Or.inl (by omega))]
          exact hnodek idx hlo hlt
        · by_cases hev : idx = 2 * (64 * c + k)
          · subst hev; rw [gapOffset_even]; exact ho0
          · have hodd : idx = 2 * (64 * c + k) + 1 := by omega
            subst hodd; rw [gapOffset_odd, ← Nat.add_assoc]; exact ho1
      · exact (hpresk.mono (le_refl _) (by omega)).trans (hpres'.mono (by omega) (by omega))
      · intro q hq j hj
        have hout : C_TD + levelBase (i + 1) + 96 * q + 64 + j < C_TD + levelBase (i + 1) + 96 * (64 * c + k) ∨
            C_TD + levelBase (i + 1) + 96 * (64 * c + k) + 64 ≤ C_TD + levelBase (i + 1) + 96 * q + 64 + j := by omega
        exact (hpres' _ (by omega) hout).trans (hgapk q hq j hj)
  obtain ⟨s64, hr64, hpc64, hreg64, hx10_64, hx12_64, hnode64, hpres64, hgap64⟩ := hind 64 (le_refl _)
  have hpc64' : s64.pc = BitVec.ofNat 64 (0x1000 + 4 * 1484) := hpc64
  let sbne := execInstrBr s64 (.BNE .x10 .x19 (5120#13))
  have hrbne : DetRun oracle (submission.image .commit) s64 1 sbne 1 0 :=
    commit_step1_tail (by omega) (by omega) hpc64' (by simp only [commitTailInstr])
  have hm_bne : sbne.mem = s64.mem := by
    rw [show sbne = execInstrBr s64 (.BNE .x10 .x19 (5120#13)) from rfl, mem_exec_BNE]
  have hs64_x10' : s64.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i + 12288 * (c + 1) - 96) :=
    hx10_64.trans (congrArg (BitVec.ofNat 64) (by omega))
  have hs64_x19 : s64.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase i - 96 + 12288 * chunks) :=
    (hreg64 .x19 (by decide) (by decide) (by decide)).trans hx19
  have hpc_bne : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < chunks then 716 else 1485)) := by
    simp only [sbne, execInstrBr, hs64_x10', hs64_x19]
    by_cases hlt : c + 1 < chunks
    · have hne : (BitVec.ofNat 64 (C_TD + levelBase i + 12288 * (c + 1) - 96) !=
          BitVec.ofNat 64 (C_TD + levelBase i - 96 + 12288 * chunks)) = true :=
        bne_iff_ne.mpr (bv64_ne_of_nat_ne (by omega) (by omega) (by omega))
      simp only [hlt, ite_true, hne, pc_setPC, hpc64', pc_bne_1484]
    · have heq : BitVec.ofNat 64 (C_TD + levelBase i + 12288 * (c + 1) - 96) =
          BitVec.ofNat 64 (C_TD + levelBase i - 96 + 12288 * chunks) :=
        congrArg (BitVec.ofNat 64) (by omega)
      simp only [hlt, ite_false, heq, bne_self_eq_false, Bool.false_eq_true, pc_setPC]
      exact pc_step_idx s64 1484 hpc64'
  refine ⟨sbne, hr64.trans hrbne, hpc_bne,
    fun r h6 h10 h12 => by rw [show sbne = execInstrBr s64 (.BNE .x10 .x19 (5120#13)) from rfl, reg_exec_BNE]; exact hreg64 r h6 h10 h12,
    by rw [show sbne = execInstrBr s64 (.BNE .x10 .x19 (5120#13)) from rfl, reg_exec_BNE]; exact hs64_x10',
    by rw [show sbne = execInstrBr s64 (.BNE .x10 .x19 (5120#13)) from rfl, reg_exec_BNE]; exact hx12_64.trans (congrArg (BitVec.ofNat 64) (by omega)),
    fun idx hlo hhi => by rw [readBuffer_of_mem_eq hm_bne]; exact hnode64 idx hlo (by omega),
    (hpres64.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hm_bne _ _),
    fun q hq j hj => by rw [getByte_of_mem_eq hm_bne]; exact hgap64 q hq j hj⟩

private theorem commit_bin238_rem_loop (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt121)
    (i p0 rem : Nat) (hi : i < 23) (hrem_pos : 0 < rem) (hrem_bd : p0 + rem ≤ levelSize (i + 1) / 2)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 1487))
    (hx5 : s0.getReg .x5 = 0#64) (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx27 : s0.getReg .x27 = mask238Word)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i + 192 * p0 - 96))
    (hx12 : s0.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * p0 - 64))
    (hx22 : s0.getReg .x22 = BitVec.ofNat 64 rem)
    (hin : ∀ idx < levelSize i, readBuffer s0 (C_TD + levelBase i + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts i idx)
    (hgap : ∀ q < levelSize i / 2, readBuffer s0 (C_TD + levelBase i + 96 * q + 64) 32 = 0) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s',
      DetRun oracle (submission.image .commit) s0 (14 * rem) s' (28 * rem) (2 * rem) ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * 1501) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → s'.getReg r = s0.getReg r) ∧
      (∀ idx, 2 * p0 ≤ idx → idx < 2 * (p0 + rem) →
        readBuffer s' (C_TD + levelBase (i + 1) + gapOffset idx) 32 = nodeVal c96 msg salts (i + 1) idx) ∧
      MemPreservedOutside s0 s' (C_TD + levelBase (i + 1) + 96 * p0) (C_TD + levelBase (i + 1) + 96 * (p0 + rem)) ∧
      (∀ q < levelSize (i + 1) / 2, ∀ j < 32,
        s'.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j)) =
          s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j))) := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  have htb := treeBytes_eq
  have hlb_i := levelBase_bound i (by omega)
  have hlb_o := levelBase_bound (i + 1) (by omega)
  have hbytes_i := levelBytes_eq_gap i (by omega)
  have hbytes_o := levelBytes_eq_gap (i + 1) (by omega)
  have hd_i := levelSize_double i (by omega)
  have hstep_b : levelBase (i + 1) = levelBase i + levelBytes i := rfl
  have hfetch_rem : ∀ j < 12, ∀ st : MachineState,
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * (1487 + j)) →
      fetch (submission.image .commit) st = some (bin238Instr j) := by
    intro j hj st hst
    have hf := commit_fetch_commitTailInstr st (1487 + j) (by omega) (by omega) hst
    rw [hf]; interval_cases j <;> simp only [Nat.reduceAdd, commitTailInstr, bin238Instr]
  have hind : ∀ k ≤ rem,
      ∃ sk,
        DetRun oracle (submission.image .commit) s0 (14 * k) sk (28 * k) (2 * k) ∧
        sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k < rem then 1487 else 1501)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → sk.getReg r = s0.getReg r) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i + 192 * (p0 + k) - 96) ∧
        sk.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * (p0 + k) - 64) ∧
        sk.getReg .x22 = BitVec.ofNat 64 (rem - k) ∧
        (∀ idx, 2 * p0 ≤ idx → idx < 2 * (p0 + k) →
          readBuffer sk (C_TD + levelBase (i + 1) + gapOffset idx) 32 = nodeVal c96 msg salts (i + 1) idx) ∧
        MemPreservedOutside s0 sk (C_TD + levelBase (i + 1) + 96 * p0) (C_TD + levelBase (i + 1) + 96 * (p0 + k)) ∧
        (∀ q < levelSize (i + 1) / 2, ∀ j < 32,
          sk.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j)) =
            s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j))) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨s0, DetRun.refl _ _ _, by simpa only [hrem_pos, ite_true] using hpc,
        fun _ _ _ _ _ => rfl, by simpa using hx10, by simpa using hx12, by simpa using hx22,
        fun _ h1 h2 => by omega, MemPreservedOutside.refl _ _ _, fun _ _ _ _ => rfl⟩
    | succ k ih =>
      obtain ⟨sk, hrunk, hpck, hregk, hx10k, hx12k, hx22k, hnodek, hpresk, hgapk⟩ := ih (by omega)
      have hpck' : sk.pc = BitVec.ofNat 64 (0x1000 + 4 * 1487) := by
        simpa only [show k < rem by omega, ite_true] using hpck
      have hsrc_le : C_TD + levelBase i + 192 * (p0 + k) + 192 ≤ C_TD + levelBase (i + 1) + 96 * p0 := by omega
      obtain ⟨sp, hpair, hpcp, hregp, hx10p, hx12p, ho0, ho1, hpresp⟩ :=
        commit_bin238_pair h768 oracle msg salts i (p0 + k) 1487 hi (by omega) sk hpck'
          ((hregk .x5 (by decide) (by decide) (by decide) (by decide)).trans hx5)
          ((hregk .x11 (by decide) (by decide) (by decide) (by decide)).trans hx11)
          ((hregk .x13 (by decide) (by decide) (by decide) (by decide)).trans hx13)
          ((hregk .x27 (by decide) (by decide) (by decide) (by decide)).trans hx27)
          hx10k hx12k hfetch_rem
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [gapOffset_even, show 4 * (p0 + k) = 2 * (2 * (p0 + k)) by omega,
                show 96 * (2 * (p0 + k)) = 192 * (p0 + k) by omega] using hin (4 * (p0 + k)) (by omega))
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [gapOffset_odd, show 4 * (p0 + k) + 1 = 2 * (2 * (p0 + k)) + 1 by omega,
                show 96 * (2 * (p0 + k)) + 32 = 192 * (p0 + k) + 32 by omega, Nat.add_assoc] using
                hin (4 * (p0 + k) + 1) (by omega))
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [show 96 * (2 * (p0 + k)) = 192 * (p0 + k) by omega] using hgap (2 * (p0 + k)) (by omega))
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [gapOffset_even, show 4 * (p0 + k) + 2 = 2 * (2 * (p0 + k) + 1) by omega,
                show 96 * (2 * (p0 + k) + 1) = 192 * (p0 + k) + 96 by omega, Nat.add_assoc] using
                hin (4 * (p0 + k) + 2) (by omega))
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [gapOffset_odd, show 4 * (p0 + k) + 3 = 2 * (2 * (p0 + k) + 1) + 1 by omega,
                show 96 * (2 * (p0 + k) + 1) + 32 = 192 * (p0 + k) + 128 by omega, Nat.add_assoc] using
                hin (4 * (p0 + k) + 3) (by omega))
          (by rw [hpresk.readBuffer_eq (by omega) (Or.inl (by omega))]
              simpa only [show 96 * (2 * (p0 + k) + 1) + 64 = 192 * (p0 + k) + 160 by omega, Nat.add_assoc] using
                hgap (2 * (p0 + k) + 1) (by omega))
      have hpcp' : sp.pc = BitVec.ofNat 64 (0x1000 + 4 * 1499) := hpcp
      let sdec := execInstrBr sp (.ADDI .x22 .x22 (4095#12))
      let sbne := execInstrBr sdec (.BNE .x22 .x0 (8140#13))
      have hsdec_pc : sdec.pc = BitVec.ofNat 64 (0x1000 + 4 * 1500) := pc_step_idx sp 1499 hpcp'
      have hrdec : DetRun oracle (submission.image .commit) sp 1 sdec 1 0 :=
        commit_step1_tail (by omega) (by omega) hpcp' (by simp only [commitTailInstr])
      have hrbne : DetRun oracle (submission.image .commit) sdec 1 sbne 1 0 :=
        commit_step1_tail (by omega) (by omega) hsdec_pc (by simp only [commitTailInstr])
      have hm_end : sbne.mem = sp.mem := by
        rw [show sbne = execInstrBr sdec (.BNE .x22 .x0 (8140#13)) from rfl, mem_exec_BNE,
            show sdec = execInstrBr sp (.ADDI .x22 .x22 (4095#12)) from rfl, mem_exec_ADDI]
      have hsdec_x22 : sdec.getReg .x22 = BitVec.ofNat 64 (rem - (k + 1)) := by
        simp only [sdec, execInstrBr, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0),
          hregp .x22 (by decide) (by decide) (by decide), hx22k, c_bv64_add_neg1 (rem - k) (by omega)]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have hpc_bne : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if k + 1 < rem then 1487 else 1501)) := by
        simp only [sbne, execInstrBr, hsdec_x22, c_getReg_x0]
        by_cases hlt : k + 1 < rem
        · have hne : (BitVec.ofNat 64 (rem - (k + 1)) != 0#64) = true :=
            bne_iff_ne.mpr (bv64_ne_of_nat_ne (by have := levelSize_le_max (i + 1) (by omega); omega) (by omega) (by omega))
          simp only [hlt, ite_true, hne, pc_setPC, hsdec_pc, pc_bne_1500]
        · have heq : BitVec.ofNat 64 (rem - (k + 1)) = 0#64 := by
            have : rem - (k + 1) = 0 := by omega
            rw [this]
          simp only [hlt, ite_false, heq, bne_self_eq_false, Bool.false_eq_true, pc_setPC]
          exact pc_step_idx sdec 1500 hsdec_pc
      have hrun_tot := ((hrunk.trans hpair).trans hrdec).trans hrbne
      rw [show 14 * k + 12 + 1 + 1 = 14 * (k + 1) by omega,
          show 28 * k + 26 + 1 + 1 = 28 * (k + 1) by omega,
          show 2 * k + 2 + 0 + 0 = 2 * (k + 1) by omega] at hrun_tot
      refine ⟨sbne, hrun_tot, hpc_bne, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro r h6 h10 h12 h22
        rw [show sbne = execInstrBr sdec (.BNE .x22 .x0 (8140#13)) from rfl, reg_exec_BNE]
        simp only [sdec, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 r (Ne.symm h22)]
        exact (hregp r h6 h10 h12).trans (hregk r h6 h10 h12 h22)
      · rw [show sbne = execInstrBr sdec (.BNE .x22 .x0 (8140#13)) from rfl, reg_exec_BNE]
        simp only [sdec, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 .x10 (by decide), hx10p]
        exact congrArg (BitVec.ofNat 64) (by omega)
      · rw [show sbne = execInstrBr sdec (.BNE .x22 .x0 (8140#13)) from rfl, reg_exec_BNE]
        simp only [sdec, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 .x12 (by decide), hx12p]
        exact congrArg (BitVec.ofNat 64) (by omega)
      · rw [show sbne = execInstrBr sdec (.BNE .x22 .x0 (8140#13)) from rfl, reg_exec_BNE]; exact hsdec_x22
      · intro idx hlo hhi
        rw [readBuffer_of_mem_eq hm_end]
        by_cases hlt : idx < 2 * (p0 + k)
        · have hgo : gapOffset idx + 32 ≤ 96 * (p0 + k) := by unfold gapOffset; omega
          rw [hpresp.readBuffer_eq (by omega) (Or.inl (by omega))]
          exact hnodek idx hlo hlt
        · by_cases hev : idx = 2 * (p0 + k)
          · subst hev; rw [gapOffset_even]; exact ho0
          · have hodd : idx = 2 * (p0 + k) + 1 := by omega
            subst hodd; rw [gapOffset_odd, ← Nat.add_assoc]; exact ho1
      · exact ((hpresk.mono (le_refl _) (by omega)).trans (hpresp.mono (by omega) (by omega))).trans
          (MemPreservedOutside.of_mem_eq hm_end _ _)
      · intro q hq j hj
        rw [getByte_of_mem_eq hm_end]
        have hout : C_TD + levelBase (i + 1) + 96 * q + 64 + j < C_TD + levelBase (i + 1) + 96 * (p0 + k) ∨
            C_TD + levelBase (i + 1) + 96 * (p0 + k) + 64 ≤ C_TD + levelBase (i + 1) + 96 * q + 64 + j := by omega
        exact (hpresp _ (by omega) hout).trans (hgapk q hq j hj)
  obtain ⟨sfin, hrfin, hpcfin, hregfin, _, _, _, hnodefin, hpresfin, hgapfin⟩ := hind rem (le_refl _)
  exact ⟨sfin, hrfin, by simpa only [Nat.lt_irrefl, ite_false] using hpcfin, hregfin, hnodefin, hpresfin, hgapfin⟩

/-! ### 5. Single Binary Level `i < 23` (`words 703..1502`) & Full Phase 2 (`L1..L23`) -/

private theorem commit_bin238_hdr_a (oracle : Oracle) (i : Nat) (hi : i < 23) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 703))
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * i))
    (hd0 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * i)) = BitVec.ofNat 64 (levelBase i)) :
    ∃ s3,
      DetRun oracle (submission.image .commit) s0 3 s3 3 0 ∧
      s3.pc = BitVec.ofNat 64 (0x1000 + 4 * 706) ∧
      s3.mem = s0.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → s3.getReg r = s0.getReg r) ∧
      s3.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i - 96) := by
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  have htb := treeBytes_eq
  have hlb_i := levelBase_bound i (by omega)
  let s1 := execInstrBr s0 (.LD .x6 .x24 (0#12))
  let s2 := execInstrBr s1 (.ADD .x10 .x9 .x6)
  let s3 := execInstrBr s2 (.ADDI .x10 .x10 (4000#12))
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 704) := pc_step_idx s0 703 hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 705) := pc_step_idx s1 704 hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * 706) := pc_step_idx s2 705 hs2_pc
  have hm3 : s3.mem = s0.mem := by
    rw [show s3 = execInstrBr s2 (.ADDI .x10 .x10 (4000#12)) from rfl, mem_exec_ADDI,
        show s2 = execInstrBr s1 (.ADD .x10 .x9 .x6) from rfl, mem_exec_ADD,
        show s1 = execInstrBr s0 (.LD .x6 .x24 (0#12)) from rfl, mem_exec_LD]
  have ha0 : s0.getReg .x24 + signExtend12 (0#12) = BitVec.ofNat 64 (C_DB + 32 * i) := by
    rw [hx24, add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
  have hs1_reg : ∀ r : Reg, r ≠ .x6 → s1.getReg r = s0.getReg r := fun r h6 => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm h6)]
  have hs1_x6 : s1.getReg .x6 = BitVec.ofNat 64 (levelBase i) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), ha0, hd0]
  have hs2_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → s2.getReg r = s0.getReg r := fun r h6 h10 => by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm h10)]
    exact hs1_reg r h6
  have hs2_x10 : s2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
      hs1_reg .x9 (by decide), hx9, hs1_x6, ← BitVec.ofNat_add]
  have hs3_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → s3.getReg r = s0.getReg r := fun r h6 h10 => by
    simp only [s3, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm h10)]
    exact hs2_reg r h6 h10
  have hs3_x10 : s3.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i - 96) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs2_x10,
      bv64_add_neg96 (C_TD + levelBase i) (by omega)]
  have r0 : DetRun oracle (submission.image .commit) s0 1 s1 1 0 :=
    commit_step1_mid (by omega) (by omega) hpc (by simp only [commitMidInstr])
      (ordinaryStep_LD s0 .x6 .x24 (0#12) (by rw [ha0]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have r1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    commit_step1_mid (by omega) (by omega) hs1_pc (by simp only [commitMidInstr])
  have r2 : DetRun oracle (submission.image .commit) s2 1 s3 1 0 :=
    commit_step1_mid (by omega) (by omega) hs2_pc (by simp only [commitMidInstr])
  exact ⟨s3, (r0.trans r1).trans r2, hs3_pc, hm3, hs3_reg, hs3_x10⟩

private theorem commit_bin238_hdr_b (oracle : Oracle) (i : Nat) (hi : i < 23) (s3 : MachineState)
    (hpc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * 706))
    (hx9 : s3.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx24 : s3.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * i))
    (hd1 : s3.getMem (BitVec.ofNat 64 (C_DB + 32 * i + 8)) = BitVec.ofNat 64 (levelBase (i + 1))) :
    ∃ s6,
      DetRun oracle (submission.image .commit) s3 3 s6 3 0 ∧
      s6.pc = BitVec.ofNat 64 (0x1000 + 4 * 709) ∧
      s6.mem = s3.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x12 → s6.getReg r = s3.getReg r) ∧
      s6.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) - 64) := by
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  have htb := treeBytes_eq
  have hlb_o := levelBase_bound (i + 1) (by omega)
  let s4 := execInstrBr s3 (.LD .x6 .x24 (8#12))
  let s5 := execInstrBr s4 (.ADD .x12 .x9 .x6)
  let s6 := execInstrBr s5 (.ADDI .x12 .x12 (4032#12))
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * 707) := pc_step_idx s3 706 hpc
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * 708) := pc_step_idx s4 707 hs4_pc
  have hs6_pc : s6.pc = BitVec.ofNat 64 (0x1000 + 4 * 709) := pc_step_idx s5 708 hs5_pc
  have hm6 : s6.mem = s3.mem := by
    rw [show s6 = execInstrBr s5 (.ADDI .x12 .x12 (4032#12)) from rfl, mem_exec_ADDI,
        show s5 = execInstrBr s4 (.ADD .x12 .x9 .x6) from rfl, mem_exec_ADD,
        show s4 = execInstrBr s3 (.LD .x6 .x24 (8#12)) from rfl, mem_exec_LD]
  have ha8 : s3.getReg .x24 + signExtend12 (8#12) = BitVec.ofNat 64 (C_DB + 32 * i + 8) := by
    rw [hx24, add_signExtend12_ofNat_small _ 8 (by omega)]
  have hs4_reg : ∀ r : Reg, r ≠ .x6 → s4.getReg r = s3.getReg r := fun r h6 => by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm h6)]
  have hs4_x6 : s4.getReg .x6 = BitVec.ofNat 64 (levelBase (i + 1)) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), ha8, hd1]
  have hs5_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x12 → s5.getReg r = s3.getReg r := fun r h6 h12 => by
    simp only [s5, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
    exact hs4_reg r h6
  have hs5_x12 : s5.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1)) := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      hs4_reg .x9 (by decide), hx9, hs4_x6, ← BitVec.ofNat_add]
  have hs6_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x12 → s6.getReg r = s3.getReg r := fun r h6 h12 => by
    simp only [s6, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
    exact hs5_reg r h6 h12
  have hs6_x12 : s6.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) - 64) := by
    simp only [s6, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs5_x12,
      bv64_add_neg64 (C_TD + levelBase (i + 1)) (by omega)]
  have r3 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    commit_step1_mid (by omega) (by omega) hpc (by simp only [commitMidInstr])
      (ordinaryStep_LD s3 .x6 .x24 (8#12) (by rw [ha8]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have r4 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    commit_step1_mid (by omega) (by omega) hs4_pc (by simp only [commitMidInstr])
  have r5 : DetRun oracle (submission.image .commit) s5 1 s6 1 0 :=
    commit_step1_mid (by omega) (by omega) hs5_pc (by simp only [commitMidInstr])
  exact ⟨s6, (r3.trans r4).trans r5, hs6_pc, hm6, hs6_reg, hs6_x12⟩

private theorem commit_bin238_hdr_c (oracle : Oracle) (i : Nat) (hi : i < 23) (s6 : MachineState)
    (hpc : s6.pc = BitVec.ofNat 64 (0x1000 + 4 * 709))
    (hx24 : s6.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * i))
    (hd2 : s6.getMem (BitVec.ofNat 64 (C_DB + 32 * i + 16)) = BitVec.ofNat 64 (levelSize (i + 1) / 2)) :
    let outPairs := levelSize (i + 1) / 2
    let chunks := outPairs / 64
    ∃ s9,
      DetRun oracle (submission.image .commit) s6 3 s9 3 0 ∧
      s9.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then 712 else 1485)) ∧
      s9.mem = s6.mem ∧
      (∀ r : Reg, r ≠ .x20 → r ≠ .x22 → s9.getReg r = s6.getReg r) ∧
      s9.getReg .x20 = BitVec.ofNat 64 outPairs ∧
      s9.getReg .x22 = BitVec.ofNat 64 chunks := by
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  have hsize_o := levelSize_le_max (i + 1) (by omega)
  let outPairs := levelSize (i + 1) / 2
  let chunks := outPairs / 64
  let s7 := execInstrBr s6 (.LD .x20 .x24 (16#12))
  let s8 := execInstrBr s7 (.SRLI .x22 .x20 (6#6))
  let s9 := execInstrBr s8 (.BEQ .x22 .x0 (3096#13))
  have hs7_pc : s7.pc = BitVec.ofNat 64 (0x1000 + 4 * 710) := pc_step_idx s6 709 hpc
  have hs8_pc : s8.pc = BitVec.ofNat 64 (0x1000 + 4 * 711) := pc_step_idx s7 710 hs7_pc
  have hm9 : s9.mem = s6.mem := by
    rw [show s9 = execInstrBr s8 (.BEQ .x22 .x0 (3096#13)) from rfl, mem_exec_BEQ,
        show s8 = execInstrBr s7 (.SRLI .x22 .x20 (6#6)) from rfl, mem_exec_SRLI,
        show s7 = execInstrBr s6 (.LD .x20 .x24 (16#12)) from rfl, mem_exec_LD]
  have ha16 : s6.getReg .x24 + signExtend12 (16#12) = BitVec.ofNat 64 (C_DB + 32 * i + 16) := by
    rw [hx24, add_signExtend12_ofNat_small _ 16 (by omega)]
  have hs7_reg : ∀ r : Reg, r ≠ .x20 → s7.getReg r = s6.getReg r := fun r h20 => by
    simp only [s7, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x20 r (Ne.symm h20)]
  have hs7_x20 : s7.getReg .x20 = BitVec.ofNat 64 outPairs := by
    simp only [s7, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0), ha16, hd2]
    rfl
  have hs8_reg : ∀ r : Reg, r ≠ .x20 → r ≠ .x22 → s8.getReg r = s6.getReg r := fun r h20 h22 => by
    simp only [s8, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 r (Ne.symm h22)]
    exact hs7_reg r h20
  have hs8_x20 : s8.getReg .x20 = BitVec.ofNat 64 outPairs := by
    simp only [s8, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 .x20 (by decide), hs7_x20]
  have hs8_x22 : s8.getReg .x22 = BitVec.ofNat 64 chunks := by
    simp only [s8, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), hs7_x20]
    exact bv64_ushiftRight_ofNat outPairs 6 (by omega)
  have hs9_pc : s9.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then 712 else 1485)) := by
    simp only [s9, execInstrBr, hs8_x22, c_getReg_x0]
    by_cases hch : 0 < chunks
    · have hne : (BitVec.ofNat 64 chunks == 0#64) = false :=
        beq_false_of_ne (bv64_ne_of_nat_ne (by omega) (by omega) (by omega))
      simp only [hch, ite_true, hne, Bool.false_eq_true, ite_false, pc_setPC]
      exact pc_step_idx s8 711 hs8_pc
    · have hch0 : chunks = 0 := by omega
      rw [show (if 0 < chunks then 712 else 1485) = 1485 by simp only [hch, ite_false], hch0]
      change (if (0#64 == (0#64 : Word)) = true then s8.setPC (s8.pc + signExtend13 (3096#13)) else _).pc = _
      simp only [beq_self_eq_true, ite_true, pc_setPC, hs8_pc, pc_beq_711]
  have r6 : DetRun oracle (submission.image .commit) s6 1 s7 1 0 :=
    commit_step1_mid (by omega) (by omega) hpc (by simp only [commitMidInstr])
      (ordinaryStep_LD s6 .x20 .x24 (16#12) (by rw [ha16]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have r7 : DetRun oracle (submission.image .commit) s7 1 s8 1 0 :=
    commit_step1_mid (by omega) (by omega) hs7_pc (by simp only [commitMidInstr])
  have r8 : DetRun oracle (submission.image .commit) s8 1 s9 1 0 :=
    commit_step1_mid (by omega) (by omega) hs8_pc (by simp only [commitMidInstr])
  exact ⟨s9, (r6.trans r7).trans r8, hs9_pc, hm9,
    fun r h20 h22 => by rw [show s9 = execInstrBr s8 (.BEQ .x22 .x0 (3096#13)) from rfl, reg_exec_BEQ]; exact hs8_reg r h20 h22,
    by rw [show s9 = execInstrBr s8 (.BEQ .x22 .x0 (3096#13)) from rfl, reg_exec_BEQ]; exact hs8_x20,
    by rw [show s9 = execInstrBr s8 (.BEQ .x22 .x0 (3096#13)) from rfl, reg_exec_BEQ]; exact hs8_x22⟩

private theorem commit_bin238_bulk_setup (oracle : Oracle) (i chunks : Nat)
    (hi : i < 23) (hch_bd : chunks ≤ 131072) (s9 : MachineState)
    (hpc : s9.pc = BitVec.ofNat 64 (0x1000 + 4 * 712))
    (hx10 : s9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i - 96))
    (hx22 : s9.getReg .x22 = BitVec.ofNat 64 chunks) :
    ∃ sa4,
      DetRun oracle (submission.image .commit) s9 4 sa4 4 0 ∧
      sa4.pc = BitVec.ofNat 64 (0x1000 + 4 * 716) ∧
      sa4.mem = s9.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x19 → sa4.getReg r = s9.getReg r) ∧
      sa4.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase i - 96 + 12288 * chunks) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have htb := treeBytes_eq
  have hlb_i := levelBase_bound i (by omega)
  let sa1 := execInstrBr s9 (.SLLI .x6 .x22 (12#6))
  let sa2 := execInstrBr sa1 (.SLLI .x7 .x22 (13#6))
  let sa3 := execInstrBr sa2 (.ADD .x6 .x6 .x7)
  let sa4 := execInstrBr sa3 (.ADD .x19 .x10 .x6)
  have hsa1_pc : sa1.pc = BitVec.ofNat 64 (0x1000 + 4 * 713) := pc_step_idx s9 712 hpc
  have hsa2_pc : sa2.pc = BitVec.ofNat 64 (0x1000 + 4 * 714) := pc_step_idx sa1 713 hsa1_pc
  have hsa3_pc : sa3.pc = BitVec.ofNat 64 (0x1000 + 4 * 715) := pc_step_idx sa2 714 hsa2_pc
  have hsa4_pc : sa4.pc = BitVec.ofNat 64 (0x1000 + 4 * 716) := pc_step_idx sa3 715 hsa3_pc
  have hma4 : sa4.mem = s9.mem := by
    rw [show sa4 = execInstrBr sa3 (.ADD .x19 .x10 .x6) from rfl, mem_exec_ADD,
        show sa3 = execInstrBr sa2 (.ADD .x6 .x6 .x7) from rfl, mem_exec_ADD,
        show sa2 = execInstrBr sa1 (.SLLI .x7 .x22 (13#6)) from rfl, mem_exec_SLLI,
        show sa1 = execInstrBr s9 (.SLLI .x6 .x22 (12#6)) from rfl, mem_exec_SLLI]
  have hsa1_reg : ∀ r : Reg, r ≠ .x6 → sa1.getReg r = s9.getReg r := fun r h6 => by
    simp only [sa1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm h6)]
  have hsa1_x6 : sa1.getReg .x6 = BitVec.ofNat 64 (chunks * 4096) := by
    simp only [sa1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hx22]
    exact (bv64_shiftLeft_ofNat chunks 12 (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have hsa2_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → sa2.getReg r = s9.getReg r := fun r h6 h7 => by
    simp only [sa2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x7 r (Ne.symm h7)]
    exact hsa1_reg r h6
  have hsa2_x6 : sa2.getReg .x6 = BitVec.ofNat 64 (chunks * 4096) := by
    simp only [sa2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x7 .x6 (by decide), hsa1_x6]
  have hsa2_x7 : sa2.getReg .x7 = BitVec.ofNat 64 (chunks * 8192) := by
    simp only [sa2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x7 ≠ .x0), hsa1_reg .x22 (by decide), hx22]
    exact (bv64_shiftLeft_ofNat chunks 13 (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have hsa3_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → sa3.getReg r = s9.getReg r := fun r h6 h7 => by
    simp only [sa3, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm h6)]
    exact hsa2_reg r h6 h7
  have hsa3_x6 : sa3.getReg .x6 = BitVec.ofNat 64 (12288 * chunks) := by
    simp only [sa3, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hsa2_x6, hsa2_x7, ← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hsa4_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x19 → sa4.getReg r = s9.getReg r := fun r h6 h7 h19 => by
    simp only [sa4, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x19 r (Ne.symm h19)]
    exact hsa3_reg r h6 h7
  have hsa4_x19 : sa4.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase i - 96 + 12288 * chunks) := by
    simp only [sa4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x19 ≠ .x0),
      hsa3_reg .x10 (by decide) (by decide), hx10, hsa3_x6, ← BitVec.ofNat_add]
  have ra1 : DetRun oracle (submission.image .commit) s9 1 sa1 1 0 :=
    commit_step1_mid (by omega) (by omega) hpc (by simp only [commitMidInstr])
  have ra2 : DetRun oracle (submission.image .commit) sa1 1 sa2 1 0 :=
    commit_step1_mid (by omega) (by omega) hsa1_pc (by simp only [commitMidInstr])
  have ra3 : DetRun oracle (submission.image .commit) sa2 1 sa3 1 0 :=
    commit_step1_mid (by omega) (by omega) hsa2_pc (by simp only [commitMidInstr])
  have ra4 : DetRun oracle (submission.image .commit) sa3 1 sa4 1 0 :=
    commit_step1_mid (by omega) (by omega) hsa3_pc (by simp only [commitMidInstr])
  exact ⟨sa4, ((ra1.trans ra2).trans ra3).trans ra4, hsa4_pc, hma4, hsa4_reg, hsa4_x19⟩

private theorem commit_bin238_level (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt121)
    (i : Nat) (hi : i < 23) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 703))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * i))
    (hx25 : s0.getReg .x25 = BitVec.ofNat 64 (C_DB + 736))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hx27 : s0.getReg .x27 = mask238Word)
    (hdata : ∀ off < 736, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hin : ∀ idx < levelSize i, readBuffer s0 (C_TD + levelBase i + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts i idx)
    (hgap : ∀ q < levelSize i / 2, readBuffer s0 (C_TD + levelBase i + 96 * q + 64) 32 = 0) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 (bin238LevelSteps i) s1
        (bin238LevelCycles i) (bin238LevelCalls i) ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (if i + 1 < 23 then 703 else 1503)) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (i + 1)) ∧
      s1.getReg .x25 = BitVec.ofNat 64 (C_DB + 736) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      s1.getReg .x27 = mask238Word ∧
      (∀ idx < levelSize (i + 1), readBuffer s1 (C_TD + levelBase (i + 1) + gapOffset idx) 32 =
        nodeVal c96 msg salts (i + 1) idx) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase (i + 1)) (C_TD + levelBase (i + 2)) ∧
      (∀ q < levelSize (i + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j)) =
          s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j))) := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  have htb := treeBytes_eq
  have hlb_i := levelBase_bound i (by omega)
  have hlb_o := levelBase_bound (i + 1) (by omega)
  have hbytes_i := levelBytes_eq_gap i (by omega)
  have hbytes_o := levelBytes_eq_gap (i + 1) (by omega)
  have hsize_o := levelSize_le_max (i + 1) (by omega)
  have hev_o := levelSize_even (i + 1) (by omega)
  have hstep_b2 : levelBase (i + 2) = levelBase (i + 1) + levelBytes (i + 1) := rfl
  let outPairs := levelSize (i + 1) / 2
  let chunks := outPairs / 64
  let rem := outPairs % 64
  -- Read table words from `commitData` at `C_DB + 32 * i`
  have hd0 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * i)) = BitVec.ofNat 64 (levelBase i) := by
    rw [hdata (32 * i) (by omega) (by omega), commit_initial_data_dword msg (32 * i) (by omega)]
    exact commitData_dword_0 ⟨i, hi⟩
  have hd1 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * i + 8)) = BitVec.ofNat 64 (levelBase (i + 1)) := by
    rw [show C_DB + 32 * i + 8 = C_DB + (32 * i + 8) by omega,
      hdata (32 * i + 8) (by omega) (by omega), commit_initial_data_dword msg (32 * i + 8) (by omega)]
    exact commitData_dword_1 ⟨i, hi⟩
  have hd2 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * i + 16)) = BitVec.ofNat 64 outPairs := by
    rw [show C_DB + 32 * i + 16 = C_DB + (32 * i + 16) by omega,
      hdata (32 * i + 16) (by omega) (by omega), commit_initial_data_dword msg (32 * i + 16) (by omega)]
    exact commitData_dword_2 ⟨i, hi⟩
  -- Header: words `703..711` (9 steps, 9 cycles, split into 3 opaque 3-step hops)
  obtain ⟨s3, hr_a, hs3_pc, hm3, hs3_reg, hs3_x10⟩ := commit_bin238_hdr_a oracle i hi s0 hpc hx9 hx24 hd0
  obtain ⟨s6, hr_b, hs6_pc, hm6, hs6_reg, hs6_x12⟩ := commit_bin238_hdr_b oracle i hi s3 hs3_pc
    ((hs3_reg .x9 (by decide) (by decide)).trans hx9)
    ((hs3_reg .x24 (by decide) (by decide)).trans hx24)
    (by simp only [MachineState.getMem, hm3]; exact hd1)
  obtain ⟨s9, hr_c, hs9_pc_if, hm9, hs9_reg_c, hs9_x20, hs9_x22⟩ := commit_bin238_hdr_c oracle i hi s6 hs6_pc
    ((hs6_reg .x24 (by decide) (by decide)).trans ((hs3_reg .x24 (by decide) (by decide)).trans hx24))
    (by simp only [MachineState.getMem, hm6, hm3]; exact hd2)
  have hhdr : DetRun oracle (submission.image .commit) s0 9 s9 9 0 := (hr_a.trans hr_b).trans hr_c
  have hm09 : s9.mem = s0.mem := hm9.trans (hm6.trans hm3)
  have hs9_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x20 → r ≠ .x22 → s9.getReg r = s0.getReg r :=
    fun r h6 h10 h12 h20 h22 =>
      (hs9_reg_c r h20 h22).trans ((hs6_reg r h6 h12).trans (hs3_reg r h6 h10))
  have hs9_x10 : s9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i - 96) :=
    (hs9_reg_c .x10 (by decide) (by decide)).trans ((hs6_reg .x10 (by decide) (by decide)).trans hs3_x10)
  have hs9_x12 : s9.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) - 64) :=
    (hs9_reg_c .x12 (by decide) (by decide)).trans hs6_x12
  -- Stage A: Bulk loop (if `0 < chunks`, runs `4 + 769 * chunks` steps / `4 + 1665 * chunks` cycles / `128 * chunks` calls)
  have hstageA :
      ∃ sA,
        DetRun oracle (submission.image .commit) s9
          (if 0 < chunks then 4 + 769 * chunks else 0) sA
          (if 0 < chunks then 4 + 1665 * chunks else 0) (128 * chunks) ∧
        sA.pc = BitVec.ofNat 64 (0x1000 + 4 * 1485) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → r ≠ .x20 → r ≠ .x22 → sA.getReg r = s0.getReg r) ∧
        sA.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i + 192 * (64 * chunks) - 96) ∧
        sA.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * (64 * chunks) - 64) ∧
        sA.getReg .x20 = BitVec.ofNat 64 outPairs ∧
        (∀ idx < 128 * chunks, readBuffer sA (C_TD + levelBase (i + 1) + gapOffset idx) 32 = nodeVal c96 msg salts (i + 1) idx) ∧
        MemPreservedOutside s0 sA (C_TD + levelBase (i + 1)) (C_TD + levelBase (i + 1) + 6144 * chunks) ∧
        (∀ q < levelSize (i + 1) / 2, ∀ j < 32,
          sA.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j)) =
            s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j))) := by
    by_cases hch : 0 < chunks
    · simp only [hch, ite_true]
      have hs9_pc : s9.pc = BitVec.ofNat 64 (0x1000 + 4 * 712) := by
        simpa only [chunks, outPairs, hch, ite_true] using hs9_pc_if
      obtain ⟨sa4, hrsetup, hsa4_pc, hma4_9, hsa4_reg, hsa4_x19⟩ :=
        commit_bin238_bulk_setup oracle i chunks hi (by omega) s9 hs9_pc hs9_x10 hs9_x22
      have hma4 : sa4.mem = s0.mem := hma4_9.trans hm09
      have hloop : ∀ c ≤ chunks,
          ∃ sc,
            DetRun oracle (submission.image .commit) sa4 (769 * c) sc (1665 * c) (128 * c) ∧
            sc.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c < chunks then 716 else 1485)) ∧
            (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sc.getReg r = sa4.getReg r) ∧
            sc.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase i + 12288 * c - 96) ∧
            sc.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 6144 * c - 64) ∧
            (∀ idx < 128 * c, readBuffer sc (C_TD + levelBase (i + 1) + gapOffset idx) 32 = nodeVal c96 msg salts (i + 1) idx) ∧
            MemPreservedOutside s0 sc (C_TD + levelBase (i + 1)) (C_TD + levelBase (i + 1) + 6144 * c) ∧
            (∀ q < levelSize (i + 1) / 2, ∀ j < 32,
              sc.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j)) =
                s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j))) := by
        intro c hc; induction c with
        | zero =>
          exact ⟨sa4, DetRun.refl _ _ _, by simpa only [hch, ite_true] using hsa4_pc,
            fun _ _ _ _ => rfl,
            by simpa only [Nat.mul_zero, Nat.add_zero] using (hsa4_reg .x10 (by decide) (by decide) (by decide)).trans hs9_x10,
            by simpa only [Nat.mul_zero, Nat.add_zero] using (hsa4_reg .x12 (by decide) (by decide) (by decide)).trans hs9_x12,
            fun _ h => (Nat.not_lt_zero _ h).elim, MemPreservedOutside.of_mem_eq hma4 _ _,
            fun q hq j hj => getByte_of_mem_eq hma4 _⟩
        | succ c ih =>
          obtain ⟨sc, hrunc, hpcc, hregc, hx10c, hx12c, hnodec, hpresc, hgapc⟩ := ih (by omega)
          have hpcc' : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 716) := by
            simpa only [show c < chunks by omega, ite_true] using hpcc
          have hin_c : ∀ idx < levelSize i, readBuffer sc (C_TD + levelBase i + gapOffset idx) 32 = nodeVal c96 msg salts i idx := by
            intro idx hidx
            have hgo := gapOffset_lt_levelBytes i idx (by omega) hidx
            have hstep_b : levelBase (i + 1) = levelBase i + levelBytes i := rfl
            rw [hpresc.readBuffer_eq (by omega) (Or.inl (by omega))]
            exact hin idx hidx
          have hgap_c : ∀ q < levelSize i / 2, readBuffer sc (C_TD + levelBase i + 96 * q + 64) 32 = 0 := by
            intro q hq
            have hstep_b : levelBase (i + 1) = levelBase i + levelBytes i := rfl
            rw [hpresc.readBuffer_eq (by omega) (Or.inl (by omega))]
            exact hgap q hq
          obtain ⟨sc', hchunk, hpc', hreg', hx10', hx12', hnode', hpres', hgap'⟩ :=
            commit_bin238_bulk_chunk h768 oracle msg salts i chunks c hi rfl (by omega) sc hpcc'
              ((hregc .x5 (by decide) (by decide) (by decide)).trans ((hsa4_reg .x5 (by decide) (by decide) (by decide)).trans
                ((hs9_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5)))
              ((hregc .x11 (by decide) (by decide) (by decide)).trans ((hsa4_reg .x11 (by decide) (by decide) (by decide)).trans
                ((hs9_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11)))
              ((hregc .x13 (by decide) (by decide) (by decide)).trans ((hsa4_reg .x13 (by decide) (by decide) (by decide)).trans
                ((hs9_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13)))
              ((hregc .x27 (by decide) (by decide) (by decide)).trans ((hsa4_reg .x27 (by decide) (by decide) (by decide)).trans
                ((hs9_reg .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)))
              hx10c hx12c ((hregc .x19 (by decide) (by decide) (by decide)).trans hsa4_x19) hin_c hgap_c
          refine ⟨sc', by simpa [Nat.mul_succ, Nat.add_assoc] using hrunc.trans hchunk, hpc',
            fun r h6 h10 h12 => (hreg' r h6 h10 h12).trans (hregc r h6 h10 h12), hx10', hx12', ?_, ?_, ?_⟩
          · intro idx hidx
            by_cases hlt : idx < 128 * c
            · have hgo : gapOffset idx + 32 ≤ 6144 * c := by unfold gapOffset; omega
              rw [hpres'.readBuffer_eq (by omega) (Or.inl (by omega))]
              exact hnodec idx hlt
            · exact hnode' idx (by omega) hidx
          · exact (hpresc.mono (le_refl _) (by omega)).trans (hpres'.mono (by omega) (by omega))
          · intro q hq j hj; exact (hgap' q hq j hj).trans (hgapc q hq j hj)
      obtain ⟨sA, hrunA, hpcA, hregA, hx10A, hx12A, hnodeA, hpresA, hgapA⟩ := hloop chunks (le_refl _)
      refine ⟨sA, by simpa only [Nat.zero_add] using hrsetup.trans hrunA, by simpa only [Nat.lt_irrefl, ite_false] using hpcA,
        fun r h6 h7 h10 h12 h19 h20 h22 =>
          (hregA r h6 h10 h12).trans ((hsa4_reg r h6 h7 h19).trans (hs9_reg r h6 h10 h12 h20 h22)),
        hx10A.trans (congrArg (BitVec.ofNat 64) (by omega)),
        hx12A.trans (congrArg (BitVec.ofNat 64) (by omega)),
        (hregA .x20 (by decide) (by decide) (by decide)).trans
          ((hsa4_reg .x20 (by decide) (by decide) (by decide)).trans hs9_x20),
        hnodeA, hpresA, hgapA⟩
    · have hch0 : chunks = 0 := by omega
      have hs9_pc : s9.pc = BitVec.ofNat 64 (0x1000 + 4 * 1485) := by
        simpa only [chunks, outPairs, hch, ite_false] using hs9_pc_if
      simp only [hch0, Nat.mul_zero, Nat.add_zero]
      exact ⟨s9, DetRun.refl _ _ _, hs9_pc,
        fun r h6 _ h10 h12 _ h20 h22 => hs9_reg r h6 h10 h12 h20 h22,
        hs9_x10, hs9_x12, hs9_x20,
        fun _ h => (Nat.not_lt_zero _ h).elim,
        MemPreservedOutside.of_mem_eq hm09 _ _, fun _ _ _ _ => getByte_of_mem_eq hm09 _⟩
  obtain ⟨sA, hrunA, hpcA, hregA, hx10A, hx12A, hx20A, hnodeA, hpresA, hgapA⟩ := hstageA
  -- Stage B: Remainder check (`1485..1486`) + remainder loop (`1487..1500`)
  let sb1 := execInstrBr sA (.ANDI .x22 .x20 (63#12))
  let sb2 := execInstrBr sb1 (.BEQ .x22 .x0 (60#13))
  have hsb1_pc : sb1.pc = BitVec.ofNat 64 (0x1000 + 4 * 1486) := pc_step_idx sA 1485 hpcA
  have hrb1 : DetRun oracle (submission.image .commit) sA 1 sb1 1 0 :=
    commit_step1_tail (by omega) (by omega) hpcA (by simp only [commitTailInstr])
  have hrb2 : DetRun oracle (submission.image .commit) sb1 1 sb2 1 0 :=
    commit_step1_tail (by omega) (by omega) hsb1_pc (by simp only [commitTailInstr])
  have hmb2 : sb2.mem = sA.mem := by
    rw [show sb2 = execInstrBr sb1 (.BEQ .x22 .x0 (60#13)) from rfl, mem_exec_BEQ,
        show sb1 = execInstrBr sA (.ANDI .x22 .x20 (63#12)) from rfl, mem_exec_ANDI]
  have hsb1_x22 : sb1.getReg .x22 = BitVec.ofNat 64 rem := by
    simp only [sb1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), hx20A]
    exact bv64_and_63 outPairs (by omega)
  have hsb2_reg : ∀ r : Reg, r ≠ .x22 → sb2.getReg r = sA.getReg r := fun r h22 => by
    rw [show sb2 = execInstrBr sb1 (.BEQ .x22 .x0 (60#13)) from rfl, reg_exec_BEQ]
    simp only [sb1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 r (Ne.symm h22)]
  have hstageB :
      ∃ sB,
        DetRun oracle (submission.image .commit) sb2 (14 * rem) sB (28 * rem) (2 * rem) ∧
        sB.pc = BitVec.ofNat 64 (0x1000 + 4 * 1501) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → r ≠ .x20 → r ≠ .x22 → sB.getReg r = s0.getReg r) ∧
        (∀ idx < levelSize (i + 1), readBuffer sB (C_TD + levelBase (i + 1) + gapOffset idx) 32 = nodeVal c96 msg salts (i + 1) idx) ∧
        MemPreservedOutside s0 sB (C_TD + levelBase (i + 1)) (C_TD + levelBase (i + 2)) ∧
        (∀ q < levelSize (i + 1) / 2, ∀ j < 32,
          sB.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j)) =
            s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (i + 1) + 96 * q + 64 + j))) := by
    by_cases hrem : 0 < rem
    · have hsb2_pc : sb2.pc = BitVec.ofNat 64 (0x1000 + 4 * 1487) := by
        simp only [sb2, execInstrBr, hsb1_x22, c_getReg_x0]
        have hne : (BitVec.ofNat 64 rem == 0#64) = false :=
          beq_false_of_ne (bv64_ne_of_nat_ne (by omega) (by omega) (by omega))
        simp only [hne, Bool.false_eq_true, ite_false, pc_setPC]
        exact pc_step_idx sb1 1486 hsb1_pc
      have hin_B : ∀ idx < levelSize i, readBuffer sb2 (C_TD + levelBase i + gapOffset idx) 32 = nodeVal c96 msg salts i idx := by
        intro idx hidx
        have hgo := gapOffset_lt_levelBytes i idx (by omega) hidx
        have hstep_b : levelBase (i + 1) = levelBase i + levelBytes i := rfl
        rw [readBuffer_of_mem_eq hmb2, hpresA.readBuffer_eq (by omega) (Or.inl (by omega))]
        exact hin idx hidx
      have hgap_B : ∀ q < levelSize i / 2, readBuffer sb2 (C_TD + levelBase i + 96 * q + 64) 32 = 0 := by
        intro q hq
        have hstep_b : levelBase (i + 1) = levelBase i + levelBytes i := rfl
        rw [readBuffer_of_mem_eq hmb2, hpresA.readBuffer_eq (by omega) (Or.inl (by omega))]
        exact hgap q hq
      obtain ⟨sB, hrunB, hpcB, hregB, hnodeB, hpresB, hgapB⟩ :=
        commit_bin238_rem_loop h768 oracle msg salts i (64 * chunks) rem hi hrem (by omega) sb2 hsb2_pc
          ((hsb2_reg .x5 (by decide)).trans ((hregA .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5))
          ((hsb2_reg .x11 (by decide)).trans ((hregA .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11))
          ((hsb2_reg .x13 (by decide)).trans ((hregA .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13))
          ((hsb2_reg .x27 (by decide)).trans ((hregA .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27))
          ((hsb2_reg .x10 (by decide)).trans hx10A)
          ((hsb2_reg .x12 (by decide)).trans hx12A)
          (by rw [show sb2 = execInstrBr sb1 (.BEQ .x22 .x0 (60#13)) from rfl, reg_exec_BEQ]; exact hsb1_x22)
          hin_B hgap_B
      refine ⟨sB, hrunB, hpcB,
        fun r h6 h7 h10 h12 h19 h20 h22 =>
          (hregB r h6 h10 h12 h22).trans ((hsb2_reg r h22).trans (hregA r h6 h7 h10 h12 h19 h20 h22)),
        ?_, ?_, ?_⟩
      · intro idx hidx
        by_cases hlt : idx < 128 * chunks
        · have hgo : gapOffset idx + 32 ≤ 96 * (64 * chunks) := by unfold gapOffset; omega
          rw [hpresB.readBuffer_eq (by omega) (Or.inl (by omega)), readBuffer_of_mem_eq hmb2]
          exact hnodeA idx hlt
        · exact hnodeB idx (by omega) (by omega)
      · have htot_end : 96 * (64 * chunks + rem) = levelBytes (i + 1) := by omega
        exact ((hpresA.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmb2 _ _)).trans
          (hpresB.mono (by omega) (by omega))
      · intro q hq j hj
        exact (hgapB q hq j hj).trans ((getByte_of_mem_eq hmb2 _).trans (hgapA q hq j hj))
    · have hrem0 : rem = 0 := by omega
      simp only [hrem0, Nat.mul_zero]
      have hsb2_pc : sb2.pc = BitVec.ofNat 64 (0x1000 + 4 * 1501) := by
        simp only [sb2, execInstrBr, hsb1_x22, hrem0, c_getReg_x0]
        simp only [beq_self_eq_true, ite_true, pc_setPC, hsb1_pc, pc_beq_1486]
      refine ⟨sb2, DetRun.refl _ _ _, hsb2_pc,
        fun r h6 h7 h10 h12 h19 h20 h22 => (hsb2_reg r h22).trans (hregA r h6 h7 h10 h12 h19 h20 h22),
        fun idx hidx => by rw [readBuffer_of_mem_eq hmb2]; exact hnodeA idx (by omega),
        (hpresA.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmb2 _ _),
        fun q hq j hj => (getByte_of_mem_eq hmb2 _).trans (hgapA q hq j hj)⟩
  obtain ⟨sB, hrunB, hpcB, hregB, hnodeB, hpresB, hgapB⟩ := hstageB
  -- Footer (`1501..1502`): `ADDI x24, x24, 32; BNE x24, x25, bin238_lvl_loop`
  let sf1 := execInstrBr sB (.ADDI .x24 .x24 (32#12))
  let sf2 := execInstrBr sf1 (.BNE .x24 .x25 (4996#13))
  have hsf1_pc : sf1.pc = BitVec.ofNat 64 (0x1000 + 4 * 1502) := pc_step_idx sB 1501 hpcB
  have hrf1 : DetRun oracle (submission.image .commit) sB 1 sf1 1 0 :=
    commit_step1_tail (by omega) (by omega) hpcB (by simp only [commitTailInstr])
  have hrf2 : DetRun oracle (submission.image .commit) sf1 1 sf2 1 0 :=
    commit_step1_tail (by omega) (by omega) hsf1_pc (by simp only [commitTailInstr])
  have hmf2 : sf2.mem = sB.mem := by
    rw [show sf2 = execInstrBr sf1 (.BNE .x24 .x25 (4996#13)) from rfl, mem_exec_BNE,
        show sf1 = execInstrBr sB (.ADDI .x24 .x24 (32#12)) from rfl, mem_exec_ADDI]
  have hsf1_x24 : sf1.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (i + 1)) := by
    simp only [sf1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x24 ≠ .x0),
      hregB .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx24,
      add_signExtend12_ofNat_small _ 32 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hsf1_x25 : sf1.getReg .x25 = BitVec.ofNat 64 (C_DB + 736) := by
    simp only [sf1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x24 .x25 (by decide),
      hregB .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx25]
  have hsf2_pc : sf2.pc = BitVec.ofNat 64 (0x1000 + 4 * (if i + 1 < 23 then 703 else 1503)) := by
    simp only [sf2, execInstrBr, hsf1_x24, hsf1_x25]
    by_cases hlt : i + 1 < 23
    · have hne : (BitVec.ofNat 64 (C_DB + 32 * (i + 1)) != BitVec.ofNat 64 (C_DB + 736)) = true :=
        bne_iff_ne.mpr (bv64_ne_of_nat_ne (by omega) (by omega) (by omega))
      simp only [hlt, ite_true, hne, pc_setPC, hsf1_pc, pc_bne_1502]
    · have heq : BitVec.ofNat 64 (C_DB + 32 * (i + 1)) = BitVec.ofNat 64 (C_DB + 736) :=
        congrArg (BitVec.ofNat 64) (by omega)
      simp only [hlt, ite_false, heq, bne_self_eq_false, Bool.false_eq_true, pc_setPC]
      exact pc_step_idx sf1 1502 hsf1_pc
  have hsf2_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → r ≠ .x20 → r ≠ .x22 → r ≠ .x24 →
      sf2.getReg r = s0.getReg r := fun r h6 h7 h10 h12 h19 h20 h22 h24 => by
    rw [show sf2 = execInstrBr sf1 (.BNE .x24 .x25 (4996#13)) from rfl, reg_exec_BNE]
    simp only [sf1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x24 r (Ne.symm h24)]
    exact hregB r h6 h7 h10 h12 h19 h20 h22
  have htot_run := (((((hhdr.trans hrunA).trans hrb1).trans hrb2).trans hrunB).trans hrf1).trans hrf2
  have hst_eq : 9 + (if 0 < chunks then 4 + 769 * chunks else 0) + 1 + 1 + 14 * rem + 1 + 1 = bin238LevelSteps i := rfl
  have hcy_eq : 9 + (if 0 < chunks then 4 + 1665 * chunks else 0) + 1 + 1 + 28 * rem + 1 + 1 = bin238LevelCycles i := rfl
  have hca_eq : 0 + 128 * chunks + 0 + 0 + 2 * rem + 0 + 0 = bin238LevelCalls i := by
    unfold bin238LevelCalls; dsimp only [outPairs, chunks, rem]; omega
  rw [hst_eq, hcy_eq, hca_eq] at htot_run
  refine ⟨sf2, htot_run, hsf2_pc,
    (hsf2_reg .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx2,
    (hsf2_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5,
    (hsf2_reg .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx9,
    (hsf2_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11,
    (hsf2_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13,
    by rw [show sf2 = execInstrBr sf1 (.BNE .x24 .x25 (4996#13)) from rfl, reg_exec_BNE]; exact hsf1_x24,
    by rw [show sf2 = execInstrBr sf1 (.BNE .x24 .x25 (4996#13)) from rfl, reg_exec_BNE]; exact hsf1_x25,
    (hsf2_reg .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26,
    (hsf2_reg .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27,
    fun idx hidx => by rw [readBuffer_of_mem_eq hmf2]; exact hnodeB idx hidx,
    hpresB.trans (MemPreservedOutside.of_mem_eq hmf2 _ _),
    fun q hq j hj => (getByte_of_mem_eq hmf2 _).trans (hgapB q hq j hj)⟩

/-- Full Phase 2 (`L1..L23`, words `701..1502`): `100,794,850` steps, `218,235,348` cycles,
`16,777,214` compression calls. -/
theorem commit_phase2 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt121) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 701))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hx27 : s0.getReg .x27 = mask238Word)
    (hdata : ∀ off < 736, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)))
    (hl0 : ∀ idx < levelSize 0, readBuffer s0 (C_TD + levelBase 0 + gapOffset idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 0 idx)
    (hzero : ∀ l < 24, ∀ q < levelSize l / 2, ∀ j < 32,
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 100794850 s1 218235348 16777214 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 1503) ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ l ≤ 23, ∀ idx < levelSize l, readBuffer s1 (C_TD + levelBase l + gapOffset idx) 32 =
        nodeVal c96 msg salts l idx) ∧
      (∀ l < 24, ∀ q < levelSize l / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 1) (C_TD + levelBase 24) := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  have htb := treeBytes_eq
  let sa0 := execInstrBr s0 (.ADDI .x24 .x2 (0#12))
  let sa := execInstrBr sa0 (.ADDI .x25 .x2 (736#12))
  have hsa0_pc : sa0.pc = BitVec.ofNat 64 (0x1000 + 4 * 702) := pc_step_idx s0 701 hpc
  have hsa_pc : sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 703) := pc_step_idx sa0 702 hsa0_pc
  have hsetup : DetRun oracle (submission.image .commit) s0 2 sa 2 0 := by
    have rs0 : DetRun oracle (submission.image .commit) s0 1 sa0 1 0 :=
      commit_step1_mid (by omega) (by omega) hpc (by simp only [commitMidInstr])
    have rs1 : DetRun oracle (submission.image .commit) sa0 1 sa 1 0 :=
      commit_step1_mid (by omega) (by omega) hsa0_pc (by simp only [commitMidInstr])
    exact rs0.trans rs1
  have hsa_mem : sa.mem = s0.mem := by
    rw [show sa = execInstrBr sa0 (.ADDI .x25 .x2 (736#12)) from rfl, mem_exec_ADDI,
        show sa0 = execInstrBr s0 (.ADDI .x24 .x2 (0#12)) from rfl, mem_exec_ADDI]
  have hsa_reg : ∀ r : Reg, r ≠ .x24 → r ≠ .x25 → sa.getReg r = s0.getReg r := fun r h24 h25 => by
    simp only [sa, sa0, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x25 r (Ne.symm h25), getReg_setReg_ne' .x24 r (Ne.symm h24)]
  have hind : ∀ n ≤ 23,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa (∑ i ∈ Finset.range n, bin238LevelSteps i) sn
          (∑ i ∈ Finset.range n, bin238LevelCycles i) (∑ i ∈ Finset.range n, bin238LevelCalls i) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 23 then 703 else 1503)) ∧
        sn.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sn.getReg .x5 = 0#64 ∧
        sn.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sn.getReg .x11 = 96#64 ∧
        sn.getReg .x13 = 0#64 ∧ sn.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * n) ∧
        sn.getReg .x25 = BitVec.ofNat 64 (C_DB + 736) ∧ sn.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        sn.getReg .x27 = mask238Word ∧
        (∀ l ≤ n, ∀ idx < levelSize l, readBuffer sn (C_TD + levelBase l + gapOffset idx) 32 = nodeVal c96 msg salts l idx) ∧
        (∀ l < 24, ∀ q < levelSize l / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0) ∧
        MemPreservedOutside s0 sn (C_TD + levelBase 1) (C_TD + levelBase (n + 1)) := by
    intro n hn; induction n with
    | zero =>
      refine ⟨sa, by simpa only [Finset.sum_range_zero] using DetRun.refl _ _ _,
        by simpa only [show (0 : Nat) < 23 by decide, ite_true] using hsa_pc,
        (hsa_reg .x2 (by decide) (by decide)).trans hx2,
        (hsa_reg .x5 (by decide) (by decide)).trans hx5,
        (hsa_reg .x9 (by decide) (by decide)).trans hx9,
        (hsa_reg .x11 (by decide) (by decide)).trans hx11,
        (hsa_reg .x13 (by decide) (by decide)).trans hx13,
        by simp only [sa, sa0, execInstrBr, MachineState.getReg_setPC,
            getReg_setReg_ne' .x25 .x24 (by decide),
            MachineState.getReg_setReg_eq (by decide : Reg.x24 ≠ .x0), hx2,
            add_signExtend12_ofNat_small _ 0 (by omega), Nat.mul_zero, Nat.add_zero],
        by simp only [sa, sa0, execInstrBr, MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0),
            getReg_setReg_ne' .x24 .x2 (by decide), hx2,
            add_signExtend12_ofNat_small _ 736 (by omega)],
        (hsa_reg .x26 (by decide) (by decide)).trans hx26,
        (hsa_reg .x27 (by decide) (by decide)).trans hx27, ?_, ?_, MemPreservedOutside.of_mem_eq hsa_mem _ _⟩
      · intro l hl idx hidx
        have hl0' : l = 0 := by omega
        subst hl0'; rw [readBuffer_of_mem_eq hsa_mem]; exact hl0 idx hidx
      · intro l hl q hq j hj
        rw [getByte_of_mem_eq hsa_mem]; exact hzero l hl q hq j hj
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hx2n, hx5n, hx9n, hx11n, hx13n, hx24n, hx25n, hx26n, hx27n, hlvln, hzeron, hpresn⟩ := ih (by omega)
      have hpcn' : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 703) := by
        simpa only [show n < 23 by omega, ite_true] using hpcn
      have hdata_n : ∀ off < 736, off % 8 = 0 →
          sn.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)) := by
        intro off hoff hal
        have hlb_n1 := levelBase_bound (n + 1) (by omega)
        rw [hpresn.getMem_eq (by omega) (by omega) (Or.inr (by omega))]
        exact hdata off hoff hal
      have hgap_n : ∀ q < levelSize n / 2, readBuffer sn (C_TD + levelBase n + 96 * q + 64) 32 = 0 := by
        intro q hq
        exact readBuffer_zero_of_bytes sn _ 32 (fun j hj => by
          simpa only [Nat.add_assoc] using hzeron n (by omega) q hq j hj)
      obtain ⟨sn', hstep, hpc', hx2', hx5', hx9', hx11', hx13', hx24', hx25', hx26', hx27', hcur', hpres', hgap'⟩ :=
        commit_bin238_level h768 oracle msg salts n (by omega) sn hpcn' hx2n hx5n hx9n hx11n hx13n hx24n hx25n hx26n hx27n
          hdata_n (hlvln n (le_refl _)) hgap_n
      have hmono_n1 : levelBase 1 ≤ levelBase (n + 1) := levelBase_mono 1 (n + 1) (by omega) (by omega)
      have hmono_n2 : levelBase (n + 1) ≤ levelBase (n + 2) := levelBase_mono (n + 1) (n + 2) (by omega) (by omega)
      refine ⟨sn', by simpa only [Finset.sum_range_succ] using hrunn.trans hstep, hpc',
        hx2', hx5', hx9', hx11', hx13', hx24', hx25', hx26', hx27', ?_, ?_, ?_⟩
      · intro l hl idx hidx
        by_cases htop : l = n + 1
        · subst htop; exact hcur' idx hidx
        · have hlb_l := levelBase_bound l (by omega)
          have hgo := gapOffset_lt_levelBytes l idx (by omega) hidx
          have hstep_l : levelBase (l + 1) = levelBase l + levelBytes l := rfl
          have hmono_l : levelBase (l + 1) ≤ levelBase (n + 1) := levelBase_mono (l + 1) (n + 1) (by omega) (by omega)
          rw [hpres'.readBuffer_eq (by omega) (Or.inl (by omega))]
          exact hlvln l (by omega) idx hidx
      · intro l hl q hq j hj
        by_cases heq : l = n + 1
        · subst heq; exact (hgap' q hq j hj).trans (hzeron (n + 1) hl q hq j hj)
        · have hbytes_l := levelBytes_eq_gap l hl
          have hlb_l := levelBase_bound l (by omega)
          have hstep_l : levelBase (l + 1) = levelBase l + levelBytes l := rfl
          have hout : C_TD + levelBase l + 96 * q + 64 + j < C_TD + levelBase (n + 1) ∨
              C_TD + levelBase (n + 2) ≤ C_TD + levelBase l + 96 * q + 64 + j := by
            by_cases hlt : l < n + 1
            · have hm := levelBase_mono (l + 1) (n + 1) (by omega) (by omega); exact Or.inl (by omega)
            · have hm := levelBase_mono (n + 2) l (by omega) (by omega); exact Or.inr (by omega)
          exact (hpres' _ (by omega) hout).trans (hzeron l hl q hq j hj)
      · have hlb_eq : levelBase (n + 1 + 1) = levelBase (n + 2) := rfl
        exact (hpresn.mono (le_refl _) (by omega)).trans (hpres'.mono (by omega) (by rw [hlb_eq]))
  obtain ⟨s1, hrun, hpc1, _, hx5_1, hx9_1, hx11_1, hx13_1, _, _, hx26_1, _, hlvl1, hzero1, hpres1⟩ := hind 23 (le_refl _)
  have htot := hsetup.trans hrun
  rw [phase2_steps_sum, phase2_cycles_sum, Nat.zero_add, phase2_calls_sum] at htot
  exact ⟨s1, htot, by simpa only [Nat.lt_irrefl, ite_false] using hpc1,
    hx5_1, hx9_1, hx11_1, hx13_1, hx26_1, hlvl1, hzero1, hpres1⟩

end CommitGolfCandidate
