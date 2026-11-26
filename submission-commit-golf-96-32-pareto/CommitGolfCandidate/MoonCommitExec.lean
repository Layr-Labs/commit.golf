import CommitGolfCandidate.MoonCommitLeaf

/-! Exact RV64IM execution proof for Phase 2 of the v4 `commit` image:
L0 -> L1 3-ary unmasked bulk (exact divisor: 683 × 4094 pairs, ZERO tail), final triplet,
and promoted leaf 16,777,215 (words 114738..139326). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem pc_jal_139315 :
    BitVec.ofNat 64 (0x1000 + 4 * 139315) + signExtend21 (1998892#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 114750) := by decide

/-- One 2-call pair of L0 -> L1 3-ary compressions (6 steps, 20 cycles, 2 calls).
Works identically for `l1_bulk` (`basePc = 3386 + 6 * p`) and `l1_tail` (`basePc = 4161`). -/
theorem commit_l1_pair (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (basePc q : Nat) (hq : 2 * q + 1 < FULL_TRIPLETS)
    (s : MachineState)
    (hfetch : ∀ j < 6, ∀ st : MachineState,
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + j)) →
      fetch (submission.image .commit) st = some (l1PairInstr j))
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (2 * q) - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q - 64))
    (hl0 : ∀ j < 6, readBuffer s (C_TD + 32 * (6 * q + j)) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 0 (6 * q + j)) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 6 s' 20 2 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 6)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (2 * q + 1)) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 32) ∧
      readBuffer s' (C_TD + levelBase 1 + 96 * q) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 (2 * q) ∧
      readBuffer s' (C_TD + levelBase 1 + 96 * q + 32) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 (2 * q + 1) ∧
      MemPreservedOutside s s' (C_TD + levelBase 1 + 96 * q) (C_TD + levelBase 1 + 96 * q + 64) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hft := full_triplets_eq
  have hlb1 : levelBase 1 = 536870912 := by decide
  let s1 := execInstrBr s (.ADDI .x10 .x10 (96#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (64#12))
  let d0 := nodeVal c96 msg salts 1 (2 * q)
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q)) d0
  let s4 := execInstrBr s3 (.ADDI .x10 .x10 (96#12))
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 (32#12))
  let d1 := nodeVal c96 msg salts 1 (2 * q + 1)
  let s6 := writeBits s5 (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 32)) d1
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) := pc_step_idx s basePc hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) := pc_step_idx s1 (basePc + 1) hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) := pc_step_idx s2 (basePc + 2) hs2_pc
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 4)) := pc_step_idx s3 (basePc + 3) hs3_pc
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 5)) := pc_step_idx s4 (basePc + 4) hs4_pc
  have hs6_pc : s6.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 6)) := pc_step_idx s5 (basePc + 5) hs5_pc
  have hs2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s2.getReg r = s.getReg r := fun r h10 h12 => by
    have h2 : s2.getReg r = s1.getReg r := by
      simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
    have h1 : s1.getReg r = s.getReg r := by
      simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm h10)]
    exact h2.trans h1
  have hs5_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s5.getReg r = s.getReg r := fun r h10 h12 => by
    have h5 : s5.getReg r = s4.getReg r := by
      simp only [s5, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
    have h4 : s4.getReg r = s3.getReg r := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm h10)]
    exact ((h5.trans h4).trans (writeBits_register s2 _ d0 r)).trans (hs2_reg_other r h10 h12)
  have hs6_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s6.getReg r = s.getReg r := fun r h10 h12 =>
    (writeBits_register s5 _ d1 r).trans (hs5_reg_other r h10 h12)
  have hm2 : s2.mem = s.mem := (mem_exec_ADDI s1 .x12 .x12 (64#12)).trans (mem_exec_ADDI s .x10 .x10 (96#12))
  have hm5 : s5.mem = s3.mem := (mem_exec_ADDI s4 .x12 .x12 (32#12)).trans (mem_exec_ADDI s3 .x10 .x10 (96#12))
  have hs1_a0 : s1.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (2 * q)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD]; omega)
  have hs2_a0 : s2.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (2 * q)) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs1_a0]
  have hs2_a2 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q) := by
    have h1x12 : s1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q - 64) := by
      simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hx12]
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h1x12,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD, hlb1]; omega)
  have hs2_in : readBuffer s2 (C_TD + 96 * (2 * q)) 96 =
      ternaryInput (nodeVal c96 msg salts 0 (6 * q))
        (nodeVal c96 msg salts 0 (6 * q + 1)) (nodeVal c96 msg salts 0 (6 * q + 2)) := by
    rw [readBuffer_of_mem_eq hm2, readBuffer_ternary]
    have h0 := hl0 0 (by omega); have h1 := hl0 1 (by omega); have h2 := hl0 2 (by omega)
    simp only [show C_TD + 96 * (2 * q) = C_TD + 32 * (6 * q + 0) by omega,
      show C_TD + 32 * (6 * q + 0) + 32 = C_TD + 32 * (6 * q + 1) by omega,
      show C_TD + 32 * (6 * q + 0) + 64 = C_TD + 32 * (6 * q + 2) by omega]
    rw [h0, h1, h2]
    simp only [Nat.add_zero]; rfl
  have hd0_eq : oracle.compression ((readBuffer s2 (C_TD + 96 * (2 * q)) 96).cast h768.symm) = d0 := by
    rw [hs2_in]; unfold d0 nodeVal nodeValFromLeaves
    simp only [show 2 * q < FULL_TRIPLETS by omega, ite_true, show 3 * (2 * q) = 6 * q by omega]
    rfl
  have hst0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (hfetch 0 (by omega) s (by simpa using hpc)) rfl
  have hst1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (hfetch 1 (by omega) s1 hs1_pc) rfl
  have hst2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s2)
      (hfetch 2 (by omega) s2 hs2_pc)
      (by rw [hs2_reg_other .x5 (by decide) (by decide)]; exact hx5)
      (by rw [hs2_reg_other .x11 (by decide) (by decide)]; exact hx11)
      (by rw [hs2_reg_other .x13 (by decide) (by decide)]; exact hx13)
      (C_TD + 96 * (2 * q)) (C_TD + levelBase 1 + 96 * q) hs2_a0 hs2_a2
      (by omega) (by omega) (by omega) (by omega) d0 hd0_eq
  have hs3_pres : MemPreservedOutside s s3 (C_TD + levelBase 1 + 96 * q) (C_TD + levelBase 1 + 96 * q + 32) :=
    (MemPreservedOutside.of_mem_eq hm2 _ _).trans
      (memPreserved_writeBits s2 (C_TD + levelBase 1 + 96 * q) d0 (by omega))
  have hs3_a0 : s3.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (2 * q)) :=
    (writeBits_register s2 _ d0 .x10).trans hs2_a0
  have hs3_a2 : s3.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q) :=
    (writeBits_register s2 _ d0 .x12).trans hs2_a2
  have hs4_a0 : s4.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (2 * q + 1)) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs3_a0,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD]; omega)
  have hs5_a0 : s5.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (2 * q + 1)) := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs4_a0]
  have hs5_a2 : s5.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 32) := by
    have h4x12 : s4.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hs3_a2]
    simp only [s5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h4x12,
      add_signExtend12_ofNat_small _ 32 (by omega)]
  have hs5_in : readBuffer s5 (C_TD + 96 * (2 * q + 1)) 96 =
      ternaryInput (nodeVal c96 msg salts 0 (6 * q + 3))
        (nodeVal c96 msg salts 0 (6 * q + 4)) (nodeVal c96 msg salts 0 (6 * q + 5)) := by
    rw [readBuffer_of_mem_eq hm5, hs3_pres.readBuffer_eq (by omega) (by omega), readBuffer_ternary]
    have h3 := hl0 3 (by omega); have h4 := hl0 4 (by omega); have h5 := hl0 5 (by omega)
    simp only [show C_TD + 96 * (2 * q + 1) = C_TD + 32 * (6 * q + 3) by omega,
      show C_TD + 32 * (6 * q + 3) + 32 = C_TD + 32 * (6 * q + 4) by omega,
      show C_TD + 32 * (6 * q + 3) + 64 = C_TD + 32 * (6 * q + 5) by omega]
    rw [h3, h4, h5]
  have hd1_eq : oracle.compression ((readBuffer s5 (C_TD + 96 * (2 * q + 1)) 96).cast h768.symm) = d1 := by
    rw [hs5_in]; unfold d1 nodeVal nodeValFromLeaves
    simp only [show 2 * q + 1 < FULL_TRIPLETS by omega, ite_true, show 3 * (2 * q + 1) = 6 * q + 3 by omega]
    rfl
  have hst3 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (hfetch 3 (by omega) s3 hs3_pc) rfl
  have hst4 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (hfetch 4 (by omega) s4 hs4_pc) rfl
  have hst5 : DetRun oracle (submission.image .commit) s5 1 s6 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s5)
      (hfetch 5 (by omega) s5 hs5_pc)
      (by rw [hs5_reg_other .x5 (by decide) (by decide)]; exact hx5)
      (by rw [hs5_reg_other .x11 (by decide) (by decide)]; exact hx11)
      (by rw [hs5_reg_other .x13 (by decide) (by decide)]; exact hx13)
      (C_TD + 96 * (2 * q + 1)) (C_TD + levelBase 1 + 96 * q + 32) hs5_a0 hs5_a2
      (by omega) (by omega) (by omega) (by omega) d1 hd1_eq
  refine ⟨s6, by simpa using ((((hst0.trans hst1).trans hst2).trans hst3).trans hst4).trans hst5,
    hs6_pc, hs6_reg_other,
    (writeBits_register s5 _ d1 .x10).trans hs5_a0,
    (writeBits_register s5 _ d1 .x12).trans hs5_a2, ?_, ?_, ?_⟩
  · have hp6 := memPreserved_writeBits s5 (C_TD + levelBase 1 + 96 * q + 32) d1 (by omega)
    rw [hp6.readBuffer_eq (by omega) (by omega), readBuffer_of_mem_eq hm5]
    exact writeBits_readBuffer_digest s2 _ d0
  · exact writeBits_readBuffer_digest s5 _ d1
  · exact ((hs3_pres.mono (le_refl _) (by omega)).trans
      (MemPreservedOutside.of_mem_eq hm5 _ _)).trans
      ((memPreserved_writeBits s5 (C_TD + levelBase 1 + 96 * q + 32) d1 (by omega)).mono (by omega) (le_refl _))

private def phase2SetupInstrs : List Instr :=
  [.ADDI .x10 .x9 (4000#12), .ADDI .x6 .x0 (128#12), .SLLI .x6 .x6 (11#6), .SLLI .x6 .x6 (11#6),
   .ADD .x12 .x9 .x6, .ADDI .x12 .x12 (4032#12),
   .ADDI .x6 .x0 (127#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (2047#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (1824#12), .ADD .x19 .x9 .x6]

private theorem commit_phase2_setup (oracle : Oracle) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 114738))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let sa := phase2SetupInstrs.foldl execInstrBr s0
    DetRun oracle (submission.image .commit) s0 12 sa 12 0 ∧
    sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 114750) ∧
    sa.mem = s0.mem ∧
    sa.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sa.getReg .x5 = 0#64 ∧
    sa.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sa.getReg .x10 = BitVec.ofNat 64 (C_TD - 96) ∧
    sa.getReg .x11 = 96#64 ∧ sa.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 - 64) ∧
    sa.getReg .x13 = 0#64 ∧ sa.getReg .x19 = BitVec.ofNat 64 (C_TD + 5592404 * 96 - 96) ∧
    sa.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ phase2SetupInstrs, isPureAlu ins = true := by decide
  have hlb1 : levelBase 1 = 536870912 := by decide
  refine ⟨?_, ?_, foldl_pureAlu_mem phase2SetupInstrs s0 hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply exec_alu_list phase2SetupInstrs s0
    intro i hi
    have hi' : i < 12 := hi
    have hpc_i : ((phase2SetupInstrs.take i).foldl execInstrBr s0).pc =
        BitVec.ofNat 64 (0x1000 + 4 * (114738 + i)) := by
      have h := foldl_pureAlu_pc (phase2SetupInstrs.take i) s0 (0x1000 + 4 * 114738)
        (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
      rw [List.length_take_of_le (by omega)] at h
      rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
    interval_cases i <;>
      exact ⟨commit_fetch_commitMid1CInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩
  · exact (foldl_pureAlu_pc phase2SetupInstrs s0 (0x1000 + 4 * 114738) hall hpc).trans (by decide)
  all_goals (
    simp only [phase2SetupInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx2, hx5, hx9, hx11, hx13, hx26, hlb1]
    try decide)

/-- One 4094-pair bulk chunk of Phase 2 (`words 114750..139315`): `24,566` (or `24,565` on last) steps,
`81,882` (or `81,881` on last) cycles, `8,188` calls. -/
private theorem commit_phase2_bulk_chunk (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (c : Nat) (hc : c < 683) (sc : MachineState)
    (hpc_c : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 114750))
    (hx5c : sc.getReg .x5 = 0#64) (hx11c : sc.getReg .x11 = 96#64) (hx13c : sc.getReg .x13 = 0#64)
    (hx10c : sc.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (8188 * c) - 96))
    (hx12c : sc.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (4094 * c) - 64))
    (hx19c : sc.getReg .x19 = BitVec.ofNat 64 (C_TD + 5592404 * 96 - 96))
    (hl0c : ∀ idx < LENGTH, readBuffer sc (C_TD + 32 * idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 0 idx) :
    let lcost : Nat := if c + 1 < 683 then 2 else 1
    ∃ sc',
      DetRun oracle (submission.image .commit) sc (24564 + lcost) sc' (81880 + lcost) 8188 ∧
      sc'.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < 683 then 114750 else 139316)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sc'.getReg r = sc.getReg r) ∧
      sc'.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (8188 * (c + 1)) - 96) ∧
      sc'.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (4094 * (c + 1)) - 64) ∧
      (∀ idx, 8188 * c ≤ idx → idx < 8188 * (c + 1) →
        readBuffer sc' (C_TD + levelBase 1 + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 idx) ∧
      (∀ q < (levelSize 1 + 1) / 2, ∀ j < 32,
        sc'.getByte (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 64 + j)) =
        sc.getByte (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 64 + j))) ∧
      MemPreservedOutside sc sc' (C_TD + levelBase 1 + 96 * (4094 * c))
        (C_TD + levelBase 1 + 96 * (4094 * (c + 1))) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hlb1 : levelBase 1 = 536870912 := by decide
  have hft := full_triplets_eq
  have hls1 := levelSize_1
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hpairs : ∀ m ≤ 4094,
      ∃ sm,
        DetRun oracle (submission.image .commit) sc (6 * m) sm (20 * m) (2 * m) ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (114750 + 6 * m)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sm.getReg r = sc.getReg r) ∧
        sm.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (2 * (4094 * c + m)) - 96) ∧
        sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (4094 * c + m) - 64) ∧
        (∀ idx, 8188 * c ≤ idx → idx < 8188 * c + 2 * m →
          readBuffer sm (C_TD + levelBase 1 + gapOffset idx) 32 = nodeVal c96 msg salts 1 idx) ∧
        (∀ q < (levelSize 1 + 1) / 2, ∀ j < 32,
          sm.getByte (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 64 + j)) =
          sc.getByte (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 64 + j))) ∧
        MemPreservedOutside sc sm (C_TD + levelBase 1 + 96 * (4094 * c)) (C_TD + levelBase 1 + 96 * (4094 * c + m)) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc_c, fun _ _ _ => rfl,
        by rw [hx10c]; exact congrArg (BitVec.ofNat 64) (by omega),
        by simpa using hx12c, fun _ h1 h2 => by omega, fun _ _ _ _ => rfl, MemPreservedOutside.refl _ _ _⟩
    | succ m ih =>
      obtain ⟨sm, hrunm, hpcm, hregm, hx10m, hx12m, hdigm, hgapm, hpresm⟩ := ih (by omega)
      obtain ⟨sn, hrun1, hpcn, hregn, hx10n, hx12n, hd0, hd1, hpres1⟩ := commit_l1_pair h768 oracle msg salts
        (114750 + 6 * m) (4094 * c + m) (by omega) sm
        (fun j hj st hst => commit_fetch_l1_bulk st m j (by omega) hj hst)
        hpcm (by rw [hregm .x5 (by decide) (by decide)]; exact hx5c)
        (by rw [hregm .x11 (by decide) (by decide)]; exact hx11c)
        (by rw [hregm .x13 (by decide) (by decide)]; exact hx13c)
        hx10m hx12m
        (fun j hj => by
          rw [hpresm.readBuffer_eq (by omega) (by omega)]
          exact hl0c (6 * (4094 * c + m) + j) (by omega))
      refine ⟨sn, by simpa [Nat.mul_succ] using hrunm.trans hrun1,
        by simpa [show 114750 + 6 * m + 6 = 114750 + 6 * (m + 1) by omega] using hpcn,
        fun r h10 h12 => (hregn r h10 h12).trans (hregm r h10 h12),
        by simpa [show C_TD + 96 * (2 * (4094 * c + m) + 1) = C_TD + 96 * (2 * (4094 * c + (m + 1))) - 96 by omega] using hx10n,
        by simpa [show C_TD + levelBase 1 + 96 * (4094 * c + m) + 32 = C_TD + levelBase 1 + 96 * (4094 * c + (m + 1)) - 64 by omega] using hx12n,
        ?_, ?_, ?_⟩
      · intro idx hlo hhi
        by_cases hold : idx < 8188 * c + 2 * m
        · rw [← hdigm idx hlo hold]
          have hgo : gapOffset idx + 32 ≤ 96 * (4094 * c + m) := by unfold gapOffset; omega
          exact hpres1.readBuffer_eq (by omega) (by omega)
        · by_cases hev : idx = 2 * (4094 * c + m)
          · subst hev; simpa [gapOffset_even] using hd0
          · have hodd : idx = 2 * (4094 * c + m) + 1 := by omega
            subst hodd; simpa [gapOffset_odd, Nat.add_assoc] using hd1
      · intro q hq j hj
        have hsep : C_TD + levelBase 1 + 96 * q + 64 + j < C_TD + levelBase 1 + 96 * (4094 * c + m) ∨
            C_TD + levelBase 1 + 96 * (4094 * c + m) + 64 ≤ C_TD + levelBase 1 + 96 * q + 64 + j := by omega
        exact (hpres1 (C_TD + levelBase 1 + 96 * q + 64 + j) (by omega) hsep).trans (hgapm q hq j hj)
      · exact (hpresm.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (by omega))
  obtain ⟨sm, hrunB, hpcB, hregB, hx10_B, hx12_B, hdigB, hgapB, hpresB⟩ := hpairs 4094 (le_refl _)
  have hx19m : sm.getReg .x19 = BitVec.ofNat 64 (C_TD + 5592404 * 96 - 96) :=
    (hregB .x19 (by decide) (by decide)).trans hx19c
  let done : Bool := decide (c + 1 = 683)
  have hcmp : (sm.getReg .x10 == sm.getReg .x19) = done := by
    dsimp only [done]
    by_cases heq : c + 1 = 683
    · have hnat : C_TD + 96 * (2 * (4094 * c + 4094)) - 96 = C_TD + 5592404 * 96 - 96 := by
        rw [show 4094 * c + 4094 = 4094 * (c + 1) by omega, heq, show 96 * (2 * (4094 * 683)) = 5592404 * 96 by decide]
      rw [hx10_B, hx19m, hnat, beq_self_eq_true, decide_eq_true heq]
    · rw [hx10_B, hx19m, decide_eq_false heq, beq_eq_false_iff_ne]
      exact bv64_ne_of_nat_ne (by rw [hC_TD]; omega) (by rw [hC_TD]; omega) (by rw [hC_TD]; omega)
  obtain ⟨hlatch, hpc_end, hmem_l, hreg_l⟩ :=
    c_beq_jal_latch oracle sm .x10 .x19 139314 114750 (1998892#21) done hpcB hcmp
      (commit_fetch_commitMid2Instr sm 139314 (by omega) (by omega) hpcB)
      (fun st hst => commit_fetch_commitMid2Instr st 139315 (by omega) (by omega) hst)
      pc_jal_139315
  have hcost_eq : (if done = true then 1 else 2) = (if c + 1 < 683 then 2 else 1) := by
    by_cases h : c + 1 < 683
    · simp only [done, decide_eq_false (by omega : c + 1 ≠ 683), Bool.false_eq_true, ite_false, h, ite_true]
    · simp only [done, decide_eq_true (by omega : c + 1 = 683), ite_true, h, ite_false]
  have hpc_norm : (if done = true then 139314 + 2 else 114750) = (if c + 1 < 683 then 114750 else 139316) := by
    by_cases h : c + 1 < 683
    · simp only [done, decide_eq_false (by omega : c + 1 ≠ 683), Bool.false_eq_true, ite_false, h, ite_true]
    · simp only [done, decide_eq_true (by omega : c + 1 = 683), ite_true, h, ite_false]
  refine ⟨_, by simpa only [hcost_eq, Nat.add_zero] using hrunB.trans hlatch,
    by rw [hpc_end, hpc_norm],
    fun r h10 h12 => (hreg_l r).trans (hregB r h10 h12),
    by rw [hreg_l .x10, hx10_B]; exact congrArg (BitVec.ofNat 64) (by omega),
    by rw [hreg_l .x12, hx12_B]; exact congrArg (BitVec.ofNat 64) (by omega),
    fun idx hlo hhi => (readBuffer_of_mem_eq hmem_l _ _).trans (hdigB idx hlo (by omega)),
    fun q hq j hj => by rw [getByte_of_mem_eq hmem_l]; exact hgapB q hq j hj,
    (hpresB.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmem_l _ _)⟩

/-- Full Phase 2 (L0 -> L1 3-ary exact-divisor bulk + final triplet + promoted leaf 16,777,215):
words `114738..139326`, exact `16,778,600` steps, `55,925,435` cycles, `5,592,405` calls. -/
theorem commit_phase2 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 114738))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hl0 : ∀ idx < LENGTH, readBuffer s0 (C_TD + 32 * idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 0 idx) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 16778600 s1 55925435 5592405 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 139327) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ idx < levelSize 1, readBuffer s1 (C_TD + levelBase 1 + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 idx) ∧
      (∀ q < (levelSize 1 + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 1) (C_TD + levelBase 2) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hlb1 : levelBase 1 = 536870912 := by decide
  have hlb2 : levelBase 2 = 805306400 := by decide
  have hft := full_triplets_eq
  -- Setup 114738..114749
  let sa := phase2SetupInstrs.foldl execInstrBr s0
  obtain ⟨hsetup, hsa_pc, hsa_mem, hsa_x2, hsa_x5, hsa_x9, hsa_x10, hsa_x11, hsa_x12,
    hsa_x13, hsa_x19, hsa_x26⟩ := commit_phase2_setup oracle s0 hpc hx2 hx5 hx9 hx11 hx13 hx26
  -- Bulk loop: 683 chunks × 4094 pairs = 2,796,202 pairs (5,592,404 triplets, ZERO tail!)
  have hbulk : ∀ n ≤ 683,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa
          (if n < 683 then 24566 * n else 16778577) sn
          (if n < 683 then 81882 * n else 55925405) (8188 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 683 then 114750 else 139316)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sn.getReg r = sa.getReg r) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (8188 * n) - 96) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (4094 * n) - 64) ∧
        (∀ idx < 8188 * n, readBuffer sn (C_TD + levelBase 1 + gapOffset idx) 32 = nodeVal c96 msg salts 1 idx) ∧
        (∀ q < (levelSize 1 + 1) / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 64 + j)) =
          sa.getByte (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 64 + j))) ∧
        MemPreservedOutside sa sn (C_TD + levelBase 1) (C_TD + levelBase 1 + 96 * (4094 * n)) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨sa, by simpa using DetRun.refl oracle (submission.image .commit) sa,
        by simpa using hsa_pc, fun _ _ _ => rfl,
        by simpa using hsa_x10, by simpa using hsa_x12,
        fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ _ => rfl, MemPreservedOutside.refl _ _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hregn, hx10n, hx12n, hdign, hgapn, hpresn⟩ := ih (by omega)
      have hlt_n : n < 683 := by omega
      simp only [hlt_n, ite_true] at hrunn
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 114750) := by
        simpa only [hlt_n, ite_true] using hpcn
      obtain ⟨sm, hrun1, hpcm, hregm, hx10m, hx12m, hdig1, hgap1, hpres1⟩ :=
        commit_phase2_bulk_chunk h768 oracle msg salts n (by omega) sn hpc_in
          (by rw [hregn .x5 (by decide) (by decide)]; exact hsa_x5)
          (by rw [hregn .x11 (by decide) (by decide)]; exact hsa_x11)
          (by rw [hregn .x13 (by decide) (by decide)]; exact hsa_x13)
          hx10n hx12n
          (by rw [hregn .x19 (by decide) (by decide)]; exact hsa_x19)
          (fun idx hidx => by
            rw [hpresn.readBuffer_eq (by omega) (by omega), readBuffer_of_mem_eq hsa_mem]
            exact hl0 idx hidx)
      have hrun_n1 : DetRun oracle (submission.image .commit) sa
          (if n + 1 < 683 then 24566 * (n + 1) else 16778577) sm
          (if n + 1 < 683 then 81882 * (n + 1) else 55925405) (8188 * (n + 1)) := by
        have h := hrunn.trans hrun1
        have hs : 24566 * n + (24564 + if n + 1 < 683 then 2 else 1) =
            if n + 1 < 683 then 24566 * (n + 1) else 16778577 := by split <;> omega
        have hc : 81882 * n + (81880 + if n + 1 < 683 then 2 else 1) =
            if n + 1 < 683 then 81882 * (n + 1) else 55925405 := by split <;> omega
        rw [hs, hc, show 8188 * n + 8188 = 8188 * (n + 1) by omega] at h
        exact h
      refine ⟨sm, hrun_n1, hpcm,
        fun r h10 h12 => (hregm r h10 h12).trans (hregn r h10 h12), hx10m, hx12m, ?_, ?_, ?_⟩
      · intro idx hidx
        by_cases hlt : idx < 8188 * n
        · rw [← hdign idx hlt]
          have hgo : gapOffset idx + 32 ≤ 96 * (4094 * n) := by unfold gapOffset; omega
          exact hpres1.readBuffer_eq (by omega) (by omega)
        · exact hdig1 idx (by omega) hidx
      · intro q hq j hj; exact (hgap1 q hq j hj).trans (hgapn q hq j hj)
      · exact (hpresn.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (le_refl _))
  obtain ⟨sb, hrun_bulk, hpc_b, hreg_b, hx10_b, hx12_b, hdig_b, hgap_b, hpres_b⟩ := hbulk 683 (le_refl _)
  simp only [Nat.lt_irrefl, ite_false] at hrun_bulk
  have hpc_b' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 139316) := by
    simpa only [Nat.lt_irrefl, ite_false] using hpc_b
  -- Final even call (139316..139318, triplet 5,592,404 -> L1[5,592,404]): 3 steps, 10 cyc, 1 call
  let sf1 := execInstrBr sb (.ADDI .x10 .x10 (96#12))
  let sf2 := execInstrBr sf1 (.ADDI .x12 .x12 (64#12))
  let df := nodeVal c96 msg salts 1 5592404
  let sf3 := writeBits sf2 (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * 2796202)) df
  have hsf1_pc : sf1.pc = BitVec.ofNat 64 (0x1000 + 4 * 139317) := pc_step_idx sb 139316 hpc_b'
  have hsf2_pc : sf2.pc = BitVec.ofNat 64 (0x1000 + 4 * 139318) := pc_step_idx sf1 139317 hsf1_pc
  have hsf3_pc : sf3.pc = BitVec.ofNat 64 (0x1000 + 4 * 139319) := pc_step_idx sf2 139318 hsf2_pc
  have hsf2_mem : sf2.mem = sb.mem :=
    (mem_exec_ADDI sf1 .x12 .x12 (64#12)).trans (mem_exec_ADDI sb .x10 .x10 (96#12))
  have hsf2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sf2.getReg r = sb.getReg r := fun r h10 h12 => by
    have h2 : sf2.getReg r = sf1.getReg r := by
      simp only [sf2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
    have h1 : sf1.getReg r = sb.getReg r := by
      simp only [sf1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm h10)]
    exact h2.trans h1
  have hsf3_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sf3.getReg r = sb.getReg r := fun r h10 h12 =>
    (writeBits_register sf2 _ df r).trans (hsf2_reg_other r h10 h12)
  have hsf1_a0 : sf1.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * 5592404) := by
    simp only [sf1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10_b,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD])
  have hsf2_a0 : sf2.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * 5592404) := by
    simp only [sf2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hsf1_a0]
  have hsf2_a2 : sf2.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * 2796202) := by
    have h1x12 : sf1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * 2796202 - 64) := by
      simp only [sf1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hx12_b]
    simp only [sf2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h1x12,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD, hlb1])
  have hsf2_in : readBuffer sf2 (C_TD + 96 * 5592404) 96 =
      ternaryInput (nodeVal c96 msg salts 0 16777212)
        (nodeVal c96 msg salts 0 16777213) (nodeVal c96 msg salts 0 16777214) := by
    rw [readBuffer_of_mem_eq hsf2_mem, hpres_b.readBuffer_eq (by omega) (by omega),
      readBuffer_of_mem_eq hsa_mem, readBuffer_ternary]
    have h0 := hl0 16777212 (by omega)
    have h1 := hl0 16777213 (by omega)
    have h2 := hl0 16777214 (by omega)
    simp only [show C_TD + 96 * 5592404 = C_TD + 32 * 16777212 by omega,
      show C_TD + 32 * 16777212 + 32 = C_TD + 32 * 16777213 by omega,
      show C_TD + 32 * 16777212 + 64 = C_TD + 32 * 16777214 by omega]
    rw [h0, h1, h2]
  have hdf_eq : oracle.compression ((readBuffer sf2 (C_TD + 96 * 5592404) 96).cast h768.symm) = df := by
    rw [hsf2_in]; unfold df nodeVal nodeValFromLeaves
    simp only [show 5592404 < FULL_TRIPLETS by omega, ite_true]; rfl
  have hfinal_call : DetRun oracle (submission.image .commit) sb 3 sf3 10 1 := by
    have hf1 : DetRun oracle (submission.image .commit) sb 1 sf1 1 0 :=
      DetRun.step1 (commit_fetch_commitMid2Instr sb 139316 (by omega) (by omega) hpc_b') rfl
    have hf2 : DetRun oracle (submission.image .commit) sf1 1 sf2 1 0 :=
      DetRun.step1 (commit_fetch_commitMid2Instr sf1 139317 (by omega) (by omega) hsf1_pc) rfl
    have hf3 : DetRun oracle (submission.image .commit) sf2 1 sf3 8 1 :=
      DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := sf2)
        (commit_fetch_commitMid2Instr sf2 139318 (by omega) (by omega) hsf2_pc)
        (by rw [hsf2_reg_other .x5 (by decide) (by decide), hreg_b .x5 (by decide) (by decide)]; exact hsa_x5)
        (by rw [hsf2_reg_other .x11 (by decide) (by decide), hreg_b .x11 (by decide) (by decide)]; exact hsa_x11)
        (by rw [hsf2_reg_other .x13 (by decide) (by decide), hreg_b .x13 (by decide) (by decide)]; exact hsa_x13)
        (C_TD + 96 * 5592404) (C_TD + levelBase 1 + 96 * 2796202) hsf2_a0 hsf2_a2
        (by rw [hC_TD]) (by rw [hC_TD, hlb1])
        (by rw [hC_TD, hMB]; omega) (by rw [hC_TD, hMB, hlb1]; omega) df hdf_eq
    exact (hf1.trans hf2).trans hf3
  -- Promoted leaf 16,777,215 copy (words 139319..139326: 4 ld/sd pairs = 8 steps, 8 cyc, 0 calls)
  have hsf3_a0 : sf3.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * 5592404) :=
    (writeBits_register sf2 _ df .x10).trans hsf2_a0
  have hsf3_a2 : sf3.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * 2796202) :=
    (writeBits_register sf2 _ df .x12).trans hsf2_a2
  obtain ⟨sfin, hprom_run, hsfin_pc, hsfin_reg, hsfin_dig, hprom_pres⟩ :=
    commit_copy32 oracle sf3 139319 .x10 .x12
      (C_TD + 96 * 5592404) (C_TD + levelBase 1 + 96 * 2796202) 96 32
      (by decide) (by decide) (by decide) (by decide)
      (by rw [hC_TD]) (by rw [hC_TD, hlb1])
      (by rw [hC_TD, hMB]; omega) (by rw [hC_TD, hMB, hlb1]; omega)
      (by rw [hC_TD, hlb1]; omega) hsf3_pc hsf3_a0 hsf3_a2
      (fun k hk st => by
        constructor
        · intro hpc'
          have h := commit_fetch_commitMid2Instr st (139319 + 2 * k) (by omega) (by omega) hpc'
          interval_cases k <;> simpa [commitMid2Instr] using h
        · intro hpc'
          have h := commit_fetch_commitMid2Instr st (139319 + 2 * k + 1) (by omega) (by omega) hpc'
          interval_cases k <;> simpa [commitMid2Instr] using h)
  have hsf3_pres_sb : MemPreservedOutside sb sf3 (C_TD + levelBase 1 + 96 * 2796202) (C_TD + levelBase 1 + 96 * 2796202 + 32) :=
    (MemPreservedOutside.of_mem_eq hsf2_mem _ _).trans
      (memPreserved_writeBits sf2 _ df (by omega))
  have hprom_dig : readBuffer sfin (C_TD + levelBase 1 + 96 * 2796202 + 32) 32 = nodeVal c96 msg salts 1 5592405 := by
    have hsrc : readBuffer sf3 (C_TD + 32 * 16777215) 32 = nodeVal c96 msg salts 1 5592405 := by
      rw [hsf3_pres_sb.readBuffer_eq (by omega) (by omega),
        hpres_b.readBuffer_eq (by omega) (by omega),
        readBuffer_of_mem_eq hsa_mem,
        hl0 16777215 (by omega)]
      unfold nodeVal nodeValFromLeaves
      simp only [hft, show ¬ (5592405 < 5592405) by omega, ite_false, ite_true]
      rfl
    rw [hsfin_dig, show C_TD + 96 * 5592404 + 96 = C_TD + 32 * 16777215 by omega]
    exact hsrc
  -- Compose all of Phase 2
  have hphase2_run : DetRun oracle (submission.image .commit) s0 16778600 sfin 55925435 5592405 := by
    have h := (hsetup.trans hrun_bulk).trans (hfinal_call.trans hprom_run)
    simpa using h
  have hpres_all : MemPreservedOutside s0 sfin (C_TD + levelBase 1) (C_TD + levelBase 2) := by
    have h0a := MemPreservedOutside.of_mem_eq hsa_mem (C_TD + levelBase 1) (C_TD + levelBase 2)
    have hab : MemPreservedOutside _ _ (C_TD + levelBase 1) (C_TD + levelBase 2) :=
      hpres_b.mono (le_refl _) (by rw [hC_TD, hlb1, hlb2]; omega)
    have hbf : MemPreservedOutside _ _ (C_TD + levelBase 1) (C_TD + levelBase 2) :=
      hsf3_pres_sb.mono (by rw [hC_TD, hlb1]; omega) (by rw [hC_TD, hlb1, hlb2]; omega)
    have hff : MemPreservedOutside _ _ (C_TD + levelBase 1) (C_TD + levelBase 2) :=
      hprom_pres.mono (by rw [hC_TD, hlb1]; omega) (by rw [hC_TD, hlb1, hlb2]; omega)
    exact ((h0a.trans hab).trans hbf).trans hff
  refine ⟨sfin, hphase2_run, hsfin_pc,
    by rw [hsfin_reg .x2 (by decide), hsf3_reg_other .x2 (by decide) (by decide),
        hreg_b .x2 (by decide) (by decide)]; exact hsa_x2,
    by rw [hsfin_reg .x5 (by decide), hsf3_reg_other .x5 (by decide) (by decide),
        hreg_b .x5 (by decide) (by decide)]; exact hsa_x5,
    by rw [hsfin_reg .x9 (by decide), hsf3_reg_other .x9 (by decide) (by decide),
        hreg_b .x9 (by decide) (by decide)]; exact hsa_x9,
    by rw [hsfin_reg .x11 (by decide), hsf3_reg_other .x11 (by decide) (by decide),
        hreg_b .x11 (by decide) (by decide)]; exact hsa_x11,
    by rw [hsfin_reg .x13 (by decide), hsf3_reg_other .x13 (by decide) (by decide),
        hreg_b .x13 (by decide) (by decide)]; exact hsa_x13,
    by rw [hsfin_reg .x26 (by decide), hsf3_reg_other .x26 (by decide) (by decide),
        hreg_b .x26 (by decide) (by decide)]; exact hsa_x26,
    ?_, ?_, hpres_all⟩
  · intro idx hidx
    rw [levelSize_1] at hidx
    by_cases h1 : idx < 5592404
    · have hgo : gapOffset idx + 32 ≤ 96 * 2796202 := by unfold gapOffset; omega
      rw [hprom_pres.readBuffer_eq (by omega) (by omega),
        hsf3_pres_sb.readBuffer_eq (by omega) (by omega)]
      exact hdig_b idx h1
    · by_cases h3 : idx = 5592404
      · subst h3
        have hgo : gapOffset 5592404 = 96 * 2796202 := by decide
        rw [hgo, hprom_pres.readBuffer_eq (by omega) (by omega)]
        exact writeBits_readBuffer_digest sf2 _ df
      · have h4 : idx = 5592405 := by omega
        subst h4
        have hgo : gapOffset 5592405 = 96 * 2796202 + 32 := by decide
        rw [hgo, ← Nat.add_assoc]
        exact hprom_dig
  · intro q hq j hj
    have hq_lt : q < 2796203 := by rw [levelSize_1] at hq; omega
    have h1 := hprom_pres (C_TD + levelBase 1 + 96 * q + 64 + j) (by omega) (by omega)
    have h2 := hsf3_pres_sb (C_TD + levelBase 1 + 96 * q + 64 + j) (by omega) (by omega)
    have h5 := hgap_b q hq j hj
    have h6 := getByte_of_mem_eq hsa_mem (BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * q + 64 + j))
    exact ((h1.trans h2).trans h5).trans h6

end CommitGolfCandidate
