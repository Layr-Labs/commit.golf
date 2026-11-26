import CommitGolfCandidate.MoonCommitLeaf

/-! Exact RV64IM execution proof for Phase 2 of the r=2 `commit` image:
- Phase 2A (`L0 -> L1` dense 3-ary, words `53299..57415`): `4,097 × 1,365` calls + promoted `L0[16,777,215]`
- Phase 2B (`L1 -> L2` dense-to-gapped 3-ary, words `57416..59444`): `2,799 × 333` pairs + odd triplet + promoted `L1[5,592,405]`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Isolated JAL Targets -/

private theorem pc_jal_57407 :
    BitVec.ofNat 64 (0x1000 + 4 * 57407) + signExtend21 (2080768#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 53311) := by decide

private theorem pc_jal_59433 :
    BitVec.ofNat 64 (0x1000 + 4 * 59433) + signExtend21 (2089156#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 57434) := by decide

/-! ### 2. Phase 2A: `L0 -> L1` Dense 3-ary (`words 53299..57415`) -/

private def phase2ASetupInstrs : List Instr :=
  [.ADDI .x10 .x9 (4000#12), .ADDI .x6 .x0 (128#12), .SLLI .x6 .x6 (11#6), .SLLI .x6 .x6 (11#6),
   .ADD .x12 .x9 .x6, .ADDI .x12 .x12 (4064#12),
   .ADDI .x6 .x0 (127#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (2047#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (1920#12), .ADD .x19 .x9 .x6]

private theorem commit_phase2A_setup (oracle : Oracle) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 53299))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let sa := phase2ASetupInstrs.foldl execInstrBr s0
    DetRun oracle (submission.image .commit) s0 12 sa 12 0 ∧
    sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 53311) ∧
    sa.mem = s0.mem ∧
    sa.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sa.getReg .x5 = 0#64 ∧
    sa.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sa.getReg .x10 = BitVec.ofNat 64 (C_TD - 96) ∧
    sa.getReg .x11 = 96#64 ∧ sa.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 - 32) ∧
    sa.getReg .x13 = 0#64 ∧ sa.getReg .x19 = BitVec.ofNat 64 (C_TD + 5592405 * 96 - 96) ∧
    sa.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ phase2ASetupInstrs, isPureAlu ins = true := by decide
  have hlb1 : levelBase 1 = 536870912 := by decide
  refine ⟨?_, ?_, foldl_pureAlu_mem phase2ASetupInstrs s0 hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply exec_alu_list phase2ASetupInstrs s0
    intro i hi
    have hi' : i < 12 := hi
    have hpc_i : ((phase2ASetupInstrs.take i).foldl execInstrBr s0).pc =
        BitVec.ofNat 64 (0x1000 + 4 * (53299 + i)) := by
      have h := foldl_pureAlu_pc (phase2ASetupInstrs.take i) s0 (0x1000 + 4 * 53299)
        (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
      rw [List.length_take_of_le (by omega)] at h
      rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
    interval_cases i <;>
      exact ⟨commit_fetch_commitMid1CInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩
  · exact (foldl_pureAlu_pc phase2ASetupInstrs s0 (0x1000 + 4 * 53299) hall hpc).trans (by decide)
  all_goals (
    simp only [phase2ASetupInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx2, hx5, hx9, hx11, hx13, hx26, hlb1]
    try decide)

/-- One single-call step of `L0 -> L1` dense 3-ary (`l1CallInstr`: 3 steps, 10 cycles, 1 call). -/
private theorem commit_l1_step (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (k idx : Nat) (hk : k < 1365) (hidx : idx < FULL_TRIPLETS_0)
    (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (53311 + 3 * k)))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * idx - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 32 * idx - 32))
    (hl0 : ∀ j < 3, readBuffer s (C_TD + 32 * (3 * idx + j)) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 0 (3 * idx + j)) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 3 s' 10 1 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (53311 + 3 * (k + 1))) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * idx) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 32 * idx) ∧
      readBuffer s' (C_TD + levelBase 1 + 32 * idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 idx ∧
      MemPreservedOutside s s' (C_TD + levelBase 1 + 32 * idx) (C_TD + levelBase 1 + 32 * (idx + 1)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hft0 := full_triplets_0_eq
  have hlb1 : levelBase 1 = 536870912 := by decide
  let s1 := execInstrBr s (.ADDI .x10 .x10 (96#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (32#12))
  let d0 := nodeVal c96 msg salts 1 idx
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + levelBase 1 + 32 * idx)) d0
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (53311 + 3 * k + 1)) := pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (53311 + 3 * k + 2)) := pc_step_idx s1 _ hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (53311 + 3 * (k + 1))) :=
    (pc_step_idx s2 _ hs2_pc).trans (congrArg (BitVec.ofNat 64) (by omega))
  have hm2 : s2.mem = s.mem := (mem_exec_ADDI s1 .x12 .x12 (32#12)).trans (mem_exec_ADDI s .x10 .x10 (96#12))
  have hs2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s2.getReg r = s.getReg r := fun r h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
  have hs1_a0 : s1.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * idx) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD]; omega)
  have hs2_a0 : s2.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * idx) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs1_a0]
  have hs2_a2 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 32 * idx) := by
    have h1x12 : s1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 32 * idx - 32) := by
      simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hx12]
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h1x12,
      add_signExtend12_ofNat_small _ 32 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD, hlb1]; omega)
  have hs2_in : readBuffer s2 (C_TD + 96 * idx) 96 =
      ternaryInput (nodeVal c96 msg salts 0 (3 * idx))
        (nodeVal c96 msg salts 0 (3 * idx + 1)) (nodeVal c96 msg salts 0 (3 * idx + 2)) := by
    rw [readBuffer_of_mem_eq hm2, readBuffer_ternary]
    have h0 := hl0 0 (by omega); have h1 := hl0 1 (by omega); have h2 := hl0 2 (by omega)
    simp only [show C_TD + 96 * idx = C_TD + 32 * (3 * idx + 0) by omega,
      show C_TD + 32 * (3 * idx + 0) + 32 = C_TD + 32 * (3 * idx + 1) by omega,
      show C_TD + 32 * (3 * idx + 0) + 64 = C_TD + 32 * (3 * idx + 2) by omega]
    rw [h0, h1, h2]
    simp only [Nat.add_zero]; rfl
  have hd0_eq : oracle.compression ((readBuffer s2 (C_TD + 96 * idx) 96).cast h768.symm) = d0 := by
    rw [hs2_in]; unfold d0 nodeVal nodeValFromLeaves
    simp only [hidx, ite_true]; rfl
  have hst0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_l1_bulk s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc)) rfl
  have hst1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_l1_bulk s1 k 1 hk (by omega) hs1_pc) rfl
  have hst2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s2)
      (commit_fetch_l1_bulk s2 k 2 hk (by omega) hs2_pc)
      ((hs2_reg_other .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg_other .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg_other .x13 (by decide) (by decide)).trans hx13)
      (C_TD + 96 * idx) (C_TD + levelBase 1 + 32 * idx) hs2_a0 hs2_a2
      (by omega) (by omega) (by omega) (by omega) d0 hd0_eq
  refine ⟨s3, (hst0.trans hst1).trans hst2, hs3_pc,
    fun r h10 h12 => (writeBits_register s2 _ d0 r).trans (hs2_reg_other r h10 h12),
    (writeBits_register s2 _ d0 .x10).trans hs2_a0,
    (writeBits_register s2 _ d0 .x12).trans hs2_a2,
    writeBits_readBuffer_digest s2 _ d0,
    ((MemPreservedOutside.of_mem_eq hm2 _ _).trans
      (memPreserved_writeBits s2 (C_TD + levelBase 1 + 32 * idx) d0 (by omega))).mono
      (le_refl _) (by omega)⟩

/-- One 1365-call chunk of Phase 2A (`words 53311..57407`): `4,097` (or `4,096` on last) steps,
`13,652` (or `13,651` on last) cycles, `1,365` calls. -/
private theorem commit_phase2A_chunk (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (c : Nat) (hc : c < 4097) (sc : MachineState)
    (hpc_c : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 53311))
    (hx5c : sc.getReg .x5 = 0#64) (hx11c : sc.getReg .x11 = 96#64) (hx13c : sc.getReg .x13 = 0#64)
    (hx10c : sc.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (1365 * c) - 96))
    (hx12c : sc.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 32 * (1365 * c) - 32))
    (hx19c : sc.getReg .x19 = BitVec.ofNat 64 (C_TD + 5592405 * 96 - 96))
    (hl0c : ∀ idx < LENGTH, readBuffer sc (C_TD + 32 * idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 0 idx) :
    let lcost : Nat := if c + 1 < 4097 then 2 else 1
    ∃ sl,
      DetRun oracle (submission.image .commit) sc (4095 + lcost) sl (13650 + lcost) 1365 ∧
      sl.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < 4097 then 53311 else 57408)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sl.getReg r = sc.getReg r) ∧
      sl.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (1365 * (c + 1)) - 96) ∧
      sl.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 32 * (1365 * (c + 1)) - 32) ∧
      (∀ idx, 1365 * c ≤ idx → idx < 1365 * (c + 1) →
        readBuffer sl (C_TD + levelBase 1 + 32 * idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 idx) ∧
      MemPreservedOutside sc sl (C_TD + levelBase 1 + 32 * (1365 * c))
        (C_TD + levelBase 1 + 32 * (1365 * (c + 1))) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hlb1 : levelBase 1 = 536870912 := by decide
  have hft0 := full_triplets_0_eq
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hcalls : ∀ m ≤ 1365,
      ∃ sm,
        DetRun oracle (submission.image .commit) sc (3 * m) sm (10 * m) m ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (53311 + 3 * m)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sm.getReg r = sc.getReg r) ∧
        sm.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (1365 * c + m) - 96) ∧
        sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 32 * (1365 * c + m) - 32) ∧
        (∀ idx, 1365 * c ≤ idx → idx < 1365 * c + m →
          readBuffer sm (C_TD + levelBase 1 + 32 * idx) 32 = nodeVal c96 msg salts 1 idx) ∧
        MemPreservedOutside sc sm (C_TD + levelBase 1 + 32 * (1365 * c))
          (C_TD + levelBase 1 + 32 * (1365 * c + m)) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc_c, fun _ _ _ => rfl,
        by simpa using hx10c, by simpa using hx12c, fun _ h1 h2 => by omega,
        MemPreservedOutside.refl _ _ _⟩
    | succ m ih =>
      obtain ⟨sm, hrunm, hpcm, hregm, hx10m, hx12m, hdigm, hpresm⟩ := ih (by omega)
      obtain ⟨sn, hrun1, hpcn, hregn, hx10n, hx12n, hd0, hpres1⟩ := commit_l1_step h768 oracle msg salts
        m (1365 * c + m) (by omega) (by omega) sm hpcm
        ((hregm .x5 (by decide) (by decide)).trans hx5c)
        ((hregm .x11 (by decide) (by decide)).trans hx11c)
        ((hregm .x13 (by decide) (by decide)).trans hx13c)
        hx10m hx12m
        (fun j hj => by
          rw [hpresm.readBuffer_eq (by omega) (by omega)]
          exact hl0c (3 * (1365 * c + m) + j) (by omega))
      have hrun_n : DetRun oracle (submission.image .commit) sc (3 * (m + 1)) sn (10 * (m + 1)) (m + 1) := by
        have h := hrunm.trans hrun1
        rw [show 3 * m + 3 = 3 * (m + 1) by omega, show 10 * m + 10 = 10 * (m + 1) by omega] at h
        exact h
      refine ⟨sn, hrun_n, hpcn, fun r h10 h12 => (hregn r h10 h12).trans (hregm r h10 h12),
        by rw [hx10n]; exact congrArg (BitVec.ofNat 64) (by omega),
        by rw [hx12n]; exact congrArg (BitVec.ofNat 64) (by omega), ?_, ?_⟩
      · intro idx hlo hhi
        by_cases hold : idx < 1365 * c + m
        · rw [← hdigm idx hlo hold]
          exact hpres1.readBuffer_eq (by omega) (by omega)
        · have heq : idx = 1365 * c + m := by omega
          subst heq; exact hd0
      · exact (hpresm.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (by omega))
  obtain ⟨sm, hrunB, hpcB, hregB, hx10_B, hx12_B, hdigB, hpresB⟩ := hcalls 1365 (le_refl _)
  have hx19m : sm.getReg .x19 = BitVec.ofNat 64 (C_TD + 5592405 * 96 - 96) :=
    (hregB .x19 (by decide) (by decide)).trans hx19c
  let done : Bool := decide (c + 1 = 4097)
  have hcmp : (sm.getReg .x10 == sm.getReg .x19) = done := by
    dsimp only [done]
    by_cases heq : c + 1 = 4097
    · have hnat : C_TD + 96 * (1365 * c + 1365) - 96 = C_TD + 5592405 * 96 - 96 := by
        rw [show 1365 * c + 1365 = 1365 * (c + 1) by omega, heq]
      rw [hx10_B, hx19m, hnat, beq_self_eq_true, decide_eq_true heq]
    · rw [hx10_B, hx19m, decide_eq_false heq, beq_eq_false_iff_ne]
      exact bv64_ne_of_nat_ne (by rw [hC_TD]; omega) (by rw [hC_TD]; omega) (by rw [hC_TD]; omega)
  obtain ⟨hlatch, hpc_end, hmem_l, hreg_l⟩ :=
    c_beq_jal_latch oracle sm .x10 .x19 57406 53311 (2080768#21) done hpcB hcmp
      (commit_fetch_commitMid2AInstr sm 57406 (by omega) (by omega) hpcB)
      (fun st hst => commit_fetch_commitMid2AInstr st 57407 (by omega) (by omega) hst)
      pc_jal_57407
  have hcost_eq : (if done = true then 1 else 2) = (if c + 1 < 4097 then 2 else 1) := by
    by_cases h : c + 1 < 4097
    · simp only [done, decide_eq_false (by omega : c + 1 ≠ 4097), Bool.false_eq_true, ite_false, h, ite_true]
    · simp only [done, decide_eq_true (by omega : c + 1 = 4097), ite_true, h, ite_false]
  have hpc_norm : (if done = true then 57406 + 2 else 53311) = (if c + 1 < 4097 then 53311 else 57408) := by
    by_cases h : c + 1 < 4097
    · simp only [done, decide_eq_false (by omega : c + 1 ≠ 4097), Bool.false_eq_true, ite_false, h, ite_true]
    · simp only [done, decide_eq_true (by omega : c + 1 = 4097), ite_true, h, ite_false]
  refine ⟨_, by simpa only [hcost_eq, Nat.add_zero] using hrunB.trans hlatch,
    by rw [hpc_end, hpc_norm],
    fun r h10 h12 => (hreg_l r).trans (hregB r h10 h12),
    by rw [hreg_l, hx10_B]; exact congrArg (BitVec.ofNat 64) (by omega),
    by rw [hreg_l, hx12_B]; exact congrArg (BitVec.ofNat 64) (by omega),
    fun idx hlo hhi => (readBuffer_of_mem_eq hmem_l _ _).trans (hdigB idx hlo (by omega)),
    (hpresB.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmem_l _ _)⟩

/-- Full Phase 2A (`L0 -> L1` dense 3-ary + promoted leaf `16,777,215`, words `53299..57415`):
exact `16,785,428` steps, `55,932,263` cycles, `5,592,405` compression calls. -/
theorem commit_phase2A (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 53299))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hl0 : ∀ idx < LENGTH, readBuffer s0 (C_TD + 32 * idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 0 idx) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 16785428 s1 55932263 5592405 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 57416) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ idx < levelSize 1, readBuffer s1 (C_TD + levelBase 1 + 32 * idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 idx) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 1) (C_TD + levelBase 2) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hlb1 : levelBase 1 = 536870912 := by decide
  have hlb2 : levelBase 2 = 715827904 := by decide
  have hft0 := full_triplets_0_eq
  have hls1 := levelSize_1
  let sa := phase2ASetupInstrs.foldl execInstrBr s0
  obtain ⟨hsetup, hsa_pc, hsa_mem, hsa_x2, hsa_x5, hsa_x9, hsa_x10, hsa_x11, hsa_x12,
    hsa_x13, hsa_x19, hsa_x26⟩ := commit_phase2A_setup oracle s0 hpc hx2 hx5 hx9 hx11 hx13 hx26
  have hbulk : ∀ n ≤ 4097,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa
          (if n < 4097 then 4097 * n else 16785408) sn
          (if n < 4097 then 13652 * n else 55932243) (1365 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 4097 then 53311 else 57408)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sn.getReg r = sa.getReg r) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_TD + 96 * (1365 * n) - 96) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 1 + 32 * (1365 * n) - 32) ∧
        (∀ idx < 1365 * n, readBuffer sn (C_TD + levelBase 1 + 32 * idx) 32 = nodeVal c96 msg salts 1 idx) ∧
        MemPreservedOutside sa sn (C_TD + levelBase 1) (C_TD + levelBase 1 + 32 * (1365 * n)) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨sa, by simpa using DetRun.refl oracle (submission.image .commit) sa,
        by simpa using hsa_pc, fun _ _ _ => rfl,
        by simpa using hsa_x10, by simpa using hsa_x12,
        fun _ h => (Nat.not_lt_zero _ h).elim, MemPreservedOutside.refl _ _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hregn, hx10n, hx12n, hdign, hpresn⟩ := ih (by omega)
      have hlt_n : n < 4097 := by omega
      simp only [hlt_n, ite_true] at hrunn
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 53311) := by simpa only [hlt_n, ite_true] using hpcn
      obtain ⟨sm, hrun1, hpcm, hregm, hx10m, hx12m, hdig1, hpres1⟩ :=
        commit_phase2A_chunk h768 oracle msg salts n (by omega) sn hpc_in
          ((hregn .x5 (by decide) (by decide)).trans hsa_x5)
          ((hregn .x11 (by decide) (by decide)).trans hsa_x11)
          ((hregn .x13 (by decide) (by decide)).trans hsa_x13)
          hx10n hx12n
          ((hregn .x19 (by decide) (by decide)).trans hsa_x19)
          (fun idx hidx => by
            rw [hpresn.readBuffer_eq (by omega) (by omega), readBuffer_of_mem_eq hsa_mem]
            exact hl0 idx hidx)
      have hrun_n1 : DetRun oracle (submission.image .commit) sa
          (if n + 1 < 4097 then 4097 * (n + 1) else 16785408) sm
          (if n + 1 < 4097 then 13652 * (n + 1) else 55932243) (1365 * (n + 1)) := by
        have h := hrunn.trans hrun1
        have hs : 4097 * n + (4095 + if n + 1 < 4097 then 2 else 1) =
            if n + 1 < 4097 then 4097 * (n + 1) else 16785408 := by split <;> omega
        have hc : 13652 * n + (13650 + if n + 1 < 4097 then 2 else 1) =
            if n + 1 < 4097 then 13652 * (n + 1) else 55932243 := by split <;> omega
        rw [hs, hc, show 1365 * n + 1365 = 1365 * (n + 1) by omega] at h
        exact h
      refine ⟨sm, hrun_n1, hpcm,
        fun r h10 h12 => (hregm r h10 h12).trans (hregn r h10 h12), hx10m, hx12m, ?_, ?_⟩
      · intro idx hidx
        by_cases hlt : idx < 1365 * n
        · rw [← hdign idx hlt]
          exact hpres1.readBuffer_eq (by omega) (by omega)
        · exact hdig1 idx (by omega) hidx
      · exact (hpresn.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (le_refl _))
  obtain ⟨sb, hrun_bulk, hpc_b, hreg_b, hx10_b, hx12_b, hdig_b, hpres_b⟩ := hbulk 4097 (le_refl _)
  simp only [Nat.lt_irrefl, ite_false] at hrun_bulk
  have hpc_b' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 57408) := by
    simpa only [Nat.lt_irrefl, ite_false] using hpc_b
  -- Promoted leaf 16,777,215 copy (words 57408..57415: 4 ld/sd pairs = 8 steps, 8 cyc, 0 calls)
  obtain ⟨sfin, hprom_run, hsfin_pc, hsfin_reg, hsfin_dig, hprom_pres⟩ :=
    commit_copy32 oracle sb 57408 .x10 .x12
      (C_TD + 96 * 5592405 - 96) (C_TD + levelBase 1 + 32 * 5592405 - 32) 96 32
      (by decide) (by decide) (by decide) (by decide)
      (by rw [hC_TD]) (by rw [hC_TD, hlb1])
      (by rw [hC_TD, hMB]; omega) (by rw [hC_TD, hMB, hlb1]; omega)
      (by rw [hC_TD, hlb1]; omega) hpc_b' hx10_b hx12_b
      (fun k hk st => by
        constructor
        · intro hpc'
          have h := commit_fetch_commitMid2AInstr st (57408 + 2 * k) (by omega) (by omega) hpc'
          interval_cases k <;> simpa only [commitMid2AInstr] using h
        · intro hpc'
          have h := commit_fetch_commitMid2AInstr st (57408 + 2 * k + 1) (by omega) (by omega) hpc'
          interval_cases k <;> simpa only [commitMid2AInstr] using h)
  have hreg_sfin : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sfin.getReg r = sa.getReg r :=
    fun r h6 h10 h12 => (hsfin_reg r h6).trans (hreg_b r h10 h12)
  refine ⟨sfin, (hsetup.trans hrun_bulk).trans hprom_run, hsfin_pc,
    (hreg_sfin .x2 (by decide) (by decide) (by decide)).trans hsa_x2,
    (hreg_sfin .x5 (by decide) (by decide) (by decide)).trans hsa_x5,
    (hreg_sfin .x9 (by decide) (by decide) (by decide)).trans hsa_x9,
    (hreg_sfin .x11 (by decide) (by decide) (by decide)).trans hsa_x11,
    (hreg_sfin .x13 (by decide) (by decide) (by decide)).trans hsa_x13,
    (hreg_sfin .x26 (by decide) (by decide) (by decide)).trans hsa_x26, ?_, ?_⟩
  · intro idx hidx
    by_cases hlt : idx < 5592405
    · rw [hprom_pres.readBuffer_eq (by omega) (by omega)]
      exact hdig_b idx hlt
    · have heq : idx = 5592405 := by omega
      subst heq
      have hdst : C_TD + levelBase 1 + 32 * 5592405 - 32 + 32 = C_TD + levelBase 1 + 32 * 5592405 := by
        rw [hC_TD, hlb1]
      have hsrc : C_TD + 96 * 5592405 - 96 + 96 = C_TD + 32 * 16777215 := by
        rw [hC_TD]
      rw [← hdst, hsfin_dig, hsrc, hpres_b.readBuffer_eq (by omega) (by omega), readBuffer_of_mem_eq hsa_mem,
          hl0 16777215 (by omega)]
      have hprom : ∀ (c : Comp96), nodeVal c msg salts 0 16777215 = nodeVal c msg salts 1 5592405 := by
        intro c; unfold nodeVal; symm; conv_lhs => rw [nodeValFromLeaves.eq_def]
        dsimp only; simp only [hft0, Nat.lt_irrefl, ite_false, ite_true]
      exact hprom c96
  · exact ((MemPreservedOutside.of_mem_eq hsa_mem _ _).trans
      (hpres_b.mono (le_refl _) (by omega))).trans (hprom_pres.mono (by omega) (by omega))

/-! ### 3. Phase 2B: `L1 -> L2` Dense-to-Gapped 3-ary (`words 57416..59444`) -/

private def phase2BSetupInstrs : List Instr :=
  [.ADDI .x6 .x0 (128#12), .SLLI .x6 .x6 (11#6), .SLLI .x6 .x6 (11#6),
   .ADD .x10 .x9 .x6, .ADDI .x10 .x10 (4000#12),
   .ADDI .x6 .x0 (170#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (1365#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (704#12), .ADD .x12 .x9 .x6, .ADDI .x12 .x12 (4032#12),
   .ADDI .x6 .x0 (170#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (1365#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (480#12), .ADD .x19 .x9 .x6]

private theorem commit_phase2B_setup (oracle : Oracle) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 57416))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let sa := phase2BSetupInstrs.foldl execInstrBr s0
    DetRun oracle (submission.image .commit) s0 18 sa 18 0 ∧
    sa.pc = BitVec.ofNat 64 (0x1000 + 4 * 57434) ∧
    sa.mem = s0.mem ∧
    sa.getReg .x2 = BitVec.ofNat 64 C_DB ∧ sa.getReg .x5 = 0#64 ∧
    sa.getReg .x9 = BitVec.ofNat 64 C_TD ∧ sa.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 - 96) ∧
    sa.getReg .x11 = 96#64 ∧ sa.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 - 64) ∧
    sa.getReg .x13 = 0#64 ∧ sa.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase 1 + 1864134 * 96 - 96) ∧
    sa.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ phase2BSetupInstrs, isPureAlu ins = true := by decide
  have hlb1 : levelBase 1 = 536870912 := by decide
  have hlb2 : levelBase 2 = 715827904 := by decide
  refine ⟨?_, ?_, foldl_pureAlu_mem phase2BSetupInstrs s0 hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply exec_alu_list phase2BSetupInstrs s0
    intro i hi
    have hi' : i < 18 := hi
    have hpc_i : ((phase2BSetupInstrs.take i).foldl execInstrBr s0).pc =
        BitVec.ofNat 64 (0x1000 + 4 * (57416 + i)) := by
      have h := foldl_pureAlu_pc (phase2BSetupInstrs.take i) s0 (0x1000 + 4 * 57416)
        (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
      rw [List.length_take_of_le (by omega)] at h
      rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
    interval_cases i <;>
      exact ⟨commit_fetch_commitMid2AInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩
  · exact (foldl_pureAlu_pc phase2BSetupInstrs s0 (0x1000 + 4 * 57416) hall hpc).trans (by decide)
  all_goals (
    simp only [phase2BSetupInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx2, hx5, hx9, hx11, hx13, hx26, hlb1, hlb2]
    try decide)

/-- One 2-call pair of `L1 -> L2` dense-to-gapped 3-ary compressions (`l2PairInstr`: 6 steps, 20 cycles, 2 calls). -/
private theorem commit_l2_pair (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (m q : Nat) (hm : m < 333) (hq : 2 * q + 1 < FULL_TRIPLETS_1)
    (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (57434 + 6 * m)))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (2 * q) - 96))
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q - 64))
    (hl1 : ∀ j < 6, readBuffer s (C_TD + levelBase 1 + 32 * (6 * q + j)) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 (6 * q + j)) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 6 s' 20 2 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (57434 + 6 * (m + 1))) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (2 * q + 1)) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q + 32) ∧
      readBuffer s' (C_TD + levelBase 2 + 96 * q) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 2 (2 * q) ∧
      readBuffer s' (C_TD + levelBase 2 + 96 * q + 32) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 2 (2 * q + 1) ∧
      MemPreservedOutside s s' (C_TD + levelBase 2 + 96 * q) (C_TD + levelBase 2 + 96 * q + 64) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hft1 := full_triplets_1_eq
  have hlb1 : levelBase 1 = 536870912 := by decide
  have hlb2 : levelBase 2 = 715827904 := by decide
  let s1 := execInstrBr s (.ADDI .x10 .x10 (96#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (64#12))
  let d0 := nodeVal c96 msg salts 2 (2 * q)
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q)) d0
  let s4 := execInstrBr s3 (.ADDI .x10 .x10 (96#12))
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 (32#12))
  let d1 := nodeVal c96 msg salts 2 (2 * q + 1)
  let s6 := writeBits s5 (BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q + 32)) d1
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (57434 + 6 * m + 1)) := pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (57434 + 6 * m + 2)) := pc_step_idx s1 _ hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (57434 + 6 * m + 3)) := pc_step_idx s2 _ hs2_pc
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (57434 + 6 * m + 4)) := pc_step_idx s3 _ hs3_pc
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * (57434 + 6 * m + 5)) := pc_step_idx s4 _ hs4_pc
  have hs6_pc : s6.pc = BitVec.ofNat 64 (0x1000 + 4 * (57434 + 6 * (m + 1))) :=
    (pc_step_idx s5 _ hs5_pc).trans (congrArg (BitVec.ofNat 64) (by omega))
  have hs2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s2.getReg r = s.getReg r := fun r h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
  have hs5_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → s5.getReg r = s.getReg r := fun r h10 h12 => by
    have h53 : s5.getReg r = s3.getReg r := by
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
    exact (h53.trans (writeBits_register s2 _ d0 r)).trans (hs2_reg_other r h10 h12)
  have hm2 : s2.mem = s.mem := (mem_exec_ADDI s1 .x12 .x12 (64#12)).trans (mem_exec_ADDI s .x10 .x10 (96#12))
  have hm5 : s5.mem = s3.mem := (mem_exec_ADDI s4 .x12 .x12 (32#12)).trans (mem_exec_ADDI s3 .x10 .x10 (96#12))
  have hs1_a0 : s1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (2 * q)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD, hlb1]; omega)
  have hs2_a0 : s2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (2 * q)) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs1_a0]
  have hs2_a2 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q) := by
    have h1x12 : s1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q - 64) := by
      simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hx12]
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h1x12,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD, hlb2]; omega)
  have hs2_in : readBuffer s2 (C_TD + levelBase 1 + 96 * (2 * q)) 96 =
      ternaryInput (nodeVal c96 msg salts 1 (6 * q))
        (nodeVal c96 msg salts 1 (6 * q + 1)) (nodeVal c96 msg salts 1 (6 * q + 2)) := by
    rw [readBuffer_of_mem_eq hm2, readBuffer_ternary]
    have h0 := hl1 0 (by omega); have h1 := hl1 1 (by omega); have h2 := hl1 2 (by omega)
    simp only [show C_TD + levelBase 1 + 96 * (2 * q) = C_TD + levelBase 1 + 32 * (6 * q + 0) by omega,
      show C_TD + levelBase 1 + 32 * (6 * q + 0) + 32 = C_TD + levelBase 1 + 32 * (6 * q + 1) by omega,
      show C_TD + levelBase 1 + 32 * (6 * q + 0) + 64 = C_TD + levelBase 1 + 32 * (6 * q + 2) by omega]
    rw [h0, h1, h2]
    simp only [Nat.add_zero]; rfl
  have hd0_eq : oracle.compression ((readBuffer s2 (C_TD + levelBase 1 + 96 * (2 * q)) 96).cast h768.symm) = d0 := by
    rw [hs2_in]; unfold d0 nodeVal nodeValFromLeaves
    simp only [show 2 * q < FULL_TRIPLETS_1 by omega, ite_true, show 3 * (2 * q) = 6 * q by omega]; rfl
  have hst0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_l2_bulk s m 0 hm (by omega) (by simpa only [Nat.add_zero] using hpc)) rfl
  have hst1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_l2_bulk s1 m 1 hm (by omega) hs1_pc) rfl
  have hst2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s2)
      (commit_fetch_l2_bulk s2 m 2 hm (by omega) hs2_pc)
      ((hs2_reg_other .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg_other .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg_other .x13 (by decide) (by decide)).trans hx13)
      (C_TD + levelBase 1 + 96 * (2 * q)) (C_TD + levelBase 2 + 96 * q) hs2_a0 hs2_a2
      (by omega) (by omega) (by omega) (by omega) d0 hd0_eq
  have hs3_pres : MemPreservedOutside s s3 (C_TD + levelBase 2 + 96 * q) (C_TD + levelBase 2 + 96 * q + 32) :=
    (MemPreservedOutside.of_mem_eq hm2 _ _).trans
      (memPreserved_writeBits s2 (C_TD + levelBase 2 + 96 * q) d0 (by omega))
  have hs3_a0 : s3.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (2 * q)) :=
    (writeBits_register s2 _ d0 .x10).trans hs2_a0
  have hs3_a2 : s3.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q) :=
    (writeBits_register s2 _ d0 .x12).trans hs2_a2
  have hs4_a0 : s4.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (2 * q + 1)) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs3_a0,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD, hlb1]; omega)
  have hs5_a0 : s5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (2 * q + 1)) := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs4_a0]
  have hs5_a2 : s5.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q + 32) := by
    have h4x12 : s4.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hs3_a2]
    simp only [s5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h4x12,
      add_signExtend12_ofNat_small _ 32 (by omega)]
  have hs5_in : readBuffer s5 (C_TD + levelBase 1 + 96 * (2 * q + 1)) 96 =
      ternaryInput (nodeVal c96 msg salts 1 (6 * q + 3))
        (nodeVal c96 msg salts 1 (6 * q + 4)) (nodeVal c96 msg salts 1 (6 * q + 5)) := by
    rw [readBuffer_of_mem_eq hm5, hs3_pres.readBuffer_eq (by omega) (by omega), readBuffer_ternary]
    have h3 := hl1 3 (by omega); have h4 := hl1 4 (by omega); have h5 := hl1 5 (by omega)
    simp only [show C_TD + levelBase 1 + 96 * (2 * q + 1) = C_TD + levelBase 1 + 32 * (6 * q + 3) by omega,
      show C_TD + levelBase 1 + 32 * (6 * q + 3) + 32 = C_TD + levelBase 1 + 32 * (6 * q + 4) by omega,
      show C_TD + levelBase 1 + 32 * (6 * q + 3) + 64 = C_TD + levelBase 1 + 32 * (6 * q + 5) by omega]
    rw [h3, h4, h5]
  have hd1_eq : oracle.compression ((readBuffer s5 (C_TD + levelBase 1 + 96 * (2 * q + 1)) 96).cast h768.symm) = d1 := by
    rw [hs5_in]; unfold d1 nodeVal nodeValFromLeaves
    simp only [show 2 * q + 1 < FULL_TRIPLETS_1 by omega, ite_true, show 3 * (2 * q + 1) = 6 * q + 3 by omega]; rfl
  have hst3 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (commit_fetch_l2_bulk s3 m 3 hm (by omega) hs3_pc) rfl
  have hst4 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (commit_fetch_l2_bulk s4 m 4 hm (by omega) hs4_pc) rfl
  have hst5 : DetRun oracle (submission.image .commit) s5 1 s6 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s5)
      (commit_fetch_l2_bulk s5 m 5 hm (by omega) hs5_pc)
      ((hs5_reg_other .x5 (by decide) (by decide)).trans hx5)
      ((hs5_reg_other .x11 (by decide) (by decide)).trans hx11)
      ((hs5_reg_other .x13 (by decide) (by decide)).trans hx13)
      (C_TD + levelBase 1 + 96 * (2 * q + 1)) (C_TD + levelBase 2 + 96 * q + 32) hs5_a0 hs5_a2
      (by omega) (by omega) (by omega) (by omega) d1 hd1_eq
  refine ⟨s6, by simpa using ((((hst0.trans hst1).trans hst2).trans hst3).trans hst4).trans hst5,
    hs6_pc, fun r h10 h12 => (writeBits_register s5 _ d1 r).trans (hs5_reg_other r h10 h12),
    (writeBits_register s5 _ d1 .x10).trans hs5_a0,
    (writeBits_register s5 _ d1 .x12).trans hs5_a2, ?_, ?_, ?_⟩
  · have hp6 := memPreserved_writeBits s5 (C_TD + levelBase 2 + 96 * q + 32) d1 (by omega)
    rw [hp6.readBuffer_eq (by omega) (by omega), readBuffer_of_mem_eq hm5]
    exact writeBits_readBuffer_digest s2 _ d0
  · exact writeBits_readBuffer_digest s5 _ d1
  · exact ((hs3_pres.mono (le_refl _) (by omega)).trans
      (MemPreservedOutside.of_mem_eq hm5 _ _)).trans
      ((memPreserved_writeBits s5 (C_TD + levelBase 2 + 96 * q + 32) d1 (by omega)).mono (by omega) (le_refl _))

/-- One 333-pair chunk of Phase 2B (`words 57434..59433`): `2,000` (or `1,999` on last) steps,
`6,662` (or `6,661` on last) cycles, `666` calls. -/
private theorem commit_phase2B_chunk (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (c : Nat) (hc : c < 2799) (sc : MachineState)
    (hpc_c : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 57434))
    (hx5c : sc.getReg .x5 = 0#64) (hx11c : sc.getReg .x11 = 96#64) (hx13c : sc.getReg .x13 = 0#64)
    (hx10c : sc.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (666 * c) - 96))
    (hx12c : sc.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * (333 * c) - 64))
    (hx19c : sc.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase 1 + 1864134 * 96 - 96))
    (hl1c : ∀ idx < levelSize 1, readBuffer sc (C_TD + levelBase 1 + 32 * idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 idx) :
    let lcost : Nat := if c + 1 < 2799 then 2 else 1
    ∃ sl,
      DetRun oracle (submission.image .commit) sc (1998 + lcost) sl (6660 + lcost) 666 ∧
      sl.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < 2799 then 57434 else 59434)) ∧
      (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sl.getReg r = sc.getReg r) ∧
      sl.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (666 * (c + 1)) - 96) ∧
      sl.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * (333 * (c + 1)) - 64) ∧
      (∀ idx, 666 * c ≤ idx → idx < 666 * (c + 1) →
        readBuffer sl (C_TD + levelBase 2 + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 2 idx) ∧
      (∀ q < (levelSize 2 + 1) / 2, ∀ j < 32,
        sl.getByte (BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q + 64 + j)) =
        sc.getByte (BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q + 64 + j))) ∧
      MemPreservedOutside sc sl (C_TD + levelBase 2 + 96 * (333 * c))
        (C_TD + levelBase 2 + 96 * (333 * (c + 1))) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hlb1 : levelBase 1 = 536870912 := by decide
  have hlb2 : levelBase 2 = 715827904 := by decide
  have hft1 := full_triplets_1_eq
  have hls1 := levelSize_1
  have hls2 := levelSize_2
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hpairs : ∀ m ≤ 333,
      ∃ sm,
        DetRun oracle (submission.image .commit) sc (6 * m) sm (20 * m) (2 * m) ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (57434 + 6 * m)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sm.getReg r = sc.getReg r) ∧
        sm.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (2 * (333 * c + m)) - 96) ∧
        sm.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * (333 * c + m) - 64) ∧
        (∀ idx, 666 * c ≤ idx → idx < 666 * c + 2 * m →
          readBuffer sm (C_TD + levelBase 2 + gapOffset idx) 32 = nodeVal c96 msg salts 2 idx) ∧
        (∀ q < (levelSize 2 + 1) / 2, ∀ j < 32,
          sm.getByte (BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q + 64 + j)) =
          sc.getByte (BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q + 64 + j))) ∧
        MemPreservedOutside sc sm (C_TD + levelBase 2 + 96 * (333 * c))
          (C_TD + levelBase 2 + 96 * (333 * c + m)) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc_c, fun _ _ _ => rfl,
        by rw [hx10c]; exact congrArg (BitVec.ofNat 64) (by omega),
        by simpa using hx12c, fun _ h1 h2 => by omega, fun _ _ _ _ => rfl,
        MemPreservedOutside.refl _ _ _⟩
    | succ m ih =>
      obtain ⟨sm, hrunm, hpcm, hregm, hx10m, hx12m, hdigm, hgapm, hpresm⟩ := ih (by omega)
      obtain ⟨sn, hrun1, hpcn, hregn, hx10n, hx12n, hd0, hd1, hpres1⟩ := commit_l2_pair h768 oracle msg salts
        m (333 * c + m) (by omega) (by omega) sm hpcm
        ((hregm .x5 (by decide) (by decide)).trans hx5c)
        ((hregm .x11 (by decide) (by decide)).trans hx11c)
        ((hregm .x13 (by decide) (by decide)).trans hx13c)
        hx10m hx12m
        (fun j hj => by
          rw [hpresm.readBuffer_eq (by omega) (by omega)]
          exact hl1c (6 * (333 * c + m) + j) (by omega))
      refine ⟨sn, by simpa [Nat.mul_succ] using hrunm.trans hrun1, hpcn,
        fun r h10 h12 => (hregn r h10 h12).trans (hregm r h10 h12),
        by rw [hx10n]; exact congrArg (BitVec.ofNat 64) (by omega),
        by rw [hx12n]; exact congrArg (BitVec.ofNat 64) (by omega), ?_, ?_, ?_⟩
      · intro idx hlo hhi
        by_cases hold : idx < 666 * c + 2 * m
        · rw [← hdigm idx hlo hold]
          have hgo : gapOffset idx + 32 ≤ 96 * (333 * c + m) := by unfold gapOffset; omega
          exact hpres1.readBuffer_eq (by omega) (by omega)
        · by_cases hev : idx = 2 * (333 * c + m)
          · subst hev; simpa [gapOffset_even] using hd0
          · have hodd : idx = 2 * (333 * c + m) + 1 := by omega
            subst hodd; simpa [gapOffset_odd, Nat.add_assoc] using hd1
      · intro q hq j hj
        have hsep : C_TD + levelBase 2 + 96 * q + 64 + j < C_TD + levelBase 2 + 96 * (333 * c + m) ∨
            C_TD + levelBase 2 + 96 * (333 * c + m) + 64 ≤ C_TD + levelBase 2 + 96 * q + 64 + j := by omega
        exact (hpres1 (C_TD + levelBase 2 + 96 * q + 64 + j) (by omega) hsep).trans (hgapm q hq j hj)
      · exact (hpresm.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (by omega))
  obtain ⟨sm, hrunB, hpcB, hregB, hx10_B, hx12_B, hdigB, hgapB, hpresB⟩ := hpairs 333 (le_refl _)
  have hx19m : sm.getReg .x19 = BitVec.ofNat 64 (C_TD + levelBase 1 + 1864134 * 96 - 96) :=
    (hregB .x19 (by decide) (by decide)).trans hx19c
  let done : Bool := decide (c + 1 = 2799)
  have hcmp : (sm.getReg .x10 == sm.getReg .x19) = done := by
    dsimp only [done]
    by_cases heq : c + 1 = 2799
    · have hnat : C_TD + levelBase 1 + 96 * (2 * (333 * c + 333)) - 96 =
          C_TD + levelBase 1 + 1864134 * 96 - 96 := by
        rw [show 333 * c + 333 = 333 * (c + 1) by omega, heq]
      rw [hx10_B, hx19m, hnat, beq_self_eq_true, decide_eq_true heq]
    · rw [hx10_B, hx19m, decide_eq_false heq, beq_eq_false_iff_ne]
      exact bv64_ne_of_nat_ne (by rw [hC_TD, hlb1]; omega) (by rw [hC_TD, hlb1]; omega) (by rw [hC_TD, hlb1]; omega)
  obtain ⟨hlatch, hpc_end, hmem_l, hreg_l⟩ :=
    c_beq_jal_latch oracle sm .x10 .x19 59432 57434 (2089156#21) done hpcB hcmp
      (commit_fetch_commitMid2BInstr sm 59432 (by omega) (by omega) hpcB)
      (fun st hst => commit_fetch_commitMid2BInstr st 59433 (by omega) (by omega) hst)
      pc_jal_59433
  have hcost_eq : (if done = true then 1 else 2) = (if c + 1 < 2799 then 2 else 1) := by
    by_cases h : c + 1 < 2799
    · simp only [done, decide_eq_false (by omega : c + 1 ≠ 2799), Bool.false_eq_true, ite_false, h, ite_true]
    · simp only [done, decide_eq_true (by omega : c + 1 = 2799), ite_true, h, ite_false]
  have hpc_norm : (if done = true then 59432 + 2 else 57434) = (if c + 1 < 2799 then 57434 else 59434) := by
    by_cases h : c + 1 < 2799
    · simp only [done, decide_eq_false (by omega : c + 1 ≠ 2799), Bool.false_eq_true, ite_false, h, ite_true]
    · simp only [done, decide_eq_true (by omega : c + 1 = 2799), ite_true, h, ite_false]
  refine ⟨_, by simpa only [hcost_eq, Nat.add_zero] using hrunB.trans hlatch,
    by rw [hpc_end, hpc_norm],
    fun r h10 h12 => (hreg_l r).trans (hregB r h10 h12),
    by rw [hreg_l, hx10_B]; exact congrArg (BitVec.ofNat 64) (by omega),
    by rw [hreg_l, hx12_B]; exact congrArg (BitVec.ofNat 64) (by omega),
    fun idx hlo hhi => (readBuffer_of_mem_eq hmem_l _ _).trans (hdigB idx hlo (by omega)),
    fun q hq j hj => (getByte_of_mem_eq hmem_l _).trans (hgapB q hq j hj),
    (hpresB.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmem_l _ _)⟩

/-- Full Phase 2B (`L1 -> L2` dense-to-gapped 3-ary + odd triplet `1,864,134` + promoted `L1[5,592,405]`,
words `57416..59444`): exact `5,598,028` steps, `18,646,973` cycles, `1,864,135` compression calls. -/
theorem commit_phase2B (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 57416))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hl1 : ∀ idx < levelSize 1, readBuffer s0 (C_TD + levelBase 1 + 32 * idx) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 1 idx) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 5598028 s1 18646973 1864135 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 59445) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ idx < levelSize 2, readBuffer s1 (C_TD + levelBase 2 + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 2 idx) ∧
      (∀ q < (levelSize 2 + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase 2) (C_TD + levelBase 3) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hlb1 : levelBase 1 = 536870912 := by decide
  have hlb2 : levelBase 2 = 715827904 := by decide
  have hlb3 : levelBase 3 = 805306432 := by decide
  have hft1 := full_triplets_1_eq
  have hls1 := levelSize_1
  have hls2 := levelSize_2
  let sa := phase2BSetupInstrs.foldl execInstrBr s0
  obtain ⟨hsetup, hsa_pc, hsa_mem, hsa_x2, hsa_x5, hsa_x9, hsa_x10, hsa_x11, hsa_x12,
    hsa_x13, hsa_x19, hsa_x26⟩ := commit_phase2B_setup oracle s0 hpc hx2 hx5 hx9 hx11 hx13 hx26
  have hbulk : ∀ n ≤ 2799,
      ∃ sn,
        DetRun oracle (submission.image .commit) sa
          (if n < 2799 then 2000 * n else 5597999) sn
          (if n < 2799 then 6662 * n else 18646937) (666 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 2799 then 57434 else 59434)) ∧
        (∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sn.getReg r = sa.getReg r) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * (666 * n) - 96) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * (333 * n) - 64) ∧
        (∀ idx < 666 * n, readBuffer sn (C_TD + levelBase 2 + gapOffset idx) 32 = nodeVal c96 msg salts 2 idx) ∧
        (∀ q < (levelSize 2 + 1) / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q + 64 + j)) =
          sa.getByte (BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * q + 64 + j))) ∧
        MemPreservedOutside sa sn (C_TD + levelBase 2) (C_TD + levelBase 2 + 96 * (333 * n)) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨sa, by simpa using DetRun.refl oracle (submission.image .commit) sa,
        by simpa using hsa_pc, fun _ _ _ => rfl,
        by simpa using hsa_x10, by simpa using hsa_x12,
        fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ _ => rfl, MemPreservedOutside.refl _ _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hregn, hx10n, hx12n, hdign, hgapn, hpresn⟩ := ih (by omega)
      have hlt_n : n < 2799 := by omega
      simp only [hlt_n, ite_true] at hrunn
      have hpc_in : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 57434) := by simpa only [hlt_n, ite_true] using hpcn
      obtain ⟨sm, hrun1, hpcm, hregm, hx10m, hx12m, hdig1, hgap1, hpres1⟩ :=
        commit_phase2B_chunk h768 oracle msg salts n (by omega) sn hpc_in
          ((hregn .x5 (by decide) (by decide)).trans hsa_x5)
          ((hregn .x11 (by decide) (by decide)).trans hsa_x11)
          ((hregn .x13 (by decide) (by decide)).trans hsa_x13)
          hx10n hx12n
          ((hregn .x19 (by decide) (by decide)).trans hsa_x19)
          (fun idx hidx => by
            rw [hpresn.readBuffer_eq (by omega) (by omega), readBuffer_of_mem_eq hsa_mem]
            exact hl1 idx hidx)
      have hrun_n1 : DetRun oracle (submission.image .commit) sa
          (if n + 1 < 2799 then 2000 * (n + 1) else 5597999) sm
          (if n + 1 < 2799 then 6662 * (n + 1) else 18646937) (666 * (n + 1)) := by
        have h := hrunn.trans hrun1
        have hs : 2000 * n + (1998 + if n + 1 < 2799 then 2 else 1) =
            if n + 1 < 2799 then 2000 * (n + 1) else 5597999 := by split <;> omega
        have hc : 6662 * n + (6660 + if n + 1 < 2799 then 2 else 1) =
            if n + 1 < 2799 then 6662 * (n + 1) else 18646937 := by split <;> omega
        rw [hs, hc, show 666 * n + 666 = 666 * (n + 1) by omega] at h
        exact h
      refine ⟨sm, hrun_n1, hpcm,
        fun r h10 h12 => (hregm r h10 h12).trans (hregn r h10 h12), hx10m, hx12m, ?_, ?_, ?_⟩
      · intro idx hidx
        by_cases hlt : idx < 666 * n
        · rw [← hdign idx hlt]
          have hgo : gapOffset idx + 32 ≤ 96 * (333 * n) := by unfold gapOffset; omega
          exact hpres1.readBuffer_eq (by omega) (by omega)
        · exact hdig1 idx (by omega) hidx
      · intro q hq j hj; exact (hgap1 q hq j hj).trans (hgapn q hq j hj)
      · exact (hpresn.mono (le_refl _) (by omega)).trans (hpres1.mono (by omega) (le_refl _))
  obtain ⟨sb, hrun_bulk, hpc_b, hreg_b, hx10_b, hx12_b, hdig_b, hgap_b, hpres_b⟩ := hbulk 2799 (le_refl _)
  simp only [Nat.lt_irrefl, ite_false] at hrun_bulk
  have hpc_b' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 59434) := by
    simpa only [Nat.lt_irrefl, ite_false] using hpc_b
  -- Final odd triplet (59434..59436, triplet 1,864,134 -> L2[1,864,134]): 3 steps, 10 cyc, 1 call
  let sf1 := execInstrBr sb (.ADDI .x10 .x10 (96#12))
  let sf2 := execInstrBr sf1 (.ADDI .x12 .x12 (64#12))
  let df := nodeVal c96 msg salts 2 1864134
  let sf3 := writeBits sf2 (BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * 932067)) df
  have hsf1_pc : sf1.pc = BitVec.ofNat 64 (0x1000 + 4 * 59435) := pc_step_idx sb 59434 hpc_b'
  have hsf2_pc : sf2.pc = BitVec.ofNat 64 (0x1000 + 4 * 59436) := pc_step_idx sf1 59435 hsf1_pc
  have hsf3_pc : sf3.pc = BitVec.ofNat 64 (0x1000 + 4 * 59437) := pc_step_idx sf2 59436 hsf2_pc
  have hsf2_mem : sf2.mem = sb.mem :=
    (mem_exec_ADDI sf1 .x12 .x12 (64#12)).trans (mem_exec_ADDI sb .x10 .x10 (96#12))
  have hsf2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sf2.getReg r = sb.getReg r := fun r h10 h12 => by
    simp only [sf2, sf1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
  have hsf3_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → sf3.getReg r = sb.getReg r := fun r h10 h12 =>
    (writeBits_register sf2 _ df r).trans (hsf2_reg_other r h10 h12)
  have hsf1_a0 : sf1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * 1864134) := by
    simp only [sf1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10_b,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD, hlb1])
  have hsf2_a0 : sf2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * 1864134) := by
    simp only [sf2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hsf1_a0]
  have hsf2_a2 : sf2.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * 932067) := by
    have h1x12 : sf1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * 932067 - 64) := by
      simp only [sf1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide), hx12_b]
    simp only [sf2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h1x12,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by rw [hC_TD, hlb2])
  have hsf2_in : readBuffer sf2 (C_TD + levelBase 1 + 96 * 1864134) 96 =
      ternaryInput (nodeVal c96 msg salts 1 5592402)
        (nodeVal c96 msg salts 1 5592403) (nodeVal c96 msg salts 1 5592404) := by
    rw [readBuffer_of_mem_eq hsf2_mem, hpres_b.readBuffer_eq (by omega) (by omega),
      readBuffer_of_mem_eq hsa_mem, readBuffer_ternary]
    have h0 := hl1 5592402 (by omega)
    have h1 := hl1 5592403 (by omega)
    have h2 := hl1 5592404 (by omega)
    have ha0 : C_TD + levelBase 1 + 96 * 1864134 = C_TD + levelBase 1 + 32 * 5592402 := by
      rw [hC_TD, hlb1]
    have ha1 : C_TD + levelBase 1 + 32 * 5592402 + 32 = C_TD + levelBase 1 + 32 * 5592403 := by
      rw [hC_TD, hlb1]
    have ha2 : C_TD + levelBase 1 + 32 * 5592402 + 64 = C_TD + levelBase 1 + 32 * 5592404 := by
      rw [hC_TD, hlb1]
    rw [ha0, ha1, ha2, h0, h1, h2]
  have hdf_eq : oracle.compression ((readBuffer sf2 (C_TD + levelBase 1 + 96 * 1864134) 96).cast h768.symm) = df := by
    rw [hsf2_in]; unfold df nodeVal nodeValFromLeaves
    simp only [show 1864134 < FULL_TRIPLETS_1 by omega, ite_true]; rfl
  have hfinal_call : DetRun oracle (submission.image .commit) sb 3 sf3 10 1 := by
    have hf1 : DetRun oracle (submission.image .commit) sb 1 sf1 1 0 :=
      DetRun.step1 (commit_fetch_commitMid2BInstr sb 59434 (by omega) (by omega) hpc_b') rfl
    have hf2 : DetRun oracle (submission.image .commit) sf1 1 sf2 1 0 :=
      DetRun.step1 (commit_fetch_commitMid2BInstr sf1 59435 (by omega) (by omega) hsf1_pc) rfl
    have hf3 : DetRun oracle (submission.image .commit) sf2 1 sf3 8 1 :=
      DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := sf2)
        (commit_fetch_commitMid2BInstr sf2 59436 (by omega) (by omega) hsf2_pc)
        ((hsf2_reg_other .x5 (by decide) (by decide)).trans ((hreg_b .x5 (by decide) (by decide)).trans hsa_x5))
        ((hsf2_reg_other .x11 (by decide) (by decide)).trans ((hreg_b .x11 (by decide) (by decide)).trans hsa_x11))
        ((hsf2_reg_other .x13 (by decide) (by decide)).trans ((hreg_b .x13 (by decide) (by decide)).trans hsa_x13))
        (C_TD + levelBase 1 + 96 * 1864134) (C_TD + levelBase 2 + 96 * 932067) hsf2_a0 hsf2_a2
        (by rw [hC_TD, hlb1]) (by rw [hC_TD, hlb2])
        (by rw [hC_TD, hMB, hlb1]; omega) (by rw [hC_TD, hMB, hlb2]; omega) df hdf_eq
    exact (hf1.trans hf2).trans hf3
  -- Promoted L1[5,592,405] copy (words 59437..59444: 4 ld/sd pairs = 8 steps, 8 cyc, 0 calls)
  have hsf3_a0 : sf3.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 1 + 96 * 1864134) :=
    (writeBits_register sf2 _ df .x10).trans hsf2_a0
  have hsf3_a2 : sf3.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase 2 + 96 * 932067) :=
    (writeBits_register sf2 _ df .x12).trans hsf2_a2
  obtain ⟨sfin, hprom_run, hsfin_pc, hsfin_reg, hsfin_dig, hprom_pres⟩ :=
    commit_copy32 oracle sf3 59437 .x10 .x12
      (C_TD + levelBase 1 + 96 * 1864134) (C_TD + levelBase 2 + 96 * 932067) 96 32
      (by decide) (by decide) (by decide) (by decide)
      (by rw [hC_TD, hlb1]) (by rw [hC_TD, hlb2])
      (by rw [hC_TD, hMB, hlb1]; omega) (by rw [hC_TD, hMB, hlb2]; omega)
      (by rw [hC_TD, hlb1, hlb2]; omega) hsf3_pc hsf3_a0 hsf3_a2
      (fun k hk st => by
        constructor
        · intro hpc'
          have h := commit_fetch_commitMid2BInstr st (59437 + 2 * k) (by omega) (by omega) hpc'
          interval_cases k <;> simpa only [commitMid2BInstr] using h
        · intro hpc'
          have h := commit_fetch_commitMid2BInstr st (59437 + 2 * k + 1) (by omega) (by omega) hpc'
          interval_cases k <;> simpa only [commitMid2BInstr] using h)
  have hsf3_pres : MemPreservedOutside sb sf3 (C_TD + levelBase 2 + 96 * 932067)
      (C_TD + levelBase 2 + 96 * 932067 + 32) :=
    (MemPreservedOutside.of_mem_eq hsf2_mem _ _).trans
      (memPreserved_writeBits sf2 (C_TD + levelBase 2 + 96 * 932067) df (by omega))
  have hreg_sfin : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sfin.getReg r = sa.getReg r :=
    fun r h6 h10 h12 => ((hsfin_reg r h6).trans (hsf3_reg_other r h10 h12)).trans (hreg_b r h10 h12)
  refine ⟨sfin, (((hsetup.trans hrun_bulk).trans hfinal_call).trans hprom_run), hsfin_pc,
    (hreg_sfin .x2 (by decide) (by decide) (by decide)).trans hsa_x2,
    (hreg_sfin .x5 (by decide) (by decide) (by decide)).trans hsa_x5,
    (hreg_sfin .x9 (by decide) (by decide) (by decide)).trans hsa_x9,
    (hreg_sfin .x11 (by decide) (by decide) (by decide)).trans hsa_x11,
    (hreg_sfin .x13 (by decide) (by decide) (by decide)).trans hsa_x13,
    (hreg_sfin .x26 (by decide) (by decide) (by decide)).trans hsa_x26, ?_, ?_, ?_⟩
  · intro idx hidx
    by_cases hlt : idx < 1864134
    · have hgo : gapOffset idx + 32 ≤ 96 * 932067 := by unfold gapOffset; omega
      rw [hprom_pres.readBuffer_eq (by omega) (by omega), hsf3_pres.readBuffer_eq (by omega) (by omega)]
      exact hdig_b idx hlt
    · by_cases h4 : idx = 1864134
      · subst h4
        have hgo : gapOffset 1864134 = 96 * 932067 := by decide
        rw [hgo, hprom_pres.readBuffer_eq (by omega) (by omega)]
        exact writeBits_readBuffer_digest sf2 _ df
      · have h5 : idx = 1864135 := by omega
        subst h5
        have hgo : gapOffset 1864135 = 96 * 932067 + 32 := by decide
        rw [hgo, ← Nat.add_assoc, hsfin_dig]
        have hsrc : C_TD + levelBase 1 + 96 * 1864134 + 96 = C_TD + levelBase 1 + 32 * 5592405 := by
          rw [hC_TD, hlb1]
        rw [hsrc, hsf3_pres.readBuffer_eq (by omega) (by omega), hpres_b.readBuffer_eq (by omega) (by omega),
            readBuffer_of_mem_eq hsa_mem, hl1 5592405 (by omega)]
        have hprom : ∀ (c : Comp96), nodeVal c msg salts 1 5592405 = nodeVal c msg salts 2 1864135 := by
          intro c; unfold nodeVal; symm; conv_lhs => rw [nodeValFromLeaves.eq_def]
          dsimp only; simp only [hft1, Nat.lt_irrefl, ite_false, ite_true]
        exact hprom c96
  · intro q hq j hj
    have h1 := hprom_pres (C_TD + levelBase 2 + 96 * q + 64 + j) (by omega) (by omega)
    have h2 := hsf3_pres (C_TD + levelBase 2 + 96 * q + 64 + j) (by omega) (by omega)
    exact ((h1.trans h2).trans (hgap_b q hq j hj)).trans (getByte_of_mem_eq hsa_mem _)
  · exact (((MemPreservedOutside.of_mem_eq hsa_mem _ _).trans
      (hpres_b.mono (le_refl _) (by omega))).trans
      (hsf3_pres.mono (by omega) (by omega))).trans
      (hprom_pres.mono (by omega) (by omega))

end CommitGolfCandidate
