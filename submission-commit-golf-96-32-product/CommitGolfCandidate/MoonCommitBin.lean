import CommitGolfCandidate.MoonCommitBinA

/-! Stage C and top-level driver proof (`commit_bin_level`, words `2632..3198`) for binary tree
levels `L2..L23` of the `commit` image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

private theorem pc_beq_2641 :
    BitVec.ofNat 64 (0x1000 + 4 * 2641) + signExtend13 (2072#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 3159) := by decide

private theorem pc_beq_3173 :
    BitVec.ofNat 64 (0x1000 + 4 * 3173) + signExtend13 (60#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 3188) := by decide

private theorem pc_beq_3178 :
    BitVec.ofNat 64 (0x1000 + 4 * 3178) + signExtend13 (76#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 3197) := by decide

private theorem pc_jal_3187 :
    BitVec.ofNat 64 (0x1000 + 4 * 3187) + signExtend21 (40#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 3197) := by decide

private theorem pc_beq_3188 :
    BitVec.ofNat 64 (0x1000 + 4 * 3188) + signExtend13 (36#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 3197) := by decide

private theorem pc_bne_3198 :
    BitVec.ofNat 64 (0x1000 + 4 * 3198) + signExtend13 (5928#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 2632) := by decide

private theorem commit_fetch_copy32_odd_prom (k : Nat) (hk : k < 4) (st : MachineState) :
    (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (3179 + 2 * k)) →
      fetch (submission.image .commit) st = some (.base (.LD .x6 .x10 (BitVec.ofNat 12 (96 + 8 * k))))) ∧
    (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (3179 + 2 * k + 1)) →
      fetch (submission.image .commit) st = some (.base (.SD .x12 .x6 (BitVec.ofNat 12 (32 + 8 * k))))) := by
  constructor
  · intro hpc'
    have h := commit_fetch_commitTailInstr st (3179 + 2 * k) (by omega) (by omega) hpc'
    interval_cases k <;> simpa only [commitTailInstr] using h
  · intro hpc'
    have h := commit_fetch_commitTailInstr st (3179 + 2 * k + 1) (by omega) (by omega) hpc'
    interval_cases k <;> simpa only [commitTailInstr] using h

private theorem commit_fetch_copy32_even_prom (k : Nat) (hk : k < 4) (st : MachineState) :
    (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (3189 + 2 * k)) →
      fetch (submission.image .commit) st = some (.base (.LD .x6 .x10 (BitVec.ofNat 12 (96 + 8 * k))))) ∧
    (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (3189 + 2 * k + 1)) →
      fetch (submission.image .commit) st = some (.base (.SD .x12 .x6 (BitVec.ofNat 12 (64 + 8 * k))))) := by
  constructor
  · intro hpc'
    have h := commit_fetch_commitTailInstr st (3189 + 2 * k) (by omega) (by omega) hpc'
    interval_cases k <;> simpa only [commitTailInstr] using h
  · intro hpc'
    have h := commit_fetch_commitTailInstr st (3189 + 2 * k + 1) (by omega) (by omega) hpc'
    interval_cases k <;> simpa only [commitTailInstr] using h

/-- Stage C odd-call branch (words `3174..3187`): 1 masked call + optional promoted copy. -/
private theorem commit_bin_stageC_odd (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128)
    (lvlIdx calls prom chunks remPairs : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hprom : prom = levelSize (lvlIdx + 1) % 2)
    (hchunks : chunks = calls / 128)
    (hrem : remPairs = (calls % 128) / 2)
    (hodd : calls % 2 = 1)
    (s0 c1 : MachineState)
    (hc1_pc : c1.pc = BitVec.ofNat 64 (0x1000 + 4 * 3174))
    (hx5 : c1.getReg .x5 = 0#64) (hx11 : c1.getReg .x11 = 96#64) (hx13 : c1.getReg .x13 = 0#64)
    (hx21 : c1.getReg .x21 = BitVec.ofNat 64 prom)
    (hx10 : c1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks + 2 * remPairs) - 96))
    (hx12 : c1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + remPairs) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 1) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64) 32 = 0)
    (hdigT : ∀ idx < 128 * chunks + 2 * remPairs,
      readBuffer c1 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hgapT : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
      c1.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)))
    (hpresT : MemPreservedOutside s0 c1 (C_TD + levelBase (lvlIdx + 2))
      (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + remPairs))) :
    ∃ sc,
      DetRun oracle (submission.image .commit) c1 (5 + 9 * prom) sc (12 + 9 * prom) 1 ∧
      sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 3197) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sc.getReg r = c1.getReg r) ∧
      (∀ idx < levelSize (lvlIdx + 2),
        readBuffer sc (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx) ∧
      (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
        sc.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 sc (C_TD + levelBase (lvlIdx + 2)) (C_TD + levelBase (lvlIdx + 3)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let qOdd := 64 * chunks + remPairs
  have hqOdd_eq : 2 * qOdd = calls - 1 := by omega
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  have hdstSize_eq : levelSize (lvlIdx + 2) = (levelSize (lvlIdx + 1) + 1) / 2 :=
    levelSize_step (lvlIdx + 1) (by omega)
  have hdstSize_eq' : levelSize (lvlIdx + 2) = calls + prom := by omega
  have hsrcB := levelBase_bound (lvlIdx + 1) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 2) (by omega)
  have htb := treeBytes_eq
  have hsrcAl := levelBase_mod8 (lvlIdx + 1) (by omega)
  have hdstAl := levelBase_mod8 (lvlIdx + 2) (by omega)
  have hsrcBytes := levelBytes_eq_gap (lvlIdx + 1) (by omega) (by omega)
  have hdstBytes := levelBytes_eq_gap (lvlIdx + 2) (by omega) (by omega)
  have hbase_step : levelBase (lvlIdx + 2) = levelBase (lvlIdx + 1) + levelBytes (lvlIdx + 1) := rfl
  have hbase_next : levelBase (lvlIdx + 3) = levelBase (lvlIdx + 2) + levelBytes (lvlIdx + 2) := rfl
  let o1 := execInstrBr c1 (.ADDI .x10 .x10 (96#12))
  let o2 := execInstrBr o1 (.ADDI .x12 .x12 (64#12))
  let rawOdd := c96 (binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (2 * (calls - 1)))
    (nodeVal c96 msg salts (lvlIdx + 1) (2 * (calls - 1) + 1)))
  let o3 := writeBits o2 (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd)) rawOdd
  let o4 := execInstrBr o3 (.SH .x12 .x0 (30#12))
  let o5 := execInstrBr o4 (.BEQ .x21 .x0 (76#13))
  have ho1_pc : o1.pc = BitVec.ofNat 64 (0x1000 + 4 * 3175) := pc_step_idx c1 3174 hc1_pc
  have ho2_pc : o2.pc = BitVec.ofNat 64 (0x1000 + 4 * 3176) := pc_step_idx o1 3175 ho1_pc
  have ho3_pc : o3.pc = BitVec.ofNat 64 (0x1000 + 4 * 3177) := pc_step_idx o2 3176 ho2_pc
  have ho4_pc : o4.pc = BitVec.ofNat 64 (0x1000 + 4 * 3178) := pc_step_idx o3 3177 ho3_pc
  have ho2_mem : o2.mem = c1.mem := (mem_exec_ADDI o1 _ _ _).trans (mem_exec_ADDI c1 _ _ _)
  have ho2_reg_other : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → o2.getReg r = c1.getReg r := fun r h10 h12 => by
    simp only [o2, o1, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10)]
  have ho1_a0 : o1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (calls - 1)) := by
    simp only [o1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ 96 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have ho2_a0 : o2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (calls - 1)) := by
    simp only [o2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), ho1_a0]
  have ho2_a2 : o2.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd) := by
    have h1x12 : o1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd - 64) := by
      have hstep : o1.getReg .x12 = c1.getReg .x12 := by
        simp only [o1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x12 (by decide)]
      exact hstep.trans hx12
    simp only [o2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h1x12,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have ho2_in : readBuffer o2 (C_TD + levelBase (lvlIdx + 1) + 96 * (calls - 1)) 96 =
      binaryInput (nodeVal c96 msg salts (lvlIdx + 1) (2 * (calls - 1)))
        (nodeVal c96 msg salts (lvlIdx + 1) (2 * (calls - 1) + 1)) := by
    have hsrc_bd : 96 * (calls - 1) + 96 ≤ levelBytes (lvlIdx + 1) := by rw [hsrcBytes]; omega
    rw [readBuffer_of_mem_eq ho2_mem, hpresT.readBuffer_eq (by omega) (by omega),
      readBuffer_binary_of_zero_gap s0 _ (hsrcGap (calls - 1) (by omega))]
    have h0 := hsrc (2 * (calls - 1)) (by omega)
    have h1 := hsrc (2 * (calls - 1) + 1) (by omega)
    rw [gapOffset_even] at h0
    rw [gapOffset_odd, ← Nat.add_assoc] at h1
    rw [h0, h1]
  have ho3_a2 : o3.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd) :=
    (writeBits_register o2 _ rawOdd .x12).trans ho2_a2
  have hsh_addr : o3.getReg .x12 + signExtend12 (30#12) =
      BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd + 30) := by
    rw [ho3_a2, add_signExtend12_ofNat_small _ 30 (by omega)]
  have hdst_bd : 96 * qOdd + 32 ≤ levelBytes (lvlIdx + 2) := by rw [hdstBytes, hdstSize_eq']; omega
  have hsrc_bd : 96 * (calls - 1) + 96 ≤ levelBytes (lvlIdx + 1) := by rw [hsrcBytes]; omega
  have hodd_run5 : DetRun oracle (submission.image .commit) c1 5 o5 12 1 := by
    have ro1 : DetRun oracle (submission.image .commit) c1 1 o1 1 0 :=
      commit_step1_tail (by omega) (by omega) hc1_pc (by simp only [commitTailInstr])
    have ro2 : DetRun oracle (submission.image .commit) o1 1 o2 1 0 :=
      commit_step1_tail (by omega) (by omega) ho1_pc (by simp only [commitTailInstr])
    have hf3176 : fetch (submission.image .commit) o2 = some (.base .ECALL) := by
      have h := commit_fetch_commitTailInstr o2 3176 (by omega) (by omega) ho2_pc
      simp only [commitTailInstr] at h
      exact h
    have ro3 : DetRun oracle (submission.image .commit) o2 1 o3 8 1 :=
      DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := o2) hf3176
        ((ho2_reg_other .x5 (by decide) (by decide)).trans hx5)
        ((ho2_reg_other .x11 (by decide) (by decide)).trans hx11)
        ((ho2_reg_other .x13 (by decide) (by decide)).trans hx13)
        (C_TD + levelBase (lvlIdx + 1) + 96 * (calls - 1)) (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd)
        ho2_a0 ho2_a2 (by omega) (by omega) (by omega) (by omega) rawOdd (by rw [ho2_in])
    have ro4 : DetRun oracle (submission.image .commit) o3 1 o4 1 0 :=
      commit_step1_tail (by omega) (by omega) ho3_pc (by simp only [commitTailInstr])
        (ordinaryStep_SH o3 .x12 .x0 (30#12) (by
          rw [hsh_addr]; exact c_accessValid_ofNat _ 2 (by omega) (by omega)))
    have ro5 : DetRun oracle (submission.image .commit) o4 1 o5 1 0 :=
      commit_step1_tail (by omega) (by omega) ho4_pc (by simp only [commitTailInstr])
    exact (((ro1.trans ro2).trans ro3).trans ro4).trans ro5
  have ho4_mem : o4.mem =
      (o3.setHalfword (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd + 30)) 0#16).mem := by
    simp only [o4, execInstrBr, hsh_addr, c_getReg_x0, c_mem_setPC]; rfl
  have ho5_mem_o4 : o5.mem = o4.mem := mem_exec_BEQ o4 .x21 .x0 (76#13)
  have ho5_mem : o5.mem =
      (o3.setHalfword (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd + 30)) 0#16).mem :=
    ho5_mem_o4.trans ho4_mem
  have ho5_pres : MemPreservedOutside c1 o5 (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd)
      (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd + 32) := by
    have h23 : MemPreservedOutside o2 o3 (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd)
        (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd + 32) := memPreserved_writeBits o2 _ rawOdd (by omega)
    have h34 : MemPreservedOutside o3 o4 (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd)
        (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd + 32) :=
      ((memPreserved_setHalfword o3 _ 0#16 (by omega) (by omega)).mono (by omega) (by omega)).trans
        (MemPreservedOutside.of_mem_eq ho4_mem _ _)
    have h45 : MemPreservedOutside o4 o5 (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd)
        (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd + 32) :=
      MemPreservedOutside.of_mem_eq ho5_mem_o4 _ _
    exact ((MemPreservedOutside.of_mem_eq ho2_mem _ _).trans h23).trans (h34.trans h45)
  have ho5_dig : ∀ idx < calls, readBuffer o5 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
      nodeVal c96 msg salts (lvlIdx + 2) idx := by
    intro idx hidx
    by_cases hold : idx < calls - 1
    · have hgo : gapOffset idx + 32 ≤ 96 * qOdd := by unfold gapOffset; omega
      rw [ho5_pres.readBuffer_eq (by omega) (by omega)]
      exact hdigT idx (by omega)
    · have heq : idx = calls - 1 := by omega
      subst heq
      rw [show gapOffset (calls - 1) = 96 * qOdd by rw [← hqOdd_eq, gapOffset_even],
        readBuffer_of_mem_eq ho5_mem,
        sh_zero_mask240 o3 _ (by omega) (by omega), writeBits_readBuffer_digest]
      exact nodeVal_bin_masked c96 msg salts lvlIdx (calls - 1) (by omega) (by omega)
  have ho5_gap : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
      o5.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) := by
    intro q hq j hj
    have hsep : C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j <
          C_TD + levelBase (lvlIdx + 2) + 96 * qOdd ∨
        C_TD + levelBase (lvlIdx + 2) + 96 * qOdd + 32 ≤
          C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j := by omega
    exact (ho5_pres (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)
      (by rw [hdstBytes] at hdstB; omega) hsep).trans (hgapT q hq j hj)
  have ho5_reg : ∀ r : Reg, r ≠ .x10 → r ≠ .x12 → o5.getReg r = c1.getReg r := fun r h10 h12 => by
    rw [reg_exec_BEQ o4 _ _ _ r, reg_exec_SH o3 _ _ _ r, writeBits_register o2 _ rawOdd r,
      ho2_reg_other r h10 h12]
  have ho4_x21 : o4.getReg .x21 = BitVec.ofNat 64 prom := by
    rw [← reg_exec_BEQ o4 .x21 .x0 (76#13) .x21, ho5_reg .x21 (by decide) (by decide)]; exact hx21
  have ho5_pres_all : MemPreservedOutside s0 o5 (C_TD + levelBase (lvlIdx + 2)) (C_TD + levelBase (lvlIdx + 3)) :=
    (hpresT.mono (le_refl _) (by omega)).trans (ho5_pres.mono (by omega) (by omega))
  by_cases hpr : prom = 1
  · have hne_pr : (o4.getReg .x21 == o4.getReg .x0) = false := by
      rw [ho4_x21, hpr, c_getReg_x0]; decide
    have ho5_pc : o5.pc = BitVec.ofNat 64 (0x1000 + 4 * 3179) := by
      simp only [o5, execInstrBr, hne_pr, Bool.false_eq_true, ite_false, pc_setPC]
      exact pc_step_idx o4 3178 ho4_pc
    have hsrc_bd' : 96 * (calls - 1) + 96 + 32 ≤ levelBytes (lvlIdx + 1) := by rw [hsrcBytes]; omega
    have hdst_bd' : 96 * qOdd + 32 + 32 ≤ levelBytes (lvlIdx + 2) := by rw [hdstBytes, hdstSize_eq']; omega
    obtain ⟨oc, hcopy_run, hoc_pc, hoc_reg, hoc_dig, hoc_pres⟩ :=
      commit_copy32 oracle o5 3179 .x10 .x12
        (C_TD + levelBase (lvlIdx + 1) + 96 * (calls - 1)) (C_TD + levelBase (lvlIdx + 2) + 96 * qOdd) 96 32
        (by decide) (by decide) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) ho5_pc
        (((reg_exec_BEQ o4 _ _ _ .x10).trans (reg_exec_SH o3 _ _ _ .x10)).trans
          ((writeBits_register o2 _ rawOdd .x10).trans ho2_a0))
        ((reg_exec_BEQ o4 _ _ _ .x12).trans ((reg_exec_SH o3 _ _ _ .x12).trans ho3_a2))
        commit_fetch_copy32_odd_prom
    let ojal := execInstrBr oc (.JAL .x0 (40#21))
    have hjal_run : DetRun oracle (submission.image .commit) oc 1 ojal 1 0 :=
      commit_step1_tail (by omega) (by omega) hoc_pc (by simp only [commitTailInstr])
    have hmem_jal : ojal.mem = oc.mem := mem_exec_JAL oc .x0 (40#21)
    have hreg_jal : ∀ r, ojal.getReg r = oc.getReg r := reg_exec_JAL0 oc (40#21)
    have hrun_out : DetRun oracle (submission.image .commit) c1 (5 + 9 * prom) ojal (12 + 9 * prom) 1 := by
      have h := (hodd_run5.trans hcopy_run).trans hjal_run
      rw [show 5 + 9 * prom = 5 + 8 + 1 by omega, show 12 + 9 * prom = 12 + 8 + 1 by omega]
      exact h
    refine ⟨ojal, hrun_out,
      by simp only [ojal, execInstrBr, pc_setPC, hoc_pc]; exact pc_jal_3187,
      fun r h6 h10 h12 => ((hreg_jal r).trans (hoc_reg r h6)).trans (ho5_reg r h10 h12), ?_, ?_, ?_⟩
    · intro idx hidx
      rw [readBuffer_of_mem_eq hmem_jal]
      by_cases hold : idx < calls
      · have hgo : gapOffset idx + 32 ≤ 96 * qOdd + 32 := by unfold gapOffset; omega
        rw [hoc_pres.readBuffer_eq (by omega) (by omega)]
        exact ho5_dig idx hold
      · have heq : idx = calls := by omega
        subst idx
        have hgo : gapOffset calls = 96 * qOdd + 32 := by unfold gapOffset; omega
        rw [hgo, ← Nat.add_assoc, hoc_dig, ho5_pres_all.readBuffer_eq (by omega) (by omega)]
        have hsrc_eq : C_TD + levelBase (lvlIdx + 1) + 96 * (calls - 1) + 96 =
            C_TD + levelBase (lvlIdx + 1) + gapOffset (2 * calls) := by rw [gapOffset_even]; omega
        rw [hsrc_eq, hsrc (2 * calls) (by omega)]
        exact nodeVal_bin_promoted c96 msg salts lvlIdx calls (by omega) (by omega)
    · intro q hq j hj
      rw [getByte_of_mem_eq hmem_jal]
      have hsep : C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j <
            C_TD + levelBase (lvlIdx + 2) + 96 * qOdd + 32 ∨
          C_TD + levelBase (lvlIdx + 2) + 96 * qOdd + 32 + 32 ≤
            C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j := by omega
      exact (hoc_pres (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)
        (by rw [hdstBytes] at hdstB; omega) hsep).trans (ho5_gap q hq j hj)
    · exact (ho5_pres_all.trans (hoc_pres.mono (by omega) (by omega))).trans
        (MemPreservedOutside.of_mem_eq hmem_jal _ _)
  · have hpr0 : prom = 0 := by omega
    have heq_pr : (o4.getReg .x21 == o4.getReg .x0) = true := by
      rw [ho4_x21, hpr0, c_getReg_x0]; exact beq_self_eq_true _
    have ho5_pc : o5.pc = BitVec.ofNat 64 (0x1000 + 4 * 3197) := by
      simp only [o5, execInstrBr, heq_pr, ite_true, pc_setPC, ho4_pc]
      exact pc_beq_3178
    have hrun_out : DetRun oracle (submission.image .commit) c1 (5 + 9 * prom) o5 (12 + 9 * prom) 1 := by
      rw [show 5 + 9 * prom = 5 by omega, show 12 + 9 * prom = 12 by omega]
      exact hodd_run5
    exact ⟨o5, hrun_out, ho5_pc, fun r _ h10 h12 => ho5_reg r h10 h12,
      fun idx hidx => ho5_dig idx (by omega), ho5_gap, ho5_pres_all⟩

/-- Stage C even-call branch (words `3188..3196`): optional promoted copy only. -/
private theorem commit_bin_stageC_even (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128)
    (lvlIdx calls prom chunks remPairs : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hprom : prom = levelSize (lvlIdx + 1) % 2)
    (hchunks : chunks = calls / 128)
    (hrem : remPairs = (calls % 128) / 2)
    (hodd0 : calls % 2 = 0)
    (s0 c1 : MachineState)
    (hc1_pc : c1.pc = BitVec.ofNat 64 (0x1000 + 4 * 3188))
    (hx21 : c1.getReg .x21 = BitVec.ofNat 64 prom)
    (hx10 : c1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks + 2 * remPairs) - 96))
    (hx12 : c1.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + remPairs) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hdigT : ∀ idx < 128 * chunks + 2 * remPairs,
      readBuffer c1 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hgapT : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
      c1.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)))
    (hpresT : MemPreservedOutside s0 c1 (C_TD + levelBase (lvlIdx + 2))
      (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + remPairs))) :
    ∃ sc,
      DetRun oracle (submission.image .commit) c1 (1 + 8 * prom) sc (1 + 8 * prom) 0 ∧
      sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 3197) ∧
      (∀ r : Reg, r ≠ .x6 → sc.getReg r = c1.getReg r) ∧
      (∀ idx < levelSize (lvlIdx + 2),
        readBuffer sc (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx) ∧
      (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
        sc.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 sc (C_TD + levelBase (lvlIdx + 2)) (C_TD + levelBase (lvlIdx + 3)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  have hdstSize_eq : levelSize (lvlIdx + 2) = (levelSize (lvlIdx + 1) + 1) / 2 :=
    levelSize_step (lvlIdx + 1) (by omega)
  have hdstSize_eq' : levelSize (lvlIdx + 2) = calls + prom := by omega
  have hsrcB := levelBase_bound (lvlIdx + 1) (by omega)
  have hdstB := levelBase_bound (lvlIdx + 2) (by omega)
  have htb := treeBytes_eq
  have hsrcAl := levelBase_mod8 (lvlIdx + 1) (by omega)
  have hdstAl := levelBase_mod8 (lvlIdx + 2) (by omega)
  have hsrcBytes := levelBytes_eq_gap (lvlIdx + 1) (by omega) (by omega)
  have hdstBytes := levelBytes_eq_gap (lvlIdx + 2) (by omega) (by omega)
  have hbase_step : levelBase (lvlIdx + 2) = levelBase (lvlIdx + 1) + levelBytes (lvlIdx + 1) := rfl
  have hbase_next : levelBase (lvlIdx + 3) = levelBase (lvlIdx + 2) + levelBytes (lvlIdx + 2) := rfl
  let c2 := execInstrBr c1 (.BEQ .x21 .x0 (36#13))
  have hc2_run : DetRun oracle (submission.image .commit) c1 1 c2 1 0 :=
    commit_step1_tail (by omega) (by omega) hc1_pc (by simp only [commitTailInstr])
  have hc2_mem : c2.mem = c1.mem := mem_exec_BEQ c1 _ _ _
  have hc2_reg : ∀ r : Reg, c2.getReg r = c1.getReg r := reg_exec_BEQ c1 _ _ _
  have hc2_pres_all : MemPreservedOutside s0 c2 (C_TD + levelBase (lvlIdx + 2)) (C_TD + levelBase (lvlIdx + 3)) := by
    have hdst_bd : 96 * (64 * chunks + remPairs) ≤ levelBytes (lvlIdx + 2) := by
      rw [hdstBytes, hdstSize_eq']; omega
    exact (hpresT.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hc2_mem _ _)
  by_cases hpr : prom = 1
  · have hne_pr : (c1.getReg .x21 == c1.getReg .x0) = false := by
      rw [hx21, hpr, c_getReg_x0]; decide
    have hc2_pc : c2.pc = BitVec.ofNat 64 (0x1000 + 4 * 3189) := by
      simp only [c2, execInstrBr, hne_pr, Bool.false_eq_true, ite_false, pc_setPC]
      exact pc_step_idx c1 3188 hc1_pc
    let qEv := 64 * chunks + remPairs
    have hqEv_eq : 2 * qEv = calls := by omega
    have hsrc_bd : 96 * calls + 32 ≤ levelBytes (lvlIdx + 1) := by rw [hsrcBytes]; omega
    have hdst_bd : 96 * qEv + 32 ≤ levelBytes (lvlIdx + 2) := by rw [hdstBytes, hdstSize_eq']; omega
    obtain ⟨oc, hcopy_run, hoc_pc, hoc_reg, hoc_dig, hoc_pres⟩ :=
      commit_copy32 oracle c2 3189 .x10 .x12
        (C_TD + levelBase (lvlIdx + 1) + 96 * calls - 96) (C_TD + levelBase (lvlIdx + 2) + 96 * qEv - 64) 96 64
        (by decide) (by decide) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) hc2_pc
        (by rw [hc2_reg .x10, hx10]; exact congrArg (BitVec.ofNat 64) (by omega))
        ((hc2_reg .x12).trans hx12)
        commit_fetch_copy32_even_prom
    have hd_add : C_TD + levelBase (lvlIdx + 2) + 96 * qEv - 64 + 64 =
        C_TD + levelBase (lvlIdx + 2) + 96 * qEv := by omega
    have hs_add : C_TD + levelBase (lvlIdx + 1) + 96 * calls - 96 + 96 =
        C_TD + levelBase (lvlIdx + 1) + 96 * calls := by omega
    rw [hd_add] at hoc_dig hoc_pres
    rw [hs_add] at hoc_dig
    have hrun_out : DetRun oracle (submission.image .commit) c1 (1 + 8 * prom) oc (1 + 8 * prom) 0 := by
      have h := hc2_run.trans hcopy_run
      rw [show 1 + 8 * prom = 1 + 8 by omega]
      exact h
    refine ⟨oc, hrun_out, hoc_pc, fun r h6 => (hoc_reg r h6).trans (hc2_reg r), ?_, ?_, ?_⟩
    · intro idx hidx
      by_cases hold : idx < calls
      · have hgo : gapOffset idx + 32 ≤ 96 * qEv := by unfold gapOffset; omega
        rw [hoc_pres.readBuffer_eq (by omega) (by omega), readBuffer_of_mem_eq hc2_mem]
        exact hdigT idx (by omega)
      · have heq : idx = calls := by omega
        subst idx
        have hgo : gapOffset calls = 96 * qEv := by unfold gapOffset; omega
        rw [hgo, hoc_dig, hc2_pres_all.readBuffer_eq (by omega) (by omega)]
        have hsrc_eq : C_TD + levelBase (lvlIdx + 1) + 96 * calls =
            C_TD + levelBase (lvlIdx + 1) + gapOffset (2 * calls) := by rw [gapOffset_even]
        rw [hsrc_eq, hsrc (2 * calls) (by omega)]
        exact nodeVal_bin_promoted c96 msg salts lvlIdx calls (by omega) (by omega)
    · intro q hq j hj
      have hsep : C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j <
            C_TD + levelBase (lvlIdx + 2) + 96 * qEv ∨
          C_TD + levelBase (lvlIdx + 2) + 96 * qEv + 32 ≤
            C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j := by omega
      rw [hoc_pres (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)
        (by rw [hdstBytes] at hdstB; omega) hsep, getByte_of_mem_eq hc2_mem]
      exact hgapT q hq j hj
    · exact hc2_pres_all.trans (hoc_pres.mono (by omega) (by omega))
  · have hpr0 : prom = 0 := by omega
    have heq_pr : (c1.getReg .x21 == c1.getReg .x0) = true := by
      rw [hx21, hpr0, c_getReg_x0]; exact beq_self_eq_true _
    have hc2_pc : c2.pc = BitVec.ofNat 64 (0x1000 + 4 * 3197) := by
      simp only [c2, execInstrBr, heq_pr, ite_true, pc_setPC, hc1_pc]
      exact pc_beq_3188
    have hrun_out : DetRun oracle (submission.image .commit) c1 (1 + 8 * prom) c2 (1 + 8 * prom) 0 := by
      rw [show 1 + 8 * prom = 1 by omega]
      exact hc2_run
    refine ⟨c2, hrun_out, hc2_pc, fun r _ => hc2_reg r, ?_, ?_, hc2_pres_all⟩
    · intro idx hidx
      rw [readBuffer_of_mem_eq hc2_mem]
      exact hdigT idx (by omega)
    · intro q hq j hj
      rw [getByte_of_mem_eq hc2_mem]
      exact hgapT q hq j hj

/-- Stage C of `commit_bin_level`: odd call + optional promoted node (`words 3172..3196`). -/
private theorem commit_bin_level_stageC (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128)
    (lvlIdx calls prom chunks remPairs oddCall : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hprom : prom = levelSize (lvlIdx + 1) % 2)
    (hchunks : chunks = calls / 128)
    (hrem : remPairs = (calls % 128) / 2)
    (hodd_def : oddCall = calls % 2)
    (s0 st : MachineState)
    (hpcT : st.pc = BitVec.ofNat 64 (0x1000 + 4 * 3172))
    (hx5T : st.getReg .x5 = 0#64) (hx11T : st.getReg .x11 = 96#64) (hx13T : st.getReg .x13 = 0#64)
    (hx20T : st.getReg .x20 = BitVec.ofNat 64 calls)
    (hx21T : st.getReg .x21 = BitVec.ofNat 64 prom)
    (hx10T : st.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) + 96 * (128 * chunks + 2 * remPairs) - 96))
    (hx12T : st.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + remPairs) - 64))
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 1) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64) 32 = 0)
    (hdigT : ∀ idx < 128 * chunks + 2 * remPairs,
      readBuffer st (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx)
    (hgapT : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
      st.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)))
    (hpresT : MemPreservedOutside s0 st (C_TD + levelBase (lvlIdx + 2))
      (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + remPairs))) :
    ∃ sc,
      DetRun oracle (submission.image .commit) st
        (if oddCall = 1 then 7 + 9 * prom else 3 + 8 * prom) sc
        (if oddCall = 1 then 14 + 9 * prom else 3 + 8 * prom) oddCall ∧
      sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 3197) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x22 → sc.getReg r = st.getReg r) ∧
      (∀ idx < levelSize (lvlIdx + 2),
        readBuffer sc (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx) ∧
      (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
        sc.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 sc (C_TD + levelBase (lvlIdx + 2)) (C_TD + levelBase (lvlIdx + 3)) := by
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  let c0 := execInstrBr st (.ANDI .x22 .x20 (1#12))
  let c1 := execInstrBr c0 (.BEQ .x22 .x0 (60#13))
  have hc0_pc : c0.pc = BitVec.ofNat 64 (0x1000 + 4 * 3173) := pc_step_idx st 3172 hpcT
  have hc_run2 : DetRun oracle (submission.image .commit) st 2 c1 2 0 := by
    have rc0 : DetRun oracle (submission.image .commit) st 1 c0 1 0 :=
      commit_step1_tail (by omega) (by omega) hpcT (by simp only [commitTailInstr])
    have rc1 : DetRun oracle (submission.image .commit) c0 1 c1 1 0 :=
      commit_step1_tail (by omega) (by omega) hc0_pc (by simp only [commitTailInstr])
    exact rc0.trans rc1
  have hc0_x22 : c0.getReg .x22 = BitVec.ofNat 64 oddCall := by
    simp only [c0, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), hx20T]
    exact (bv64_and_1 calls (by omega)).trans (congrArg (BitVec.ofNat 64) hodd_def.symm)
  have hc1_mem : c1.mem = st.mem := (mem_exec_BEQ c0 _ _ _).trans (mem_exec_ANDI st _ _ _)
  have hc1_reg : ∀ r : Reg, r ≠ .x22 → c1.getReg r = st.getReg r := fun r hr => by
    rw [reg_exec_BEQ c0 _ _ _ r]
    simp only [c0, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 r (Ne.symm hr)]
  have hdig1 : ∀ idx < 128 * chunks + 2 * remPairs,
      readBuffer c1 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx := fun idx hidx => by
    rw [readBuffer_of_mem_eq hc1_mem]; exact hdigT idx hidx
  have hgap1 : ∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
      c1.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
      s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) := fun q hq j hj => by
    rw [getByte_of_mem_eq hc1_mem]; exact hgapT q hq j hj
  have hpres1 : MemPreservedOutside s0 c1 (C_TD + levelBase (lvlIdx + 2))
      (C_TD + levelBase (lvlIdx + 2) + 96 * (64 * chunks + remPairs)) :=
    hpresT.trans (MemPreservedOutside.of_mem_eq hc1_mem _ _)
  by_cases hodd : oddCall = 1
  · have hne0 : (c0.getReg .x22 == c0.getReg .x0) = false := by
      rw [hc0_x22, hodd, c_getReg_x0]; decide
    have hc1_pc : c1.pc = BitVec.ofNat 64 (0x1000 + 4 * 3174) := by
      simp only [c1, execInstrBr, hne0, Bool.false_eq_true, ite_false, pc_setPC]
      exact pc_step_idx c0 3173 hc0_pc
    obtain ⟨sc, hrunO, hpcC, hregO, hdigC, hgapC, hpresC⟩ :=
      commit_bin_stageC_odd h768 oracle msg salts lvlIdx calls prom chunks remPairs hlvl
        hcalls hprom hchunks hrem (by omega) s0 c1 hc1_pc
        ((hc1_reg .x5 (by decide)).trans hx5T)
        ((hc1_reg .x11 (by decide)).trans hx11T)
        ((hc1_reg .x13 (by decide)).trans hx13T)
        ((hc1_reg .x21 (by decide)).trans hx21T)
        ((hc1_reg .x10 (by decide)).trans hx10T)
        ((hc1_reg .x12 (by decide)).trans hx12T)
        hsrc hsrcGap hdig1 hgap1 hpres1
    have hrun_all : DetRun oracle (submission.image .commit) st
        (if oddCall = 1 then 7 + 9 * prom else 3 + 8 * prom) sc
        (if oddCall = 1 then 14 + 9 * prom else 3 + 8 * prom) oddCall := by
      have h := hc_run2.trans hrunO
      rw [show (if oddCall = 1 then 7 + 9 * prom else 3 + 8 * prom) = 2 + (5 + 9 * prom) by
            simp only [hodd, ite_true]; omega,
          show (if oddCall = 1 then 14 + 9 * prom else 3 + 8 * prom) = 2 + (12 + 9 * prom) by
            simp only [hodd, ite_true]; omega,
          show oddCall = 0 + 1 by omega]
      exact h
    exact ⟨sc, hrun_all, hpcC, fun r h6 h10 h12 h22 => (hregO r h6 h10 h12).trans (hc1_reg r h22),
      hdigC, hgapC, hpresC⟩
  · have hodd0 : oddCall = 0 := by omega
    have heq0 : (c0.getReg .x22 == c0.getReg .x0) = true := by
      rw [hc0_x22, hodd0, c_getReg_x0]; exact beq_self_eq_true _
    have hc1_pc : c1.pc = BitVec.ofNat 64 (0x1000 + 4 * 3188) := by
      simp only [c1, execInstrBr, heq0, ite_true, pc_setPC, hc0_pc]
      exact pc_beq_3173
    obtain ⟨sc, hrunE, hpcC, hregE, hdigC, hgapC, hpresC⟩ :=
      commit_bin_stageC_even h768 oracle msg salts lvlIdx calls prom chunks remPairs hlvl
        hcalls hprom hchunks hrem (by omega) s0 c1 hc1_pc
        ((hc1_reg .x21 (by decide)).trans hx21T)
        ((hc1_reg .x10 (by decide)).trans hx10T)
        ((hc1_reg .x12 (by decide)).trans hx12T)
        hsrc hdig1 hgap1 hpres1
    have hrun_all : DetRun oracle (submission.image .commit) st
        (if oddCall = 1 then 7 + 9 * prom else 3 + 8 * prom) sc
        (if oddCall = 1 then 14 + 9 * prom else 3 + 8 * prom) oddCall := by
      have h := hc_run2.trans hrunE
      rw [show (if oddCall = 1 then 7 + 9 * prom else 3 + 8 * prom) = 2 + (1 + 8 * prom) by
            simp only [hodd, ite_false]; omega,
          show (if oddCall = 1 then 14 + 9 * prom else 3 + 8 * prom) = 2 + (1 + 8 * prom) by
            simp only [hodd, ite_false]; omega,
          show oddCall = 0 + 0 by omega]
      exact h
    exact ⟨sc, hrun_all, hpcC, fun r h6 _ _ h22 => (hregE r h6).trans (hc1_reg r h22),
      hdigC, hgapC, hpresC⟩

private theorem bv64_add_neg96 (n : Nat) (hn : 96 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4000#12) = BitVec.ofNat 64 (n - 96) := by
  have h : (4000#12 : BitVec 12) = BitVec.ofNat 12 (4096 - 96) := by decide
  rw [h]
  exact add_signExtend12_neg' n 96 (by omega) (by omega) hn

private theorem bv64_add_neg64 (n : Nat) (hn : 64 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4032#12) = BitVec.ofNat 64 (n - 64) := by
  have h : (4032#12 : BitVec 12) = BitVec.ofNat 12 (4096 - 64) := by decide
  rw [h]
  exact add_signExtend12_neg' n 64 (by omega) (by omega) hn

/-- Binary-level header part 1 (words `2632..2637`: `6` steps, `6` cycles, `0` calls): loads
`x10 = C_TD + levelBase (lvlIdx + 1) - 96` and `x12 = C_TD + levelBase (lvlIdx + 2) - 64`. -/
private theorem commit_bin_header_ptrs (oracle : Oracle) (lvlIdx : Nat) (hlvl : lvlIdx < 22)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 2632))
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * lvlIdx))
    (hd0 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx)) = BitVec.ofNat 64 (levelBase (lvlIdx + 1)))
    (hd1 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + 8)) = BitVec.ofNat 64 (levelBase (lvlIdx + 2))) :
    ∃ h5,
      DetRun oracle (submission.image .commit) s0 6 h5 6 0 ∧
      h5.pc = BitVec.ofNat 64 (0x1000 + 4 * 2638) ∧
      h5.mem = s0.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → h5.getReg r = s0.getReg r) ∧
      h5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 96) ∧
      h5.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) - 64) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_DB : C_DB = 68719476032 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  let h0 := execInstrBr s0 (.LD .x6 .x24 (0#12))
  let h1 := execInstrBr h0 (.ADD .x10 .x9 .x6)
  let h2 := execInstrBr h1 (.ADDI .x10 .x10 (4000#12))
  let h3 := execInstrBr h2 (.LD .x6 .x24 (8#12))
  let h4 := execInstrBr h3 (.ADD .x12 .x9 .x6)
  let h5 := execInstrBr h4 (.ADDI .x12 .x12 (4032#12))
  have hh0_pc : h0.pc = BitVec.ofNat 64 (0x1000 + 4 * 2633) := pc_step_idx s0 2632 hpc
  have hh1_pc : h1.pc = BitVec.ofNat 64 (0x1000 + 4 * 2634) := pc_step_idx h0 2633 hh0_pc
  have hh2_pc : h2.pc = BitVec.ofNat 64 (0x1000 + 4 * 2635) := pc_step_idx h1 2634 hh1_pc
  have hh3_pc : h3.pc = BitVec.ofNat 64 (0x1000 + 4 * 2636) := pc_step_idx h2 2635 hh2_pc
  have hh4_pc : h4.pc = BitVec.ofNat 64 (0x1000 + 4 * 2637) := pc_step_idx h3 2636 hh3_pc
  have hh5_pc : h5.pc = BitVec.ofNat 64 (0x1000 + 4 * 2638) := pc_step_idx h4 2637 hh4_pc
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
      commit_step1_mid2 (by omega) (by omega) hpc (by simp only [commitMid2Instr])
        (ordinaryStep_LD s0 .x6 .x24 (0#12) (by rw [hh0_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have r1 : DetRun oracle (submission.image .commit) h0 1 h1 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hh0_pc (by simp only [commitMid2Instr])
    have r2 : DetRun oracle (submission.image .commit) h1 1 h2 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hh1_pc (by simp only [commitMid2Instr])
    have r3 : DetRun oracle (submission.image .commit) h2 1 h3 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hh2_pc (by simp only [commitMid2Instr])
        (ordinaryStep_LD h2 .x6 .x24 (8#12) (by rw [hh3_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have r4 : DetRun oracle (submission.image .commit) h3 1 h4 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hh3_pc (by simp only [commitMid2Instr])
    have r5 : DetRun oracle (submission.image .commit) h4 1 h5 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hh4_pc (by simp only [commitMid2Instr])
    exact ((((r0.trans r1).trans r2).trans r3).trans r4).trans r5
  have hh5_x10 : h5.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 96) := by
    have h06 : h0.getReg .x6 = BitVec.ofNat 64 (levelBase (lvlIdx + 1)) := by
      simp only [h0, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hh0_addr, hd0]
    have h110 : h1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1)) := by
      have : h0.getReg .x9 = BitVec.ofNat 64 C_TD := by
        simp only [h0, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x9 (by decide), hx9]
      simp only [h1, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), this, h06, ← BitVec.ofNat_add]
    have h210 : h2.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 96) := by
      simp only [h2, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), h110]
      exact bv64_add_neg96 (C_TD + levelBase (lvlIdx + 1)) (by omega)
    simp only [h5, h4, h3, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 .x10 (by decide), getReg_setReg_ne' .x6 .x10 (by decide), h210]
  have hh5_x12 : h5.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) - 64) := by
    have h2mem : ∀ a, h2.getMem a = s0.getMem a := fun a => by simp only [MachineState.getMem, hh2_mem]
    have h36 : h3.getReg .x6 = BitVec.ofNat 64 (levelBase (lvlIdx + 2)) := by
      simp only [h3, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hh3_addr, h2mem, hd1]
    have h412 : h4.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2)) := by
      have h39 : h3.getReg .x9 = BitVec.ofNat 64 C_TD := by
        simp only [h3, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x9 (by decide),
          hh2_reg_other .x9 (by decide) (by decide), hx9]
      simp only [h4, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h39, h36, ← BitVec.ofNat_add]
    simp only [h5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h412]
    exact bv64_add_neg64 (C_TD + levelBase (lvlIdx + 2)) (by omega)
  exact ⟨h5, hrun, hh5_pc, hh5_mem, hh5_reg_other, hh5_x10, hh5_x12⟩

/-- Binary-level header (words `2632..2641`: `10` steps, `10` cycles, `0` calls). -/
private theorem commit_bin_header (oracle : Oracle) (msg : Message)
    (lvlIdx calls prom chunks : Nat) (hlvl : lvlIdx < 22)
    (hcalls : calls = levelSize (lvlIdx + 1) / 2)
    (hprom : prom = levelSize (lvlIdx + 1) % 2)
    (hchunks : chunks = calls / 128)
    (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 2632))
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * lvlIdx))
    (hdata : ∀ off < 32, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + off)) =
        (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + off))) :
    ∃ h9,
      DetRun oracle (submission.image .commit) s0 10 h9 10 0 ∧
      h9.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then 2642 else 3159)) ∧
      h9.mem = s0.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 →
        h9.getReg r = s0.getReg r) ∧
      h9.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 1) - 96) ∧
      h9.getReg .x12 = BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) - 64) ∧
      h9.getReg .x20 = BitVec.ofNat 64 calls ∧
      h9.getReg .x21 = BitVec.ofNat 64 prom ∧
      h9.getReg .x22 = BitVec.ofNat 64 chunks := by
  have hC_DB : C_DB = 68719476032 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hsrcSize_le := levelSize_le_max (lvlIdx + 1) (by omega)
  have hd0 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx)) = BitVec.ofNat 64 (levelBase (lvlIdx + 1)) := by
    have h := hdata 0 (by omega) (by omega)
    simp only [Nat.add_zero] at h
    rw [h, commit_initial_data_dword msg (32 * lvlIdx) (by omega)]
    exact commitData_dword_0 ⟨lvlIdx, hlvl⟩
  have hd1 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + 8)) = BitVec.ofNat 64 (levelBase (lvlIdx + 2)) := by
    rw [hdata 8 (by omega) (by omega), Nat.add_assoc,
      commit_initial_data_dword msg (32 * lvlIdx + 8) (by omega)]
    exact commitData_dword_1 ⟨lvlIdx, hlvl⟩
  have hd2 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + 16)) = BitVec.ofNat 64 calls := by
    rw [hdata 16 (by omega) (by omega), Nat.add_assoc,
      commit_initial_data_dword msg (32 * lvlIdx + 16) (by omega), hcalls]
    exact commitData_dword_2 ⟨lvlIdx, hlvl⟩
  have hd3 : s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + 24)) = BitVec.ofNat 64 prom := by
    rw [hdata 24 (by omega) (by omega), Nat.add_assoc,
      commit_initial_data_dword msg (32 * lvlIdx + 24) (by omega), hprom]
    exact commitData_dword_3 ⟨lvlIdx, hlvl⟩
  obtain ⟨h5, hrun1, hh5_pc, hh5_mem, hh5_reg, hh5_x10, hh5_x12⟩ :=
    commit_bin_header_ptrs oracle lvlIdx hlvl s0 hpc hx9 hx24 hd0 hd1
  let h6 := execInstrBr h5 (.LD .x20 .x24 (16#12))
  let h7 := execInstrBr h6 (.LD .x21 .x24 (24#12))
  let h8 := execInstrBr h7 (.SRLI .x22 .x20 (7#6))
  let h9 := execInstrBr h8 (.BEQ .x22 .x0 (2072#13))
  have hh6_pc : h6.pc = BitVec.ofNat 64 (0x1000 + 4 * 2639) := pc_step_idx h5 2638 hh5_pc
  have hh7_pc : h7.pc = BitVec.ofNat 64 (0x1000 + 4 * 2640) := pc_step_idx h6 2639 hh6_pc
  have hh8_pc : h8.pc = BitVec.ofNat 64 (0x1000 + 4 * 2641) := pc_step_idx h7 2640 hh7_pc
  have hh6_mem : h6.mem = s0.mem := (mem_exec_LD h5 _ _ _).trans hh5_mem
  have hh_mem : h9.mem = s0.mem :=
    ((mem_exec_BEQ h8 _ _ _).trans (mem_exec_SRLI h7 _ _ _)).trans ((mem_exec_LD h6 _ _ _).trans hh6_mem)
  have hh8_reg_h5 : ∀ r : Reg, r ≠ .x20 → r ≠ .x21 → r ≠ .x22 → h8.getReg r = h5.getReg r :=
    fun r h20r h21r h22r => by
      simp only [h8, h7, h6, execInstrBr, MachineState.getReg_setPC,
        getReg_setReg_ne' .x22 r (Ne.symm h22r), getReg_setReg_ne' .x21 r (Ne.symm h21r),
        getReg_setReg_ne' .x20 r (Ne.symm h20r)]
  have hh6_addr : h5.getReg .x24 + signExtend12 (16#12) = BitVec.ofNat 64 (C_DB + 32 * lvlIdx + 16) := by
    rw [hh5_reg .x24 (by decide) (by decide) (by decide), hx24, add_signExtend12_ofNat_small _ 16 (by omega)]
  have hh7_addr : h6.getReg .x24 + signExtend12 (24#12) = BitVec.ofNat 64 (C_DB + 32 * lvlIdx + 24) := by
    have h6_x24 : h6.getReg .x24 = h5.getReg .x24 := by
      simp only [h6, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x20 .x24 (by decide)]
    rw [h6_x24, hh5_reg .x24 (by decide) (by decide) (by decide), hx24, add_signExtend12_ofNat_small _ 24 (by omega)]
  have hrun2 : DetRun oracle (submission.image .commit) h5 4 h9 4 0 := by
    have r6 : DetRun oracle (submission.image .commit) h5 1 h6 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hh5_pc (by simp only [commitMid2Instr])
        (ordinaryStep_LD h5 .x20 .x24 (16#12) (by rw [hh6_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have r7 : DetRun oracle (submission.image .commit) h6 1 h7 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hh6_pc (by simp only [commitMid2Instr])
        (ordinaryStep_LD h6 .x21 .x24 (24#12) (by rw [hh7_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
    have r8 : DetRun oracle (submission.image .commit) h7 1 h8 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hh7_pc (by simp only [commitMid2Instr])
    have r9 : DetRun oracle (submission.image .commit) h8 1 h9 1 0 :=
      commit_step1_mid2 (by omega) (by omega) hh8_pc (by simp only [commitMid2Instr])
    exact ((r6.trans r7).trans r8).trans r9
  have h5mem : ∀ a, h5.getMem a = s0.getMem a := fun a => by simp only [MachineState.getMem, hh5_mem]
  have h6mem : ∀ a, h6.getMem a = s0.getMem a := fun a => by simp only [MachineState.getMem, hh6_mem]
  have hh8_x20 : h8.getReg .x20 = BitVec.ofNat 64 calls := by
    have h620 : h6.getReg .x20 = BitVec.ofNat 64 calls := by
      simp only [h6, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0), hh6_addr, h5mem, hd2]
    simp only [h8, h7, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x22 .x20 (by decide), getReg_setReg_ne' .x21 .x20 (by decide), h620]
  have hh8_x21 : h8.getReg .x21 = BitVec.ofNat 64 prom := by
    have h721 : h7.getReg .x21 = BitVec.ofNat 64 prom := by
      simp only [h7, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x21 ≠ .x0), hh7_addr, h6mem, hd3]
    simp only [h8, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x22 .x21 (by decide), h721]
  have hh8_x22 : h8.getReg .x22 = BitVec.ofNat 64 chunks := by
    have h720 : h7.getReg .x20 = BitVec.ofNat 64 calls := by
      have : h8.getReg .x20 = h7.getReg .x20 := by
        simp only [h8, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x22 .x20 (by decide)]
      rw [← this]; exact hh8_x20
    simp only [h8, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x22 ≠ .x0), h720]
    exact (bv64_ushiftRight_ofNat calls 7 (by omega)).trans (congrArg (BitVec.ofNat 64) (by omega))
  have hh9_reg : ∀ r : Reg, h9.getReg r = h8.getReg r := reg_exec_BEQ h8 .x22 .x0 (2072#13)
  have hh9_pc : h9.pc = BitVec.ofNat 64 (0x1000 + 4 * (if 0 < chunks then 2642 else 3159)) := by
    by_cases hch : 0 < chunks
    · have hne0 : (h8.getReg .x22 == h8.getReg .x0) = false := by
        rw [hh8_x22, c_getReg_x0, beq_eq_false_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hch, ite_true, h9, execInstrBr, hne0, Bool.false_eq_true, ite_false, pc_setPC]
      exact pc_step_idx h8 2641 hh8_pc
    · have hch0 : chunks = 0 := by omega
      have heq0 : (h8.getReg .x22 == h8.getReg .x0) = true := by
        rw [hh8_x22, hch0, c_getReg_x0]; exact beq_self_eq_true _
      simp only [hch, ite_false, h9, execInstrBr, heq0, ite_true, pc_setPC, hh8_pc]
      exact pc_beq_2641
  exact ⟨h9, hrun1.trans hrun2, hh9_pc, hh_mem,
    fun r h6 h10 h12 h20 h21 h22 => ((hh9_reg r).trans (hh8_reg_h5 r h20 h21 h22)).trans (hh5_reg r h6 h10 h12),
    ((hh9_reg .x10).trans (hh8_reg_h5 .x10 (by decide) (by decide) (by decide))).trans hh5_x10,
    ((hh9_reg .x12).trans (hh8_reg_h5 .x12 (by decide) (by decide) (by decide))).trans hh5_x12,
    (hh9_reg .x20).trans hh8_x20, (hh9_reg .x21).trans hh8_x21, (hh9_reg .x22).trans hh8_x22⟩

/-- Binary-level loop tail (words `3197..3198`: `2` steps, `2` cycles, `0` calls). -/
private theorem commit_bin_tail (oracle : Oracle) (lvlIdx : Nat) (hlvl : lvlIdx < 22)
    (sc : MachineState)
    (hpcC : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 3197))
    (hx24 : sc.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * lvlIdx))
    (hx25 : sc.getReg .x25 = BitVec.ofNat 64 (C_DB + 704)) :
    ∃ e2,
      DetRun oracle (submission.image .commit) sc 2 e2 2 0 ∧
      e2.pc = BitVec.ofNat 64 (0x1000 + 4 * (if lvlIdx + 1 < 22 then 2632 else 3199)) ∧
      e2.mem = sc.mem ∧
      e2.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (lvlIdx + 1)) ∧
      (∀ r : Reg, r ≠ .x24 → e2.getReg r = sc.getReg r) := by
  have hC_DB : C_DB = 68719476032 := rfl
  let e1 := execInstrBr sc (.ADDI .x24 .x24 (32#12))
  let e2 := execInstrBr e1 (.BNE .x24 .x25 (5928#13))
  have he1_pc : e1.pc = BitVec.ofNat 64 (0x1000 + 4 * 3198) := pc_step_idx sc 3197 hpcC
  have he_run : DetRun oracle (submission.image .commit) sc 2 e2 2 0 := by
    have re1 : DetRun oracle (submission.image .commit) sc 1 e1 1 0 :=
      commit_step1_tail (by omega) (by omega) hpcC (by simp only [commitTailInstr])
    have re2 : DetRun oracle (submission.image .commit) e1 1 e2 1 0 :=
      commit_step1_tail (by omega) (by omega) he1_pc (by simp only [commitTailInstr])
    exact re1.trans re2
  have he1_x24 : e1.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (lvlIdx + 1)) := by
    simp only [e1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x24 ≠ .x0), hx24,
      add_signExtend12_ofNat_small _ 32 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have he1_x25 : e1.getReg .x25 = BitVec.ofNat 64 (C_DB + 704) := by
    simp only [e1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x24 .x25 (by decide), hx25]
  have he2_pc : e2.pc = BitVec.ofNat 64 (0x1000 + 4 * (if lvlIdx + 1 < 22 then 2632 else 3199)) := by
    by_cases hlt : lvlIdx + 1 < 22
    · have hne : (e1.getReg .x24 != e1.getReg .x25) = true := by
        rw [he1_x24, he1_x25, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp only [hlt, ite_true, e2, execInstrBr, hne, pc_setPC, he1_pc]
      exact pc_bne_3198
    · have heq : (e1.getReg .x24 != e1.getReg .x25) = false := by
        rw [he1_x24, he1_x25, show 32 * (lvlIdx + 1) = 704 by omega]
        exact bne_self_eq_false _
      simp only [hlt, ite_false, e2, execInstrBr, heq, Bool.false_eq_true, pc_setPC]
      exact pc_step_idx e1 3198 he1_pc
  have he2_mem : e2.mem = sc.mem := (mem_exec_BNE e1 _ _ _).trans (mem_exec_ADDI sc _ _ _)
  have he2_reg : ∀ r : Reg, r ≠ .x24 → e2.getReg r = sc.getReg r := fun r hr => by
    rw [reg_exec_BNE e1 _ _ _ r]
    simp only [e1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x24 r (Ne.symm hr)]
  exact ⟨e2, he_run, he2_pc, he2_mem, (reg_exec_BNE e1 _ _ _ .x24).trans he1_x24, he2_reg⟩

/-- One full iteration of `bin_driver` (words `2632..3198`) for binary level `lvlIdx < 22`
building `L_{lvlIdx+2}` from `L_{lvlIdx+1}`. -/
theorem commit_bin_level (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128)
    (lvlIdx : Nat) (hlvl : lvlIdx < 22) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 2632))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx24 : s0.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * lvlIdx))
    (hx25 : s0.getReg .x25 = BitVec.ofNat 64 (C_DB + 704))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hdata : ∀ off < 32, off % 8 = 0 →
      s0.getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + off)) =
        (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + 32 * lvlIdx + off)))
    (hsrc : ∀ idx < levelSize (lvlIdx + 1),
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + gapOffset idx) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 1) idx)
    (hsrcGap : ∀ q < (levelSize (lvlIdx + 1) + 1) / 2,
      readBuffer s0 (C_TD + levelBase (lvlIdx + 1) + 96 * q + 64) 32 = 0) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0
        (binLevelSteps lvlIdx) s1 (binLevelCycles lvlIdx) (binLevelCalls lvlIdx) ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (if lvlIdx + 1 < 22 then 2632 else 3199)) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x24 = BitVec.ofNat 64 (C_DB + 32 * (lvlIdx + 1)) ∧
      s1.getReg .x25 = BitVec.ofNat 64 (C_DB + 704) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ idx < levelSize (lvlIdx + 2),
        readBuffer s1 (C_TD + levelBase (lvlIdx + 2) + gapOffset idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts (lvlIdx + 2) idx) ∧
      (∀ q < (levelSize (lvlIdx + 2) + 1) / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j)) =
        s0.getByte (BitVec.ofNat 64 (C_TD + levelBase (lvlIdx + 2) + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 s1 (C_TD + levelBase (lvlIdx + 2)) (C_TD + levelBase (lvlIdx + 3)) := by
  let calls := levelSize (lvlIdx + 1) / 2
  let prom := levelSize (lvlIdx + 1) % 2
  let chunks := calls / 128
  let remPairs := (calls % 128) / 2
  let oddCall := calls % 2
  -- Header (words 2632..2641)
  obtain ⟨h9, hh_run, hh9_pc, hh_mem, hh9_reg, hh9_x10, hh9_x12, hh9_x20, hh9_x21, hh9_x22⟩ :=
    commit_bin_header oracle msg lvlIdx calls prom chunks hlvl rfl rfl rfl s0 hpc hx9 hx24 hdata
  -- Stage A: Bulk chunks (words 2642..3158)
  obtain ⟨sb, hrunA, hpcB, hregA, hx10B, hx12B, hdigB, hgapB, hpresB⟩ :=
    commit_bin_level_stageA h768 oracle msg salts lvlIdx calls chunks hlvl rfl rfl s0 h9 hh_mem hh9_pc
      ((hh9_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5)
      ((hh9_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11)
      ((hh9_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13)
      hh9_x10 hh9_x12 hh9_x22 hsrc hsrcGap
  -- Stage B: Tail pairs (words 3159..3171)
  obtain ⟨st, hrunB, hpcT, hregB, hx10T, hx12T, hdigT, hgapT, hpresT⟩ :=
    commit_bin_level_stageB h768 oracle msg salts lvlIdx calls chunks remPairs hlvl rfl rfl rfl s0 sb hpcB
      ((hregA .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh9_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5))
      ((hregA .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh9_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11))
      ((hregA .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        ((hh9_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13))
      ((hregA .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh9_x20)
      hx10B hx12B hsrc hsrcGap hdigB hgapB hpresB
  -- Stage C: Odd call + optional promoted node (words 3172..3196)
  obtain ⟨sc, hrunC, hpcC, hregC, hdigC, hgapC, hpresC⟩ :=
    commit_bin_level_stageC h768 oracle msg salts lvlIdx calls prom chunks remPairs oddCall hlvl
      rfl rfl rfl rfl rfl s0 st hpcT
      ((hregB .x5 (by decide) (by decide) (by decide)).trans
        ((hregA .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((hh9_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5)))
      ((hregB .x11 (by decide) (by decide) (by decide)).trans
        ((hregA .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((hh9_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11)))
      ((hregB .x13 (by decide) (by decide) (by decide)).trans
        ((hregA .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((hh9_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13)))
      ((hregB .x20 (by decide) (by decide) (by decide)).trans
        ((hregA .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh9_x20))
      ((hregB .x21 (by decide) (by decide) (by decide)).trans
        ((hregA .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh9_x21))
      hx10T hx12T hsrc hsrcGap hdigT hgapT hpresT
  have hsc_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x12 → r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x22 →
      sc.getReg r = s0.getReg r := fun r h6 h7 h10 h12 h19 h20 h21 h22 =>
    (((hregC r h6 h10 h12 h22).trans (hregB r h10 h12 h22)).trans
      (hregA r h6 h7 h10 h12 h19)).trans (hh9_reg r h6 h10 h12 h20 h21 h22)
  -- Stage D: Loop tail (words 3197..3198)
  obtain ⟨e2, he_run, he2_pc, he2_mem, he2_x24, he2_reg⟩ :=
    commit_bin_tail oracle lvlIdx hlvl sc hpcC
      ((hsc_reg .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24)
      ((hsc_reg .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25)
  have hrun_all : DetRun oracle (submission.image .commit) s0
      (binLevelSteps lvlIdx) e2 (binLevelCycles lvlIdx) (binLevelCalls lvlIdx) := by
    have h := (((hh_run.trans hrunA).trans hrunB).trans hrunC).trans he_run
    have hs : 10 + (if 0 < chunks then 4 + 513 * chunks else 0) + (3 + 10 * remPairs) +
        (if oddCall = 1 then 7 + 9 * prom else 3 + 8 * prom) + 2 = binLevelSteps lvlIdx := rfl
    have hc : 10 + (if 0 < chunks then 4 + 1409 * chunks else 0) + (3 + 24 * remPairs) +
        (if oddCall = 1 then 14 + 9 * prom else 3 + 8 * prom) + 2 = binLevelCycles lvlIdx := rfl
    have hq : 0 + 128 * chunks + 2 * remPairs + oddCall + 0 = binLevelCalls lvlIdx := by
      unfold binLevelCalls; omega
    rw [hs, hc, hq] at h
    exact h
  refine ⟨e2, hrun_all, he2_pc,
    (he2_reg .x2 (by decide)).trans ((hsc_reg .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx2),
    (he2_reg .x5 (by decide)).trans ((hsc_reg .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5),
    (he2_reg .x9 (by decide)).trans ((hsc_reg .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx9),
    (he2_reg .x11 (by decide)).trans ((hsc_reg .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11),
    (he2_reg .x13 (by decide)).trans ((hsc_reg .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13),
    he2_x24,
    (he2_reg .x25 (by decide)).trans ((hsc_reg .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25),
    (he2_reg .x26 (by decide)).trans ((hsc_reg .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26),
    fun idx hidx => by rw [readBuffer_of_mem_eq he2_mem]; exact hdigC idx hidx,
    fun q hq j hj => by rw [getByte_of_mem_eq he2_mem]; exact hgapC q hq j hj,
    hpresC.trans (MemPreservedOutside.of_mem_eq he2_mem _ _)⟩

end CommitGolfCandidate
