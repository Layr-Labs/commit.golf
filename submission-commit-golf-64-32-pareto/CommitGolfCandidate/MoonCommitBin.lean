import CommitGolfCandidate.MoonCommitExec

/-! Exact RV64IM execution proofs for Phases 2 (`L1`, words `28747..34895`), 3 (`L2..L5`, words
`34896..43095`), and 4 + Root + Copy + Halt Prep (`L6..L23` bulk/tail + `L24` root + 32B copy +
`HALT(0)` register prep, words `43096..43885`) of the 64-32 `commit` image. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Unified 1-Indexed Binary Heap Value (`c_heapVal`) -/

def c_heapLevel (h : Nat) : Nat := 24 - Nat.log 2 h

def c_heapOffset (h : Nat) : Nat := h - 2 ^ (Nat.log 2 h)

def c_heapVal (c : Comp64) (p : Perm200) (msg : Message) (salts : Index → Salt192) (h : Nat) : Digest :=
  nodeVal c p msg salts (c_heapLevel h) (c_heapOffset h)

theorem c_log2_heapIdx (l idx : Nat) (hl : l ≤ 24) (hidx : idx < levelSize l) :
    Nat.log 2 (heapIdx l idx) = 24 - l := by
  unfold heapIdx levelSize at *
  apply (Nat.log_eq_iff (by omega)).mpr
  refine ⟨by omega, ?_⟩
  rw [Nat.pow_succ, Nat.mul_two]
  omega

theorem c_heapVal_eq_nodeVal (c : Comp64) (p : Perm200) (msg : Message) (salts : Index → Salt192)
    (l idx : Nat) (hl : l ≤ 24) (hidx : idx < levelSize l) :
    c_heapVal c p msg salts (heapIdx l idx) = nodeVal c p msg salts l idx := by
  unfold c_heapVal c_heapLevel c_heapOffset
  rw [c_log2_heapIdx l idx hl hidx]
  have hl' : 24 - (24 - l) = l := by omega
  have ho' : heapIdx l idx - 2 ^ (24 - l) = idx := by unfold heapIdx levelSize; omega
  rw [hl', ho']

theorem c_heapVal_step (c : Comp64) (p : Perm200) (msg : Message) (salts : Index → Salt192)
    (h : Nat) (h1 : 1 ≤ h) (h2 : h < 2 ^ 24) :
    c_heapVal c p msg salts h =
      maskLevel (c_heapLevel h)
        (c (binaryInput (c_heapVal c p msg salts (2 * h)) (c_heapVal c p msg salts (2 * h + 1)))) := by
  have hlog_lt : Nat.log 2 h < 24 := Nat.log_lt_of_lt_pow (by omega) h2
  have hpow_le : 2 ^ (Nat.log 2 h) ≤ h := Nat.pow_log_le_self 2 (by omega)
  have hlt_pow : h < 2 ^ (Nat.log 2 h + 1) := Nat.lt_pow_succ_log_self (by decide) h
  set k := Nat.log 2 h
  set l := 23 - k
  set idx := h - 2 ^ k
  have hl_lt : l < 24 := by omega
  have hls_succ : levelSize (l + 1) = 2 ^ k := by
    unfold levelSize; congr 1; omega
  have hidx_lt : idx < levelSize (l + 1) := by
    rw [hls_succ]; rw [Nat.pow_succ, Nat.mul_two] at hlt_pow; omega
  have hh : h = heapIdx (l + 1) idx := by
    unfold heapIdx; rw [hls_succ]; omega
  have hls_l : levelSize l = 2 * levelSize (l + 1) := levelSize_double l hl_lt
  have hchL : 2 * h = heapIdx l (2 * idx) := by
    rw [hh, heapIdx_left_child l idx hl_lt]
  have hchR : 2 * h + 1 = heapIdx l (2 * idx + 1) := by
    rw [hh, heapIdx_right_child l idx hl_lt]
  rw [hchR, hchL]
  rw [c_heapVal_eq_nodeVal c p msg salts l (2 * idx) (by omega) (by omega)]
  rw [c_heapVal_eq_nodeVal c p msg salts l (2 * idx + 1) (by omega) (by omega)]
  have hlvl : c_heapLevel h = l + 1 := by
    unfold c_heapLevel; omega
  rw [hlvl, hh, c_heapVal_eq_nodeVal c p msg salts (l + 1) idx (by omega) hidx_lt]
  simp only [nodeVal, nodeValFromLeaves, hidx_lt, ite_true]

theorem c_heapLevel_l1 (h : Nat) (hlo : 2 ^ 23 ≤ h) (hhi : h < 2 ^ 24) :
    c_heapLevel h = 1 := by
  have hlog : Nat.log 2 h = 23 := (Nat.log_eq_iff (by omega)).mpr ⟨hlo, hhi⟩
  unfold c_heapLevel; omega

theorem c_heapLevel_l25 (h : Nat) (hlo : 2 ^ 19 ≤ h) (hhi : h < 2 ^ 23) :
    2 ≤ c_heapLevel h ∧ c_heapLevel h < 6 := by
  have h1 : 19 ≤ Nat.log 2 h := Nat.le_log_of_pow_le (by decide) hlo
  have h2 : Nat.log 2 h < 23 := Nat.log_lt_of_lt_pow (by omega) hhi
  unfold c_heapLevel; omega

theorem c_heapLevel_l623 (h : Nat) (hlo : 2 ≤ h) (hhi : h < 2 ^ 19) :
    6 ≤ c_heapLevel h ∧ c_heapLevel h < 24 := by
  have h1 : 1 ≤ Nat.log 2 h := Nat.le_log_of_pow_le (by decide) (by omega)
  have h2 : Nat.log 2 h < 19 := Nat.log_lt_of_lt_pow (by omega) hhi
  unfold c_heapLevel; omega

theorem c_heapVal_step_l1 (c : Comp64) (p : Perm200) (msg : Message) (salts : Index → Salt192)
    (h : Nat) (hlo : 2 ^ 23 ≤ h) (hhi : h < 2 ^ 24) :
    c_heapVal c p msg salts h =
      c (binaryInput (c_heapVal c p msg salts (2 * h)) (c_heapVal c p msg salts (2 * h + 1))) := by
  rw [c_heapVal_step c p msg salts h (by omega) hhi, c_heapLevel_l1 h hlo hhi]
  rfl

theorem c_heapVal_step_l25 (c : Comp64) (p : Perm200) (msg : Message) (salts : Index → Salt192)
    (h : Nat) (hlo : 2 ^ 19 ≤ h) (hhi : h < 2 ^ 23) :
    c_heapVal c p msg salts h =
      mask240 (c (binaryInput (c_heapVal c p msg salts (2 * h)) (c_heapVal c p msg salts (2 * h + 1)))) := by
  rw [c_heapVal_step c p msg salts h (by omega) (by omega)]
  have ⟨h1, h2⟩ := c_heapLevel_l25 h hlo hhi
  unfold maskLevel
  simp only [show ¬ (c_heapLevel h < 2 ∨ c_heapLevel h = 24) by omega, ite_false, h2, ite_true]

theorem c_heapVal_step_l623 (c : Comp64) (p : Perm200) (msg : Message) (salts : Index → Salt192)
    (h : Nat) (hlo : 2 ≤ h) (hhi : h < 2 ^ 19) :
    c_heapVal c p msg salts h =
      mask238 (c (binaryInput (c_heapVal c p msg salts (2 * h)) (c_heapVal c p msg salts (2 * h + 1)))) := by
  rw [c_heapVal_step c p msg salts h (by omega) (by omega)]
  have ⟨h1, h2⟩ := c_heapLevel_l623 h hlo hhi
  unfold maskLevel
  simp only [show ¬ (c_heapLevel h < 2 ∨ c_heapLevel h = 24) by omega,
    show ¬ (c_heapLevel h < 6) by omega, ite_false]

theorem c_heapVal_root (c : Comp64) (p : Perm200) (msg : Message) (salts : Index → Salt192) :
    c_heapVal c p msg salts 1 =
      c (binaryInput (c_heapVal c p msg salts 2) (c_heapVal c p msg salts 3)) := by
  rw [c_heapVal_step c p msg salts 1 (le_refl _) (by decide)]
  have hlog : Nat.log 2 1 = 0 := by decide
  unfold c_heapLevel; rw [hlog]; rfl

theorem c_heapVal_one_eq_rootVal (c : Comp64) (p : Perm200) (msg : Message) (salts : Index → Salt192) :
    c_heapVal c p msg salts 1 = rootVal c p msg salts := by
  have hh : (1 : Nat) = heapIdx 24 0 := by decide
  rw [hh, c_heapVal_eq_nodeVal c p msg salts 24 0 (le_refl _) (by decide)]
  rfl

/-! ### 2. Phase 2 (`L1`: words `28747..34895`) -/

private theorem c_pc_beq_34891 :
    BitVec.ofNat 64 (0x1000 + 4 * 34891) + signExtend13 (8#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 34893) := by decide

private theorem c_pc_jal_34892 :
    BitVec.ofNat 64 (0x1000 + 4 * 34892) + signExtend21 (2072572#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 28747) := by decide

private def c_midL1Instrs : List Instr :=
  [.ADDI .x6 .x0 (1#12), .SLLI .x6 .x6 (24#6), .ADD .x19 .x9 .x6]

private theorem c_midL1_run (oracle : Oracle) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 34893)) :
    DetRun oracle (submission.image .commit) s 3 (c_midL1Instrs.foldl execInstrBr s) 3 0 := by
  have hall : ∀ ins ∈ c_midL1Instrs, c_isPureAlu ins = true := by decide
  apply c_exec_alu_list c_midL1Instrs s
  intro i hi
  have hi' : i < 3 := hi
  have hpc_i : ((c_midL1Instrs.take i).foldl execInstrBr s).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (34893 + i)) := by
    have h := c_foldl_pureAlu_pc (c_midL1Instrs.take i) s (0x1000 + 4 * 34893)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitMidL1Instr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem c_midL1_spec (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 34893))
    (hx5 : s.getReg .x5 = 0#64)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * 2 ^ 23))
    (hx11 : s.getReg .x11 = 64#64)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 23))
    (hx13 : s.getReg .x13 = 0#64)
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s' := c_midL1Instrs.foldl execInstrBr s
    s'.pc = BitVec.ofNat 64 (0x1000 + 4 * 34896) ∧
    s'.mem = s.mem ∧
    s'.getReg .x5 = 0#64 ∧
    s'.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s'.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * 2 ^ 23) ∧
    s'.getReg .x11 = 64#64 ∧
    s'.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 23) ∧
    s'.getReg .x13 = 0#64 ∧
    s'.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 19) ∧
    s'.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ c_midL1Instrs, c_isPureAlu ins = true := by decide
  refine ⟨?_, c_foldl_pureAlu_mem c_midL1Instrs s hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (c_foldl_pureAlu_pc c_midL1Instrs s (0x1000 + 4 * 34893) hall hpc).trans (by decide)
  all_goals (
    simp only [c_midL1Instrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx5, hx9, hx10, hx11, hx12, hx13, hx26]
    try decide)

/-- One `L1` node step (`ADDI x10,-64; ADDI x12,-32; ECALL`): 3 steps, 10 cycles, 1 call. -/
private theorem c_l1_node_step (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (s : MachineState)
    (k h : Nat) (hk : k < 2048) (hlo : 2 ^ 23 ≤ h) (hhi : h < 2 ^ 24)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (28747 + 3 * k)))
    (hx5 : s.getReg .x5 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (h + 1)))
    (hx11 : s.getReg .x11 = 64#64)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (h + 1)))
    (hx13 : s.getReg .x13 = 0#64)
    (hchL : readBuffer s (C_TD + 32 * (2 * h)) 32 =
      c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts (2 * h))
    (hchR : readBuffer s (C_TD + 32 * (2 * h + 1)) 32 =
      c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts (2 * h + 1)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ s',
      DetRun oracle (submission.image .commit) s 3 s' 10 1 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (28747 + 3 * (k + 1))) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s'.getReg reg = s.getReg reg) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * h) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * h) ∧
      readBuffer s' (C_TD + 32 * h) 32 = c_heapVal c64 p200 msg salts h ∧
      CommitMemOutside s s' (C_TD + 32 * h) (C_TD + 32 * (h + 1)) := by
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hCT : C_TD = 4294971424 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  let out := c_heapVal c64 p200 msg salts h
  let s1 := execInstrBr s (.ADDI .x10 .x10 (4032#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (4064#12))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + 32 * h)) out
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (28747 + 3 * k + 1)) := c_pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (28747 + 3 * k + 2)) := c_pc_step_idx s1 _ hs1_pc
  have hs1_x10 : s1.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * h) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      c_bv64_add_neg64 (C_TD + 64 * (h + 1)) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_x10 : s2.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * h) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne .x12 .x10 (by decide), hs1_x10]
  have hs2_x12 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * h) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      c_getReg_setReg_ne .x10 .x12 (by decide), hx12,
      c_bv64_add_neg32 (C_TD + 32 * (h + 1)) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_mem : s2.mem = s.mem := (c_mem_exec_ADDI s1 _ _ _).trans (c_mem_exec_ADDI s _ _ _)
  have hs2_reg : ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s2.getReg reg = s.getReg reg := fun reg h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x12 reg (Ne.symm h12), c_getReg_setReg_ne .x10 reg (Ne.symm h10)]
  have hr0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_l1 s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc)) rfl
  have hr1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_l1 s1 k 1 hk (by omega) hs1_pc) rfl
  have hread : oracle.compression ((readBuffer s2 (C_TD + 64 * h) 64).cast h512.symm) = out := by
    rw [c_readBuffer_of_mem_eq hs2_mem, readBuffer_binary]
    have haL : C_TD + 64 * h = C_TD + 32 * (2 * h) := by omega
    have haR : C_TD + 32 * (2 * h) + 32 = C_TD + 32 * (2 * h + 1) := by omega
    rw [haL, haR, hchL, hchR]
    exact (c_heapVal_step_l1 c64 p200 msg salts h hlo hhi).symm
  have hr2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h512 (commit_fetch_l1 s2 k 2 hk (by omega) hs2_pc)
      ((hs2_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg .x13 (by decide) (by decide)).trans hx13)
      (C_TD + 64 * h) (C_TD + 32 * h) hs2_x10 hs2_x12
      (by omega) (by omega) (by omega) (by omega) out hread
  refine ⟨s3, (hr0.trans hr1).trans hr2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c_pc_writeBits, c_pc_step_idx s2 _ hs2_pc]; exact congrArg (BitVec.ofNat 64) (by omega)
  · intro reg h10 h12; exact (writeBits_register s2 _ out reg).trans (hs2_reg reg h10 h12)
  · exact (writeBits_register s2 _ out .x10).trans hs2_x10
  · exact (writeBits_register s2 _ out .x12).trans hs2_x12
  · exact writeBits_readBuffer_digest s2 _ out
  · exact (CommitMemOutside.of_mem_eq hs2_mem _ _).trans
      (by simpa only [show C_TD + 32 * h + (256 + 7) / 8 = C_TD + 32 * (h + 1) by omega] using
        c_memPreserved_writeBits s2 (C_TD + 32 * h) out (by omega))

/-- One 2048-node `L1` chunk body (`28747..34890`): 6144 steps, 20480 cycles, 2048 calls. -/
private theorem c_l1_chunk_body (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (sc : MachineState)
    (chunkIdx : Nat) (hchunk : chunkIdx < 4096)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 28747))
    (hx5 : sc.getReg .x5 = 0#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 24 - 2048 * chunkIdx)))
    (hx11 : sc.getReg .x11 = 64#64)
    (hx12 : sc.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 24 - 2048 * chunkIdx)))
    (hx13 : sc.getReg .x13 = 0#64)
    (hheap : ∀ h', 2 ^ 24 - 2048 * chunkIdx ≤ h' → h' < 2 ^ 25 →
      readBuffer sc (C_TD + 32 * h') 32 =
        c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts h') :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ se,
      DetRun oracle (submission.image .commit) sc 6144 se 20480 2048 ∧
      se.pc = BitVec.ofNat 64 (0x1000 + 4 * 34891) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → se.getReg reg = sc.getReg reg) ∧
      se.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 24 - 2048 * (chunkIdx + 1))) ∧
      se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 24 - 2048 * (chunkIdx + 1))) ∧
      (∀ h', 2 ^ 24 - 2048 * (chunkIdx + 1) ≤ h' → h' < 2 ^ 25 →
        readBuffer se (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
      CommitMemOutside sc se (C_TD + 32 * (2 ^ 24 - 2048 * (chunkIdx + 1)))
        (C_TD + 32 * (2 ^ 24 - 2048 * chunkIdx)) := by
  have hCT : C_TD = 4294971424 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  have hind : ∀ k ≤ 2048,
      ∃ sk,
        DetRun oracle (submission.image .commit) sc (3 * k) sk (10 * k) k ∧
        sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (28747 + 3 * k)) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sk.getReg reg = sc.getReg reg) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 24 - 2048 * chunkIdx - k)) ∧
        sk.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 24 - 2048 * chunkIdx - k)) ∧
        (∀ h', 2 ^ 24 - 2048 * chunkIdx - k ≤ h' → h' < 2 ^ 25 →
          readBuffer sk (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
        CommitMemOutside sc sk (C_TD + 32 * (2 ^ 24 - 2048 * chunkIdx - k))
          (C_TD + 32 * (2 ^ 24 - 2048 * chunkIdx)) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12,
        fun h' h1 h2 => hheap h' (by omega) h2, CommitMemOutside.refl _ _ _⟩
    | succ k ih =>
      obtain ⟨sk, hrun_k, hpck, hregk, hx10k, hx12k, hheapk, hpresk⟩ := ih (by omega)
      set h := 2 ^ 24 - 2048 * chunkIdx - (k + 1)
      have hh_succ : h + 1 = 2 ^ 24 - 2048 * chunkIdx - k := by omega
      have hlo : 2 ^ 23 ≤ h := by omega
      have hhi : h < 2 ^ 24 := by omega
      obtain ⟨s', hst, hpc', hreg', hx10', hx12', hval', hpres'⟩ :=
        c_l1_node_step h512 oracle msg salts sk k h (by omega) hlo hhi hpck
          ((hregk .x5 (by decide) (by decide)).trans hx5)
          (by simpa only [hh_succ] using hx10k)
          ((hregk .x11 (by decide) (by decide)).trans hx11)
          (by simpa only [hh_succ] using hx12k)
          ((hregk .x13 (by decide) (by decide)).trans hx13)
          (hheapk (2 * h) (by omega) (by omega))
          (hheapk (2 * h + 1) (by omega) (by omega))
      refine ⟨s', by simpa [Nat.mul_succ, Nat.add_assoc] using hrun_k.trans hst,
        hpc', fun reg h10 h12 => (hreg' reg h10 h12).trans (hregk reg h10 h12),
        hx10', hx12', ?_, ?_⟩
      · intro h' h1 h2
        by_cases heq : h' = h
        · subst heq; exact hval'
        · exact (hpres'.readBuffer_eq (by omega) (by omega)).trans (hheapk h' (by omega) h2)
      · exact (hpresk.mono (lo' := C_TD + 32 * h) (hi' := C_TD + 32 * (2 ^ 24 - 2048 * chunkIdx)) (by omega) (le_refl _)).trans
          (hpres'.mono (lo' := C_TD + 32 * h) (hi' := C_TD + 32 * (2 ^ 24 - 2048 * chunkIdx)) (le_refl _) (by omega))
  obtain ⟨se, hrun, hpce, hrege, hx10e, hx12e, hheape, hprese⟩ := hind 2048 (le_refl _)
  have hsub : 2 ^ 24 - 2048 * chunkIdx - 2048 = 2 ^ 24 - 2048 * (chunkIdx + 1) := by omega
  rw [hsub] at hx10e hx12e hheape hprese
  exact ⟨se, hrun, hpce, hrege, hx10e, hx12e, hheape, hprese⟩

private theorem c_l1_latch_back (oracle : Oracle) (chunkIdx : Nat) (hchunk : chunkIdx < 4095)
    (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 34891))
    (hx12 : se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 24 - 2048 * (chunkIdx + 1))))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 23)) :
    let sb := execInstrBr (execInstrBr se (.BEQ .x12 .x19 (8#13))) (.JAL .x0 (2072572#21))
    DetRun oracle (submission.image .commit) se 2 sb 2 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 28747) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  have hCT : C_TD = 4294971424 := rfl
  let s1 := execInstrBr se (.BEQ .x12 .x19 (8#13))
  let s2 := execInstrBr s1 (.JAL .x0 (2072572#21))
  have hst1 : DetRun oracle (submission.image .commit) se 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_commitMidL1Instr se 34891 (by omega) (by omega) hpc) rfl
  have hne : (se.getReg .x12 == se.getReg .x19) = false := by
    rw [hx12, hx19, beq_eq_false_iff_ne]
    exact c_bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 34892) := by
    simp only [s1, execInstrBr, hne, Bool.false_eq_true, ite_false, c_pc_setPC]
    exact c_pc_step_idx se 34891 hpc
  have hst2 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_commitMidL1Instr s1 34892 (by omega) (by omega) hs1_pc) rfl
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 28747) := by
    simp only [s2, execInstrBr, c_pc_setPC, hs1_pc]; exact c_pc_jal_34892
  exact ⟨hst1.trans hst2, hs2_pc,
    (c_mem_exec_JAL s1 _ _).trans (c_mem_exec_BEQ se _ _ _),
    fun reg => (c_reg_exec_JAL0 s1 _ reg).trans (c_reg_exec_BEQ se _ _ _ reg)⟩

private theorem c_l1_latch_exit (oracle : Oracle) (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 34891))
    (hx12 : se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 24 - 2048 * 4096)))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 23)) :
    let sb := execInstrBr se (.BEQ .x12 .x19 (8#13))
    DetRun oracle (submission.image .commit) se 1 sb 1 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 34893) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  let sb := execInstrBr se (.BEQ .x12 .x19 (8#13))
  have hst : DetRun oracle (submission.image .commit) se 1 sb 1 0 :=
    DetRun.step1 (commit_fetch_commitMidL1Instr se 34891 (by omega) (by omega) hpc) rfl
  have heq : (se.getReg .x12 == se.getReg .x19) = true := by
    rw [hx12, hx19, show 2 ^ 24 - 2048 * 4096 = 2 ^ 23 by decide]
    exact beq_self_eq_true _
  have hpc' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 34893) := by
    simp only [sb, execInstrBr, heq, ite_true, c_pc_setPC, hpc]; exact c_pc_beq_34891
  exact ⟨hst, hpc', c_mem_exec_BEQ se _ _ _, c_reg_exec_BEQ se _ _ _⟩

/-- Full Phase 2 (`L1` + Phase 3 setup, words `28747..34895`):
`25,174,018` steps, `83,894,274` cycles, `8,388,608` calls. -/
theorem commit_phase2 (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 28747))
    (hx5 : s0.getReg .x5 = 0#64)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 25))
    (hx11 : s0.getReg .x11 = 64#64)
    (hx12 : s0.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 24))
    (hx13 : s0.getReg .x13 = 0#64)
    (hx19 : s0.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 23))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hheap0 : ∀ h', 2 ^ 24 ≤ h' → h' < 2 ^ 25 →
      readBuffer s0 (C_TD + 32 * h') 32 =
        c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts h') :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 25174018 s1 83894274 8388608 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 34896) ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * 2 ^ 23) ∧
      s1.getReg .x11 = 64#64 ∧
      s1.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 23) ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 19) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ h', 2 ^ 23 ≤ h' → h' < 2 ^ 25 →
        readBuffer s1 (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
      CommitMemOutside s0 s1 (C_TD + 32 * 2 ^ 23) (C_TD + 32 * 2 ^ 24) := by
  have hCT : C_TD = 4294971424 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  have hx10' : s0.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * 2 ^ 24) := by
    simpa only [show 32 * 2 ^ 25 = 64 * 2 ^ 24 by decide] using hx10
  have hind : ∀ n ≤ 4095,
      ∃ sn,
        DetRun oracle (submission.image .commit) s0 (6146 * n) sn (20482 * n) (2048 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 28747) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sn.getReg reg = s0.getReg reg) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 24 - 2048 * n)) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 24 - 2048 * n)) ∧
        (∀ h', 2 ^ 24 - 2048 * n ≤ h' → h' < 2 ^ 25 →
          readBuffer sn (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
        CommitMemOutside s0 sn (C_TD + 32 * (2 ^ 24 - 2048 * n)) (C_TD + 32 * 2 ^ 24) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨s0, DetRun.refl _ _ _, hpc, fun _ _ _ => rfl,
        by simpa using hx10', by simpa using hx12,
        fun h' h1 h2 => hheap0 h' (by omega) h2, CommitMemOutside.refl _ _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrun_n, hpcn, hregn, hx10n, hx12n, hheapn, hpresn⟩ := ih (by omega)
      obtain ⟨se, hbody, hpce, hrege, hx10e, hx12e, hheape, hprese⟩ :=
        c_l1_chunk_body h512 oracle msg salts sn n (by omega) hpcn
          ((hregn .x5 (by decide) (by decide)).trans hx5) hx10n
          ((hregn .x11 (by decide) (by decide)).trans hx11) hx12n
          ((hregn .x13 (by decide) (by decide)).trans hx13) hheapn
      obtain ⟨hlatch, hpc_b, hmem_b, hreg_b⟩ :=
        c_l1_latch_back oracle n (by omega) se hpce hx12e
          ((hrege .x19 (by decide) (by decide)).trans ((hregn .x19 (by decide) (by decide)).trans hx19))
      refine ⟨_, by simpa [Nat.mul_succ, Nat.add_assoc] using (hrun_n.trans hbody).trans hlatch,
        hpc_b, fun reg h10 h12 => (hreg_b reg).trans ((hrege reg h10 h12).trans (hregn reg h10 h12)),
        (hreg_b .x10).trans hx10e, (hreg_b .x12).trans hx12e, ?_, ?_⟩
      · intro h' h1 h2
        rw [c_readBuffer_of_mem_eq hmem_b]; exact hheape h' h1 h2
      · exact ((hpresn.mono (lo' := C_TD + 32 * (2 ^ 24 - 2048 * (n + 1))) (hi' := C_TD + 32 * 2 ^ 24) (by omega) (le_refl _)).trans
            (hprese.mono (lo' := C_TD + 32 * (2 ^ 24 - 2048 * (n + 1))) (hi' := C_TD + 32 * 2 ^ 24) (le_refl _) (by omega))).trans
          (CommitMemOutside.of_mem_eq hmem_b _ _)
  obtain ⟨sp, hrun_p, hpcp, hregp, hx10p, hx12p, hheapp, hpresp⟩ := hind 4095 (le_refl _)
  obtain ⟨se, hbody, hpce, hrege, hx10e, hx12e, hheape, hprese⟩ :=
    c_l1_chunk_body h512 oracle msg salts sp 4095 (by omega) hpcp
      ((hregp .x5 (by decide) (by decide)).trans hx5) hx10p
      ((hregp .x11 (by decide) (by decide)).trans hx11) hx12p
      ((hregp .x13 (by decide) (by decide)).trans hx13) hheapp
  obtain ⟨hlatch, hpc_l, hmem_l, hreg_l⟩ :=
    c_l1_latch_exit oracle se hpce hx12e
      ((hrege .x19 (by decide) (by decide)).trans ((hregp .x19 (by decide) (by decide)).trans hx19))
  let sLoop := execInstrBr se (.BEQ .x12 .x19 (8#13))
  let sFin := c_midL1Instrs.foldl execInstrBr sLoop
  have hmid_run := c_midL1_run oracle sLoop hpc_l
  have hsub23 : 2 ^ 24 - 2048 * 4096 = 2 ^ 23 := by decide
  obtain ⟨hpc_f, hmem_f, hx5_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx19_f, hx26_f⟩ :=
    c_midL1_spec sLoop hpc_l
      ((hreg_l .x5).trans ((hrege .x5 (by decide) (by decide)).trans ((hregp .x5 (by decide) (by decide)).trans hx5)))
      ((hreg_l .x9).trans ((hrege .x9 (by decide) (by decide)).trans ((hregp .x9 (by decide) (by decide)).trans hx9)))
      (by simpa only [hsub23] using (hreg_l .x10).trans hx10e)
      ((hreg_l .x11).trans ((hrege .x11 (by decide) (by decide)).trans ((hregp .x11 (by decide) (by decide)).trans hx11)))
      (by simpa only [hsub23] using (hreg_l .x12).trans hx12e)
      ((hreg_l .x13).trans ((hrege .x13 (by decide) (by decide)).trans ((hregp .x13 (by decide) (by decide)).trans hx13)))
      ((hreg_l .x26).trans ((hrege .x26 (by decide) (by decide)).trans ((hregp .x26 (by decide) (by decide)).trans hx26)))
  refine ⟨sFin,
    by simpa only [show 6146 * 4095 + 6144 + 1 + 3 = 25174018 by decide,
      show 20482 * 4095 + 20480 + 1 + 3 = 83894274 by decide,
      show 2048 * 4095 + 2048 + 0 + 0 = 8388608 by decide] using
      (((hrun_p.trans hbody).trans hlatch).trans hmid_run),
    hpc_f, hx5_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx19_f, hx26_f, ?_, ?_⟩
  · intro h' h1 h2
    rw [c_readBuffer_of_mem_eq hmem_f, c_readBuffer_of_mem_eq hmem_l]
    exact hheape h' (by omega) h2
  · exact (((hpresp.mono (lo' := C_TD + 32 * 2 ^ 23) (hi' := C_TD + 32 * 2 ^ 24) (by omega) (le_refl _)).trans
        (hprese.mono (lo' := C_TD + 32 * 2 ^ 23) (hi' := C_TD + 32 * 2 ^ 24) (by omega) (by omega))).trans
      (CommitMemOutside.of_mem_eq hmem_l _ _)).trans (CommitMemOutside.of_mem_eq hmem_f _ _)

/-! ### 3. Phase 3 (`L2..L5`: words `34896..43095`) -/

private theorem c_pc_beq_43088 :
    BitVec.ofNat 64 (0x1000 + 4 * 43088) + signExtend13 (8#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 43090) := by decide

private theorem c_pc_jal_43089 :
    BitVec.ofNat 64 (0x1000 + 4 * 43089) + signExtend21 (2064380#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 34896) := by decide

private def c_midL25Instrs : List Instr :=
  [.ADDI .x27 .x0 (1#12), .SLLI .x27 .x27 (46#6), .ADDI .x27 .x27 (4095#12),
   .ADDI .x6 .x0 (1#12), .SLLI .x6 .x6 (12#6), .ADD .x19 .x9 .x6]

private theorem c_midL25_run (oracle : Oracle) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 43090)) :
    DetRun oracle (submission.image .commit) s 6 (c_midL25Instrs.foldl execInstrBr s) 6 0 := by
  have hall : ∀ ins ∈ c_midL25Instrs, c_isPureAlu ins = true := by decide
  apply c_exec_alu_list c_midL25Instrs s
  intro i hi
  have hi' : i < 6 := hi
  have hpc_i : ((c_midL25Instrs.take i).foldl execInstrBr s).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (43090 + i)) := by
    have h := c_foldl_pureAlu_pc (c_midL25Instrs.take i) s (0x1000 + 4 * 43090)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitMidL25Instr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem c_midL25_spec (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 43090))
    (hx5 : s.getReg .x5 = 0#64)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * 2 ^ 19))
    (hx11 : s.getReg .x11 = 64#64)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 19))
    (hx13 : s.getReg .x13 = 0#64)
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s' := c_midL25Instrs.foldl execInstrBr s
    s'.pc = BitVec.ofNat 64 (0x1000 + 4 * 43096) ∧
    s'.mem = s.mem ∧
    s'.getReg .x5 = 0#64 ∧
    s'.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s'.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * 2 ^ 19) ∧
    s'.getReg .x11 = 64#64 ∧
    s'.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 19) ∧
    s'.getReg .x13 = 0#64 ∧
    s'.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 128) ∧
    s'.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
    s'.getReg .x27 = mask238Word := by
  have hall : ∀ ins ∈ c_midL25Instrs, c_isPureAlu ins = true := by decide
  refine ⟨?_, c_foldl_pureAlu_mem c_midL25Instrs s hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (c_foldl_pureAlu_pc c_midL25Instrs s (0x1000 + 4 * 43090) hall hpc).trans (by decide)
  all_goals (
    simp only [c_midL25Instrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx5, hx9, hx10, hx11, hx12, hx13, hx26, mask238Word]
    try decide)

/-- One `L2..L5` node step (`ADDI -64; ADDI -32; ECALL; SH x12, x0, 30`):
4 steps, 11 cycles, 1 compression call. -/
private theorem c_l25_node_step (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (s : MachineState)
    (k h : Nat) (hk : k < 2048) (hlo : 2 ^ 19 ≤ h) (hhi : h < 2 ^ 23)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (34896 + 4 * k)))
    (hx5 : s.getReg .x5 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (h + 1)))
    (hx11 : s.getReg .x11 = 64#64)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (h + 1)))
    (hx13 : s.getReg .x13 = 0#64)
    (hchL : readBuffer s (C_TD + 32 * (2 * h)) 32 =
      c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts (2 * h))
    (hchR : readBuffer s (C_TD + 32 * (2 * h + 1)) 32 =
      c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts (2 * h + 1)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ s',
      DetRun oracle (submission.image .commit) s 4 s' 11 1 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (34896 + 4 * (k + 1))) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s'.getReg reg = s.getReg reg) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * h) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * h) ∧
      readBuffer s' (C_TD + 32 * h) 32 = c_heapVal c64 p200 msg salts h ∧
      CommitMemOutside s s' (C_TD + 32 * h) (C_TD + 32 * (h + 1)) := by
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hCT : C_TD = 4294971424 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  let raw := c64 (binaryInput (c_heapVal c64 p200 msg salts (2 * h)) (c_heapVal c64 p200 msg salts (2 * h + 1)))
  let s1 := execInstrBr s (.ADDI .x10 .x10 (4032#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (4064#12))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + 32 * h)) raw
  let s4 := execInstrBr s3 (.SH .x12 .x0 (30#12))
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (34896 + 4 * k + 1)) := c_pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (34896 + 4 * k + 2)) := c_pc_step_idx s1 _ hs1_pc
  have hs1_x10 : s1.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * h) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      c_bv64_add_neg64 (C_TD + 64 * (h + 1)) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_x10 : s2.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * h) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne .x12 .x10 (by decide), hs1_x10]
  have hs2_x12 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * h) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      c_getReg_setReg_ne .x10 .x12 (by decide), hx12,
      c_bv64_add_neg32 (C_TD + 32 * (h + 1)) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_mem : s2.mem = s.mem := (c_mem_exec_ADDI s1 _ _ _).trans (c_mem_exec_ADDI s _ _ _)
  have hs2_reg : ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s2.getReg reg = s.getReg reg := fun reg h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x12 reg (Ne.symm h12), c_getReg_setReg_ne .x10 reg (Ne.symm h10)]
  have hr0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_l25 s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc)) rfl
  have hr1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_l25 s1 k 1 hk (by omega) hs1_pc) rfl
  have hread : oracle.compression ((readBuffer s2 (C_TD + 64 * h) 64).cast h512.symm) = raw := by
    rw [c_readBuffer_of_mem_eq hs2_mem, readBuffer_binary]
    have haL : C_TD + 64 * h = C_TD + 32 * (2 * h) := by omega
    have haR : C_TD + 32 * (2 * h) + 32 = C_TD + 32 * (2 * h + 1) := by omega
    rw [haL, haR, hchL, hchR]
  have hr2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h512 (commit_fetch_l25 s2 k 2 hk (by omega) hs2_pc)
      ((hs2_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg .x13 (by decide) (by decide)).trans hx13)
      (C_TD + 64 * h) (C_TD + 32 * h) hs2_x10 hs2_x12
      (by omega) (by omega) (by omega) (by omega) raw hread
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (34896 + 4 * k + 3)) := by
    rw [c_pc_writeBits, c_pc_step_idx s2 _ hs2_pc]
  have hs3_x12 : s3.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * h) :=
    (writeBits_register s2 _ raw .x12).trans hs2_x12
  have hsh_addr : s3.getReg .x12 + signExtend12 (30#12) = BitVec.ofNat 64 (C_TD + 32 * h + 30) := by
    rw [hs3_x12, c_add_signExtend12_ofNat_small _ 30 (by omega)]
  have hr3 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (commit_fetch_l25 s3 k 3 hk (by omega) hs3_pc)
      (c_ordinaryStep_SH s3 .x12 .x0 (30#12) (by
        rw [hsh_addr]; exact c_accessValid_ofNat _ 2 (by omega) (by omega)))
  have hs4_mem : s4.mem = (s3.setHalfword (BitVec.ofNat 64 (C_TD + 32 * h + 30)) 0#16).mem := by
    simp only [s4, execInstrBr, c_mem_setPC, hsh_addr, c_getReg_x0]; rfl
  refine ⟨s4, ((hr0.trans hr1).trans hr2).trans hr3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c_pc_exec_SH, c_pc_step_idx s3 _ hs3_pc]; exact congrArg (BitVec.ofNat 64) (by omega)
  · intro reg h10 h12
    exact (c_reg_exec_SH s3 _ _ _ reg).trans ((writeBits_register s2 _ raw reg).trans (hs2_reg reg h10 h12))
  · exact (c_reg_exec_SH s3 _ _ _ .x10).trans ((writeBits_register s2 _ raw .x10).trans hs2_x10)
  · exact (c_reg_exec_SH s3 _ _ _ .x12).trans hs3_x12
  · rw [c_readBuffer_of_mem_eq hs4_mem, sh_zero_mask240 s3 (C_TD + 32 * h) (by omega) (by omega),
      writeBits_readBuffer_digest s2 _ raw]
    exact (c_heapVal_step_l25 c64 p200 msg salts h hlo hhi).symm
  · have hp23 : CommitMemOutside s s3 (C_TD + 32 * h) (C_TD + 32 * (h + 1)) :=
      (CommitMemOutside.of_mem_eq hs2_mem _ _).trans
        (by simpa only [show C_TD + 32 * h + (256 + 7) / 8 = C_TD + 32 * (h + 1) by omega] using
          c_memPreserved_writeBits s2 (C_TD + 32 * h) raw (by omega))
    have hp34 : CommitMemOutside s3 s4 (C_TD + 32 * h) (C_TD + 32 * (h + 1)) :=
      ((c_memPreserved_setHalfword s3 (C_TD + 32 * h + 30) 0#16 (by omega) (by omega)).mono
        (by omega) (by omega)).trans (CommitMemOutside.of_mem_eq hs4_mem _ _)
    exact hp23.trans hp34

/-- One 2048-node `L2..L5` chunk body (`34896..43087`): 8192 steps, 22528 cycles, 2048 calls. -/
private theorem c_l25_chunk_body (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (sc : MachineState)
    (chunkIdx : Nat) (hchunk : chunkIdx < 3840)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 34896))
    (hx5 : sc.getReg .x5 = 0#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 23 - 2048 * chunkIdx)))
    (hx11 : sc.getReg .x11 = 64#64)
    (hx12 : sc.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 23 - 2048 * chunkIdx)))
    (hx13 : sc.getReg .x13 = 0#64)
    (hheap : ∀ h', 2 ^ 23 - 2048 * chunkIdx ≤ h' → h' < 2 ^ 25 →
      readBuffer sc (C_TD + 32 * h') 32 =
        c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts h') :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ se,
      DetRun oracle (submission.image .commit) sc 8192 se 22528 2048 ∧
      se.pc = BitVec.ofNat 64 (0x1000 + 4 * 43088) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → se.getReg reg = sc.getReg reg) ∧
      se.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 23 - 2048 * (chunkIdx + 1))) ∧
      se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 23 - 2048 * (chunkIdx + 1))) ∧
      (∀ h', 2 ^ 23 - 2048 * (chunkIdx + 1) ≤ h' → h' < 2 ^ 25 →
        readBuffer se (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
      CommitMemOutside sc se (C_TD + 32 * (2 ^ 23 - 2048 * (chunkIdx + 1)))
        (C_TD + 32 * (2 ^ 23 - 2048 * chunkIdx)) := by
  have hCT : C_TD = 4294971424 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  have hind : ∀ k ≤ 2048,
      ∃ sk,
        DetRun oracle (submission.image .commit) sc (4 * k) sk (11 * k) k ∧
        sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (34896 + 4 * k)) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sk.getReg reg = sc.getReg reg) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 23 - 2048 * chunkIdx - k)) ∧
        sk.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 23 - 2048 * chunkIdx - k)) ∧
        (∀ h', 2 ^ 23 - 2048 * chunkIdx - k ≤ h' → h' < 2 ^ 25 →
          readBuffer sk (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
        CommitMemOutside sc sk (C_TD + 32 * (2 ^ 23 - 2048 * chunkIdx - k))
          (C_TD + 32 * (2 ^ 23 - 2048 * chunkIdx)) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12,
        fun h' h1 h2 => hheap h' (by omega) h2, CommitMemOutside.refl _ _ _⟩
    | succ k ih =>
      obtain ⟨sk, hrun_k, hpck, hregk, hx10k, hx12k, hheapk, hpresk⟩ := ih (by omega)
      set h := 2 ^ 23 - 2048 * chunkIdx - (k + 1)
      have hh_succ : h + 1 = 2 ^ 23 - 2048 * chunkIdx - k := by omega
      have hlo : 2 ^ 19 ≤ h := by omega
      have hhi : h < 2 ^ 23 := by omega
      obtain ⟨s', hst, hpc', hreg', hx10', hx12', hval', hpres'⟩ :=
        c_l25_node_step h512 oracle msg salts sk k h (by omega) hlo hhi hpck
          ((hregk .x5 (by decide) (by decide)).trans hx5)
          (by simpa only [hh_succ] using hx10k)
          ((hregk .x11 (by decide) (by decide)).trans hx11)
          (by simpa only [hh_succ] using hx12k)
          ((hregk .x13 (by decide) (by decide)).trans hx13)
          (hheapk (2 * h) (by omega) (by omega))
          (hheapk (2 * h + 1) (by omega) (by omega))
      refine ⟨s', by simpa [Nat.mul_succ, Nat.add_assoc] using hrun_k.trans hst,
        hpc', fun reg h10 h12 => (hreg' reg h10 h12).trans (hregk reg h10 h12),
        hx10', hx12', ?_, ?_⟩
      · intro h' h1 h2
        by_cases heq : h' = h
        · subst heq; exact hval'
        · exact (hpres'.readBuffer_eq (by omega) (by omega)).trans (hheapk h' (by omega) h2)
      · exact (hpresk.mono (lo' := C_TD + 32 * h) (hi' := C_TD + 32 * (2 ^ 23 - 2048 * chunkIdx)) (by omega) (le_refl _)).trans
          (hpres'.mono (lo' := C_TD + 32 * h) (hi' := C_TD + 32 * (2 ^ 23 - 2048 * chunkIdx)) (le_refl _) (by omega))
  obtain ⟨se, hrun, hpce, hrege, hx10e, hx12e, hheape, hprese⟩ := hind 2048 (le_refl _)
  have hsub : 2 ^ 23 - 2048 * chunkIdx - 2048 = 2 ^ 23 - 2048 * (chunkIdx + 1) := by omega
  rw [hsub] at hx10e hx12e hheape hprese
  exact ⟨se, hrun, hpce, hrege, hx10e, hx12e, hheape, hprese⟩

private theorem c_l25_latch_back (oracle : Oracle) (chunkIdx : Nat) (hchunk : chunkIdx < 3839)
    (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 43088))
    (hx12 : se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 23 - 2048 * (chunkIdx + 1))))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 19)) :
    let sb := execInstrBr (execInstrBr se (.BEQ .x12 .x19 (8#13))) (.JAL .x0 (2064380#21))
    DetRun oracle (submission.image .commit) se 2 sb 2 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 34896) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  have hCT : C_TD = 4294971424 := rfl
  let s1 := execInstrBr se (.BEQ .x12 .x19 (8#13))
  let s2 := execInstrBr s1 (.JAL .x0 (2064380#21))
  have hst1 : DetRun oracle (submission.image .commit) se 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_commitMidL25Instr se 43088 (by omega) (by omega) hpc) rfl
  have hne : (se.getReg .x12 == se.getReg .x19) = false := by
    rw [hx12, hx19, beq_eq_false_iff_ne]
    exact c_bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 43089) := by
    simp only [s1, execInstrBr, hne, Bool.false_eq_true, ite_false, c_pc_setPC]
    exact c_pc_step_idx se 43088 hpc
  have hst2 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_commitMidL25Instr s1 43089 (by omega) (by omega) hs1_pc) rfl
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 34896) := by
    simp only [s2, execInstrBr, c_pc_setPC, hs1_pc]; exact c_pc_jal_43089
  exact ⟨hst1.trans hst2, hs2_pc,
    (c_mem_exec_JAL s1 _ _).trans (c_mem_exec_BEQ se _ _ _),
    fun reg => (c_reg_exec_JAL0 s1 _ reg).trans (c_reg_exec_BEQ se _ _ _ reg)⟩

private theorem c_l25_latch_exit (oracle : Oracle) (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 43088))
    (hx12 : se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 23 - 2048 * 3840)))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 19)) :
    let sb := execInstrBr se (.BEQ .x12 .x19 (8#13))
    DetRun oracle (submission.image .commit) se 1 sb 1 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 43090) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  let sb := execInstrBr se (.BEQ .x12 .x19 (8#13))
  have hst : DetRun oracle (submission.image .commit) se 1 sb 1 0 :=
    DetRun.step1 (commit_fetch_commitMidL25Instr se 43088 (by omega) (by omega) hpc) rfl
  have heq : (se.getReg .x12 == se.getReg .x19) = true := by
    rw [hx12, hx19, show 2 ^ 23 - 2048 * 3840 = 2 ^ 19 by decide]
    exact beq_self_eq_true _
  have hpc' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 43090) := by
    simp only [sb, execInstrBr, heq, ite_true, c_pc_setPC, hpc]; exact c_pc_beq_43088
  exact ⟨hst, hpc', c_mem_exec_BEQ se _ _ _, c_reg_exec_BEQ se _ _ _⟩

/-- Full Phase 3 (`L2..L5` + Phase 4 setup, words `34896..43095`):
`31,464,965` steps, `86,515,205` cycles, `7,864,320` calls. -/
theorem commit_phase3 (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 34896))
    (hx5 : s0.getReg .x5 = 0#64)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * 2 ^ 23))
    (hx11 : s0.getReg .x11 = 64#64)
    (hx12 : s0.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 23))
    (hx13 : s0.getReg .x13 = 0#64)
    (hx19 : s0.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 19))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hheap0 : ∀ h', 2 ^ 23 ≤ h' → h' < 2 ^ 25 →
      readBuffer s0 (C_TD + 32 * h') 32 =
        c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts h') :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 31464965 s1 86515205 7864320 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 43096) ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * 2 ^ 19) ∧
      s1.getReg .x11 = 64#64 ∧
      s1.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 19) ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 128) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      s1.getReg .x27 = mask238Word ∧
      (∀ h', 2 ^ 19 ≤ h' → h' < 2 ^ 25 →
        readBuffer s1 (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
      CommitMemOutside s0 s1 (C_TD + 32 * 2 ^ 19) (C_TD + 32 * 2 ^ 23) := by
  have hCT : C_TD = 4294971424 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  have hind : ∀ n ≤ 3839,
      ∃ sn,
        DetRun oracle (submission.image .commit) s0 (8194 * n) sn (22530 * n) (2048 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 34896) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sn.getReg reg = s0.getReg reg) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 23 - 2048 * n)) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 23 - 2048 * n)) ∧
        (∀ h', 2 ^ 23 - 2048 * n ≤ h' → h' < 2 ^ 25 →
          readBuffer sn (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
        CommitMemOutside s0 sn (C_TD + 32 * (2 ^ 23 - 2048 * n)) (C_TD + 32 * 2 ^ 23) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨s0, DetRun.refl _ _ _, hpc, fun _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12,
        fun h' h1 h2 => hheap0 h' (by omega) h2, CommitMemOutside.refl _ _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrun_n, hpcn, hregn, hx10n, hx12n, hheapn, hpresn⟩ := ih (by omega)
      obtain ⟨se, hbody, hpce, hrege, hx10e, hx12e, hheape, hprese⟩ :=
        c_l25_chunk_body h512 oracle msg salts sn n (by omega) hpcn
          ((hregn .x5 (by decide) (by decide)).trans hx5) hx10n
          ((hregn .x11 (by decide) (by decide)).trans hx11) hx12n
          ((hregn .x13 (by decide) (by decide)).trans hx13) hheapn
      obtain ⟨hlatch, hpc_b, hmem_b, hreg_b⟩ :=
        c_l25_latch_back oracle n (by omega) se hpce hx12e
          ((hrege .x19 (by decide) (by decide)).trans ((hregn .x19 (by decide) (by decide)).trans hx19))
      refine ⟨_, by simpa [Nat.mul_succ, Nat.add_assoc] using (hrun_n.trans hbody).trans hlatch,
        hpc_b, fun reg h10 h12 => (hreg_b reg).trans ((hrege reg h10 h12).trans (hregn reg h10 h12)),
        (hreg_b .x10).trans hx10e, (hreg_b .x12).trans hx12e, ?_, ?_⟩
      · intro h' h1 h2
        rw [c_readBuffer_of_mem_eq hmem_b]; exact hheape h' h1 h2
      · exact ((hpresn.mono (lo' := C_TD + 32 * (2 ^ 23 - 2048 * (n + 1))) (hi' := C_TD + 32 * 2 ^ 23) (by omega) (le_refl _)).trans
            (hprese.mono (lo' := C_TD + 32 * (2 ^ 23 - 2048 * (n + 1))) (hi' := C_TD + 32 * 2 ^ 23) (le_refl _) (by omega))).trans
          (CommitMemOutside.of_mem_eq hmem_b _ _)
  obtain ⟨sp, hrun_p, hpcp, hregp, hx10p, hx12p, hheapp, hpresp⟩ := hind 3839 (le_refl _)
  obtain ⟨se, hbody, hpce, hrege, hx10e, hx12e, hheape, hprese⟩ :=
    c_l25_chunk_body h512 oracle msg salts sp 3839 (by omega) hpcp
      ((hregp .x5 (by decide) (by decide)).trans hx5) hx10p
      ((hregp .x11 (by decide) (by decide)).trans hx11) hx12p
      ((hregp .x13 (by decide) (by decide)).trans hx13) hheapp
  obtain ⟨hlatch, hpc_l, hmem_l, hreg_l⟩ :=
    c_l25_latch_exit oracle se hpce hx12e
      ((hrege .x19 (by decide) (by decide)).trans ((hregp .x19 (by decide) (by decide)).trans hx19))
  let sLoop := execInstrBr se (.BEQ .x12 .x19 (8#13))
  let sFin := c_midL25Instrs.foldl execInstrBr sLoop
  have hmid_run := c_midL25_run oracle sLoop hpc_l
  have hsub19 : 2 ^ 23 - 2048 * 3840 = 2 ^ 19 := by decide
  obtain ⟨hpc_f, hmem_f, hx5_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx19_f, hx26_f, hx27_f⟩ :=
    c_midL25_spec sLoop hpc_l
      ((hreg_l .x5).trans ((hrege .x5 (by decide) (by decide)).trans ((hregp .x5 (by decide) (by decide)).trans hx5)))
      ((hreg_l .x9).trans ((hrege .x9 (by decide) (by decide)).trans ((hregp .x9 (by decide) (by decide)).trans hx9)))
      (by simpa only [hsub19] using (hreg_l .x10).trans hx10e)
      ((hreg_l .x11).trans ((hrege .x11 (by decide) (by decide)).trans ((hregp .x11 (by decide) (by decide)).trans hx11)))
      (by simpa only [hsub19] using (hreg_l .x12).trans hx12e)
      ((hreg_l .x13).trans ((hrege .x13 (by decide) (by decide)).trans ((hregp .x13 (by decide) (by decide)).trans hx13)))
      ((hreg_l .x26).trans ((hrege .x26 (by decide) (by decide)).trans ((hregp .x26 (by decide) (by decide)).trans hx26)))
  refine ⟨sFin,
    by simpa only [show 8194 * 3839 + 8192 + 1 + 6 = 31464965 by decide,
      show 22530 * 3839 + 22528 + 1 + 6 = 86515205 by decide,
      show 2048 * 3839 + 2048 + 0 + 0 = 7864320 by decide] using
      (((hrun_p.trans hbody).trans hlatch).trans hmid_run),
    hpc_f, hx5_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx19_f, hx26_f, hx27_f, ?_, ?_⟩
  · intro h' h1 h2
    rw [c_readBuffer_of_mem_eq hmem_f, c_readBuffer_of_mem_eq hmem_l]
    exact hheape h' (by omega) h2
  · exact (((hpresp.mono (lo' := C_TD + 32 * 2 ^ 19) (hi' := C_TD + 32 * 2 ^ 23) (by omega) (le_refl _)).trans
        (hprese.mono (lo' := C_TD + 32 * 2 ^ 19) (hi' := C_TD + 32 * 2 ^ 23) (by omega) (by omega))).trans
      (CommitMemOutside.of_mem_eq hmem_l _ _)).trans (CommitMemOutside.of_mem_eq hmem_f _ _)

/-! ### 4. Phase 4 (`L6..L23` bulk + tail) + Root (`L24`) + Copy + Halt Prep (`43096..43885`) -/

private theorem c_pc_bne_43864 :
    BitVec.ofNat 64 (0x1000 + 4 * 43864) + signExtend13 (5120#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 43096) := by decide

private theorem c_pc_bne_43872 :
    BitVec.ofNat 64 (0x1000 + 4 * 43872) + signExtend13 (8168#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 43866) := by decide

/-- Generic 6-instruction `L6..L23` masked-238 node step (`ADDI -64; ADDI -32; ECALL; LD/AND/SD`),
reused for both `l623_bulk` and `l623_tail`: 6 steps, 13 cycles, 1 compression call. -/
private theorem c_l623_node_step (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (s : MachineState)
    (basePc h : Nat) (hlo : 2 ≤ h) (hhi : h < 2 ^ 19)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hx5 : s.getReg .x5 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (h + 1)))
    (hx11 : s.getReg .x11 = 64#64)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (h + 1)))
    (hx13 : s.getReg .x13 = 0#64)
    (hx27 : s.getReg .x27 = mask238Word)
    (hfetch : ∀ j < 6, ∀ st : MachineState,
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + j)) →
      fetch (submission.image .commit) st = some (l623Instr j))
    (hchL : readBuffer s (C_TD + 32 * (2 * h)) 32 =
      c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts (2 * h))
    (hchR : readBuffer s (C_TD + 32 * (2 * h + 1)) 32 =
      c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts (2 * h + 1)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ s',
      DetRun oracle (submission.image .commit) s 6 s' 13 1 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 6)) ∧
      (∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → s'.getReg reg = s.getReg reg) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * h) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * h) ∧
      readBuffer s' (C_TD + 32 * h) 32 = c_heapVal c64 p200 msg salts h ∧
      CommitMemOutside s s' (C_TD + 32 * h) (C_TD + 32 * (h + 1)) := by
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hCT : C_TD = 4294971424 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  let raw := c64 (binaryInput (c_heapVal c64 p200 msg salts (2 * h)) (c_heapVal c64 p200 msg salts (2 * h + 1)))
  let s1 := execInstrBr s (.ADDI .x10 .x10 (4032#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (4064#12))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + 32 * h)) raw
  let s4 := execInstrBr s3 (.LD .x6 .x12 (24#12))
  let s5 := execInstrBr s4 (.AND .x6 .x6 .x27)
  let s6 := execInstrBr s5 (.SD .x12 .x6 (24#12))
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 1)) := c_pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2)) := c_pc_step_idx s1 _ hs1_pc
  have hs1_x10 : s1.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * h) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      c_bv64_add_neg64 (C_TD + 64 * (h + 1)) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_x10 : s2.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * h) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne .x12 .x10 (by decide), hs1_x10]
  have hs2_x12 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * h) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      c_getReg_setReg_ne .x10 .x12 (by decide), hx12,
      c_bv64_add_neg32 (C_TD + 32 * (h + 1)) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_mem : s2.mem = s.mem := (c_mem_exec_ADDI s1 _ _ _).trans (c_mem_exec_ADDI s _ _ _)
  have hs2_reg : ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s2.getReg reg = s.getReg reg := fun reg h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x12 reg (Ne.symm h12), c_getReg_setReg_ne .x10 reg (Ne.symm h10)]
  have hr0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (hfetch 0 (by omega) s (by simpa only [Nat.add_zero] using hpc)) rfl
  have hr1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (hfetch 1 (by omega) s1 hs1_pc) rfl
  have hread : oracle.compression ((readBuffer s2 (C_TD + 64 * h) 64).cast h512.symm) = raw := by
    rw [c_readBuffer_of_mem_eq hs2_mem, readBuffer_binary]
    have haL : C_TD + 64 * h = C_TD + 32 * (2 * h) := by omega
    have haR : C_TD + 32 * (2 * h) + 32 = C_TD + 32 * (2 * h + 1) := by omega
    rw [haL, haR, hchL, hchR]
  have hr2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h512 (hfetch 2 (by omega) s2 hs2_pc)
      ((hs2_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg .x13 (by decide) (by decide)).trans hx13)
      (C_TD + 64 * h) (C_TD + 32 * h) hs2_x10 hs2_x12
      (by omega) (by omega) (by omega) (by omega) raw hread
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 3)) := by
    rw [c_pc_writeBits, c_pc_step_idx s2 _ hs2_pc]
  have hs3_x12 : s3.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * h) :=
    (writeBits_register s2 _ raw .x12).trans hs2_x12
  have hs3_x27 : s3.getReg .x27 = mask238Word :=
    (writeBits_register s2 _ raw .x27).trans ((hs2_reg .x27 (by decide) (by decide)).trans hx27)
  have hld_addr : s3.getReg .x12 + signExtend12 (24#12) = BitVec.ofNat 64 (C_TD + 32 * h + 24) := by
    rw [hs3_x12, c_add_signExtend12_ofNat_small _ 24 (by omega)]
  have hr3 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (hfetch 3 (by omega) s3 hs3_pc)
      (c_ordinaryStep_LD s3 .x6 .x12 (24#12) (by
        rw [hld_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 4)) := by
    rw [c_pc_exec_LD, c_pc_step_idx s3 _ hs3_pc]
  have hr4 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (hfetch 4 (by omega) s4 hs4_pc) rfl
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 5)) := by
    rw [c_pc_exec_AND, c_pc_step_idx s4 _ hs4_pc]
  have hs5_x12 : s5.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * h) := by
    simp only [s5, s4, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x6 .x12 (by decide), hs3_x12]
  have hs5_x6 : s5.getReg .x6 = s3.getMem (BitVec.ofNat 64 (C_TD + 32 * h + 24)) &&& mask238Word := by
    have h4x6 : s4.getReg .x6 = s3.getMem (BitVec.ofNat 64 (C_TD + 32 * h + 24)) := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hld_addr]
    have h4x27 : s4.getReg .x27 = mask238Word := by
      simp only [s4, execInstrBr, MachineState.getReg_setPC,
        c_getReg_setReg_ne .x6 .x27 (by decide), hs3_x27]
    simp only [s5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), h4x6, h4x27]
  have hsd_addr : s5.getReg .x12 + signExtend12 (24#12) = BitVec.ofNat 64 (C_TD + 32 * h + 24) := by
    rw [hs5_x12, c_add_signExtend12_ofNat_small _ 24 (by omega)]
  have hr5 : DetRun oracle (submission.image .commit) s5 1 s6 1 0 :=
    DetRun.step1 (hfetch 5 (by omega) s5 hs5_pc)
      (c_ordinaryStep_SD s5 .x12 .x6 (24#12) (by
        rw [hsd_addr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hs5_mem : s5.mem = s3.mem := (c_mem_exec_AND s4 _ _ _).trans (c_mem_exec_LD s3 _ _ _)
  have hs6_mem : s6.mem =
      (s3.setMem (BitVec.ofNat 64 (C_TD + 32 * h + 24))
        (s3.getMem (BitVec.ofNat 64 (C_TD + 32 * h + 24)) &&& mask238Word)).mem := by
    simp only [s6, execInstrBr, c_mem_setPC, hsd_addr, hs5_x6, MachineState.setMem, hs5_mem]
  refine ⟨s6, (((((hr0.trans hr1).trans hr2).trans hr3).trans hr4).trans hr5), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c_pc_exec_SD, c_pc_step_idx s5 _ hs5_pc]
  · intro reg h6 h10 h12
    have h65 : s6.getReg reg = s5.getReg reg := c_reg_exec_SD s5 _ _ _ reg
    have h53 : s5.getReg reg = s3.getReg reg := by
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC,
        c_getReg_setReg_ne .x6 reg (Ne.symm h6)]
    exact (h65.trans h53).trans ((writeBits_register s2 _ raw reg).trans (hs2_reg reg h10 h12))
  · have h65 : s6.getReg .x10 = s5.getReg .x10 := c_reg_exec_SD s5 _ _ _ .x10
    have h53 : s5.getReg .x10 = s3.getReg .x10 := by
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne .x6 .x10 (by decide)]
    exact (h65.trans h53).trans ((writeBits_register s2 _ raw .x10).trans hs2_x10)
  · exact (c_reg_exec_SD s5 _ _ _ .x12).trans hs5_x12
  · rw [c_readBuffer_of_mem_eq hs6_mem, sd_and_mask238 s3 (C_TD + 32 * h) (by omega) (by omega),
      writeBits_readBuffer_digest s2 _ raw]
    exact (c_heapVal_step_l623 c64 p200 msg salts h hlo hhi).symm
  · have hp23 : CommitMemOutside s s3 (C_TD + 32 * h) (C_TD + 32 * (h + 1)) :=
      (CommitMemOutside.of_mem_eq hs2_mem _ _).trans
        (by simpa only [show C_TD + 32 * h + (256 + 7) / 8 = C_TD + 32 * (h + 1) by omega] using
          c_memPreserved_writeBits s2 (C_TD + 32 * h) raw (by omega))
    have hp36 : CommitMemOutside s3 s6 (C_TD + 32 * h) (C_TD + 32 * (h + 1)) :=
      ((c_memPreserved_setMem s3 (C_TD + 32 * h + 24)
        (s3.getMem (BitVec.ofNat 64 (C_TD + 32 * h + 24)) &&& mask238Word)
        (by omega) (by omega)).mono (by omega) (by omega)).trans
        (CommitMemOutside.of_mem_eq hs6_mem _ _)
    exact hp23.trans hp36

/-- One 128-node `l623_bulk` chunk body (`43096..43863`): 768 steps, 1664 cycles, 128 calls. -/
private theorem c_l623_bulk_chunk_body (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (sc : MachineState)
    (chunkIdx : Nat) (hchunk : chunkIdx < 4095)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 43096))
    (hx5 : sc.getReg .x5 = 0#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 19 - 128 * chunkIdx)))
    (hx11 : sc.getReg .x11 = 64#64)
    (hx12 : sc.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 19 - 128 * chunkIdx)))
    (hx13 : sc.getReg .x13 = 0#64)
    (hx27 : sc.getReg .x27 = mask238Word)
    (hheap : ∀ h', 2 ^ 19 - 128 * chunkIdx ≤ h' → h' < 2 ^ 25 →
      readBuffer sc (C_TD + 32 * h') 32 =
        c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts h') :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ se,
      DetRun oracle (submission.image .commit) sc 768 se 1664 128 ∧
      se.pc = BitVec.ofNat 64 (0x1000 + 4 * 43864) ∧
      (∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → se.getReg reg = sc.getReg reg) ∧
      se.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 19 - 128 * (chunkIdx + 1))) ∧
      se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 19 - 128 * (chunkIdx + 1))) ∧
      (∀ h', 2 ^ 19 - 128 * (chunkIdx + 1) ≤ h' → h' < 2 ^ 25 →
        readBuffer se (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
      CommitMemOutside sc se (C_TD + 32 * (2 ^ 19 - 128 * (chunkIdx + 1)))
        (C_TD + 32 * (2 ^ 19 - 128 * chunkIdx)) := by
  have hCT : C_TD = 4294971424 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  have hind : ∀ k ≤ 128,
      ∃ sk,
        DetRun oracle (submission.image .commit) sc (6 * k) sk (13 * k) k ∧
        sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (43096 + 6 * k)) ∧
        (∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → sk.getReg reg = sc.getReg reg) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 19 - 128 * chunkIdx - k)) ∧
        sk.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 19 - 128 * chunkIdx - k)) ∧
        (∀ h', 2 ^ 19 - 128 * chunkIdx - k ≤ h' → h' < 2 ^ 25 →
          readBuffer sk (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
        CommitMemOutside sc sk (C_TD + 32 * (2 ^ 19 - 128 * chunkIdx - k))
          (C_TD + 32 * (2 ^ 19 - 128 * chunkIdx)) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12,
        fun h' h1 h2 => hheap h' (by omega) h2, CommitMemOutside.refl _ _ _⟩
    | succ k ih =>
      obtain ⟨sk, hrun_k, hpck, hregk, hx10k, hx12k, hheapk, hpresk⟩ := ih (by omega)
      set h := 2 ^ 19 - 128 * chunkIdx - (k + 1)
      have hh_succ : h + 1 = 2 ^ 19 - 128 * chunkIdx - k := by omega
      obtain ⟨s', hst, hpc', hreg', hx10', hx12', hval', hpres'⟩ :=
        c_l623_node_step h512 oracle msg salts sk (43096 + 6 * k) h (by omega) (by omega) hpck
          ((hregk .x5 (by decide) (by decide) (by decide)).trans hx5)
          (by simpa only [hh_succ] using hx10k)
          ((hregk .x11 (by decide) (by decide) (by decide)).trans hx11)
          (by simpa only [hh_succ] using hx12k)
          ((hregk .x13 (by decide) (by decide) (by decide)).trans hx13)
          ((hregk .x27 (by decide) (by decide) (by decide)).trans hx27)
          (fun j hj st hpcst => commit_fetch_l623 st k j (by omega) hj hpcst)
          (hheapk (2 * h) (by omega) (by omega))
          (hheapk (2 * h + 1) (by omega) (by omega))
      refine ⟨s', by simpa [Nat.mul_succ, Nat.add_assoc] using hrun_k.trans hst,
        by simpa only [Nat.mul_succ, Nat.add_assoc] using hpc',
        fun reg h6 h10 h12 => (hreg' reg h6 h10 h12).trans (hregk reg h6 h10 h12),
        hx10', hx12', ?_, ?_⟩
      · intro h' h1 h2
        by_cases heq : h' = h
        · subst heq; exact hval'
        · exact (hpres'.readBuffer_eq (by omega) (by omega)).trans (hheapk h' (by omega) h2)
      · exact (hpresk.mono (lo' := C_TD + 32 * h) (hi' := C_TD + 32 * (2 ^ 19 - 128 * chunkIdx)) (by omega) (le_refl _)).trans
          (hpres'.mono (lo' := C_TD + 32 * h) (hi' := C_TD + 32 * (2 ^ 19 - 128 * chunkIdx)) (le_refl _) (by omega))
  obtain ⟨se, hrun, hpce, hrege, hx10e, hx12e, hheape, hprese⟩ := hind 128 (le_refl _)
  have hsub : 2 ^ 19 - 128 * chunkIdx - 128 = 2 ^ 19 - 128 * (chunkIdx + 1) := by omega
  rw [hsub] at hx10e hx12e hheape hprese
  exact ⟨se, hrun, hpce, hrege, hx10e, hx12e, hheape, hprese⟩

/-- Isolated backward `BNE x12, x19, 5120#13` at word `43864` (taken vs exit). -/
private theorem c_l623_bulk_bne_back (oracle : Oracle) (chunkIdx : Nat) (hchunk : chunkIdx < 4094)
    (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 43864))
    (hx12 : se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 19 - 128 * (chunkIdx + 1))))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 128)) :
    let sb := execInstrBr se (.BNE .x12 .x19 (5120#13))
    DetRun oracle (submission.image .commit) se 1 sb 1 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 43096) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  have hCT : C_TD = 4294971424 := rfl
  let sb := execInstrBr se (.BNE .x12 .x19 (5120#13))
  have hst : DetRun oracle (submission.image .commit) se 1 sb 1 0 :=
    DetRun.step1 (commit_fetch_commitTailInstr se 43864 (by omega) (by omega) hpc) rfl
  have hne : (se.getReg .x12 != se.getReg .x19) = true := by
    rw [hx12, hx19, bne_iff_ne]
    exact c_bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
  have hpc' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 43096) := by
    simp only [sb, execInstrBr, hne, ite_true, c_pc_setPC, hpc]; exact c_pc_bne_43864
  exact ⟨hst, hpc', c_mem_exec_BNE se _ _ _, c_reg_exec_BNE se _ _ _⟩

private theorem c_l623_bulk_bne_exit (oracle : Oracle) (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 43864))
    (hx12 : se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 19 - 128 * 4095)))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 128)) :
    let sb := execInstrBr se (.BNE .x12 .x19 (5120#13))
    DetRun oracle (submission.image .commit) se 1 sb 1 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 43865) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  let sb := execInstrBr se (.BNE .x12 .x19 (5120#13))
  have hst : DetRun oracle (submission.image .commit) se 1 sb 1 0 :=
    DetRun.step1 (commit_fetch_commitTailInstr se 43864 (by omega) (by omega) hpc) rfl
  have heq : (se.getReg .x12 != se.getReg .x19) = false := by
    rw [hx12, hx19, show 2 ^ 19 - 128 * 4095 = 128 by decide]; exact bne_self_eq_false _
  have hpc' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 43865) := by
    simp only [sb, execInstrBr, heq, Bool.false_eq_true, ite_false, c_pc_setPC]
    exact c_pc_step_idx se 43864 hpc
  exact ⟨hst, hpc', c_mem_exec_BNE se _ _ _, c_reg_exec_BNE se _ _ _⟩

/-- Isolated backward `BNE x12, x19, 8168#13` at word `43872` (taken vs exit). -/
private theorem c_l623_tail_bne_back (oracle : Oracle) (h : Nat) (hlo : 3 ≤ h) (hhi : h < 128)
    (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 43872))
    (hx12 : se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * h))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2)) :
    let sb := execInstrBr se (.BNE .x12 .x19 (8168#13))
    DetRun oracle (submission.image .commit) se 1 sb 1 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 43866) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  have hCT : C_TD = 4294971424 := rfl
  let sb := execInstrBr se (.BNE .x12 .x19 (8168#13))
  have hst : DetRun oracle (submission.image .commit) se 1 sb 1 0 :=
    DetRun.step1 (commit_fetch_commitTailInstr se 43872 (by omega) (by omega) hpc) rfl
  have hne : (se.getReg .x12 != se.getReg .x19) = true := by
    rw [hx12, hx19, bne_iff_ne]
    exact c_bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
  have hpc' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 43866) := by
    simp only [sb, execInstrBr, hne, ite_true, c_pc_setPC, hpc]; exact c_pc_bne_43872
  exact ⟨hst, hpc', c_mem_exec_BNE se _ _ _, c_reg_exec_BNE se _ _ _⟩

private theorem c_l623_tail_bne_exit (oracle : Oracle) (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 43872))
    (hx12 : se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2)) :
    let sb := execInstrBr se (.BNE .x12 .x19 (8168#13))
    DetRun oracle (submission.image .commit) se 1 sb 1 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 43873) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  let sb := execInstrBr se (.BNE .x12 .x19 (8168#13))
  have hst : DetRun oracle (submission.image .commit) se 1 sb 1 0 :=
    DetRun.step1 (commit_fetch_commitTailInstr se 43872 (by omega) (by omega) hpc) rfl
  have heq : (se.getReg .x12 != se.getReg .x19) = false := by
    rw [hx12, hx19]; exact bne_self_eq_false _
  have hpc' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 43873) := by
    simp only [sb, execInstrBr, heq, Bool.false_eq_true, ite_false, c_pc_setPC]
    exact c_pc_step_idx se 43872 hpc
  exact ⟨hst, hpc', c_mem_exec_BNE se _ _ _, c_reg_exec_BNE se _ _ _⟩

/-- Full Phase 4 + Root + Copy + Halt Prep (`words 43096..43885`):
`3,149,951` steps, `6,819,960` cycles, `524,287` calls. Lands at `pc = 43886` (`ECALL HALT(0)`). -/
theorem commit_phase4_and_root (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt192) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 43096))
    (hx5 : s0.getReg .x5 = 0#64)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * 2 ^ 19))
    (hx11 : s0.getReg .x11 = 64#64)
    (hx12 : s0.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 19))
    (hx13 : s0.getReg .x13 = 0#64)
    (hx19 : s0.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 128))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hx27 : s0.getReg .x27 = mask238Word)
    (hheap0 : ∀ h', 2 ^ 19 ≤ h' → h' < 2 ^ 25 →
      readBuffer s0 (C_TD + 32 * h') 32 =
        c_heapVal (fun x => oracle.compression (x.cast h512.symm)) oracle.permutation msg salts h') :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ sHalt,
      DetRun oracle (submission.image .commit) s0 3149951 sHalt 6819960 524287 ∧
      sHalt.pc = BitVec.ofNat 64 (0x1000 + 4 * 43886) ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      readBuffer sHalt C_CMT 32 = rootVal c64 p200 msg salts ∧
      (∀ h', 1 ≤ h' → h' < 2 ^ 25 →
        readBuffer sHalt (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
      CommitMemOutside s0 sHalt C_CMT (C_TD + 32 * 2 ^ 19) := by
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hCT : C_TD = 4294971424 := rfl
  have hCC : C_CMT = 4294971392 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  -- 4A. `l623_bulk`: 4094 back chunks + 1 final chunk (4095 * 769 = 3,149,055 steps, 6,818,175 cycles, 524,160 calls)
  have hbulk_ind : ∀ n ≤ 4094,
      ∃ sn,
        DetRun oracle (submission.image .commit) s0 (769 * n) sn (1665 * n) (128 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 43096) ∧
        (∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → sn.getReg reg = s0.getReg reg) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (2 ^ 19 - 128 * n)) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (2 ^ 19 - 128 * n)) ∧
        (∀ h', 2 ^ 19 - 128 * n ≤ h' → h' < 2 ^ 25 →
          readBuffer sn (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
        CommitMemOutside s0 sn (C_TD + 32 * (2 ^ 19 - 128 * n)) (C_TD + 32 * 2 ^ 19) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨s0, DetRun.refl _ _ _, hpc, fun _ _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12,
        fun h' h1 h2 => hheap0 h' (by omega) h2, CommitMemOutside.refl _ _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrun_n, hpcn, hregn, hx10n, hx12n, hheapn, hpresn⟩ := ih (by omega)
      obtain ⟨se, hbody, hpce, hrege, hx10e, hx12e, hheape, hprese⟩ :=
        c_l623_bulk_chunk_body h512 oracle msg salts sn n (by omega) hpcn
          ((hregn .x5 (by decide) (by decide) (by decide)).trans hx5) hx10n
          ((hregn .x11 (by decide) (by decide) (by decide)).trans hx11) hx12n
          ((hregn .x13 (by decide) (by decide) (by decide)).trans hx13)
          ((hregn .x27 (by decide) (by decide) (by decide)).trans hx27) hheapn
      obtain ⟨hlatch, hpc_b, hmem_b, hreg_b⟩ :=
        c_l623_bulk_bne_back oracle n (by omega) se hpce hx12e
          ((hrege .x19 (by decide) (by decide) (by decide)).trans
            ((hregn .x19 (by decide) (by decide) (by decide)).trans hx19))
      refine ⟨_, by simpa [Nat.mul_succ, Nat.add_assoc] using (hrun_n.trans hbody).trans hlatch,
        hpc_b, fun reg h6 h10 h12 => (hreg_b reg).trans ((hrege reg h6 h10 h12).trans (hregn reg h6 h10 h12)),
        (hreg_b .x10).trans hx10e, (hreg_b .x12).trans hx12e, ?_, ?_⟩
      · intro h' h1 h2; rw [c_readBuffer_of_mem_eq hmem_b]; exact hheape h' h1 h2
      · exact ((hpresn.mono (lo' := C_TD + 32 * (2 ^ 19 - 128 * (n + 1))) (hi' := C_TD + 32 * 2 ^ 19) (by omega) (le_refl _)).trans
            (hprese.mono (lo' := C_TD + 32 * (2 ^ 19 - 128 * (n + 1))) (hi' := C_TD + 32 * 2 ^ 19) (le_refl _) (by omega))).trans
          (CommitMemOutside.of_mem_eq hmem_b _ _)
  obtain ⟨sp, hrun_p, hpcp, hregp, hx10p, hx12p, hheapp, hpresp⟩ := hbulk_ind 4094 (le_refl _)
  obtain ⟨se, hbody, hpce, hrege, hx10e, hx12e, hheape, hprese⟩ :=
    c_l623_bulk_chunk_body h512 oracle msg salts sp 4094 (by omega) hpcp
      ((hregp .x5 (by decide) (by decide) (by decide)).trans hx5) hx10p
      ((hregp .x11 (by decide) (by decide) (by decide)).trans hx11) hx12p
      ((hregp .x13 (by decide) (by decide) (by decide)).trans hx13)
      ((hregp .x27 (by decide) (by decide) (by decide)).trans hx27) hheapp
  obtain ⟨hlatch, hpc_b, hmem_b, hreg_b⟩ :=
    c_l623_bulk_bne_exit oracle se hpce hx12e
      ((hrege .x19 (by decide) (by decide) (by decide)).trans
        ((hregp .x19 (by decide) (by decide) (by decide)).trans hx19))
  let sBulk := execInstrBr se (.BNE .x12 .x19 (5120#13))
  have hrun_bulk : DetRun oracle (submission.image .commit) s0 3149055 sBulk 6818175 524160 := by
    simpa only [show 769 * 4094 + 768 + 1 = 3149055 by decide,
      show 1665 * 4094 + 1664 + 1 = 6818175 by decide,
      show 128 * 4094 + 128 + 0 = 524160 by decide] using (hrun_p.trans hbody).trans hlatch
  have hbulk_reg : ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → sBulk.getReg reg = s0.getReg reg :=
    fun reg h6 h10 h12 => (hreg_b reg).trans ((hrege reg h6 h10 h12).trans (hregp reg h6 h10 h12))
  have hsub128 : 2 ^ 19 - 128 * 4095 = 128 := by decide
  have hbulk_x10 : sBulk.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * 128) := by
    simpa only [hsub128] using (hreg_b .x10).trans hx10e
  have hbulk_x12 : sBulk.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 128) := by
    simpa only [hsub128] using (hreg_b .x12).trans hx12e
  have hbulk_heap : ∀ h', 128 ≤ h' → h' < 2 ^ 25 →
      readBuffer sBulk (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h' := fun h' h1 h2 => by
    rw [c_readBuffer_of_mem_eq hmem_b]; exact hheape h' (by omega) h2
  have hbulk_pres : CommitMemOutside s0 sBulk (C_TD + 32 * 128) (C_TD + 32 * 2 ^ 19) :=
    ((hpresp.mono (lo' := C_TD + 32 * 128) (hi' := C_TD + 32 * 2 ^ 19) (by omega) (le_refl _)).trans
      (hprese.mono (lo' := C_TD + 32 * 128) (hi' := C_TD + 32 * 2 ^ 19) (by omega) (by omega))).trans
      (CommitMemOutside.of_mem_eq hmem_b _ _)
  -- 4B. Word `43865`: `ADDI x19, x9, 64` (1 step, 1 cycle)
  let sT0 := execInstrBr sBulk (.ADDI .x19 .x9 (64#12))
  have hrun_tsetup : DetRun oracle (submission.image .commit) sBulk 1 sT0 1 0 :=
    DetRun.step1 (commit_fetch_commitTailInstr sBulk 43865 (by omega) (by omega) hpc_b) rfl
  have hsT0_pc : sT0.pc = BitVec.ofNat 64 (0x1000 + 4 * 43866) := c_pc_step_idx sBulk 43865 hpc_b
  have hsT0_mem : sT0.mem = sBulk.mem := c_mem_exec_ADDI sBulk _ _ _
  have hsT0_x19 : sT0.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2) := by
    simp only [sT0, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x19 ≠ .x0),
      (hbulk_reg .x9 (by decide) (by decide) (by decide)).trans hx9,
      c_add_signExtend12_ofNat_small _ 64 (by omega)]
  have hsT0_reg : ∀ reg : Reg, reg ≠ .x19 → sT0.getReg reg = sBulk.getReg reg := fun reg h19 => by
    simp only [sT0, execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne .x19 reg (Ne.symm h19)]
  -- 4C. `l623_tail` (`43866..43872`): 125 back iters + 1 final iter (`126 * 7 = 882` steps, `1764` cycles, `126` calls)
  have htail_fetch : ∀ j < 6, ∀ st : MachineState,
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * (43866 + j)) →
      fetch (submission.image .commit) st = some (l623Instr j) := by
    intro j hj st hpcst
    interval_cases j <;> exact commit_fetch_commitTailInstr st _ (by omega) (by omega) hpcst
  have htail_ind : ∀ n ≤ 125,
      ∃ sn,
        DetRun oracle (submission.image .commit) sT0 (7 * n) sn (14 * n) n ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 43866) ∧
        (∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → sn.getReg reg = sT0.getReg reg) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * (128 - n)) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (128 - n)) ∧
        (∀ h', 128 - n ≤ h' → h' < 2 ^ 25 →
          readBuffer sn (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h') ∧
        CommitMemOutside sT0 sn (C_TD + 32 * (128 - n)) (C_TD + 32 * 128) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨sT0, DetRun.refl _ _ _, hsT0_pc, fun _ _ _ _ => rfl,
        (hsT0_reg .x10 (by decide)).trans hbulk_x10,
        (hsT0_reg .x12 (by decide)).trans hbulk_x12,
        fun h' h1 h2 => by rw [c_readBuffer_of_mem_eq hsT0_mem]; exact hbulk_heap h' (by omega) h2,
        CommitMemOutside.refl _ _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrun_n, hpcn, hregn, hx10n, hx12n, hheapn, hpresn⟩ := ih (by omega)
      set h := 128 - (n + 1)
      have hh_succ : h + 1 = 128 - n := by omega
      obtain ⟨se, hstep, hpce, hrege, hx10e, hx12e, hvale, hprese⟩ :=
        c_l623_node_step h512 oracle msg salts sn 43866 h (by omega) (by omega) hpcn
          ((hregn .x5 (by decide) (by decide) (by decide)).trans ((hsT0_reg .x5 (by decide)).trans
            ((hbulk_reg .x5 (by decide) (by decide) (by decide)).trans hx5)))
          (by simpa only [hh_succ] using hx10n)
          ((hregn .x11 (by decide) (by decide) (by decide)).trans ((hsT0_reg .x11 (by decide)).trans
            ((hbulk_reg .x11 (by decide) (by decide) (by decide)).trans hx11)))
          (by simpa only [hh_succ] using hx12n)
          ((hregn .x13 (by decide) (by decide) (by decide)).trans ((hsT0_reg .x13 (by decide)).trans
            ((hbulk_reg .x13 (by decide) (by decide) (by decide)).trans hx13)))
          ((hregn .x27 (by decide) (by decide) (by decide)).trans ((hsT0_reg .x27 (by decide)).trans
            ((hbulk_reg .x27 (by decide) (by decide) (by decide)).trans hx27)))
          htail_fetch
          (hheapn (2 * h) (by omega) (by omega))
          (hheapn (2 * h + 1) (by omega) (by omega))
      obtain ⟨hlatch, hpc_l, hmem_l, hreg_l⟩ :=
        c_l623_tail_bne_back oracle h (by omega) (by omega) se hpce hx12e
          ((hrege .x19 (by decide) (by decide) (by decide)).trans
            ((hregn .x19 (by decide) (by decide) (by decide)).trans hsT0_x19))
      refine ⟨_, by simpa [Nat.mul_succ, Nat.add_assoc] using (hrun_n.trans hstep).trans hlatch,
        hpc_l, fun reg h6 h10 h12 => (hreg_l reg).trans ((hrege reg h6 h10 h12).trans (hregn reg h6 h10 h12)),
        (hreg_l .x10).trans hx10e, (hreg_l .x12).trans hx12e, ?_, ?_⟩
      · intro h' h1 h2
        rw [c_readBuffer_of_mem_eq hmem_l]
        by_cases heq : h' = h
        · subst heq; exact hvale
        · exact (hprese.readBuffer_eq (by omega) (by omega)).trans (hheapn h' (by omega) h2)
      · exact ((hpresn.mono (lo' := C_TD + 32 * h) (hi' := C_TD + 32 * 128) (by omega) (le_refl _)).trans
            (hprese.mono (lo' := C_TD + 32 * h) (hi' := C_TD + 32 * 128) (le_refl _) (by omega))).trans
          (CommitMemOutside.of_mem_eq hmem_l _ _)
  obtain ⟨st125, hrun_t125, hpct, hregt, hx10t, hx12t, hheapt, hprest⟩ := htail_ind 125 (le_refl _)
  obtain ⟨stLast, hstepLast, hpcLast, hregLast, hx10Last, hx12Last, hvalLast, hpresLast⟩ :=
    c_l623_node_step h512 oracle msg salts st125 43866 2 (by omega) (by omega) hpct
      ((hregt .x5 (by decide) (by decide) (by decide)).trans ((hsT0_reg .x5 (by decide)).trans
        ((hbulk_reg .x5 (by decide) (by decide) (by decide)).trans hx5)))
      (by simpa only [show 128 - 125 = 2 + 1 by decide] using hx10t)
      ((hregt .x11 (by decide) (by decide) (by decide)).trans ((hsT0_reg .x11 (by decide)).trans
        ((hbulk_reg .x11 (by decide) (by decide) (by decide)).trans hx11)))
      (by simpa only [show 128 - 125 = 2 + 1 by decide] using hx12t)
      ((hregt .x13 (by decide) (by decide) (by decide)).trans ((hsT0_reg .x13 (by decide)).trans
        ((hbulk_reg .x13 (by decide) (by decide) (by decide)).trans hx13)))
      ((hregt .x27 (by decide) (by decide) (by decide)).trans ((hsT0_reg .x27 (by decide)).trans
        ((hbulk_reg .x27 (by decide) (by decide) (by decide)).trans hx27)))
      htail_fetch
      (hheapt 4 (by omega) (by omega))
      (hheapt 5 (by omega) (by omega))
  obtain ⟨hlatchT, hpcT_end, hmemT_end, hregT_end⟩ :=
    c_l623_tail_bne_exit oracle stLast hpcLast hx12Last
      ((hregLast .x19 (by decide) (by decide) (by decide)).trans
        ((hregt .x19 (by decide) (by decide) (by decide)).trans hsT0_x19))
  let sTail := execInstrBr stLast (.BNE .x12 .x19 (8168#13))
  have hrun_tail : DetRun oracle (submission.image .commit) sT0 882 sTail 1764 126 := by
    simpa only [show 7 * 125 + 6 + 1 = 882 by decide,
      show 14 * 125 + 13 + 1 = 1764 by decide,
      show 125 + 1 + 0 = 126 by decide] using (hrun_t125.trans hstepLast).trans hlatchT
  have hsTail_reg : ∀ reg : Reg, reg ≠ .x6 → reg ≠ .x10 → reg ≠ .x12 → reg ≠ .x19 →
      sTail.getReg reg = s0.getReg reg := fun reg h6 h10 h12 h19 =>
    (hregT_end reg).trans ((hregLast reg h6 h10 h12).trans ((hregt reg h6 h10 h12).trans
      ((hsT0_reg reg h19).trans (hbulk_reg reg h6 h10 h12))))
  have hsTail_x10 : sTail.getReg .x10 = BitVec.ofNat 64 (C_TD + 64 * 2) := (hregT_end .x10).trans hx10Last
  have hsTail_x12 : sTail.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2) := (hregT_end .x12).trans hx12Last
  have hsTail_heap : ∀ h', 2 ≤ h' → h' < 2 ^ 25 →
      readBuffer sTail (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h' := fun h' h1 h2 => by
    rw [c_readBuffer_of_mem_eq hmemT_end]
    by_cases heq : h' = 2
    · subst heq; exact hvalLast
    · exact (hpresLast.readBuffer_eq (by omega) (by omega)).trans (hheapt h' (by omega) h2)
  have hsTail_pres : CommitMemOutside s0 sTail (C_TD + 32 * 2) (C_TD + 32 * 2 ^ 19) := by
    have hpT : CommitMemOutside sT0 sTail (C_TD + 32 * 2) (C_TD + 32 * 128) :=
      ((hprest.mono (lo' := C_TD + 32 * 2) (hi' := C_TD + 32 * 128) (by omega) (le_refl _)).trans
        (hpresLast.mono (lo' := C_TD + 32 * 2) (hi' := C_TD + 32 * 128) (le_refl _) (by omega))).trans
        (CommitMemOutside.of_mem_eq hmemT_end _ _)
    exact ((hbulk_pres.mono (lo' := C_TD + 32 * 2) (hi' := C_TD + 32 * 2 ^ 19) (by omega) (le_refl _)).trans
      (CommitMemOutside.of_mem_eq hsT0_mem _ _)).trans
      (hpT.mono (lo' := C_TD + 32 * 2) (hi' := C_TD + 32 * 2 ^ 19) (le_refl _) (by omega))
  -- 4D. Root `L24` (`43873..43875`): 3 steps, 10 cycles, 1 call
  let r1 := execInstrBr sTail (.ADDI .x10 .x10 (4032#12))
  let r2 := execInstrBr r1 (.ADDI .x12 .x12 (4064#12))
  let r3 := writeBits r2 (BitVec.ofNat 64 (C_TD + 32)) (rootVal c64 p200 msg salts)
  have hr1_pc : r1.pc = BitVec.ofNat 64 (0x1000 + 4 * 43874) := c_pc_step_idx sTail 43873 hpcT_end
  have hr2_pc : r2.pc = BitVec.ofNat 64 (0x1000 + 4 * 43875) := c_pc_step_idx r1 43874 hr1_pc
  have hr1_x10 : r1.getReg .x10 = BitVec.ofNat 64 (C_TD + 64) := by
    simp only [r1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hsTail_x10,
      c_bv64_add_neg64 (C_TD + 64 * 2) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hr2_x10 : r2.getReg .x10 = BitVec.ofNat 64 (C_TD + 64) := by
    simp only [r2, execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne .x12 .x10 (by decide), hr1_x10]
  have hr2_x12 : r2.getReg .x12 = BitVec.ofNat 64 (C_TD + 32) := by
    simp only [r2, r1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      c_getReg_setReg_ne .x10 .x12 (by decide), hsTail_x12,
      c_bv64_add_neg32 (C_TD + 32 * 2) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hr2_mem : r2.mem = sTail.mem := (c_mem_exec_ADDI r1 _ _ _).trans (c_mem_exec_ADDI sTail _ _ _)
  have hr2_reg : ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → r2.getReg reg = sTail.getReg reg := fun reg h10 h12 => by
    simp only [r2, r1, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x12 reg (Ne.symm h12), c_getReg_setReg_ne .x10 reg (Ne.symm h10)]
  have hrun_r0 : DetRun oracle (submission.image .commit) sTail 1 r1 1 0 :=
    DetRun.step1 (commit_fetch_commitTailInstr sTail 43873 (by omega) (by omega) hpcT_end) rfl
  have hrun_r1 : DetRun oracle (submission.image .commit) r1 1 r2 1 0 :=
    DetRun.step1 (commit_fetch_commitTailInstr r1 43874 (by omega) (by omega) hr1_pc) rfl
  have hread_root : oracle.compression ((readBuffer r2 (C_TD + 64) 64).cast h512.symm) =
      rootVal c64 p200 msg salts := by
    rw [c_readBuffer_of_mem_eq hr2_mem, readBuffer_binary]
    have hL := hsTail_heap 2 (by omega) (by omega)
    have hR := hsTail_heap 3 (by omega) (by omega)
    rw [show C_TD + 64 = C_TD + 32 * 2 by omega, show C_TD + 32 * 2 + 32 = C_TD + 32 * 3 by omega, hL, hR]
    exact ((c_heapVal_root c64 p200 msg salts).symm).trans (c_heapVal_one_eq_rootVal c64 p200 msg salts)
  have hrun_r2 : DetRun oracle (submission.image .commit) r2 1 r3 8 1 :=
    DetRun.compress_eq h512 (commit_fetch_commitTailInstr r2 43875 (by omega) (by omega) hr2_pc)
      ((hr2_reg .x5 (by decide) (by decide)).trans
        ((hsTail_reg .x5 (by decide) (by decide) (by decide) (by decide)).trans hx5))
      ((hr2_reg .x11 (by decide) (by decide)).trans
        ((hsTail_reg .x11 (by decide) (by decide) (by decide) (by decide)).trans hx11))
      ((hr2_reg .x13 (by decide) (by decide)).trans
        ((hsTail_reg .x13 (by decide) (by decide) (by decide) (by decide)).trans hx13))
      (C_TD + 64) (C_TD + 32) hr2_x10 hr2_x12
      (by omega) (by omega) (by omega) (by omega) (rootVal c64 p200 msg salts) hread_root
  have hr3_pc : r3.pc = BitVec.ofNat 64 (0x1000 + 4 * 43876) := by
    rw [c_pc_writeBits, c_pc_step_idx r2 43875 hr2_pc]
  have hr3_x12 : r3.getReg .x12 = BitVec.ofNat 64 (C_TD + 32) :=
    (writeBits_register r2 _ _ .x12).trans hr2_x12
  have hr3_x26 : r3.getReg .x26 = BitVec.ofNat 64 C_CMT :=
    (writeBits_register r2 _ _ .x26).trans ((hr2_reg .x26 (by decide) (by decide)).trans
      ((hsTail_reg .x26 (by decide) (by decide) (by decide) (by decide)).trans hx26))
  have hr3_pres : CommitMemOutside sTail r3 (C_TD + 32) (C_TD + 64) :=
    (CommitMemOutside.of_mem_eq hr2_mem _ _).trans
      (by simpa only [show C_TD + 32 + (256 + 7) / 8 = C_TD + 64 by omega] using
        c_memPreserved_writeBits r2 (C_TD + 32) (rootVal c64 p200 msg salts) (by omega))
  have hr3_heap : ∀ h', 1 ≤ h' → h' < 2 ^ 25 →
      readBuffer r3 (C_TD + 32 * h') 32 = c_heapVal c64 p200 msg salts h' := by
    intro h' h1 h2
    by_cases heq : h' = 1
    · subst heq
      rw [show C_TD + 32 * 1 = C_TD + 32 by omega, writeBits_readBuffer_digest]
      exact (c_heapVal_one_eq_rootVal c64 p200 msg salts).symm
    · exact (hr3_pres.readBuffer_eq (by omega) (by omega)).trans (hsTail_heap h' (by omega) h2)
  -- 4E. Copy root 32B from `x12` (`C_TD + 32`) to `x26` (`C_CMT`) (`43876..43883`: 8 steps, 8 cycles)
  obtain ⟨sCopy, hrun_copy, hpc_copy, _, hcopy_read, hcopy_pres⟩ :=
    c_commit_copy32 oracle r3 43876 .x12 .x26 (C_TD + 32) C_CMT 0 0
      (by decide) (by decide) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hr3_pc hr3_x12 hr3_x26 (by
        intro k hk st
        constructor <;> (intro hpcst; interval_cases k <;>
          exact commit_fetch_commitTailInstr st _ (by omega) (by omega) hpcst))
  -- 4F. Halt prep (`43884..43885`: `ADDI x5, x0, 1; ADDI x10, x0, 0`, 2 steps, 2 cycles)
  let sH1 := execInstrBr sCopy (.ADDI .x5 .x0 (1#12))
  let sHalt := execInstrBr sH1 (.ADDI .x10 .x0 (0#12))
  have hrun_h1 : DetRun oracle (submission.image .commit) sCopy 1 sH1 1 0 :=
    DetRun.step1 (commit_fetch_commitTailInstr sCopy 43884 (by omega) (by omega) hpc_copy) rfl
  have hsH1_pc : sH1.pc = BitVec.ofNat 64 (0x1000 + 4 * 43885) := c_pc_step_idx sCopy 43884 hpc_copy
  have hrun_h2 : DetRun oracle (submission.image .commit) sH1 1 sHalt 1 0 :=
    DetRun.step1 (commit_fetch_commitTailInstr sH1 43885 (by omega) (by omega) hsH1_pc) rfl
  have hsHalt_mem : sHalt.mem = sCopy.mem := (c_mem_exec_ADDI sH1 _ _ _).trans (c_mem_exec_ADDI sCopy _ _ _)
  have hsHalt_pc : sHalt.pc = BitVec.ofNat 64 (0x1000 + 4 * 43886) := c_pc_step_idx sH1 43885 hsH1_pc
  have hsHalt_x5 : sHalt.getReg .x5 = 1#64 := by
    simp only [sHalt, sH1, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x10 .x5 (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x5 ≠ .x0), c_getReg_x0]
    decide
  have hsHalt_x10 : sHalt.getReg .x10 = 0#64 := by
    simp only [sHalt, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), c_getReg_x0]
    decide
  refine ⟨sHalt,
    by simpa only [show 3149055 + 1 + 882 + 1 + 1 + 1 + 8 + 1 + 1 = 3149951 by decide,
      show 6818175 + 1 + 1764 + 1 + 1 + 8 + 8 + 1 + 1 = 6819960 by decide,
      show 524160 + 0 + 126 + 0 + 0 + 1 + 0 + 0 + 0 = 524287 by decide] using
      (((((((hrun_bulk.trans hrun_tsetup).trans hrun_tail).trans hrun_r0).trans hrun_r1).trans
        hrun_r2).trans hrun_copy).trans hrun_h1).trans hrun_h2,
    hsHalt_pc, hsHalt_x5, hsHalt_x10, ?_, ?_, ?_⟩
  · rw [c_readBuffer_of_mem_eq hsHalt_mem]
    have hcm := hcopy_read
    simp only [Nat.add_zero] at hcm
    rw [hcm, writeBits_readBuffer_digest]
  · intro h' h1 h2
    rw [c_readBuffer_of_mem_eq hsHalt_mem]
    have hp := hcopy_pres.readBuffer_eq (addr := C_TD + 32 * h') (n := 32) (by omega) (by omega)
    exact hp.trans (hr3_heap h' h1 h2)
  · have hp1 := (hsTail_pres.mono (lo' := C_CMT) (hi' := C_TD + 32 * 2 ^ 19) (by omega) (le_refl _)).trans
      (hr3_pres.mono (lo' := C_CMT) (hi' := C_TD + 32 * 2 ^ 19) (by omega) (by omega))
    have hp2 := hp1.trans (hcopy_pres.mono (lo' := C_CMT) (hi' := C_TD + 32 * 2 ^ 19) (by omega) (by omega))
    exact hp2.trans (CommitMemOutside.of_mem_eq hsHalt_mem _ _)

end CommitGolfCandidate
