import CommitGolfCandidate.MoonCommitBase

/-! Exact RV64IM execution proofs for Phases 1A (`C0`, words `4122..10276`) and 1B (`P1`,
words `10277..16432`) of the 64-32 `commit` image:
- Phase 1A: `16,777,216` in-place `C0` compressions `v[192..256) -> c0_i`, writing `c0_i` at
  `msg[i][192..224)` so `msg[i][24..224)` equals `leafP1Input c0_i (msg i)`.
- Phase 1B: `16,777,216` in-place `P1` permutations `msg[i][24..224) -> y_i`, writing `y_i` at
  `msg[i][24..224)` so `msg[i][0..64)` equals `leafC2Input y_i (msg i)`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Phase 1A (`C0`: words `4122..10276`) -/

private theorem c_pc_beq_10266 :
    BitVec.ofNat 64 (0x1000 + 4 * 10266) + signExtend13 (8#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 10268) := by decide

private theorem c_pc_jal_10267 :
    BitVec.ofNat 64 (0x1000 + 4 * 10267) + signExtend21 (2072572#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 4122) := by decide

private def c_mid1AInstrs : List Instr :=
  [.ADDI .x11 .x0 (200#12), .ADDI .x13 .x0 (1#12), .ADDI .x10 .x8 (3864#12),
   .ADDI .x6 .x0 (1023#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (2047#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (1816#12), .ADD .x19 .x8 .x6]

private theorem c_mid1A_run (oracle : Oracle) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 10268)) :
    DetRun oracle (submission.image .commit) s 9 (c_mid1AInstrs.foldl execInstrBr s) 9 0 := by
  have hall : ∀ ins ∈ c_mid1AInstrs, c_isPureAlu ins = true := by decide
  apply c_exec_alu_list c_mid1AInstrs s
  intro i hi
  have hi' : i < 9 := hi
  have hpc_i : ((c_mid1AInstrs.take i).foldl execInstrBr s).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (10268 + i)) := by
    have h := c_foldl_pureAlu_pc (c_mid1AInstrs.take i) s (0x1000 + 4 * 10268)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitMid1AInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem c_mid1A_spec (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 10268))
    (hx5 : s.getReg .x5 = 0#64)
    (hx8 : s.getReg .x8 = BitVec.ofNat 64 C_MSG)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx18 : s.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s' := c_mid1AInstrs.foldl execInstrBr s
    s'.pc = BitVec.ofNat 64 (0x1000 + 4 * 10277) ∧
    s'.mem = s.mem ∧
    s'.getReg .x5 = 0#64 ∧
    s'.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
    s'.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s'.getReg .x10 = BitVec.ofNat 64 (C_MSG - 232) ∧
    s'.getReg .x11 = 200#64 ∧
    s'.getReg .x13 = 1#64 ∧
    s'.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
    s'.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 232) ∧
    s'.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ c_mid1AInstrs, c_isPureAlu ins = true := by decide
  refine ⟨?_, c_foldl_pureAlu_mem c_mid1AInstrs s hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (c_foldl_pureAlu_pc c_mid1AInstrs s (0x1000 + 4 * 10268) hall hpc).trans (by decide)
  all_goals (
    simp only [c_mid1AInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx5, hx8, hx9, hx18, hx26]
    try decide)

/-- One `c0` leaf step (`ADDI x10, x10, 256; ADDI x12, x10, 0; ECALL`): 3 steps, 10 cycles, 1 call. -/
private theorem c_p1a_leaf_step (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (s : MachineState)
    (k leafIdx : Nat) (hk : k < 2048) (hleaf : leafIdx < LENGTH)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (4122 + 3 * k)))
    (hx5 : s.getReg .x5 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * leafIdx - 64))
    (hx11 : s.getReg .x11 = 64#64)
    (hx13 : s.getReg .x13 = 0#64)
    (hsrc : readBuffer s (C_MSG + 256 * leafIdx + 192) 64 = leafC0Input (msg ⟨leafIdx, hleaf⟩)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    ∃ s',
      DetRun oracle (submission.image .commit) s 3 s' 10 1 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (4122 + 3 * (k + 1))) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s'.getReg reg = s.getReg reg) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (leafIdx + 1) - 64) ∧
      readBuffer s' (C_MSG + 256 * leafIdx + 192) 32 = c64 (leafC0Input (msg ⟨leafIdx, hleaf⟩)) ∧
      CommitMemOutside s s' (C_MSG + 256 * leafIdx + 192) (C_MSG + 256 * leafIdx + 224) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hCM : C_MSG = 4096 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let out := c64 (leafC0Input (msg ⟨leafIdx, hleaf⟩))
  let s1 := execInstrBr s (.ADDI .x10 .x10 (256#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x10 (0#12))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_MSG + 256 * leafIdx + 192)) out
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (4122 + 3 * k + 1)) :=
    c_pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (4122 + 3 * k + 2)) :=
    c_pc_step_idx s1 _ hs1_pc
  have hs1_x10 : s1.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * leafIdx + 192) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      c_add_signExtend12_ofNat_small _ 256 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_x10 : s2.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * leafIdx + 192) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x12 .x10 (by decide), hs1_x10]
  have hs2_x12 : s2.getReg .x12 = BitVec.ofNat 64 (C_MSG + 256 * leafIdx + 192) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs1_x10,
      c_add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
  have hs2_mem : s2.mem = s.mem := (c_mem_exec_ADDI s1 _ _ _).trans (c_mem_exec_ADDI s _ _ _)
  have hs2_reg : ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s2.getReg reg = s.getReg reg := fun reg h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x12 reg (Ne.symm h12), c_getReg_setReg_ne .x10 reg (Ne.symm h10)]
  have hr0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_c0 s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc)) rfl
  have hr1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_c0 s1 k 1 hk (by omega) hs1_pc) rfl
  have hread : oracle.compression ((readBuffer s2 (C_MSG + 256 * leafIdx + 192) 64).cast h512.symm) = out := by
    rw [c_readBuffer_of_mem_eq hs2_mem, hsrc]
  have hr2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h512 (commit_fetch_c0 s2 k 2 hk (by omega) hs2_pc)
      ((hs2_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg .x13 (by decide) (by decide)).trans hx13)
      (C_MSG + 256 * leafIdx + 192) (C_MSG + 256 * leafIdx + 192)
      hs2_x10 hs2_x12 (by omega) (by omega) (by omega) (by omega) out hread
  refine ⟨s3, (hr0.trans hr1).trans hr2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c_pc_writeBits, c_pc_step_idx s2 _ hs2_pc]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · intro reg h10 h12
    exact (writeBits_register s2 _ out reg).trans (hs2_reg reg h10 h12)
  · rw [writeBits_register s2 _ out .x10, hs2_x10]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · exact writeBits_readBuffer_digest s2 _ out
  · exact (CommitMemOutside.of_mem_eq hs2_mem _ _).trans
      (by simpa only [show C_MSG + 256 * leafIdx + 192 + (256 + 7) / 8 = C_MSG + 256 * leafIdx + 224 by omega] using
        c_memPreserved_writeBits s2 (C_MSG + 256 * leafIdx + 192) out (by omega))

/-- One 2048-leaf `c0` chunk body (`4122..10265`): 6144 steps, 20480 cycles, 2048 calls. -/
private theorem c_p1a_chunk_body (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (sc : MachineState)
    (chunkIdx : Nat) (hchunk : chunkIdx < 8192)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 4122))
    (hx5 : sc.getReg .x5 = 0#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * chunkIdx) - 64))
    (hx11 : sc.getReg .x11 = 64#64)
    (hx13 : sc.getReg .x13 = 0#64)
    (hmsg : ∀ j (hj : j < 2048),
      readBuffer sc (C_MSG + 256 * (2048 * chunkIdx + j) + 192) 64 =
        leafC0Input (msg ⟨2048 * chunkIdx + j, by unfold LENGTH LOG_LENGTH; omega⟩)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    ∃ se,
      DetRun oracle (submission.image .commit) sc 6144 se 20480 2048 ∧
      se.pc = BitVec.ofNat 64 (0x1000 + 4 * 10266) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → se.getReg reg = sc.getReg reg) ∧
      se.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * (chunkIdx + 1)) - 64) ∧
      (∀ j (hj : j < 2048),
        readBuffer se (C_MSG + 256 * (2048 * chunkIdx + j) + 192) 32 =
          c64 (leafC0Input (msg ⟨2048 * chunkIdx + j, by unfold LENGTH LOG_LENGTH; omega⟩))) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (∀ j < 2048, q < C_MSG + 256 * (2048 * chunkIdx + j) + 192 ∨
          C_MSG + 256 * (2048 * chunkIdx + j) + 224 ≤ q) →
        se.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hCM : C_MSG = 4096 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  have hind : ∀ k (hk : k ≤ 2048),
      ∃ sk,
        DetRun oracle (submission.image .commit) sc (3 * k) sk (10 * k) k ∧
        sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (4122 + 3 * k)) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sk.getReg reg = sc.getReg reg) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * chunkIdx + k) - 64) ∧
        (∀ j (hj : j < k),
          readBuffer sk (C_MSG + 256 * (2048 * chunkIdx + j) + 192) 32 =
            c64 (leafC0Input (msg ⟨2048 * chunkIdx + j, by omega⟩))) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ j < k, q < C_MSG + 256 * (2048 * chunkIdx + j) + 192 ∨
            C_MSG + 256 * (2048 * chunkIdx + j) + 224 ≤ q) →
          sk.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩
    | succ k ih =>
      obtain ⟨sk, hrun_k, hpck, hregk, hx10k, hresk, hpresk⟩ := ih (by omega)
      have hsrc : readBuffer sk (C_MSG + 256 * (2048 * chunkIdx + k) + 192) 64 =
          leafC0Input (msg ⟨2048 * chunkIdx + k, by omega⟩) := by
        have hEq := readBuffer_congr sk sc (C_MSG + 256 * (2048 * chunkIdx + k) + 192) 64
          (fun b hb => hpresk _ (by omega) (fun j hj => by omega))
        exact hEq.trans (hmsg k (by omega))
      obtain ⟨s', hstep, hpc', hreg', hx10', hres', hpres'⟩ :=
        c_p1a_leaf_step h512 oracle msg sk k (2048 * chunkIdx + k) (by omega) (by omega)
          hpck ((hregk .x5 (by decide) (by decide)).trans hx5) hx10k
          ((hregk .x11 (by decide) (by decide)).trans hx11)
          ((hregk .x13 (by decide) (by decide)).trans hx13) hsrc
      refine ⟨s', by simpa [Nat.mul_succ, Nat.add_assoc] using hrun_k.trans hstep, hpc',
        fun reg h10 h12 => (hreg' reg h10 h12).trans (hregk reg h10 h12),
        by simpa only [Nat.add_assoc] using hx10', ?_, ?_⟩
      · intro j hj
        by_cases hjk : j < k
        · exact (hpres'.readBuffer_eq (by omega) (by omega)).trans (hresk j hjk)
        · have heqj : j = k := by omega
          subst heqj; exact hres'
      · intro q hq hout
        exact (hpres' q hq (hout k (by omega))).trans (hpresk q hq (fun j hj => hout j (by omega)))
  simpa only [show 2048 * (chunkIdx + 1) = 2048 * chunkIdx + 2048 by omega] using hind 2048 (le_refl _)

private theorem c_p1a_latch_back (oracle : Oracle) (chunkIdx : Nat) (hchunk : chunkIdx < 8191)
    (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 10266))
    (hx10 : se.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * (chunkIdx + 1)) - 64))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 64)) :
    let sb := execInstrBr (execInstrBr se (.BEQ .x10 .x19 (8#13))) (.JAL .x0 (2072572#21))
    DetRun oracle (submission.image .commit) se 2 sb 2 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 4122) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  have hCM : C_MSG = 4096 := rfl
  let s1 := execInstrBr se (.BEQ .x10 .x19 (8#13))
  let s2 := execInstrBr s1 (.JAL .x0 (2072572#21))
  have hst1 : DetRun oracle (submission.image .commit) se 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1AInstr se 10266 (by omega) (by omega) hpc) rfl
  have hne : (se.getReg .x10 == se.getReg .x19) = false := by
    rw [hx10, hx19, beq_eq_false_iff_ne]
    exact c_bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 10267) := by
    simp only [s1, execInstrBr, hne, Bool.false_eq_true, ite_false, c_pc_setPC]
    exact c_pc_step_idx se 10266 hpc
  have hst2 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1AInstr s1 10267 (by omega) (by omega) hs1_pc) rfl
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 4122) := by
    simp only [s2, execInstrBr, c_pc_setPC, hs1_pc]
    exact c_pc_jal_10267
  exact ⟨hst1.trans hst2, hs2_pc,
    (c_mem_exec_JAL s1 _ _).trans (c_mem_exec_BEQ se _ _ _),
    fun reg => (c_reg_exec_JAL0 s1 _ reg).trans (c_reg_exec_BEQ se _ _ _ reg)⟩

private theorem c_p1a_latch_exit (oracle : Oracle) (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 10266))
    (hx10 : se.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * 8192) - 64))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 64)) :
    let sb := execInstrBr se (.BEQ .x10 .x19 (8#13))
    DetRun oracle (submission.image .commit) se 1 sb 1 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 10268) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  let sb := execInstrBr se (.BEQ .x10 .x19 (8#13))
  have hst : DetRun oracle (submission.image .commit) se 1 sb 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1AInstr se 10266 (by omega) (by omega) hpc) rfl
  have heq : (se.getReg .x10 == se.getReg .x19) = true := by
    rw [hx10, hx19]; exact beq_self_eq_true _
  have hpc' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 10268) := by
    simp only [sb, execInstrBr, heq, ite_true, c_pc_setPC, hpc]
    exact c_pc_beq_10266
  exact ⟨hst, hpc', c_mem_exec_BEQ se _ _ _, c_reg_exec_BEQ se _ _ _⟩

/-- Full Phase 1A (`C0`, words `4122..10276`): `50,348,040` steps, `167,788,552` cycles,
`16,777,216` compression calls. Leaves `msg[i][0..192)` intact and `msg[i][24..224)` = `leafP1Input`. -/
theorem commit_phase1A (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 4122))
    (hx5 : s0.getReg .x5 = 0#64)
    (hx8 : s0.getReg .x8 = BitVec.ofNat 64 C_MSG)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 (C_MSG - 64))
    (hx11 : s0.getReg .x11 = 64#64)
    (hx13 : s0.getReg .x13 = 0#64)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx19 : s0.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 64))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hmsg : ∀ (i : Index) (j : Nat), j < 256 →
      s0.getByte (BitVec.ofNat 64 (C_MSG + 256 * i.val + j)) = (msg i).extractLsb' (8 * j) 8) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 50348040 s1 167788552 16777216 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 10277) ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x10 = BitVec.ofNat 64 (C_MSG - 232) ∧
      s1.getReg .x11 = 200#64 ∧
      s1.getReg .x13 = 1#64 ∧
      s1.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
      s1.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 232) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ (i : Index) (j : Nat), j < 24 →
        s1.getByte (BitVec.ofNat 64 (C_MSG + 256 * i.val + j)) = (msg i).extractLsb' (8 * j) 8) ∧
      (∀ i : Index,
        readBuffer s1 (C_MSG + 256 * i.val + 24) 200 =
          leafP1Input (c64 (leafC0Input (msg i))) (msg i)) ∧
      CommitMemOutside s0 s1 C_MSG (C_MSG + 2 ^ 32) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hCM : C_MSG = 4096 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  have hmsg_c0 : ∀ i : Index, readBuffer s0 (C_MSG + 256 * i.val + 192) 64 = leafC0Input (msg i) := by
    intro i
    have h := read_serialized_slice s0 (msg i) (C_MSG + 256 * i.val + 192) 192 64 (fun j hj => by
      rw [show C_MSG + 256 * i.val + 192 + j = C_MSG + 256 * i.val + (192 + j) by omega]
      exact hmsg i (192 + j) (by omega))
    exact h
  have hind : ∀ n (hn : n ≤ 8191),
      ∃ sn,
        DetRun oracle (submission.image .commit) s0 (6146 * n) sn (20482 * n) (2048 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 4122) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sn.getReg reg = s0.getReg reg) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * n) - 64) ∧
        (∀ idx (hidx : idx < 2048 * n),
          readBuffer sn (C_MSG + 256 * idx + 192) 32 =
            c64 (leafC0Input (msg ⟨idx, by omega⟩))) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ idx < 2048 * n, q < C_MSG + 256 * idx + 192 ∨ C_MSG + 256 * idx + 224 ≤ q) →
          sn.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨s0, DetRun.refl _ _ _, hpc, fun _ _ _ => rfl, by simpa using hx10,
        fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩
    | succ n ih =>
      obtain ⟨sn, hrun_n, hpcn, hregn, hx10n, hresn, hpresn⟩ := ih (by omega)
      have hsrc : ∀ j (hj : j < 2048),
          readBuffer sn (C_MSG + 256 * (2048 * n + j) + 192) 64 =
            leafC0Input (msg ⟨2048 * n + j, by omega⟩) := by
        intro j hj
        have hEq := readBuffer_congr sn s0 (C_MSG + 256 * (2048 * n + j) + 192) 64
          (fun b hb => hpresn _ (by omega) (fun idx hidx => by omega))
        exact hEq.trans (hmsg_c0 ⟨2048 * n + j, by omega⟩)
      obtain ⟨se, hbody, hpce, hrege, hx10e, hrese, hprese⟩ :=
        c_p1a_chunk_body h512 oracle msg sn n (by omega) hpcn
          ((hregn .x5 (by decide) (by decide)).trans hx5) hx10n
          ((hregn .x11 (by decide) (by decide)).trans hx11)
          ((hregn .x13 (by decide) (by decide)).trans hx13) hsrc
      obtain ⟨hlatch, hpc_b, hmem_b, hreg_b⟩ :=
        c_p1a_latch_back oracle n (by omega) se hpce hx10e
          ((hrege .x19 (by decide) (by decide)).trans ((hregn .x19 (by decide) (by decide)).trans hx19))
      refine ⟨_, by simpa [Nat.mul_succ, Nat.add_assoc] using (hrun_n.trans hbody).trans hlatch,
        hpc_b, fun reg h10 h12 => (hreg_b reg).trans ((hrege reg h10 h12).trans (hregn reg h10 h12)),
        (hreg_b .x10).trans hx10e, ?_, ?_⟩
      · intro idx hidx
        rw [c_readBuffer_of_mem_eq hmem_b]
        by_cases hlt : idx < 2048 * n
        · exact (readBuffer_congr se sn (C_MSG + 256 * idx + 192) 32
            (fun b hb => hprese _ (by omega) (fun j hj => by omega))).trans (hresn idx hlt)
        · have hj : idx - 2048 * n < 2048 := by omega
          have heq : 2048 * n + (idx - 2048 * n) = idx := by omega
          simpa only [heq] using hrese (idx - 2048 * n) hj
      · intro q hq hout
        rw [c_getByte_of_mem_eq hmem_b]
        exact (hprese q hq (fun j hj => hout (2048 * n + j) (by omega))).trans
          (hpresn q hq (fun idx hidx => hout idx (by omega)))
  obtain ⟨sp, hrun_p, hpcp, hregp, hx10p, hresp, hpresp⟩ := hind 8191 (le_refl _)
  have hsrc_last : ∀ j (hj : j < 2048),
      readBuffer sp (C_MSG + 256 * (2048 * 8191 + j) + 192) 64 =
        leafC0Input (msg ⟨2048 * 8191 + j, by omega⟩) := by
    intro j hj
    have hEq := readBuffer_congr sp s0 (C_MSG + 256 * (2048 * 8191 + j) + 192) 64
      (fun b hb => hpresp _ (by omega) (fun idx hidx => by omega))
    exact hEq.trans (hmsg_c0 ⟨2048 * 8191 + j, by omega⟩)
  obtain ⟨se, hbody, hpce, hrege, hx10e, hrese, hprese⟩ :=
    c_p1a_chunk_body h512 oracle msg sp 8191 (by omega) hpcp
      ((hregp .x5 (by decide) (by decide)).trans hx5) hx10p
      ((hregp .x11 (by decide) (by decide)).trans hx11)
      ((hregp .x13 (by decide) (by decide)).trans hx13) hsrc_last
  obtain ⟨hlatch, hpc_l, hmem_l, hreg_l⟩ :=
    c_p1a_latch_exit oracle se hpce hx10e
      ((hrege .x19 (by decide) (by decide)).trans ((hregp .x19 (by decide) (by decide)).trans hx19))
  let sLoop := execInstrBr se (.BEQ .x10 .x19 (8#13))
  let sFin := c_mid1AInstrs.foldl execInstrBr sLoop
  have hmid_run := c_mid1A_run oracle sLoop hpc_l
  obtain ⟨hpc_f, hmem_f, hx5_f, hx8_f, hx9_f, hx10_f, hx11_f, hx13_f, hx18_f, hx19_f, hx26_f⟩ :=
    c_mid1A_spec sLoop hpc_l
      ((hreg_l .x5).trans ((hrege .x5 (by decide) (by decide)).trans ((hregp .x5 (by decide) (by decide)).trans hx5)))
      ((hreg_l .x8).trans ((hrege .x8 (by decide) (by decide)).trans ((hregp .x8 (by decide) (by decide)).trans hx8)))
      ((hreg_l .x9).trans ((hrege .x9 (by decide) (by decide)).trans ((hregp .x9 (by decide) (by decide)).trans hx9)))
      ((hreg_l .x18).trans ((hrege .x18 (by decide) (by decide)).trans ((hregp .x18 (by decide) (by decide)).trans hx18)))
      ((hreg_l .x26).trans ((hrege .x26 (by decide) (by decide)).trans ((hregp .x26 (by decide) (by decide)).trans hx26)))
  have hpres_all : ∀ q : Nat, q < 2 ^ 64 →
      (∀ idx < LENGTH, q < C_MSG + 256 * idx + 192 ∨ C_MSG + 256 * idx + 224 ≤ q) →
      sFin.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q) := by
    intro q hq hout
    rw [c_getByte_of_mem_eq hmem_f, c_getByte_of_mem_eq hmem_l]
    exact (hprese q hq (fun j hj => hout (2048 * 8191 + j) (by omega))).trans
      (hpresp q hq (fun idx hidx => hout idx (by omega)))
  have hc0_all : ∀ i : Index,
      readBuffer sFin (C_MSG + 256 * i.val + 192) 32 = c64 (leafC0Input (msg i)) := by
    intro i
    have hi := i.isLt
    rw [c_readBuffer_of_mem_eq hmem_f, c_readBuffer_of_mem_eq hmem_l]
    by_cases hlt : i.val < 2048 * 8191
    · exact (readBuffer_congr se sp (C_MSG + 256 * i.val + 192) 32
        (fun b hb => hprese _ (by omega) (fun j hj => by omega))).trans (hresp i.val hlt)
    · have hj : i.val - 2048 * 8191 < 2048 := by omega
      have heq : 2048 * 8191 + (i.val - 2048 * 8191) = i.val := by omega
      have hr := hrese (i.val - 2048 * 8191) hj
      have hfin : (⟨2048 * 8191 + (i.val - 2048 * 8191), by omega⟩ : Index) = i := Fin.ext heq
      rw [hfin] at hr
      simpa only [heq] using hr
  refine ⟨sFin,
    by simpa only [show 6146 * 8191 + 6144 + 1 + 9 = 50348040 by decide,
      show 20482 * 8191 + 20480 + 1 + 9 = 167788552 by decide,
      show 2048 * 8191 + 2048 + 0 + 0 = 16777216 by decide] using
      (((hrun_p.trans hbody).trans hlatch).trans hmid_run),
    hpc_f, hx5_f, hx8_f, hx9_f, hx10_f, hx11_f, hx13_f, hx18_f, hx19_f, hx26_f, ?_, ?_, ?_⟩
  · intro i j hj
    have hi := i.isLt
    rw [hpres_all (C_MSG + 256 * i.val + j) (by omega) (fun idx _ => by
      by_cases he : idx = i.val
      · subst he; omega
      · omega)]
    exact hmsg i j (by omega)
  · intro i
    have hi := i.isLt
    rw [readBuffer_p1 sFin (C_MSG + 256 * i.val + 24)]
    have hmid_eq : readBuffer sFin (C_MSG + 256 * i.val + 24) 168 = (msg i).extractLsb' 192 1344 := by
      have h := read_serialized_slice sFin (msg i) (C_MSG + 256 * i.val + 24) 24 168 (fun j hj => by
        rw [show C_MSG + 256 * i.val + 24 + j = C_MSG + 256 * i.val + (24 + j) by omega,
          hpres_all (C_MSG + 256 * i.val + (24 + j)) (by omega) (fun idx _ => by
            by_cases he : idx = i.val
            · subst he; omega
            · omega)]
        exact hmsg i (24 + j) (by omega))
      exact h
    have hadd : C_MSG + 256 * i.val + 24 + 168 = C_MSG + 256 * i.val + 192 := by omega
    rw [hadd, hc0_all i, hmid_eq]
    rfl
  · intro q hq hout
    exact hpres_all q hq (fun idx hidx => by omega)

/-! ### 2. Phase 1B (`P1`: words `10277..16432`) -/

private theorem c_pc_beq_16421 :
    BitVec.ofNat 64 (0x1000 + 4 * 16421) + signExtend13 (8#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 16423) := by decide

private theorem c_pc_jal_16422 :
    BitVec.ofNat 64 (0x1000 + 4 * 16422) + signExtend21 (2072572#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 10277) := by decide

private def c_mid1BInstrs : List Instr :=
  [.ADDI .x11 .x0 (64#12), .ADDI .x13 .x0 (0#12),
   .ADDI .x10 .x8 (3840#12), .ADDI .x12 .x18 (4064#12),
   .ADDI .x6 .x0 (1023#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (2047#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (1792#12), .ADD .x19 .x8 .x6]

private theorem c_mid1B_run (oracle : Oracle) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 16423)) :
    DetRun oracle (submission.image .commit) s 10 (c_mid1BInstrs.foldl execInstrBr s) 10 0 := by
  have hall : ∀ ins ∈ c_mid1BInstrs, c_isPureAlu ins = true := by decide
  apply c_exec_alu_list c_mid1BInstrs s
  intro i hi
  have hi' : i < 10 := hi
  have hpc_i : ((c_mid1BInstrs.take i).foldl execInstrBr s).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (16423 + i)) := by
    have h := c_foldl_pureAlu_pc (c_mid1BInstrs.take i) s (0x1000 + 4 * 16423)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitMid1BInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem c_mid1B_spec (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 16423))
    (hx5 : s.getReg .x5 = 0#64)
    (hx8 : s.getReg .x8 = BitVec.ofNat 64 C_MSG)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx18 : s.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s' := c_mid1BInstrs.foldl execInstrBr s
    s'.pc = BitVec.ofNat 64 (0x1000 + 4 * 16433) ∧
    s'.mem = s.mem ∧
    s'.getReg .x5 = 0#64 ∧
    s'.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
    s'.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s'.getReg .x10 = BitVec.ofNat 64 (C_MSG - 256) ∧
    s'.getReg .x11 = 64#64 ∧
    s'.getReg .x12 = BitVec.ofNat 64 (C_ROW - 32) ∧
    s'.getReg .x13 = 0#64 ∧
    s'.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
    s'.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256) ∧
    s'.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ c_mid1BInstrs, c_isPureAlu ins = true := by decide
  refine ⟨?_, c_foldl_pureAlu_mem c_mid1BInstrs s hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (c_foldl_pureAlu_pc c_mid1BInstrs s (0x1000 + 4 * 16423) hall hpc).trans (by decide)
  all_goals (
    simp only [c_mid1BInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx5, hx8, hx9, hx18, hx26]
    try decide)

/-- One `p1` leaf step (`ADDI x10, x10, 256; ADDI x12, x10, 0; ECALL PERM`): 3 steps, 32 cycles, 1 call. -/
private theorem c_p1b_leaf_step (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (s : MachineState)
    (k leafIdx : Nat) (hk : k < 2048) (hleaf : leafIdx < LENGTH)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (10277 + 3 * k)))
    (hx5 : s.getReg .x5 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * leafIdx - 232))
    (hx11 : s.getReg .x11 = 200#64)
    (hx13 : s.getReg .x13 = 1#64)
    (hsrc : readBuffer s (C_MSG + 256 * leafIdx + 24) 200 =
      leafP1Input (oracle.compression ((leafC0Input (msg ⟨leafIdx, hleaf⟩)).cast h512.symm))
        (msg ⟨leafIdx, hleaf⟩)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let y : BitVec 1600 := oracle.permutation (leafP1Input (c64 (leafC0Input (msg ⟨leafIdx, hleaf⟩))) (msg ⟨leafIdx, hleaf⟩))
    ∃ s',
      DetRun oracle (submission.image .commit) s 3 s' 32 1 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (10277 + 3 * (k + 1))) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s'.getReg reg = s.getReg reg) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (leafIdx + 1) - 232) ∧
      readBuffer s' (C_MSG + 256 * leafIdx + 24) 40 = y.extractLsb' 0 320 ∧
      CommitMemOutside s s' (C_MSG + 256 * leafIdx + 24) (C_MSG + 256 * leafIdx + 224) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hCM : C_MSG = 4096 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let y : BitVec 1600 := oracle.permutation (leafP1Input (c64 (leafC0Input (msg ⟨leafIdx, hleaf⟩))) (msg ⟨leafIdx, hleaf⟩))
  let s1 := execInstrBr s (.ADDI .x10 .x10 (256#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x10 (0#12))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_MSG + 256 * leafIdx + 24)) y
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (10277 + 3 * k + 1)) := c_pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (10277 + 3 * k + 2)) := c_pc_step_idx s1 _ hs1_pc
  have hs1_x10 : s1.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * leafIdx + 24) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      c_add_signExtend12_ofNat_small _ 256 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_x10 : s2.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * leafIdx + 24) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x12 .x10 (by decide), hs1_x10]
  have hs2_x12 : s2.getReg .x12 = BitVec.ofNat 64 (C_MSG + 256 * leafIdx + 24) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs1_x10,
      c_add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
  have hs2_mem : s2.mem = s.mem := (c_mem_exec_ADDI s1 _ _ _).trans (c_mem_exec_ADDI s _ _ _)
  have hs2_reg : ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s2.getReg reg = s.getReg reg := fun reg h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x12 reg (Ne.symm h12), c_getReg_setReg_ne .x10 reg (Ne.symm h10)]
  have hr0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_p1 s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc)) rfl
  have hr1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_p1 s1 k 1 hk (by omega) hs1_pc) rfl
  have hread : (oracle.permutation (readBuffer s2 (C_MSG + 256 * leafIdx + 24) 200) : BitVec 1600) = y := by
    rw [c_readBuffer_of_mem_eq hs2_mem, hsrc]
  have hr2 : DetRun oracle (submission.image .commit) s2 1 s3 30 1 :=
    DetRun.permute_eq (commit_fetch_p1 s2 k 2 hk (by omega) hs2_pc)
      ((hs2_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg .x13 (by decide) (by decide)).trans hx13)
      (C_MSG + 256 * leafIdx + 24) (C_MSG + 256 * leafIdx + 24)
      hs2_x10 hs2_x12 (by omega) (by omega) (by omega) (by omega) y hread
  refine ⟨s3, (hr0.trans hr1).trans hr2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c_pc_writeBits, c_pc_step_idx s2 _ hs2_pc]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · intro reg h10 h12
    exact (writeBits_register s2 _ y reg).trans (hs2_reg reg h10 h12)
  · rw [writeBits_register s2 _ y .x10, hs2_x10]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · exact writeBits_readBuffer_perm40 s2 _ y
  · exact (CommitMemOutside.of_mem_eq hs2_mem _ _).trans
      (by simpa only [show C_MSG + 256 * leafIdx + 24 + (1600 + 7) / 8 = C_MSG + 256 * leafIdx + 224 by omega] using
        c_memPreserved_writeBits s2 (C_MSG + 256 * leafIdx + 24) y (by omega))

/-- One 2048-leaf `p1` chunk body (`10277..16420`): 6144 steps, 65536 cycles, 2048 calls. -/
private theorem c_p1b_chunk_body (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (sc : MachineState)
    (chunkIdx : Nat) (hchunk : chunkIdx < 8192)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 10277))
    (hx5 : sc.getReg .x5 = 0#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * chunkIdx) - 232))
    (hx11 : sc.getReg .x11 = 200#64)
    (hx13 : sc.getReg .x13 = 1#64)
    (hsrc_all : ∀ j (hj : j < 2048),
      readBuffer sc (C_MSG + 256 * (2048 * chunkIdx + j) + 24) 200 =
        leafP1Input (oracle.compression ((leafC0Input (msg ⟨2048 * chunkIdx + j, by unfold LENGTH LOG_LENGTH; omega⟩)).cast h512.symm))
          (msg ⟨2048 * chunkIdx + j, by unfold LENGTH LOG_LENGTH; omega⟩)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    ∃ se,
      DetRun oracle (submission.image .commit) sc 6144 se 65536 2048 ∧
      se.pc = BitVec.ofNat 64 (0x1000 + 4 * 16421) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → se.getReg reg = sc.getReg reg) ∧
      se.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * (chunkIdx + 1)) - 232) ∧
      (∀ j (hj : j < 2048),
        readBuffer se (C_MSG + 256 * (2048 * chunkIdx + j) + 24) 40 =
          ((oracle.permutation (leafP1Input (c64 (leafC0Input (msg ⟨2048 * chunkIdx + j, by unfold LENGTH LOG_LENGTH; omega⟩)))
            (msg ⟨2048 * chunkIdx + j, by unfold LENGTH LOG_LENGTH; omega⟩)) : BitVec 1600)).extractLsb' 0 320) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (∀ j < 2048, q < C_MSG + 256 * (2048 * chunkIdx + j) + 24 ∨
          C_MSG + 256 * (2048 * chunkIdx + j) + 224 ≤ q) →
        se.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hCM : C_MSG = 4096 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  have hind : ∀ k (hk : k ≤ 2048),
      ∃ sk,
        DetRun oracle (submission.image .commit) sc (3 * k) sk (32 * k) k ∧
        sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (10277 + 3 * k)) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sk.getReg reg = sc.getReg reg) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * chunkIdx + k) - 232) ∧
        (∀ j (hj : j < k),
          readBuffer sk (C_MSG + 256 * (2048 * chunkIdx + j) + 24) 40 =
            ((oracle.permutation (leafP1Input (c64 (leafC0Input (msg ⟨2048 * chunkIdx + j, by omega⟩)))
              (msg ⟨2048 * chunkIdx + j, by omega⟩)) : BitVec 1600)).extractLsb' 0 320) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ j < k, q < C_MSG + 256 * (2048 * chunkIdx + j) + 24 ∨
            C_MSG + 256 * (2048 * chunkIdx + j) + 224 ≤ q) →
          sk.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩
    | succ k ih =>
      obtain ⟨sk, hrun_k, hpck, hregk, hx10k, hresk, hpresk⟩ := ih (by omega)
      have hsrc : readBuffer sk (C_MSG + 256 * (2048 * chunkIdx + k) + 24) 200 =
          leafP1Input (c64 (leafC0Input (msg ⟨2048 * chunkIdx + k, by omega⟩)))
            (msg ⟨2048 * chunkIdx + k, by omega⟩) := by
        have hEq := readBuffer_congr sk sc (C_MSG + 256 * (2048 * chunkIdx + k) + 24) 200
          (fun b hb => hpresk _ (by omega) (fun j hj => by omega))
        exact hEq.trans (hsrc_all k (by omega))
      obtain ⟨s', hstep, hpc', hreg', hx10', hres', hpres'⟩ :=
        c_p1b_leaf_step h512 oracle msg sk k (2048 * chunkIdx + k) (by omega) (by omega)
          hpck ((hregk .x5 (by decide) (by decide)).trans hx5) hx10k
          ((hregk .x11 (by decide) (by decide)).trans hx11)
          ((hregk .x13 (by decide) (by decide)).trans hx13) hsrc
      refine ⟨s', by simpa [Nat.mul_succ, Nat.add_assoc] using hrun_k.trans hstep, hpc',
        fun reg h10 h12 => (hreg' reg h10 h12).trans (hregk reg h10 h12),
        by simpa only [Nat.add_assoc] using hx10', ?_, ?_⟩
      · intro j hj
        by_cases hjk : j < k
        · exact (hpres'.readBuffer_eq (by omega) (by omega)).trans (hresk j hjk)
        · have heqj : j = k := by omega
          subst heqj; exact hres'
      · intro q hq hout
        exact (hpres' q hq (hout k (by omega))).trans (hpresk q hq (fun j hj => hout j (by omega)))
  simpa only [show 2048 * (chunkIdx + 1) = 2048 * chunkIdx + 2048 by omega] using hind 2048 (le_refl _)

private theorem c_p1b_latch_back (oracle : Oracle) (chunkIdx : Nat) (hchunk : chunkIdx < 8191)
    (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 16421))
    (hx10 : se.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * (chunkIdx + 1)) - 232))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 232)) :
    let sb := execInstrBr (execInstrBr se (.BEQ .x10 .x19 (8#13))) (.JAL .x0 (2072572#21))
    DetRun oracle (submission.image .commit) se 2 sb 2 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 10277) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  have hCM : C_MSG = 4096 := rfl
  let s1 := execInstrBr se (.BEQ .x10 .x19 (8#13))
  let s2 := execInstrBr s1 (.JAL .x0 (2072572#21))
  have hst1 : DetRun oracle (submission.image .commit) se 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1BInstr se 16421 (by omega) (by omega) hpc) rfl
  have hne : (se.getReg .x10 == se.getReg .x19) = false := by
    rw [hx10, hx19, beq_eq_false_iff_ne]
    exact c_bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 16422) := by
    simp only [s1, execInstrBr, hne, Bool.false_eq_true, ite_false, c_pc_setPC]
    exact c_pc_step_idx se 16421 hpc
  have hst2 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1BInstr s1 16422 (by omega) (by omega) hs1_pc) rfl
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 10277) := by
    simp only [s2, execInstrBr, c_pc_setPC, hs1_pc]
    exact c_pc_jal_16422
  exact ⟨hst1.trans hst2, hs2_pc,
    (c_mem_exec_JAL s1 _ _).trans (c_mem_exec_BEQ se _ _ _),
    fun reg => (c_reg_exec_JAL0 s1 _ reg).trans (c_reg_exec_BEQ se _ _ _ reg)⟩

private theorem c_p1b_latch_exit (oracle : Oracle) (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 16421))
    (hx10 : se.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * 8192) - 232))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 232)) :
    let sb := execInstrBr se (.BEQ .x10 .x19 (8#13))
    DetRun oracle (submission.image .commit) se 1 sb 1 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 16423) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  let sb := execInstrBr se (.BEQ .x10 .x19 (8#13))
  have hst : DetRun oracle (submission.image .commit) se 1 sb 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1BInstr se 16421 (by omega) (by omega) hpc) rfl
  have heq : (se.getReg .x10 == se.getReg .x19) = true := by
    rw [hx10, hx19]; exact beq_self_eq_true _
  have hpc' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 16423) := by
    simp only [sb, execInstrBr, heq, ite_true, c_pc_setPC, hpc]
    exact c_pc_beq_16421
  exact ⟨hst, hpc', c_mem_exec_BEQ se _ _ _, c_reg_exec_BEQ se _ _ _⟩

/-- Full Phase 1B (`P1`, words `10277..16432`): `50,348,041` steps, `536,887,305` cycles,
`16,777,216` permutation calls. Leaves `msg[i][0..64)` = `leafC2Input y_i (msg i)`. -/
theorem commit_phase1B (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 10277))
    (hx5 : s0.getReg .x5 = 0#64)
    (hx8 : s0.getReg .x8 = BitVec.ofNat 64 C_MSG)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 (C_MSG - 232))
    (hx11 : s0.getReg .x11 = 200#64)
    (hx13 : s0.getReg .x13 = 1#64)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx19 : s0.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 232))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hmsgLo : ∀ (i : Index) (j : Nat), j < 24 →
      s0.getByte (BitVec.ofNat 64 (C_MSG + 256 * i.val + j)) = (msg i).extractLsb' (8 * j) 8)
    (hp1 : ∀ i : Index,
      readBuffer s0 (C_MSG + 256 * i.val + 24) 200 =
        leafP1Input (oracle.compression ((leafC0Input (msg i)).cast h512.symm)) (msg i)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 50348041 s1 536887305 16777216 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 16433) ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x10 = BitVec.ofNat 64 (C_MSG - 256) ∧
      s1.getReg .x11 = 64#64 ∧
      s1.getReg .x12 = BitVec.ofNat 64 (C_ROW - 32) ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
      s1.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ i : Index,
        readBuffer s1 (C_MSG + 256 * i.val) 64 =
          leafC2Input (oracle.permutation (leafP1Input (c64 (leafC0Input (msg i))) (msg i))) (msg i)) ∧
      CommitMemOutside s0 s1 C_MSG (C_MSG + 2 ^ 32) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hCM : C_MSG = 4096 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  have hind : ∀ n (hn : n ≤ 8191),
      ∃ sn,
        DetRun oracle (submission.image .commit) s0 (6146 * n) sn (65538 * n) (2048 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 10277) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sn.getReg reg = s0.getReg reg) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2048 * n) - 232) ∧
        (∀ idx (hidx : idx < 2048 * n),
          readBuffer sn (C_MSG + 256 * idx + 24) 40 =
            ((oracle.permutation (leafP1Input (c64 (leafC0Input (msg ⟨idx, by omega⟩)))
              (msg ⟨idx, by omega⟩)) : BitVec 1600)).extractLsb' 0 320) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ idx < 2048 * n, q < C_MSG + 256 * idx + 24 ∨ C_MSG + 256 * idx + 224 ≤ q) →
          sn.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨s0, DetRun.refl _ _ _, hpc, fun _ _ _ => rfl, by simpa using hx10,
        fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩
    | succ n ih =>
      obtain ⟨sn, hrun_n, hpcn, hregn, hx10n, hresn, hpresn⟩ := ih (by omega)
      have hsrc : ∀ j (hj : j < 2048),
          readBuffer sn (C_MSG + 256 * (2048 * n + j) + 24) 200 =
            leafP1Input (c64 (leafC0Input (msg ⟨2048 * n + j, by omega⟩)))
              (msg ⟨2048 * n + j, by omega⟩) := by
        intro j hj
        have hEq := readBuffer_congr sn s0 (C_MSG + 256 * (2048 * n + j) + 24) 200
          (fun b hb => hpresn _ (by omega) (fun idx hidx => by omega))
        exact hEq.trans (hp1 ⟨2048 * n + j, by omega⟩)
      obtain ⟨se, hbody, hpce, hrege, hx10e, hrese, hprese⟩ :=
        c_p1b_chunk_body h512 oracle msg sn n (by omega) hpcn
          ((hregn .x5 (by decide) (by decide)).trans hx5) hx10n
          ((hregn .x11 (by decide) (by decide)).trans hx11)
          ((hregn .x13 (by decide) (by decide)).trans hx13) hsrc
      obtain ⟨hlatch, hpc_b, hmem_b, hreg_b⟩ :=
        c_p1b_latch_back oracle n (by omega) se hpce hx10e
          ((hrege .x19 (by decide) (by decide)).trans ((hregn .x19 (by decide) (by decide)).trans hx19))
      refine ⟨_, by simpa [Nat.mul_succ, Nat.add_assoc] using (hrun_n.trans hbody).trans hlatch,
        hpc_b, fun reg h10 h12 => (hreg_b reg).trans ((hrege reg h10 h12).trans (hregn reg h10 h12)),
        (hreg_b .x10).trans hx10e, ?_, ?_⟩
      · intro idx hidx
        rw [c_readBuffer_of_mem_eq hmem_b]
        by_cases hlt : idx < 2048 * n
        · exact (readBuffer_congr se sn (C_MSG + 256 * idx + 24) 40
            (fun b hb => hprese _ (by omega) (fun j hj => by omega))).trans (hresn idx hlt)
        · have hj : idx - 2048 * n < 2048 := by omega
          have heq : 2048 * n + (idx - 2048 * n) = idx := by omega
          simpa only [heq] using hrese (idx - 2048 * n) hj
      · intro q hq hout
        rw [c_getByte_of_mem_eq hmem_b]
        exact (hprese q hq (fun j hj => hout (2048 * n + j) (by omega))).trans
          (hpresn q hq (fun idx hidx => hout idx (by omega)))
  obtain ⟨sp, hrun_p, hpcp, hregp, hx10p, hresp, hpresp⟩ := hind 8191 (le_refl _)
  have hsrc_last : ∀ j (hj : j < 2048),
      readBuffer sp (C_MSG + 256 * (2048 * 8191 + j) + 24) 200 =
        leafP1Input (c64 (leafC0Input (msg ⟨2048 * 8191 + j, by omega⟩)))
          (msg ⟨2048 * 8191 + j, by omega⟩) := by
    intro j hj
    have hEq := readBuffer_congr sp s0 (C_MSG + 256 * (2048 * 8191 + j) + 24) 200
      (fun b hb => hpresp _ (by omega) (fun idx hidx => by omega))
    exact hEq.trans (hp1 ⟨2048 * 8191 + j, by omega⟩)
  obtain ⟨se, hbody, hpce, hrege, hx10e, hrese, hprese⟩ :=
    c_p1b_chunk_body h512 oracle msg sp 8191 (by omega) hpcp
      ((hregp .x5 (by decide) (by decide)).trans hx5) hx10p
      ((hregp .x11 (by decide) (by decide)).trans hx11)
      ((hregp .x13 (by decide) (by decide)).trans hx13) hsrc_last
  obtain ⟨hlatch, hpc_l, hmem_l, hreg_l⟩ :=
    c_p1b_latch_exit oracle se hpce hx10e
      ((hrege .x19 (by decide) (by decide)).trans ((hregp .x19 (by decide) (by decide)).trans hx19))
  let sLoop := execInstrBr se (.BEQ .x10 .x19 (8#13))
  let sFin := c_mid1BInstrs.foldl execInstrBr sLoop
  have hmid_run := c_mid1B_run oracle sLoop hpc_l
  obtain ⟨hpc_f, hmem_f, hx5_f, hx8_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx18_f, hx19_f, hx26_f⟩ :=
    c_mid1B_spec sLoop hpc_l
      ((hreg_l .x5).trans ((hrege .x5 (by decide) (by decide)).trans ((hregp .x5 (by decide) (by decide)).trans hx5)))
      ((hreg_l .x8).trans ((hrege .x8 (by decide) (by decide)).trans ((hregp .x8 (by decide) (by decide)).trans hx8)))
      ((hreg_l .x9).trans ((hrege .x9 (by decide) (by decide)).trans ((hregp .x9 (by decide) (by decide)).trans hx9)))
      ((hreg_l .x18).trans ((hrege .x18 (by decide) (by decide)).trans ((hregp .x18 (by decide) (by decide)).trans hx18)))
      ((hreg_l .x26).trans ((hrege .x26 (by decide) (by decide)).trans ((hregp .x26 (by decide) (by decide)).trans hx26)))
  have hpres_all : ∀ q : Nat, q < 2 ^ 64 →
      (∀ idx < LENGTH, q < C_MSG + 256 * idx + 24 ∨ C_MSG + 256 * idx + 224 ≤ q) →
      sFin.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q) := by
    intro q hq hout
    rw [c_getByte_of_mem_eq hmem_f, c_getByte_of_mem_eq hmem_l]
    exact (hprese q hq (fun j hj => hout (2048 * 8191 + j) (by omega))).trans
      (hpresp q hq (fun idx hidx => hout idx (by omega)))
  have hy40_all : ∀ i : Index,
      readBuffer sFin (C_MSG + 256 * i.val + 24) 40 =
        ((oracle.permutation (leafP1Input (c64 (leafC0Input (msg i))) (msg i)) : BitVec 1600)).extractLsb' 0 320 := by
    intro i
    have hi := i.isLt
    rw [c_readBuffer_of_mem_eq hmem_f, c_readBuffer_of_mem_eq hmem_l]
    by_cases hlt : i.val < 2048 * 8191
    · exact (readBuffer_congr se sp (C_MSG + 256 * i.val + 24) 40
        (fun b hb => hprese _ (by omega) (fun j hj => by omega))).trans (hresp i.val hlt)
    · have hj : i.val - 2048 * 8191 < 2048 := by omega
      have heq : 2048 * 8191 + (i.val - 2048 * 8191) = i.val := by omega
      have hr := hrese (i.val - 2048 * 8191) hj
      have hfin : (⟨2048 * 8191 + (i.val - 2048 * 8191), by omega⟩ : Index) = i := Fin.ext heq
      rw [hfin] at hr
      simpa only [heq] using hr
  refine ⟨sFin,
    by simpa only [show 6146 * 8191 + 6144 + 1 + 10 = 50348041 by decide,
      show 65538 * 8191 + 65536 + 1 + 10 = 536887305 by decide,
      show 2048 * 8191 + 2048 + 0 + 0 = 16777216 by decide] using
      (((hrun_p.trans hbody).trans hlatch).trans hmid_run),
    hpc_f, hx5_f, hx8_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx18_f, hx19_f, hx26_f, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    rw [readBuffer_c2 sFin (C_MSG + 256 * i.val), hy40_all i]
    have hlo_eq : readBuffer sFin (C_MSG + 256 * i.val) 24 = (msg i).extractLsb' 0 192 := by
      have h := read_serialized_slice sFin (msg i) (C_MSG + 256 * i.val) 0 24 (fun j hj => by
        rw [Nat.zero_add, hpres_all (C_MSG + 256 * i.val + j) (by omega) (fun idx _ => by
          by_cases he : idx = i.val
          · subst he; omega
          · omega)]
        exact hmsgLo i j hj)
      simpa only [Nat.add_zero] using h
    rw [hlo_eq]
    rfl
  · intro q hq hout
    exact hpres_all q hq (fun idx hidx => by omega)

end CommitGolfCandidate
