import CommitGolfCandidate.MoonCommitLeaf

/-! Exact RV64IM execution proofs for Phases 1C (`C2`, words `16433..22591`) and 1D (`C3`,
words `22592..28746`) of the 64-32 `commit` image:
- Phase 1C: `8,388,608` pairs of `C2` compressions writing `a_{2p}` at `row[p]+0` and `a_{2p+1}`
  at `row[p]+88`, leaving zero gaps `row[p]+32..40`, `row[p]+80..88` and salts `row[p]+40..80` intact.
- Phase 1D: `8,388,608` pairs of `SM-PLS-40` `C3` compressions writing all `16,777,216` `L0` leaf
  digests `nodeVal ... 0 i` directly to `C_TD + 32 * heapIdx 0 i`, preserving all salts in `C_ROW`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Phase 1C (`C2`: words `16433..22591`) -/

private theorem c_pc_beq_22577 :
    BitVec.ofNat 64 (0x1000 + 4 * 22577) + signExtend13 (8#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 22579) := by decide

private theorem c_pc_jal_22578 :
    BitVec.ofNat 64 (0x1000 + 4 * 22578) + signExtend21 (2072572#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 16433) := by decide

private def c_mid1CInstrs : List Instr :=
  [.ADDI .x10 .x18 (4032#12),
   .ADDI .x6 .x0 (127#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (2047#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (2016#12), .ADD .x12 .x9 .x6,
   .ADDI .x6 .x0 (239#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (2047#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (1984#12), .ADD .x19 .x18 .x6]

private theorem c_mid1C_run (oracle : Oracle) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 22579)) :
    DetRun oracle (submission.image .commit) s 13 (c_mid1CInstrs.foldl execInstrBr s) 13 0 := by
  have hall : ∀ ins ∈ c_mid1CInstrs, c_isPureAlu ins = true := by decide
  apply c_exec_alu_list c_mid1CInstrs s
  intro i hi
  have hi' : i < 13 := hi
  have hpc_i : ((c_mid1CInstrs.take i).foldl execInstrBr s).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (22579 + i)) := by
    have h := c_foldl_pureAlu_pc (c_mid1CInstrs.take i) s (0x1000 + 4 * 22579)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitMid1CInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem c_mid1C_spec (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 22579))
    (hx5 : s.getReg .x5 = 0#64)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s.getReg .x11 = 64#64)
    (hx13 : s.getReg .x13 = 0#64)
    (hx18 : s.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s' := c_mid1CInstrs.foldl execInstrBr s
    s'.pc = BitVec.ofNat 64 (0x1000 + 4 * 22592) ∧
    s'.mem = s.mem ∧
    s'.getReg .x5 = 0#64 ∧
    s'.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s'.getReg .x10 = BitVec.ofNat 64 (C_ROW - 64) ∧
    s'.getReg .x11 = 64#64 ∧
    s'.getReg .x12 = BitVec.ofNat 64 (C_TD + 536870912 - 32) ∧
    s'.getReg .x13 = 0#64 ∧
    s'.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
    s'.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes - 64) ∧
    s'.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ c_mid1CInstrs, c_isPureAlu ins = true := by decide
  refine ⟨?_, c_foldl_pureAlu_mem c_mid1CInstrs s hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (c_foldl_pureAlu_pc c_mid1CInstrs s (0x1000 + 4 * 22579) hall hpc).trans (by decide)
  all_goals (
    simp only [c_mid1CInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx5, hx9, hx11, hx13, hx18, hx26, rowBytes_eq]
    try decide)

/-- One `c2Pair` pair step (2 leaves): 6 steps, 20 cycles, 2 compression calls. -/
private theorem c_p1c_pair_step (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (s : MachineState)
    (k pairIdx : Nat) (hk : k < 1024) (hpair : pairIdx < LENGTH / 2)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (16433 + 6 * k)))
    (hx5 : s.getReg .x5 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * pairIdx - 256))
    (hx11 : s.getReg .x11 = 64#64)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx - 32))
    (hx13 : s.getReg .x13 = 0#64)
    (hsrcE : readBuffer s (C_MSG + 256 * (2 * pairIdx)) 64 =
      leafC2Input (oracle.permutation (leafP1Input
        (oracle.compression ((leafC0Input (msg ⟨2 * pairIdx, by unfold LENGTH LOG_LENGTH at *; omega⟩)).cast h512.symm))
        (msg ⟨2 * pairIdx, by unfold LENGTH LOG_LENGTH at *; omega⟩)))
        (msg ⟨2 * pairIdx, by unfold LENGTH LOG_LENGTH at *; omega⟩))
    (hsrcO : readBuffer s (C_MSG + 256 * (2 * pairIdx + 1)) 64 =
      leafC2Input (oracle.permutation (leafP1Input
        (oracle.compression ((leafC0Input (msg ⟨2 * pairIdx + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩)).cast h512.symm))
        (msg ⟨2 * pairIdx + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩)))
        (msg ⟨2 * pairIdx + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ s',
      DetRun oracle (submission.image .commit) s 6 s' 20 2 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (16433 + 6 * (k + 1))) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s'.getReg reg = s.getReg reg) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (pairIdx + 1) - 256) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_ROW + 120 * (pairIdx + 1) - 32) ∧
      readBuffer s' (C_ROW + 120 * pairIdx) 32 =
        leafA c64 p200 (msg ⟨2 * pairIdx, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer s' (C_ROW + 120 * pairIdx + 88) 32 =
        leafA c64 p200 (msg ⟨2 * pairIdx + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < C_ROW + 120 * pairIdx ∨
         (C_ROW + 120 * pairIdx + 32 ≤ q ∧ q < C_ROW + 120 * pairIdx + 88) ∨
         C_ROW + 120 * pairIdx + 120 ≤ q) →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hCM : C_MSG = 4096 := rfl
  have hCT : C_TD = 4294971424 := rfl
  have hCR : C_ROW = 5368713248 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  let aE := leafA c64 p200 (msg ⟨2 * pairIdx, by omega⟩)
  let aO := leafA c64 p200 (msg ⟨2 * pairIdx + 1, by omega⟩)
  -- First half: even leaf 2*pairIdx
  let s1 := execInstrBr s (.ADDI .x10 .x10 (256#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (32#12))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_ROW + 120 * pairIdx)) aE
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (16433 + 6 * k + 1)) := c_pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (16433 + 6 * k + 2)) := c_pc_step_idx s1 _ hs1_pc
  have hs1_x10 : s1.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2 * pairIdx)) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      c_add_signExtend12_ofNat_small _ 256 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_x10 : s2.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2 * pairIdx)) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne .x12 .x10 (by decide), hs1_x10]
  have hs2_x12 : s2.getReg .x12 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      c_getReg_setReg_ne .x10 .x12 (by decide), hx12,
      c_add_signExtend12_ofNat_small _ 32 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_mem : s2.mem = s.mem := (c_mem_exec_ADDI s1 _ _ _).trans (c_mem_exec_ADDI s _ _ _)
  have hs2_reg : ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s2.getReg reg = s.getReg reg := fun reg h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x12 reg (Ne.symm h12), c_getReg_setReg_ne .x10 reg (Ne.symm h10)]
  have hr0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_c2Pair s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc)) rfl
  have hr1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_c2Pair s1 k 1 hk (by omega) hs1_pc) rfl
  have hreadE : oracle.compression ((readBuffer s2 (C_MSG + 256 * (2 * pairIdx)) 64).cast h512.symm) = aE := by
    rw [c_readBuffer_of_mem_eq hs2_mem, hsrcE]; rfl
  have hr2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h512 (commit_fetch_c2Pair s2 k 2 hk (by omega) hs2_pc)
      ((hs2_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg .x13 (by decide) (by decide)).trans hx13)
      (C_MSG + 256 * (2 * pairIdx)) (C_ROW + 120 * pairIdx)
      hs2_x10 hs2_x12 (by omega) (by omega) (by omega) (by omega) aE hreadE
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (16433 + 6 * k + 3)) := by
    rw [c_pc_writeBits, c_pc_step_idx s2 _ hs2_pc]
  have hpresE : CommitMemOutside s s3 (C_ROW + 120 * pairIdx) (C_ROW + 120 * pairIdx + 32) :=
    (CommitMemOutside.of_mem_eq hs2_mem _ _).trans
      (by simpa only [show C_ROW + 120 * pairIdx + (256 + 7) / 8 = C_ROW + 120 * pairIdx + 32 by omega] using
        c_memPreserved_writeBits s2 (C_ROW + 120 * pairIdx) aE (by omega))
  -- Second half: odd leaf 2*pairIdx + 1
  let s4 := execInstrBr s3 (.ADDI .x10 .x10 (256#12))
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 (88#12))
  let s6 := writeBits s5 (BitVec.ofNat 64 (C_ROW + 120 * pairIdx + 88)) aO
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (16433 + 6 * k + 4)) := c_pc_step_idx s3 _ hs3_pc
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * (16433 + 6 * k + 5)) := c_pc_step_idx s4 _ hs4_pc
  have hs3_x10 : s3.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2 * pairIdx)) :=
    (writeBits_register s2 _ aE .x10).trans hs2_x10
  have hs3_x12 : s3.getReg .x12 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx) :=
    (writeBits_register s2 _ aE .x12).trans hs2_x12
  have hs4_x10 : s4.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2 * pairIdx + 1)) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs3_x10,
      c_add_signExtend12_ofNat_small _ 256 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs5_x10 : s5.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (2 * pairIdx + 1)) := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne .x12 .x10 (by decide), hs4_x10]
  have hs5_x12 : s5.getReg .x12 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx + 88) := by
    simp only [s5, s4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      c_getReg_setReg_ne .x10 .x12 (by decide), hs3_x12,
      c_add_signExtend12_ofNat_small _ 88 (by omega)]
  have hs5_mem : s5.mem = s3.mem := (c_mem_exec_ADDI s4 _ _ _).trans (c_mem_exec_ADDI s3 _ _ _)
  have hs5_reg : ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s5.getReg reg = s.getReg reg := fun reg h10 h12 => by
    have h1 : s5.getReg reg = s3.getReg reg := by
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC,
        c_getReg_setReg_ne .x12 reg (Ne.symm h12), c_getReg_setReg_ne .x10 reg (Ne.symm h10)]
    exact h1.trans ((writeBits_register s2 _ aE reg).trans (hs2_reg reg h10 h12))
  have hr3 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (commit_fetch_c2Pair s3 k 3 hk (by omega) hs3_pc) rfl
  have hr4 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (commit_fetch_c2Pair s4 k 4 hk (by omega) hs4_pc) rfl
  have hreadO : oracle.compression ((readBuffer s5 (C_MSG + 256 * (2 * pairIdx + 1)) 64).cast h512.symm) = aO := by
    rw [c_readBuffer_of_mem_eq hs5_mem, hpresE.readBuffer_eq (by omega) (by omega), hsrcO]; rfl
  have hr5 : DetRun oracle (submission.image .commit) s5 1 s6 8 1 :=
    DetRun.compress_eq h512 (commit_fetch_c2Pair s5 k 5 hk (by omega) hs5_pc)
      ((hs5_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs5_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs5_reg .x13 (by decide) (by decide)).trans hx13)
      (C_MSG + 256 * (2 * pairIdx + 1)) (C_ROW + 120 * pairIdx + 88)
      hs5_x10 hs5_x12 (by omega) (by omega) (by omega) (by omega) aO hreadO
  have hpresO : CommitMemOutside s3 s6 (C_ROW + 120 * pairIdx + 88) (C_ROW + 120 * pairIdx + 120) :=
    (CommitMemOutside.of_mem_eq hs5_mem _ _).trans
      (by simpa only [show C_ROW + 120 * pairIdx + 88 + (256 + 7) / 8 = C_ROW + 120 * pairIdx + 120 by omega] using
        c_memPreserved_writeBits s5 (C_ROW + 120 * pairIdx + 88) aO (by omega))
  refine ⟨s6, (((hr0.trans hr1).trans hr2).trans ((hr3.trans hr4).trans hr5)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c_pc_writeBits, c_pc_step_idx s5 _ hs5_pc]; exact congrArg (BitVec.ofNat 64) (by omega)
  · intro reg h10 h12; exact (writeBits_register s5 _ aO reg).trans (hs5_reg reg h10 h12)
  · rw [writeBits_register s5 _ aO .x10, hs5_x10]
    have hnat : C_MSG + 256 * (2 * pairIdx + 1) = C_MSG + 512 * (pairIdx + 1) - 256 := by
      have h1 : 512 * (pairIdx + 1) = 256 * (2 * pairIdx + 1) + 256 := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.add_assoc]
      rw [h1, ← Nat.add_assoc, Nat.add_sub_cancel]
    exact congrArg (BitVec.ofNat 64) hnat
  · rw [writeBits_register s5 _ aO .x12, hs5_x12]
    exact congrArg (BitVec.ofNat 64) (by clear * - hCR; omega)
  · rw [hpresO.readBuffer_eq (by omega) (by omega)]; exact writeBits_readBuffer_digest s2 _ aE
  · exact writeBits_readBuffer_digest s5 _ aO
  · intro q hq hout
    rcases hout with h1 | ⟨h2, h3⟩ | h4
    · exact (hpresO q hq (by omega)).trans (hpresE q hq (by omega))
    · exact (hpresO q hq (by omega)).trans (hpresE q hq (by omega))
    · exact (hpresO q hq (by omega)).trans (hpresE q hq (by omega))

/-- One 1024-pair `c2Pair` chunk body (`16433..22576`): 6144 steps, 20480 cycles, 2048 calls. -/
private theorem c_p1c_chunk_body (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (sc : MachineState)
    (chunkIdx : Nat) (hchunk : chunkIdx < 8192)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 16433))
    (hx5 : sc.getReg .x5 = 0#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (1024 * chunkIdx) - 256))
    (hx11 : sc.getReg .x11 = 64#64)
    (hx12 : sc.getReg .x12 = BitVec.ofNat 64 (C_ROW + 120 * (1024 * chunkIdx) - 32))
    (hx13 : sc.getReg .x13 = 0#64)
    (hsrc_all : ∀ i : Index,
      readBuffer sc (C_MSG + 256 * i.val) 64 =
        leafC2Input (oracle.permutation (leafP1Input
          (oracle.compression ((leafC0Input (msg i)).cast h512.symm)) (msg i))) (msg i)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ se,
      DetRun oracle (submission.image .commit) sc 6144 se 20480 2048 ∧
      se.pc = BitVec.ofNat 64 (0x1000 + 4 * 22577) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → se.getReg reg = sc.getReg reg) ∧
      se.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (1024 * (chunkIdx + 1)) - 256) ∧
      se.getReg .x12 = BitVec.ofNat 64 (C_ROW + 120 * (1024 * (chunkIdx + 1)) - 32) ∧
      (∀ j (hj : j < 1024),
        let p := 1024 * chunkIdx + j
        readBuffer se (C_ROW + 120 * p) 32 =
          leafA c64 p200 (msg ⟨2 * p, by unfold LENGTH LOG_LENGTH; omega⟩) ∧
        readBuffer se (C_ROW + 120 * p + 88) 32 =
          leafA c64 p200 (msg ⟨2 * p + 1, by unfold LENGTH LOG_LENGTH; omega⟩)) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (∀ j < 1024,
          let p := 1024 * chunkIdx + j
          q < C_ROW + 120 * p ∨
          (C_ROW + 120 * p + 32 ≤ q ∧ q < C_ROW + 120 * p + 88) ∨
          C_ROW + 120 * p + 120 ≤ q) →
        se.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hCM : C_MSG = 4096 := rfl
  have hCT : C_TD = 4294971424 := rfl
  have hCR : C_ROW = 5368713248 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  have hind : ∀ k (hk : k ≤ 1024),
      ∃ sk,
        DetRun oracle (submission.image .commit) sc (6 * k) sk (20 * k) (2 * k) ∧
        sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (16433 + 6 * k)) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sk.getReg reg = sc.getReg reg) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (1024 * chunkIdx + k) - 256) ∧
        sk.getReg .x12 = BitVec.ofNat 64 (C_ROW + 120 * (1024 * chunkIdx + k) - 32) ∧
        (∀ j (hj : j < k),
          let p := 1024 * chunkIdx + j
          readBuffer sk (C_ROW + 120 * p) 32 = leafA c64 p200 (msg ⟨2 * p, by omega⟩) ∧
          readBuffer sk (C_ROW + 120 * p + 88) 32 = leafA c64 p200 (msg ⟨2 * p + 1, by omega⟩)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ j < k,
            let p := 1024 * chunkIdx + j
            q < C_ROW + 120 * p ∨
            (C_ROW + 120 * p + 32 ≤ q ∧ q < C_ROW + 120 * p + 88) ∨
            C_ROW + 120 * p + 120 ≤ q) →
          sk.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩
    | succ k ih =>
      obtain ⟨sk, hrun_k, hpck, hregk, hx10k, hx12k, hresk, hpresk⟩ := ih (by omega)
      have hsrcE : readBuffer sk (C_MSG + 256 * (2 * (1024 * chunkIdx + k))) 64 =
          leafC2Input (oracle.permutation (leafP1Input
            (c64 (leafC0Input (msg ⟨2 * (1024 * chunkIdx + k), by omega⟩)))
            (msg ⟨2 * (1024 * chunkIdx + k), by omega⟩)))
            (msg ⟨2 * (1024 * chunkIdx + k), by omega⟩) :=
        (readBuffer_congr sk sc _ 64 (fun b hb => hpresk _ (by omega) (fun j _ => by omega))).trans
          (hsrc_all ⟨2 * (1024 * chunkIdx + k), by omega⟩)
      have hsrcO : readBuffer sk (C_MSG + 256 * (2 * (1024 * chunkIdx + k) + 1)) 64 =
          leafC2Input (oracle.permutation (leafP1Input
            (c64 (leafC0Input (msg ⟨2 * (1024 * chunkIdx + k) + 1, by omega⟩)))
            (msg ⟨2 * (1024 * chunkIdx + k) + 1, by omega⟩)))
            (msg ⟨2 * (1024 * chunkIdx + k) + 1, by omega⟩) :=
        (readBuffer_congr sk sc _ 64 (fun b hb => hpresk _ (by omega) (fun j _ => by omega))).trans
          (hsrc_all ⟨2 * (1024 * chunkIdx + k) + 1, by omega⟩)
      obtain ⟨s', hstep, hpc', hreg', hx10', hx12', haE', haO', hpres'⟩ :=
        c_p1c_pair_step h512 oracle msg sk k (1024 * chunkIdx + k) (by omega) (by omega)
          hpck ((hregk .x5 (by decide) (by decide)).trans hx5) hx10k
          ((hregk .x11 (by decide) (by decide)).trans hx11) hx12k
          ((hregk .x13 (by decide) (by decide)).trans hx13) hsrcE hsrcO
      refine ⟨s', by simpa [Nat.mul_succ, Nat.add_assoc] using hrun_k.trans hstep, hpc',
        fun reg h10 h12 => (hreg' reg h10 h12).trans (hregk reg h10 h12),
        by simpa only [Nat.add_assoc] using hx10',
        by simpa only [Nat.add_assoc] using hx12', ?_, ?_⟩
      · intro j hj
        by_cases hjk : j < k
        · obtain ⟨hE, hO⟩ := hresk j hjk
          exact ⟨(readBuffer_congr s' sk _ 32 (fun b hb => hpres' _ (by omega) (by omega))).trans hE,
                 (readBuffer_congr s' sk _ 32 (fun b hb => hpres' _ (by omega) (by omega))).trans hO⟩
        · have heqj : j = k := by omega
          subst heqj; exact ⟨haE', haO'⟩
      · intro q hq hout
        exact (hpres' q hq (hout k (by omega))).trans (hpresk q hq (fun j hj => hout j (by omega)))
  simpa only [show 1024 * (chunkIdx + 1) = 1024 * chunkIdx + 1024 by omega] using hind 1024 (le_refl _)

private theorem c_p1c_latch_back (oracle : Oracle) (chunkIdx : Nat) (hchunk : chunkIdx < 8191)
    (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 22577))
    (hx10 : se.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (1024 * (chunkIdx + 1)) - 256))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256)) :
    let sb := execInstrBr (execInstrBr se (.BEQ .x10 .x19 (8#13))) (.JAL .x0 (2072572#21))
    DetRun oracle (submission.image .commit) se 2 sb 2 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 16433) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  have hCM : C_MSG = 4096 := rfl
  let s1 := execInstrBr se (.BEQ .x10 .x19 (8#13))
  let s2 := execInstrBr s1 (.JAL .x0 (2072572#21))
  have hst1 : DetRun oracle (submission.image .commit) se 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1CInstr se 22577 (by omega) (by omega) hpc) rfl
  have hne : (se.getReg .x10 == se.getReg .x19) = false := by
    rw [hx10, hx19, beq_eq_false_iff_ne]
    exact c_bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 22578) := by
    simp only [s1, execInstrBr, hne, Bool.false_eq_true, ite_false, c_pc_setPC]
    exact c_pc_step_idx se 22577 hpc
  have hst2 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1CInstr s1 22578 (by omega) (by omega) hs1_pc) rfl
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 16433) := by
    simp only [s2, execInstrBr, c_pc_setPC, hs1_pc]
    exact c_pc_jal_22578
  exact ⟨hst1.trans hst2, hs2_pc,
    (c_mem_exec_JAL s1 _ _).trans (c_mem_exec_BEQ se _ _ _),
    fun reg => (c_reg_exec_JAL0 s1 _ reg).trans (c_reg_exec_BEQ se _ _ _ reg)⟩

private theorem c_p1c_latch_exit (oracle : Oracle) (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 22577))
    (hx10 : se.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (1024 * 8192) - 256))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256)) :
    let sb := execInstrBr se (.BEQ .x10 .x19 (8#13))
    DetRun oracle (submission.image .commit) se 1 sb 1 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 22579) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  let sb := execInstrBr se (.BEQ .x10 .x19 (8#13))
  have hst : DetRun oracle (submission.image .commit) se 1 sb 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1CInstr se 22577 (by omega) (by omega) hpc) rfl
  have heq : (se.getReg .x10 == se.getReg .x19) = true := by
    rw [hx10, hx19]; exact beq_self_eq_true _
  have hpc' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 22579) := by
    simp only [sb, execInstrBr, heq, ite_true, c_pc_setPC, hpc]
    exact c_pc_beq_22577
  exact ⟨hst, hpc', c_mem_exec_BEQ se _ _ _, c_reg_exec_BEQ se _ _ _⟩

/-- Full Phase 1C (`C2`, words `16433..22591`): `50,348,044` steps, `167,788,556` cycles,
`16,777,216` compression calls. Writes `a_{2p}, a_{2p+1}` into `C_ROW`, leaving gaps and salts intact. -/
theorem commit_phase1C (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 16433))
    (hx5 : s0.getReg .x5 = 0#64)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 (C_MSG - 256))
    (hx11 : s0.getReg .x11 = 64#64)
    (hx12 : s0.getReg .x12 = BitVec.ofNat 64 (C_ROW - 32))
    (hx13 : s0.getReg .x13 = 0#64)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx19 : s0.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hc2 : ∀ i : Index,
      readBuffer s0 (C_MSG + 256 * i.val) 64 =
        leafC2Input (oracle.permutation (leafP1Input
          (oracle.compression ((leafC0Input (msg i)).cast h512.symm)) (msg i))) (msg i)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 50348044 s1 167788556 16777216 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 22592) ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x10 = BitVec.ofNat 64 (C_ROW - 64) ∧
      s1.getReg .x11 = 64#64 ∧
      s1.getReg .x12 = BitVec.ofNat 64 (C_TD + 536870912 - 32) ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
      s1.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes - 64) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ p : Fin (LENGTH / 2),
        readBuffer s1 (C_ROW + 120 * p.val) 32 =
          leafA c64 p200 (msg ⟨2 * p.val, by have := p.isLt; unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
        readBuffer s1 (C_ROW + 120 * p.val + 88) 32 =
          leafA c64 p200 (msg ⟨2 * p.val + 1, by have := p.isLt; unfold LENGTH LOG_LENGTH at *; omega⟩)) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (∀ p < LENGTH / 2,
          q < C_ROW + 120 * p ∨
          (C_ROW + 120 * p + 32 ≤ q ∧ q < C_ROW + 120 * p + 88) ∨
          C_ROW + 120 * p + 120 ≤ q) →
        s1.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hCM : C_MSG = 4096 := rfl
  have hCT : C_TD = 4294971424 := rfl
  have hCR : C_ROW = 5368713248 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  have hind : ∀ n (hn : n ≤ 8191),
      ∃ sn,
        DetRun oracle (submission.image .commit) s0 (6146 * n) sn (20482 * n) (2048 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 16433) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sn.getReg reg = s0.getReg reg) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_MSG + 512 * (1024 * n) - 256) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_ROW + 120 * (1024 * n) - 32) ∧
        (∀ p (hp : p < 1024 * n),
          readBuffer sn (C_ROW + 120 * p) 32 = leafA c64 p200 (msg ⟨2 * p, by omega⟩) ∧
          readBuffer sn (C_ROW + 120 * p + 88) 32 = leafA c64 p200 (msg ⟨2 * p + 1, by omega⟩)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ p < 1024 * n,
            q < C_ROW + 120 * p ∨
            (C_ROW + 120 * p + 32 ≤ q ∧ q < C_ROW + 120 * p + 88) ∨
            C_ROW + 120 * p + 120 ≤ q) →
          sn.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨s0, DetRun.refl _ _ _, hpc, fun _ _ _ => rfl, by simpa using hx10, by simpa using hx12,
        fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩
    | succ n ih =>
      obtain ⟨sn, hrun_n, hpcn, hregn, hx10n, hx12n, hresn, hpresn⟩ := ih (by omega)
      have hsrc : ∀ i : Index,
          readBuffer sn (C_MSG + 256 * i.val) 64 =
            leafC2Input (oracle.permutation (leafP1Input
              (c64 (leafC0Input (msg i))) (msg i))) (msg i) := by
        intro i; have hi := i.isLt
        exact (readBuffer_congr sn s0 _ 64 (fun b hb => hpresn _ (by omega) (fun p _ => by omega))).trans (hc2 i)
      obtain ⟨se, hbody, hpce, hrege, hx10e, hx12e, hrese, hprese⟩ :=
        c_p1c_chunk_body h512 oracle msg sn n (by omega) hpcn
          ((hregn .x5 (by decide) (by decide)).trans hx5) hx10n
          ((hregn .x11 (by decide) (by decide)).trans hx11) hx12n
          ((hregn .x13 (by decide) (by decide)).trans hx13) hsrc
      obtain ⟨hlatch, hpc_b, hmem_b, hreg_b⟩ :=
        c_p1c_latch_back oracle n (by omega) se hpce hx10e
          ((hrege .x19 (by decide) (by decide)).trans ((hregn .x19 (by decide) (by decide)).trans hx19))
      refine ⟨_, by simpa [Nat.mul_succ, Nat.add_assoc] using (hrun_n.trans hbody).trans hlatch,
        hpc_b, fun reg h10 h12 => (hreg_b reg).trans ((hrege reg h10 h12).trans (hregn reg h10 h12)),
        (hreg_b .x10).trans hx10e, (hreg_b .x12).trans hx12e, ?_, ?_⟩
      · intro p hp
        rw [c_readBuffer_of_mem_eq hmem_b, c_readBuffer_of_mem_eq hmem_b]
        by_cases hlt : p < 1024 * n
        · obtain ⟨hE, hO⟩ := hresn p hlt
          exact ⟨(readBuffer_congr se sn _ 32 (fun b hb => hprese _ (by omega) (fun j _ => by omega))).trans hE,
                 (readBuffer_congr se sn _ 32 (fun b hb => hprese _ (by omega) (fun j _ => by omega))).trans hO⟩
        · have hj : p - 1024 * n < 1024 := by omega
          have heq : 1024 * n + (p - 1024 * n) = p := by omega
          simpa only [heq] using hrese (p - 1024 * n) hj
      · intro q hq hout
        rw [c_getByte_of_mem_eq hmem_b]
        exact (hprese q hq (fun j hj => hout (1024 * n + j) (by omega))).trans
          (hpresn q hq (fun p hp => hout p (by omega)))
  obtain ⟨sp, hrun_p, hpcp, hregp, hx10p, hx12p, hresp, hpresp⟩ := hind 8191 (le_refl _)
  have hsrc_last : ∀ i : Index,
      readBuffer sp (C_MSG + 256 * i.val) 64 =
        leafC2Input (oracle.permutation (leafP1Input
          (c64 (leafC0Input (msg i))) (msg i))) (msg i) := by
    intro i; have hi := i.isLt
    exact (readBuffer_congr sp s0 _ 64 (fun b hb => hpresp _ (by omega) (fun p _ => by omega))).trans (hc2 i)
  obtain ⟨se, hbody, hpce, hrege, hx10e, _, hrese, hprese⟩ :=
    c_p1c_chunk_body h512 oracle msg sp 8191 (by omega) hpcp
      ((hregp .x5 (by decide) (by decide)).trans hx5) hx10p
      ((hregp .x11 (by decide) (by decide)).trans hx11) hx12p
      ((hregp .x13 (by decide) (by decide)).trans hx13) hsrc_last
  obtain ⟨hlatch, hpc_l, hmem_l, hreg_l⟩ :=
    c_p1c_latch_exit oracle se hpce hx10e
      ((hrege .x19 (by decide) (by decide)).trans ((hregp .x19 (by decide) (by decide)).trans hx19))
  let sLoop := execInstrBr se (.BEQ .x10 .x19 (8#13))
  let sFin := c_mid1CInstrs.foldl execInstrBr sLoop
  have hmid_run := c_mid1C_run oracle sLoop hpc_l
  obtain ⟨hpc_f, hmem_f, hx5_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx18_f, hx19_f, hx26_f⟩ :=
    c_mid1C_spec sLoop hpc_l
      ((hreg_l .x5).trans ((hrege .x5 (by decide) (by decide)).trans ((hregp .x5 (by decide) (by decide)).trans hx5)))
      ((hreg_l .x9).trans ((hrege .x9 (by decide) (by decide)).trans ((hregp .x9 (by decide) (by decide)).trans hx9)))
      ((hreg_l .x11).trans ((hrege .x11 (by decide) (by decide)).trans ((hregp .x11 (by decide) (by decide)).trans hx11)))
      ((hreg_l .x13).trans ((hrege .x13 (by decide) (by decide)).trans ((hregp .x13 (by decide) (by decide)).trans hx13)))
      ((hreg_l .x18).trans ((hrege .x18 (by decide) (by decide)).trans ((hregp .x18 (by decide) (by decide)).trans hx18)))
      ((hreg_l .x26).trans ((hrege .x26 (by decide) (by decide)).trans ((hregp .x26 (by decide) (by decide)).trans hx26)))
  refine ⟨sFin,
    by simpa only [show 6146 * 8191 + 6144 + 1 + 13 = 50348044 by decide,
      show 20482 * 8191 + 20480 + 1 + 13 = 167788556 by decide,
      show 2048 * 8191 + 2048 + 0 + 0 = 16777216 by decide] using
      (((hrun_p.trans hbody).trans hlatch).trans hmid_run),
    hpc_f, hx5_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx18_f, hx19_f, hx26_f, ?_, ?_⟩
  · intro ⟨p, hp⟩
    dsimp only
    rw [c_readBuffer_of_mem_eq hmem_f, c_readBuffer_of_mem_eq hmem_l,
        c_readBuffer_of_mem_eq hmem_f, c_readBuffer_of_mem_eq hmem_l]
    by_cases hlt : p < 1024 * 8191
    · obtain ⟨hE, hO⟩ := hresp p hlt
      exact ⟨(readBuffer_congr se sp _ 32 (fun b hb => hprese _ (by omega) (fun j _ => by omega))).trans hE,
             (readBuffer_congr se sp _ 32 (fun b hb => hprese _ (by omega) (fun j _ => by omega))).trans hO⟩
    · have hj : p - 1024 * 8191 < 1024 := by omega
      have heq : 1024 * 8191 + (p - 1024 * 8191) = p := by omega
      simpa only [heq] using hrese (p - 1024 * 8191) hj
  · intro q hq hout
    rw [c_getByte_of_mem_eq hmem_f, c_getByte_of_mem_eq hmem_l]
    exact (hprese q hq (fun j hj => hout (1024 * 8191 + j) (by omega))).trans
      (hpresp q hq (fun p hp => hout p (by omega)))

/-! ### 2. Phase 1D (`C3` / SM-PLS-40: words `22592..28746`) -/

private theorem c_pc_beq_28736 :
    BitVec.ofNat 64 (0x1000 + 4 * 28736) + signExtend13 (8#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 28738) := by decide

private theorem c_pc_jal_28737 :
    BitVec.ofNat 64 (0x1000 + 4 * 28737) + signExtend21 (2072572#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 22592) := by decide

private def c_mid1DInstrs : List Instr :=
  [.ADDI .x6 .x0 (1#12), .SLLI .x6 .x6 (30#6), .ADD .x10 .x9 .x6,
   .ADDI .x6 .x0 (1#12), .SLLI .x6 .x6 (29#6), .ADD .x12 .x9 .x6,
   .ADDI .x6 .x0 (1#12), .SLLI .x6 .x6 (28#6), .ADD .x19 .x9 .x6]

private theorem c_mid1D_run (oracle : Oracle) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 28738)) :
    DetRun oracle (submission.image .commit) s 9 (c_mid1DInstrs.foldl execInstrBr s) 9 0 := by
  have hall : ∀ ins ∈ c_mid1DInstrs, c_isPureAlu ins = true := by decide
  apply c_exec_alu_list c_mid1DInstrs s
  intro i hi
  have hi' : i < 9 := hi
  have hpc_i : ((c_mid1DInstrs.take i).foldl execInstrBr s).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (28738 + i)) := by
    have h := c_foldl_pureAlu_pc (c_mid1DInstrs.take i) s (0x1000 + 4 * 28738)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitMid1DInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem c_mid1D_spec (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 28738))
    (hx5 : s.getReg .x5 = 0#64)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s.getReg .x11 = 64#64)
    (hx13 : s.getReg .x13 = 0#64)
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s' := c_mid1DInstrs.foldl execInstrBr s
    s'.pc = BitVec.ofNat 64 (0x1000 + 4 * 28747) ∧
    s'.mem = s.mem ∧
    s'.getReg .x5 = 0#64 ∧
    s'.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s'.getReg .x10 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 25) ∧
    s'.getReg .x11 = 64#64 ∧
    s'.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 24) ∧
    s'.getReg .x13 = 0#64 ∧
    s'.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 23) ∧
    s'.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ c_mid1DInstrs, c_isPureAlu ins = true := by decide
  refine ⟨?_, c_foldl_pureAlu_mem c_mid1DInstrs s hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (c_foldl_pureAlu_pc c_mid1DInstrs s (0x1000 + 4 * 28738) hall hpc).trans (by decide)
  all_goals (
    simp only [c_mid1DInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx5, hx9, hx11, hx13, hx26]
    try decide)

/-- One `c3Pair` pair step (2 leaves): 6 steps, 20 cycles, 2 compression calls. -/
private theorem c_p1d_pair_step (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (rand : Fin (LENGTH / 2) → PairRand) (s : MachineState)
    (k pairIdx : Nat) (hk : k < 1024) (hpair : pairIdx < LENGTH / 2)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (22592 + 6 * k)))
    (hx5 : s.getReg .x5 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx - 64))
    (hx11 : s.getReg .x11 = 64#64)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 2 * pairIdx) - 32))
    (hx13 : s.getReg .x13 = 0#64)
    (haE : readBuffer s (C_ROW + 120 * pairIdx) 32 =
      leafA (fun x => oracle.compression (x.cast h512.symm)) (fun x => oracle.permutation x)
        (msg ⟨2 * pairIdx, by unfold LENGTH LOG_LENGTH at *; omega⟩))
    (haO : readBuffer s (C_ROW + 120 * pairIdx + 88) 32 =
      leafA (fun x => oracle.compression (x.cast h512.symm)) (fun x => oracle.permutation x)
        (msg ⟨2 * pairIdx + 1, by unfold LENGTH LOG_LENGTH at *; omega⟩))
    (hgapE : readBuffer s (C_ROW + 120 * pairIdx + 32) 8 = 0)
    (hgapO : readBuffer s (C_ROW + 120 * pairIdx + 80) 8 = 0)
    (hsaltE : readBuffer s (C_ROW + 120 * pairIdx + 40) 24 = pairSaltEven (rand ⟨pairIdx, hpair⟩))
    (hsaltO : readBuffer s (C_ROW + 120 * pairIdx + 56) 24 = pairSaltOdd (rand ⟨pairIdx, hpair⟩)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ s',
      DetRun oracle (submission.image .commit) s 6 s' 20 2 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (22592 + 6 * (k + 1))) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s'.getReg reg = s.getReg reg) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (pairIdx + 1) - 64) ∧
      s'.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 2 * (pairIdx + 1)) - 32) ∧
      readBuffer s' (C_TD + 32 * (LENGTH + 2 * pairIdx)) 32 =
        nodeVal c64 p200 msg (pairSalts rand) 0 (2 * pairIdx) ∧
      readBuffer s' (C_TD + 32 * (LENGTH + 2 * pairIdx + 1)) 32 =
        nodeVal c64 p200 msg (pairSalts rand) 0 (2 * pairIdx + 1) ∧
      CommitMemOutside s s' (C_TD + 32 * (LENGTH + 2 * pairIdx)) (C_TD + 32 * (LENGTH + 2 * pairIdx + 2)) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hCM : C_MSG = 4096 := rfl
  have hCT : C_TD = 4294971424 := rfl
  have hCR : C_ROW = 5368713248 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  let dE := nodeVal c64 p200 msg (pairSalts rand) 0 (2 * pairIdx)
  let dO := nodeVal c64 p200 msg (pairSalts rand) 0 (2 * pairIdx + 1)
  have hdE_eq : c64 (leafFinalEven (leafA c64 p200 (msg ⟨2 * pairIdx, by omega⟩))
      (pairSaltEven (rand ⟨pairIdx, hpair⟩))) = dE := by
    have hlt : 2 * pairIdx < LENGTH := by omega
    unfold dE nodeVal nodeValFromLeaves leafDigest leafFinalInput pairSalts
    simp only [hlt, dite_true, show 2 * pairIdx % 2 = 0 by omega, ite_true,
      show 2 * pairIdx / 2 = pairIdx by omega]
  have hdO_eq : c64 (leafFinalOdd (leafA c64 p200 (msg ⟨2 * pairIdx + 1, by omega⟩))
      (pairSaltOdd (rand ⟨pairIdx, hpair⟩))) = dO := by
    have hlt : 2 * pairIdx + 1 < LENGTH := by omega
    unfold dO nodeVal nodeValFromLeaves leafDigest leafFinalInput pairSalts
    simp only [hlt, dite_true, show ¬ ((2 * pairIdx + 1) % 2 = 0) by omega, ite_false,
      show (2 * pairIdx + 1) / 2 = pairIdx by omega]
  -- Even leaf 2*pairIdx
  let s1 := execInstrBr s (.ADDI .x10 .x10 (64#12))
  let s2 := execInstrBr s1 (.ADDI .x12 .x12 (32#12))
  let s3 := writeBits s2 (BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 2 * pairIdx))) dE
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (22592 + 6 * k + 1)) := c_pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (22592 + 6 * k + 2)) := c_pc_step_idx s1 _ hs1_pc
  have hs1_x10 : s1.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      c_add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_x10 : s2.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx) := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne .x12 .x10 (by decide), hs1_x10]
  have hs2_x12 : s2.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 2 * pairIdx)) := by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      c_getReg_setReg_ne .x10 .x12 (by decide), hx12,
      c_add_signExtend12_ofNat_small _ 32 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs2_mem : s2.mem = s.mem := (c_mem_exec_ADDI s1 _ _ _).trans (c_mem_exec_ADDI s _ _ _)
  have hs2_reg : ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s2.getReg reg = s.getReg reg := fun reg h10 h12 => by
    simp only [s2, s1, execInstrBr, MachineState.getReg_setPC,
      c_getReg_setReg_ne .x12 reg (Ne.symm h12), c_getReg_setReg_ne .x10 reg (Ne.symm h10)]
  have hr0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_c3Pair s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc)) rfl
  have hr1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_c3Pair s1 k 1 hk (by omega) hs1_pc) rfl
  have hreadE : oracle.compression ((readBuffer s2 (C_ROW + 120 * pairIdx) 64).cast h512.symm) = dE := by
    rw [c_readBuffer_of_mem_eq hs2_mem, readBuffer_lateEven s (C_ROW + 120 * pairIdx) hgapE, haE, hsaltE]
    exact hdE_eq
  have hr2 : DetRun oracle (submission.image .commit) s2 1 s3 8 1 :=
    DetRun.compress_eq h512 (commit_fetch_c3Pair s2 k 2 hk (by omega) hs2_pc)
      ((hs2_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs2_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs2_reg .x13 (by decide) (by decide)).trans hx13)
      (C_ROW + 120 * pairIdx) (C_TD + 32 * (LENGTH + 2 * pairIdx))
      hs2_x10 hs2_x12 (by omega) (by omega) (by omega) (by omega) dE hreadE
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (22592 + 6 * k + 3)) := by
    rw [c_pc_writeBits, c_pc_step_idx s2 _ hs2_pc]
  have hpresE : CommitMemOutside s s3 (C_TD + 32 * (LENGTH + 2 * pairIdx)) (C_TD + 32 * (LENGTH + 2 * pairIdx + 1)) :=
    (CommitMemOutside.of_mem_eq hs2_mem _ _).trans
      (by simpa only [show C_TD + 32 * (LENGTH + 2 * pairIdx) + (256 + 7) / 8 =
          C_TD + 32 * (LENGTH + 2 * pairIdx + 1) by omega] using
        c_memPreserved_writeBits s2 (C_TD + 32 * (LENGTH + 2 * pairIdx)) dE (by omega))
  -- Odd leaf 2*pairIdx + 1
  let s4 := execInstrBr s3 (.ADDI .x10 .x10 (56#12))
  let s5 := execInstrBr s4 (.ADDI .x12 .x12 (32#12))
  let s6 := writeBits s5 (BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 2 * pairIdx + 1))) dO
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (22592 + 6 * k + 4)) := c_pc_step_idx s3 _ hs3_pc
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * (22592 + 6 * k + 5)) := c_pc_step_idx s4 _ hs4_pc
  have hs3_x10 : s3.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx) :=
    (writeBits_register s2 _ dE .x10).trans hs2_x10
  have hs3_x12 : s3.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 2 * pairIdx)) :=
    (writeBits_register s2 _ dE .x12).trans hs2_x12
  have hs4_x10 : s4.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx + 56) := by
    simp only [s4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs3_x10,
      c_add_signExtend12_ofNat_small _ 56 (by omega)]
  have hs5_x10 : s5.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx + 56) := by
    simp only [s5, execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne .x12 .x10 (by decide), hs4_x10]
  have hs5_x12 : s5.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 2 * pairIdx + 1)) := by
    simp only [s5, s4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0),
      c_getReg_setReg_ne .x10 .x12 (by decide), hs3_x12,
      c_add_signExtend12_ofNat_small _ 32 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs5_mem : s5.mem = s3.mem := (c_mem_exec_ADDI s4 _ _ _).trans (c_mem_exec_ADDI s3 _ _ _)
  have hs5_reg : ∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → s5.getReg reg = s.getReg reg := fun reg h10 h12 => by
    have h1 : s5.getReg reg = s3.getReg reg := by
      simp only [s5, s4, execInstrBr, MachineState.getReg_setPC,
        c_getReg_setReg_ne .x12 reg (Ne.symm h12), c_getReg_setReg_ne .x10 reg (Ne.symm h10)]
    exact h1.trans ((writeBits_register s2 _ dE reg).trans (hs2_reg reg h10 h12))
  have hr3 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (commit_fetch_c3Pair s3 k 3 hk (by omega) hs3_pc) rfl
  have hr4 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (commit_fetch_c3Pair s4 k 4 hk (by omega) hs4_pc) rfl
  have hreadO : oracle.compression ((readBuffer s5 (C_ROW + 120 * pairIdx + 56) 64).cast h512.symm) = dO := by
    rw [c_readBuffer_of_mem_eq hs5_mem, hpresE.readBuffer_eq (by omega) (by omega)]
    rw [readBuffer_lateOdd s (C_ROW + 120 * pairIdx + 56)
      (by simpa only [show C_ROW + 120 * pairIdx + 56 + 24 = C_ROW + 120 * pairIdx + 80 by omega] using hgapO),
      hsaltO,
      show C_ROW + 120 * pairIdx + 56 + 32 = C_ROW + 120 * pairIdx + 88 by omega, haO]
    exact hdO_eq
  have hr5 : DetRun oracle (submission.image .commit) s5 1 s6 8 1 :=
    DetRun.compress_eq h512 (commit_fetch_c3Pair s5 k 5 hk (by omega) hs5_pc)
      ((hs5_reg .x5 (by decide) (by decide)).trans hx5)
      ((hs5_reg .x11 (by decide) (by decide)).trans hx11)
      ((hs5_reg .x13 (by decide) (by decide)).trans hx13)
      (C_ROW + 120 * pairIdx + 56) (C_TD + 32 * (LENGTH + 2 * pairIdx + 1))
      hs5_x10 hs5_x12 (by omega) (by omega) (by omega) (by omega) dO hreadO
  have hpresO : CommitMemOutside s3 s6 (C_TD + 32 * (LENGTH + 2 * pairIdx + 1)) (C_TD + 32 * (LENGTH + 2 * pairIdx + 2)) :=
    (CommitMemOutside.of_mem_eq hs5_mem _ _).trans
      (by simpa only [show C_TD + 32 * (LENGTH + 2 * pairIdx + 1) + (256 + 7) / 8 =
          C_TD + 32 * (LENGTH + 2 * pairIdx + 2) by omega] using
        c_memPreserved_writeBits s5 (C_TD + 32 * (LENGTH + 2 * pairIdx + 1)) dO (by omega))
  refine ⟨s6, (((hr0.trans hr1).trans hr2).trans ((hr3.trans hr4).trans hr5)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [c_pc_writeBits, c_pc_step_idx s5 _ hs5_pc]; exact congrArg (BitVec.ofNat 64) (by omega)
  · intro reg h10 h12; exact (writeBits_register s5 _ dO reg).trans (hs5_reg reg h10 h12)
  · rw [writeBits_register s5 _ dO .x10, hs5_x10]; exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [writeBits_register s5 _ dO .x12, hs5_x12]; exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [hpresO.readBuffer_eq (by omega) (by omega)]; exact writeBits_readBuffer_digest s2 _ dE
  · exact writeBits_readBuffer_digest s5 _ dO
  · exact (hpresE.mono (le_refl _) (by omega)).trans (hpresO.mono (by omega) (le_refl _))

/-- One 1024-pair `c3Pair` chunk body (`22592..28735`): 6144 steps, 20480 cycles, 2048 calls. -/
private theorem c_p1d_chunk_body (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (rand : Fin (LENGTH / 2) → PairRand) (sc : MachineState)
    (chunkIdx : Nat) (hchunk : chunkIdx < 8192)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 22592))
    (hx5 : sc.getReg .x5 = 0#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (1024 * chunkIdx) - 64))
    (hx11 : sc.getReg .x11 = 64#64)
    (hx12 : sc.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 2 * (1024 * chunkIdx)) - 32))
    (hx13 : sc.getReg .x13 = 0#64)
    (hrow : ∀ p : Fin (LENGTH / 2),
      readBuffer sc (C_ROW + 120 * p.val) 32 =
        leafA (fun x => oracle.compression (x.cast h512.symm)) (fun x => oracle.permutation x)
          (msg ⟨2 * p.val, by have := p.isLt; unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer sc (C_ROW + 120 * p.val + 88) 32 =
        leafA (fun x => oracle.compression (x.cast h512.symm)) (fun x => oracle.permutation x)
          (msg ⟨2 * p.val + 1, by have := p.isLt; unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer sc (C_ROW + 120 * p.val + 32) 8 = 0 ∧
      readBuffer sc (C_ROW + 120 * p.val + 80) 8 = 0 ∧
      readBuffer sc (C_ROW + 120 * p.val + 40) 24 = pairSaltEven (rand p) ∧
      readBuffer sc (C_ROW + 120 * p.val + 56) 24 = pairSaltOdd (rand p)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ se,
      DetRun oracle (submission.image .commit) sc 6144 se 20480 2048 ∧
      se.pc = BitVec.ofNat 64 (0x1000 + 4 * 28736) ∧
      (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → se.getReg reg = sc.getReg reg) ∧
      se.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (1024 * (chunkIdx + 1)) - 64) ∧
      se.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 2 * (1024 * (chunkIdx + 1))) - 32) ∧
      (∀ j < 2048,
        readBuffer se (C_TD + 32 * (LENGTH + 2048 * chunkIdx + j)) 32 =
          nodeVal c64 p200 msg (pairSalts rand) 0 (2048 * chunkIdx + j)) ∧
      CommitMemOutside sc se
        (C_TD + 32 * (LENGTH + 2048 * chunkIdx))
        (C_TD + 32 * (LENGTH + 2048 * (chunkIdx + 1))) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hCT : C_TD = 4294971424 := rfl
  have hCR : C_ROW = 5368713248 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  have hind : ∀ k ≤ 1024,
      ∃ sk,
        DetRun oracle (submission.image .commit) sc (6 * k) sk (20 * k) (2 * k) ∧
        sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (22592 + 6 * k)) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sk.getReg reg = sc.getReg reg) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (1024 * chunkIdx + k) - 64) ∧
        sk.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 2 * (1024 * chunkIdx + k)) - 32) ∧
        (∀ j < 2 * k,
          readBuffer sk (C_TD + 32 * (LENGTH + 2048 * chunkIdx + j)) 32 =
            nodeVal c64 p200 msg (pairSalts rand) 0 (2048 * chunkIdx + j)) ∧
        CommitMemOutside sc sk
          (C_TD + 32 * (LENGTH + 2048 * chunkIdx))
          (C_TD + 32 * (LENGTH + 2048 * chunkIdx + 2 * k)) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ => rfl,
        by simpa using hx10, by simpa using hx12,
        fun _ h => (Nat.not_lt_zero _ h).elim, CommitMemOutside.refl _ _ _⟩
    | succ k ih =>
      obtain ⟨sk, hrun_k, hpck, hregk, hx10k, hx12k, hresk, hpresk⟩ := ih (by omega)
      let pFin : Fin (LENGTH / 2) := ⟨1024 * chunkIdx + k, by omega⟩
      obtain ⟨haE, haO, hgapE, hgapO, hsaltE, hsaltO⟩ := hrow pFin
      have hpres_row : ∀ addr len, C_ROW ≤ addr → addr + len ≤ 2 ^ 64 →
          readBuffer sk addr len = readBuffer sc addr len :=
        fun addr len hlo hbd => hpresk.readBuffer_eq hbd (by omega)
      obtain ⟨s', hstep, hpc', hreg', hx10', hx12', hdE', hdO', hpres'⟩ :=
        c_p1d_pair_step h512 oracle msg rand sk k (1024 * chunkIdx + k) (by omega) (by omega)
          hpck ((hregk .x5 (by decide) (by decide)).trans hx5) hx10k
          ((hregk .x11 (by decide) (by decide)).trans hx11) hx12k
          ((hregk .x13 (by decide) (by decide)).trans hx13)
          ((hpres_row _ 32 (by omega) (by omega)).trans haE)
          ((hpres_row _ 32 (by omega) (by omega)).trans haO)
          ((hpres_row _ 8 (by omega) (by omega)).trans hgapE)
          ((hpres_row _ 8 (by omega) (by omega)).trans hgapO)
          ((hpres_row _ 24 (by omega) (by omega)).trans hsaltE)
          ((hpres_row _ 24 (by omega) (by omega)).trans hsaltO)
      refine ⟨s', by simpa [Nat.mul_succ, Nat.add_assoc] using hrun_k.trans hstep, hpc',
        fun reg h10 h12 => (hreg' reg h10 h12).trans (hregk reg h10 h12),
        by simpa only [Nat.add_assoc] using hx10',
        by simpa only [Nat.add_assoc] using hx12', ?_, ?_⟩
      · intro j hj
        by_cases hjk : j < 2 * k
        · exact (hpres'.readBuffer_eq (by omega) (by omega)).trans (hresk j hjk)
        · by_cases he : j = 2 * k
          · subst he
            simpa only [show LENGTH + 2048 * chunkIdx + 2 * k = LENGTH + 2 * (1024 * chunkIdx + k) by omega,
              show 2048 * chunkIdx + 2 * k = 2 * (1024 * chunkIdx + k) by omega] using hdE'
          · have ho : j = 2 * k + 1 := by omega
            subst ho
            simpa only [show LENGTH + 2048 * chunkIdx + (2 * k + 1) = LENGTH + 2 * (1024 * chunkIdx + k) + 1 by omega,
              show 2048 * chunkIdx + (2 * k + 1) = 2 * (1024 * chunkIdx + k) + 1 by omega] using hdO'
      · exact (hpresk.mono (le_refl _) (hi' := C_TD + 32 * (LENGTH + 2048 * chunkIdx + 2 * (k + 1))) (by omega)).trans
          (hpres'.mono (lo' := C_TD + 32 * (LENGTH + 2048 * chunkIdx))
            (hi' := C_TD + 32 * (LENGTH + 2048 * chunkIdx + 2 * (k + 1))) (by omega) (by omega))
  simpa only [show 1024 * (chunkIdx + 1) = 1024 * chunkIdx + 1024 by omega,
    show 2048 * (chunkIdx + 1) = 2048 * chunkIdx + 2 * 1024 by omega, Nat.add_assoc] using hind 1024 (le_refl _)

private theorem c_p1d_latch_back (oracle : Oracle) (chunkIdx : Nat) (hchunk : chunkIdx < 8191)
    (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 28736))
    (hx10 : se.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (1024 * (chunkIdx + 1)) - 64))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes - 64)) :
    let sb := execInstrBr (execInstrBr se (.BEQ .x10 .x19 (8#13))) (.JAL .x0 (2072572#21))
    DetRun oracle (submission.image .commit) se 2 sb 2 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 22592) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  have hrb := rowBytes_eq
  have hCR : C_ROW = 5368713248 := rfl
  let s1 := execInstrBr se (.BEQ .x10 .x19 (8#13))
  let s2 := execInstrBr s1 (.JAL .x0 (2072572#21))
  have hst1 : DetRun oracle (submission.image .commit) se 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1DInstr se 28736 (by omega) (by omega) hpc) rfl
  have hne : (se.getReg .x10 == se.getReg .x19) = false := by
    rw [hx10, hx19, hrb, beq_eq_false_iff_ne]
    exact c_bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 28737) := by
    simp only [s1, execInstrBr, hne, Bool.false_eq_true, ite_false, c_pc_setPC]
    exact c_pc_step_idx se 28736 hpc
  have hst2 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1DInstr s1 28737 (by omega) (by omega) hs1_pc) rfl
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 22592) := by
    simp only [s2, execInstrBr, c_pc_setPC, hs1_pc]
    exact c_pc_jal_28737
  exact ⟨hst1.trans hst2, hs2_pc,
    (c_mem_exec_JAL s1 _ _).trans (c_mem_exec_BEQ se _ _ _),
    fun reg => (c_reg_exec_JAL0 s1 _ reg).trans (c_reg_exec_BEQ se _ _ _ reg)⟩

private theorem c_p1d_latch_exit (oracle : Oracle) (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 28736))
    (hx10 : se.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (1024 * 8192) - 64))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes - 64)) :
    let sb := execInstrBr se (.BEQ .x10 .x19 (8#13))
    DetRun oracle (submission.image .commit) se 1 sb 1 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 28738) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  have hrb := rowBytes_eq
  let sb := execInstrBr se (.BEQ .x10 .x19 (8#13))
  have hst : DetRun oracle (submission.image .commit) se 1 sb 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1DInstr se 28736 (by omega) (by omega) hpc) rfl
  have heq : (se.getReg .x10 == se.getReg .x19) = true := by
    rw [hx10, hx19, hrb]; exact beq_self_eq_true _
  have hpc' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 28738) := by
    simp only [sb, execInstrBr, heq, ite_true, c_pc_setPC, hpc]
    exact c_pc_beq_28736
  exact ⟨hst, hpc', c_mem_exec_BEQ se _ _ _, c_reg_exec_BEQ se _ _ _⟩

/-- Full Phase 1D (`C3`, words `22592..28746`): `50,348,040` steps, `167,788,552` cycles,
`16,777,216` compression calls. Populates all `L0` heap leaves `C_TD + 32 * (2^24 + idx)`
and preserves everything outside `[C_TD + 32 * 2^24, C_ROW)`. -/
theorem commit_phase1D (h512 : COMPRESSION_INPUT_LENGTH = 512)
    (oracle : Oracle) (msg : Message) (rand : Fin (LENGTH / 2) → PairRand) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 22592))
    (hx5 : s0.getReg .x5 = 0#64)
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 (C_ROW - 64))
    (hx11 : s0.getReg .x11 = 64#64)
    (hx12 : s0.getReg .x12 = BitVec.ofNat 64 (C_TD + 536870912 - 32))
    (hx13 : s0.getReg .x13 = 0#64)
    (hx19 : s0.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes - 64))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hrow : ∀ p : Fin (LENGTH / 2),
      readBuffer s0 (C_ROW + 120 * p.val) 32 =
        leafA (fun x => oracle.compression (x.cast h512.symm)) (fun x => oracle.permutation x)
          (msg ⟨2 * p.val, by have := p.isLt; unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer s0 (C_ROW + 120 * p.val + 88) 32 =
        leafA (fun x => oracle.compression (x.cast h512.symm)) (fun x => oracle.permutation x)
          (msg ⟨2 * p.val + 1, by have := p.isLt; unfold LENGTH LOG_LENGTH at *; omega⟩) ∧
      readBuffer s0 (C_ROW + 120 * p.val + 32) 8 = 0 ∧
      readBuffer s0 (C_ROW + 120 * p.val + 80) 8 = 0 ∧
      readBuffer s0 (C_ROW + 120 * p.val + 40) 24 = pairSaltEven (rand p) ∧
      readBuffer s0 (C_ROW + 120 * p.val + 56) 24 = pairSaltOdd (rand p)) :
    let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
    let p200 : Perm200 := fun x => oracle.permutation x
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 50348040 s1 167788552 16777216 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 28747) ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x10 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 25) ∧
      s1.getReg .x11 = 64#64 ∧
      s1.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 24) ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x19 = BitVec.ofNat 64 (C_TD + 32 * 2 ^ 23) ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ idx < levelSize 0,
        readBuffer s1 (C_TD + 32 * heapIdx 0 idx) 32 =
          nodeVal c64 p200 msg (pairSalts rand) 0 idx) ∧
      CommitMemOutside s0 s1 (C_TD + 32 * 2 ^ 24) C_ROW := by
  have hLEN : LENGTH = 16777216 := rfl
  have hHLEN : LENGTH / 2 = 8388608 := by decide
  have hCT : C_TD = 4294971424 := rfl
  have hCR : C_ROW = 5368713248 := rfl
  let c64 : Comp64 := fun x => oracle.compression (x.cast h512.symm)
  let p200 : Perm200 := fun x => oracle.permutation x
  have hind : ∀ n ≤ 8191,
      ∃ sn,
        DetRun oracle (submission.image .commit) s0 (6146 * n) sn (20482 * n) (2048 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 22592) ∧
        (∀ reg : Reg, reg ≠ .x10 → reg ≠ .x12 → sn.getReg reg = s0.getReg reg) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (1024 * n) - 64) ∧
        sn.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * (LENGTH + 2 * (1024 * n)) - 32) ∧
        (∀ idx < 2048 * n,
          readBuffer sn (C_TD + 32 * (LENGTH + idx)) 32 =
            nodeVal c64 p200 msg (pairSalts rand) 0 idx) ∧
        CommitMemOutside s0 sn (C_TD + 32 * 2 ^ 24) (C_TD + 32 * (2 ^ 24 + 2048 * n)) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨s0, DetRun.refl _ _ _, hpc, fun _ _ _ => rfl, by simpa using hx10,
        by simpa only [Nat.mul_zero, Nat.add_zero, hLEN] using hx12,
        fun _ h => (Nat.not_lt_zero _ h).elim, CommitMemOutside.refl _ _ _⟩
    | succ n ih =>
      obtain ⟨sn, hrun_n, hpcn, hregn, hx10n, hx12n, hresn, hpresn⟩ := ih (by omega)
      have hrow_n : ∀ p : Fin (LENGTH / 2),
          readBuffer sn (C_ROW + 120 * p.val) 32 = leafA c64 p200 (msg ⟨2 * p.val, by have := p.isLt; omega⟩) ∧
          readBuffer sn (C_ROW + 120 * p.val + 88) 32 = leafA c64 p200 (msg ⟨2 * p.val + 1, by have := p.isLt; omega⟩) ∧
          readBuffer sn (C_ROW + 120 * p.val + 32) 8 = 0 ∧
          readBuffer sn (C_ROW + 120 * p.val + 80) 8 = 0 ∧
          readBuffer sn (C_ROW + 120 * p.val + 40) 24 = pairSaltEven (rand p) ∧
          readBuffer sn (C_ROW + 120 * p.val + 56) 24 = pairSaltOdd (rand p) := by
        intro p; have hp := p.isLt
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrow p
        exact ⟨(hpresn.readBuffer_eq (by omega) (by omega)).trans h1,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans h2,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans h3,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans h4,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans h5,
               (hpresn.readBuffer_eq (by omega) (by omega)).trans h6⟩
      obtain ⟨se, hbody, hpce, hrege, hx10e, hx12e, hrese, hprese⟩ :=
        c_p1d_chunk_body h512 oracle msg rand sn n (by omega) hpcn
          ((hregn .x5 (by decide) (by decide)).trans hx5) hx10n
          ((hregn .x11 (by decide) (by decide)).trans hx11) hx12n
          ((hregn .x13 (by decide) (by decide)).trans hx13) hrow_n
      obtain ⟨hlatch, hpc_b, hmem_b, hreg_b⟩ :=
        c_p1d_latch_back oracle n (by omega) se hpce hx10e
          ((hrege .x19 (by decide) (by decide)).trans ((hregn .x19 (by decide) (by decide)).trans hx19))
      refine ⟨_, by simpa [Nat.mul_succ, Nat.add_assoc] using (hrun_n.trans hbody).trans hlatch,
        hpc_b, fun reg h10 h12 => (hreg_b reg).trans ((hrege reg h10 h12).trans (hregn reg h10 h12)),
        (hreg_b .x10).trans hx10e, (hreg_b .x12).trans hx12e, ?_, ?_⟩
      · intro idx hidx
        rw [c_readBuffer_of_mem_eq hmem_b]
        by_cases hlt : idx < 2048 * n
        · exact (hprese.readBuffer_eq (by omega) (by omega)).trans (hresn idx hlt)
        · have hj : idx - 2048 * n < 2048 := by omega
          have heq : 2048 * n + (idx - 2048 * n) = idx := by omega
          simpa only [Nat.add_assoc, heq] using hrese (idx - 2048 * n) hj
      · have hp1 := (hpresn.mono (le_refl _) (hi' := C_TD + 32 * (2 ^ 24 + 2048 * (n + 1))) (by omega)).trans
          (hprese.mono (lo' := C_TD + 32 * 2 ^ 24) (hi' := C_TD + 32 * (2 ^ 24 + 2048 * (n + 1))) (by omega) (by omega))
        exact hp1.trans (CommitMemOutside.of_mem_eq hmem_b _ _)
  obtain ⟨sp, hrun_p, hpcp, hregp, hx10p, hx12p, hresp, hpresp⟩ := hind 8191 (le_refl _)
  have hrow_last : ∀ p : Fin (LENGTH / 2),
      readBuffer sp (C_ROW + 120 * p.val) 32 = leafA c64 p200 (msg ⟨2 * p.val, by have := p.isLt; omega⟩) ∧
      readBuffer sp (C_ROW + 120 * p.val + 88) 32 = leafA c64 p200 (msg ⟨2 * p.val + 1, by have := p.isLt; omega⟩) ∧
      readBuffer sp (C_ROW + 120 * p.val + 32) 8 = 0 ∧
      readBuffer sp (C_ROW + 120 * p.val + 80) 8 = 0 ∧
      readBuffer sp (C_ROW + 120 * p.val + 40) 24 = pairSaltEven (rand p) ∧
      readBuffer sp (C_ROW + 120 * p.val + 56) 24 = pairSaltOdd (rand p) := by
    intro p; have hp := p.isLt
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hrow p
    exact ⟨(hpresp.readBuffer_eq (by omega) (by omega)).trans h1,
           (hpresp.readBuffer_eq (by omega) (by omega)).trans h2,
           (hpresp.readBuffer_eq (by omega) (by omega)).trans h3,
           (hpresp.readBuffer_eq (by omega) (by omega)).trans h4,
           (hpresp.readBuffer_eq (by omega) (by omega)).trans h5,
           (hpresp.readBuffer_eq (by omega) (by omega)).trans h6⟩
  obtain ⟨se, hbody, hpce, hrege, hx10e, _, hrese, hprese⟩ :=
    c_p1d_chunk_body h512 oracle msg rand sp 8191 (by omega) hpcp
      ((hregp .x5 (by decide) (by decide)).trans hx5) hx10p
      ((hregp .x11 (by decide) (by decide)).trans hx11) hx12p
      ((hregp .x13 (by decide) (by decide)).trans hx13) hrow_last
  obtain ⟨hlatch, hpc_l, hmem_l, hreg_l⟩ :=
    c_p1d_latch_exit oracle se hpce hx10e
      ((hrege .x19 (by decide) (by decide)).trans ((hregp .x19 (by decide) (by decide)).trans hx19))
  let sLoop := execInstrBr se (.BEQ .x10 .x19 (8#13))
  let sFin := c_mid1DInstrs.foldl execInstrBr sLoop
  have hmid_run := c_mid1D_run oracle sLoop hpc_l
  obtain ⟨hpc_f, hmem_f, hx5_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx19_f, hx26_f⟩ :=
    c_mid1D_spec sLoop hpc_l
      ((hreg_l .x5).trans ((hrege .x5 (by decide) (by decide)).trans ((hregp .x5 (by decide) (by decide)).trans hx5)))
      ((hreg_l .x9).trans ((hrege .x9 (by decide) (by decide)).trans ((hregp .x9 (by decide) (by decide)).trans hx9)))
      ((hreg_l .x11).trans ((hrege .x11 (by decide) (by decide)).trans ((hregp .x11 (by decide) (by decide)).trans hx11)))
      ((hreg_l .x13).trans ((hrege .x13 (by decide) (by decide)).trans ((hregp .x13 (by decide) (by decide)).trans hx13)))
      ((hreg_l .x26).trans ((hrege .x26 (by decide) (by decide)).trans ((hregp .x26 (by decide) (by decide)).trans hx26)))
  refine ⟨sFin,
    by simpa only [show 6146 * 8191 + 6144 + 1 + 9 = 50348040 by decide,
      show 20482 * 8191 + 20480 + 1 + 9 = 167788552 by decide,
      show 2048 * 8191 + 2048 + 0 + 0 = 16777216 by decide] using
      (((hrun_p.trans hbody).trans hlatch).trans hmid_run),
    hpc_f, hx5_f, hx9_f, hx10_f, hx11_f, hx12_f, hx13_f, hx19_f, hx26_f, ?_, ?_⟩
  · intro idx hidx
    rw [levelSize_0] at hidx
    rw [c_readBuffer_of_mem_eq hmem_f, c_readBuffer_of_mem_eq hmem_l]
    have hhi : heapIdx 0 idx = LENGTH + idx := by unfold heapIdx levelSize LENGTH LOG_LENGTH; rfl
    rw [hhi]
    by_cases hlt : idx < 2048 * 8191
    · exact (hprese.readBuffer_eq (by omega) (by omega)).trans (hresp idx hlt)
    · have hj : idx - 2048 * 8191 < 2048 := by omega
      have heq : 2048 * 8191 + (idx - 2048 * 8191) = idx := by omega
      simpa only [Nat.add_assoc, heq] using hrese (idx - 2048 * 8191) hj
  · have hp1 := (hpresp.mono (le_refl _) (hi' := C_ROW) (by omega)).trans
      (hprese.mono (lo' := C_TD + 32 * 2 ^ 24) (hi' := C_ROW) (by omega) (by omega))
    exact (hp1.trans (CommitMemOutside.of_mem_eq hmem_l _ _)).trans (CommitMemOutside.of_mem_eq hmem_f _ _)

end CommitGolfCandidate
