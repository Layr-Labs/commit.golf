import CommitGolfCandidate.MoonCommitBin
import CommitGolfCandidate.CompressionSampling

/-! Exact RV64IM execution proof for Phase 3 of the B1-Ultra-121 `commit` image
(`L24` unmasked 256-bit root + copy to commitment + `HALT(0)`, words `1503..1522`), plus
full-commit composition proving `commit_run_exact`, `commit_oracle_run_exact`, and `commit_termination`:
- Exact `454,689,296` steps, `1,075,446,281` cycles, `83,886,079` compression calls
- Output distribution matches `$ᵗ BitVec (128 * LENGTH)` with `salts i = (packed.extractLsb' (128 * i.val) 128).extractLsb' 0 121`
  (definitionally `splitSalts121 packed`), satisfying `CommittedTrapdoor` and `HonestTranscriptRefines`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Phase 3: Unmasked `L24` Root + Copy to `C_CMT` + `HALT(0)` (words `1503..1522`) -/

private theorem levelBase_23_eq : levelBase 23 = 1610612544 := by decide
private theorem levelBase_24_eq : levelBase 24 = 1610612640 := by decide

private theorem fetch_tail_eq {st : MachineState} {idx : Nat} {instr : Instruction}
    (hlo : 1484 ≤ idx) (hhi : idx < 1523)
    (hpc : st.pc = BitVec.ofNat 64 (0x1000 + 4 * idx))
    (heq : commitTailInstr idx = instr) :
    fetch (submission.image .commit) st = some instr :=
  (commit_fetch_commitTailInstr st idx hlo hhi hpc).trans (congrArg some heq)

private theorem nodeVal_root_eq (c96 : Comp96) (msg : Message) (salts : Index → Salt121) :
    c96 (binaryInput (nodeVal c96 msg salts 23 0) (nodeVal c96 msg salts 23 1)) =
      rootVal c96 msg salts := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) 24 0 = _
  rw [nodeValFromLeaves]
  dsimp only
  unfold maskLevel
  have hlt : 2 * 0 + 1 < levelSize 23 := by rw [levelSize_23]; omega
  simp only [hlt, ite_true]; rfl

private theorem commit_rootSetup_half (oracle : Oracle) (s0 : MachineState) (pcIdx : Nat)
    (rd : Reg) (imm : BitVec 12) (lvlOff : Nat)
    (hrd : rd ≠ .x0) (_hrd6 : rd ≠ .x6)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * pcIdx))
    (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hf0 : fetch (submission.image .commit) s0 = some (.base (.ADDI .x6 .x0 (1536#12))))
    (hf1 : ∀ st : MachineState, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcIdx + 1)) →
      fetch (submission.image .commit) st = some (.base (.SLLI .x6 .x6 (20#6))))
    (hf2 : ∀ st : MachineState, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcIdx + 2)) →
      fetch (submission.image .commit) st = some (.base (.ADDI .x6 .x6 imm)))
    (hf3 : ∀ st : MachineState, st.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcIdx + 3)) →
      fetch (submission.image .commit) st = some (.base (.ADD rd .x9 .x6)))
    (hval : (BitVec.ofNat 64 (1536 * 1048576) + signExtend12 imm) = BitVec.ofNat 64 lvlOff) :
    ∃ s4,
      DetRun oracle (submission.image .commit) s0 4 s4 4 0 ∧
      s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcIdx + 4)) ∧
      s4.mem = s0.mem ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ rd → s4.getReg r = s0.getReg r) ∧
      s4.getReg rd = BitVec.ofNat 64 (C_TD + lvlOff) := by
  let r1 := execInstrBr s0 (.ADDI .x6 .x0 (1536#12))
  let r2 := execInstrBr r1 (.SLLI .x6 .x6 (20#6))
  let r3 := execInstrBr r2 (.ADDI .x6 .x6 imm)
  let r4 := execInstrBr r3 (.ADD rd .x9 .x6)
  have hr1_pc : r1.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcIdx + 1)) := pc_step_idx s0 pcIdx hpc
  have hr2_pc : r2.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcIdx + 2)) := pc_step_idx r1 (pcIdx + 1) hr1_pc
  have hr3_pc : r3.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcIdx + 3)) := pc_step_idx r2 (pcIdx + 2) hr2_pc
  have hr4_pc : r4.pc = BitVec.ofNat 64 (0x1000 + 4 * (pcIdx + 4)) := pc_step_idx r3 (pcIdx + 3) hr3_pc
  have hm4 : r4.mem = s0.mem := by
    rw [show r4 = execInstrBr r3 (.ADD rd .x9 .x6) from rfl, mem_exec_ADD,
        show r3 = execInstrBr r2 (.ADDI .x6 .x6 imm) from rfl, mem_exec_ADDI,
        show r2 = execInstrBr r1 (.SLLI .x6 .x6 (20#6)) from rfl, mem_exec_SLLI,
        show r1 = execInstrBr s0 (.ADDI .x6 .x0 (1536#12)) from rfl, mem_exec_ADDI]
  have hr1_reg : ∀ r : Reg, r ≠ .x6 → r1.getReg r = s0.getReg r := fun r h6 => by
    simp only [r1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm h6)]
  have hr1_x6 : r1.getReg .x6 = 1536#64 := by
    simp only [r1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), c_getReg_x0]; decide
  have hr2_reg : ∀ r : Reg, r ≠ .x6 → r2.getReg r = s0.getReg r := fun r h6 => by
    simp only [r2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm h6)]
    exact hr1_reg r h6
  have hr2_x6 : r2.getReg .x6 = BitVec.ofNat 64 (1536 * 1048576) := by
    simp only [r2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hr1_x6]; decide
  have hr3_reg : ∀ r : Reg, r ≠ .x6 → r3.getReg r = s0.getReg r := fun r h6 => by
    simp only [r3, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm h6)]
    exact hr2_reg r h6
  have hr3_x6 : r3.getReg .x6 = BitVec.ofNat 64 lvlOff := by
    simp only [r3, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hr2_x6, hval]
  have hr4_reg : ∀ r : Reg, r ≠ .x6 → r ≠ rd → r4.getReg r = s0.getReg r := fun r h6 hrd' => by
    simp only [r4, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' rd r (Ne.symm hrd')]
    exact hr3_reg r h6
  have hr4_rd : r4.getReg rd = BitVec.ofNat 64 (C_TD + lvlOff) := by
    simp only [r4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq hrd, hr3_reg .x9 (by decide), hx9, hr3_x6, ← BitVec.ofNat_add]
  have d0 : DetRun oracle (submission.image .commit) s0 1 r1 1 0 := DetRun.step1 hf0 rfl
  have d1 : DetRun oracle (submission.image .commit) r1 1 r2 1 0 := DetRun.step1 (hf1 r1 hr1_pc) rfl
  have d2 : DetRun oracle (submission.image .commit) r2 1 r3 1 0 := DetRun.step1 (hf2 r2 hr2_pc) rfl
  have d3 : DetRun oracle (submission.image .commit) r3 1 r4 1 0 := DetRun.step1 (hf3 r3 hr3_pc) rfl
  exact ⟨r4, ((d0.trans d1).trans d2).trans d3, hr4_pc, hm4, hr4_reg, hr4_rd⟩

private theorem commit_phase3 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt121) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 1503))
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hl23_0 : readBuffer s0 (C_TD + levelBase 23) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 23 0)
    (hl23_1 : readBuffer s0 (C_TD + levelBase 23 + 32) 32 =
      nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 23 1)
    (hgap23 : readBuffer s0 (C_TD + levelBase 23 + 64) 32 = 0) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 19 s1 26 1 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 1522) ∧
      s1.getReg .x5 = 1#64 ∧
      s1.getReg .x10 = 0#64 ∧
      readBuffer s1 (C_TD + levelBase 24) 32 = rootVal c96 msg salts ∧
      readBuffer s1 C_CMT 32 = rootVal c96 msg salts ∧
      (∀ addr : Nat, addr < 2 ^ 64 →
        (addr < C_CMT ∨ C_CMT + 32 ≤ addr) →
        (addr < C_TD + levelBase 24 ∨ C_TD + levelBase 24 + 32 ≤ addr) →
        s1.getByte (BitVec.ofNat 64 addr) = s0.getByte (BitVec.ofNat 64 addr)) := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hC_CMT : C_CMT = 4294971392 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hlb23 := levelBase_23_eq
  have hlb24 := levelBase_24_eq
  obtain ⟨smid, hr1a, hmid_pc, hmid_mem, hmid_reg, hmid_x10⟩ :=
    commit_rootSetup_half oracle s0 1503 .x10 (3904#12) (levelBase 23) (by decide) (by decide) hpc hx9
      (fetch_tail_eq (by omega) (by omega) hpc (by simp only [commitTailInstr]))
      (fun st hst => fetch_tail_eq (by omega) (by omega) hst (by simp only [Nat.reduceAdd, commitTailInstr]))
      (fun st hst => fetch_tail_eq (by omega) (by omega) hst (by simp only [Nat.reduceAdd, commitTailInstr]))
      (fun st hst => fetch_tail_eq (by omega) (by omega) hst (by simp only [Nat.reduceAdd, commitTailInstr]))
      (by rw [hlb23]; decide)
  obtain ⟨s1, hr1b, hs1_pc, hs1_mem_m, hs1_reg_m, hs1_x12⟩ :=
    commit_rootSetup_half oracle smid 1507 .x12 (4000#12) (levelBase 24) (by decide) (by decide) hmid_pc
      ((hmid_reg .x9 (by decide) (by decide)).trans hx9)
      (fetch_tail_eq (by omega) (by omega) hmid_pc (by simp only [Nat.reduceAdd, commitTailInstr]))
      (fun st hst => fetch_tail_eq (by omega) (by omega) hst (by simp only [Nat.reduceAdd, commitTailInstr]))
      (fun st hst => fetch_tail_eq (by omega) (by omega) hst (by simp only [Nat.reduceAdd, commitTailInstr]))
      (fun st hst => fetch_tail_eq (by omega) (by omega) hst (by simp only [Nat.reduceAdd, commitTailInstr]))
      (by rw [hlb24]; decide)
  have hr1 : DetRun oracle (submission.image .commit) s0 8 s1 8 0 := hr1a.trans hr1b
  have hs1_mem : s1.mem = s0.mem := hs1_mem_m.trans hmid_mem
  have hs1_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s1.getReg r = s0.getReg r := fun r h6 h10 h12 =>
    (hs1_reg_m r h6 h12).trans (hmid_reg r h6 h10)
  have hs1_x5 : s1.getReg .x5 = 0#64 := (hs1_reg .x5 (by decide) (by decide) (by decide)).trans hx5
  have hs1_x11 : s1.getReg .x11 = 96#64 := (hs1_reg .x11 (by decide) (by decide) (by decide)).trans hx11
  have hs1_x13 : s1.getReg .x13 = 0#64 := (hs1_reg .x13 (by decide) (by decide) (by decide)).trans hx13
  have hs1_x26 : s1.getReg .x26 = BitVec.ofNat 64 C_CMT := (hs1_reg .x26 (by decide) (by decide) (by decide)).trans hx26
  have hs1_x10 : s1.getReg .x10 = BitVec.ofNat 64 (C_TD + levelBase 23) :=
    (hs1_reg_m .x10 (by decide) (by decide)).trans hmid_x10
  -- Word 1511: Root compression ECALL
  let rt : Digest := rootVal c96 msg salts
  let s2 := writeBits s1 (BitVec.ofNat 64 (C_TD + levelBase 24)) rt
  have hrb23 : readBuffer s1 (C_TD + levelBase 23) 96 =
      binaryInput (nodeVal c96 msg salts 23 0) (nodeVal c96 msg salts 23 1) := by
    rw [readBuffer_of_mem_eq hs1_mem, readBuffer_binary_of_zero_gap s0 (C_TD + levelBase 23) hgap23, hl23_0, hl23_1]
  have hr2 : DetRun oracle (submission.image .commit) s1 1 s2 8 1 :=
    DetRun.compress_eq h768 (fetch_tail_eq (by omega) (by omega) hs1_pc (by simp only [commitTailInstr]))
      hs1_x5 hs1_x11 hs1_x13 (C_TD + levelBase 23) (C_TD + levelBase 24) hs1_x10 hs1_x12
      (by omega) (by omega) (by omega) (by omega) rt (by rw [hrb23]; exact nodeVal_root_eq c96 msg salts)
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 1512) := pc_step_idx s1 1511 hs1_pc
  have hp02 : MemPreservedOutside s0 s2 (C_TD + levelBase 24) (C_TD + levelBase 24 + 32) :=
    (MemPreservedOutside.of_mem_eq hs1_mem _ _).trans (memPreserved_writeBits s1 (C_TD + levelBase 24) rt (by omega))
  -- Words 1512..1519: copy 32 bytes from `C_TD + levelBase 24` to `C_CMT`
  obtain ⟨s3, hr3, hs3_pc, _, hs3_cmt, hp23⟩ :=
    commit_copy32 oracle s2 1512 .x12 .x26 (C_TD + levelBase 24) C_CMT 0 0
      (by decide) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      hs2_pc ((writeBits_register s1 _ rt .x12).trans hs1_x12) ((writeBits_register s1 _ rt .x26).trans hs1_x26)
      (fun k hk st => ⟨fun hst => by
          have hf := commit_fetch_commitTailInstr st (1512 + 2 * k) (by omega) (by omega) hst
          rw [hf]; interval_cases k <;> simp only [Nat.reduceMul, Nat.reduceAdd, commitTailInstr],
        fun hst => by
          have hf := commit_fetch_commitTailInstr st (1512 + 2 * k + 1) (by omega) (by omega) hst
          rw [hf]; interval_cases k <;> simp only [Nat.reduceMul, Nat.reduceAdd, commitTailInstr]⟩)
  -- Words 1520..1521: `ADDI x5, x0, 1; ADDI x10, x0, 0`
  let s4 := execInstrBr s3 (.ADDI .x5 .x0 (1#12))
  let s5 := execInstrBr s4 (.ADDI .x10 .x0 (0#12))
  have hs3_pc' : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * 1520) := hs3_pc
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * 1521) := pc_step_idx s3 1520 hs3_pc'
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * 1522) := pc_step_idx s4 1521 hs4_pc
  have hr4 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (fetch_tail_eq (instr := .base (.ADDI .x5 .x0 (1#12))) (by omega) (by omega) hs3_pc' (by simp only [commitTailInstr])) rfl
  have hr5 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (fetch_tail_eq (instr := .base (.ADDI .x10 .x0 (0#12))) (by omega) (by omega) hs4_pc (by simp only [commitTailInstr])) rfl
  have hm35 : s5.mem = s3.mem := by
    rw [show s5 = execInstrBr s4 (.ADDI .x10 .x0 (0#12)) from rfl, mem_exec_ADDI,
        show s4 = execInstrBr s3 (.ADDI .x5 .x0 (1#12)) from rfl, mem_exec_ADDI]
  refine ⟨s5, (((hr1.trans hr2).trans hr3).trans hr4).trans hr5, hs5_pc, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [s5, s4, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x5 (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x5 ≠ .x0), c_getReg_x0]; decide
  · simp only [s5, s4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), c_getReg_x0]; decide
  · rw [readBuffer_of_mem_eq hm35, hp23.readBuffer_eq (by omega) (Or.inr (by omega))]
    exact writeBits_readBuffer_digest s1 (C_TD + levelBase 24) rt
  · rw [readBuffer_of_mem_eq hm35]
    simpa only [Nat.add_zero] using hs3_cmt.trans (writeBits_readBuffer_digest s1 (C_TD + levelBase 24) rt)
  · intro addr hbd houtC houtR
    rw [getByte_of_mem_eq hm35, hp23 addr hbd (by simpa only [Nat.add_zero] using houtC)]
    exact hp02 addr hbd houtR

/-! ### 2. Full Commit Composition (`commit_run_exact`, `commit_oracle_run_exact`, `commit_termination`) -/

private theorem commit_det_phases (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (s0 : MachineState) (packed : BitVec (128 * LENGTH))
    (hinv0 :
      s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 26) ∧
      s0.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s0.getReg .x5 = 0#64 ∧
      s0.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
      s0.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s0.getReg .x10 = BitVec.ofNat 64 (C_MSG - 96) ∧
      s0.getReg .x11 = 96#64 ∧
      s0.getReg .x13 = 0#64 ∧
      s0.getReg .x18 = BitVec.ofNat 64 (C_SALTS + 256) ∧
      s0.getReg .x19 = BitVec.ofNat 64 (C_MSG - 96 + 2 ^ 32) ∧
      s0.getReg .x23 = BitVec.ofNat 64 (C_TD + 768) ∧
      s0.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      s0.getReg .x27 = mask238Word ∧
      s0.getReg .x28 = maskSalt121Word ∧
      (∀ i : Index, readBuffer s0 (C_TD + saltOff i) 16 = packed.extractLsb' (128 * i.val) 128) ∧
      MemPreservedOutside (submission.initialState .commit msg) s0 C_SALTS (C_SALTS + 268435456)) :
    let rawSalts : Index → BitVec 128 := fun i => packed.extractLsb' (128 * i.val) 128
    let salts : Index → Salt121 := fun i => (rawSalts i).extractLsb' 0 121
    ∃ sfin : MachineState,
      oracle.run (execute (submission.image .commit) (submission.steps .commit - 26) s0 true) =
        pure (⟨.success, sfin, 1041891823, 83886079⟩, 83886079) ∧
      readBuffer sfin C_CMT 32 =
        rootVal (fun x => oracle.compression (x.cast h768.symm)) msg salts ∧
      CommittedTrapdoor h768 oracle.compression msg salts
        (readBuffer sfin C_TD submission.sizes.trapdoor) := by
  obtain ⟨hpc0, hx2_0, hx5_0, _, hx9_0, hx10_0, hx11_0, hx13_0, hx18_0, hx19_0, hx23_0,
    hx26_0, hx27_0, hx28_0, hsalt0, hpres0⟩ := hinv0
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let rawSalts : Index → BitVec 128 := fun i => packed.extractLsb' (128 * i.val) 128
  let salts : Index → Salt121 := fun i => (rawSalts i).extractLsb' 0 121
  have htb := treeBytes_eq
  have hso := saltsOff_eq
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_CMT : C_CMT = 4294971392 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_SALTS : C_SALTS = 5905584096 := rfl
  have hC_DB : C_DB = 68719476000 := rfl
  have htd_sz : submission.sizes.trapdoor = 1879048128 := rfl
  have hmsg0 : ∀ (i : Index), ∀ j < 256,
      s0.getByte (BitVec.ofNat 64 (C_MSG + 256 * i.val + j)) = (msg i).extractLsb' (8 * j) 8 := by
    intro i j hj
    have hi : i.val < 16777216 := i.isLt
    rw [hpres0 _ (by omega) (Or.inl (by omega))]
    exact commit_initial_msg_byte msg i j hj
  -- Phase 1: leaf loop (`L0`)
  obtain ⟨s1, hr1, hpc1, hx2_1, hx5_1, hx9_1, hx11_1, hx13_1, hx26_1, hx27_1, hl0_1, hgap0_1, hpres1⟩ :=
    commit_phase1 h768 oracle msg rawSalts s0 hpc0 hx2_0 hx5_0 hx9_0 hx10_0 hx11_0 hx13_0
      hx18_0 hx19_0 hx23_0 hx26_0 hx27_0 hx28_0 hmsg0 hsalt0
  have hbytes0 : levelBytes 0 = levelBase 1 := by decide
  have hdata1 : ∀ off < 736, off % 8 = 0 →
      s1.getMem (BitVec.ofNat 64 (C_DB + off)) = (submission.initialState .commit msg).getMem (BitVec.ofNat 64 (C_DB + off)) := by
    intro off hoff hal
    have hlb0 := levelBase_bound 0 (by omega)
    rw [hpres1.getMem_eq (by omega) (by omega) (Or.inr (by omega)),
      hpres0.getMem_eq (by omega) (by omega) (Or.inr (by omega))]
  have hzero1 : ∀ l < 24, ∀ q < levelSize l / 2, ∀ j < 32,
      s1.getByte (BitVec.ofNat 64 (C_TD + levelBase l + 96 * q + 64 + j)) = 0 := by
    intro l hl q hq j hj
    have hlb_l := levelBase_bound l (by omega)
    have hbytes_l : levelBytes l = (levelSize l / 2) * 96 := by unfold levelBytes; simp [hl]
    by_cases hl0 : l = 0
    · subst hl0
      rw [hgap0_1 q hq j hj, hpres0 _ (by omega) (Or.inl (by omega))]
      exact commit_initial_zero_byte msg _ (Or.inr (by omega))
    · have hmono : levelBase 1 ≤ levelBase l := levelBase_mono 1 l (by omega) (by omega)
      rw [hpres1 _ (by omega) (Or.inr (by omega)), hpres0 _ (by omega) (Or.inl (by omega))]
      exact commit_initial_zero_byte msg _ (Or.inr (by omega))
  -- Phase 2: binary band (`L1..L23`)
  obtain ⟨s2, hr2, hpc2, hx5_2, hx9_2, hx11_2, hx13_2, hx26_2, hlvl2, hzero2, hpres2⟩ :=
    commit_phase2 h768 oracle msg salts s1 hpc1 hx2_1 hx5_1 hx9_1 hx11_1 hx13_1 hx26_1 hx27_1 hdata1 hl0_1 hzero1
  -- Phase 3: root `L24` + copy to `C_CMT` + halt setup
  have hl23_0 : readBuffer s2 (C_TD + levelBase 23) 32 = nodeVal c96 msg salts 23 0 := by
    simpa only [gapOffset, Nat.zero_div, Nat.add_zero, Nat.mul_zero] using hlvl2 23 (le_refl _) 0 (by rw [levelSize_23]; omega)
  have hl23_1 : readBuffer s2 (C_TD + levelBase 23 + 32) 32 = nodeVal c96 msg salts 23 1 := by
    simpa only [gapOffset, show 32 * (1 + 1 / 2) = 32 by decide] using hlvl2 23 (le_refl _) 1 (by rw [levelSize_23]; omega)
  have hgap23 : readBuffer s2 (C_TD + levelBase 23 + 64) 32 = 0 :=
    readBuffer_zero_of_bytes s2 _ 32 (fun j hj => by
      simpa only [Nat.mul_zero, Nat.add_zero, Nat.add_assoc] using hzero2 23 (by omega) 0 (by rw [levelSize_23]; omega) j hj)
  obtain ⟨s3, hr3, hpc3, hx5_3, hx10_3, hrt3, hcmt3, hpres3⟩ :=
    commit_phase3 h768 oracle msg salts s2 hpc2 hx5_2 hx9_2 hx11_2 hx13_2 hx26_2 hl23_0 hl23_1 hgap23
  -- Finish with `HALT(0)` ECALL at word 1522
  have htot := (hr1.trans hr2).trans hr3
  have hsteps_bd : 353894400 + 100794850 + 19 + 1 ≤ submission.steps .commit - 26 := by
    change 353894400 + 100794850 + 19 + 1 ≤ 4294967296 - 26; omega
  have hfin := DetRun.finish htot (fetch_tail_eq (by omega) (by omega) hpc3 (by simp only [commitTailInstr]))
    hx5_3 hx10_3 (submission.steps .commit - 26) hsteps_bd
  refine ⟨s3, hfin, hcmt3, ?_, ?_, ?_⟩
  · -- All tree nodes `l ≤ 24` match `nodeVal`
    intro l hl idx hidx
    have hlb_l := levelBase_bound l hl
    have hlb24 := levelBase_24_eq
    by_cases h24 : l = 24
    · subst h24
      rw [levelSize_24] at hidx
      have hi0 : idx = 0 := by omega
      subst hi0
      have hsl := read_buffer_slice s3 C_TD submission.sizes.trapdoor (levelBase 24 + nodeOffset 24 0) 32
        (by unfold nodeOffset gapOffset; rw [htd_sz, hlb24]; omega)
      rw [hsl]
      have haddr : C_TD + (levelBase 24 + nodeOffset 24 0) = C_TD + levelBase 24 := by
        unfold nodeOffset gapOffset; omega
      rw [haddr]
      exact hrt3
    · have hgo := gapOffset_lt_levelBytes l idx (by omega) hidx
      have hstep_l : levelBase (l + 1) = levelBase l + levelBytes l := rfl
      have hmono24 : levelBase (l + 1) ≤ levelBase 24 := levelBase_mono (l + 1) 24 (by omega) (by omega)
      have hsl := read_buffer_slice s3 C_TD submission.sizes.trapdoor (levelBase l + nodeOffset l idx) 32
        (by unfold nodeOffset; rw [htd_sz]; omega)
      rw [hsl]
      have hp3 : readBuffer s3 (C_TD + (levelBase l + gapOffset idx)) 32 =
          readBuffer s2 (C_TD + (levelBase l + gapOffset idx)) 32 :=
        readBuffer_congr _ _ _ _ (fun j hj => hpres3 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega)))
      unfold nodeOffset
      rw [hp3, ← Nat.add_assoc]
      exact hlvl2 l (by omega) idx hidx
  · -- All zero gaps `l < 24` are zero
    intro l hl q hq
    have hlb_l := levelBase_bound l (by omega)
    have hbytes_l : levelBytes l = (levelSize l / 2) * 96 := by unfold levelBytes; simp [hl]
    have hlb24 := levelBase_24_eq
    have hstep_l : levelBase (l + 1) = levelBase l + levelBytes l := rfl
    have hmono24 : levelBase (l + 1) ≤ levelBase 24 := levelBase_mono (l + 1) 24 (by omega) (by omega)
    have hsl := read_buffer_slice s3 C_TD submission.sizes.trapdoor (levelBase l + 96 * q + 64) 32
      (by rw [htd_sz]; omega)
    rw [hsl]
    exact readBuffer_zero_of_bytes s3 _ 32 (fun j hj => by
      rw [hpres3 _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
      simpa only [Nat.add_assoc] using hzero2 l hl q hq j hj)
  · -- All 121-bit salts match `salts i = (packed.extractLsb' (128 * i.val) 128).extractLsb' 0 121`
    intro i
    have hso_bd : saltOff i + 16 ≤ submission.sizes.trapdoor := by
      rw [htd_sz, ← trapdoorBytes_eq]; exact saltOff_add_16_le i
    have hlb24 := levelBase_24_eq
    have hlb0 := levelBase_bound 0 (by omega)
    have hso_ge : levelBase 24 + 32 ≤ saltOff i := by unfold saltOff; rw [hso, hlb24]; omega
    have hsl16 := read_buffer_slice s3 C_TD submission.sizes.trapdoor (saltOff i) 16 hso_bd
    have h121 : (readBuffer s3 C_TD submission.sizes.trapdoor).extractLsb' (8 * saltOff i) 121 =
        ((readBuffer s3 C_TD submission.sizes.trapdoor).extractLsb' (8 * saltOff i) 128).extractLsb' 0 121 := by
      apply BitVec.eq_of_getLsbD_eq; intro b hb
      simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, Nat.zero_add,
        show b < 128 by omega]
    rw [h121, hsl16]
    have hp3 : readBuffer s3 (C_TD + saltOff i) 16 = readBuffer s2 (C_TD + saltOff i) 16 :=
      readBuffer_congr _ _ _ _ (fun j hj => hpres3 _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)))
    rw [hp3, hpres2.readBuffer_eq (by omega) (Or.inr (by omega)),
      hpres1.readBuffer_eq (by omega) (Or.inr (by omega)), hsalt0 i]

private theorem readBuffer_digest_eq (s : MachineState) (a : Nat) (v : Commitment)
    (h : readBuffer s a 32 = v) : readBuffer s a DIGEST_BYTES = v := by
  have hgen : ∀ (n : Nat) (hn : n = 32) (w : BitVec (8 * n)),
      readBuffer s a 32 = w.cast (by rw [hn]) → readBuffer s a n = w := by
    intro n hn; subst hn; intro w hw; exact hw
  exact hgen DIGEST_BYTES rfl v h

private theorem commit_run_eq_helper (oracle : Oracle) (message : Message)
    (post0 finalState : BitVec (128 * LENGTH) → MachineState)
    (hrun0 : oracle.run (execute (submission.image .commit) (26 + (submission.steps .commit - 26))
        (submission.initialState .commit message) true) =
      (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
        (fun p : Execution × Nat => (p.1.charge 33554458 0, p.2)) <$>
          oracle.run (execute (submission.image .commit) (submission.steps .commit - 26) (post0 packed) true)))
    (hs : ∀ packed, oracle.run (execute (submission.image .commit) (submission.steps .commit - 26) (post0 packed) true) =
      pure (⟨.success, finalState packed, 1041891823, 83886079⟩, 83886079)) :
    oracle.run (submission.run .commit message) =ᵈ
      (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
        pure (({ exit := Riscv.Exit.success, state := finalState packed,
                 cycles := 1075446281, oracleCalls := 83886079 } : Execution), 83886079)) := by
  have hsteps_commit : submission.steps .commit = 26 + (submission.steps .commit - 26) := by
    have hge : 26 ≤ submission.steps .commit := by change 26 ≤ 4294967296; omega
    omega
  rw [submission_run_commit submission message, hsteps_commit, hrun0]
  have heq :
      (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
        (fun p : Execution × Nat => (p.1.charge 33554458 0, p.2)) <$>
          oracle.run (execute (submission.image .commit) (submission.steps .commit - 26) (post0 packed) true)) =
      (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
        pure (({ exit := Riscv.Exit.success, state := finalState packed,
                 cycles := 1075446281, oracleCalls := 83886079 } : Execution), 83886079)) := by
    apply bind_congr; intro packed
    rw [hs packed, map_pure]
    unfold Execution.charge; dsimp only
  rw [heq]

private theorem commit_read_spec_helper (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) (sfin : MachineState) (salts : Index → Salt121)
    (hcmt : readBuffer sfin C_CMT 32 = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts)
    (htd : CommittedTrapdoor h768 oracle.compression message salts (readBuffer sfin C_TD submission.sizes.trapdoor)) :
    let (cmt, td) := submission.readCommit ⟨.success, sfin, 1075446281, 83886079⟩
    cmt = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts ∧
    CommittedTrapdoor h768 oracle.compression message salts td := by
  have hC_CMT_eq : submission.layout.commitment = C_CMT := rfl
  have hC_TD_eq : submission.layout.trapdoor = C_TD := rfl
  dsimp only
  unfold Submission.readCommit
  dsimp only
  rw [hC_CMT_eq, hC_TD_eq]
  exact ⟨readBuffer_digest_eq sfin C_CMT _ hcmt, htd⟩

/-- Full exact execution of `submission.run .commit message` for any fixed oracle and message:
always halts with `.success`, exactly `1,075,446,281` cycles and `83,886,079` compression calls,
writing `rootVal` to the commitment buffer and a valid `CommittedTrapdoor` to the trapdoor buffer. -/
theorem commit_run_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    ∃ finalState : BitVec (128 * LENGTH) → MachineState,
      oracle.run (submission.run .commit message) =ᵈ
        (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
          pure (({ exit := Riscv.Exit.success, state := finalState packed,
                   cycles := 1075446281, oracleCalls := 83886079 } : Execution), 83886079)) ∧
      ∀ packed : BitVec (128 * LENGTH),
        let salts : Index → Salt121 := fun i => (packed.extractLsb' (128 * i.val) 128).extractLsb' 0 121
        let (cmt, td) := submission.readCommit
          ⟨Riscv.Exit.success, finalState packed, 1075446281, 83886079⟩
        cmt = rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts ∧
        CommittedTrapdoor h768 oracle.compression message salts td := by
  obtain ⟨post0, hrun0, hinv0⟩ := commit_phase0 oracle message (submission.steps .commit - 26)
  have hdet : ∀ packed : BitVec (128 * LENGTH),
      let salts : Index → Salt121 := fun i => (packed.extractLsb' (128 * i.val) 128).extractLsb' 0 121
      ∃ sfin : MachineState,
        oracle.run (execute (submission.image .commit) (submission.steps .commit - 26) (post0 packed) true) =
          pure (⟨.success, sfin, 1041891823, 83886079⟩, 83886079) ∧
        readBuffer sfin C_CMT 32 =
          rootVal (fun x => oracle.compression (x.cast h768.symm)) message salts ∧
        CommittedTrapdoor h768 oracle.compression message salts
          (readBuffer sfin C_TD submission.sizes.trapdoor) :=
    fun packed => commit_det_phases h768 oracle message (post0 packed) packed (hinv0 packed)
  let finalState (packed : BitVec (128 * LENGTH)) : MachineState := Classical.choose (hdet packed)
  exact ⟨finalState,
    commit_run_eq_helper oracle message post0 finalState hrun0 (fun packed => (Classical.choose_spec (hdet packed)).1),
    fun packed => commit_read_spec_helper h768 oracle message (finalState packed)
      (fun i => (packed.extractLsb' (128 * i.val) 128).extractLsb' 0 121)
      (Classical.choose_spec (hdet packed)).2.1 (Classical.choose_spec (hdet packed)).2.2⟩

/-- Exact `fixedOracleRun` refinement of `submission.scheme.commit message` for `MoonHiding`. -/
theorem commit_oracle_run_exact (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    ∃ trapdoorOf : BitVec (128 * LENGTH) → BitVec (8 * submission.sizes.trapdoor),
      fixedOracleRun oracle (submission.scheme.commit message) =ᵈ
        (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
          pure (rootVal (fun x => oracle.compression (x.cast h768.symm)) message
            (fun i => (packed.extractLsb' (128 * i.val) 128).extractLsb' 0 121), trapdoorOf packed)) ∧
      ∀ packed : BitVec (128 * LENGTH),
        CommittedTrapdoor h768 oracle.compression message
          (fun i => (packed.extractLsb' (128 * i.val) 128).extractLsb' 0 121) (trapdoorOf packed) := by
  obtain ⟨finalState, hrun, hspec⟩ := commit_run_exact h768 oracle message
  refine ⟨fun packed => (submission.readCommit ⟨.success, finalState packed, 1075446281, 83886079⟩).2, ?_, ?_⟩
  · let f : Execution × Nat → Commitment × BitVec (8 * submission.sizes.trapdoor) :=
      fun p => submission.readCommit p.1
    have hmap : (fixedOracleRun oracle (submission.scheme.commit message) :
          ProbComp (Commitment × BitVec (8 * submission.sizes.trapdoor))) =
        f <$> oracle.run (submission.run .commit message) := by
      simp only [fixedOracleRun, Submission.scheme, oracle_run_map, Functor.map_map, f]
    have hstep : f <$> (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
          pure (({ exit := Riscv.Exit.success, state := finalState packed,
                   cycles := 1075446281, oracleCalls := 83886079 } : Execution), 83886079)) =
        (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
          pure (rootVal (fun x => oracle.compression (x.cast h768.symm)) message
                  (fun i => (packed.extractLsb' (128 * i.val) 128).extractLsb' 0 121),
                (submission.readCommit ⟨.success, finalState packed, 1075446281, 83886079⟩).2)) := by
      rw [map_bind]
      apply bind_congr; intro packed
      rw [map_pure]
      exact congrArg pure (Prod.ext (hspec packed).1 rfl)
    exact hmap.symm ▸ (hstep ▸ (hrun.map f))
  · intro packed; exact (hspec packed).2

private theorem commit_prEvent_uniform_bind_pure_eq_one {α β : Type} [SampleableType α]
    (f : α → β) (p : β → Prop) (h : ∀ a, p (f a)) :
    Pr{let y ← (($ᵗ α) >>= fun a => pure (f a))}[p y] = 1 := by
  have h1 : Pr{let y ← (($ᵗ α) >>= fun a => pure (f a))}[p y] =
      Pr{let y ← (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit))}[True] := by
    apply prEvent_bind_congr ($ᵗ α) (fun a => pure (f a)) (fun _ => pure ()) p (fun _ => True)
    intro a
    classical
    simp only [prEvent_pure, h a, ite_true]
  rw [h1]
  have h2 : (fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit)) =
      (($ᵗ α) >>= fun _ => (pure True : ProbComp Prop)) := by
    simp only [map_bind, map_pure]
  change prEvent ((fun _ : Unit => True) <$> (($ᵗ α) >>= fun _ => (pure () : ProbComp Unit))) = 1
  rw [h2, prEvent_def, OracleComp.evalDist_bind_const]
  change prEvent (pure True : ProbComp Prop) = 1
  simp only [prEvent_pure_prop, ite_true]

/-- `submission.run .commit` always terminates with probability 1 for every oracle and message. -/
theorem commit_termination (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (message : Message) :
    Pr{let result ← oracle.run (submission.run .commit message)}[
      result.1.exit ≠ Riscv.Exit.unfinished] = 1 := by
  obtain ⟨finalState, hrun, _⟩ := commit_run_exact h768 oracle message
  rw [hrun.prEvent_eq _]
  exact commit_prEvent_uniform_bind_pure_eq_one
    (fun packed => ((⟨.success, finalState packed, 1075446281, 83886079⟩ : Execution), 83886079))
    (fun result => result.1.exit ≠ Riscv.Exit.unfinished)
    (fun _ => by dsimp only; decide)

end CommitGolfCandidate
