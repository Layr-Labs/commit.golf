import CommitGolfCandidate.MoonCommitBase

/-! Exact RV64IM execution proof for Phase 1 of the B1-Ultra-121 `commit` image
(`leaf_loop`, words `26..700`, `U = 32` lanes × `21` words/lane, `524,288` chunks):
- Exact `353,894,400` steps, `823,656,448` cycles, `67,108,864` compression calls
- Computes `mask238 (leafDigest c96 i (salts i) (msg i)) = nodeVal c96 msg salts 0 i`
  into `L0` at `C_TD + gapOffset i`, preserving all zero gaps of `L0..L23`, all raw salts,
  and embedded `commitData`. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Isolated Branch-Target & Geometry Helpers -/

private theorem pc_bne_700 :
    BitVec.ofNat 64 (0x1000 + 4 * 700) + signExtend13 (5496#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 26) := by decide

private theorem gapOffset_block (c k : Nat) :
    gapOffset (32 * c + k) = 1536 * c + gapOffset k := by
  unfold gapOffset; omega

private theorem nodeVal_level0 (c96 : Comp96) (msg : Message) (salts : Index → Salt121)
    (idx : Nat) (hidx : idx < LENGTH) :
    mask238 (leafDigest c96 ⟨idx, hidx⟩ (salts ⟨idx, hidx⟩) (msg ⟨idx, hidx⟩)) =
      nodeVal c96 msg salts 0 idx := by
  symm
  show nodeValFromLeaves c96 (fun i => leafDigest c96 i (salts i) (msg i)) 0 idx = _
  rw [nodeValFromLeaves]
  simp only [hidx, dite_true, maskLevel]
  rfl

/-! ### 2. Single Leaf Lane (`21` words = `21` steps, `49` cycles, `4` calls) -/

private theorem commit_leaf_step (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (rawSalts : Index → BitVec 128)
    (c k : Nat) (hc : c < 524288) (hk : k < 32) (s : MachineState)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k)))
    (hx5 : s.getReg .x5 = 0#64) (hx11 : s.getReg .x11 = 96#64) (hx13 : s.getReg .x13 = 0#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (32 * c + k) - 96))
    (hx18 : s.getReg .x18 = BitVec.ofNat 64 (C_SALTS + 512 * c + 256))
    (hx23 : s.getReg .x23 = BitVec.ofNat 64 (C_TD + 1536 * c + 768))
    (hx27 : s.getReg .x27 = mask238Word) (hx28 : s.getReg .x28 = maskSalt121Word)
    (hmsg : ∀ j < 256, s.getByte (BitVec.ofNat 64 (C_MSG + 256 * (32 * c + k) + j)) =
      (msg ⟨32 * c + k, by unfold LENGTH LOG_LENGTH; omega⟩).extractLsb' (8 * j) 8)
    (hsalt : readBuffer s (C_SALTS + 16 * (32 * c + k)) 16 =
      rawSalts ⟨32 * c + k, by unfold LENGTH LOG_LENGTH; omega⟩) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let salts : Index → Salt121 := fun i => (rawSalts i).extractLsb' 0 121
    let idx := 32 * c + k
    ∃ s',
      DetRun oracle (submission.image .commit) s 21 s' 49 4 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * (k + 1))) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (idx + 1) - 96) ∧
      readBuffer s' (C_TD + gapOffset idx) 32 = nodeVal c96 msg salts 0 idx ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < C_MSG + 256 * idx - 24 ∨ C_MSG + 256 * idx + 192 ≤ q) →
        (q < C_TD + gapOffset idx ∨ C_TD + gapOffset idx + 32 ≤ q) →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have hLEN : LENGTH = 16777216 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_SALTS : C_SALTS = 5905584096 := rfl
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let salts : Index → Salt121 := fun i => (rawSalts i).extractLsb' 0 121
  let idx := 32 * c + k
  have hidx : idx < LENGTH := by omega
  let iFin : Index := ⟨idx, hidx⟩
  let M : Nat := C_MSG + 256 * idx
  let S : Nat := C_SALTS + 16 * idx
  let H : Nat := C_TD + gapOffset idx
  have hgapk : gapOffset k ≤ 1504 := by unfold gapOffset; omega
  have hgap_idx : gapOffset idx = 1536 * c + gapOffset k := gapOffset_block c k
  have hH_bd : H + 32 ≤ C_SALTS := by
    have hlb : levelBase 0 + levelBytes 0 ≤ treeBytes := levelBase_bound 0 (by omega)
    have hgo : gapOffset idx + 32 ≤ levelBytes 0 := gapOffset_lt_levelBytes 0 idx (by omega) (by rw [levelSize_0]; omega)
    have htb := treeBytes_eq
    have hlb0 : levelBase 0 = 0 := rfl
    omega
  have hM_lt_H : M + 256 ≤ C_TD := by omega
  -- Fetch helper for words 0..20 of lane `k`
  have hfetch : ∀ j < 21, ∀ st : MachineState,
      st.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + j)) →
      fetch (submission.image .commit) st = some (leafLaneInstr k j) :=
    fun j hj st hst => commit_fetch_leaf st k j hk hj hst
  -- Extract raw 64-bit salt words from `hsalt`
  have hsalt_lo : s.getMem (BitVec.ofNat 64 S) = (rawSalts iFin).extractLsb' 0 64 := by
    have h0 := read_buffer_slice s S 16 0 8 (by decide)
    rw [Nat.add_zero, readBuffer_word s S (by omega), hsalt] at h0
    simpa only [Nat.mul_zero] using h0.symm
  have hsalt_hi : s.getMem (BitVec.ofNat 64 (S + 8)) = (rawSalts iFin).extractLsb' 64 64 := by
    have h1 := read_buffer_slice s S 16 8 8 (by decide)
    rw [readBuffer_word s (S + 8) (by omega), hsalt] at h1
    simpa only [show 8 * 8 = 64 from rfl] using h1.symm
  -- Steps 0..7: prepare Call 0 input at `[M - 24, M + 72)` (`salt121Word16 ++ leafTag ++ msg[0..72)`)
  let soff : BitVec 12 := BitVec.ofNat 12 ((4096 - 256 + 16 * k) % 4096)
  let soff8 : BitVec 12 := BitVec.ofNat 12 ((4096 - 248 + 16 * k) % 4096)
  let hoff : BitVec 12 := BitVec.ofNat 12 ((4096 - 768 + 32 * (k + k / 2)) % 4096)
  have haddr_soff : s.getReg .x18 + signExtend12 soff = BitVec.ofNat 64 S := by
    rw [hx18, add_signExtend12_signed_offset _ 256 (16 * k) (by omega) (by omega) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have haddr_soff8 : s.getReg .x18 + signExtend12 soff8 = BitVec.ofNat 64 (S + 8) := by
    rw [hx18]
    have h8 : (4096 - 248 + 16 * k) % 4096 = (4096 - 256 + (16 * k + 8)) % 4096 := by omega
    rw [show soff8 = BitVec.ofNat 12 ((4096 - 256 + (16 * k + 8)) % 4096) by simp only [soff8, h8],
      add_signExtend12_signed_offset _ 256 (16 * k + 8) (by omega) (by omega) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have haddr_hoff : s.getReg .x23 + signExtend12 hoff = BitVec.ofNat 64 H := by
    rw [hx23, add_signExtend12_signed_offset _ 768 (32 * (k + k / 2)) (by omega) (by omega) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by unfold H; rw [hgap_idx]; unfold gapOffset; omega)
  let s1 := execInstrBr s (.ADDI .x10 .x10 (72#12))
  let s2 := execInstrBr s1 (.LD .x6 .x18 soff)
  let s3 := execInstrBr s2 (.SD .x10 .x6 (0#12))
  let s4 := execInstrBr s3 (.LD .x6 .x18 soff8)
  let s5 := execInstrBr s4 (.AND .x6 .x6 .x28)
  let s6 := execInstrBr s5 (.SD .x10 .x6 (8#12))
  let s7 := execInstrBr s6 (.SD .x10 .x10 (16#12))
  let s8 := execInstrBr s7 (.ADDI .x12 .x10 (64#12))
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 1)) := pc_step_idx s _ hpc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 2)) := pc_step_idx s1 _ hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 3)) := pc_step_idx s2 _ hs2_pc
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 4)) := pc_step_idx s3 _ hs3_pc
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 5)) := pc_step_idx s4 _ hs4_pc
  have hs6_pc : s6.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 6)) := pc_step_idx s5 _ hs5_pc
  have hs7_pc : s7.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 7)) := pc_step_idx s6 _ hs6_pc
  have hs8_pc : s8.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 8)) := pc_step_idx s7 _ hs7_pc
  have hs1_x10 : s1.getReg .x10 = BitVec.ofNat 64 (M - 24) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hx10,
      add_signExtend12_ofNat_small _ 72 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs1_reg : ∀ r : Reg, r ≠ .x10 → s1.getReg r = s.getReg r := fun r hr => by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm hr)]
  have hs2_reg : ∀ r : Reg, r ≠ .x6 → s2.getReg r = s1.getReg r := fun r hr => by
    simp only [s2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm hr)]
  have hs4_reg : ∀ r : Reg, r ≠ .x6 → s4.getReg r = s3.getReg r := fun r hr => by
    simp only [s4, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm hr)]
  have hs5_reg : ∀ r : Reg, r ≠ .x6 → s5.getReg r = s4.getReg r := fun r hr => by
    simp only [s5, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm hr)]
  have hs8_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s8.getReg r = s.getReg r := fun r h6 h10 h12 => by
    have h87 : s8.getReg r = s7.getReg r := by
      simp only [s8, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
    rw [h87, reg_exec_SD, reg_exec_SD, hs5_reg r h6, hs4_reg r h6, reg_exec_SD, hs2_reg r h6, hs1_reg r h10]
  have hs8_x10 : s8.getReg .x10 = BitVec.ofNat 64 (M - 24) := by
    have h87 : s8.getReg .x10 = s7.getReg .x10 := by
      simp only [s8, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide)]
    rw [h87, reg_exec_SD, reg_exec_SD, hs5_reg .x10 (by decide), hs4_reg .x10 (by decide),
      reg_exec_SD, hs2_reg .x10 (by decide), hs1_x10]
  have hs8_x12 : s8.getReg .x12 = BitVec.ofNat 64 (M + 40) := by
    have h7_x10 : s7.getReg .x10 = BitVec.ofNat 64 (M - 24) := by
      rw [reg_exec_SD, reg_exec_SD, hs5_reg .x10 (by decide), hs4_reg .x10 (by decide),
        reg_exec_SD, hs2_reg .x10 (by decide), hs1_x10]
    simp only [s8, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), h7_x10,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  -- Track memory updates through steps 0..7
  have hm1 : s1.mem = s.mem := mem_exec_ADDI s _ _ _
  have hm2 : s2.mem = s.mem := (mem_exec_LD s1 _ _ _).trans hm1
  have hs2_x6 : s2.getReg .x6 = (rawSalts iFin).extractLsb' 0 64 := by
    simp only [s2, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hs1_reg .x18 (by decide), haddr_soff,
      MachineState.getMem, hm1]
    exact hsalt_lo
  have hs2_a0 : s2.getReg .x10 + signExtend12 (0#12) = BitVec.ofNat 64 (M - 24) := by
    rw [hs2_reg .x10 (by decide), hs1_x10, add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
  have hs3_mem : s3.mem = (s.setMem (BitVec.ofNat 64 (M - 24)) ((rawSalts iFin).extractLsb' 0 64)).mem := by
    simp only [s3, execInstrBr, hs2_a0, hs2_x6, c_mem_setPC, MachineState.setMem, hm2]
  have hp3 : MemPreservedOutside s s3 (M - 24) (M - 16) :=
    (memPreserved_setMem s (M - 24) _ (by omega) (by omega)).mono (le_refl _) (by omega)
      |>.trans (MemPreservedOutside.of_mem_eq hs3_mem _ _)
  have hm4 : s4.mem = s3.mem := mem_exec_LD s3 _ _ _
  have hm5 : s5.mem = s3.mem := (c_mem_exec_AND s4 _ _ _).trans hm4
  have hs4_x6 : s4.getReg .x6 = (rawSalts iFin).extractLsb' 64 64 := by
    have hr18 : s3.getReg .x18 = s.getReg .x18 := by
      rw [reg_exec_SD, hs2_reg .x18 (by decide), hs1_reg .x18 (by decide)]
    simp only [s4, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hr18, haddr_soff8]
    rw [hp3.getMem_eq (by omega) (by omega) (by omega)]
    exact hsalt_hi
  have hs5_x6 : s5.getReg .x6 = (rawSalts iFin).extractLsb' 64 64 &&& maskSalt121Word := by
    have hr28 : s4.getReg .x28 = maskSalt121Word := by
      rw [hs4_reg .x28 (by decide), reg_exec_SD, hs2_reg .x28 (by decide), hs1_reg .x28 (by decide), hx28]
    simp only [s5, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hs4_x6, hr28]
  have hs5_a8 : s5.getReg .x10 + signExtend12 (8#12) = BitVec.ofNat 64 (M - 16) := by
    rw [hs5_reg .x10 (by decide), hs4_reg .x10 (by decide), reg_exec_SD, hs2_reg .x10 (by decide), hs1_x10,
      add_signExtend12_ofNat_small _ 8 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs6_mem : s6.mem = (s3.setMem (BitVec.ofNat 64 (M - 16))
      ((rawSalts iFin).extractLsb' 64 64 &&& maskSalt121Word)).mem := by
    simp only [s6, execInstrBr, hs5_a8, hs5_x6, c_mem_setPC, MachineState.setMem, hm5]
  have hp36 : MemPreservedOutside s3 s6 (M - 16) (M - 8) :=
    (memPreserved_setMem s3 (M - 16) _ (by omega) (by omega)).mono (le_refl _) (by omega)
      |>.trans (MemPreservedOutside.of_mem_eq hs6_mem _ _)
  have hs6_x10 : s6.getReg .x10 = BitVec.ofNat 64 (M - 24) := by
    rw [reg_exec_SD, hs5_reg .x10 (by decide), hs4_reg .x10 (by decide), reg_exec_SD, hs2_reg .x10 (by decide), hs1_x10]
  have hs6_a16 : s6.getReg .x10 + signExtend12 (16#12) = BitVec.ofNat 64 (M - 8) := by
    rw [hs6_x10, add_signExtend12_ofNat_small _ 16 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs7_mem : s7.mem = (s6.setMem (BitVec.ofNat 64 (M - 8)) (BitVec.ofNat 64 (M - 24))).mem := by
    simp only [s7, execInstrBr, c_mem_setPC]
    rw [hs6_a16, hs6_x10]
  have hp67 : MemPreservedOutside s6 s7 (M - 8) M :=
    (memPreserved_setMem s6 (M - 8) _ (by omega) (by omega)).mono (le_refl _) (by omega)
      |>.trans (MemPreservedOutside.of_mem_eq hs7_mem _ _)
  have hm8 : s8.mem = s7.mem := mem_exec_ADDI s7 _ _ _
  have hp08 : MemPreservedOutside s s8 (M - 24) M :=
    ((hp3.mono (le_refl _) (by omega)).trans (hp36.mono (by omega) (by omega))).trans
      ((hp67.mono (by omega) (le_refl _)).trans (MemPreservedOutside.of_mem_eq hm8 _ _))
  -- DetRun for steps 0..7
  have hr0 : DetRun oracle (submission.image .commit) s 1 s1 1 0 :=
    DetRun.step1 (hfetch 0 (by omega) s (by simpa using hpc)) rfl
  have hr1 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (hfetch 1 (by omega) s1 hs1_pc) (ordinaryStep_LD s1 .x6 .x18 soff (by
      rw [hs1_reg .x18 (by decide), haddr_soff]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hr2 : DetRun oracle (submission.image .commit) s2 1 s3 1 0 :=
    DetRun.step1 (hfetch 2 (by omega) s2 hs2_pc) (ordinaryStep_SD s2 .x10 .x6 (0#12) (by
      rw [hs2_a0]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hr3 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (hfetch 3 (by omega) s3 hs3_pc) (ordinaryStep_LD s3 .x6 .x18 soff8 (by
      rw [reg_exec_SD, hs2_reg .x18 (by decide), hs1_reg .x18 (by decide), haddr_soff8]
      exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hr4 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (hfetch 4 (by omega) s4 hs4_pc) rfl
  have hr5 : DetRun oracle (submission.image .commit) s5 1 s6 1 0 :=
    DetRun.step1 (hfetch 5 (by omega) s5 hs5_pc) (ordinaryStep_SD s5 .x10 .x6 (8#12) (by
      rw [hs5_a8]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hr6 : DetRun oracle (submission.image .commit) s6 1 s7 1 0 :=
    DetRun.step1 (hfetch 6 (by omega) s6 hs6_pc) (ordinaryStep_SD s6 .x10 .x10 (16#12) (by
      rw [hs6_a16]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hr7 : DetRun oracle (submission.image .commit) s7 1 s8 1 0 :=
    DetRun.step1 (hfetch 7 (by omega) s7 hs7_pc) rfl
  have hr07 : DetRun oracle (submission.image .commit) s 8 s8 8 0 :=
    ((((((hr0.trans hr1).trans hr2).trans hr3).trans hr4).trans hr5).trans hr6).trans hr7
  -- Verify Call-0 96-byte input buffer at `M - 24` in `s8`
  have hin0 : readBuffer s8 (M - 24) 96 = leafCall0Input iFin (salts iFin) (msg iFin) := by
    rw [readBuffer_call0]
    have h16 : readBuffer s8 (M - 24) 16 = salt121Word16 (salts iFin) := by
      rw [readBuffer_salt16 s8 (M - 24) (by omega)]
      have hw0 : s8.getMem (BitVec.ofNat 64 (M - 24)) = (rawSalts iFin).extractLsb' 0 64 := by
        rw [show s8.getMem (BitVec.ofNat 64 (M - 24)) = s7.getMem (BitVec.ofNat 64 (M - 24)) by simp [MachineState.getMem, hm8],
          hp67.getMem_eq (by omega) (by omega) (Or.inl (by omega)),
          hp36.getMem_eq (by omega) (by omega) (Or.inl (by omega))]
        simp only [MachineState.getMem, hs3_mem]; exact MachineState.getMem_setMem_eq
      have hw1 : s8.getMem (BitVec.ofNat 64 (M - 24 + 8)) = (rawSalts iFin).extractLsb' 64 64 &&& maskSalt121Word := by
        rw [show M - 24 + 8 = M - 16 by omega,
          show s8.getMem (BitVec.ofNat 64 (M - 16)) = s7.getMem (BitVec.ofNat 64 (M - 16)) by simp [MachineState.getMem, hm8],
          hp67.getMem_eq (by omega) (by omega) (Or.inl (by omega))]
        simp only [MachineState.getMem, hs6_mem]; exact MachineState.getMem_setMem_eq
      rw [hw0, hw1]
      exact (salt121Word16_from_raw16 (rawSalts iFin)).symm
    have htag : readBuffer s8 (M - 24 + 16) 8 = leafTag iFin := by
      rw [show M - 24 + 16 = M - 8 by omega, readBuffer_word s8 (M - 8) (by omega),
        show s8.getMem (BitVec.ofNat 64 (M - 8)) = s7.getMem (BitVec.ofNat 64 (M - 8)) by simp [MachineState.getMem, hm8]]
      change s7.mem (BitVec.ofNat 64 (M - 8)) = leafTag iFin
      rw [hs7_mem]
      change (s6.setMem (BitVec.ofNat 64 (M - 8)) (BitVec.ofNat 64 (M - 24))).getMem (BitVec.ofNat 64 (M - 8)) = leafTag iFin
      rw [MachineState.getMem_setMem_eq]
      unfold leafTag; dsimp only [iFin]; exact congrArg (BitVec.ofNat 64) (by omega)
    have hmsg0 : readBuffer s8 (M - 24 + 24) 72 = (msg iFin).extractLsb' 0 576 := by
      rw [show M - 24 + 24 = M by omega, hp08.readBuffer_eq (by omega) (by omega)]
      have h := read_serialized_slice s (msg iFin) M 0 72 (fun j hj => by simpa using hmsg j (by omega))
      simpa using h
    rw [h16, htag, hmsg0]; rfl
  -- Step 8: Call 0 ECALL -> writes `cv0` at `M + 40`
  let cv0 : Digest := c96 (leafCall0Input iFin (salts iFin) (msg iFin))
  let s9 := writeBits s8 (BitVec.ofNat 64 (M + 40)) cv0
  have hr8 : DetRun oracle (submission.image .commit) s8 1 s9 8 1 :=
    DetRun.compress_eq h768 (hfetch 8 (by omega) s8 hs8_pc)
      ((hs8_reg .x5 (by decide) (by decide) (by decide)).trans hx5)
      ((hs8_reg .x11 (by decide) (by decide) (by decide)).trans hx11)
      ((hs8_reg .x13 (by decide) (by decide) (by decide)).trans hx13)
      (M - 24) (M + 40) hs8_x10 hs8_x12 (by omega) (by omega) (by omega) (by omega) cv0 (by rw [hin0])
  have hs9_pc : s9.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 9)) := pc_step_idx s8 _ hs8_pc
  have hp89 : MemPreservedOutside s8 s9 (M + 40) (M + 72) := memPreserved_writeBits s8 (M + 40) cv0 (by omega)
  -- Steps 9..11: Call 1 (`x10 = M + 40`, `x12 = M + 104`) -> writes `cv1` at `M + 104`
  let s10 := execInstrBr s9 (.ADDI .x10 .x10 (64#12))
  let s11 := execInstrBr s10 (.ADDI .x12 .x10 (64#12))
  have hs10_pc : s10.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 10)) := pc_step_idx s9 _ hs9_pc
  have hs11_pc : s11.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 11)) := pc_step_idx s10 _ hs10_pc
  have hs10_x10 : s10.getReg .x10 = BitVec.ofNat 64 (M + 40) := by
    simp only [s10, s9, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), writeBits_register, hs8_x10,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs11_x10 : s11.getReg .x10 = BitVec.ofNat 64 (M + 40) := by
    simp only [s11, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs10_x10]
  have hs11_x12 : s11.getReg .x12 = BitVec.ofNat 64 (M + 104) := by
    simp only [s11, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs10_x10,
      add_signExtend12_ofNat_small _ 64 (by omega)]
  have hs11_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s11.getReg r = s.getReg r := fun r h6 h10 h12 => by
    simp only [s11, s10, s9, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10), writeBits_register]
    exact hs8_reg r h6 h10 h12
  have hm11 : s11.mem = s9.mem := (mem_exec_ADDI s10 _ _ _).trans (mem_exec_ADDI s9 _ _ _)
  have hin1 : readBuffer s11 (M + 40) 96 = leafCall1Input cv0 (msg iFin) := by
    rw [readBuffer_of_mem_eq hm11, readBuffer_chain96, writeBits_readBuffer_digest]
    have hmsg1 : readBuffer s9 (M + 40 + 32) 64 = (msg iFin).extractLsb' 576 512 := by
      rw [show M + 40 + 32 = M + 72 by omega, hp89.readBuffer_eq (by omega) (by omega),
        hp08.readBuffer_eq (by omega) (by omega)]
      have h := read_serialized_slice s (msg iFin) (M + 72) 72 64 (fun j hj => by
        rw [show M + 72 + j = M + (72 + j) by omega]; exact hmsg (72 + j) (by omega))
      simpa using h
    rw [hmsg1]; rfl
  let cv1 : Digest := c96 (leafCall1Input cv0 (msg iFin))
  let s12 := writeBits s11 (BitVec.ofNat 64 (M + 104)) cv1
  have hr9 : DetRun oracle (submission.image .commit) s9 1 s10 1 0 :=
    DetRun.step1 (hfetch 9 (by omega) s9 hs9_pc) rfl
  have hr10 : DetRun oracle (submission.image .commit) s10 1 s11 1 0 :=
    DetRun.step1 (hfetch 10 (by omega) s10 hs10_pc) rfl
  have hr11 : DetRun oracle (submission.image .commit) s11 1 s12 8 1 :=
    DetRun.compress_eq h768 (hfetch 11 (by omega) s11 hs11_pc)
      ((hs11_reg .x5 (by decide) (by decide) (by decide)).trans hx5)
      ((hs11_reg .x11 (by decide) (by decide) (by decide)).trans hx11)
      ((hs11_reg .x13 (by decide) (by decide) (by decide)).trans hx13)
      (M + 40) (M + 104) hs11_x10 hs11_x12 (by omega) (by omega) (by omega) (by omega) cv1 (by rw [hin1])
  have hs12_pc : s12.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 12)) := pc_step_idx s11 _ hs11_pc
  have hp912 : MemPreservedOutside s9 s12 (M + 104) (M + 136) :=
    (MemPreservedOutside.of_mem_eq hm11 _ _).trans (memPreserved_writeBits s11 (M + 104) cv1 (by omega))
  -- Steps 12..14: Call 2 (`x10 = M + 104`, `x12 = M + 160`) -> writes `cv2` at `M + 160`
  let s13 := execInstrBr s12 (.ADDI .x10 .x10 (64#12))
  let s14 := execInstrBr s13 (.ADDI .x12 .x10 (56#12))
  have hs13_pc : s13.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 13)) := pc_step_idx s12 _ hs12_pc
  have hs14_pc : s14.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 14)) := pc_step_idx s13 _ hs13_pc
  have hs13_x10 : s13.getReg .x10 = BitVec.ofNat 64 (M + 104) := by
    simp only [s13, s12, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), writeBits_register, hs11_x10,
      add_signExtend12_ofNat_small _ 64 (by omega)]
  have hs14_x10 : s14.getReg .x10 = BitVec.ofNat 64 (M + 104) := by
    simp only [s14, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs13_x10]
  have hs14_x12 : s14.getReg .x12 = BitVec.ofNat 64 (M + 160) := by
    simp only [s14, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs13_x10,
      add_signExtend12_ofNat_small _ 56 (by omega)]
  have hs14_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s14.getReg r = s.getReg r := fun r h6 h10 h12 => by
    simp only [s14, s13, s12, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10), writeBits_register]
    exact hs11_reg r h6 h10 h12
  have hm14 : s14.mem = s12.mem := (mem_exec_ADDI s13 _ _ _).trans (mem_exec_ADDI s12 _ _ _)
  have hin2 : readBuffer s14 (M + 104) 96 = leafCall2Input cv1 (msg iFin) := by
    rw [readBuffer_of_mem_eq hm14, readBuffer_chain96, writeBits_readBuffer_digest]
    have hmsg2 : readBuffer s12 (M + 104 + 32) 64 = (msg iFin).extractLsb' 1088 512 := by
      rw [show M + 104 + 32 = M + 136 by omega, hp912.readBuffer_eq (by omega) (by omega),
        hp89.readBuffer_eq (by omega) (by omega), hp08.readBuffer_eq (by omega) (by omega)]
      have h := read_serialized_slice s (msg iFin) (M + 136) 136 64 (fun j hj => by
        rw [show M + 136 + j = M + (136 + j) by omega]; exact hmsg (136 + j) (by omega))
      simpa using h
    rw [hmsg2]; rfl
  let cv2 : Digest := c96 (leafCall2Input cv1 (msg iFin))
  let s15 := writeBits s14 (BitVec.ofNat 64 (M + 160)) cv2
  have hr12 : DetRun oracle (submission.image .commit) s12 1 s13 1 0 :=
    DetRun.step1 (hfetch 12 (by omega) s12 hs12_pc) rfl
  have hr13 : DetRun oracle (submission.image .commit) s13 1 s14 1 0 :=
    DetRun.step1 (hfetch 13 (by omega) s13 hs13_pc) rfl
  have hr14 : DetRun oracle (submission.image .commit) s14 1 s15 8 1 :=
    DetRun.compress_eq h768 (hfetch 14 (by omega) s14 hs14_pc)
      ((hs14_reg .x5 (by decide) (by decide) (by decide)).trans hx5)
      ((hs14_reg .x11 (by decide) (by decide) (by decide)).trans hx11)
      ((hs14_reg .x13 (by decide) (by decide) (by decide)).trans hx13)
      (M + 104) (M + 160) hs14_x10 hs14_x12 (by omega) (by omega) (by omega) (by omega) cv2 (by rw [hin2])
  have hs15_pc : s15.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 15)) := pc_step_idx s14 _ hs14_pc
  have hp1215 : MemPreservedOutside s12 s15 (M + 160) (M + 192) :=
    (MemPreservedOutside.of_mem_eq hm14 _ _).trans (memPreserved_writeBits s14 (M + 160) cv2 (by omega))
  -- Steps 15..17: Call 3 (`x10 = M + 160`, `x12 = H`) -> writes `leafDigest` at `H`
  let s16 := execInstrBr s15 (.ADDI .x10 .x10 (56#12))
  let s17 := execInstrBr s16 (.ADDI .x12 .x23 hoff)
  have hs16_pc : s16.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 16)) := pc_step_idx s15 _ hs15_pc
  have hs17_pc : s17.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 17)) := pc_step_idx s16 _ hs16_pc
  have hs16_x10 : s16.getReg .x10 = BitVec.ofNat 64 (M + 160) := by
    simp only [s16, s15, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), writeBits_register, hs14_x10,
      add_signExtend12_ofNat_small _ 56 (by omega)]
  have hs17_x10 : s17.getReg .x10 = BitVec.ofNat 64 (M + 160) := by
    simp only [s17, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs16_x10]
  have hs17_x12 : s17.getReg .x12 = BitVec.ofNat 64 H := by
    have hr23 : s16.getReg .x23 = s.getReg .x23 := by
      simp only [s16, s15, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 .x23 (by decide),
        writeBits_register]
      exact hs14_reg .x23 (by decide) (by decide) (by decide)
    simp only [s17, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hr23, haddr_hoff]
  have hs17_reg : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s17.getReg r = s.getReg r := fun r h6 h10 h12 => by
    simp only [s17, s16, s15, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x12 r (Ne.symm h12), getReg_setReg_ne' .x10 r (Ne.symm h10), writeBits_register]
    exact hs14_reg r h6 h10 h12
  have hm17 : s17.mem = s15.mem := (mem_exec_ADDI s16 _ _ _).trans (mem_exec_ADDI s15 _ _ _)
  have hin3 : readBuffer s17 (M + 160) 96 = leafCall3Input cv2 (msg iFin) := by
    rw [readBuffer_of_mem_eq hm17, readBuffer_chain96, writeBits_readBuffer_digest]
    have hmsg3 : readBuffer s15 (M + 160 + 32) 64 = (msg iFin).extractLsb' 1536 512 := by
      rw [show M + 160 + 32 = M + 192 by omega, hp1215.readBuffer_eq (by omega) (by omega),
        hp912.readBuffer_eq (by omega) (by omega), hp89.readBuffer_eq (by omega) (by omega),
        hp08.readBuffer_eq (by omega) (by omega)]
      have h := read_serialized_slice s (msg iFin) (M + 192) 192 64 (fun j hj => by
        rw [show M + 192 + j = M + (192 + j) by omega]; exact hmsg (192 + j) (by omega))
      simpa using h
    rw [hmsg3]; rfl
  let d3 : Digest := leafDigest c96 iFin (salts iFin) (msg iFin)
  let s18 := writeBits s17 (BitVec.ofNat 64 H) d3
  have hr15 : DetRun oracle (submission.image .commit) s15 1 s16 1 0 :=
    DetRun.step1 (hfetch 15 (by omega) s15 hs15_pc) rfl
  have hr16 : DetRun oracle (submission.image .commit) s16 1 s17 1 0 :=
    DetRun.step1 (hfetch 16 (by omega) s16 hs16_pc) rfl
  have hr17 : DetRun oracle (submission.image .commit) s17 1 s18 8 1 :=
    DetRun.compress_eq h768 (hfetch 17 (by omega) s17 hs17_pc)
      ((hs17_reg .x5 (by decide) (by decide) (by decide)).trans hx5)
      ((hs17_reg .x11 (by decide) (by decide) (by decide)).trans hx11)
      ((hs17_reg .x13 (by decide) (by decide) (by decide)).trans hx13)
      (M + 160) H hs17_x10 hs17_x12 (by omega) (by unfold H gapOffset; omega)
      (by omega) (by omega) d3 (by rw [hin3]; rfl)
  have hs18_pc : s18.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * k + 18)) := pc_step_idx s17 _ hs17_pc
  have hp1518 : MemPreservedOutside s15 s18 H (H + 32) :=
    (MemPreservedOutside.of_mem_eq hm17 _ _).trans (memPreserved_writeBits s17 H d3 (by omega))
  -- Steps 18..20: mask `d3` at `H` to `mask238 d3 = nodeVal c96 msg salts 0 idx`
  obtain ⟨s21, hr1820, hs21_pc, hs21_reg, hs21_val, hp1821⟩ :=
    commit_mask238_step oracle s18 (26 + 21 * k + 18) H (by unfold H gapOffset; omega) (by omega)
      hs18_pc ((writeBits_register s17 _ d3 .x12).trans hs17_x12)
      ((writeBits_register s17 _ d3 .x27).trans ((hs17_reg .x27 (by decide) (by decide) (by decide)).trans hx27))
      (fun st hst => hfetch 18 (by omega) st hst)
      (fun st hst => hfetch 19 (by omega) st hst)
      (fun st hst => hfetch 20 (by omega) st hst)
  have hr_all : DetRun oracle (submission.image .commit) s 21 s21 49 4 := by
    have h := (((((((((hr07.trans hr8).trans hr9).trans hr10).trans hr11).trans hr12).trans hr13).trans hr14).trans hr15).trans hr16).trans hr17
    exact h.trans hr1820
  refine ⟨s21, hr_all, hs21_pc.trans (congrArg (BitVec.ofNat 64) (by omega)), ?_, ?_, ?_, ?_⟩
  · intro r h6 h10 h12
    exact (hs21_reg r h6).trans ((writeBits_register s17 _ d3 r).trans (hs17_reg r h6 h10 h12))
  · rw [hs21_reg .x10 (by decide), writeBits_register, hs17_x10]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [hs21_val, writeBits_readBuffer_digest]
    exact nodeVal_level0 c96 msg salts idx hidx
  · intro q hq houtM houtH
    have hp_msg : MemPreservedOutside s s15 (M - 24) (M + 192) :=
      ((hp08.mono (le_refl _) (by omega)).trans (hp89.mono (by omega) (by omega))).trans
        ((hp912.mono (by omega) (by omega)).trans (hp1215.mono (by omega) (le_refl _)))
    have hp_td : MemPreservedOutside s15 s21 H (H + 32) :=
      hp1518.trans (hp1821.mono (by omega) (le_refl _))
    exact (hp_td q hq houtH).trans (hp_msg q hq houtM)

/-! ### 3. One 32-Leaf Chunk (`words 26..700`: `675` steps, `1571` cycles, `128` calls) -/

private theorem commit_leaf_chunk (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (rawSalts : Index → BitVec 128)
    (c : Nat) (hc : c < 524288) (sc : MachineState)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 26))
    (hx5 : sc.getReg .x5 = 0#64) (hx11 : sc.getReg .x11 = 96#64) (hx13 : sc.getReg .x13 = 0#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (32 * c) - 96))
    (hx18 : sc.getReg .x18 = BitVec.ofNat 64 (C_SALTS + 512 * c + 256))
    (hx19 : sc.getReg .x19 = BitVec.ofNat 64 (C_MSG - 96 + 2 ^ 32))
    (hx23 : sc.getReg .x23 = BitVec.ofNat 64 (C_TD + 1536 * c + 768))
    (hx27 : sc.getReg .x27 = mask238Word) (hx28 : sc.getReg .x28 = maskSalt121Word)
    (hmsg : ∀ k (hk : k < 32), ∀ j < 256,
      sc.getByte (BitVec.ofNat 64 (C_MSG + 256 * (32 * c + k) + j)) =
        (msg ⟨32 * c + k, by unfold LENGTH LOG_LENGTH; omega⟩).extractLsb' (8 * j) 8)
    (hsalt : ∀ k (hk : k < 32),
      readBuffer sc (C_SALTS + 16 * (32 * c + k)) 16 =
        rawSalts ⟨32 * c + k, by unfold LENGTH LOG_LENGTH; omega⟩) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let salts : Index → Salt121 := fun i => (rawSalts i).extractLsb' 0 121
    ∃ s',
      DetRun oracle (submission.image .commit) sc 675 s' 1571 128 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < 524288 then 26 else 701)) ∧
      (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x18 → r ≠ .x23 → s'.getReg r = sc.getReg r) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (32 * (c + 1)) - 96) ∧
      s'.getReg .x18 = BitVec.ofNat 64 (C_SALTS + 512 * (c + 1) + 256) ∧
      s'.getReg .x23 = BitVec.ofNat 64 (C_TD + 1536 * (c + 1) + 768) ∧
      (∀ k < 32, readBuffer s' (C_TD + gapOffset (32 * c + k)) 32 = nodeVal c96 msg salts 0 (32 * c + k)) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < C_MSG + 256 * (32 * c) - 24 ∨ C_MSG + 256 * (32 * (c + 1)) ≤ q) →
        (∀ k < 32, q < C_TD + gapOffset (32 * c + k) ∨ C_TD + gapOffset (32 * c + k) + 32 ≤ q) →
        s'.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let salts : Index → Salt121 := fun i => (rawSalts i).extractLsb' 0 121
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_SALTS : C_SALTS = 5905584096 := rfl
  have hind : ∀ m ≤ 32,
      ∃ sm,
        DetRun oracle (submission.image .commit) sc (21 * m) sm (49 * m) (4 * m) ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (26 + 21 * m)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → sm.getReg r = sc.getReg r) ∧
        sm.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (32 * c + m) - 96) ∧
        (∀ k < m, readBuffer sm (C_TD + gapOffset (32 * c + k)) 32 = nodeVal c96 msg salts 0 (32 * c + k)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (q < C_MSG + 256 * (32 * c) - 24 ∨ C_MSG + 256 * (32 * c + m) ≤ q) →
          (∀ k < m, q < C_TD + gapOffset (32 * c + k) ∨ C_TD + gapOffset (32 * c + k) + 32 ≤ q) →
          sm.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨sc, DetRun.refl _ _ _, by simpa using hpc, fun _ _ _ _ => rfl, by simpa using hx10,
        fun _ hk => (Nat.not_lt_zero _ hk).elim, fun _ _ _ _ => rfl⟩
    | succ m ih =>
      obtain ⟨sm, hrunm, hpcm, hregm, hx10m, hnodem, hpresm⟩ := ih (by omega)
      have hmsg_m : ∀ j < 256, sm.getByte (BitVec.ofNat 64 (C_MSG + 256 * (32 * c + m) + j)) =
          (msg ⟨32 * c + m, by unfold LENGTH LOG_LENGTH; omega⟩).extractLsb' (8 * j) 8 := by
        intro j hj
        have h1 : sm.getByte (BitVec.ofNat 64 (C_MSG + 256 * (32 * c + m) + j)) =
            sc.getByte (BitVec.ofNat 64 (C_MSG + 256 * (32 * c + m) + j)) :=
          hpresm _ (by omega) (Or.inr (by omega)) (fun k hk => Or.inl (by omega))
        exact h1.trans (hmsg m (by omega) j hj)
      have hsalt_m : readBuffer sm (C_SALTS + 16 * (32 * c + m)) 16 =
          rawSalts ⟨32 * c + m, by unfold LENGTH LOG_LENGTH; omega⟩ := by
        have h1 : readBuffer sm (C_SALTS + 16 * (32 * c + m)) 16 =
            readBuffer sc (C_SALTS + 16 * (32 * c + m)) 16 := by
          apply readBuffer_congr; intro j hj
          have hgo : ∀ k < m, C_TD + gapOffset (32 * c + k) + 32 ≤ C_SALTS := fun k hk => by
            have hlb := levelBase_bound 0 (by omega)
            have hgb := gapOffset_lt_levelBytes 0 (32 * c + k) (by omega) (by rw [levelSize_0]; omega)
            have htb := treeBytes_eq; have hlb0 : levelBase 0 = 0 := rfl; omega
          exact hpresm _ (by omega) (Or.inr (by omega)) (fun k hk => Or.inr (by have := hgo k hk; omega))
        exact h1.trans (hsalt m (by omega))
      obtain ⟨sm', hstep, hpc', hreg', hx10', hnode', hpres'⟩ :=
        commit_leaf_step h768 oracle msg rawSalts c m hc (by omega) sm hpcm
          ((hregm .x5 (by decide) (by decide) (by decide)).trans hx5)
          ((hregm .x11 (by decide) (by decide) (by decide)).trans hx11)
          ((hregm .x13 (by decide) (by decide) (by decide)).trans hx13)
          hx10m
          ((hregm .x18 (by decide) (by decide) (by decide)).trans hx18)
          ((hregm .x23 (by decide) (by decide) (by decide)).trans hx23)
          ((hregm .x27 (by decide) (by decide) (by decide)).trans hx27)
          ((hregm .x28 (by decide) (by decide) (by decide)).trans hx28)
          hmsg_m hsalt_m
      refine ⟨sm', by simpa [Nat.mul_succ, Nat.add_assoc] using hrunm.trans hstep, hpc',
        fun r h6 h10 h12 => (hreg' r h6 h10 h12).trans (hregm r h6 h10 h12),
        by simpa only [show 32 * c + m + 1 = 32 * c + (m + 1) by omega] using hx10', ?_, ?_⟩
      · intro k hk
        by_cases hkm : k = m
        · subst hkm; exact hnode'
        · have hdisj : gapOffset (32 * c + k) + 32 ≤ gapOffset (32 * c + m) := by
            unfold gapOffset; omega
          have hgo_k : gapOffset (32 * c + k) < 1610612672 := by unfold gapOffset; omega
          have h1 : readBuffer sm' (C_TD + gapOffset (32 * c + k)) 32 =
              readBuffer sm (C_TD + gapOffset (32 * c + k)) 32 := by
            apply readBuffer_congr; intro j hj
            exact hpres' _ (by omega) (Or.inr (by omega)) (Or.inl (by omega))
          exact h1.trans (hnodem k (by omega))
      · intro q hq houtM houtH
        have h1 : sm'.getByte (BitVec.ofNat 64 q) = sm.getByte (BitVec.ofNat 64 q) :=
          hpres' q hq (by omega) (houtH m (by omega))
        have h2 : sm.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q) :=
          hpresm q hq (by omega) (fun k hk => houtH k (by omega))
        exact h1.trans h2
  obtain ⟨s32, hrun32, hpc32, hreg32, hx10_32, hnode32, hpres32⟩ := hind 32 (le_refl _)
  have hpc32' : s32.pc = BitVec.ofNat 64 (0x1000 + 4 * 698) := hpc32
  -- Words 698..700: `ADDI x18, x18, 512; ADDI x23, x23, 1536; BNE x10, x19, leaf_loop`
  let sA := execInstrBr s32 (.ADDI .x18 .x18 (512#12))
  let sB := execInstrBr sA (.ADDI .x23 .x23 (1536#12))
  let sC := execInstrBr sB (.BNE .x10 .x19 (5496#13))
  have hsA_pc : sA.pc = BitVec.ofNat 64 (0x1000 + 4 * 699) := pc_step_idx s32 698 hpc32'
  have hsB_pc : sB.pc = BitVec.ofNat 64 (0x1000 + 4 * 700) := pc_step_idx sA 699 hsA_pc
  have hrA : DetRun oracle (submission.image .commit) s32 1 sA 1 0 :=
    DetRun.step1 (commit_fetch_commitMidInstr s32 698 (by omega) (by omega) hpc32') rfl
  have hrB : DetRun oracle (submission.image .commit) sA 1 sB 1 0 :=
    DetRun.step1 (commit_fetch_commitMidInstr sA 699 (by omega) (by omega) hsA_pc) rfl
  have hrC : DetRun oracle (submission.image .commit) sB 1 sC 1 0 :=
    DetRun.step1 (commit_fetch_commitMidInstr sB 700 (by omega) (by omega) hsB_pc) rfl
  have hmC : sC.mem = s32.mem :=
    (mem_exec_BNE sB _ _ _).trans ((mem_exec_ADDI sA _ _ _).trans (mem_exec_ADDI s32 _ _ _))
  have hsB_x10 : sB.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (32 * (c + 1)) - 96) := by
    simp only [sB, sA, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x23 .x10 (by decide), getReg_setReg_ne' .x18 .x10 (by decide), hx10_32]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hsB_x19 : sB.getReg .x19 = BitVec.ofNat 64 (C_MSG - 96 + 2 ^ 32) := by
    simp only [sB, sA, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x23 .x19 (by decide), getReg_setReg_ne' .x18 .x19 (by decide)]
    exact (hreg32 .x19 (by decide) (by decide) (by decide)).trans hx19
  have hsC_pc : sC.pc = BitVec.ofNat 64 (0x1000 + 4 * (if c + 1 < 524288 then 26 else 701)) := by
    simp only [sC, execInstrBr, hsB_x10, hsB_x19]
    by_cases hlt : c + 1 < 524288
    · have hne : (BitVec.ofNat 64 (C_MSG + 256 * (32 * (c + 1)) - 96) !=
          BitVec.ofNat 64 (C_MSG - 96 + 2 ^ 32)) = true :=
        bne_iff_ne.mpr (bv64_ne_of_nat_ne (by omega) (by omega) (by omega))
      simp only [hlt, ite_true, hne, pc_setPC, hsB_pc, pc_bne_700]
    · have heq : BitVec.ofNat 64 (C_MSG + 256 * (32 * (c + 1)) - 96) =
          BitVec.ofNat 64 (C_MSG - 96 + 2 ^ 32) :=
        congrArg (BitVec.ofNat 64) (by omega)
      simp only [hlt, ite_false, heq, bne_self_eq_false, Bool.false_eq_true, pc_setPC]
      exact pc_step_idx sB 700 hsB_pc
  refine ⟨sC, ((hrun32.trans hrA).trans hrB).trans hrC, hsC_pc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h6 h10 h12 h18 h23
    rw [reg_exec_BNE]
    simp only [sB, sA, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x23 r (Ne.symm h23), getReg_setReg_ne' .x18 r (Ne.symm h18)]
    exact hreg32 r h6 h10 h12
  · rw [reg_exec_BNE]; exact hsB_x10
  · rw [reg_exec_BNE]
    simp only [sB, sA, execInstrBr, MachineState.getReg_setPC,
      getReg_setReg_ne' .x23 .x18 (by decide),
      MachineState.getReg_setReg_eq (by decide : Reg.x18 ≠ .x0),
      hreg32 .x18 (by decide) (by decide) (by decide), hx18,
      add_signExtend12_ofNat_small _ 512 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · rw [reg_exec_BNE]
    simp only [sB, sA, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x23 ≠ .x0),
      getReg_setReg_ne' .x18 .x23 (by decide),
      hreg32 .x23 (by decide) (by decide) (by decide), hx23,
      add_signExtend12_ofNat_small _ 1536 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · intro k hk
    rw [readBuffer_of_mem_eq hmC]; exact hnode32 k hk
  · intro q hq houtM houtH
    rw [getByte_of_mem_eq hmC]
    exact hpres32 q hq (by omega) houtH

/-! ### 4. Full Phase 1 (`524,288` chunks = `353,894,400` steps, `823,656,448` cycles, `67,108,864` calls) -/

theorem commit_phase1 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (rawSalts : Index → BitVec 128) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 26))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx5 : s0.getReg .x5 = 0#64) (hx9 : s0.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 (C_MSG - 96))
    (hx11 : s0.getReg .x11 = 96#64) (hx13 : s0.getReg .x13 = 0#64)
    (hx18 : s0.getReg .x18 = BitVec.ofNat 64 (C_SALTS + 256))
    (hx19 : s0.getReg .x19 = BitVec.ofNat 64 (C_MSG - 96 + 2 ^ 32))
    (hx23 : s0.getReg .x23 = BitVec.ofNat 64 (C_TD + 768))
    (hx26 : s0.getReg .x26 = BitVec.ofNat 64 C_CMT)
    (hx27 : s0.getReg .x27 = mask238Word) (hx28 : s0.getReg .x28 = maskSalt121Word)
    (hmsg : ∀ (i : Index), ∀ j < 256,
      s0.getByte (BitVec.ofNat 64 (C_MSG + 256 * i.val + j)) = (msg i).extractLsb' (8 * j) 8)
    (hsalt : ∀ i : Index, readBuffer s0 (C_TD + saltOff i) 16 = rawSalts i) :
    let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
    let salts : Index → Salt121 := fun i => (rawSalts i).extractLsb' 0 121
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 353894400 s1 823656448 67108864 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 701) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      s1.getReg .x27 = mask238Word ∧
      (∀ idx < levelSize 0, readBuffer s1 (C_TD + levelBase 0 + gapOffset idx) 32 = nodeVal c96 msg salts 0 idx) ∧
      (∀ q < levelSize 0 / 2, ∀ j < 32,
        s1.getByte (BitVec.ofNat 64 (C_TD + levelBase 0 + 96 * q + 64 + j)) =
          s0.getByte (BitVec.ofNat 64 (C_TD + levelBase 0 + 96 * q + 64 + j))) ∧
      MemPreservedOutside s0 s1 (C_MSG - 24) (C_TD + levelBytes 0) := by
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  let salts : Index → Salt121 := fun i => (rawSalts i).extractLsb' 0 121
  have hC_MSG : C_MSG = 4096 := rfl
  have hC_TD : C_TD = 4294971424 := rfl
  have hC_SALTS : C_SALTS = 5905584096 := rfl
  have hind : ∀ n ≤ 524288,
      ∃ sn,
        DetRun oracle (submission.image .commit) s0 (675 * n) sn (1571 * n) (128 * n) ∧
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 524288 then 26 else 701)) ∧
        (∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → r ≠ .x18 → r ≠ .x23 → sn.getReg r = s0.getReg r) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_MSG + 256 * (32 * n) - 96) ∧
        sn.getReg .x18 = BitVec.ofNat 64 (C_SALTS + 512 * n + 256) ∧
        sn.getReg .x23 = BitVec.ofNat 64 (C_TD + 1536 * n + 768) ∧
        (∀ idx < 32 * n, readBuffer sn (C_TD + gapOffset idx) 32 = nodeVal c96 msg salts 0 idx) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (q < C_MSG - 24 ∨ C_MSG + 256 * (32 * n) ≤ q) →
          (q < C_TD ∨ C_TD + 1536 * n ≤ q) →
          sn.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) ∧
        (∀ q < levelSize 0 / 2, ∀ j < 32,
          sn.getByte (BitVec.ofNat 64 (C_TD + 96 * q + 64 + j)) =
            s0.getByte (BitVec.ofNat 64 (C_TD + 96 * q + 64 + j))) := by
    intro n hn; induction n with
    | zero =>
      exact ⟨s0, DetRun.refl _ _ _, by simpa only [show (0 : Nat) < 524288 by decide, ite_true] using hpc,
        fun _ _ _ _ _ _ => rfl, by simpa using hx10, by simpa using hx18, by simpa using hx23,
        fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hpcn, hregn, hx10n, hx18n, hx23n, hnoden, hpresn, hgapn⟩ := ih (by omega)
      have hpcn' : sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 26) := by
        simpa only [show n < 524288 by omega, ite_true] using hpcn
      have hmsg_n : ∀ k (hk : k < 32), ∀ j < 256,
          sn.getByte (BitVec.ofNat 64 (C_MSG + 256 * (32 * n + k) + j)) =
            (msg ⟨32 * n + k, by unfold LENGTH LOG_LENGTH; omega⟩).extractLsb' (8 * j) 8 := by
        intro k hk j hj
        have h1 := hpresn (C_MSG + 256 * (32 * n + k) + j) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
        exact h1.trans (hmsg ⟨32 * n + k, by unfold LENGTH LOG_LENGTH; omega⟩ j hj)
      have hsalt_n : ∀ k (hk : k < 32), readBuffer sn (C_SALTS + 16 * (32 * n + k)) 16 =
          rawSalts ⟨32 * n + k, by unfold LENGTH LOG_LENGTH; omega⟩ := by
        intro k hk
        have h1 : readBuffer sn (C_SALTS + 16 * (32 * n + k)) 16 =
            readBuffer s0 (C_SALTS + 16 * (32 * n + k)) 16 := by
          apply readBuffer_congr; intro j hj
          exact hpresn _ (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        have haddr : C_SALTS + 16 * (32 * n + k) = C_TD + saltOff ⟨32 * n + k, by unfold LENGTH LOG_LENGTH; omega⟩ := by
          unfold saltOff; dsimp only; rw [C_SALTS_eq]; omega
        rw [h1, haddr]
        exact hsalt ⟨32 * n + k, by unfold LENGTH LOG_LENGTH; omega⟩
      obtain ⟨sn', hchunk, hpc', hreg', hx10', hx18', hx23', hnode', hpres'⟩ :=
        commit_leaf_chunk h768 oracle msg rawSalts n (by omega) sn hpcn'
          ((hregn .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5)
          ((hregn .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11)
          ((hregn .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13)
          hx10n hx18n
          ((hregn .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx19)
          hx23n
          ((hregn .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27)
          ((hregn .x28 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx28)
          hmsg_n hsalt_n
      refine ⟨sn', by simpa [Nat.mul_succ, Nat.add_assoc] using hrunn.trans hchunk, hpc',
        fun r h6 h10 h12 h18 h23 => (hreg' r h6 h10 h12 h18 h23).trans (hregn r h6 h10 h12 h18 h23),
        hx10', hx18', hx23', ?_, ?_, ?_⟩
      · intro idx hidx
        by_cases hlt : idx < 32 * n
        · have hdisj : ∀ k < 32, gapOffset idx + 32 ≤ gapOffset (32 * n + k) := fun k _ => by
            unfold gapOffset; omega
          have hgo_idx : gapOffset idx < 1610612672 := by unfold gapOffset; omega
          have h1 : readBuffer sn' (C_TD + gapOffset idx) 32 = readBuffer sn (C_TD + gapOffset idx) 32 := by
            apply readBuffer_congr; intro j hj
            exact hpres' _ (by omega) (Or.inr (by omega)) (fun k hk => Or.inl (by have := hdisj k hk; omega))
          exact h1.trans (hnoden idx hlt)
        · have hk : idx - 32 * n < 32 := by omega
          simpa only [show 32 * n + (idx - 32 * n) = idx by omega] using hnode' (idx - 32 * n) hk
      · intro q hq houtM houtH
        have hgo : ∀ k < 32, C_TD + 1536 * n ≤ C_TD + gapOffset (32 * n + k) ∧
            C_TD + gapOffset (32 * n + k) + 32 ≤ C_TD + 1536 * (n + 1) := fun k hk => by
          rw [gapOffset_block]; unfold gapOffset; omega
        have h1 : sn'.getByte (BitVec.ofNat 64 q) = sn.getByte (BitVec.ofNat 64 q) :=
          hpres' q hq (by omega) (fun k hk => by have := hgo k hk; omega)
        have h2 : sn.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q) :=
          hpresn q hq (by omega) (by omega)
        exact h1.trans h2
      · intro q hq j hj
        have hgap_ne : ∀ k < 32,
            C_TD + 96 * q + 64 + j < C_TD + gapOffset (32 * n + k) ∨
            C_TD + gapOffset (32 * n + k) + 32 ≤ C_TD + 96 * q + 64 + j := fun k _ => by
          unfold gapOffset
          rcases Nat.even_or_odd (32 * n + k) with ⟨p, hp⟩ | ⟨p, hp⟩ <;> omega
        have h1 : sn'.getByte (BitVec.ofNat 64 (C_TD + 96 * q + 64 + j)) =
            sn.getByte (BitVec.ofNat 64 (C_TD + 96 * q + 64 + j)) :=
          hpres' _ (by rw [levelSize_0] at hq; omega) (Or.inr (by rw [levelSize_0] at hq; omega)) hgap_ne
        exact h1.trans (hgapn q hq j hj)
  obtain ⟨s1, hrun1, hpc1, hreg1, _, _, _, hnode1, hpres1, hgap1⟩ := hind 524288 (le_refl _)
  have hlb0 : levelBase 0 = 0 := rfl
  have hbytes0 : levelBytes 0 = 1536 * 524288 := by decide
  refine ⟨s1, hrun1, by simpa only [Nat.lt_irrefl, ite_false] using hpc1,
    (hreg1 .x2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx2,
    (hreg1 .x5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx5,
    (hreg1 .x9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx9,
    (hreg1 .x11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx11,
    (hreg1 .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13,
    (hreg1 .x26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26,
    (hreg1 .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27, ?_, ?_, ?_⟩
  · intro idx hidx
    rw [hlb0, Nat.add_zero]
    rw [levelSize_0] at hidx
    exact hnode1 idx (by omega)
  · intro q hq j hj
    rw [hlb0, Nat.add_zero]
    exact hgap1 q hq j hj
  · intro addr hbd hout
    rw [hbytes0] at hout
    exact hpres1 addr hbd (by omega) (by omega)

end CommitGolfCandidate
