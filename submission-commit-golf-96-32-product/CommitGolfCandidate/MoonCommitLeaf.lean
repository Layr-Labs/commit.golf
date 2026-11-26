import CommitGolfCandidate.MoonCommitBase

/-! Exact RV64IM execution proof for Phase 1 of the `commit` image:
the 128-lane unrolled zero-zeroing 8B-overlap running-`a0` leaf loop (`words 29..2208`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-- Exact register invariants preserved across the entire 128-lane leaf loop. -/
structure LeafLoopRegs (s : MachineState) (blk k : Nat) : Prop where
  pc   : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k))
  x2   : s.getReg .x2 = BitVec.ofNat 64 C_DB
  x5   : s.getReg .x5 = 0#64
  x9   : s.getReg .x9 = BitVec.ofNat 64 C_TD
  x10  : s.getReg .x10 = BitVec.ofNat 64 (4000 + 256 * (128 * blk + k))
  x11  : s.getReg .x11 = 96#64
  x13  : s.getReg .x13 = 0#64
  x18  : s.getReg .x18 = BitVec.ofNat 64 (C_TD + saltsOff + 1024 + 2048 * blk)
  x19  : s.getReg .x19 = BitVec.ofNat 64 (4000 + 2 ^ 32)
  x20  : s.getReg .x20 = BitVec.ofNat 64 4096
  x21  : s.getReg .x21 = BitVec.ofNat 64 2048
  x23  : s.getReg .x23 = BitVec.ofNat 64 (C_TD + 2048 + 4096 * blk)
  x26  : s.getReg .x26 = BitVec.ofNat 64 C_CMT

/-- One leaf lane `k < 128` inside block `blk < 131072`: 17 steps, 45 cycles, 4 compression calls.
Writes only inside `[M_i - 24, M_i + 192)` and `[C_TD + 32*i, C_TD + 32*i + 32)`, storing the exact
`leafDigest` at `C_TD + 32*i` while preserving all future leaves, all prior L0 digests, and all salts. -/
theorem commit_leaf_lane (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128)
    (blk k : Nat) (hblk : blk < 131072) (hk : k < 128)
    (s : MachineState) (hregs : LeafLoopRegs s blk k)
    (hi : 128 * blk + k < LENGTH)
    (hmsg : ∀ j < 256, s.getByte (BitVec.ofNat 64 (4096 + 256 * (128 * blk + k) + j)) =
      (msg ⟨128 * blk + k, hi⟩).extractLsb' (8 * j) 8)
    (hsalt : readBuffer s (C_TD + saltsOff + 16 * (128 * blk + k)) 16 = salts ⟨128 * blk + k, hi⟩) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 17 s' 45 4 ∧
      LeafLoopRegs s' blk (k + 1) ∧
      readBuffer s' (C_TD + 32 * (128 * blk + k)) 32 =
        leafDigest (fun x => oracle.compression (x.cast h768.symm))
          ⟨128 * blk + k, hi⟩ (salts ⟨128 * blk + k, hi⟩) (msg ⟨128 * blk + k, hi⟩) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < 4072 + 256 * (128 * blk + k) ∨ 4096 + 256 * (128 * blk + k) + 192 ≤ q) →
        (q < C_TD + 32 * (128 * blk + k) ∨ C_TD + 32 * (128 * blk + k) + 32 ≤ q) →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hso := saltsOff_eq
  let i : Nat := 128 * blk + k
  let idx : Index := ⟨i, hi⟩
  let M : Nat := 4096 + 256 * i
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hi_lt : i < 16777216 := hi
  -- Steps 0..6: addi a0,+72; ld/sd salt0; ld/sd salt1; sd a0,16(a0); addi a2,a0,64
  let s0 := execInstrBr s (.ADDI .x10 .x10 (72#12))
  let soff := BitVec.ofNat 12 ((4096 - 1024 + 16 * k) % 4096)
  let soff8 := BitVec.ofNat 12 ((4096 - 1016 + 16 * k) % 4096)
  let hoff := BitVec.ofNat 12 ((4096 - 2048 + 32 * k) % 4096)
  let s1 := execInstrBr s0 (.LD .x6 .x18 soff)
  let s2 := execInstrBr s1 (.SD .x10 .x6 (0#12))
  let s3 := execInstrBr s2 (.LD .x6 .x18 soff8)
  let s4 := execInstrBr s3 (.SD .x10 .x6 (8#12))
  let s5 := execInstrBr s4 (.SD .x10 .x10 (16#12))
  let s6 := execInstrBr s5 (.ADDI .x12 .x10 (64#12))
  have hs0_pc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 1)) := pc_step_idx s _ hregs.pc
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 2)) := pc_step_idx s0 _ hs0_pc
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 3)) := pc_step_idx s1 _ hs1_pc
  have hs3_pc : s3.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 4)) := pc_step_idx s2 _ hs2_pc
  have hs4_pc : s4.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 5)) := pc_step_idx s3 _ hs3_pc
  have hs5_pc : s5.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 6)) := pc_step_idx s4 _ hs4_pc
  have hs6_pc : s6.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 7)) := pc_step_idx s5 _ hs5_pc
  have hs0_reg_other : ∀ r : Reg, r ≠ .x10 → s0.getReg r = s.getReg r := fun r hr => by
    simp only [s0, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm hr)]
  have hs2_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → s2.getReg r = s.getReg r := fun r h6 h10 => by
    rw [reg_exec_SD]
    have h1 : s1.getReg r = s0.getReg r := by
      simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm h6)]
    exact h1.trans (hs0_reg_other r h10)
  have hs5_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → s5.getReg r = s.getReg r := fun r h6 h10 => by
    rw [reg_exec_SD, reg_exec_SD]
    have h3 : s3.getReg r = s2.getReg r := by
      simp only [s3, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 r (Ne.symm h6)]
    exact h3.trans (hs2_reg_other r h6 h10)
  have hs6_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s6.getReg r = s.getReg r :=
    fun r h6 h10 h12 => by
      have h6' : s6.getReg r = s5.getReg r := by
        simp only [s6, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
      exact h6'.trans (hs5_reg_other r h6 h10)
  have hs0_a0 : s0.getReg .x10 = BitVec.ofNat 64 (M - 24) := by
    simp only [s0, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0),
      hregs.x10, add_signExtend12_ofNat_small _ 72 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs1_a0 : s1.getReg .x10 = BitVec.ofNat 64 (M - 24) := by
    simp only [s1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x10 (by decide), hs0_a0]
  have hs2_a0 : s2.getReg .x10 = BitVec.ofNat 64 (M - 24) := (reg_exec_SD s1 _ _ _ .x10).trans hs1_a0
  have hs3_a0 : s3.getReg .x10 = BitVec.ofNat 64 (M - 24) := by
    simp only [s3, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x10 (by decide), hs2_a0]
  have hs4_a0 : s4.getReg .x10 = BitVec.ofNat 64 (M - 24) := (reg_exec_SD s3 _ _ _ .x10).trans hs3_a0
  have hs5_a0 : s5.getReg .x10 = BitVec.ofNat 64 (M - 24) := (reg_exec_SD s4 _ _ _ .x10).trans hs4_a0
  have hs6_a0 : s6.getReg .x10 = BitVec.ofNat 64 (M - 24) := by
    simp only [s6, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs5_a0]
  have hsalt_addr0 : s0.getReg .x18 + signExtend12 soff = BitVec.ofNat 64 (C_TD + saltsOff + 16 * i) := by
    rw [hs0_reg_other .x18 (by decide), hregs.x18, add_signExtend12_soff _ k hk (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hsalt_addr1 : s2.getReg .x18 + signExtend12 soff8 = BitVec.ofNat 64 (C_TD + saltsOff + 16 * i + 8) := by
    rw [hs2_reg_other .x18 (by decide) (by decide), hregs.x18, add_signExtend12_soff8 _ k hk (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have ha2 : s1.getReg .x10 + signExtend12 (0#12) = BitVec.ofNat 64 (M - 24) := by
    rw [hs1_a0, add_signExtend12_ofNat_small _ 0 (by omega), Nat.add_zero]
  have ha4 : s3.getReg .x10 + signExtend12 (8#12) = BitVec.ofNat 64 (M - 16) := by
    rw [hs3_a0, add_signExtend12_ofNat_small _ 8 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have ha5 : s4.getReg .x10 + signExtend12 (16#12) = BitVec.ofNat 64 (M - 8) := by
    rw [hs4_a0, add_signExtend12_ofNat_small _ 16 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hstep0 : DetRun oracle (submission.image .commit) s 1 s0 1 0 :=
    DetRun.step1 (commit_fetch_leaf s k 0 hk (by omega) (by simpa using hregs.pc)) rfl
  have hstep1 : DetRun oracle (submission.image .commit) s0 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_leaf s0 k 1 hk (by omega) hs0_pc)
      (ordinaryStep_LD s0 .x6 .x18 soff (by
        rw [hsalt_addr0]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hstep2 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_leaf s1 k 2 hk (by omega) hs1_pc)
      (ordinaryStep_SD s1 .x10 .x6 (0#12) (by
        rw [ha2]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hstep3 : DetRun oracle (submission.image .commit) s2 1 s3 1 0 :=
    DetRun.step1 (commit_fetch_leaf s2 k 3 hk (by omega) hs2_pc)
      (ordinaryStep_LD s2 .x6 .x18 soff8 (by
        rw [hsalt_addr1]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hstep4 : DetRun oracle (submission.image .commit) s3 1 s4 1 0 :=
    DetRun.step1 (commit_fetch_leaf s3 k 4 hk (by omega) hs3_pc)
      (ordinaryStep_SD s3 .x10 .x6 (8#12) (by
        rw [ha4]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hstep5 : DetRun oracle (submission.image .commit) s4 1 s5 1 0 :=
    DetRun.step1 (commit_fetch_leaf s4 k 5 hk (by omega) hs4_pc)
      (ordinaryStep_SD s4 .x10 .x10 (16#12) (by
        rw [ha5]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
  have hstep6 : DetRun oracle (submission.image .commit) s5 1 s6 1 0 :=
    DetRun.step1 (commit_fetch_leaf s5 k 6 hk (by omega) hs5_pc) rfl
  -- Memory after steps 0..6: only [M-24, M) written (with salt16 ++ leafTag)
  have hs0_mem : s0.mem = s.mem := mem_exec_ADDI s .x10 .x10 (72#12)
  have hs1_mem : s1.mem = s.mem := (mem_exec_LD s0 .x6 .x18 soff).trans hs0_mem
  have hs3_mem : s3.mem = s2.mem := mem_exec_LD s2 .x6 .x18 soff8
  have hs6_mem : s6.mem = s5.mem := mem_exec_ADDI s5 .x12 .x10 (64#12)
  have hs2_mem : s2.mem = (s1.setMem (BitVec.ofNat 64 (M - 24)) (s1.getReg .x6)).mem := by
    simp only [s2, execInstrBr, ha2, c_mem_setPC]
  have hs4_mem : s4.mem = (s3.setMem (BitVec.ofNat 64 (M - 16)) (s3.getReg .x6)).mem := by
    simp only [s4, execInstrBr, ha4, c_mem_setPC]
  have hs5_mem : s5.mem = (s4.setMem (BitVec.ofNat 64 (M - 8)) (s4.getReg .x10)).mem := by
    simp only [s5, execInstrBr, ha5, c_mem_setPC]
  have hs6_pres : MemPreservedOutside s s6 (M - 24) M := by
    have h01 : MemPreservedOutside s s1 (M - 24) M := MemPreservedOutside.of_mem_eq hs1_mem _ _
    have h12 : MemPreservedOutside s1 s2 (M - 24) M :=
      ((memPreserved_setMem s1 (M - 24) (s1.getReg .x6) (by omega) (by omega)).mono (by omega) (by omega)).trans
        (MemPreservedOutside.of_mem_eq hs2_mem _ _)
    have h23 : MemPreservedOutside s2 s3 (M - 24) M := MemPreservedOutside.of_mem_eq hs3_mem _ _
    have h34 : MemPreservedOutside s3 s4 (M - 24) M :=
      ((memPreserved_setMem s3 (M - 16) (s3.getReg .x6) (by omega) (by omega)).mono (by omega) (by omega)).trans
        (MemPreservedOutside.of_mem_eq hs4_mem _ _)
    have h45 : MemPreservedOutside s4 s5 (M - 24) M :=
      ((memPreserved_setMem s4 (M - 8) (s4.getReg .x10) (by omega) (by omega)).mono (by omega) (by omega)).trans
        (MemPreservedOutside.of_mem_eq hs5_mem _ _)
    have h56 : MemPreservedOutside s5 s6 (M - 24) M := MemPreservedOutside.of_mem_eq hs6_mem _ _
    exact ((((h01.trans h12).trans h23).trans h34).trans h45).trans h56
  -- Verify Call 0 input at [M - 24, M + 72) equals `leafCall0Input idx (salts idx) (msg idx)`
  have hs6_in0 : readBuffer s6 (M - 24) 96 = leafCall0Input idx (salts idx) (msg idx) := by
    rw [readBuffer_call0]
    have hmsg0 : readBuffer s6 (M - 24 + 24) 72 = (msg idx).extractLsb' 0 576 := by
      have hm : M - 24 + 24 = M := by omega
      rw [hm]
      have hr := read_serialized_slice s6 (msg idx) M 0 72 (fun j hj => by
        rw [hs6_pres (M + j) (by omega) (by omega), hmsg j (by omega)]
        simp only [Nat.zero_add]; rfl)
      simpa using hr
    have htag0 : readBuffer s6 (M - 24 + 16) 8 = leafTag idx := by
      have hm : M - 24 + 16 = M - 8 := by omega
      rw [hm, readBuffer_word s6 (M - 8) (by omega)]
      simp only [MachineState.getMem, hs6_mem, hs5_mem]
      change (s4.setMem (BitVec.ofNat 64 (M - 8)) (s4.getReg .x10)).getMem (BitVec.ofNat 64 (M - 8)) = leafTag idx
      rw [MachineState.getMem_setMem_eq, hs4_a0]
      unfold leafTag
      dsimp only [idx]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have hsalt0 : readBuffer s6 (M - 24) 16 = salts idx := by
      rw [readBuffer_salt16 s6 (M - 24) (by omega)]
      rw [← hsalt, readBuffer_salt16 s (C_TD + saltsOff + 16 * i) (by omega)]
      have hs1_x6 : s1.getReg .x6 = s.getMem (BitVec.ofNat 64 (C_TD + saltsOff + 16 * i)) := by
        simp only [s1, execInstrBr, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hsalt_addr0, MachineState.getMem, hs0_mem]
      have hs3_x6 : s3.getReg .x6 = s.getMem (BitVec.ofNat 64 (C_TD + saltsOff + 16 * i + 8)) := by
        have hne_salt : BitVec.ofNat 64 (C_TD + saltsOff + 16 * i + 8) ≠ BitVec.ofNat 64 (M - 24) :=
          bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
        simp only [s3, execInstrBr, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hsalt_addr1, MachineState.getMem, hs2_mem]
        change (s1.setMem (BitVec.ofNat 64 (M - 24)) (s1.getReg .x6)).getMem
            (BitVec.ofNat 64 (C_TD + saltsOff + 16 * i + 8)) = _
        rw [MachineState.getMem_setMem_ne hne_salt]
        simp only [MachineState.getMem, hs1_mem]
      have hne16 : BitVec.ofNat 64 (M - 24) ≠ BitVec.ofNat 64 (M - 16) :=
        bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      have hne8 : BitVec.ofNat 64 (M - 24) ≠ BitVec.ofNat 64 (M - 8) :=
        bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      have hne16_8 : BitVec.ofNat 64 (M - 16) ≠ BitVec.ofNat 64 (M - 8) :=
        bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      have hlo : s6.getMem (BitVec.ofNat 64 (M - 24)) = s.getMem (BitVec.ofNat 64 (C_TD + saltsOff + 16 * i)) := by
        simp only [MachineState.getMem, hs6_mem, hs5_mem]
        change (s4.setMem (BitVec.ofNat 64 (M - 8)) (s4.getReg .x10)).getMem (BitVec.ofNat 64 (M - 24)) = _
        rw [MachineState.getMem_setMem_ne hne8]
        simp only [MachineState.getMem, hs4_mem]
        change (s3.setMem (BitVec.ofNat 64 (M - 16)) (s3.getReg .x6)).getMem (BitVec.ofNat 64 (M - 24)) = _
        rw [MachineState.getMem_setMem_ne hne16]
        simp only [MachineState.getMem, hs3_mem, hs2_mem]
        change (s1.setMem (BitVec.ofNat 64 (M - 24)) (s1.getReg .x6)).getMem (BitVec.ofNat 64 (M - 24)) = _
        rw [MachineState.getMem_setMem_eq, hs1_x6]; rfl
      have hhi : s6.getMem (BitVec.ofNat 64 (M - 24 + 8)) = s.getMem (BitVec.ofNat 64 (C_TD + saltsOff + 16 * i + 8)) := by
        have hm16 : M - 24 + 8 = M - 16 := by omega
        rw [hm16]
        simp only [MachineState.getMem, hs6_mem, hs5_mem]
        change (s4.setMem (BitVec.ofNat 64 (M - 8)) (s4.getReg .x10)).getMem (BitVec.ofNat 64 (M - 16)) = _
        rw [MachineState.getMem_setMem_ne hne16_8]
        simp only [MachineState.getMem, hs4_mem]
        change (s3.setMem (BitVec.ofNat 64 (M - 16)) (s3.getReg .x6)).getMem (BitVec.ofNat 64 (M - 16)) = _
        rw [MachineState.getMem_setMem_eq, hs3_x6]; rfl
      rw [hlo, hhi]
    rw [hmsg0, htag0, hsalt0]; rfl
  -- Call 0 (word 7): writes cv0 to M + 40
  let cv0 := c96 (leafCall0Input idx (salts idx) (msg idx))
  let s7 := writeBits s6 (BitVec.ofNat 64 (M + 40)) cv0
  have hs7_pc : s7.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 8)) := pc_step_idx s6 _ hs6_pc
  have hstep7 : DetRun oracle (submission.image .commit) s6 1 s7 8 1 := by
    have ha2 : s6.getReg .x12 = BitVec.ofNat 64 (M + 40) := by
      simp only [s6, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs5_a0,
        add_signExtend12_ofNat_small _ 64 (by omega)]
      exact congrArg (BitVec.ofNat 64) (by omega)
    exact DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s6)
      (commit_fetch_leaf s6 k 7 hk (by omega) hs6_pc)
      (by rw [hs6_reg_other .x5 (by decide) (by decide) (by decide)]; exact hregs.x5)
      (by rw [hs6_reg_other .x11 (by decide) (by decide) (by decide)]; exact hregs.x11)
      (by rw [hs6_reg_other .x13 (by decide) (by decide) (by decide)]; exact hregs.x13)
      (M - 24) (M + 40) hs6_a0 ha2
      (by omega) (by omega) (by omega) (by omega) cv0 (by rw [hs6_in0])
  -- Steps 8..9 + Call 1 (word 10): writes cv1 to M + 104
  let s8 := execInstrBr s7 (.ADDI .x10 .x10 (64#12))
  let s9 := execInstrBr s8 (.ADDI .x12 .x10 (64#12))
  let cv1 := c96 (leafCall1Input cv0 (msg idx))
  let s10 := writeBits s9 (BitVec.ofNat 64 (M + 104)) cv1
  have hs8_pc : s8.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 9)) := pc_step_idx s7 _ hs7_pc
  have hs9_pc : s9.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 10)) := pc_step_idx s8 _ hs8_pc
  have hs10_pc : s10.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 11)) := pc_step_idx s9 _ hs9_pc
  have hs9_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s9.getReg r = s.getReg r :=
    fun r h6 h10 h12 => by
      have h9 : s9.getReg r = s8.getReg r := by
        simp only [s9, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
      have h8 : s8.getReg r = s7.getReg r := by
        simp only [s8, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm h10)]
      exact ((h9.trans h8).trans (writeBits_register s6 _ cv0 r)).trans (hs6_reg_other r h6 h10 h12)
  have hs7_pres : MemPreservedOutside s s7 (M - 24) (M + 72) :=
    (hs6_pres.mono (le_refl _) (by omega)).trans
      ((memPreserved_writeBits s6 (M + 40) cv0 (by omega)).mono (by omega) (by omega))
  have hmem9 : s9.mem = s7.mem :=
    (mem_exec_ADDI s8 .x12 .x10 (64#12)).trans (mem_exec_ADDI s7 .x10 .x10 (64#12))
  have hs9_in1 : readBuffer s9 (M + 40) 96 = leafCall1Input cv0 (msg idx) := by
    rw [readBuffer_of_mem_eq hmem9, read_leaf_query]
    have hcv : readBuffer s7 (M + 40) 32 = cv0 := writeBits_readBuffer_digest s6 (M + 40) cv0
    have hm1 : readBuffer s7 (M + 40 + 32) 64 = (msg idx).extractLsb' 576 512 := by
      have ha : M + 40 + 32 = M + 72 := by omega
      rw [ha]
      have hr := read_serialized_slice s7 (msg idx) (M + 72) 72 64 (fun j hj => by
        rw [hs7_pres (M + 72 + j) (by omega) (by omega), show M + 72 + j = M + (72 + j) by omega,
          hmsg (72 + j) (by omega)])
      simpa using hr
    rw [hcv, hm1]; rfl
  have hstep8 : DetRun oracle (submission.image .commit) s7 1 s8 1 0 :=
    DetRun.step1 (commit_fetch_leaf s7 k 8 hk (by omega) hs7_pc) rfl
  have hstep9 : DetRun oracle (submission.image .commit) s8 1 s9 1 0 :=
    DetRun.step1 (commit_fetch_leaf s8 k 9 hk (by omega) hs8_pc) rfl
  have hs7_a0 : s7.getReg .x10 = BitVec.ofNat 64 (M - 24) :=
    (writeBits_register s6 _ cv0 .x10).trans hs6_a0
  have hs8_a0 : s8.getReg .x10 = BitVec.ofNat 64 (M + 40) := by
    simp only [s8, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs7_a0,
      add_signExtend12_ofNat_small _ 64 (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hs9_a0 : s9.getReg .x10 = BitVec.ofNat 64 (M + 40) := by
    simp only [s9, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs8_a0]
  have hstep10 : DetRun oracle (submission.image .commit) s9 1 s10 8 1 := by
    have ha2 : s9.getReg .x12 = BitVec.ofNat 64 (M + 104) := by
      simp only [s9, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs8_a0,
        add_signExtend12_ofNat_small _ 64 (by omega)]
    exact DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s9)
      (commit_fetch_leaf s9 k 10 hk (by omega) hs9_pc)
      (by rw [hs9_reg_other .x5 (by decide) (by decide) (by decide)]; exact hregs.x5)
      (by rw [hs9_reg_other .x11 (by decide) (by decide) (by decide)]; exact hregs.x11)
      (by rw [hs9_reg_other .x13 (by decide) (by decide) (by decide)]; exact hregs.x13)
      (M + 40) (M + 104) hs9_a0 ha2
      (by omega) (by omega) (by omega) (by omega) cv1 (by rw [hs9_in1])
  -- Steps 11..12 + Call 2 (word 13): writes cv2 to M + 160
  let s11 := execInstrBr s10 (.ADDI .x10 .x10 (64#12))
  let s12 := execInstrBr s11 (.ADDI .x12 .x10 (56#12))
  let cv2 := c96 (leafCall2Input cv1 (msg idx))
  let s13 := writeBits s12 (BitVec.ofNat 64 (M + 160)) cv2
  have hs11_pc : s11.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 12)) := pc_step_idx s10 _ hs10_pc
  have hs12_pc : s12.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 13)) := pc_step_idx s11 _ hs11_pc
  have hs13_pc : s13.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 14)) := pc_step_idx s12 _ hs12_pc
  have hs12_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s12.getReg r = s.getReg r :=
    fun r h6 h10 h12 => by
      have h12' : s12.getReg r = s11.getReg r := by
        simp only [s12, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
      have h11' : s11.getReg r = s10.getReg r := by
        simp only [s11, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm h10)]
      exact ((h12'.trans h11').trans (writeBits_register s9 _ cv1 r)).trans (hs9_reg_other r h6 h10 h12)
  have hs10_pres : MemPreservedOutside s s10 (M - 24) (M + 136) :=
    ((hs7_pres.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmem9 _ _)).trans
      ((memPreserved_writeBits s9 (M + 104) cv1 (by omega)).mono (by omega) (by omega))
  have hmem12 : s12.mem = s10.mem :=
    (mem_exec_ADDI s11 .x12 .x10 (56#12)).trans (mem_exec_ADDI s10 .x10 .x10 (64#12))
  have hs12_in2 : readBuffer s12 (M + 104) 96 = leafCall2Input cv1 (msg idx) := by
    rw [readBuffer_of_mem_eq hmem12, read_leaf_query]
    have hcv : readBuffer s10 (M + 104) 32 = cv1 := writeBits_readBuffer_digest s9 (M + 104) cv1
    have hm2 : readBuffer s10 (M + 104 + 32) 64 = (msg idx).extractLsb' 1088 512 := by
      have ha : M + 104 + 32 = M + 136 := by omega
      rw [ha]
      have hr := read_serialized_slice s10 (msg idx) (M + 136) 136 64 (fun j hj => by
        rw [hs10_pres (M + 136 + j) (by omega) (by omega), show M + 136 + j = M + (136 + j) by omega,
          hmsg (136 + j) (by omega)])
      simpa using hr
    rw [hcv, hm2]; rfl
  have hstep11 : DetRun oracle (submission.image .commit) s10 1 s11 1 0 :=
    DetRun.step1 (commit_fetch_leaf s10 k 11 hk (by omega) hs10_pc) rfl
  have hstep12 : DetRun oracle (submission.image .commit) s11 1 s12 1 0 :=
    DetRun.step1 (commit_fetch_leaf s11 k 12 hk (by omega) hs11_pc) rfl
  have hs10_a0 : s10.getReg .x10 = BitVec.ofNat 64 (M + 40) :=
    (writeBits_register s9 _ cv1 .x10).trans hs9_a0
  have hs11_a0 : s11.getReg .x10 = BitVec.ofNat 64 (M + 104) := by
    simp only [s11, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs10_a0,
      add_signExtend12_ofNat_small _ 64 (by omega)]
  have hs12_a0 : s12.getReg .x10 = BitVec.ofNat 64 (M + 104) := by
    simp only [s12, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs11_a0]
  have hstep13 : DetRun oracle (submission.image .commit) s12 1 s13 8 1 := by
    have ha2 : s12.getReg .x12 = BitVec.ofNat 64 (M + 160) := by
      simp only [s12, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hs11_a0,
        add_signExtend12_ofNat_small _ 56 (by omega)]
    exact DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s12)
      (commit_fetch_leaf s12 k 13 hk (by omega) hs12_pc)
      (by rw [hs12_reg_other .x5 (by decide) (by decide) (by decide)]; exact hregs.x5)
      (by rw [hs12_reg_other .x11 (by decide) (by decide) (by decide)]; exact hregs.x11)
      (by rw [hs12_reg_other .x13 (by decide) (by decide) (by decide)]; exact hregs.x13)
      (M + 104) (M + 160) hs12_a0 ha2
      (by omega) (by omega) (by omega) (by omega) cv2 (by rw [hs12_in2])
  -- Steps 14..15 + Call 3 (word 16): writes leafDigest to C_TD + 32 * i
  let s14 := execInstrBr s13 (.ADDI .x10 .x10 (56#12))
  let s15 := execInstrBr s14 (.ADDI .x12 .x23 hoff)
  let cv3 := c96 (leafCall3Input cv2 (msg idx))
  let s16 := writeBits s15 (BitVec.ofNat 64 (C_TD + 32 * i)) cv3
  have hs14_pc : s14.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 15)) := pc_step_idx s13 _ hs13_pc
  have hs15_pc : s15.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * k + 16)) := pc_step_idx s14 _ hs14_pc
  have hs16_pc : s16.pc = BitVec.ofNat 64 (0x1000 + 4 * (29 + 17 * (k + 1))) :=
    (pc_step_idx s15 _ hs15_pc).trans (congrArg (BitVec.ofNat 64) (by omega))
  have hs14_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s14.getReg r = s.getReg r :=
    fun r h6 h10 h12 => by
      have h14' : s14.getReg r = s13.getReg r := by
        simp only [s14, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm h10)]
      exact (h14'.trans (writeBits_register s12 _ cv2 r)).trans (hs12_reg_other r h6 h10 h12)
  have hs15_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s15.getReg r = s.getReg r :=
    fun r h6 h10 h12 => by
      have h15' : s15.getReg r = s14.getReg r := by
        simp only [s15, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 r (Ne.symm h12)]
      exact h15'.trans (hs14_reg_other r h6 h10 h12)
  have hs16_reg_other : ∀ r : Reg, r ≠ .x6 → r ≠ .x10 → r ≠ .x12 → s16.getReg r = s.getReg r :=
    fun r h6 h10 h12 => (writeBits_register s15 _ cv3 r).trans (hs15_reg_other r h6 h10 h12)
  have hs13_pres : MemPreservedOutside s s13 (M - 24) (M + 192) :=
    ((hs10_pres.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hmem12 _ _)).trans
      ((memPreserved_writeBits s12 (M + 160) cv2 (by omega)).mono (by omega) (by omega))
  have hmem15 : s15.mem = s13.mem :=
    (mem_exec_ADDI s14 .x12 .x23 hoff).trans (mem_exec_ADDI s13 .x10 .x10 (56#12))
  have hs15_in3 : readBuffer s15 (M + 160) 96 = leafCall3Input cv2 (msg idx) := by
    rw [readBuffer_of_mem_eq hmem15, read_leaf_query]
    have hcv : readBuffer s13 (M + 160) 32 = cv2 := writeBits_readBuffer_digest s12 (M + 160) cv2
    have hm3 : readBuffer s13 (M + 160 + 32) 64 = (msg idx).extractLsb' 1536 512 := by
      have ha : M + 160 + 32 = M + 192 := by omega
      rw [ha]
      have hr := read_serialized_slice s13 (msg idx) (M + 192) 192 64 (fun j hj => by
        rw [hs13_pres (M + 192 + j) (by omega) (by omega), show M + 192 + j = M + (192 + j) by omega,
          hmsg (192 + j) (by omega)])
      simpa using hr
    rw [hcv, hm3]; rfl
  have hstep14 : DetRun oracle (submission.image .commit) s13 1 s14 1 0 :=
    DetRun.step1 (commit_fetch_leaf s13 k 14 hk (by omega) hs13_pc) rfl
  have hstep15 : DetRun oracle (submission.image .commit) s14 1 s15 1 0 :=
    DetRun.step1 (commit_fetch_leaf s14 k 15 hk (by omega) hs14_pc) rfl
  have hs13_a0 : s13.getReg .x10 = BitVec.ofNat 64 (M + 104) :=
    (writeBits_register s12 _ cv2 .x10).trans hs12_a0
  have hs14_a0 : s14.getReg .x10 = BitVec.ofNat 64 (M + 160) := by
    simp only [s14, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs13_a0,
      add_signExtend12_ofNat_small _ 56 (by omega)]
  have hs15_a0 : s15.getReg .x10 = BitVec.ofNat 64 (M + 160) := by
    simp only [s15, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x12 .x10 (by decide), hs14_a0]
  have hs15_a2 : s15.getReg .x12 = BitVec.ofNat 64 (C_TD + 32 * i) := by
    have hx23 : s14.getReg .x23 = BitVec.ofNat 64 (C_TD + 2048 + 4096 * blk) :=
      (hs14_reg_other .x23 (by decide) (by decide) (by decide)).trans hregs.x23
    simp only [s15, execInstrBr, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq (by decide : Reg.x12 ≠ .x0), hx23]
    rw [add_signExtend12_hoff _ k hk (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hstep16 : DetRun oracle (submission.image .commit) s15 1 s16 8 1 :=
    DetRun.compress_eq h768 (oracle := oracle) (img := submission.image .commit) (s := s15)
      (commit_fetch_leaf s15 k 16 hk (by omega) hs15_pc)
      (by rw [hs15_reg_other .x5 (by decide) (by decide) (by decide)]; exact hregs.x5)
      (by rw [hs15_reg_other .x11 (by decide) (by decide) (by decide)]; exact hregs.x11)
      (by rw [hs15_reg_other .x13 (by decide) (by decide) (by decide)]; exact hregs.x13)
      (M + 160) (C_TD + 32 * i) hs15_a0 hs15_a2
      (by omega) (by omega) (by omega) (by omega) cv3 (by rw [hs15_in3])
  -- Compose all 17 steps
  have hall : DetRun oracle (submission.image .commit) s 17 s16 45 4 := by
    have h0_7 := ((((((hstep0.trans hstep1).trans hstep2).trans hstep3).trans hstep4).trans hstep5).trans hstep6).trans hstep7
    have h8_16 := (((((((hstep8.trans hstep9).trans hstep10).trans hstep11).trans hstep12).trans hstep13).trans hstep14).trans hstep15).trans hstep16
    simpa using h0_7.trans h8_16
  refine ⟨s16, hall, ?_, ?_, ?_⟩
  · refine ⟨hs16_pc,
      (hs16_reg_other .x2 (by decide) (by decide) (by decide)).trans hregs.x2,
      (hs16_reg_other .x5 (by decide) (by decide) (by decide)).trans hregs.x5,
      (hs16_reg_other .x9 (by decide) (by decide) (by decide)).trans hregs.x9,
      ?_,
      (hs16_reg_other .x11 (by decide) (by decide) (by decide)).trans hregs.x11,
      (hs16_reg_other .x13 (by decide) (by decide) (by decide)).trans hregs.x13,
      (hs16_reg_other .x18 (by decide) (by decide) (by decide)).trans hregs.x18,
      (hs16_reg_other .x19 (by decide) (by decide) (by decide)).trans hregs.x19,
      (hs16_reg_other .x20 (by decide) (by decide) (by decide)).trans hregs.x20,
      (hs16_reg_other .x21 (by decide) (by decide) (by decide)).trans hregs.x21,
      (hs16_reg_other .x23 (by decide) (by decide) (by decide)).trans hregs.x23,
      (hs16_reg_other .x26 (by decide) (by decide) (by decide)).trans hregs.x26⟩
    rw [writeBits_register, hs15_a0]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · exact writeBits_readBuffer_digest s15 (C_TD + 32 * i) cv3
  · intro q hq houtM houtL0
    have hp16 := memPreserved_writeBits s15 (C_TD + 32 * i) cv3 (by omega) q hq (by simpa using houtL0)
    have hp13 := hs13_pres q hq (by omega)
    exact (hp16.trans (getByte_of_mem_eq hmem15 _)).trans hp13

/-- One 128-lane block (without tail) for any `blk < 131072`: 2,176 steps, 5,760 cycles, 512 calls. -/
private theorem commit_leaf_block128 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128)
    (blk : Nat) (hblk : blk < 131072) (sb : MachineState)
    (hr : LeafLoopRegs sb blk 0)
    (hmb : ∀ (idx : Nat) (hidx : idx < LENGTH), 128 * blk ≤ idx → ∀ j < 256,
      sb.getByte (BitVec.ofNat 64 (4096 + 256 * idx + j)) = (msg ⟨idx, hidx⟩).extractLsb' (8 * j) 8)
    (hsb : ∀ i : Index, readBuffer sb (C_TD + saltsOff + 16 * i.val) 16 = salts i) :
    ∃ se,
      DetRun oracle (submission.image .commit) sb 2176 se 5760 512 ∧
      LeafLoopRegs se blk 128 ∧
      (∀ k < 128, readBuffer se (C_TD + 32 * (128 * blk + k)) 32 =
        nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 0 (128 * blk + k)) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (q < 4072 + 256 * (128 * blk) ∨ 4096 + 256 * (128 * (blk + 1)) ≤ q) →
        (q < C_TD + 32 * (128 * blk) ∨ C_TD + 32 * (128 * (blk + 1)) ≤ q) →
        se.getByte (BitVec.ofNat 64 q) = sb.getByte (BitVec.ofNat 64 q)) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hso := saltsOff_eq
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  have hind : ∀ m ≤ 128,
      ∃ sm,
        DetRun oracle (submission.image .commit) sb (17 * m) sm (45 * m) (4 * m) ∧
        LeafLoopRegs sm blk m ∧
        (∀ k < m, readBuffer sm (C_TD + 32 * (128 * blk + k)) 32 =
          nodeVal c96 msg salts 0 (128 * blk + k)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (q < 4072 + 256 * (128 * blk) ∨ 4096 + 256 * (128 * blk + m) ≤ q) →
          (q < C_TD + 32 * (128 * blk) ∨ C_TD + 32 * (128 * blk + m) ≤ q) →
          sm.getByte (BitVec.ofNat 64 q) = sb.getByte (BitVec.ofNat 64 q)) := by
    intro m hm; induction m with
    | zero => exact ⟨sb, DetRun.refl _ _ _, hr, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ _ => rfl⟩
    | succ m ih =>
      obtain ⟨sm, hrunm, hrm, hdigm, hpresm⟩ := ih (by omega)
      have hi : 128 * blk + m < LENGTH := by omega
      have hmsgm : ∀ j < 256, sm.getByte (BitVec.ofNat 64 (4096 + 256 * (128 * blk + m) + j)) =
          (msg ⟨128 * blk + m, hi⟩).extractLsb' (8 * j) 8 := by
        intro j hj
        rw [hpresm (4096 + 256 * (128 * blk + m) + j) (by omega) (by omega) (by omega)]
        exact hmb (128 * blk + m) hi (by omega) j hj
      have hsaltm : readBuffer sm (C_TD + saltsOff + 16 * (128 * blk + m)) 16 = salts ⟨128 * blk + m, hi⟩ := by
        rw [← hsb ⟨128 * blk + m, hi⟩]
        apply readBuffer_congr; intro j hj
        exact hpresm (C_TD + saltsOff + 16 * (128 * blk + m) + j) (by omega) (by omega) (by omega)
      obtain ⟨sn, hrun1, hrn, hdign, hpresn⟩ :=
        commit_leaf_lane h768 oracle msg salts blk m hblk (by omega) sm hrm hi hmsgm hsaltm
      refine ⟨sn, by simpa [Nat.mul_succ] using hrunm.trans hrun1, hrn, ?_, ?_⟩
      · intro k hk
        by_cases hkm : k = m
        · subst hkm; simpa [nodeVal, nodeValFromLeaves, hi] using hdign
        · rw [← hdigm k (by omega)]
          apply readBuffer_congr; intro j hj
          exact hpresn (C_TD + 32 * (128 * blk + k) + j) (by omega) (by omega) (by omega)
      · intro q hq hqM hqL0
        exact (hpresn q hq (by omega) (by omega)).trans (hpresm q hq (by omega) (by omega))
  simpa [Nat.mul_add] using hind 128 (le_refl _)

/-- Full Phase 1 leaf loop (`131,072` blocks × `128` lanes = `16,777,216` leaves):
exact `285,736,959` steps, `755,499,007` cycles, `67,108,864` compression calls. -/
theorem commit_phase1 (h768 : COMPRESSION_INPUT_LENGTH = 768)
    (oracle : Oracle) (msg : Message) (salts : Index → Salt128)
    (s0 : MachineState) (hregs0 : LeafLoopRegs s0 0 0)
    (hmsg0 : ∀ (i : Index) (j : Nat), j < 256 →
      s0.getByte (BitVec.ofNat 64 (4096 + 256 * i.val + j)) = (msg i).extractLsb' (8 * j) 8)
    (hsalt0 : ∀ i : Index, readBuffer s0 (C_TD + saltsOff + 16 * i.val) 16 = salts i) :
    ∃ s1,
      DetRun oracle (submission.image .commit) s0 285736959 s1 755499007 67108864 ∧
      s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 2209) ∧
      s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
      s1.getReg .x5 = 0#64 ∧
      s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
      s1.getReg .x11 = 96#64 ∧
      s1.getReg .x13 = 0#64 ∧
      s1.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
      (∀ idx < LENGTH,
        readBuffer s1 (C_TD + 32 * idx) 32 =
          nodeVal (fun x => oracle.compression (x.cast h768.symm)) msg salts 0 idx) ∧
      MemPreservedOutside s0 s1 4072 (C_TD + levelBase 1) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have hso := saltsOff_eq
  let c96 : Comp96 := fun x => oracle.compression (x.cast h768.symm)
  -- Induct over `n ≤ 131071` full loop iterations (each 2180 steps, 5764 cyc, 512 calls)
  have hloop : ∀ n ≤ 131071,
      ∃ sn,
        DetRun oracle (submission.image .commit) s0 (2180 * n) sn (5764 * n) (512 * n) ∧
        LeafLoopRegs sn n 0 ∧
        (∀ idx < 128 * n, readBuffer sn (C_TD + 32 * idx) 32 = nodeVal c96 msg salts 0 idx) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (q < 4072 ∨ 4096 + 256 * (128 * n) ≤ q) →
          (q < C_TD ∨ C_TD + 32 * (128 * n) ≤ q) →
          sn.getByte (BitVec.ofNat 64 q) = s0.getByte (BitVec.ofNat 64 q)) := by
    intro n hn; induction n with
    | zero => exact ⟨s0, DetRun.refl _ _ _, hregs0, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ _ => rfl⟩
    | succ n ih =>
      obtain ⟨sn, hrunn, hrn, hdign, hpresn⟩ := ih (by omega)
      have hmb : ∀ (idx : Nat) (hidx : idx < LENGTH), 128 * n ≤ idx → ∀ j < 256,
          sn.getByte (BitVec.ofNat 64 (4096 + 256 * idx + j)) = (msg ⟨idx, hidx⟩).extractLsb' (8 * j) 8 := by
        intro idx hidx hge j hj
        rw [hpresn (4096 + 256 * idx + j) (by omega) (by omega) (by omega)]
        exact hmsg0 ⟨idx, hidx⟩ j hj
      have hsb : ∀ i : Index, readBuffer sn (C_TD + saltsOff + 16 * i.val) 16 = salts i := by
        intro i; rw [← hsalt0 i]
        have hi : i.val < 16777216 := i.isLt
        apply readBuffer_congr; intro j hj
        exact hpresn (C_TD + saltsOff + 16 * i.val + j) (by omega) (by omega) (by omega)
      obtain ⟨se, hrune, hre, hdige, hprese⟩ := commit_leaf_block128 h768 oracle msg salts n (by omega) sn hrn hmb hsb
      -- Tail 2205..2208: add x23,x23,x20; add x18,x18,x21; beq x10,x19 (+8, NOT taken); jal x0, leaf_loop
      let t1 := execInstrBr se (.ADD .x23 .x23 .x20)
      let t2 := execInstrBr t1 (.ADD .x18 .x18 .x21)
      let t3 := execInstrBr t2 (.BEQ .x10 .x19 (8#13))
      let t4 := execInstrBr t3 (.JAL .x0 (2088436#21))
      have hse_pc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 2205) := hre.pc
      have ht1_pc : t1.pc = BitVec.ofNat 64 (0x1000 + 4 * 2206) := pc_step_idx se 2205 hse_pc
      have ht2_pc : t2.pc = BitVec.ofNat 64 (0x1000 + 4 * 2207) := pc_step_idx t1 2206 ht1_pc
      have ht1 : DetRun oracle (submission.image .commit) se 1 t1 1 0 :=
        DetRun.step1 (commit_fetch_commitMid1Instr se 2205 (by omega) (by omega) hse_pc) rfl
      have ht2 : DetRun oracle (submission.image .commit) t1 1 t2 1 0 :=
        DetRun.step1 (commit_fetch_commitMid1Instr t1 2206 (by omega) (by omega) ht1_pc) rfl
      have ht3 : DetRun oracle (submission.image .commit) t2 1 t3 1 0 :=
        DetRun.step1 (commit_fetch_commitMid1Instr t2 2207 (by omega) (by omega) ht2_pc) rfl
      have ht2_reg_other : ∀ r : Reg, r ≠ .x18 → r ≠ .x23 → t2.getReg r = se.getReg r := fun r h18 h23 => by
        have h2 : t2.getReg r = t1.getReg r := by
          simp only [t2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x18 r (Ne.symm h18)]
        have h1 : t1.getReg r = se.getReg r := by
          simp only [t1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x23 r (Ne.symm h23)]
        exact h2.trans h1
      have ht4_reg_eq_t2 : ∀ r : Reg, t4.getReg r = t2.getReg r := fun r =>
        (reg_exec_JAL0 t3 _ r).trans (reg_exec_BEQ t2 _ _ _ r)
      have hne_end : (t2.getReg .x10 == t2.getReg .x19) = false := by
        rw [ht2_reg_other .x10 (by decide) (by decide), ht2_reg_other .x19 (by decide) (by decide),
          hre.x10, hre.x19, beq_eq_false_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      have ht3_pc : t3.pc = BitVec.ofNat 64 (0x1000 + 4 * 2208) := by
        simp only [t3, execInstrBr, hne_end, Bool.false_eq_true, ite_false, pc_setPC, ht2_pc]
        decide
      have ht4 : DetRun oracle (submission.image .commit) t3 1 t4 1 0 :=
        DetRun.step1 (commit_fetch_commitMid1Instr t3 2208 (by omega) (by omega) ht3_pc) rfl
      have hmem_t4 : t4.mem = se.mem :=
        ((mem_exec_JAL t3 _ _).trans (mem_exec_BEQ t2 _ _ _)).trans
          ((mem_exec_ADD t1 _ _ _).trans (mem_exec_ADD se _ _ _))
      have hrun_next : DetRun oracle (submission.image .commit) s0 (2180 * (n + 1)) t4 (5764 * (n + 1)) (512 * (n + 1)) := by
        have h := ((hrunn.trans hrune).trans (((ht1.trans ht2).trans ht3).trans ht4))
        simpa [Nat.mul_succ, Nat.add_assoc] using h
      refine ⟨t4, hrun_next, ?_, ?_, ?_⟩
      · refine ⟨?_,
          (ht4_reg_eq_t2 .x2).trans ((ht2_reg_other .x2 (by decide) (by decide)).trans hre.x2),
          (ht4_reg_eq_t2 .x5).trans ((ht2_reg_other .x5 (by decide) (by decide)).trans hre.x5),
          (ht4_reg_eq_t2 .x9).trans ((ht2_reg_other .x9 (by decide) (by decide)).trans hre.x9),
          ?_,
          (ht4_reg_eq_t2 .x11).trans ((ht2_reg_other .x11 (by decide) (by decide)).trans hre.x11),
          (ht4_reg_eq_t2 .x13).trans ((ht2_reg_other .x13 (by decide) (by decide)).trans hre.x13),
          ?_,
          (ht4_reg_eq_t2 .x19).trans ((ht2_reg_other .x19 (by decide) (by decide)).trans hre.x19),
          (ht4_reg_eq_t2 .x20).trans ((ht2_reg_other .x20 (by decide) (by decide)).trans hre.x20),
          (ht4_reg_eq_t2 .x21).trans ((ht2_reg_other .x21 (by decide) (by decide)).trans hre.x21),
          ?_,
          (ht4_reg_eq_t2 .x26).trans ((ht2_reg_other .x26 (by decide) (by decide)).trans hre.x26)⟩
        · simp only [t4, execInstrBr, pc_setPC, ht3_pc]; decide
        · rw [ht4_reg_eq_t2 .x10, ht2_reg_other .x10 (by decide) (by decide), hre.x10]
          exact congrArg (BitVec.ofNat 64) (by clear * -; omega)
        · rw [ht4_reg_eq_t2 .x18]
          have h1_x18 : t1.getReg .x18 = se.getReg .x18 := by
            simp only [t1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x23 .x18 (by decide)]
          have h1_x21 : t1.getReg .x21 = se.getReg .x21 := by
            simp only [t1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x23 .x21 (by decide)]
          simp only [t2, execInstrBr, MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide : Reg.x18 ≠ .x0), h1_x18, h1_x21,
            hre.x18, hre.x21, ← BitVec.ofNat_add]
          exact congrArg (BitVec.ofNat 64) (by clear * -; omega)
        · rw [ht4_reg_eq_t2 .x23]
          have h2_x23 : t2.getReg .x23 = t1.getReg .x23 := by
            simp only [t2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x18 .x23 (by decide)]
          rw [h2_x23]
          simp only [t1, execInstrBr, MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide : Reg.x23 ≠ .x0), hre.x23, hre.x20, ← BitVec.ofNat_add]
          exact congrArg (BitVec.ofNat 64) (by clear * -; omega)
      · intro idx hidx
        rw [readBuffer_of_mem_eq hmem_t4]
        by_cases hlt : idx < 128 * n
        · rw [← hdign idx hlt]
          apply readBuffer_congr; intro j hj
          exact hprese (C_TD + 32 * idx + j) (by omega) (by omega) (by omega)
        · have hk : idx - 128 * n < 128 := by omega
          simpa [show 128 * n + (idx - 128 * n) = idx by omega] using hdige (idx - 128 * n) hk
      · intro q hq hqM hqL0
        rw [getByte_of_mem_eq hmem_t4]
        exact (hprese q hq (by omega) (by omega)).trans (hpresn q hq (by omega) (by omega))
  -- Final block `blk = 131071`: BEQ at 2207 IS TAKEN -> jumps to 2209
  obtain ⟨sl, hrunl, hrl, hdigl, hpresl⟩ := hloop 131071 (le_refl _)
  have hmb_last : ∀ (idx : Nat) (hidx : idx < LENGTH), 128 * 131071 ≤ idx → ∀ j < 256,
      sl.getByte (BitVec.ofNat 64 (4096 + 256 * idx + j)) = (msg ⟨idx, hidx⟩).extractLsb' (8 * j) 8 := by
    intro idx hidx hge j hj
    rw [hpresl (4096 + 256 * idx + j) (by omega) (by omega) (by omega)]
    exact hmsg0 ⟨idx, hidx⟩ j hj
  have hsb_last : ∀ i : Index, readBuffer sl (C_TD + saltsOff + 16 * i.val) 16 = salts i := by
    intro i; rw [← hsalt0 i]
    have hi : i.val < 16777216 := i.isLt
    apply readBuffer_congr; intro j hj
    exact hpresl (C_TD + saltsOff + 16 * i.val + j) (by omega) (by omega) (by omega)
  obtain ⟨se, hrune, hre, hdige, hprese⟩ := commit_leaf_block128 h768 oracle msg salts 131071 (by omega) sl hrl hmb_last hsb_last
  let t1 := execInstrBr se (.ADD .x23 .x23 .x20)
  let t2 := execInstrBr t1 (.ADD .x18 .x18 .x21)
  let t3 := execInstrBr t2 (.BEQ .x10 .x19 (8#13))
  have hse_pc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 2205) := hre.pc
  have ht1_pc : t1.pc = BitVec.ofNat 64 (0x1000 + 4 * 2206) := pc_step_idx se 2205 hse_pc
  have ht2_pc : t2.pc = BitVec.ofNat 64 (0x1000 + 4 * 2207) := pc_step_idx t1 2206 ht1_pc
  have ht1 : DetRun oracle (submission.image .commit) se 1 t1 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1Instr se 2205 (by omega) (by omega) hse_pc) rfl
  have ht2 : DetRun oracle (submission.image .commit) t1 1 t2 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1Instr t1 2206 (by omega) (by omega) ht1_pc) rfl
  have ht3 : DetRun oracle (submission.image .commit) t2 1 t3 1 0 :=
    DetRun.step1 (commit_fetch_commitMid1Instr t2 2207 (by omega) (by omega) ht2_pc) rfl
  have ht2_reg_other : ∀ r : Reg, r ≠ .x18 → r ≠ .x23 → t2.getReg r = se.getReg r := fun r h18 h23 => by
    have h2 : t2.getReg r = t1.getReg r := by
      simp only [t2, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x18 r (Ne.symm h18)]
    have h1 : t1.getReg r = se.getReg r := by
      simp only [t1, execInstrBr, MachineState.getReg_setPC, getReg_setReg_ne' .x23 r (Ne.symm h23)]
    exact h2.trans h1
  have ht3_reg_other : ∀ r : Reg, r ≠ .x18 → r ≠ .x23 → t3.getReg r = se.getReg r := fun r h18 h23 =>
    (reg_exec_BEQ t2 _ _ _ r).trans (ht2_reg_other r h18 h23)
  have hmem_t3 : t3.mem = se.mem :=
    (mem_exec_BEQ t2 _ _ _).trans ((mem_exec_ADD t1 _ _ _).trans (mem_exec_ADD se _ _ _))
  have heq_end : (t2.getReg .x10 == t2.getReg .x19) = true := by
    rw [ht2_reg_other .x10 (by decide) (by decide), ht2_reg_other .x19 (by decide) (by decide),
      hre.x10, hre.x19]
    decide
  refine ⟨t3, by simpa using (hrunl.trans hrune).trans ((ht1.trans ht2).trans ht3),
    by simp only [t3, execInstrBr, heq_end, ite_true, pc_setPC, ht2_pc]; decide,
    (ht3_reg_other .x2 (by decide) (by decide)).trans hre.x2,
    (ht3_reg_other .x5 (by decide) (by decide)).trans hre.x5,
    (ht3_reg_other .x9 (by decide) (by decide)).trans hre.x9,
    (ht3_reg_other .x11 (by decide) (by decide)).trans hre.x11,
    (ht3_reg_other .x13 (by decide) (by decide)).trans hre.x13,
    (ht3_reg_other .x26 (by decide) (by decide)).trans hre.x26, ?_, ?_⟩
  · intro idx hidx
    rw [readBuffer_of_mem_eq hmem_t3]
    by_cases hlt : idx < 128 * 131071
    · rw [← hdigl idx hlt]
      apply readBuffer_congr; intro j hj
      exact hprese (C_TD + 32 * idx + j) (by omega) (by omega) (by omega)
    · have hk : idx - 128 * 131071 < 128 := by omega
      simpa [show 128 * 131071 + (idx - 128 * 131071) = idx by omega] using hdige (idx - 128 * 131071) hk
  · intro q hq hout
    rw [getByte_of_mem_eq hmem_t3]
    have hlb1 : levelBase 1 = 536870912 := by decide
    rw [hlb1] at hout
    exact (hprese q hq (by omega) (by omega)).trans (hpresl q hq (by omega) (by omega))

end CommitGolfCandidate
