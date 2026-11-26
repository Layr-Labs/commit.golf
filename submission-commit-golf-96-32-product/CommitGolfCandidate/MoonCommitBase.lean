import CommitGolfCandidate.MoonMemory
import CommitGolfCandidate.MoonHidingCore

/-! Deterministic execution engine (`DetRun`), fast `MachineState` step/copy/arithmetic helpers,
memory-framing lemmas (`MemPreservedOutside`), and exact RV64IM execution proof for Phase 0 of the
`commit` image (setup + `RANDOM(16 * 2^24)` + leaf-loop initialization, words 0..28). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Deterministic `oracle.run` Composition Engine (`DetRun`) -/

/-- `DetRun oracle img s steps s' cyc calls` states that executing `steps` instructions from `s`
deterministically reaches `s'`, charging `cyc` cycles and `calls` public oracle calls, for any
remaining fuel `extra`. Covers both `oracle.run` and `fixedOracleRun` simultaneously. -/
def DetRun (oracle : Oracle) (img : Image) (s : MachineState) (steps : Nat)
    (s' : MachineState) (cyc calls : Nat) : Prop :=
  ∀ extra,
    oracle.run (execute img (steps + extra) s true) =
      (fun p : Execution × Nat => (p.1.charge cyc calls, calls + p.2)) <$>
        oracle.run (execute img extra s' true)

theorem DetRun.refl (oracle : Oracle) (img : Image) (s : MachineState) :
    DetRun oracle img s 0 s 0 0 := by
  intro extra
  have hid : (fun p : Execution × Nat => (p.1.charge 0 0, 0 + p.2)) = id := by
    funext ⟨⟨ex, st, cy, ca⟩, n⟩
    simp only [Execution.charge, Nat.zero_add, id_eq]
  rw [Nat.zero_add, hid]
  exact (id_map _).symm

theorem DetRun.trans {oracle : Oracle} {img : Image} {s1 s2 s3 : MachineState}
    {n1 n2 c1 c2 q1 q2 : Nat}
    (h1 : DetRun oracle img s1 n1 s2 c1 q1)
    (h2 : DetRun oracle img s2 n2 s3 c2 q2) :
    DetRun oracle img s1 (n1 + n2) s3 (c1 + c2) (q1 + q2) := by
  intro extra
  rw [Nat.add_assoc, h1 (n2 + extra), h2 extra, Functor.map_map]
  congr 1
  funext ⟨e, n⟩
  simp [Execution.charge, Nat.add_assoc]

theorem DetRun.step {oracle : Oracle} {img : Image} {s s' : MachineState} {instr : Instruction}
    (hfetch : fetch img s = some instr)
    (hstep : ordinaryStep s instr = some s') :
    DetRun oracle img s 1 s' (instructionCycles instr) 0 := by
  intro extra
  rw [Nat.add_comm 1 extra, execute_ordinary_step img instr s s' extra true hfetch hstep]
  have hmap : (do let result ← execute img extra s' true
                  return result.charge (instructionCycles instr) 0) =
      (fun result : Execution => result.charge (instructionCycles instr) 0) <$>
        execute img extra s' true := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [hmap, oracle_run_map]
  congr 1; funext ⟨e, n⟩; simp only [Nat.zero_add]

theorem DetRun.step1 {oracle : Oracle} {img : Image} {s s' : MachineState} {instr : Instruction}
    (hfetch : fetch img s = some instr)
    (hstep : ordinaryStep s instr = some s')
    (hcyc : instructionCycles instr = 1 := by rfl) :
    DetRun oracle img s 1 s' 1 0 := by
  have h := DetRun.step (oracle := oracle) hfetch hstep
  rw [hcyc] at h
  exact h

private theorem readBuffer_toNat_congr_commit (s : MachineState) (src : Nat) {n1 n2 : Nat} (h : n1 = n2) :
    (readBuffer s src n1).toNat = (readBuffer s src n2).toNat := by
  subst h; rfl

private theorem ofNat_toNat_cast_commit {n m : Nat} (h : n = m) (v : BitVec n) :
    BitVec.ofNat m v.toNat = v.cast h := by
  subst h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_cast]
  exact Nat.mod_eq_of_lt v.isLt

theorem DetRun.compress (h768 : COMPRESSION_INPUT_LENGTH = 768)
    {oracle : Oracle} {img : Image} {s : MachineState}
    (hfetch : fetch img s = some (.base .ECALL))
    (hx5 : s.getReg .x5 = 0#64)
    (hx11 : s.getReg .x11 = 96#64)
    (hx13 : s.getReg .x13 = 0#64)
    (src dst : Nat)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 8 = 0) (hdst_al : dst % 8 = 0)
    (hsrc_bd : src + 96 ≤ MEMORY_BYTES) (hdst_bd : dst + 32 ≤ MEMORY_BYTES) :
    DetRun oracle img s 1
      (writeBits s (BitVec.ofNat 64 dst)
        (oracle.compression ((readBuffer s src 96).cast h768.symm)))
      8 1 := by
  intro extra
  have hsrc_lt : src < 2 ^ 64 := by unfold MEMORY_BYTES at hsrc_bd; omega
  have hdst_lt : dst < 2 ^ 64 := by unfold MEMORY_BYTES at hdst_bd; omega
  have hsrc_toNat : (s.getReg .x10).toNat = src := by
    rw [hx10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc_lt]
  have hdst_toNat : (s.getReg .x12).toNat = dst := by
    rw [hx12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdst_lt]
  have hrv_src : rangeValid (s.getReg .x10) 96 = true := by
    unfold rangeValid; rw [hsrc_toNat]; exact decide_eq_true hsrc_bd
  have hrv_dst : rangeValid (s.getReg .x12) 32 = true := by
    unfold rangeValid; rw [hdst_toNat]; exact decide_eq_true hdst_bd
  have hoinp : oracleInput s = some (Sum.inl ((readBuffer s src 96).cast h768.symm)) := by
    unfold oracleInput
    dsimp only
    have hk : (s.getReg .x13).toNat = 0 := by rw [hx13]; rfl
    have hlen : (s.getReg .x11).toNat = 96 := by rw [hx11]; rfl
    have hinb : (COMPRESSION_INPUT_LENGTH + 7) / 8 = 96 := by rw [h768]
    have hinb_full :
        (((if (s.getReg .x13).toNat = 0 then COMPRESSION_INPUT_LENGTH else PERMUTATION_WIDTH) + 7) / 8) = 96 := by
      rw [hk]; simp only [ite_true]; exact hinb
    have houtb : (COMPRESSION_OUTPUT_LENGTH + 7) / 8 = 32 := by rfl
    simp only [hk, ite_true, hsrc_toNat]
    rw [readBuffer_toNat_congr_commit s src hinb_full]
    simp only [hinb, houtb, hlen, hdst_toNat, hsrc_al, hdst_al,
      hrv_src, hrv_dst, Nat.zero_le, and_self, ite_true]
    exact congrArg (fun x : BitVec COMPRESSION_INPUT_LENGTH => (some (Sum.inl x) : Option PublicSpec.Domain))
      (ofNat_toNat_cast_commit (show 8 * 96 = COMPRESSION_INPUT_LENGTH by rw [h768]) (readBuffer s src 96))
  rw [Nat.add_comm 1 extra]
  have hx5' : s.getReg .x5 = (0 : Word) := hx5
  simp only [execute, hfetch, hx5', ite_true, hoinp]
  change oracle.run ((liftM (World.query (.inr (Sum.inl ((readBuffer s src 96).cast h768.symm)))) : OracleComp World _) >>=
    fun ans => execute img extra (writeBits s (s.getReg .x12) ans) true >>= fun res =>
      pure (res.charge COMPRESSION_CYCLES 1)) = _
  rw [oracle_run_public_bind, hx12]
  change (oracle.run (execute img extra
      (writeBits s (BitVec.ofNat 64 dst) (oracle.compression ((readBuffer s src 96).cast h768.symm))) true >>=
      fun res => pure (res.charge 8 1)) >>= fun p => pure (p.1, 1 + p.2)) = _
  have hmap : (execute img extra
        (writeBits s (BitVec.ofNat 64 dst) (oracle.compression ((readBuffer s src 96).cast h768.symm))) true >>=
        fun res => pure (res.charge 8 1)) =
      (fun res : Execution => res.charge 8 1) <$>
        execute img extra
          (writeBits s (BitVec.ofNat 64 dst) (oracle.compression ((readBuffer s src 96).cast h768.symm))) true := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [hmap, oracle_run_map, bind_map_left, map_eq_bind_pure_comp]
  apply bind_congr; intro ⟨e, n⟩; rfl

/-- Variant of `DetRun.compress` returning `writeBits` at explicit width `256` (`Digest`) with a
caller-supplied equality `hout`, avoiding width-cast unification issues at call sites. -/
theorem DetRun.compress_eq (h768 : COMPRESSION_INPUT_LENGTH = 768)
    {oracle : Oracle} {img : Image} {s : MachineState}
    (hfetch : fetch img s = some (.base .ECALL))
    (hx5 : s.getReg .x5 = 0#64)
    (hx11 : s.getReg .x11 = 96#64)
    (hx13 : s.getReg .x13 = 0#64)
    (src dst : Nat)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 8 = 0) (hdst_al : dst % 8 = 0)
    (hsrc_bd : src + 96 ≤ MEMORY_BYTES) (hdst_bd : dst + 32 ≤ MEMORY_BYTES)
    (out : Digest)
    (hout : oracle.compression ((readBuffer s src 96).cast h768.symm) = out) :
    DetRun oracle img s 1 (writeBits s (BitVec.ofNat 64 dst) out) 8 1 := by
  have h := DetRun.compress h768 (oracle := oracle) hfetch hx5 hx11 hx13 src dst hx10 hx12 hsrc_al hdst_al hsrc_bd hdst_bd
  have hw : writeBits s (BitVec.ofNat 64 dst)
        (oracle.compression ((readBuffer s src 96).cast h768.symm)) =
      writeBits s (BitVec.ofNat 64 dst) out := by
    change writeBits s (BitVec.ofNat 64 dst)
        (oracle.compression ((readBuffer s src 96).cast h768.symm) : Digest) =
      writeBits s (BitVec.ofNat 64 dst) out
    rw [hout]
    rfl
  rw [← hw]
  exact h

theorem DetRun.halt_ok {oracle : Oracle} {img : Image} {s : MachineState}
    (hfetch : fetch img s = some (.base .ECALL))
    (hx5 : s.getReg .x5 = 1#64)
    (hx10 : s.getReg .x10 = 0#64) (extra : Nat) :
    oracle.run (execute img (1 + extra) s true) = pure (⟨.success, s, 1, 0⟩, 0) := by
  rw [Nat.add_comm 1 extra]
  have hne0 : ¬ (s.getReg .x5 = (0 : Word)) := by rw [hx5]; decide
  have heq1 : s.getReg .x5 = (1 : Word) := hx5
  have heq0 : s.getReg .x10 = (0 : Word) := hx10
  have h1 : execute img (extra + 1) s true = pure ⟨.success, s, 1, 0⟩ := by
    simp only [execute, hfetch]
    rw [if_neg hne0, if_pos heq1, if_pos heq0]
  rw [h1, oracle_run_pure]

theorem DetRun.finish {oracle : Oracle} {img : Image} {s s' : MachineState}
    {steps cyc calls : Nat}
    (hrun : DetRun oracle img s steps s' cyc calls)
    (hfetch : fetch img s' = some (.base .ECALL))
    (hx5 : s'.getReg .x5 = 1#64)
    (hx10 : s'.getReg .x10 = 0#64)
    (totalSteps : Nat) (hfuel : steps + 1 ≤ totalSteps) :
    oracle.run (execute img totalSteps s true) =
      pure (⟨.success, s', cyc + 1, calls⟩, calls) := by
  obtain ⟨extra, rfl⟩ : ∃ extra, totalSteps = steps + (1 + extra) := ⟨totalSteps - (steps + 1), by omega⟩
  rw [hrun (1 + extra), DetRun.halt_ok hfetch hx5 hx10 extra, map_pure]
  simp [Execution.charge]

/-! ### 1b. Fast `MachineState`, Step, BitVec, and Copy Helpers -/

theorem pc_setPC (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl
theorem c_mem_setPC (s : MachineState) (v : Word) : (s.setPC v).mem = s.mem := rfl
theorem c_mem_setReg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl
theorem c_getReg_x0 (s : MachineState) : s.getReg .x0 = 0#64 := rfl
theorem getReg_setReg_x0 (s : MachineState) (v : Word) (r : Reg) :
    (s.setReg .x0 v).getReg r = s.getReg r := rfl
theorem getReg_setReg_ne' (r r' : Reg) (h : r ≠ r') (s : MachineState) (v : Word) :
    (s.setReg r v).getReg r' = s.getReg r' :=
  MachineState.getReg_setReg_ne s r r' v h
theorem getReg_setMem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl
theorem getReg_setHalfword (s : MachineState) (a : Word) (h : BitVec 16) (r : Reg) :
    (s.setHalfword a h).getReg r = s.getReg r := by cases r <;> rfl
theorem getByte_of_mem_eq {s1 s2 : MachineState} (h : s1.mem = s2.mem) (a : Word) :
    s1.getByte a = s2.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem, h]
theorem readBuffer_of_mem_eq {s1 s2 : MachineState} (h : s1.mem = s2.mem) (addr n : Nat) :
    readBuffer s1 addr n = readBuffer s2 addr n :=
  readBuffer_congr s1 s2 addr n (fun _ _ => getByte_of_mem_eq h _)
theorem pc_writeBits {bits : Nat} (s : MachineState) (a : Word) (v : BitVec bits) :
    (writeBits s a v).pc = s.pc + 4 := rfl
theorem bv64_add4 (n : Nat) : BitVec.ofNat 64 n + (4 : Word) = BitVec.ofNat 64 (n + 4) := by
  change BitVec.ofNat 64 n + BitVec.ofNat 64 4 = BitVec.ofNat 64 (n + 4)
  exact (BitVec.ofNat_add n 4).symm
theorem pc_step_idx (s : MachineState) (idx : Nat)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    s.pc + (4 : Word) = BitVec.ofNat 64 (0x1000 + 4 * (idx + 1)) := by
  rw [hpc, bv64_add4]
  exact congrArg (BitVec.ofNat 64) (by omega)
theorem submission_run_commit (s : Submission) (message : Message) :
    s.run .commit message =
      execute (s.image .commit) (s.steps .commit) (s.initialState .commit message) true := by
  unfold Submission.run; dsimp only; exact if_pos rfl

theorem pc_exec_ADDI (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI rd rs1 imm)).pc = s.pc + 4 := rfl
theorem pc_exec_ADD (s : MachineState) (rd rs1 rs2 : Reg) :
    (execInstrBr s (.ADD rd rs1 rs2)).pc = s.pc + 4 := rfl
theorem pc_exec_SLLI (s : MachineState) (rd rs1 : Reg) (sh : BitVec 6) :
    (execInstrBr s (.SLLI rd rs1 sh)).pc = s.pc + 4 := rfl
theorem pc_exec_SRLI (s : MachineState) (rd rs1 : Reg) (sh : BitVec 6) :
    (execInstrBr s (.SRLI rd rs1 sh)).pc = s.pc + 4 := rfl
theorem pc_exec_ANDI (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ANDI rd rs1 imm)).pc = s.pc + 4 := rfl
theorem pc_exec_LD (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.LD rd rs1 imm)).pc = s.pc + 4 := rfl
theorem pc_exec_SD (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.SD rs1 rs2 imm)).pc = s.pc + 4 := rfl
theorem pc_exec_SH (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.SH rs1 rs2 imm)).pc = s.pc + 4 := rfl

theorem mem_exec_ADDI (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI rd rs1 imm)).mem = s.mem := by cases rd <;> rfl
theorem mem_exec_ADD (s : MachineState) (rd rs1 rs2 : Reg) :
    (execInstrBr s (.ADD rd rs1 rs2)).mem = s.mem := by cases rd <;> rfl
theorem mem_exec_SLLI (s : MachineState) (rd rs1 : Reg) (sh : BitVec 6) :
    (execInstrBr s (.SLLI rd rs1 sh)).mem = s.mem := by cases rd <;> rfl
theorem mem_exec_SRLI (s : MachineState) (rd rs1 : Reg) (sh : BitVec 6) :
    (execInstrBr s (.SRLI rd rs1 sh)).mem = s.mem := by cases rd <;> rfl
theorem mem_exec_ANDI (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ANDI rd rs1 imm)).mem = s.mem := by cases rd <;> rfl
theorem mem_exec_LD (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.LD rd rs1 imm)).mem = s.mem := by cases rd <;> rfl
theorem mem_exec_JAL (s : MachineState) (rd : Reg) (off : BitVec 21) :
    (execInstrBr s (.JAL rd off)).mem = s.mem := by cases rd <;> rfl
theorem mem_exec_BEQ (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 13) :
    (execInstrBr s (.BEQ rs1 rs2 off)).mem = s.mem := by simp only [execInstrBr]; split <;> rfl
theorem mem_exec_BNE (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 13) :
    (execInstrBr s (.BNE rs1 rs2 off)).mem = s.mem := by simp only [execInstrBr]; split <;> rfl

theorem reg_exec_SD (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12) (r : Reg) :
    (execInstrBr s (.SD rs1 rs2 imm)).getReg r = s.getReg r := by cases r <;> rfl
theorem reg_exec_SH (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12) (r : Reg) :
    (execInstrBr s (.SH rs1 rs2 imm)).getReg r = s.getReg r := by cases r <;> rfl
theorem reg_exec_BEQ (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 13) (r : Reg) :
    (execInstrBr s (.BEQ rs1 rs2 off)).getReg r = s.getReg r := by
  simp only [execInstrBr]; split <;> exact MachineState.getReg_setPC
theorem reg_exec_BNE (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 13) (r : Reg) :
    (execInstrBr s (.BNE rs1 rs2 off)).getReg r = s.getReg r := by
  simp only [execInstrBr]; split <;> exact MachineState.getReg_setPC
theorem reg_exec_JAL0 (s : MachineState) (off : BitVec 21) (r : Reg) :
    (execInstrBr s (.JAL .x0 off)).getReg r = s.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, getReg_setReg_x0]

theorem ordinaryStep_LD (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12)
    (h : accessValid (s.getReg rs1 + signExtend12 imm) 8 = true) :
    ordinaryStep s (.base (.LD rd rs1 imm)) = some (execInstrBr s (.LD rd rs1 imm)) := by
  simp only [ordinaryStep, memoryArgumentsValid, memAccess, h, ite_true]
theorem ordinaryStep_SD (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12)
    (h : accessValid (s.getReg rs1 + signExtend12 imm) 8 = true) :
    ordinaryStep s (.base (.SD rs1 rs2 imm)) = some (execInstrBr s (.SD rs1 rs2 imm)) := by
  simp only [ordinaryStep, memoryArgumentsValid, memAccess, h, ite_true]
theorem ordinaryStep_SH (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12)
    (h : accessValid (s.getReg rs1 + signExtend12 imm) 2 = true) :
    ordinaryStep s (.base (.SH rs1 rs2 imm)) = some (execInstrBr s (.SH rs1 rs2 imm)) := by
  simp only [ordinaryStep, memoryArgumentsValid, memAccess, h, ite_true]

theorem bv64_ushiftRight_ofNat (n k : Nat) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> k = BitVec.ofNat 64 (n / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn)).symm

theorem bv64_shiftLeft_ofNat (n k : Nat) (h : n * 2 ^ k < 2 ^ 64) :
    BitVec.ofNat 64 n <<< k = BitVec.ofNat 64 (n * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  have hn : n < 2 ^ 64 := by
    have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    nlinarith
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.shiftLeft_eq]

theorem bv64_and_127 (n : Nat) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& signExtend12 (127#12) = BitVec.ofNat 64 (n % 128) := by
  have hse : signExtend12 (127#12) = BitVec.ofNat 64 127 := by decide
  rw [hse]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : 127 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : n % 128 < 2 ^ 64)]
  exact Nat.and_two_pow_sub_one_eq_mod n 7

theorem bv64_and_1 (n : Nat) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& signExtend12 (1#12) = BitVec.ofNat 64 (n % 2) := by
  have hse : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  rw [hse]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : n % 2 < 2 ^ 64)]
  exact Nat.and_two_pow_sub_one_eq_mod n 1

theorem bv64_ne_of_nat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro h
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hn
  exact hne hn

/-! ### 2. Memory Framing & Concrete Address/Immediate Arithmetic Helpers -/

def MemPreservedOutside (s1 s2 : MachineState) (lo hi : Nat) : Prop :=
  ∀ addr : Nat, addr < 2 ^ 64 → (addr < lo ∨ hi ≤ addr) →
    s2.getByte (BitVec.ofNat 64 addr) = s1.getByte (BitVec.ofNat 64 addr)

theorem MemPreservedOutside.refl (s : MachineState) (lo hi : Nat) :
    MemPreservedOutside s s lo hi := fun _ _ _ => rfl

theorem MemPreservedOutside.of_mem_eq {s1 s2 : MachineState} (h : s2.mem = s1.mem) (lo hi : Nat) :
    MemPreservedOutside s1 s2 lo hi := fun addr _ _ => getByte_of_mem_eq h _

theorem MemPreservedOutside.mono {s1 s2 : MachineState} {lo hi lo' hi' : Nat}
    (h : MemPreservedOutside s1 s2 lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    MemPreservedOutside s1 s2 lo' hi' := by
  intro addr hbd hout
  exact h addr hbd (by omega)

theorem MemPreservedOutside.trans {s1 s2 s3 : MachineState} {lo hi : Nat}
    (h1 : MemPreservedOutside s1 s2 lo hi) (h2 : MemPreservedOutside s2 s3 lo hi) :
    MemPreservedOutside s1 s3 lo hi := by
  intro addr hbd hout
  exact (h2 addr hbd hout).trans (h1 addr hbd hout)

theorem MemPreservedOutside.readBuffer_eq {s1 s2 : MachineState} {lo hi addr n : Nat}
    (h : MemPreservedOutside s1 s2 lo hi) (hbd : addr + n ≤ 2 ^ 64)
    (hsep : addr + n ≤ lo ∨ hi ≤ addr) :
    readBuffer s2 addr n = readBuffer s1 addr n := by
  apply readBuffer_congr
  intro j hj
  exact h (addr + j) (by omega) (by omega)

theorem MemPreservedOutside.getMem_eq {s1 s2 : MachineState} {lo hi addr : Nat}
    (h : MemPreservedOutside s1 s2 lo hi) (halign : addr % 8 = 0) (hbd : addr + 8 ≤ 2 ^ 64)
    (hsep : addr + 8 ≤ lo ∨ hi ≤ addr) :
    s2.getMem (BitVec.ofNat 64 addr) = s1.getMem (BitVec.ofNat 64 addr) := by
  rw [← readBuffer_word s2 addr halign, ← readBuffer_word s1 addr halign]
  exact h.readBuffer_eq hbd hsep

theorem memPreserved_setMem (s : MachineState) (addr : Nat) (val : Word)
    (halign : addr % 8 = 0) (hbd : addr + 8 ≤ 2 ^ 64) :
    MemPreservedOutside s (s.setMem (BitVec.ofNat 64 addr) val) addr (addr + 8) := by
  intro q hq hout
  exact setMem_getByte_ofNat s addr q val halign hbd hq hout

theorem memPreserved_setHalfword (s : MachineState) (addr : Nat) (val : BitVec 16)
    (halign : addr % 2 = 0) (hbd : addr + 2 ≤ 2 ^ 64) :
    MemPreservedOutside s (s.setHalfword (BitVec.ofNat 64 addr) val) addr (addr + 2) := by
  intro q hq hout
  have hal : (BitVec.ofNat 64 addr).toNat % 2 = 0 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : addr < 2 ^ 64)]; exact halign
  rw [setHalfword_getByte s (BitVec.ofNat 64 addr) (BitVec.ofNat 64 q) val hal]
  have hne0 : BitVec.ofNat 64 q ≠ BitVec.ofNat 64 addr := by
    intro heq
    have hn := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (by omega : addr < 2 ^ 64)] at hn
    omega
  have hne1 : BitVec.ofNat 64 q ≠ BitVec.ofNat 64 addr + 1#64 := by
    intro heq
    have heq' : BitVec.ofNat 64 q = BitVec.ofNat 64 (addr + 1) := by
      simpa only [show (1#64 : Word) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add] using heq
    have hn := congrArg BitVec.toNat heq'
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (by omega : addr + 1 < 2 ^ 64)] at hn
    omega
  simp only [hne0, hne1, ite_false]

theorem memPreserved_writeBits {bits : Nat} (s : MachineState) (addr : Nat) (ans : BitVec bits)
    (hbd : addr + (bits + 7) / 8 ≤ 2 ^ 64) :
    MemPreservedOutside s (writeBits s (BitVec.ofNat 64 addr) ans) addr (addr + (bits + 7) / 8) := by
  intro q hq hout
  apply write_bits_byte_outside
  intro i hi heq
  have hn := congrArg BitVec.toNat heq
  rw [← BitVec.ofNat_add] at hn
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (by omega : addr + i < 2 ^ 64)] at hn
  omega

/-- Convenience constants matching `submission.layout` and `commit_dataBase`. -/
abbrev C_MSG : Nat := 4096
abbrev C_CMT : Nat := 4294971392
abbrev C_TD  : Nat := 4294971424
abbrev C_DB  : Nat := 68719476032

theorem add_signExtend12_ofNat_small (a b : Nat) (hb : b < 2048) :
    BitVec.ofNat 64 a + signExtend12 (BitVec.ofNat 12 b) = BitVec.ofNat 64 (a + b) := by
  have hse : signExtend12 (BitVec.ofNat 12 b) = BitVec.ofNat 64 b := by
    unfold signExtend12
    apply BitVec.eq_of_toNat_eq
    have hmod12 : b % 2 ^ 12 = b := Nat.mod_eq_of_lt (by omega)
    have hmod64 : b % 2 ^ 64 = b := Nat.mod_eq_of_lt (by omega)
    have hmsb : (BitVec.ofNat 12 b).msb = false := by
      rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, hmod12]
      exact decide_eq_false (by omega)
    simp only [BitVec.toNat_signExtend, hmsb, Bool.false_eq_true, ite_false, Nat.add_zero,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, hmod12, hmod64]
  rw [hse, ← BitVec.ofNat_add]

private theorem signExtend12_neg_add_cancel (d : Nat) (hd1 : 0 < d) (hd2 : d ≤ 2048) :
    signExtend12 (BitVec.ofNat 12 (4096 - d)) + BitVec.ofNat 64 d = 0#64 := by
  have hmod12 : (4096 - d) % 2 ^ 12 = 4096 - d := Nat.mod_eq_of_lt (by omega)
  have hmod64 : (4096 - d) % 2 ^ 64 = 4096 - d := Nat.mod_eq_of_lt (by omega)
  have hmsb : (BitVec.ofNat 12 (4096 - d)).msb = true := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, hmod12]
    exact decide_eq_true (by omega)
  have hse_toNat : (signExtend12 (BitVec.ofNat 12 (4096 - d))).toNat = 2 ^ 64 - d := by
    unfold signExtend12
    simp only [BitVec.toNat_signExtend, hmsb, ite_true,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, hmod12, hmod64]
    omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, hse_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
  change (2 ^ 64 - d + d) % 2 ^ 64 = 0
  have hsum : 2 ^ 64 - d + d = 2 ^ 64 := by omega
  rw [hsum, Nat.mod_self]

theorem add_signExtend12_neg' (a d : Nat) (hd1 : 0 < d) (hd2 : d ≤ 2048) (ha : d ≤ a) :
    BitVec.ofNat 64 a + signExtend12 (BitVec.ofNat 12 (4096 - d)) = BitVec.ofNat 64 (a - d) := by
  have hsplit : BitVec.ofNat 64 a = BitVec.ofNat 64 (a - d) + BitVec.ofNat 64 d := by
    rw [← BitVec.ofNat_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  calc
    BitVec.ofNat 64 a + signExtend12 (BitVec.ofNat 12 (4096 - d))
      = BitVec.ofNat 64 (a - d) + (signExtend12 (BitVec.ofNat 12 (4096 - d)) + BitVec.ofNat 64 d) := by
          rw [hsplit]; ac_rfl
    _ = BitVec.ofNat 64 (a - d) := by rw [signExtend12_neg_add_cancel d hd1 hd2, BitVec.add_zero]

theorem add_signExtend12_soff (base k : Nat) (hk : k < 128) (hbase : 1024 ≤ base) :
    BitVec.ofNat 64 base + signExtend12 (BitVec.ofNat 12 ((4096 - 1024 + 16 * k) % 4096)) =
      BitVec.ofNat 64 (base - 1024 + 16 * k) := by
  by_cases hlt : k < 64
  · have hmod : (4096 - 1024 + 16 * k) % 4096 = 4096 - (1024 - 16 * k) := by omega
    rw [hmod, add_signExtend12_neg' base (1024 - 16 * k) (by omega) (by omega) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · have hmod : (4096 - 1024 + 16 * k) % 4096 = 16 * k - 1024 := by omega
    rw [hmod, add_signExtend12_ofNat_small base (16 * k - 1024) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)

theorem add_signExtend12_soff8 (base k : Nat) (hk : k < 128) (hbase : 1024 ≤ base) :
    BitVec.ofNat 64 base + signExtend12 (BitVec.ofNat 12 ((4096 - 1016 + 16 * k) % 4096)) =
      BitVec.ofNat 64 (base - 1016 + 16 * k) := by
  by_cases hlt : k < 64
  · have hmod : (4096 - 1016 + 16 * k) % 4096 = 4096 - (1016 - 16 * k) := by omega
    rw [hmod, add_signExtend12_neg' base (1016 - 16 * k) (by omega) (by omega) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · have hmod : (4096 - 1016 + 16 * k) % 4096 = 16 * k - 1016 := by omega
    rw [hmod, add_signExtend12_ofNat_small base (16 * k - 1016) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)

theorem add_signExtend12_hoff (base k : Nat) (hk : k < 128) (hbase : 2048 ≤ base) :
    BitVec.ofNat 64 base + signExtend12 (BitVec.ofNat 12 ((4096 - 2048 + 32 * k) % 4096)) =
      BitVec.ofNat 64 (base - 2048 + 32 * k) := by
  by_cases hlt : k < 64
  · have hmod : (4096 - 2048 + 32 * k) % 4096 = 4096 - (2048 - 32 * k) := by omega
    rw [hmod, add_signExtend12_neg' base (2048 - 32 * k) (by omega) (by omega) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)
  · have hmod : (4096 - 2048 + 32 * k) % 4096 = 32 * k - 2048 := by omega
    rw [hmod, add_signExtend12_ofNat_small base (32 * k - 2048) (by omega)]
    exact congrArg (BitVec.ofNat 64) (by omega)

theorem c_accessValid_ofNat (addr w : Nat) (hal : addr % w = 0) (hbd : addr + w ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 addr) w = true := by
  have ha : addr < 2 ^ 64 := by unfold MEMORY_BYTES at hbd; omega
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hbd, hal⟩

/-- Reusable 4-dword (32-byte) aligned copy sequence (`LD x6 / SD x6` × 4 = 8 steps, 8 cycles).
Used for promoted nodes in Phase 2/3 and the root copy in Phase 4. -/
theorem commit_copy32 (oracle : Oracle) (s : MachineState)
    (basePc : Nat) (srcReg dstReg : Reg) (srcBase dstBase srcOff dstOff : Nat)
    (hsrcReg : srcReg ≠ .x6) (hdstReg : dstReg ≠ .x6)
    (hsrcOff : srcOff + 24 < 2048) (hdstOff : dstOff + 24 < 2048)
    (hsrcAl : (srcBase + srcOff) % 8 = 0) (hdstAl : (dstBase + dstOff) % 8 = 0)
    (hsrcBd : srcBase + srcOff + 32 ≤ MEMORY_BYTES) (hdstBd : dstBase + dstOff + 32 ≤ MEMORY_BYTES)
    (hdisj : srcBase + srcOff + 32 ≤ dstBase + dstOff ∨ dstBase + dstOff + 32 ≤ srcBase + srcOff)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * basePc))
    (hsrc : s.getReg srcReg = BitVec.ofNat 64 srcBase)
    (hdst : s.getReg dstReg = BitVec.ofNat 64 dstBase)
    (hfetch : ∀ k < 4, ∀ st : MachineState,
      (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2 * k)) →
        fetch (submission.image .commit) st = some (.base (.LD .x6 srcReg (BitVec.ofNat 12 (srcOff + 8 * k))))) ∧
      (st.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2 * k + 1)) →
        fetch (submission.image .commit) st = some (.base (.SD dstReg .x6 (BitVec.ofNat 12 (dstOff + 8 * k)))))) :
    ∃ s',
      DetRun oracle (submission.image .commit) s 8 s' 8 0 ∧
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 8)) ∧
      (∀ r : Reg, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      readBuffer s' (dstBase + dstOff) 32 = readBuffer s (srcBase + srcOff) 32 ∧
      MemPreservedOutside s s' (dstBase + dstOff) (dstBase + dstOff + 32) := by
  have hmemBd : MEMORY_BYTES < 2 ^ 64 := by unfold MEMORY_BYTES; decide
  have hind : ∀ m ≤ 4,
      ∃ sm,
        DetRun oracle (submission.image .commit) s (2 * m) sm (2 * m) 0 ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2 * m)) ∧
        (∀ r : Reg, r ≠ .x6 → sm.getReg r = s.getReg r) ∧
        (∀ k < m, sm.getMem (BitVec.ofNat 64 (dstBase + dstOff + 8 * k)) =
          s.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k))) ∧
        MemPreservedOutside s sm (dstBase + dstOff) (dstBase + dstOff + 8 * m) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨s, DetRun.refl _ _ _, by simpa using hpc, fun _ _ => rfl,
        fun _ hk => (Nat.not_lt_zero _ hk).elim, MemPreservedOutside.refl _ _ _⟩
    | succ m ih =>
      obtain ⟨sm, hrunm, hpcm, hregm, hwordm, hpresm⟩ := ih (by omega)
      let insL := Instr.LD .x6 srcReg (BitVec.ofNat 12 (srcOff + 8 * m))
      let insS := Instr.SD dstReg .x6 (BitVec.ofNat 12 (dstOff + 8 * m))
      let s1 := execInstrBr sm insL
      let s2 := execInstrBr s1 insS
      have hsrcAddr : sm.getReg srcReg + signExtend12 (BitVec.ofNat 12 (srcOff + 8 * m)) =
          BitVec.ofNat 64 (srcBase + srcOff + 8 * m) := by
        rw [hregm srcReg hsrcReg, hsrc, add_signExtend12_ofNat_small _ (srcOff + 8 * m) (by omega)]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have hdstAddr : s1.getReg dstReg + signExtend12 (BitVec.ofNat 12 (dstOff + 8 * m)) =
          BitVec.ofNat 64 (dstBase + dstOff + 8 * m) := by
        have hd1 : s1.getReg dstReg = sm.getReg dstReg := by
          simp only [s1, insL, execInstrBr, MachineState.getReg_setPC,
            getReg_setReg_ne' .x6 dstReg (Ne.symm hdstReg)]
        rw [hd1, hregm dstReg hdstReg, hdst, add_signExtend12_ofNat_small _ (dstOff + 8 * m) (by omega)]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have hstL : DetRun oracle (submission.image .commit) sm 1 s1 1 0 :=
        DetRun.step1 ((hfetch m (by omega) sm).1 hpcm)
          (ordinaryStep_LD sm .x6 srcReg _ (by
            rw [hsrcAddr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
      have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2 * m + 1)) := by
        rw [pc_exec_LD, hpcm, bv64_add4]; exact congrArg (BitVec.ofNat 64) (by omega)
      have hstS : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
        DetRun.step1 ((hfetch m (by omega) s1).2 hs1_pc)
          (ordinaryStep_SD s1 dstReg .x6 _ (by
            rw [hdstAddr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
      have hs2_mem : s2.mem = (sm.setMem (BitVec.ofNat 64 (dstBase + dstOff + 8 * m))
          (sm.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * m)))).mem := by
        have hm1 : s1.mem = sm.mem := mem_exec_LD sm .x6 srcReg _
        have hx6 : s1.getReg .x6 = sm.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * m)) := by
          simp only [s1, insL, execInstrBr, MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hsrcAddr]
        simp only [s2, insS, execInstrBr, hdstAddr, hx6, c_mem_setPC, MachineState.setMem, hm1]
      have hp12 : MemPreservedOutside sm s2 (dstBase + dstOff + 8 * m) (dstBase + dstOff + 8 * (m + 1)) := by
        have hp := memPreserved_setMem sm (dstBase + dstOff + 8 * m)
          (sm.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * m))) (by omega) (by omega)
        exact (hp.mono (le_refl _) (by omega)).trans (MemPreservedOutside.of_mem_eq hs2_mem _ _)
      refine ⟨s2, by simpa [Nat.mul_succ, Nat.add_assoc] using (hrunm.trans hstL).trans hstS, ?_, ?_, ?_, ?_⟩
      · rw [pc_exec_SD, hs1_pc, bv64_add4]; exact congrArg (BitVec.ofNat 64) (by omega)
      · intro r hr
        have h1 : s2.getReg r = s1.getReg r := reg_exec_SD s1 dstReg .x6 _ r
        have h2 : s1.getReg r = sm.getReg r := by
          simp only [s1, insL, execInstrBr, MachineState.getReg_setPC,
            getReg_setReg_ne' .x6 r (Ne.symm hr)]
        exact (h1.trans h2).trans (hregm r hr)
      · intro k hk
        by_cases hkm : k = m
        · subst hkm
          have hsrc_eq : sm.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k)) =
              s.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k)) :=
            hpresm.getMem_eq (by omega) (by omega) (by omega)
          rw [← hsrc_eq]
          simp only [MachineState.getMem, hs2_mem]
          exact MachineState.getMem_setMem_eq
        · rw [hp12.getMem_eq (by omega) (by omega) (by omega)]
          exact hwordm k (by omega)
      · exact (hpresm.mono (le_refl _) (by omega)).trans (hp12.mono (by omega) (le_refl _))
  obtain ⟨s4, hrun4, hpc4, hreg4, hword4, hpres4⟩ := hind 4 (le_refl _)
  refine ⟨s4, hrun4, hpc4, hreg4, ?_, hpres4⟩
  exact (read_digest_eq_iff s4 s (dstBase + dstOff) (srcBase + srcOff) hdstAl hsrcAl).mpr hword4

/-! ### 3. Pure-ALU List Execution & Phase 0 (words 0..28) -/

def isPureAlu : Instr → Bool
  | .ADDI .. | .ADD .. | .SLLI .. | .SRLI .. | .ANDI .. => true
  | _ => false

theorem execInstrBr_pureAlu_pc (s : MachineState) (ins : Instr) (h : isPureAlu ins = true) :
    (execInstrBr s ins).pc = s.pc + 4 := by
  cases ins <;> simp_all [isPureAlu, execInstrBr, pc_setPC]

theorem execInstrBr_pureAlu_mem (s : MachineState) (ins : Instr) (h : isPureAlu ins = true) :
    (execInstrBr s ins).mem = s.mem := by
  cases ins <;> simp_all [isPureAlu, execInstrBr, c_mem_setPC, c_mem_setReg]

theorem foldl_pureAlu_pc (instrs : List Instr) (s : MachineState) (n : Nat)
    (hall : ∀ ins ∈ instrs, isPureAlu ins = true)
    (hpc : s.pc = BitVec.ofNat 64 n) :
    (instrs.foldl execInstrBr s).pc = BitVec.ofNat 64 (n + 4 * instrs.length) := by
  induction instrs generalizing s n with
  | nil => simp [hpc]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hhd : (execInstrBr s hd).pc = BitVec.ofNat 64 (n + 4) := by
      rw [execInstrBr_pureAlu_pc s hd (hall hd (by simp)), hpc, bv64_add4]
    have htl := ih (execInstrBr s hd) (n + 4) (fun x hx => hall x (by simp [hx])) hhd
    rw [htl]; exact congrArg (BitVec.ofNat 64) (by omega)

theorem foldl_pureAlu_mem (instrs : List Instr) (s : MachineState)
    (hall : ∀ ins ∈ instrs, isPureAlu ins = true) :
    (instrs.foldl execInstrBr s).mem = s.mem := by
  induction instrs generalizing s with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldl_cons, ih (execInstrBr s hd) (fun x hx => hall x (by simp [hx])),
      execInstrBr_pureAlu_mem s hd (hall hd (by simp))]

theorem exec_alu_list {oracle : Oracle} {img : Image} (instrs : List Instr)
    (s0 : MachineState)
    (hstep : ∀ i (hi : i < instrs.length),
      let si := (instrs.take i).foldl execInstrBr s0
      let ins := instrs[i]
      fetch img si = some (.base ins) ∧
      ordinaryStep si (.base ins) = some (execInstrBr si ins) ∧
      instructionCycles (.base ins) = 1) :
    DetRun oracle img s0 instrs.length (instrs.foldl execInstrBr s0) instrs.length 0 := by
  have hgen : ∀ k ≤ instrs.length,
      DetRun oracle img s0 k ((instrs.take k).foldl execInstrBr s0) k 0 := by
    intro k hk; induction k with
    | zero => exact DetRun.refl oracle img s0
    | succ k ih =>
      have hprev := ih (by omega)
      have hcur := hstep k (by omega)
      have htake : instrs.take (k + 1) = instrs.take k ++ [instrs[k]'(by omega)] :=
        List.take_succ_eq_append_getElem (by omega)
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact hprev.trans (DetRun.step1 hcur.1 hcur.2.1 hcur.2.2)
  simpa using hgen instrs.length (le_refl _)

private theorem initialState_pc (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).pc = 0x1000#64 := rfl
private theorem initialState_x2 (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).getReg .x2 = BitVec.ofNat 64 (dataBase (s.image p)) := rfl
private theorem initialState_x10 (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).getReg .x10 = BitVec.ofNat 64 s.layout.message := rfl
private theorem initialState_x11 (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).getReg .x11 = BitVec.ofNat 64 s.layout.commitment := rfl
private theorem initialState_x12 (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).getReg .x12 = BitVec.ofNat 64 s.layout.trapdoor := rfl

private theorem commit_initial_pc (message : Message) :
    (submission.initialState .commit message).pc = BitVec.ofNat 64 (0x1000 + 4 * 0) :=
  initialState_pc submission .commit message
private theorem commit_initial_x2 (message : Message) :
    (submission.initialState .commit message).getReg .x2 = BitVec.ofNat 64 C_DB :=
  (initialState_x2 submission .commit message).trans (congrArg (BitVec.ofNat 64) commit_dataBase)
private theorem commit_initial_x10 (message : Message) :
    (submission.initialState .commit message).getReg .x10 = BitVec.ofNat 64 C_MSG :=
  initialState_x10 submission .commit message
private theorem commit_initial_x11 (message : Message) :
    (submission.initialState .commit message).getReg .x11 = BitVec.ofNat 64 C_CMT :=
  initialState_x11 submission .commit message
private theorem commit_initial_x12 (message : Message) :
    (submission.initialState .commit message).getReg .x12 = BitVec.ofNat 64 C_TD :=
  initialState_x12 submission .commit message

private def commitPreRandomInstrs : List Instr :=
  [.ADDI .x8 .x10 (0#12), .ADDI .x26 .x11 (0#12), .ADDI .x9 .x12 (0#12),
   .ADDI .x6 .x0 (256#12), .SLLI .x6 .x6 (11#6), .SLLI .x6 .x6 (11#6),
   .ADDI .x6 .x6 (1056#12), .ADD .x18 .x9 .x6,
   .ADDI .x5 .x0 (2#12), .ADDI .x10 .x18 (0#12),
   .ADDI .x11 .x0 (64#12), .SLLI .x11 .x11 (11#6), .SLLI .x11 .x11 (11#6)]

private def commitPostRandomInstrs : List Instr :=
  [.ADDI .x10 .x8 (4000#12),
   .ADDI .x19 .x0 (1024#12), .SLLI .x19 .x19 (11#6), .ADDI .x19 .x19 (1#12),
   .SLLI .x19 .x19 (11#6), .ADDI .x19 .x19 (1952#12),
   .ADDI .x20 .x0 (2#12), .SLLI .x20 .x20 (11#6),
   .ADDI .x21 .x0 (1#12), .SLLI .x21 .x21 (11#6),
   .ADDI .x18 .x18 (1024#12), .ADD .x23 .x9 .x21,
   .ADDI .x5 .x0 (0#12), .ADDI .x11 .x0 (96#12), .ADDI .x13 .x0 (0#12)]

private theorem commit_preRandom_run (oracle : Oracle) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 0)) :
    DetRun oracle (submission.image .commit) s0 13 (commitPreRandomInstrs.foldl execInstrBr s0) 13 0 := by
  have hall : ∀ ins ∈ commitPreRandomInstrs, isPureAlu ins = true := by decide
  apply exec_alu_list commitPreRandomInstrs s0
  intro i hi
  have hi' : i < 13 := hi
  have hpc_i : ((commitPreRandomInstrs.take i).foldl execInstrBr s0).pc =
      BitVec.ofNat 64 (0x1000 + 4 * i) := by
    have h := foldl_pureAlu_pc (commitPreRandomInstrs.take i) s0 (0x1000 + 4 * 0)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    simpa only [Nat.mul_zero, Nat.add_zero] using h
  interval_cases i <;>
    exact ⟨commit_fetch_commitPrefixInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem commit_preRandom_spec (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 0))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 C_MSG)
    (hx11 : s0.getReg .x11 = BitVec.ofNat 64 C_CMT)
    (hx12 : s0.getReg .x12 = BitVec.ofNat 64 C_TD) :
    let s1 := commitPreRandomInstrs.foldl execInstrBr s0
    s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 13) ∧
    s1.mem = s0.mem ∧
    s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
    s1.getReg .x5 = 2#64 ∧
    s1.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
    s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s1.getReg .x10 = BitVec.ofNat 64 (C_TD + saltsOff) ∧
    s1.getReg .x11 = BitVec.ofNat 64 (16 * LENGTH) ∧
    s1.getReg .x18 = BitVec.ofNat 64 (C_TD + saltsOff) ∧
    s1.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ commitPreRandomInstrs, isPureAlu ins = true := by decide
  refine ⟨?_, foldl_pureAlu_mem commitPreRandomInstrs s0 hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (foldl_pureAlu_pc commitPreRandomInstrs s0 (0x1000 + 4 * 0) hall hpc).trans (by decide)
  all_goals (
    simp only [commitPreRandomInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx2, hx10, hx11, hx12, saltsOff_eq, LENGTH, LOG_LENGTH]
    try decide)

private theorem commit_postRandom_run (oracle : Oracle) (s2 : MachineState)
    (hpc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 14)) :
    DetRun oracle (submission.image .commit) s2 15 (commitPostRandomInstrs.foldl execInstrBr s2) 15 0 := by
  have hall : ∀ ins ∈ commitPostRandomInstrs, isPureAlu ins = true := by decide
  apply exec_alu_list commitPostRandomInstrs s2
  intro i hi
  have hi' : i < 15 := hi
  have hpc_i : ((commitPostRandomInstrs.take i).foldl execInstrBr s2).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (14 + i)) := by
    have h := foldl_pureAlu_pc (commitPostRandomInstrs.take i) s2 (0x1000 + 4 * 14)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitPrefixInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem commit_postRandom_spec (s2 : MachineState)
    (hpc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 14))
    (hx2 : s2.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx8 : s2.getReg .x8 = BitVec.ofNat 64 C_MSG)
    (hx9 : s2.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx18 : s2.getReg .x18 = BitVec.ofNat 64 (C_TD + saltsOff))
    (hx26 : s2.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s3 := commitPostRandomInstrs.foldl execInstrBr s2
    s3.pc = BitVec.ofNat 64 (0x1000 + 4 * 29) ∧
    s3.mem = s2.mem ∧
    s3.getReg .x2 = BitVec.ofNat 64 C_DB ∧
    s3.getReg .x5 = 0#64 ∧
    s3.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
    s3.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s3.getReg .x10 = BitVec.ofNat 64 4000 ∧
    s3.getReg .x11 = 96#64 ∧
    s3.getReg .x13 = 0#64 ∧
    s3.getReg .x18 = BitVec.ofNat 64 (C_TD + saltsOff + 1024) ∧
    s3.getReg .x19 = BitVec.ofNat 64 (4000 + 2 ^ 32) ∧
    s3.getReg .x20 = BitVec.ofNat 64 4096 ∧
    s3.getReg .x21 = BitVec.ofNat 64 2048 ∧
    s3.getReg .x23 = BitVec.ofNat 64 (C_TD + 2048) ∧
    s3.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ commitPostRandomInstrs, isPureAlu ins = true := by decide
  refine ⟨?_, foldl_pureAlu_mem commitPostRandomInstrs s2 hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (foldl_pureAlu_pc commitPostRandomInstrs s2 (0x1000 + 4 * 14) hall hpc).trans (by decide)
  all_goals (
    simp only [commitPostRandomInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx2, hx8, hx9, hx18, hx26, saltsOff_eq]
    try decide)

theorem commit_phase0 (oracle : Oracle) (message : Message) (extra : Nat) :
    ∃ (postState : BitVec (128 * LENGTH) → MachineState),
      oracle.run (execute (submission.image .commit) (29 + extra) (submission.initialState .commit message) true) =
        (($ᵗ BitVec (128 * LENGTH)) >>= fun packed =>
          (fun p : Execution × Nat => (p.1.charge 33554461 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) extra (postState packed) true)) ∧
      ∀ packed,
        let s := postState packed
        s.pc = BitVec.ofNat 64 (0x1000 + 4 * 29) ∧
        s.getReg .x2 = BitVec.ofNat 64 C_DB ∧
        s.getReg .x5 = 0#64 ∧
        s.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
        s.getReg .x9 = BitVec.ofNat 64 C_TD ∧
        s.getReg .x10 = BitVec.ofNat 64 4000 ∧
        s.getReg .x11 = 96#64 ∧
        s.getReg .x13 = 0#64 ∧
        s.getReg .x18 = BitVec.ofNat 64 (C_TD + saltsOff + 1024) ∧
        s.getReg .x19 = BitVec.ofNat 64 (4000 + 2 ^ 32) ∧
        s.getReg .x20 = BitVec.ofNat 64 4096 ∧
        s.getReg .x21 = BitVec.ofNat 64 2048 ∧
        s.getReg .x23 = BitVec.ofNat 64 (C_TD + 2048) ∧
        s.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        MemPreservedOutside (submission.initialState .commit message) s (C_TD + saltsOff) (C_TD + trapdoorBytes) ∧
        (∀ i : Index, readBuffer s (C_TD + saltsOff + 16 * i.val) 16 = splitBlocks 128 LENGTH packed i) := by
  have hC_TD : C_TD = 4294971424 := rfl
  have hLEN : LENGTH = 16777216 := rfl
  have htd := trapdoorBytes_eq
  let s0 := submission.initialState .commit message
  let s1 := commitPreRandomInstrs.foldl execInstrBr s0
  have hpre : DetRun oracle (submission.image .commit) s0 13 s1 13 0 :=
    commit_preRandom_run oracle s0 (commit_initial_pc message)
  obtain ⟨hs1_pc, hs1_mem, hs1_x2, hs1_x5, hs1_x8, hs1_x9, hs1_x10, hs1_x11, hs1_x18, hs1_x26⟩ :=
    commit_preRandom_spec s0 (commit_initial_pc message) (commit_initial_x2 message)
      (commit_initial_x10 message) (commit_initial_x11 message) (commit_initial_x12 message)
  -- Word 13: ECALL RANDOM(16 * LENGTH bytes at C_TD + saltsOff)
  have hfetch13 : fetch (submission.image .commit) s1 = some (.base .ECALL) :=
    commit_fetch_commitPrefixInstr s1 13 (by omega) (by omega) hs1_pc
  have hrand_valid : randomArgumentsValid s1 = true := by
    unfold randomArgumentsValid rangeValid
    rw [hs1_x10, hs1_x11, saltsOff_eq]
    decide
  have hbytes : (s1.getReg .x11).toNat = 16 * LENGTH := by
    rw [hs1_x11]; decide
  have hwidth : 8 * (s1.getReg .x11).toNat = 128 * LENGTH := by rw [hbytes]; omega
  let postState (packed : BitVec (128 * LENGTH)) : MachineState :=
    commitPostRandomInstrs.foldl execInstrBr (writeBits s1 (BitVec.ofNat 64 (C_TD + saltsOff)) packed)
  refine ⟨postState, ?_, ?_⟩
  · have hsplit : 29 + extra = 13 + (1 + (15 + extra)) := by omega
    rw [hsplit, hpre (1 + (15 + extra)), Nat.add_comm 1 (15 + extra)]
    have hne0 : ¬ (s1.getReg .x5 = (0 : Word)) := by rw [hs1_x5]; decide
    have hne1 : ¬ (s1.getReg .x5 = (1 : Word)) := by rw [hs1_x5]; decide
    have heq2 : s1.getReg .x5 = (2 : Word) := hs1_x5
    have hcond2 : (true && decide (s1.getReg .x5 = (2 : Word)) && randomArgumentsValid s1) = true := by
      rw [heq2, hrand_valid]; rfl
    have hstep13 : execute (submission.image .commit) ((15 + extra) + 1) s1 true =
        (do let answer ← liftM ($ᵗ BitVec (8 * (s1.getReg .x11).toNat) : ProbComp _)
            let res ← execute (submission.image .commit) (15 + extra) (writeBits s1 (s1.getReg .x10) answer) true
            return res.charge (1 + ((s1.getReg .x11).toNat + 7) / 8) 0) := by
      simp only [execute, hfetch13, hne0, hne1, hcond2, ite_false, ite_true]
    rw [hstep13, oracle_run_coins_bind]
    have hcast_bind :
        (do let ans ← ($ᵗ BitVec (8 * (s1.getReg .x11).toNat))
            oracle.run (execute (submission.image .commit) (15 + extra) (writeBits s1 (s1.getReg .x10) ans) true >>=
              fun res => pure (res.charge (1 + ((s1.getReg .x11).toNat + 7) / 8) 0))) =
        (do let packed ← ($ᵗ BitVec (128 * LENGTH))
            oracle.run (execute (submission.image .commit) (15 + extra)
              (writeBits s1 (BitVec.ofNat 64 (C_TD + saltsOff)) packed) true >>=
              fun res => pure (res.charge 33554433 0))) := by
      have hcost : 1 + ((s1.getReg .x11).toNat + 7) / 8 = 33554433 := by rw [hbytes]; decide
      rw [hcost, hs1_x10]
      generalize h : 8 * (s1.getReg .x11).toNat = w at hwidth ⊢
      subst hwidth; rfl
    rw [hcast_bind, map_bind]
    apply bind_congr; intro packed
    let s2 := writeBits s1 (BitVec.ofNat 64 (C_TD + saltsOff)) packed
    have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 14) := pc_step_idx s1 13 hs1_pc
    have hpost : DetRun oracle (submission.image .commit) s2 15 (postState packed) 15 0 :=
      commit_postRandom_run oracle s2 hs2_pc
    have hmap : (execute (submission.image .commit) (15 + extra) s2 true >>=
          fun res => pure (res.charge 33554433 0)) =
        (fun res : Execution => res.charge 33554433 0) <$>
          execute (submission.image .commit) (15 + extra) s2 true := by
      rw [map_eq_bind_pure_comp]; rfl
    rw [hmap, oracle_run_map, hpost extra, Functor.map_map, Functor.map_map]
    refine congrArg (fun fn => fn <$> oracle.run (execute (submission.image .commit) extra (postState packed) true)) ?_
    funext ⟨⟨ex, st, cy, ca⟩, n⟩
    simp only [Execution.charge, Nat.zero_add, Prod.mk.injEq, Execution.mk.injEq]
    exact ⟨⟨trivial, trivial, by omega, trivial⟩, trivial⟩
  · intro packed
    let s2 := writeBits s1 (BitVec.ofNat 64 (C_TD + saltsOff)) packed
    have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 14) := pc_step_idx s1 13 hs1_pc
    obtain ⟨hpc3, hmem3, hx2_3, hx5_3, hx8_3, hx9_3, hx10_3, hx11_3, hx13_3, hx18_3, hx19_3,
      hx20_3, hx21_3, hx23_3, hx26_3⟩ :=
      commit_postRandom_spec s2 hs2_pc
        ((writeBits_register s1 _ packed .x2).trans hs1_x2)
        ((writeBits_register s1 _ packed .x8).trans hs1_x8)
        ((writeBits_register s1 _ packed .x9).trans hs1_x9)
        ((writeBits_register s1 _ packed .x18).trans hs1_x18)
        ((writeBits_register s1 _ packed .x26).trans hs1_x26)
    refine ⟨hpc3, hx2_3, hx5_3, hx8_3, hx9_3, hx10_3, hx11_3, hx13_3, hx18_3, hx19_3,
      hx20_3, hx21_3, hx23_3, hx26_3, ?_, ?_⟩
    · have h1 : MemPreservedOutside s0 s1 (C_TD + saltsOff) (C_TD + trapdoorBytes) :=
        MemPreservedOutside.of_mem_eq hs1_mem _ _
      have h2 : MemPreservedOutside s1 s2 (C_TD + saltsOff) (C_TD + trapdoorBytes) := by
        have hlen : (128 * LENGTH + 7) / 8 = 16 * LENGTH := by omega
        have htr : C_TD + saltsOff + (128 * LENGTH + 7) / 8 = C_TD + trapdoorBytes := by
          rw [hlen]; unfold trapdoorBytes; omega
        simpa [htr] using memPreserved_writeBits s1 (C_TD + saltsOff) packed (by rw [htr]; omega)
      have h3 : MemPreservedOutside s2 (postState packed) (C_TD + saltsOff) (C_TD + trapdoorBytes) :=
        MemPreservedOutside.of_mem_eq hmem3 _ _
      exact (h1.trans h2).trans h3
    · intro i
      rw [readBuffer_of_mem_eq hmem3]
      have h := writeBits_readBuffer_slice s1 (C_TD + saltsOff) (16 * i.val) 16 packed
        (by have := i.isLt; omega) (by omega)
      simpa [splitBlocks, show 8 * (16 * i.val) = 128 * i.val by omega] using h

end CommitGolfCandidate
