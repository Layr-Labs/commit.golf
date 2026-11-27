import CommitGolfCandidate.R4Memory
import CommitGolfCandidate.CountingCoins
import CommitGolfCandidate.Probability
import VCVio.OracleComp.Constructions.SampleableType.Basic

set_option Elab.async false

/-! Deterministic execution engine (`DetRun`), fast `MachineState` step/copy/arithmetic helpers,
memory-framing lemmas (`MemPreservedOutside`), uniform-distribution collapse lemmas (`=ᵈ`),
and exact RV64IM execution proof for Phase 0 of the R4a `commit` image
(setup + `8,388,608` paired `RANDOM(40)` draws + Phase 1A initialization, words 0..32796). -/
namespace CommitGolfCandidate.R4
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

/-- Convenience constants matching `submission.layout`, `rowOff`, and `commit_dataBase`. -/
abbrev C_MSG : Nat := 4096
abbrev C_CMT : Nat := 4294971392
abbrev C_TD  : Nat := 4294971424
abbrev C_ROW : Nat := 5905584160
abbrev C_DB  : Nat := 68719476736

theorem C_ROW_eq : C_ROW = C_TD + rowOff := by
  rw [rowOff_eq]

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

theorem bv64_add_neg256 (n : Nat) (hn : 256 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (3840#12) = BitVec.ofNat 64 (n - 256) := by
  have h : (3840#12 : BitVec 12) = BitVec.ofNat 12 (4096 - 256) := by decide
  rw [h]
  exact add_signExtend12_neg' n 256 (by omega) (by omega) hn

theorem bv64_add_neg96 (n : Nat) (hn : 96 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4000#12) = BitVec.ofNat 64 (n - 96) := by
  have h : (4000#12 : BitVec 12) = BitVec.ofNat 12 (4096 - 96) := by decide
  rw [h]
  exact add_signExtend12_neg' n 96 (by omega) (by omega) hn

theorem bv64_add_neg64 (n : Nat) (hn : 64 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4032#12) = BitVec.ofNat 64 (n - 64) := by
  have h : (4032#12 : BitVec 12) = BitVec.ofNat 12 (4096 - 64) := by decide
  rw [h]
  exact add_signExtend12_neg' n 64 (by omega) (by omega) hn

theorem bv64_add_neg32 (n : Nat) (hn : 32 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4064#12) = BitVec.ofNat 64 (n - 32) := by
  have h : (4064#12 : BitVec 12) = BitVec.ofNat 12 (4096 - 32) := by decide
  rw [h]
  exact add_signExtend12_neg' n 32 (by omega) (by omega) hn

theorem c_bv64_add_neg1 (n : Nat) (hn : 1 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4095#12) = BitVec.ofNat 64 (n - 1) := by
  have h : (4095#12 : BitVec 12) = BitVec.ofNat 12 (4096 - 1) := by decide
  rw [h]
  exact add_signExtend12_neg' n 1 (by omega) (by omega) hn

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

/-! ### 3. Pure-ALU List Execution Helpers -/

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

/-! ### 4. Uniform Distribution Collapse (`=ᵈ`) for Sequential `PairRand` Draws -/

private def snocFn {k : Nat} (acc : Fin k → PairRand) (r : PairRand) : Fin (k + 1) → PairRand :=
  fun i => if h : i.val < k then acc ⟨i.val, h⟩ else r

private def snocEquiv (k : Nat) : ((Fin k → PairRand) × PairRand) ≃ (Fin (k + 1) → PairRand) where
  toFun p := snocFn p.1 p.2
  invFun f := (fun i => f ⟨i.val, by omega⟩, f ⟨k, by omega⟩)
  left_inv := fun ⟨acc, r⟩ => by
    apply Prod.ext
    · funext ⟨i, hi⟩; simp [snocFn, hi]
    · simp [snocFn]
  right_inv := fun f => by
    funext ⟨i, hi⟩
    by_cases h : i < k
    · simp [snocFn, h]
    · have heq : i = k := by omega
      subst heq; simp [snocFn]

private def concatFn (a b : Nat) (f : Fin a → PairRand) (g : Fin b → PairRand) :
    Fin (a + b) → PairRand :=
  fun i => if h : i.val < a then f ⟨i.val, h⟩ else g ⟨i.val - a, by omega⟩

private def concatEquiv (a b : Nat) :
    ((Fin a → PairRand) × (Fin b → PairRand)) ≃ (Fin (a + b) → PairRand) where
  toFun p := concatFn a b p.1 p.2
  invFun h := (fun i => h ⟨i.val, by omega⟩, fun j => h ⟨a + j.val, by omega⟩)
  left_inv := fun ⟨f, g⟩ => by
    apply Prod.ext
    · funext ⟨i, hi⟩; simp [concatFn, hi]
    · funext ⟨j, hj⟩
      have hnot : ¬ (a + j < a) := by omega
      simp [concatFn, hnot]
  right_inv := fun h => by
    funext ⟨i, hi⟩
    by_cases hlt : i < a
    · simp [concatFn, hlt]
    · simp only [concatFn, hlt, dite_false]
      congr 1; apply Fin.ext; dsimp only; omega

private def finFnCastEquiv (n m : Nat) (h : n = m) :
    (Fin n → PairRand) ≃ (Fin m → PairRand) where
  toFun f i := f ⟨i.val, by omega⟩
  invFun g i := g ⟨i.val, by omega⟩
  left_inv f := by funext ⟨i, hi⟩; rfl
  right_inv g := by funext ⟨i, hi⟩; rfl

private theorem uniformSample_fin0_pairRand :
    (pure (fun i : Fin 0 => i.elim0) : ProbComp (Fin 0 → PairRand)) =ᵈ ($ᵗ (Fin 0 → PairRand)) := by
  intro p
  have hall : ∀ f : Fin 0 → PairRand, f = fun i => i.elim0 := fun f => by
    funext i; exact i.elim0
  classical
  rw [prEvent_pure, SampleableType.prEvent_uniformSample]
  have hcard : Fintype.card (Fin 0 → PairRand) = 1 := by
    simp [Fintype.card_fun]
  rw [hcard]
  by_cases hp : p (fun i => i.elim0)
  · rw [if_pos hp]
    have hfilt : (Finset.univ.filter p) = Finset.univ := by
      ext f; simp [hall f, hp]
    rw [hfilt, Finset.card_univ, hcard]; simp
  · rw [if_neg hp]
    have hfilt : (Finset.univ.filter p) = ∅ := by
      ext f; simp [hall f, hp]
    rw [hfilt]; simp

private theorem uniformSample_snoc_pairRand (k : Nat) {α : Type}
    (next : (Fin (k + 1) → PairRand) → ProbComp α) :
    (do let acc ← $ᵗ (Fin k → PairRand)
        let r ← $ᵗ PairRand
        next (snocFn acc r)) =ᵈ (($ᵗ (Fin (k + 1) → PairRand)) >>= next) := by
  have heq : (do let acc ← $ᵗ (Fin k → PairRand)
                 let r ← $ᵗ PairRand
                 next (snocFn acc r)) =
      (((snocEquiv k) <$> ($ᵗ ((Fin k → PairRand) × PairRand))) >>= next) := by
    rw [SampleableType.uniformSample_prod_eq_bind, map_bind, bind_assoc]
    apply bind_congr; intro acc
    rw [map_bind, bind_assoc]
    apply bind_congr; intro r
    simp only [map_pure, pure_bind, snocEquiv, Equiv.coe_fn_mk]
  rw [heq]
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective (snocEquiv k).bijective).bind_left next

private theorem uniformSample_concat_pairRand (a b : Nat) {α : Type}
    (next : (Fin (a + b) → PairRand) → ProbComp α) :
    (do let f ← $ᵗ (Fin a → PairRand)
        let g ← $ᵗ (Fin b → PairRand)
        next (concatFn a b f g)) =ᵈ (($ᵗ (Fin (a + b) → PairRand)) >>= next) := by
  have heq : (do let f ← $ᵗ (Fin a → PairRand)
                 let g ← $ᵗ (Fin b → PairRand)
                 next (concatFn a b f g)) =
      (((concatEquiv a b) <$> ($ᵗ ((Fin a → PairRand) × (Fin b → PairRand)))) >>= next) := by
    rw [SampleableType.uniformSample_prod_eq_bind, map_bind, bind_assoc]
    apply bind_congr; intro f
    rw [map_bind, bind_assoc]
    apply bind_congr; intro g
    simp only [map_pure, pure_bind, concatEquiv, Equiv.coe_fn_mk]
  rw [heq]
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective (concatEquiv a b).bijective).bind_left next

private theorem uniformSample_fin_cast (n m : Nat) (h : n = m) {α : Type}
    (next : (Fin m → PairRand) → ProbComp α) :
    (($ᵗ (Fin n → PairRand)) >>= fun f => next (fun i => f ⟨i.val, by omega⟩)) =ᵈ
      (($ᵗ (Fin m → PairRand)) >>= next) := by
  have heq : (($ᵗ (Fin n → PairRand)) >>= fun f => next (fun i => f ⟨i.val, by omega⟩)) =
      (((finFnCastEquiv n m h) <$> ($ᵗ (Fin n → PairRand))) >>= next) := by
    rw [bind_map_left]; rfl
  rw [heq]
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective (finFnCastEquiv n m h).bijective).bind_left next

/-! ### 5. Exact RV64IM Execution Proof for Phase 0 (words 0..32796) -/

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

private def commitPrefixInstrs : List Instr :=
  [.ADDI .x8 .x10 (0#12), .ADDI .x26 .x11 (0#12), .ADDI .x9 .x12 (0#12),
   .ADDI .x6 .x0 (384#12), .SLLI .x6 .x6 (11#6), .SLLI .x6 .x6 (11#6),
   .ADDI .x6 .x6 (0#12), .ADD .x18 .x9 .x6,
   .ADDI .x5 .x0 (2#12), .ADDI .x10 .x18 (72#12), .ADDI .x11 .x0 (40#12),
   .ADDI .x6 .x0 (368#12), .SLLI .x6 .x6 (11#6), .SLLI .x6 .x6 (11#6),
   .ADDI .x6 .x6 (72#12), .ADD .x19 .x18 .x6]

private def commitMid0Instrs : List Instr :=
  [.ADDI .x5 .x0 (0#12), .ADDI .x11 .x0 (96#12), .ADDI .x13 .x0 (0#12),
   .ADDI .x10 .x8 (3840#12),
   .ADDI .x6 .x0 (1023#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (2047#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (1792#12), .ADD .x19 .x8 .x6]

private theorem commit_prefix_run (oracle : Oracle) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 0)) :
    DetRun oracle (submission.image .commit) s0 16 (commitPrefixInstrs.foldl execInstrBr s0) 16 0 := by
  have hall : ∀ ins ∈ commitPrefixInstrs, isPureAlu ins = true := by decide
  apply exec_alu_list commitPrefixInstrs s0
  intro i hi
  have hi' : i < 16 := hi
  have hpc_i : ((commitPrefixInstrs.take i).foldl execInstrBr s0).pc =
      BitVec.ofNat 64 (0x1000 + 4 * i) := by
    have h := foldl_pureAlu_pc (commitPrefixInstrs.take i) s0 (0x1000 + 4 * 0)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    simpa only [Nat.mul_zero, Nat.add_zero] using h
  interval_cases i <;>
    exact ⟨commit_fetch_commitPrefixInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem commit_prefix_spec (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 0))
    (hx2 : s0.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 C_MSG)
    (hx11 : s0.getReg .x11 = BitVec.ofNat 64 C_CMT)
    (hx12 : s0.getReg .x12 = BitVec.ofNat 64 C_TD) :
    let s1 := commitPrefixInstrs.foldl execInstrBr s0
    s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 16) ∧
    s1.mem = s0.mem ∧
    s1.getReg .x2 = BitVec.ofNat 64 C_DB ∧
    s1.getReg .x5 = 2#64 ∧
    s1.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
    s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s1.getReg .x10 = BitVec.ofNat 64 (C_ROW + 72) ∧
    s1.getReg .x11 = 40#64 ∧
    s1.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
    s1.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes + 72) ∧
    s1.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ commitPrefixInstrs, isPureAlu ins = true := by decide
  refine ⟨?_, foldl_pureAlu_mem commitPrefixInstrs s0 hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (foldl_pureAlu_pc commitPrefixInstrs s0 (0x1000 + 4 * 0) hall hpc).trans (by decide)
  all_goals (
    simp only [commitPrefixInstrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx2, hx10, hx11, hx12, rowBytes_eq]
    try decide)

private theorem commit_mid0_run (oracle : Oracle) (s2 : MachineState)
    (hpc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 32787)) :
    DetRun oracle (submission.image .commit) s2 10 (commitMid0Instrs.foldl execInstrBr s2) 10 0 := by
  have hall : ∀ ins ∈ commitMid0Instrs, isPureAlu ins = true := by decide
  apply exec_alu_list commitMid0Instrs s2
  intro i hi
  have hi' : i < 10 := hi
  have hpc_i : ((commitMid0Instrs.take i).foldl execInstrBr s2).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (32787 + i)) := by
    have h := foldl_pureAlu_pc (commitMid0Instrs.take i) s2 (0x1000 + 4 * 32787)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitMid0Instr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem commit_mid0_spec (s2 : MachineState)
    (hpc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 32787))
    (hx2 : s2.getReg .x2 = BitVec.ofNat 64 C_DB)
    (hx8 : s2.getReg .x8 = BitVec.ofNat 64 C_MSG)
    (hx9 : s2.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx18 : s2.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx26 : s2.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s3 := commitMid0Instrs.foldl execInstrBr s2
    s3.pc = BitVec.ofNat 64 (0x1000 + 4 * 32797) ∧
    s3.mem = s2.mem ∧
    s3.getReg .x2 = BitVec.ofNat 64 C_DB ∧
    s3.getReg .x5 = 0#64 ∧
    s3.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
    s3.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s3.getReg .x10 = BitVec.ofNat 64 (C_MSG - 256) ∧
    s3.getReg .x11 = 96#64 ∧
    s3.getReg .x13 = 0#64 ∧
    s3.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
    s3.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256) ∧
    s3.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ commitMid0Instrs, isPureAlu ins = true := by decide
  refine ⟨?_, foldl_pureAlu_mem commitMid0Instrs s2 hall,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (foldl_pureAlu_pc commitMid0Instrs s2 (0x1000 + 4 * 32787) hall hpc).trans (by decide)
  all_goals (
    simp only [commitMid0Instrs, List.foldl, execInstrBr,
      MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne, c_getReg_x0, ne_eq, not_false_eq_true, reduceCtorEq,
      hx2, hx8, hx9, hx18, hx26]
    try decide)

/-- Deterministic state transformer for one `rand_loop` pair given its drawn 40-byte `PairRand`. -/
private def randPairState (s : MachineState) (r : PairRand) : MachineState :=
  execInstrBr (writeBits s (s.getReg .x10) r) (.ADDI .x10 .x10 (184#12))

private def randChunkBodyState (s : MachineState) : (k : Nat) → (Fin k → PairRand) → MachineState
  | 0, _ => s
  | k + 1, f => randPairState (randChunkBodyState s k (fun i => f ⟨i.val, by omega⟩)) (f ⟨k, by omega⟩)


def latchResult (s : MachineState) (first done : Nat) : MachineState :=
  s.setPC (lpc (if s.getReg .x10 != s.getReg .x19 then first else done))

theorem longRun (o : Oracle) (s : MachineState) (n first : Nat) (enc : LongSite n first)
    (pc : s.pc = lpc n) : DetRun o (submission.image .commit) s 2 (latchResult s first (n+3)) 2 0 := by
  have step := pc_step_idx s n pc
  have skip : s.pc + signExtend13 8 = lpc (n+2) := by
    rw [pc]
    change BitVec.ofNat 64 _ + BitVec.ofNat 64 8 = BitVec.ofNat 64 _
    rw [← BitVec.ofNat_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  by_cases h : (s.getReg .x10 == s.getReg .x19) = true
  · let u := s.setPC (lpc (n+2))
    have b : DetRun o (submission.image .commit) s 1 u 1 0 := by
      apply DetRun.step1 (fetchLong s pc enc.1)
      change some (if _ then _ else _) = some u
      rw [if_pos h,skip]
    have next := pc_step_idx u (n+2) (by rfl)
    refine b.trans (DetRun.step1 (fetchLong u (by rfl) enc.2.2.1) ?_)
    have eq : (s.getReg .x10 != s.getReg .x19)=false := by simp [bne,h]
    change some (u.setPC (u.pc + 4)) = some (latchResult s first (n+3))
    rw [next];simp only [latchResult,eq,Bool.false_eq_true,ite_false];rfl
  · let u := s.setPC (lpc (n+1))
    have b : DetRun o (submission.image .commit) s 1 u 1 0 := by
      apply DetRun.step1 (fetchLong s pc enc.1)
      change some (if _ then _ else _) = some u
      rw [if_neg h,step];rfl
    refine b.trans (DetRun.step1 (fetchLong u (by rfl) enc.2.1) ?_)
    have ne : (s.getReg .x10 != s.getReg .x19)=true := by simp [bne,h]
    change some (u.setPC (lpc (n+1) + signExtend21 (longOff n first))) = some (latchResult s first (n+3))
    rw [enc.2.2.2];simp only [latchResult,ne,ite_true];rfl

private def randChunksState (s : MachineState) : (n : Nat) → (Fin (16384 * n) → PairRand) → MachineState
  | 0, _ => s
  | n + 1, f =>
      latchResult
        (randChunkBodyState
          (randChunksState s n (fun i => f ⟨i.val, by omega⟩))
          16384 (fun j => f ⟨16384 * n + j.val, by omega⟩))
        16 32787

private theorem charge_compose (c1 c2 : Nat) :
    (fun p : Execution × Nat => (p.1.charge c1 0, p.2)) ∘
      (fun p : Execution × Nat => (p.1.charge c2 0, p.2)) =
    (fun p : Execution × Nat => (p.1.charge (c1 + c2) 0, p.2)) := by
  funext ⟨⟨ex, st, cy, ca⟩, n⟩
  simp only [Function.comp_apply, Execution.charge, Nat.zero_add, Prod.mk.injEq, Execution.mk.injEq]
  exact ⟨⟨trivial, trivial, by omega, trivial⟩, trivial⟩

private theorem charge_compose_beta (c1 c2 : Nat) :
    (fun a : Execution × Nat => ((a.1.charge c2 0, a.2).1.charge c1 0, (a.1.charge c2 0, a.2).2)) =
    (fun p : Execution × Nat => (p.1.charge (c1 + c2) 0, p.2)) := by
  funext ⟨⟨ex, st, cy, ca⟩, n⟩
  simp only [Execution.charge, Nat.zero_add, Prod.mk.injEq, Execution.mk.injEq]
  exact ⟨⟨trivial, trivial, by omega, trivial⟩, trivial⟩

/-- One `rand_loop` pair (`ECALL RANDOM(40); ADDI x10, x10, 184`): 2 steps, 7 cycles, 0 oracle calls. -/
private theorem commit_rand_pair_step (oracle : Oracle) (s : MachineState)
    (k pairIdx : Nat) (hk : k < 16384) (hpair : pairIdx < LENGTH / 2)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (16 + 2 * k)))
    (hx5 : s.getReg .x5 = 2#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * pairIdx + 72))
    (hx11 : s.getReg .x11 = 40#64) :
    (∀ extra,
      oracle.run (execute (submission.image .commit) (2 + extra) s true) =
        (($ᵗ PairRand) >>= fun r =>
          (fun p : Execution × Nat => (p.1.charge 7 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) extra (randPairState s r) true))) ∧
    ∀ r : PairRand,
      let s' := randPairState s r
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (16 + 2 * (k + 1))) ∧
      (∀ reg : Reg, reg ≠ .x10 → s'.getReg reg = s.getReg reg) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (pairIdx + 1) + 72) ∧
      readBuffer s' (C_ROW + 184 * pairIdx + 72) 24 = pairSaltEven r ∧
      readBuffer s' (C_ROW + 184 * pairIdx + 88) 24 = pairSaltOdd r ∧
      MemPreservedOutside s s' (C_ROW + 184 * pairIdx + 72) (C_ROW + 184 * pairIdx + 112) := by
  have hCR : C_ROW = 5905584160 := rfl
  have hLEN : LENGTH / 2 = 8388608 := by decide
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have haddr_lt : C_ROW + 184 * pairIdx + 72 < 2 ^ 64 := by omega
  have haddr_bd : C_ROW + 184 * pairIdx + 72 + 40 ≤ MEMORY_BYTES := by omega
  have haddr_toNat : (s.getReg .x10).toNat = C_ROW + 184 * pairIdx + 72 := by
    rw [hx10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr_lt]
  have hx11_toNat : (s.getReg .x11).toNat = 40 := by rw [hx11]; rfl
  have hrand_valid : randomArgumentsValid s = true := by
    unfold randomArgumentsValid rangeValid
    rw [haddr_toNat, hx11_toNat]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, haddr_bd⟩
  have hfetch0 : fetch (submission.image .commit) s = some (.base .ECALL) :=
    commit_fetch_rand s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc)
  constructor
  · intro extra
    have hsplit : 2 + extra = (1 + extra) + 1 := by omega
    rw [hsplit]
    have hne0 : ¬ (s.getReg .x5 = (0 : Word)) := by rw [hx5]; decide
    have hne1 : ¬ (s.getReg .x5 = (1 : Word)) := by rw [hx5]; decide
    have hcond2 : (true && decide (s.getReg .x5 = (2 : Word)) && randomArgumentsValid s) = true := by
      rw [hx5, hrand_valid]; rfl
    have hstep0 : execute (submission.image .commit) ((1 + extra) + 1) s true =
        (do let answer ← liftM ($ᵗ BitVec (8 * (s.getReg .x11).toNat) : ProbComp _)
            let res ← execute (submission.image .commit) (1 + extra) (writeBits s (s.getReg .x10) answer) true
            return res.charge (1 + ((s.getReg .x11).toNat + 7) / 8) 0) := by
      simp only [execute, hfetch0, hne0, hne1, hcond2, ite_false, ite_true]
    rw [hstep0, oracle_run_coins_bind]
    have hwidth : 8 * (s.getReg .x11).toNat = 320 := by rw [hx11_toNat]
    have hcost : 1 + ((s.getReg .x11).toNat + 7) / 8 = 6 := by rw [hx11_toNat]
    have hcast_bind :
        (do let ans ← ($ᵗ BitVec (8 * (s.getReg .x11).toNat))
            oracle.run (execute (submission.image .commit) (1 + extra) (writeBits s (s.getReg .x10) ans) true >>=
              fun res => pure (res.charge (1 + ((s.getReg .x11).toNat + 7) / 8) 0))) =
        (do let r ← ($ᵗ PairRand)
            oracle.run (execute (submission.image .commit) (1 + extra) (writeBits s (s.getReg .x10) r) true >>=
              fun res => pure (res.charge 6 0))) := by
      rw [hcost]
      generalize h : 8 * (s.getReg .x11).toNat = w at hwidth ⊢
      subst hwidth; rfl
    rw [hcast_bind]
    apply bind_congr; intro r
    let s1 := writeBits s (s.getReg .x10) r
    have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (16 + 2 * k + 1)) := pc_step_idx s _ hpc
    have hst1 : DetRun oracle (submission.image .commit) s1 1 (randPairState s r) 1 0 :=
      DetRun.step1 (commit_fetch_rand s1 k 1 hk (by omega) hs1_pc) rfl
    have hmap : (execute (submission.image .commit) (1 + extra) s1 true >>=
          fun res => pure (res.charge 6 0)) =
        (fun res : Execution => res.charge 6 0) <$> execute (submission.image .commit) (1 + extra) s1 true := by
      rw [map_eq_bind_pure_comp]; rfl
    rw [hmap, oracle_run_map, hst1 extra, Functor.map_map]
    refine congrArg (fun fn => fn <$> oracle.run (execute (submission.image .commit) extra (randPairState s r) true)) ?_
    funext ⟨⟨ex, st, cy, ca⟩, n⟩
    simp only [Execution.charge, Nat.zero_add, Prod.mk.injEq, Execution.mk.injEq]
    exact ⟨⟨trivial, trivial, by omega, trivial⟩, trivial⟩
  · intro r
    let s1 := writeBits s (s.getReg .x10) r
    have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (16 + 2 * k + 1)) := pc_step_idx s _ hpc
    have hs1_eq : s1 = writeBits s (BitVec.ofNat 64 (C_ROW + 184 * pairIdx + 72)) r := by
      simp only [s1, hx10]
    have hmem : (randPairState s r).mem = s1.mem := mem_exec_ADDI s1 .x10 .x10 (184#12)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [randPairState, pc_exec_ADDI, pc_step_idx s1 _ hs1_pc]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · intro reg hreg
      have h1 : (randPairState s r).getReg reg = s1.getReg reg := by
        simp only [randPairState, s1, execInstrBr, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 reg (Ne.symm hreg)]
      exact h1.trans (writeBits_register s _ r reg)
    · have hs1_x10 : s1.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * pairIdx + 72) :=
        (writeBits_register s _ r .x10).trans hx10
      simp only [randPairState, s1, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs1_x10,
        add_signExtend12_ofNat_small _ 184 (by omega)]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · rw [readBuffer_of_mem_eq hmem, hs1_eq]
      exact writeBits_readBuffer_pairSaltEven s _ r
    · rw [readBuffer_of_mem_eq hmem, hs1_eq,
        show C_ROW + 184 * pairIdx + 88 = (C_ROW + 184 * pairIdx + 72) + 16 by omega]
      exact writeBits_readBuffer_pairSaltOdd s _ r
    · have hpres1 : MemPreservedOutside s s1 (C_ROW + 184 * pairIdx + 72) (C_ROW + 184 * pairIdx + 112) := by
        rw [hs1_eq]
        simpa only [show C_ROW + 184 * pairIdx + 72 + (320 + 7) / 8 = C_ROW + 184 * pairIdx + 112 by omega] using
          memPreserved_writeBits s (C_ROW + 184 * pairIdx + 72) r (by omega)
      exact hpres1.trans (MemPreservedOutside.of_mem_eq hmem _ _)

/-- One 16,384-pair `rand_loop` body (`words 16..32783`): 32768 steps, 114688 cycles, 0 oracle calls. -/
private theorem commit_rand_chunk_body (oracle : Oracle) (sc : MachineState)
    (chunkIdx : Nat) (hchunk : chunkIdx < 512)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 16))
    (hx5 : sc.getReg .x5 = 2#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (16384 * chunkIdx) + 72))
    (hx11 : sc.getReg .x11 = 40#64) :
    (∀ extra,
      oracle.run (execute (submission.image .commit) (32768 + extra) sc true) =ᵈ
        (($ᵗ (Fin 16384 → PairRand)) >>= fun f =>
          (fun p : Execution × Nat => (p.1.charge 114688 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) extra (randChunkBodyState sc 16384 f) true))) ∧
    ∀ f : Fin 16384 → PairRand,
      let se := randChunkBodyState sc 16384 f
      se.pc = BitVec.ofNat 64 (0x1000 + 4 * 32784) ∧
      (∀ reg : Reg, reg ≠ .x10 → se.getReg reg = sc.getReg reg) ∧
      se.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (16384 * (chunkIdx + 1)) + 72) ∧
      (∀ j : Fin 16384,
        readBuffer se (C_ROW + 184 * (16384 * chunkIdx + j.val) + 72) 24 = pairSaltEven (f j) ∧
        readBuffer se (C_ROW + 184 * (16384 * chunkIdx + j.val) + 88) 24 = pairSaltOdd (f j)) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (∀ j < 16384, q < C_ROW + 184 * (16384 * chunkIdx + j) + 72 ∨
          C_ROW + 184 * (16384 * chunkIdx + j) + 112 ≤ q) →
        se.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
  have hLEN : LENGTH / 2 = 8388608 := by decide
  have hind : ∀ k ≤ 16384,
      (∀ extra,
        oracle.run (execute (submission.image .commit) (2 * k + extra) sc true) =ᵈ
          (($ᵗ (Fin k → PairRand)) >>= fun f =>
            (fun p : Execution × Nat => (p.1.charge (7 * k) 0, p.2)) <$>
              oracle.run (execute (submission.image .commit) extra (randChunkBodyState sc k f) true))) ∧
      ∀ f : Fin k → PairRand,
        let sk := randChunkBodyState sc k f
        sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (16 + 2 * k)) ∧
        (∀ reg : Reg, reg ≠ .x10 → sk.getReg reg = sc.getReg reg) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (16384 * chunkIdx + k) + 72) ∧
        (∀ j : Fin k,
          readBuffer sk (C_ROW + 184 * (16384 * chunkIdx + j.val) + 72) 24 = pairSaltEven (f j) ∧
          readBuffer sk (C_ROW + 184 * (16384 * chunkIdx + j.val) + 88) 24 = pairSaltOdd (f j)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ j < k, q < C_ROW + 184 * (16384 * chunkIdx + j) + 72 ∨
            C_ROW + 184 * (16384 * chunkIdx + j) + 112 ≤ q) →
          sk.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
    intro k hk; induction k with
    | zero =>
      constructor
      · intro extra
        have hid : (fun p : Execution × Nat => (p.1.charge 0 0, p.2)) = id := by
          funext ⟨⟨ex, st, cy, ca⟩, n⟩; simp only [Execution.charge, Nat.zero_add, id_eq]
        simpa only [Nat.mul_zero, Nat.zero_add, hid, id_map, randChunkBodyState, pure_bind] using
          uniformSample_fin0_pairRand.bind_left
            (fun _ => oracle.run (execute (submission.image .commit) extra sc true))
      · intro f
        dsimp only [randChunkBodyState]
        exact ⟨by simpa using hpc, fun _ _ => rfl, by simpa using hx10,
          fun j => j.elim0, fun _ _ _ => rfl⟩
    | succ k ih =>
      obtain ⟨hrun_k, hspec_k⟩ := ih (by omega)
      have hstep_all : ∀ acc : Fin k → PairRand,
          let sk := randChunkBodyState sc k acc
          (∀ extra,
            oracle.run (execute (submission.image .commit) (2 + extra) sk true) =
              (($ᵗ PairRand) >>= fun r =>
                (fun p : Execution × Nat => (p.1.charge 7 0, p.2)) <$>
                  oracle.run (execute (submission.image .commit) extra (randPairState sk r) true))) ∧
          ∀ r : PairRand,
            let s' := randPairState sk r
            s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (16 + 2 * (k + 1))) ∧
            (∀ reg : Reg, reg ≠ .x10 → s'.getReg reg = sk.getReg reg) ∧
            s'.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (16384 * chunkIdx + k + 1) + 72) ∧
            readBuffer s' (C_ROW + 184 * (16384 * chunkIdx + k) + 72) 24 = pairSaltEven r ∧
            readBuffer s' (C_ROW + 184 * (16384 * chunkIdx + k) + 88) 24 = pairSaltOdd r ∧
            MemPreservedOutside sk s' (C_ROW + 184 * (16384 * chunkIdx + k) + 72)
              (C_ROW + 184 * (16384 * chunkIdx + k) + 112) := by
        intro acc
        obtain ⟨hpck, hregk, hx10k, _, _⟩ := hspec_k acc
        exact commit_rand_pair_step oracle (randChunkBodyState sc k acc) k (16384 * chunkIdx + k)
          (by omega) (by omega) hpck
          ((hregk .x5 (by decide)).trans hx5) hx10k ((hregk .x11 (by decide)).trans hx11)
      constructor
      · intro extra
        have hsplit : 2 * (k + 1) + extra = 2 * k + (2 + extra) := by omega
        rw [hsplit]
        refine (hrun_k (2 + extra)).trans ?_
        have hstep_eq :
            (($ᵗ (Fin k → PairRand)) >>= fun acc =>
              (fun p : Execution × Nat => (p.1.charge (7 * k) 0, p.2)) <$>
                oracle.run (execute (submission.image .commit) (2 + extra) (randChunkBodyState sc k acc) true)) =
            (do let acc ← $ᵗ (Fin k → PairRand)
                let r ← $ᵗ PairRand
                (fun p : Execution × Nat => (p.1.charge (7 * (k + 1)) 0, p.2)) <$>
                  oracle.run (execute (submission.image .commit) extra
                    (randChunkBodyState sc (k + 1) (snocFn acc r)) true)) := by
          apply bind_congr; intro acc
          rw [(hstep_all acc).1 extra, map_bind]
          apply bind_congr; intro r
          rw [Functor.map_map, charge_compose_beta]
          have hst_eq : randChunkBodyState sc (k + 1) (snocFn acc r) =
              randPairState (randChunkBodyState sc k acc) r := by
            conv_lhs => unfold randChunkBodyState
            have h1 : (fun i : Fin k => snocFn acc r ⟨i.val, by omega⟩) = acc := by
              funext ⟨i, hi⟩; simp [snocFn, hi]
            have h2 : snocFn acc r ⟨k, by omega⟩ = r := by simp [snocFn]
            rw [h1, h2]
          rw [hst_eq, show 7 * k + 7 = 7 * (k + 1) by omega]
        rw [hstep_eq]
        exact uniformSample_snoc_pairRand k (fun f =>
          (fun p : Execution × Nat => (p.1.charge (7 * (k + 1)) 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) extra (randChunkBodyState sc (k + 1) f) true))
      · intro f
        dsimp only [randChunkBodyState]
        let acc : Fin k → PairRand := fun i => f ⟨i.val, by omega⟩
        let r : PairRand := f ⟨k, by omega⟩
        obtain ⟨hpck, hregk, hx10k, hsaltk, hpresk⟩ := hspec_k acc
        obtain ⟨hpc', hreg', hx10', hev', hodd', hpres'⟩ := (hstep_all acc).2 r
        refine ⟨hpc', fun reg hr => (hreg' reg hr).trans (hregk reg hr),
          by simpa only [Nat.add_assoc] using hx10', ?_, ?_⟩
        · intro ⟨j, hj⟩
          have hCR : C_ROW = 5905584160 := rfl
          dsimp only
          by_cases hjk : j < k
          · obtain ⟨hevj, hoddj⟩ := hsaltk ⟨j, hjk⟩
            dsimp only at hevj hoddj
            exact ⟨(hpres'.readBuffer_eq (by omega) (by omega)).trans hevj,
                   (hpres'.readBuffer_eq (by omega) (by omega)).trans hoddj⟩
          · have heqj : j = k := by omega
            subst heqj
            exact ⟨hev', hodd'⟩
        · intro q hq hout
          have h1 := hpres' q hq (hout k (by omega))
          have h2 := hpresk q hq (fun j hj => hout j (by omega))
          exact h1.trans h2
  exact hind 16384 (le_refl _)

/-- Isolated `BNE x10, x19, 4096#13` latch at word `32784` (`1` step, `1` cycle). -/
private theorem commit_rand_chunk_bne (oracle : Oracle) (chunkIdx : Nat) (hchunk : chunkIdx < 512)
    (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 32784))
    (hx10 : se.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (16384 * (chunkIdx + 1)) + 72))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes + 72)) :
    let sbne := latchResult se 16 32787
    DetRun oracle (submission.image .commit) se 2 sbne 2 0 ∧
    sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if chunkIdx + 1 < 512 then 16 else 32787)) ∧
    sbne.mem = se.mem ∧
    (∀ reg : Reg, sbne.getReg reg = se.getReg reg) := by
  have hCR : C_ROW = 5905584160 := rfl
  have hrb := rowBytes_eq
  let sbne := latchResult se 16 32787
  have hstep : DetRun oracle (submission.image .commit) se 2 sbne 2 0 :=
    longRun oracle se 32784 16 (by decide +kernel) hpc
  have hpc_end : sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if chunkIdx + 1 < 512 then 16 else 32787)) := by
    by_cases hlt : chunkIdx + 1 < 512
    · have hne : (se.getReg .x10 != se.getReg .x19) = true := by
        rw [hx10, hx19, bne_iff_ne]
        exact bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
      simp [sbne,latchResult,lpc,hne,hlt,pc_setPC]
    · have hc : chunkIdx = 511 := by omega
      have heq : (se.getReg .x10 != se.getReg .x19) = false := by
        rw [hx10, hx19, hc, hrb]
        exact bne_self_eq_false _
      simp [sbne,latchResult,lpc,heq,hlt,pc_setPC]
  exact ⟨hstep, hpc_end, rfl, fun _ => rfl⟩

private theorem half_len_eq : LENGTH / 2 = 16384 * 512 := by decide

private def castHalfLen (rand : Fin (LENGTH / 2) → PairRand) : Fin (16384 * 512) → PairRand :=
  fun i => rand ⟨i.val, by rw [half_len_eq]; exact i.isLt⟩

/-- Full `rand_loop` (`512` chunks × `16,384` pairs = `8,388,608` `RANDOM(40)` draws,
words `16..32786`): `16,778,240` steps, `58,721,280` cycles, `0` oracle calls. -/
private theorem commit_rand_loop (oracle : Oracle) (s1 : MachineState)
    (hpc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 16))
    (hx5 : s1.getReg .x5 = 2#64)
    (hx10 : s1.getReg .x10 = BitVec.ofNat 64 (C_ROW + 72))
    (hx11 : s1.getReg .x11 = 40#64)
    (hx19 : s1.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes + 72)) :
    (∀ extra,
      oracle.run (execute (submission.image .commit) (16778240 + extra) s1 true) =ᵈ
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          (fun p : Execution × Nat => (p.1.charge 58721280 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) extra
              (randChunksState s1 512 (castHalfLen rand)) true))) ∧
    ∀ rand : Fin (LENGTH / 2) → PairRand,
      let s2 := randChunksState s1 512 (castHalfLen rand)
      s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 32787) ∧
      (∀ reg : Reg, reg ≠ .x10 → s2.getReg reg = s1.getReg reg) ∧
      (∀ j : Fin (LENGTH / 2),
        readBuffer s2 (C_ROW + 184 * j.val + 72) 24 = pairSaltEven (rand j) ∧
        readBuffer s2 (C_ROW + 184 * j.val + 88) 24 = pairSaltOdd (rand j)) ∧
      (∀ q : Nat, q < 2 ^ 64 →
        (∀ j < LENGTH / 2, q < C_ROW + 184 * j + 72 ∨ C_ROW + 184 * j + 112 ≤ q) →
        s2.getByte (BitVec.ofNat 64 q) = s1.getByte (BitVec.ofNat 64 q)) := by
  have hLEN := half_len_eq
  have hind : ∀ n ≤ 512,
      (∀ extra,
        oracle.run (execute (submission.image .commit) (32770 * n + extra) s1 true) =ᵈ
          (($ᵗ (Fin (16384 * n) → PairRand)) >>= fun f =>
            (fun p : Execution × Nat => (p.1.charge (114690 * n) 0, p.2)) <$>
              oracle.run (execute (submission.image .commit) extra (randChunksState s1 n f) true))) ∧
      ∀ f : Fin (16384 * n) → PairRand,
        let sn := randChunksState s1 n f
        sn.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n < 512 then 16 else 32787)) ∧
        (∀ reg : Reg, reg ≠ .x10 → sn.getReg reg = s1.getReg reg) ∧
        sn.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (16384 * n) + 72) ∧
        (∀ j : Fin (16384 * n),
          readBuffer sn (C_ROW + 184 * j.val + 72) 24 = pairSaltEven (f j) ∧
          readBuffer sn (C_ROW + 184 * j.val + 88) 24 = pairSaltOdd (f j)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ j < 16384 * n, q < C_ROW + 184 * j + 72 ∨ C_ROW + 184 * j + 112 ≤ q) →
          sn.getByte (BitVec.ofNat 64 q) = s1.getByte (BitVec.ofNat 64 q)) := by
    intro n hn; induction n with
    | zero =>
      constructor
      · intro extra
        have hid : (fun p : Execution × Nat => (p.1.charge 0 0, p.2)) = id := by
          funext ⟨⟨ex, st, cy, ca⟩, m⟩; simp only [Execution.charge, Nat.zero_add, id_eq]
        simpa only [Nat.mul_zero, Nat.zero_add, hid, id_map, randChunksState, pure_bind] using
          uniformSample_fin0_pairRand.bind_left
            (fun _ => oracle.run (execute (submission.image .commit) extra s1 true))
      · intro f
        dsimp only [randChunksState]
        exact ⟨by simpa only [show (0 : Nat) < 512 by decide, ite_true] using hpc,
          fun _ _ => rfl, by simpa only [Nat.mul_zero, Nat.add_zero] using hx10,
          fun j => j.elim0, fun _ _ _ => rfl⟩
    | succ n ih =>
      obtain ⟨hrun_n, hspec_n⟩ := ih (by omega)
      have hchunk_all : ∀ acc : Fin (16384 * n) → PairRand,
          let sn := randChunksState s1 n acc
          (∀ extra,
            oracle.run (execute (submission.image .commit) (32770 + extra) sn true) =ᵈ
              (($ᵗ (Fin 16384 → PairRand)) >>= fun ch =>
                (fun p : Execution × Nat => (p.1.charge 114690 0, p.2)) <$>
                  oracle.run (execute (submission.image .commit) extra
                    (latchResult (randChunkBodyState sn 16384 ch) 16 32787) true))) ∧
          ∀ ch : Fin 16384 → PairRand,
            let sbne := latchResult (randChunkBodyState sn 16384 ch) 16 32787
            sbne.pc = BitVec.ofNat 64 (0x1000 + 4 * (if n + 1 < 512 then 16 else 32787)) ∧
            (∀ reg : Reg, reg ≠ .x10 → sbne.getReg reg = sn.getReg reg) ∧
            sbne.getReg .x10 = BitVec.ofNat 64 (C_ROW + 184 * (16384 * (n + 1)) + 72) ∧
            (∀ j : Fin 16384,
              readBuffer sbne (C_ROW + 184 * (16384 * n + j.val) + 72) 24 = pairSaltEven (ch j) ∧
              readBuffer sbne (C_ROW + 184 * (16384 * n + j.val) + 88) 24 = pairSaltOdd (ch j)) ∧
            (∀ q : Nat, q < 2 ^ 64 →
              (∀ j < 16384, q < C_ROW + 184 * (16384 * n + j) + 72 ∨
                C_ROW + 184 * (16384 * n + j) + 112 ≤ q) →
              sbne.getByte (BitVec.ofNat 64 q) = sn.getByte (BitVec.ofNat 64 q)) := by
        intro acc
        obtain ⟨hpcn, hregn, hx10n, _, _⟩ := hspec_n acc
        have hpcn' : (randChunksState s1 n acc).pc = BitVec.ofNat 64 (0x1000 + 4 * 16) := by
          simpa only [show n < 512 by omega, ite_true] using hpcn
        obtain ⟨hbody_run, hbody_spec⟩ := commit_rand_chunk_body oracle (randChunksState s1 n acc) n (by omega)
          hpcn' ((hregn .x5 (by decide)).trans hx5) hx10n ((hregn .x11 (by decide)).trans hx11)
        constructor
        · intro extra
          have hsp : 32770 + extra = 32768 + (2 + extra) := by omega
          rw [hsp]
          refine (hbody_run (2 + extra)).trans ?_
          apply EvalDistEq.bind_right
          intro ch
          obtain ⟨hpce, hrege, hx10e, _, _⟩ := hbody_spec ch
          obtain ⟨hbne_run, _, _, _⟩ := commit_rand_chunk_bne oracle n (by omega)
            (randChunkBodyState (randChunksState s1 n acc) 16384 ch) hpce hx10e
            ((hrege .x19 (by decide)).trans ((hregn .x19 (by decide)).trans hx19))
          rw [hbne_run extra, Functor.map_map]
          have hfn : (fun a : Execution × Nat =>
                ((a.1.charge 2 0, 0 + a.2).1.charge 114688 0, (a.1.charge 2 0, 0 + a.2).2)) =
              (fun p : Execution × Nat => (p.1.charge 114690 0, p.2)) := by
            funext ⟨⟨ex, st, cy, ca⟩, m⟩
            simp only [Execution.charge, Nat.zero_add, Prod.mk.injEq, Execution.mk.injEq]
            exact ⟨⟨trivial, trivial, by omega, trivial⟩, trivial⟩
          rw [hfn]
        · intro ch
          obtain ⟨hpce, hrege, hx10e, hsalte, hprese⟩ := hbody_spec ch
          obtain ⟨_, hpc_end, hmem_bne, hreg_bne⟩ := commit_rand_chunk_bne oracle n (by omega)
            (randChunkBodyState (randChunksState s1 n acc) 16384 ch) hpce hx10e
            ((hrege .x19 (by decide)).trans ((hregn .x19 (by decide)).trans hx19))
          refine ⟨hpc_end, fun reg hr => (hreg_bne reg).trans (hrege reg hr),
            (hreg_bne .x10).trans hx10e, ?_, ?_⟩
          · intro j
            rw [readBuffer_of_mem_eq hmem_bne, readBuffer_of_mem_eq hmem_bne]
            exact hsalte j
          · intro q hq hout
            rw [getByte_of_mem_eq hmem_bne]
            exact hprese q hq hout
      constructor
      · intro extra
        have hsplit : 32770 * (n + 1) + extra = 32770 * n + (32770 + extra) := by omega
        rw [hsplit]
        refine (hrun_n (32770 + extra)).trans ?_
        have hstep_d :
            (($ᵗ (Fin (16384 * n) → PairRand)) >>= fun acc =>
              (fun p : Execution × Nat => (p.1.charge (114690 * n) 0, p.2)) <$>
                oracle.run (execute (submission.image .commit) (32770 + extra) (randChunksState s1 n acc) true)) =ᵈ
            (do let acc ← $ᵗ (Fin (16384 * n) → PairRand)
                let ch ← $ᵗ (Fin 16384 → PairRand)
                (fun p : Execution × Nat => (p.1.charge (114690 * (n + 1)) 0, p.2)) <$>
                  oracle.run (execute (submission.image .commit) extra
                    (randChunksState s1 (n + 1) (concatFn (16384 * n) 16384 acc ch)) true)) := by
          apply EvalDistEq.bind_right; intro acc
          refine ((hchunk_all acc).1 extra).map _ |>.trans ?_
          rw [map_bind]
          apply EvalDistEq.bind_right; intro ch
          rw [Functor.map_map, charge_compose_beta]
          have hst_eq : randChunksState s1 (n + 1) (concatFn (16384 * n) 16384 acc ch) =
              latchResult (randChunkBodyState (randChunksState s1 n acc) 16384 ch) 16 32787 := by
            conv_lhs => unfold randChunksState
            have h1 : (fun i : Fin (16384 * n) => concatFn (16384 * n) 16384 acc ch ⟨i.val, by omega⟩) = acc := by
              funext ⟨i, hi⟩; simp [concatFn, hi]
            have h2 : (fun j : Fin 16384 => concatFn (16384 * n) 16384 acc ch ⟨16384 * n + j.val, by omega⟩) = ch := by
              funext ⟨j, hj⟩
              have hnot : ¬ (16384 * n + j < 16384 * n) := by omega
              simp [concatFn, hnot]
            rw [h1, h2]
          rw [hst_eq, show 114690 * n + 114690 = 114690 * (n + 1) by omega]
        exact hstep_d.trans (uniformSample_concat_pairRand (16384 * n) 16384 (fun f =>
          (fun p : Execution × Nat => (p.1.charge (114690 * (n + 1)) 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) extra (randChunksState s1 (n + 1) f) true)))
      · intro f
        let acc : Fin (16384 * n) → PairRand := fun i => f ⟨i.val, by omega⟩
        let ch : Fin 16384 → PairRand := fun j => f ⟨16384 * n + j.val, by omega⟩
        obtain ⟨hpcn, hregn, hx10n, hsaltn, hpresn⟩ := hspec_n acc
        obtain ⟨hpc', hreg', hx10', hsalt', hpres'⟩ := (hchunk_all acc).2 ch
        refine ⟨hpc', fun reg hr => (hreg' reg hr).trans (hregn reg hr), hx10', ?_, ?_⟩
        · intro ⟨j, hj⟩
          have hCR : C_ROW = 5905584160 := rfl
          dsimp only [randChunksState]
          by_cases hjn : j < 16384 * n
          · obtain ⟨hevj, hoddj⟩ := hsaltn ⟨j, hjn⟩
            refine ⟨?_, ?_⟩
            · exact (readBuffer_congr _ _ (C_ROW + 184 * j + 72) 24 (fun b hb => hpres' (C_ROW + 184 * j + 72 + b) (by omega)
                (fun j' _ => by omega))).trans hevj
            · exact (readBuffer_congr _ _ (C_ROW + 184 * j + 88) 24 (fun b hb => hpres' (C_ROW + 184 * j + 88 + b) (by omega)
                (fun j' _ => by omega))).trans hoddj
          · have hsub : j - 16384 * n < 16384 := by omega
            have heqj : 16384 * n + (j - 16384 * n) = j := by omega
            simpa only [acc, ch, heqj] using hsalt' ⟨j - 16384 * n, hsub⟩
        · intro q hq hout
          have h1 := hpres' q hq (fun j hj => hout (16384 * n + j) (by omega))
          have h2 := hpresn q hq (fun j hj => hout j (by omega))
          exact h1.trans h2
  obtain ⟨hrun_full, hspec_full⟩ := hind 512 (le_refl _)
  constructor
  · intro extra
    refine (hrun_full extra).trans ?_
    exact (uniformSample_fin_cast (LENGTH / 2) (16384 * 512) hLEN (fun f =>
      (fun p : Execution × Nat => (p.1.charge 58721280 0, p.2)) <$>
        oracle.run (execute (submission.image .commit) extra (randChunksState s1 512 f) true))).symm
  · intro rand
    obtain ⟨hpc2, hreg2, _, hsalt2, hpres2⟩ := hspec_full (castHalfLen rand)
    refine ⟨by simpa only [Nat.lt_irrefl, ite_false] using hpc2, hreg2, ?_, ?_⟩
    · intro ⟨j, hj⟩
      simpa only [castHalfLen] using hsalt2 ⟨j, by omega⟩
    · intro q hq hout
      exact hpres2 q hq (fun j hj => hout j (by omega))

/-- Full Phase 0 (`words 0..32796`): prefix (`0..15`) + `8,388,608` paired `RANDOM(40)` draws
(`16..32786`) + Phase 1A setup (`32787..32796`). Exact `16,778,266` steps, `58,721,306` cycles,
`0` public oracle calls, collapsing in distribution (`=ᵈ`) to `$ᵗ (Fin (LENGTH / 2) → PairRand)`. -/
theorem commit_phase0 (oracle : Oracle) (message : Message) (extra : Nat) :
    ∃ (postState : (Fin (LENGTH / 2) → PairRand) → MachineState),
      oracle.run (execute (submission.image .commit) (16778266 + extra)
          (submission.initialState .commit message) true) =ᵈ
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          (fun p : Execution × Nat => (p.1.charge 58721306 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) extra (postState rand) true)) ∧
      ∀ rand,
        let s := postState rand
        s.pc = BitVec.ofNat 64 (0x1000 + 4 * 32797) ∧
        s.getReg .x2 = BitVec.ofNat 64 C_DB ∧
        s.getReg .x5 = 0#64 ∧
        s.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
        s.getReg .x9 = BitVec.ofNat 64 C_TD ∧
        s.getReg .x10 = BitVec.ofNat 64 (C_MSG - 256) ∧
        s.getReg .x11 = 96#64 ∧
        s.getReg .x13 = 0#64 ∧
        s.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
        s.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 256) ∧
        s.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        (∀ j : Fin (LENGTH / 2),
          readBuffer s (C_ROW + 184 * j.val + 72) 24 = pairSaltEven (rand j) ∧
          readBuffer s (C_ROW + 184 * j.val + 88) 24 = pairSaltOdd (rand j)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ j < LENGTH / 2, q < C_ROW + 184 * j + 72 ∨ C_ROW + 184 * j + 112 ≤ q) →
          s.getByte (BitVec.ofNat 64 q) = (submission.initialState .commit message).getByte (BitVec.ofNat 64 q)) := by
  let s0 := submission.initialState .commit message
  let s1 := commitPrefixInstrs.foldl execInstrBr s0
  have hpre : DetRun oracle (submission.image .commit) s0 16 s1 16 0 :=
    commit_prefix_run oracle s0 (commit_initial_pc message)
  obtain ⟨hs1_pc, hs1_mem, hs1_x2, hs1_x5, hs1_x8, hs1_x9, hs1_x10, hs1_x11, hs1_x18, hs1_x19, hs1_x26⟩ :=
    commit_prefix_spec s0 (commit_initial_pc message) (commit_initial_x2 message)
      (commit_initial_x10 message) (commit_initial_x11 message) (commit_initial_x12 message)
  obtain ⟨hloop_run, hloop_spec⟩ :=
    commit_rand_loop oracle s1 hs1_pc hs1_x5 hs1_x10 hs1_x11 hs1_x19
  let postState (rand : Fin (LENGTH / 2) → PairRand) : MachineState :=
    commitMid0Instrs.foldl execInstrBr (randChunksState s1 512 (castHalfLen rand))
  refine ⟨postState, ?_, ?_⟩
  · have hsplit : 16778266 + extra = 16 + (16778240 + (10 + extra)) := by omega
    rw [hsplit, hpre (16778240 + (10 + extra))]
    refine ((hloop_run (10 + extra)).map _).trans ?_
    rw [map_bind]
    apply EvalDistEq.bind_right; intro rand
    obtain ⟨hpc2, _, _, _⟩ := hloop_spec rand
    have hmid : DetRun oracle (submission.image .commit)
        (randChunksState s1 512 (castHalfLen rand)) 10 (postState rand) 10 0 :=
      commit_mid0_run oracle _ hpc2
    rw [hmid extra, Functor.map_map, Functor.map_map]
    have hfn :
        (fun a : Execution × Nat =>
          (((a.1.charge 10 0, 0 + a.2).1.charge 58721280 0, (a.1.charge 10 0, 0 + a.2).2).1.charge 16 0,
            0 + ((a.1.charge 10 0, 0 + a.2).1.charge 58721280 0, (a.1.charge 10 0, 0 + a.2).2).2)) =
        (fun p : Execution × Nat => (p.1.charge 58721306 0, p.2)) := by
      funext ⟨⟨ex, st, cy, ca⟩, n⟩
      simp only [Execution.charge, Nat.zero_add, Prod.mk.injEq, Execution.mk.injEq]
      exact ⟨⟨trivial, trivial, by omega, trivial⟩, trivial⟩
    rw [hfn]
  · intro rand
    let s2 := randChunksState s1 512 (castHalfLen rand)
    obtain ⟨hpc2, hreg2, hsalt2, hpres2⟩ := hloop_spec rand
    obtain ⟨hpc3, hmem3, hx2_3, hx5_3, hx8_3, hx9_3, hx10_3, hx11_3, hx13_3, hx18_3, hx19_3, hx26_3⟩ :=
      commit_mid0_spec s2 hpc2
        ((hreg2 .x2 (by decide)).trans hs1_x2)
        ((hreg2 .x8 (by decide)).trans hs1_x8)
        ((hreg2 .x9 (by decide)).trans hs1_x9)
        ((hreg2 .x18 (by decide)).trans hs1_x18)
        ((hreg2 .x26 (by decide)).trans hs1_x26)
    refine ⟨hpc3, hx2_3, hx5_3, hx8_3, hx9_3, hx10_3, hx11_3, hx13_3, hx18_3, hx19_3, hx26_3, ?_, ?_⟩
    · intro j
      rw [readBuffer_of_mem_eq hmem3, readBuffer_of_mem_eq hmem3]
      exact hsalt2 j
    · intro q hq hout
      rw [getByte_of_mem_eq hmem3, hpres2 q hq hout, getByte_of_mem_eq hs1_mem]

end CommitGolfCandidate.R4
