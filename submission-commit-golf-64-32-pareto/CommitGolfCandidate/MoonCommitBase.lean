import CommitGolfCandidate.MoonMemory
import CommitGolfCandidate.CountingCoins
import CommitGolfCandidate.Probability
import VCVio.OracleComp.Constructions.SampleableType.Basic

/-! Deterministic execution engine (`DetRun`), fast `c_`-prefixed `MachineState` step/copy/arithmetic
helpers, memory-framing (`CommitMemOutside`), uniform distribution collapse (`=ᵈ`), and exact RV64IM
execution proof for Phase 0 of the 64-32 `commit` image (setup + `8,388,608` paired `RANDOM(40)`
draws + Phase 1A setup, words `0..4121`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-! ### 1. Deterministic `oracle.run` Composition Engine (`DetRun`) -/

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

private theorem c_readBuffer_toNat_congr (s : MachineState) (src : Nat) {n1 n2 : Nat} (h : n1 = n2) :
    (readBuffer s src n1).toNat = (readBuffer s src n2).toNat := by
  subst h; rfl

private theorem c_ofNat_toNat_cast {n m : Nat} (h : n = m) (v : BitVec n) :
    BitVec.ofNat m v.toNat = v.cast h := by
  subst h
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_cast]
  exact Nat.mod_eq_of_lt v.isLt

private theorem c_ofNat_toNat_eq {n : Nat} (v : BitVec n) :
    BitVec.ofNat n v.toNat = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt v.isLt

theorem DetRun.compress (h512 : COMPRESSION_INPUT_LENGTH = 512)
    {oracle : Oracle} {img : Image} {s : MachineState}
    (hfetch : fetch img s = some (.base .ECALL))
    (hx5 : s.getReg .x5 = 0#64)
    (hx11 : s.getReg .x11 = 64#64)
    (hx13 : s.getReg .x13 = 0#64)
    (src dst : Nat)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 8 = 0) (hdst_al : dst % 8 = 0)
    (hsrc_bd : src + 64 ≤ MEMORY_BYTES) (hdst_bd : dst + 32 ≤ MEMORY_BYTES) :
    DetRun oracle img s 1
      (writeBits s (BitVec.ofNat 64 dst)
        (oracle.compression ((readBuffer s src 64).cast h512.symm)))
      8 1 := by
  intro extra
  have hsrc_lt : src < 2 ^ 64 := by unfold MEMORY_BYTES at hsrc_bd; omega
  have hdst_lt : dst < 2 ^ 64 := by unfold MEMORY_BYTES at hdst_bd; omega
  have hsrc_toNat : (s.getReg .x10).toNat = src := by
    rw [hx10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc_lt]
  have hdst_toNat : (s.getReg .x12).toNat = dst := by
    rw [hx12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdst_lt]
  have hrv_src : rangeValid (s.getReg .x10) 64 = true := by
    unfold rangeValid; rw [hsrc_toNat]; exact decide_eq_true hsrc_bd
  have hrv_dst : rangeValid (s.getReg .x12) 32 = true := by
    unfold rangeValid; rw [hdst_toNat]; exact decide_eq_true hdst_bd
  have hoinp : oracleInput s = some (Sum.inl ((readBuffer s src 64).cast h512.symm)) := by
    unfold oracleInput
    dsimp only
    have hk : (s.getReg .x13).toNat = 0 := by rw [hx13]; rfl
    have hlen : (s.getReg .x11).toNat = 64 := by rw [hx11]; rfl
    have hinb : (COMPRESSION_INPUT_LENGTH + 7) / 8 = 64 := by rw [h512]
    have hinb_full :
        (((if (s.getReg .x13).toNat = 0 then COMPRESSION_INPUT_LENGTH else PERMUTATION_WIDTH) + 7) / 8) = 64 := by
      rw [hk]; simp only [ite_true]; exact hinb
    have houtb : (COMPRESSION_OUTPUT_LENGTH + 7) / 8 = 32 := by rfl
    simp only [hk, ite_true, hsrc_toNat]
    rw [c_readBuffer_toNat_congr s src hinb_full]
    simp only [hinb, houtb, hlen, hdst_toNat, hsrc_al, hdst_al,
      hrv_src, hrv_dst, Nat.zero_le, and_self, ite_true]
    exact congrArg (fun x : BitVec COMPRESSION_INPUT_LENGTH => (some (Sum.inl x) : Option PublicSpec.Domain))
      (c_ofNat_toNat_cast (show 8 * 64 = COMPRESSION_INPUT_LENGTH by rw [h512]) (readBuffer s src 64))
  rw [Nat.add_comm 1 extra]
  have hx5' : s.getReg .x5 = (0 : Word) := hx5
  simp only [execute, hfetch, hx5', ite_true, hoinp]
  change oracle.run ((liftM (World.query (.inr (Sum.inl ((readBuffer s src 64).cast h512.symm)))) : OracleComp World _) >>=
    fun ans => execute img extra (writeBits s (s.getReg .x12) ans) true >>= fun res =>
      pure (res.charge COMPRESSION_CYCLES 1)) = _
  rw [oracle_run_public_bind, hx12]
  change (oracle.run (execute img extra
      (writeBits s (BitVec.ofNat 64 dst) (oracle.compression ((readBuffer s src 64).cast h512.symm))) true >>=
      fun res => pure (res.charge 8 1)) >>= fun p => pure (p.1, 1 + p.2)) = _
  have hmap : (execute img extra
        (writeBits s (BitVec.ofNat 64 dst) (oracle.compression ((readBuffer s src 64).cast h512.symm))) true >>=
        fun res => pure (res.charge 8 1)) =
      (fun res : Execution => res.charge 8 1) <$>
        execute img extra
          (writeBits s (BitVec.ofNat 64 dst) (oracle.compression ((readBuffer s src 64).cast h512.symm))) true := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [hmap, oracle_run_map, bind_map_left, map_eq_bind_pure_comp]
  apply bind_congr; intro ⟨e, n⟩; rfl

theorem DetRun.compress_eq (h512 : COMPRESSION_INPUT_LENGTH = 512)
    {oracle : Oracle} {img : Image} {s : MachineState}
    (hfetch : fetch img s = some (.base .ECALL))
    (hx5 : s.getReg .x5 = 0#64)
    (hx11 : s.getReg .x11 = 64#64)
    (hx13 : s.getReg .x13 = 0#64)
    (src dst : Nat)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 8 = 0) (hdst_al : dst % 8 = 0)
    (hsrc_bd : src + 64 ≤ MEMORY_BYTES) (hdst_bd : dst + 32 ≤ MEMORY_BYTES)
    (out : Digest)
    (hout : oracle.compression ((readBuffer s src 64).cast h512.symm) = out) :
    DetRun oracle img s 1 (writeBits s (BitVec.ofNat 64 dst) out) 8 1 := by
  have h := DetRun.compress h512 (oracle := oracle) hfetch hx5 hx11 hx13 src dst hx10 hx12 hsrc_al hdst_al hsrc_bd hdst_bd
  have hw : writeBits s (BitVec.ofNat 64 dst)
        (oracle.compression ((readBuffer s src 64).cast h512.symm)) =
      writeBits s (BitVec.ofNat 64 dst) out := by
    change writeBits s (BitVec.ofNat 64 dst)
        (oracle.compression ((readBuffer s src 64).cast h512.symm) : Digest) =
      writeBits s (BitVec.ofNat 64 dst) out
    rw [hout]
    rfl
  rw [← hw]
  exact h

theorem DetRun.permute
    {oracle : Oracle} {img : Image} {s : MachineState}
    (hfetch : fetch img s = some (.base .ECALL))
    (hx5 : s.getReg .x5 = 0#64)
    (hx11 : s.getReg .x11 = 200#64)
    (hx13 : s.getReg .x13 = 1#64)
    (src dst : Nat)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 8 = 0) (hdst_al : dst % 8 = 0)
    (hsrc_bd : src + 200 ≤ MEMORY_BYTES) (hdst_bd : dst + 200 ≤ MEMORY_BYTES) :
    DetRun oracle img s 1
      (writeBits s (BitVec.ofNat 64 dst)
        (oracle.permutation (readBuffer s src 200)))
      30 1 := by
  intro extra
  have hsrc_lt : src < 2 ^ 64 := by unfold MEMORY_BYTES at hsrc_bd; omega
  have hdst_lt : dst < 2 ^ 64 := by unfold MEMORY_BYTES at hdst_bd; omega
  have hsrc_toNat : (s.getReg .x10).toNat = src := by
    rw [hx10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsrc_lt]
  have hdst_toNat : (s.getReg .x12).toNat = dst := by
    rw [hx12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdst_lt]
  have hrv_src : rangeValid (s.getReg .x10) 200 = true := by
    unfold rangeValid; rw [hsrc_toNat]; exact decide_eq_true hsrc_bd
  have hrv_dst : rangeValid (s.getReg .x12) 200 = true := by
    unfold rangeValid; rw [hdst_toNat]; exact decide_eq_true hdst_bd
  have hoinp : oracleInput s = some (Sum.inr (Sum.inl (readBuffer s src 200))) := by
    unfold oracleInput
    dsimp only
    have hk : (s.getReg .x13).toNat = 1 := by rw [hx13]; rfl
    have hlen : (s.getReg .x11).toNat = 200 := by rw [hx11]; rfl
    have hinb : (PERMUTATION_WIDTH + 7) / 8 = 200 := by rfl
    have hinb_full :
        (((if (s.getReg .x13).toNat = 0 then COMPRESSION_INPUT_LENGTH else PERMUTATION_WIDTH) + 7) / 8) = 200 := by
      rw [hk]; rfl
    have h1ne0 : ¬ ((1 : Nat) = 0) := by decide
    simp only [hsrc_toNat]
    rw [c_readBuffer_toNat_congr s src hinb_full]
    simp only [hk, h1ne0, ite_false, hinb, hlen, hdst_toNat, hsrc_al, hdst_al,
      hrv_src, hrv_dst, show (1 : Nat) ≤ 2 by decide, and_self, ite_true]
    exact congrArg (fun x : BitVec PERMUTATION_WIDTH =>
      (some (Sum.inr (Sum.inl x)) : Option PublicSpec.Domain))
      (c_ofNat_toNat_eq (readBuffer s src 200))
  rw [Nat.add_comm 1 extra]
  have hx5' : s.getReg .x5 = (0 : Word) := hx5
  simp only [execute, hfetch, hx5', ite_true, hoinp]
  change oracle.run ((liftM (World.query (.inr (Sum.inr (Sum.inl (readBuffer s src 200))))) : OracleComp World _) >>=
    fun ans => execute img extra (writeBits s (s.getReg .x12) ans) true >>= fun res =>
      pure (res.charge PERMUTATION_CYCLES 1)) = _
  rw [oracle_run_public_bind, hx12]
  change (oracle.run (execute img extra
      (writeBits s (BitVec.ofNat 64 dst) (oracle.permutation (readBuffer s src 200))) true >>=
      fun res => pure (res.charge 30 1)) >>= fun p => pure (p.1, 1 + p.2)) = _
  have hmap : (execute img extra
        (writeBits s (BitVec.ofNat 64 dst) (oracle.permutation (readBuffer s src 200))) true >>=
        fun res => pure (res.charge 30 1)) =
      (fun res : Execution => res.charge 30 1) <$>
        execute img extra
          (writeBits s (BitVec.ofNat 64 dst) (oracle.permutation (readBuffer s src 200))) true := by
    rw [map_eq_bind_pure_comp]; rfl
  rw [hmap, oracle_run_map, bind_map_left, map_eq_bind_pure_comp]
  apply bind_congr; intro ⟨e, n⟩; rfl

theorem DetRun.permute_eq
    {oracle : Oracle} {img : Image} {s : MachineState}
    (hfetch : fetch img s = some (.base .ECALL))
    (hx5 : s.getReg .x5 = 0#64)
    (hx11 : s.getReg .x11 = 200#64)
    (hx13 : s.getReg .x13 = 1#64)
    (src dst : Nat)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx12 : s.getReg .x12 = BitVec.ofNat 64 dst)
    (hsrc_al : src % 8 = 0) (hdst_al : dst % 8 = 0)
    (hsrc_bd : src + 200 ≤ MEMORY_BYTES) (hdst_bd : dst + 200 ≤ MEMORY_BYTES)
    (out : BitVec 1600)
    (hout : (oracle.permutation (readBuffer s src 200) : BitVec 1600) = out) :
    DetRun oracle img s 1 (writeBits s (BitVec.ofNat 64 dst) out) 30 1 := by
  have h := DetRun.permute (oracle := oracle) hfetch hx5 hx11 hx13 src dst hx10 hx12 hsrc_al hdst_al hsrc_bd hdst_bd
  have hw : writeBits s (BitVec.ofNat 64 dst) (oracle.permutation (readBuffer s src 200)) =
      writeBits s (BitVec.ofNat 64 dst) out := by
    change writeBits s (BitVec.ofNat 64 dst) (oracle.permutation (readBuffer s src 200) : BitVec 1600) =
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

/-! ### 2. Fast `c_`-Prefixed `MachineState`, Step, BitVec, and Copy Helpers -/

theorem c_pc_setPC (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl
theorem c_mem_setPC (s : MachineState) (v : Word) : (s.setPC v).mem = s.mem := rfl
theorem c_mem_setReg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).mem = s.mem := by
  cases r <;> rfl
theorem c_getReg_x0 (s : MachineState) : s.getReg .x0 = 0#64 := rfl
theorem c_getReg_setReg_x0 (s : MachineState) (v : Word) (r : Reg) :
    (s.setReg .x0 v).getReg r = s.getReg r := rfl
theorem c_getReg_setReg_ne (r r' : Reg) (h : r ≠ r') (s : MachineState) (v : Word) :
    (s.setReg r v).getReg r' = s.getReg r' :=
  MachineState.getReg_setReg_ne s r r' v h
theorem c_getReg_setMem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl
theorem c_getReg_setHalfword (s : MachineState) (a : Word) (h : BitVec 16) (r : Reg) :
    (s.setHalfword a h).getReg r = s.getReg r := by cases r <;> rfl
theorem c_getByte_of_mem_eq {s1 s2 : MachineState} (h : s1.mem = s2.mem) (a : Word) :
    s1.getByte a = s2.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem, h]
theorem c_readBuffer_of_mem_eq {s1 s2 : MachineState} (h : s1.mem = s2.mem) (addr n : Nat) :
    readBuffer s1 addr n = readBuffer s2 addr n :=
  readBuffer_congr s1 s2 addr n (fun _ _ => c_getByte_of_mem_eq h _)
theorem c_pc_writeBits {bits : Nat} (s : MachineState) (a : Word) (v : BitVec bits) :
    (writeBits s a v).pc = s.pc + 4 := rfl
theorem c_bv64_add4 (n : Nat) : BitVec.ofNat 64 n + (4 : Word) = BitVec.ofNat 64 (n + 4) := by
  change BitVec.ofNat 64 n + BitVec.ofNat 64 4 = BitVec.ofNat 64 (n + 4)
  exact (BitVec.ofNat_add n 4).symm
theorem c_pc_step_idx (s : MachineState) (idx : Nat)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * idx)) :
    s.pc + (4 : Word) = BitVec.ofNat 64 (0x1000 + 4 * (idx + 1)) := by
  rw [hpc, c_bv64_add4]
  exact congrArg (BitVec.ofNat 64) (by omega)
theorem c_submission_run_commit (s : Submission) (message : Message) :
    s.run .commit message =
      execute (s.image .commit) (s.steps .commit) (s.initialState .commit message) true := by
  unfold Submission.run; dsimp only; exact if_pos rfl

theorem c_pc_exec_ADDI (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI rd rs1 imm)).pc = s.pc + 4 := rfl
theorem c_pc_exec_ADD (s : MachineState) (rd rs1 rs2 : Reg) :
    (execInstrBr s (.ADD rd rs1 rs2)).pc = s.pc + 4 := rfl
theorem c_pc_exec_AND (s : MachineState) (rd rs1 rs2 : Reg) :
    (execInstrBr s (.AND rd rs1 rs2)).pc = s.pc + 4 := rfl
theorem c_pc_exec_SLLI (s : MachineState) (rd rs1 : Reg) (sh : BitVec 6) :
    (execInstrBr s (.SLLI rd rs1 sh)).pc = s.pc + 4 := rfl
theorem c_pc_exec_SRLI (s : MachineState) (rd rs1 : Reg) (sh : BitVec 6) :
    (execInstrBr s (.SRLI rd rs1 sh)).pc = s.pc + 4 := rfl
theorem c_pc_exec_LD (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.LD rd rs1 imm)).pc = s.pc + 4 := rfl
theorem c_pc_exec_SD (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.SD rs1 rs2 imm)).pc = s.pc + 4 := rfl
theorem c_pc_exec_SH (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.SH rs1 rs2 imm)).pc = s.pc + 4 := rfl

theorem c_mem_exec_ADDI (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.ADDI rd rs1 imm)).mem = s.mem := by cases rd <;> rfl
theorem c_mem_exec_ADD (s : MachineState) (rd rs1 rs2 : Reg) :
    (execInstrBr s (.ADD rd rs1 rs2)).mem = s.mem := by cases rd <;> rfl
theorem c_mem_exec_AND (s : MachineState) (rd rs1 rs2 : Reg) :
    (execInstrBr s (.AND rd rs1 rs2)).mem = s.mem := by cases rd <;> rfl
theorem c_mem_exec_SLLI (s : MachineState) (rd rs1 : Reg) (sh : BitVec 6) :
    (execInstrBr s (.SLLI rd rs1 sh)).mem = s.mem := by cases rd <;> rfl
theorem c_mem_exec_SRLI (s : MachineState) (rd rs1 : Reg) (sh : BitVec 6) :
    (execInstrBr s (.SRLI rd rs1 sh)).mem = s.mem := by cases rd <;> rfl
theorem c_mem_exec_LD (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12) :
    (execInstrBr s (.LD rd rs1 imm)).mem = s.mem := by cases rd <;> rfl
theorem c_mem_exec_JAL (s : MachineState) (rd : Reg) (off : BitVec 21) :
    (execInstrBr s (.JAL rd off)).mem = s.mem := by cases rd <;> rfl
theorem c_mem_exec_BEQ (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 13) :
    (execInstrBr s (.BEQ rs1 rs2 off)).mem = s.mem := by simp only [execInstrBr]; split <;> rfl
theorem c_mem_exec_BNE (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 13) :
    (execInstrBr s (.BNE rs1 rs2 off)).mem = s.mem := by simp only [execInstrBr]; split <;> rfl

theorem c_reg_exec_SD (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12) (r : Reg) :
    (execInstrBr s (.SD rs1 rs2 imm)).getReg r = s.getReg r := by cases r <;> rfl
theorem c_reg_exec_SH (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12) (r : Reg) :
    (execInstrBr s (.SH rs1 rs2 imm)).getReg r = s.getReg r := by cases r <;> rfl
theorem c_reg_exec_BEQ (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 13) (r : Reg) :
    (execInstrBr s (.BEQ rs1 rs2 off)).getReg r = s.getReg r := by
  simp only [execInstrBr]; split <;> exact MachineState.getReg_setPC
theorem c_reg_exec_BNE (s : MachineState) (rs1 rs2 : Reg) (off : BitVec 13) (r : Reg) :
    (execInstrBr s (.BNE rs1 rs2 off)).getReg r = s.getReg r := by
  simp only [execInstrBr]; split <;> exact MachineState.getReg_setPC
theorem c_reg_exec_JAL0 (s : MachineState) (off : BitVec 21) (r : Reg) :
    (execInstrBr s (.JAL .x0 off)).getReg r = s.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_x0]

theorem c_ordinaryStep_LD (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12)
    (h : accessValid (s.getReg rs1 + signExtend12 imm) 8 = true) :
    ordinaryStep s (.base (.LD rd rs1 imm)) = some (execInstrBr s (.LD rd rs1 imm)) := by
  simp only [ordinaryStep, memoryArgumentsValid, memAccess, h, ite_true]
theorem c_ordinaryStep_SD (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12)
    (h : accessValid (s.getReg rs1 + signExtend12 imm) 8 = true) :
    ordinaryStep s (.base (.SD rs1 rs2 imm)) = some (execInstrBr s (.SD rs1 rs2 imm)) := by
  simp only [ordinaryStep, memoryArgumentsValid, memAccess, h, ite_true]
theorem c_ordinaryStep_SH (s : MachineState) (rs1 rs2 : Reg) (imm : BitVec 12)
    (h : accessValid (s.getReg rs1 + signExtend12 imm) 2 = true) :
    ordinaryStep s (.base (.SH rs1 rs2 imm)) = some (execInstrBr s (.SH rs1 rs2 imm)) := by
  simp only [ordinaryStep, memoryArgumentsValid, memAccess, h, ite_true]

theorem c_bv64_ne_of_nat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro h
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hn
  exact hne hn

/-! ### 3. Memory Framing (`CommitMemOutside`) & Concrete Arithmetic Helpers -/

def CommitMemOutside (s1 s2 : MachineState) (lo hi : Nat) : Prop :=
  ∀ addr : Nat, addr < 2 ^ 64 → (addr < lo ∨ hi ≤ addr) →
    s2.getByte (BitVec.ofNat 64 addr) = s1.getByte (BitVec.ofNat 64 addr)

theorem CommitMemOutside.refl (s : MachineState) (lo hi : Nat) :
    CommitMemOutside s s lo hi := fun _ _ _ => rfl

theorem CommitMemOutside.of_mem_eq {s1 s2 : MachineState} (h : s2.mem = s1.mem) (lo hi : Nat) :
    CommitMemOutside s1 s2 lo hi := fun _ _ _ => c_getByte_of_mem_eq h _

theorem CommitMemOutside.mono {s1 s2 : MachineState} {lo hi lo' hi' : Nat}
    (h : CommitMemOutside s1 s2 lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    CommitMemOutside s1 s2 lo' hi' := by
  intro addr hbd hout
  exact h addr hbd (by omega)

theorem CommitMemOutside.trans {s1 s2 s3 : MachineState} {lo hi : Nat}
    (h1 : CommitMemOutside s1 s2 lo hi) (h2 : CommitMemOutside s2 s3 lo hi) :
    CommitMemOutside s1 s3 lo hi := by
  intro addr hbd hout
  exact (h2 addr hbd hout).trans (h1 addr hbd hout)

theorem CommitMemOutside.readBuffer_eq {s1 s2 : MachineState} {lo hi addr n : Nat}
    (h : CommitMemOutside s1 s2 lo hi) (hbd : addr + n ≤ 2 ^ 64)
    (hsep : addr + n ≤ lo ∨ hi ≤ addr) :
    readBuffer s2 addr n = readBuffer s1 addr n := by
  apply readBuffer_congr
  intro j hj
  exact h (addr + j) (by omega) (by omega)

theorem CommitMemOutside.getMem_eq {s1 s2 : MachineState} {lo hi addr : Nat}
    (h : CommitMemOutside s1 s2 lo hi) (halign : addr % 8 = 0) (hbd : addr + 8 ≤ 2 ^ 64)
    (hsep : addr + 8 ≤ lo ∨ hi ≤ addr) :
    s2.getMem (BitVec.ofNat 64 addr) = s1.getMem (BitVec.ofNat 64 addr) := by
  rw [← readBuffer_word s2 addr halign, ← readBuffer_word s1 addr halign]
  exact h.readBuffer_eq hbd hsep

theorem c_memPreserved_setMem (s : MachineState) (addr : Nat) (val : Word)
    (halign : addr % 8 = 0) (hbd : addr + 8 ≤ 2 ^ 64) :
    CommitMemOutside s (s.setMem (BitVec.ofNat 64 addr) val) addr (addr + 8) := by
  intro q hq hout
  exact setMem_getByte_ofNat s addr q val halign hbd hq hout

theorem c_memPreserved_setHalfword (s : MachineState) (addr : Nat) (val : BitVec 16)
    (halign : addr % 2 = 0) (hbd : addr + 2 ≤ 2 ^ 64) :
    CommitMemOutside s (s.setHalfword (BitVec.ofNat 64 addr) val) addr (addr + 2) := by
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

theorem c_memPreserved_writeBits {bits : Nat} (s : MachineState) (addr : Nat) (ans : BitVec bits)
    (hbd : addr + (bits + 7) / 8 ≤ 2 ^ 64) :
    CommitMemOutside s (writeBits s (BitVec.ofNat 64 addr) ans) addr (addr + (bits + 7) / 8) := by
  intro q hq hout
  apply write_bits_byte_outside
  intro i hi heq
  have hn := congrArg BitVec.toNat heq
  rw [← BitVec.ofNat_add] at hn
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (by omega : addr + i < 2 ^ 64)] at hn
  omega

/-- Convenience constants matching our exact 64-32 layout (`submission.layout` and `rowOff`). -/
abbrev C_MSG : Nat := 4096
abbrev C_CMT : Nat := 4294971392
abbrev C_TD  : Nat := 4294971424
abbrev C_ROW : Nat := 5368713248

theorem C_ROW_eq : C_ROW = C_TD + rowOff := by
  rw [rowOff_eq]

theorem c_add_signExtend12_ofNat_small (a b : Nat) (hb : b < 2048) :
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

private theorem c_signExtend12_neg_add_cancel (d : Nat) (hd1 : 0 < d) (hd2 : d ≤ 2048) :
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

theorem c_add_signExtend12_neg (a d : Nat) (hd1 : 0 < d) (hd2 : d ≤ 2048) (ha : d ≤ a) :
    BitVec.ofNat 64 a + signExtend12 (BitVec.ofNat 12 (4096 - d)) = BitVec.ofNat 64 (a - d) := by
  have hsplit : BitVec.ofNat 64 a = BitVec.ofNat 64 (a - d) + BitVec.ofNat 64 d := by
    rw [← BitVec.ofNat_add]; exact congrArg (BitVec.ofNat 64) (by omega)
  calc
    BitVec.ofNat 64 a + signExtend12 (BitVec.ofNat 12 (4096 - d))
      = BitVec.ofNat 64 (a - d) + (signExtend12 (BitVec.ofNat 12 (4096 - d)) + BitVec.ofNat 64 d) := by
          rw [hsplit]; ac_rfl
    _ = BitVec.ofNat 64 (a - d) := by rw [c_signExtend12_neg_add_cancel d hd1 hd2, BitVec.add_zero]

theorem c_bv64_add_neg64 (n : Nat) (hn : 64 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4032#12) = BitVec.ofNat 64 (n - 64) := by
  have h : (4032#12 : BitVec 12) = BitVec.ofNat 12 (4096 - 64) := by decide
  rw [h]
  exact c_add_signExtend12_neg n 64 (by omega) (by omega) hn

theorem c_bv64_add_neg32 (n : Nat) (hn : 32 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4064#12) = BitVec.ofNat 64 (n - 32) := by
  have h : (4064#12 : BitVec 12) = BitVec.ofNat 12 (4096 - 32) := by decide
  rw [h]
  exact c_add_signExtend12_neg n 32 (by omega) (by omega) hn

theorem c_accessValid_ofNat (addr w : Nat) (hal : addr % w = 0) (hbd : addr + w ≤ MEMORY_BYTES) :
    accessValid (BitVec.ofNat 64 addr) w = true := by
  have ha : addr < 2 ^ 64 := by unfold MEMORY_BYTES at hbd; omega
  simp only [accessValid, rangeValid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hbd, hal⟩

/-- Reusable 4-dword (32-byte) aligned copy (`LD x6 / SD x6` × 4 = 8 steps, 8 cycles). -/
theorem c_commit_copy32 (oracle : Oracle) (s : MachineState)
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
      CommitMemOutside s s' (dstBase + dstOff) (dstBase + dstOff + 32) := by
  have hmemBd : MEMORY_BYTES < 2 ^ 64 := by unfold MEMORY_BYTES; decide
  have hind : ∀ m ≤ 4,
      ∃ sm,
        DetRun oracle (submission.image .commit) s (2 * m) sm (2 * m) 0 ∧
        sm.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2 * m)) ∧
        (∀ r : Reg, r ≠ .x6 → sm.getReg r = s.getReg r) ∧
        (∀ k < m, sm.getMem (BitVec.ofNat 64 (dstBase + dstOff + 8 * k)) =
          s.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * k))) ∧
        CommitMemOutside s sm (dstBase + dstOff) (dstBase + dstOff + 8 * m) := by
    intro m hm; induction m with
    | zero =>
      exact ⟨s, DetRun.refl _ _ _, by simpa using hpc, fun _ _ => rfl,
        fun _ hk => (Nat.not_lt_zero _ hk).elim, CommitMemOutside.refl _ _ _⟩
    | succ m ih =>
      obtain ⟨sm, hrunm, hpcm, hregm, hwordm, hpresm⟩ := ih (by omega)
      let insL := Instr.LD .x6 srcReg (BitVec.ofNat 12 (srcOff + 8 * m))
      let insS := Instr.SD dstReg .x6 (BitVec.ofNat 12 (dstOff + 8 * m))
      let s1 := execInstrBr sm insL
      let s2 := execInstrBr s1 insS
      have hsrcAddr : sm.getReg srcReg + signExtend12 (BitVec.ofNat 12 (srcOff + 8 * m)) =
          BitVec.ofNat 64 (srcBase + srcOff + 8 * m) := by
        rw [hregm srcReg hsrcReg, hsrc, c_add_signExtend12_ofNat_small _ (srcOff + 8 * m) (by omega)]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have hdstAddr : s1.getReg dstReg + signExtend12 (BitVec.ofNat 12 (dstOff + 8 * m)) =
          BitVec.ofNat 64 (dstBase + dstOff + 8 * m) := by
        have hd1 : s1.getReg dstReg = sm.getReg dstReg := by
          simp only [s1, insL, execInstrBr, MachineState.getReg_setPC,
            c_getReg_setReg_ne .x6 dstReg (Ne.symm hdstReg)]
        rw [hd1, hregm dstReg hdstReg, hdst, c_add_signExtend12_ofNat_small _ (dstOff + 8 * m) (by omega)]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have hstL : DetRun oracle (submission.image .commit) sm 1 s1 1 0 :=
        DetRun.step1 ((hfetch m (by omega) sm).1 hpcm)
          (c_ordinaryStep_LD sm .x6 srcReg _ (by
            rw [hsrcAddr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
      have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (basePc + 2 * m + 1)) := by
        rw [c_pc_exec_LD, hpcm, c_bv64_add4]; exact congrArg (BitVec.ofNat 64) (by omega)
      have hstS : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
        DetRun.step1 ((hfetch m (by omega) s1).2 hs1_pc)
          (c_ordinaryStep_SD s1 dstReg .x6 _ (by
            rw [hdstAddr]; exact c_accessValid_ofNat _ 8 (by omega) (by omega)))
      have hs2_mem : s2.mem = (sm.setMem (BitVec.ofNat 64 (dstBase + dstOff + 8 * m))
          (sm.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * m)))).mem := by
        have hm1 : s1.mem = sm.mem := c_mem_exec_LD sm .x6 srcReg _
        have hx6 : s1.getReg .x6 = sm.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * m)) := by
          simp only [s1, insL, execInstrBr, MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq (by decide : Reg.x6 ≠ .x0), hsrcAddr]
        simp only [s2, insS, execInstrBr, hdstAddr, hx6, c_mem_setPC, MachineState.setMem, hm1]
      have hp12 : CommitMemOutside sm s2 (dstBase + dstOff + 8 * m) (dstBase + dstOff + 8 * (m + 1)) := by
        have hp := c_memPreserved_setMem sm (dstBase + dstOff + 8 * m)
          (sm.getMem (BitVec.ofNat 64 (srcBase + srcOff + 8 * m))) (by omega) (by omega)
        exact (hp.mono (le_refl _) (by omega)).trans (CommitMemOutside.of_mem_eq hs2_mem _ _)
      refine ⟨s2, by simpa [Nat.mul_succ, Nat.add_assoc] using (hrunm.trans hstL).trans hstS, ?_, ?_, ?_, ?_⟩
      · rw [c_pc_exec_SD, hs1_pc, c_bv64_add4]; exact congrArg (BitVec.ofNat 64) (by omega)
      · intro r hr
        have h1 : s2.getReg r = s1.getReg r := c_reg_exec_SD s1 dstReg .x6 _ r
        have h2 : s1.getReg r = sm.getReg r := by
          simp only [s1, insL, execInstrBr, MachineState.getReg_setPC,
            c_getReg_setReg_ne .x6 r (Ne.symm hr)]
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

/-! ### 4. Pure-ALU List Execution Helpers -/

def c_isPureAlu : Instr → Bool
  | .ADDI .. | .ADD .. | .SLLI .. | .SRLI .. | .ANDI .. => true
  | _ => false

theorem c_execInstrBr_pureAlu_pc (s : MachineState) (ins : Instr) (h : c_isPureAlu ins = true) :
    (execInstrBr s ins).pc = s.pc + 4 := by
  cases ins <;> simp_all [c_isPureAlu, execInstrBr, c_pc_setPC]

theorem c_execInstrBr_pureAlu_mem (s : MachineState) (ins : Instr) (h : c_isPureAlu ins = true) :
    (execInstrBr s ins).mem = s.mem := by
  cases ins <;> simp_all [c_isPureAlu, execInstrBr, c_mem_setPC, c_mem_setReg]

theorem c_foldl_pureAlu_pc (instrs : List Instr) (s : MachineState) (n : Nat)
    (hall : ∀ ins ∈ instrs, c_isPureAlu ins = true)
    (hpc : s.pc = BitVec.ofNat 64 n) :
    (instrs.foldl execInstrBr s).pc = BitVec.ofNat 64 (n + 4 * instrs.length) := by
  induction instrs generalizing s n with
  | nil => simp [hpc]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length_cons]
    have hhd : (execInstrBr s hd).pc = BitVec.ofNat 64 (n + 4) := by
      rw [c_execInstrBr_pureAlu_pc s hd (hall hd (by simp)), hpc, c_bv64_add4]
    have htl := ih (execInstrBr s hd) (n + 4) (fun x hx => hall x (by simp [hx])) hhd
    rw [htl]; exact congrArg (BitVec.ofNat 64) (by omega)

theorem c_foldl_pureAlu_mem (instrs : List Instr) (s : MachineState)
    (hall : ∀ ins ∈ instrs, c_isPureAlu ins = true) :
    (instrs.foldl execInstrBr s).mem = s.mem := by
  induction instrs generalizing s with
  | nil => rfl
  | cons hd tl ih =>
    rw [List.foldl_cons, ih (execInstrBr s hd) (fun x hx => hall x (by simp [hx])),
      c_execInstrBr_pureAlu_mem s hd (hall hd (by simp))]

theorem c_exec_alu_list {oracle : Oracle} {img : Image} (instrs : List Instr)
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

/-! ### 5. Uniform Distribution Collapse (`=ᵈ`) for Sequential `PairRand` Draws -/

private def c_snocFn {k : Nat} (acc : Fin k → PairRand) (r : PairRand) : Fin (k + 1) → PairRand :=
  fun i => if h : i.val < k then acc ⟨i.val, h⟩ else r

private def c_snocEquiv (k : Nat) : ((Fin k → PairRand) × PairRand) ≃ (Fin (k + 1) → PairRand) where
  toFun p := c_snocFn p.1 p.2
  invFun f := (fun i => f ⟨i.val, by omega⟩, f ⟨k, by omega⟩)
  left_inv := fun ⟨acc, r⟩ => by
    apply Prod.ext
    · funext ⟨i, hi⟩; simp [c_snocFn, hi]
    · simp [c_snocFn]
  right_inv := fun f => by
    funext ⟨i, hi⟩
    by_cases h : i < k
    · simp [c_snocFn, h]
    · have heq : i = k := by omega
      subst heq; simp [c_snocFn]

private def c_concatFn (a b : Nat) (f : Fin a → PairRand) (g : Fin b → PairRand) :
    Fin (a + b) → PairRand :=
  fun i => if h : i.val < a then f ⟨i.val, h⟩ else g ⟨i.val - a, by omega⟩

private def c_concatEquiv (a b : Nat) :
    ((Fin a → PairRand) × (Fin b → PairRand)) ≃ (Fin (a + b) → PairRand) where
  toFun p := c_concatFn a b p.1 p.2
  invFun h := (fun i => h ⟨i.val, by omega⟩, fun j => h ⟨a + j.val, by omega⟩)
  left_inv := fun ⟨f, g⟩ => by
    apply Prod.ext
    · funext ⟨i, hi⟩; simp [c_concatFn, hi]
    · funext ⟨j, hj⟩
      have hnot : ¬ (a + j < a) := by omega
      simp [c_concatFn, hnot]
  right_inv := fun h => by
    funext ⟨i, hi⟩
    by_cases hlt : i < a
    · simp [c_concatFn, hlt]
    · simp only [c_concatFn, hlt, dite_false]
      congr 1; apply Fin.ext; dsimp only; omega

private def c_finFnCastEquiv (n m : Nat) (h : n = m) :
    (Fin n → PairRand) ≃ (Fin m → PairRand) where
  toFun f i := f ⟨i.val, by omega⟩
  invFun g i := g ⟨i.val, by omega⟩
  left_inv f := by funext ⟨i, hi⟩; rfl
  right_inv g := by funext ⟨i, hi⟩; rfl

private theorem c_uniformSample_fin0_pairRand :
    (pure (fun i : Fin 0 => i.elim0) : ProbComp (Fin 0 → PairRand)) =ᵈ ($ᵗ (Fin 0 → PairRand)) := by
  intro p
  have hall : ∀ f : Fin 0 → PairRand, f = fun i => i.elim0 := fun f => by
    funext i; exact i.elim0
  classical
  rw [prEvent_pure, SampleableType.prEvent_uniformSample]
  have hcard : Fintype.card (Fin 0 → PairRand) = 1 := by simp [Fintype.card_fun]
  rw [hcard]
  by_cases hp : p (fun i => i.elim0)
  · rw [if_pos hp]
    have hfilt : (Finset.univ.filter p) = Finset.univ := by ext f; simp [hall f, hp]
    rw [hfilt, Finset.card_univ, hcard]; simp
  · rw [if_neg hp]
    have hfilt : (Finset.univ.filter p) = ∅ := by ext f; simp [hall f, hp]
    rw [hfilt]; simp

private theorem c_uniformSample_snoc_pairRand (k : Nat) {α : Type}
    (next : (Fin (k + 1) → PairRand) → ProbComp α) :
    (do let acc ← $ᵗ (Fin k → PairRand)
        let r ← $ᵗ PairRand
        next (c_snocFn acc r)) =ᵈ (($ᵗ (Fin (k + 1) → PairRand)) >>= next) := by
  have heq : (do let acc ← $ᵗ (Fin k → PairRand)
                 let r ← $ᵗ PairRand
                 next (c_snocFn acc r)) =
      (((c_snocEquiv k) <$> ($ᵗ ((Fin k → PairRand) × PairRand))) >>= next) := by
    rw [SampleableType.uniformSample_prod_eq_bind, map_bind, bind_assoc]
    apply bind_congr; intro acc
    rw [map_bind, bind_assoc]
    apply bind_congr; intro r
    simp only [map_pure, pure_bind, c_snocEquiv, Equiv.coe_fn_mk]
  rw [heq]
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective (c_snocEquiv k).bijective).bind_left next

private theorem c_uniformSample_concat_pairRand (a b : Nat) {α : Type}
    (next : (Fin (a + b) → PairRand) → ProbComp α) :
    (do let f ← $ᵗ (Fin a → PairRand)
        let g ← $ᵗ (Fin b → PairRand)
        next (c_concatFn a b f g)) =ᵈ (($ᵗ (Fin (a + b) → PairRand)) >>= next) := by
  have heq : (do let f ← $ᵗ (Fin a → PairRand)
                 let g ← $ᵗ (Fin b → PairRand)
                 next (c_concatFn a b f g)) =
      (((c_concatEquiv a b) <$> ($ᵗ ((Fin a → PairRand) × (Fin b → PairRand)))) >>= next) := by
    rw [SampleableType.uniformSample_prod_eq_bind, map_bind, bind_assoc]
    apply bind_congr; intro f
    rw [map_bind, bind_assoc]
    apply bind_congr; intro g
    simp only [map_pure, pure_bind, c_concatEquiv, Equiv.coe_fn_mk]
  rw [heq]
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective (c_concatEquiv a b).bijective).bind_left next

private theorem c_uniformSample_fin_cast (n m : Nat) (h : n = m) {α : Type}
    (next : (Fin m → PairRand) → ProbComp α) :
    (($ᵗ (Fin n → PairRand)) >>= fun f => next (fun i => f ⟨i.val, by omega⟩)) =ᵈ
      (($ᵗ (Fin m → PairRand)) >>= next) := by
  have heq : (($ᵗ (Fin n → PairRand)) >>= fun f => next (fun i => f ⟨i.val, by omega⟩)) =
      (((c_finFnCastEquiv n m h) <$> ($ᵗ (Fin n → PairRand))) >>= next) := by
    rw [bind_map_left]; rfl
  rw [heq]
  exact (SampleableType.map_uniformSample_evalDistEq_of_bijective (c_finFnCastEquiv n m h).bijective).bind_left next

/-! ### 6. Exact RV64IM Execution Proof for Phase 0 (words `0..4121`) -/

private theorem c_initialState_pc (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).pc = 0x1000#64 := rfl
private theorem c_initialState_x10 (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).getReg .x10 = BitVec.ofNat 64 s.layout.message := rfl
private theorem c_initialState_x11 (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).getReg .x11 = BitVec.ofNat 64 s.layout.commitment := rfl
private theorem c_initialState_x12 (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).getReg .x12 = BitVec.ofNat 64 s.layout.trapdoor := rfl

private theorem c_initial_pc (message : Message) :
    (submission.initialState .commit message).pc = BitVec.ofNat 64 (0x1000 + 4 * 0) :=
  c_initialState_pc submission .commit message
private theorem c_initial_x10 (message : Message) :
    (submission.initialState .commit message).getReg .x10 = BitVec.ofNat 64 C_MSG :=
  c_initialState_x10 submission .commit message
private theorem c_initial_x11 (message : Message) :
    (submission.initialState .commit message).getReg .x11 = BitVec.ofNat 64 C_CMT :=
  c_initialState_x11 submission .commit message
private theorem c_initial_x12 (message : Message) :
    (submission.initialState .commit message).getReg .x12 = BitVec.ofNat 64 C_TD :=
  c_initialState_x12 submission .commit message

private def c_prefixInstrs : List Instr :=
  [.ADDI .x8 .x10 (0#12), .ADDI .x26 .x11 (0#12), .ADDI .x9 .x12 (0#12),
   .ADDI .x6 .x0 (1#12), .SLLI .x6 .x6 (30#6), .ADD .x18 .x9 .x6,
   .ADDI .x5 .x0 (2#12), .ADDI .x10 .x18 (40#12), .ADDI .x11 .x0 (40#12),
   .ADDI .x6 .x0 (240#12), .SLLI .x6 .x6 (11#6), .SLLI .x6 .x6 (11#6),
   .ADDI .x6 .x6 (40#12), .ADD .x19 .x18 .x6]

private def c_mid0Instrs : List Instr :=
  [.ADDI .x5 .x0 (0#12), .ADDI .x11 .x0 (64#12), .ADDI .x13 .x0 (0#12),
   .ADDI .x10 .x8 (4032#12),
   .ADDI .x6 .x0 (1023#12), .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (2047#12),
   .SLLI .x6 .x6 (11#6), .ADDI .x6 .x6 (1984#12), .ADD .x19 .x8 .x6]

private theorem c_prefix_run (oracle : Oracle) (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 0)) :
    DetRun oracle (submission.image .commit) s0 14 (c_prefixInstrs.foldl execInstrBr s0) 14 0 := by
  have hall : ∀ ins ∈ c_prefixInstrs, c_isPureAlu ins = true := by decide
  apply c_exec_alu_list c_prefixInstrs s0
  intro i hi
  have hi' : i < 14 := hi
  have hpc_i : ((c_prefixInstrs.take i).foldl execInstrBr s0).pc =
      BitVec.ofNat 64 (0x1000 + 4 * i) := by
    have h := c_foldl_pureAlu_pc (c_prefixInstrs.take i) s0 (0x1000 + 4 * 0)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    simpa only [Nat.mul_zero, Nat.add_zero] using h
  interval_cases i <;>
    exact ⟨commit_fetch_commitPrefixInstr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem c_getReg_exec_ADDI_eq (s : MachineState) (rd rs1 : Reg) (imm : BitVec 12) (h : rd ≠ .x0) :
    (execInstrBr s (.ADDI rd rs1 imm)).getReg rd = s.getReg rs1 + signExtend12 imm := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq h]

private theorem c_getReg_exec_ADDI_ne (s : MachineState) (rd rs1 r : Reg) (imm : BitVec 12) (h : rd ≠ r) :
    (execInstrBr s (.ADDI rd rs1 imm)).getReg r = s.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne rd r h]

private theorem c_getReg_exec_ADD_eq (s : MachineState) (rd rs1 rs2 : Reg) (h : rd ≠ .x0) :
    (execInstrBr s (.ADD rd rs1 rs2)).getReg rd = s.getReg rs1 + s.getReg rs2 := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq h]

private theorem c_getReg_exec_ADD_ne (s : MachineState) (rd rs1 rs2 r : Reg) (h : rd ≠ r) :
    (execInstrBr s (.ADD rd rs1 rs2)).getReg r = s.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne rd r h]

private theorem c_getReg_exec_SLLI_eq (s : MachineState) (rd rs1 : Reg) (sh : BitVec 6) (h : rd ≠ .x0) :
    (execInstrBr s (.SLLI rd rs1 sh)).getReg rd = s.getReg rs1 <<< sh.toNat := by
  simp only [execInstrBr, MachineState.getReg_setPC, MachineState.getReg_setReg_eq h]

private theorem c_getReg_exec_SLLI_ne (s : MachineState) (rd rs1 r : Reg) (sh : BitVec 6) (h : rd ≠ r) :
    (execInstrBr s (.SLLI rd rs1 sh)).getReg r = s.getReg r := by
  simp only [execInstrBr, MachineState.getReg_setPC, c_getReg_setReg_ne rd r h]

private theorem c_prefix_spec (s0 : MachineState)
    (hpc : s0.pc = BitVec.ofNat 64 (0x1000 + 4 * 0))
    (hx10 : s0.getReg .x10 = BitVec.ofNat 64 C_MSG)
    (hx11 : s0.getReg .x11 = BitVec.ofNat 64 C_CMT)
    (hx12 : s0.getReg .x12 = BitVec.ofNat 64 C_TD) :
    let s1 := c_prefixInstrs.foldl execInstrBr s0
    s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 14) ∧
    s1.mem = s0.mem ∧
    s1.getReg .x5 = 2#64 ∧
    s1.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
    s1.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s1.getReg .x10 = BitVec.ofNat 64 (C_ROW + 40) ∧
    s1.getReg .x11 = 40#64 ∧
    s1.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
    s1.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes + 40) ∧
    s1.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ c_prefixInstrs, c_isPureAlu ins = true := by decide
  refine ⟨(c_foldl_pureAlu_pc c_prefixInstrs s0 (0x1000 + 4 * 0) hall hpc).trans (by decide),
    c_foldl_pureAlu_mem c_prefixInstrs s0 hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- x5
    let t1 := execInstrBr s0 (.ADDI .x8 .x10 (0#12))
    let t2 := execInstrBr t1 (.ADDI .x26 .x11 (0#12))
    let t3 := execInstrBr t2 (.ADDI .x9 .x12 (0#12))
    let t4 := execInstrBr t3 (.ADDI .x6 .x0 (1#12))
    let t5 := execInstrBr t4 (.SLLI .x6 .x6 (30#6))
    let t6 := execInstrBr t5 (.ADD .x18 .x9 .x6)
    let t7 := execInstrBr t6 (.ADDI .x5 .x0 (2#12))
    let t8 := execInstrBr t7 (.ADDI .x10 .x18 (40#12))
    let t9 := execInstrBr t8 (.ADDI .x11 .x0 (40#12))
    let t10 := execInstrBr t9 (.ADDI .x6 .x0 (240#12))
    let t11 := execInstrBr t10 (.SLLI .x6 .x6 (11#6))
    let t12 := execInstrBr t11 (.SLLI .x6 .x6 (11#6))
    let t13 := execInstrBr t12 (.ADDI .x6 .x6 (40#12))
    let t14 := execInstrBr t13 (.ADD .x19 .x18 .x6)
    change t14.getReg .x5 = 2#64
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_x0]
    decide
  · -- x8
    let t1 := execInstrBr s0 (.ADDI .x8 .x10 (0#12))
    let t2 := execInstrBr t1 (.ADDI .x26 .x11 (0#12))
    let t3 := execInstrBr t2 (.ADDI .x9 .x12 (0#12))
    let t4 := execInstrBr t3 (.ADDI .x6 .x0 (1#12))
    let t5 := execInstrBr t4 (.SLLI .x6 .x6 (30#6))
    let t6 := execInstrBr t5 (.ADD .x18 .x9 .x6)
    let t7 := execInstrBr t6 (.ADDI .x5 .x0 (2#12))
    let t8 := execInstrBr t7 (.ADDI .x10 .x18 (40#12))
    let t9 := execInstrBr t8 (.ADDI .x11 .x0 (40#12))
    let t10 := execInstrBr t9 (.ADDI .x6 .x0 (240#12))
    let t11 := execInstrBr t10 (.SLLI .x6 .x6 (11#6))
    let t12 := execInstrBr t11 (.SLLI .x6 .x6 (11#6))
    let t13 := execInstrBr t12 (.ADDI .x6 .x6 (40#12))
    let t14 := execInstrBr t13 (.ADD .x19 .x18 .x6)
    change t14.getReg .x8 = BitVec.ofNat 64 C_MSG
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_eq _ _ _ _ (by decide), hx10]
    decide
  · -- x9
    let t1 := execInstrBr s0 (.ADDI .x8 .x10 (0#12))
    let t2 := execInstrBr t1 (.ADDI .x26 .x11 (0#12))
    let t3 := execInstrBr t2 (.ADDI .x9 .x12 (0#12))
    let t4 := execInstrBr t3 (.ADDI .x6 .x0 (1#12))
    let t5 := execInstrBr t4 (.SLLI .x6 .x6 (30#6))
    let t6 := execInstrBr t5 (.ADD .x18 .x9 .x6)
    let t7 := execInstrBr t6 (.ADDI .x5 .x0 (2#12))
    let t8 := execInstrBr t7 (.ADDI .x10 .x18 (40#12))
    let t9 := execInstrBr t8 (.ADDI .x11 .x0 (40#12))
    let t10 := execInstrBr t9 (.ADDI .x6 .x0 (240#12))
    let t11 := execInstrBr t10 (.SLLI .x6 .x6 (11#6))
    let t12 := execInstrBr t11 (.SLLI .x6 .x6 (11#6))
    let t13 := execInstrBr t12 (.ADDI .x6 .x6 (40#12))
    let t14 := execInstrBr t13 (.ADD .x19 .x18 .x6)
    change t14.getReg .x9 = BitVec.ofNat 64 C_TD
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_eq _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), hx12]
    decide
  · -- x10
    let t1 := execInstrBr s0 (.ADDI .x8 .x10 (0#12))
    let t2 := execInstrBr t1 (.ADDI .x26 .x11 (0#12))
    let t3 := execInstrBr t2 (.ADDI .x9 .x12 (0#12))
    let t4 := execInstrBr t3 (.ADDI .x6 .x0 (1#12))
    let t5 := execInstrBr t4 (.SLLI .x6 .x6 (30#6))
    let t6 := execInstrBr t5 (.ADD .x18 .x9 .x6)
    let t7 := execInstrBr t6 (.ADDI .x5 .x0 (2#12))
    let t8 := execInstrBr t7 (.ADDI .x10 .x18 (40#12))
    let t9 := execInstrBr t8 (.ADDI .x11 .x0 (40#12))
    let t10 := execInstrBr t9 (.ADDI .x6 .x0 (240#12))
    let t11 := execInstrBr t10 (.SLLI .x6 .x6 (11#6))
    let t12 := execInstrBr t11 (.SLLI .x6 .x6 (11#6))
    let t13 := execInstrBr t12 (.ADDI .x6 .x6 (40#12))
    let t14 := execInstrBr t13 (.ADD .x19 .x18 .x6)
    have h9 : t3.getReg .x9 = BitVec.ofNat 64 C_TD := by
      rw [c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
        c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), hx12]; decide
    have h6 : t5.getReg .x6 = BitVec.ofNat 64 (2 ^ 30) := by
      rw [c_getReg_exec_SLLI_eq _ _ _ _ (by decide), c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_x0]; decide
    have h18 : t6.getReg .x18 = BitVec.ofNat 64 C_ROW := by
      rw [c_getReg_exec_ADD_eq _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
        c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), h9, h6]; decide
    change t14.getReg .x10 = BitVec.ofNat 64 (C_ROW + 40)
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), h18]
    decide
  · -- x11
    let t1 := execInstrBr s0 (.ADDI .x8 .x10 (0#12))
    let t2 := execInstrBr t1 (.ADDI .x26 .x11 (0#12))
    let t3 := execInstrBr t2 (.ADDI .x9 .x12 (0#12))
    let t4 := execInstrBr t3 (.ADDI .x6 .x0 (1#12))
    let t5 := execInstrBr t4 (.SLLI .x6 .x6 (30#6))
    let t6 := execInstrBr t5 (.ADD .x18 .x9 .x6)
    let t7 := execInstrBr t6 (.ADDI .x5 .x0 (2#12))
    let t8 := execInstrBr t7 (.ADDI .x10 .x18 (40#12))
    let t9 := execInstrBr t8 (.ADDI .x11 .x0 (40#12))
    let t10 := execInstrBr t9 (.ADDI .x6 .x0 (240#12))
    let t11 := execInstrBr t10 (.SLLI .x6 .x6 (11#6))
    let t12 := execInstrBr t11 (.SLLI .x6 .x6 (11#6))
    let t13 := execInstrBr t12 (.ADDI .x6 .x6 (40#12))
    let t14 := execInstrBr t13 (.ADD .x19 .x18 .x6)
    change t14.getReg .x11 = 40#64
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_x0]
    decide
  · -- x18
    let t1 := execInstrBr s0 (.ADDI .x8 .x10 (0#12))
    let t2 := execInstrBr t1 (.ADDI .x26 .x11 (0#12))
    let t3 := execInstrBr t2 (.ADDI .x9 .x12 (0#12))
    let t4 := execInstrBr t3 (.ADDI .x6 .x0 (1#12))
    let t5 := execInstrBr t4 (.SLLI .x6 .x6 (30#6))
    let t6 := execInstrBr t5 (.ADD .x18 .x9 .x6)
    let t7 := execInstrBr t6 (.ADDI .x5 .x0 (2#12))
    let t8 := execInstrBr t7 (.ADDI .x10 .x18 (40#12))
    let t9 := execInstrBr t8 (.ADDI .x11 .x0 (40#12))
    let t10 := execInstrBr t9 (.ADDI .x6 .x0 (240#12))
    let t11 := execInstrBr t10 (.SLLI .x6 .x6 (11#6))
    let t12 := execInstrBr t11 (.SLLI .x6 .x6 (11#6))
    let t13 := execInstrBr t12 (.ADDI .x6 .x6 (40#12))
    let t14 := execInstrBr t13 (.ADD .x19 .x18 .x6)
    have h9 : t3.getReg .x9 = BitVec.ofNat 64 C_TD := by
      rw [c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
        c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), hx12]; decide
    have h6 : t5.getReg .x6 = BitVec.ofNat 64 (2 ^ 30) := by
      rw [c_getReg_exec_SLLI_eq _ _ _ _ (by decide), c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_x0]; decide
    change t14.getReg .x18 = BitVec.ofNat 64 C_ROW
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADD_eq _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), h9, h6]
    decide
  · -- x19
    let t1 := execInstrBr s0 (.ADDI .x8 .x10 (0#12))
    let t2 := execInstrBr t1 (.ADDI .x26 .x11 (0#12))
    let t3 := execInstrBr t2 (.ADDI .x9 .x12 (0#12))
    let t4 := execInstrBr t3 (.ADDI .x6 .x0 (1#12))
    let t5 := execInstrBr t4 (.SLLI .x6 .x6 (30#6))
    let t6 := execInstrBr t5 (.ADD .x18 .x9 .x6)
    let t7 := execInstrBr t6 (.ADDI .x5 .x0 (2#12))
    let t8 := execInstrBr t7 (.ADDI .x10 .x18 (40#12))
    let t9 := execInstrBr t8 (.ADDI .x11 .x0 (40#12))
    let t10 := execInstrBr t9 (.ADDI .x6 .x0 (240#12))
    let t11 := execInstrBr t10 (.SLLI .x6 .x6 (11#6))
    let t12 := execInstrBr t11 (.SLLI .x6 .x6 (11#6))
    let t13 := execInstrBr t12 (.ADDI .x6 .x6 (40#12))
    let t14 := execInstrBr t13 (.ADD .x19 .x18 .x6)
    have h9 : t3.getReg .x9 = BitVec.ofNat 64 C_TD := by
      rw [c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
        c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), hx12]; decide
    have h6a : t5.getReg .x6 = BitVec.ofNat 64 (2 ^ 30) := by
      rw [c_getReg_exec_SLLI_eq _ _ _ _ (by decide), c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_x0]; decide
    have h18 : t13.getReg .x18 = BitVec.ofNat 64 C_ROW := by
      rw [c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
        c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
        c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
        c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADD_eq _ _ _ _ (by decide),
        c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), h9, h6a]; decide
    have h6b : t13.getReg .x6 = BitVec.ofNat 64 (rowBytes + 40) := by
      rw [c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_exec_SLLI_eq _ _ _ _ (by decide),
        c_getReg_exec_SLLI_eq _ _ _ _ (by decide), c_getReg_exec_ADDI_eq _ _ _ _ (by decide),
        c_getReg_x0, rowBytes_eq]; decide
    change t14.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes + 40)
    rw [c_getReg_exec_ADD_eq _ _ _ _ (by decide), h18, h6b, rowBytes_eq]
    decide
  · -- x26
    let t1 := execInstrBr s0 (.ADDI .x8 .x10 (0#12))
    let t2 := execInstrBr t1 (.ADDI .x26 .x11 (0#12))
    let t3 := execInstrBr t2 (.ADDI .x9 .x12 (0#12))
    let t4 := execInstrBr t3 (.ADDI .x6 .x0 (1#12))
    let t5 := execInstrBr t4 (.SLLI .x6 .x6 (30#6))
    let t6 := execInstrBr t5 (.ADD .x18 .x9 .x6)
    let t7 := execInstrBr t6 (.ADDI .x5 .x0 (2#12))
    let t8 := execInstrBr t7 (.ADDI .x10 .x18 (40#12))
    let t9 := execInstrBr t8 (.ADDI .x11 .x0 (40#12))
    let t10 := execInstrBr t9 (.ADDI .x6 .x0 (240#12))
    let t11 := execInstrBr t10 (.SLLI .x6 .x6 (11#6))
    let t12 := execInstrBr t11 (.SLLI .x6 .x6 (11#6))
    let t13 := execInstrBr t12 (.ADDI .x6 .x6 (40#12))
    let t14 := execInstrBr t13 (.ADD .x19 .x18 .x6)
    change t14.getReg .x26 = BitVec.ofNat 64 C_CMT
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), hx11]
    decide

private theorem c_mid0_run (oracle : Oracle) (s2 : MachineState)
    (hpc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 4112)) :
    DetRun oracle (submission.image .commit) s2 10 (c_mid0Instrs.foldl execInstrBr s2) 10 0 := by
  have hall : ∀ ins ∈ c_mid0Instrs, c_isPureAlu ins = true := by decide
  apply c_exec_alu_list c_mid0Instrs s2
  intro i hi
  have hi' : i < 10 := hi
  have hpc_i : ((c_mid0Instrs.take i).foldl execInstrBr s2).pc =
      BitVec.ofNat 64 (0x1000 + 4 * (4112 + i)) := by
    have h := c_foldl_pureAlu_pc (c_mid0Instrs.take i) s2 (0x1000 + 4 * 4112)
      (fun ins hmem => hall ins (List.mem_of_mem_take hmem)) hpc
    rw [List.length_take_of_le (by omega)] at h
    rw [h]; exact congrArg (BitVec.ofNat 64) (by omega)
  interval_cases i <;>
    exact ⟨commit_fetch_commitMid0Instr _ _ (by omega) (by omega) hpc_i, rfl, rfl⟩

private theorem c_mid0_spec (s2 : MachineState)
    (hpc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 4112))
    (hx8 : s2.getReg .x8 = BitVec.ofNat 64 C_MSG)
    (hx9 : s2.getReg .x9 = BitVec.ofNat 64 C_TD)
    (hx18 : s2.getReg .x18 = BitVec.ofNat 64 C_ROW)
    (hx26 : s2.getReg .x26 = BitVec.ofNat 64 C_CMT) :
    let s3 := c_mid0Instrs.foldl execInstrBr s2
    s3.pc = BitVec.ofNat 64 (0x1000 + 4 * 4122) ∧
    s3.mem = s2.mem ∧
    s3.getReg .x5 = 0#64 ∧
    s3.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
    s3.getReg .x9 = BitVec.ofNat 64 C_TD ∧
    s3.getReg .x10 = BitVec.ofNat 64 (C_MSG - 64) ∧
    s3.getReg .x11 = 64#64 ∧
    s3.getReg .x13 = 0#64 ∧
    s3.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
    s3.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 64) ∧
    s3.getReg .x26 = BitVec.ofNat 64 C_CMT := by
  have hall : ∀ ins ∈ c_mid0Instrs, c_isPureAlu ins = true := by decide
  let t1 := execInstrBr s2 (.ADDI .x5 .x0 (0#12))
  let t2 := execInstrBr t1 (.ADDI .x11 .x0 (64#12))
  let t3 := execInstrBr t2 (.ADDI .x13 .x0 (0#12))
  let t4 := execInstrBr t3 (.ADDI .x10 .x8 (4032#12))
  let t5 := execInstrBr t4 (.ADDI .x6 .x0 (1023#12))
  let t6 := execInstrBr t5 (.SLLI .x6 .x6 (11#6))
  let t7 := execInstrBr t6 (.ADDI .x6 .x6 (2047#12))
  let t8 := execInstrBr t7 (.SLLI .x6 .x6 (11#6))
  let t9 := execInstrBr t8 (.ADDI .x6 .x6 (1984#12))
  let t10 := execInstrBr t9 (.ADD .x19 .x8 .x6)
  have ht8_x8 : t9.getReg .x8 = BitVec.ofNat 64 C_MSG := by
    rw [c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), hx8]
  have ht9_x6 : t9.getReg .x6 = BitVec.ofNat 64 (2 ^ 32 - 64) := by
    rw [c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_exec_SLLI_eq _ _ _ _ (by decide),
      c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_exec_SLLI_eq _ _ _ _ (by decide),
      c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_x0]
    decide
  refine ⟨(c_foldl_pureAlu_pc c_mid0Instrs s2 (0x1000 + 4 * 4112) hall hpc).trans (by decide),
    c_foldl_pureAlu_mem c_mid0Instrs s2 hall, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change t10.getReg .x5 = 0#64
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_x0]; decide
  · change t10.getReg .x8 = BitVec.ofNat 64 C_MSG
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), ht8_x8]
  · change t10.getReg .x9 = BitVec.ofNat 64 C_TD
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), hx9]
  · change t10.getReg .x10 = BitVec.ofNat 64 (C_MSG - 64)
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), hx8]; decide
  · change t10.getReg .x11 = 64#64
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_x0]; decide
  · change t10.getReg .x13 = 0#64
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_eq _ _ _ _ (by decide), c_getReg_x0]; decide
  · change t10.getReg .x18 = BitVec.ofNat 64 C_ROW
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), hx18]
  · change t10.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 64)
    rw [c_getReg_exec_ADD_eq _ _ _ _ (by decide), ht8_x8, ht9_x6]; decide
  · change t10.getReg .x26 = BitVec.ofNat 64 C_CMT
    rw [c_getReg_exec_ADD_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_SLLI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide),
      c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), c_getReg_exec_ADDI_ne _ _ _ _ _ (by decide), hx26]

/-- Deterministic state transformer for one `p0_loop` pair given its drawn 40-byte `PairRand`. -/
private def c_randPairState (s : MachineState) (r : PairRand) : MachineState :=
  execInstrBr (writeBits s (s.getReg .x10) r) (.ADDI .x10 .x10 (120#12))

private theorem c_pc_beq_4110 :
    BitVec.ofNat 64 (0x1000 + 4 * 4110) + signExtend13 (8#13) =
      BitVec.ofNat 64 (0x1000 + 4 * 4112) := by decide

private theorem c_pc_jal_4111 :
    BitVec.ofNat 64 (0x1000 + 4 * 4111) + signExtend21 (2080764#21) =
      BitVec.ofNat 64 (0x1000 + 4 * 14) := by decide

private theorem c_charge_compose_beta (c1 c2 : Nat) :
    (fun a : Execution × Nat => ((a.1.charge c2 0, a.2).1.charge c1 0, (a.1.charge c2 0, a.2).2)) =
    (fun p : Execution × Nat => (p.1.charge (c1 + c2) 0, p.2)) := by
  funext ⟨⟨ex, st, cy, ca⟩, n⟩
  simp only [Execution.charge, Nat.zero_add, Prod.mk.injEq, Execution.mk.injEq]
  exact ⟨⟨trivial, trivial, by omega, trivial⟩, trivial⟩

/-- One `p0_loop` pair (`ECALL RANDOM(40); ADDI x10, x10, 120`): 2 steps, 7 cycles, 0 oracle calls. -/
private theorem c_rand_pair_step (oracle : Oracle) (s : MachineState)
    (k pairIdx : Nat) (hk : k < 2048) (hpair : pairIdx < LENGTH / 2)
    (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * (14 + 2 * k)))
    (hx5 : s.getReg .x5 = 2#64)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx + 40))
    (hx11 : s.getReg .x11 = 40#64) :
    (∀ extra,
      oracle.run (execute (submission.image .commit) (2 + extra) s true) =
        (($ᵗ PairRand) >>= fun r =>
          (fun p : Execution × Nat => (p.1.charge 7 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) extra (c_randPairState s r) true))) ∧
    ∀ r : PairRand,
      let s' := c_randPairState s r
      s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (14 + 2 * (k + 1))) ∧
      (∀ reg : Reg, reg ≠ .x10 → s'.getReg reg = s.getReg reg) ∧
      s'.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (pairIdx + 1) + 40) ∧
      readBuffer s' (C_ROW + 120 * pairIdx + 40) 24 = pairSaltEven r ∧
      readBuffer s' (C_ROW + 120 * pairIdx + 56) 24 = pairSaltOdd r ∧
      CommitMemOutside s s' (C_ROW + 120 * pairIdx + 40) (C_ROW + 120 * pairIdx + 80) := by
  have hCR : C_ROW = 5368713248 := rfl
  have hLEN : LENGTH / 2 = 8388608 := by decide
  have hMB : MEMORY_BYTES = 68719476736 := rfl
  have haddr_lt : C_ROW + 120 * pairIdx + 40 < 2 ^ 64 := by omega
  have haddr_bd : C_ROW + 120 * pairIdx + 40 + 40 ≤ MEMORY_BYTES := by omega
  have haddr_toNat : (s.getReg .x10).toNat = C_ROW + 120 * pairIdx + 40 := by
    rw [hx10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr_lt]
  have hx11_toNat : (s.getReg .x11).toNat = 40 := by rw [hx11]; rfl
  have hrand_valid : randomArgumentsValid s = true := by
    unfold randomArgumentsValid rangeValid
    rw [haddr_toNat, hx11_toNat]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by omega, haddr_bd⟩
  have hfetch0 : fetch (submission.image .commit) s = some (.base .ECALL) :=
    commit_fetch_p0 s k 0 hk (by omega) (by simpa only [Nat.add_zero] using hpc)
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
    have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (14 + 2 * k + 1)) := c_pc_step_idx s _ hpc
    have hst1 : DetRun oracle (submission.image .commit) s1 1 (c_randPairState s r) 1 0 :=
      DetRun.step1 (commit_fetch_p0 s1 k 1 hk (by omega) hs1_pc) rfl
    have hmap : (execute (submission.image .commit) (1 + extra) s1 true >>=
          fun res => pure (res.charge 6 0)) =
        (fun res : Execution => res.charge 6 0) <$> execute (submission.image .commit) (1 + extra) s1 true := by
      rw [map_eq_bind_pure_comp]; rfl
    rw [hmap, oracle_run_map, hst1 extra, Functor.map_map]
    refine congrArg (fun fn => fn <$> oracle.run (execute (submission.image .commit) extra (c_randPairState s r) true)) ?_
    funext ⟨⟨ex, st, cy, ca⟩, n⟩
    simp only [Execution.charge, Nat.zero_add, Prod.mk.injEq, Execution.mk.injEq]
    exact ⟨⟨trivial, trivial, by omega, trivial⟩, trivial⟩
  · intro r
    let s1 := writeBits s (s.getReg .x10) r
    have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * (14 + 2 * k + 1)) := c_pc_step_idx s _ hpc
    have hs1_eq : s1 = writeBits s (BitVec.ofNat 64 (C_ROW + 120 * pairIdx + 40)) r := by
      simp only [s1, hx10]
    have hmem : (c_randPairState s r).mem = s1.mem := c_mem_exec_ADDI s1 .x10 .x10 (120#12)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [c_randPairState, c_pc_exec_ADDI, c_pc_step_idx s1 _ hs1_pc]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · intro reg hreg
      have h1 : (c_randPairState s r).getReg reg = s1.getReg reg := by
        simp only [c_randPairState, s1, execInstrBr, MachineState.getReg_setPC,
          c_getReg_setReg_ne .x10 reg (Ne.symm hreg)]
      exact h1.trans (writeBits_register s _ r reg)
    · have hs1_x10 : s1.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * pairIdx + 40) :=
        (writeBits_register s _ r .x10).trans hx10
      simp only [c_randPairState, s1, execInstrBr, MachineState.getReg_setPC,
        MachineState.getReg_setReg_eq (by decide : Reg.x10 ≠ .x0), hs1_x10,
        c_add_signExtend12_ofNat_small _ 120 (by omega)]
      exact congrArg (BitVec.ofNat 64) (by omega)
    · rw [c_readBuffer_of_mem_eq hmem, hs1_eq]
      exact writeBits_readBuffer_pairSaltEven s _ r
    · rw [c_readBuffer_of_mem_eq hmem, hs1_eq,
        show C_ROW + 120 * pairIdx + 56 = (C_ROW + 120 * pairIdx + 40) + 16 by omega]
      exact writeBits_readBuffer_pairSaltOdd s _ r
    · have hpres1 : CommitMemOutside s s1 (C_ROW + 120 * pairIdx + 40) (C_ROW + 120 * pairIdx + 80) := by
        rw [hs1_eq]
        simpa only [show C_ROW + 120 * pairIdx + 40 + (320 + 7) / 8 = C_ROW + 120 * pairIdx + 80 by omega] using
          c_memPreserved_writeBits s (C_ROW + 120 * pairIdx + 40) r (by omega)
      exact hpres1.trans (CommitMemOutside.of_mem_eq hmem _ _)

/-- One 2048-pair `p0_loop` body (`words 14..4109`): 4096 steps, 14336 cycles, 0 oracle calls.
Uses existential state transformer so the kernel never unfolds 2048 steps. -/
private theorem c_rand_chunk_body (oracle : Oracle) (sc : MachineState)
    (chunkIdx : Nat) (hchunk : chunkIdx < 4096)
    (hpc : sc.pc = BitVec.ofNat 64 (0x1000 + 4 * 14))
    (hx5 : sc.getReg .x5 = 2#64)
    (hx10 : sc.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (2048 * chunkIdx) + 40))
    (hx11 : sc.getReg .x11 = 40#64) :
    ∃ (bodyState : (Fin 2048 → PairRand) → MachineState),
      (∀ extra,
        oracle.run (execute (submission.image .commit) (4096 + extra) sc true) =ᵈ
          (($ᵗ (Fin 2048 → PairRand)) >>= fun f =>
            (fun p : Execution × Nat => (p.1.charge 14336 0, p.2)) <$>
              oracle.run (execute (submission.image .commit) extra (bodyState f) true))) ∧
      ∀ f : Fin 2048 → PairRand,
        let se := bodyState f
        se.pc = BitVec.ofNat 64 (0x1000 + 4 * 4110) ∧
        (∀ reg : Reg, reg ≠ .x10 → se.getReg reg = sc.getReg reg) ∧
        se.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (2048 * (chunkIdx + 1)) + 40) ∧
        (∀ j : Fin 2048,
          readBuffer se (C_ROW + 120 * (2048 * chunkIdx + j.val) + 40) 24 = pairSaltEven (f j) ∧
          readBuffer se (C_ROW + 120 * (2048 * chunkIdx + j.val) + 56) 24 = pairSaltOdd (f j)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ j < 2048, q < C_ROW + 120 * (2048 * chunkIdx + j) + 40 ∨
            C_ROW + 120 * (2048 * chunkIdx + j) + 80 ≤ q) →
          se.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
  have hLEN : LENGTH / 2 = 8388608 := by decide
  have hind : ∀ k ≤ 2048,
      ∃ (stateOf : (Fin k → PairRand) → MachineState),
        (∀ extra,
          oracle.run (execute (submission.image .commit) (2 * k + extra) sc true) =ᵈ
            (($ᵗ (Fin k → PairRand)) >>= fun f =>
              (fun p : Execution × Nat => (p.1.charge (7 * k) 0, p.2)) <$>
                oracle.run (execute (submission.image .commit) extra (stateOf f) true))) ∧
        ∀ f : Fin k → PairRand,
          let sk := stateOf f
          sk.pc = BitVec.ofNat 64 (0x1000 + 4 * (14 + 2 * k)) ∧
          (∀ reg : Reg, reg ≠ .x10 → sk.getReg reg = sc.getReg reg) ∧
          sk.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (2048 * chunkIdx + k) + 40) ∧
          (∀ j : Fin k,
            readBuffer sk (C_ROW + 120 * (2048 * chunkIdx + j.val) + 40) 24 = pairSaltEven (f j) ∧
            readBuffer sk (C_ROW + 120 * (2048 * chunkIdx + j.val) + 56) 24 = pairSaltOdd (f j)) ∧
          (∀ q : Nat, q < 2 ^ 64 →
            (∀ j < k, q < C_ROW + 120 * (2048 * chunkIdx + j) + 40 ∨
              C_ROW + 120 * (2048 * chunkIdx + j) + 80 ≤ q) →
            sk.getByte (BitVec.ofNat 64 q) = sc.getByte (BitVec.ofNat 64 q)) := by
    intro k hk; induction k with
    | zero =>
      refine ⟨fun _ => sc, ?_, ?_⟩
      · intro extra
        have hid : (fun p : Execution × Nat => (p.1.charge 0 0, p.2)) = id := by
          funext ⟨⟨ex, st, cy, ca⟩, n⟩; simp only [Execution.charge, Nat.zero_add, id_eq]
        simpa only [Nat.mul_zero, Nat.zero_add, hid, id_map, pure_bind] using
          c_uniformSample_fin0_pairRand.bind_left
            (fun _ => oracle.run (execute (submission.image .commit) extra sc true))
      · intro f
        exact ⟨by simpa using hpc, fun _ _ => rfl, by simpa using hx10,
          fun j => j.elim0, fun _ _ _ => rfl⟩
    | succ k ih =>
      obtain ⟨stateOf, hrun_k, hspec_k⟩ := ih (by omega)
      let stateNext : (Fin (k + 1) → PairRand) → MachineState :=
        fun f => c_randPairState (stateOf (fun i => f ⟨i.val, by omega⟩)) (f ⟨k, by omega⟩)
      have hstep_all : ∀ acc : Fin k → PairRand,
          let sk := stateOf acc
          (∀ extra,
            oracle.run (execute (submission.image .commit) (2 + extra) sk true) =
              (($ᵗ PairRand) >>= fun r =>
                (fun p : Execution × Nat => (p.1.charge 7 0, p.2)) <$>
                  oracle.run (execute (submission.image .commit) extra (c_randPairState sk r) true))) ∧
          ∀ r : PairRand,
            let s' := c_randPairState sk r
            s'.pc = BitVec.ofNat 64 (0x1000 + 4 * (14 + 2 * (k + 1))) ∧
            (∀ reg : Reg, reg ≠ .x10 → s'.getReg reg = sk.getReg reg) ∧
            s'.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (2048 * chunkIdx + k + 1) + 40) ∧
            readBuffer s' (C_ROW + 120 * (2048 * chunkIdx + k) + 40) 24 = pairSaltEven r ∧
            readBuffer s' (C_ROW + 120 * (2048 * chunkIdx + k) + 56) 24 = pairSaltOdd r ∧
            CommitMemOutside sk s' (C_ROW + 120 * (2048 * chunkIdx + k) + 40)
              (C_ROW + 120 * (2048 * chunkIdx + k) + 80) := by
        intro acc
        obtain ⟨hpck, hregk, hx10k, _, _⟩ := hspec_k acc
        exact c_rand_pair_step oracle (stateOf acc) k (2048 * chunkIdx + k)
          (by omega) (by omega) hpck
          ((hregk .x5 (by decide)).trans hx5) hx10k ((hregk .x11 (by decide)).trans hx11)
      refine ⟨stateNext, ?_, ?_⟩
      · intro extra
        have hsplit : 2 * (k + 1) + extra = 2 * k + (2 + extra) := by omega
        rw [hsplit]
        refine (hrun_k (2 + extra)).trans ?_
        have hstep_eq :
            (($ᵗ (Fin k → PairRand)) >>= fun acc =>
              (fun p : Execution × Nat => (p.1.charge (7 * k) 0, p.2)) <$>
                oracle.run (execute (submission.image .commit) (2 + extra) (stateOf acc) true)) =
            (do let acc ← $ᵗ (Fin k → PairRand)
                let r ← $ᵗ PairRand
                (fun p : Execution × Nat => (p.1.charge (7 * (k + 1)) 0, p.2)) <$>
                  oracle.run (execute (submission.image .commit) extra
                    (stateNext (c_snocFn acc r)) true)) := by
          apply bind_congr; intro acc
          rw [(hstep_all acc).1 extra, map_bind]
          apply bind_congr; intro r
          rw [Functor.map_map, c_charge_compose_beta]
          have hst_eq : stateNext (c_snocFn acc r) = c_randPairState (stateOf acc) r := by
            dsimp only [stateNext]
            have h1 : (fun i : Fin k => c_snocFn acc r ⟨i.val, by omega⟩) = acc := by
              funext ⟨i, hi⟩; simp [c_snocFn, hi]
            have h2 : c_snocFn acc r ⟨k, by omega⟩ = r := by simp [c_snocFn]
            rw [h1, h2]
          rw [hst_eq, show 7 * k + 7 = 7 * (k + 1) by omega]
        rw [hstep_eq]
        exact c_uniformSample_snoc_pairRand k (fun f =>
          (fun p : Execution × Nat => (p.1.charge (7 * (k + 1)) 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) extra (stateNext f) true))
      · intro f
        let acc : Fin k → PairRand := fun i => f ⟨i.val, by omega⟩
        let r : PairRand := f ⟨k, by omega⟩
        obtain ⟨hpck, hregk, hx10k, hsaltk, hpresk⟩ := hspec_k acc
        obtain ⟨hpc', hreg', hx10', hev', hodd', hpres'⟩ := (hstep_all acc).2 r
        refine ⟨hpc', fun reg hr => (hreg' reg hr).trans (hregk reg hr),
          by simpa only [Nat.add_assoc] using hx10', ?_, ?_⟩
        · intro ⟨j, hj⟩
          have hCR : C_ROW = 5368713248 := rfl
          dsimp only [stateNext]
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
  obtain ⟨bodyState, hrun, hspec⟩ := hind 2048 (le_refl _)
  refine ⟨bodyState, hrun, fun f => ?_⟩
  obtain ⟨hpc', hreg', hx10', hsalt', hpres'⟩ := hspec f
  exact ⟨hpc', hreg', hx10'.trans (congrArg (BitVec.ofNat 64) (by omega)), hsalt', hpres'⟩

/-- Isolated non-last latch `BEQ x10, x19, 8#13; JAL x0, 2080764#21` at words `4110..4111` (2 steps). -/
private theorem c_rand_latch_back (oracle : Oracle) (chunkIdx : Nat) (hchunk : chunkIdx < 4095)
    (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 4110))
    (hx10 : se.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (2048 * (chunkIdx + 1)) + 40))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes + 40)) :
    let sb := execInstrBr (execInstrBr se (.BEQ .x10 .x19 (8#13))) (.JAL .x0 (2080764#21))
    DetRun oracle (submission.image .commit) se 2 sb 2 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 14) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  have hCR : C_ROW = 5368713248 := rfl
  have hrb := rowBytes_eq
  let s1 := execInstrBr se (.BEQ .x10 .x19 (8#13))
  let s2 := execInstrBr s1 (.JAL .x0 (2080764#21))
  have hst1 : DetRun oracle (submission.image .commit) se 1 s1 1 0 :=
    DetRun.step1 (commit_fetch_commitMid0Instr se 4110 (by omega) (by omega) hpc) rfl
  have hne : (se.getReg .x10 == se.getReg .x19) = false := by
    rw [hx10, hx19, beq_eq_false_iff_ne]
    exact c_bv64_ne_of_nat_ne (by omega) (by omega) (by omega)
  have hs1_pc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 4111) := by
    simp only [s1, execInstrBr, hne, Bool.false_eq_true, ite_false, c_pc_setPC]
    exact c_pc_step_idx se 4110 hpc
  have hst2 : DetRun oracle (submission.image .commit) s1 1 s2 1 0 :=
    DetRun.step1 (commit_fetch_commitMid0Instr s1 4111 (by omega) (by omega) hs1_pc) rfl
  have hs2_pc : s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 14) := by
    simp only [s2, execInstrBr, c_pc_setPC, hs1_pc]
    exact c_pc_jal_4111
  exact ⟨hst1.trans hst2, hs2_pc,
    (c_mem_exec_JAL s1 _ _).trans (c_mem_exec_BEQ se _ _ _),
    fun reg => (c_reg_exec_JAL0 s1 _ reg).trans (c_reg_exec_BEQ se _ _ _ reg)⟩

/-- Isolated final latch `BEQ x10, x19, 8#13` (taken) at word `4110` (1 step → word `4112`). -/
private theorem c_rand_latch_exit (oracle : Oracle) (se : MachineState)
    (hpc : se.pc = BitVec.ofNat 64 (0x1000 + 4 * 4110))
    (hx10 : se.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (2048 * 4096) + 40))
    (hx19 : se.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes + 40)) :
    let sb := execInstrBr se (.BEQ .x10 .x19 (8#13))
    DetRun oracle (submission.image .commit) se 1 sb 1 0 ∧
    sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 4112) ∧
    sb.mem = se.mem ∧
    (∀ reg : Reg, sb.getReg reg = se.getReg reg) := by
  have hrb := rowBytes_eq
  let sb := execInstrBr se (.BEQ .x10 .x19 (8#13))
  have hst : DetRun oracle (submission.image .commit) se 1 sb 1 0 :=
    DetRun.step1 (commit_fetch_commitMid0Instr se 4110 (by omega) (by omega) hpc) rfl
  have heq : (se.getReg .x10 == se.getReg .x19) = true := by
    rw [hx10, hx19, hrb]; exact beq_self_eq_true _
  have hpc' : sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 4112) := by
    simp only [sb, execInstrBr, heq, ite_true, c_pc_setPC, hpc]
    exact c_pc_beq_4110
  exact ⟨hst, hpc', c_mem_exec_BEQ se _ _ _, c_reg_exec_BEQ se _ _ _⟩

private theorem c_half_len_eq : LENGTH / 2 = 2048 * 4095 + 2048 := by decide

/-- Full `p0_loop` (`4096` chunks × `2048` pairs = `8,388,608` `RANDOM(40)` draws,
words `14..4111`): `16,785,407` steps, `58,728,447` cycles, `0` oracle calls.
Uses existential state transformers so the kernel never unfolds 4095 × 2048 steps. -/
private theorem c_rand_loop (oracle : Oracle) (s1 : MachineState)
    (hpc : s1.pc = BitVec.ofNat 64 (0x1000 + 4 * 14))
    (hx5 : s1.getReg .x5 = 2#64)
    (hx10 : s1.getReg .x10 = BitVec.ofNat 64 (C_ROW + 40))
    (hx11 : s1.getReg .x11 = 40#64)
    (hx19 : s1.getReg .x19 = BitVec.ofNat 64 (C_ROW + rowBytes + 40)) :
    ∃ (fullState : (Fin (LENGTH / 2) → PairRand) → MachineState),
      (∀ extra,
        oracle.run (execute (submission.image .commit) (16785407 + extra) s1 true) =ᵈ
          (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
            (fun p : Execution × Nat => (p.1.charge 58728447 0, p.2)) <$>
              oracle.run (execute (submission.image .commit) extra (fullState rand) true))) ∧
      ∀ rand : Fin (LENGTH / 2) → PairRand,
        let s2 := fullState rand
        s2.pc = BitVec.ofNat 64 (0x1000 + 4 * 4112) ∧
        (∀ reg : Reg, reg ≠ .x10 → s2.getReg reg = s1.getReg reg) ∧
        (∀ j : Fin (LENGTH / 2),
          readBuffer s2 (C_ROW + 120 * j.val + 40) 24 = pairSaltEven (rand j) ∧
          readBuffer s2 (C_ROW + 120 * j.val + 56) 24 = pairSaltOdd (rand j)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ j < LENGTH / 2, q < C_ROW + 120 * j + 40 ∨ C_ROW + 120 * j + 80 ≤ q) →
          s2.getByte (BitVec.ofNat 64 q) = s1.getByte (BitVec.ofNat 64 q)) := by
  have hLEN := c_half_len_eq
  have hind : ∀ n ≤ 4095,
      ∃ (prefState : (Fin (2048 * n) → PairRand) → MachineState),
        (∀ extra,
          oracle.run (execute (submission.image .commit) (4098 * n + extra) s1 true) =ᵈ
            (($ᵗ (Fin (2048 * n) → PairRand)) >>= fun f =>
              (fun p : Execution × Nat => (p.1.charge (14338 * n) 0, p.2)) <$>
                oracle.run (execute (submission.image .commit) extra (prefState f) true))) ∧
        ∀ f : Fin (2048 * n) → PairRand,
          let sn := prefState f
          sn.pc = BitVec.ofNat 64 (0x1000 + 4 * 14) ∧
          (∀ reg : Reg, reg ≠ .x10 → sn.getReg reg = s1.getReg reg) ∧
          sn.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (2048 * n) + 40) ∧
          (∀ j : Fin (2048 * n),
            readBuffer sn (C_ROW + 120 * j.val + 40) 24 = pairSaltEven (f j) ∧
            readBuffer sn (C_ROW + 120 * j.val + 56) 24 = pairSaltOdd (f j)) ∧
          (∀ q : Nat, q < 2 ^ 64 →
            (∀ j < 2048 * n, q < C_ROW + 120 * j + 40 ∨ C_ROW + 120 * j + 80 ≤ q) →
            sn.getByte (BitVec.ofNat 64 q) = s1.getByte (BitVec.ofNat 64 q)) := by
    intro n hn; induction n with
    | zero =>
      refine ⟨fun _ => s1, ?_, ?_⟩
      · intro extra
        have hid : (fun p : Execution × Nat => (p.1.charge 0 0, p.2)) = id := by
          funext ⟨⟨ex, st, cy, ca⟩, m⟩; simp only [Execution.charge, Nat.zero_add, id_eq]
        simpa only [Nat.mul_zero, Nat.zero_add, hid, id_map, pure_bind] using
          c_uniformSample_fin0_pairRand.bind_left
            (fun _ => oracle.run (execute (submission.image .commit) extra s1 true))
      · intro f
        exact ⟨hpc, fun _ _ => rfl, by simpa only [Nat.mul_zero, Nat.add_zero] using hx10,
          fun j => j.elim0, fun _ _ _ => rfl⟩
    | succ n ih =>
      obtain ⟨prefState, hrun_n, hspec_n⟩ := ih (by omega)
      have hbody_ex : ∀ acc : Fin (2048 * n) → PairRand,
          ∃ (bodyState : (Fin 2048 → PairRand) → MachineState),
            (∀ extra,
              oracle.run (execute (submission.image .commit) (4096 + extra) (prefState acc) true) =ᵈ
                (($ᵗ (Fin 2048 → PairRand)) >>= fun f =>
                  (fun p : Execution × Nat => (p.1.charge 14336 0, p.2)) <$>
                    oracle.run (execute (submission.image .commit) extra (bodyState f) true))) ∧
            ∀ f : Fin 2048 → PairRand,
              let se := bodyState f
              se.pc = BitVec.ofNat 64 (0x1000 + 4 * 4110) ∧
              (∀ reg : Reg, reg ≠ .x10 → se.getReg reg = (prefState acc).getReg reg) ∧
              se.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (2048 * (n + 1)) + 40) ∧
              (∀ j : Fin 2048,
                readBuffer se (C_ROW + 120 * (2048 * n + j.val) + 40) 24 = pairSaltEven (f j) ∧
                readBuffer se (C_ROW + 120 * (2048 * n + j.val) + 56) 24 = pairSaltOdd (f j)) ∧
              (∀ q : Nat, q < 2 ^ 64 →
                (∀ j < 2048, q < C_ROW + 120 * (2048 * n + j) + 40 ∨
                  C_ROW + 120 * (2048 * n + j) + 80 ≤ q) →
                se.getByte (BitVec.ofNat 64 q) = (prefState acc).getByte (BitVec.ofNat 64 q)) := by
        intro acc
        obtain ⟨hpcn, hregn, hx10n, _, _⟩ := hspec_n acc
        exact c_rand_chunk_body oracle (prefState acc) n (by omega)
          hpcn ((hregn .x5 (by decide)).trans hx5) hx10n ((hregn .x11 (by decide)).trans hx11)
      let bodyOf (acc : Fin (2048 * n) → PairRand) : (Fin 2048 → PairRand) → MachineState :=
        Classical.choose (hbody_ex acc)
      let backOf (acc : Fin (2048 * n) → PairRand) (ch : Fin 2048 → PairRand) : MachineState :=
        execInstrBr (execInstrBr (bodyOf acc ch) (.BEQ .x10 .x19 (8#13))) (.JAL .x0 (2080764#21))
      let prefNext : (Fin (2048 * (n + 1)) → PairRand) → MachineState :=
        fun f => backOf (fun i => f ⟨i.val, by omega⟩) (fun j => f ⟨2048 * n + j.val, by omega⟩)
      have hchunk_all : ∀ acc : Fin (2048 * n) → PairRand,
          let sn := prefState acc
          (∀ extra,
            oracle.run (execute (submission.image .commit) (4098 + extra) sn true) =ᵈ
              (($ᵗ (Fin 2048 → PairRand)) >>= fun ch =>
                (fun p : Execution × Nat => (p.1.charge 14338 0, p.2)) <$>
                  oracle.run (execute (submission.image .commit) extra (backOf acc ch) true))) ∧
          ∀ ch : Fin 2048 → PairRand,
            let sb := backOf acc ch
            sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 14) ∧
            (∀ reg : Reg, reg ≠ .x10 → sb.getReg reg = sn.getReg reg) ∧
            sb.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (2048 * (n + 1)) + 40) ∧
            (∀ j : Fin 2048,
              readBuffer sb (C_ROW + 120 * (2048 * n + j.val) + 40) 24 = pairSaltEven (ch j) ∧
              readBuffer sb (C_ROW + 120 * (2048 * n + j.val) + 56) 24 = pairSaltOdd (ch j)) ∧
            (∀ q : Nat, q < 2 ^ 64 →
              (∀ j < 2048, q < C_ROW + 120 * (2048 * n + j) + 40 ∨
                C_ROW + 120 * (2048 * n + j) + 80 ≤ q) →
              sb.getByte (BitVec.ofNat 64 q) = sn.getByte (BitVec.ofNat 64 q)) := by
        intro acc
        obtain ⟨_, hregn, _, _, _⟩ := hspec_n acc
        obtain ⟨hbody_run, hbody_spec⟩ := Classical.choose_spec (hbody_ex acc)
        constructor
        · intro extra
          have hsp : 4098 + extra = 4096 + (2 + extra) := by omega
          rw [hsp]
          refine (hbody_run (2 + extra)).trans ?_
          apply EvalDistEq.bind_right; intro ch
          obtain ⟨hpce, hrege, hx10e, _, _⟩ := hbody_spec ch
          obtain ⟨hlatch_run, _, _, _⟩ := c_rand_latch_back oracle n (by omega)
            (bodyOf acc ch) hpce hx10e
            ((hrege .x19 (by decide)).trans ((hregn .x19 (by decide)).trans hx19))
          rw [hlatch_run extra, Functor.map_map]
          have hfn : (fun a : Execution × Nat =>
                ((a.1.charge 2 0, 0 + a.2).1.charge 14336 0, (a.1.charge 2 0, 0 + a.2).2)) =
              (fun p : Execution × Nat => (p.1.charge 14338 0, p.2)) := by
            funext ⟨⟨ex, st, cy, ca⟩, m⟩
            simp only [Execution.charge, Nat.zero_add, Prod.mk.injEq, Execution.mk.injEq]
            exact ⟨⟨trivial, trivial, by omega, trivial⟩, trivial⟩
          rw [hfn]
        · intro ch
          obtain ⟨hpce, hrege, hx10e, hsalte, hprese⟩ := hbody_spec ch
          obtain ⟨_, hpc_end, hmem_l, hreg_l⟩ := c_rand_latch_back oracle n (by omega)
            (bodyOf acc ch) hpce hx10e
            ((hrege .x19 (by decide)).trans ((hregn .x19 (by decide)).trans hx19))
          refine ⟨hpc_end, fun reg hr => (hreg_l reg).trans (hrege reg hr),
            (hreg_l .x10).trans hx10e, ?_, ?_⟩
          · intro j
            rw [c_readBuffer_of_mem_eq hmem_l, c_readBuffer_of_mem_eq hmem_l]
            exact hsalte j
          · intro q hq hout
            rw [c_getByte_of_mem_eq hmem_l]
            exact hprese q hq hout
      refine ⟨prefNext, ?_, ?_⟩
      · intro extra
        have hsplit : 4098 * (n + 1) + extra = 4098 * n + (4098 + extra) := by omega
        rw [hsplit]
        refine (hrun_n (4098 + extra)).trans ?_
        have hstep_d :
            (($ᵗ (Fin (2048 * n) → PairRand)) >>= fun acc =>
              (fun p : Execution × Nat => (p.1.charge (14338 * n) 0, p.2)) <$>
                oracle.run (execute (submission.image .commit) (4098 + extra) (prefState acc) true)) =ᵈ
            (do let acc ← $ᵗ (Fin (2048 * n) → PairRand)
                let ch ← $ᵗ (Fin 2048 → PairRand)
                (fun p : Execution × Nat => (p.1.charge (14338 * (n + 1)) 0, p.2)) <$>
                  oracle.run (execute (submission.image .commit) extra
                    (prefNext (c_concatFn (2048 * n) 2048 acc ch)) true)) := by
          apply EvalDistEq.bind_right; intro acc
          refine ((hchunk_all acc).1 extra).map _ |>.trans ?_
          rw [map_bind]
          apply EvalDistEq.bind_right; intro ch
          rw [Functor.map_map, c_charge_compose_beta]
          have hst_eq : prefNext (c_concatFn (2048 * n) 2048 acc ch) = backOf acc ch := by
            dsimp only [prefNext]
            have h1 : (fun i : Fin (2048 * n) => c_concatFn (2048 * n) 2048 acc ch ⟨i.val, by omega⟩) = acc := by
              funext ⟨i, hi⟩; simp [c_concatFn, hi]
            have h2 : (fun j : Fin 2048 => c_concatFn (2048 * n) 2048 acc ch ⟨2048 * n + j.val, by omega⟩) = ch := by
              funext ⟨j, hj⟩
              have hnot : ¬ (2048 * n + j < 2048 * n) := by omega
              simp [c_concatFn, hnot]
            rw [h1, h2]
          rw [hst_eq, show 14338 * n + 14338 = 14338 * (n + 1) by omega]
        exact hstep_d.trans (c_uniformSample_concat_pairRand (2048 * n) 2048 (fun f =>
          (fun p : Execution × Nat => (p.1.charge (14338 * (n + 1)) 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) extra (prefNext f) true)))
      · intro f
        let acc : Fin (2048 * n) → PairRand := fun i => f ⟨i.val, by omega⟩
        let ch : Fin 2048 → PairRand := fun j => f ⟨2048 * n + j.val, by omega⟩
        obtain ⟨hpcn, hregn, hx10n, hsaltn, hpresn⟩ := hspec_n acc
        obtain ⟨hpc', hreg', hx10', hsalt', hpres'⟩ := (hchunk_all acc).2 ch
        refine ⟨hpc', fun reg hr => (hreg' reg hr).trans (hregn reg hr), hx10', ?_, ?_⟩
        · intro ⟨j, hj⟩
          have hCR : C_ROW = 5368713248 := rfl
          dsimp only [prefNext]
          by_cases hjn : j < 2048 * n
          · obtain ⟨hevj, hoddj⟩ := hsaltn ⟨j, hjn⟩
            refine ⟨?_, ?_⟩
            · exact (readBuffer_congr _ _ (C_ROW + 120 * j + 40) 24 (fun b hb => hpres' (C_ROW + 120 * j + 40 + b) (by omega)
                (fun j' _ => by omega))).trans hevj
            · exact (readBuffer_congr _ _ (C_ROW + 120 * j + 56) 24 (fun b hb => hpres' (C_ROW + 120 * j + 56 + b) (by omega)
                (fun j' _ => by omega))).trans hoddj
          · have hsub : j - 2048 * n < 2048 := by omega
            have heqj : 2048 * n + (j - 2048 * n) = j := by omega
            simpa only [acc, ch, heqj] using hsalt' ⟨j - 2048 * n, hsub⟩
        · intro q hq hout
          have h1 := hpres' q hq (fun j hj => hout (2048 * n + j) (by omega))
          have h2 := hpresn q hq (fun j hj => hout j (by omega))
          exact h1.trans h2
  -- Combine 4095 prefix chunks with final chunk 4095 (BEQ taken -> word 4112)
  obtain ⟨prefState, hrun_pref, hspec_pref⟩ := hind 4095 (le_refl _)
  have hlast_ex : ∀ acc : Fin (2048 * 4095) → PairRand,
      ∃ (bodyState : (Fin 2048 → PairRand) → MachineState),
        (∀ extra,
          oracle.run (execute (submission.image .commit) (4096 + extra) (prefState acc) true) =ᵈ
            (($ᵗ (Fin 2048 → PairRand)) >>= fun f =>
              (fun p : Execution × Nat => (p.1.charge 14336 0, p.2)) <$>
                oracle.run (execute (submission.image .commit) extra (bodyState f) true))) ∧
        ∀ f : Fin 2048 → PairRand,
          let se := bodyState f
          se.pc = BitVec.ofNat 64 (0x1000 + 4 * 4110) ∧
          (∀ reg : Reg, reg ≠ .x10 → se.getReg reg = (prefState acc).getReg reg) ∧
          se.getReg .x10 = BitVec.ofNat 64 (C_ROW + 120 * (2048 * 4096) + 40) ∧
          (∀ j : Fin 2048,
            readBuffer se (C_ROW + 120 * (2048 * 4095 + j.val) + 40) 24 = pairSaltEven (f j) ∧
            readBuffer se (C_ROW + 120 * (2048 * 4095 + j.val) + 56) 24 = pairSaltOdd (f j)) ∧
          (∀ q : Nat, q < 2 ^ 64 →
            (∀ j < 2048, q < C_ROW + 120 * (2048 * 4095 + j) + 40 ∨
              C_ROW + 120 * (2048 * 4095 + j) + 80 ≤ q) →
            se.getByte (BitVec.ofNat 64 q) = (prefState acc).getByte (BitVec.ofNat 64 q)) := by
    intro acc
    obtain ⟨hpcn, hregn, hx10n, _, _⟩ := hspec_pref acc
    exact c_rand_chunk_body oracle (prefState acc) 4095 (by omega)
      hpcn ((hregn .x5 (by decide)).trans hx5) hx10n ((hregn .x11 (by decide)).trans hx11)
  let lastBody (acc : Fin (2048 * 4095) → PairRand) : (Fin 2048 → PairRand) → MachineState :=
    Classical.choose (hlast_ex acc)
  let lastExit (acc : Fin (2048 * 4095) → PairRand) (ch : Fin 2048 → PairRand) : MachineState :=
    execInstrBr (lastBody acc ch) (.BEQ .x10 .x19 (8#13))
  let fullRaw : (Fin (2048 * 4095 + 2048) → PairRand) → MachineState :=
    fun f => lastExit (fun i => f ⟨i.val, by omega⟩) (fun j => f ⟨2048 * 4095 + j.val, by omega⟩)
  let fullState : (Fin (LENGTH / 2) → PairRand) → MachineState :=
    fun rand => fullRaw (fun i => rand ⟨i.val, by rw [hLEN]; exact i.isLt⟩)
  have hlast_all : ∀ acc : Fin (2048 * 4095) → PairRand,
      let sn := prefState acc
      (∀ extra,
        oracle.run (execute (submission.image .commit) (4097 + extra) sn true) =ᵈ
          (($ᵗ (Fin 2048 → PairRand)) >>= fun ch =>
            (fun p : Execution × Nat => (p.1.charge 14337 0, p.2)) <$>
              oracle.run (execute (submission.image .commit) extra (lastExit acc ch) true))) ∧
      ∀ ch : Fin 2048 → PairRand,
        let sb := lastExit acc ch
        sb.pc = BitVec.ofNat 64 (0x1000 + 4 * 4112) ∧
        (∀ reg : Reg, reg ≠ .x10 → sb.getReg reg = sn.getReg reg) ∧
        (∀ j : Fin 2048,
          readBuffer sb (C_ROW + 120 * (2048 * 4095 + j.val) + 40) 24 = pairSaltEven (ch j) ∧
          readBuffer sb (C_ROW + 120 * (2048 * 4095 + j.val) + 56) 24 = pairSaltOdd (ch j)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ j < 2048, q < C_ROW + 120 * (2048 * 4095 + j) + 40 ∨
            C_ROW + 120 * (2048 * 4095 + j) + 80 ≤ q) →
          sb.getByte (BitVec.ofNat 64 q) = sn.getByte (BitVec.ofNat 64 q)) := by
    intro acc
    obtain ⟨_, hregn, _, _, _⟩ := hspec_pref acc
    obtain ⟨hbody_run, hbody_spec⟩ := Classical.choose_spec (hlast_ex acc)
    constructor
    · intro extra
      have hsp : 4097 + extra = 4096 + (1 + extra) := by omega
      rw [hsp]
      refine (hbody_run (1 + extra)).trans ?_
      apply EvalDistEq.bind_right; intro ch
      obtain ⟨hpce, hrege, hx10e, _, _⟩ := hbody_spec ch
      obtain ⟨hlatch_run, _, _, _⟩ := c_rand_latch_exit oracle
        (lastBody acc ch) hpce hx10e
        ((hrege .x19 (by decide)).trans ((hregn .x19 (by decide)).trans hx19))
      rw [hlatch_run extra, Functor.map_map]
      have hfn : (fun a : Execution × Nat =>
            ((a.1.charge 1 0, 0 + a.2).1.charge 14336 0, (a.1.charge 1 0, 0 + a.2).2)) =
          (fun p : Execution × Nat => (p.1.charge 14337 0, p.2)) := by
        funext ⟨⟨ex, st, cy, ca⟩, m⟩
        simp only [Execution.charge, Nat.zero_add, Prod.mk.injEq, Execution.mk.injEq]
        exact ⟨⟨trivial, trivial, by omega, trivial⟩, trivial⟩
      rw [hfn]
    · intro ch
      obtain ⟨hpce, hrege, hx10e, hsalte, hprese⟩ := hbody_spec ch
      obtain ⟨_, hpc_end, hmem_l, hreg_l⟩ := c_rand_latch_exit oracle
        (lastBody acc ch) hpce hx10e
        ((hrege .x19 (by decide)).trans ((hregn .x19 (by decide)).trans hx19))
      refine ⟨hpc_end, fun reg hr => (hreg_l reg).trans (hrege reg hr), ?_, ?_⟩
      · intro j
        rw [c_readBuffer_of_mem_eq hmem_l, c_readBuffer_of_mem_eq hmem_l]
        exact hsalte j
      · intro q hq hout
        rw [c_getByte_of_mem_eq hmem_l]
        exact hprese q hq hout
  refine ⟨fullState, ?_, ?_⟩
  · intro extra
    have hsplit : 16785407 + extra = 4098 * 4095 + (4097 + extra) := by omega
    rw [hsplit]
    refine (hrun_pref (4097 + extra)).trans ?_
    have hstep_d :
        (($ᵗ (Fin (2048 * 4095) → PairRand)) >>= fun acc =>
          (fun p : Execution × Nat => (p.1.charge (14338 * 4095) 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) (4097 + extra) (prefState acc) true)) =ᵈ
        (do let acc ← $ᵗ (Fin (2048 * 4095) → PairRand)
            let ch ← $ᵗ (Fin 2048 → PairRand)
            (fun p : Execution × Nat => (p.1.charge 58728447 0, p.2)) <$>
              oracle.run (execute (submission.image .commit) extra
                (fullRaw (c_concatFn (2048 * 4095) 2048 acc ch)) true)) := by
      apply EvalDistEq.bind_right; intro acc
      refine ((hlast_all acc).1 extra).map _ |>.trans ?_
      rw [map_bind]
      apply EvalDistEq.bind_right; intro ch
      rw [Functor.map_map, c_charge_compose_beta]
      have hst_eq : fullRaw (c_concatFn (2048 * 4095) 2048 acc ch) = lastExit acc ch := by
        dsimp only [fullRaw]
        have h1 : (fun i : Fin (2048 * 4095) => c_concatFn (2048 * 4095) 2048 acc ch ⟨i.val, by omega⟩) = acc := by
          funext ⟨i, hi⟩; simp [c_concatFn, hi]
        have h2 : (fun j : Fin 2048 => c_concatFn (2048 * 4095) 2048 acc ch ⟨2048 * 4095 + j.val, by omega⟩) = ch := by
          funext ⟨j, hj⟩
          have hnot : ¬ (2048 * 4095 + j < 2048 * 4095) := by omega
          simp [c_concatFn, hnot]
        rw [h1, h2]
      rw [hst_eq, show 14338 * 4095 + 14337 = 58728447 by decide]
    have hcat := hstep_d.trans (c_uniformSample_concat_pairRand (2048 * 4095) 2048 (fun f =>
      (fun p : Execution × Nat => (p.1.charge 58728447 0, p.2)) <$>
        oracle.run (execute (submission.image .commit) extra (fullRaw f) true)))
    exact hcat.trans (c_uniformSample_fin_cast (LENGTH / 2) (2048 * 4095 + 2048) hLEN (fun f =>
      (fun p : Execution × Nat => (p.1.charge 58728447 0, p.2)) <$>
        oracle.run (execute (submission.image .commit) extra (fullRaw f) true))).symm
  · intro rand
    let acc : Fin (2048 * 4095) → PairRand := fun i => rand ⟨i.val, by rw [hLEN]; omega⟩
    let ch : Fin 2048 → PairRand := fun j => rand ⟨2048 * 4095 + j.val, by rw [hLEN]; omega⟩
    obtain ⟨_, hreg_p, _, hsalt_p, hpres_p⟩ := hspec_pref acc
    obtain ⟨hpc_l, hreg_l, hsalt_l, hpres_l⟩ := (hlast_all acc).2 ch
    refine ⟨hpc_l, fun reg hr => (hreg_l reg hr).trans (hreg_p reg hr), ?_, ?_⟩
    · intro ⟨j, hj⟩
      have hCR : C_ROW = 5368713248 := rfl
      dsimp only [fullState, fullRaw]
      by_cases hjn : j < 2048 * 4095
      · obtain ⟨hevj, hoddj⟩ := hsalt_p ⟨j, hjn⟩
        refine ⟨?_, ?_⟩
        · exact (readBuffer_congr _ _ (C_ROW + 120 * j + 40) 24 (fun b hb => hpres_l (C_ROW + 120 * j + 40 + b) (by omega)
            (fun j' _ => by omega))).trans hevj
        · exact (readBuffer_congr _ _ (C_ROW + 120 * j + 56) 24 (fun b hb => hpres_l (C_ROW + 120 * j + 56 + b) (by omega)
            (fun j' _ => by omega))).trans hoddj
      · have hsub : j - 2048 * 4095 < 2048 := by omega
        have heqj : 2048 * 4095 + (j - 2048 * 4095) = j := by omega
        simpa only [acc, ch, heqj] using hsalt_l ⟨j - 2048 * 4095, hsub⟩
    · intro q hq hout
      have h1 := hpres_l q hq (fun j hj => hout (2048 * 4095 + j) (by rw [hLEN]; omega))
      have h2 := hpres_p q hq (fun j hj => hout j (by rw [hLEN]; omega))
      exact h1.trans h2

/-- Full Phase 0 (`words 0..4121`): prefix (`0..13`) + `8,388,608` paired `RANDOM(40)` draws
(`14..4111`) + Phase 1A setup (`4112..4121`). Exact `16,785,431` steps, `58,728,471` cycles,
`0` public oracle calls, collapsing in distribution (`=ᵈ`) to `$ᵗ (Fin (LENGTH / 2) → PairRand)`. -/
theorem commit_phase0 (oracle : Oracle) (message : Message) (extra : Nat) :
    ∃ (postState : (Fin (LENGTH / 2) → PairRand) → MachineState),
      oracle.run (execute (submission.image .commit) (16785431 + extra)
          (submission.initialState .commit message) true) =ᵈ
        (($ᵗ (Fin (LENGTH / 2) → PairRand)) >>= fun rand =>
          (fun p : Execution × Nat => (p.1.charge 58728471 0, p.2)) <$>
            oracle.run (execute (submission.image .commit) extra (postState rand) true)) ∧
      ∀ rand,
        let s := postState rand
        s.pc = BitVec.ofNat 64 (0x1000 + 4 * 4122) ∧
        s.getReg .x5 = 0#64 ∧
        s.getReg .x8 = BitVec.ofNat 64 C_MSG ∧
        s.getReg .x9 = BitVec.ofNat 64 C_TD ∧
        s.getReg .x10 = BitVec.ofNat 64 (C_MSG - 64) ∧
        s.getReg .x11 = 64#64 ∧
        s.getReg .x13 = 0#64 ∧
        s.getReg .x18 = BitVec.ofNat 64 C_ROW ∧
        s.getReg .x19 = BitVec.ofNat 64 (C_MSG + 2 ^ 32 - 64) ∧
        s.getReg .x26 = BitVec.ofNat 64 C_CMT ∧
        (∀ j : Fin (LENGTH / 2),
          readBuffer s (C_ROW + 120 * j.val + 40) 24 = pairSaltEven (rand j) ∧
          readBuffer s (C_ROW + 120 * j.val + 56) 24 = pairSaltOdd (rand j)) ∧
        (∀ q : Nat, q < 2 ^ 64 →
          (∀ j < LENGTH / 2, q < C_ROW + 120 * j + 40 ∨ C_ROW + 120 * j + 80 ≤ q) →
          s.getByte (BitVec.ofNat 64 q) = (submission.initialState .commit message).getByte (BitVec.ofNat 64 q)) := by
  let s0 := submission.initialState .commit message
  let s1 := c_prefixInstrs.foldl execInstrBr s0
  have hpre : DetRun oracle (submission.image .commit) s0 14 s1 14 0 :=
    c_prefix_run oracle s0 (c_initial_pc message)
  obtain ⟨hs1_pc, hs1_mem, hs1_x5, hs1_x8, hs1_x9, hs1_x10, hs1_x11, hs1_x18, hs1_x19, hs1_x26⟩ :=
    c_prefix_spec s0 (c_initial_pc message) (c_initial_x10 message) (c_initial_x11 message) (c_initial_x12 message)
  obtain ⟨fullState, hloop_run, hloop_spec⟩ :=
    c_rand_loop oracle s1 hs1_pc hs1_x5 hs1_x10 hs1_x11 hs1_x19
  let postState (rand : Fin (LENGTH / 2) → PairRand) : MachineState :=
    c_mid0Instrs.foldl execInstrBr (fullState rand)
  refine ⟨postState, ?_, ?_⟩
  · have hsplit : 16785431 + extra = 14 + (16785407 + (10 + extra)) := by omega
    rw [hsplit, hpre (16785407 + (10 + extra))]
    refine ((hloop_run (10 + extra)).map _).trans ?_
    rw [map_bind]
    apply EvalDistEq.bind_right; intro rand
    obtain ⟨hpc2, _, _, _⟩ := hloop_spec rand
    have hmid : DetRun oracle (submission.image .commit) (fullState rand) 10 (postState rand) 10 0 :=
      c_mid0_run oracle _ hpc2
    rw [hmid extra, Functor.map_map, Functor.map_map]
    have hfn :
        (fun a : Execution × Nat =>
          (((a.1.charge 10 0, 0 + a.2).1.charge 58728447 0, (a.1.charge 10 0, 0 + a.2).2).1.charge 14 0,
            0 + ((a.1.charge 10 0, 0 + a.2).1.charge 58728447 0, (a.1.charge 10 0, 0 + a.2).2).2)) =
        (fun p : Execution × Nat => (p.1.charge 58728471 0, p.2)) := by
      funext ⟨⟨ex, st, cy, ca⟩, n⟩
      simp only [Execution.charge, Nat.zero_add, Prod.mk.injEq, Execution.mk.injEq]
      exact ⟨⟨trivial, trivial, by omega, trivial⟩, trivial⟩
    rw [hfn]
  · intro rand
    let s2 := fullState rand
    obtain ⟨hpc2, hreg2, hsalt2, hpres2⟩ := hloop_spec rand
    obtain ⟨hpc3, hmem3, hx5_3, hx8_3, hx9_3, hx10_3, hx11_3, hx13_3, hx18_3, hx19_3, hx26_3⟩ :=
      c_mid0_spec s2 hpc2
        ((hreg2 .x8 (by decide)).trans hs1_x8)
        ((hreg2 .x9 (by decide)).trans hs1_x9)
        ((hreg2 .x18 (by decide)).trans hs1_x18)
        ((hreg2 .x26 (by decide)).trans hs1_x26)
    refine ⟨hpc3, hx5_3, hx8_3, hx9_3, hx10_3, hx11_3, hx13_3, hx18_3, hx19_3, hx26_3, ?_, ?_⟩
    · intro j
      rw [c_readBuffer_of_mem_eq hmem3, c_readBuffer_of_mem_eq hmem3]
      exact hsalt2 j
    · intro q hq hout
      rw [c_getByte_of_mem_eq hmem3, hpres2 q hq hout, c_getByte_of_mem_eq hs1_mem]

end CommitGolfCandidate
