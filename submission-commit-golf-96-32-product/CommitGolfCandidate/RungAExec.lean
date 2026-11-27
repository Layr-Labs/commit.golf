import CommitGolfCandidate.Probability
import CommitGolfCandidate.CountingCoins
import CommitGolfCandidate.RungAInterface
import CommitGolfCandidate.S4Machine
set_option Elab.async false
namespace CommitGolfCandidate.RungA
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec
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

end CommitGolfCandidate.RungA
