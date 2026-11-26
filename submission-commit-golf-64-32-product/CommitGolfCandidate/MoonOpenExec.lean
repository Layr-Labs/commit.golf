import CommitGolfCandidate.MoonMemory

/-! Exact deterministic symbolic execution of the 235-word 64-32 opening image with branchless
64-bit aligned dword-buffered proof writing and streaming 6-bit tail packing (`pack6BitsRev`).
Tracks registers, read-only trapdoor/indices framing, flat 512-byte heap-indexed cap-mark scratch
bytes (`[4096, 4608)`), forward proof bytes (`[10804531232, 19285417728)`), tail-stream scratch
bytes (`[20000000000, 68719476736)`), and exact telescoping step/cycle counts with zero oracle
calls (`≤ 110,258` cycles at `positions.card = BATCH`, `≤ 2^38` universally). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-! ### 1. Program Counter, Trapdoor Views, and Deterministic Multi-Step Relation -/

def o_pcAt (idx : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * idx)

def tdNode (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (l idx : Nat) : Digest :=
  trapdoor.extractLsb' (8 * (32 * heapIdx l idx)) 256

def tdSalt (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) : Salt192 :=
  trapdoor.extractLsb' (8 * saltOff i) 192

/-- Deterministic multi-step execution of ordinary instructions in the opening image. -/
def OpenRuns (s : MachineState) (steps cycles : Nat) (s' : MachineState) : Prop :=
  ∀ fuel : Nat,
    execute (submission.image .opening) (steps + fuel) s true =
      (do let result ← execute (submission.image .opening) fuel s' true
          return result.charge cycles 0)

theorem OpenRuns.refl (s : MachineState) : OpenRuns s 0 0 s := by
  intro fuel
  simp [Execution.charge]

theorem OpenRuns.trans {s s1 s2 : MachineState} {n1 n2 c1 c2 : Nat}
    (h1 : OpenRuns s n1 c1 s1) (h2 : OpenRuns s1 n2 c2 s2) :
    OpenRuns s (n1 + n2) (c1 + c2) s2 := by
  intro fuel
  rw [Nat.add_assoc, h1 (n2 + fuel), h2 fuel]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext result
  simp [Execution.charge, Nat.add_assoc]

theorem OpenRuns.step {s s' : MachineState} {instr : Instruction}
    (hf : fetch (submission.image .opening) s = some instr)
    (hs : ordinaryStep s instr = some s') :
    OpenRuns s 1 (instructionCycles instr) s' := by
  intro fuel
  rw [Nat.add_comm 1 fuel]
  exact execute_ordinary_step (submission.image .opening) instr s s' fuel true hf hs

theorem OpenRuns.halt {s0 sHalt : MachineState} {haltIdx steps cycles totalFuel : Nat}
    (hrun : OpenRuns s0 steps cycles sHalt)
    (hhi : haltIdx < 235)
    (hi : openingInstr haltIdx = .base .ECALL)
    (hpc : sHalt.pc = o_pcAt haltIdx)
    (hx5 : sHalt.getReg .x5 = 1#64)
    (hx10 : sHalt.getReg .x10 = 0#64)
    (hfuel : steps + 1 ≤ totalFuel) :
    execute (submission.image .opening) totalFuel s0 true =
      pure { exit := .success, state := sHalt, cycles := cycles + 1, oracleCalls := 0 } := by
  have hf : fetch (submission.image .opening) sHalt = some (.base .ECALL) := by
    rw [opening_fetch sHalt haltIdx hhi hpc, hi]
  obtain ⟨extra, rfl⟩ : ∃ extra, totalFuel = steps + (extra + 1) :=
    ⟨totalFuel - (steps + 1), by omega⟩
  rw [hrun (extra + 1)]
  have hne0 : ¬ (sHalt.getReg .x5 = (0 : Word)) := by rw [hx5]; decide
  have heq1 : sHalt.getReg .x5 = (1 : Word) := hx5
  have heq0 : sHalt.getReg .x10 = (0 : Word) := hx10
  have h1 : execute (submission.image .opening) (extra + 1) sHalt true =
      pure { exit := .success, state := sHalt, cycles := 1, oracleCalls := 0 } := by
    simp only [execute, hf]
    rw [if_neg hne0, if_pos heq1, if_pos heq0]
  rw [h1, pure_bind]
  rfl

attribute [local irreducible] OpenRuns

/-! ### 2. `o_`-Prefixed MachineState, BitVec, Pack6, and List Helpers -/

private theorem o_getReg_setReg_ne (r r' : Reg) (h : r ≠ r') (s : MachineState) (v : Word) :
    (s.setReg r v).getReg r' = s.getReg r' :=
  MachineState.getReg_setReg_ne s r r' v h

private theorem o_getReg_setMem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

private theorem o_getReg_setByte (s : MachineState) (a : Word) (b : BitVec 8) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by cases r <;> rfl

private theorem o_getByte_setReg (s : MachineState) (r : Reg) (v a : Word) :
    (s.setReg r v).getByte a = s.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem_setReg]

private theorem o_getByte_setPC (s : MachineState) (v a : Word) :
    (s.setPC v).getByte a = s.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem_setPC]

private theorem o_pcAt_add4 (idx : Nat) : o_pcAt idx + 4 = o_pcAt (idx + 1) := by
  unfold o_pcAt
  change BitVec.ofNat 64 (0x1000 + 4 * idx) + BitVec.ofNat 64 4 = _
  rw [← BitVec.ofNat_add]
  congr 1

private theorem o_and_not_one_of_even (n : Nat) (heven : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  have hlow : BitVec.ofNat 64 n &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change (n % 2 ^ 64) &&& (2 ^ 1 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hor : (BitVec.ofNat 64 n &&& ~~~1#64) ||| (BitVec.ofNat 64 n &&& 1#64) =
      BitVec.ofNat 64 n := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    cases (1#64 : Word)[i] <;> simp
  simpa only [hlow, BitVec.or_zero] using hor

private theorem o_pcAt_jalr_return (idx : Nat) :
    (o_pcAt idx + signExtend12 (0#12)) &&& ~~~1#64 = o_pcAt idx := by
  have hse0 : signExtend12 (0#12) = 0#64 := by decide
  rw [hse0, BitVec.add_zero]
  exact o_and_not_one_of_even (0x1000 + 4 * idx) (by omega)

private theorem o_bv64_ofNat_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

private theorem o_bv64_ofNat_sub (a b : Nat) (hle : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have h : BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b = BitVec.ofNat 64 a := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel hle]
  have hc := congrArg (fun v : Word => v - BitVec.ofNat 64 b) h.symm
  simpa only [BitVec.add_sub_cancel] using hc

private theorem o_bv64_add_neg1 (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (4095#12) = BitVec.ofNat 64 n := by
  have hse : signExtend12 (4095#12) = BitVec.ofNat 64 (2 ^ 64 - 1) := by decide
  rw [hse, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have heq : n + 1 + (2 ^ 64 - 1) = n + 2 ^ 64 := by omega
  rw [heq, Nat.add_mod_right]

private theorem o_bv64_add_neg8 (n : Nat) (h : 8 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4088#12) = BitVec.ofNat 64 (n - 8) := by
  have hse : signExtend12 (4088#12) = BitVec.ofNat 64 (2 ^ 64 - 8) := by decide
  rw [hse, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have heq : n + (2 ^ 64 - 8) = (n - 8) + 2 ^ 64 := by omega
  rw [heq, Nat.add_mod_right]

private theorem o_bv64_add_neg64 (n : Nat) (h : 64 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4032#12) = BitVec.ofNat 64 (n - 64) := by
  have hse : signExtend12 (4032#12) = BitVec.ofNat 64 (2 ^ 64 - 64) := by decide
  rw [hse, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have heq : n + (2 ^ 64 - 64) = (n - 64) + 2 ^ 64 := by omega
  rw [heq, Nat.add_mod_right]

private theorem o_bv64_shl (a k : Nat) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_mod (a % 2 ^ 64), Nat.mod_mod, ← Nat.mul_mod]

private theorem o_bv64_ushr (a k : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a >>> k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

private theorem o_bv64_xor1 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ signExtend12 (1#12) = BitVec.ofNat 64 (a ^^^ 1) := by
  have hse : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  rw [hse]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64)]
  have hlt : a ^^^ 1 < 2 ^ 64 := by
    rcases Nat.even_or_odd' a with ⟨q, rfl | rfl⟩
    · rw [xor_one_even]; omega
    · rw [xor_one_odd]; omega
  rw [Nat.mod_eq_of_lt hlt]

private theorem o_bv64_xor63_8mul (r : Nat) (hr : r < 8) :
    BitVec.ofNat 64 (8 * r) ^^^ signExtend12 (63#12) = BitVec.ofNat 64 (63 - 8 * r) := by
  interval_cases r <;> decide

private theorem o_bv64_and1 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& signExtend12 (1#12) = BitVec.ofNat 64 (a % 2) := by
  have hse : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  rw [hse]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : a % 2 < 2 ^ 64)]
  change a &&& (2 ^ 1 - 1) = a % 2 ^ 1
  exact Nat.and_two_pow_sub_one_eq_mod a 1

private theorem o_bv64_ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro heq
  have hn := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hn
  exact hne hn

private theorem o_byte_zeroExtend_truncate8 (b : Byte) :
    (b.zeroExtend 64).truncate 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth]
  have hlt : b.toNat < 256 := b.isLt
  rw [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64), Nat.mod_eq_of_lt hlt]

private theorem o_bv64_ofNat_truncate8 (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).truncate 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem o_bool_byte_zeroExtend (b : Bool) :
    (if b then (1#8 : Byte) else 0#8).zeroExtend 64 = if b then 1#64 else 0#64 := by
  cases b <;> decide

private theorem o_bool_word_or (a b : Bool) :
    (if a then (1#64 : Word) else 0#64) ||| (if b then 1#64 else 0#64) =
      if (a || b) then 1#64 else 0#64 := by
  cases a <;> cases b <;> decide

private theorem o_bool_word_truncate8 (b : Bool) :
    (if b then (1#64 : Word) else 0#64).truncate 8 = if b then 1#8 else 0#8 := by
  cases b <;> decide

private theorem o_bool_word_ne_of_ne {a b : Bool} (h : a ≠ b) :
    (if a then (1#64 : Word) else 0#64) ≠ (if b then 1#64 else 0#64) := by
  cases a <;> cases b <;> first | exact absurd rfl h | decide

private theorem o_accessValid_ofNat (a w : Nat) (hle : a + w ≤ 68719476736) (hal : a % w = 0) :
    accessValid (BitVec.ofNat 64 a) w = true := by
  have ha : a < 2 ^ 64 := by omega
  simp only [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by omega, hal⟩

private theorem o_extractLsb'_extractLsb' {w : Nat} (x : BitVec w) (a m b k : Nat) (h : b + k ≤ m) :
    (x.extractLsb' a m).extractLsb' b k = x.extractLsb' (a + b) k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show b + i < m by omega, Nat.add_assoc]

private theorem o_getMem_extractByte {s : MachineState} {addr j : Nat}
    (hal : addr % 8 = 0) (hj : j < 8) :
    (s.getMem (BitVec.ofNat 64 addr)).extractLsb' (8 * j) 8 =
      s.getByte (BitVec.ofNat 64 (addr + j)) := by
  have hd := alignToDword_ofNat_eq addr j hj hal
  have hbo : byteOffset (BitVec.ofNat 64 (addr + j)) = j := by
    unfold byteOffset
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change ((addr + j) % 2 ^ 64) &&& (2 ^ 3 - 1) = j
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  simp only [MachineState.getByte, hd, hbo]
  unfold extractByte
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp [BitVec.truncate, hb, Nat.mul_comm]

private theorem o_word_or_shl_byte (w v : Word) (r : Nat) (hr : r < 8)
    (hwHi : ∀ j, r ≤ j → j < 8 → w.extractLsb' (8 * j) 8 = 0#8) (j : Nat) (hj : j < 8) :
    (w ||| (v <<< (8 * r))).extractLsb' (8 * j) 8 =
      if j < r then w.extractLsb' (8 * j) 8 else v.extractLsb' (8 * (j - r)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    hb, decide_true, Bool.true_and]
  by_cases hlt : j < r
  · rw [if_pos hlt]
    have hnot : ¬ (8 * r ≤ 8 * j + b) := by omega
    simp [BitVec.getLsbD_extractLsb', hb, hnot]
  · rw [if_neg hlt]
    have hw0 := congrArg (fun x : Byte => x.getLsbD b) (hwHi j (by omega) hj)
    simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and, BitVec.getLsbD_zero] at hw0
    have hle : 8 * r ≤ 8 * j + b := by omega
    have hnotlt : ¬ (8 * j + b < 8 * r) := by omega
    have hlt64 : 8 * j + b < 64 := by omega
    have hsub : 8 * j + b - 8 * r = 8 * (j - r) + b := by omega
    rw [hw0]
    simp [hb, hle, hnotlt, hlt64, hsub]

private theorem o_word_ushr1_ushr_byte (v : Word) (r : Nat) (hr : r < 8) (j : Nat) (hj : j < 8) :
    ((v >>> 1) >>> (63 - 8 * r)).extractLsb' (8 * j) 8 =
      if j < r then v.extractLsb' (8 * (8 - r + j)) 8 else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hb, decide_true, Bool.true_and]
  by_cases hlt : j < r
  · rw [if_pos hlt]
    have hidx : 1 + (63 - 8 * r + (8 * j + b)) = 8 * (8 - r + j) + b := by omega
    simp [hb, hidx]
  · rw [if_neg hlt]
    have hge : 64 ≤ 1 + (63 - 8 * r + (8 * j + b)) := by omega
    have hpow : 2 ^ 64 ≤ 2 ^ (1 + (63 - 8 * r + (8 * j + b))) :=
      Nat.pow_le_pow_right (by decide) hge
    have hdiv : v.toNat / 2 ^ (1 + (63 - 8 * r + (8 * j + b))) = 0 :=
      Nat.div_eq_of_lt (Nat.lt_of_lt_of_le v.isLt hpow)
    rw [BitVec.getLsbD_zero]
    simp [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, hdiv]

private theorem o_word_mask_low_bytes (v : Word) (m : Nat) (hm : m ≤ 8) (j : Nat) (hj : j < 8) :
    ((v <<< (8 * (8 - m))) >>> (8 * (8 - m))).extractLsb' (8 * j) 8 =
      if j < m then v.extractLsb' (8 * j) 8 else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    hb, decide_true, Bool.true_and]
  by_cases hlt : j < m
  · rw [if_pos hlt]
    have hlt64 : 8 * (8 - m) + (8 * j + b) < 64 := by omega
    have hle : 8 * (8 - m) ≤ 8 * (8 - m) + (8 * j + b) := by omega
    have hsub : 8 * (8 - m) + (8 * j + b) - 8 * (8 - m) = 8 * j + b := by omega
    simp [BitVec.getLsbD_extractLsb', hb, hlt64, hle, hsub]
  · rw [if_neg hlt]
    have hnot : ¬ (8 * (8 - m) + (8 * j + b) < 64) := by omega
    simp [hnot]

private theorem o_word_truncate8_eq_extractLsb'0 (w : Word) :
    w.truncate 8 = w.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp [BitVec.truncate, hb]

private theorem o_word_ushr8_extractLsb' (w : Word) (j : Nat) (hj : j + 1 < 8) :
    (w >>> 8).extractLsb' (8 * j) 8 = w.extractLsb' (8 * (j + 1)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hb, decide_true, Bool.true_and]
  congr 1; omega

private theorem o_word_tail6_from_hi (v : Word) (d : Digest)
    (hbyte5 : v.extractLsb' (8 * 5) 8 = d.extractLsb' (8 * 29) 8) :
    (v >>> 40) &&& signExtend12 (63#12) = BitVec.ofNat 64 (tail6 d).toNat := by
  have hse63 : signExtend12 (63#12) = 63#64 := by decide
  rw [hse63]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  by_cases h6 : b < 6
  · have hm : (63#64 : Word).getLsbD b = true := by interval_cases b <;> decide
    have hbit5 := congrArg (fun x : Byte => x.getLsbD b) hbyte5
    simp only [BitVec.getLsbD_extractLsb', show b < 8 by omega, decide_true, Bool.true_and] at hbit5
    have hlt64 : (tail6 d).toNat < 64 := (tail6 d).isLt
    have hrhs : (BitVec.ofNat 64 (tail6 d).toNat).getLsbD b = (tail6 d).getLsbD b := by
      simp only [BitVec.getLsbD, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : (tail6 d).toNat < 2 ^ 64)]
    rw [hm, Bool.and_true, hrhs]
    unfold tail6
    simp only [BitVec.getLsbD_extractLsb', h6, decide_true, Bool.true_and]
    simpa only [show 8 * 5 + b = 40 + b by omega, show 8 * 29 + b = 232 + b by omega] using hbit5
  · have hm : (63#64 : Word).getLsbD b = false := by
      simp only [BitVec.getLsbD_ofNat, hb, decide_true, Bool.true_and, Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 64 ≤ 2 ^ b := by
        have h1 : 2 ^ 6 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
        have h2 : 2 ^ 6 = 64 := by decide
        omega
      have hdiv : 63 / 2 ^ b = 0 := Nat.div_eq_of_lt (by omega)
      simp [hdiv]
    have hrhs : (BitVec.ofNat 64 (tail6 d).toNat).getLsbD b = false := by
      simp only [BitVec.getLsbD_ofNat, hb, decide_true, Bool.true_and, Nat.testBit_eq_decide_div_mod_eq]
      have hlt64 : (tail6 d).toNat < 64 := (tail6 d).isLt
      have hpow : 64 ≤ 2 ^ b := by
        have h1 : 2 ^ 6 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
        have h2 : 2 ^ 6 = 64 := by decide
        omega
      have hdiv : (tail6 d).toNat / 2 ^ b = 0 := Nat.div_eq_of_lt (by omega)
      simp [hdiv]
    rw [hm, Bool.and_false, hrhs]

private theorem o_tail_or_shl_eq_add (tBuf tCnt tVal : Nat)
    (hcnt : tCnt < 8) (hbuf : tBuf < 2 ^ tCnt) (hval : tVal < 64) :
    BitVec.ofNat 64 tBuf ||| (BitVec.ofNat 64 tVal <<< tCnt) =
      BitVec.ofNat 64 (tBuf + tVal * 2 ^ tCnt) := by
  have hpow : 2 ^ tCnt ≤ 128 := by
    have h1 : 2 ^ tCnt ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 7 = 128 := by decide
    omega
  rw [o_bv64_shl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : tBuf < 2 ^ 64),
    Nat.mod_eq_of_lt (by nlinarith : tVal * 2 ^ tCnt < 2 ^ 64),
    Nat.mod_eq_of_lt (by nlinarith : tBuf + tVal * 2 ^ tCnt < 2 ^ 64)]
  rw [← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hbuf, Nat.shiftLeft_eq,
    Nat.add_comm]

private theorem o_pack6Step_bounds (acc : List Byte) (buf cnt n : Nat) (t : BitVec 6)
    (hcnt : cnt < 8) (hbuf : buf < 2 ^ cnt) (hbits : 8 * acc.length + cnt = 6 * n) :
    let st := pack6Step (acc, buf, cnt) t
    st.2.2 < 8 ∧ st.2.1 < 2 ^ st.2.2 ∧ 8 * st.1.length + st.2.2 = 6 * (n + 1) := by
  unfold pack6Step; dsimp only
  have ht : t.toNat < 64 := t.isLt
  have hbuf' : buf + t.toNat * 2 ^ cnt < 2 ^ (cnt + 6) := by
    rw [Nat.pow_add, show (2 : Nat) ^ 6 = 64 by decide]
    have hm := Nat.mul_le_mul_right (2 ^ cnt) (show t.toNat ≤ 63 by omega)
    omega
  split_ifs with hge
  · dsimp only
    refine ⟨by omega, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
      rw [show 2 ^ (cnt + 6 - 8) * 256 = 2 ^ (cnt + 6) by
        rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_add, show cnt + 6 - 8 + 8 = cnt + 6 by omega]]
      exact hbuf'
    · simp only [List.length_append, List.length_singleton]; omega
  · dsimp only
    exact ⟨by omega, hbuf', by omega⟩

private theorem o_pack6_foldl_bounds_aux (tails : List (BitVec 6)) :
    ∀ acc buf cnt n,
      cnt < 8 → buf < 2 ^ cnt → 8 * acc.length + cnt = 6 * n →
      let st := tails.foldl pack6Step (acc, buf, cnt)
      st.2.2 < 8 ∧ st.2.1 < 2 ^ st.2.2 ∧ 8 * st.1.length + st.2.2 = 6 * (n + tails.length) := by
  induction tails with
  | nil =>
    intro acc buf cnt n hcnt hbuf hbits
    simpa using And.intro hcnt (And.intro hbuf hbits)
  | cons t rest ih =>
    intro acc buf cnt n hcnt hbuf hbits
    simp only [List.foldl_cons, List.length_cons]
    have h1 := o_pack6Step_bounds acc buf cnt n t hcnt hbuf hbits
    rcases hst : pack6Step (acc, buf, cnt) t with ⟨acc1, buf1, cnt1⟩
    rw [hst] at h1
    have h2 := ih acc1 buf1 cnt1 (n + 1) h1.1 h1.2.1 h1.2.2
    simpa only [show n + 1 + rest.length = n + (rest.length + 1) by omega] using h2

private theorem o_pack6_foldl_bounds (tails : List (BitVec 6)) :
    let st := tails.foldl pack6Step ([], 0, 0)
    st.2.2 < 8 ∧ st.2.1 < 2 ^ st.2.2 ∧ 8 * st.1.length + st.2.2 = 6 * tails.length := by
  simpa using o_pack6_foldl_bounds_aux tails [] 0 0 0 (by omega) (by decide) (by simp)

private theorem o_list_getElem_append_left {α : Type} (l1 l2 : List α) (i : Nat) (h : i < l1.length) :
    (l1 ++ l2)[i]'(by simp; omega) = l1[i] := by
  induction l1 generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k (by simp at h; omega)

private theorem o_list_getElem_append_right {α : Type} (l1 l2 : List α) (i : Nat)
    (h1 : l1.length ≤ i) (h2 : i < (l1 ++ l2).length) :
    (l1 ++ l2)[i]'h2 = l2[i - l1.length]'(by simp at h2; omega) := by
  induction l1 generalizing i with
  | nil => simp
  | cons a rest ih =>
    cases i with
    | zero => simp at h1
    | succ k =>
      simp only [List.cons_append, List.getElem_cons_succ, List.length_cons, Nat.succ_sub_succ_eq_sub]
      exact ih k (by simp at h1; omega) (by simp at h2 ⊢; omega)

private theorem o_list_mem_exists_getElem {α : Type} {l : List α} {x : α} (hx : x ∈ l) :
    ∃ (u : Nat) (hu : u < l.length), l[u]'hu = x := by
  induction l with
  | nil => cases hx
  | cons a rest ih =>
    rcases List.mem_cons.mp hx with rfl | hrest
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨u, hu, heq⟩ := ih hrest
      exact ⟨u + 1, by simp; omega, heq⟩

private theorem o_positions_card_le (positions : Positions) : positions.card ≤ 16777216 := by
  have h := Finset.card_le_univ positions
  rw [Fintype.card_fin] at h
  exact h

private theorem o_saltOff_formula (i : Index) :
    rowOff + 40 + (120 * (i.val / 2) + 16 * (i.val % 2)) = saltOff i := by
  unfold saltOff PAIR_STRIDE
  split_ifs <;> omega

private theorem o_saltOff_align8 (i : Index) : saltOff i % 8 = 0 := by
  unfold saltOff PAIR_STRIDE
  rw [rowOff_eq]
  split_ifs <;> omega

private theorem o_heapIdx_xor1 (l idx : Nat) (hl : l < 24) (hidx : idx < levelSize l) :
    heapIdx l idx ^^^ 1 = heapIdx l (idx ^^^ 1) := by
  have hev : levelSize l % 2 = 0 := by
    rw [levelSize_double l hl]; omega
  unfold heapIdx
  have hls : levelSize l = 2 * (levelSize l / 2) := by omega
  rcases Nat.even_or_odd' idx with ⟨q, rfl | rfl⟩
  · rw [xor_one_even, hls, show 2 * (levelSize l / 2) + 2 * q = 2 * (levelSize l / 2 + q) by omega,
      xor_one_even]; omega
  · rw [xor_one_odd, hls,
      show 2 * (levelSize l / 2) + (2 * q + 1) = 2 * (levelSize l / 2 + q) + 1 by omega,
      xor_one_odd]; omega

private theorem o_heapIdx_shr1 (l idx : Nat) (hl : l < 24) :
    heapIdx l idx >>> 1 = heapIdx (l + 1) (idx >>> 1) := by
  simp only [Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 1 = 2 from rfl]
  exact heapIdx_parent l idx hl

/-! ### 3. Single-Instruction Step Lemmas (`o_step_*`) -/

private theorem o_step_ADDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.ADDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (o_pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_ADD {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.ADD rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADD rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADD rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (o_pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SUB {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.SUB rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SUB rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SUB rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (o_pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SLLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.SLLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SLLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SLLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (o_pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SRLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.SRLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SRLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SRLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (o_pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SLL {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.SLL rd rs1 rs2)) :
    OpenRuns s 1 1
      ((s.setReg rd (s.getReg rs1 <<< ((s.getReg rs2).toNat % 64))).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SLL rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SLL rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 <<< ((s.getReg rs2).toNat % 64))).setPC (o_pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 <<< ((s.getReg rs2).toNat % 64))).setPC (s.pc + 4)) = _
    rw [hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SRL {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.SRL rd rs1 rs2)) :
    OpenRuns s 1 1
      ((s.setReg rd (s.getReg rs1 >>> ((s.getReg rs2).toNat % 64))).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SRL rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SRL rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 >>> ((s.getReg rs2).toNat % 64))).setPC (o_pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 >>> ((s.getReg rs2).toNat % 64))).setPC (s.pc + 4)) = _
    rw [hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_XORI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.XORI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.XORI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.XORI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (o_pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_ANDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.ANDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ANDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ANDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (o_pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_OR {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.OR rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.OR rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.OR rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (o_pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_LD {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.LD rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    OpenRuns s 1 1 ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.LD rd rs1 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.LD rd rs1 off)) =
      some ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (o_pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 8 = true
            then some ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SD {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.SD rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    OpenRuns s 1 1
      ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SD rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SD rs1 rs2 off)) =
      some ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (o_pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 8 = true
            then some ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_LBU {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.LBU rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 1 = true) :
    OpenRuns s 1 1
      ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.LBU rd rs1 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.LBU rd rs1 off)) =
      some ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (o_pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 1 = true
            then some ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SB {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.SB rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 1 = true) :
    OpenRuns s 1 1
      ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SB rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SB rs1 rs2 off)) =
      some ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (o_pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 1 = true
            then some ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_BEQ_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
    (heq : s.getReg rs1 = s.getReg rs2) (htgt : o_pcAt idx + signExtend13 off = o_pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (o_pcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BEQ rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : (s.getReg rs1 == s.getReg rs2) = true := by rw [heq]; simp
  have hst : ordinaryStep s (.base (.BEQ rs1 rs2 off)) = some (s.setPC (o_pcAt tgt)) := by
    change some (if (s.getReg rs1 == s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem o_step_BEQ_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
    (hne : s.getReg rs1 ≠ s.getReg rs2) :
    OpenRuns s 1 1 (s.setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BEQ rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : ¬ ((s.getReg rs1 == s.getReg rs2) = true) := fun h => hne (eq_of_beq h)
  have hst : ordinaryStep s (.base (.BEQ rs1 rs2 off)) = some (s.setPC (o_pcAt (idx + 1))) := by
    change some (if (s.getReg rs1 == s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_BNE_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
    (hne : s.getReg rs1 ≠ s.getReg rs2) (htgt : o_pcAt idx + signExtend13 off = o_pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (o_pcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BNE rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : (s.getReg rs1 != s.getReg rs2) = true := by
    cases hb : (s.getReg rs1 == s.getReg rs2) with
    | true => exact absurd (eq_of_beq hb) hne
    | false => simp [bne, hb]
  have hst : ordinaryStep s (.base (.BNE rs1 rs2 off)) = some (s.setPC (o_pcAt tgt)) := by
    change some (if (s.getReg rs1 != s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem o_step_BNE_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
    (heq : s.getReg rs1 = s.getReg rs2) :
    OpenRuns s 1 1 (s.setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BNE rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : ¬ ((s.getReg rs1 != s.getReg rs2) = true) := by rw [heq]; simp
  have hst : ordinaryStep s (.base (.BNE rs1 rs2 off)) = some (s.setPC (o_pcAt (idx + 1))) := by
    change some (if (s.getReg rs1 != s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_BLTU_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
    (hlt : (s.getReg rs1).toNat < (s.getReg rs2).toNat)
    (htgt : o_pcAt idx + signExtend13 off = o_pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (o_pcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BLTU rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : BitVec.ult (s.getReg rs1) (s.getReg rs2) = true := by
    simp only [BitVec.ult, decide_eq_true_eq]; exact hlt
  have hst : ordinaryStep s (.base (.BLTU rs1 rs2 off)) = some (s.setPC (o_pcAt tgt)) := by
    change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem o_step_BLTU_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
    (hle : (s.getReg rs2).toNat ≤ (s.getReg rs1).toNat) :
    OpenRuns s 1 1 (s.setPC (o_pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BLTU rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true) := by
    simp only [BitVec.ult, decide_eq_true_eq]; omega
  have hst : ordinaryStep s (.base (.BLTU rs1 rs2 off)) = some (s.setPC (o_pcAt (idx + 1))) := by
    change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, o_pcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_JAL {s : MachineState} {idx tgt : Nat} {rd : Reg} {off : BitVec 21}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx) (hi : openingInstr idx = .base (.JAL rd off))
    (htgt : o_pcAt idx + signExtend21 off = o_pcAt tgt) :
    OpenRuns s 1 1 ((s.setReg rd (o_pcAt (idx + 1))).setPC (o_pcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.JAL rd off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.JAL rd off)) =
      some ((s.setReg rd (o_pcAt (idx + 1))).setPC (o_pcAt tgt)) := by
    change some ((s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 off)) = _
    rw [hpc, o_pcAt_add4, htgt]
  exact OpenRuns.step hf hst

private theorem o_step_JALR_x0 {s : MachineState} {idx retIdx : Nat}
    (hidx : idx < 235) (hpc : s.pc = o_pcAt idx)
    (hi : openingInstr idx = .base (.JALR .x0 .x1 (0#12)))
    (hx1 : s.getReg .x1 = o_pcAt retIdx) :
    OpenRuns s 1 1 (s.setPC (o_pcAt retIdx)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.JALR .x0 .x1 (0#12))) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.JALR .x0 .x1 (0#12))) = some (s.setPC (o_pcAt retIdx)) := by
    change some ((s.setReg .x0 (s.pc + 4)).setPC ((s.getReg .x1 + signExtend12 (0#12)) &&& ~~~1#64)) = _
    rw [show s.setReg .x0 (s.pc + 4) = s from rfl, hx1, o_pcAt_jalr_return retIdx]
  exact OpenRuns.step hf hst

/-! ### 4. Memory Framing, Dword Writer, and 6-Bit Tail Packer Predicates -/

/-- Read-only region: trapdoor `[4294971424, 6375346208)` and indices `[6375346208, 6509563936)`. -/
def OpenReadOnlyPreserved (s0 s : MachineState) : Prop :=
  ∀ addr : Word, 4294971424 ≤ addr.toNat → addr.toNat < 6509563936 →
    s.getMem addr = s0.getMem addr

/-- Exact byte contents of the proof output prefix `[10804531232, 10804531232 + bytes.length)`. -/
def OpenProofPrefix (s : MachineState) (bytes : List Byte) : Prop :=
  ∀ j (hj : j < bytes.length),
    s.getByte (BitVec.ofNat 64 (10804531232 + j)) = bytes[j]

/-- Exact byte contents of the tail scratch prefix `[tailBufBase, tailBufBase + tailBytes.length)`. -/
def OpenTailBufPrefix (s : MachineState) (tailBytes : List Byte) : Prop :=
  ∀ j (hj : j < tailBytes.length),
    s.getByte (BitVec.ofNat 64 (tailBufBase + j)) = tailBytes[j]

/-- Exact state of the branchless 64-bit aligned dword-buffered writer for forward proof bytes. -/
private structure OpenWriterState (s : MachineState) (fwdBytes : List Byte) : Prop where
  rx25 : s.getReg .x25 = BitVec.ofNat 64 (10804531232 + 8 * (fwdBytes.length / 8))
  rx13 : s.getReg .x13 = BitVec.ofNat 64 (8 * (fwdBytes.length % 8))
  rx14 : s.getReg .x14 = BitVec.ofNat 64 (63 - 8 * (fwdBytes.length % 8))
  wbufLo : ∀ j (hj : j < fwdBytes.length % 8),
    (s.getReg .x12).extractLsb' (8 * j) 8 =
      fwdBytes[8 * (fwdBytes.length / 8) + j]'(by omega)
  wbufHi : ∀ j, fwdBytes.length % 8 ≤ j → j < 8 →
    (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8
  memDwords : ∀ j (hj : j < 8 * (fwdBytes.length / 8)),
    s.getByte (BitVec.ofNat 64 (10804531232 + j)) = fwdBytes[j]'(by omega)

/-- Exact state of the streaming 6-bit tail packer for emitted 6-bit tails. -/
private structure OpenTailState (s : MachineState) (tails : List (BitVec 6)) : Prop where
  rx31 : s.getReg .x31 = BitVec.ofNat 64 tailBufBase
  rx15 : s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (tails.foldl pack6Step ([], 0, 0)).1.length)
  rx16 : s.getReg .x16 = BitVec.ofNat 64 (tails.foldl pack6Step ([], 0, 0)).2.1
  rx17 : s.getReg .x17 = BitVec.ofNat 64 (tails.foldl pack6Step ([], 0, 0)).2.2
  memTail : OpenTailBufPrefix s (tails.foldl pack6Step ([], 0, 0)).1

private theorem OpenWriterState.of_eq {s1 s2 : MachineState} {fwdBytes : List Byte}
    (hw : OpenWriterState s1 fwdBytes)
    (h25 : s2.getReg .x25 = s1.getReg .x25 := by rfl)
    (h13 : s2.getReg .x13 = s1.getReg .x13 := by rfl)
    (h14 : s2.getReg .x14 = s1.getReg .x14 := by rfl)
    (h12 : s2.getReg .x12 = s1.getReg .x12 := by rfl)
    (hmem : ∀ a, s2.getByte a = s1.getByte a := by intro _; rfl) :
    OpenWriterState s2 fwdBytes :=
  ⟨h25.trans hw.rx25, h13.trans hw.rx13, h14.trans hw.rx14,
   fun j hj => by rw [h12]; exact hw.wbufLo j hj,
   fun j h1 h2 => by rw [h12]; exact hw.wbufHi j h1 h2,
   fun j hj => by rw [hmem]; exact hw.memDwords j hj⟩

private theorem OpenWriterState.castList {s : MachineState} {a b : List Byte}
    (h : a = b) (hw : OpenWriterState s a) : OpenWriterState s b :=
  h ▸ hw

private theorem OpenTailState.of_eq {s1 s2 : MachineState} {tails : List (BitVec 6)}
    (ht : OpenTailState s1 tails)
    (h31 : s2.getReg .x31 = s1.getReg .x31 := by rfl)
    (h15 : s2.getReg .x15 = s1.getReg .x15 := by rfl)
    (h16 : s2.getReg .x16 = s1.getReg .x16 := by rfl)
    (h17 : s2.getReg .x17 = s1.getReg .x17 := by rfl)
    (hmem : ∀ a, s2.getByte a = s1.getByte a := by intro _; rfl) :
    OpenTailState s2 tails :=
  ⟨h31.trans ht.rx31, h15.trans ht.rx15, h16.trans ht.rx16, h17.trans ht.rx17,
   fun j hj => by rw [hmem]; exact ht.memTail j hj⟩

private theorem o_readOnly_getMem_index {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (ordinal : Nat) (hord : ordinal < positions.card) :
    s.getMem (BitVec.ofNat 64 (6375346208 + 8 * ordinal)) =
      BitVec.ofNat 64 (openingIndex positions ordinal) := by
  have hcard := o_positions_card_le positions
  have haddr : (BitVec.ofNat 64 (6375346208 + 8 * ordinal)).toNat = 6375346208 + 8 * ordinal := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (by omega) (by omega)]
  exact opening_initial_index trapdoor positions ordinal hord

private theorem o_readOnly_getByte_trapdoor {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (off : Nat) (hoff : off < 2080374784) :
    s.getByte (BitVec.ofNat 64 (4294971424 + off)) = trapdoor.extractLsb' (8 * off) 8 := by
  set a := 4294971424 + off
  have hdec : alignToDword (BitVec.ofNat 64 a) = BitVec.ofNat 64 (8 * (a / 8)) := by
    have h := alignToDword_ofNat_eq (8 * (a / 8)) (a % 8) (by omega) (by omega)
    simpa only [show 8 * (a / 8) + a % 8 = a by omega] using h
  have hmem : s.getMem (alignToDword (BitVec.ofNat 64 a)) =
      (submission.initialState .opening (trapdoor, positions)).getMem
        (alignToDword (BitVec.ofNat 64 a)) := by
    rw [hdec]
    apply hro
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  change extractByte (s.getMem (alignToDword (BitVec.ofNat 64 a))) (byteOffset (BitVec.ofNat 64 a)) = _
  rw [hmem]
  exact opening_initial_trapdoor_byte trapdoor positions off hoff

private theorem o_readOnly_getMem_trapdoor_byte {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (off j : Nat) (hal : off % 8 = 0) (hj : j < 8) (hbd : off + 8 ≤ 2080374784) :
    (s.getMem (BitVec.ofNat 64 (4294971424 + off))).extractLsb' (8 * j) 8 =
      trapdoor.extractLsb' (8 * (off + j)) 8 := by
  rw [o_getMem_extractByte (by omega) hj, Nat.add_assoc]
  exact o_readOnly_getByte_trapdoor hro (off + j) (by omega)

private theorem o_readOnly_setMem_proof {s0 s : MachineState} (dst : Nat) (val : Word)
    (hro : OpenReadOnlyPreserved s0 s) (hlo : 10804531232 ≤ dst) (hhi : dst + 8 ≤ 19285417728) :
    OpenReadOnlyPreserved s0 (s.setMem (BitVec.ofNat 64 dst) val) := by
  intro addr h1 h2
  have hne : addr ≠ BitVec.ofNat 64 dst := by
    intro heq
    have hn := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
    omega
  rw [MachineState.getMem_setMem_ne hne]
  exact hro addr h1 h2

private theorem o_readOnly_setByte_cap {s0 s : MachineState} (dst : Nat) (b : BitVec 8)
    (hro : OpenReadOnlyPreserved s0 s) (hlo : 4096 ≤ dst) (hhi : dst < 4608) :
    OpenReadOnlyPreserved s0 (s.setByte (BitVec.ofNat 64 dst) b) := by
  intro addr h1 h2
  have hdec : alignToDword (BitVec.ofNat 64 dst) = BitVec.ofNat 64 (8 * (dst / 8)) := by
    have h := alignToDword_ofNat_eq (8 * (dst / 8)) (dst % 8) (by omega) (by omega)
    simpa only [show 8 * (dst / 8) + dst % 8 = dst by omega] using h
  have hne : addr ≠ alignToDword (BitVec.ofNat 64 dst) := by
    intro heq; rw [hdec] at heq
    have hn := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
    omega
  simp only [MachineState.setByte, MachineState.getMem_setMem_ne hne]
  exact hro addr h1 h2

private theorem o_readOnly_setByte_tail {s0 s : MachineState} (dst : Nat) (b : BitVec 8)
    (hro : OpenReadOnlyPreserved s0 s) (hlo : tailBufBase ≤ dst) (hhi : dst < 68719476736) :
    OpenReadOnlyPreserved s0 (s.setByte (BitVec.ofNat 64 dst) b) := by
  intro addr h1 h2
  have htb : tailBufBase = 20000000000 := rfl
  have hdec : alignToDword (BitVec.ofNat 64 dst) = BitVec.ofNat 64 (8 * (dst / 8)) := by
    have h := alignToDword_ofNat_eq (8 * (dst / 8)) (dst % 8) (by omega) (by omega)
    simpa only [show 8 * (dst / 8) + dst % 8 = dst by omega] using h
  have hne : addr ≠ alignToDword (BitVec.ofNat 64 dst) := by
    intro heq; rw [hdec] at heq
    have hn := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
    omega
  simp only [MachineState.setByte, MachineState.getMem_setMem_ne hne]
  exact hro addr h1 h2

private theorem o_writerState_setByte_outside {s : MachineState} {fwdBytes : List Byte} (dst : Nat)
    (b : BitVec 8) (hw : OpenWriterState s fwdBytes) (hbd : fwdBytes.length ≤ proofCap)
    (hout : dst < 10804531232 ∨ 19285417728 ≤ dst) (hdst : dst < 2 ^ 64) :
    OpenWriterState (s.setByte (BitVec.ofNat 64 dst) b) fwdBytes := by
  have hpc : proofCap = 8480886496 := rfl
  exact ⟨by rw [o_getReg_setByte]; exact hw.rx25,
   by rw [o_getReg_setByte]; exact hw.rx13,
   by rw [o_getReg_setByte]; exact hw.rx14,
   fun j hj => by rw [o_getReg_setByte]; exact hw.wbufLo j hj,
   fun j h1 h2 => by rw [o_getReg_setByte]; exact hw.wbufHi j h1 h2,
   fun j hj => by
     rw [set_byte_read, if_neg (o_bv64_ofNat_ne (by omega) hdst (by omega))]
     exact hw.memDwords j hj⟩

private theorem o_tailState_setByte_outside {s : MachineState} {tails : List (BitVec 6)} (dst : Nat)
    (b : BitVec 8) (ht : OpenTailState s tails) (htbd : tails.length ≤ 200000000)
    (hout : dst < tailBufBase) :
    OpenTailState (s.setByte (BitVec.ofNat 64 dst) b) tails := by
  have htb : tailBufBase = 20000000000 := rfl
  have hlen := (o_pack6_foldl_bounds tails).2.2
  exact ⟨by rw [o_getReg_setByte]; exact ht.rx31,
   by rw [o_getReg_setByte]; exact ht.rx15,
   by rw [o_getReg_setByte]; exact ht.rx16,
   by rw [o_getReg_setByte]; exact ht.rx17,
   fun j hj => by
     rw [set_byte_read, if_neg (o_bv64_ofNat_ne (by omega) (by omega) (by omega))]
     exact ht.memTail j hj⟩

private theorem o_tailState_of_mem_eq {s1 s2 : MachineState} {tails : List (BitVec 6)}
    (ht : OpenTailState s1 tails) (htbd : tails.length ≤ 200000000)
    (hreg : ∀ r, r = .x15 ∨ r = .x16 ∨ r = .x17 ∨ r = .x31 → s2.getReg r = s1.getReg r)
    (hmem : ∀ q, tailBufBase ≤ q → q < 68719476736 →
      s2.getByte (BitVec.ofNat 64 q) = s1.getByte (BitVec.ofNat 64 q)) :
    OpenTailState s2 tails :=
  ⟨by rw [hreg .x31 (by simp)]; exact ht.rx31,
   by rw [hreg .x15 (by simp)]; exact ht.rx15,
   by rw [hreg .x16 (by simp)]; exact ht.rx16,
   by rw [hreg .x17 (by simp)]; exact ht.rx17,
   fun j hj => by
     have htb : tailBufBase = 20000000000 := rfl
     have hlen := (o_pack6_foldl_bounds tails).2.2
     rw [hmem (tailBufBase + j) (by omega) (by omega)]
     exact ht.memTail j hj⟩

private theorem o_chunk_tdSalt (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index)
    (j : Nat) (hj : j < 24) :
    trapdoor.extractLsb' (8 * (saltOff i + j)) 8 =
      (bitsToBytes (tdSalt trapdoor i) 24)[j]'(by simp [bitsToBytes]; exact hj) := by
  simp only [bitsToBytes, List.getElem_map, List.getElem_range, tdSalt]
  rw [o_extractLsb'_extractLsb' trapdoor (8 * saltOff i) 192 (8 * j) 8 (by omega)]
  congr 1; omega

private theorem o_chunk_tdNode (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (l idx n j : Nat) (hn : n ≤ 32) (hj : j < n) :
    trapdoor.extractLsb' (8 * (32 * heapIdx l idx + j)) 8 =
      (bitsToBytes (tdNode trapdoor l idx) n)[j]'(by simp [bitsToBytes]; exact hj) := by
  simp only [bitsToBytes, List.getElem_map, List.getElem_range, tdNode]
  rw [o_extractLsb'_extractLsb' trapdoor (8 * (32 * heapIdx l idx)) 256 (8 * j) 8 (by omega)]
  congr 1; omega

/-! ### 5. Branchless Dword Writer & Streaming 6-Bit Tail Subroutines (`110..234`) -/

private theorem o_emit_dword {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base srcOff qBase k : Nat} {imm : BitVec 12}
    {cur chunk8 : List Byte}
    (hbase : base + 5 < 235)
    (himm : signExtend12 imm = BitVec.ofNat 64 (8 * k))
    (hi0 : openingInstr base = .base (.LD .x5 .x10 imm))
    (hi1 : openingInstr (base + 1) = .base (.SLL .x6 .x5 .x13))
    (hi2 : openingInstr (base + 2) = .base (.OR .x12 .x12 .x6))
    (hi3 : openingInstr (base + 3) = .base (.SD .x25 .x12 imm))
    (hi4 : openingInstr (base + 4) = .base (.SRLI .x5 .x5 (1#6)))
    (hi5 : openingInstr (base + 5) = .base (.SRL .x12 .x5 .x14))
    (hpc : s.pc = o_pcAt base)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (10804531232 + 8 * qBase))
    (hqeq : cur.length / 8 = qBase + k)
    (hx13 : s.getReg .x13 = BitVec.ofNat 64 (8 * (cur.length % 8)))
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (63 - 8 * (cur.length % 8)))
    (hwLo : ∀ j (hj : j < cur.length % 8),
      (s.getReg .x12).extractLsb' (8 * j) 8 = cur[8 * (cur.length / 8) + j]'(by omega))
    (hwHi : ∀ j, cur.length % 8 ≤ j → j < 8 →
      (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8)
    (hmem : ∀ j (hj : j < 8 * (cur.length / 8)),
      s.getByte (BitVec.ofNat 64 (10804531232 + j)) = cur[j]'(by omega))
    (hsrc_al : srcOff % 8 = 0)
    (hsrc_bd : srcOff + 8 * k + 8 ≤ 2080374784)
    (hcur_bd : cur.length + 8 ≤ proofCap)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hclen : chunk8.length = 8)
    (hchunk : ∀ j (hj : j < 8),
      trapdoor.extractLsb' (8 * (srcOff + 8 * k + j)) 8 = chunk8[j]'(by omega)) :
    let cur' := cur ++ chunk8
    ∃ s', OpenRuns s 6 6 s' ∧
      s'.pc = o_pcAt (base + 6) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      (∀ j (hj : j < cur'.length % 8),
        (s'.getReg .x12).extractLsb' (8 * j) 8 = cur'[8 * (cur'.length / 8) + j]'(by omega)) ∧
      (∀ j, cur'.length % 8 ≤ j → j < 8 →
        (s'.getReg .x12).extractLsb' (8 * j) 8 = 0#8) ∧
      (∀ j (hj : j < 8 * (cur'.length / 8)),
        s'.getByte (BitVec.ofNat 64 (10804531232 + j)) = cur'[j]'(by omega)) ∧
      OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      (∀ q < 4608, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719476736 →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro cur'
  have hpc_eq : proofCap = 8480886496 := rfl
  set r := cur.length % 8
  set q := cur.length / 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  have hcur'_len : cur'.length = cur.length + 8 := by simp [cur', hclen]
  have hq' : cur'.length / 8 = q + 1 := by omega
  have hr' : cur'.length % 8 = r := by omega
  set v := s.getMem (BitVec.ofNat 64 (4294971424 + (srcOff + 8 * k)))
  have hv_byte : ∀ j (hj : j < 8), v.extractLsb' (8 * j) 8 = chunk8[j]'(by omega) := by
    intro j hj
    rw [o_readOnly_getMem_trapdoor_byte hro (srcOff + 8 * k) j (by omega) hj (by omega)]
    exact hchunk j hj
  have hsrcAddr : s.getReg .x10 + signExtend12 imm =
      BitVec.ofNat 64 (4294971424 + (srcOff + 8 * k)) := by
    rw [hx10, himm, o_bv64_ofNat_add, Nat.add_assoc]
  have h0 := o_step_LD (by omega) hpc hi0
    (by rw [hsrcAddr]; exact o_accessValid_ofNat _ 8 (by omega) (by omega))
  let s1 := (s.setReg .x5 v).setPC (o_pcAt (base + 1))
  have h0' : OpenRuns s 1 1 s1 := by simpa only [hsrcAddr, v, s1] using h0
  have h1 := o_step_SLL (by omega) (rfl : s1.pc = o_pcAt (base + 1)) hi1
  have hx13_mod : (s1.getReg .x13).toNat % 64 = 8 * r := by
    have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hx13
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s2 := (s1.setReg .x6 (v <<< (8 * r))).setPC (o_pcAt (base + 2))
  have h1' : OpenRuns s1 1 1 s2 := by
    simpa only [show s1.getReg .x5 = v from rfl, hx13_mod, s2, show base + 1 + 1 = base + 2 by omega] using h1
  set w := s.getReg .x12
  set wOut := w ||| (v <<< (8 * r))
  have h2 := o_step_OR (by omega) (rfl : s2.pc = o_pcAt (base + 2)) hi2
  let s3 := (s2.setReg .x12 wOut).setPC (o_pcAt (base + 3))
  have h2' : OpenRuns s2 1 1 s3 := by
    simpa only [show s2.getReg .x12 = w from rfl, show s2.getReg .x6 = v <<< (8 * r) from rfl,
      wOut, s3, show base + 2 + 1 = base + 3 by omega] using h2
  have hdstAddr : s3.getReg .x25 + signExtend12 imm = BitVec.ofNat 64 (10804531232 + 8 * q) := by
    have hr25 : s3.getReg .x25 = BitVec.ofNat 64 (10804531232 + 8 * qBase) := hx25
    rw [hr25, himm, o_bv64_ofNat_add]; congr 1; omega
  have h3 := o_step_SD (by omega) (rfl : s3.pc = o_pcAt (base + 3)) hi3
    (by rw [hdstAddr]; exact o_accessValid_ofNat _ 8 (by omega) (by omega))
  let s4 := (s3.setMem (BitVec.ofNat 64 (10804531232 + 8 * q)) wOut).setPC (o_pcAt (base + 4))
  have h3' : OpenRuns s3 1 1 s4 := by
    simpa only [hdstAddr, show s3.getReg .x12 = wOut from rfl, s4, show base + 3 + 1 = base + 4 by omega] using h3
  have h4 := o_step_SRLI (by omega) (rfl : s4.pc = o_pcAt (base + 4)) hi4
  let s5 := (s4.setReg .x5 (v >>> 1)).setPC (o_pcAt (base + 5))
  have h4' : OpenRuns s4 1 1 s5 := by
    have hr5 : s4.getReg .x5 = v := by simp only [s4, MachineState.getReg_setPC, o_getReg_setMem, s3, s2, s1]; rfl
    simpa only [hr5, show (1#6 : BitVec 6).toNat = 1 from rfl, s5, show base + 4 + 1 = base + 5 by omega] using h4
  set wNew := (v >>> 1) >>> (63 - 8 * r)
  have h5 := o_step_SRL (by omega) (rfl : s5.pc = o_pcAt (base + 5)) hi5
  have hx14_mod : (s5.getReg .x14).toNat % 64 = 63 - 8 * r := by
    have h : s5.getReg .x14 = BitVec.ofNat 64 (63 - 8 * r) := by
      simp only [s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setMem,
        o_getReg_setReg_ne .x5 .x14 (by decide),
        o_getReg_setReg_ne .x12 .x14 (by decide),
        o_getReg_setReg_ne .x6 .x14 (by decide)]
      exact hx14
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 63 - 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s6 := (s5.setReg .x12 wNew).setPC (o_pcAt (base + 6))
  have h5' : OpenRuns s5 1 1 s6 := by
    simpa only [show s5.getReg .x5 = v >>> 1 from rfl, hx14_mod, wNew, s6,
      show base + 5 + 1 = base + 6 by omega] using h5
  have hmem6 : ∀ a, s6.getByte a =
      (s.setMem (BitVec.ofNat 64 (10804531232 + 8 * q)) wOut).getByte a := fun a => by
    simp only [s6, s5, s4, s3, s2, s1, o_getByte_setPC, o_getByte_setReg]; rfl
  refine ⟨s6, ((((h0'.trans h1').trans h2').trans h3').trans h4').trans h5', rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro reg h5ne h6ne h12ne
    simp only [s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setMem,
      o_getReg_setReg_ne .x12 reg (Ne.symm h12ne),
      o_getReg_setReg_ne .x5 reg (Ne.symm h5ne),
      o_getReg_setReg_ne .x6 reg (Ne.symm h6ne)]
  · intro j hj
    have hjr : j < r := by omega
    have hbyte := o_word_ushr1_ushr_byte v r hr j (by omega)
    rw [if_pos hjr, hv_byte (8 - r + j) (by omega)] at hbyte
    change wNew.extractLsb' (8 * j) 8 = _
    rw [hbyte, o_list_getElem_append_right cur chunk8 (8 * (cur'.length / 8) + j) (by omega) (by rw [List.length_append, hclen]; omega)]
    congr 1; omega
  · intro j hj1 hj2
    have hbyte := o_word_ushr1_ushr_byte v r hr j hj2
    rw [if_neg (by omega)] at hbyte
    exact hbyte
  · intro j hj
    rw [hmem6]
    by_cases hlt : j < 8 * q
    · rw [setMem_getByte_ofNat s (10804531232 + 8 * q) (10804531232 + j) wOut
        (by omega) (by omega) (by omega) (by omega)]
      rw [hmem j hlt, o_list_getElem_append_left cur chunk8 j (by omega)]
    · have hu : j - 8 * q < 8 := by omega
      have hadd : 10804531232 + 8 * q + (j - 8 * q) = 10804531232 + j := by omega
      rw [← hadd, setMem_getByte_inside s (10804531232 + 8 * q) (j - 8 * q) wOut (by omega) hu]
      rw [o_word_or_shl_byte w v r hr hwHi (j - 8 * q) hu]
      by_cases hur : j - 8 * q < r
      · rw [if_pos hur, hwLo (j - 8 * q) hur, o_list_getElem_append_left cur chunk8 j (by omega)]
        congr 1; omega
      · rw [if_neg hur, hv_byte (j - 8 * q - r) (by omega),
          o_list_getElem_append_right cur chunk8 j (by omega) (by rw [List.length_append, hclen]; omega)]
        congr 1; omega
  · intro addr h1 h2
    change (s.setMem (BitVec.ofNat 64 (10804531232 + 8 * q)) wOut).getMem addr = _
    exact o_readOnly_setMem_proof (10804531232 + 8 * q) wOut hro (by omega) (by omega) addr h1 h2
  · intro a ha
    rw [hmem6, setMem_getByte_ofNat s (10804531232 + 8 * q) a wOut
      (by omega) (by omega) (by omega) (by omega)]
  · intro a ha1 ha2
    have htb : tailBufBase = 20000000000 := rfl
    rw [hmem6, setMem_getByte_ofNat s (10804531232 + 8 * q) a wOut
      (by omega) (by omega) (by omega) (by omega)]

private theorem o_emit_3dwords {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base srcOff : Nat}
    {fwdBytes chunk24 : List Byte}
    (hbase : base + 18 < 235)
    (hc0 : openingInstr base = .base (.LD .x5 .x10 (0#12)) ∧
      openingInstr (base + 1) = .base (.SLL .x6 .x5 .x13) ∧
      openingInstr (base + 2) = .base (.OR .x12 .x12 .x6) ∧
      openingInstr (base + 3) = .base (.SD .x25 .x12 (0#12)) ∧
      openingInstr (base + 4) = .base (.SRLI .x5 .x5 (1#6)) ∧
      openingInstr (base + 5) = .base (.SRL .x12 .x5 .x14))
    (hc1 : openingInstr (base + 6) = .base (.LD .x5 .x10 (8#12)) ∧
      openingInstr (base + 7) = .base (.SLL .x6 .x5 .x13) ∧
      openingInstr (base + 8) = .base (.OR .x12 .x12 .x6) ∧
      openingInstr (base + 9) = .base (.SD .x25 .x12 (8#12)) ∧
      openingInstr (base + 10) = .base (.SRLI .x5 .x5 (1#6)) ∧
      openingInstr (base + 11) = .base (.SRL .x12 .x5 .x14))
    (hc2 : openingInstr (base + 12) = .base (.LD .x5 .x10 (16#12)) ∧
      openingInstr (base + 13) = .base (.SLL .x6 .x5 .x13) ∧
      openingInstr (base + 14) = .base (.OR .x12 .x12 .x6) ∧
      openingInstr (base + 15) = .base (.SD .x25 .x12 (16#12)) ∧
      openingInstr (base + 16) = .base (.SRLI .x5 .x5 (1#6)) ∧
      openingInstr (base + 17) = .base (.SRL .x12 .x5 .x14))
    (hadv : openingInstr (base + 18) = .base (.ADDI .x25 .x25 (24#12)))
    (hpc : s.pc = o_pcAt base)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0)
    (hsrc_bd : srcOff + 24 ≤ 2080374784)
    (hbd : fwdBytes.length + 24 ≤ proofCap)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : OpenWriterState s fwdBytes)
    (hclen : chunk24.length = 24)
    (hchunk : ∀ j (hj : j < 24),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk24[j]'(by omega)) :
    ∃ s', OpenRuns s 19 19 s' ∧
      s'.pc = o_pcAt (base + 19) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      OpenWriterState s' (fwdBytes ++ chunk24) ∧
      (∀ q < 4608, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719476736 →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  let c0 := chunk24.take 8
  let c1 := (chunk24.drop 8).take 8
  let c2 := chunk24.drop 16
  have hc0_len : c0.length = 8 := by simp [c0, hclen]
  have hc1_len : c1.length = 8 := by simp [c1, hclen]
  have hc2_len : c2.length = 8 := by simp [c2, hclen]
  have hsplit : c0 ++ c1 ++ c2 = chunk24 := by
    have h1 : c0 ++ chunk24.drop 8 = chunk24 := List.take_append_drop 8 chunk24
    have h2 : c1 ++ c2 = chunk24.drop 8 := by
      simpa [c1, c2, List.drop_drop] using List.take_append_drop 8 (chunk24.drop 8)
    rw [List.append_assoc, h2, h1]
  have hcur_eq : ((fwdBytes ++ c0) ++ c1) ++ c2 = fwdBytes ++ chunk24 := by
    rw [List.append_assoc, List.append_assoc, ← List.append_assoc c0 c1 c2, hsplit]
  set qBase := fwdBytes.length / 8
  obtain ⟨s1, hr1, hpc1, hreg1, hwLo1, hwHi1, hmem1, hro1, hcap1, htail1⟩ :=
    o_emit_dword (base := base) (srcOff := srcOff) (qBase := qBase) (k := 0) (imm := 0#12)
      (cur := fwdBytes) (chunk8 := c0) (by omega) (by decide)
      hc0.1 hc0.2.1 hc0.2.2.1 hc0.2.2.2.1 hc0.2.2.2.2.1 hc0.2.2.2.2.2
      hpc hx10 hw.rx25 (by omega) hw.rx13 hw.rx14 hw.wbufLo hw.wbufHi hw.memDwords
      hsrc_al (by omega) (by omega) hro hc0_len (fun j hj => by
        simpa [c0, List.getElem_take] using hchunk j (by omega))
  have hlen1 : (fwdBytes ++ c0).length = fwdBytes.length + 8 := by simp [hc0_len]
  obtain ⟨s2, hr2, hpc2, hreg2, hwLo2, hwHi2, hmem2, hro2, hcap2, htail2⟩ :=
    o_emit_dword (base := base + 6) (srcOff := srcOff) (qBase := qBase) (k := 1) (imm := 8#12)
      (cur := fwdBytes ++ c0) (chunk8 := c1) (by omega) (by decide)
      hc1.1 hc1.2.1 hc1.2.2.1 hc1.2.2.2.1 hc1.2.2.2.2.1 hc1.2.2.2.2.2
      hpc1 (by rw [hreg1 .x10 (by decide) (by decide) (by decide)]; exact hx10)
      (by rw [hreg1 .x25 (by decide) (by decide) (by decide)]; exact hw.rx25)
      (by omega)
      (by rw [hreg1 .x13 (by decide) (by decide) (by decide), hw.rx13]; congr 1; omega)
      (by rw [hreg1 .x14 (by decide) (by decide) (by decide), hw.rx14]; congr 1; omega)
      hwLo1 hwHi1 hmem1 hsrc_al (by omega) (by omega) hro1 hc1_len (fun j hj => by
        simpa [c1, List.getElem_take, List.getElem_drop, Nat.add_assoc] using hchunk (8 + j) (by omega))
  have hlen2 : ((fwdBytes ++ c0) ++ c1).length = fwdBytes.length + 16 := by
    simp only [List.length_append, hc0_len, hc1_len]
  obtain ⟨s3, hr3, hpc3, hreg3, hwLo3, hwHi3, hmem3, hro3, hcap3, htail3⟩ :=
    o_emit_dword (base := base + 12) (srcOff := srcOff) (qBase := qBase) (k := 2) (imm := 16#12)
      (cur := (fwdBytes ++ c0) ++ c1) (chunk8 := c2) (by omega) (by decide)
      hc2.1 hc2.2.1 hc2.2.2.1 hc2.2.2.2.1 hc2.2.2.2.2.1 hc2.2.2.2.2.2
      hpc2 (by rw [hreg2 .x10 (by decide) (by decide) (by decide), hreg1 .x10 (by decide) (by decide) (by decide)]; exact hx10)
      (by rw [hreg2 .x25 (by decide) (by decide) (by decide), hreg1 .x25 (by decide) (by decide) (by decide)]; exact hw.rx25)
      (by omega)
      (by rw [hreg2 .x13 (by decide) (by decide) (by decide), hreg1 .x13 (by decide) (by decide) (by decide), hw.rx13]; congr 1; omega)
      (by rw [hreg2 .x14 (by decide) (by decide) (by decide), hreg1 .x14 (by decide) (by decide) (by decide), hw.rx14]; congr 1; omega)
      hwLo2 hwHi2 hmem2 hsrc_al (by omega) (by omega) hro2 hc2_len (fun j hj => by
        simpa [c2, List.getElem_drop, Nat.add_assoc] using hchunk (16 + j) (by omega))
  have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
  have hadvStep := o_step_ADDI (by omega) (by simpa only [show base + 12 + 6 = base + 18 by omega] using hpc3) hadv
  have hx25_3 : s3.getReg .x25 = BitVec.ofNat 64 (10804531232 + 8 * qBase) := by
    rw [hreg3 .x25 (by decide) (by decide) (by decide),
      hreg2 .x25 (by decide) (by decide) (by decide),
      hreg1 .x25 (by decide) (by decide) (by decide)]
    exact hw.rx25
  have hnew25 : s3.getReg .x25 + signExtend12 (24#12) =
      BitVec.ofNat 64 (10804531232 + 8 * ((fwdBytes ++ chunk24).length / 8)) := by
    rw [hx25_3, hse24, o_bv64_ofNat_add]; congr 1
    simp only [List.length_append, hclen]; omega
  let s4 := (s3.setReg .x25 (BitVec.ofNat 64 (10804531232 + 8 * ((fwdBytes ++ chunk24).length / 8)))).setPC
    (o_pcAt (base + 19))
  have hadv' : OpenRuns s3 1 1 s4 := by
    simpa only [hnew25, s4, show base + 18 + 1 = base + 19 by omega] using hadvStep
  have hpres3 : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → s3.getReg r = s.getReg r := fun r h5 h6 h12 => by
    rw [hreg3 r h5 h6 h12, hreg2 r h5 h6 h12, hreg1 r h5 h6 h12]
  refine ⟨s4, ((hr1.trans hr2).trans hr3).trans hadv', rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h5 h6 h12 h25
    simp only [s4, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 r (Ne.symm h25)]
    exact hpres3 r h5 h6 h12
  · intro a h1 h2
    simp only [s4, MachineState.getMem_setPC, MachineState.getMem_setReg]
    exact hro3 a h1 h2
  · refine OpenWriterState.castList hcur_eq ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcur_eq]; rfl
    · simp only [s4, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x13 (by decide)]
      rw [hpres3 .x13 (by decide) (by decide) (by decide), hw.rx13, hcur_eq]; congr 1
      simp only [List.length_append, hclen]; omega
    · simp only [s4, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x14 (by decide)]
      rw [hpres3 .x14 (by decide) (by decide) (by decide), hw.rx14, hcur_eq]; congr 1
      simp only [List.length_append, hclen]; omega
    · intro j hj
      simp only [s4, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x12 (by decide)]
      exact hwLo3 j hj
    · intro j h1 h2
      simp only [s4, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x12 (by decide)]
      exact hwHi3 j h1 h2
    · intro j hj
      simp only [s4, o_getByte_setPC, o_getByte_setReg]
      exact hmem3 j hj
  · intro a ha
    simp only [s4, o_getByte_setPC, o_getByte_setReg]
    rw [hcap3 a ha, hcap2 a ha, hcap1 a ha]
  · intro a ha1 ha2
    simp only [s4, o_getByte_setPC, o_getByte_setReg]
    rw [htail3 a ha1 ha2, htail2 a ha1 ha2, htail1 a ha1 ha2]

/-- Partial tail flush of `m ∈ [1..7]` bytes into the dword writer with EXACT telescoping step count:
`steps = 6 + 5 * ((fwdBytes ++ chunkM).length / 8 - fwdBytes.length / 8)`. -/
private theorem o_emit_partial {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base m : Nat} {immBits : BitVec 12}
    {fwdBytes chunkM : List Byte}
    (hbase : base + 10 < 235) (hm1 : 1 ≤ m) (hm2 : m < 8)
    (himm : signExtend12 immBits = BitVec.ofNat 64 (8 * m))
    (hbr : o_pcAt (base + 4) + signExtend13 (24#13) = o_pcAt (base + 10))
    (hc : openingInstr base = .base (.SLL .x6 .x5 .x13) ∧
      openingInstr (base + 1) = .base (.OR .x12 .x12 .x6) ∧
      openingInstr (base + 2) = .base (.ADDI .x13 .x13 immBits) ∧
      openingInstr (base + 3) = .base (.ADDI .x7 .x0 (64#12)) ∧
      openingInstr (base + 4) = .base (.BLTU .x13 .x7 (24#13)) ∧
      openingInstr (base + 5) = .base (.SD .x25 .x12 (0#12)) ∧
      openingInstr (base + 6) = .base (.ADDI .x25 .x25 (8#12)) ∧
      openingInstr (base + 7) = .base (.SRLI .x5 .x5 (1#6)) ∧
      openingInstr (base + 8) = .base (.SRL .x12 .x5 .x14) ∧
      openingInstr (base + 9) = .base (.ADDI .x13 .x13 (4032#12)) ∧
      openingInstr (base + 10) = .base (.XORI .x14 .x13 (63#12)))
    (hpc : s.pc = o_pcAt base)
    (hbd : fwdBytes.length + m ≤ proofCap)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : OpenWriterState s fwdBytes)
    (hclen : chunkM.length = m)
    (hx5 : ∀ j (hj : j < 8),
      (s.getReg .x5).extractLsb' (8 * j) 8 =
        if hj' : j < m then chunkM[j]'(by omega) else 0#8) :
    let steps := 6 + 5 * ((fwdBytes ++ chunkM).length / 8 - fwdBytes.length / 8)
    ∃ s', OpenRuns s steps steps s' ∧
      s'.pc = o_pcAt (base + 11) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x25 →
        s'.getReg r = s.getReg r) ∧
      OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      OpenWriterState s' (fwdBytes ++ chunkM) ∧
      (∀ q < 4608, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719476736 →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro steps
  have hpc_eq : proofCap = 8480886496 := rfl
  set r := fwdBytes.length % 8
  set q := fwdBytes.length / 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  set v := s.getReg .x5
  set w := s.getReg .x12
  set wOut := w ||| (v <<< (8 * r))
  have h0 := o_step_SLL (by omega) hpc hc.1
  have hx13_mod : (s.getReg .x13).toNat % 64 = 8 * r := by
    rw [hw.rx13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s1 := (s.setReg .x6 (v <<< (8 * r))).setPC (o_pcAt (base + 1))
  have h0' : OpenRuns s 1 1 s1 := by simpa only [hx13_mod, v, s1] using h0
  have h1 := o_step_OR (by omega) (rfl : s1.pc = o_pcAt (base + 1)) hc.2.1
  let s2 := (s1.setReg .x12 wOut).setPC (o_pcAt (base + 2))
  have h1' : OpenRuns s1 1 1 s2 := by
    simpa only [show s1.getReg .x12 = w from rfl, show s1.getReg .x6 = v <<< (8 * r) from rfl,
      wOut, s2, show base + 1 + 1 = base + 2 by omega] using h1
  have h2 := o_step_ADDI (by omega) (rfl : s2.pc = o_pcAt (base + 2)) hc.2.2.1
  let s3 := (s2.setReg .x13 (BitVec.ofNat 64 (8 * (r + m)))).setPC (o_pcAt (base + 3))
  have h2' : OpenRuns s2 1 1 s3 := by
    have hr13 : s2.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13
    have hv : s2.getReg .x13 + signExtend12 immBits = BitVec.ofNat 64 (8 * (r + m)) := by
      rw [hr13, himm, o_bv64_ofNat_add]; congr 1; omega
    simpa only [hv, s3, show base + 2 + 1 = base + 3 by omega] using h2
  have h3 := o_step_ADDI (by omega) (rfl : s3.pc = o_pcAt (base + 3)) hc.2.2.2.1
  let s4 := (s3.setReg .x7 64#64).setPC (o_pcAt (base + 4))
  have h3' : OpenRuns s3 1 1 s4 := by
    have hv : s3.getReg .x0 + signExtend12 (64#12) = 64#64 := by
      change (0#64 : Word) + signExtend12 (64#12) = 64#64; decide
    simpa only [hv, s4, show base + 3 + 1 = base + 4 by omega] using h3
  have hpre : OpenRuns s 4 4 s4 := ((h0'.trans h1').trans h2').trans h3'
  have hx13_4 : (s4.getReg .x13).toNat = 8 * (r + m) := by
    change (BitVec.ofNat 64 (8 * (r + m))).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx7_4 : (s4.getReg .x7).toNat = 64 := by change (64#64 : Word).toNat = 64; decide
  have hlen_app : (fwdBytes ++ chunkM).length = fwdBytes.length + m := by simp [hclen]
  by_cases hlt : r + m < 8
  · have hq' : (fwdBytes ++ chunkM).length / 8 = q := by omega
    have hr' : (fwdBytes ++ chunkM).length % 8 = r + m := by omega
    have hsteps_eq : steps = 6 := by simp only [steps, hq']; omega
    have h4 := o_step_BLTU_taken (by omega) (rfl : s4.pc = o_pcAt (base + 4)) hc.2.2.2.2.1
      (by rw [hx13_4, hx7_4]; omega) hbr
    let s10 := s4.setPC (o_pcAt (base + 10))
    have h10 := o_step_XORI (by omega) (rfl : s10.pc = o_pcAt (base + 10)) hc.2.2.2.2.2.2.2.2.2.2
    let s11 := (s10.setReg .x14 (BitVec.ofNat 64 (63 - 8 * (r + m)))).setPC (o_pcAt (base + 11))
    have h10' : OpenRuns s10 1 1 s11 := by
      have hv : s10.getReg .x13 ^^^ signExtend12 (63#12) = BitVec.ofNat 64 (63 - 8 * (r + m)) := by
        change BitVec.ofNat 64 (8 * (r + m)) ^^^ signExtend12 (63#12) = _
        exact o_bv64_xor63_8mul (r + m) hlt
      simpa only [hv, s11, show base + 10 + 1 = base + 11 by omega] using h10
    rw [hsteps_eq]
    refine ⟨s11, (hpre.trans h4).trans h10', rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro reg _ h6 h7 h12 h13 h14 _
      simp only [s11, s10, s4, s3, s2, s1, MachineState.getReg_setPC,
        o_getReg_setReg_ne .x14 reg (Ne.symm h14),
        o_getReg_setReg_ne .x7 reg (Ne.symm h7),
        o_getReg_setReg_ne .x13 reg (Ne.symm h13),
        o_getReg_setReg_ne .x12 reg (Ne.symm h12),
        o_getReg_setReg_ne .x6 reg (Ne.symm h6)]
    · intro a h1 h2
      simp only [s11, s10, s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]
      exact hro a h1 h2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq']; exact hw.rx25
      · rw [hr']; rfl
      · rw [hr']; rfl
      · intro j hj
        change wOut.extractLsb' (8 * j) 8 = _
        rw [o_word_or_shl_byte w v r hr hw.wbufHi j (by omega)]
        by_cases hjr : j < r
        · rw [if_pos hjr, hw.wbufLo j hjr,
            o_list_getElem_append_left fwdBytes chunkM (8 * ((fwdBytes ++ chunkM).length / 8) + j) (by omega)]
          congr 1; omega
        · rw [if_neg hjr, hx5 (j - r) (by omega), dif_pos (by omega),
            o_list_getElem_append_right fwdBytes chunkM (8 * ((fwdBytes ++ chunkM).length / 8) + j) (by omega) (by omega)]
          congr 1; omega
      · intro j hj1 hj2
        change wOut.extractLsb' (8 * j) 8 = 0#8
        rw [o_word_or_shl_byte w v r hr hw.wbufHi j hj2, if_neg (by omega),
          hx5 (j - r) (by omega), dif_neg (by omega)]
      · intro j hj
        simp only [s11, s10, s4, s3, s2, s1, o_getByte_setPC, o_getByte_setReg]
        rw [hw.memDwords j (by omega), o_list_getElem_append_left fwdBytes chunkM j (by omega)]
    · intro a _; simp only [s11, s10, s4, s3, s2, s1, o_getByte_setPC, o_getByte_setReg]
    · intro a _ _; simp only [s11, s10, s4, s3, s2, s1, o_getByte_setPC, o_getByte_setReg]
  · have hge : 8 ≤ r + m := by omega
    have hq' : (fwdBytes ++ chunkM).length / 8 = q + 1 := by omega
    have hr' : (fwdBytes ++ chunkM).length % 8 = r + m - 8 := by omega
    have hsteps_eq : steps = 11 := by simp only [steps, hq']; omega
    have h4 := o_step_BLTU_not_taken (by omega) (rfl : s4.pc = o_pcAt (base + 4)) hc.2.2.2.2.1
      (by rw [hx13_4, hx7_4]; omega)
    let s5 := s4.setPC (o_pcAt (base + 5))
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hdstAddr : s5.getReg .x25 + signExtend12 (0#12) = BitVec.ofNat 64 (10804531232 + 8 * q) := by
      have hr25 : s5.getReg .x25 = BitVec.ofNat 64 (10804531232 + 8 * q) := hw.rx25
      rw [hr25, hse0, o_bv64_ofNat_add, Nat.add_zero]
    have h5 := o_step_SD (by omega) (rfl : s5.pc = o_pcAt (base + 5)) hc.2.2.2.2.2.1
      (by rw [hdstAddr]; exact o_accessValid_ofNat _ 8 (by omega) (by omega))
    let s6 := (s5.setMem (BitVec.ofNat 64 (10804531232 + 8 * q)) wOut).setPC (o_pcAt (base + 6))
    have h5' : OpenRuns s5 1 1 s6 := by
      simpa only [hdstAddr, show s5.getReg .x12 = wOut from rfl, s6, show base + 5 + 1 = base + 6 by omega] using h5
    have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
    have h6 := o_step_ADDI (by omega) (rfl : s6.pc = o_pcAt (base + 6)) hc.2.2.2.2.2.2.1
    let s7 := (s6.setReg .x25 (BitVec.ofNat 64 (10804531232 + 8 * (q + 1)))).setPC (o_pcAt (base + 7))
    have h6' : OpenRuns s6 1 1 s7 := by
      have hr25 : s6.getReg .x25 = BitVec.ofNat 64 (10804531232 + 8 * q) := by
        simp only [s6, MachineState.getReg_setPC, o_getReg_setMem]; exact hw.rx25
      have hv : s6.getReg .x25 + signExtend12 (8#12) = BitVec.ofNat 64 (10804531232 + 8 * (q + 1)) := by
        rw [hr25, hse8, o_bv64_ofNat_add]; congr 1
      simpa only [hv, s7, show base + 6 + 1 = base + 7 by omega] using h6
    have h7 := o_step_SRLI (by omega) (rfl : s7.pc = o_pcAt (base + 7)) hc.2.2.2.2.2.2.2.1
    let s8 := (s7.setReg .x5 (v >>> 1)).setPC (o_pcAt (base + 8))
    have h7' : OpenRuns s7 1 1 s8 := by
      have hr5 : s7.getReg .x5 = v := by
        simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setMem,
          o_getReg_setReg_ne .x25 .x5 (by decide),
          o_getReg_setReg_ne .x7 .x5 (by decide),
          o_getReg_setReg_ne .x13 .x5 (by decide),
          o_getReg_setReg_ne .x12 .x5 (by decide),
          o_getReg_setReg_ne .x6 .x5 (by decide)]
        rfl
      simpa only [hr5, show (1#6 : BitVec 6).toNat = 1 from rfl, s8, show base + 7 + 1 = base + 8 by omega] using h7
    set wNew := (v >>> 1) >>> (63 - 8 * r)
    have h8 := o_step_SRL (by omega) (rfl : s8.pc = o_pcAt (base + 8)) hc.2.2.2.2.2.2.2.2.1
    have hx14_mod : (s8.getReg .x14).toNat % 64 = 63 - 8 * r := by
      have h : s8.getReg .x14 = BitVec.ofNat 64 (63 - 8 * r) := by
        simp only [s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setMem,
          o_getReg_setReg_ne .x5 .x14 (by decide),
          o_getReg_setReg_ne .x25 .x14 (by decide),
          o_getReg_setReg_ne .x7 .x14 (by decide),
          o_getReg_setReg_ne .x13 .x14 (by decide),
          o_getReg_setReg_ne .x12 .x14 (by decide),
          o_getReg_setReg_ne .x6 .x14 (by decide)]
        exact hw.rx14
      rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 63 - 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    let s9 := (s8.setReg .x12 wNew).setPC (o_pcAt (base + 9))
    have h8' : OpenRuns s8 1 1 s9 := by
      simpa only [show s8.getReg .x5 = v >>> 1 from rfl, hx14_mod, wNew, s9,
        show base + 8 + 1 = base + 9 by omega] using h8
    have h9 := o_step_ADDI (by omega) (rfl : s9.pc = o_pcAt (base + 9)) hc.2.2.2.2.2.2.2.2.2.1
    let s10 := (s9.setReg .x13 (BitVec.ofNat 64 (8 * (r + m - 8)))).setPC (o_pcAt (base + 10))
    have h9' : OpenRuns s9 1 1 s10 := by
      have hr13 : s9.getReg .x13 = BitVec.ofNat 64 (8 * (r + m)) := by
        simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setMem,
          o_getReg_setReg_ne .x12 .x13 (by decide),
          o_getReg_setReg_ne .x5 .x13 (by decide),
          o_getReg_setReg_ne .x25 .x13 (by decide),
          o_getReg_setReg_ne .x7 .x13 (by decide)]
        rfl
      have hv : s9.getReg .x13 + signExtend12 (4032#12) = BitVec.ofNat 64 (8 * (r + m - 8)) := by
        rw [hr13, o_bv64_add_neg64 (8 * (r + m)) (by omega)]; congr 1; omega
      simpa only [hv, s10, show base + 9 + 1 = base + 10 by omega] using h9
    have h10 := o_step_XORI (by omega) (rfl : s10.pc = o_pcAt (base + 10)) hc.2.2.2.2.2.2.2.2.2.2
    let s11 := (s10.setReg .x14 (BitVec.ofNat 64 (63 - 8 * (r + m - 8)))).setPC (o_pcAt (base + 11))
    have h10' : OpenRuns s10 1 1 s11 := by
      have hv : s10.getReg .x13 ^^^ signExtend12 (63#12) = BitVec.ofNat 64 (63 - 8 * (r + m - 8)) := by
        change BitVec.ofNat 64 (8 * (r + m - 8)) ^^^ signExtend12 (63#12) = _
        exact o_bv64_xor63_8mul (r + m - 8) (by omega)
      simpa only [hv, s11, show base + 10 + 1 = base + 11 by omega] using h10
    have htail_steps := (((((h4.trans h5').trans h6').trans h7').trans h8').trans h9').trans h10'
    have hmem11 : ∀ a, s11.getByte a =
        (s.setMem (BitVec.ofNat 64 (10804531232 + 8 * q)) wOut).getByte a := fun a => by
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, o_getByte_setPC, o_getByte_setReg]; rfl
    rw [hsteps_eq]
    refine ⟨s11, hpre.trans htail_steps, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro reg h5ne h6ne h7ne h12ne h13ne h14ne h25ne
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setMem,
        o_getReg_setReg_ne .x14 reg (Ne.symm h14ne),
        o_getReg_setReg_ne .x13 reg (Ne.symm h13ne),
        o_getReg_setReg_ne .x12 reg (Ne.symm h12ne),
        o_getReg_setReg_ne .x5 reg (Ne.symm h5ne),
        o_getReg_setReg_ne .x25 reg (Ne.symm h25ne),
        o_getReg_setReg_ne .x7 reg (Ne.symm h7ne),
        o_getReg_setReg_ne .x6 reg (Ne.symm h6ne)]
    · intro a h1 h2
      change (s.setMem (BitVec.ofNat 64 (10804531232 + 8 * q)) wOut).getMem a = _
      exact o_readOnly_setMem_proof (10804531232 + 8 * q) wOut hro (by omega) (by omega) a h1 h2
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq']
        simp only [s11, s10, s9, s8, s7, MachineState.getReg_setPC,
          o_getReg_setReg_ne .x14 .x25 (by decide),
          o_getReg_setReg_ne .x13 .x25 (by decide),
          o_getReg_setReg_ne .x12 .x25 (by decide),
          o_getReg_setReg_ne .x5 .x25 (by decide)]
        rfl
      · rw [hr']
        simp only [s11, s10, MachineState.getReg_setPC, o_getReg_setReg_ne .x14 .x13 (by decide)]; rfl
      · rw [hr']; rfl
      · intro j hj
        have hjr : j < r := by omega
        change wNew.extractLsb' (8 * j) 8 = _
        rw [o_word_ushr1_ushr_byte v r hr j (by omega), if_pos hjr,
          hx5 (8 - r + j) (by omega), dif_pos (by omega),
          o_list_getElem_append_right fwdBytes chunkM (8 * ((fwdBytes ++ chunkM).length / 8) + j) (by omega) (by omega)]
        congr 1; omega
      · intro j hj1 hj2
        change wNew.extractLsb' (8 * j) 8 = 0#8
        rw [o_word_ushr1_ushr_byte v r hr j hj2]
        by_cases hjr : j < r
        · rw [if_pos hjr, hx5 (8 - r + j) (by omega), dif_neg (by omega)]
        · rw [if_neg hjr]
      · intro j hj
        rw [hmem11]
        by_cases hltq : j < 8 * q
        · rw [setMem_getByte_ofNat s (10804531232 + 8 * q) (10804531232 + j) wOut
            (by omega) (by omega) (by omega) (by omega)]
          rw [hw.memDwords j hltq, o_list_getElem_append_left fwdBytes chunkM j (by omega)]
        · have hu : j - 8 * q < 8 := by omega
          have hadd : 10804531232 + 8 * q + (j - 8 * q) = 10804531232 + j := by omega
          rw [← hadd, setMem_getByte_inside s (10804531232 + 8 * q) (j - 8 * q) wOut (by omega) hu]
          rw [o_word_or_shl_byte w v r hr hw.wbufHi (j - 8 * q) hu]
          by_cases hur : j - 8 * q < r
          · rw [if_pos hur, hw.wbufLo (j - 8 * q) hur, o_list_getElem_append_left fwdBytes chunkM j (by omega)]
            congr 1; omega
          · rw [if_neg hur, hx5 (j - 8 * q - r) (by omega), dif_pos (by omega),
              o_list_getElem_append_right fwdBytes chunkM j (by omega) (by omega)]
            congr 1; omega
    · intro a ha
      rw [hmem11, setMem_getByte_ofNat s (10804531232 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]
    · intro a ha1 ha2
      have htb : tailBufBase = 20000000000 := rfl
      rw [hmem11, setMem_getByte_ofNat s (10804531232 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]

/-- Push one 6-bit tail (`words 223..233`) with EXACT telescoping step count:
`steps = 7 + 4 * (((tails ++ [tail6 d]).foldl pack6Step ([], 0, 0)).1.length - (tails.foldl pack6Step ([], 0, 0)).1.length)`. -/
private theorem o_push_tail6 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {d : Digest}
    (hpc : s.pc = o_pcAt 223)
    (hx11 : (s.getReg .x11).extractLsb' (8 * 5) 8 = d.extractLsb' (8 * 29) 8)
    (hfbd : fwdBytes.length ≤ proofCap)
    (htbd : tails.length < 200000000)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : OpenWriterState s fwdBytes)
    (ht : OpenTailState s tails) :
    let steps := 7 + 4 * (((tails ++ [tail6 d]).foldl pack6Step ([], 0, 0)).1.length -
      (tails.foldl pack6Step ([], 0, 0)).1.length)
    ∃ s', OpenRuns s steps steps s' ∧
      s'.pc = o_pcAt 234 ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 →
        s'.getReg r = s.getReg r) ∧
      OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      OpenWriterState s' fwdBytes ∧
      OpenTailState s' (tails ++ [tail6 d]) ∧
      (∀ q < 4608, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro steps
  have htb : tailBufBase = 20000000000 := rfl
  set st := tails.foldl pack6Step ([], 0, 0)
  have hst_bd := o_pack6_foldl_bounds tails
  set acc := st.1
  set tBuf := st.2.1
  set tCnt := st.2.2
  have htCnt_lt : tCnt < 8 := hst_bd.1
  have htBuf_lt : tBuf < 2 ^ tCnt := hst_bd.2.1
  have hacc_len : 8 * acc.length + tCnt = 6 * tails.length := hst_bd.2.2
  have hpow : 2 ^ tCnt ≤ 128 := by
    have h1 : 2 ^ tCnt ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 7 = 128 := by decide
    omega
  set t := tail6 d
  have ht_lt : t.toNat < 64 := t.isLt
  have hfold_app : (tails ++ [t]).foldl pack6Step ([], 0, 0) = pack6Step (acc, tBuf, tCnt) t := by
    rw [List.foldl_append]; rfl
  have h0 := o_step_SRLI (by omega) hpc (rfl : openingInstr 223 = .base (.SRLI .x5 .x11 (40#6)))
  let s1 := (s.setReg .x5 (s.getReg .x11 >>> 40)).setPC (o_pcAt 224)
  have h0' : OpenRuns s 1 1 s1 := by
    simpa only [show (40#6 : BitVec 6).toNat = 40 from rfl, s1] using h0
  have h1 := o_step_ANDI (by omega) (rfl : s1.pc = o_pcAt 224)
    (rfl : openingInstr 224 = .base (.ANDI .x5 .x5 (63#12)))
  let s2 := (s1.setReg .x5 (BitVec.ofNat 64 t.toNat)).setPC (o_pcAt 225)
  have h1' : OpenRuns s1 1 1 s2 := by
    have hv := o_word_tail6_from_hi (s.getReg .x11) d hx11
    simpa only [show s1.getReg .x5 = s.getReg .x11 >>> 40 from rfl, hv, t, s2] using h1
  have h2 := o_step_SLL (by omega) (rfl : s2.pc = o_pcAt 225)
    (rfl : openingInstr 225 = .base (.SLL .x6 .x5 .x17))
  have hx17_mod : (s2.getReg .x17).toNat % 64 = tCnt := by
    have h : s2.getReg .x17 = BitVec.ofNat 64 tCnt := ht.rx17
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tCnt < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s3 := (s2.setReg .x6 (BitVec.ofNat 64 t.toNat <<< tCnt)).setPC (o_pcAt 226)
  have h2' : OpenRuns s2 1 1 s3 := by
    simpa only [show s2.getReg .x5 = BitVec.ofNat 64 t.toNat from rfl, hx17_mod, s3] using h2
  set buf' := tBuf + t.toNat * 2 ^ tCnt
  have hbuf'_lt : buf' < 8192 := by
    have hmul : t.toNat * 2 ^ tCnt ≤ 63 * 128 := Nat.mul_le_mul (by omega) hpow
    change tBuf + t.toNat * 2 ^ tCnt < 8192; omega
  have h3 := o_step_OR (by omega) (rfl : s3.pc = o_pcAt 226)
    (rfl : openingInstr 226 = .base (.OR .x16 .x16 .x6))
  let s4 := (s3.setReg .x16 (BitVec.ofNat 64 buf')).setPC (o_pcAt 227)
  have h3' : OpenRuns s3 1 1 s4 := by
    have hr16 : s3.getReg .x16 = BitVec.ofNat 64 tBuf := ht.rx16
    have hv : s3.getReg .x16 ||| s3.getReg .x6 = BitVec.ofNat 64 buf' := by
      rw [hr16]; exact o_tail_or_shl_eq_add tBuf tCnt t.toNat htCnt_lt htBuf_lt ht_lt
    simpa only [hv, s4] using h3
  have hse6 : signExtend12 (6#12) = BitVec.ofNat 64 6 := by decide
  have h4 := o_step_ADDI (by omega) (rfl : s4.pc = o_pcAt 227)
    (rfl : openingInstr 227 = .base (.ADDI .x17 .x17 (6#12)))
  let s5 := (s4.setReg .x17 (BitVec.ofNat 64 (tCnt + 6))).setPC (o_pcAt 228)
  have h4' : OpenRuns s4 1 1 s5 := by
    have hr17 : s4.getReg .x17 = BitVec.ofNat 64 tCnt := ht.rx17
    rw [hr17, hse6, o_bv64_ofNat_add] at h4; exact h4
  have h5 := o_step_ADDI (by omega) (rfl : s5.pc = o_pcAt 228)
    (rfl : openingInstr 228 = .base (.ADDI .x7 .x0 (8#12)))
  let s6 := (s5.setReg .x7 8#64).setPC (o_pcAt 229)
  have h5' : OpenRuns s5 1 1 s6 := by
    have hv : s5.getReg .x0 + signExtend12 (8#12) = 8#64 := by
      change (0#64 : Word) + signExtend12 (8#12) = 8#64; decide
    simpa only [hv, s6] using h5
  have hpre : OpenRuns s 6 6 s6 := ((((h0'.trans h1').trans h2').trans h3').trans h4').trans h5'
  have hx17_6 : (s6.getReg .x17).toNat = tCnt + 6 := by
    change (BitVec.ofNat 64 (tCnt + 6)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx7_6 : (s6.getReg .x7).toNat = 8 := by change (8#64 : Word).toNat = 8; decide
  by_cases hlt8 : tCnt + 6 < 8
  · have hpack : (tails ++ [t]).foldl pack6Step ([], 0, 0) = (acc, buf', tCnt + 6) := by
      rw [hfold_app]; unfold pack6Step; dsimp only; rw [if_neg (by omega)]
    have hsteps_eq : steps = 7 := by simp only [steps, t, hpack]; change 7 + 4 * (acc.length - acc.length) = 7; omega
    have h6 := o_step_BLTU_taken (by omega) (rfl : s6.pc = o_pcAt 229)
      (rfl : openingInstr 229 = .base (.BLTU .x17 .x7 (20#13)))
      (by rw [hx17_6, hx7_6]; exact hlt8)
      (by decide : o_pcAt 229 + signExtend13 (20#13) = o_pcAt 234)
    let s7 := s6.setPC (o_pcAt 234)
    rw [hsteps_eq]
    refine ⟨s7, hpre.trans h6, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro r h5ne h6ne h7ne _ h16ne h17ne
      simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC,
        o_getReg_setReg_ne .x7 r (Ne.symm h7ne),
        o_getReg_setReg_ne .x17 r (Ne.symm h17ne),
        o_getReg_setReg_ne .x16 r (Ne.symm h16ne),
        o_getReg_setReg_ne .x6 r (Ne.symm h6ne),
        o_getReg_setReg_ne .x5 r (Ne.symm h5ne)]
    · intro a h1 h2
      simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]
      exact hro a h1 h2
    · exact ⟨hw.rx25, hw.rx13, hw.rx14, hw.wbufLo, hw.wbufHi, hw.memDwords⟩
    · refine ⟨ht.rx31, ?_, ?_, ?_, ?_⟩
      · rw [hpack]; exact ht.rx15
      · rw [hpack]; rfl
      · rw [hpack]; rfl
      · rw [hpack]; exact ht.memTail
    · intro a _; rfl
  · have hge8 : 8 ≤ tCnt + 6 := by omega
    have hpack : (tails ++ [t]).foldl pack6Step ([], 0, 0) =
        (acc ++ [BitVec.ofNat 8 buf'], buf' / 256, tCnt + 6 - 8) := by
      rw [hfold_app]; unfold pack6Step; dsimp only; rw [if_pos hge8]
    have hsteps_eq : steps = 11 := by
      simp only [steps, t, hpack, List.length_append, List.length_singleton]
      change 7 + 4 * (acc.length + 1 - acc.length) = 11; omega
    have h6 := o_step_BLTU_not_taken (by omega) (rfl : s6.pc = o_pcAt 229)
      (rfl : openingInstr 229 = .base (.BLTU .x17 .x7 (20#13)))
      (by rw [hx17_6, hx7_6]; exact hge8)
    let s7 := s6.setPC (o_pcAt 230)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have haddr7 : s7.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + acc.length) := by
      have hr15 : s7.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := ht.rx15
      rw [hr15, hse0, o_bv64_ofNat_add, Nat.add_zero]
    have h7 := o_step_SB (by omega) (rfl : s7.pc = o_pcAt 230)
      (rfl : openingInstr 230 = .base (.SB .x15 .x16 (0#12)))
      (by rw [haddr7]; exact o_accessValid_ofNat _ 1 (by omega) (by omega))
    let s8 := (s7.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).setPC (o_pcAt 231)
    have h7' : OpenRuns s7 1 1 s8 := by
      have htr : (s7.getReg .x16).truncate 8 = BitVec.ofNat 8 buf' := by
        change (BitVec.ofNat 64 buf').truncate 8 = _
        exact o_bv64_ofNat_truncate8 buf' (by omega)
      simpa only [haddr7, htr, s8] using h7
    have h8 := o_step_ADDI (by omega) (rfl : s8.pc = o_pcAt 231)
      (rfl : openingInstr 231 = .base (.ADDI .x15 .x15 (1#12)))
    let s9 := (s8.setReg .x15 (BitVec.ofNat 64 (tailBufBase + (acc.length + 1)))).setPC (o_pcAt 232)
    have h8' : OpenRuns s8 1 1 s9 := by
      have hr15 : s8.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := by
        simp only [s8, MachineState.getReg_setPC, o_getReg_setByte]; exact ht.rx15
      have hv : s8.getReg .x15 + signExtend12 (1#12) = BitVec.ofNat 64 (tailBufBase + (acc.length + 1)) := by
        rw [hr15, hse1, o_bv64_ofNat_add, Nat.add_assoc]
      simpa only [hv, s9] using h8
    have h9 := o_step_SRLI (by omega) (rfl : s9.pc = o_pcAt 232)
      (rfl : openingInstr 232 = .base (.SRLI .x16 .x16 (8#6)))
    let s10 := (s9.setReg .x16 (BitVec.ofNat 64 (buf' / 256))).setPC (o_pcAt 233)
    have h9' : OpenRuns s9 1 1 s10 := by
      have hr16 : s9.getReg .x16 = BitVec.ofNat 64 buf' := by
        simp only [s9, s8, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x15 .x16 (by decide)]; rfl
      have hv : s9.getReg .x16 >>> (8#6 : BitVec 6).toNat = BitVec.ofNat 64 (buf' / 256) := by
        rw [hr16]; change BitVec.ofNat 64 buf' >>> 8 = _
        rw [o_bv64_ushr buf' 8 (by omega), Nat.shiftRight_eq_div_pow]
      simpa only [hv, s10] using h9
    have h10 := o_step_ADDI (by omega) (rfl : s10.pc = o_pcAt 233)
      (rfl : openingInstr 233 = .base (.ADDI .x17 .x17 (4088#12)))
    let s11 := (s10.setReg .x17 (BitVec.ofNat 64 (tCnt + 6 - 8))).setPC (o_pcAt 234)
    have h10' : OpenRuns s10 1 1 s11 := by
      have hr17 : s10.getReg .x17 = BitVec.ofNat 64 (tCnt + 6) := by
        simp only [s10, s9, s8, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x16 .x17 (by decide),
          o_getReg_setReg_ne .x15 .x17 (by decide)]; rfl
      have hv : s10.getReg .x17 + signExtend12 (4088#12) = BitVec.ofNat 64 (tCnt + 6 - 8) := by
        rw [hr17, o_bv64_add_neg8 (tCnt + 6) hge8]
      simpa only [hv, s11] using h10
    have hmem11 : ∀ a, s11.getByte a =
        (s.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).getByte a := fun a => by
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, o_getByte_setPC, o_getByte_setReg]; rfl
    rw [hsteps_eq]
    refine ⟨s11, hpre.trans ((((h6.trans h7').trans h8').trans h9').trans h10'), rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro r h5ne h6ne h7ne h15ne h16ne h17ne
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setByte,
        o_getReg_setReg_ne .x17 r (Ne.symm h17ne),
        o_getReg_setReg_ne .x16 r (Ne.symm h16ne),
        o_getReg_setReg_ne .x15 r (Ne.symm h15ne),
        o_getReg_setReg_ne .x7 r (Ne.symm h7ne),
        o_getReg_setReg_ne .x6 r (Ne.symm h6ne),
        o_getReg_setReg_ne .x5 r (Ne.symm h5ne)]
    · intro a h1 h2
      change (s.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).getMem a = _
      exact o_readOnly_setByte_tail (tailBufBase + acc.length) (BitVec.ofNat 8 buf') hro
        (by omega) (by omega) a h1 h2
    · have hw' := o_writerState_setByte_outside (tailBufBase + acc.length) (BitVec.ofNat 8 buf')
        hw hfbd (by omega) (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x17 .x25 (by decide), o_getReg_setReg_ne .x16 .x25 (by decide),
          o_getReg_setReg_ne .x15 .x25 (by decide), o_getReg_setReg_ne .x7 .x25 (by decide),
          o_getReg_setReg_ne .x6 .x25 (by decide), o_getReg_setReg_ne .x5 .x25 (by decide)]; exact hw.rx25
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x17 .x13 (by decide), o_getReg_setReg_ne .x16 .x13 (by decide),
          o_getReg_setReg_ne .x15 .x13 (by decide), o_getReg_setReg_ne .x7 .x13 (by decide),
          o_getReg_setReg_ne .x6 .x13 (by decide), o_getReg_setReg_ne .x5 .x13 (by decide)]; exact hw.rx13
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x17 .x14 (by decide), o_getReg_setReg_ne .x16 .x14 (by decide),
          o_getReg_setReg_ne .x15 .x14 (by decide), o_getReg_setReg_ne .x7 .x14 (by decide),
          o_getReg_setReg_ne .x6 .x14 (by decide), o_getReg_setReg_ne .x5 .x14 (by decide)]; exact hw.rx14
      · intro j hj
        have h12 : s11.getReg .x12 = s.getReg .x12 := by
          simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setByte,
            o_getReg_setReg_ne .x17 .x12 (by decide), o_getReg_setReg_ne .x16 .x12 (by decide),
            o_getReg_setReg_ne .x15 .x12 (by decide), o_getReg_setReg_ne .x7 .x12 (by decide),
            o_getReg_setReg_ne .x6 .x12 (by decide), o_getReg_setReg_ne .x5 .x12 (by decide)]
        rw [h12]; exact hw.wbufLo j hj
      · intro j h1 h2
        have h12 : s11.getReg .x12 = s.getReg .x12 := by
          simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setByte,
            o_getReg_setReg_ne .x17 .x12 (by decide), o_getReg_setReg_ne .x16 .x12 (by decide),
            o_getReg_setReg_ne .x15 .x12 (by decide), o_getReg_setReg_ne .x7 .x12 (by decide),
            o_getReg_setReg_ne .x6 .x12 (by decide), o_getReg_setReg_ne .x5 .x12 (by decide)]
        rw [h12]; exact hw.wbufHi j h1 h2
      · intro j hj; rw [hmem11]; exact hw'.memDwords j hj
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x17 .x31 (by decide), o_getReg_setReg_ne .x16 .x31 (by decide),
          o_getReg_setReg_ne .x15 .x31 (by decide), o_getReg_setReg_ne .x7 .x31 (by decide),
          o_getReg_setReg_ne .x6 .x31 (by decide), o_getReg_setReg_ne .x5 .x31 (by decide)]; exact ht.rx31
      · rw [hpack]; simp only [s11, s10, s9, MachineState.getReg_setPC,
          o_getReg_setReg_ne .x17 .x15 (by decide), o_getReg_setReg_ne .x16 .x15 (by decide),
          List.length_append, List.length_singleton]; rfl
      · rw [hpack]; simp only [s11, s10, MachineState.getReg_setPC, o_getReg_setReg_ne .x17 .x16 (by decide)]; rfl
      · rw [hpack]; rfl
      · rw [hpack]; intro j hj
        rw [hmem11, set_byte_read]
        have hjlen : j < acc.length + 1 := by simpa using hj
        by_cases hlast : j = acc.length
        · subst hlast
          rw [if_pos rfl, o_list_getElem_append_right acc [BitVec.ofNat 8 buf'] acc.length (by omega) hj]
          simp
        · rw [if_neg (o_bv64_ofNat_ne (by omega) (by omega) (by omega)),
            ht.memTail j (by omega), o_list_getElem_append_left acc [BitVec.ofNat 8 buf'] j (by omega)]
    · intro a ha
      rw [hmem11, set_byte_read, if_neg (o_bv64_ofNat_ne (by omega) (by omega) (by omega))]

/-- Call `emit24` (`110..129`): `21` steps = `6 + 5 * (q' - q)`. -/
private theorem o_call_emit24 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx srcOff : Nat} {jOff : BitVec 21}
    {fwdBytes chunk : List Byte} {tails : List (BitVec 6)}
    (hcall : callIdx < 235)
    (hi : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : o_pcAt callIdx + signExtend21 jOff = o_pcAt 110)
    (hpc : s.pc = o_pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 24 ≤ 2080374784)
    (hbd : fwdBytes.length + 24 ≤ proofCap) (htbd : tails.length ≤ 200000000)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : OpenWriterState s fwdBytes) (ht : OpenTailState s tails)
    (hclen : chunk.length = 24)
    (hchunk : ∀ j (hj : j < 24),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk[j]'(by omega)) :
    ∃ s', OpenRuns s 21 21 s' ∧
      s'.pc = o_pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      OpenWriterState s' (fwdBytes ++ chunk) ∧
      OpenTailState s' tails ∧
      (∀ q < 4608, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have hjal := o_step_JAL hcall hpc hi htgt
  let s1 := (s.setReg .x1 (o_pcAt (callIdx + 1))).setPC (o_pcAt 110)
  obtain ⟨s2, hr2, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    o_emit_3dwords (s := s1) (base := 110) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := chunk)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl hx10 hsrc_al hsrc_bd hbd hro hw.of_eq hclen hchunk
  have hret := o_step_JALR_x0 (by omega) hpc2 (rfl : openingInstr 129 = .base (.JALR .x0 .x1 (0#12)))
    (by rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl)
  refine ⟨s2.setPC (o_pcAt (callIdx + 1)), (hjal.trans hr2).trans hret, rfl, ?_, hro2, hw2.of_eq, ?_, hcap2⟩
  · intro r h1 h5 h6 h12 h25
    rw [MachineState.getReg_setPC, hreg2 r h5 h6 h12 h25]
    simp only [s1, MachineState.getReg_setPC, o_getReg_setReg_ne .x1 r (Ne.symm h1)]
  · exact o_tailState_of_mem_eq ht htbd
      (fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl
        · exact hreg2 .x15 (by decide) (by decide) (by decide) (by decide)
        · exact hreg2 .x16 (by decide) (by decide) (by decide) (by decide)
        · exact hreg2 .x17 (by decide) (by decide) (by decide) (by decide)
        · exact hreg2 .x31 (by decide) (by decide) (by decide) (by decide))
      htail2

/-- Call `emit32` (`130..155`): `27` steps = `7 + 5 * (q' - q)`. -/
private theorem o_call_emit32 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx srcOff : Nat} {jOff : BitVec 21}
    {fwdBytes chunk : List Byte} {tails : List (BitVec 6)}
    (hcall : callIdx < 235)
    (hi : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : o_pcAt callIdx + signExtend21 jOff = o_pcAt 130)
    (hpc : s.pc = o_pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 32 ≤ 2080374784)
    (hbd : fwdBytes.length + 32 ≤ proofCap) (htbd : tails.length ≤ 200000000)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : OpenWriterState s fwdBytes) (ht : OpenTailState s tails)
    (hclen : chunk.length = 32)
    (hchunk : ∀ j (hj : j < 32),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk[j]'(by omega)) :
    ∃ s', OpenRuns s 27 27 s' ∧
      s'.pc = o_pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      OpenWriterState s' (fwdBytes ++ chunk) ∧
      OpenTailState s' tails ∧
      (∀ q < 4608, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have hjal := o_step_JAL hcall hpc hi htgt
  let s1 := (s.setReg .x1 (o_pcAt (callIdx + 1))).setPC (o_pcAt 130)
  let c0 := chunk.take 8
  let c1 := (chunk.drop 8).take 8
  let c2 := (chunk.drop 16).take 8
  let c3 := chunk.drop 24
  have hc0_len : c0.length = 8 := by simp [c0, hclen]
  have hc1_len : c1.length = 8 := by simp [c1, hclen]
  have hc2_len : c2.length = 8 := by simp [c2, hclen]
  have hc3_len : c3.length = 8 := by simp [c3, hclen]
  have hsplit : c0 ++ c1 ++ c2 ++ c3 = chunk := by
    have h1 : c0 ++ chunk.drop 8 = chunk := List.take_append_drop 8 chunk
    have h2 : c1 ++ chunk.drop 16 = chunk.drop 8 := by
      simpa [c1, List.drop_drop] using List.take_append_drop 8 (chunk.drop 8)
    have h3 : c2 ++ c3 = chunk.drop 16 := by
      simpa [c2, c3, List.drop_drop] using List.take_append_drop 8 (chunk.drop 16)
    rw [List.append_assoc, List.append_assoc, h3, h2, h1]
  have hcur_eq : (((fwdBytes ++ c0) ++ c1) ++ c2) ++ c3 = fwdBytes ++ chunk := by
    rw [List.append_assoc, List.append_assoc, List.append_assoc,
      ← List.append_assoc c0 c1, ← List.append_assoc (c0 ++ c1) c2, hsplit]
  set qBase := fwdBytes.length / 8
  obtain ⟨s2, hr2, hpc2, hreg2, hwLo2, hwHi2, hmem2, hro2, hcap2, htail2⟩ :=
    o_emit_dword (s := s1) (base := 130) (srcOff := srcOff) (qBase := qBase) (k := 0) (imm := 0#12)
      (cur := fwdBytes) (chunk8 := c0) (by omega) (by decide) rfl rfl rfl rfl rfl rfl
      rfl hx10 hw.rx25 (by omega) hw.rx13 hw.rx14 hw.wbufLo hw.wbufHi hw.memDwords
      hsrc_al (by omega) (by omega) hro hc0_len (fun j hj => by simpa [c0, List.getElem_take] using hchunk j (by omega))
  have hlen1 : (fwdBytes ++ c0).length = fwdBytes.length + 8 := by simp [hc0_len]
  obtain ⟨s3, hr3, hpc3, hreg3, hwLo3, hwHi3, hmem3, hro3, hcap3, htail3⟩ :=
    o_emit_dword (base := 136) (srcOff := srcOff) (qBase := qBase) (k := 1) (imm := 8#12)
      (cur := fwdBytes ++ c0) (chunk8 := c1) (by omega) (by decide) rfl rfl rfl rfl rfl rfl
      hpc2 (by rw [hreg2 .x10 (by decide) (by decide) (by decide)]; exact hx10)
      (by rw [hreg2 .x25 (by decide) (by decide) (by decide)]; exact hw.rx25)
      (by omega)
      (by rw [hreg2 .x13 (by decide) (by decide) (by decide), show s1.getReg .x13 = _ from hw.rx13]; congr 1; omega)
      (by rw [hreg2 .x14 (by decide) (by decide) (by decide), show s1.getReg .x14 = _ from hw.rx14]; congr 1; omega)
      hwLo2 hwHi2 hmem2 hsrc_al (by omega) (by omega) hro2 hc1_len
      (fun j hj => by simpa [c1, List.getElem_take, List.getElem_drop, Nat.add_assoc] using hchunk (8 + j) (by omega))
  have hlen2 : ((fwdBytes ++ c0) ++ c1).length = fwdBytes.length + 16 := by simp [hc0_len, hc1_len]
  obtain ⟨s4, hr4, hpc4, hreg4, hwLo4, hwHi4, hmem4, hro4, hcap4, htail4⟩ :=
    o_emit_dword (base := 142) (srcOff := srcOff) (qBase := qBase) (k := 2) (imm := 16#12)
      (cur := (fwdBytes ++ c0) ++ c1) (chunk8 := c2) (by omega) (by decide) rfl rfl rfl rfl rfl rfl
      hpc3 (by rw [hreg3 .x10 (by decide) (by decide) (by decide), hreg2 .x10 (by decide) (by decide) (by decide)]; exact hx10)
      (by rw [hreg3 .x25 (by decide) (by decide) (by decide), hreg2 .x25 (by decide) (by decide) (by decide)]; exact hw.rx25)
      (by omega)
      (by rw [hreg3 .x13 (by decide) (by decide) (by decide), hreg2 .x13 (by decide) (by decide) (by decide), show s1.getReg .x13 = _ from hw.rx13]; congr 1; omega)
      (by rw [hreg3 .x14 (by decide) (by decide) (by decide), hreg2 .x14 (by decide) (by decide) (by decide), show s1.getReg .x14 = _ from hw.rx14]; congr 1; omega)
      hwLo3 hwHi3 hmem3 hsrc_al (by omega) (by omega) hro3 hc2_len
      (fun j hj => by simpa [c2, List.getElem_take, List.getElem_drop, Nat.add_assoc] using hchunk (16 + j) (by omega))
  have hlen3 : (((fwdBytes ++ c0) ++ c1) ++ c2).length = fwdBytes.length + 24 := by simp [hc0_len, hc1_len, hc2_len]
  obtain ⟨s5, hr5, hpc5, hreg5, hwLo5, hwHi5, hmem5, hro5, hcap5, htail5⟩ :=
    o_emit_dword (base := 148) (srcOff := srcOff) (qBase := qBase) (k := 3) (imm := 24#12)
      (cur := ((fwdBytes ++ c0) ++ c1) ++ c2) (chunk8 := c3) (by omega) (by decide) rfl rfl rfl rfl rfl rfl
      hpc4 (by rw [hreg4 .x10 (by decide) (by decide) (by decide), hreg3 .x10 (by decide) (by decide) (by decide),
          hreg2 .x10 (by decide) (by decide) (by decide)]; exact hx10)
      (by rw [hreg4 .x25 (by decide) (by decide) (by decide), hreg3 .x25 (by decide) (by decide) (by decide),
          hreg2 .x25 (by decide) (by decide) (by decide)]; exact hw.rx25)
      (by omega)
      (by rw [hreg4 .x13 (by decide) (by decide) (by decide), hreg3 .x13 (by decide) (by decide) (by decide),
          hreg2 .x13 (by decide) (by decide) (by decide), show s1.getReg .x13 = _ from hw.rx13]; congr 1; omega)
      (by rw [hreg4 .x14 (by decide) (by decide) (by decide), hreg3 .x14 (by decide) (by decide) (by decide),
          hreg2 .x14 (by decide) (by decide) (by decide), show s1.getReg .x14 = _ from hw.rx14]; congr 1; omega)
      hwLo4 hwHi4 hmem4 hsrc_al (by omega) (by omega) hro4 hc3_len
      (fun j hj => by simpa [c3, List.getElem_drop, Nat.add_assoc] using hchunk (24 + j) (by omega))
  have hpres5 : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → s5.getReg r = s1.getReg r := fun r h5 h6 h12 => by
    rw [hreg5 r h5 h6 h12, hreg4 r h5 h6 h12, hreg3 r h5 h6 h12, hreg2 r h5 h6 h12]
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have hadv := o_step_ADDI (by omega) hpc5 (rfl : openingInstr 154 = .base (.ADDI .x25 .x25 (32#12)))
  have hnew25 : s5.getReg .x25 + signExtend12 (32#12) =
      BitVec.ofNat 64 (10804531232 + 8 * ((fwdBytes ++ chunk).length / 8)) := by
    rw [hpres5 .x25 (by decide) (by decide) (by decide), show s1.getReg .x25 = BitVec.ofNat 64 (10804531232 + 8 * qBase) from hw.rx25,
      hse32, o_bv64_ofNat_add]; congr 1; simp only [List.length_append, hclen]; omega
  let s6 := (s5.setReg .x25 (BitVec.ofNat 64 (10804531232 + 8 * ((fwdBytes ++ chunk).length / 8)))).setPC (o_pcAt 155)
  have hadv' : OpenRuns s5 1 1 s6 := by simpa only [hnew25, s6] using hadv
  have hret := o_step_JALR_x0 (by omega) (rfl : s6.pc = o_pcAt 155)
    (rfl : openingInstr 155 = .base (.JALR .x0 .x1 (0#12)))
    (by simp only [s6, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x1 (by decide)]
        rw [hpres5 .x1 (by decide) (by decide) (by decide)]; rfl)
  refine ⟨s6.setPC (o_pcAt (callIdx + 1)), (((((hjal.trans hr2).trans hr3).trans hr4).trans hr5).trans hadv').trans hret,
    rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h1 h5 h6 h12 h25
    simp only [s6, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 r (Ne.symm h25)]
    rw [hpres5 r h5 h6 h12]
    simp only [s1, MachineState.getReg_setPC, o_getReg_setReg_ne .x1 r (Ne.symm h1)]
  · intro a h1 h2
    simp only [s6, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro5 a h1 h2
  · refine OpenWriterState.castList hcur_eq ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcur_eq]; rfl
    · simp only [s6, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x13 (by decide)]
      rw [hpres5 .x13 (by decide) (by decide) (by decide), show s1.getReg .x13 = _ from hw.rx13, hcur_eq]
      congr 1; simp only [List.length_append, hclen]; omega
    · simp only [s6, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x14 (by decide)]
      rw [hpres5 .x14 (by decide) (by decide) (by decide), show s1.getReg .x14 = _ from hw.rx14, hcur_eq]
      congr 1; simp only [List.length_append, hclen]; omega
    · intro j hj
      simp only [s6, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x12 (by decide)]; exact hwLo5 j hj
    · intro j h1 h2
      simp only [s6, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x12 (by decide)]; exact hwHi5 j h1 h2
    · intro j hj; simp only [s6, o_getByte_setPC, o_getByte_setReg]; exact hmem5 j hj
  · exact o_tailState_of_mem_eq ht htbd
      (fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl
        · simp only [s6, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x15 (by decide)]
          exact hpres5 .x15 (by decide) (by decide) (by decide)
        · simp only [s6, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x16 (by decide)]
          exact hpres5 .x16 (by decide) (by decide) (by decide)
        · simp only [s6, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x17 (by decide)]
          exact hpres5 .x17 (by decide) (by decide) (by decide)
        · simp only [s6, MachineState.getReg_setPC, o_getReg_setReg_ne .x25 .x31 (by decide)]
          exact hpres5 .x31 (by decide) (by decide) (by decide))
      (fun a ha1 ha2 => by
        simp only [s6, o_getByte_setPC, o_getByte_setReg]
        rw [htail5 a ha1 ha2, htail4 a ha1 ha2, htail3 a ha1 ha2, htail2 a ha1 ha2]; rfl)
  · intro a ha
    simp only [s6, o_getByte_setPC, o_getByte_setReg]
    rw [hcap5 a ha, hcap4 a ha, hcap3 a ha, hcap2 a ha]; rfl

/-- Call `emit30` (`156..189`): EXACT `15 + 5 * ((fwdBytes ++ chunk).length / 8 - fwdBytes.length / 8)` steps! -/
private theorem o_call_emit30 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx srcOff : Nat} {jOff : BitVec 21}
    {fwdBytes chunk : List Byte} {tails : List (BitVec 6)}
    (hcall : callIdx < 235)
    (hi : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : o_pcAt callIdx + signExtend21 jOff = o_pcAt 156)
    (hpc : s.pc = o_pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 32 ≤ 2080374784)
    (hbd : fwdBytes.length + 30 ≤ proofCap) (htbd : tails.length ≤ 200000000)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : OpenWriterState s fwdBytes) (ht : OpenTailState s tails)
    (hclen : chunk.length = 30)
    (hchunk : ∀ j (hj : j < 30),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk[j]'(by omega)) :
    let steps := 15 + 5 * ((fwdBytes ++ chunk).length / 8 - fwdBytes.length / 8)
    ∃ s', OpenRuns s steps steps s' ∧
      s'.pc = o_pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x25 →
        s'.getReg r = s.getReg r) ∧
      OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      OpenWriterState s' (fwdBytes ++ chunk) ∧
      OpenTailState s' tails ∧
      (∀ q < 4608, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro steps
  have hjal := o_step_JAL hcall hpc hi htgt
  let s1 := (s.setReg .x1 (o_pcAt (callIdx + 1))).setPC (o_pcAt 156)
  let c24 := chunk.take 24
  let c6 := chunk.drop 24
  have hc24_len : c24.length = 24 := by simp [c24, hclen]
  have hc6_len : c6.length = 6 := by simp [c6, hclen]
  have hsplit : (fwdBytes ++ c24) ++ c6 = fwdBytes ++ chunk := by
    rw [List.append_assoc, List.take_append_drop]
  obtain ⟨s2, hr2, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    o_emit_3dwords (s := s1) (base := 156) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := c24)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl hx10 hsrc_al (by omega) (by omega) hro hw.of_eq hc24_len
      (fun j hj => by simpa [c24, List.getElem_take] using hchunk j (by omega))
  -- 175: LD x5, 24(x10); 176: SLLI x5, x5, 16; 177: SRLI x5, x5, 16
  have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
  have hx10_2 : s2.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff) := by
    rw [hreg2 .x10 (by decide) (by decide) (by decide) (by decide)]; exact hx10
  have hsrc24 : s2.getReg .x10 + signExtend12 (24#12) = BitVec.ofNat 64 (4294971424 + (srcOff + 24)) := by
    rw [hx10_2, hse24, o_bv64_ofNat_add, Nat.add_assoc]
  set v := s2.getMem (BitVec.ofNat 64 (4294971424 + (srcOff + 24)))
  have h175 := o_step_LD (by omega) hpc2 (rfl : openingInstr 175 = .base (.LD .x5 .x10 (24#12)))
    (by rw [hsrc24]; exact o_accessValid_ofNat _ 8 (by omega) (by omega))
  let s3 := (s2.setReg .x5 v).setPC (o_pcAt 176)
  have h175' : OpenRuns s2 1 1 s3 := by simpa only [hsrc24, v, s3] using h175
  have h176 := o_step_SLLI (by omega) (rfl : s3.pc = o_pcAt 176) (rfl : openingInstr 176 = .base (.SLLI .x5 .x5 (16#6)))
  let s4 := (s3.setReg .x5 (v <<< 16)).setPC (o_pcAt 177)
  have h176' : OpenRuns s3 1 1 s4 := by simpa only [show s3.getReg .x5 = v from rfl, show (16#6 : BitVec 6).toNat = 16 from rfl, s4] using h176
  have h177 := o_step_SRLI (by omega) (rfl : s4.pc = o_pcAt 177) (rfl : openingInstr 177 = .base (.SRLI .x5 .x5 (16#6)))
  let s5 := (s4.setReg .x5 ((v <<< 16) >>> 16)).setPC (o_pcAt 178)
  have h177' : OpenRuns s4 1 1 s5 := by simpa only [show s4.getReg .x5 = v <<< 16 from rfl, show (16#6 : BitVec 6).toNat = 16 from rfl, s5] using h177
  have hx5_5 : ∀ j (hj : j < 8), (s5.getReg .x5).extractLsb' (8 * j) 8 =
      if hj' : j < 6 then c6[j]'(by omega) else 0#8 := by
    intro j hj
    change ((v <<< 16) >>> 16).extractLsb' (8 * j) 8 = _
    rw [show (16 : Nat) = 8 * (8 - 6) from rfl, o_word_mask_low_bytes v 6 (by omega) j hj]
    by_cases hlt6 : j < 6
    · rw [if_pos hlt6, dif_pos hlt6, o_readOnly_getMem_trapdoor_byte hro2 (srcOff + 24) j (by omega) hj (by omega)]
      simpa [c6, List.getElem_drop, Nat.add_assoc] using hchunk (24 + j) (by omega)
    · rw [if_neg hlt6, dif_neg hlt6]
  obtain ⟨s6, hr6, hpc6, hreg6, hro6, hw6, hcap6, htail6⟩ :=
    o_emit_partial (s := s5) (base := 178) (m := 6) (immBits := 48#12) (fwdBytes := fwdBytes ++ c24) (chunkM := c6)
      (by omega) (by omega) (by omega) (by decide) (by decide)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
      (by simp only [List.length_append, hc24_len]; omega) hro2 hw2.of_eq hc6_len hx5_5
  have hret := o_step_JALR_x0 (by omega) hpc6 (rfl : openingInstr 189 = .base (.JALR .x0 .x1 (0#12)))
    (by rw [hreg6 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp only [s5, s4, s3, MachineState.getReg_setPC, o_getReg_setReg_ne .x5 .x1 (by decide)]
        rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl)
  have hsteps_eq : 1 + 19 + 1 + 1 + 1 +
      (6 + 5 * (((fwdBytes ++ c24) ++ c6).length / 8 - (fwdBytes ++ c24).length / 8)) + 1 = steps := by
    simp only [steps, hsplit, List.length_append, hc24_len, hclen]; omega
  refine ⟨s6.setPC (o_pcAt (callIdx + 1)), ?_, rfl, ?_, hro6, (hw6.castList hsplit).of_eq, ?_, ?_⟩
  · rw [← hsteps_eq]
    exact (((((hjal.trans hr2).trans h175').trans h176').trans h177').trans hr6).trans hret
  · intro r h1 h5 h6 h7 h12 h13 h14 h25
    rw [MachineState.getReg_setPC, hreg6 r h5 h6 h7 h12 h13 h14 h25]
    simp only [s5, s4, s3, MachineState.getReg_setPC, o_getReg_setReg_ne .x5 r (Ne.symm h5)]
    rw [hreg2 r h5 h6 h12 h25]
    simp only [s1, MachineState.getReg_setPC, o_getReg_setReg_ne .x1 r (Ne.symm h1)]
  · exact o_tailState_of_mem_eq ht htbd
      (fun r hr => by
        have h1 : r ≠ .x1 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h5 : r ≠ .x5 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h6 : r ≠ .x6 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h7 : r ≠ .x7 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h12 : r ≠ .x12 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h13 : r ≠ .x13 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h14 : r ≠ .x14 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h25 : r ≠ .x25 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        rw [MachineState.getReg_setPC, hreg6 r h5 h6 h7 h12 h13 h14 h25]
        simp only [s5, s4, s3, MachineState.getReg_setPC, o_getReg_setReg_ne .x5 r (Ne.symm h5)]
        rw [hreg2 r h5 h6 h12 h25]
        simp only [s1, MachineState.getReg_setPC, o_getReg_setReg_ne .x1 r (Ne.symm h1)])
      (fun a ha1 ha2 => (htail6 a ha1 ha2).trans (htail2 a ha1 ha2))
  · intro a ha; exact (hcap6 a ha).trans (hcap2 a ha)

/-- Call `emit29_tail6` (`190..234`): EXACT
`21 + 5 * ((fwdBytes ++ chunk).length / 8 - fwdBytes.length / 8) + 4 * (acc'.length - acc.length)` steps! -/
private theorem o_call_emit29_tail6 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx srcOff : Nat} {jOff : BitVec 21}
    {fwdBytes chunk : List Byte} {tails : List (BitVec 6)} {d : Digest}
    (hcall : callIdx < 235)
    (hi : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : o_pcAt callIdx + signExtend21 jOff = o_pcAt 190)
    (hpc : s.pc = o_pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 32 ≤ 2080374784)
    (hbd : fwdBytes.length + 29 ≤ proofCap) (htbd : tails.length < 200000000)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : OpenWriterState s fwdBytes) (ht : OpenTailState s tails)
    (hclen : chunk.length = 29)
    (hchunk : ∀ j (hj : j < 29),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk[j]'(by omega))
    (hbyte29 : trapdoor.extractLsb' (8 * (srcOff + 29)) 8 = d.extractLsb' (8 * 29) 8) :
    let steps := 22 + 5 * ((fwdBytes ++ chunk).length / 8 - fwdBytes.length / 8) +
      4 * (((tails ++ [tail6 d]).foldl pack6Step ([], 0, 0)).1.length -
        (tails.foldl pack6Step ([], 0, 0)).1.length)
    ∃ s', OpenRuns s steps steps s' ∧
      s'.pc = o_pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
        r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      OpenWriterState s' (fwdBytes ++ chunk) ∧
      OpenTailState s' (tails ++ [tail6 d]) ∧
      (∀ q < 4608, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro steps
  have hjal := o_step_JAL hcall hpc hi htgt
  let s1 := (s.setReg .x1 (o_pcAt (callIdx + 1))).setPC (o_pcAt 190)
  let c24 := chunk.take 24
  let c5 := chunk.drop 24
  have hc24_len : c24.length = 24 := by simp [c24, hclen]
  have hc5_len : c5.length = 5 := by simp [c5, hclen]
  have hsplit : (fwdBytes ++ c24) ++ c5 = fwdBytes ++ chunk := by
    rw [List.append_assoc, List.take_append_drop]
  obtain ⟨s2, hr2, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    o_emit_3dwords (s := s1) (base := 190) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := c24)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl hx10 hsrc_al (by omega) (by omega) hro hw.of_eq hc24_len
      (fun j hj => by simpa [c24, List.getElem_take] using hchunk j (by omega))
  -- 209: LD x11, 24(x10); 210: SLLI x5, x11, 24; 211: SRLI x5, x5, 24
  have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
  have hx10_2 : s2.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff) := by
    rw [hreg2 .x10 (by decide) (by decide) (by decide) (by decide)]; exact hx10
  have hsrc24 : s2.getReg .x10 + signExtend12 (24#12) = BitVec.ofNat 64 (4294971424 + (srcOff + 24)) := by
    rw [hx10_2, hse24, o_bv64_ofNat_add, Nat.add_assoc]
  set v := s2.getMem (BitVec.ofNat 64 (4294971424 + (srcOff + 24)))
  have h209 := o_step_LD (by omega) hpc2 (rfl : openingInstr 209 = .base (.LD .x11 .x10 (24#12)))
    (by rw [hsrc24]; exact o_accessValid_ofNat _ 8 (by omega) (by omega))
  let s3 := (s2.setReg .x11 v).setPC (o_pcAt 210)
  have h209' : OpenRuns s2 1 1 s3 := by simpa only [hsrc24, v, s3] using h209
  have h210 := o_step_SLLI (by omega) (rfl : s3.pc = o_pcAt 210) (rfl : openingInstr 210 = .base (.SLLI .x5 .x11 (24#6)))
  let s4 := (s3.setReg .x5 (v <<< 24)).setPC (o_pcAt 211)
  have h210' : OpenRuns s3 1 1 s4 := by simpa only [show s3.getReg .x11 = v from rfl, show (24#6 : BitVec 6).toNat = 24 from rfl, s4] using h210
  have h211 := o_step_SRLI (by omega) (rfl : s4.pc = o_pcAt 211) (rfl : openingInstr 211 = .base (.SRLI .x5 .x5 (24#6)))
  let s5 := (s4.setReg .x5 ((v <<< 24) >>> 24)).setPC (o_pcAt 212)
  have h211' : OpenRuns s4 1 1 s5 := by simpa only [show s4.getReg .x5 = v <<< 24 from rfl, show (24#6 : BitVec 6).toNat = 24 from rfl, s5] using h211
  have hx5_5 : ∀ j (hj : j < 8), (s5.getReg .x5).extractLsb' (8 * j) 8 =
      if hj' : j < 5 then c5[j]'(by omega) else 0#8 := by
    intro j hj
    change ((v <<< 24) >>> 24).extractLsb' (8 * j) 8 = _
    rw [show (24 : Nat) = 8 * (8 - 5) from rfl, o_word_mask_low_bytes v 5 (by omega) j hj]
    by_cases hlt5 : j < 5
    · rw [if_pos hlt5, dif_pos hlt5, o_readOnly_getMem_trapdoor_byte hro2 (srcOff + 24) j (by omega) hj (by omega)]
      simpa [c5, List.getElem_drop, Nat.add_assoc] using hchunk (24 + j) (by omega)
    · rw [if_neg hlt5, dif_neg hlt5]
  obtain ⟨s6, hr6, hpc6, hreg6, hro6, hw6, hcap6, htail6⟩ :=
    o_emit_partial (s := s5) (base := 212) (m := 5) (immBits := 40#12) (fwdBytes := fwdBytes ++ c24) (chunkM := c5)
      (by omega) (by omega) (by omega) (by decide) (by decide)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
      (by simp only [List.length_append, hc24_len]; omega) hro2 hw2.of_eq hc5_len hx5_5
  have ht6 : OpenTailState s6 tails :=
    o_tailState_of_mem_eq ht (by omega)
      (fun r hr => by
        have h1 : r ≠ .x1 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h5 : r ≠ .x5 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h6 : r ≠ .x6 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h7 : r ≠ .x7 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h11 : r ≠ .x11 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h12 : r ≠ .x12 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h13 : r ≠ .x13 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h14 : r ≠ .x14 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        have h25 : r ≠ .x25 := by rcases hr with rfl | rfl | rfl | rfl <;> decide
        rw [hreg6 r h5 h6 h7 h12 h13 h14 h25]
        simp only [s5, s4, s3, MachineState.getReg_setPC, o_getReg_setReg_ne .x5 r (Ne.symm h5),
          o_getReg_setReg_ne .x11 r (Ne.symm h11)]
        rw [hreg2 r h5 h6 h12 h25]
        simp only [s1, MachineState.getReg_setPC, o_getReg_setReg_ne .x1 r (Ne.symm h1)])
      (fun a ha1 ha2 => (htail6 a ha1 ha2).trans (htail2 a ha1 ha2))
  have hx11_6 : (s6.getReg .x11).extractLsb' (8 * 5) 8 = d.extractLsb' (8 * 29) 8 := by
    rw [hreg6 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    have h11 : s5.getReg .x11 = v := by
      simp only [s5, s4, s3, MachineState.getReg_setPC, o_getReg_setReg_ne .x5 .x11 (by decide)]; rfl
    rw [h11, o_readOnly_getMem_trapdoor_byte hro2 (srcOff + 24) 5 (by omega) (by omega) (by omega)]
    simpa only [show srcOff + 24 + 5 = srcOff + 29 by omega] using hbyte29
  obtain ⟨s7, hr7, hpc7, hreg7, hro7, hw7, ht7, hcap7⟩ :=
    o_push_tail6 (d := d) hpc6 hx11_6
      (by rw [List.length_append, hclen]; omega) htbd hro6 (hw6.castList hsplit) ht6
  have hret := o_step_JALR_x0 (by omega) hpc7 (rfl : openingInstr 234 = .base (.JALR .x0 .x1 (0#12)))
    (by rw [hreg7 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg6 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp only [s5, s4, s3, MachineState.getReg_setPC, o_getReg_setReg_ne .x5 .x1 (by decide),
          o_getReg_setReg_ne .x11 .x1 (by decide)]
        rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl)
  have hsteps_eq : 1 + 19 + 1 + 1 + 1 +
      (6 + 5 * (((fwdBytes ++ c24) ++ c5).length / 8 - (fwdBytes ++ c24).length / 8)) +
      (7 + 4 * (((tails ++ [tail6 d]).foldl pack6Step ([], 0, 0)).1.length -
        (tails.foldl pack6Step ([], 0, 0)).1.length)) + 1 = steps := by
    simp only [steps, hsplit, List.length_append, hc24_len, hclen]; omega
  refine ⟨s7.setPC (o_pcAt (callIdx + 1)), ?_, rfl, ?_, hro7, hw7.of_eq, ht7.of_eq, ?_⟩
  · rw [← hsteps_eq]
    exact ((((((hjal.trans hr2).trans h209').trans h210').trans h211').trans hr6).trans hr7).trans hret
  · intro r h1 h5 h6 h7 h11 h12 h13 h14 h15 h16 h17 h25
    rw [MachineState.getReg_setPC, hreg7 r h5 h6 h7 h15 h16 h17, hreg6 r h5 h6 h7 h12 h13 h14 h25]
    simp only [s5, s4, s3, MachineState.getReg_setPC, o_getReg_setReg_ne .x5 r (Ne.symm h5),
      o_getReg_setReg_ne .x11 r (Ne.symm h11)]
    rw [hreg2 r h5 h6 h12 h25]
    simp only [s1, MachineState.getReg_setPC, o_getReg_setReg_ne .x1 r (Ne.symm h1)]
  · intro a ha; exact (hcap7 a ha).trans ((hcap6 a ha).trans (hcap2 a ha))

/-! ### 6. Final Flush, Reversed Tail Copy, and Halt (`86..109`) -/

private theorem o_flush_wbuf {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    (hpc : s.pc = o_pcAt 86)
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 10804531232)
    (hfbd : fwdBytes.length ≤ proofCap) (htbd : tails.length ≤ 200000000)
    (hw : OpenWriterState s fwdBytes) (ht : OpenTailState s tails) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 37 ∧
      s'.pc = o_pcAt 93 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (10804531232 + fwdBytes.length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
      OpenProofPrefix s' fwdBytes ∧
      OpenTailState s' tails := by
  have hpc_eq : proofCap = 8480886496 := rfl
  set q := fwdBytes.length / 8
  set r := fwdBytes.length % 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  have h86 := o_step_ADDI (by omega) hpc (rfl : openingInstr 86 = .base (.ADDI .x10 .x25 (0#12)))
  let s1 := (s.setReg .x10 (BitVec.ofNat 64 (10804531232 + 8 * q))).setPC (o_pcAt 87)
  have h86' : OpenRuns s 1 1 s1 := by
    have hv : s.getReg .x25 + signExtend12 (0#12) = BitVec.ofNat 64 (10804531232 + 8 * q) := by
      rw [hw.rx25, hse0, o_bv64_ofNat_add, Nat.add_zero]
    simpa only [hv, s1] using h86
  by_cases hr0 : r = 0
  · have h87 := o_step_BEQ_taken (by omega) (rfl : s1.pc = o_pcAt 87)
      (rfl : openingInstr 87 = .base (.BEQ .x13 .x0 (24#13)))
      (by have hr13 : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13
          rw [hr13, hr0]; rfl)
      (by decide : o_pcAt 87 + signExtend13 (24#13) = o_pcAt 93)
    refine ⟨2, s1.setPC (o_pcAt 93), h86'.trans h87, by omega, rfl, ?_, hx26, ?_, ht.of_eq⟩
    · change BitVec.ofNat 64 (10804531232 + 8 * q) = _; congr 1; omega
    · intro j hj; exact hw.memDwords j (by omega)
  · have hrpos : 0 < r := by omega
    have h87 := o_step_BEQ_not_taken (by omega) (rfl : s1.pc = o_pcAt 87)
      (rfl : openingInstr 87 = .base (.BEQ .x13 .x0 (24#13)))
      (by have hr13 : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13
          rw [hr13]; exact o_bv64_ofNat_ne (by omega) (by decide) (by omega))
    let s2 := s1.setPC (o_pcAt 88)
    have hdiv : 8 * q + r = fwdBytes.length := by omega
    have hloop : ∀ k (hk : k ≤ r), ∃ sk, OpenRuns s2 (5 * k) (5 * k) sk ∧
        sk.pc = (if k < r then o_pcAt 88 else o_pcAt 93) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (10804531232 + 8 * q + k) ∧
        sk.getReg .x13 = BitVec.ofNat 64 (8 * (r - k)) ∧
        sk.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
        (∀ j (hj : j < r - k), (sk.getReg .x12).extractLsb' (8 * j) 8 = fwdBytes[8 * q + k + j]'(by omega)) ∧
        (∀ j (hj : j < 8 * q + k), sk.getByte (BitVec.ofNat 64 (10804531232 + j)) = fwdBytes[j]'(by omega)) ∧
        OpenTailState sk tails := by
      intro k hk; induction k with
      | zero =>
        exact ⟨s2, OpenRuns.refl s2, by rw [if_pos hrpos]; rfl, rfl, hw.rx13, hx26,
          fun j hj => by change (s.getReg .x12).extractLsb' (8 * j) 8 = fwdBytes[8 * q + 0 + j]'(by omega); simpa only [Nat.add_zero] using hw.wbufLo j (by omega),
          fun j hj => hw.memDwords j (by omega), ht.of_eq⟩
      | succ k ih =>
        obtain ⟨sk, hrk, hpck, hx10k, hx13k, hx26k, hwLoK, hmemk, htk⟩ := ih (by omega)
        have hpck' : sk.pc = o_pcAt 88 := by simpa only [show k < r by omega, ite_true] using hpck
        have haddr : sk.getReg .x10 + signExtend12 (0#12) = BitVec.ofNat 64 (10804531232 + 8 * q + k) := by
          rw [hx10k, hse0, o_bv64_ofNat_add, Nat.add_zero]
        have ha := o_step_SB (by omega) hpck' (rfl : openingInstr 88 = .base (.SB .x10 .x12 (0#12)))
          (by rw [haddr]; exact o_accessValid_ofNat _ 1 (by omega) (by omega))
        have hbyte0 : (sk.getReg .x12).truncate 8 = fwdBytes[8 * q + k]'(by omega) := by
          rw [o_word_truncate8_eq_extractLsb'0]; simpa using hwLoK 0 (by omega)
        let sa := (sk.setByte (BitVec.ofNat 64 (10804531232 + 8 * q + k)) (fwdBytes[8 * q + k]'(by omega))).setPC (o_pcAt 89)
        have ha' : OpenRuns sk 1 1 sa := by simpa only [haddr, hbyte0, sa] using ha
        have hb := o_step_ADDI (by omega) (rfl : sa.pc = o_pcAt 89) (rfl : openingInstr 89 = .base (.ADDI .x10 .x10 (1#12)))
        let sb := (sa.setReg .x10 (BitVec.ofNat 64 (10804531232 + 8 * q + (k + 1)))).setPC (o_pcAt 90)
        have hb' : OpenRuns sa 1 1 sb := by
          have hr10 : sa.getReg .x10 = BitVec.ofNat 64 (10804531232 + 8 * q + k) := by
            simp only [sa, MachineState.getReg_setPC, o_getReg_setByte]; exact hx10k
          rw [hr10, hse1, o_bv64_ofNat_add, Nat.add_assoc] at hb; exact hb
        have hc := o_step_SRLI (by omega) (rfl : sb.pc = o_pcAt 90) (rfl : openingInstr 90 = .base (.SRLI .x12 .x12 (8#6)))
        let sc := (sb.setReg .x12 (sk.getReg .x12 >>> 8)).setPC (o_pcAt 91)
        have hc' : OpenRuns sb 1 1 sc := by
          have hr12 : sb.getReg .x12 = sk.getReg .x12 := by
            simp only [sb, sa, MachineState.getReg_setPC, o_getReg_setByte, o_getReg_setReg_ne .x10 .x12 (by decide)]
          simpa only [hr12, show (8#6 : BitVec 6).toNat = 8 from rfl, sc] using hc
        have hd := o_step_ADDI (by omega) (rfl : sc.pc = o_pcAt 91) (rfl : openingInstr 91 = .base (.ADDI .x13 .x13 (4088#12)))
        let sd := (sc.setReg .x13 (BitVec.ofNat 64 (8 * (r - (k + 1))))).setPC (o_pcAt 92)
        have hd' : OpenRuns sc 1 1 sd := by
          have hr13 : sc.getReg .x13 = BitVec.ofNat 64 (8 * (r - k)) := by
            simp only [sc, sb, sa, MachineState.getReg_setPC, o_getReg_setByte,
              o_getReg_setReg_ne .x12 .x13 (by decide), o_getReg_setReg_ne .x10 .x13 (by decide)]; exact hx13k
          have hv : sc.getReg .x13 + signExtend12 (4088#12) = BitVec.ofNat 64 (8 * (r - (k + 1))) := by
            rw [hr13, o_bv64_add_neg8 (8 * (r - k)) (by omega)]; congr 1; omega
          simpa only [hv, sd] using hd
        have hstep4 := ((ha'.trans hb').trans hc').trans hd'
        have hmem_d : ∀ j (hj : j < 8 * q + (k + 1)),
            sd.getByte (BitVec.ofNat 64 (10804531232 + j)) = fwdBytes[j]'(by omega) := by
          intro j hj
          simp only [sd, sc, sb, sa, o_getByte_setPC, o_getByte_setReg, set_byte_read]
          by_cases hlast : j = 8 * q + k
          · subst hlast
            rw [show 10804531232 + (8 * q + k) = 10804531232 + 8 * q + k by omega, if_pos rfl]
          · rw [if_neg (o_bv64_ofNat_ne (by omega) (by omega) (by omega))]
            exact hmemk j (by omega)
        have htd : OpenTailState sd tails := by
          have htb : tailBufBase = 20000000000 := rfl
          have ht' := o_tailState_setByte_outside (10804531232 + 8 * q + k) (fwdBytes[8 * q + k]'(by omega)) htk htbd (by omega)
          exact ⟨by simp only [sd, sc, sb, sa, MachineState.getReg_setPC, o_getReg_setByte,
                o_getReg_setReg_ne .x13 .x31 (by decide), o_getReg_setReg_ne .x12 .x31 (by decide),
                o_getReg_setReg_ne .x10 .x31 (by decide)]; exact htk.rx31,
            by simp only [sd, sc, sb, sa, MachineState.getReg_setPC, o_getReg_setByte,
                o_getReg_setReg_ne .x13 .x15 (by decide), o_getReg_setReg_ne .x12 .x15 (by decide),
                o_getReg_setReg_ne .x10 .x15 (by decide)]; exact htk.rx15,
            by simp only [sd, sc, sb, sa, MachineState.getReg_setPC, o_getReg_setByte,
                o_getReg_setReg_ne .x13 .x16 (by decide), o_getReg_setReg_ne .x12 .x16 (by decide),
                o_getReg_setReg_ne .x10 .x16 (by decide)]; exact htk.rx16,
            by simp only [sd, sc, sb, sa, MachineState.getReg_setPC, o_getReg_setByte,
                o_getReg_setReg_ne .x13 .x17 (by decide), o_getReg_setReg_ne .x12 .x17 (by decide),
                o_getReg_setReg_ne .x10 .x17 (by decide)]; exact htk.rx17,
            fun j hj => by simp only [sd, sc, sb, sa, o_getByte_setPC, o_getByte_setReg]; exact ht'.memTail j hj⟩
        have hwLo_d : ∀ j (hj : j < r - (k + 1)),
            (sd.getReg .x12).extractLsb' (8 * j) 8 = fwdBytes[8 * q + (k + 1) + j]'(by omega) := by
          intro j hj
          have h12 : sd.getReg .x12 = sk.getReg .x12 >>> 8 := by
            simp only [sd, sc, MachineState.getReg_setPC, o_getReg_setReg_ne .x13 .x12 (by decide)]; rfl
          rw [h12, o_word_ushr8_extractLsb' _ j (by omega)]
          simpa only [show 8 * q + k + (j + 1) = 8 * q + (k + 1) + j by omega] using hwLoK (j + 1) (by omega)
        have hx10_d : sd.getReg .x10 = BitVec.ofNat 64 (10804531232 + 8 * q + (k + 1)) := by
          simp only [sd, sc, sb, MachineState.getReg_setPC,
            o_getReg_setReg_ne .x13 .x10 (by decide), o_getReg_setReg_ne .x12 .x10 (by decide)]; rfl
        have hx26_d : sd.getReg .x26 = BitVec.ofNat 64 10804531232 := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, o_getReg_setByte,
            o_getReg_setReg_ne .x13 .x26 (by decide), o_getReg_setReg_ne .x12 .x26 (by decide),
            o_getReg_setReg_ne .x10 .x26 (by decide)]; exact hx26k
        by_cases hmore : k + 1 < r
        · have he := o_step_BNE_taken (by omega) (rfl : sd.pc = o_pcAt 92)
            (rfl : openingInstr 92 = .base (.BNE .x13 .x0 (8176#13)))
            (by change BitVec.ofNat 64 (8 * (r - (k + 1))) ≠ BitVec.ofNat 64 0
                exact o_bv64_ofNat_ne (by omega) (by decide) (by omega))
            (by decide : o_pcAt 92 + signExtend13 (8176#13) = o_pcAt 88)
          exact ⟨sd.setPC (o_pcAt 88), by simpa only [Nat.mul_succ] using (hrk.trans hstep4).trans he,
            by rw [if_pos hmore]; rfl, hx10_d, rfl, hx26_d, hwLo_d, hmem_d, htd.of_eq⟩
        · have hdone : r - (k + 1) = 0 := by omega
          have he := o_step_BNE_not_taken (by omega) (rfl : sd.pc = o_pcAt 92)
            (rfl : openingInstr 92 = .base (.BNE .x13 .x0 (8176#13)))
            (by change BitVec.ofNat 64 (8 * (r - (k + 1))) = 0#64; rw [hdone])
          exact ⟨sd.setPC (o_pcAt 93), by simpa only [Nat.mul_succ] using (hrk.trans hstep4).trans he,
            by rw [if_neg hmore]; rfl, hx10_d, rfl, hx26_d, hwLo_d, hmem_d, htd.of_eq⟩
    obtain ⟨sf, hrf, hpcf, hx10f, _, hx26f, _, hmemf, htf⟩ := hloop r (Nat.le_refl r)
    refine ⟨2 + 5 * r, sf, (h86'.trans h87).trans hrf, by omega,
      by simpa only [Nat.lt_irrefl, ite_false] using hpcf,
      by rw [hx10f]; congr 1; omega, hx26f, fun j hj => hmemf j (by omega), htf⟩

private theorem o_flush_tail {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    (hpc : s.pc = o_pcAt 93)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (10804531232 + fwdBytes.length))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 10804531232)
    (hfbd : fwdBytes.length ≤ proofCap) (htbd : tails.length ≤ 200000000)
    (hpr : OpenProofPrefix s fwdBytes) (ht : OpenTailState s tails) :
    let packed := pack6Bits tails
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 3 ∧
      s'.pc = o_pcAt 96 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (10804531232 + fwdBytes.length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
      s'.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
      s'.getReg .x15 = BitVec.ofNat 64 (tailBufBase + packed.length) ∧
      OpenProofPrefix s' fwdBytes ∧
      OpenTailBufPrefix s' packed := by
  intro packed
  have hpc_eq : proofCap = 8480886496 := rfl
  have htb : tailBufBase = 20000000000 := rfl
  set st := tails.foldl pack6Step ([], 0, 0)
  have hst_bd := o_pack6_foldl_bounds tails
  set acc := st.1
  set tBuf := st.2.1
  set tCnt := st.2.2
  have htCnt_lt : tCnt < 8 := hst_bd.1
  have htBuf_lt : tBuf < 2 ^ tCnt := hst_bd.2.1
  have hacc_len : 8 * acc.length + tCnt = 6 * tails.length := hst_bd.2.2
  have hpow : 2 ^ tCnt ≤ 128 := by
    have h1 : 2 ^ tCnt ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 7 = 128 := by decide
    omega
  by_cases hcnt0 : tCnt = 0
  · have h93 := o_step_BEQ_taken (by omega) hpc
      (rfl : openingInstr 93 = .base (.BEQ .x17 .x0 (12#13)))
      (by rw [ht.rx17]; exact congrArg (BitVec.ofNat 64) hcnt0)
      (by decide : o_pcAt 93 + signExtend13 (12#13) = o_pcAt 96)
    have hpack_eq : packed = acc := by
      unfold packed pack6Bits pack6Finish
      change (if 0 < tCnt then _ else acc) = acc; rw [if_neg (by omega)]
    rw [hpack_eq]
    exact ⟨1, s.setPC (o_pcAt 96), h93, by omega, rfl, hx10, hx26, ht.rx31, ht.rx15, hpr, ht.memTail⟩
  · have hpos : 0 < tCnt := by omega
    have hpack_eq : packed = acc ++ [BitVec.ofNat 8 tBuf] := by
      unfold packed pack6Bits pack6Finish
      change (if 0 < tCnt then acc ++ [BitVec.ofNat 8 tBuf] else acc) = _; rw [if_pos hpos]
    have h93 := o_step_BEQ_not_taken (by omega) hpc
      (rfl : openingInstr 93 = .base (.BEQ .x17 .x0 (12#13)))
      (by rw [ht.rx17]; exact o_bv64_ofNat_ne (by omega) (by decide) hcnt0)
    let s1 := s.setPC (o_pcAt 94)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have haddr : s1.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + acc.length) := by
      have hr15 : s1.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := ht.rx15
      rw [hr15, hse0, o_bv64_ofNat_add, Nat.add_zero]
    have h94 := o_step_SB (by omega) (rfl : s1.pc = o_pcAt 94)
      (rfl : openingInstr 94 = .base (.SB .x15 .x16 (0#12)))
      (by rw [haddr]; exact o_accessValid_ofNat _ 1 (by omega) (by omega))
    let s2 := (s1.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 tBuf)).setPC (o_pcAt 95)
    have h94' : OpenRuns s1 1 1 s2 := by
      have htr : (s1.getReg .x16).truncate 8 = BitVec.ofNat 8 tBuf := by
        have hr16 : s1.getReg .x16 = BitVec.ofNat 64 tBuf := ht.rx16
        rw [hr16]; exact o_bv64_ofNat_truncate8 tBuf (by omega)
      simpa only [haddr, htr, s2] using h94
    have h95 := o_step_ADDI (by omega) (rfl : s2.pc = o_pcAt 95)
      (rfl : openingInstr 95 = .base (.ADDI .x15 .x15 (1#12)))
    let s3 := (s2.setReg .x15 (BitVec.ofNat 64 (tailBufBase + packed.length))).setPC (o_pcAt 96)
    have h95' : OpenRuns s2 1 1 s3 := by
      have hr15 : s2.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := by
        simp only [s2, MachineState.getReg_setPC, o_getReg_setByte]; exact ht.rx15
      have hv : s2.getReg .x15 + signExtend12 (1#12) = BitVec.ofNat 64 (tailBufBase + packed.length) := by
        rw [hr15, hse1, o_bv64_ofNat_add, hpack_eq, List.length_append, List.length_singleton, Nat.add_assoc]
      simpa only [hv, s3] using h95
    refine ⟨3, s3, (h93.trans h94').trans h95', Nat.le_refl 3, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · simp only [s3, s2, s1, MachineState.getReg_setPC, o_getReg_setByte, o_getReg_setReg_ne .x15 .x10 (by decide)]; exact hx10
    · simp only [s3, s2, s1, MachineState.getReg_setPC, o_getReg_setByte, o_getReg_setReg_ne .x15 .x26 (by decide)]; exact hx26
    · simp only [s3, s2, s1, MachineState.getReg_setPC, o_getReg_setByte, o_getReg_setReg_ne .x15 .x31 (by decide)]; exact ht.rx31
    · intro j hj
      simp only [s3, s2, s1, o_getByte_setPC, o_getByte_setReg, set_byte_read]
      rw [if_neg (o_bv64_ofNat_ne (by omega) (by omega) (by omega))]; exact hpr j hj
    · rw [hpack_eq]
      intro j hj
      simp only [s3, s2, s1, o_getByte_setPC, o_getByte_setReg, set_byte_read]
      have hjlen : j < acc.length + 1 := by simpa using hj
      by_cases hlast : j = acc.length
      · subst hlast
        rw [if_pos rfl, o_list_getElem_append_right acc [BitVec.ofNat 8 tBuf] acc.length (by omega) hj]; simp
      · rw [if_neg (o_bv64_ofNat_ne (by omega) (by omega) (by omega)),
          ht.memTail j (by omega), o_list_getElem_append_left acc [BitVec.ofNat 8 tBuf] j (by omega)]

private theorem o_rev_tail {s : MachineState} {fwdBytes packed : List Byte}
    (hpc : s.pc = o_pcAt 96)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (10804531232 + fwdBytes.length))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 10804531232)
    (hx31 : s.getReg .x31 = BitVec.ofNat 64 tailBufBase)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + packed.length))
    (hbd : fwdBytes.length + packed.length ≤ proofCap)
    (hpr : OpenProofPrefix s fwdBytes) (htail : OpenTailBufPrefix s packed) :
    ∃ s', OpenRuns s (1 + 5 * packed.length) (1 + 5 * packed.length) s' ∧
      s'.pc = o_pcAt 102 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (10804531232 + (fwdBytes ++ packed.reverse).length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
      OpenProofPrefix s' (fwdBytes ++ packed.reverse) := by
  have hpc_eq : proofCap = 8480886496 := rfl
  have htb : tailBufBase = 20000000000 := rfl
  set m := packed.length
  by_cases hm0 : m = 0
  · have hnil : packed = [] := List.eq_nil_of_length_eq_zero hm0
    have h96 := o_step_BEQ_taken (by omega) hpc
      (rfl : openingInstr 96 = .base (.BEQ .x15 .x31 (24#13)))
      (by rw [hx15, hx31, hm0, Nat.add_zero])
      (by decide : o_pcAt 96 + signExtend13 (24#13) = o_pcAt 102)
    subst hnil
    exact ⟨s.setPC (o_pcAt 102), by rw [hm0, Nat.mul_zero, Nat.add_zero]; exact h96,
      rfl, by rw [List.reverse_nil, List.append_nil]; exact hx10, hx26,
      by rw [List.reverse_nil, List.append_nil]; exact hpr⟩
  · have hmpos : 0 < m := by omega
    have h96 := o_step_BEQ_not_taken (by omega) hpc
      (rfl : openingInstr 96 = .base (.BEQ .x15 .x31 (24#13)))
      (by rw [hx15, hx31]; exact o_bv64_ofNat_ne (by omega) (by omega) (by omega))
    let s1 := s.setPC (o_pcAt 97)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have hloop : ∀ u ≤ m, ∃ su, OpenRuns s1 (5 * u) (5 * u) su ∧
        su.pc = (if u < m then o_pcAt 97 else o_pcAt 102) ∧
        su.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (m - u)) ∧
        su.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
        su.getReg .x10 = BitVec.ofNat 64 (10804531232 + fwdBytes.length + u) ∧
        su.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
        OpenProofPrefix su (fwdBytes ++ packed.reverse.take u) ∧
        OpenTailBufPrefix su packed := by
      intro u hu; induction u with
      | zero =>
        exact ⟨s1, OpenRuns.refl s1, by rw [if_pos hmpos]; rfl, by rw [Nat.sub_zero]; exact hx15,
          hx31, by rw [Nat.add_zero]; exact hx10, hx26,
          by rw [List.take_zero, List.append_nil]; exact hpr, htail⟩
      | succ u ih =>
        obtain ⟨su, hru, hpcu, hx15u, hx31u, hx10u, hx26u, hpru, htailu⟩ := ih (by omega)
        have hpcu' : su.pc = o_pcAt 97 := by simpa only [show u < m by omega, ite_true] using hpcu
        have ha := o_step_ADDI (by omega) hpcu' (rfl : openingInstr 97 = .base (.ADDI .x15 .x15 (4095#12)))
        let sa := (su.setReg .x15 (BitVec.ofNat 64 (tailBufBase + (m - (u + 1))))).setPC (o_pcAt 98)
        have ha' : OpenRuns su 1 1 sa := by
          have hr15 : su.getReg .x15 = BitVec.ofNat 64 ((tailBufBase + (m - (u + 1))) + 1) := by
            rw [hx15u]; congr 1; omega
          rw [hr15, o_bv64_add_neg1] at ha; exact ha
        have haddr6 : sa.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + (m - (u + 1))) := by
          change BitVec.ofNat 64 _ + _ = _; rw [hse0, o_bv64_ofNat_add, Nat.add_zero]
        have hb := o_step_LBU (by omega) (rfl : sa.pc = o_pcAt 98)
          (rfl : openingInstr 98 = .base (.LBU .x6 .x15 (0#12)))
          (by rw [haddr6]; exact o_accessValid_ofNat _ 1 (by omega) (by omega))
        set bCur := packed[m - (u + 1)]'(by omega)
        let sb := (sa.setReg .x6 (bCur.zeroExtend 64)).setPC (o_pcAt 99)
        have hb' : OpenRuns sa 1 1 sb := by
          have hget : sa.getByte (BitVec.ofNat 64 (tailBufBase + (m - (u + 1)))) = bCur :=
            htailu (m - (u + 1)) (by omega)
          simpa only [haddr6, hget, sb] using hb
        have haddr10 : sb.getReg .x10 + signExtend12 (0#12) = BitVec.ofNat 64 (10804531232 + fwdBytes.length + u) := by
          have hr10 : sb.getReg .x10 = BitVec.ofNat 64 (10804531232 + fwdBytes.length + u) := hx10u
          rw [hr10, hse0, o_bv64_ofNat_add, Nat.add_zero]
        have hc := o_step_SB (by omega) (rfl : sb.pc = o_pcAt 99)
          (rfl : openingInstr 99 = .base (.SB .x10 .x6 (0#12)))
          (by rw [haddr10]; exact o_accessValid_ofNat _ 1 (by omega) (by omega))
        let sc := (sb.setByte (BitVec.ofNat 64 (10804531232 + fwdBytes.length + u)) bCur).setPC (o_pcAt 100)
        have hc' : OpenRuns sb 1 1 sc := by
          have htr : (sb.getReg .x6).truncate 8 = bCur := o_byte_zeroExtend_truncate8 bCur
          simpa only [haddr10, htr, sc] using hc
        have hd := o_step_ADDI (by omega) (rfl : sc.pc = o_pcAt 100)
          (rfl : openingInstr 100 = .base (.ADDI .x10 .x10 (1#12)))
        let sd := (sc.setReg .x10 (BitVec.ofNat 64 (10804531232 + fwdBytes.length + (u + 1)))).setPC (o_pcAt 101)
        have hd' : OpenRuns sc 1 1 sd := by
          have hr10 : sc.getReg .x10 = BitVec.ofNat 64 (10804531232 + fwdBytes.length + u) := by
            simp only [sc, sb, sa, MachineState.getReg_setPC, o_getReg_setByte,
              o_getReg_setReg_ne .x6 .x10 (by decide), o_getReg_setReg_ne .x15 .x10 (by decide)]
            exact hx10u
          rw [hr10, hse1, o_bv64_ofNat_add, Nat.add_assoc] at hd; exact hd
        have hstep4 := ((ha'.trans hb').trans hc').trans hd'
        have hx15_d : sd.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (m - (u + 1))) := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, o_getReg_setByte,
            o_getReg_setReg_ne .x10 .x15 (by decide), o_getReg_setReg_ne .x6 .x15 (by decide)]; rfl
        have hx31_d : sd.getReg .x31 = BitVec.ofNat 64 tailBufBase := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, o_getReg_setByte,
            o_getReg_setReg_ne .x10 .x31 (by decide), o_getReg_setReg_ne .x6 .x31 (by decide),
            o_getReg_setReg_ne .x15 .x31 (by decide)]; exact hx31u
        have hx26_d : sd.getReg .x26 = BitVec.ofNat 64 10804531232 := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, o_getReg_setByte,
            o_getReg_setReg_ne .x10 .x26 (by decide), o_getReg_setReg_ne .x6 .x26 (by decide),
            o_getReg_setReg_ne .x15 .x26 (by decide)]; exact hx26u
        have hrev_u : packed.reverse[u]'(by simp [m]; omega) = bCur := by
          rw [List.getElem_reverse]; congr 1; omega
        have htake_succ : fwdBytes ++ packed.reverse.take (u + 1) =
            (fwdBytes ++ packed.reverse.take u) ++ [bCur] := by
          rw [List.take_succ_eq_append_getElem (by simp [m]; omega), hrev_u, List.append_assoc]
        have hpr_d : OpenProofPrefix sd (fwdBytes ++ packed.reverse.take (u + 1)) := by
          rw [htake_succ]
          intro j hj
          have hlen_pre : (fwdBytes ++ packed.reverse.take u).length = fwdBytes.length + u := by
            simp only [List.length_append, List.length_take, List.length_reverse]; omega
          have hjle : j < fwdBytes.length + u + 1 := by
            rw [List.length_append, List.length_singleton] at hj; omega
          simp only [sd, sc, sb, sa, o_getByte_setPC, o_getByte_setReg, set_byte_read]
          by_cases hlast : j = fwdBytes.length + u
          · subst hlast
            rw [show 10804531232 + (fwdBytes.length + u) = 10804531232 + fwdBytes.length + u by omega,
              if_pos rfl, o_list_getElem_append_right _ [bCur] (fwdBytes.length + u) (by omega) hj]
            simp [hlen_pre]
          · rw [if_neg (o_bv64_ofNat_ne (by omega) (by omega) (by omega))]
            have hjlt : j < (fwdBytes ++ packed.reverse.take u).length := by omega
            rw [hpru j hjlt, o_list_getElem_append_left _ [bCur] j hjlt]
        have htail_d : OpenTailBufPrefix sd packed := by
          intro j hj
          simp only [sd, sc, sb, sa, o_getByte_setPC, o_getByte_setReg, set_byte_read]
          rw [if_neg (o_bv64_ofNat_ne (by omega) (by omega) (by omega))]; exact htailu j hj
        by_cases hmore : u + 1 < m
        · have he := o_step_BNE_taken (by omega) (rfl : sd.pc = o_pcAt 101)
            (rfl : openingInstr 101 = .base (.BNE .x15 .x31 (8176#13)))
            (by rw [hx15_d, hx31_d]; exact o_bv64_ofNat_ne (by omega) (by omega) (by omega))
            (by decide : o_pcAt 101 + signExtend13 (8176#13) = o_pcAt 97)
          exact ⟨sd.setPC (o_pcAt 97), by simpa only [Nat.mul_succ] using (hru.trans hstep4).trans he,
            by rw [if_pos hmore]; rfl, hx15_d, hx31_d, rfl, hx26_d, hpr_d, htail_d⟩
        · have hdone : m - (u + 1) = 0 := by omega
          have he := o_step_BNE_not_taken (by omega) (rfl : sd.pc = o_pcAt 101)
            (rfl : openingInstr 101 = .base (.BNE .x15 .x31 (8176#13)))
            (by rw [hx15_d, hx31_d, hdone, Nat.add_zero])
          exact ⟨sd.setPC (o_pcAt 102), by simpa only [Nat.mul_succ] using (hru.trans hstep4).trans he,
            by rw [if_neg hmore]; rfl, hx15_d, hx31_d, rfl, hx26_d, hpr_d, htail_d⟩
    obtain ⟨sf, hrf, hpcf, _, _, hx10f, hx26f, hprf, _⟩ := hloop m (Nat.le_refl m)
    have htakeAll : packed.reverse.take m = packed.reverse := by
      rw [show m = packed.reverse.length by simp [m], List.take_length]
    rw [htakeAll] at hprf
    refine ⟨sf, h96.trans hrf, by simpa only [Nat.lt_irrefl, ite_false] using hpcf, ?_, hx26f, hprf⟩
    rw [hx10f]; congr 1; simp [m]; omega

private theorem o_finish {s : MachineState} {proofLen : Nat}
    (hpc : s.pc = o_pcAt 102)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (10804531232 + proofLen))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 10804531232) :
    ∃ sHalt, OpenRuns s 3 3 sHalt ∧
      sHalt.pc = o_pcAt 105 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = BitVec.ofNat 64 proofLen ∧
      sHalt.mem = s.mem := by
  have h1 := o_step_SUB (by omega) hpc (rfl : openingInstr 102 = .base (.SUB .x11 .x10 .x26))
  have hsub : s.getReg .x10 - s.getReg .x26 = BitVec.ofNat 64 proofLen := by
    rw [hx10, hx26, o_bv64_ofNat_sub _ _ (by omega), Nat.add_sub_cancel_left]
  let s1 := (s.setReg .x11 (BitVec.ofNat 64 proofLen)).setPC (o_pcAt 103)
  have h1' : OpenRuns s 1 1 s1 := by simpa only [hsub, s1] using h1
  have h2 := o_step_ADDI (by omega) (rfl : s1.pc = o_pcAt 103) (rfl : openingInstr 103 = .base (.ADDI .x5 .x0 (1#12)))
  let s2 := (s1.setReg .x5 1#64).setPC (o_pcAt 104)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x0 + signExtend12 (1#12) = 1#64 := by change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s2] using h2
  have h3 := o_step_ADDI (by omega) (rfl : s2.pc = o_pcAt 104) (rfl : openingInstr 104 = .base (.ADDI .x10 .x0 (0#12)))
  let s3 := (s2.setReg .x10 0#64).setPC (o_pcAt 105)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hv : s2.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s3] using h3
  exact ⟨s3, (h1'.trans h2').trans h3', rfl, rfl, rfl, rfl, rfl⟩

/-! ### 7. Position Loop (`27..69`) and Descending Cap Frontier Loop (`70..85`) -/

private def o_capMark16Prefix (positions : Positions) (t idx : Nat) : Bool :=
  decide (∃ u < t, openingIndex positions u >>> 16 = idx)

private theorem o_capMark16Prefix_card (positions : Positions) (idx : Nat) :
    o_capMark16Prefix positions positions.card idx = capMark positions 16 idx := by
  simp only [o_capMark16Prefix, capMark_16]
  by_cases hL : ∃ u < positions.card, openingIndex positions u >>> 16 = idx
  · have hR : ∃ i ∈ positions, capLeafOf i = idx := by
      obtain ⟨u, hu, heq⟩ := hL
      have hlen : u < (positions.sort (· ≤ ·)).length := by simpa using hu
      refine ⟨(positions.sort (· ≤ ·))[u]'hlen,
        (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hlen), ?_⟩
      simpa only [capLeafOf, openingIndex, dif_pos hu] using heq
    simp [hL, hR]
  · have hR : ¬ ∃ i ∈ positions, capLeafOf i = idx := by
      rintro ⟨i, hi, heq⟩
      have hmem : i ∈ positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
      obtain ⟨u, hu, hget⟩ := o_list_mem_exists_getElem hmem
      have hu' : u < positions.card := by simpa using hu
      apply hL; refine ⟨u, hu', ?_⟩
      simp only [openingIndex, dif_pos hu', hget]; exact heq
    simp [hL, hR]

private structure OpenPosInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (t : Nat) (fwdBytes : List Byte) (tails : List (BitVec 6))
    (s : MachineState) : Prop where
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + (rowOff + 40))
  rx20 : s.getReg .x20 = BitVec.ofNat 64 16777216
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx24 : s.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * t)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 10804531232
  rx27 : s.getReg .x27 = BitVec.ofNat 64 (positions.card - t)
  ro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  writer : OpenWriterState s fwdBytes
  tail : OpenTailState s tails
  cap16 : ∀ c < 256, s.getByte (BitVec.ofNat 64 (4096 + 256 + c)) =
    if o_capMark16Prefix positions t c then 1#8 else 0#8

private theorem OpenPosInv.after_sub {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes fwdBytes' : List Byte}
    {tails tails' : List (BitVec 6)} {s s' : MachineState}
    (inv : OpenPosInv trapdoor positions t fwdBytes tails s)
    (hreg : ∀ r, r = .x9 ∨ r = .x18 ∨ r = .x20 ∨ r = .x21 ∨ r = .x24 ∨ r = .x26 ∨ r = .x27 →
      s'.getReg r = s.getReg r)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s')
    (hw : OpenWriterState s' fwdBytes')
    (ht : OpenTailState s' tails')
    (hcap : ∀ q < 4608, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) :
    OpenPosInv trapdoor positions t fwdBytes' tails' s' :=
  ⟨by rw [hreg .x9 (by simp)]; exact inv.rx9,
   by rw [hreg .x18 (by simp)]; exact inv.rx18,
   by rw [hreg .x20 (by simp)]; exact inv.rx20,
   by rw [hreg .x21 (by simp)]; exact inv.rx21,
   by rw [hreg .x24 (by simp)]; exact inv.rx24,
   by rw [hreg .x26 (by simp)]; exact inv.rx26,
   by rw [hreg .x27 (by simp)]; exact inv.rx27,
   hro, hw, ht, fun c hc => by rw [hcap (4096 + 256 + c) (by omega)]; exact inv.cap16 c hc⟩

/-- Helper: one sibling step (`XORI x6, x22, 1; SLLI x6, x6, 5; ADD x10, x9, x6`) producing
`x10 = C_TD + 32 * heapIdx l ((i >>> l) ^^^ 1)` (3 steps). -/
private theorem o_sib_addr_steps {s : MachineState} {base l : Nat} {i : Index}
    (hbase : base + 2 < 235) (hl : l < 24)
    (hi0 : openingInstr base = .base (.XORI .x6 .x22 (1#12)))
    (hi1 : openingInstr (base + 1) = .base (.SLLI .x6 .x6 (5#6)))
    (hi2 : openingInstr (base + 2) = .base (.ADD .x10 .x9 .x6))
    (hpc : s.pc = o_pcAt base)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (heapIdx l (i.val >>> l))) :
    let sib := (i.val >>> l) ^^^ 1
    let s3 := (((s.setReg .x6 (BitVec.ofNat 64 (heapIdx l sib))).setPC (o_pcAt (base + 1))
                |>.setReg .x6 (BitVec.ofNat 64 (32 * heapIdx l sib))).setPC (o_pcAt (base + 2))
                |>.setReg .x10 (BitVec.ofNat 64 (4294971424 + 32 * heapIdx l sib))).setPC (o_pcAt (base + 3))
    OpenRuns s 3 3 s3 ∧
    s3.pc = o_pcAt (base + 3) ∧
    s3.getReg .x10 = BitVec.ofNat 64 (4294971424 + 32 * heapIdx l sib) ∧
    (∀ r, r ≠ .x6 → r ≠ .x10 → s3.getReg r = s.getReg r) ∧
    (∀ a, s3.getByte a = s.getByte a) ∧
    (∀ a, s3.getMem a = s.getMem a) := by
  intro sib s3
  have hi_lt : i.val < 2 ^ 24 := i.isLt
  have hsh : i.val >>> l < levelSize l := by
    rw [Nat.shiftRight_eq_div_pow]; unfold levelSize
    rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2)), ← Nat.pow_add,
      show 24 - l + l = 24 by omega]; exact hi_lt
  have hhl_lt : heapIdx l (i.val >>> l) < 2 ^ 25 := heapIdx_lt l _ (by omega) hsh
  have h0 := o_step_XORI (by omega) hpc hi0
  let s1 := (s.setReg .x6 (BitVec.ofNat 64 (heapIdx l sib))).setPC (o_pcAt (base + 1))
  have h0' : OpenRuns s 1 1 s1 := by
    have hv : s.getReg .x22 ^^^ signExtend12 (1#12) = BitVec.ofNat 64 (heapIdx l sib) := by
      rw [hx22, o_bv64_xor1 _ (by omega), o_heapIdx_xor1 l _ hl hsh]
    simpa only [hv, s1] using h0
  have h1 := o_step_SLLI (by omega) (rfl : s1.pc = o_pcAt (base + 1)) hi1
  let s2 := (s1.setReg .x6 (BitVec.ofNat 64 (32 * heapIdx l sib))).setPC (o_pcAt (base + 2))
  have h1' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x6 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (32 * heapIdx l sib) := by
      change BitVec.ofNat 64 (heapIdx l sib) <<< 5 = _
      rw [o_bv64_shl]; congr 1; omega
    simpa only [hv, s2, show base + 1 + 1 = base + 2 by omega] using h1
  have h2 := o_step_ADD (by omega) (rfl : s2.pc = o_pcAt (base + 2)) hi2
  have h2' : OpenRuns s2 1 1 s3 := by
    have hr9 : s2.getReg .x9 = BitVec.ofNat 64 4294971424 := hx9
    have hv : s2.getReg .x9 + s2.getReg .x6 = BitVec.ofNat 64 (4294971424 + 32 * heapIdx l sib) := by
      rw [hr9]; change BitVec.ofNat 64 4294971424 + BitVec.ofNat 64 (32 * heapIdx l sib) = _
      exact o_bv64_ofNat_add _ _
    simpa only [hv, s3, s2, s1, show base + 2 + 1 = base + 3 by omega] using h2
  refine ⟨(h0'.trans h1').trans h2', rfl, rfl, ?_, ?_, ?_⟩
  · intro r h6 h10
    simp only [s3, MachineState.getReg_setPC, o_getReg_setReg_ne .x10 r (Ne.symm h10),
      o_getReg_setReg_ne .x6 r (Ne.symm h6)]
  · intro a; simp only [s3, o_getByte_setPC, o_getByte_setReg]
  · intro a; simp only [s3, MachineState.getMem_setPC, MachineState.getMem_setReg]

/-- Single position iteration of `pos_loop` (`words 27..69`): emits `recordFwd` (`498 B`) and
`recordTails` (`10` tails), marks `capMark[256 + (i >>> 16)] = 1`, advances `x24`/`x27`, with
EXACT telescoping step count `400 + 5 * (q' - q) + 4 * (acc' - acc)`! -/
private theorem o_pos_iter {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (ht : t < positions.card) (hpc : s.pc = o_pcAt 27)
    (hbd : fwdBytes.length + 498 ≤ proofCap)
    (htbd : tails.length + 10 ≤ 200000000)
    (inv : OpenPosInv trapdoor positions t fwdBytes tails s) :
    let i : Index := (positions.sort (· ≤ ·))[t]'(by simpa using ht)
    let fwd' := fwdBytes ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) i
    let tails' := tails ++ recordTails (tdNode trapdoor) i
    let steps := 410 + 5 * (fwd'.length / 8 - fwdBytes.length / 8) +
      4 * ((tails'.foldl pack6Step ([], 0, 0)).1.length - (tails.foldl pack6Step ([], 0, 0)).1.length)
    ∃ s', OpenRuns s steps steps s' ∧
      s'.pc = (if t + 1 < positions.card then o_pcAt 27 else o_pcAt 70) ∧
      OpenPosInv trapdoor positions (t + 1) fwd' tails' s' := by
  intro i fwd' tails' steps
  have hcard := o_positions_card_le positions
  have hi_lt : i.val < 16777216 := i.isLt
  have hopen : openingIndex positions t = i.val := by simp only [openingIndex, dif_pos ht]; rfl
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  -- Part A (`27..36`): load index `i`, compute salt address, call `emit24` (30 steps = 15 + 5*3)
  have haddr27 : s.getReg .x24 + signExtend12 (0#12) = BitVec.ofNat 64 (6375346208 + 8 * t) := by
    rw [inv.rx24, hse0, o_bv64_ofNat_add, Nat.add_zero]
  have h27 := o_step_LD (by omega) hpc (rfl : openingInstr 27 = .base (.LD .x8 .x24 (0#12)))
    (by rw [haddr27]; exact o_accessValid_ofNat _ 8 (by omega) (by omega))
  let s28 := (s.setReg .x8 (BitVec.ofNat 64 i.val)).setPC (o_pcAt 28)
  have h27' : OpenRuns s 1 1 s28 := by
    have hmem := o_readOnly_getMem_index inv.ro t ht; rw [hopen] at hmem
    simpa only [haddr27, hmem, s28] using h27
  have h28 := o_step_SRLI (by omega) (rfl : s28.pc = o_pcAt 28) (rfl : openingInstr 28 = .base (.SRLI .x6 .x8 (1#6)))
  let s29 := (s28.setReg .x6 (BitVec.ofNat 64 (i.val / 2))).setPC (o_pcAt 29)
  have h28' : OpenRuns s28 1 1 s29 := by
    have hv : s28.getReg .x8 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (i.val / 2) := by
      change BitVec.ofNat 64 i.val >>> 1 = _; rw [o_bv64_ushr i.val 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s29] using h28
  have h29 := o_step_SLLI (by omega) (rfl : s29.pc = o_pcAt 29) (rfl : openingInstr 29 = .base (.SLLI .x7 .x6 (7#6)))
  let s30 := (s29.setReg .x7 (BitVec.ofNat 64 (128 * (i.val / 2)))).setPC (o_pcAt 30)
  have h29' : OpenRuns s29 1 1 s30 := by
    have hv : s29.getReg .x6 <<< (7#6 : BitVec 6).toNat = BitVec.ofNat 64 (128 * (i.val / 2)) := by
      change BitVec.ofNat 64 (i.val / 2) <<< 7 = _; rw [o_bv64_shl]; congr 1; omega
    simpa only [hv, s30] using h29
  have h30 := o_step_SLLI (by omega) (rfl : s30.pc = o_pcAt 30) (rfl : openingInstr 30 = .base (.SLLI .x10 .x6 (3#6)))
  let s31 := (s30.setReg .x10 (BitVec.ofNat 64 (8 * (i.val / 2)))).setPC (o_pcAt 31)
  have h30' : OpenRuns s30 1 1 s31 := by
    have hv : s30.getReg .x6 <<< (3#6 : BitVec 6).toNat = BitVec.ofNat 64 (8 * (i.val / 2)) := by
      change BitVec.ofNat 64 (i.val / 2) <<< 3 = _; rw [o_bv64_shl]; congr 1; omega
    simpa only [hv, s31] using h30
  have h31 := o_step_SUB (by omega) (rfl : s31.pc = o_pcAt 31) (rfl : openingInstr 31 = .base (.SUB .x7 .x7 .x10))
  let s32 := (s31.setReg .x7 (BitVec.ofNat 64 (120 * (i.val / 2)))).setPC (o_pcAt 32)
  have h31' : OpenRuns s31 1 1 s32 := by
    have hv : s31.getReg .x7 - s31.getReg .x10 = BitVec.ofNat 64 (120 * (i.val / 2)) := by
      change BitVec.ofNat 64 (128 * (i.val / 2)) - BitVec.ofNat 64 (8 * (i.val / 2)) = _
      rw [o_bv64_ofNat_sub _ _ (by omega)]; congr 1; omega
    simpa only [hv, s32] using h31
  have h32 := o_step_ANDI (by omega) (rfl : s32.pc = o_pcAt 32) (rfl : openingInstr 32 = .base (.ANDI .x6 .x8 (1#12)))
  let s33 := (s32.setReg .x6 (BitVec.ofNat 64 (i.val % 2))).setPC (o_pcAt 33)
  have h32' : OpenRuns s32 1 1 s33 := by
    have hv : s32.getReg .x8 &&& signExtend12 (1#12) = BitVec.ofNat 64 (i.val % 2) := by
      change BitVec.ofNat 64 i.val &&& signExtend12 (1#12) = _; exact o_bv64_and1 i.val (by omega)
    simpa only [hv, s33] using h32
  have h33 := o_step_SLLI (by omega) (rfl : s33.pc = o_pcAt 33) (rfl : openingInstr 33 = .base (.SLLI .x6 .x6 (4#6)))
  let s34 := (s33.setReg .x6 (BitVec.ofNat 64 (16 * (i.val % 2)))).setPC (o_pcAt 34)
  have h33' : OpenRuns s33 1 1 s34 := by
    have hv : s33.getReg .x6 <<< (4#6 : BitVec 6).toNat = BitVec.ofNat 64 (16 * (i.val % 2)) := by
      change BitVec.ofNat 64 (i.val % 2) <<< 4 = _; rw [o_bv64_shl]; congr 1; omega
    simpa only [hv, s34] using h33
  have h34 := o_step_ADD (by omega) (rfl : s34.pc = o_pcAt 34) (rfl : openingInstr 34 = .base (.ADD .x7 .x7 .x6))
  let s35 := (s34.setReg .x7 (BitVec.ofNat 64 (120 * (i.val / 2) + 16 * (i.val % 2)))).setPC (o_pcAt 35)
  have h34' : OpenRuns s34 1 1 s35 := by
    have hv : s34.getReg .x7 + s34.getReg .x6 = BitVec.ofNat 64 (120 * (i.val / 2) + 16 * (i.val % 2)) := by
      change BitVec.ofNat 64 (120 * (i.val / 2)) + BitVec.ofNat 64 (16 * (i.val % 2)) = _; exact o_bv64_ofNat_add _ _
    simpa only [hv, s35] using h34
  have h35 := o_step_ADD (by omega) (rfl : s35.pc = o_pcAt 35) (rfl : openingInstr 35 = .base (.ADD .x10 .x18 .x7))
  let s36 := (s35.setReg .x10 (BitVec.ofNat 64 (4294971424 + saltOff i))).setPC (o_pcAt 36)
  have h35' : OpenRuns s35 1 1 s36 := by
    have hr18 : s35.getReg .x18 = BitVec.ofNat 64 (4294971424 + (rowOff + 40)) := inv.rx18
    have hv : s35.getReg .x18 + s35.getReg .x7 = BitVec.ofNat 64 (4294971424 + saltOff i) := by
      rw [hr18]; change BitVec.ofNat 64 _ + BitVec.ofNat 64 _ = _
      rw [o_bv64_ofNat_add, Nat.add_assoc, o_saltOff_formula i]
    simpa only [hv, s36] using h35
  have hsalt_bd : saltOff i + 24 ≤ 2080374784 := by
    have h := saltOff_add_24_le i; rw [trapdoorBytes_eq] at h; exact h
  let fwdS := fwdBytes ++ bitsToBytes (tdSalt trapdoor i) 24
  obtain ⟨s37, hr_salt, hpc37, hreg37, hro37, hw37, ht37, hcap37⟩ :=
    o_call_emit24 (s := s36) (callIdx := 36) (srcOff := saltOff i) (jOff := 296#21)
      (fwdBytes := fwdBytes) (chunk := bitsToBytes (tdSalt trapdoor i) 24) (tails := tails)
      (by omega) rfl (by decide) rfl rfl (o_saltOff_align8 i) hsalt_bd (by omega) (by omega)
      inv.ro inv.writer.of_eq inv.tail.of_eq (bitsToBytes_length _ 24) (o_chunk_tdSalt trapdoor i)
  have hrunA : OpenRuns s 30 30 s37 :=
    ((((((((h27'.trans h28').trans h29').trans h30').trans h31').trans h32').trans h33').trans h34').trans h35').trans hr_salt
  have hinv37 : OpenPosInv trapdoor positions t fwdS tails s37 :=
    OpenPosInv.after_sub
      ⟨inv.rx9, inv.rx18, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27, inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap16⟩
      (fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (rw [hreg37] <;> first | rfl | decide))
      hro37 hw37 ht37 hcap37
  have hx8_37 : s37.getReg .x8 = BitVec.ofNat 64 i.val := by
    rw [hreg37 .x8 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  -- Part B (`37..47`): `x22 = heapIdx 0 i`, L0 (`emit32`) + L1 (`emit32`) (63 steps)
  have h37 := o_step_ADD (by omega) hpc37 (rfl : openingInstr 37 = .base (.ADD .x22 .x20 .x8))
  let s38 := (s37.setReg .x22 (BitVec.ofNat 64 (heapIdx 0 (i.val >>> 0)))).setPC (o_pcAt 38)
  have h37' : OpenRuns s37 1 1 s38 := by
    have hv : s37.getReg .x20 + s37.getReg .x8 = BitVec.ofNat 64 (heapIdx 0 (i.val >>> 0)) := by
      rw [hinv37.rx20, hx8_37, o_bv64_ofNat_add]; rfl
    simpa only [hv, s38] using h37
  -- L0 (`38..42`)
  obtain ⟨hr_a0, hpc41, hx10_41, hreg41, hbyte41, hmem41⟩ :=
    o_sib_addr_steps (s := s38) (base := 38) (l := 0) (i := i) (by omega) (by omega) rfl rfl rfl rfl hinv37.rx9 rfl
  set s41 := _
  have hro41 : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s41 :=
    fun a h1 h2 => by rw [hmem41]; exact hinv37.ro a h1 h2
  have hbd_l0 : 32 * heapIdx 0 ((i.val >>> 0) ^^^ 1) + 32 ≤ 2080374784 := by
    have hlt := heapIdx_lt 0 _ (by omega) (shiftRight_xor_one_lt i 0 (by omega)); omega
  let fwd0 := fwdS ++ bitsToBytes (tdNode trapdoor 0 ((i.val >>> 0) ^^^ 1)) 32
  obtain ⟨s42, hr_c0, hpc42, hreg42, hro42, hw42, ht42, hcap42⟩ :=
    o_call_emit32 (s := s41) (callIdx := 41) (srcOff := 32 * heapIdx 0 ((i.val >>> 0) ^^^ 1)) (jOff := 356#21)
      (fwdBytes := fwdS) (chunk := bitsToBytes (tdNode trapdoor 0 ((i.val >>> 0) ^^^ 1)) 32) (tails := tails)
      (by omega) rfl (by decide) hpc41 hx10_41 (by omega) hbd_l0
      (by simp only [fwdS, List.length_append, bitsToBytes_length]; omega) (by omega)
      hro41 (hinv37.writer.of_eq (h25 := hreg41 .x25 (by decide) (by decide))
        (h13 := hreg41 .x13 (by decide) (by decide)) (h14 := hreg41 .x14 (by decide) (by decide))
        (h12 := hreg41 .x12 (by decide) (by decide)) (hmem := hbyte41))
      (hinv37.tail.of_eq (h31 := hreg41 .x31 (by decide) (by decide))
        (h15 := hreg41 .x15 (by decide) (by decide)) (h16 := hreg41 .x16 (by decide) (by decide))
        (h17 := hreg41 .x17 (by decide) (by decide)) (hmem := hbyte41))
      (bitsToBytes_length _ 32) (fun j hj => o_chunk_tdNode trapdoor 0 _ 32 j (by omega) hj)
  have h42 := o_step_SRLI (by omega) hpc42 (rfl : openingInstr 42 = .base (.SRLI .x22 .x22 (1#6)))
  let s43 := (s42.setReg .x22 (BitVec.ofNat 64 (heapIdx 1 (i.val >>> 1)))).setPC (o_pcAt 43)
  have h42' : OpenRuns s42 1 1 s43 := by
    have hr22 : s42.getReg .x22 = BitVec.ofNat 64 (heapIdx 0 (i.val >>> 0)) := by
      rw [hreg42 .x22 (by decide) (by decide) (by decide) (by decide) (by decide),
          hreg41 .x22 (by decide) (by decide)]; rfl
    have hlt0 : heapIdx 0 (i.val >>> 0) < 2 ^ 64 := by
      have := heapIdx_lt 0 (i.val >>> 0) (by omega) (by unfold levelSize; simpa using hi_lt); omega
    have hv : s42.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (heapIdx 1 (i.val >>> 1)) := by
      rw [hr22]; change BitVec.ofNat 64 _ >>> 1 = _
      rw [o_bv64_ushr _ 1 hlt0, o_heapIdx_shr1 0 _ (by omega)]; rfl
    simpa only [hv, s43] using h42
  have hinv43 : OpenPosInv trapdoor positions t fwd0 tails s43 :=
    OpenPosInv.after_sub hinv37
      (fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · simp only [s43, MachineState.getReg_setPC]
          rw [o_getReg_setReg_ne, hreg42, hreg41] <;> first | rfl | decide)
      hro42 hw42.of_eq ht42.of_eq (fun q hq => (hcap42 q hq).trans (hbyte41 _))
  -- L1 (`43..47`)
  obtain ⟨hr_a1, hpc46, hx10_46, hreg46, hbyte46, hmem46⟩ :=
    o_sib_addr_steps (s := s43) (base := 43) (l := 1) (i := i) (by omega) (by omega) rfl rfl rfl rfl hinv43.rx9 rfl
  set s46 := _
  have hro46 : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s46 :=
    fun a h1 h2 => by rw [hmem46]; exact hinv43.ro a h1 h2
  have hbd_l1 : 32 * heapIdx 1 ((i.val >>> 1) ^^^ 1) + 32 ≤ 2080374784 := by
    have hlt := heapIdx_lt 1 _ (by omega) (shiftRight_xor_one_lt i 1 (by omega)); omega
  let fwd1 := fwd0 ++ bitsToBytes (tdNode trapdoor 1 ((i.val >>> 1) ^^^ 1)) 32
  obtain ⟨s47, hr_c1, hpc47, hreg47, hro47, hw47, ht47, hcap47⟩ :=
    o_call_emit32 (s := s46) (callIdx := 46) (srcOff := 32 * heapIdx 1 ((i.val >>> 1) ^^^ 1)) (jOff := 336#21)
      (fwdBytes := fwd0) (chunk := bitsToBytes (tdNode trapdoor 1 ((i.val >>> 1) ^^^ 1)) 32) (tails := tails)
      (by omega) rfl (by decide) hpc46 hx10_46 (by omega) hbd_l1
      (by simp only [fwd0, fwdS, List.length_append, bitsToBytes_length]; omega) (by omega)
      hro46 (hinv43.writer.of_eq (h25 := hreg46 .x25 (by decide) (by decide))
        (h13 := hreg46 .x13 (by decide) (by decide)) (h14 := hreg46 .x14 (by decide) (by decide))
        (h12 := hreg46 .x12 (by decide) (by decide)) (hmem := hbyte46))
      (hinv43.tail.of_eq (h31 := hreg46 .x31 (by decide) (by decide))
        (h15 := hreg46 .x15 (by decide) (by decide)) (h16 := hreg46 .x16 (by decide) (by decide))
        (h17 := hreg46 .x17 (by decide) (by decide)) (hmem := hbyte46))
      (bitsToBytes_length _ 32) (fun j hj => o_chunk_tdNode trapdoor 1 _ 32 j (by omega) hj)
  have h47 := o_step_SRLI (by omega) hpc47 (rfl : openingInstr 47 = .base (.SRLI .x22 .x22 (1#6)))
  let s48 := (s47.setReg .x22 (BitVec.ofNat 64 (heapIdx 2 (i.val >>> 2)))).setPC (o_pcAt 48)
  have h47' : OpenRuns s47 1 1 s48 := by
    have hr22 : s47.getReg .x22 = BitVec.ofNat 64 (heapIdx 1 (i.val >>> 1)) := by
      rw [hreg47 .x22 (by decide) (by decide) (by decide) (by decide) (by decide),
          hreg46 .x22 (by decide) (by decide)]; rfl
    have hlt1 : heapIdx 1 (i.val >>> 1) < 2 ^ 64 := by
      have hsh1 : i.val >>> 1 < levelSize 1 := by rw [Nat.shiftRight_eq_div_pow, levelSize_1]; omega
      have := heapIdx_lt 1 (i.val >>> 1) (by omega) hsh1; omega
    have hv : s47.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (heapIdx 2 (i.val >>> 2)) := by
      rw [hr22]; change BitVec.ofNat 64 _ >>> 1 = _
      rw [o_bv64_ushr _ 1 hlt1, o_heapIdx_shr1 1 _ (by omega)]
      congr 2
    simpa only [hv, s48] using h47
  have hinv48 : OpenPosInv trapdoor positions t fwd1 tails s48 :=
    OpenPosInv.after_sub hinv43
      (fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        · simp only [s48, MachineState.getReg_setPC]
          rw [o_getReg_setReg_ne, hreg47, hreg46] <;> first | rfl | decide)
      hro47 hw47.of_eq ht47.of_eq (fun q hq => (hcap47 q hq).trans (hbyte46 _))
  have hrunB : OpenRuns s37 63 63 s48 :=
    (((((h37'.trans hr_a0).trans hr_c0).trans h42').trans hr_a1).trans hr_c1).trans h47'
  -- Part C (`48..55`): `l25_sib_loop` (4 iterations: `l = 2, 3, 4, 5`)
  have h48 := o_step_ADDI (by omega) (rfl : s48.pc = o_pcAt 48) (rfl : openingInstr 48 = .base (.ADDI .x23 .x0 (4#12)))
  let s49 := (s48.setReg .x23 (BitVec.ofNat 64 4)).setPC (o_pcAt 49)
  have h48' : OpenRuns s48 1 1 s49 := by
    have hv : s48.getReg .x0 + signExtend12 (4#12) = BitVec.ofNat 64 4 := by
      change (0#64 : Word) + signExtend12 (4#12) = _; decide
    simpa only [hv, s49] using h48
  have hinv49 : OpenPosInv trapdoor positions t fwd1 tails s49 :=
    OpenPosInv.after_sub hinv48 (fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      hinv48.ro hinv48.writer.of_eq hinv48.tail.of_eq (fun _ _ => rfl)
  let l25Chunk (m : Nat) : List Byte :=
    (List.range m).flatMap fun k => bitsToBytes (tdNode trapdoor (2 + k) ((i.val >>> (2 + k)) ^^^ 1)) 30
  have hl25_len : ∀ m, (l25Chunk m).length = 30 * m := by
    intro m; induction m with
    | zero => simp [l25Chunk]
    | succ m ih =>
      simp only [l25Chunk, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.length_append, bitsToBytes_length] at ih ⊢; omega
  have hl25 : ∀ m ≤ 4,
      let fwdM := fwd1 ++ l25Chunk m
      let stM := 21 * m + 5 * (fwdM.length / 8 - fwd1.length / 8)
      ∃ sm, OpenRuns s49 stM stM sm ∧
        sm.pc = (if m < 4 then o_pcAt 49 else o_pcAt 56) ∧
        sm.getReg .x22 = BitVec.ofNat 64 (heapIdx (2 + m) (i.val >>> (2 + m))) ∧
        sm.getReg .x23 = BitVec.ofNat 64 (4 - m) ∧
        OpenPosInv trapdoor positions t fwdM tails sm := by
    intro m hm; induction m with
    | zero =>
      exact ⟨s49, by simpa [l25Chunk] using OpenRuns.refl s49, rfl, rfl, rfl, by simpa [l25Chunk] using hinv49⟩
    | succ m ih =>
      obtain ⟨sm, hrm, hpcm, hx22m, hx23m, hinvm⟩ := ih (by omega)
      have hpcm' : sm.pc = o_pcAt 49 := by simpa only [show m < 4 by omega, ite_true] using hpcm
      set l := 2 + m
      obtain ⟨hr_am, hpc52, hx10_52, hreg52, hbyte52, hmem52⟩ :=
        o_sib_addr_steps (s := sm) (base := 49) (l := l) (i := i) (by omega) (by omega) rfl rfl rfl hpcm' hinvm.rx9 hx22m
      set s52 := _
      have hro52 : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s52 :=
        fun a h1 h2 => by rw [hmem52]; exact hinvm.ro a h1 h2
      have hbd_lm : 32 * heapIdx l ((i.val >>> l) ^^^ 1) + 32 ≤ 2080374784 := by
        have hlt := heapIdx_lt l _ (by omega) (shiftRight_xor_one_lt i l (by omega)); omega
      let curM := fwd1 ++ l25Chunk m
      let ch := bitsToBytes (tdNode trapdoor l ((i.val >>> l) ^^^ 1)) 30
      have hcur_bd : curM.length + 30 ≤ proofCap := by
        simp only [curM, fwd1, fwd0, fwdS, List.length_append, bitsToBytes_length, hl25_len]; omega
      obtain ⟨s53, hr_cm, hpc53, hreg53, hro53, hw53, ht53, hcap53⟩ :=
        o_call_emit30 (s := s52) (callIdx := 52) (srcOff := 32 * heapIdx l ((i.val >>> l) ^^^ 1)) (jOff := 416#21)
          (fwdBytes := curM) (chunk := ch) (tails := tails)
          (by omega) rfl (by decide) hpc52 hx10_52 (by omega) hbd_lm hcur_bd (by omega)
          hro52 (hinvm.writer.of_eq (h25 := hreg52 .x25 (by decide) (by decide))
            (h13 := hreg52 .x13 (by decide) (by decide)) (h14 := hreg52 .x14 (by decide) (by decide))
            (h12 := hreg52 .x12 (by decide) (by decide)) (hmem := hbyte52))
          (hinvm.tail.of_eq (h31 := hreg52 .x31 (by decide) (by decide))
            (h15 := hreg52 .x15 (by decide) (by decide)) (h16 := hreg52 .x16 (by decide) (by decide))
            (h17 := hreg52 .x17 (by decide) (by decide)) (hmem := hbyte52))
          (bitsToBytes_length _ 30) (fun j hj => o_chunk_tdNode trapdoor l _ 30 j (by omega) hj)
      -- 53: SRLI x22, x22, 1; 54: ADDI x23, x23, -1; 55: BNE x23, x0, -24 (-> 49)
      have h53 := o_step_SRLI (by omega) hpc53 (rfl : openingInstr 53 = .base (.SRLI .x22 .x22 (1#6)))
      let s54 := (s53.setReg .x22 (BitVec.ofNat 64 (heapIdx (2 + (m + 1)) (i.val >>> (2 + (m + 1)))))).setPC (o_pcAt 54)
      have h53' : OpenRuns s53 1 1 s54 := by
        have hr22 : s53.getReg .x22 = BitVec.ofNat 64 (heapIdx l (i.val >>> l)) := by
          rw [hreg53 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg52 .x22 (by decide) (by decide)]; exact hx22m
        have hshl : i.val >>> l < levelSize l := by
          rw [Nat.shiftRight_eq_div_pow]; unfold levelSize
          rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2)), ← Nat.pow_add,
            show 24 - l + l = 24 by omega]; exact hi_lt
        have hltl : heapIdx l (i.val >>> l) < 2 ^ 64 := by have := heapIdx_lt l _ (by omega) hshl; omega
        have hv : s53.getReg .x22 >>> (1#6 : BitVec 6).toNat =
            BitVec.ofNat 64 (heapIdx (2 + (m + 1)) (i.val >>> (2 + (m + 1)))) := by
          rw [hr22]; change BitVec.ofNat 64 _ >>> 1 = _
          rw [o_bv64_ushr _ 1 hltl, o_heapIdx_shr1 l _ (by omega)]
          have hl1 : l + 1 = 2 + (m + 1) := by omega
          rw [hl1]; congr 2
        simpa only [hv, s54] using h53
      have h54 := o_step_ADDI (by omega) (rfl : s54.pc = o_pcAt 54) (rfl : openingInstr 54 = .base (.ADDI .x23 .x23 (4095#12)))
      let s55 := (s54.setReg .x23 (BitVec.ofNat 64 (4 - (m + 1)))).setPC (o_pcAt 55)
      have h54' : OpenRuns s54 1 1 s55 := by
        have hr23 : s54.getReg .x23 = BitVec.ofNat 64 ((4 - (m + 1)) + 1) := by
          simp only [s54, MachineState.getReg_setPC, o_getReg_setReg_ne .x22 .x23 (by decide)]
          rw [hreg53 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg52 .x23 (by decide) (by decide), hx23m]; congr 1; omega
        rw [hr23, o_bv64_add_neg1] at h54; exact h54
      have hchunk_succ : fwd1 ++ l25Chunk (m + 1) = curM ++ ch := by
        simp only [curM, ch, l, l25Chunk, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
      have hinv55 : OpenPosInv trapdoor positions t (fwd1 ++ l25Chunk (m + 1)) tails s55 :=
        OpenPosInv.after_sub hinvm
          (fun r hr => by
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            · simp only [s55, MachineState.getReg_setPC]
              rw [o_getReg_setReg_ne]
              · simp only [s54, MachineState.getReg_setPC]
                rw [o_getReg_setReg_ne, hreg53, hreg52] <;> first | rfl | decide
              · decide)
          hro53 (hw53.castList hchunk_succ.symm).of_eq ht53.of_eq (fun q hq => (hcap53 q hq).trans (hbyte52 _))
      have hsteps_m : (21 * m + 5 * (curM.length / 8 - fwd1.length / 8)) + 3 +
          (15 + 5 * ((curM ++ ch).length / 8 - curM.length / 8)) + 1 + 1 + 1 =
          21 * (m + 1) + 5 * ((fwd1 ++ l25Chunk (m + 1)).length / 8 - fwd1.length / 8) := by
        rw [hchunk_succ]
        have hle1 : fwd1.length / 8 ≤ curM.length / 8 := Nat.div_le_div_right (by simp [curM])
        have hle2 : curM.length / 8 ≤ (curM ++ ch).length / 8 := Nat.div_le_div_right (by simp)
        omega
      by_cases hmore : m + 1 < 4
      · have h55 := o_step_BNE_taken (by omega) (rfl : s55.pc = o_pcAt 55)
          (rfl : openingInstr 55 = .base (.BNE .x23 .x0 (8168#13)))
          (by change BitVec.ofNat 64 (4 - (m + 1)) ≠ BitVec.ofNat 64 0
              exact o_bv64_ofNat_ne (by omega) (by decide) (by omega))
          (by decide : o_pcAt 55 + signExtend13 (8168#13) = o_pcAt 49)
        refine ⟨s55.setPC (o_pcAt 49), ?_, by rw [if_pos hmore]; rfl, rfl, rfl,
          ⟨hinv55.rx9, hinv55.rx18, hinv55.rx20, hinv55.rx21, hinv55.rx24, hinv55.rx26, hinv55.rx27,
           hinv55.ro, hinv55.writer.of_eq, hinv55.tail.of_eq, hinv55.cap16⟩⟩
        rw [← hsteps_m]; exact ((((hrm.trans hr_am).trans hr_cm).trans h53').trans h54').trans h55
      · have hdone : 4 - (m + 1) = 0 := by omega
        have h55 := o_step_BNE_not_taken (by omega) (rfl : s55.pc = o_pcAt 55)
          (rfl : openingInstr 55 = .base (.BNE .x23 .x0 (8168#13)))
          (by change BitVec.ofNat 64 (4 - (m + 1)) = 0#64; rw [hdone])
        refine ⟨s55.setPC (o_pcAt 56), ?_, by rw [if_neg hmore]; rfl, rfl, rfl,
          ⟨hinv55.rx9, hinv55.rx18, hinv55.rx20, hinv55.rx21, hinv55.rx24, hinv55.rx26, hinv55.rx27,
           hinv55.ro, hinv55.writer.of_eq, hinv55.tail.of_eq, hinv55.cap16⟩⟩
        rw [← hsteps_m]; exact ((((hrm.trans hr_am).trans hr_cm).trans h53').trans h54').trans h55
  obtain ⟨s56, hr_l25, hpc56, hx22_56, _, hinv56⟩ := hl25 4 (le_refl _)
  have hpc56' : s56.pc = o_pcAt 56 := by simpa only [Nat.lt_irrefl, ite_false] using hpc56
  -- Part D (`56..63`): `l615_sib_loop` (10 iterations: `l = 6..15`)
  have h56 := o_step_ADDI (by omega) hpc56' (rfl : openingInstr 56 = .base (.ADDI .x23 .x0 (10#12)))
  let s57 := (s56.setReg .x23 (BitVec.ofNat 64 10)).setPC (o_pcAt 57)
  have h56' : OpenRuns s56 1 1 s57 := by
    have hv : s56.getReg .x0 + signExtend12 (10#12) = BitVec.ofNat 64 10 := by
      change (0#64 : Word) + signExtend12 (10#12) = _; decide
    simpa only [hv, s57] using h56
  let fwd25 := fwd1 ++ l25Chunk 4
  have hinv57 : OpenPosInv trapdoor positions t fwd25 tails s57 :=
    OpenPosInv.after_sub hinv56 (fun r hr => by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      hinv56.ro hinv56.writer.of_eq hinv56.tail.of_eq (fun _ _ => rfl)
  let l615Chunk (m : Nat) : List Byte :=
    (List.range m).flatMap fun k => bitsToBytes (tdNode trapdoor (6 + k) ((i.val >>> (6 + k)) ^^^ 1)) 29
  let l615Tails (m : Nat) : List (BitVec 6) :=
    (List.range m).map fun k => tail6 (tdNode trapdoor (6 + k) ((i.val >>> (6 + k)) ^^^ 1))
  have hl615_len : ∀ m, (l615Chunk m).length = 29 * m := by
    intro m; induction m with
    | zero => simp [l615Chunk]
    | succ m ih =>
      simp only [l615Chunk, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.length_append, bitsToBytes_length] at ih ⊢; omega
  have hl615_tlen : ∀ m, (l615Tails m).length = m := fun m => by simp [l615Tails]
  have hl615 : ∀ m ≤ 10,
      let fwdM := fwd25 ++ l615Chunk m
      let tailsM := tails ++ l615Tails m
      let stM := 28 * m + 5 * (fwdM.length / 8 - fwd25.length / 8) +
        4 * ((tailsM.foldl pack6Step ([], 0, 0)).1.length - (tails.foldl pack6Step ([], 0, 0)).1.length)
      ∃ sm, OpenRuns s57 stM stM sm ∧
        sm.pc = (if m < 10 then o_pcAt 57 else o_pcAt 64) ∧
        sm.getReg .x22 = BitVec.ofNat 64 (heapIdx (6 + m) (i.val >>> (6 + m))) ∧
        sm.getReg .x23 = BitVec.ofNat 64 (10 - m) ∧
        OpenPosInv trapdoor positions t fwdM tailsM sm := by
    intro m hm; induction m with
    | zero =>
      exact ⟨s57, by simpa [l615Chunk, l615Tails] using OpenRuns.refl s57, rfl,
        by simpa only [s57, MachineState.getReg_setPC, o_getReg_setReg_ne .x23 .x22 (by decide)] using hx22_56,
        rfl, by simpa [l615Chunk, l615Tails] using hinv57⟩
    | succ m ih =>
      obtain ⟨sm, hrm, hpcm, hx22m, hx23m, hinvm⟩ := ih (by omega)
      have hpcm' : sm.pc = o_pcAt 57 := by simpa only [show m < 10 by omega, ite_true] using hpcm
      set l := 6 + m
      obtain ⟨hr_am, hpc60, hx10_60, hreg60, hbyte60, hmem60⟩ :=
        o_sib_addr_steps (s := sm) (base := 57) (l := l) (i := i) (by omega) (by omega) rfl rfl rfl hpcm' hinvm.rx9 hx22m
      set s60 := _
      have hro60 : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s60 :=
        fun a h1 h2 => by rw [hmem60]; exact hinvm.ro a h1 h2
      have hbd_lm : 32 * heapIdx l ((i.val >>> l) ^^^ 1) + 32 ≤ 2080374784 := by
        have hlt := heapIdx_lt l _ (by omega) (shiftRight_xor_one_lt i l (by omega)); omega
      let curM := fwd25 ++ l615Chunk m
      let curT := tails ++ l615Tails m
      let dSib := tdNode trapdoor l ((i.val >>> l) ^^^ 1)
      let ch := bitsToBytes dSib 29
      have hcur_bd : curM.length + 29 ≤ proofCap := by
        simp only [curM, fwd25, fwd1, fwd0, fwdS, List.length_append, bitsToBytes_length, hl25_len, hl615_len]; omega
      have hcurT_bd : curT.length < 200000000 := by simp only [curT, List.length_append, hl615_tlen]; omega
      have hbyte29 : trapdoor.extractLsb' (8 * (32 * heapIdx l ((i.val >>> l) ^^^ 1) + 29)) 8 =
          dSib.extractLsb' (8 * 29) 8 := by
        unfold dSib tdNode
        rw [o_extractLsb'_extractLsb' trapdoor (8 * (32 * heapIdx l ((i.val >>> l) ^^^ 1))) 256 (8 * 29) 8 (by omega)]
        exact congrArg (fun off => trapdoor.extractLsb' off 8) (by omega)
      obtain ⟨s61, hr_cm, hpc61, hreg61, hro61, hw61, ht61, hcap61⟩ :=
        o_call_emit29_tail6 (s := s60) (callIdx := 60) (srcOff := 32 * heapIdx l ((i.val >>> l) ^^^ 1)) (jOff := 520#21)
          (fwdBytes := curM) (chunk := ch) (tails := curT) (d := dSib)
          (by omega) rfl (by decide) hpc60 hx10_60 (by omega) hbd_lm hcur_bd hcurT_bd
          hro60 (hinvm.writer.of_eq (h25 := hreg60 .x25 (by decide) (by decide))
            (h13 := hreg60 .x13 (by decide) (by decide)) (h14 := hreg60 .x14 (by decide) (by decide))
            (h12 := hreg60 .x12 (by decide) (by decide)) (hmem := hbyte60))
          (hinvm.tail.of_eq (h31 := hreg60 .x31 (by decide) (by decide))
            (h15 := hreg60 .x15 (by decide) (by decide)) (h16 := hreg60 .x16 (by decide) (by decide))
            (h17 := hreg60 .x17 (by decide) (by decide)) (hmem := hbyte60))
          (bitsToBytes_length _ 29) (fun j hj => o_chunk_tdNode trapdoor l _ 29 j (by omega) hj) hbyte29
      have h61 := o_step_SRLI (by omega) hpc61 (rfl : openingInstr 61 = .base (.SRLI .x22 .x22 (1#6)))
      let s62 := (s61.setReg .x22 (BitVec.ofNat 64 (heapIdx (6 + (m + 1)) (i.val >>> (6 + (m + 1)))))).setPC (o_pcAt 62)
      have h61' : OpenRuns s61 1 1 s62 := by
        have hr22 : s61.getReg .x22 = BitVec.ofNat 64 (heapIdx l (i.val >>> l)) := by
          rw [hreg61 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg60 .x22 (by decide) (by decide)]; exact hx22m
        have hshl : i.val >>> l < levelSize l := by
          rw [Nat.shiftRight_eq_div_pow]; unfold levelSize
          rw [Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide : 0 < 2)), ← Nat.pow_add,
            show 24 - l + l = 24 by omega]; exact hi_lt
        have hltl : heapIdx l (i.val >>> l) < 2 ^ 64 := by have := heapIdx_lt l _ (by omega) hshl; omega
        have hv : s61.getReg .x22 >>> (1#6 : BitVec 6).toNat =
            BitVec.ofNat 64 (heapIdx (6 + (m + 1)) (i.val >>> (6 + (m + 1)))) := by
          rw [hr22]; change BitVec.ofNat 64 _ >>> 1 = _
          rw [o_bv64_ushr _ 1 hltl, o_heapIdx_shr1 l _ (by omega)]
          have hl1 : l + 1 = 6 + (m + 1) := by omega
          rw [hl1]; congr 2
        simpa only [hv, s62] using h61
      have h62 := o_step_ADDI (by omega) (rfl : s62.pc = o_pcAt 62) (rfl : openingInstr 62 = .base (.ADDI .x23 .x23 (4095#12)))
      let s63 := (s62.setReg .x23 (BitVec.ofNat 64 (10 - (m + 1)))).setPC (o_pcAt 63)
      have h62' : OpenRuns s62 1 1 s63 := by
        have hr23 : s62.getReg .x23 = BitVec.ofNat 64 ((10 - (m + 1)) + 1) := by
          simp only [s62, MachineState.getReg_setPC, o_getReg_setReg_ne .x22 .x23 (by decide)]
          rw [hreg61 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide),
              hreg60 .x23 (by decide) (by decide), hx23m]; congr 1; omega
        rw [hr23, o_bv64_add_neg1] at h62; exact h62
      have hchunk_succ : fwd25 ++ l615Chunk (m + 1) = curM ++ ch := by
        simp only [curM, ch, dSib, l, l615Chunk, List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
      have htail_succ : tails ++ l615Tails (m + 1) = curT ++ [tail6 dSib] := by
        simp only [curT, dSib, l, l615Tails, List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
      have hinv63 : OpenPosInv trapdoor positions t (fwd25 ++ l615Chunk (m + 1)) (tails ++ l615Tails (m + 1)) s63 :=
        OpenPosInv.after_sub hinvm
          (fun r hr => by
            rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            · simp only [s63, MachineState.getReg_setPC]
              rw [o_getReg_setReg_ne]
              · simp only [s62, MachineState.getReg_setPC]
                rw [o_getReg_setReg_ne, hreg61, hreg60] <;> first | rfl | decide
              · decide)
          hro61 (hw61.castList hchunk_succ.symm).of_eq (htail_succ.symm ▸ ht61.of_eq)
          (fun q hq => (hcap61 q hq).trans (hbyte60 _))
      have hsteps_m : (28 * m + 5 * (curM.length / 8 - fwd25.length / 8) +
            4 * ((curT.foldl pack6Step ([], 0, 0)).1.length - (tails.foldl pack6Step ([], 0, 0)).1.length)) + 3 +
          (22 + 5 * ((curM ++ ch).length / 8 - curM.length / 8) +
            4 * (((curT ++ [tail6 dSib]).foldl pack6Step ([], 0, 0)).1.length -
              (curT.foldl pack6Step ([], 0, 0)).1.length)) + 1 + 1 + 1 =
          28 * (m + 1) + 5 * ((fwd25 ++ l615Chunk (m + 1)).length / 8 - fwd25.length / 8) +
            4 * (((tails ++ l615Tails (m + 1)).foldl pack6Step ([], 0, 0)).1.length -
              (tails.foldl pack6Step ([], 0, 0)).1.length) := by
        rw [hchunk_succ, htail_succ]
        have hle1 : fwd25.length / 8 ≤ curM.length / 8 := Nat.div_le_div_right (by simp [curM])
        have hle2 : curM.length / 8 ≤ (curM ++ ch).length / 8 := Nat.div_le_div_right (by simp)
        have hbt0 := o_pack6_foldl_bounds tails
        have hbt1 := o_pack6_foldl_bounds curT
        have hbt2 := o_pack6_foldl_bounds (curT ++ [tail6 dSib])
        have htl1 : tails.length ≤ curT.length := by simp [curT]
        have htl2 : curT.length ≤ (curT ++ [tail6 dSib]).length := by simp
        have hat1 : (tails.foldl pack6Step ([], 0, 0)).1.length ≤ (curT.foldl pack6Step ([], 0, 0)).1.length := by omega
        have hat2 : (curT.foldl pack6Step ([], 0, 0)).1.length ≤
            ((curT ++ [tail6 dSib]).foldl pack6Step ([], 0, 0)).1.length := by omega
        omega
      by_cases hmore : m + 1 < 10
      · have h63 := o_step_BNE_taken (by omega) (rfl : s63.pc = o_pcAt 63)
          (rfl : openingInstr 63 = .base (.BNE .x23 .x0 (8168#13)))
          (by change BitVec.ofNat 64 (10 - (m + 1)) ≠ BitVec.ofNat 64 0
              exact o_bv64_ofNat_ne (by omega) (by decide) (by omega))
          (by decide : o_pcAt 63 + signExtend13 (8168#13) = o_pcAt 57)
        refine ⟨s63.setPC (o_pcAt 57), ?_, by rw [if_pos hmore]; rfl, rfl, rfl,
          ⟨hinv63.rx9, hinv63.rx18, hinv63.rx20, hinv63.rx21, hinv63.rx24, hinv63.rx26, hinv63.rx27,
           hinv63.ro, hinv63.writer.of_eq, hinv63.tail.of_eq, hinv63.cap16⟩⟩
        rw [← hsteps_m]; exact ((((hrm.trans hr_am).trans hr_cm).trans h61').trans h62').trans h63
      · have hdone : 10 - (m + 1) = 0 := by omega
        have h63 := o_step_BNE_not_taken (by omega) (rfl : s63.pc = o_pcAt 63)
          (rfl : openingInstr 63 = .base (.BNE .x23 .x0 (8168#13)))
          (by change BitVec.ofNat 64 (10 - (m + 1)) = 0#64; rw [hdone])
        refine ⟨s63.setPC (o_pcAt 64), ?_, by rw [if_neg hmore]; rfl, rfl, rfl,
          ⟨hinv63.rx9, hinv63.rx18, hinv63.rx20, hinv63.rx21, hinv63.rx24, hinv63.rx26, hinv63.rx27,
           hinv63.ro, hinv63.writer.of_eq, hinv63.tail.of_eq, hinv63.cap16⟩⟩
        rw [← hsteps_m]; exact ((((hrm.trans hr_am).trans hr_cm).trans h61').trans h62').trans h63
  obtain ⟨s64, hr_l615, hpc64, hx22_64, _, hinv64⟩ := hl615 10 (le_refl _)
  have hpc64' : s64.pc = o_pcAt 64 := by simpa only [Nat.lt_irrefl, ite_false] using hpc64
  -- Match `fwd25 ++ l615Chunk 10` = `fwd'` and `tails ++ l615Tails 10` = `tails'`
  have hfwd_eq : fwd25 ++ l615Chunk 10 = fwd' := by
    simp only [fwd', recordFwd, pathFwd, fwd25, fwd1, fwd0, fwdS, l25Chunk, l615Chunk]
    simp only [List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_singleton,
      List.flatMap_nil, List.nil_append, List.append_assoc]
    rfl
  have htails_eq : tails ++ l615Tails 10 = tails' := rfl
  -- Part E (`64..69`): mark `4096 + (256 + (i >>> 16)) = 1`, advance `x24`/`x27`, branch (6 steps)
  have hc_lt : i.val >>> 16 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hhi16 : heapIdx 16 (i.val >>> 16) = 256 + (i.val >>> 16) := rfl
  have h64 := o_step_ADD (by omega) hpc64' (rfl : openingInstr 64 = .base (.ADD .x6 .x21 .x22))
  let s65 := (s64.setReg .x6 (BitVec.ofNat 64 (4096 + 256 + (i.val >>> 16)))).setPC (o_pcAt 65)
  have h64' : OpenRuns s64 1 1 s65 := by
    have hv : s64.getReg .x21 + s64.getReg .x22 = BitVec.ofNat 64 (4096 + 256 + (i.val >>> 16)) := by
      rw [hinv64.rx21, hx22_64, hhi16, o_bv64_ofNat_add, Nat.add_assoc]
    simpa only [hv, s65] using h64
  have h65 := o_step_ADDI (by omega) (rfl : s65.pc = o_pcAt 65) (rfl : openingInstr 65 = .base (.ADDI .x7 .x0 (1#12)))
  let s66 := (s65.setReg .x7 1#64).setPC (o_pcAt 66)
  have h65' : OpenRuns s65 1 1 s66 := by
    have hv : s65.getReg .x0 + signExtend12 (1#12) = 1#64 := by change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s66] using h65
  have haddr66 : s66.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (4096 + 256 + (i.val >>> 16)) := by
    change BitVec.ofNat 64 _ + signExtend12 (0#12) = _; rw [hse0, o_bv64_ofNat_add, Nat.add_zero]
  have h66 := o_step_SB (by omega) (rfl : s66.pc = o_pcAt 66) (rfl : openingInstr 66 = .base (.SB .x6 .x7 (0#12)))
    (by rw [haddr66]; exact o_accessValid_ofNat _ 1 (by omega) (by omega))
  let s67 := (s66.setByte (BitVec.ofNat 64 (4096 + 256 + (i.val >>> 16))) 1#8).setPC (o_pcAt 67)
  have h66' : OpenRuns s66 1 1 s67 := by
    simpa only [haddr66, show (s66.getReg .x7).truncate 8 = 1#8 from rfl, s67] using h66
  have h67 := o_step_ADDI (by omega) (rfl : s67.pc = o_pcAt 67) (rfl : openingInstr 67 = .base (.ADDI .x24 .x24 (8#12)))
  let s68 := (s67.setReg .x24 (BitVec.ofNat 64 (6375346208 + 8 * (t + 1)))).setPC (o_pcAt 68)
  have h67' : OpenRuns s67 1 1 s68 := by
    have hr24 : s67.getReg .x24 = BitVec.ofNat 64 (6375346208 + 8 * t) := by
      simp only [s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
        o_getReg_setReg_ne .x7 .x24 (by decide), o_getReg_setReg_ne .x6 .x24 (by decide)]; exact hinv64.rx24
    have hv : s67.getReg .x24 + signExtend12 (8#12) = BitVec.ofNat 64 (6375346208 + 8 * (t + 1)) := by
      rw [hr24, hse8, o_bv64_ofNat_add]; congr 1
    simpa only [hv, s68] using h67
  have h68 := o_step_ADDI (by omega) (rfl : s68.pc = o_pcAt 68) (rfl : openingInstr 68 = .base (.ADDI .x27 .x27 (4095#12)))
  let s69 := (s68.setReg .x27 (BitVec.ofNat 64 (positions.card - (t + 1)))).setPC (o_pcAt 69)
  have h68' : OpenRuns s68 1 1 s69 := by
    have hr27 : s68.getReg .x27 = BitVec.ofNat 64 ((positions.card - (t + 1)) + 1) := by
      simp only [s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
        o_getReg_setReg_ne .x24 .x27 (by decide), o_getReg_setReg_ne .x7 .x27 (by decide),
        o_getReg_setReg_ne .x6 .x27 (by decide), hinv64.rx27]; congr 1; omega
    rw [hr27, o_bv64_add_neg1] at h68; exact h68
  have hro69 : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s69 := by
    intro a h1 h2
    change (s64.setByte (BitVec.ofNat 64 (4096 + 256 + (i.val >>> 16))) 1#8).getMem a = _
    exact o_readOnly_setByte_cap _ 1#8 hinv64.ro (by omega) (by omega) a h1 h2
  have hw69 : OpenWriterState s69 fwd' := by
    have hpc_eq : proofCap = 8480886496 := rfl
    have hflen : fwd'.length ≤ proofCap := by
      simp only [fwd', List.length_append, recordFwd_length]; omega
    have hw_sb := o_writerState_setByte_outside (4096 + 256 + (i.val >>> 16)) 1#8
      (hinv64.writer.castList hfwd_eq) hflen (by omega) (by omega)
    exact hw_sb.of_eq
      (h25 := by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x27 .x25 (by decide), o_getReg_setReg_ne .x24 .x25 (by decide),
          o_getReg_setReg_ne .x7 .x25 (by decide), o_getReg_setReg_ne .x6 .x25 (by decide)])
      (h13 := by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x27 .x13 (by decide), o_getReg_setReg_ne .x24 .x13 (by decide),
          o_getReg_setReg_ne .x7 .x13 (by decide), o_getReg_setReg_ne .x6 .x13 (by decide)])
      (h14 := by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x27 .x14 (by decide), o_getReg_setReg_ne .x24 .x14 (by decide),
          o_getReg_setReg_ne .x7 .x14 (by decide), o_getReg_setReg_ne .x6 .x14 (by decide)])
      (h12 := by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x27 .x12 (by decide), o_getReg_setReg_ne .x24 .x12 (by decide),
          o_getReg_setReg_ne .x7 .x12 (by decide), o_getReg_setReg_ne .x6 .x12 (by decide)])
      (hmem := fun a => by simp only [s69, s68, s67, s66, s65, o_getByte_setPC, o_getByte_setReg]; rfl)
  have ht69 : OpenTailState s69 tails' := by
    have htb : tailBufBase = 20000000000 := rfl
    have ht_sb := o_tailState_setByte_outside (4096 + 256 + (i.val >>> 16)) 1#8
      (htails_eq ▸ hinv64.tail) (by simp only [tails', List.length_append, recordTails_length]; omega) (by omega)
    exact ht_sb.of_eq
      (h31 := by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x27 .x31 (by decide), o_getReg_setReg_ne .x24 .x31 (by decide),
          o_getReg_setReg_ne .x7 .x31 (by decide), o_getReg_setReg_ne .x6 .x31 (by decide)])
      (h15 := by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x27 .x15 (by decide), o_getReg_setReg_ne .x24 .x15 (by decide),
          o_getReg_setReg_ne .x7 .x15 (by decide), o_getReg_setReg_ne .x6 .x15 (by decide)])
      (h16 := by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x27 .x16 (by decide), o_getReg_setReg_ne .x24 .x16 (by decide),
          o_getReg_setReg_ne .x7 .x16 (by decide), o_getReg_setReg_ne .x6 .x16 (by decide)])
      (h17 := by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
          o_getReg_setReg_ne .x27 .x17 (by decide), o_getReg_setReg_ne .x24 .x17 (by decide),
          o_getReg_setReg_ne .x7 .x17 (by decide), o_getReg_setReg_ne .x6 .x17 (by decide)])
      (hmem := fun a => by simp only [s69, s68, s67, s66, s65, o_getByte_setPC, o_getByte_setReg]; rfl)
  have hcap69 : ∀ c < 256, s69.getByte (BitVec.ofNat 64 (4096 + 256 + c)) =
      if o_capMark16Prefix positions (t + 1) c then 1#8 else 0#8 := by
    intro c hc
    have hmem_c : s69.getByte (BitVec.ofNat 64 (4096 + 256 + c)) =
        (s64.setByte (BitVec.ofNat 64 (4096 + 256 + (i.val >>> 16))) 1#8).getByte
          (BitVec.ofNat 64 (4096 + 256 + c)) := by
      simp only [s69, s68, s67, s66, s65, o_getByte_setPC, o_getByte_setReg]; rfl
    rw [hmem_c, set_byte_read]
    by_cases heq : c = i.val >>> 16
    · subst heq
      rw [if_pos rfl]
      have htr : o_capMark16Prefix positions (t + 1) (i.val >>> 16) = true := by
        unfold o_capMark16Prefix; rw [decide_eq_true_eq]
        exact ⟨t, by omega, by rw [hopen]⟩
      rw [htr]; rfl
    · rw [if_neg (o_bv64_ofNat_ne (by omega) (by omega) (by omega)), hinv64.cap16 c hc]
      have hiff : o_capMark16Prefix positions t c = o_capMark16Prefix positions (t + 1) c := by
        unfold o_capMark16Prefix
        congr 1; apply propext; constructor
        · rintro ⟨u, hu, he⟩; exact ⟨u, by omega, he⟩
        · rintro ⟨u, hu, he⟩
          by_cases hut : u = t
          · subst hut; rw [hopen] at he; exact absurd he.symm heq
          · exact ⟨u, by omega, he⟩
      rw [hiff]
  have hinv69 : OpenPosInv trapdoor positions (t + 1) fwd' tails' s69 :=
    ⟨by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
        o_getReg_setReg_ne .x27 .x9 (by decide), o_getReg_setReg_ne .x24 .x9 (by decide),
        o_getReg_setReg_ne .x7 .x9 (by decide), o_getReg_setReg_ne .x6 .x9 (by decide)]; exact hinv64.rx9,
     by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
        o_getReg_setReg_ne .x27 .x18 (by decide), o_getReg_setReg_ne .x24 .x18 (by decide),
        o_getReg_setReg_ne .x7 .x18 (by decide), o_getReg_setReg_ne .x6 .x18 (by decide)]; exact hinv64.rx18,
     by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
        o_getReg_setReg_ne .x27 .x20 (by decide), o_getReg_setReg_ne .x24 .x20 (by decide),
        o_getReg_setReg_ne .x7 .x20 (by decide), o_getReg_setReg_ne .x6 .x20 (by decide)]; exact hinv64.rx20,
     by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
        o_getReg_setReg_ne .x27 .x21 (by decide), o_getReg_setReg_ne .x24 .x21 (by decide),
        o_getReg_setReg_ne .x7 .x21 (by decide), o_getReg_setReg_ne .x6 .x21 (by decide)]; exact hinv64.rx21,
     by simp only [s69, MachineState.getReg_setPC, o_getReg_setReg_ne .x27 .x24 (by decide)]; rfl,
     by simp only [s69, s68, s67, s66, s65, MachineState.getReg_setPC, o_getReg_setByte,
        o_getReg_setReg_ne .x27 .x26 (by decide), o_getReg_setReg_ne .x24 .x26 (by decide),
        o_getReg_setReg_ne .x7 .x26 (by decide), o_getReg_setReg_ne .x6 .x26 (by decide)]; exact hinv64.rx26,
     rfl, hro69, hw69, ht69, hcap69⟩
  have hsteps_tot :
      30 + 63 + 1 + (21 * 4 + 5 * (fwd25.length / 8 - fwd1.length / 8)) + 1 +
      (28 * 10 + 5 * ((fwd25 ++ l615Chunk 10).length / 8 - fwd25.length / 8) +
        4 * (((tails ++ l615Tails 10).foldl pack6Step ([], 0, 0)).1.length -
          (tails.foldl pack6Step ([], 0, 0)).1.length)) + 5 + 1 = steps := by
    rw [hfwd_eq, htails_eq]
    have h1 : fwd1.length = fwdBytes.length + 88 := by
      simp only [fwd1, fwd0, fwdS, List.length_append, bitsToBytes_length]
    have h2 : fwd1.length / 8 ≤ fwd25.length / 8 := Nat.div_le_div_right (by simp [fwd25])
    have h3 : fwd25.length / 8 ≤ fwd'.length / 8 := Nat.div_le_div_right (by rw [← hfwd_eq]; simp)
    simp only [steps]; omega
  have hrunE : OpenRuns s64 5 5 s69 := (((h64'.trans h65').trans h66').trans h67').trans h68'
  by_cases hmore : t + 1 < positions.card
  · have h69 := o_step_BNE_taken (by omega) (rfl : s69.pc = o_pcAt 69)
      (rfl : openingInstr 69 = .base (.BNE .x27 .x0 (8024#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) ≠ BitVec.ofNat 64 0
          exact o_bv64_ofNat_ne (by omega) (by decide) (by omega))
      (by decide : o_pcAt 69 + signExtend13 (8024#13) = o_pcAt 27)
    refine ⟨s69.setPC (o_pcAt 27), ?_, by rw [if_pos hmore]; rfl,
      ⟨hinv69.rx9, hinv69.rx18, hinv69.rx20, hinv69.rx21, hinv69.rx24, hinv69.rx26, hinv69.rx27,
       hinv69.ro, hinv69.writer.of_eq, hinv69.tail.of_eq, hinv69.cap16⟩⟩
    rw [← hsteps_tot]
    exact ((((((hrunA.trans hrunB).trans h48').trans hr_l25).trans h56').trans hr_l615).trans hrunE).trans h69
  · have hdone : positions.card - (t + 1) = 0 := by omega
    have h69 := o_step_BNE_not_taken (by omega) (rfl : s69.pc = o_pcAt 69)
      (rfl : openingInstr 69 = .base (.BNE .x27 .x0 (8024#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) = 0#64; rw [hdone])
    refine ⟨s69.setPC (o_pcAt 70), ?_, by rw [if_neg hmore]; rfl,
      ⟨hinv69.rx9, hinv69.rx18, hinv69.rx20, hinv69.rx21, hinv69.rx24, hinv69.rx26, hinv69.rx27,
       hinv69.ro, hinv69.writer.of_eq, hinv69.tail.of_eq, hinv69.cap16⟩⟩
    rw [← hsteps_tot]
    exact ((((((hrunA.trans hrunB).trans h48').trans hr_l25).trans h56').trans hr_l615).trans hrunE).trans h69

/-- One iteration of `cap_loop` (`71..85`) at parent `p = heapIdx (l + 1) q` (`16 ≤ l ≤ 23`,
`q < levelSize (l + 1)`): propagates `mark[p] = mark[2*p] | mark[2*p+1]`, and when `mL ≠ mR`
emits the unmarked child via `emit29_tail6`! -/
private theorem o_cap_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {l q : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hl1 : 16 ≤ l) (hl2 : l ≤ 23) (hq : q < levelSize (l + 1))
    (hpc : s.pc = o_pcAt 71)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx21 : s.getReg .x21 = BitVec.ofNat 64 4096)
    (hx23 : s.getReg .x23 = BitVec.ofNat 64 (heapIdx (l + 1) q))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 10804531232)
    (hbd : fwdBytes.length + 29 ≤ proofCap)
    (htbd : tails.length < 200000000)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : OpenWriterState s fwdBytes)
    (ht : OpenTailState s tails)
    (hmL : s.getByte (BitVec.ofNat 64 (4096 + 2 * heapIdx (l + 1) q)) =
      if capMark positions l (2 * q) then 1#8 else 0#8)
    (hmR : s.getByte (BitVec.ofNat 64 (4096 + 2 * heapIdx (l + 1) q + 1)) =
      if capMark positions l (2 * q + 1) then 1#8 else 0#8) :
    let mL := capMark positions l (2 * q)
    let mR := capMark positions l (2 * q + 1)
    let addFwd : List Byte := if mL = mR then [] else if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) 29
        else bitsToBytes (tdNode trapdoor l (2 * q + 1)) 29
    let addTails : List (BitVec 6) := if mL = mR then [] else if !mL then [tail6 (tdNode trapdoor l (2 * q))]
        else [tail6 (tdNode trapdoor l (2 * q + 1))]
    let fwd' := fwdBytes ++ addFwd
    let tails' := tails ++ addTails
    let p := heapIdx (l + 1) q
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 10 + (if mL != mR then 26 else 0) + 5 * (fwd'.length / 8 - fwdBytes.length / 8) +
        4 * ((tails'.foldl pack6Step ([], 0, 0)).1.length - (tails.foldl pack6Step ([], 0, 0)).1.length) ∧
      s'.pc = (if p - 1 = 0 then o_pcAt 86 else o_pcAt 71) ∧
      s'.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s'.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s'.getReg .x23 = BitVec.ofNat 64 (p - 1) ∧
      s'.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
      OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      OpenWriterState s' fwd' ∧
      OpenTailState s' tails' ∧
      s'.getByte (BitVec.ofNat 64 (4096 + p)) = (if capMark positions (l + 1) q then 1#8 else 0#8) ∧
      (∀ addr < 4608, addr ≠ 4096 + p → s'.getByte (BitVec.ofNat 64 addr) = s.getByte (BitVec.ofNat 64 addr)) := by
  intro mL mR addFwd addTails fwd' tails' p
  have hp_lo : 1 ≤ p := heapIdx_pos (l + 1) q
  have hls_le : levelSize (l + 1) ≤ 128 := by
    have : l + 1 = 17 ∨ l + 1 = 18 ∨ l + 1 = 19 ∨ l + 1 = 20 ∨ l + 1 = 21 ∨ l + 1 = 22 ∨ l + 1 = 23 ∨ l + 1 = 24 := by omega
    rcases this with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hp_lt : p < 256 := by unfold p heapIdx; omega
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  -- 71..77: load mL, mR, store mL | mR at 4096 + p (7 steps)
  have h71 := o_step_SLLI (by omega) hpc (rfl : openingInstr 71 = .base (.SLLI .x6 .x23 (1#6)))
  let s72 := (s.setReg .x6 (BitVec.ofNat 64 (2 * p))).setPC (o_pcAt 72)
  have h71' : OpenRuns s 1 1 s72 := by
    have hv : s.getReg .x23 <<< (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (2 * p) := by
      rw [hx23]; change BitVec.ofNat 64 p <<< 1 = _; rw [o_bv64_shl]; congr 1; omega
    simpa only [hv, s72] using h71
  have h72 := o_step_ADD (by omega) (rfl : s72.pc = o_pcAt 72) (rfl : openingInstr 72 = .base (.ADD .x6 .x21 .x6))
  let s73 := (s72.setReg .x6 (BitVec.ofNat 64 (4096 + 2 * p))).setPC (o_pcAt 73)
  have h72' : OpenRuns s72 1 1 s73 := by
    have hv : s72.getReg .x21 + s72.getReg .x6 = BitVec.ofNat 64 (4096 + 2 * p) := by
      rw [show s72.getReg .x21 = BitVec.ofNat 64 4096 from hx21]
      change BitVec.ofNat 64 4096 + BitVec.ofNat 64 (2 * p) = _; exact o_bv64_ofNat_add _ _
    simpa only [hv, s73] using h72
  have haddr73 : s73.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (4096 + 2 * p) := by
    change BitVec.ofNat 64 _ + _ = _; rw [hse0, o_bv64_ofNat_add, Nat.add_zero]
  have h73 := o_step_LBU (by omega) (rfl : s73.pc = o_pcAt 73) (rfl : openingInstr 73 = .base (.LBU .x7 .x6 (0#12)))
    (by rw [haddr73]; exact o_accessValid_ofNat _ 1 (by omega) (by omega))
  let s74 := (s73.setReg .x7 (if mL then 1#64 else 0#64)).setPC (o_pcAt 74)
  have h73' : OpenRuns s73 1 1 s74 := by
    have hget : s73.getByte (BitVec.ofNat 64 (4096 + 2 * p)) = if mL then 1#8 else 0#8 := hmL
    simpa only [haddr73, hget, o_bool_byte_zeroExtend, s74] using h73
  have haddr74 : s74.getReg .x6 + signExtend12 (1#12) = BitVec.ofNat 64 (4096 + 2 * p + 1) := by
    change BitVec.ofNat 64 _ + _ = _; rw [hse1, o_bv64_ofNat_add]
  have h74 := o_step_LBU (by omega) (rfl : s74.pc = o_pcAt 74) (rfl : openingInstr 74 = .base (.LBU .x8 .x6 (1#12)))
    (by rw [haddr74]; exact o_accessValid_ofNat _ 1 (by omega) (by omega))
  let s75 := (s74.setReg .x8 (if mR then 1#64 else 0#64)).setPC (o_pcAt 75)
  have h74' : OpenRuns s74 1 1 s75 := by
    have hget : s74.getByte (BitVec.ofNat 64 (4096 + 2 * p + 1)) = if mR then 1#8 else 0#8 := hmR
    simpa only [haddr74, hget, o_bool_byte_zeroExtend, s75] using h74
  have h75 := o_step_OR (by omega) (rfl : s75.pc = o_pcAt 75) (rfl : openingInstr 75 = .base (.OR .x11 .x7 .x8))
  let s76 := (s75.setReg .x11 (if (mL || mR) then 1#64 else 0#64)).setPC (o_pcAt 76)
  have h75' : OpenRuns s75 1 1 s76 := by
    have hv : s75.getReg .x7 ||| s75.getReg .x8 = if (mL || mR) then 1#64 else 0#64 := o_bool_word_or mL mR
    simpa only [hv, s76] using h75
  have h76 := o_step_ADD (by omega) (rfl : s76.pc = o_pcAt 76) (rfl : openingInstr 76 = .base (.ADD .x6 .x21 .x23))
  let s77 := (s76.setReg .x6 (BitVec.ofNat 64 (4096 + p))).setPC (o_pcAt 77)
  have h76' : OpenRuns s76 1 1 s77 := by
    have hr21 : s76.getReg .x21 = BitVec.ofNat 64 4096 := hx21
    have hr23 : s76.getReg .x23 = BitVec.ofNat 64 p := hx23
    have hv : s76.getReg .x21 + s76.getReg .x23 = BitVec.ofNat 64 (4096 + p) := by
      rw [hr21, hr23, o_bv64_ofNat_add]
    simpa only [hv, s77] using h76
  have haddr77 : s77.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (4096 + p) := by
    change BitVec.ofNat 64 _ + _ = _; rw [hse0, o_bv64_ofNat_add, Nat.add_zero]
  have h77 := o_step_SB (by omega) (rfl : s77.pc = o_pcAt 77) (rfl : openingInstr 77 = .base (.SB .x6 .x11 (0#12)))
    (by rw [haddr77]; exact o_accessValid_ofNat _ 1 (by omega) (by omega))
  let s78 := (s77.setByte (BitVec.ofNat 64 (4096 + p)) (if (mL || mR) then 1#8 else 0#8)).setPC (o_pcAt 78)
  have h77' : OpenRuns s77 1 1 s78 := by
    have htr : (s77.getReg .x11).truncate 8 = if (mL || mR) then 1#8 else 0#8 := o_bool_word_truncate8 (mL || mR)
    simpa only [haddr77, htr, s78] using h77
  have hpre7 : OpenRuns s 7 7 s78 := (((((h71'.trans h72').trans h73').trans h74').trans h75').trans h76').trans h77'
  have hro78 : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s78 := by
    intro a h1 h2
    change (s.setByte (BitVec.ofNat 64 (4096 + p)) _).getMem a = _
    exact o_readOnly_setByte_cap (4096 + p) _ hro (by omega) (by omega) a h1 h2
  have hw78 : OpenWriterState s78 fwdBytes := by
    have hpc_eq : proofCap = 8480886496 := rfl
    exact (o_writerState_setByte_outside (4096 + p) _ hw (by omega) (by omega) (by omega)).of_eq
      (h25 := by simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; rfl)
      (h13 := by simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; rfl)
      (h14 := by simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; rfl)
      (h12 := by simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; rfl)
      (hmem := fun a => by simp only [s78, s77, s76, s75, s74, s73, s72, o_getByte_setPC, o_getByte_setReg]; rfl)
  have ht78 : OpenTailState s78 tails := by
    have htb : tailBufBase = 20000000000 := rfl
    exact (o_tailState_setByte_outside (4096 + p) _ ht (by omega) (by omega)).of_eq
      (h31 := by simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; rfl)
      (h15 := by simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; rfl)
      (h16 := by simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; rfl)
      (h17 := by simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; rfl)
      (hmem := fun a => by simp only [s78, s77, s76, s75, s74, s73, s72, o_getByte_setPC, o_getByte_setReg]; rfl)
  have hmark_p : s78.getByte (BitVec.ofNat 64 (4096 + p)) = if capMark positions (l + 1) q then 1#8 else 0#8 := by
    rw [capMark_succ positions l q hl1 hq]
    simp only [s78, o_getByte_setPC, set_byte_read, if_pos rfl]; rfl
  have hmark_other : ∀ addr < 4608, addr ≠ 4096 + p →
      s78.getByte (BitVec.ofNat 64 addr) = s.getByte (BitVec.ofNat 64 addr) := by
    intro addr hlt hne
    simp only [s78, s77, s76, s75, s74, s73, s72, o_getByte_setPC, o_getByte_setReg, set_byte_read]
    rw [if_neg (o_bv64_ofNat_ne (by omega) (by omega) hne)]
  -- Helper for tail latch `84..85` from any state `s84` at `pc = 84`
  have hfinish_latch : ∀ (s84 : MachineState) (midSteps : Nat),
      OpenRuns s78 midSteps midSteps s84 →
      midSteps ≤ 1 + (if mL != mR then 26 else 0) + 5 * (fwd'.length / 8 - fwdBytes.length / 8) +
        4 * ((tails'.foldl pack6Step ([], 0, 0)).1.length - (tails.foldl pack6Step ([], 0, 0)).1.length) →
      s84.pc = o_pcAt 84 →
      s84.getReg .x9 = BitVec.ofNat 64 4294971424 →
      s84.getReg .x21 = BitVec.ofNat 64 4096 →
      s84.getReg .x23 = BitVec.ofNat 64 p →
      s84.getReg .x26 = BitVec.ofNat 64 10804531232 →
      OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s84 →
      OpenWriterState s84 fwd' → OpenTailState s84 tails' →
      (∀ q < 4608, s84.getByte (BitVec.ofNat 64 q) = s78.getByte (BitVec.ofNat 64 q)) →
      ∃ steps s', OpenRuns s steps steps s' ∧
        steps ≤ 10 + (if mL != mR then 26 else 0) + 5 * (fwd'.length / 8 - fwdBytes.length / 8) +
          4 * ((tails'.foldl pack6Step ([], 0, 0)).1.length - (tails.foldl pack6Step ([], 0, 0)).1.length) ∧
        s'.pc = (if p - 1 = 0 then o_pcAt 86 else o_pcAt 71) ∧
        s'.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
        s'.getReg .x21 = BitVec.ofNat 64 4096 ∧
        s'.getReg .x23 = BitVec.ofNat 64 (p - 1) ∧
        s'.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
        OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
        OpenWriterState s' fwd' ∧ OpenTailState s' tails' ∧
        s'.getByte (BitVec.ofNat 64 (4096 + p)) = (if capMark positions (l + 1) q then 1#8 else 0#8) ∧
        (∀ addr < 4608, addr ≠ 4096 + p → s'.getByte (BitVec.ofNat 64 addr) = s.getByte (BitVec.ofNat 64 addr)) := by
    intro s84 midSteps hrmid hmid_le hpc84 hx9_84 hx21_84 hx23_84 hx26_84 hro84 hw84 ht84 hcap84
    have h84 := o_step_ADDI (by omega) hpc84 (rfl : openingInstr 84 = .base (.ADDI .x23 .x23 (4095#12)))
    let s85 := (s84.setReg .x23 (BitVec.ofNat 64 (p - 1))).setPC (o_pcAt 85)
    have h84' : OpenRuns s84 1 1 s85 := by
      have hr23 : s84.getReg .x23 = BitVec.ofNat 64 ((p - 1) + 1) := by rw [hx23_84]; congr 1; omega
      rw [hr23, o_bv64_add_neg1] at h84; exact h84
    by_cases hp1 : p - 1 = 0
    · have h85 := o_step_BNE_not_taken (by omega) (rfl : s85.pc = o_pcAt 85)
        (rfl : openingInstr 85 = .base (.BNE .x23 .x0 (8136#13)))
        (by change BitVec.ofNat 64 (p - 1) = 0#64; rw [hp1])
      refine ⟨7 + midSteps + 1 + 1, s85.setPC (o_pcAt 86), ((hpre7.trans hrmid).trans h84').trans h85,
        by omega, by rw [if_pos hp1]; rfl, hx9_84, hx21_84, rfl, hx26_84, hro84, hw84.of_eq, ht84.of_eq,
        (hcap84 _ (by omega)).trans hmark_p, fun a ha hne => (hcap84 a ha).trans (hmark_other a ha hne)⟩
    · have h85 := o_step_BNE_taken (by omega) (rfl : s85.pc = o_pcAt 85)
        (rfl : openingInstr 85 = .base (.BNE .x23 .x0 (8136#13)))
        (by change BitVec.ofNat 64 (p - 1) ≠ BitVec.ofNat 64 0; exact o_bv64_ofNat_ne (by omega) (by decide) hp1)
        (by decide : o_pcAt 85 + signExtend13 (8136#13) = o_pcAt 71)
      refine ⟨7 + midSteps + 1 + 1, s85.setPC (o_pcAt 71), ((hpre7.trans hrmid).trans h84').trans h85,
        by omega, by rw [if_neg hp1]; rfl, hx9_84, hx21_84, rfl, hx26_84, hro84, hw84.of_eq, ht84.of_eq,
        (hcap84 _ (by omega)).trans hmark_p, fun a ha hne => (hcap84 a ha).trans (hmark_other a ha hne)⟩
  -- Branch at word 78: `BEQ x7, x8, +24 (-> 84)`
  have hx7_78 : s78.getReg .x7 = if mL then 1#64 else 0#64 := by
    simp only [s78, s77, s76, s75, s74, MachineState.getReg_setPC, o_getReg_setByte]; rfl
  have hx8_78 : s78.getReg .x8 = if mR then 1#64 else 0#64 := by
    simp only [s78, s77, s76, s75, MachineState.getReg_setPC, o_getReg_setByte]; rfl
  have hx9_78 : s78.getReg .x9 = BitVec.ofNat 64 4294971424 := by
    simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; exact hx9
  have hx21_78 : s78.getReg .x21 = BitVec.ofNat 64 4096 := by
    simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; exact hx21
  have hx23_78 : s78.getReg .x23 = BitVec.ofNat 64 p := by
    simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; exact hx23
  have hx26_78 : s78.getReg .x26 = BitVec.ofNat 64 10804531232 := by
    simp only [s78, s77, s76, s75, s74, s73, s72, MachineState.getReg_setPC, o_getReg_setByte]; exact hx26
  by_cases heq : mL = mR
  · have h78 := o_step_BEQ_taken (by omega) (rfl : s78.pc = o_pcAt 78)
      (rfl : openingInstr 78 = .base (.BEQ .x7 .x8 (24#13))) (by rw [hx7_78, hx8_78, heq])
      (by decide : o_pcAt 78 + signExtend13 (24#13) = o_pcAt 84)
    have hfwd_nil : fwd' = fwdBytes := by simp [fwd', addFwd, heq]
    have ht_nil : tails' = tails := by simp [tails', addTails, heq]
    exact hfinish_latch (s78.setPC (o_pcAt 84)) 1 h78 (by omega) rfl hx9_78 hx21_78 hx23_78 hx26_78
      hro78 (hfwd_nil ▸ hw78.of_eq) (ht_nil ▸ ht78.of_eq) (fun _ _ => rfl)
  · have hbne_true : (mL != mR) = true := by revert heq; cases mL <;> cases mR <;> decide
    have h78 := o_step_BEQ_not_taken (by omega) (rfl : s78.pc = o_pcAt 78)
      (rfl : openingInstr 78 = .base (.BEQ .x7 .x8 (24#13)))
      (by rw [hx7_78, hx8_78]; exact o_bool_word_ne_of_ne heq)
    let s79 := s78.setPC (o_pcAt 79)
    have h79 := o_step_SLLI (by omega) (rfl : s79.pc = o_pcAt 79) (rfl : openingInstr 79 = .base (.SLLI .x6 .x23 (6#6)))
    let s80 := (s79.setReg .x6 (BitVec.ofNat 64 (32 * (2 * p)))).setPC (o_pcAt 80)
    have h79' : OpenRuns s79 1 1 s80 := by
      have hv : s79.getReg .x23 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (32 * (2 * p)) := by
        rw [show s79.getReg .x23 = BitVec.ofNat 64 p from hx23_78]
        change BitVec.ofNat 64 p <<< 6 = _; rw [o_bv64_shl]; congr 1; omega
      simpa only [hv, s80] using h79
    have h80 := o_step_ADD (by omega) (rfl : s80.pc = o_pcAt 80) (rfl : openingInstr 80 = .base (.ADD .x10 .x9 .x6))
    let s81 := (s80.setReg .x10 (BitVec.ofNat 64 (4294971424 + 32 * (2 * p)))).setPC (o_pcAt 81)
    have h80' : OpenRuns s80 1 1 s81 := by
      have hv : s80.getReg .x9 + s80.getReg .x6 = BitVec.ofNat 64 (4294971424 + 32 * (2 * p)) := by
        rw [show s80.getReg .x9 = BitVec.ofNat 64 4294971424 from hx9_78]
        change BitVec.ofNat 64 _ + BitVec.ofNat 64 _ = _; exact o_bv64_ofNat_add _ _
      simpa only [hv, s81] using h80
    have hchL : 2 * p = heapIdx l (2 * q) := heapIdx_left_child l q (by omega)
    have hchR : 2 * p + 1 = heapIdx l (2 * q + 1) := heapIdx_right_child l q (by omega)
    have hls_dbl := levelSize_double l (by omega)
    by_cases hmLv : mL = false
    · -- `mL = false`: `BEQ x7, x0, +8 (-> 83)` taken, emit `2 * q`
      have h81 := o_step_BEQ_taken (by omega) (rfl : s81.pc = o_pcAt 81)
        (rfl : openingInstr 81 = .base (.BEQ .x7 .x0 (8#13)))
        (by simp only [s81, s80, s79, MachineState.getReg_setPC, o_getReg_setReg_ne .x10 .x7 (by decide),
            o_getReg_setReg_ne .x6 .x7 (by decide), hx7_78, hmLv]; rfl)
        (by decide : o_pcAt 81 + signExtend13 (8#13) = o_pcAt 83)
      let s83 := s81.setPC (o_pcAt 83)
      let dSib := tdNode trapdoor l (2 * q)
      have hbd_c : 32 * heapIdx l (2 * q) + 32 ≤ 2080374784 := by
        have := heapIdx_lt l (2 * q) (by omega) (by omega); omega
      have hbyte29 : trapdoor.extractLsb' (8 * (32 * heapIdx l (2 * q) + 29)) 8 = dSib.extractLsb' (8 * 29) 8 := by
        unfold dSib tdNode
        rw [o_extractLsb'_extractLsb' trapdoor (8 * (32 * heapIdx l (2 * q))) 256 (8 * 29) 8 (by omega)]
        exact congrArg (fun off => trapdoor.extractLsb' off 8) (by omega)
      obtain ⟨s84, hrc, hpc84, hreg84, hro84, hw84, ht84, hcap84⟩ :=
        o_call_emit29_tail6 (s := s83) (callIdx := 83) (srcOff := 32 * heapIdx l (2 * q)) (jOff := 428#21)
          (fwdBytes := fwdBytes) (chunk := bitsToBytes dSib 29) (tails := tails) (d := dSib)
          (by omega) rfl (by decide) rfl (by change BitVec.ofNat 64 (4294971424 + 32 * (2 * p)) = _; rw [hchL])
          (by omega) hbd_c hbd htbd hro78 hw78.of_eq ht78.of_eq (bitsToBytes_length _ 29)
          (fun j hj => o_chunk_tdNode trapdoor l (2 * q) 29 j (by omega) hj) hbyte29
      have hfeq : fwdBytes ++ bitsToBytes dSib 29 = fwd' := by
        unfold fwd' addFwd; rw [if_neg heq, hmLv]; rfl
      have hteq : tails ++ [tail6 dSib] = tails' := by
        unfold tails' addTails; rw [if_neg heq, hmLv]; rfl
      exact hfinish_latch s84 _ ((((h78.trans h79').trans h80').trans h81).trans hrc)
        (by rw [hbne_true, hfeq, hteq]; simp only [ite_true]; omega) hpc84
        (by rw [hreg84 .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx9_78)
        (by rw [hreg84 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx21_78)
        (by rw [hreg84 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx23_78)
        (by rw [hreg84 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx26_78)
        hro84 (hw84.castList hfeq) (hteq ▸ ht84) hcap84
    · -- `mL = true`: `BEQ x7, x0` not taken, `ADDI x10, x10, 32`, emit `2 * q + 1`
      have hmLt : mL = true := by cases hm : mL <;> simp_all
      have h81 := o_step_BEQ_not_taken (by omega) (rfl : s81.pc = o_pcAt 81)
        (rfl : openingInstr 81 = .base (.BEQ .x7 .x0 (8#13)))
        (by simp only [s81, s80, s79, MachineState.getReg_setPC, o_getReg_setReg_ne .x10 .x7 (by decide),
            o_getReg_setReg_ne .x6 .x7 (by decide), hx7_78, hmLt]; change (1#64 : Word) ≠ 0#64; decide)
      let s82 := s81.setPC (o_pcAt 82)
      have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
      have h82 := o_step_ADDI (by omega) (rfl : s82.pc = o_pcAt 82) (rfl : openingInstr 82 = .base (.ADDI .x10 .x10 (32#12)))
      let s83 := (s82.setReg .x10 (BitVec.ofNat 64 (4294971424 + 32 * heapIdx l (2 * q + 1)))).setPC (o_pcAt 83)
      have h82' : OpenRuns s82 1 1 s83 := by
        have hv : s82.getReg .x10 + signExtend12 (32#12) = BitVec.ofNat 64 (4294971424 + 32 * heapIdx l (2 * q + 1)) := by
          change BitVec.ofNat 64 (4294971424 + 32 * (2 * p)) + signExtend12 (32#12) = _
          rw [hse32, o_bv64_ofNat_add, ← hchR]; congr 1
        simpa only [hv, s83] using h82
      let dSib := tdNode trapdoor l (2 * q + 1)
      have hbd_c : 32 * heapIdx l (2 * q + 1) + 32 ≤ 2080374784 := by
        have := heapIdx_lt l (2 * q + 1) (by omega) (by omega); omega
      have hbyte29 : trapdoor.extractLsb' (8 * (32 * heapIdx l (2 * q + 1) + 29)) 8 = dSib.extractLsb' (8 * 29) 8 := by
        unfold dSib tdNode
        rw [o_extractLsb'_extractLsb' trapdoor (8 * (32 * heapIdx l (2 * q + 1))) 256 (8 * 29) 8 (by omega)]
        exact congrArg (fun off => trapdoor.extractLsb' off 8) (by omega)
      obtain ⟨s84, hrc, hpc84, hreg84, hro84, hw84, ht84, hcap84⟩ :=
        o_call_emit29_tail6 (s := s83) (callIdx := 83) (srcOff := 32 * heapIdx l (2 * q + 1)) (jOff := 428#21)
          (fwdBytes := fwdBytes) (chunk := bitsToBytes dSib 29) (tails := tails) (d := dSib)
          (by omega) rfl (by decide) rfl rfl (by omega) hbd_c hbd htbd hro78 hw78.of_eq ht78.of_eq
          (bitsToBytes_length _ 29) (fun j hj => o_chunk_tdNode trapdoor l (2 * q + 1) 29 j (by omega) hj) hbyte29
      have hfeq : fwdBytes ++ bitsToBytes dSib 29 = fwd' := by
        unfold fwd' addFwd; rw [if_neg heq, hmLt]; rfl
      have hteq : tails ++ [tail6 dSib] = tails' := by
        unfold tails' addTails; rw [if_neg heq, hmLt]; rfl
      exact hfinish_latch s84 _ (((((h78.trans h79').trans h80').trans h81).trans h82').trans hrc)
        (by rw [hbne_true, hfeq, hteq]; simp only [ite_true]; omega) hpc84
        (by rw [hreg84 .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx9_78)
        (by rw [hreg84 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx21_78)
        (by rw [hreg84 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx23_78)
        (by rw [hreg84 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx26_78)
        hro84 (hw84.castList hfeq) (hteq ▸ ht84) hcap84

private theorem o_pack6_acc_mono (ts1 ts2 : List (BitVec 6)) :
    (ts1.foldl pack6Step ([], 0, 0)).1.length ≤
      ((ts1 ++ ts2).foldl pack6Step ([], 0, 0)).1.length := by
  have h1 := o_pack6_foldl_bounds ts1
  have h2 := o_pack6_foldl_bounds (ts1 ++ ts2)
  rw [List.length_append] at h2
  omega

/-- One full cap level `l ∈ [16..23]` of `cap_loop` (`q = levelSize (l + 1) - 1` down to `0`). -/
private theorem o_cap_level {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {l : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hl1 : 16 ≤ l) (hl2 : l ≤ 23)
    (hpc : s.pc = o_pcAt 71)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx21 : s.getReg .x21 = BitVec.ofNat 64 4096)
    (hx23 : s.getReg .x23 = BitVec.ofNat 64 (levelSize l - 1))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 10804531232)
    (hbd : fwdBytes.length + 29 * levelFrontierCount positions l + 29 ≤ proofCap)
    (htbd : tails.length + levelFrontierCount positions l < 200000000)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : OpenWriterState s fwdBytes) (ht : OpenTailState s tails)
    (hmarks : ∀ idx < levelSize l,
      s.getByte (BitVec.ofNat 64 (4096 + heapIdx l idx)) = if capMark positions l idx then 1#8 else 0#8) :
    let fwd' := fwdBytes ++ capLevelFrontierFwd (tdNode trapdoor) positions l
    let tails' := tails ++ capLevelFrontierTails (tdNode trapdoor) positions l
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 10 * levelSize (l + 1) + 26 * levelFrontierCount positions l +
        5 * (fwd'.length / 8 - fwdBytes.length / 8) +
        4 * ((tails'.foldl pack6Step ([], 0, 0)).1.length - (tails.foldl pack6Step ([], 0, 0)).1.length) ∧
      s'.pc = (if l = 23 then o_pcAt 86 else o_pcAt 71) ∧
      s'.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s'.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s'.getReg .x23 = BitVec.ofNat 64 (levelSize (l + 1) - 1) ∧
      s'.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
      OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      OpenWriterState s' fwd' ∧ OpenTailState s' tails' ∧
      (∀ idx < levelSize (l + 1),
        s'.getByte (BitVec.ofNat 64 (4096 + heapIdx (l + 1) idx)) =
          if capMark positions (l + 1) idx then 1#8 else 0#8) := by
  intro fwd' tails'
  set M := levelSize (l + 1)
  have hdbl : levelSize l = 2 * M := levelSize_double l (by omega)
  have hMpos : 0 < M := levelSize_pos (l + 1)
  have hMle : M ≤ 128 := by
    unfold M
    have : l + 1 = 17 ∨ l + 1 = 18 ∨ l + 1 = 19 ∨ l + 1 = 20 ∨ l + 1 = 21 ∨ l + 1 = 22 ∨ l + 1 = 23 ∨ l + 1 = 24 := by omega
    rcases this with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  have hM1 : M = 1 ↔ l = 23 := by
    have : l = 16 ∨ l = 17 ∨ l = 18 ∨ l = 19 ∨ l = 20 ∨ l = 21 ∨ l = 22 ∨ l = 23 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have htakeAll : (List.range M).reverse.take M = (List.range M).reverse := by
    simpa only [List.length_reverse, List.length_range] using List.take_length (l := (List.range M).reverse)
  let stepFwd (q : Nat) : List Byte :=
    let mL := capMark positions l (2 * q); let mR := capMark positions l (2 * q + 1)
    if mL = mR then [] else if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) 29
    else bitsToBytes (tdNode trapdoor l (2 * q + 1)) 29
  let stepTails (q : Nat) : List (BitVec 6) :=
    let mL := capMark positions l (2 * q); let mR := capMark positions l (2 * q + 1)
    if mL = mR then [] else if !mL then [tail6 (tdNode trapdoor l (2 * q))]
    else [tail6 (tdNode trapdoor l (2 * q + 1))]
  let stepCnt (q : Nat) : Nat := if (capMark positions l (2 * q) != capMark positions l (2 * q + 1)) then 1 else 0
  let prefFwd (k : Nat) : List Byte := ((List.range M).reverse.take k).flatMap stepFwd
  let prefTails (k : Nat) : List (BitVec 6) := ((List.range M).reverse.take k).flatMap stepTails
  let prefCnt (k : Nat) : Nat := (((List.range M).reverse.take k).map stepCnt).sum
  have htake_rev_succ : ∀ k < M,
      (List.range M).reverse.take (k + 1) = (List.range M).reverse.take k ++ [M - 1 - k] := by
    intro k hk
    rw [List.take_succ_eq_append_getElem (by simp; omega)]
    congr 2; rw [List.getElem_reverse]; simp only [List.length_range, List.getElem_range]
  have hprefCnt_all : prefCnt M = levelFrontierCount positions l := by
    unfold prefCnt levelFrontierCount
    rw [htakeAll, List.map_reverse, List.sum_reverse, show levelSize l / 2 = M by omega]
    have hsum : ∀ n, ((List.range n).map stepCnt).sum =
        ((Finset.range n).filter fun q => capMark positions l (2 * q) != capMark positions l (2 * q + 1)).card := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ih,
          Finset.range_add_one, Finset.filter_insert]
        by_cases hc : (capMark positions l (2 * n) != capMark positions l (2 * n + 1)) = true
        · have hnm : n ∉ (Finset.range n).filter (fun q => (capMark positions l (2 * q) != capMark positions l (2 * q + 1)) = true) := by simp
          rw [if_pos hc, Finset.card_insert_of_notMem hnm]; simp only [stepCnt, hc, ite_true]
        · rw [if_neg hc]; simp only [stepCnt]; rw [if_neg hc]; omega
    exact hsum M
  have hprefCnt_le : ∀ k ≤ M, prefCnt k ≤ levelFrontierCount positions l := by
    intro k hk
    rw [← hprefCnt_all]; unfold prefCnt
    have h1 : (List.range M).reverse = (List.range M).reverse.take k ++ (List.range M).reverse.drop k :=
      (List.take_append_drop k _).symm
    rw [htakeAll]; conv_rhs => rw [h1]
    rw [List.map_append, List.sum_append]; omega
  have hprefFwd_len : ∀ k ≤ M, (prefFwd k).length = 29 * prefCnt k := by
    intro k hk; induction k with
    | zero => simp [prefFwd, prefCnt]
    | succ k ih =>
      have hih := ih (by omega)
      simp only [prefFwd, prefCnt, htake_rev_succ k (by omega), List.flatMap_append, List.flatMap_singleton,
        List.map_append, List.map_singleton, List.length_append, List.sum_append, List.sum_singleton]
      have h1 : (stepFwd (M - 1 - k)).length = 29 * stepCnt (M - 1 - k) := by
        unfold stepFwd stepCnt
        cases capMark positions l (2 * (M - 1 - k)) <;> cases capMark positions l (2 * (M - 1 - k) + 1) <;>
          simp [bitsToBytes]
      change (prefFwd k).length + (stepFwd (M - 1 - k)).length = 29 * (prefCnt k + stepCnt (M - 1 - k))
      omega
  have hprefTails_len : ∀ k ≤ M, (prefTails k).length = prefCnt k := by
    intro k hk; induction k with
    | zero => simp [prefTails, prefCnt]
    | succ k ih =>
      have hih := ih (by omega)
      simp only [prefTails, prefCnt, htake_rev_succ k (by omega), List.flatMap_append, List.flatMap_singleton,
        List.map_append, List.map_singleton, List.length_append, List.sum_append, List.sum_singleton]
      have h1 : (stepTails (M - 1 - k)).length = stepCnt (M - 1 - k) := by
        unfold stepTails stepCnt
        cases capMark positions l (2 * (M - 1 - k)) <;> cases capMark positions l (2 * (M - 1 - k) + 1) <;> simp
      change (prefTails k).length + (stepTails (M - 1 - k)).length = prefCnt k + stepCnt (M - 1 - k)
      omega
  have hind : ∀ k ≤ M,
      let curF := fwdBytes ++ prefFwd k
      let curT := tails ++ prefTails k
      ∃ steps sk, OpenRuns s steps steps sk ∧
        steps ≤ 10 * k + 26 * prefCnt k + 5 * (curF.length / 8 - fwdBytes.length / 8) +
          4 * ((curT.foldl pack6Step ([], 0, 0)).1.length - (tails.foldl pack6Step ([], 0, 0)).1.length) ∧
        sk.pc = (if M - k = 0 ∧ l = 23 then o_pcAt 86 else o_pcAt 71) ∧
        sk.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
        sk.getReg .x21 = BitVec.ofNat 64 4096 ∧
        sk.getReg .x23 = BitVec.ofNat 64 (2 * M - 1 - k) ∧
        sk.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
        OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) sk ∧
        OpenWriterState sk curF ∧ OpenTailState sk curT ∧
        (∀ idx < levelSize l,
          sk.getByte (BitVec.ofNat 64 (4096 + heapIdx l idx)) = if capMark positions l idx then 1#8 else 0#8) ∧
        (∀ q, M - k ≤ q → q < M →
          sk.getByte (BitVec.ofNat 64 (4096 + heapIdx (l + 1) q)) = if capMark positions (l + 1) q then 1#8 else 0#8) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨0, s, OpenRuns.refl s, by simp [prefCnt, prefFwd, prefTails],
        by rw [if_neg (by omega)]; exact hpc, hx9, hx21, by rw [hx23, hdbl]; rfl, hx26,
        hro, by simpa [prefFwd] using hw, by simpa [prefTails] using ht, hmarks, fun _ h1 h2 => by omega⟩
    | succ k ih =>
      obtain ⟨stK, sk, hrk, hstk_le, hpck, hx9k, hx21k, hx23k, hx26k, hrok, hwk, htk, hmlk, hmpk⟩ := ih (by omega)
      have hpck' : sk.pc = o_pcAt 71 := by rw [if_neg (by omega)] at hpck; exact hpck
      set q := M - 1 - k
      have hq_lt : q < M := by omega
      have hp_eq : heapIdx (l + 1) q = 2 * M - 1 - k := by unfold heapIdx; omega
      have hchL : 2 * heapIdx (l + 1) q = heapIdx l (2 * q) := heapIdx_left_child l q (by omega)
      have hchR : 2 * heapIdx (l + 1) q + 1 = heapIdx l (2 * q + 1) := heapIdx_right_child l q (by omega)
      have hpcnt_le := hprefCnt_le k (by omega)
      have hpf_len := hprefFwd_len k (by omega)
      have hpt_len := hprefTails_len k (by omega)
      have hbd_step : (fwdBytes ++ prefFwd k).length + 29 ≤ proofCap := by
        rw [List.length_append, hpf_len]; omega
      have htbd_step : (tails ++ prefTails k).length < 200000000 := by
        rw [List.length_append, hpt_len]; omega
      obtain ⟨st1, sk1, hr1, hst1, hpc1, hx9_1, hx21_1, hx23_1, hx26_1, hro1, hw1, ht1, hmp_q, hother⟩ :=
        o_cap_step hl1 hl2 hq_lt hpck' hx9k hx21k (by rw [hp_eq]; exact hx23k) hx26k
          hbd_step htbd_step hrok hwk htk
          (by rw [hchL]; exact hmlk (2 * q) (by omega))
          (by rw [Nat.add_assoc, hchR]; exact hmlk (2 * q + 1) (by omega))
      have hpf_succ : fwdBytes ++ prefFwd (k + 1) = (fwdBytes ++ prefFwd k) ++ stepFwd q := by
        simp only [prefFwd, htake_rev_succ k (by omega), List.flatMap_append, List.flatMap_singleton,
          List.append_assoc, q]
      have hpt_succ : tails ++ prefTails (k + 1) = (tails ++ prefTails k) ++ stepTails q := by
        simp only [prefTails, htake_rev_succ k (by omega), List.flatMap_append, List.flatMap_singleton,
          List.append_assoc, q]
      have hpcnt_succ : prefCnt (k + 1) = prefCnt k + stepCnt q := by
        simp only [prefCnt, htake_rev_succ k (by omega), List.map_append, List.map_singleton,
          List.sum_append, List.sum_singleton, q]
      have hsc26 : (if (capMark positions l (2 * q) != capMark positions l (2 * q + 1)) = true then 26 else 0) =
          26 * stepCnt q := by
        unfold stepCnt
        cases capMark positions l (2 * q) <;> cases capMark positions l (2 * q + 1) <;> decide
      have hdiv1 : fwdBytes.length / 8 ≤ (fwdBytes ++ prefFwd k).length / 8 :=
        Nat.div_le_div_right (by simp)
      have hdiv2 : (fwdBytes ++ prefFwd k).length / 8 ≤ ((fwdBytes ++ prefFwd k) ++ stepFwd q).length / 8 :=
        Nat.div_le_div_right (by simp)
      have hacc1 := o_pack6_acc_mono tails (prefTails k)
      have hacc2 := o_pack6_acc_mono (tails ++ prefTails k) (stepTails q)
      have hpc_iff : (heapIdx (l + 1) q - 1 = 0) ↔ (M - (k + 1) = 0 ∧ l = 23) := by
        rw [hp_eq, ← hM1]; omega
      refine ⟨stK + st1, sk1, hrk.trans hr1, ?_, ?_, hx9_1, hx21_1, ?_, hx26_1, hro1,
        hw1.castList hpf_succ.symm, hpt_succ.symm ▸ ht1, ?_, ?_⟩
      · rw [hpf_succ, hpt_succ, hpcnt_succ]
        rw [hsc26] at hst1
        change st1 ≤ 10 + 26 * stepCnt q +
            5 * (((fwdBytes ++ prefFwd k) ++ stepFwd q).length / 8 - (fwdBytes ++ prefFwd k).length / 8) +
            4 * ((((tails ++ prefTails k) ++ stepTails q).foldl pack6Step ([], 0, 0)).1.length -
              ((tails ++ prefTails k).foldl pack6Step ([], 0, 0)).1.length) at hst1
        omega
      · rw [hpc1]; simp only [hpc_iff]
      · rw [hx23_1, hp_eq]; congr 1
      · intro idx hidx
        have hhi : 4096 + heapIdx l idx < 4608 := by unfold heapIdx; omega
        have hne : 4096 + heapIdx l idx ≠ 4096 + heapIdx (l + 1) q := by unfold heapIdx; omega
        exact (hother _ hhi hne).trans (hmlk idx hidx)
      · intro q' hq'1 hq'2
        by_cases hqq : q' = q
        · subst hqq; exact hmp_q
        · have hhi : 4096 + heapIdx (l + 1) q' < 4608 := by unfold heapIdx; omega
          have hne : 4096 + heapIdx (l + 1) q' ≠ 4096 + heapIdx (l + 1) q := by unfold heapIdx; omega
          exact (hother _ hhi hne).trans (hmpk q' (by omega) hq'2)
  obtain ⟨stM, sM, hrM, hstM, hpcM, hx9M, hx21M, hx23M, hx26M, hroM, hwM, htM, _, hmpM⟩ := hind M (le_refl M)
  have hMdiv : levelSize l / 2 = M := by omega
  have hpfM : prefFwd M = capLevelFrontierFwd (tdNode trapdoor) positions l := by
    unfold prefFwd capLevelFrontierFwd; rw [htakeAll, hMdiv]
  have hptM : prefTails M = capLevelFrontierTails (tdNode trapdoor) positions l := by
    unfold prefTails capLevelFrontierTails; rw [htakeAll, hMdiv]
  rw [hpfM, hptM, hprefCnt_all] at hstM
  rw [hpfM] at hwM
  rw [hptM] at htM
  refine ⟨stM, sM, hrM, hstM, ?_, hx9M, hx21M, ?_, hx26M, hroM, hwM, htM,
    fun idx hidx => hmpM idx (by omega) hidx⟩
  · rw [hpcM]; simp only [Nat.sub_self, true_and]
  · rw [hx23M]; congr 1; omega

private theorem o_cap_levelSize_sum :
    (∑ step ∈ Finset.range 8, levelSize (17 + step)) = 255 := by decide

/-- Full descending cap-frontier pass (`70..85`): `255` parent nodes across `L16..L23`. -/
private theorem o_cap_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {recFwd : List Byte} {recTails : List (BitVec 6)}
    {s70 : MachineState}
    (hpc : s70.pc = o_pcAt 70)
    (hx9 : s70.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx21 : s70.getReg .x21 = BitVec.ofNat 64 4096)
    (hx26 : s70.getReg .x26 = BitVec.ofNat 64 10804531232)
    (hbd : recFwd.length + 29 * capFrontierCount positions + 29 ≤ proofCap)
    (htbd : recTails.length + capFrontierCount positions < 200000000)
    (hro : OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s70)
    (hw : OpenWriterState s70 recFwd) (ht : OpenTailState s70 recTails)
    (hcap16 : ∀ c < 256,
      s70.getByte (BitVec.ofNat 64 (4096 + 256 + c)) = if capMark positions 16 c then 1#8 else 0#8) :
    let allFwd := recFwd ++ capFrontierFwd (tdNode trapdoor) positions
    let allTails := recTails ++ capFrontierTails (tdNode trapdoor) positions
    ∃ steps s86, OpenRuns s70 steps steps s86 ∧
      steps ≤ 1 + 10 * 255 + 26 * capFrontierCount positions +
        5 * (allFwd.length / 8 - recFwd.length / 8) +
        4 * ((allTails.foldl pack6Step ([], 0, 0)).1.length - (recTails.foldl pack6Step ([], 0, 0)).1.length) ∧
      s86.pc = o_pcAt 86 ∧
      s86.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
      OpenWriterState s86 allFwd ∧
      OpenTailState s86 allTails := by
  intro allFwd allTails
  have h70 := o_step_ADDI (by omega) hpc (rfl : openingInstr 70 = .base (.ADDI .x23 .x0 (255#12)))
  let s71 := (s70.setReg .x23 (BitVec.ofNat 64 (levelSize 16 - 1))).setPC (o_pcAt 71)
  have h70' : OpenRuns s70 1 1 s71 := by
    have hv : s70.getReg .x0 + signExtend12 (255#12) = BitVec.ofNat 64 (levelSize 16 - 1) := by
      change (0#64 : Word) + signExtend12 (255#12) = BitVec.ofNat 64 (levelSize 16 - 1); decide
    simpa only [hv, s71] using h70
  have hpart_le : ∀ k ≤ 8, (∑ step ∈ Finset.range k, levelFrontierCount positions (16 + step)) ≤
      capFrontierCount positions := by
    intro k hk; unfold capFrontierCount
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hk)
  have hpartF_len : ∀ k, ((List.range k).flatMap (fun step =>
      capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))).length =
      29 * ∑ step ∈ Finset.range k, levelFrontierCount positions (16 + step) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append, ih,
        capLevelFrontierFwd_length, Finset.sum_range_succ]; omega
  have hpartT_len : ∀ k, ((List.range k).flatMap (fun step =>
      capLevelFrontierTails (tdNode trapdoor) positions (16 + step))).length =
      ∑ step ∈ Finset.range k, levelFrontierCount positions (16 + step) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append, ih,
        capLevelFrontierTails_length, Finset.sum_range_succ]
  have hind : ∀ k ≤ 8,
      let curF := recFwd ++ (List.range k).flatMap (fun step => capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))
      let curT := recTails ++ (List.range k).flatMap (fun step => capLevelFrontierTails (tdNode trapdoor) positions (16 + step))
      ∃ steps sk, OpenRuns s71 steps steps sk ∧
        steps ≤ 10 * (∑ step ∈ Finset.range k, levelSize (17 + step)) +
          26 * (∑ step ∈ Finset.range k, levelFrontierCount positions (16 + step)) +
          5 * (curF.length / 8 - recFwd.length / 8) +
          4 * ((curT.foldl pack6Step ([], 0, 0)).1.length - (recTails.foldl pack6Step ([], 0, 0)).1.length) ∧
        sk.pc = (if k = 8 then o_pcAt 86 else o_pcAt 71) ∧
        sk.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
        sk.getReg .x21 = BitVec.ofNat 64 4096 ∧
        sk.getReg .x23 = BitVec.ofNat 64 (levelSize (16 + k) - 1) ∧
        sk.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
        OpenReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) sk ∧
        OpenWriterState sk curF ∧ OpenTailState sk curT ∧
        (∀ idx < levelSize (16 + k),
          sk.getByte (BitVec.ofNat 64 (4096 + heapIdx (16 + k) idx)) =
            if capMark positions (16 + k) idx then 1#8 else 0#8) := by
    intro k hk; induction k with
    | zero =>
      exact ⟨0, s71, OpenRuns.refl s71, by simp, rfl, hx9, hx21, rfl, hx26, hro,
        by simpa using hw.of_eq, by simpa using ht.of_eq, fun idx hidx => by
          have h16 : levelSize 16 = 256 := by decide
          rw [Nat.add_zero, h16] at hidx
          have hh : heapIdx 16 idx = 256 + idx := by unfold heapIdx; rw [h16]
          rw [Nat.add_zero, hh, ← Nat.add_assoc]; exact hcap16 idx hidx⟩
    | succ k ih =>
      obtain ⟨stK, sk, hrk, hstk, hpck, hx9k, hx21k, hx23k, hx26k, hrok, hwk, htk, hmk⟩ := ih (by omega)
      have hpck' : sk.pc = o_pcAt 71 := by rw [if_neg (by omega)] at hpck; exact hpck
      have hsum_succ : (∑ step ∈ Finset.range k, levelFrontierCount positions (16 + step)) +
          levelFrontierCount positions (16 + k) ≤ capFrontierCount positions := by
        rw [← Finset.sum_range_succ]; exact hpart_le (k + 1) hk
      have hbd_k : (recFwd ++ (List.range k).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))).length +
          29 * levelFrontierCount positions (16 + k) + 29 ≤ proofCap := by
        rw [List.length_append, hpartF_len]; omega
      have htbd_k : (recTails ++ (List.range k).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (16 + step))).length +
          levelFrontierCount positions (16 + k) < 200000000 := by
        rw [List.length_append, hpartT_len]; omega
      obtain ⟨st1, sk1, hr1, hst1, hpc1, hx9_1, hx21_1, hx23_1, hx26_1, hro1, hw1, ht1, hm1⟩ :=
        o_cap_level (l := 16 + k) (by omega) (by omega) hpck' hx9k hx21k hx23k hx26k
          hbd_k htbd_k hrok hwk htk hmk
      have hF_eq : recFwd ++ (List.range (k + 1)).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step)) =
          (recFwd ++ (List.range k).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))) ++
          capLevelFrontierFwd (tdNode trapdoor) positions (16 + k) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
      have hT_eq : recTails ++ (List.range (k + 1)).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (16 + step)) =
          (recTails ++ (List.range k).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (16 + step))) ++
          capLevelFrontierTails (tdNode trapdoor) positions (16 + k) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
      have hdiv1 : recFwd.length / 8 ≤ (recFwd ++ (List.range k).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))).length / 8 :=
        Nat.div_le_div_right (by simp)
      have hdiv2 : (recFwd ++ (List.range k).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))).length / 8 ≤
          (recFwd ++ (List.range (k + 1)).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))).length / 8 := by
        rw [hF_eq]; exact Nat.div_le_div_right (by simp)
      have hacc1 := o_pack6_acc_mono recTails ((List.range k).flatMap (fun step =>
        capLevelFrontierTails (tdNode trapdoor) positions (16 + step)))
      have hacc2 := o_pack6_acc_mono (recTails ++ (List.range k).flatMap (fun step =>
        capLevelFrontierTails (tdNode trapdoor) positions (16 + step)))
        (capLevelFrontierTails (tdNode trapdoor) positions (16 + k))
      have h16k : 16 + k + 1 = 16 + (k + 1) := by omega
      have h17k : 16 + k + 1 = 17 + k := by omega
      refine ⟨stK + st1, sk1, hrk.trans hr1, ?_, ?_, hx9_1, hx21_1, ?_, hx26_1, hro1,
        hw1.castList hF_eq.symm, hT_eq.symm ▸ ht1, by rw [← h16k]; exact hm1⟩
      · rw [hF_eq, hT_eq]
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ← h17k]
        rw [hF_eq] at hdiv2
        omega
      · rw [hpc1]; simp only [show (16 + k = 23) ↔ (k + 1 = 8) by omega]
      · rw [← h16k]; exact hx23_1
  obtain ⟨stCap, s86, hrCap, hstCap, hpc86, _, _, _, hx26_86, _, hw86, ht86, _⟩ := hind 8 (le_refl 8)
  have hsumSz := o_cap_levelSize_sum
  have hcnt8 : (∑ step ∈ Finset.range 8, levelFrontierCount positions (16 + step)) =
      capFrontierCount positions := rfl
  have hF8 : recFwd ++ (List.range 8).flatMap (fun step => capLevelFrontierFwd (tdNode trapdoor) positions (16 + step)) = allFwd := rfl
  have hT8 : recTails ++ (List.range 8).flatMap (fun step => capLevelFrontierTails (tdNode trapdoor) positions (16 + step)) = allTails := rfl
  rw [hsumSz, hcnt8, hF8, hT8] at hstCap
  rw [hF8] at hw86; rw [hT8] at ht86
  exact ⟨1 + stCap, s86, h70'.trans hrCap, by omega, hpc86, hx26_86, hw86, ht86⟩

/-! ### 8. Entry Setup (`0..26`, `106..109`), Position Loop, and Top-Level `opening_exec_spec` -/

private theorem o_initialState_pc (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).pc = 0x1000#64 := rfl
private theorem o_initialState_x12 (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).getReg .x12 = BitVec.ofNat 64 s.layout.trapdoor := rfl
private theorem o_initialState_x13 (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).getReg .x13 = BitVec.ofNat 64 s.layout.indices := rfl
private theorem o_initialState_x15 (s : Submission) (p : Program) (input : Input s.sizes p) :
    (s.initialState p input).getReg .x15 = BitVec.ofNat 64 s.layout.proof := rfl
private theorem o_initialState_x16_opening (s : Submission)
    (td : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) :
    (s.initialState .opening (td, positions)).getReg .x16 = BitVec.ofNat 64 positions.card := rfl

private theorem o_entry_prefix (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ s5, OpenRuns s0 5 5 s5 ∧
      s5.pc = o_pcAt 5 ∧
      s5.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s5.getReg .x24 = BitVec.ofNat 64 6375346208 ∧
      s5.getReg .x25 = BitVec.ofNat 64 10804531232 ∧
      s5.getReg .x26 = BitVec.ofNat 64 10804531232 ∧
      s5.getReg .x27 = BitVec.ofNat 64 positions.card ∧
      s5.mem = s0.mem := by
  intro s0
  have hpc0 : s0.pc = o_pcAt 0 := o_initialState_pc submission .opening (trapdoor, positions)
  have hx12 : s0.getReg .x12 = BitVec.ofNat 64 4294971424 := o_initialState_x12 submission .opening (trapdoor, positions)
  have hx13 : s0.getReg .x13 = BitVec.ofNat 64 6375346208 := o_initialState_x13 submission .opening (trapdoor, positions)
  have hx15 : s0.getReg .x15 = BitVec.ofNat 64 10804531232 := o_initialState_x15 submission .opening (trapdoor, positions)
  have hx16 : s0.getReg .x16 = BitVec.ofNat 64 positions.card := o_initialState_x16_opening submission trapdoor positions
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have h0 := o_step_ADDI (by omega) hpc0 (rfl : openingInstr 0 = .base (.ADDI .x9 .x12 (0#12)))
  let s1 := (s0.setReg .x9 (BitVec.ofNat 64 4294971424)).setPC (o_pcAt 1)
  have h0' : OpenRuns s0 1 1 s1 := by simpa only [hx12, hse0, o_bv64_ofNat_add, Nat.add_zero, s1] using h0
  have h1 := o_step_ADDI (by omega) (rfl : s1.pc = o_pcAt 1) (rfl : openingInstr 1 = .base (.ADDI .x24 .x13 (0#12)))
  let s2 := (s1.setReg .x24 (BitVec.ofNat 64 6375346208)).setPC (o_pcAt 2)
  have h1' : OpenRuns s1 1 1 s2 := by
    have hr : s1.getReg .x13 = BitVec.ofNat 64 6375346208 := hx13
    simpa only [hr, hse0, o_bv64_ofNat_add, Nat.add_zero, s2] using h1
  have h2 := o_step_ADDI (by omega) (rfl : s2.pc = o_pcAt 2) (rfl : openingInstr 2 = .base (.ADDI .x25 .x15 (0#12)))
  let s3 := (s2.setReg .x25 (BitVec.ofNat 64 10804531232)).setPC (o_pcAt 3)
  have h2' : OpenRuns s2 1 1 s3 := by
    have hr : s2.getReg .x15 = BitVec.ofNat 64 10804531232 := hx15
    simpa only [hr, hse0, o_bv64_ofNat_add, Nat.add_zero, s3] using h2
  have h3 := o_step_ADDI (by omega) (rfl : s3.pc = o_pcAt 3) (rfl : openingInstr 3 = .base (.ADDI .x26 .x15 (0#12)))
  let s4 := (s3.setReg .x26 (BitVec.ofNat 64 10804531232)).setPC (o_pcAt 4)
  have h3' : OpenRuns s3 1 1 s4 := by
    have hr : s3.getReg .x15 = BitVec.ofNat 64 10804531232 := hx15
    simpa only [hr, hse0, o_bv64_ofNat_add, Nat.add_zero, s4] using h3
  have h4 := o_step_ADDI (by omega) (rfl : s4.pc = o_pcAt 4) (rfl : openingInstr 4 = .base (.ADDI .x27 .x16 (0#12)))
  let s5 := (s4.setReg .x27 (BitVec.ofNat 64 positions.card)).setPC (o_pcAt 5)
  have h4' : OpenRuns s4 1 1 s5 := by
    have hr : s4.getReg .x16 = BitVec.ofNat 64 positions.card := hx16
    simpa only [hr, hse0, o_bv64_ofNat_add, Nat.add_zero, s5] using h4
  exact ⟨s5, (((h0'.trans h1').trans h2').trans h3').trans h4', rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem o_open_empty_epilogue {s : MachineState} (hpc : s.pc = o_pcAt 106) :
    ∃ sHalt, OpenRuns s 3 3 sHalt ∧
      sHalt.pc = o_pcAt 109 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = 0#64 ∧
      sHalt.mem = s.mem := by
  have h1 := o_step_ADDI (by omega) hpc (rfl : openingInstr 106 = .base (.ADDI .x11 .x0 (0#12)))
  let s1 := (s.setReg .x11 0#64).setPC (o_pcAt 107)
  have h1' : OpenRuns s 1 1 s1 := by
    have hv : s.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s1] using h1
  have h2 := o_step_ADDI (by omega) (rfl : s1.pc = o_pcAt 107) (rfl : openingInstr 107 = .base (.ADDI .x5 .x0 (1#12)))
  let s2 := (s1.setReg .x5 1#64).setPC (o_pcAt 108)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x0 + signExtend12 (1#12) = 1#64 := by change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s2] using h2
  have h3 := o_step_ADDI (by omega) (rfl : s2.pc = o_pcAt 108) (rfl : openingInstr 108 = .base (.ADDI .x10 .x0 (0#12)))
  let s3 := (s2.setReg .x10 0#64).setPC (o_pcAt 109)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hv : s2.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s3] using h3
  exact ⟨s3, (h1'.trans h2').trans h3', rfl, rfl, rfl, rfl, rfl⟩

private theorem o_init_nonempty (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (hne : positions.card ≠ 0) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ s27, OpenRuns s0 27 27 s27 ∧
      s27.pc = o_pcAt 27 ∧
      OpenPosInv trapdoor positions 0 [] [] s27 := by
  intro s0
  have hcard := o_positions_card_le positions
  obtain ⟨s5, hr5, hpc5, hx9, hx24, hx25, hx26, hx27, hmem5⟩ := o_entry_prefix trapdoor positions
  have h5 := o_step_BEQ_not_taken (by omega) hpc5 (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (404#13)))
    (by rw [hx27]; exact o_bv64_ofNat_ne (by omega) (by decide) hne)
  let s6 := s5.setPC (o_pcAt 6)
  -- 6..17: writer & tail-packer init
  have h6 := o_step_ADDI (by omega) (rfl : s6.pc = o_pcAt 6) (rfl : openingInstr 6 = .base (.ADDI .x12 .x0 (0#12)))
  let s7 := (s6.setReg .x12 0#64).setPC (o_pcAt 7)
  have h6' : OpenRuns s6 1 1 s7 := by
    have hv : s6.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s7] using h6
  have h7 := o_step_ADDI (by omega) (rfl : s7.pc = o_pcAt 7) (rfl : openingInstr 7 = .base (.ADDI .x13 .x0 (0#12)))
  let s8 := (s7.setReg .x13 0#64).setPC (o_pcAt 8)
  have h7' : OpenRuns s7 1 1 s8 := by
    have hv : s7.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s8] using h7
  have h8 := o_step_ADDI (by omega) (rfl : s8.pc = o_pcAt 8) (rfl : openingInstr 8 = .base (.ADDI .x14 .x0 (63#12)))
  let s9 := (s8.setReg .x14 (BitVec.ofNat 64 63)).setPC (o_pcAt 9)
  have h8' : OpenRuns s8 1 1 s9 := by
    have hv : s8.getReg .x0 + signExtend12 (63#12) = BitVec.ofNat 64 63 := by
      change (0#64 : Word) + signExtend12 (63#12) = BitVec.ofNat 64 63; decide
    simpa only [hv, s9] using h8
  have h9 := o_step_ADDI (by omega) (rfl : s9.pc = o_pcAt 9) (rfl : openingInstr 9 = .base (.ADDI .x31 .x0 (2#12)))
  let s10 := (s9.setReg .x31 (BitVec.ofNat 64 2)).setPC (o_pcAt 10)
  have h9' : OpenRuns s9 1 1 s10 := by
    have hv : s9.getReg .x0 + signExtend12 (2#12) = BitVec.ofNat 64 2 := by
      change (0#64 : Word) + signExtend12 (2#12) = BitVec.ofNat 64 2; decide
    simpa only [hv, s10] using h9
  have h10 := o_step_SLLI (by omega) (rfl : s10.pc = o_pcAt 10) (rfl : openingInstr 10 = .base (.SLLI .x31 .x31 (11#6)))
  let s11 := (s10.setReg .x31 (BitVec.ofNat 64 4096)).setPC (o_pcAt 11)
  have h10' : OpenRuns s10 1 1 s11 := by
    have hv : s10.getReg .x31 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096 := by
      change BitVec.ofNat 64 2 <<< 11 = BitVec.ofNat 64 4096; decide
    simpa only [hv, s11] using h10
  have h11 := o_step_ADDI (by omega) (rfl : s11.pc = o_pcAt 11) (rfl : openingInstr 11 = .base (.ADDI .x31 .x31 (672#12)))
  let s12 := (s11.setReg .x31 (BitVec.ofNat 64 4768)).setPC (o_pcAt 12)
  have h11' : OpenRuns s11 1 1 s12 := by
    have hv : s11.getReg .x31 + signExtend12 (672#12) = BitVec.ofNat 64 4768 := by
      change BitVec.ofNat 64 4096 + signExtend12 (672#12) = BitVec.ofNat 64 4768; decide
    simpa only [hv, s12] using h11
  have h12 := o_step_SLLI (by omega) (rfl : s12.pc = o_pcAt 12) (rfl : openingInstr 12 = .base (.SLLI .x31 .x31 (11#6)))
  let s13 := (s12.setReg .x31 (BitVec.ofNat 64 9764864)).setPC (o_pcAt 13)
  have h12' : OpenRuns s12 1 1 s13 := by
    have hv : s12.getReg .x31 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 9764864 := by
      change BitVec.ofNat 64 4768 <<< 11 = BitVec.ofNat 64 9764864; decide
    simpa only [hv, s13] using h12
  have h13 := o_step_ADDI (by omega) (rfl : s13.pc = o_pcAt 13) (rfl : openingInstr 13 = .base (.ADDI .x31 .x31 (761#12)))
  let s14 := (s13.setReg .x31 (BitVec.ofNat 64 9765625)).setPC (o_pcAt 14)
  have h13' : OpenRuns s13 1 1 s14 := by
    have hv : s13.getReg .x31 + signExtend12 (761#12) = BitVec.ofNat 64 9765625 := by
      change BitVec.ofNat 64 9764864 + signExtend12 (761#12) = BitVec.ofNat 64 9765625; decide
    simpa only [hv, s14] using h13
  have h14 := o_step_SLLI (by omega) (rfl : s14.pc = o_pcAt 14) (rfl : openingInstr 14 = .base (.SLLI .x31 .x31 (11#6)))
  let s15 := (s14.setReg .x31 (BitVec.ofNat 64 tailBufBase)).setPC (o_pcAt 15)
  have h14' : OpenRuns s14 1 1 s15 := by
    have hv : s14.getReg .x31 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 tailBufBase := by
      change BitVec.ofNat 64 9765625 <<< 11 = BitVec.ofNat 64 20000000000; decide
    simpa only [hv, s15] using h14
  have h15 := o_step_ADDI (by omega) (rfl : s15.pc = o_pcAt 15) (rfl : openingInstr 15 = .base (.ADDI .x15 .x31 (0#12)))
  let s16 := (s15.setReg .x15 (BitVec.ofNat 64 tailBufBase)).setPC (o_pcAt 16)
  have h15' : OpenRuns s15 1 1 s16 := by
    have hv : s15.getReg .x31 + signExtend12 (0#12) = BitVec.ofNat 64 tailBufBase := by
      change BitVec.ofNat 64 20000000000 + signExtend12 (0#12) = BitVec.ofNat 64 20000000000; decide
    simpa only [hv, s16] using h15
  have h16 := o_step_ADDI (by omega) (rfl : s16.pc = o_pcAt 16) (rfl : openingInstr 16 = .base (.ADDI .x16 .x0 (0#12)))
  let s17 := (s16.setReg .x16 0#64).setPC (o_pcAt 17)
  have h16' : OpenRuns s16 1 1 s17 := by
    have hv : s16.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s17] using h16
  have h17 := o_step_ADDI (by omega) (rfl : s17.pc = o_pcAt 17) (rfl : openingInstr 17 = .base (.ADDI .x17 .x0 (0#12)))
  let s18 := (s17.setReg .x17 0#64).setPC (o_pcAt 18)
  have h17' : OpenRuns s17 1 1 s18 := by
    have hv : s17.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s18] using h17
  -- 18..26: x18 = C_TD + rowOff + 40, x20 = 2^24, x21 = 4096
  have h18 := o_step_ADDI (by omega) (rfl : s18.pc = o_pcAt 18) (rfl : openingInstr 18 = .base (.ADDI .x6 .x0 (256#12)))
  let s19 := (s18.setReg .x6 (BitVec.ofNat 64 256)).setPC (o_pcAt 19)
  have h18' : OpenRuns s18 1 1 s19 := by
    have hv : s18.getReg .x0 + signExtend12 (256#12) = BitVec.ofNat 64 256 := by
      change (0#64 : Word) + signExtend12 (256#12) = BitVec.ofNat 64 256; decide
    simpa only [hv, s19] using h18
  have h19 := o_step_SLLI (by omega) (rfl : s19.pc = o_pcAt 19) (rfl : openingInstr 19 = .base (.SLLI .x6 .x6 (11#6)))
  let s20 := (s19.setReg .x6 (BitVec.ofNat 64 524288)).setPC (o_pcAt 20)
  have h19' : OpenRuns s19 1 1 s20 := by
    have hv : s19.getReg .x6 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 524288 := by
      change BitVec.ofNat 64 256 <<< 11 = BitVec.ofNat 64 524288; decide
    simpa only [hv, s20] using h19
  have h20 := o_step_SLLI (by omega) (rfl : s20.pc = o_pcAt 20) (rfl : openingInstr 20 = .base (.SLLI .x6 .x6 (11#6)))
  let s21 := (s20.setReg .x6 (BitVec.ofNat 64 rowOff)).setPC (o_pcAt 21)
  have h20' : OpenRuns s20 1 1 s21 := by
    have hv : s20.getReg .x6 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 rowOff := by
      rw [rowOff_eq]; change BitVec.ofNat 64 524288 <<< 11 = BitVec.ofNat 64 1073741824; decide
    simpa only [hv, s21] using h20
  have h21 := o_step_ADDI (by omega) (rfl : s21.pc = o_pcAt 21) (rfl : openingInstr 21 = .base (.ADDI .x6 .x6 (40#12)))
  let s22 := (s21.setReg .x6 (BitVec.ofNat 64 (rowOff + 40))).setPC (o_pcAt 22)
  have h21' : OpenRuns s21 1 1 s22 := by
    have hv : s21.getReg .x6 + signExtend12 (40#12) = BitVec.ofNat 64 (rowOff + 40) := by
      rw [rowOff_eq]; change BitVec.ofNat 64 1073741824 + signExtend12 (40#12) = BitVec.ofNat 64 1073741864; decide
    simpa only [hv, s22] using h21
  have h22 := o_step_ADD (by omega) (rfl : s22.pc = o_pcAt 22) (rfl : openingInstr 22 = .base (.ADD .x18 .x9 .x6))
  let s23 := (s22.setReg .x18 (BitVec.ofNat 64 (4294971424 + (rowOff + 40)))).setPC (o_pcAt 23)
  have h22' : OpenRuns s22 1 1 s23 := by
    have hr9 : s22.getReg .x9 = BitVec.ofNat 64 4294971424 := hx9
    have hv : s22.getReg .x9 + s22.getReg .x6 = BitVec.ofNat 64 (4294971424 + (rowOff + 40)) := by
      rw [hr9]; change BitVec.ofNat 64 4294971424 + BitVec.ofNat 64 (rowOff + 40) = _; exact o_bv64_ofNat_add _ _
    simpa only [hv, s23] using h22
  have h23 := o_step_ADDI (by omega) (rfl : s23.pc = o_pcAt 23) (rfl : openingInstr 23 = .base (.ADDI .x20 .x0 (1#12)))
  let s24 := (s23.setReg .x20 (BitVec.ofNat 64 1)).setPC (o_pcAt 24)
  have h23' : OpenRuns s23 1 1 s24 := by
    have hv : s23.getReg .x0 + signExtend12 (1#12) = BitVec.ofNat 64 1 := by
      change (0#64 : Word) + signExtend12 (1#12) = BitVec.ofNat 64 1; decide
    simpa only [hv, s24] using h23
  have h24 := o_step_SLLI (by omega) (rfl : s24.pc = o_pcAt 24) (rfl : openingInstr 24 = .base (.SLLI .x20 .x20 (24#6)))
  let s25 := (s24.setReg .x20 (BitVec.ofNat 64 16777216)).setPC (o_pcAt 25)
  have h24' : OpenRuns s24 1 1 s25 := by
    have hv : s24.getReg .x20 <<< (24#6 : BitVec 6).toNat = BitVec.ofNat 64 16777216 := by
      change BitVec.ofNat 64 1 <<< 24 = BitVec.ofNat 64 16777216; decide
    simpa only [hv, s25] using h24
  have h25 := o_step_ADDI (by omega) (rfl : s25.pc = o_pcAt 25) (rfl : openingInstr 25 = .base (.ADDI .x21 .x0 (1#12)))
  let s26 := (s25.setReg .x21 (BitVec.ofNat 64 1)).setPC (o_pcAt 26)
  have h25' : OpenRuns s25 1 1 s26 := by
    have hv : s25.getReg .x0 + signExtend12 (1#12) = BitVec.ofNat 64 1 := by
      change (0#64 : Word) + signExtend12 (1#12) = BitVec.ofNat 64 1; decide
    simpa only [hv, s26] using h25
  have h26 := o_step_SLLI (by omega) (rfl : s26.pc = o_pcAt 26) (rfl : openingInstr 26 = .base (.SLLI .x21 .x21 (12#6)))
  let s27 := (s26.setReg .x21 (BitVec.ofNat 64 4096)).setPC (o_pcAt 27)
  have h26' : OpenRuns s26 1 1 s27 := by
    have hv : s26.getReg .x21 <<< (12#6 : BitVec 6).toNat = BitVec.ofNat 64 4096 := by
      change BitVec.ofNat 64 1 <<< 12 = BitVec.ofNat 64 4096; decide
    simpa only [hv, s27] using h26
  have hrA : OpenRuns s0 15 15 s15 :=
    (((((((((hr5.trans h5).trans h6').trans h7').trans h8').trans h9').trans h10').trans h11').trans h12').trans h13').trans h14'
  have hrB : OpenRuns s15 12 12 s27 :=
    ((((((((((h15'.trans h16').trans h17').trans h18').trans h19').trans h20').trans h21').trans h22').trans h23').trans h24').trans h25').trans h26'
  have hmem27 : s27.mem = s0.mem := hmem5
  refine ⟨s27, hrA.trans hrB, rfl, ?_⟩
  refine ⟨hx9, rfl, rfl, rfl, by change s5.getReg .x24 = _; exact hx24, hx26, by change s5.getReg .x27 = _; exact hx27,
    fun a _ _ => by change s27.mem a = s0.mem a; rw [hmem27], ?_, ?_, ?_⟩
  · exact ⟨by change s5.getReg .x25 = _; exact hx25, rfl, rfl,
      fun _ hj => absurd hj (Nat.not_lt_zero _),
      fun j _ _ => by change (0#64 : Word).extractLsb' (8 * j) 8 = 0#8; apply BitVec.eq_of_getLsbD_eq; intro b _; simp,
      fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  · exact ⟨rfl, rfl, rfl, rfl,
      fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  · intro c hc
    change extractByte (s27.mem _) _ = _
    rw [hmem27]
    have hz := opening_initial_zero_low trapdoor positions (4096 + 256 + c) (by omega)
    have hf : o_capMark16Prefix positions 0 c = false := by simp [o_capMark16Prefix]
    rw [hf, if_neg Bool.false_ne_true]; exact hz

private theorem o_pos_loop {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s27 : MachineState}
    (hpos : 0 < positions.card) (hpc : s27.pc = o_pcAt 27)
    (inv0 : OpenPosInv trapdoor positions 0 [] [] s27) :
    let recFwd := (positions.sort (· ≤ ·)).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
    let recTails := (positions.sort (· ≤ ·)).flatMap (recordTails (tdNode trapdoor))
    let steps := 410 * positions.card + 5 * (recFwd.length / 8) +
      4 * (recTails.foldl pack6Step ([], 0, 0)).1.length
    ∃ s70, OpenRuns s27 steps steps s70 ∧
      s70.pc = o_pcAt 70 ∧
      OpenPosInv trapdoor positions positions.card recFwd recTails s70 := by
  intro recFwd recTails steps
  have hcard := o_positions_card_le positions
  have hpc_eq : proofCap = 8480886496 := rfl
  let prefF (t : Nat) : List Byte := ((positions.sort (· ≤ ·)).take t).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
  let prefT (t : Nat) : List (BitVec 6) := ((positions.sort (· ≤ ·)).take t).flatMap (recordTails (tdNode trapdoor))
  have htake_pos : ∀ t (ht : t < positions.card),
      (positions.sort (· ≤ ·)).take (t + 1) =
        (positions.sort (· ≤ ·)).take t ++ [(positions.sort (· ≤ ·))[t]'(by simpa using ht)] :=
    fun t ht => List.take_succ_eq_append_getElem (by simpa using ht)
  have hpf_len : ∀ t ≤ positions.card, (prefF t).length = 498 * t := by
    intro t ht; induction t with
    | zero => simp [prefF]
    | succ t ih =>
      have hih := ih (by omega)
      simp only [prefF, htake_pos t (by omega), List.flatMap_append, List.flatMap_singleton,
        List.length_append, recordFwd_length]
      change (prefF t).length + 498 = 498 * (t + 1); omega
  have hpt_len : ∀ t ≤ positions.card, (prefT t).length = 10 * t := by
    intro t ht; induction t with
    | zero => simp [prefT]
    | succ t ih =>
      have hih := ih (by omega)
      simp only [prefT, htake_pos t (by omega), List.flatMap_append, List.flatMap_singleton,
        List.length_append, recordTails_length]
      change (prefT t).length + 10 = 10 * (t + 1); omega
  have hind : ∀ t ≤ positions.card,
      let st := 410 * t + 5 * ((prefF t).length / 8) + 4 * ((prefT t).foldl pack6Step ([], 0, 0)).1.length
      ∃ stS, OpenRuns s27 st st stS ∧
        stS.pc = (if t < positions.card then o_pcAt 27 else o_pcAt 70) ∧
        OpenPosInv trapdoor positions t (prefF t) (prefT t) stS := by
    intro t ht; induction t with
    | zero =>
      exact ⟨s27, by simpa [prefF, prefT] using OpenRuns.refl s27, by rw [if_pos hpos]; exact hpc, inv0⟩
    | succ t ih =>
      obtain ⟨stS, hrt, hpct, invt⟩ := ih (by omega)
      have hpct' : stS.pc = o_pcAt 27 := by rw [if_pos (by omega)] at hpct; exact hpct
      have hbd_t : (prefF t).length + 498 ≤ proofCap := by rw [hpf_len t (by omega)]; omega
      have htbd_t : (prefT t).length + 10 ≤ 200000000 := by rw [hpt_len t (by omega)]; omega
      obtain ⟨st1, hr1, hpc1, inv1⟩ := o_pos_iter (by omega) hpct' hbd_t htbd_t invt
      have hF_eq : prefF t ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor)
            ((positions.sort (· ≤ ·))[t]'(by simpa using (show t < positions.card by omega))) = prefF (t + 1) := by
        simp only [prefF, htake_pos t (by omega), List.flatMap_append, List.flatMap_singleton]
      have hT_eq : prefT t ++ recordTails (tdNode trapdoor)
            ((positions.sort (· ≤ ·))[t]'(by simpa using (show t < positions.card by omega))) = prefT (t + 1) := by
        simp only [prefT, htake_pos t (by omega), List.flatMap_append, List.flatMap_singleton]
      have hdiv : (prefF t).length / 8 ≤ (prefF (t + 1)).length / 8 := by
        rw [← hF_eq]; exact Nat.div_le_div_right (by simp)
      have hacc : ((prefT t).foldl pack6Step ([], 0, 0)).1.length ≤
          ((prefT (t + 1)).foldl pack6Step ([], 0, 0)).1.length := by
        rw [← hT_eq]; exact o_pack6_acc_mono _ _
      have hst_eq : (410 * t + 5 * ((prefF t).length / 8) + 4 * ((prefT t).foldl pack6Step ([], 0, 0)).1.length) +
          (410 + 5 * ((prefF (t + 1)).length / 8 - (prefF t).length / 8) +
            4 * (((prefT (t + 1)).foldl pack6Step ([], 0, 0)).1.length -
              ((prefT t).foldl pack6Step ([], 0, 0)).1.length)) =
          410 * (t + 1) + 5 * ((prefF (t + 1)).length / 8) + 4 * ((prefT (t + 1)).foldl pack6Step ([], 0, 0)).1.length := by
        omega
      rw [hF_eq, hT_eq] at hr1 inv1
      refine ⟨st1, ?_, hpc1, inv1⟩
      rw [← hst_eq]; exact hrt.trans hr1
  obtain ⟨s70, hr70, hpc70, inv70⟩ := hind positions.card (le_refl _)
  have htakeAll : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) := by
    rw [show positions.card = (positions.sort (· ≤ ·)).length by simp, List.take_length]
  have hF_all : prefF positions.card = recFwd := by unfold prefF recFwd; rw [htakeAll]
  have hT_all : prefT positions.card = recTails := by unfold prefT recTails; rw [htakeAll]
  rw [hF_all, hT_all] at hr70 inv70
  exact ⟨s70, hr70, by simpa only [Nat.lt_irrefl, ite_false] using hpc70, inv70⟩

private theorem o_submission_run_opening (s : Submission)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) :
    s.run .opening (trapdoor, positions) =
      execute (s.image .opening) (s.steps .opening)
        (s.initialState .opening (trapdoor, positions)) true := by
  unfold Submission.run; dsimp only; exact if_pos rfl

/-- Exact deterministic execution specification for the 64-32 `opening` image:
always halts with `.success`, `0` oracle calls, writes `referenceProof` byte-for-byte at
`10804531232`, reports its exact length in `x11`, and uses `≤ 110,258` cycles at `BATCH = 128`. -/
theorem opening_exec_spec (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (positions : Positions) :
    let pf := referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions
    ∃ exec : Execution,
      submission.run .opening (trapdoor, positions) = pure exec ∧
      exec.exit = Riscv.Exit.success ∧
      exec.oracleCalls = 0 ∧
      (exec.state.getReg .x11).toNat = pf.length ∧
      (∀ j (hj : j < pf.length), exec.state.getByte (BitVec.ofNat 64 (10804531232 + j)) = pf[j]) ∧
      (positions.card = BATCH → exec.cycles ≤ 110258) := by
  intro pf
  have hsteps_open : submission.steps .opening = 274877906944 := rfl
  have hpc_eq : proofCap = 8480886496 := rfl
  rw [o_submission_run_opening submission trapdoor positions]
  by_cases hempty : positions.card = 0
  · obtain ⟨s5, hr5, hpc5, _, _, _, _, hx27, _⟩ := o_entry_prefix trapdoor positions
    have h5 := o_step_BEQ_taken (by omega) hpc5 (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (404#13)))
      (by rw [hx27, hempty]; rfl) (by decide : o_pcAt 5 + signExtend13 (404#13) = o_pcAt 106)
    obtain ⟨sHalt, hrepi, hpcH, hx5H, hx10H, hx11H, _⟩ := o_open_empty_epilogue (rfl : (s5.setPC (o_pcAt 106)).pc = o_pcAt 106)
    have hexec := OpenRuns.halt (haltIdx := 109) (totalFuel := submission.steps .opening)
      ((hr5.trans h5).trans hrepi) (by omega) rfl hpcH hx5H hx10H (by rw [hsteps_open]; omega)
    have hpf_nil : pf = [] := by unfold pf referenceProof; rw [if_pos hempty]
    refine ⟨{ exit := .success, state := sHalt, cycles := 5 + 1 + 3 + 1, oracleCalls := 0 },
      hexec, rfl, rfl, ?_, ?_, ?_⟩
    · rw [hpf_nil, hx11H]; rfl
    · rw [hpf_nil]; intro j hj; exact absurd hj (Nat.not_lt_zero _)
    · intro hb; change positions.card = 128 at hb; omega
  · have hpos : 0 < positions.card := Nat.pos_of_ne_zero hempty
    have hcard := o_positions_card_le positions
    obtain ⟨s27, hr27, hpc27, inv27⟩ := o_init_nonempty trapdoor positions hempty
    obtain ⟨s70, hrPos, hpc70, inv70⟩ := o_pos_loop hpos hpc27 inv27
    set recFwd := (positions.sort (· ≤ ·)).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
    set recTails := (positions.sort (· ≤ ·)).flatMap (recordTails (tdNode trapdoor))
    have hrecF_len : recFwd.length = 498 * positions.card := by
      simp only [recFwd, List.length_flatMap, recordFwd_length, List.map_const', List.sum_replicate,
        Finset.length_sort, smul_eq_mul, Nat.mul_comm]
    have hrecT_len : recTails.length = 10 * positions.card := by
      simp only [recTails, List.length_flatMap, recordTails_length, List.map_const', List.sum_replicate,
        Finset.length_sort, smul_eq_mul, Nat.mul_comm]
    have hcap128 := cap_frontier_le_128 positions
    obtain ⟨stCap, s86, hrCap, hstCap, hpc86, hx26_86, hw86, ht86⟩ :=
      o_cap_all hpc70 inv70.rx9 inv70.rx21 inv70.rx26 (by omega) (by omega)
        inv70.ro inv70.writer inv70.tail (fun c hc => by
          rw [inv70.cap16 c hc, o_capMark16Prefix_card])
    set allFwd := referenceProofFwd (tdNode trapdoor) (tdSalt trapdoor) positions
    set allTails := referenceProofTails (tdNode trapdoor) positions
    have hallF_def : recFwd ++ capFrontierFwd (tdNode trapdoor) positions = allFwd := rfl
    have hallT_def : recTails ++ capFrontierTails (tdNode trapdoor) positions = allTails := rfl
    rw [hallF_def] at hw86 hstCap
    rw [hallT_def] at ht86 hstCap
    have hallF_len : allFwd.length = 498 * positions.card + 29 * capFrontierCount positions := by
      rw [← hallF_def, List.length_append, hrecF_len, capFrontierFwd_length]
    have hallT_len : allTails.length = 10 * positions.card + capFrontierCount positions := by
      rw [← hallT_def, List.length_append, hrecT_len, capFrontierTails_length]
    have hlen_cap := referenceProof_length_le_cap (tdNode trapdoor) (tdSalt trapdoor) positions
    have hpf_len_cap : pf.length ≤ 8480886496 := hlen_cap
    have hpf_eq : allFwd ++ pack6BitsRev allTails = pf := by
      unfold pf referenceProof; rw [if_neg hempty]
    have hlen_sum : allFwd.length + (pack6Bits allTails).length ≤ proofCap := by
      have h1 : (allFwd ++ pack6BitsRev allTails).length ≤ proofCap := by rw [hpf_eq]; exact hlen_cap
      simpa only [List.length_append, pack6BitsRev, List.length_reverse] using h1
    obtain ⟨stFl, s93, hrFl, hstFl, hpc93, hx10_93, hx26_93, hpr93, ht93⟩ :=
      o_flush_wbuf hpc86 hx26_86 (by omega) (by omega) hw86 ht86
    obtain ⟨stFt, s96, hrFt, hstFt, hpc96, hx10_96, hx26_96, hx31_96, hx15_96, hpr96, htb96⟩ :=
      o_flush_tail hpc93 hx10_93 hx26_93 (by omega) (by omega) hpr93 ht93
    obtain ⟨s102, hrRev, hpc102, hx10_102, hx26_102, hpr102⟩ :=
      o_rev_tail hpc96 hx10_96 hx26_96 hx31_96 hx15_96 hlen_sum hpr96 htb96
    have hrev_eq : allFwd ++ (pack6Bits allTails).reverse = pf := hpf_eq
    rw [hrev_eq] at hx10_102 hpr102
    obtain ⟨sHalt, hrFin, hpcH, hx5H, hx10H, hx11H, hmemH⟩ := o_finish hpc102 hx10_102 hx26_102
    have htot := (((((hr27.trans hrPos).trans hrCap).trans hrFl).trans hrFt).trans hrRev).trans hrFin
    have hacc_all := (o_pack6_foldl_bounds allTails).2.2
    have hacc_rec_le : (recTails.foldl pack6Step ([], 0, 0)).1.length ≤
        (allTails.foldl pack6Step ([], 0, 0)).1.length :=
      o_pack6_acc_mono recTails (capFrontierTails (tdNode trapdoor) positions)
    have hdiv_rec_le : recFwd.length / 8 ≤ allFwd.length / 8 :=
      Nat.div_le_div_right (by omega)
    have hpack_len : (pack6Bits allTails).length = (6 * allTails.length + 7) / 8 :=
      pack6Bits_length allTails
    have hfuel : 27 + (410 * positions.card + 5 * (recFwd.length / 8) +
        4 * (recTails.foldl pack6Step ([], 0, 0)).1.length) + stCap + stFl + stFt +
        (1 + 5 * (pack6Bits allTails).length) + 3 + 1 ≤ submission.steps .opening := by
      rw [hsteps_open]
      have h1 : allFwd.length / 8 ≤ proofCap / 8 := Nat.div_le_div_right (by omega)
      have h2 : (allTails.foldl pack6Step ([], 0, 0)).1.length ≤ 6 * allTails.length / 8 := by omega
      have h3 : (pack6Bits allTails).length ≤ (6 * (10 * 16777216 + 128) + 7) / 8 := by
        rw [hpack_len]; exact Nat.div_le_div_right (by omega)
      omega
    have hexec := OpenRuns.halt (haltIdx := 105) (totalFuel := submission.steps .opening)
      htot (by omega) rfl hpcH hx5H hx10H hfuel
    refine ⟨{ exit := .success, state := sHalt,
              cycles := 27 + (410 * positions.card + 5 * (recFwd.length / 8) +
                4 * (recTails.foldl pack6Step ([], 0, 0)).1.length) + stCap + stFl + stFt +
                (1 + 5 * (pack6Bits allTails).length) + 3 + 1,
              oracleCalls := 0 },
      hexec, rfl, rfl, ?_, ?_, ?_⟩
    · change (sHalt.getReg .x11).toNat = _
      rw [hx11H, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro j hj
      change extractByte (sHalt.mem _) _ = _
      rw [hmemH]; exact hpr102 j hj
    · intro hb
      change positions.card = 128 at hb
      have hF128 : allFwd.length / 8 ≤ (498 * 128 + 29 * 128) / 8 :=
        Nat.div_le_div_right (by omega)
      have hA128 : (allTails.foldl pack6Step ([], 0, 0)).1.length ≤ 6 * (10 * 128 + 128) / 8 := by omega
      have hP128 : (pack6Bits allTails).length ≤ (6 * (10 * 128 + 128) + 7) / 8 := by
        rw [hpack_len]; exact Nat.div_le_div_right (by omega)
      change 27 + (410 * positions.card + 5 * (recFwd.length / 8) +
        4 * (recTails.foldl pack6Step ([], 0, 0)).1.length) + stCap + stFl + stFt +
        (1 + 5 * (pack6Bits allTails).length) + 3 + 1 ≤ 110258
      omega

end CommitGolfCandidate
