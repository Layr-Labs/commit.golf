import CommitGolfCandidate.MoonMemory

/-! Exact deterministic symbolic execution of the 332-word opening image with branchless
64-bit aligned dword-buffered proof writing and streaming 6-bit tail packing (`pack6BitsRev`).
Tracks registers, read-only input/table framing, capMark scratch bytes, forward proof bytes,
tail-stream scratch bytes, and exact step/cycle bounds with zero oracle calls. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-! ### 1. Program Counter, Trapdoor Views, and Deterministic Multi-Step Relation -/

def pcAt (idx : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * idx)

def tdNode (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (l idx : Nat) : Digest :=
  trapdoor.extractLsb' (8 * (levelBase l + nodeOffset l idx)) 256

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
    (hhi : haltIdx < 332)
    (hi : openingInstr haltIdx = .base .ECALL)
    (hpc : sHalt.pc = pcAt haltIdx)
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

/-! ### 2. MachineState, BitVec, Pack6, and List Helpers -/

private theorem getReg_setReg_ne' (r r' : Reg) (h : r ≠ r') (s : MachineState) (v : Word) :
    (s.setReg r v).getReg r' = s.getReg r' :=
  MachineState.getReg_setReg_ne s r r' v h

private theorem getReg_setMem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

private theorem getReg_setByte (s : MachineState) (a : Word) (b : BitVec 8) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by cases r <;> rfl

private theorem getByte_setReg (s : MachineState) (r : Reg) (v a : Word) :
    (s.setReg r v).getByte a = s.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem_setReg]

private theorem getByte_setPC (s : MachineState) (v a : Word) :
    (s.setPC v).getByte a = s.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem_setPC]

private theorem pcAt_add4 (idx : Nat) : pcAt idx + 4 = pcAt (idx + 1) := by
  unfold pcAt
  change BitVec.ofNat 64 (0x1000 + 4 * idx) + BitVec.ofNat 64 4 = _
  rw [← BitVec.ofNat_add]
  congr 1

private theorem and_not_one_of_even (n : Nat) (heven : n % 2 = 0) :
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

private theorem pcAt_jalr_return (idx : Nat) :
    (pcAt idx + signExtend12 (0#12)) &&& ~~~1#64 = pcAt idx := by
  have hse0 : signExtend12 (0#12) = 0#64 := by decide
  rw [hse0, BitVec.add_zero]
  exact and_not_one_of_even (0x1000 + 4 * idx) (by omega)

private theorem bv64_ofNat_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

private theorem bv64_ofNat_sub (a b : Nat) (hle : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have h : BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b = BitVec.ofNat 64 a := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel hle]
  have hc := congrArg (fun v : Word => v - BitVec.ofNat 64 b) h.symm
  simpa only [BitVec.add_sub_cancel] using hc

private theorem bv64_add_neg1 (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (4095#12) = BitVec.ofNat 64 n := by
  have hse : (1#64 : Word) + signExtend12 (4095#12) = 0#64 := by decide
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  change BitVec.ofNat 64 n + (1#64 + signExtend12 (4095#12)) = BitVec.ofNat 64 n
  rw [hse, BitVec.add_zero]

private theorem bv64_add_neg8 (n : Nat) (h : 8 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4088#12) = BitVec.ofNat 64 (n - 8) := by
  have hse : (8#64 : Word) + signExtend12 (4088#12) = 0#64 := by decide
  have hn : n = (n - 8) + 8 := by omega
  conv_lhs => rw [hn]
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  change BitVec.ofNat 64 (n - 8) + (8#64 + signExtend12 (4088#12)) = BitVec.ofNat 64 (n - 8)
  rw [hse, BitVec.add_zero]

private theorem bv64_add_neg64 (n : Nat) (h : 64 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4032#12) = BitVec.ofNat 64 (n - 64) := by
  have hse : (64#64 : Word) + signExtend12 (4032#12) = 0#64 := by decide
  have hn : n = (n - 64) + 64 := by omega
  conv_lhs => rw [hn]
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  change BitVec.ofNat 64 (n - 64) + (64#64 + signExtend12 (4032#12)) = BitVec.ofNat 64 (n - 64)
  rw [hse, BitVec.add_zero]

private theorem bv64_shl (a k : Nat) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_mod (a % 2 ^ 64), Nat.mod_mod, ← Nat.mul_mod]

private theorem bv64_ushr (a k : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a >>> k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

private theorem nat_ushr_ushr1 (a k : Nat) : (a >>> k) >>> 1 = a >>> (k + 1) := by
  simp only [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul,
    show (2 : Nat) ^ 1 = 2 from rfl, ← Nat.pow_succ]

private theorem bv64_xor1 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ signExtend12 (1#12) = BitVec.ofNat 64 (a ^^^ 1) := by
  have hse : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  rw [hse]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64)]
  have hlt : a ^^^ 1 < 2 ^ 64 := by
    rcases Nat.even_or_odd' a with ⟨q, rfl | rfl⟩
    · rw [xor_one_even]; omega
    · rw [xor_one_odd]; omega
  rw [Nat.mod_eq_of_lt hlt]

private theorem bv64_xor63_8mul (r : Nat) (hr : r < 8) :
    BitVec.ofNat 64 (8 * r) ^^^ signExtend12 (63#12) = BitVec.ofNat 64 (63 - 8 * r) := by
  interval_cases r <;> decide

private theorem bv64_and1 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& signExtend12 (1#12) = BitVec.ofNat 64 (a % 2) := by
  have hse : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  rw [hse]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (by omega : 1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : a % 2 < 2 ^ 64)]
  change a &&& (2 ^ 1 - 1) = a % 2 ^ 1
  exact Nat.and_two_pow_sub_one_eq_mod a 1

private theorem bv64_ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro heq
  have hn := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hn
  exact hne hn

private theorem byte_zeroExtend_truncate8 (b : Byte) :
    (b.zeroExtend 64).truncate 8 = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth]
  have hlt : b.toNat < 256 := b.isLt
  rw [Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 64), Nat.mod_eq_of_lt hlt]

private theorem bv64_ofNat_truncate8 (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).truncate 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

private theorem bool_byte_zeroExtend (b : Bool) :
    (if b then (1#8 : Byte) else 0#8).zeroExtend 64 = if b then 1#64 else 0#64 := by
  cases b <;> decide

private theorem bool_word_or (a b : Bool) :
    (if a then (1#64 : Word) else 0#64) ||| (if b then 1#64 else 0#64) =
      if (a || b) then 1#64 else 0#64 := by
  cases a <;> cases b <;> decide

private theorem bool_word_truncate8 (b : Bool) :
    (if b then (1#64 : Word) else 0#64).truncate 8 = if b then 1#8 else 0#8 := by
  cases b <;> decide

private theorem bool_word_ne_of_ne {a b : Bool} (h : a ≠ b) :
    (if a then (1#64 : Word) else 0#64) ≠ (if b then 1#64 else 0#64) := by
  cases a <;> cases b <;> first | exact absurd rfl h | decide

private theorem bool_bne_one_of_ne {a b : Bool} (h : a ≠ b) :
    (if (a != b) = true then (1 : Nat) else 0) = 1 := by
  cases a <;> cases b <;> first | exact absurd rfl h | decide

private theorem accessValid_ofNat (a w : Nat) (hle : a + w ≤ 68719476736) (hal : a % w = 0) :
    accessValid (BitVec.ofNat 64 a) w = true := by
  have ha : a < 2 ^ 64 := by omega
  simp only [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by omega, hal⟩

private theorem extractLsb'_extractLsb' {w : Nat} (x : BitVec w) (a m b k : Nat) (h : b + k ≤ m) :
    (x.extractLsb' a m).extractLsb' b k = x.extractLsb' (a + b) k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
    show b + i < m by omega, Nat.add_assoc]

private theorem getMem_extractByte {s : MachineState} {addr j : Nat}
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

private theorem word_or_shl_byte (w v : Word) (r : Nat) (hr : r < 8)
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

private theorem word_ushr1_ushr_byte (v : Word) (r : Nat) (hr : r < 8) (j : Nat) (hj : j < 8) :
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

private theorem word_mask_low_bytes (v : Word) (m : Nat) (hm : m ≤ 8) (j : Nat) (hj : j < 8) :
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

private theorem word_truncate8_eq_extractLsb'0 (w : Word) :
    w.truncate 8 = w.extractLsb' 0 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp [BitVec.truncate, hb]

private theorem word_ushr8_extractLsb' (w : Word) (j : Nat) (hj : j + 1 < 8) :
    (w >>> 8).extractLsb' (8 * j) 8 = w.extractLsb' (8 * (j + 1)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hb, decide_true, Bool.true_and]
  congr 1
  omega

private theorem word_tail6_from_hi (v : Word) (d : Digest)
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

private theorem tail_or_shl_eq_add (tBuf tCnt tVal : Nat)
    (hcnt : tCnt < 8) (hbuf : tBuf < 2 ^ tCnt) (hval : tVal < 64) :
    BitVec.ofNat 64 tBuf ||| (BitVec.ofNat 64 tVal <<< tCnt) =
      BitVec.ofNat 64 (tBuf + tVal * 2 ^ tCnt) := by
  have hpow : 2 ^ tCnt ≤ 128 := by
    have h1 : 2 ^ tCnt ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 7 = 128 := by decide
    omega
  rw [bv64_shl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : tBuf < 2 ^ 64),
    Nat.mod_eq_of_lt (by nlinarith : tVal * 2 ^ tCnt < 2 ^ 64),
    Nat.mod_eq_of_lt (by nlinarith : tBuf + tVal * 2 ^ tCnt < 2 ^ 64)]
  rw [← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hbuf, Nat.shiftLeft_eq,
    Nat.add_comm]

private theorem pack6Step_bounds (acc : List Byte) (buf cnt n : Nat) (t : BitVec 6)
    (hcnt : cnt < 8) (hbuf : buf < 2 ^ cnt) (hbits : 8 * acc.length + cnt = 6 * n) :
    let st := pack6Step (acc, buf, cnt) t
    st.2.2 < 8 ∧ st.2.1 < 2 ^ st.2.2 ∧ 8 * st.1.length + st.2.2 = 6 * (n + 1) := by
  unfold pack6Step
  dsimp only
  have ht : t.toNat < 64 := t.isLt
  have hbuf' : buf + t.toNat * 2 ^ cnt < 2 ^ (cnt + 6) := by
    rw [Nat.pow_add]
    have h64 : 2 ^ 6 = 64 := by decide
    rw [h64]
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

private theorem pack6_foldl_bounds_aux (tails : List (BitVec 6)) :
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
    have h1 := pack6Step_bounds acc buf cnt n t hcnt hbuf hbits
    rcases hst : pack6Step (acc, buf, cnt) t with ⟨acc1, buf1, cnt1⟩
    rw [hst] at h1
    have h2 := ih acc1 buf1 cnt1 (n + 1) h1.1 h1.2.1 h1.2.2
    simpa only [show n + 1 + rest.length = n + (rest.length + 1) by omega] using h2

private theorem pack6_foldl_bounds (tails : List (BitVec 6)) :
    let st := tails.foldl pack6Step ([], 0, 0)
    st.2.2 < 8 ∧ st.2.1 < 2 ^ st.2.2 ∧ 8 * st.1.length + st.2.2 = 6 * tails.length := by
  simpa using pack6_foldl_bounds_aux tails [] 0 0 0 (by omega) (by decide) (by simp)

private theorem list_getElem_append_left {α : Type} (l1 l2 : List α) (i : Nat) (h : i < l1.length) :
    (l1 ++ l2)[i]'(by simp; omega) = l1[i] := by
  induction l1 generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    cases i with
    | zero => rfl
    | succ k => exact ih k (by simp at h; omega)

private theorem list_getElem_append_right {α : Type} (l1 l2 : List α) (i : Nat)
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

private theorem list_mem_exists_getElem {α : Type} {l : List α} {x : α} (hx : x ∈ l) :
    ∃ (u : Nat) (hu : u < l.length), l[u]'hu = x := by
  induction l with
  | nil => cases hx
  | cons a rest ih =>
    rcases List.mem_cons.mp hx with rfl | hrest
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨u, hu, heq⟩ := ih hrest
      exact ⟨u + 1, by simp; omega, heq⟩

private theorem sum_range_le_of_le (f : Nat → Nat) {a b : Nat} (h : a ≤ b) :
    (∑ i ∈ Finset.range a, f i) ≤ ∑ i ∈ Finset.range b, f i := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha; exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · rw [Finset.sum_range_succ]
      exact Nat.le_trans (ih hab) (Nat.le_add_right _ _)
    · have ha : a = b + 1 := by omega
      subst ha; exact Nat.le_refl _

private theorem positions_card_le (positions : Positions) : positions.card ≤ 16777216 := by
  have h := Finset.card_le_univ positions
  rw [Fintype.card_fin] at h
  exact h

private theorem levelSize_le_max (l : Nat) (hl : l ≤ 23) : levelSize l ≤ 16777216 := by
  interval_cases l <;> decide

private theorem nodeOffset_lt_treeBytes (l idx : Nat) (hl : l ≤ 23) (hidx : idx < levelSize l) :
    levelBase l + nodeOffset l idx + 32 ≤ treeBytes := by
  by_cases hlt2 : l < 2
  · by_cases h0 : l = 0
    · subst h0
      have hlb : levelBase 0 = 0 := rfl
      have hno : nodeOffset 0 idx = 32 * idx := rfl
      have hls : levelSize 0 = 16777216 := levelSize_0
      have htb : treeBytes = 894785760 := treeBytes_eq
      omega
    · have h1 : l = 1 := by omega
      subst h1
      have hlb : levelBase 1 = 536870912 := by decide
      have hno : nodeOffset 1 idx = 32 * idx := rfl
      have hls : levelSize 1 = 5592406 := levelSize_1
      have htb : treeBytes = 894785760 := treeBytes_eq
      omega
  · by_cases h23 : l < 23
    · have hno : nodeOffset l idx = gapOffset idx := by
        unfold nodeOffset; rw [if_neg hlt2]
      have hg := gapOffset_lt_levelBytes l idx (by omega) h23 hidx
      have hb := levelBase_bound l hl
      rw [hno]; omega
    · have hl23 : l = 23 := by omega
      subst hl23
      have hls : levelSize 23 = 1 := levelSize_23
      have hidx0 : idx = 0 := by omega
      subst hidx0
      decide

private theorem nodeOffset_align8 (l idx : Nat) : nodeOffset l idx % 8 = 0 := by
  unfold nodeOffset gapOffset
  split <;> omega

private theorem levelBase_align8 (l : Nat) (hl : l ≤ 23) : levelBase l % 8 = 0 := by
  interval_cases l <;> decide

private theorem saltOff_formula (i : Index) :
    rowOff + 72 + (184 * (i.val / 2) + 16 * (i.val % 2)) = saltOff i := by
  unfold saltOff PAIR_STRIDE
  split_ifs <;> omega

private theorem saltOff_align8 (i : Index) : saltOff i % 8 = 0 := by
  unfold saltOff PAIR_STRIDE
  rw [rowOff_eq]
  split_ifs <;> omega

private theorem capMarkOff_step_disjoint (l : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 22) :
    capMarkOff l + levelSize l ≤ capMarkOff (l + 1) := by
  interval_cases l <;> decide

/-! ### 3. Single-Instruction Step Lemmas -/

private theorem step_ADDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ADDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_ADD {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ADD rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADD rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADD rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SUB {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SUB rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SUB rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SUB rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SLLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SLLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SLLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SLLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SRLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SRLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SRLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SRLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SLL {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SLL rd rs1 rs2)) :
    OpenRuns s 1 1
      ((s.setReg rd (s.getReg rs1 <<< ((s.getReg rs2).toNat % 64))).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SLL rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SLL rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 <<< ((s.getReg rs2).toNat % 64))).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 <<< ((s.getReg rs2).toNat % 64))).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SRL {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SRL rd rs1 rs2)) :
    OpenRuns s 1 1
      ((s.setReg rd (s.getReg rs1 >>> ((s.getReg rs2).toNat % 64))).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SRL rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SRL rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 >>> ((s.getReg rs2).toNat % 64))).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 >>> ((s.getReg rs2).toNat % 64))).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_XORI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.XORI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.XORI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.XORI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_ANDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ANDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ANDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ANDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_OR {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.OR rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.OR rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.OR rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_DIVU {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.DIVU rd rs1 rs2)) :
    OpenRuns s 1 4 ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.DIVU rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.DIVU rd rs1 rs2)) =
      some ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_REMU {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.REMU rd rs1 rs2)) :
    OpenRuns s 1 4 ((s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.REMU rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.REMU rd rs1 rs2)) =
      some ((s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_LD {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.LD rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    OpenRuns s 1 1 ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.LD rd rs1 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.LD rd rs1 off)) =
      some ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 8 = true
            then some ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SD {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SD rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    OpenRuns s 1 1
      ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SD rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SD rs1 rs2 off)) =
      some ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 8 = true
            then some ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_LBU {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.LBU rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 1 = true) :
    OpenRuns s 1 1
      ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.LBU rd rs1 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.LBU rd rs1 off)) =
      some ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 1 = true
            then some ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SB {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SB rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 1 = true) :
    OpenRuns s 1 1
      ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SB rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SB rs1 rs2 off)) =
      some ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 1 = true
            then some ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_BEQ_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
    (heq : s.getReg rs1 = s.getReg rs2) (htgt : pcAt idx + signExtend13 off = pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (pcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BEQ rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : (s.getReg rs1 == s.getReg rs2) = true := by rw [heq]; simp
  have hst : ordinaryStep s (.base (.BEQ rs1 rs2 off)) = some (s.setPC (pcAt tgt)) := by
    change some (if (s.getReg rs1 == s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem step_BEQ_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
    (hne : s.getReg rs1 ≠ s.getReg rs2) :
    OpenRuns s 1 1 (s.setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BEQ rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : ¬ ((s.getReg rs1 == s.getReg rs2) = true) := fun h => hne (eq_of_beq h)
  have hst : ordinaryStep s (.base (.BEQ rs1 rs2 off)) = some (s.setPC (pcAt (idx + 1))) := by
    change some (if (s.getReg rs1 == s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_BNE_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
    (hne : s.getReg rs1 ≠ s.getReg rs2) (htgt : pcAt idx + signExtend13 off = pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (pcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BNE rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : (s.getReg rs1 != s.getReg rs2) = true := by
    cases hb : (s.getReg rs1 == s.getReg rs2) with
    | true => exact absurd (eq_of_beq hb) hne
    | false => simp [bne, hb]
  have hst : ordinaryStep s (.base (.BNE rs1 rs2 off)) = some (s.setPC (pcAt tgt)) := by
    change some (if (s.getReg rs1 != s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem step_BNE_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
    (heq : s.getReg rs1 = s.getReg rs2) :
    OpenRuns s 1 1 (s.setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BNE rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : ¬ ((s.getReg rs1 != s.getReg rs2) = true) := by rw [heq]; simp
  have hst : ordinaryStep s (.base (.BNE rs1 rs2 off)) = some (s.setPC (pcAt (idx + 1))) := by
    change some (if (s.getReg rs1 != s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_BLTU_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
    (hlt : (s.getReg rs1).toNat < (s.getReg rs2).toNat)
    (htgt : pcAt idx + signExtend13 off = pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (pcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BLTU rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : BitVec.ult (s.getReg rs1) (s.getReg rs2) = true := by
    simp only [BitVec.ult, decide_eq_true_eq]
    exact hlt
  have hst : ordinaryStep s (.base (.BLTU rs1 rs2 off)) = some (s.setPC (pcAt tgt)) := by
    change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem step_BLTU_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
    (hle : (s.getReg rs2).toNat ≤ (s.getReg rs1).toNat) :
    OpenRuns s 1 1 (s.setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BLTU rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true) := by
    simp only [BitVec.ult, decide_eq_true_eq]
    omega
  have hst : ordinaryStep s (.base (.BLTU rs1 rs2 off)) = some (s.setPC (pcAt (idx + 1))) := by
    change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_BGEU_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BGEU rs1 rs2 off))
    (hle : (s.getReg rs2).toNat ≤ (s.getReg rs1).toNat)
    (htgt : pcAt idx + signExtend13 off = pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (pcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BGEU rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true) := by
    simp only [BitVec.ult, decide_eq_true_eq]
    omega
  have hst : ordinaryStep s (.base (.BGEU rs1 rs2 off)) = some (s.setPC (pcAt tgt)) := by
    change some (if ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true)
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem step_BGEU_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BGEU rs1 rs2 off))
    (hlt : (s.getReg rs1).toNat < (s.getReg rs2).toNat) :
    OpenRuns s 1 1 (s.setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BGEU rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hult : BitVec.ult (s.getReg rs1) (s.getReg rs2) = true := by
    simp only [BitVec.ult, decide_eq_true_eq]
    exact hlt
  have hcond : ¬ ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true) := fun h => h hult
  have hst : ordinaryStep s (.base (.BGEU rs1 rs2 off)) = some (s.setPC (pcAt (idx + 1))) := by
    change some (if ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true)
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_JAL {s : MachineState} {idx tgt : Nat} {rd : Reg} {off : BitVec 21}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.JAL rd off))
    (htgt : pcAt idx + signExtend21 off = pcAt tgt) :
    OpenRuns s 1 1 ((s.setReg rd (pcAt (idx + 1))).setPC (pcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.JAL rd off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.JAL rd off)) =
      some ((s.setReg rd (pcAt (idx + 1))).setPC (pcAt tgt)) := by
    change some ((s.setReg rd (s.pc + 4)).setPC (s.pc + signExtend21 off)) = _
    rw [hpc, pcAt_add4, htgt]
  exact OpenRuns.step hf hst

private theorem step_JALR_x0 {s : MachineState} {idx retIdx : Nat}
    (hidx : idx < 332) (hpc : s.pc = pcAt idx)
    (hi : openingInstr idx = .base (.JALR .x0 .x1 (0#12)))
    (hx1 : s.getReg .x1 = pcAt retIdx) :
    OpenRuns s 1 1 (s.setPC (pcAt retIdx)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.JALR .x0 .x1 (0#12))) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.JALR .x0 .x1 (0#12))) = some (s.setPC (pcAt retIdx)) := by
    change some ((s.setReg .x0 (s.pc + 4)).setPC ((s.getReg .x1 + signExtend12 (0#12)) &&& ~~~1#64)) = _
    rw [show s.setReg .x0 (s.pc + 4) = s from rfl, hx1, pcAt_jalr_return retIdx]
  exact OpenRuns.step hf hst

/-! ### 4. Memory Framing, Dword Writer, and 6-Bit Tail Packer Predicates -/

/-- Read-only regions: trapdoor `[4294971424, 6733261056)`, indices `[6733261056, 6867478784)`,
and embedded metadata `[68719475968, 68719476736)`. -/
def ReadOnlyPreserved (s0 s : MachineState) : Prop :=
  ∀ addr : Word,
    (4294971424 ≤ addr.toNat ∧ addr.toNat < 6867478784) ∨
    (68719475968 ≤ addr.toNat ∧ addr.toNat < 68719476736) →
    s.getMem addr = s0.getMem addr

/-- Exact byte contents of the proof output prefix `[11162446080, 11162446080 + bytes.length)`. -/
def ProofPrefix (s : MachineState) (bytes : List Byte) : Prop :=
  ∀ j (hj : j < bytes.length),
    s.getByte (BitVec.ofNat 64 (11162446080 + j)) = bytes[j]

/-- Exact byte contents of the tail scratch prefix `[tailBufBase, tailBufBase + tailBytes.length)`. -/
def TailBufPrefix (s : MachineState) (tailBytes : List Byte) : Prop :=
  ∀ j (hj : j < tailBytes.length),
    s.getByte (BitVec.ofNat 64 (tailBufBase + j)) = tailBytes[j]

/-- Level `l` cap-mark bytes in `[4096 + capMarkOff l, 4096 + capMarkOff l + levelSize l)`. -/
def CapLevelMarks (s : MachineState) (positions : Positions) (l : Nat) : Prop :=
  ∀ idx < levelSize l,
    s.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + idx)) =
      if capMark positions l idx then 1#8 else 0#8

/-- Exact state of the branchless 64-bit aligned dword-buffered writer for forward proof bytes. -/
private structure WriterState (s : MachineState) (fwdBytes : List Byte) : Prop where
  rx25 : s.getReg .x25 = BitVec.ofNat 64 (11162446080 + 8 * (fwdBytes.length / 8))
  rx13 : s.getReg .x13 = BitVec.ofNat 64 (8 * (fwdBytes.length % 8))
  rx14 : s.getReg .x14 = BitVec.ofNat 64 (63 - 8 * (fwdBytes.length % 8))
  wbufLo : ∀ j (hj : j < fwdBytes.length % 8),
    (s.getReg .x12).extractLsb' (8 * j) 8 =
      fwdBytes[8 * (fwdBytes.length / 8) + j]'(by omega)
  wbufHi : ∀ j, fwdBytes.length % 8 ≤ j → j < 8 →
    (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8
  memDwords : ∀ j (hj : j < 8 * (fwdBytes.length / 8)),
    s.getByte (BitVec.ofNat 64 (11162446080 + j)) = fwdBytes[j]'(by omega)

/-- Exact state of the streaming 6-bit tail packer for emitted 6-bit tails. -/
private structure TailState (s : MachineState) (tails : List (BitVec 6)) : Prop where
  rx31 : s.getReg .x31 = BitVec.ofNat 64 tailBufBase
  rx15 : s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (tails.foldl pack6Step ([], 0, 0)).1.length)
  rx16 : s.getReg .x16 = BitVec.ofNat 64 (tails.foldl pack6Step ([], 0, 0)).2.1
  rx17 : s.getReg .x17 = BitVec.ofNat 64 (tails.foldl pack6Step ([], 0, 0)).2.2
  memTail : TailBufPrefix s (tails.foldl pack6Step ([], 0, 0)).1

private theorem WriterState.of_eq {s1 s2 : MachineState} {fwdBytes : List Byte}
    (hw : WriterState s1 fwdBytes)
    (h25 : s2.getReg .x25 = s1.getReg .x25 := by rfl)
    (h13 : s2.getReg .x13 = s1.getReg .x13 := by rfl)
    (h14 : s2.getReg .x14 = s1.getReg .x14 := by rfl)
    (h12 : s2.getReg .x12 = s1.getReg .x12 := by rfl)
    (hmem : ∀ a, s2.getByte a = s1.getByte a := by intro _; rfl) :
    WriterState s2 fwdBytes :=
  ⟨h25.trans hw.rx25, h13.trans hw.rx13, h14.trans hw.rx14,
   fun j hj => by rw [h12]; exact hw.wbufLo j hj,
   fun j h1 h2 => by rw [h12]; exact hw.wbufHi j h1 h2,
   fun j hj => by rw [hmem]; exact hw.memDwords j hj⟩

private theorem WriterState.castList {s : MachineState} {a b : List Byte}
    (h : a = b) (hw : WriterState s a) : WriterState s b :=
  h ▸ hw

private theorem TailState.of_eq {s1 s2 : MachineState} {tails : List (BitVec 6)}
    (ht : TailState s1 tails)
    (h31 : s2.getReg .x31 = s1.getReg .x31 := by rfl)
    (h15 : s2.getReg .x15 = s1.getReg .x15 := by rfl)
    (h16 : s2.getReg .x16 = s1.getReg .x16 := by rfl)
    (h17 : s2.getReg .x17 = s1.getReg .x17 := by rfl)
    (hmem : ∀ a, s2.getByte a = s1.getByte a := by intro _; rfl) :
    TailState s2 tails :=
  ⟨h31.trans ht.rx31, h15.trans ht.rx15, h16.trans ht.rx16, h17.trans ht.rx17,
   fun j hj => by rw [hmem]; exact ht.memTail j hj⟩

private theorem readOnly_getMem_index {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (ordinal : Nat) (hord : ordinal < positions.card) :
    s.getMem (BitVec.ofNat 64 (6733261056 + 8 * ordinal)) =
      BitVec.ofNat 64 (openingIndex positions ordinal) := by
  have hcard := positions_card_le positions
  have haddr : (BitVec.ofNat 64 (6733261056 + 8 * ordinal)).toNat = 6733261056 + 8 * ordinal := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inl (by omega))]
  exact opening_initial_index trapdoor positions ordinal hord

private theorem readOnly_getMem_data_base {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 24) :
    s.getMem (BitVec.ofNat 64 (68719475968 + 32 * l)) = BitVec.ofNat 64 (levelBase l) := by
  have haddr : (BitVec.ofNat 64 (68719475968 + 32 * l)).toNat = 68719475968 + 32 * l := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), opening_initial_data_dword trapdoor positions (32 * l) (by omega)]
  exact openingData_dword_0 ⟨l, hl⟩

private theorem readOnly_getMem_data_size {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 24) :
    s.getMem (BitVec.ofNat 64 (68719475968 + 32 * l + 8)) = BitVec.ofNat 64 (levelSize l) := by
  have haddr : (BitVec.ofNat 64 (68719475968 + 32 * l + 8)).toNat = 68719475968 + 32 * l + 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), show 68719475968 + 32 * l + 8 = 68719475968 + (32 * l + 8) by omega,
    opening_initial_data_dword trapdoor positions (32 * l + 8) (by omega)]
  exact openingData_dword_1 ⟨l, hl⟩

private theorem readOnly_getMem_data_markOff {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 24) :
    s.getMem (BitVec.ofNat 64 (68719475968 + 32 * l + 16)) = BitVec.ofNat 64 (capMarkOff l) := by
  have haddr : (BitVec.ofNat 64 (68719475968 + 32 * l + 16)).toNat = 68719475968 + 32 * l + 16 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), show 68719475968 + 32 * l + 16 = 68719475968 + (32 * l + 16) by omega,
    opening_initial_data_dword trapdoor positions (32 * l + 16) (by omega)]
  exact openingData_dword_2 ⟨l, hl⟩

private theorem readOnly_getByte_trapdoor {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (off : Nat) (hoff : off < 2438289632) :
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
    left
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  change extractByte (s.getMem (alignToDword (BitVec.ofNat 64 a))) (byteOffset (BitVec.ofNat 64 a)) = _
  rw [hmem]
  exact opening_initial_trapdoor_byte trapdoor positions off hoff

private theorem readOnly_getMem_trapdoor_byte {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (off j : Nat) (hal : off % 8 = 0) (hj : j < 8) (hbd : off + 8 ≤ 2438289632) :
    (s.getMem (BitVec.ofNat 64 (4294971424 + off))).extractLsb' (8 * j) 8 =
      trapdoor.extractLsb' (8 * (off + j)) 8 := by
  rw [getMem_extractByte (by omega) hj, Nat.add_assoc]
  exact readOnly_getByte_trapdoor hro (off + j) (by omega)

private theorem readOnly_setMem_proof {s0 s : MachineState} (dst : Nat) (val : Word)
    (hro : ReadOnlyPreserved s0 s) (hlo : 11162446080 ≤ dst) (hhi : dst + 8 ≤ 19832079232) :
    ReadOnlyPreserved s0 (s.setMem (BitVec.ofNat 64 dst) val) := by
  intro addr had
  have hne : addr ≠ BitVec.ofNat 64 dst := by
    intro heq
    have hn := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
    rcases had with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  rw [MachineState.getMem_setMem_ne hne]
  exact hro addr had

private theorem readOnly_setByte_cap {s0 s : MachineState} (dst : Nat) (b : BitVec 8)
    (hro : ReadOnlyPreserved s0 s) (hlo : 4096 ≤ dst) (hhi : dst < 5120) :
    ReadOnlyPreserved s0 (s.setByte (BitVec.ofNat 64 dst) b) := by
  intro addr had
  have hdec : alignToDword (BitVec.ofNat 64 dst) = BitVec.ofNat 64 (8 * (dst / 8)) := by
    have h1 := alignToDword_ofNat_eq (8 * (dst / 8)) (dst % 8) (by omega) (by omega)
    simpa only [show 8 * (dst / 8) + dst % 8 = dst by omega] using h1
  have hne : addr ≠ alignToDword (BitVec.ofNat 64 dst) := by
    intro heq
    rw [hdec] at heq
    have hn := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
    rcases had with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  simp only [MachineState.setByte, MachineState.getMem_setMem_ne hne]
  exact hro addr had

private theorem readOnly_setByte_tail {s0 s : MachineState} (dst : Nat) (b : BitVec 8)
    (hro : ReadOnlyPreserved s0 s) (hlo : tailBufBase ≤ dst) (hhi : dst < 68719475968) :
    ReadOnlyPreserved s0 (s.setByte (BitVec.ofNat 64 dst) b) := by
  intro addr had
  have htb : tailBufBase = 20000000000 := rfl
  have hdec : alignToDword (BitVec.ofNat 64 dst) = BitVec.ofNat 64 (8 * (dst / 8)) := by
    have h1 := alignToDword_ofNat_eq (8 * (dst / 8)) (dst % 8) (by omega) (by omega)
    simpa only [show 8 * (dst / 8) + dst % 8 = dst by omega] using h1
  have hne : addr ≠ alignToDword (BitVec.ofNat 64 dst) := by
    intro heq
    rw [hdec] at heq
    have hn := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
    rcases had with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  simp only [MachineState.setByte, MachineState.getMem_setMem_ne hne]
  exact hro addr had

private theorem writerState_setByte_outside {s : MachineState} {fwdBytes : List Byte} (dst : Nat)
    (b : BitVec 8) (hw : WriterState s fwdBytes) (hbd : fwdBytes.length ≤ 8669633152)
    (hout : dst < 11162446080 ∨ 19832079232 ≤ dst) (hdst : dst < 2 ^ 64) :
    WriterState (s.setByte (BitVec.ofNat 64 dst) b) fwdBytes :=
  ⟨by rw [getReg_setByte]; exact hw.rx25,
   by rw [getReg_setByte]; exact hw.rx13,
   by rw [getReg_setByte]; exact hw.rx14,
   fun j hj => by rw [getReg_setByte]; exact hw.wbufLo j hj,
   fun j h1 h2 => by rw [getReg_setByte]; exact hw.wbufHi j h1 h2,
   fun j hj => by
     rw [set_byte_read, if_neg (bv64_ofNat_ne (by omega) hdst (by omega))]
     exact hw.memDwords j hj⟩

private theorem tailState_setByte_outside {s : MachineState} {tails : List (BitVec 6)} (dst : Nat)
    (b : BitVec 8) (ht : TailState s tails) (htbd : tails.length ≤ 200000000)
    (hdst : dst < tailBufBase) :
    TailState (s.setByte (BitVec.ofNat 64 dst) b) tails :=
  ⟨by rw [getReg_setByte]; exact ht.rx31,
   by rw [getReg_setByte]; exact ht.rx15,
   by rw [getReg_setByte]; exact ht.rx16,
   by rw [getReg_setByte]; exact ht.rx17,
   fun j hj => by
     have htb : tailBufBase = 20000000000 := rfl
     have hlen := (pack6_foldl_bounds tails).2.2
     rw [set_byte_read, if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
     exact ht.memTail j hj⟩

private theorem tailState_of_mem_eq {s1 s2 : MachineState} {tails : List (BitVec 6)}
    (ht : TailState s1 tails) (htbd : tails.length ≤ 200000000)
    (hreg : ∀ r, r = .x15 ∨ r = .x16 ∨ r = .x17 ∨ r = .x31 → s2.getReg r = s1.getReg r)
    (hmem : ∀ q, tailBufBase ≤ q → q < 68719475968 →
      s2.getByte (BitVec.ofNat 64 q) = s1.getByte (BitVec.ofNat 64 q)) :
    TailState s2 tails :=
  ⟨by rw [hreg .x31 (by simp)]; exact ht.rx31,
   by rw [hreg .x15 (by simp)]; exact ht.rx15,
   by rw [hreg .x16 (by simp)]; exact ht.rx16,
   by rw [hreg .x17 (by simp)]; exact ht.rx17,
   fun j hj => by
     have htb : tailBufBase = 20000000000 := rfl
     have hlen := (pack6_foldl_bounds tails).2.2
     rw [hmem (tailBufBase + j) (by omega) (by omega)]
     exact ht.memTail j hj⟩

private theorem chunk_tdSalt (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index)
    (j : Nat) (hj : j < 24) :
    trapdoor.extractLsb' (8 * (saltOff i + j)) 8 =
      (bitsToBytes (tdSalt trapdoor i) 24)[j]'(by simp [bitsToBytes]; exact hj) := by
  simp only [bitsToBytes, List.getElem_map, List.getElem_range, tdSalt]
  rw [extractLsb'_extractLsb' trapdoor (8 * saltOff i) 192 (8 * j) 8 (by omega)]
  congr 1
  omega

private theorem chunk_tdNode (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (l idx n j : Nat) (hn : n ≤ 32) (hj : j < n) :
    trapdoor.extractLsb' (8 * (levelBase l + nodeOffset l idx + j)) 8 =
      (bitsToBytes (tdNode trapdoor l idx) n)[j]'(by simp [bitsToBytes]; exact hj) := by
  simp only [bitsToBytes, List.getElem_map, List.getElem_range, tdNode]
  rw [extractLsb'_extractLsb' trapdoor (8 * (levelBase l + nodeOffset l idx)) 256 (8 * j) 8 (by omega)]
  congr 1
  omega


/-! ### 5. Branchless Dword Writer & Streaming 6-Bit Tail Subroutines (`207..331`) -/

private theorem openRuns_emit_dword {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base srcOff qBase k : Nat} {imm : BitVec 12}
    {cur chunk8 : List Byte}
    (hbase : base + 5 < 332)
    (himm : signExtend12 imm = BitVec.ofNat 64 (8 * k))
    (hi0 : openingInstr base = .base (.LD .x5 .x10 imm))
    (hi1 : openingInstr (base + 1) = .base (.SLL .x6 .x5 .x13))
    (hi2 : openingInstr (base + 2) = .base (.OR .x12 .x12 .x6))
    (hi3 : openingInstr (base + 3) = .base (.SD .x25 .x12 imm))
    (hi4 : openingInstr (base + 4) = .base (.SRLI .x5 .x5 (1#6)))
    (hi5 : openingInstr (base + 5) = .base (.SRL .x12 .x5 .x14))
    (hpc : s.pc = pcAt base)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (11162446080 + 8 * qBase))
    (hqeq : cur.length / 8 = qBase + k)
    (hx13 : s.getReg .x13 = BitVec.ofNat 64 (8 * (cur.length % 8)))
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (63 - 8 * (cur.length % 8)))
    (hwLo : ∀ j (hj : j < cur.length % 8),
      (s.getReg .x12).extractLsb' (8 * j) 8 = cur[8 * (cur.length / 8) + j]'(by omega))
    (hwHi : ∀ j, cur.length % 8 ≤ j → j < 8 →
      (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8)
    (hmem : ∀ j (hj : j < 8 * (cur.length / 8)),
      s.getByte (BitVec.ofNat 64 (11162446080 + j)) = cur[j]'(by omega))
    (hsrc_al : srcOff % 8 = 0)
    (hsrc_bd : srcOff + 8 * k + 8 ≤ 2438289632)
    (hcur_bd : cur.length + 8 ≤ 8669633152)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hclen : chunk8.length = 8)
    (hchunk : ∀ j (hj : j < 8),
      trapdoor.extractLsb' (8 * (srcOff + 8 * k + j)) 8 = chunk8[j]'(by omega)) :
    let cur' := cur ++ chunk8
    ∃ s', OpenRuns s 6 6 s' ∧
      s'.pc = pcAt (base + 6) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → s'.getReg r = s.getReg r) ∧
      (∀ j (hj : j < cur'.length % 8),
        (s'.getReg .x12).extractLsb' (8 * j) 8 = cur'[8 * (cur'.length / 8) + j]'(by omega)) ∧
      (∀ j, cur'.length % 8 ≤ j → j < 8 →
        (s'.getReg .x12).extractLsb' (8 * j) 8 = 0#8) ∧
      (∀ j (hj : j < 8 * (cur'.length / 8)),
        s'.getByte (BitVec.ofNat 64 (11162446080 + j)) = cur'[j]'(by omega)) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      (∀ q < 5120, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475968 →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro cur'
  set r := cur.length % 8
  set q := cur.length / 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  have hcur'_len : cur'.length = cur.length + 8 := by simp [cur', hclen]
  have happ_len : (cur ++ chunk8).length = cur.length + 8 := by simp [hclen]
  have hq' : cur'.length / 8 = q + 1 := by omega
  have hr' : cur'.length % 8 = r := by omega
  set v := s.getMem (BitVec.ofNat 64 (4294971424 + (srcOff + 8 * k)))
  have hv_byte : ∀ j (hj : j < 8), v.extractLsb' (8 * j) 8 = chunk8[j]'(by omega) := by
    intro j hj
    rw [readOnly_getMem_trapdoor_byte hro (srcOff + 8 * k) j (by omega) hj (by omega)]
    exact hchunk j hj
  -- +0: LD x5, imm(x10)
  have hsrcAddr : s.getReg .x10 + signExtend12 imm =
      BitVec.ofNat 64 (4294971424 + (srcOff + 8 * k)) := by
    rw [hx10, himm, bv64_ofNat_add, Nat.add_assoc]
  have h0 := step_LD (by omega) hpc hi0
    (by rw [hsrcAddr]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s1 := (s.setReg .x5 v).setPC (pcAt (base + 1))
  have h0' : OpenRuns s 1 1 s1 := by simpa only [hsrcAddr, v, s1] using h0
  -- +1: SLL x6, x5, x13
  have h1 := step_SLL (by omega) (rfl : s1.pc = pcAt (base + 1)) hi1
  have hx13_mod : (s1.getReg .x13).toNat % 64 = 8 * r := by
    have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hx13
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s2 := (s1.setReg .x6 (v <<< (8 * r))).setPC (pcAt (base + 2))
  have h1' : OpenRuns s1 1 1 s2 := by
    simpa only [show s1.getReg .x5 = v from rfl, hx13_mod, s2, show base + 1 + 1 = base + 2 by omega] using h1
  -- +2: OR x12, x12, x6
  set w := s.getReg .x12
  set wOut := w ||| (v <<< (8 * r))
  have h2 := step_OR (by omega) (rfl : s2.pc = pcAt (base + 2)) hi2
  let s3 := (s2.setReg .x12 wOut).setPC (pcAt (base + 3))
  have h2' : OpenRuns s2 1 1 s3 := by
    have hr12 : s2.getReg .x12 = w := rfl
    have hr6 : s2.getReg .x6 = v <<< (8 * r) := rfl
    simpa only [hr12, hr6, wOut, s3, show base + 2 + 1 = base + 3 by omega] using h2
  -- +3: SD x25, x12, imm
  have hdstAddr : s3.getReg .x25 + signExtend12 imm = BitVec.ofNat 64 (11162446080 + 8 * q) := by
    have hr25 : s3.getReg .x25 = BitVec.ofNat 64 (11162446080 + 8 * qBase) := hx25
    rw [hr25, himm, bv64_ofNat_add]; congr 1; omega
  have h3 := step_SD (by omega) (rfl : s3.pc = pcAt (base + 3)) hi3
    (by rw [hdstAddr]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s4 := (s3.setMem (BitVec.ofNat 64 (11162446080 + 8 * q)) wOut).setPC (pcAt (base + 4))
  have h3' : OpenRuns s3 1 1 s4 := by
    simpa only [hdstAddr, show s3.getReg .x12 = wOut from rfl, s4, show base + 3 + 1 = base + 4 by omega] using h3
  -- +4: SRLI x5, x5, 1
  have h4 := step_SRLI (by omega) (rfl : s4.pc = pcAt (base + 4)) hi4
  let s5 := (s4.setReg .x5 (v >>> 1)).setPC (pcAt (base + 5))
  have h4' : OpenRuns s4 1 1 s5 := by
    have hr5 : s4.getReg .x5 = v := by
      simp only [s4, MachineState.getReg_setPC, getReg_setMem, s3, s2, s1]
      rfl
    simpa only [hr5, show (1#6 : BitVec 6).toNat = 1 from rfl, s5, show base + 4 + 1 = base + 5 by omega] using h4
  -- +5: SRL x12, x5, x14
  set wNew := (v >>> 1) >>> (63 - 8 * r)
  have h5 := step_SRL (by omega) (rfl : s5.pc = pcAt (base + 5)) hi5
  have hx14_mod : (s5.getReg .x14).toNat % 64 = 63 - 8 * r := by
    have h : s5.getReg .x14 = BitVec.ofNat 64 (63 - 8 * r) := by
      simp only [s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
        getReg_setReg_ne' .x5 .x14 (by decide),
        getReg_setReg_ne' .x12 .x14 (by decide),
        getReg_setReg_ne' .x6 .x14 (by decide)]
      exact hx14
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 63 - 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s6 := (s5.setReg .x12 wNew).setPC (pcAt (base + 6))
  have h5' : OpenRuns s5 1 1 s6 := by
    simpa only [show s5.getReg .x5 = v >>> 1 from rfl, hx14_mod, wNew, s6,
      show base + 5 + 1 = base + 6 by omega] using h5
  have htot := ((((h0'.trans h1').trans h2').trans h3').trans h4').trans h5'
  have hmem6 : ∀ a, s6.getByte a =
      (s.setMem (BitVec.ofNat 64 (11162446080 + 8 * q)) wOut).getByte a := fun a => by
    simp only [s6, s5, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
    rfl
  refine ⟨s6, htot, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro reg h5ne h6ne h12ne
    simp only [s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
      getReg_setReg_ne' .x12 reg (Ne.symm h12ne),
      getReg_setReg_ne' .x5 reg (Ne.symm h5ne),
      getReg_setReg_ne' .x6 reg (Ne.symm h6ne)]
  · intro j hj
    have hjr : j < r := by omega
    have hbyte := word_ushr1_ushr_byte v r hr j (by omega)
    rw [if_pos hjr, hv_byte (8 - r + j) (by omega)] at hbyte
    change wNew.extractLsb' (8 * j) 8 = _
    rw [hbyte, list_getElem_append_right cur chunk8 (8 * (cur'.length / 8) + j) (by omega) (by omega)]
    congr 1; omega
  · intro j hj1 hj2
    have hbyte := word_ushr1_ushr_byte v r hr j hj2
    rw [if_neg (by omega)] at hbyte
    exact hbyte
  · intro j hj
    rw [hmem6]
    by_cases hlt : j < 8 * q
    · rw [setMem_getByte_ofNat s (11162446080 + 8 * q) (11162446080 + j) wOut
        (by omega) (by omega) (by omega) (by omega)]
      rw [hmem j hlt, list_getElem_append_left cur chunk8 j (by omega)]
    · have hu : j - 8 * q < 8 := by omega
      have hadd : 11162446080 + 8 * q + (j - 8 * q) = 11162446080 + j := by omega
      rw [← hadd, setMem_getByte_inside s (11162446080 + 8 * q) (j - 8 * q) wOut (by omega) hu]
      rw [word_or_shl_byte w v r hr hwHi (j - 8 * q) hu]
      by_cases hur : j - 8 * q < r
      · rw [if_pos hur, hwLo (j - 8 * q) hur, list_getElem_append_left cur chunk8 j (by omega)]
        congr 1; omega
      · rw [if_neg hur, hv_byte (j - 8 * q - r) (by omega),
          list_getElem_append_right cur chunk8 j (by omega) (by omega)]
        congr 1; omega
  · intro addr had
    change (s.setMem (BitVec.ofNat 64 (11162446080 + 8 * q)) wOut).getMem addr = _
    exact readOnly_setMem_proof (11162446080 + 8 * q) wOut hro (by omega) (by omega) addr had
  · intro a ha
    rw [hmem6, setMem_getByte_ofNat s (11162446080 + 8 * q) a wOut
      (by omega) (by omega) (by omega) (by omega)]
  · intro a ha1 ha2
    have htb : tailBufBase = 20000000000 := rfl
    rw [hmem6, setMem_getByte_ofNat s (11162446080 + 8 * q) a wOut
      (by omega) (by omega) (by omega) (by omega)]

private theorem openRuns_emit_3dwords {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base srcOff : Nat}
    {fwdBytes chunk24 : List Byte}
    (hbase : base + 18 < 332)
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
    (hpc : s.pc = pcAt base)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0)
    (hsrc_bd : srcOff + 24 ≤ 2438289632)
    (hbd : fwdBytes.length + 24 ≤ 8669633152)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (hclen : chunk24.length = 24)
    (hchunk : ∀ j (hj : j < 24),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk24[j]'(by omega)) :
    ∃ s', OpenRuns s 19 19 s' ∧
      s'.pc = pcAt (base + 19) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ chunk24) ∧
      (∀ q < 5120, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475968 →
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
    openRuns_emit_dword (base := base) (srcOff := srcOff) (qBase := qBase) (k := 0) (imm := 0#12)
      (cur := fwdBytes) (chunk8 := c0) (by omega) (by decide)
      hc0.1 hc0.2.1 hc0.2.2.1 hc0.2.2.2.1 hc0.2.2.2.2.1 hc0.2.2.2.2.2
      hpc hx10 hw.rx25 (by omega) hw.rx13 hw.rx14 hw.wbufLo hw.wbufHi hw.memDwords
      hsrc_al (by omega) (by omega) hro hc0_len (fun j hj => by
        simpa [c0, List.getElem_take] using hchunk j (by omega))
  have hlen1 : (fwdBytes ++ c0).length = fwdBytes.length + 8 := by simp [hc0_len]
  obtain ⟨s2, hr2, hpc2, hreg2, hwLo2, hwHi2, hmem2, hro2, hcap2, htail2⟩ :=
    openRuns_emit_dword (base := base + 6) (srcOff := srcOff) (qBase := qBase) (k := 1) (imm := 8#12)
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
    openRuns_emit_dword (base := base + 12) (srcOff := srcOff) (qBase := qBase) (k := 2) (imm := 16#12)
      (cur := (fwdBytes ++ c0) ++ c1) (chunk8 := c2) (by omega) (by decide)
      hc2.1 hc2.2.1 hc2.2.2.1 hc2.2.2.2.1 hc2.2.2.2.2.1 hc2.2.2.2.2.2
      hpc2 (by rw [hreg2 .x10 (by decide) (by decide) (by decide), hreg1 .x10 (by decide) (by decide) (by decide)]; exact hx10)
      (by rw [hreg2 .x25 (by decide) (by decide) (by decide), hreg1 .x25 (by decide) (by decide) (by decide)]; exact hw.rx25)
      (by omega)
      (by rw [hreg2 .x13 (by decide) (by decide) (by decide), hreg1 .x13 (by decide) (by decide) (by decide), hw.rx13]; congr 1; omega)
      (by rw [hreg2 .x14 (by decide) (by decide) (by decide), hreg1 .x14 (by decide) (by decide) (by decide), hw.rx14]; congr 1; omega)
      hwLo2 hwHi2 hmem2 hsrc_al (by omega) (by omega) hro2 hc2_len (fun j hj => by
        simpa [c2, List.getElem_drop, Nat.add_assoc] using hchunk (16 + j) (by omega))
  -- +18: ADDI x25, x25, 24
  have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
  have hadvStep := step_ADDI (by omega) (by simpa only [show base + 12 + 6 = base + 18 by omega] using hpc3) hadv
  have hx25_3 : s3.getReg .x25 = BitVec.ofNat 64 (11162446080 + 8 * qBase) := by
    rw [hreg3 .x25 (by decide) (by decide) (by decide),
      hreg2 .x25 (by decide) (by decide) (by decide),
      hreg1 .x25 (by decide) (by decide) (by decide)]
    exact hw.rx25
  have hnew25 : s3.getReg .x25 + signExtend12 (24#12) =
      BitVec.ofNat 64 (11162446080 + 8 * ((fwdBytes ++ chunk24).length / 8)) := by
    rw [hx25_3, hse24, bv64_ofNat_add]; congr 1
    simp only [List.length_append, hclen]; omega
  let s4 := (s3.setReg .x25 (BitVec.ofNat 64 (11162446080 + 8 * ((fwdBytes ++ chunk24).length / 8)))).setPC
    (pcAt (base + 19))
  have hadv' : OpenRuns s3 1 1 s4 := by
    simpa only [hnew25, s4, show base + 18 + 1 = base + 19 by omega] using hadvStep
  have hpres3 : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → s3.getReg r = s.getReg r := fun r h5 h6 h12 => by
    rw [hreg3 r h5 h6 h12, hreg2 r h5 h6 h12, hreg1 r h5 h6 h12]
  refine ⟨s4, ((hr1.trans hr2).trans hr3).trans hadv', rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h5 h6 h12 h25
    simp only [s4, MachineState.getReg_setPC, getReg_setReg_ne' .x25 r (Ne.symm h25)]
    exact hpres3 r h5 h6 h12
  · intro a ha
    simp only [s4, MachineState.getMem_setPC, MachineState.getMem_setReg]
    exact hro3 a ha
  · refine WriterState.castList hcur_eq ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcur_eq]; rfl
    · simp only [s4, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x13 (by decide)]
      rw [hpres3 .x13 (by decide) (by decide) (by decide), hw.rx13, hcur_eq]; congr 1
      simp only [List.length_append, hclen]; omega
    · simp only [s4, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x14 (by decide)]
      rw [hpres3 .x14 (by decide) (by decide) (by decide), hw.rx14, hcur_eq]; congr 1
      simp only [List.length_append, hclen]; omega
    · intro j hj
      simp only [s4, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x12 (by decide)]
      exact hwLo3 j hj
    · intro j h1 h2
      simp only [s4, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x12 (by decide)]
      exact hwHi3 j h1 h2
    · intro j hj
      simp only [s4, getByte_setPC, getByte_setReg]
      exact hmem3 j hj
  · intro a ha
    simp only [s4, getByte_setPC, getByte_setReg]
    rw [hcap3 a ha, hcap2 a ha, hcap1 a ha]
  · intro a ha1 ha2
    simp only [s4, getByte_setPC, getByte_setReg]
    rw [htail3 a ha1 ha2, htail2 a ha1 ha2, htail1 a ha1 ha2]

private theorem openRuns_emit_partial {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base m : Nat} {immBits : BitVec 12}
    {fwdBytes chunkM : List Byte}
    (hbase : base + 10 < 332) (hm1 : 1 ≤ m) (hm2 : m < 8)
    (himm : signExtend12 immBits = BitVec.ofNat 64 (8 * m))
    (hbr : pcAt (base + 4) + signExtend13 (24#13) = pcAt (base + 10))
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
    (hpc : s.pc = pcAt base)
    (hbd : fwdBytes.length + m ≤ 8669633152)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (hclen : chunkM.length = m)
    (hx5 : ∀ j (hj : j < 8),
      (s.getReg .x5).extractLsb' (8 * j) 8 =
        if hj' : j < m then chunkM[j]'(by omega) else 0#8) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 11 ∧
      s'.pc = pcAt (base + 11) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x25 →
        s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ chunkM) ∧
      (∀ q < 5120, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475968 →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  set r := fwdBytes.length % 8
  set q := fwdBytes.length / 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  set v := s.getReg .x5
  set w := s.getReg .x12
  set wOut := w ||| (v <<< (8 * r))
  -- +0: SLL x6, x5, x13
  have h0 := step_SLL (by omega) hpc hc.1
  have hx13_mod : (s.getReg .x13).toNat % 64 = 8 * r := by
    rw [hw.rx13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s1 := (s.setReg .x6 (v <<< (8 * r))).setPC (pcAt (base + 1))
  have h0' : OpenRuns s 1 1 s1 := by simpa only [hx13_mod, v, s1] using h0
  -- +1: OR x12, x12, x6
  have h1 := step_OR (by omega) (rfl : s1.pc = pcAt (base + 1)) hc.2.1
  let s2 := (s1.setReg .x12 wOut).setPC (pcAt (base + 2))
  have h1' : OpenRuns s1 1 1 s2 := by
    simpa only [show s1.getReg .x12 = w from rfl, show s1.getReg .x6 = v <<< (8 * r) from rfl,
      wOut, s2, show base + 1 + 1 = base + 2 by omega] using h1
  -- +2: ADDI x13, x13, immBits
  have h2 := step_ADDI (by omega) (rfl : s2.pc = pcAt (base + 2)) hc.2.2.1
  let s3 := (s2.setReg .x13 (BitVec.ofNat 64 (8 * (r + m)))).setPC (pcAt (base + 3))
  have h2' : OpenRuns s2 1 1 s3 := by
    have hr13 : s2.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13
    have hv : s2.getReg .x13 + signExtend12 immBits = BitVec.ofNat 64 (8 * (r + m)) := by
      rw [hr13, himm, bv64_ofNat_add]; congr 1; omega
    simpa only [hv, s3, show base + 2 + 1 = base + 3 by omega] using h2
  -- +3: ADDI x7, x0, 64
  have h3 := step_ADDI (by omega) (rfl : s3.pc = pcAt (base + 3)) hc.2.2.2.1
  let s4 := (s3.setReg .x7 64#64).setPC (pcAt (base + 4))
  have h3' : OpenRuns s3 1 1 s4 := by
    have hv : s3.getReg .x0 + signExtend12 (64#12) = 64#64 := by
      change (0#64 : Word) + signExtend12 (64#12) = 64#64; decide
    simpa only [hv, s4, show base + 3 + 1 = base + 4 by omega] using h3
  have hpre : OpenRuns s 4 4 s4 := ((h0'.trans h1').trans h2').trans h3'
  have hx13_4 : (s4.getReg .x13).toNat = 8 * (r + m) := by
    change (BitVec.ofNat 64 (8 * (r + m))).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx7_4 : (s4.getReg .x7).toNat = 64 := by
    change (64#64 : Word).toNat = 64; decide
  have hlen_app : (fwdBytes ++ chunkM).length = fwdBytes.length + m := by simp [hclen]
  by_cases hlt : r + m < 8
  · -- Branch taken to base + 10
    have h4 := step_BLTU_taken (by omega) (rfl : s4.pc = pcAt (base + 4)) hc.2.2.2.2.1
      (by rw [hx13_4, hx7_4]; omega) hbr
    let s10 := s4.setPC (pcAt (base + 10))
    have h10 := step_XORI (by omega) (rfl : s10.pc = pcAt (base + 10)) hc.2.2.2.2.2.2.2.2.2.2
    let s11 := (s10.setReg .x14 (BitVec.ofNat 64 (63 - 8 * (r + m)))).setPC (pcAt (base + 11))
    have h10' : OpenRuns s10 1 1 s11 := by
      have hv : s10.getReg .x13 ^^^ signExtend12 (63#12) = BitVec.ofNat 64 (63 - 8 * (r + m)) := by
        change BitVec.ofNat 64 (8 * (r + m)) ^^^ signExtend12 (63#12) = _
        exact bv64_xor63_8mul (r + m) hlt
      simpa only [hv, s11, show base + 10 + 1 = base + 11 by omega] using h10
    have hq' : (fwdBytes ++ chunkM).length / 8 = q := by omega
    have hr' : (fwdBytes ++ chunkM).length % 8 = r + m := by omega
    refine ⟨6, s11, (hpre.trans h4).trans h10', by omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro reg _ h6 h7 h12 h13 h14 _
      simp only [s11, s10, s4, s3, s2, s1, MachineState.getReg_setPC,
        getReg_setReg_ne' .x14 reg (Ne.symm h14),
        getReg_setReg_ne' .x7 reg (Ne.symm h7),
        getReg_setReg_ne' .x13 reg (Ne.symm h13),
        getReg_setReg_ne' .x12 reg (Ne.symm h12),
        getReg_setReg_ne' .x6 reg (Ne.symm h6)]
    · intro a ha
      simp only [s11, s10, s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]
      exact hro a ha
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq']; exact hw.rx25
      · rw [hr']; rfl
      · rw [hr']; rfl
      · intro j hj
        change wOut.extractLsb' (8 * j) 8 = _
        rw [word_or_shl_byte w v r hr hw.wbufHi j (by omega)]
        by_cases hjr : j < r
        · rw [if_pos hjr, hw.wbufLo j hjr,
            list_getElem_append_left fwdBytes chunkM (8 * ((fwdBytes ++ chunkM).length / 8) + j) (by omega)]
          congr 1; omega
        · rw [if_neg hjr, hx5 (j - r) (by omega), dif_pos (by omega),
            list_getElem_append_right fwdBytes chunkM (8 * ((fwdBytes ++ chunkM).length / 8) + j) (by omega) (by omega)]
          congr 1; omega
      · intro j hj1 hj2
        change wOut.extractLsb' (8 * j) 8 = 0#8
        rw [word_or_shl_byte w v r hr hw.wbufHi j hj2, if_neg (by omega),
          hx5 (j - r) (by omega), dif_neg (by omega)]
      · intro j hj
        simp only [s11, s10, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
        rw [hw.memDwords j (by omega), list_getElem_append_left fwdBytes chunkM j (by omega)]
    · intro a _; simp only [s11, s10, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
    · intro a _ _; simp only [s11, s10, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
  · -- Branch not taken: flush full dword and carry remaining bytes
    have hge : 8 ≤ r + m := by omega
    have hq' : (fwdBytes ++ chunkM).length / 8 = q + 1 := by omega
    have hr' : (fwdBytes ++ chunkM).length % 8 = r + m - 8 := by omega
    have h4 := step_BLTU_not_taken (by omega) (rfl : s4.pc = pcAt (base + 4)) hc.2.2.2.2.1
      (by rw [hx13_4, hx7_4]; omega)
    let s5 := s4.setPC (pcAt (base + 5))
    -- +5: SD x25, x12, 0
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hdstAddr : s5.getReg .x25 + signExtend12 (0#12) = BitVec.ofNat 64 (11162446080 + 8 * q) := by
      have hr25 : s5.getReg .x25 = BitVec.ofNat 64 (11162446080 + 8 * q) := hw.rx25
      rw [hr25, hse0, bv64_ofNat_add, Nat.add_zero]
    have h5 := step_SD (by omega) (rfl : s5.pc = pcAt (base + 5)) hc.2.2.2.2.2.1
      (by rw [hdstAddr]; exact accessValid_ofNat _ 8 (by omega) (by omega))
    let s6 := (s5.setMem (BitVec.ofNat 64 (11162446080 + 8 * q)) wOut).setPC (pcAt (base + 6))
    have h5' : OpenRuns s5 1 1 s6 := by
      simpa only [hdstAddr, show s5.getReg .x12 = wOut from rfl, s6, show base + 5 + 1 = base + 6 by omega] using h5
    -- +6: ADDI x25, x25, 8
    have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
    have h6 := step_ADDI (by omega) (rfl : s6.pc = pcAt (base + 6)) hc.2.2.2.2.2.2.1
    let s7 := (s6.setReg .x25 (BitVec.ofNat 64 (11162446080 + 8 * (q + 1)))).setPC (pcAt (base + 7))
    have h6' : OpenRuns s6 1 1 s7 := by
      have hr25 : s6.getReg .x25 = BitVec.ofNat 64 (11162446080 + 8 * q) := by
        simp only [s6, MachineState.getReg_setPC, getReg_setMem]; exact hw.rx25
      have hv : s6.getReg .x25 + signExtend12 (8#12) = BitVec.ofNat 64 (11162446080 + 8 * (q + 1)) := by
        rw [hr25, hse8, bv64_ofNat_add]; congr 1
      simpa only [hv, s7, show base + 6 + 1 = base + 7 by omega] using h6
    -- +7: SRLI x5, x5, 1
    have h7 := step_SRLI (by omega) (rfl : s7.pc = pcAt (base + 7)) hc.2.2.2.2.2.2.2.1
    let s8 := (s7.setReg .x5 (v >>> 1)).setPC (pcAt (base + 8))
    have h7' : OpenRuns s7 1 1 s8 := by
      have hr5 : s7.getReg .x5 = v := by
        simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
          getReg_setReg_ne' .x25 .x5 (by decide),
          getReg_setReg_ne' .x7 .x5 (by decide),
          getReg_setReg_ne' .x13 .x5 (by decide),
          getReg_setReg_ne' .x12 .x5 (by decide),
          getReg_setReg_ne' .x6 .x5 (by decide)]
        rfl
      simpa only [hr5, show (1#6 : BitVec 6).toNat = 1 from rfl, s8, show base + 7 + 1 = base + 8 by omega] using h7
    -- +8: SRL x12, x5, x14
    set wNew := (v >>> 1) >>> (63 - 8 * r)
    have h8 := step_SRL (by omega) (rfl : s8.pc = pcAt (base + 8)) hc.2.2.2.2.2.2.2.2.1
    have hx14_mod : (s8.getReg .x14).toNat % 64 = 63 - 8 * r := by
      have h : s8.getReg .x14 = BitVec.ofNat 64 (63 - 8 * r) := by
        simp only [s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
          getReg_setReg_ne' .x5 .x14 (by decide),
          getReg_setReg_ne' .x25 .x14 (by decide),
          getReg_setReg_ne' .x7 .x14 (by decide),
          getReg_setReg_ne' .x13 .x14 (by decide),
          getReg_setReg_ne' .x12 .x14 (by decide),
          getReg_setReg_ne' .x6 .x14 (by decide)]
        exact hw.rx14
      rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 63 - 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    let s9 := (s8.setReg .x12 wNew).setPC (pcAt (base + 9))
    have h8' : OpenRuns s8 1 1 s9 := by
      simpa only [show s8.getReg .x5 = v >>> 1 from rfl, hx14_mod, wNew, s9,
        show base + 8 + 1 = base + 9 by omega] using h8
    -- +9: ADDI x13, x13, 4032 (-64)
    have h9 := step_ADDI (by omega) (rfl : s9.pc = pcAt (base + 9)) hc.2.2.2.2.2.2.2.2.2.1
    let s10 := (s9.setReg .x13 (BitVec.ofNat 64 (8 * (r + m - 8)))).setPC (pcAt (base + 10))
    have h9' : OpenRuns s9 1 1 s10 := by
      have hr13 : s9.getReg .x13 = BitVec.ofNat 64 (8 * (r + m)) := by
        simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
          getReg_setReg_ne' .x12 .x13 (by decide),
          getReg_setReg_ne' .x5 .x13 (by decide),
          getReg_setReg_ne' .x25 .x13 (by decide),
          getReg_setReg_ne' .x7 .x13 (by decide)]
        rfl
      have hv : s9.getReg .x13 + signExtend12 (4032#12) = BitVec.ofNat 64 (8 * (r + m - 8)) := by
        rw [hr13, bv64_add_neg64 (8 * (r + m)) (by omega)]; congr 1; omega
      simpa only [hv, s10, show base + 9 + 1 = base + 10 by omega] using h9
    -- +10: XORI x14, x13, 63
    have h10 := step_XORI (by omega) (rfl : s10.pc = pcAt (base + 10)) hc.2.2.2.2.2.2.2.2.2.2
    let s11 := (s10.setReg .x14 (BitVec.ofNat 64 (63 - 8 * (r + m - 8)))).setPC (pcAt (base + 11))
    have h10' : OpenRuns s10 1 1 s11 := by
      have hv : s10.getReg .x13 ^^^ signExtend12 (63#12) = BitVec.ofNat 64 (63 - 8 * (r + m - 8)) := by
        change BitVec.ofNat 64 (8 * (r + m - 8)) ^^^ signExtend12 (63#12) = _
        exact bv64_xor63_8mul (r + m - 8) (by omega)
      simpa only [hv, s11, show base + 10 + 1 = base + 11 by omega] using h10
    have htail_steps := (((((h4.trans h5').trans h6').trans h7').trans h8').trans h9').trans h10'
    have hmem11 : ∀ a, s11.getByte a =
        (s.setMem (BitVec.ofNat 64 (11162446080 + 8 * q)) wOut).getByte a := fun a => by
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
      rfl
    refine ⟨11, s11, hpre.trans htail_steps, Nat.le_refl 11, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro reg h5ne h6ne h7ne h12ne h13ne h14ne h25ne
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
        getReg_setReg_ne' .x14 reg (Ne.symm h14ne),
        getReg_setReg_ne' .x13 reg (Ne.symm h13ne),
        getReg_setReg_ne' .x12 reg (Ne.symm h12ne),
        getReg_setReg_ne' .x5 reg (Ne.symm h5ne),
        getReg_setReg_ne' .x25 reg (Ne.symm h25ne),
        getReg_setReg_ne' .x7 reg (Ne.symm h7ne),
        getReg_setReg_ne' .x6 reg (Ne.symm h6ne)]
    · intro a ha
      change (s.setMem (BitVec.ofNat 64 (11162446080 + 8 * q)) wOut).getMem a = _
      exact readOnly_setMem_proof (11162446080 + 8 * q) wOut hro (by omega) (by omega) a ha
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq']
        simp only [s11, s10, s9, s8, s7, MachineState.getReg_setPC,
          getReg_setReg_ne' .x14 .x25 (by decide),
          getReg_setReg_ne' .x13 .x25 (by decide),
          getReg_setReg_ne' .x12 .x25 (by decide),
          getReg_setReg_ne' .x5 .x25 (by decide)]
        rfl
      · rw [hr']
        simp only [s11, s10, MachineState.getReg_setPC, getReg_setReg_ne' .x14 .x13 (by decide)]
        rfl
      · rw [hr']; rfl
      · intro j hj
        have hj' : j < r + m - 8 := by omega
        have hjr : j < r := by omega
        change wNew.extractLsb' (8 * j) 8 = _
        rw [word_ushr1_ushr_byte v r hr j (by omega), if_pos hjr,
          hx5 (8 - r + j) (by omega), dif_pos (by omega),
          list_getElem_append_right fwdBytes chunkM (8 * ((fwdBytes ++ chunkM).length / 8) + j) (by omega) (by omega)]
        congr 1; omega
      · intro j hj1 hj2
        change wNew.extractLsb' (8 * j) 8 = 0#8
        rw [word_ushr1_ushr_byte v r hr j hj2]
        by_cases hjr : j < r
        · rw [if_pos hjr, hx5 (8 - r + j) (by omega), dif_neg (by omega)]
        · rw [if_neg hjr]
      · intro j hj
        rw [hmem11]
        by_cases hltq : j < 8 * q
        · rw [setMem_getByte_ofNat s (11162446080 + 8 * q) (11162446080 + j) wOut
            (by omega) (by omega) (by omega) (by omega)]
          rw [hw.memDwords j hltq, list_getElem_append_left fwdBytes chunkM j (by omega)]
        · have hu : j - 8 * q < 8 := by omega
          have hadd : 11162446080 + 8 * q + (j - 8 * q) = 11162446080 + j := by omega
          rw [← hadd, setMem_getByte_inside s (11162446080 + 8 * q) (j - 8 * q) wOut (by omega) hu]
          rw [word_or_shl_byte w v r hr hw.wbufHi (j - 8 * q) hu]
          by_cases hur : j - 8 * q < r
          · rw [if_pos hur, hw.wbufLo (j - 8 * q) hur, list_getElem_append_left fwdBytes chunkM j (by omega)]
            congr 1; omega
          · rw [if_neg hur, hx5 (j - 8 * q - r) (by omega), dif_pos (by omega),
              list_getElem_append_right fwdBytes chunkM j (by omega) (by omega)]
            congr 1; omega
    · intro a ha
      rw [hmem11, setMem_getByte_ofNat s (11162446080 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]
    · intro a ha1 ha2
      have htb : tailBufBase = 20000000000 := rfl
      rw [hmem11, setMem_getByte_ofNat s (11162446080 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]

private theorem openRuns_push_tail6 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {d : Digest}
    (hpc : s.pc = pcAt 320)
    (hx11 : (s.getReg .x11).extractLsb' (8 * 5) 8 = d.extractLsb' (8 * 29) 8)
    (hfbd : fwdBytes.length ≤ 8669633152)
    (htbd : tails.length < 200000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 11 ∧
      s'.pc = pcAt 331 ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 →
        s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' fwdBytes ∧
      TailState s' (tails ++ [tail6 d]) ∧
      (∀ q < 5120, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have htb : tailBufBase = 20000000000 := rfl
  set st := tails.foldl pack6Step ([], 0, 0)
  have hst_bd := pack6_foldl_bounds tails
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
  -- 285: SRLI x5, x11, 40
  have h0 := step_SRLI (by omega) hpc (rfl : openingInstr 320 = .base (.SRLI .x5 .x11 (40#6)))
  let s1 := (s.setReg .x5 (s.getReg .x11 >>> 40)).setPC (pcAt 321)
  have h0' : OpenRuns s 1 1 s1 := by
    simpa only [show (40#6 : BitVec 6).toNat = 40 from rfl, s1] using h0
  -- 286: ANDI x5, x5, 63
  have h1 := step_ANDI (by omega) (rfl : s1.pc = pcAt 321)
    (rfl : openingInstr 321 = .base (.ANDI .x5 .x5 (63#12)))
  let s2 := (s1.setReg .x5 (BitVec.ofNat 64 t.toNat)).setPC (pcAt 322)
  have h1' : OpenRuns s1 1 1 s2 := by
    have hv := word_tail6_from_hi (s.getReg .x11) d hx11
    simpa only [show s1.getReg .x5 = s.getReg .x11 >>> 40 from rfl, hv, t, s2] using h1
  -- 287: SLL x6, x5, x17
  have h2 := step_SLL (by omega) (rfl : s2.pc = pcAt 322)
    (rfl : openingInstr 322 = .base (.SLL .x6 .x5 .x17))
  have hx17_mod : (s2.getReg .x17).toNat % 64 = tCnt := by
    have h : s2.getReg .x17 = BitVec.ofNat 64 tCnt := ht.rx17
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tCnt < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s3 := (s2.setReg .x6 (BitVec.ofNat 64 t.toNat <<< tCnt)).setPC (pcAt 323)
  have h2' : OpenRuns s2 1 1 s3 := by
    simpa only [show s2.getReg .x5 = BitVec.ofNat 64 t.toNat from rfl, hx17_mod, s3] using h2
  -- 288: OR x16, x16, x6
  set buf' := tBuf + t.toNat * 2 ^ tCnt
  have hbuf'_lt : buf' < 8192 := by
    have hmul : t.toNat * 2 ^ tCnt ≤ 63 * 128 := Nat.mul_le_mul (by omega) hpow
    change tBuf + t.toNat * 2 ^ tCnt < 8192
    omega
  have h3 := step_OR (by omega) (rfl : s3.pc = pcAt 323)
    (rfl : openingInstr 323 = .base (.OR .x16 .x16 .x6))
  let s4 := (s3.setReg .x16 (BitVec.ofNat 64 buf')).setPC (pcAt 324)
  have h3' : OpenRuns s3 1 1 s4 := by
    have hr16 : s3.getReg .x16 = BitVec.ofNat 64 tBuf := ht.rx16
    have hv : s3.getReg .x16 ||| s3.getReg .x6 = BitVec.ofNat 64 buf' := by
      rw [hr16]; exact tail_or_shl_eq_add tBuf tCnt t.toNat htCnt_lt htBuf_lt ht_lt
    simpa only [hv, s4] using h3
  -- 289: ADDI x17, x17, 6
  have hse6 : signExtend12 (6#12) = BitVec.ofNat 64 6 := by decide
  have h4 := step_ADDI (by omega) (rfl : s4.pc = pcAt 324)
    (rfl : openingInstr 324 = .base (.ADDI .x17 .x17 (6#12)))
  let s5 := (s4.setReg .x17 (BitVec.ofNat 64 (tCnt + 6))).setPC (pcAt 325)
  have h4' : OpenRuns s4 1 1 s5 := by
    have hr17 : s4.getReg .x17 = BitVec.ofNat 64 tCnt := ht.rx17
    rw [hr17, hse6, bv64_ofNat_add] at h4; exact h4
  -- 290: ADDI x7, x0, 8
  have h5 := step_ADDI (by omega) (rfl : s5.pc = pcAt 325)
    (rfl : openingInstr 325 = .base (.ADDI .x7 .x0 (8#12)))
  let s6 := (s5.setReg .x7 8#64).setPC (pcAt 326)
  have h5' : OpenRuns s5 1 1 s6 := by
    have hv : s5.getReg .x0 + signExtend12 (8#12) = 8#64 := by
      change (0#64 : Word) + signExtend12 (8#12) = 8#64; decide
    simpa only [hv, s6] using h5
  have hpre : OpenRuns s 6 6 s6 := ((((h0'.trans h1').trans h2').trans h3').trans h4').trans h5'
  have hx17_6 : (s6.getReg .x17).toNat = tCnt + 6 := by
    change (BitVec.ofNat 64 (tCnt + 6)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx7_6 : (s6.getReg .x7).toNat = 8 := by
    change (8#64 : Word).toNat = 8; decide
  by_cases hlt8 : tCnt + 6 < 8
  · have h6 := step_BLTU_taken (by omega) (rfl : s6.pc = pcAt 326)
      (rfl : openingInstr 326 = .base (.BLTU .x17 .x7 (20#13)))
      (by rw [hx17_6, hx7_6]; exact hlt8)
      (by decide : pcAt 326 + signExtend13 (20#13) = pcAt 331)
    let s7 := s6.setPC (pcAt 331)
    have hpack : (tails ++ [t]).foldl pack6Step ([], 0, 0) = (acc, buf', tCnt + 6) := by
      rw [hfold_app]; unfold pack6Step; dsimp only; rw [if_neg (by omega)]
    refine ⟨7, s7, hpre.trans h6, by omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro r h5ne h6ne h7ne _ h16ne h17ne
      simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC,
        getReg_setReg_ne' .x7 r (Ne.symm h7ne),
        getReg_setReg_ne' .x17 r (Ne.symm h17ne),
        getReg_setReg_ne' .x16 r (Ne.symm h16ne),
        getReg_setReg_ne' .x6 r (Ne.symm h6ne),
        getReg_setReg_ne' .x5 r (Ne.symm h5ne)]
    · intro a ha
      simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]
      exact hro a ha
    · exact ⟨hw.rx25, hw.rx13, hw.rx14, hw.wbufLo, hw.wbufHi, hw.memDwords⟩
    · refine ⟨ht.rx31, ?_, ?_, ?_, ?_⟩
      · rw [hpack]; exact ht.rx15
      · rw [hpack]; rfl
      · rw [hpack]; rfl
      · rw [hpack]; exact ht.memTail
    · intro a _; rfl
  · have hge8 : 8 ≤ tCnt + 6 := by omega
    have h6 := step_BLTU_not_taken (by omega) (rfl : s6.pc = pcAt 326)
      (rfl : openingInstr 326 = .base (.BLTU .x17 .x7 (20#13)))
      (by rw [hx17_6, hx7_6]; exact hge8)
    let s7 := s6.setPC (pcAt 327)
    -- 292: SB x15, x16, 0
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have haddr7 : s7.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + acc.length) := by
      have hr15 : s7.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := ht.rx15
      rw [hr15, hse0, bv64_ofNat_add, Nat.add_zero]
    have h7 := step_SB (by omega) (rfl : s7.pc = pcAt 327)
      (rfl : openingInstr 327 = .base (.SB .x15 .x16 (0#12)))
      (by rw [haddr7]; exact accessValid_ofNat _ 1 (by omega) (by omega))
    let s8 := (s7.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).setPC (pcAt 328)
    have h7' : OpenRuns s7 1 1 s8 := by
      have htr : (s7.getReg .x16).truncate 8 = BitVec.ofNat 8 buf' := by
        change (BitVec.ofNat 64 buf').truncate 8 = _
        exact bv64_ofNat_truncate8 buf' (by omega)
      simpa only [haddr7, htr, s8] using h7
    -- 293: ADDI x15, x15, 1
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have h8 := step_ADDI (by omega) (rfl : s8.pc = pcAt 328)
      (rfl : openingInstr 328 = .base (.ADDI .x15 .x15 (1#12)))
    let s9 := (s8.setReg .x15 (BitVec.ofNat 64 (tailBufBase + (acc ++ [BitVec.ofNat 8 buf']).length))).setPC (pcAt 329)
    have h8' : OpenRuns s8 1 1 s9 := by
      have hr15 : s8.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := by
        simp only [s8, MachineState.getReg_setPC, getReg_setByte]; exact ht.rx15
      have hv : s8.getReg .x15 + signExtend12 (1#12) =
          BitVec.ofNat 64 (tailBufBase + (acc ++ [BitVec.ofNat 8 buf']).length) := by
        rw [hr15, hse1, bv64_ofNat_add, List.length_append, List.length_singleton, Nat.add_assoc]
      simpa only [hv, s9] using h8
    -- 294: SRLI x16, x16, 8
    have h9 := step_SRLI (by omega) (rfl : s9.pc = pcAt 329)
      (rfl : openingInstr 329 = .base (.SRLI .x16 .x16 (8#6)))
    let s10 := (s9.setReg .x16 (BitVec.ofNat 64 (buf' / 256))).setPC (pcAt 330)
    have h9' : OpenRuns s9 1 1 s10 := by
      have hr16 : s9.getReg .x16 = BitVec.ofNat 64 buf' := by
        simp only [s9, s8, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x15 .x16 (by decide)]
        rfl
      have hv : s9.getReg .x16 >>> (8#6 : BitVec 6).toNat = BitVec.ofNat 64 (buf' / 256) := by
        rw [hr16]; change BitVec.ofNat 64 buf' >>> 8 = _
        rw [bv64_ushr buf' 8 (by omega), Nat.shiftRight_eq_div_pow]
      simpa only [hv, s10] using h9
    -- 295: ADDI x17, x17, 4088 (-8)
    have h10 := step_ADDI (by omega) (rfl : s10.pc = pcAt 330)
      (rfl : openingInstr 330 = .base (.ADDI .x17 .x17 (4088#12)))
    let s11 := (s10.setReg .x17 (BitVec.ofNat 64 (tCnt + 6 - 8))).setPC (pcAt 331)
    have h10' : OpenRuns s10 1 1 s11 := by
      have hr17 : s10.getReg .x17 = BitVec.ofNat 64 (tCnt + 6) := by
        simp only [s10, s9, s8, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x16 .x17 (by decide),
          getReg_setReg_ne' .x15 .x17 (by decide)]
        rfl
      rw [hr17, bv64_add_neg8 (tCnt + 6) hge8] at h10; exact h10
    have hpack : (tails ++ [t]).foldl pack6Step ([], 0, 0) =
        (acc ++ [BitVec.ofNat 8 buf'], buf' / 256, tCnt + 6 - 8) := by
      rw [hfold_app]; unfold pack6Step; dsimp only; rw [if_pos hge8]
    have hmem11 : ∀ a, s11.getByte a =
        (s.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).getByte a := fun a => by
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
      rfl
    have htot := hpre.trans ((((h6.trans h7').trans h8').trans h9').trans h10')
    refine ⟨11, s11, htot, Nat.le_refl 11, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro r h5ne h6ne h7ne h15ne h16ne h17ne
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x17 r (Ne.symm h17ne),
        getReg_setReg_ne' .x16 r (Ne.symm h16ne),
        getReg_setReg_ne' .x15 r (Ne.symm h15ne),
        getReg_setReg_ne' .x7 r (Ne.symm h7ne),
        getReg_setReg_ne' .x6 r (Ne.symm h6ne),
        getReg_setReg_ne' .x5 r (Ne.symm h5ne)]
    · intro a ha
      change (s.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).getMem a = _
      exact readOnly_setByte_tail (tailBufBase + acc.length) _ hro (by omega) (by omega) a ha
    · have hw' := writerState_setByte_outside (tailBufBase + acc.length) (BitVec.ofNat 8 buf')
        hw hfbd (Or.inr (by omega)) (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x17 .x25 (by decide), getReg_setReg_ne' .x16 .x25 (by decide),
          getReg_setReg_ne' .x15 .x25 (by decide), getReg_setReg_ne' .x7 .x25 (by decide),
          getReg_setReg_ne' .x6 .x25 (by decide), getReg_setReg_ne' .x5 .x25 (by decide)]
        exact hw.rx25
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x17 .x13 (by decide), getReg_setReg_ne' .x16 .x13 (by decide),
          getReg_setReg_ne' .x15 .x13 (by decide), getReg_setReg_ne' .x7 .x13 (by decide),
          getReg_setReg_ne' .x6 .x13 (by decide), getReg_setReg_ne' .x5 .x13 (by decide)]
        exact hw.rx13
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x17 .x14 (by decide), getReg_setReg_ne' .x16 .x14 (by decide),
          getReg_setReg_ne' .x15 .x14 (by decide), getReg_setReg_ne' .x7 .x14 (by decide),
          getReg_setReg_ne' .x6 .x14 (by decide), getReg_setReg_ne' .x5 .x14 (by decide)]
        exact hw.rx14
      · intro j hj
        have h12 : s11.getReg .x12 = s.getReg .x12 := by
          simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x17 .x12 (by decide), getReg_setReg_ne' .x16 .x12 (by decide),
            getReg_setReg_ne' .x15 .x12 (by decide), getReg_setReg_ne' .x7 .x12 (by decide),
            getReg_setReg_ne' .x6 .x12 (by decide), getReg_setReg_ne' .x5 .x12 (by decide)]
        rw [h12]; exact hw.wbufLo j hj
      · intro j h1 h2
        have h12 : s11.getReg .x12 = s.getReg .x12 := by
          simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x17 .x12 (by decide), getReg_setReg_ne' .x16 .x12 (by decide),
            getReg_setReg_ne' .x15 .x12 (by decide), getReg_setReg_ne' .x7 .x12 (by decide),
            getReg_setReg_ne' .x6 .x12 (by decide), getReg_setReg_ne' .x5 .x12 (by decide)]
        rw [h12]; exact hw.wbufHi j h1 h2
      · intro j hj; rw [hmem11]; exact hw'.memDwords j hj
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x17 .x31 (by decide), getReg_setReg_ne' .x16 .x31 (by decide),
          getReg_setReg_ne' .x15 .x31 (by decide), getReg_setReg_ne' .x7 .x31 (by decide),
          getReg_setReg_ne' .x6 .x31 (by decide), getReg_setReg_ne' .x5 .x31 (by decide)]
        exact ht.rx31
      · rw [hpack]
        simp only [s11, s10, s9, MachineState.getReg_setPC,
          getReg_setReg_ne' .x17 .x15 (by decide), getReg_setReg_ne' .x16 .x15 (by decide)]
        rfl
      · rw [hpack]
        simp only [s11, s10, MachineState.getReg_setPC, getReg_setReg_ne' .x17 .x16 (by decide)]
        rfl
      · rw [hpack]; rfl
      · rw [hpack]
        intro j hj
        rw [hmem11, set_byte_read]
        have hjlen : j < acc.length + 1 := by simpa using hj
        by_cases hlast : j = acc.length
        · subst hlast
          rw [if_pos rfl, list_getElem_append_right acc [BitVec.ofNat 8 buf'] acc.length (by omega) hj]
          simp
        · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega)),
            ht.memTail j (by omega), list_getElem_append_left acc [BitVec.ofNat 8 buf'] j (by omega)]
    · intro a ha
      rw [hmem11, set_byte_read, if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]

private theorem openRuns_call_copy24 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx srcOff : Nat} {jOff : BitVec 21}
    {fwdBytes chunk : List Byte} {tails : List (BitVec 6)}
    (hcall : callIdx < 332)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 207)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 24 ≤ 2438289632)
    (hbd : fwdBytes.length + 24 ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails)
    (hclen : chunk.length = 24)
    (hchunk : ∀ j (hj : j < 24),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk[j]'(by omega)) :
    ∃ s', OpenRuns s 21 21 s' ∧
      s'.pc = pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ chunk) ∧
      TailState s' tails ∧
      (∀ q < 5120, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have hr_jal := step_JAL hcall hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 207)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  have hw1 : WriterState s1 fwdBytes :=
    ⟨hw.rx25, hw.rx13, hw.rx14, hw.wbufLo, hw.wbufHi, hw.memDwords⟩
  obtain ⟨s2, hr_body, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    openRuns_emit_3dwords (base := 207) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := chunk)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (by exact hx10) hsrc_al hsrc_bd hbd hro1 hw1 hclen hchunk
  have hx1_2 : s2.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl
  have hr_ret := step_JALR_x0 (by omega) hpc2 (rfl : openingInstr 226 = .base (.JALR .x0 .x1 (0#12))) hx1_2
  let s3 := s2.setPC (pcAt (callIdx + 1))
  have hpres : ∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → r ≠ .x25 →
      s3.getReg r = s.getReg r := fun r h1 h5 h6 h12 h25 => by
    simp only [s3, MachineState.getReg_setPC, hreg2 r h5 h6 h12 h25, s1,
      getReg_setReg_ne' .x1 r (Ne.symm h1)]
  refine ⟨s3, (hr_jal.trans hr_body).trans hr_ret, rfl, hpres, hro2,
    ⟨hw2.rx25, hw2.rx13, hw2.rx14, hw2.wbufLo, hw2.wbufHi, hw2.memDwords⟩,
    tailState_of_mem_eq ht htbd (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact hpres _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun a ha1 ha2 => htail2 a ha1 ha2),
    fun a ha => hcap2 a ha⟩

private theorem openRuns_call_copy32 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx srcOff : Nat} {jOff : BitVec 21}
    {fwdBytes chunk : List Byte} {tails : List (BitVec 6)}
    (hcall : callIdx < 332)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 227)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 32 ≤ 2438289632)
    (hbd : fwdBytes.length + 32 ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails)
    (hclen : chunk.length = 32)
    (hchunk : ∀ j (hj : j < 32),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk[j]'(by omega)) :
    ∃ s', OpenRuns s 27 27 s' ∧
      s'.pc = pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ chunk) ∧
      TailState s' tails ∧
      (∀ q < 5120, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  let c0 := chunk.take 8
  let c1 := (chunk.drop 8).take 8
  let c2 := (chunk.drop 16).take 8
  let c3 := chunk.drop 24
  have hc0_len : c0.length = 8 := by simp [c0, hclen]
  have hc1_len : c1.length = 8 := by simp [c1, hclen]
  have hc2_len : c2.length = 8 := by simp [c2, hclen]
  have hc3_len : c3.length = 8 := by simp [c3, hclen]
  have hsplit : ((c0 ++ c1) ++ c2) ++ c3 = chunk := by
    have h1 : c0 ++ chunk.drop 8 = chunk := List.take_append_drop 8 chunk
    have h2 : c1 ++ chunk.drop 16 = chunk.drop 8 := by
      simpa [c1, List.drop_drop] using List.take_append_drop 8 (chunk.drop 8)
    have h3 : c2 ++ c3 = chunk.drop 16 := by
      simpa [c2, c3, List.drop_drop] using List.take_append_drop 8 (chunk.drop 16)
    rw [List.append_assoc, List.append_assoc, h3, h2, h1]
  have hcur_eq : (((fwdBytes ++ c0) ++ c1) ++ c2) ++ c3 = fwdBytes ++ chunk := by
    rw [← hsplit]; simp only [List.append_assoc]
  have hr_jal := step_JAL hcall hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 227)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  set qBase := fwdBytes.length / 8
  have hw1 : WriterState s1 fwdBytes := hw.of_eq
  obtain ⟨s2, hr2, hpc2, hreg2, hwLo2, hwHi2, hmem2, hro2, hcap2, htail2⟩ :=
    openRuns_emit_dword (s := s1) (base := 227) (srcOff := srcOff) (qBase := qBase) (k := 0) (imm := 0#12)
      (cur := fwdBytes) (chunk8 := c0) (by omega) (by decide)
      rfl rfl rfl rfl rfl rfl rfl (by exact hx10) hw1.rx25 (by omega) hw1.rx13 hw1.rx14
      hw1.wbufLo hw1.wbufHi hw1.memDwords hsrc_al (by omega) (by omega) hro1 hc0_len
      (fun j hj => by simpa [c0, List.getElem_take] using hchunk j (by omega))
  have hlen2 : (fwdBytes ++ c0).length = fwdBytes.length + 8 := by simp [hc0_len]
  obtain ⟨s3, hr3, hpc3, hreg3, hwLo3, hwHi3, hmem3, hro3, hcap3, htail3⟩ :=
    openRuns_emit_dword (base := 233) (srcOff := srcOff) (qBase := qBase) (k := 1) (imm := 8#12)
      (cur := fwdBytes ++ c0) (chunk8 := c1) (by omega) (by decide)
      rfl rfl rfl rfl rfl rfl hpc2
      (by rw [hreg2 .x10 (by decide) (by decide) (by decide)]; exact hx10)
      (by rw [hreg2 .x25 (by decide) (by decide) (by decide)]; exact hw.rx25)
      (by omega)
      (by rw [hreg2 .x13 (by decide) (by decide) (by decide), hw1.rx13]; congr 1; omega)
      (by rw [hreg2 .x14 (by decide) (by decide) (by decide), hw1.rx14]; congr 1; omega)
      hwLo2 hwHi2 hmem2 hsrc_al (by omega) (by omega) hro2 hc1_len
      (fun j hj => by simpa [c1, List.getElem_take, List.getElem_drop, Nat.add_assoc] using hchunk (8 + j) (by omega))
  have hlen3 : ((fwdBytes ++ c0) ++ c1).length = fwdBytes.length + 16 := by
    simp only [List.length_append, hc0_len, hc1_len]
  obtain ⟨s4, hr4, hpc4, hreg4, hwLo4, hwHi4, hmem4, hro4, hcap4, htail4⟩ :=
    openRuns_emit_dword (base := 239) (srcOff := srcOff) (qBase := qBase) (k := 2) (imm := 16#12)
      (cur := (fwdBytes ++ c0) ++ c1) (chunk8 := c2) (by omega) (by decide)
      rfl rfl rfl rfl rfl rfl hpc3
      (by rw [hreg3 .x10 (by decide) (by decide) (by decide), hreg2 .x10 (by decide) (by decide) (by decide)]; exact hx10)
      (by rw [hreg3 .x25 (by decide) (by decide) (by decide), hreg2 .x25 (by decide) (by decide) (by decide)]; exact hw1.rx25)
      (by omega)
      (by rw [hreg3 .x13 (by decide) (by decide) (by decide), hreg2 .x13 (by decide) (by decide) (by decide), hw1.rx13]; congr 1; omega)
      (by rw [hreg3 .x14 (by decide) (by decide) (by decide), hreg2 .x14 (by decide) (by decide) (by decide), hw1.rx14]; congr 1; omega)
      hwLo3 hwHi3 hmem3 hsrc_al (by omega) (by omega) hro3 hc2_len
      (fun j hj => by simpa [c2, List.getElem_take, List.getElem_drop, Nat.add_assoc] using hchunk (16 + j) (by omega))
  have hlen4 : (((fwdBytes ++ c0) ++ c1) ++ c2).length = fwdBytes.length + 24 := by
    simp only [List.length_append, hc0_len, hc1_len, hc2_len]
  obtain ⟨s5, hr5, hpc5, hreg5, hwLo5, hwHi5, hmem5, hro5, hcap5, htail5⟩ :=
    openRuns_emit_dword (base := 245) (srcOff := srcOff) (qBase := qBase) (k := 3) (imm := 24#12)
      (cur := ((fwdBytes ++ c0) ++ c1) ++ c2) (chunk8 := c3) (by omega) (by decide)
      rfl rfl rfl rfl rfl rfl hpc4
      (by rw [hreg4 .x10 (by decide) (by decide) (by decide), hreg3 .x10 (by decide) (by decide) (by decide),
        hreg2 .x10 (by decide) (by decide) (by decide)]; exact hx10)
      (by rw [hreg4 .x25 (by decide) (by decide) (by decide), hreg3 .x25 (by decide) (by decide) (by decide),
        hreg2 .x25 (by decide) (by decide) (by decide)]; exact hw1.rx25)
      (by omega)
      (by rw [hreg4 .x13 (by decide) (by decide) (by decide), hreg3 .x13 (by decide) (by decide) (by decide),
        hreg2 .x13 (by decide) (by decide) (by decide), hw1.rx13]; congr 1; omega)
      (by rw [hreg4 .x14 (by decide) (by decide) (by decide), hreg3 .x14 (by decide) (by decide) (by decide),
        hreg2 .x14 (by decide) (by decide) (by decide), hw1.rx14]; congr 1; omega)
      hwLo4 hwHi4 hmem4 hsrc_al (by omega) (by omega) hro4 hc3_len
      (fun j hj => by simpa [c3, List.getElem_drop, Nat.add_assoc] using hchunk (24 + j) (by omega))
  have hpres5 : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → s5.getReg r = s1.getReg r := fun r h5 h6 h12 => by
    rw [hreg5 r h5 h6 h12, hreg4 r h5 h6 h12, hreg3 r h5 h6 h12, hreg2 r h5 h6 h12]
  -- 216: ADDI x25, x25, 32
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have hadv := step_ADDI (by omega) hpc5 (rfl : openingInstr 251 = .base (.ADDI .x25 .x25 (32#12)))
  have hnew25 : s5.getReg .x25 + signExtend12 (32#12) =
      BitVec.ofNat 64 (11162446080 + 8 * ((fwdBytes ++ chunk).length / 8)) := by
    rw [hpres5 .x25 (by decide) (by decide) (by decide)]
    have hx25_1 : s1.getReg .x25 = BitVec.ofNat 64 (11162446080 + 8 * qBase) := hw.rx25
    rw [hx25_1, hse32, bv64_ofNat_add]; congr 1
    simp only [List.length_append, hclen]; omega
  let s6 := (s5.setReg .x25 (BitVec.ofNat 64 (11162446080 + 8 * ((fwdBytes ++ chunk).length / 8)))).setPC (pcAt 252)
  have hadv' : OpenRuns s5 1 1 s6 := by simpa only [hnew25, s6] using hadv
  -- 217: JALR x0, x1, 0
  have hx1_6 : s6.getReg .x1 = pcAt (callIdx + 1) := by
    simp only [s6, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x1 (by decide)]
    rw [hpres5 .x1 (by decide) (by decide) (by decide)]; rfl
  have hret := step_JALR_x0 (by omega) (rfl : s6.pc = pcAt 252)
    (rfl : openingInstr 252 = .base (.JALR .x0 .x1 (0#12))) hx1_6
  let s7 := s6.setPC (pcAt (callIdx + 1))
  have hpres7 : ∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → r ≠ .x25 →
      s7.getReg r = s.getReg r := fun r h1 h5 h6 h12 h25 => by
    simp only [s7, s6, MachineState.getReg_setPC, getReg_setReg_ne' .x25 r (Ne.symm h25)]
    rw [hpres5 r h5 h6 h12]; exact getReg_setReg_ne' .x1 r (Ne.symm h1) s _
  have htot := (((((hr_jal.trans hr2).trans hr3).trans hr4).trans hr5).trans hadv').trans hret
  refine ⟨s7, htot, rfl, hpres7, ?_, ?_, ?_, ?_⟩
  · intro a ha
    simp only [s7, s6, MachineState.getMem_setPC, MachineState.getMem_setReg]
    exact hro5 a ha
  · refine WriterState.castList hcur_eq ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcur_eq]; rfl
    · rw [hpres7 .x13 (by decide) (by decide) (by decide) (by decide) (by decide), hw.rx13, hcur_eq]
      congr 1; simp only [List.length_append, hclen]; omega
    · rw [hpres7 .x14 (by decide) (by decide) (by decide) (by decide) (by decide), hw.rx14, hcur_eq]
      congr 1; simp only [List.length_append, hclen]; omega
    · intro j hj
      simp only [s7, s6, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x12 (by decide)]
      exact hwLo5 j hj
    · intro j h1 h2
      simp only [s7, s6, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x12 (by decide)]
      exact hwHi5 j h1 h2
    · intro j hj
      simp only [s7, s6, getByte_setPC, getByte_setReg]
      exact hmem5 j hj
  · exact tailState_of_mem_eq ht htbd (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact hpres7 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun a ha1 ha2 => by
        simp only [s7, s6, getByte_setPC, getByte_setReg]
        rw [htail5 a ha1 ha2, htail4 a ha1 ha2, htail3 a ha1 ha2, htail2 a ha1 ha2]; rfl)
  · intro a ha
    simp only [s7, s6, getByte_setPC, getByte_setReg]
    rw [hcap5 a ha, hcap4 a ha, hcap3 a ha, hcap2 a ha]; rfl

private theorem openRuns_call_copy30 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx srcOff : Nat} {jOff : BitVec 21}
    {fwdBytes chunk : List Byte} {tails : List (BitVec 6)}
    (hcall : callIdx < 332)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 253)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 32 ≤ 2438289632)
    (hbd : fwdBytes.length + 30 ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails)
    (hclen : chunk.length = 30)
    (hchunk : ∀ j (hj : j < 30),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk[j]'(by omega)) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 35 ∧
      s'.pc = pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x25 →
        s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ chunk) ∧
      TailState s' tails ∧
      (∀ q < 5120, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  let c24 := chunk.take 24
  let c6 := chunk.drop 24
  have hc24_len : c24.length = 24 := by simp [c24, hclen]
  have hc6_len : c6.length = 6 := by simp [c6, hclen]
  have hsplit : (fwdBytes ++ c24) ++ c6 = fwdBytes ++ chunk := by
    rw [List.append_assoc, List.take_append_drop]
  have hr_jal := step_JAL hcall hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 253)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  have hw1 : WriterState s1 fwdBytes :=
    ⟨hw.rx25, hw.rx13, hw.rx14, hw.wbufLo, hw.wbufHi, hw.memDwords⟩
  obtain ⟨s2, hr_3d, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    openRuns_emit_3dwords (base := 253) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := c24)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (by exact hx10) hsrc_al (by omega) (by omega)
      hro1 hw1 hc24_len (fun j hj => by simpa [c24, List.getElem_take] using hchunk j (by omega))
  -- 237: LD x5, 24(x10); 238: SLLI x5, x5, 16; 239: SRLI x5, x5, 16
  have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
  have hx10_2 : s2.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff) := by
    rw [hreg2 .x10 (by decide) (by decide) (by decide) (by decide)]; exact hx10
  have haddr237 : s2.getReg .x10 + signExtend12 (24#12) =
      BitVec.ofNat 64 (4294971424 + (srcOff + 24)) := by
    rw [hx10_2, hse24, bv64_ofNat_add, Nat.add_assoc]
  set v3 := s2.getMem (BitVec.ofNat 64 (4294971424 + (srcOff + 24)))
  have h237 := step_LD (by omega) hpc2 (rfl : openingInstr 272 = .base (.LD .x5 .x10 (24#12)))
    (by rw [haddr237]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s3 := (s2.setReg .x5 v3).setPC (pcAt 273)
  have h237' : OpenRuns s2 1 1 s3 := by simpa only [haddr237, v3, s3] using h237
  have h238 := step_SLLI (by omega) (rfl : s3.pc = pcAt 273)
    (rfl : openingInstr 273 = .base (.SLLI .x5 .x5 (16#6)))
  let s4 := (s3.setReg .x5 (v3 <<< 16)).setPC (pcAt 274)
  have h238' : OpenRuns s3 1 1 s4 := by
    simpa only [show s3.getReg .x5 = v3 from rfl, show (16#6 : BitVec 6).toNat = 16 from rfl, s4] using h238
  have h239 := step_SRLI (by omega) (rfl : s4.pc = pcAt 274)
    (rfl : openingInstr 274 = .base (.SRLI .x5 .x5 (16#6)))
  let s5 := (s4.setReg .x5 ((v3 <<< 16) >>> 16)).setPC (pcAt 275)
  have h239' : OpenRuns s4 1 1 s5 := by
    simpa only [show s4.getReg .x5 = v3 <<< 16 from rfl, show (16#6 : BitVec 6).toNat = 16 from rfl, s5] using h239
  have hro5 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s5 := by
    intro a ha; simp only [s5, s4, s3, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro2 a ha
  have hw5 : WriterState s5 (fwdBytes ++ c24) :=
    ⟨hw2.rx25, hw2.rx13, hw2.rx14, hw2.wbufLo, hw2.wbufHi, hw2.memDwords⟩
  have hx5_5 : ∀ j (hj : j < 8),
      (s5.getReg .x5).extractLsb' (8 * j) 8 = if hj' : j < 6 then c6[j]'(by omega) else 0#8 := by
    intro j hj
    change ((v3 <<< (8 * (8 - 6))) >>> (8 * (8 - 6))).extractLsb' (8 * j) 8 = _
    rw [word_mask_low_bytes v3 6 (by omega) j hj]
    by_cases hj6 : j < 6
    · rw [if_pos hj6, dif_pos hj6,
        readOnly_getMem_trapdoor_byte hro2 (srcOff + 24) j (by omega) hj (by omega)]
      simpa [c6, List.getElem_drop, Nat.add_assoc] using hchunk (24 + j) (by omega)
    · rw [if_neg hj6, dif_neg hj6]
  obtain ⟨stP, s6, hrP, hstP, hpc6, hreg6, hro6, hw6, hcap6, htail6⟩ :=
    openRuns_emit_partial (base := 275) (m := 6) (immBits := 48#12)
      (fwdBytes := fwdBytes ++ c24) (chunkM := c6)
      (by omega) (by omega) (by omega) (by decide) (by decide)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl (by simp only [List.length_append, hc24_len]; omega) hro5 hw5 hc6_len hx5_5
  -- 251: JALR x0, x1, 0
  have hx1_6 : s6.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hreg6 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s5, s4, s3, MachineState.getReg_setPC, getReg_setReg_ne' .x5 .x1 (by decide)]
    rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl
  have hret := step_JALR_x0 (by omega) hpc6 (rfl : openingInstr 286 = .base (.JALR .x0 .x1 (0#12))) hx1_6
  let s7 := s6.setPC (pcAt (callIdx + 1))
  rw [hsplit] at hw6
  have hpres7 : ∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x25 →
      s7.getReg r = s.getReg r := fun r h1 h5 h6 h7 h12 h13 h14 h25 => by
    simp only [s7, MachineState.getReg_setPC]
    rw [hreg6 r h5 h6 h7 h12 h13 h14 h25]
    simp only [s5, s4, s3, MachineState.getReg_setPC, getReg_setReg_ne' .x5 r (Ne.symm h5)]
    rw [hreg2 r h5 h6 h12 h25]; exact getReg_setReg_ne' .x1 r (Ne.symm h1) s _
  have htot := (((((hr_jal.trans hr_3d).trans h237').trans h238').trans h239').trans hrP).trans hret
  refine ⟨1 + 19 + 1 + 1 + 1 + stP + 1, s7, htot, by omega, rfl, hpres7, hro6,
    ⟨hw6.rx25, hw6.rx13, hw6.rx14, hw6.wbufLo, hw6.wbufHi, hw6.memDwords⟩,
    tailState_of_mem_eq ht htbd (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact hpres7 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun a ha1 ha2 => by
        simp only [s7, getByte_setPC]
        rw [htail6 a ha1 ha2]
        simp only [s5, s4, s3, getByte_setPC, getByte_setReg]
        rw [htail2 a ha1 ha2]; rfl),
    fun a ha => by
      simp only [s7, getByte_setPC]
      rw [hcap6 a ha]
      simp only [s5, s4, s3, getByte_setPC, getByte_setReg]
      rw [hcap2 a ha]; rfl⟩

private theorem openRuns_call_copy29_tail {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx l nodeIdx : Nat} {jOff : BitVec 21}
    {fwdBytes : List Byte} {tails : List (BitVec 6)}
    (hcall : callIdx < 332)
    (hl : l ≤ 23) (hnode : nodeIdx < levelSize l)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 287)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l nodeIdx)))
    (hbd : fwdBytes.length + 29 ≤ 8669633152)
    (htbd : tails.length < 200000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    let d := tdNode trapdoor l nodeIdx
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 46 ∧
      s'.pc = pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
        r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ bitsToBytes d 29) ∧
      TailState s' (tails ++ [tail6 d]) ∧
      (∀ q < 5120, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro d
  set srcOff := levelBase l + nodeOffset l nodeIdx
  have htb : treeBytes = 894785760 := treeBytes_eq
  have hsrc_bd : srcOff + 32 ≤ 2438289632 := by
    have := nodeOffset_lt_treeBytes l nodeIdx hl hnode; omega
  have hsrc_al : srcOff % 8 = 0 := by
    have h1 := levelBase_align8 l hl; have h2 := nodeOffset_align8 l nodeIdx; omega
  let chunk := bitsToBytes d 29
  have hclen : chunk.length = 29 := bitsToBytes_length d 29
  let c24 := chunk.take 24
  let c5 := chunk.drop 24
  have hc24_len : c24.length = 24 := by simp [c24, hclen]
  have hc5_len : c5.length = 5 := by simp [c5, hclen]
  have hsplit : (fwdBytes ++ c24) ++ c5 = fwdBytes ++ chunk := by
    rw [List.append_assoc, List.take_append_drop]
  have hr_jal := step_JAL hcall hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 287)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  have hw1 : WriterState s1 fwdBytes :=
    ⟨hw.rx25, hw.rx13, hw.rx14, hw.wbufLo, hw.wbufHi, hw.memDwords⟩
  obtain ⟨s2, hr_3d, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    openRuns_emit_3dwords (base := 287) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := c24)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (by exact hx10) hsrc_al (by omega) (by omega)
      hro1 hw1 hc24_len (fun j hj => by
        simpa [c24, chunk, List.getElem_take] using chunk_tdNode trapdoor l nodeIdx 29 j (by omega) (by omega))
  -- 271: LD x11, 24(x10); 272: SLLI x5, x11, 24; 273: SRLI x5, x5, 24
  have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
  have hx10_2 : s2.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff) := by
    rw [hreg2 .x10 (by decide) (by decide) (by decide) (by decide)]; exact hx10
  have haddr271 : s2.getReg .x10 + signExtend12 (24#12) =
      BitVec.ofNat 64 (4294971424 + (srcOff + 24)) := by
    rw [hx10_2, hse24, bv64_ofNat_add, Nat.add_assoc]
  set v3 := s2.getMem (BitVec.ofNat 64 (4294971424 + (srcOff + 24)))
  have h271 := step_LD (by omega) hpc2 (rfl : openingInstr 306 = .base (.LD .x11 .x10 (24#12)))
    (by rw [haddr271]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s3 := (s2.setReg .x11 v3).setPC (pcAt 307)
  have h271' : OpenRuns s2 1 1 s3 := by simpa only [haddr271, v3, s3] using h271
  have h272 := step_SLLI (by omega) (rfl : s3.pc = pcAt 307)
    (rfl : openingInstr 307 = .base (.SLLI .x5 .x11 (24#6)))
  let s4 := (s3.setReg .x5 (v3 <<< 24)).setPC (pcAt 308)
  have h272' : OpenRuns s3 1 1 s4 := by
    simpa only [show s3.getReg .x11 = v3 from rfl, show (24#6 : BitVec 6).toNat = 24 from rfl, s4] using h272
  have h273 := step_SRLI (by omega) (rfl : s4.pc = pcAt 308)
    (rfl : openingInstr 308 = .base (.SRLI .x5 .x5 (24#6)))
  let s5 := (s4.setReg .x5 ((v3 <<< 24) >>> 24)).setPC (pcAt 309)
  have h273' : OpenRuns s4 1 1 s5 := by
    simpa only [show s4.getReg .x5 = v3 <<< 24 from rfl, show (24#6 : BitVec 6).toNat = 24 from rfl, s5] using h273
  have hro5 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s5 := by
    intro a ha; simp only [s5, s4, s3, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro2 a ha
  have hw5 : WriterState s5 (fwdBytes ++ c24) :=
    ⟨hw2.rx25, hw2.rx13, hw2.rx14, hw2.wbufLo, hw2.wbufHi, hw2.memDwords⟩
  have hx5_5 : ∀ j (hj : j < 8),
      (s5.getReg .x5).extractLsb' (8 * j) 8 = if hj' : j < 5 then c5[j]'(by omega) else 0#8 := by
    intro j hj
    change ((v3 <<< (8 * (8 - 5))) >>> (8 * (8 - 5))).extractLsb' (8 * j) 8 = _
    rw [word_mask_low_bytes v3 5 (by omega) j hj]
    by_cases hj5 : j < 5
    · rw [if_pos hj5, dif_pos hj5,
        readOnly_getMem_trapdoor_byte hro2 (srcOff + 24) j (by omega) hj (by omega)]
      simpa [c5, chunk, d, srcOff, List.getElem_drop, Nat.add_assoc] using
        chunk_tdNode trapdoor l nodeIdx 29 (24 + j) (by omega) (by omega)
    · rw [if_neg hj5, dif_neg hj5]
  obtain ⟨stP, s6, hrP, hstP, hpc6, hreg6, hro6, hw6, hcap6, htail6⟩ :=
    openRuns_emit_partial (base := 309) (m := 5) (immBits := 40#12)
      (fwdBytes := fwdBytes ++ c24) (chunkM := c5)
      (by omega) (by omega) (by omega) (by decide) (by decide)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl (by simp only [List.length_append, hc24_len]; omega) hro5 hw5 hc5_len hx5_5
  rw [hsplit] at hw6
  -- 285..295: push 6-bit tail
  have hx11_6 : (s6.getReg .x11).extractLsb' (8 * 5) 8 = d.extractLsb' (8 * 29) 8 := by
    have h11 : s6.getReg .x11 = v3 := by
      rw [hreg6 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      rfl
    rw [h11, readOnly_getMem_trapdoor_byte hro2 (srcOff + 24) 5 (by omega) (by omega) (by omega)]
    unfold d tdNode
    rw [extractLsb'_extractLsb' trapdoor (8 * srcOff) 256 (8 * 29) 8 (by omega)]
    congr 1
  have ht6 : TailState s6 tails := tailState_of_mem_eq ht (by omega)
    (fun r hr => by
      have hne : r ≠ .x1 ∧ r ≠ .x5 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x13 ∧ r ≠ .x14 ∧ r ≠ .x25 := by
        rcases hr with rfl | rfl | rfl | rfl <;> decide
      rw [hreg6 r hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.2.1 hne.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2]
      simp only [s5, s4, s3, MachineState.getReg_setPC,
        getReg_setReg_ne' .x5 r (Ne.symm hne.2.1), getReg_setReg_ne' .x11 r (Ne.symm hne.2.2.2.2.1)]
      rw [hreg2 r hne.2.1 hne.2.2.1 hne.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2]
      exact getReg_setReg_ne' .x1 r (Ne.symm hne.1) s _)
    (fun a ha1 ha2 => by
      rw [htail6 a ha1 ha2]
      simp only [s5, s4, s3, getByte_setPC, getByte_setReg]
      rw [htail2 a ha1 ha2]; rfl)
  obtain ⟨stT, s7, hrT, hstT, hpc7, hreg7, hro7, hw7, ht7, hcap7⟩ :=
    openRuns_push_tail6 hpc6 hx11_6 (by simp only [List.length_append, hclen]; omega)
      htbd hro6 hw6 ht6
  -- 296: JALR x0, x1, 0
  have hx1_7 : s7.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hreg7 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg6 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s5, s4, s3, MachineState.getReg_setPC,
      getReg_setReg_ne' .x5 .x1 (by decide), getReg_setReg_ne' .x11 .x1 (by decide)]
    rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl
  have hret := step_JALR_x0 (by omega) hpc7 (rfl : openingInstr 331 = .base (.JALR .x0 .x1 (0#12))) hx1_7
  let s8 := s7.setPC (pcAt (callIdx + 1))
  have hpres8 : ∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
      r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x25 → s8.getReg r = s.getReg r :=
    fun r h1 h5 h6 h7 h11 h12 h13 h14 h15 h16 h17 h25 => by
      simp only [s8, MachineState.getReg_setPC]
      rw [hreg7 r h5 h6 h7 h15 h16 h17, hreg6 r h5 h6 h7 h12 h13 h14 h25]
      simp only [s5, s4, s3, MachineState.getReg_setPC,
        getReg_setReg_ne' .x5 r (Ne.symm h5), getReg_setReg_ne' .x11 r (Ne.symm h11)]
      rw [hreg2 r h5 h6 h12 h25]; exact getReg_setReg_ne' .x1 r (Ne.symm h1) s _
  have htot := ((((((hr_jal.trans hr_3d).trans h271').trans h272').trans h273').trans hrP).trans hrT).trans hret
  refine ⟨1 + 19 + 1 + 1 + 1 + stP + stT + 1, s8, htot, by omega, rfl, hpres8, hro7,
    ⟨hw7.rx25, hw7.rx13, hw7.rx14, hw7.wbufLo, hw7.wbufHi, hw7.memDwords⟩,
    ⟨ht7.rx31, ht7.rx15, ht7.rx16, ht7.rx17, ht7.memTail⟩,
    fun a ha => by
      simp only [s8, getByte_setPC]
      rw [hcap7 a ha, hcap6 a ha]
      simp only [s5, s4, s3, getByte_setPC, getByte_setReg]
      rw [hcap2 a ha]; rfl⟩

/-! ### 6. Entry and Epilogue Blocks (`0..31`, `183..206`) -/

private theorem opening_initial_regs (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    s0.pc = pcAt 0 ∧
    s0.getReg .x2 = BitVec.ofNat 64 68719475968 ∧
    s0.getReg .x12 = BitVec.ofNat 64 4294971424 ∧
    s0.getReg .x13 = BitVec.ofNat 64 6733261056 ∧
    s0.getReg .x15 = BitVec.ofNat 64 11162446080 ∧
    s0.getReg .x16 = BitVec.ofNat 64 positions.card := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  change BitVec.ofNat 64 (dataBase (submission.image .opening)) = _
  rw [opening_dataBase]

private theorem openRuns_entry_prefix (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ s5, OpenRuns s0 5 5 s5 ∧
      s5.pc = pcAt 5 ∧
      s5.getReg .x2 = BitVec.ofNat 64 68719475968 ∧
      s5.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s5.getReg .x24 = BitVec.ofNat 64 6733261056 ∧
      s5.getReg .x25 = BitVec.ofNat 64 11162446080 ∧
      s5.getReg .x26 = BitVec.ofNat 64 11162446080 ∧
      s5.getReg .x27 = BitVec.ofNat 64 positions.card ∧
      s5.mem = s0.mem := by
  intro s0
  obtain ⟨hpc0, hx2, hx12, hx13, hx15, hx16⟩ := opening_initial_regs trapdoor positions
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have h1 := step_ADDI (by omega) hpc0 (rfl : openingInstr 0 = .base (.ADDI .x9 .x12 (0#12)))
  let s1 := (s0.setReg .x9 (BitVec.ofNat 64 4294971424)).setPC (pcAt 1)
  have h1' : OpenRuns s0 1 1 s1 := by
    simpa only [hx12, hse0, bv64_ofNat_add, Nat.add_zero, s1] using h1
  have h2 := step_ADDI (by omega) (rfl : s1.pc = pcAt 1)
    (rfl : openingInstr 1 = .base (.ADDI .x24 .x13 (0#12)))
  let s2 := (s1.setReg .x24 (BitVec.ofNat 64 6733261056)).setPC (pcAt 2)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hr : s1.getReg .x13 = BitVec.ofNat 64 6733261056 := hx13
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 2)
    (rfl : openingInstr 2 = .base (.ADDI .x25 .x15 (0#12)))
  let s3 := (s2.setReg .x25 (BitVec.ofNat 64 11162446080)).setPC (pcAt 3)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hr : s2.getReg .x15 = BitVec.ofNat 64 11162446080 := hx15
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s3] using h3
  have h4 := step_ADDI (by omega) (rfl : s3.pc = pcAt 3)
    (rfl : openingInstr 3 = .base (.ADDI .x26 .x15 (0#12)))
  let s4 := (s3.setReg .x26 (BitVec.ofNat 64 11162446080)).setPC (pcAt 4)
  have h4' : OpenRuns s3 1 1 s4 := by
    have hr : s3.getReg .x15 = BitVec.ofNat 64 11162446080 := hx15
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s4] using h4
  have h5 := step_ADDI (by omega) (rfl : s4.pc = pcAt 4)
    (rfl : openingInstr 4 = .base (.ADDI .x27 .x16 (0#12)))
  let s5 := (s4.setReg .x27 (BitVec.ofNat 64 positions.card)).setPC (pcAt 5)
  have h5' : OpenRuns s4 1 1 s5 := by
    have hr : s4.getReg .x16 = BitVec.ofNat 64 positions.card := hx16
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s5] using h5
  exact ⟨s5, (((h1'.trans h2').trans h3').trans h4').trans h5',
    rfl, hx2, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem openRuns_empty_epilogue {s : MachineState} (hpc : s.pc = pcAt 203) :
    ∃ sHalt, OpenRuns s 3 3 sHalt ∧
      sHalt.pc = pcAt 206 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = 0#64 ∧
      sHalt.mem = s.mem := by
  have h1 := step_ADDI (by omega) hpc (rfl : openingInstr 203 = .base (.ADDI .x11 .x0 (0#12)))
  let s1 := (s.setReg .x11 0#64).setPC (pcAt 204)
  have h1' : OpenRuns s 1 1 s1 := by
    have hv : s.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s1] using h1
  have h2 := step_ADDI (by omega) (rfl : s1.pc = pcAt 204)
    (rfl : openingInstr 204 = .base (.ADDI .x5 .x0 (1#12)))
  let s2 := (s1.setReg .x5 1#64).setPC (pcAt 205)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x0 + signExtend12 (1#12) = 1#64 := by
      change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 205)
    (rfl : openingInstr 205 = .base (.ADDI .x10 .x0 (0#12)))
  let s3 := (s2.setReg .x10 0#64).setPC (pcAt 206)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hv : s2.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s3] using h3
  exact ⟨s3, (h1'.trans h2').trans h3', rfl, rfl, rfl, rfl, rfl⟩


private theorem openRuns_entry_nonzero (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (hne : positions.card ≠ 0) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ s32, OpenRuns s0 32 32 s32 ∧
      s32.pc = pcAt 32 ∧
      s32.getReg .x2 = BitVec.ofNat 64 68719475968 ∧
      s32.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s32.getReg .x12 = 0#64 ∧
      s32.getReg .x13 = 0#64 ∧
      s32.getReg .x14 = BitVec.ofNat 64 63 ∧
      s32.getReg .x15 = BitVec.ofNat 64 tailBufBase ∧
      s32.getReg .x16 = 0#64 ∧
      s32.getReg .x17 = 0#64 ∧
      s32.getReg .x18 = BitVec.ofNat 64 (4294971424 + (rowOff + 72)) ∧
      s32.getReg .x19 = 3#64 ∧
      s32.getReg .x20 = BitVec.ofNat 64 FULL_TRIPLETS_0 ∧
      s32.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s32.getReg .x24 = BitVec.ofNat 64 6733261056 ∧
      s32.getReg .x25 = BitVec.ofNat 64 11162446080 ∧
      s32.getReg .x26 = BitVec.ofNat 64 11162446080 ∧
      s32.getReg .x27 = BitVec.ofNat 64 positions.card ∧
      s32.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
      s32.mem = s0.mem := by
  intro s0
  obtain ⟨s5, hr5, hpc5, hx2, hx9, hx24, hx25, hx26, hx27, hmem5⟩ :=
    openRuns_entry_prefix trapdoor positions
  have hcard := positions_card_le positions
  have h6 := step_BEQ_not_taken (by omega) hpc5
    (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (792#13)))
    (by rw [hx27]; exact bv64_ofNat_ne (by omega) (by decide) hne)
  let s6 := s5.setPC (pcAt 6)
  -- 6..17: writer & tail-packer init
  have h7 := step_ADDI (by omega) (rfl : s6.pc = pcAt 6)
    (rfl : openingInstr 6 = .base (.ADDI .x12 .x0 (0#12)))
  let s7 := (s6.setReg .x12 0#64).setPC (pcAt 7)
  have h7' : OpenRuns s6 1 1 s7 := by
    have hv : s6.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s7] using h7
  have h8 := step_ADDI (by omega) (rfl : s7.pc = pcAt 7)
    (rfl : openingInstr 7 = .base (.ADDI .x13 .x0 (0#12)))
  let s8 := (s7.setReg .x13 0#64).setPC (pcAt 8)
  have h8' : OpenRuns s7 1 1 s8 := by
    have hv : s7.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s8] using h8
  have h9 := step_ADDI (by omega) (rfl : s8.pc = pcAt 8)
    (rfl : openingInstr 8 = .base (.ADDI .x14 .x0 (63#12)))
  let s9 := (s8.setReg .x14 (BitVec.ofNat 64 63)).setPC (pcAt 9)
  have h9' : OpenRuns s8 1 1 s9 := by
    have hv : s8.getReg .x0 + signExtend12 (63#12) = BitVec.ofNat 64 63 := by
      change (0#64 : Word) + signExtend12 (63#12) = BitVec.ofNat 64 63; decide
    simpa only [hv, s9] using h9
  have h10 := step_ADDI (by omega) (rfl : s9.pc = pcAt 9)
    (rfl : openingInstr 9 = .base (.ADDI .x31 .x0 (2#12)))
  let s10 := (s9.setReg .x31 (BitVec.ofNat 64 2)).setPC (pcAt 10)
  have h10' : OpenRuns s9 1 1 s10 := by
    have hv : s9.getReg .x0 + signExtend12 (2#12) = BitVec.ofNat 64 2 := by
      change (0#64 : Word) + signExtend12 (2#12) = BitVec.ofNat 64 2; decide
    simpa only [hv, s10] using h10
  have h11 := step_SLLI (by omega) (rfl : s10.pc = pcAt 10)
    (rfl : openingInstr 10 = .base (.SLLI .x31 .x31 (11#6)))
  let s11 := (s10.setReg .x31 (BitVec.ofNat 64 4096)).setPC (pcAt 11)
  have h11' : OpenRuns s10 1 1 s11 := by
    have hv : s10.getReg .x31 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096 := by
      change BitVec.ofNat 64 2 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096; decide
    simpa only [hv, s11] using h11
  have h12 := step_ADDI (by omega) (rfl : s11.pc = pcAt 11)
    (rfl : openingInstr 11 = .base (.ADDI .x31 .x31 (672#12)))
  let s12 := (s11.setReg .x31 (BitVec.ofNat 64 4768)).setPC (pcAt 12)
  have h12' : OpenRuns s11 1 1 s12 := by
    have hv : s11.getReg .x31 + signExtend12 (672#12) = BitVec.ofNat 64 4768 := by
      change BitVec.ofNat 64 4096 + signExtend12 (672#12) = BitVec.ofNat 64 4768; decide
    simpa only [hv, s12] using h12
  have h13 := step_SLLI (by omega) (rfl : s12.pc = pcAt 12)
    (rfl : openingInstr 12 = .base (.SLLI .x31 .x31 (11#6)))
  let s13 := (s12.setReg .x31 (BitVec.ofNat 64 9764864)).setPC (pcAt 13)
  have h13' : OpenRuns s12 1 1 s13 := by
    have hv : s12.getReg .x31 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 9764864 := by
      change BitVec.ofNat 64 4768 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 9764864; decide
    simpa only [hv, s13] using h13
  have h14 := step_ADDI (by omega) (rfl : s13.pc = pcAt 13)
    (rfl : openingInstr 13 = .base (.ADDI .x31 .x31 (761#12)))
  let s14 := (s13.setReg .x31 (BitVec.ofNat 64 9765625)).setPC (pcAt 14)
  have h14' : OpenRuns s13 1 1 s14 := by
    have hv : s13.getReg .x31 + signExtend12 (761#12) = BitVec.ofNat 64 9765625 := by
      change BitVec.ofNat 64 9764864 + signExtend12 (761#12) = BitVec.ofNat 64 9765625; decide
    simpa only [hv, s14] using h14
  have h15 := step_SLLI (by omega) (rfl : s14.pc = pcAt 14)
    (rfl : openingInstr 14 = .base (.SLLI .x31 .x31 (11#6)))
  let s15 := (s14.setReg .x31 (BitVec.ofNat 64 tailBufBase)).setPC (pcAt 15)
  have h15' : OpenRuns s14 1 1 s15 := by
    have hv : s14.getReg .x31 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 tailBufBase := by
      change BitVec.ofNat 64 9765625 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 20000000000; decide
    simpa only [hv, s15] using h15
  have h16 := step_ADDI (by omega) (rfl : s15.pc = pcAt 15)
    (rfl : openingInstr 15 = .base (.ADDI .x15 .x31 (0#12)))
  let s16 := (s15.setReg .x15 (BitVec.ofNat 64 tailBufBase)).setPC (pcAt 16)
  have h16' : OpenRuns s15 1 1 s16 := by
    have hv : s15.getReg .x31 + signExtend12 (0#12) = BitVec.ofNat 64 tailBufBase := by
      change BitVec.ofNat 64 20000000000 + signExtend12 (0#12) = BitVec.ofNat 64 20000000000; decide
    simpa only [hv, s16] using h16
  have h17 := step_ADDI (by omega) (rfl : s16.pc = pcAt 16)
    (rfl : openingInstr 16 = .base (.ADDI .x16 .x0 (0#12)))
  let s17 := (s16.setReg .x16 0#64).setPC (pcAt 17)
  have h17' : OpenRuns s16 1 1 s17 := by
    have hv : s16.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s17] using h17
  have h18 := step_ADDI (by omega) (rfl : s17.pc = pcAt 17)
    (rfl : openingInstr 17 = .base (.ADDI .x17 .x0 (0#12)))
  let s18 := (s17.setReg .x17 0#64).setPC (pcAt 18)
  have h18' : OpenRuns s17 1 1 s18 := by
    have hv : s17.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s18] using h18
  -- 18..31: trapdoor/salt/triplet/cap constants (rowOff + 72 = 894785832)
  have h19 := step_ADDI (by omega) (rfl : s18.pc = pcAt 18)
    (rfl : openingInstr 18 = .base (.ADDI .x6 .x0 (213#12)))
  let s19 := (s18.setReg .x6 (BitVec.ofNat 64 213)).setPC (pcAt 19)
  have h19' : OpenRuns s18 1 1 s19 := by
    have hv : s18.getReg .x0 + signExtend12 (213#12) = BitVec.ofNat 64 213 := by
      change (0#64 : Word) + signExtend12 (213#12) = BitVec.ofNat 64 213; decide
    simpa only [hv, s19] using h19
  have h20 := step_SLLI (by omega) (rfl : s19.pc = pcAt 19)
    (rfl : openingInstr 19 = .base (.SLLI .x6 .x6 (11#6)))
  let s20 := (s19.setReg .x6 (BitVec.ofNat 64 436224)).setPC (pcAt 20)
  have h20' : OpenRuns s19 1 1 s20 := by
    have hv : s19.getReg .x6 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 436224 := by
      change BitVec.ofNat 64 213 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 436224; decide
    simpa only [hv, s20] using h20
  have h21 := step_ADDI (by omega) (rfl : s20.pc = pcAt 20)
    (rfl : openingInstr 20 = .base (.ADDI .x6 .x6 (683#12)))
  let s21 := (s20.setReg .x6 (BitVec.ofNat 64 436907)).setPC (pcAt 21)
  have h21' : OpenRuns s20 1 1 s21 := by
    have hv : s20.getReg .x6 + signExtend12 (683#12) = BitVec.ofNat 64 436907 := by
      change BitVec.ofNat 64 436224 + signExtend12 (683#12) = BitVec.ofNat 64 436907; decide
    simpa only [hv, s21] using h21
  have h22 := step_SLLI (by omega) (rfl : s21.pc = pcAt 21)
    (rfl : openingInstr 21 = .base (.SLLI .x6 .x6 (11#6)))
  let s22 := (s21.setReg .x6 (BitVec.ofNat 64 894785536)).setPC (pcAt 22)
  have h22' : OpenRuns s21 1 1 s22 := by
    have hv : s21.getReg .x6 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 894785536 := by
      change BitVec.ofNat 64 436907 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 894785536; decide
    simpa only [hv, s22] using h22
  have h23 := step_ADDI (by omega) (rfl : s22.pc = pcAt 22)
    (rfl : openingInstr 22 = .base (.ADDI .x6 .x6 (296#12)))
  let s23 := (s22.setReg .x6 (BitVec.ofNat 64 (rowOff + 72))).setPC (pcAt 23)
  have h23' : OpenRuns s22 1 1 s23 := by
    have hv : s22.getReg .x6 + signExtend12 (296#12) = BitVec.ofNat 64 (rowOff + 72) := by
      change BitVec.ofNat 64 894785536 + signExtend12 (296#12) = BitVec.ofNat 64 (rowOff + 72)
      rw [rowOff_eq]; decide
    simpa only [hv, s23] using h23
  have h24 := step_ADD (by omega) (rfl : s23.pc = pcAt 23)
    (rfl : openingInstr 23 = .base (.ADD .x18 .x9 .x6))
  let s24 := (s23.setReg .x18 (BitVec.ofNat 64 (4294971424 + (rowOff + 72)))).setPC (pcAt 24)
  have h24' : OpenRuns s23 1 1 s24 := by
    have hr9 : s23.getReg .x9 = BitVec.ofNat 64 4294971424 := hx9
    simpa only [hr9, show s23.getReg .x6 = BitVec.ofNat 64 (rowOff + 72) from rfl, bv64_ofNat_add, s24] using h24
  have h25 := step_ADDI (by omega) (rfl : s24.pc = pcAt 24)
    (rfl : openingInstr 24 = .base (.ADDI .x19 .x0 (3#12)))
  let s25 := (s24.setReg .x19 3#64).setPC (pcAt 25)
  have h25' : OpenRuns s24 1 1 s25 := by
    have hv : s24.getReg .x0 + signExtend12 (3#12) = 3#64 := by
      change (0#64 : Word) + signExtend12 (3#12) = 3#64; decide
    simpa only [hv, s25] using h25
  have h26 := step_ADDI (by omega) (rfl : s25.pc = pcAt 25)
    (rfl : openingInstr 25 = .base (.ADDI .x20 .x0 (1#12)))
  let s26 := (s25.setReg .x20 (BitVec.ofNat 64 1)).setPC (pcAt 26)
  have h26' : OpenRuns s25 1 1 s26 := by
    have hv : s25.getReg .x0 + signExtend12 (1#12) = BitVec.ofNat 64 1 := by
      change (0#64 : Word) + signExtend12 (1#12) = BitVec.ofNat 64 1; decide
    simpa only [hv, s26] using h26
  have h27 := step_SLLI (by omega) (rfl : s26.pc = pcAt 26)
    (rfl : openingInstr 26 = .base (.SLLI .x20 .x20 (11#6)))
  let s27 := (s26.setReg .x20 (BitVec.ofNat 64 2048)).setPC (pcAt 27)
  have h27' : OpenRuns s26 1 1 s27 := by
    have hv : s26.getReg .x20 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 2048 := by
      change BitVec.ofNat 64 1 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 2048; decide
    simpa only [hv, s27] using h27
  have h28 := step_ADDI (by omega) (rfl : s27.pc = pcAt 27)
    (rfl : openingInstr 27 = .base (.ADDI .x20 .x20 (682#12)))
  let s28 := (s27.setReg .x20 (BitVec.ofNat 64 2730)).setPC (pcAt 28)
  have h28' : OpenRuns s27 1 1 s28 := by
    have hv : s27.getReg .x20 + signExtend12 (682#12) = BitVec.ofNat 64 2730 := by
      change BitVec.ofNat 64 2048 + signExtend12 (682#12) = BitVec.ofNat 64 2730; decide
    simpa only [hv, s28] using h28
  have h29 := step_SLLI (by omega) (rfl : s28.pc = pcAt 28)
    (rfl : openingInstr 28 = .base (.SLLI .x20 .x20 (11#6)))
  let s29 := (s28.setReg .x20 (BitVec.ofNat 64 5591040)).setPC (pcAt 29)
  have h29' : OpenRuns s28 1 1 s29 := by
    have hv : s28.getReg .x20 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 5591040 := by
      change BitVec.ofNat 64 2730 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 5591040; decide
    simpa only [hv, s29] using h29
  have h30 := step_ADDI (by omega) (rfl : s29.pc = pcAt 29)
    (rfl : openingInstr 29 = .base (.ADDI .x20 .x20 (1365#12)))
  let s30 := (s29.setReg .x20 (BitVec.ofNat 64 FULL_TRIPLETS_0)).setPC (pcAt 30)
  have h30' : OpenRuns s29 1 1 s30 := by
    have hv : s29.getReg .x20 + signExtend12 (1365#12) = BitVec.ofNat 64 FULL_TRIPLETS_0 := by
      change BitVec.ofNat 64 5591040 + signExtend12 (1365#12) = BitVec.ofNat 64 FULL_TRIPLETS_0
      rw [full_triplets_0_eq]; decide
    simpa only [hv, s30] using h30
  have h31 := step_ADDI (by omega) (rfl : s30.pc = pcAt 30)
    (rfl : openingInstr 30 = .base (.ADDI .x21 .x0 (2#12)))
  let s31 := (s30.setReg .x21 (BitVec.ofNat 64 2)).setPC (pcAt 31)
  have h31' : OpenRuns s30 1 1 s31 := by
    have hv : s30.getReg .x0 + signExtend12 (2#12) = BitVec.ofNat 64 2 := by
      change (0#64 : Word) + signExtend12 (2#12) = BitVec.ofNat 64 2; decide
    simpa only [hv, s31] using h31
  have h32 := step_SLLI (by omega) (rfl : s31.pc = pcAt 31)
    (rfl : openingInstr 31 = .base (.SLLI .x21 .x21 (11#6)))
  let s32 := (s31.setReg .x21 (BitVec.ofNat 64 4096)).setPC (pcAt 32)
  have h32' : OpenRuns s31 1 1 s32 := by
    have hv : s31.getReg .x21 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096 := by
      change BitVec.ofNat 64 2 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096; decide
    simpa only [hv, s32] using h32
  have ha := ((((((hr5.trans h6).trans h7').trans h8').trans h9').trans h10').trans h11').trans h12'
  have hb := ((((((ha.trans h13').trans h14').trans h15').trans h16').trans h17').trans h18').trans h19'
  have hc := ((((((hb.trans h20').trans h21').trans h22').trans h23').trans h24').trans h25').trans h26'
  have htot := (((((hc.trans h27').trans h28').trans h29').trans h30').trans h31').trans h32'
  exact ⟨s32, htot, rfl, hx2, hx9, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx24, hx25,
    hx26, hx27, rfl, hmem5⟩

private theorem openRuns_flush_wbuf {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    (hpc : s.pc = pcAt 183)
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11162446080)
    (hfbd : fwdBytes.length ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 37 ∧
      s'.pc = pcAt 190 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (11162446080 + fwdBytes.length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 11162446080 ∧
      ProofPrefix s' fwdBytes ∧
      TailState s' tails := by
  set q := fwdBytes.length / 8
  set r := fwdBytes.length % 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  -- 148: ADDI x10, x25, 0
  have h148 := step_ADDI (by omega) hpc (rfl : openingInstr 183 = .base (.ADDI .x10 .x25 (0#12)))
  let s1 := (s.setReg .x10 (BitVec.ofNat 64 (11162446080 + 8 * q))).setPC (pcAt 184)
  have h148' : OpenRuns s 1 1 s1 := by
    rw [hw.rx25, hse0, bv64_ofNat_add, Nat.add_zero] at h148; exact h148
  by_cases hr0 : r = 0
  · have h149 := step_BEQ_taken (by omega) (rfl : s1.pc = pcAt 184)
      (rfl : openingInstr 184 = .base (.BEQ .x13 .x0 (24#13)))
      (by have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13; rw [h, hr0]; rfl)
      (by decide : pcAt 184 + signExtend13 (24#13) = pcAt 190)
    let s2 := s1.setPC (pcAt 190)
    refine ⟨2, s2, h148'.trans h149, by omega, rfl, ?_, hx26, ?_,
      ⟨ht.rx31, ht.rx15, ht.rx16, ht.rx17, ht.memTail⟩⟩
    · change BitVec.ofNat 64 (11162446080 + 8 * q) = _
      congr 1; omega
    · intro j hj
      exact hw.memDwords j (by omega)
  · have hrpos : 0 < r := by omega
    have h149 := step_BEQ_not_taken (by omega) (rfl : s1.pc = pcAt 184)
      (rfl : openingInstr 184 = .base (.BEQ .x13 .x0 (24#13)))
      (by have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13
          rw [h]; exact bv64_ofNat_ne (by omega) (by decide) (by omega))
    let s2 := s1.setPC (pcAt 185)
    have hloop : ∀ k (hk : k ≤ r), ∃ sk, OpenRuns s2 (5 * k) (5 * k) sk ∧
        sk.pc = (if k < r then pcAt 185 else pcAt 190) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (11162446080 + 8 * q + k) ∧
        sk.getReg .x13 = BitVec.ofNat 64 (8 * (r - k)) ∧
        sk.getReg .x26 = BitVec.ofNat 64 11162446080 ∧
        (∀ j (hj : j < r - k), (sk.getReg .x12).extractLsb' (8 * j) 8 = fwdBytes[8 * q + k + j]'(by omega)) ∧
        (∀ j (hj : j < 8 * q + k), sk.getByte (BitVec.ofNat 64 (11162446080 + j)) = fwdBytes[j]'(by omega)) ∧
        TailState sk tails := by
      intro k hk
      induction k with
      | zero =>
        refine ⟨s2, OpenRuns.refl s2, by rw [if_pos hrpos]; rfl,
          by rw [Nat.add_zero]; rfl,
          by rw [Nat.sub_zero]; exact hw.rx13, hx26,
          fun j hj => (hw.wbufLo j (by omega)).trans (by congr 1),
          fun j hj => hw.memDwords j (by omega),
          ht.of_eq⟩
      | succ k ih =>
        obtain ⟨sk, hrk, hpck, hx10k, hx13k, hx26k, hwLoK, hmemk, htk⟩ := ih (by omega)
        have hpck' : sk.pc = pcAt 185 := by simpa only [show k < r by omega, ite_true] using hpck
        -- 150: SB x10, x12, 0
        have haddr : sk.getReg .x10 + signExtend12 (0#12) = BitVec.ofNat 64 (11162446080 + 8 * q + k) := by
          rw [hx10k, hse0, bv64_ofNat_add, Nat.add_zero]
        have ha := step_SB (by omega) hpck' (rfl : openingInstr 185 = .base (.SB .x10 .x12 (0#12)))
          (by rw [haddr]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        have hbyte0 : (sk.getReg .x12).truncate 8 = fwdBytes[8 * q + k]'(by omega) := by
          rw [word_truncate8_eq_extractLsb'0]
          simpa using hwLoK 0 (by omega)
        let sa := (sk.setByte (BitVec.ofNat 64 (11162446080 + 8 * q + k))
          (fwdBytes[8 * q + k]'(by omega))).setPC (pcAt 186)
        have ha' : OpenRuns sk 1 1 sa := by simpa only [haddr, hbyte0, sa] using ha
        -- 151: ADDI x10, x10, 1
        have hb := step_ADDI (by omega) (rfl : sa.pc = pcAt 186)
          (rfl : openingInstr 186 = .base (.ADDI .x10 .x10 (1#12)))
        let sb := (sa.setReg .x10 (BitVec.ofNat 64 (11162446080 + 8 * q + (k + 1)))).setPC (pcAt 187)
        have hb' : OpenRuns sa 1 1 sb := by
          have hr10 : sa.getReg .x10 = BitVec.ofNat 64 (11162446080 + 8 * q + k) := by
            simp only [sa, MachineState.getReg_setPC, getReg_setByte]; exact hx10k
          rw [hr10, hse1, bv64_ofNat_add, Nat.add_assoc] at hb; exact hb
        -- 152: SRLI x12, x12, 8
        have hc := step_SRLI (by omega) (rfl : sb.pc = pcAt 187)
          (rfl : openingInstr 187 = .base (.SRLI .x12 .x12 (8#6)))
        let sc := (sb.setReg .x12 (sk.getReg .x12 >>> 8)).setPC (pcAt 188)
        have hc' : OpenRuns sb 1 1 sc := by
          have hr12 : sb.getReg .x12 = sk.getReg .x12 := by
            simp only [sb, sa, MachineState.getReg_setPC, getReg_setByte,
              getReg_setReg_ne' .x10 .x12 (by decide)]
          simpa only [hr12, show (8#6 : BitVec 6).toNat = 8 from rfl, sc] using hc
        -- 153: ADDI x13, x13, 4088 (-8)
        have hd := step_ADDI (by omega) (rfl : sc.pc = pcAt 188)
          (rfl : openingInstr 188 = .base (.ADDI .x13 .x13 (4088#12)))
        let sd := (sc.setReg .x13 (BitVec.ofNat 64 (8 * (r - (k + 1))))).setPC (pcAt 189)
        have hd' : OpenRuns sc 1 1 sd := by
          have hr13 : sc.getReg .x13 = BitVec.ofNat 64 (8 * (r - k)) := by
            simp only [sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
              getReg_setReg_ne' .x12 .x13 (by decide), getReg_setReg_ne' .x10 .x13 (by decide)]
            exact hx13k
          have hv : sc.getReg .x13 + signExtend12 (4088#12) = BitVec.ofNat 64 (8 * (r - (k + 1))) := by
            rw [hr13, bv64_add_neg8 (8 * (r - k)) (by omega)]; congr 1; omega
          simpa only [hv, sd] using hd
        have hstep4 := ((ha'.trans hb').trans hc').trans hd'
        have hmem_d : ∀ j (hj : j < 8 * q + (k + 1)),
            sd.getByte (BitVec.ofNat 64 (11162446080 + j)) = fwdBytes[j]'(by omega) := by
          intro j hj
          simp only [sd, sc, sb, sa, getByte_setPC, getByte_setReg, set_byte_read]
          by_cases hlast : j = 8 * q + k
          · subst hlast
            rw [show 11162446080 + (8 * q + k) = 11162446080 + 8 * q + k by omega, if_pos rfl]
          · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
            exact hmemk j (by omega)
        have htd : TailState sd tails := by
          have htb : tailBufBase = 20000000000 := rfl
          have ht' := tailState_setByte_outside (11162446080 + 8 * q + k)
            (fwdBytes[8 * q + k]'(by omega)) htk htbd (by omega)
          exact ⟨by simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
                getReg_setReg_ne' .x13 .x31 (by decide), getReg_setReg_ne' .x12 .x31 (by decide),
                getReg_setReg_ne' .x10 .x31 (by decide)]; exact htk.rx31,
            by simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
                getReg_setReg_ne' .x13 .x15 (by decide), getReg_setReg_ne' .x12 .x15 (by decide),
                getReg_setReg_ne' .x10 .x15 (by decide)]; exact htk.rx15,
            by simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
                getReg_setReg_ne' .x13 .x16 (by decide), getReg_setReg_ne' .x12 .x16 (by decide),
                getReg_setReg_ne' .x10 .x16 (by decide)]; exact htk.rx16,
            by simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
                getReg_setReg_ne' .x13 .x17 (by decide), getReg_setReg_ne' .x12 .x17 (by decide),
                getReg_setReg_ne' .x10 .x17 (by decide)]; exact htk.rx17,
            fun j hj => by
              simp only [sd, sc, sb, sa, getByte_setPC, getByte_setReg]
              exact ht'.memTail j hj⟩
        have hwLo_d : ∀ j (hj : j < r - (k + 1)),
            (sd.getReg .x12).extractLsb' (8 * j) 8 = fwdBytes[8 * q + (k + 1) + j]'(by omega) := by
          intro j hj
          have h12 : sd.getReg .x12 = sk.getReg .x12 >>> 8 := by
            simp only [sd, sc, MachineState.getReg_setPC, getReg_setReg_ne' .x13 .x12 (by decide)]; rfl
          rw [h12, word_ushr8_extractLsb' _ j (by omega)]
          simpa only [show 8 * q + k + (j + 1) = 8 * q + (k + 1) + j by omega] using hwLoK (j + 1) (by omega)
        have hx10_d : sd.getReg .x10 = BitVec.ofNat 64 (11162446080 + 8 * q + (k + 1)) := by
          simp only [sd, sc, sb, MachineState.getReg_setPC,
            getReg_setReg_ne' .x13 .x10 (by decide), getReg_setReg_ne' .x12 .x10 (by decide)]; rfl
        have hx26_d : sd.getReg .x26 = BitVec.ofNat 64 11162446080 := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x13 .x26 (by decide), getReg_setReg_ne' .x12 .x26 (by decide),
            getReg_setReg_ne' .x10 .x26 (by decide)]; exact hx26k
        -- 154: BNE x13, x0, 8176 (-16 -> 150)
        by_cases hmore : k + 1 < r
        · have he := step_BNE_taken (by omega) (rfl : sd.pc = pcAt 189)
            (rfl : openingInstr 189 = .base (.BNE .x13 .x0 (8176#13)))
            (by change BitVec.ofNat 64 (8 * (r - (k + 1))) ≠ BitVec.ofNat 64 0
                exact bv64_ofNat_ne (by omega) (by decide) (by omega))
            (by decide : pcAt 189 + signExtend13 (8176#13) = pcAt 185)
          exact ⟨sd.setPC (pcAt 185), by simpa only [Nat.mul_succ] using (hrk.trans hstep4).trans he,
            by rw [if_pos hmore]; rfl, hx10_d, rfl, hx26_d, hwLo_d, hmem_d, htd.of_eq⟩
        · have hdone : r - (k + 1) = 0 := by omega
          have he := step_BNE_not_taken (by omega) (rfl : sd.pc = pcAt 189)
            (rfl : openingInstr 189 = .base (.BNE .x13 .x0 (8176#13)))
            (by change BitVec.ofNat 64 (8 * (r - (k + 1))) = 0#64; rw [hdone])
          exact ⟨sd.setPC (pcAt 190), by simpa only [Nat.mul_succ] using (hrk.trans hstep4).trans he,
            by rw [if_neg hmore]; rfl, hx10_d, rfl, hx26_d, hwLo_d, hmem_d, htd.of_eq⟩
    obtain ⟨sf, hrf, hpcf, hx10f, _, hx26f, _, hmemf, htf⟩ := hloop r (Nat.le_refl r)
    have hpcf' : sf.pc = pcAt 190 := by simpa only [Nat.lt_irrefl, ite_false] using hpcf
    refine ⟨2 + 5 * r, sf, (h148'.trans h149).trans hrf, by omega, hpcf',
      by rw [hx10f]; congr 1; omega, hx26f,
      fun j hj => hmemf j (by omega), htf⟩

private theorem openRuns_flush_tail {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    (hpc : s.pc = pcAt 190)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (11162446080 + fwdBytes.length))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11162446080)
    (hfbd : fwdBytes.length ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (hpr : ProofPrefix s fwdBytes)
    (ht : TailState s tails) :
    let packed := pack6Bits tails
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 3 ∧
      s'.pc = pcAt 193 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (11162446080 + fwdBytes.length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 11162446080 ∧
      s'.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
      s'.getReg .x15 = BitVec.ofNat 64 (tailBufBase + packed.length) ∧
      ProofPrefix s' fwdBytes ∧
      TailBufPrefix s' packed := by
  intro packed
  have htb : tailBufBase = 20000000000 := rfl
  set st := tails.foldl pack6Step ([], 0, 0)
  have hst_bd := pack6_foldl_bounds tails
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
  · have h155 := step_BEQ_taken (by omega) hpc
      (rfl : openingInstr 190 = .base (.BEQ .x17 .x0 (12#13)))
      (by rw [ht.rx17]; exact congrArg (BitVec.ofNat 64) hcnt0)
      (by decide : pcAt 190 + signExtend13 (12#13) = pcAt 193)
    have hpack_eq : packed = acc := by
      unfold packed pack6Bits pack6Finish
      change (if 0 < tCnt then _ else acc) = acc
      rw [if_neg (by omega)]
    rw [hpack_eq]
    exact ⟨1, s.setPC (pcAt 193), h155, by omega, rfl, hx10, hx26, ht.rx31, ht.rx15, hpr, ht.memTail⟩
  · have hpos : 0 < tCnt := by omega
    have hpack_eq : packed = acc ++ [BitVec.ofNat 8 tBuf] := by
      unfold packed pack6Bits pack6Finish
      change (if 0 < tCnt then acc ++ [BitVec.ofNat 8 tBuf] else acc) = _
      rw [if_pos hpos]
    have h155 := step_BEQ_not_taken (by omega) hpc
      (rfl : openingInstr 190 = .base (.BEQ .x17 .x0 (12#13)))
      (by rw [ht.rx17]; exact bv64_ofNat_ne (by omega) (by decide) hcnt0)
    let s1 := s.setPC (pcAt 191)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have haddr : s1.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + acc.length) := by
      have hr15 : s1.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := ht.rx15
      rw [hr15, hse0, bv64_ofNat_add, Nat.add_zero]
    have h156 := step_SB (by omega) (rfl : s1.pc = pcAt 191)
      (rfl : openingInstr 191 = .base (.SB .x15 .x16 (0#12)))
      (by rw [haddr]; exact accessValid_ofNat _ 1 (by omega) (by omega))
    let s2 := (s1.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 tBuf)).setPC (pcAt 192)
    have h156' : OpenRuns s1 1 1 s2 := by
      have htr : (s1.getReg .x16).truncate 8 = BitVec.ofNat 8 tBuf := by
        have hr16 : s1.getReg .x16 = BitVec.ofNat 64 tBuf := ht.rx16
        rw [hr16]; exact bv64_ofNat_truncate8 tBuf (by omega)
      simpa only [haddr, htr, s2] using h156
    have h157 := step_ADDI (by omega) (rfl : s2.pc = pcAt 192)
      (rfl : openingInstr 192 = .base (.ADDI .x15 .x15 (1#12)))
    let s3 := (s2.setReg .x15 (BitVec.ofNat 64 (tailBufBase + packed.length))).setPC (pcAt 193)
    have h157' : OpenRuns s2 1 1 s3 := by
      have hr15 : s2.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := by
        simp only [s2, MachineState.getReg_setPC, getReg_setByte]; exact ht.rx15
      have hv : s2.getReg .x15 + signExtend12 (1#12) = BitVec.ofNat 64 (tailBufBase + packed.length) := by
        rw [hr15, hse1, bv64_ofNat_add, hpack_eq, List.length_append, List.length_singleton, Nat.add_assoc]
      simpa only [hv, s3] using h157
    refine ⟨3, s3, (h155.trans h156').trans h157', Nat.le_refl 3, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · simp only [s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x15 .x10 (by decide)]; exact hx10
    · simp only [s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x15 .x26 (by decide)]; exact hx26
    · simp only [s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x15 .x31 (by decide)]; exact ht.rx31
    · intro j hj
      simp only [s3, s2, s1, getByte_setPC, getByte_setReg, set_byte_read]
      rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
      exact hpr j hj
    · rw [hpack_eq]
      intro j hj
      simp only [s3, s2, s1, getByte_setPC, getByte_setReg, set_byte_read]
      have hjlen : j < acc.length + 1 := by simpa using hj
      by_cases hlast : j = acc.length
      · subst hlast
        rw [if_pos rfl, list_getElem_append_right acc [BitVec.ofNat 8 tBuf] acc.length (by omega) hj]
        simp
      · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega)),
          ht.memTail j (by omega), list_getElem_append_left acc [BitVec.ofNat 8 tBuf] j (by omega)]

private theorem openRuns_rev_tail {s : MachineState} {fwdBytes packed : List Byte}
    (hpc : s.pc = pcAt 193)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (11162446080 + fwdBytes.length))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11162446080)
    (hx31 : s.getReg .x31 = BitVec.ofNat 64 tailBufBase)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + packed.length))
    (hbd : fwdBytes.length + packed.length ≤ 8669633152)
    (hpr : ProofPrefix s fwdBytes)
    (htail : TailBufPrefix s packed) :
    ∃ s', OpenRuns s (1 + 5 * packed.length) (1 + 5 * packed.length) s' ∧
      s'.pc = pcAt 199 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (11162446080 + (fwdBytes ++ packed.reverse).length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 11162446080 ∧
      ProofPrefix s' (fwdBytes ++ packed.reverse) := by
  have htb : tailBufBase = 20000000000 := rfl
  set m := packed.length
  by_cases hm0 : m = 0
  · have hnil : packed = [] := List.eq_nil_of_length_eq_zero hm0
    have h158 := step_BEQ_taken (by omega) hpc
      (rfl : openingInstr 193 = .base (.BEQ .x15 .x31 (24#13)))
      (by rw [hx15, hx31, hm0, Nat.add_zero])
      (by decide : pcAt 193 + signExtend13 (24#13) = pcAt 199)
    subst hnil
    exact ⟨s.setPC (pcAt 199),
      by rw [hm0, Nat.mul_zero, Nat.add_zero]; exact h158,
      rfl,
      by rw [List.reverse_nil, List.append_nil]; exact hx10,
      hx26,
      by rw [List.reverse_nil, List.append_nil]; exact hpr⟩
  · have hmpos : 0 < m := by omega
    have h158 := step_BEQ_not_taken (by omega) hpc
      (rfl : openingInstr 193 = .base (.BEQ .x15 .x31 (24#13)))
      (by rw [hx15, hx31]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
    let s1 := s.setPC (pcAt 194)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have hloop : ∀ u ≤ m, ∃ su, OpenRuns s1 (5 * u) (5 * u) su ∧
        su.pc = (if u < m then pcAt 194 else pcAt 199) ∧
        su.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (m - u)) ∧
        su.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
        su.getReg .x10 = BitVec.ofNat 64 (11162446080 + fwdBytes.length + u) ∧
        su.getReg .x26 = BitVec.ofNat 64 11162446080 ∧
        ProofPrefix su (fwdBytes ++ packed.reverse.take u) ∧
        TailBufPrefix su packed := by
      intro u hu
      induction u with
      | zero =>
        refine ⟨s1, OpenRuns.refl s1, by rw [if_pos hmpos]; rfl,
          by rw [Nat.sub_zero]; exact hx15, hx31,
          by rw [Nat.add_zero]; exact hx10, hx26,
          by rw [List.take_zero, List.append_nil]; exact hpr, htail⟩
      | succ u ih =>
        obtain ⟨su, hru, hpcu, hx15u, hx31u, hx10u, hx26u, hpru, htailu⟩ := ih (by omega)
        have hpcu' : su.pc = pcAt 194 := by simpa only [show u < m by omega, ite_true] using hpcu
        -- 159: ADDI x15, x15, 4095 (-1)
        have ha := step_ADDI (by omega) hpcu' (rfl : openingInstr 194 = .base (.ADDI .x15 .x15 (4095#12)))
        let sa := (su.setReg .x15 (BitVec.ofNat 64 (tailBufBase + (m - (u + 1))))).setPC (pcAt 195)
        have ha' : OpenRuns su 1 1 sa := by
          have hr15 : su.getReg .x15 = BitVec.ofNat 64 ((tailBufBase + (m - (u + 1))) + 1) := by
            rw [hx15u]; congr 1; omega
          rw [hr15, bv64_add_neg1] at ha; exact ha
        -- 160: LBU x6, 0(x15)
        have haddr6 : sa.getReg .x15 + signExtend12 (0#12) =
            BitVec.ofNat 64 (tailBufBase + (m - (u + 1))) := by
          change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
        have hb := step_LBU (by omega) (rfl : sa.pc = pcAt 195)
          (rfl : openingInstr 195 = .base (.LBU .x6 .x15 (0#12)))
          (by rw [haddr6]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        set bCur := packed[m - (u + 1)]'(by omega)
        let sb := (sa.setReg .x6 (bCur.zeroExtend 64)).setPC (pcAt 196)
        have hb' : OpenRuns sa 1 1 sb := by
          have hget : sa.getByte (BitVec.ofNat 64 (tailBufBase + (m - (u + 1)))) = bCur :=
            htailu (m - (u + 1)) (by omega)
          simpa only [haddr6, hget, sb] using hb
        -- 161: SB x10, x6, 0
        have haddr10 : sb.getReg .x10 + signExtend12 (0#12) =
            BitVec.ofNat 64 (11162446080 + fwdBytes.length + u) := by
          have hr10 : sb.getReg .x10 = BitVec.ofNat 64 (11162446080 + fwdBytes.length + u) := hx10u
          rw [hr10, hse0, bv64_ofNat_add, Nat.add_zero]
        have hc := step_SB (by omega) (rfl : sb.pc = pcAt 196)
          (rfl : openingInstr 196 = .base (.SB .x10 .x6 (0#12)))
          (by rw [haddr10]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        let sc := (sb.setByte (BitVec.ofNat 64 (11162446080 + fwdBytes.length + u)) bCur).setPC (pcAt 197)
        have hc' : OpenRuns sb 1 1 sc := by
          have htr : (sb.getReg .x6).truncate 8 = bCur := byte_zeroExtend_truncate8 bCur
          simpa only [haddr10, htr, sc] using hc
        -- 162: ADDI x10, x10, 1
        have hd := step_ADDI (by omega) (rfl : sc.pc = pcAt 197)
          (rfl : openingInstr 197 = .base (.ADDI .x10 .x10 (1#12)))
        let sd := (sc.setReg .x10 (BitVec.ofNat 64 (11162446080 + fwdBytes.length + (u + 1)))).setPC (pcAt 198)
        have hd' : OpenRuns sc 1 1 sd := by
          have hr10 : sc.getReg .x10 = BitVec.ofNat 64 (11162446080 + fwdBytes.length + u) := by
            simp only [sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
              getReg_setReg_ne' .x6 .x10 (by decide), getReg_setReg_ne' .x15 .x10 (by decide)]
            exact hx10u
          rw [hr10, hse1, bv64_ofNat_add, Nat.add_assoc] at hd; exact hd
        have hstep4 := ((ha'.trans hb').trans hc').trans hd'
        have hx15_d : sd.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (m - (u + 1))) := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x10 .x15 (by decide), getReg_setReg_ne' .x6 .x15 (by decide)]; rfl
        have hx31_d : sd.getReg .x31 = BitVec.ofNat 64 tailBufBase := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x10 .x31 (by decide), getReg_setReg_ne' .x6 .x31 (by decide),
            getReg_setReg_ne' .x15 .x31 (by decide)]; exact hx31u
        have hx26_d : sd.getReg .x26 = BitVec.ofNat 64 11162446080 := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x10 .x26 (by decide), getReg_setReg_ne' .x6 .x26 (by decide),
            getReg_setReg_ne' .x15 .x26 (by decide)]; exact hx26u
        have hrev_u : packed.reverse[u]'(by simp [m]; omega) = bCur := by
          rw [List.getElem_reverse]; congr 1; omega
        have htake_succ : fwdBytes ++ packed.reverse.take (u + 1) =
            (fwdBytes ++ packed.reverse.take u) ++ [bCur] := by
          rw [List.take_succ_eq_append_getElem (by simp [m]; omega), hrev_u, List.append_assoc]
        have hpr_d : ProofPrefix sd (fwdBytes ++ packed.reverse.take (u + 1)) := by
          rw [htake_succ]
          intro j hj
          have hlen_pre : (fwdBytes ++ packed.reverse.take u).length = fwdBytes.length + u := by
            simp only [List.length_append, List.length_take, List.length_reverse]; omega
          have hjle : j < fwdBytes.length + u + 1 := by
            rw [List.length_append, List.length_singleton] at hj; omega
          simp only [sd, sc, sb, sa, getByte_setPC, getByte_setReg, set_byte_read]
          by_cases hlast : j = fwdBytes.length + u
          · subst hlast
            rw [show 11162446080 + (fwdBytes.length + u) = 11162446080 + fwdBytes.length + u by omega,
              if_pos rfl, list_getElem_append_right _ [bCur] (fwdBytes.length + u) (by omega) hj]
            simp [hlen_pre]
          · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
            have hjlt : j < (fwdBytes ++ packed.reverse.take u).length := by omega
            rw [hpru j hjlt, list_getElem_append_left _ [bCur] j hjlt]
        have htail_d : TailBufPrefix sd packed := by
          intro j hj
          simp only [sd, sc, sb, sa, getByte_setPC, getByte_setReg, set_byte_read]
          rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
          exact htailu j hj
        -- 163: BNE x15, x31, 8176 (-16 -> 159)
        by_cases hmore : u + 1 < m
        · have he := step_BNE_taken (by omega) (rfl : sd.pc = pcAt 198)
            (rfl : openingInstr 198 = .base (.BNE .x15 .x31 (8176#13)))
            (by rw [hx15_d, hx31_d]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
            (by decide : pcAt 198 + signExtend13 (8176#13) = pcAt 194)
          exact ⟨sd.setPC (pcAt 194), by simpa only [Nat.mul_succ] using (hru.trans hstep4).trans he,
            by rw [if_pos hmore]; rfl, hx15_d, hx31_d, rfl, hx26_d, hpr_d, htail_d⟩
        · have hdone : m - (u + 1) = 0 := by omega
          have he := step_BNE_not_taken (by omega) (rfl : sd.pc = pcAt 198)
            (rfl : openingInstr 198 = .base (.BNE .x15 .x31 (8176#13)))
            (by rw [hx15_d, hx31_d, hdone, Nat.add_zero])
          exact ⟨sd.setPC (pcAt 199), by simpa only [Nat.mul_succ] using (hru.trans hstep4).trans he,
            by rw [if_neg hmore]; rfl, hx15_d, hx31_d, rfl, hx26_d, hpr_d, htail_d⟩
    obtain ⟨sf, hrf, hpcf, _, _, hx10f, hx26f, hprf, _⟩ := hloop m (Nat.le_refl m)
    have hpcf' : sf.pc = pcAt 199 := by simpa only [Nat.lt_irrefl, ite_false] using hpcf
    have htakeAll : packed.reverse.take m = packed.reverse := by
      rw [show m = packed.reverse.length by simp [m], List.take_length]
    rw [htakeAll] at hprf
    refine ⟨sf, h158.trans hrf, hpcf', ?_, hx26f, hprf⟩
    rw [hx10f]; congr 1; simp [m]; omega

private theorem openRuns_finish {s : MachineState} {proofLen : Nat}
    (hpc : s.pc = pcAt 199)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (11162446080 + proofLen))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11162446080) :
    ∃ sHalt, OpenRuns s 3 3 sHalt ∧
      sHalt.pc = pcAt 202 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = BitVec.ofNat 64 proofLen ∧
      sHalt.mem = s.mem := by
  have h1 := step_SUB (by omega) hpc (rfl : openingInstr 199 = .base (.SUB .x11 .x10 .x26))
  have hsub : s.getReg .x10 - s.getReg .x26 = BitVec.ofNat 64 proofLen := by
    rw [hx10, hx26, bv64_ofNat_sub _ _ (by omega), Nat.add_sub_cancel_left]
  let s1 := (s.setReg .x11 (BitVec.ofNat 64 proofLen)).setPC (pcAt 200)
  have h1' : OpenRuns s 1 1 s1 := by simpa only [hsub, s1] using h1
  have h2 := step_ADDI (by omega) (rfl : s1.pc = pcAt 200)
    (rfl : openingInstr 200 = .base (.ADDI .x5 .x0 (1#12)))
  let s2 := (s1.setReg .x5 1#64).setPC (pcAt 201)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x0 + signExtend12 (1#12) = 1#64 := by
      change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 201)
    (rfl : openingInstr 201 = .base (.ADDI .x10 .x0 (0#12)))
  let s3 := (s2.setReg .x10 0#64).setPC (pcAt 202)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hv : s2.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s3] using h3
  exact ⟨s3, (h1'.trans h2').trans h3', rfl, rfl, rfl, rfl, rfl⟩


/-! ### 7. Record Loop (`32..145`) -/

private def capLeafNat (i : Nat) : Nat := ((i / 3) / 3) >>> 12

private def capMark14Prefix (positions : Positions) (t idx : Nat) : Bool :=
  decide (∃ u < t, capLeafNat (openingIndex positions u) = idx)

private theorem capMark14Prefix_card (positions : Positions) (idx : Nat) :
    capMark14Prefix positions positions.card idx = capMark positions 14 idx := by
  simp only [capMark14Prefix, capMark_14]
  by_cases hL : ∃ u < positions.card, capLeafNat (openingIndex positions u) = idx
  · have hR : ∃ i ∈ positions, capLeafOf i = idx := by
      obtain ⟨u, hu, heq⟩ := hL
      have hlen : u < (positions.sort (· ≤ ·)).length := by simpa using hu
      refine ⟨(positions.sort (· ≤ ·))[u]'hlen,
        (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hlen), ?_⟩
      simpa only [capLeafOf, capLeafNat, openingIndex, dif_pos hu] using heq
    simp [hL, hR]
  · have hR : ¬ ∃ i ∈ positions, capLeafOf i = idx := by
      rintro ⟨i, hi, heq⟩
      have hmem : i ∈ positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
      obtain ⟨u, hu, hget⟩ := list_mem_exists_getElem hmem
      have hu' : u < positions.card := by simpa using hu
      apply hL
      refine ⟨u, hu', ?_⟩
      simp only [openingIndex, dif_pos hu', hget]
      exact heq
    simp [hL, hR]

/-- Loop invariant preserved across the record-loop body (`32..145`). -/
private structure RecInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (t : Nat) (fwdBytes : List Byte) (tails : List (BitVec 6))
    (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475968
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + (rowOff + 72))
  rx19 : s.getReg .x19 = 3#64
  rx20 : s.getReg .x20 = BitVec.ofNat 64 FULL_TRIPLETS_0
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx24 : s.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * t)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 11162446080
  rx27 : s.getReg .x27 = BitVec.ofNat 64 (positions.card - t)
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  writer : WriterState s fwdBytes
  tail : TailState s tails
  cap14 : ∀ c < 456, s.getByte (BitVec.ofNat 64 (4096 + c)) =
    if capMark14Prefix positions t c then 1#8 else 0#8

private theorem RecInv.setPC {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState} (inv : RecInv trapdoor positions t fwdBytes tails s) (pc : Word) :
    RecInv trapdoor positions t fwdBytes tails (s.setPC pc) :=
  ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
   inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩

private theorem RecInv.after_sub {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes fwdBytes' : List Byte}
    {tails tails' : List (BitVec 6)} {s s' : MachineState}
    (inv : RecInv trapdoor positions t fwdBytes tails s)
    (hreg : ∀ r, r = .x2 ∨ r = .x9 ∨ r = .x18 ∨ r = .x19 ∨ r = .x20 ∨ r = .x21 ∨
      r = .x24 ∨ r = .x26 ∨ r = .x27 → s'.getReg r = s.getReg r)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s')
    (hw : WriterState s' fwdBytes')
    (ht : TailState s' tails')
    (hcap : ∀ q < 5120, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) :
    RecInv trapdoor positions t fwdBytes' tails' s' :=
  ⟨by rw [hreg .x2 (by simp)]; exact inv.rx2,
   by rw [hreg .x9 (by simp)]; exact inv.rx9,
   by rw [hreg .x18 (by simp)]; exact inv.rx18,
   by rw [hreg .x19 (by simp)]; exact inv.rx19,
   by rw [hreg .x20 (by simp)]; exact inv.rx20,
   by rw [hreg .x21 (by simp)]; exact inv.rx21,
   by rw [hreg .x24 (by simp)]; exact inv.rx24,
   by rw [hreg .x26 (by simp)]; exact inv.rx26,
   by rw [hreg .x27 (by simp)]; exact inv.rx27,
   hro, hw, ht,
   fun c hc => by rw [hcap (4096 + c) (by omega)]; exact inv.cap14 c hc⟩

private theorem openRuns_rec_salt {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (ht : t < positions.card) (hpc : s.pc = pcAt 32)
    (hbd : fwdBytes.length + 24 ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let idx : Index := (positions.sort (· ≤ ·))[t]'(by simpa using ht)
    let fwd1 := fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24
    ∃ s1, OpenRuns s 32 32 s1 ∧
      s1.pc = pcAt 44 ∧
      s1.getReg .x8 = BitVec.ofNat 64 idx.val ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro idx fwd1
  have hcard := positions_card_le positions
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hopen : openingIndex positions t = idx.val := by simp only [openingIndex, dif_pos ht]; rfl
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have haddr32 : s.getReg .x24 + signExtend12 (0#12) = BitVec.ofNat 64 (6733261056 + 8 * t) := by
    rw [inv.rx24, hse0, bv64_ofNat_add, Nat.add_zero]
  have h32 := step_LD (by omega) hpc (rfl : openingInstr 32 = .base (.LD .x8 .x24 (0#12)))
    (by rw [haddr32]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s32 := (s.setReg .x8 (BitVec.ofNat 64 idx.val)).setPC (pcAt 33)
  have h32' : OpenRuns s 1 1 s32 := by
    have hmem := readOnly_getMem_index inv.ro t ht
    rw [hopen] at hmem
    simpa only [haddr32, hmem, s32] using h32
  have h33 := step_SRLI (by omega) (rfl : s32.pc = pcAt 33)
    (rfl : openingInstr 33 = .base (.SRLI .x6 .x8 (1#6)))
  let s33 := (s32.setReg .x6 (BitVec.ofNat 64 (idx.val / 2))).setPC (pcAt 34)
  have h33' : OpenRuns s32 1 1 s33 := by
    have hv : s32.getReg .x8 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (idx.val / 2) := by
      change BitVec.ofNat 64 idx.val >>> 1 = _
      rw [bv64_ushr idx.val 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s33] using h33
  have h34 := step_SLLI (by omega) (rfl : s33.pc = pcAt 34)
    (rfl : openingInstr 34 = .base (.SLLI .x7 .x6 (7#6)))
  let s34 := (s33.setReg .x7 (BitVec.ofNat 64 (128 * (idx.val / 2)))).setPC (pcAt 35)
  have h34' : OpenRuns s33 1 1 s34 := by
    have hv : s33.getReg .x6 <<< (7#6 : BitVec 6).toNat = BitVec.ofNat 64 (128 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (idx.val / 2) <<< 7 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hv, s34] using h34
  have h35 := step_SLLI (by omega) (rfl : s34.pc = pcAt 35)
    (rfl : openingInstr 35 = .base (.SLLI .x10 .x6 (6#6)))
  let s35 := (s34.setReg .x10 (BitVec.ofNat 64 (64 * (idx.val / 2)))).setPC (pcAt 36)
  have h35' : OpenRuns s34 1 1 s35 := by
    have hv : s34.getReg .x6 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (idx.val / 2) <<< 6 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hv, s35] using h35
  have h36 := step_ADD (by omega) (rfl : s35.pc = pcAt 36)
    (rfl : openingInstr 36 = .base (.ADD .x7 .x7 .x10))
  let s36 := (s35.setReg .x7 (BitVec.ofNat 64 (192 * (idx.val / 2)))).setPC (pcAt 37)
  have h36' : OpenRuns s35 1 1 s36 := by
    have hv : s35.getReg .x7 + s35.getReg .x10 = BitVec.ofNat 64 (192 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (128 * (idx.val / 2)) + BitVec.ofNat 64 (64 * (idx.val / 2)) = _
      rw [bv64_ofNat_add]; congr 1; omega
    simpa only [hv, s36] using h36
  have h37 := step_SLLI (by omega) (rfl : s36.pc = pcAt 37)
    (rfl : openingInstr 37 = .base (.SLLI .x10 .x6 (3#6)))
  let s37 := (s36.setReg .x10 (BitVec.ofNat 64 (8 * (idx.val / 2)))).setPC (pcAt 38)
  have h37' : OpenRuns s36 1 1 s37 := by
    have hv : s36.getReg .x6 <<< (3#6 : BitVec 6).toNat = BitVec.ofNat 64 (8 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (idx.val / 2) <<< 3 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hv, s37] using h37
  have h38 := step_SUB (by omega) (rfl : s37.pc = pcAt 38)
    (rfl : openingInstr 38 = .base (.SUB .x7 .x7 .x10))
  let s38 := (s37.setReg .x7 (BitVec.ofNat 64 (184 * (idx.val / 2)))).setPC (pcAt 39)
  have h38' : OpenRuns s37 1 1 s38 := by
    have hv : s37.getReg .x7 - s37.getReg .x10 = BitVec.ofNat 64 (184 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (192 * (idx.val / 2)) - BitVec.ofNat 64 (8 * (idx.val / 2)) = _
      rw [bv64_ofNat_sub _ _ (by omega)]; congr 1; omega
    simpa only [hv, s38] using h38
  have h39 := step_ANDI (by omega) (rfl : s38.pc = pcAt 39)
    (rfl : openingInstr 39 = .base (.ANDI .x6 .x8 (1#12)))
  let s39 := (s38.setReg .x6 (BitVec.ofNat 64 (idx.val % 2))).setPC (pcAt 40)
  have h39' : OpenRuns s38 1 1 s39 := by
    have hv : s38.getReg .x8 &&& signExtend12 (1#12) = BitVec.ofNat 64 (idx.val % 2) := by
      change BitVec.ofNat 64 idx.val &&& signExtend12 (1#12) = _
      exact bv64_and1 idx.val (by omega)
    simpa only [hv, s39] using h39
  have h40 := step_SLLI (by omega) (rfl : s39.pc = pcAt 40)
    (rfl : openingInstr 40 = .base (.SLLI .x6 .x6 (4#6)))
  let s40 := (s39.setReg .x6 (BitVec.ofNat 64 (16 * (idx.val % 2)))).setPC (pcAt 41)
  have h40' : OpenRuns s39 1 1 s40 := by
    have hv : s39.getReg .x6 <<< (4#6 : BitVec 6).toNat = BitVec.ofNat 64 (16 * (idx.val % 2)) := by
      change BitVec.ofNat 64 (idx.val % 2) <<< 4 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hv, s40] using h40
  have h41 := step_ADD (by omega) (rfl : s40.pc = pcAt 41)
    (rfl : openingInstr 41 = .base (.ADD .x7 .x7 .x6))
  let s41 := (s40.setReg .x7 (BitVec.ofNat 64 (184 * (idx.val / 2) + 16 * (idx.val % 2)))).setPC (pcAt 42)
  have h41' : OpenRuns s40 1 1 s41 := by
    have hv : s40.getReg .x7 + s40.getReg .x6 =
        BitVec.ofNat 64 (184 * (idx.val / 2) + 16 * (idx.val % 2)) := by
      change BitVec.ofNat 64 (184 * (idx.val / 2)) + BitVec.ofNat 64 (16 * (idx.val % 2)) = _
      exact bv64_ofNat_add _ _
    simpa only [hv, s41] using h41
  have h42 := step_ADD (by omega) (rfl : s41.pc = pcAt 42)
    (rfl : openingInstr 42 = .base (.ADD .x10 .x18 .x7))
  let s42 := (s41.setReg .x10 (BitVec.ofNat 64 (4294971424 + saltOff idx))).setPC (pcAt 43)
  have h42' : OpenRuns s41 1 1 s42 := by
    have hr18 : s41.getReg .x18 = BitVec.ofNat 64 (4294971424 + (rowOff + 72)) := inv.rx18
    have hr7 : s41.getReg .x7 = BitVec.ofNat 64 (184 * (idx.val / 2) + 16 * (idx.val % 2)) := rfl
    have hsum : s41.getReg .x18 + s41.getReg .x7 = BitVec.ofNat 64 (4294971424 + saltOff idx) := by
      rw [hr18, hr7, bv64_ofNat_add, Nat.add_assoc, saltOff_formula idx]
    simpa only [hsum, s42] using h42
  have hinv42 : RecInv trapdoor positions t fwdBytes tails s42 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  have hsalt_bd : saltOff idx + 24 ≤ 2438289632 := by
    have h := saltOff_add_24_le idx
    rw [trapdoorBytes_eq] at h
    exact h
  obtain ⟨s44, hrcopy, hpc44, hreg44, hro44, hw44, ht44, hcap44⟩ :=
    openRuns_call_copy24 (callIdx := 43) (srcOff := saltOff idx) (jOff := 656#21)
      (fwdBytes := fwdBytes) (chunk := bitsToBytes (tdSalt trapdoor idx) 24) (tails := tails)
      (by omega) rfl (by decide) rfl rfl (saltOff_align8 idx) hsalt_bd hbd htbd
      hinv42.ro hinv42.writer hinv42.tail (bitsToBytes_length _ 24)
      (fun j hj => chunk_tdSalt trapdoor idx j hj)
  have hpre1 : OpenRuns s 6 6 s37 := ((((h32'.trans h33').trans h34').trans h35').trans h36').trans h37'
  have hpre2 : OpenRuns s37 5 5 s42 := (((h38'.trans h39').trans h40').trans h41').trans h42'
  refine ⟨s44, (hpre1.trans hpre2).trans hrcopy, hpc44, ?_, ?_⟩
  · rw [hreg44 .x8 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  · exact hinv42.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg44 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      hro44 hw44 ht44 hcap44

/-- Two consecutive `copy32` calls from `x28 + 32*k1`, `x28 + 32*k2` on dense ternary level `l < 2`. -/
private theorem openRuns_ternary_pair {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t l g k1 k2 a b c1 c2 : Nat} {j1 j2 : BitVec 21} {imm1 imm2 : BitVec 12}
    {fwdBytes : List Byte} {tails : List (BitVec 6)} {s : MachineState}
    (hl : l < 2) (hg : 3 * g + 2 < levelSize l) (hc1 : c1 + 4 < 332) (hc2 : c2 = c1 + 2)
    (hk1 : k1 < 3) (hk2 : k2 < 3)
    (ha : a = 3 * g + k1) (hb : b = 3 * g + k2)
    (hse1 : signExtend12 imm1 = BitVec.ofNat 64 (32 * k1))
    (hse2 : signExtend12 imm2 = BitVec.ofNat 64 (32 * k2))
    (hi0 : openingInstr c1 = .base (.ADDI .x10 .x28 imm1))
    (hi1 : openingInstr (c1 + 1) = .base (.JAL .x1 j1))
    (htgt1 : pcAt (c1 + 1) + signExtend21 j1 = pcAt 227)
    (hi2 : openingInstr c2 = .base (.ADDI .x10 .x28 imm2))
    (hi3 : openingInstr (c2 + 1) = .base (.JAL .x1 j2))
    (htgt2 : pcAt (c2 + 1) + signExtend21 j2 = pcAt 227)
    (hpc : s.pc = pcAt c1)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 g)
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 (4294971424 + (levelBase l + 96 * g)))
    (hbd_extra : fwdBytes.length + 64 ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let chunk := bitsToBytes (tdNode trapdoor l a) 32 ++ bitsToBytes (tdNode trapdoor l b) 32
    ∃ s', OpenRuns s 56 56 s' ∧
      s'.pc = pcAt (c2 + 2) ∧
      s'.getReg .x22 = BitVec.ofNat 64 g ∧
      RecInv trapdoor positions t (fwdBytes ++ chunk) tails s' := by
  intro chunk
  have ha_lt : a < levelSize l := by omega
  have hb_lt : b < levelSize l := by omega
  have htb : treeBytes = 894785760 := treeBytes_eq
  have hno_a : levelBase l + nodeOffset l a = levelBase l + 96 * g + 32 * k1 := by
    unfold nodeOffset; rw [if_pos hl]; omega
  have hno_b : levelBase l + nodeOffset l b = levelBase l + 96 * g + 32 * k2 := by
    unfold nodeOffset; rw [if_pos hl]; omega
  have ha_bd : levelBase l + nodeOffset l a + 32 ≤ 2438289632 := by
    have := nodeOffset_lt_treeBytes l a (by omega) ha_lt; omega
  have hb_bd : levelBase l + nodeOffset l b + 32 ≤ 2438289632 := by
    have := nodeOffset_lt_treeBytes l b (by omega) hb_lt; omega
  have hlb_al : levelBase l % 8 = 0 := levelBase_align8 l (by omega)
  -- First sibling
  have hstep1 := step_ADDI (by omega) hpc hi0
  let s1 := (s.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l a)))).setPC
    (pcAt (c1 + 1))
  have hstep1' : OpenRuns s 1 1 s1 := by
    have hsum : s.getReg .x28 + signExtend12 imm1 =
        BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l a)) := by
      rw [hx28, hse1, bv64_ofNat_add]; congr 1; omega
    simpa only [hsum, s1] using hstep1
  have hinv1 : RecInv trapdoor positions t fwdBytes tails s1 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  obtain ⟨s2, hrc1, hpc2, hreg2, hro2, hw2, ht2, hcap2⟩ :=
    openRuns_call_copy32 (callIdx := c1 + 1) (srcOff := levelBase l + nodeOffset l a) (jOff := j1)
      (fwdBytes := fwdBytes) (chunk := bitsToBytes (tdNode trapdoor l a) 32) (tails := tails)
      (by omega) hi1 htgt1 rfl rfl
      (by have := nodeOffset_align8 l a; omega) ha_bd
      (by omega) htbd hinv1.ro hinv1.writer hinv1.tail (bitsToBytes_length _ 32)
      (fun j hj => chunk_tdNode trapdoor l a 32 j (by omega) hj)
  have hinv2 : RecInv trapdoor positions t (fwdBytes ++ bitsToBytes (tdNode trapdoor l a) 32) tails s2 :=
    hinv1.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      hro2 hw2 ht2 hcap2
  -- Second sibling
  have hpc2' : s2.pc = pcAt c2 := by rw [hpc2]; congr 1; omega
  have hx28_2 : s2.getReg .x28 = BitVec.ofNat 64 (4294971424 + (levelBase l + 96 * g)) := by
    rw [hreg2 .x28 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx28
  have hx22_2 : s2.getReg .x22 = BitVec.ofNat 64 g := by
    rw [hreg2 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx22
  have hstep2 := step_ADDI (by omega) hpc2' hi2
  let s3 := (s2.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l b)))).setPC
    (pcAt (c2 + 1))
  have hstep2' : OpenRuns s2 1 1 s3 := by
    have hsum : s2.getReg .x28 + signExtend12 imm2 =
        BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l b)) := by
      rw [hx28_2, hse2, bv64_ofNat_add]; congr 1; omega
    simpa only [hsum, s3] using hstep2
  have hinv3 : RecInv trapdoor positions t (fwdBytes ++ bitsToBytes (tdNode trapdoor l a) 32) tails s3 :=
    ⟨hinv2.rx2, hinv2.rx9, hinv2.rx18, hinv2.rx19, hinv2.rx20, hinv2.rx21, hinv2.rx24, hinv2.rx26,
     hinv2.rx27, hinv2.ro, hinv2.writer.of_eq, hinv2.tail.of_eq, hinv2.cap14⟩
  obtain ⟨s4, hrc2, hpc4, hreg4, hro4, hw4, ht4, hcap4⟩ :=
    openRuns_call_copy32 (callIdx := c2 + 1) (srcOff := levelBase l + nodeOffset l b) (jOff := j2)
      (fwdBytes := fwdBytes ++ bitsToBytes (tdNode trapdoor l a) 32)
      (chunk := bitsToBytes (tdNode trapdoor l b) 32) (tails := tails)
      (by omega) hi3 htgt2 rfl rfl
      (by have := nodeOffset_align8 l b; omega) hb_bd
      (by simp only [List.length_append, bitsToBytes_length]; omega) htbd
      hinv3.ro hinv3.writer hinv3.tail (bitsToBytes_length _ 32)
      (fun j hj => chunk_tdNode trapdoor l b 32 j (by omega) hj)
  have hinv4 := hinv3.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg4 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      hro4 hw4 ht4 hcap4
  have happ : (fwdBytes ++ bitsToBytes (tdNode trapdoor l a) 32) ++ bitsToBytes (tdNode trapdoor l b) 32 =
      fwdBytes ++ chunk := List.append_assoc _ _ _
  rw [happ] at hinv4
  refine ⟨s4, ((hstep1'.trans hrc1).trans hstep2').trans hrc2, hpc4, ?_, hinv4⟩
  rw [hreg4 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx22_2

private theorem openRuns_rec_l0 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hpc : s.pc = pcAt 44)
    (idx : Index) (hx8 : s.getReg .x8 = BitVec.ofNat 64 idx.val)
    (hbd_extra : fwdBytes.length + 64 ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ l0SiblingsProof (tdNode trapdoor) idx
    ∃ steps cycles s1, OpenRuns s steps cycles s1 ∧
      steps ≤ 67 ∧ cycles ≤ 73 ∧
      s1.pc = pcAt 68 ∧
      s1.getReg .x22 = BitVec.ofNat 64 (idx.val / 3) ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hft : FULL_TRIPLETS_0 = 5592405 := full_triplets_0_eq
  have hls0 : levelSize 0 = 16777216 := levelSize_0
  set g := idx.val / 3
  set r := idx.val % 3
  have hdiv := step_DIVU (by omega) hpc (rfl : openingInstr 44 = .base (.DIVU .x22 .x8 .x19))
  let s45 := (s.setReg .x22 (BitVec.ofNat 64 g)).setPC (pcAt 45)
  have hdiv' : OpenRuns s 1 4 s45 := by
    have hv : rv64_divu (s.getReg .x8) (s.getReg .x19) = BitVec.ofNat 64 g := by
      rw [hx8, inv.rx19, rv64_divu_three, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : idx.val < 2 ^ 64)]
    simpa only [hv, s45] using hdiv
  have hrem := step_REMU (by omega) (rfl : s45.pc = pcAt 45)
    (rfl : openingInstr 45 = .base (.REMU .x23 .x8 .x19))
  let s46 := (s45.setReg .x23 (BitVec.ofNat 64 r)).setPC (pcAt 46)
  have hrem' : OpenRuns s45 1 4 s46 := by
    have hv : rv64_remu (s45.getReg .x8) (s45.getReg .x19) = BitVec.ofNat 64 r := by
      have hr8 : s45.getReg .x8 = BitVec.ofNat 64 idx.val := hx8
      have hr19 : s45.getReg .x19 = 3#64 := inv.rx19
      rw [hr8, hr19, rv64_remu_three, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : idx.val < 2 ^ 64)]
    simpa only [hv, s46] using hrem
  have hinv46 : RecInv trapdoor positions t fwdBytes tails s46 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  by_cases hg : g = FULL_TRIPLETS_0
  · have hbeq := step_BEQ_taken (by omega) (rfl : s46.pc = pcAt 46)
      (rfl : openingInstr 46 = .base (.BEQ .x22 .x20 (88#13)))
      (by change BitVec.ofNat 64 g = s.getReg .x20; rw [hg, inv.rx20])
      (by decide : pcAt 46 + signExtend13 (88#13) = pcAt 68)
    have hfwd1 : fwd1 = fwdBytes := by
      change fwdBytes ++ (if g = FULL_TRIPLETS_0 then [] else _) = fwdBytes
      rw [if_pos hg, List.append_nil]
    rw [hfwd1]
    exact ⟨3, 9, s46.setPC (pcAt 68), (hdiv'.trans hrem').trans hbeq, by omega, by omega,
      rfl, rfl, hinv46.setPC (pcAt 68)⟩
  · have hg_lt : 3 * g + 2 < levelSize 0 := by omega
    have hbeq := step_BEQ_not_taken (by omega) (rfl : s46.pc = pcAt 46)
      (rfl : openingInstr 46 = .base (.BEQ .x22 .x20 (88#13)))
      (by change BitVec.ofNat 64 g ≠ s.getReg .x20; rw [inv.rx20]
          exact bv64_ofNat_ne (by omega) (by omega) hg)
    let s47 := s46.setPC (pcAt 47)
    have h47 := step_SLLI (by omega) (rfl : s47.pc = pcAt 47)
      (rfl : openingInstr 47 = .base (.SLLI .x6 .x22 (6#6)))
    let s48 := (s47.setReg .x6 (BitVec.ofNat 64 (64 * g))).setPC (pcAt 48)
    have h47' : OpenRuns s47 1 1 s48 := by
      have hv : s47.getReg .x22 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * g) := by
        change BitVec.ofNat 64 g <<< 6 = _; rw [bv64_shl]; congr 1; omega
      simpa only [hv, s48] using h47
    have h48 := step_SLLI (by omega) (rfl : s48.pc = pcAt 48)
      (rfl : openingInstr 48 = .base (.SLLI .x7 .x22 (5#6)))
    let s49 := (s48.setReg .x7 (BitVec.ofNat 64 (32 * g))).setPC (pcAt 49)
    have h48' : OpenRuns s48 1 1 s49 := by
      have hv : s48.getReg .x22 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (32 * g) := by
        change BitVec.ofNat 64 g <<< 5 = _; rw [bv64_shl]; congr 1; omega
      simpa only [hv, s49] using h48
    have h49 := step_ADD (by omega) (rfl : s49.pc = pcAt 49)
      (rfl : openingInstr 49 = .base (.ADD .x28 .x6 .x7))
    let s50 := (s49.setReg .x28 (BitVec.ofNat 64 (96 * g))).setPC (pcAt 50)
    have h49' : OpenRuns s49 1 1 s50 := by
      have hv : s49.getReg .x6 + s49.getReg .x7 = BitVec.ofNat 64 (96 * g) := by
        change BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 (32 * g) = _
        rw [bv64_ofNat_add]; congr 1; omega
      simpa only [hv, s50] using h49
    have h50 := step_ADD (by omega) (rfl : s50.pc = pcAt 50)
      (rfl : openingInstr 50 = .base (.ADD .x28 .x9 .x28))
    let s51 := (s50.setReg .x28 (BitVec.ofNat 64 (4294971424 + (levelBase 0 + 96 * g)))).setPC (pcAt 51)
    have h50' : OpenRuns s50 1 1 s51 := by
      have hr9 : s50.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
      have hv : s50.getReg .x9 + s50.getReg .x28 = BitVec.ofNat 64 (4294971424 + (levelBase 0 + 96 * g)) := by
        rw [hr9]; change BitVec.ofNat 64 4294971424 + BitVec.ofNat 64 (96 * g) = _
        rw [bv64_ofNat_add]; congr 1; change _ = 4294971424 + (0 + 96 * g); omega
      simpa only [hv, s51] using h50
    have hpre : OpenRuns s 7 13 s51 :=
      (((((hdiv'.trans hrem').trans hbeq).trans h47').trans h48').trans h49').trans h50'
    have hinv51 : RecInv trapdoor positions t fwdBytes tails s51 :=
      ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
       inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
    by_cases hr0 : r = 0
    · have h51 := step_BEQ_taken (by omega) (rfl : s51.pc = pcAt 51)
        (rfl : openingInstr 51 = .base (.BEQ .x23 .x0 (32#13)))
        (by change BitVec.ofNat 64 r = 0#64; rw [hr0])
        (by decide : pcAt 51 + signExtend13 (32#13) = pcAt 59)
      obtain ⟨s63, hrpair, hpc63, hx22_63, inv63⟩ :=
        openRuns_ternary_pair (l := 0) (c1 := 59) (c2 := 61) (j1 := 668#21) (j2 := 660#21)
          (imm1 := 32#12) (imm2 := 64#12) (k1 := 1) (k2 := 2) (a := 3 * g + 1) (b := 3 * g + 2)
          (by omega) hg_lt (by omega) rfl (by omega) (by omega) rfl rfl (by decide) (by decide)
          rfl rfl (by decide) rfl rfl (by decide)
          rfl rfl rfl hbd_extra htbd (hinv51.setPC (pcAt 59))
      have h63 := step_JAL (by omega) hpc63 (rfl : openingInstr 63 = .base (.JAL .x0 (20#21)))
        (by decide : pcAt 63 + signExtend21 (20#21) = pcAt 68)
      have hfwd1 : fwd1 = fwdBytes ++ (bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32 ++
          bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32) := by
        change fwdBytes ++ (if g = FULL_TRIPLETS_0 then [] else
          if r = 0 then bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32 ++
            bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32
          else _) = _
        rw [if_neg hg, if_pos hr0]
      rw [hfwd1]
      exact ⟨65, 71, (s63.setReg .x0 (pcAt 64)).setPC (pcAt 68),
        ((hpre.trans h51).trans hrpair).trans h63, by omega, by omega,
        rfl, hx22_63, inv63.setPC (pcAt 68)⟩
    · have h51 := step_BEQ_not_taken (by omega) (rfl : s51.pc = pcAt 51)
        (rfl : openingInstr 51 = .base (.BEQ .x23 .x0 (32#13)))
        (by change BitVec.ofNat 64 r ≠ BitVec.ofNat 64 0; exact bv64_ofNat_ne (by omega) (by decide) hr0)
      let s52 := s51.setPC (pcAt 52)
      have h52 := step_ADDI (by omega) (rfl : s52.pc = pcAt 52)
        (rfl : openingInstr 52 = .base (.ADDI .x7 .x0 (1#12)))
      let s53 := (s52.setReg .x7 (BitVec.ofNat 64 1)).setPC (pcAt 53)
      have h52' : OpenRuns s52 1 1 s53 := by
        have hv : s52.getReg .x0 + signExtend12 (1#12) = BitVec.ofNat 64 1 := by
          change (0#64 : Word) + signExtend12 (1#12) = BitVec.ofNat 64 1; decide
        simpa only [hv, s53] using h52
      have hinv53 : RecInv trapdoor positions t fwdBytes tails s53 :=
        ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
         inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
      by_cases hr1 : r = 1
      · have h53 := step_BEQ_taken (by omega) (rfl : s53.pc = pcAt 53)
          (rfl : openingInstr 53 = .base (.BEQ .x23 .x7 (44#13)))
          (by change BitVec.ofNat 64 r = BitVec.ofNat 64 1; rw [hr1])
          (by decide : pcAt 53 + signExtend13 (44#13) = pcAt 64)
        obtain ⟨s68, hrpair, hpc68, hx22_68, inv68⟩ :=
          openRuns_ternary_pair (l := 0) (c1 := 64) (c2 := 66) (j1 := 648#21) (j2 := 640#21)
            (imm1 := 0#12) (imm2 := 64#12) (k1 := 0) (k2 := 2) (a := 3 * g) (b := 3 * g + 2)
            (by omega) hg_lt (by omega) rfl (by omega) (by omega) (by omega) rfl (by decide) (by decide)
            rfl rfl (by decide) rfl rfl (by decide)
            rfl rfl rfl hbd_extra htbd (hinv53.setPC (pcAt 64))
        have hfwd1 : fwd1 = fwdBytes ++ (bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
            bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32) := by
          change fwdBytes ++ (if g = FULL_TRIPLETS_0 then [] else
            if r = 0 then _ else
            if r = 1 then bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
              bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32
            else _) = _
          rw [if_neg hg, if_neg hr0, if_pos hr1]
        rw [hfwd1]
        exact ⟨66, 72, s68, (((hpre.trans h51).trans h52').trans h53).trans hrpair,
          by omega, by omega, hpc68, hx22_68, inv68⟩
      · have h53 := step_BEQ_not_taken (by omega) (rfl : s53.pc = pcAt 53)
          (rfl : openingInstr 53 = .base (.BEQ .x23 .x7 (44#13)))
          (by change BitVec.ofNat 64 r ≠ BitVec.ofNat 64 1; exact bv64_ofNat_ne (by omega) (by decide) hr1)
        obtain ⟨s58, hrpair, hpc58, hx22_58, inv58⟩ :=
          openRuns_ternary_pair (l := 0) (c1 := 54) (c2 := 56) (j1 := 688#21) (j2 := 680#21)
            (imm1 := 0#12) (imm2 := 32#12) (k1 := 0) (k2 := 1) (a := 3 * g) (b := 3 * g + 1)
            (by omega) hg_lt (by omega) rfl (by omega) (by omega) (by omega) rfl (by decide) (by decide)
            rfl rfl (by decide) rfl rfl (by decide)
            rfl rfl rfl hbd_extra htbd (hinv53.setPC (pcAt 54))
        have h58 := step_JAL (by omega) hpc58 (rfl : openingInstr 58 = .base (.JAL .x0 (40#21)))
          (by decide : pcAt 58 + signExtend21 (40#21) = pcAt 68)
        have hfwd1 : fwd1 = fwdBytes ++ (bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
            bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32) := by
          change fwdBytes ++ (if g = FULL_TRIPLETS_0 then [] else
            if r = 0 then _ else
            if r = 1 then _ else
            bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
              bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32) = _
          rw [if_neg hg, if_neg hr0, if_neg hr1]
        rw [hfwd1]
        exact ⟨67, 73, (s58.setReg .x0 (pcAt 59)).setPC (pcAt 68),
          ((((hpre.trans h51).trans h52').trans h53).trans hrpair).trans h58,
          by omega, by omega, rfl, hx22_58, inv58.setPC (pcAt 68)⟩

private theorem openRuns_rec_l1 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hpc : s.pc = pcAt 68)
    (idx : Index) (hx22 : s.getReg .x22 = BitVec.ofNat 64 (idx.val / 3))
    (hbd_extra : fwdBytes.length + 64 ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ l1SiblingsProof (tdNode trapdoor) idx
    ∃ steps cycles s1, OpenRuns s steps cycles s1 ∧
      steps ≤ 72 ∧ cycles ≤ 78 ∧
      s1.pc = pcAt 97 ∧
      s1.getReg .x22 = BitVec.ofNat 64 ((idx.val / 3) / 3) ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hft1 : FULL_TRIPLETS_1 = 1864135 := full_triplets_1_eq
  have hls1 : levelSize 1 = 5592406 := levelSize_1
  set g0 := idx.val / 3
  set g1 := g0 / 3
  set r1 := g0 % 3
  have hg0_le : g0 ≤ 5592405 := by omega
  have hg1_le : g1 ≤ FULL_TRIPLETS_1 := by omega
  -- 68: REMU x23, x22, x19
  have hrem := step_REMU (by omega) hpc (rfl : openingInstr 68 = .base (.REMU .x23 .x22 .x19))
  let s69 := (s.setReg .x23 (BitVec.ofNat 64 r1)).setPC (pcAt 69)
  have hrem' : OpenRuns s 1 4 s69 := by
    have hv : rv64_remu (s.getReg .x22) (s.getReg .x19) = BitVec.ofNat 64 r1 := by
      rw [hx22, inv.rx19, rv64_remu_three, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : g0 < 2 ^ 64)]
    simpa only [hv, s69] using hrem
  -- 69: DIVU x22, x22, x19
  have hdiv := step_DIVU (by omega) (rfl : s69.pc = pcAt 69)
    (rfl : openingInstr 69 = .base (.DIVU .x22 .x22 .x19))
  let s70 := (s69.setReg .x22 (BitVec.ofNat 64 g1)).setPC (pcAt 70)
  have hdiv' : OpenRuns s69 1 4 s70 := by
    have hv : rv64_divu (s69.getReg .x22) (s69.getReg .x19) = BitVec.ofNat 64 g1 := by
      have hr22 : s69.getReg .x22 = BitVec.ofNat 64 g0 := hx22
      have hr19 : s69.getReg .x19 = 3#64 := inv.rx19
      rw [hr22, hr19, rv64_divu_three, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : g0 < 2 ^ 64)]
    simpa only [hv, s70] using hdiv
  -- 70..72: li x6, FULL_TRIPLETS_1 (1864135)
  have h70 := step_ADDI (by omega) (rfl : s70.pc = pcAt 70)
    (rfl : openingInstr 70 = .base (.ADDI .x6 .x0 (910#12)))
  let s71 := (s70.setReg .x6 (BitVec.ofNat 64 910)).setPC (pcAt 71)
  have h70' : OpenRuns s70 1 1 s71 := by
    have hv : s70.getReg .x0 + signExtend12 (910#12) = BitVec.ofNat 64 910 := by
      change (0#64 : Word) + signExtend12 (910#12) = BitVec.ofNat 64 910; decide
    simpa only [hv, s71] using h70
  have h71 := step_SLLI (by omega) (rfl : s71.pc = pcAt 71)
    (rfl : openingInstr 71 = .base (.SLLI .x6 .x6 (11#6)))
  let s72 := (s71.setReg .x6 (BitVec.ofNat 64 1863680)).setPC (pcAt 72)
  have h71' : OpenRuns s71 1 1 s72 := by
    have hv : s71.getReg .x6 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 1863680 := by
      change BitVec.ofNat 64 910 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 1863680; decide
    simpa only [hv, s72] using h71
  have h72 := step_ADDI (by omega) (rfl : s72.pc = pcAt 72)
    (rfl : openingInstr 72 = .base (.ADDI .x6 .x6 (455#12)))
  let s73 := (s72.setReg .x6 (BitVec.ofNat 64 FULL_TRIPLETS_1)).setPC (pcAt 73)
  have h72' : OpenRuns s72 1 1 s73 := by
    have hv : s72.getReg .x6 + signExtend12 (455#12) = BitVec.ofNat 64 FULL_TRIPLETS_1 := by
      change BitVec.ofNat 64 1863680 + signExtend12 (455#12) = BitVec.ofNat 64 FULL_TRIPLETS_1
      rw [hft1]; decide
    simpa only [hv, s73] using h72
  have hpre0 : OpenRuns s 5 11 s73 := (((hrem'.trans hdiv').trans h70').trans h71').trans h72'
  have hinv73 : RecInv trapdoor positions t fwdBytes tails s73 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  by_cases hg1 : g1 = FULL_TRIPLETS_1
  · have hbeq := step_BEQ_taken (by omega) (rfl : s73.pc = pcAt 73)
      (rfl : openingInstr 73 = .base (.BEQ .x22 .x6 (96#13)))
      (by change BitVec.ofNat 64 g1 = BitVec.ofNat 64 FULL_TRIPLETS_1; rw [hg1])
      (by decide : pcAt 73 + signExtend13 (96#13) = pcAt 97)
    have hfwd1 : fwd1 = fwdBytes := by
      change fwdBytes ++ (if g1 = FULL_TRIPLETS_1 then [] else _) = fwdBytes
      rw [if_pos hg1, List.append_nil]
    rw [hfwd1]
    exact ⟨6, 12, s73.setPC (pcAt 97), hpre0.trans hbeq, by omega, by omega,
      rfl, rfl, hinv73.setPC (pcAt 97)⟩
  · have hg1_lt : 3 * g1 + 2 < levelSize 1 := by omega
    have hbeq := step_BEQ_not_taken (by omega) (rfl : s73.pc = pcAt 73)
      (rfl : openingInstr 73 = .base (.BEQ .x22 .x6 (96#13)))
      (by change BitVec.ofNat 64 g1 ≠ BitVec.ofNat 64 FULL_TRIPLETS_1
          exact bv64_ofNat_ne (by omega) (by omega) hg1)
    let s74 := s73.setPC (pcAt 74)
    have h74 := step_SLLI (by omega) (rfl : s74.pc = pcAt 74)
      (rfl : openingInstr 74 = .base (.SLLI .x6 .x22 (6#6)))
    let s75 := (s74.setReg .x6 (BitVec.ofNat 64 (64 * g1))).setPC (pcAt 75)
    have h74' : OpenRuns s74 1 1 s75 := by
      have hv : s74.getReg .x22 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * g1) := by
        change BitVec.ofNat 64 g1 <<< 6 = _; rw [bv64_shl]; congr 1; omega
      simpa only [hv, s75] using h74
    have h75 := step_SLLI (by omega) (rfl : s75.pc = pcAt 75)
      (rfl : openingInstr 75 = .base (.SLLI .x7 .x22 (5#6)))
    let s76 := (s75.setReg .x7 (BitVec.ofNat 64 (32 * g1))).setPC (pcAt 76)
    have h75' : OpenRuns s75 1 1 s76 := by
      have hv : s75.getReg .x22 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (32 * g1) := by
        change BitVec.ofNat 64 g1 <<< 5 = _; rw [bv64_shl]; congr 1; omega
      simpa only [hv, s76] using h75
    have h76 := step_ADD (by omega) (rfl : s76.pc = pcAt 76)
      (rfl : openingInstr 76 = .base (.ADD .x28 .x6 .x7))
    let s77 := (s76.setReg .x28 (BitVec.ofNat 64 (96 * g1))).setPC (pcAt 77)
    have h76' : OpenRuns s76 1 1 s77 := by
      have hv : s76.getReg .x6 + s76.getReg .x7 = BitVec.ofNat 64 (96 * g1) := by
        change BitVec.ofNat 64 (64 * g1) + BitVec.ofNat 64 (32 * g1) = _
        rw [bv64_ofNat_add]; congr 1; omega
      simpa only [hv, s77] using h76
    have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
    have haddr77 : s77.getReg .x2 + signExtend12 (32#12) = BitVec.ofNat 64 (68719475968 + 32 * 1) := by
      have hr2 : s77.getReg .x2 = BitVec.ofNat 64 68719475968 := inv.rx2
      rw [hr2, hse32, bv64_ofNat_add]
    have h77 := step_LD (by omega) (rfl : s77.pc = pcAt 77)
      (rfl : openingInstr 77 = .base (.LD .x6 .x2 (32#12)))
      (by rw [haddr77]; exact accessValid_ofNat _ 8 (by omega) (by omega))
    let s78 := (s77.setReg .x6 (BitVec.ofNat 64 (levelBase 1))).setPC (pcAt 78)
    have h77' : OpenRuns s77 1 1 s78 := by
      have hmem : s77.getMem (BitVec.ofNat 64 (68719475968 + 32 * 1)) = BitVec.ofNat 64 (levelBase 1) :=
        readOnly_getMem_data_base inv.ro 1 (by omega)
      simpa only [haddr77, hmem, s78] using h77
    have h78 := step_ADD (by omega) (rfl : s78.pc = pcAt 78)
      (rfl : openingInstr 78 = .base (.ADD .x28 .x28 .x6))
    let s79 := (s78.setReg .x28 (BitVec.ofNat 64 (levelBase 1 + 96 * g1))).setPC (pcAt 79)
    have h78' : OpenRuns s78 1 1 s79 := by
      have hv : s78.getReg .x28 + s78.getReg .x6 = BitVec.ofNat 64 (levelBase 1 + 96 * g1) := by
        change BitVec.ofNat 64 (96 * g1) + BitVec.ofNat 64 (levelBase 1) = _
        rw [bv64_ofNat_add, Nat.add_comm]
      simpa only [hv, s79] using h78
    have h79 := step_ADD (by omega) (rfl : s79.pc = pcAt 79)
      (rfl : openingInstr 79 = .base (.ADD .x28 .x9 .x28))
    let s80 := (s79.setReg .x28 (BitVec.ofNat 64 (4294971424 + (levelBase 1 + 96 * g1)))).setPC (pcAt 80)
    have h79' : OpenRuns s79 1 1 s80 := by
      have hr9 : s79.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
      have hv : s79.getReg .x9 + s79.getReg .x28 = BitVec.ofNat 64 (4294971424 + (levelBase 1 + 96 * g1)) := by
        rw [hr9]; change BitVec.ofNat 64 4294971424 + BitVec.ofNat 64 (levelBase 1 + 96 * g1) = _
        exact bv64_ofNat_add _ _
      simpa only [hv, s80] using h79
    have hpre : OpenRuns s 12 18 s80 :=
      ((((((hpre0.trans hbeq).trans h74').trans h75').trans h76').trans h77').trans h78').trans h79'
    have hinv80 : RecInv trapdoor positions t fwdBytes tails s80 :=
      ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
       inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
    by_cases hr0 : r1 = 0
    · have h80 := step_BEQ_taken (by omega) (rfl : s80.pc = pcAt 80)
        (rfl : openingInstr 80 = .base (.BEQ .x23 .x0 (32#13)))
        (by change BitVec.ofNat 64 r1 = 0#64; rw [hr0])
        (by decide : pcAt 80 + signExtend13 (32#13) = pcAt 88)
      obtain ⟨s92, hrpair, hpc92, hx22_92, inv92⟩ :=
        openRuns_ternary_pair (l := 1) (c1 := 88) (c2 := 90) (j1 := 552#21) (j2 := 544#21)
          (imm1 := 32#12) (imm2 := 64#12) (k1 := 1) (k2 := 2) (a := 3 * g1 + 1) (b := 3 * g1 + 2)
          (by omega) hg1_lt (by omega) rfl (by omega) (by omega) rfl rfl (by decide) (by decide)
          rfl rfl (by decide) rfl rfl (by decide)
          rfl rfl rfl hbd_extra htbd (hinv80.setPC (pcAt 88))
      have h92 := step_JAL (by omega) hpc92 (rfl : openingInstr 92 = .base (.JAL .x0 (20#21)))
        (by decide : pcAt 92 + signExtend21 (20#21) = pcAt 97)
      have hfwd1 : fwd1 = fwdBytes ++ (bitsToBytes (tdNode trapdoor 1 (3 * g1 + 1)) 32 ++
          bitsToBytes (tdNode trapdoor 1 (3 * g1 + 2)) 32) := by
        change fwdBytes ++ (if g1 = FULL_TRIPLETS_1 then [] else
          if r1 = 0 then bitsToBytes (tdNode trapdoor 1 (3 * g1 + 1)) 32 ++
            bitsToBytes (tdNode trapdoor 1 (3 * g1 + 2)) 32
          else _) = _
        rw [if_neg hg1, if_pos hr0]
      rw [hfwd1]
      exact ⟨70, 76, (s92.setReg .x0 (pcAt 93)).setPC (pcAt 97),
        ((hpre.trans h80).trans hrpair).trans h92, by omega, by omega,
        rfl, hx22_92, inv92.setPC (pcAt 97)⟩
    · have h80 := step_BEQ_not_taken (by omega) (rfl : s80.pc = pcAt 80)
        (rfl : openingInstr 80 = .base (.BEQ .x23 .x0 (32#13)))
        (by change BitVec.ofNat 64 r1 ≠ BitVec.ofNat 64 0; exact bv64_ofNat_ne (by omega) (by decide) hr0)
      let s81 := s80.setPC (pcAt 81)
      have h81 := step_ADDI (by omega) (rfl : s81.pc = pcAt 81)
        (rfl : openingInstr 81 = .base (.ADDI .x7 .x0 (1#12)))
      let s82 := (s81.setReg .x7 (BitVec.ofNat 64 1)).setPC (pcAt 82)
      have h81' : OpenRuns s81 1 1 s82 := by
        have hv : s81.getReg .x0 + signExtend12 (1#12) = BitVec.ofNat 64 1 := by
          change (0#64 : Word) + signExtend12 (1#12) = BitVec.ofNat 64 1; decide
        simpa only [hv, s82] using h81
      have hinv82 : RecInv trapdoor positions t fwdBytes tails s82 :=
        ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
         inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
      by_cases hr1 : r1 = 1
      · have h82 := step_BEQ_taken (by omega) (rfl : s82.pc = pcAt 82)
          (rfl : openingInstr 82 = .base (.BEQ .x23 .x7 (44#13)))
          (by change BitVec.ofNat 64 r1 = BitVec.ofNat 64 1; rw [hr1])
          (by decide : pcAt 82 + signExtend13 (44#13) = pcAt 93)
        obtain ⟨s97, hrpair, hpc97, hx22_97, inv97⟩ :=
          openRuns_ternary_pair (l := 1) (c1 := 93) (c2 := 95) (j1 := 532#21) (j2 := 524#21)
            (imm1 := 0#12) (imm2 := 64#12) (k1 := 0) (k2 := 2) (a := 3 * g1) (b := 3 * g1 + 2)
            (by omega) hg1_lt (by omega) rfl (by omega) (by omega) (by omega) rfl (by decide) (by decide)
            rfl rfl (by decide) rfl rfl (by decide)
            rfl rfl rfl hbd_extra htbd (hinv82.setPC (pcAt 93))
        have hfwd1 : fwd1 = fwdBytes ++ (bitsToBytes (tdNode trapdoor 1 (3 * g1)) 32 ++
            bitsToBytes (tdNode trapdoor 1 (3 * g1 + 2)) 32) := by
          change fwdBytes ++ (if g1 = FULL_TRIPLETS_1 then [] else
            if r1 = 0 then _ else
            if r1 = 1 then bitsToBytes (tdNode trapdoor 1 (3 * g1)) 32 ++
              bitsToBytes (tdNode trapdoor 1 (3 * g1 + 2)) 32
            else _) = _
          rw [if_neg hg1, if_neg hr0, if_pos hr1]
        rw [hfwd1]
        exact ⟨71, 77, s97, (((hpre.trans h80).trans h81').trans h82).trans hrpair,
          by omega, by omega, hpc97, hx22_97, inv97⟩
      · have h82 := step_BEQ_not_taken (by omega) (rfl : s82.pc = pcAt 82)
          (rfl : openingInstr 82 = .base (.BEQ .x23 .x7 (44#13)))
          (by change BitVec.ofNat 64 r1 ≠ BitVec.ofNat 64 1; exact bv64_ofNat_ne (by omega) (by decide) hr1)
        obtain ⟨s87, hrpair, hpc87, hx22_87, inv87⟩ :=
          openRuns_ternary_pair (l := 1) (c1 := 83) (c2 := 85) (j1 := 572#21) (j2 := 564#21)
            (imm1 := 0#12) (imm2 := 32#12) (k1 := 0) (k2 := 1) (a := 3 * g1) (b := 3 * g1 + 1)
            (by omega) hg1_lt (by omega) rfl (by omega) (by omega) (by omega) rfl (by decide) (by decide)
            rfl rfl (by decide) rfl rfl (by decide)
            rfl rfl rfl hbd_extra htbd (hinv82.setPC (pcAt 83))
        have h87 := step_JAL (by omega) hpc87 (rfl : openingInstr 87 = .base (.JAL .x0 (40#21)))
          (by decide : pcAt 87 + signExtend21 (40#21) = pcAt 97)
        have hfwd1 : fwd1 = fwdBytes ++ (bitsToBytes (tdNode trapdoor 1 (3 * g1)) 32 ++
            bitsToBytes (tdNode trapdoor 1 (3 * g1 + 1)) 32) := by
          change fwdBytes ++ (if g1 = FULL_TRIPLETS_1 then [] else
            if r1 = 0 then _ else
            if r1 = 1 then _ else
            bitsToBytes (tdNode trapdoor 1 (3 * g1)) 32 ++
              bitsToBytes (tdNode trapdoor 1 (3 * g1 + 1)) 32) = _
          rw [if_neg hg1, if_neg hr0, if_neg hr1]
        rw [hfwd1]
        exact ⟨72, 78, (s87.setReg .x0 (pcAt 88)).setPC (pcAt 97),
          ((((hpre.trans h80).trans h81').trans h82).trans hrpair).trans h87,
          by omega, by omega, rfl, hx22_87, inv87.setPC (pcAt 97)⟩

private def bin256StepFwd (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (g1 step : Nat) :
    List Byte :=
  let l := 2 + step
  let sib := (g1 >>> step) ^^^ 1
  if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 32 else []

private def bin240StepFwd (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (g1 step : Nat) :
    List Byte :=
  let l := 5 + step
  let sib := (g1 >>> (step + 3)) ^^^ 1
  if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 30 else []

private def bin238StepFwd (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (g1 step : Nat) :
    List Byte :=
  let l := 9 + step
  let sib := (g1 >>> (step + 7)) ^^^ 1
  if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 29 else []

private def bin238StepTails (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (g1 step : Nat) :
    List (BitVec 6) :=
  let l := 9 + step
  let sib := (g1 >>> (step + 7)) ^^^ 1
  if sib < levelSize l then [tail6 (tdNode trapdoor l sib)] else []

private theorem binPathFwd_split (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (g1 : Nat) :
    (List.range 3).flatMap (bin256StepFwd trapdoor g1) ++
      (List.range 4).flatMap (bin240StepFwd trapdoor g1) ++
      (List.range 5).flatMap (bin238StepFwd trapdoor g1) =
    binPathFwd (tdNode trapdoor) g1 := by
  unfold binPathFwd
  rw [show (12 : Nat) = 3 + 4 + 5 from rfl, List.range_add, List.range_add,
    List.flatMap_append, List.flatMap_append, List.flatMap_map, List.flatMap_map]
  refine congrArg₂ List.append (congrArg₂ List.append ?_ ?_) ?_
  · apply List.flatMap_congr; intro step hstep
    have hs : step < 3 := List.mem_range.mp hstep
    unfold bin256StepFwd
    simp only [show 2 + step < 5 by omega, ite_true]
  · apply List.flatMap_congr; intro step hstep
    have hs : step < 4 := List.mem_range.mp hstep
    unfold bin240StepFwd
    rw [show 3 + step = step + 3 by omega, show 2 + (step + 3) = 5 + step by omega]
    simp only [show ¬ (5 + step < 5) by omega, ite_false, show 5 + step < 9 by omega, ite_true]
  · apply List.flatMap_congr; intro step hstep
    have hs : step < 5 := List.mem_range.mp hstep
    unfold bin238StepFwd
    rw [show 3 + 4 + step = step + 7 by omega, show 2 + (step + 7) = 9 + step by omega]
    simp only [show ¬ (9 + step < 5) by omega, show ¬ (9 + step < 9) by omega, ite_false]

private theorem openRuns_rec_bin256_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g1 step : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hg : g1 ≤ FULL_TRIPLETS_1) (hstep : step < 3) (hpc : s.pc = pcAt 99)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (g1 >>> step))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5))
    (hbd : fwdBytes.length + 32 ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ bin256StepFwd trapdoor g1 step
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 39 ∧
      s1.pc = (if step + 1 < 3 then pcAt 99 else pcAt 112) ∧
      s1.getReg .x22 = BitVec.ofNat 64 (g1 >>> (step + 1)) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + (step + 1))) ∧
      s1.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5) ∧
      fwd1.length ≤ fwdBytes.length + 32 ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hft1 : FULL_TRIPLETS_1 = 1864135 := full_triplets_1_eq
  have hgs_le : g1 >>> step ≤ g1 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  set l := 2 + step
  set idx := g1 >>> step
  set sib := idx ^^^ 1
  have hsib_lt64 : sib < 2 ^ 64 := by
    rcases Nat.even_or_odd' idx with ⟨q, hq | hq⟩
    · rw [show sib = (2 * q) ^^^ 1 from by rw [← hq], xor_one_even]; omega
    · rw [show sib = (2 * q + 1) ^^^ 1 from by rw [← hq], xor_one_odd]; omega
  have hls_le := levelSize_le_max l (by omega)
  have h99 := step_XORI (by omega) hpc (rfl : openingInstr 99 = .base (.XORI .x28 .x22 (1#12)))
  let s100 := (s.setReg .x28 (BitVec.ofNat 64 sib)).setPC (pcAt 100)
  have h99' : OpenRuns s 1 1 s100 := by
    rw [hx22, bv64_xor1 idx (by omega)] at h99; exact h99
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have haddr100 : s100.getReg .x29 + signExtend12 (8#12) = BitVec.ofNat 64 (68719475968 + 32 * l + 8) := by
    have hr29 : s100.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := hx29
    rw [hr29, hse8, bv64_ofNat_add]
  have h100 := step_LD (by omega) (rfl : s100.pc = pcAt 100)
    (rfl : openingInstr 100 = .base (.LD .x7 .x29 (8#12)))
    (by rw [haddr100]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s101 := (s100.setReg .x7 (BitVec.ofNat 64 (levelSize l))).setPC (pcAt 101)
  have h100' : OpenRuns s100 1 1 s101 := by
    have hmem : s100.getMem (BitVec.ofNat 64 (68719475968 + 32 * l + 8)) = BitVec.ofNat 64 (levelSize l) :=
      readOnly_getMem_data_size inv.ro l (by omega)
    simpa only [haddr100, hmem, s101] using h100
  have hpre : OpenRuns s 2 2 s101 := h99'.trans h100'
  have hx28_toNat : (s101.getReg .x28).toNat = sib := by
    change (BitVec.ofNat 64 sib).toNat = sib
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsib_lt64]
  have hx7_toNat : (s101.getReg .x7).toNat = levelSize l := by
    change (BitVec.ofNat 64 (levelSize l)).toNat = levelSize l
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hinv101 : RecInv trapdoor positions t fwdBytes tails s101 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  have hto109 : ∃ n109 s109, OpenRuns s101 n109 n109 s109 ∧ n109 ≤ 34 ∧
      s109.pc = pcAt 109 ∧
      s109.getReg .x22 = BitVec.ofNat 64 idx ∧
      s109.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) ∧
      s109.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5) ∧
      fwd1.length ≤ fwdBytes.length + 32 ∧
      RecInv trapdoor positions t fwd1 tails s109 := by
    by_cases hsib_lt : sib < levelSize l
    · have h101 := step_BGEU_not_taken (by omega) (rfl : s101.pc = pcAt 101)
        (rfl : openingInstr 101 = .base (.BGEU .x28 .x7 (32#13)))
        (by rw [hx28_toNat, hx7_toNat]; exact hsib_lt)
      let s102 := s101.setPC (pcAt 102)
      have h102 := step_SRLI (by omega) (rfl : s102.pc = pcAt 102)
        (rfl : openingInstr 102 = .base (.SRLI .x6 .x28 (1#6)))
      let s103 := (s102.setReg .x6 (BitVec.ofNat 64 (sib / 2))).setPC (pcAt 103)
      have h102' : OpenRuns s102 1 1 s103 := by
        have hv : s102.getReg .x28 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (sib / 2) := by
          change BitVec.ofNat 64 sib >>> 1 = _
          rw [bv64_ushr sib 1 hsib_lt64, Nat.shiftRight_eq_div_pow]
        simpa only [hv, s103] using h102
      have h103 := step_ADD (by omega) (rfl : s103.pc = pcAt 103)
        (rfl : openingInstr 103 = .base (.ADD .x28 .x28 .x6))
      let s104 := (s103.setReg .x28 (BitVec.ofNat 64 (sib + sib / 2))).setPC (pcAt 104)
      have h103' : OpenRuns s103 1 1 s104 := by
        have hv : s103.getReg .x28 + s103.getReg .x6 = BitVec.ofNat 64 (sib + sib / 2) := by
          change BitVec.ofNat 64 sib + BitVec.ofNat 64 (sib / 2) = _; exact bv64_ofNat_add _ _
        simpa only [hv, s104] using h103
      have h104 := step_SLLI (by omega) (rfl : s104.pc = pcAt 104)
        (rfl : openingInstr 104 = .base (.SLLI .x28 .x28 (5#6)))
      let s105 := (s104.setReg .x28 (BitVec.ofNat 64 (nodeOffset l sib))).setPC (pcAt 105)
      have h104' : OpenRuns s104 1 1 s105 := by
        have hv : s104.getReg .x28 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (nodeOffset l sib) := by
          change BitVec.ofNat 64 (sib + sib / 2) <<< 5 = _
          rw [bv64_shl]; congr 1
          have hl2 : ¬ (l < 2) := by omega
          unfold nodeOffset gapOffset
          rw [if_neg hl2]; omega
        simpa only [hv, s105] using h104
      have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
      have haddr105 : s105.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475968 + 32 * l) := by
        have hr29 : s105.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := hx29
        rw [hr29, hse0, bv64_ofNat_add, Nat.add_zero]
      have h105 := step_LD (by omega) (rfl : s105.pc = pcAt 105)
        (rfl : openingInstr 105 = .base (.LD .x6 .x29 (0#12)))
        (by rw [haddr105]; exact accessValid_ofNat _ 8 (by omega) (by omega))
      let s106 := (s105.setReg .x6 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 106)
      have h105' : OpenRuns s105 1 1 s106 := by
        have hmem : s105.getMem (BitVec.ofNat 64 (68719475968 + 32 * l)) = BitVec.ofNat 64 (levelBase l) :=
          readOnly_getMem_data_base inv.ro l (by omega)
        simpa only [haddr105, hmem, s106] using h105
      have h106 := step_ADD (by omega) (rfl : s106.pc = pcAt 106)
        (rfl : openingInstr 106 = .base (.ADD .x10 .x9 .x6))
      let s107 := (s106.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 107)
      have h106' : OpenRuns s106 1 1 s107 := by
        have hr9 : s106.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
        rw [hr9] at h106
        simpa only [show s106.getReg .x6 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s107] using h106
      have h107 := step_ADD (by omega) (rfl : s107.pc = pcAt 107)
        (rfl : openingInstr 107 = .base (.ADD .x10 .x10 .x28))
      let s108 := (s107.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)))).setPC
        (pcAt 108)
      have h107' : OpenRuns s107 1 1 s108 := by
        have hv : s107.getReg .x10 + s107.getReg .x28 =
            BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)) := by
          change BitVec.ofNat 64 (4294971424 + levelBase l) + BitVec.ofNat 64 (nodeOffset l sib) = _
          rw [bv64_ofNat_add, Nat.add_assoc]
        simpa only [hv, s108] using h107
      have hinv108 : RecInv trapdoor positions t fwdBytes tails s108 :=
        ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
         inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
      have htb : treeBytes = 894785760 := treeBytes_eq
      have hno_bd : levelBase l + nodeOffset l sib + 32 ≤ 2438289632 := by
        have := nodeOffset_lt_treeBytes l sib (by omega) hsib_lt; omega
      obtain ⟨s109, hrcopy, hpc109, hreg109, hro109, hw109, ht109, hcap109⟩ :=
        openRuns_call_copy32 (callIdx := 108) (srcOff := levelBase l + nodeOffset l sib) (jOff := 476#21)
          (fwdBytes := fwdBytes) (chunk := bitsToBytes (tdNode trapdoor l sib) 32) (tails := tails)
          (by omega) rfl (by decide) rfl rfl
          (by have h1 := levelBase_align8 l (by omega); have h2 := nodeOffset_align8 l sib; omega) hno_bd
          hbd htbd hinv108.ro hinv108.writer hinv108.tail (bitsToBytes_length _ 32)
          (fun j hj => chunk_tdNode trapdoor l sib 32 j (by omega) hj)
      have hf1 : fwd1 = fwdBytes ++ bitsToBytes (tdNode trapdoor l sib) 32 := by
        change fwdBytes ++ (if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 32 else []) = _
        rw [if_pos hsib_lt]
      rw [hf1]
      refine ⟨34, s109, ((((((h101.trans h102').trans h103').trans h104').trans h105').trans h106').trans h107').trans hrcopy,
        by omega, hpc109, ?_, ?_, ?_,
        by simp only [List.length_append, bitsToBytes_length]; omega,
        hinv108.after_sub (fun r hr => by
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact hreg109 _ (by decide) (by decide) (by decide) (by decide) (by decide))
          hro109 hw109 ht109 hcap109⟩
      · rw [hreg109 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx22
      · rw [hreg109 .x29 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx29
      · rw [hreg109 .x30 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx30
    · have h101 := step_BGEU_taken (by omega) (rfl : s101.pc = pcAt 101)
        (rfl : openingInstr 101 = .base (.BGEU .x28 .x7 (32#13)))
        (by rw [hx28_toNat, hx7_toNat]; omega)
        (by decide : pcAt 101 + signExtend13 (32#13) = pcAt 109)
      have hf1 : fwd1 = fwdBytes := by
        change fwdBytes ++ (if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 32 else []) = _
        rw [if_neg hsib_lt, List.append_nil]
      rw [hf1]
      exact ⟨1, s101.setPC (pcAt 109), h101, by omega, rfl, hx22, hx29, hx30, by omega,
        hinv101.setPC (pcAt 109)⟩
  obtain ⟨n109, s109, hr109, hn109, hpc109, hx22_109, hx29_109, hx30_109, hlen1, inv109⟩ := hto109
  have h109 := step_SRLI (by omega) hpc109 (rfl : openingInstr 109 = .base (.SRLI .x22 .x22 (1#6)))
  let s110 := (s109.setReg .x22 (BitVec.ofNat 64 (g1 >>> (step + 1)))).setPC (pcAt 110)
  have h109' : OpenRuns s109 1 1 s110 := by
    have hv : s109.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (g1 >>> (step + 1)) := by
      rw [hx22_109]; change BitVec.ofNat 64 (g1 >>> step) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), nat_ushr_ushr1]
    simpa only [hv, s110] using h109
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have h110 := step_ADDI (by omega) (rfl : s110.pc = pcAt 110)
    (rfl : openingInstr 110 = .base (.ADDI .x29 .x29 (32#12)))
  let s111 := (s110.setReg .x29 (BitVec.ofNat 64 (68719475968 + 32 * (2 + (step + 1))))).setPC (pcAt 111)
  have h110' : OpenRuns s110 1 1 s111 := by
    have hr29 : s110.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := hx29_109
    have hv : s110.getReg .x29 + signExtend12 (32#12) =
        BitVec.ofNat 64 (68719475968 + 32 * (2 + (step + 1))) := by
      rw [hr29, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s111] using h110
  have hinv111 : RecInv trapdoor positions t fwd1 tails s111 :=
    ⟨inv109.rx2, inv109.rx9, inv109.rx18, inv109.rx19, inv109.rx20, inv109.rx21, inv109.rx24,
     inv109.rx26, inv109.rx27, inv109.ro, inv109.writer.of_eq, inv109.tail.of_eq, inv109.cap14⟩
  by_cases hmore : step + 1 < 3
  · have h111 := step_BNE_taken (by omega) (rfl : s111.pc = pcAt 111)
      (rfl : openingInstr 111 = .base (.BNE .x29 .x30 (8144#13)))
      (by change BitVec.ofNat 64 (68719475968 + 32 * (2 + (step + 1))) ≠ s109.getReg .x30
          rw [hx30_109]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 111 + signExtend13 (8144#13) = pcAt 99)
    exact ⟨2 + n109 + 1 + 1 + 1, s111.setPC (pcAt 99),
      (((hpre.trans hr109).trans h109').trans h110').trans h111,
      by omega, by rw [if_pos hmore]; rfl, rfl, rfl, hx30_109, hlen1, hinv111.setPC (pcAt 99)⟩
  · have hlast : step + 1 = 3 := by omega
    have h111 := step_BNE_not_taken (by omega) (rfl : s111.pc = pcAt 111)
      (rfl : openingInstr 111 = .base (.BNE .x29 .x30 (8144#13)))
      (by change BitVec.ofNat 64 (68719475968 + 32 * (2 + (step + 1))) = s109.getReg .x30
          rw [hx30_109, hlast])
    exact ⟨2 + n109 + 1 + 1 + 1, s111.setPC (pcAt 112),
      (((hpre.trans hr109).trans h109').trans h110').trans h111,
      by omega, by rw [if_neg hmore]; rfl, rfl, rfl, hx30_109, hlen1, hinv111.setPC (pcAt 112)⟩

private theorem openRuns_rec_bin256 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g1 : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hg : g1 ≤ FULL_TRIPLETS_1) (hpc : s.pc = pcAt 97)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 g1)
    (hbd : fwdBytes.length + 96 ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ (List.range 3).flatMap (bin256StepFwd trapdoor g1)
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 119 ∧
      s1.pc = pcAt 112 ∧
      s1.getReg .x22 = BitVec.ofNat 64 (g1 >>> 3) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * 5) ∧
      fwd1.length ≤ fwdBytes.length + 96 ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hse64 : signExtend12 (64#12) = BitVec.ofNat 64 64 := by decide
  have hse160 : signExtend12 (160#12) = BitVec.ofNat 64 160 := by decide
  have h97 := step_ADDI (by omega) hpc (rfl : openingInstr 97 = .base (.ADDI .x29 .x2 (64#12)))
  let s98 := (s.setReg .x29 (BitVec.ofNat 64 (68719475968 + 32 * 2))).setPC (pcAt 98)
  have h97' : OpenRuns s 1 1 s98 := by
    rw [inv.rx2, hse64, bv64_ofNat_add] at h97; exact h97
  have h98 := step_ADDI (by omega) (rfl : s98.pc = pcAt 98)
    (rfl : openingInstr 98 = .base (.ADDI .x30 .x2 (160#12)))
  let s99 := (s98.setReg .x30 (BitVec.ofNat 64 (68719475968 + 32 * 5))).setPC (pcAt 99)
  have h98' : OpenRuns s98 1 1 s99 := by
    have hr2 : s98.getReg .x2 = BitVec.ofNat 64 68719475968 := inv.rx2
    rw [hr2, hse160, bv64_ofNat_add] at h98; exact h98
  have hinv99 : RecInv trapdoor positions t fwdBytes tails s99 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  have hloop : ∀ n ≤ 3,
      let cur := fwdBytes ++ (List.range n).flatMap (bin256StepFwd trapdoor g1)
      ∃ steps sn, OpenRuns s99 steps steps sn ∧
        steps ≤ 39 * n ∧
        sn.pc = (if n < 3 then pcAt 99 else pcAt 112) ∧
        sn.getReg .x22 = BitVec.ofNat 64 (g1 >>> n) ∧
        sn.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (2 + n)) ∧
        sn.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 5) ∧
        cur.length ≤ fwdBytes.length + 32 * n ∧
        RecInv trapdoor positions t cur tails sn := by
    intro n hn
    induction n with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.add_zero]
      exact ⟨0, s99, OpenRuns.refl s99, Nat.le_refl 0, by rw [if_pos (by omega : 0 < 3)]; rfl,
        by rw [Nat.shiftRight_zero]; exact hx22, rfl, rfl, Nat.le_refl _, hinv99⟩
    | succ n ih =>
      obtain ⟨st, sn, hrn, hstn, hpcn, hx22n, hx29n, hx30n, hlenn, invn⟩ := ih (by omega)
      have hpcn' : sn.pc = pcAt 99 := by simpa only [show n < 3 by omega, ite_true] using hpcn
      obtain ⟨st1, sn1, hr1, hst1, hpc1, hx22_1, hx29_1, hx30_1, hlen1, inv1⟩ :=
        openRuns_rec_bin256_step hg (by omega) hpcn' hx22n hx29n hx30n (by omega) htbd invn
      have happ : fwdBytes ++ (List.range n).flatMap (bin256StepFwd trapdoor g1) ++ bin256StepFwd trapdoor g1 n =
          fwdBytes ++ (List.range (n + 1)).flatMap (bin256StepFwd trapdoor g1) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      rw [happ] at hlen1 inv1
      exact ⟨st + st1, sn1, hrn.trans hr1, by omega, hpc1, hx22_1, hx29_1, hx30_1, by omega, inv1⟩
  obtain ⟨st, s112, hrloop, hst, hpc112, hx22_112, hx29_112, _, hlen112, inv112⟩ := hloop 3 (Nat.le_refl 3)
  have hpc112' : s112.pc = pcAt 112 := by simpa only [Nat.lt_irrefl, ite_false] using hpc112
  exact ⟨2 + st, s112, (h97'.trans h98').trans hrloop, by omega, hpc112', hx22_112, hx29_112, hlen112, inv112⟩

private theorem openRuns_rec_bin240_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g1 step : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hg : g1 ≤ FULL_TRIPLETS_1) (hstep : step < 4) (hpc : s.pc = pcAt 113)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (g1 >>> (3 + step)))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9))
    (hbd : fwdBytes.length + 30 ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ bin240StepFwd trapdoor g1 step
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 47 ∧
      s1.pc = (if step + 1 < 4 then pcAt 113 else pcAt 126) ∧
      s1.getReg .x22 = BitVec.ofNat 64 (g1 >>> (3 + (step + 1))) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + (step + 1))) ∧
      s1.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9) ∧
      fwd1.length ≤ fwdBytes.length + 30 ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hft1 : FULL_TRIPLETS_1 = 1864135 := full_triplets_1_eq
  have hgs_le : g1 >>> (step + 3) ≤ g1 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  set l := 5 + step
  set idx := g1 >>> (step + 3)
  set sib := idx ^^^ 1
  have hidx_eq : g1 >>> (3 + step) = idx := by congr 1; omega
  have hsib_lt64 : sib < 2 ^ 64 := by
    rcases Nat.even_or_odd' idx with ⟨q, hq | hq⟩
    · rw [show sib = (2 * q) ^^^ 1 from by rw [← hq], xor_one_even]; omega
    · rw [show sib = (2 * q + 1) ^^^ 1 from by rw [← hq], xor_one_odd]; omega
  have hls_le := levelSize_le_max l (by omega)
  have hx22' : s.getReg .x22 = BitVec.ofNat 64 idx := by rw [hx22, hidx_eq]
  have h113 := step_XORI (by omega) hpc (rfl : openingInstr 113 = .base (.XORI .x28 .x22 (1#12)))
  let s114 := (s.setReg .x28 (BitVec.ofNat 64 sib)).setPC (pcAt 114)
  have h113' : OpenRuns s 1 1 s114 := by
    rw [hx22', bv64_xor1 idx (by omega)] at h113; exact h113
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have haddr114 : s114.getReg .x29 + signExtend12 (8#12) = BitVec.ofNat 64 (68719475968 + 32 * l + 8) := by
    have hr29 : s114.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := hx29
    rw [hr29, hse8, bv64_ofNat_add]
  have h114 := step_LD (by omega) (rfl : s114.pc = pcAt 114)
    (rfl : openingInstr 114 = .base (.LD .x7 .x29 (8#12)))
    (by rw [haddr114]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s115 := (s114.setReg .x7 (BitVec.ofNat 64 (levelSize l))).setPC (pcAt 115)
  have h114' : OpenRuns s114 1 1 s115 := by
    have hmem : s114.getMem (BitVec.ofNat 64 (68719475968 + 32 * l + 8)) = BitVec.ofNat 64 (levelSize l) :=
      readOnly_getMem_data_size inv.ro l (by omega)
    simpa only [haddr114, hmem, s115] using h114
  have hpre : OpenRuns s 2 2 s115 := h113'.trans h114'
  have hx28_toNat : (s115.getReg .x28).toNat = sib := by
    change (BitVec.ofNat 64 sib).toNat = sib
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsib_lt64]
  have hx7_toNat : (s115.getReg .x7).toNat = levelSize l := by
    change (BitVec.ofNat 64 (levelSize l)).toNat = levelSize l
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hinv115 : RecInv trapdoor positions t fwdBytes tails s115 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  have hto123 : ∃ n123 s123, OpenRuns s115 n123 n123 s123 ∧ n123 ≤ 42 ∧
      s123.pc = pcAt 123 ∧
      s123.getReg .x22 = BitVec.ofNat 64 idx ∧
      s123.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) ∧
      s123.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9) ∧
      fwd1.length ≤ fwdBytes.length + 30 ∧
      RecInv trapdoor positions t fwd1 tails s123 := by
    by_cases hsib_lt : sib < levelSize l
    · have h115 := step_BGEU_not_taken (by omega) (rfl : s115.pc = pcAt 115)
        (rfl : openingInstr 115 = .base (.BGEU .x28 .x7 (32#13)))
        (by rw [hx28_toNat, hx7_toNat]; exact hsib_lt)
      let s116 := s115.setPC (pcAt 116)
      have h116 := step_SRLI (by omega) (rfl : s116.pc = pcAt 116)
        (rfl : openingInstr 116 = .base (.SRLI .x6 .x28 (1#6)))
      let s117 := (s116.setReg .x6 (BitVec.ofNat 64 (sib / 2))).setPC (pcAt 117)
      have h116' : OpenRuns s116 1 1 s117 := by
        have hv : s116.getReg .x28 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (sib / 2) := by
          change BitVec.ofNat 64 sib >>> 1 = _
          rw [bv64_ushr sib 1 hsib_lt64, Nat.shiftRight_eq_div_pow]
        simpa only [hv, s117] using h116
      have h117 := step_ADD (by omega) (rfl : s117.pc = pcAt 117)
        (rfl : openingInstr 117 = .base (.ADD .x28 .x28 .x6))
      let s118 := (s117.setReg .x28 (BitVec.ofNat 64 (sib + sib / 2))).setPC (pcAt 118)
      have h117' : OpenRuns s117 1 1 s118 := by
        have hv : s117.getReg .x28 + s117.getReg .x6 = BitVec.ofNat 64 (sib + sib / 2) := by
          change BitVec.ofNat 64 sib + BitVec.ofNat 64 (sib / 2) = _; exact bv64_ofNat_add _ _
        simpa only [hv, s118] using h117
      have h118 := step_SLLI (by omega) (rfl : s118.pc = pcAt 118)
        (rfl : openingInstr 118 = .base (.SLLI .x28 .x28 (5#6)))
      let s119 := (s118.setReg .x28 (BitVec.ofNat 64 (nodeOffset l sib))).setPC (pcAt 119)
      have h118' : OpenRuns s118 1 1 s119 := by
        have hv : s118.getReg .x28 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (nodeOffset l sib) := by
          change BitVec.ofNat 64 (sib + sib / 2) <<< 5 = _
          rw [bv64_shl]; congr 1
          have hl2 : ¬ (l < 2) := by omega
          unfold nodeOffset gapOffset
          rw [if_neg hl2]; omega
        simpa only [hv, s119] using h118
      have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
      have haddr119 : s119.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475968 + 32 * l) := by
        have hr29 : s119.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := hx29
        rw [hr29, hse0, bv64_ofNat_add, Nat.add_zero]
      have h119 := step_LD (by omega) (rfl : s119.pc = pcAt 119)
        (rfl : openingInstr 119 = .base (.LD .x6 .x29 (0#12)))
        (by rw [haddr119]; exact accessValid_ofNat _ 8 (by omega) (by omega))
      let s120 := (s119.setReg .x6 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 120)
      have h119' : OpenRuns s119 1 1 s120 := by
        have hmem : s119.getMem (BitVec.ofNat 64 (68719475968 + 32 * l)) = BitVec.ofNat 64 (levelBase l) :=
          readOnly_getMem_data_base inv.ro l (by omega)
        simpa only [haddr119, hmem, s120] using h119
      have h120 := step_ADD (by omega) (rfl : s120.pc = pcAt 120)
        (rfl : openingInstr 120 = .base (.ADD .x10 .x9 .x6))
      let s121 := (s120.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 121)
      have h120' : OpenRuns s120 1 1 s121 := by
        have hr9 : s120.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
        rw [hr9] at h120
        simpa only [show s120.getReg .x6 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s121] using h120
      have h121 := step_ADD (by omega) (rfl : s121.pc = pcAt 121)
        (rfl : openingInstr 121 = .base (.ADD .x10 .x10 .x28))
      let s122 := (s121.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)))).setPC
        (pcAt 122)
      have h121' : OpenRuns s121 1 1 s122 := by
        have hv : s121.getReg .x10 + s121.getReg .x28 =
            BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)) := by
          change BitVec.ofNat 64 (4294971424 + levelBase l) + BitVec.ofNat 64 (nodeOffset l sib) = _
          rw [bv64_ofNat_add, Nat.add_assoc]
        simpa only [hv, s122] using h121
      have hinv122 : RecInv trapdoor positions t fwdBytes tails s122 :=
        ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
         inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
      have htb : treeBytes = 894785760 := treeBytes_eq
      have hno_bd : levelBase l + nodeOffset l sib + 32 ≤ 2438289632 := by
        have := nodeOffset_lt_treeBytes l sib (by omega) hsib_lt; omega
      obtain ⟨stC, s123, hrcopy, hstC, hpc123, hreg123, hro123, hw123, ht123, hcap123⟩ :=
        openRuns_call_copy30 (callIdx := 122) (srcOff := levelBase l + nodeOffset l sib) (jOff := 524#21)
          (fwdBytes := fwdBytes) (chunk := bitsToBytes (tdNode trapdoor l sib) 30) (tails := tails)
          (by omega) rfl (by decide) rfl rfl
          (by have h1 := levelBase_align8 l (by omega); have h2 := nodeOffset_align8 l sib; omega) hno_bd
          hbd htbd hinv122.ro hinv122.writer hinv122.tail (bitsToBytes_length _ 30)
          (fun j hj => chunk_tdNode trapdoor l sib 30 j (by omega) hj)
      have hf1 : fwd1 = fwdBytes ++ bitsToBytes (tdNode trapdoor l sib) 30 := by
        change fwdBytes ++ (if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 30 else []) = _
        rw [if_pos hsib_lt]
      rw [hf1]
      refine ⟨7 + stC, s123, ((((((h115.trans h116').trans h117').trans h118').trans h119').trans h120').trans h121').trans hrcopy,
        by omega, hpc123, ?_, ?_, ?_,
        by simp only [List.length_append, bitsToBytes_length]; omega,
        hinv122.after_sub (fun r hr => by
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact hreg123 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
          hro123 hw123 ht123 hcap123⟩
      · rw [hreg123 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx22'
      · rw [hreg123 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx29
      · rw [hreg123 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx30
    · have h115 := step_BGEU_taken (by omega) (rfl : s115.pc = pcAt 115)
        (rfl : openingInstr 115 = .base (.BGEU .x28 .x7 (32#13)))
        (by rw [hx28_toNat, hx7_toNat]; omega)
        (by decide : pcAt 115 + signExtend13 (32#13) = pcAt 123)
      have hf1 : fwd1 = fwdBytes := by
        change fwdBytes ++ (if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 30 else []) = _
        rw [if_neg hsib_lt, List.append_nil]
      rw [hf1]
      exact ⟨1, s115.setPC (pcAt 123), h115, by omega, rfl, hx22', hx29, hx30, by omega,
        hinv115.setPC (pcAt 123)⟩
  obtain ⟨n123, s123, hr123, hn123, hpc123, hx22_123, hx29_123, hx30_123, hlen1, inv123⟩ := hto123
  have h123 := step_SRLI (by omega) hpc123 (rfl : openingInstr 123 = .base (.SRLI .x22 .x22 (1#6)))
  let s124 := (s123.setReg .x22 (BitVec.ofNat 64 (g1 >>> (3 + (step + 1))))).setPC (pcAt 124)
  have h123' : OpenRuns s123 1 1 s124 := by
    have hv : s123.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (g1 >>> (3 + (step + 1))) := by
      rw [hx22_123]; change BitVec.ofNat 64 (g1 >>> (step + 3)) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), nat_ushr_ushr1, show step + 3 + 1 = 3 + (step + 1) by omega]
    simpa only [hv, s124] using h123
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have h124 := step_ADDI (by omega) (rfl : s124.pc = pcAt 124)
    (rfl : openingInstr 124 = .base (.ADDI .x29 .x29 (32#12)))
  let s125 := (s124.setReg .x29 (BitVec.ofNat 64 (68719475968 + 32 * (5 + (step + 1))))).setPC (pcAt 125)
  have h124' : OpenRuns s124 1 1 s125 := by
    have hr29 : s124.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := hx29_123
    have hv : s124.getReg .x29 + signExtend12 (32#12) =
        BitVec.ofNat 64 (68719475968 + 32 * (5 + (step + 1))) := by
      rw [hr29, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s125] using h124
  have hinv125 : RecInv trapdoor positions t fwd1 tails s125 :=
    ⟨inv123.rx2, inv123.rx9, inv123.rx18, inv123.rx19, inv123.rx20, inv123.rx21, inv123.rx24,
     inv123.rx26, inv123.rx27, inv123.ro, inv123.writer.of_eq, inv123.tail.of_eq, inv123.cap14⟩
  by_cases hmore : step + 1 < 4
  · have h125 := step_BNE_taken (by omega) (rfl : s125.pc = pcAt 125)
      (rfl : openingInstr 125 = .base (.BNE .x29 .x30 (8144#13)))
      (by change BitVec.ofNat 64 (68719475968 + 32 * (5 + (step + 1))) ≠ s123.getReg .x30
          rw [hx30_123]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 125 + signExtend13 (8144#13) = pcAt 113)
    exact ⟨2 + n123 + 1 + 1 + 1, s125.setPC (pcAt 113),
      (((hpre.trans hr123).trans h123').trans h124').trans h125,
      by omega, by rw [if_pos hmore]; rfl, rfl, rfl, hx30_123, hlen1, hinv125.setPC (pcAt 113)⟩
  · have hlast : step + 1 = 4 := by omega
    have h125 := step_BNE_not_taken (by omega) (rfl : s125.pc = pcAt 125)
      (rfl : openingInstr 125 = .base (.BNE .x29 .x30 (8144#13)))
      (by change BitVec.ofNat 64 (68719475968 + 32 * (5 + (step + 1))) = s123.getReg .x30
          rw [hx30_123, hlast])
    exact ⟨2 + n123 + 1 + 1 + 1, s125.setPC (pcAt 126),
      (((hpre.trans hr123).trans h123').trans h124').trans h125,
      by omega, by rw [if_neg hmore]; rfl, rfl, rfl, hx30_123, hlen1, hinv125.setPC (pcAt 126)⟩

private theorem openRuns_rec_bin240 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g1 : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hg : g1 ≤ FULL_TRIPLETS_1) (hpc : s.pc = pcAt 112)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (g1 >>> 3))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * 5))
    (hbd : fwdBytes.length + 120 ≤ 8669633152)
    (htbd : tails.length ≤ 200000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ (List.range 4).flatMap (bin240StepFwd trapdoor g1)
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 189 ∧
      s1.pc = pcAt 126 ∧
      s1.getReg .x22 = BitVec.ofNat 64 (g1 >>> 7) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * 9) ∧
      fwd1.length ≤ fwdBytes.length + 120 ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hse288 : signExtend12 (288#12) = BitVec.ofNat 64 288 := by decide
  have h112 := step_ADDI (by omega) hpc (rfl : openingInstr 112 = .base (.ADDI .x30 .x2 (288#12)))
  let s113 := (s.setReg .x30 (BitVec.ofNat 64 (68719475968 + 32 * 9))).setPC (pcAt 113)
  have h112' : OpenRuns s 1 1 s113 := by
    rw [inv.rx2, hse288, bv64_ofNat_add] at h112; exact h112
  have hinv113 : RecInv trapdoor positions t fwdBytes tails s113 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  have hloop : ∀ n ≤ 4,
      let cur := fwdBytes ++ (List.range n).flatMap (bin240StepFwd trapdoor g1)
      ∃ steps sn, OpenRuns s113 steps steps sn ∧
        steps ≤ 47 * n ∧
        sn.pc = (if n < 4 then pcAt 113 else pcAt 126) ∧
        sn.getReg .x22 = BitVec.ofNat 64 (g1 >>> (3 + n)) ∧
        sn.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (5 + n)) ∧
        sn.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 9) ∧
        cur.length ≤ fwdBytes.length + 30 * n ∧
        RecInv trapdoor positions t cur tails sn := by
    intro n hn
    induction n with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.add_zero]
      exact ⟨0, s113, OpenRuns.refl s113, Nat.le_refl 0, by rw [if_pos (by omega : 0 < 4)]; rfl,
        hx22, hx29, rfl, Nat.le_refl _, hinv113⟩
    | succ n ih =>
      obtain ⟨st, sn, hrn, hstn, hpcn, hx22n, hx29n, hx30n, hlenn, invn⟩ := ih (by omega)
      have hpcn' : sn.pc = pcAt 113 := by simpa only [show n < 4 by omega, ite_true] using hpcn
      obtain ⟨st1, sn1, hr1, hst1, hpc1, hx22_1, hx29_1, hx30_1, hlen1, inv1⟩ :=
        openRuns_rec_bin240_step hg (by omega) hpcn' hx22n hx29n hx30n (by omega) htbd invn
      have happ : fwdBytes ++ (List.range n).flatMap (bin240StepFwd trapdoor g1) ++ bin240StepFwd trapdoor g1 n =
          fwdBytes ++ (List.range (n + 1)).flatMap (bin240StepFwd trapdoor g1) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      rw [happ] at hlen1 inv1
      exact ⟨st + st1, sn1, hrn.trans hr1, by omega, hpc1, hx22_1, hx29_1, hx30_1, by omega, inv1⟩
  obtain ⟨st, s126, hrloop, hst, hpc126, hx22_126, hx29_126, _, hlen126, inv126⟩ := hloop 4 (Nat.le_refl 4)
  have hpc126' : s126.pc = pcAt 126 := by simpa only [Nat.lt_irrefl, ite_false] using hpc126
  exact ⟨1 + st, s126, h112'.trans hrloop, by omega, hpc126', hx22_126, hx29_126, hlen126, inv126⟩

private theorem openRuns_rec_bin238_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g1 step : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hg : g1 ≤ FULL_TRIPLETS_1) (hstep : step < 5) (hpc : s.pc = pcAt 127)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (g1 >>> (7 + step)))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14))
    (hbd : fwdBytes.length + 29 ≤ 8669633152)
    (htbd : tails.length < 200000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ bin238StepFwd trapdoor g1 step
    let tails1 := tails ++ bin238StepTails trapdoor g1 step
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 58 ∧
      s1.pc = (if step + 1 < 5 then pcAt 127 else pcAt 140) ∧
      s1.getReg .x22 = BitVec.ofNat 64 (g1 >>> (7 + (step + 1))) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + (step + 1))) ∧
      s1.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14) ∧
      fwd1.length ≤ fwdBytes.length + 29 ∧
      tails1.length ≤ tails.length + 1 ∧
      RecInv trapdoor positions t fwd1 tails1 s1 := by
  intro fwd1 tails1
  have hft1 : FULL_TRIPLETS_1 = 1864135 := full_triplets_1_eq
  have hgs_le : g1 >>> (step + 7) ≤ g1 := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  set l := 9 + step
  set idx := g1 >>> (step + 7)
  set sib := idx ^^^ 1
  have hidx_eq : g1 >>> (7 + step) = idx := by congr 1; omega
  have hsib_lt64 : sib < 2 ^ 64 := by
    rcases Nat.even_or_odd' idx with ⟨q, hq | hq⟩
    · rw [show sib = (2 * q) ^^^ 1 from by rw [← hq], xor_one_even]; omega
    · rw [show sib = (2 * q + 1) ^^^ 1 from by rw [← hq], xor_one_odd]; omega
  have hls_le := levelSize_le_max l (by omega)
  have hx22' : s.getReg .x22 = BitVec.ofNat 64 idx := by rw [hx22, hidx_eq]
  have h127 := step_XORI (by omega) hpc (rfl : openingInstr 127 = .base (.XORI .x28 .x22 (1#12)))
  let s128 := (s.setReg .x28 (BitVec.ofNat 64 sib)).setPC (pcAt 128)
  have h127' : OpenRuns s 1 1 s128 := by
    rw [hx22', bv64_xor1 idx (by omega)] at h127; exact h127
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have haddr128 : s128.getReg .x29 + signExtend12 (8#12) = BitVec.ofNat 64 (68719475968 + 32 * l + 8) := by
    have hr29 : s128.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := hx29
    rw [hr29, hse8, bv64_ofNat_add]
  have h128 := step_LD (by omega) (rfl : s128.pc = pcAt 128)
    (rfl : openingInstr 128 = .base (.LD .x7 .x29 (8#12)))
    (by rw [haddr128]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s129 := (s128.setReg .x7 (BitVec.ofNat 64 (levelSize l))).setPC (pcAt 129)
  have h128' : OpenRuns s128 1 1 s129 := by
    have hmem : s128.getMem (BitVec.ofNat 64 (68719475968 + 32 * l + 8)) = BitVec.ofNat 64 (levelSize l) :=
      readOnly_getMem_data_size inv.ro l (by omega)
    simpa only [haddr128, hmem, s129] using h128
  have hpre : OpenRuns s 2 2 s129 := h127'.trans h128'
  have hx28_toNat : (s129.getReg .x28).toNat = sib := by
    change (BitVec.ofNat 64 sib).toNat = sib
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsib_lt64]
  have hx7_toNat : (s129.getReg .x7).toNat = levelSize l := by
    change (BitVec.ofNat 64 (levelSize l)).toNat = levelSize l
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hinv129 : RecInv trapdoor positions t fwdBytes tails s129 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  have hto137 : ∃ n137 s137, OpenRuns s129 n137 n137 s137 ∧ n137 ≤ 53 ∧
      s137.pc = pcAt 137 ∧
      s137.getReg .x22 = BitVec.ofNat 64 idx ∧
      s137.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) ∧
      s137.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14) ∧
      fwd1.length ≤ fwdBytes.length + 29 ∧
      tails1.length ≤ tails.length + 1 ∧
      RecInv trapdoor positions t fwd1 tails1 s137 := by
    by_cases hsib_lt : sib < levelSize l
    · have h129 := step_BGEU_not_taken (by omega) (rfl : s129.pc = pcAt 129)
        (rfl : openingInstr 129 = .base (.BGEU .x28 .x7 (32#13)))
        (by rw [hx28_toNat, hx7_toNat]; exact hsib_lt)
      let s130 := s129.setPC (pcAt 130)
      have h130 := step_SRLI (by omega) (rfl : s130.pc = pcAt 130)
        (rfl : openingInstr 130 = .base (.SRLI .x6 .x28 (1#6)))
      let s131 := (s130.setReg .x6 (BitVec.ofNat 64 (sib / 2))).setPC (pcAt 131)
      have h130' : OpenRuns s130 1 1 s131 := by
        have hv : s130.getReg .x28 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (sib / 2) := by
          change BitVec.ofNat 64 sib >>> 1 = _
          rw [bv64_ushr sib 1 hsib_lt64, Nat.shiftRight_eq_div_pow]
        simpa only [hv, s131] using h130
      have h131 := step_ADD (by omega) (rfl : s131.pc = pcAt 131)
        (rfl : openingInstr 131 = .base (.ADD .x28 .x28 .x6))
      let s132 := (s131.setReg .x28 (BitVec.ofNat 64 (sib + sib / 2))).setPC (pcAt 132)
      have h131' : OpenRuns s131 1 1 s132 := by
        have hv : s131.getReg .x28 + s131.getReg .x6 = BitVec.ofNat 64 (sib + sib / 2) := by
          change BitVec.ofNat 64 sib + BitVec.ofNat 64 (sib / 2) = _; exact bv64_ofNat_add _ _
        simpa only [hv, s132] using h131
      have h132 := step_SLLI (by omega) (rfl : s132.pc = pcAt 132)
        (rfl : openingInstr 132 = .base (.SLLI .x28 .x28 (5#6)))
      let s133 := (s132.setReg .x28 (BitVec.ofNat 64 (nodeOffset l sib))).setPC (pcAt 133)
      have h132' : OpenRuns s132 1 1 s133 := by
        have hv : s132.getReg .x28 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (nodeOffset l sib) := by
          change BitVec.ofNat 64 (sib + sib / 2) <<< 5 = _
          rw [bv64_shl]; congr 1
          have hl2 : ¬ (l < 2) := by omega
          unfold nodeOffset gapOffset
          rw [if_neg hl2]; omega
        simpa only [hv, s133] using h132
      have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
      have haddr133 : s133.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475968 + 32 * l) := by
        have hr29 : s133.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := hx29
        rw [hr29, hse0, bv64_ofNat_add, Nat.add_zero]
      have h133 := step_LD (by omega) (rfl : s133.pc = pcAt 133)
        (rfl : openingInstr 133 = .base (.LD .x6 .x29 (0#12)))
        (by rw [haddr133]; exact accessValid_ofNat _ 8 (by omega) (by omega))
      let s134 := (s133.setReg .x6 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 134)
      have h133' : OpenRuns s133 1 1 s134 := by
        have hmem : s133.getMem (BitVec.ofNat 64 (68719475968 + 32 * l)) = BitVec.ofNat 64 (levelBase l) :=
          readOnly_getMem_data_base inv.ro l (by omega)
        simpa only [haddr133, hmem, s134] using h133
      have h134 := step_ADD (by omega) (rfl : s134.pc = pcAt 134)
        (rfl : openingInstr 134 = .base (.ADD .x10 .x9 .x6))
      let s135 := (s134.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 135)
      have h134' : OpenRuns s134 1 1 s135 := by
        have hr9 : s134.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
        rw [hr9] at h134
        simpa only [show s134.getReg .x6 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s135] using h134
      have h135 := step_ADD (by omega) (rfl : s135.pc = pcAt 135)
        (rfl : openingInstr 135 = .base (.ADD .x10 .x10 .x28))
      let s136 := (s135.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)))).setPC
        (pcAt 136)
      have h135' : OpenRuns s135 1 1 s136 := by
        have hv : s135.getReg .x10 + s135.getReg .x28 =
            BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)) := by
          change BitVec.ofNat 64 (4294971424 + levelBase l) + BitVec.ofNat 64 (nodeOffset l sib) = _
          rw [bv64_ofNat_add, Nat.add_assoc]
        simpa only [hv, s136] using h135
      have hinv136 : RecInv trapdoor positions t fwdBytes tails s136 :=
        ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
         inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
      obtain ⟨stC, s137, hrcopy, hstC, hpc137, hreg137, hro137, hw137, ht137, hcap137⟩ :=
        openRuns_call_copy29_tail (callIdx := 136) (l := l) (nodeIdx := sib) (jOff := 604#21)
          (fwdBytes := fwdBytes) (tails := tails) (by omega) (by omega) hsib_lt
          rfl (by decide) rfl rfl hbd htbd hinv136.ro hinv136.writer hinv136.tail
      have hf1 : fwd1 = fwdBytes ++ bitsToBytes (tdNode trapdoor l sib) 29 := by
        change fwdBytes ++ (if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 29 else []) = _
        rw [if_pos hsib_lt]
      have ht1 : tails1 = tails ++ [tail6 (tdNode trapdoor l sib)] := by
        change tails ++ (if sib < levelSize l then [tail6 (tdNode trapdoor l sib)] else []) = _
        rw [if_pos hsib_lt]
      rw [hf1, ht1]
      refine ⟨7 + stC, s137,
        ((((((h129.trans h130').trans h131').trans h132').trans h133').trans h134').trans h135').trans hrcopy,
        by omega, hpc137, ?_, ?_, ?_,
        by simp only [List.length_append, bitsToBytes_length]; omega,
        by simp only [List.length_append, List.length_singleton]; omega,
        hinv136.after_sub (fun r hr => by
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact hreg137 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
          hro137 hw137 ht137 hcap137⟩
      · exact (hreg137 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx22'
      · rw [hreg137 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx29
      · rw [hreg137 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx30
    · have h129 := step_BGEU_taken (by omega) (rfl : s129.pc = pcAt 129)
        (rfl : openingInstr 129 = .base (.BGEU .x28 .x7 (32#13)))
        (by rw [hx28_toNat, hx7_toNat]; omega)
        (by decide : pcAt 129 + signExtend13 (32#13) = pcAt 137)
      have hf1 : fwd1 = fwdBytes := by
        change fwdBytes ++ (if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 29 else []) = _
        rw [if_neg hsib_lt, List.append_nil]
      have ht1 : tails1 = tails := by
        change tails ++ (if sib < levelSize l then [tail6 (tdNode trapdoor l sib)] else []) = _
        rw [if_neg hsib_lt, List.append_nil]
      rw [hf1, ht1]
      exact ⟨1, s129.setPC (pcAt 137), h129, by omega, rfl, hx22', hx29, hx30, by omega, by omega,
        hinv129.setPC (pcAt 137)⟩
  obtain ⟨n137, s137, hr137, hn137, hpc137, hx22_137, hx29_137, hx30_137, hlen1, htlen1, inv137⟩ := hto137
  have h137 := step_SRLI (by omega) hpc137 (rfl : openingInstr 137 = .base (.SRLI .x22 .x22 (1#6)))
  let s138 := (s137.setReg .x22 (BitVec.ofNat 64 (g1 >>> (7 + (step + 1))))).setPC (pcAt 138)
  have h137' : OpenRuns s137 1 1 s138 := by
    have hv : s137.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (g1 >>> (7 + (step + 1))) := by
      rw [hx22_137]; change BitVec.ofNat 64 (g1 >>> (step + 7)) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), nat_ushr_ushr1, show step + 7 + 1 = 7 + (step + 1) by omega]
    simpa only [hv, s138] using h137
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have h138 := step_ADDI (by omega) (rfl : s138.pc = pcAt 138)
    (rfl : openingInstr 138 = .base (.ADDI .x29 .x29 (32#12)))
  let s139 := (s138.setReg .x29 (BitVec.ofNat 64 (68719475968 + 32 * (9 + (step + 1))))).setPC (pcAt 139)
  have h138' : OpenRuns s138 1 1 s139 := by
    have hr29 : s138.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := hx29_137
    have hv : s138.getReg .x29 + signExtend12 (32#12) =
        BitVec.ofNat 64 (68719475968 + 32 * (9 + (step + 1))) := by
      rw [hr29, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s139] using h138
  have hinv139 : RecInv trapdoor positions t fwd1 tails1 s139 :=
    ⟨inv137.rx2, inv137.rx9, inv137.rx18, inv137.rx19, inv137.rx20, inv137.rx21, inv137.rx24,
     inv137.rx26, inv137.rx27, inv137.ro, inv137.writer.of_eq, inv137.tail.of_eq, inv137.cap14⟩
  by_cases hmore : step + 1 < 5
  · have h139 := step_BNE_taken (by omega) (rfl : s139.pc = pcAt 139)
      (rfl : openingInstr 139 = .base (.BNE .x29 .x30 (8144#13)))
      (by change BitVec.ofNat 64 (68719475968 + 32 * (9 + (step + 1))) ≠ s137.getReg .x30
          rw [hx30_137]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 139 + signExtend13 (8144#13) = pcAt 127)
    exact ⟨2 + n137 + 1 + 1 + 1, s139.setPC (pcAt 127),
      (((hpre.trans hr137).trans h137').trans h138').trans h139,
      by omega, by rw [if_pos hmore]; rfl, rfl, rfl, hx30_137, hlen1, htlen1, hinv139.setPC (pcAt 127)⟩
  · have hlast : step + 1 = 5 := by omega
    have h139 := step_BNE_not_taken (by omega) (rfl : s139.pc = pcAt 139)
      (rfl : openingInstr 139 = .base (.BNE .x29 .x30 (8144#13)))
      (by change BitVec.ofNat 64 (68719475968 + 32 * (9 + (step + 1))) = s137.getReg .x30
          rw [hx30_137, hlast])
    exact ⟨2 + n137 + 1 + 1 + 1, s139.setPC (pcAt 140),
      (((hpre.trans hr137).trans h137').trans h138').trans h139,
      by omega, by rw [if_neg hmore]; rfl, rfl, rfl, hx30_137, hlen1, htlen1, hinv139.setPC (pcAt 140)⟩

private theorem openRuns_rec_bin238 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g1 : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hg : g1 ≤ FULL_TRIPLETS_1) (hpc : s.pc = pcAt 126)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (g1 >>> 7))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * 9))
    (hbd : fwdBytes.length + 145 ≤ 8669633152)
    (htbd : tails.length + 5 ≤ 200000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ (List.range 5).flatMap (bin238StepFwd trapdoor g1)
    let tails1 := tails ++ binPathTails (tdNode trapdoor) g1
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 291 ∧
      s1.pc = pcAt 140 ∧
      s1.getReg .x22 = BitVec.ofNat 64 (g1 >>> 12) ∧
      RecInv trapdoor positions t fwd1 tails1 s1 := by
  intro fwd1 tails1
  have hse448 : signExtend12 (448#12) = BitVec.ofNat 64 448 := by decide
  have h126 := step_ADDI (by omega) hpc (rfl : openingInstr 126 = .base (.ADDI .x30 .x2 (448#12)))
  let s127 := (s.setReg .x30 (BitVec.ofNat 64 (68719475968 + 32 * 14))).setPC (pcAt 127)
  have h126' : OpenRuns s 1 1 s127 := by
    rw [inv.rx2, hse448, bv64_ofNat_add] at h126; exact h126
  have hinv127 : RecInv trapdoor positions t fwdBytes tails s127 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  have hloop : ∀ n ≤ 5,
      let curF := fwdBytes ++ (List.range n).flatMap (bin238StepFwd trapdoor g1)
      let curT := tails ++ (List.range n).flatMap (bin238StepTails trapdoor g1)
      ∃ steps sn, OpenRuns s127 steps steps sn ∧
        steps ≤ 58 * n ∧
        sn.pc = (if n < 5 then pcAt 127 else pcAt 140) ∧
        sn.getReg .x22 = BitVec.ofNat 64 (g1 >>> (7 + n)) ∧
        sn.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (9 + n)) ∧
        sn.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 14) ∧
        curF.length ≤ fwdBytes.length + 29 * n ∧
        curT.length ≤ tails.length + n ∧
        RecInv trapdoor positions t curF curT sn := by
    intro n hn
    induction n with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.add_zero]
      exact ⟨0, s127, OpenRuns.refl s127, Nat.le_refl 0, by rw [if_pos (by omega : 0 < 5)]; rfl,
        hx22, hx29, rfl, Nat.le_refl _, Nat.le_refl _, hinv127⟩
    | succ n ih =>
      obtain ⟨st, sn, hrn, hstn, hpcn, hx22n, hx29n, hx30n, hlenn, htlenn, invn⟩ := ih (by omega)
      have hpcn' : sn.pc = pcAt 127 := by simpa only [show n < 5 by omega, ite_true] using hpcn
      obtain ⟨st1, sn1, hr1, hst1, hpc1, hx22_1, hx29_1, hx30_1, hlen1, htlen1, inv1⟩ :=
        openRuns_rec_bin238_step hg (by omega) hpcn' hx22n hx29n hx30n (by omega) (by omega) invn
      have happF : fwdBytes ++ (List.range n).flatMap (bin238StepFwd trapdoor g1) ++ bin238StepFwd trapdoor g1 n =
          fwdBytes ++ (List.range (n + 1)).flatMap (bin238StepFwd trapdoor g1) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      have happT : tails ++ (List.range n).flatMap (bin238StepTails trapdoor g1) ++ bin238StepTails trapdoor g1 n =
          tails ++ (List.range (n + 1)).flatMap (bin238StepTails trapdoor g1) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      rw [happF] at hlen1 inv1
      rw [happT] at htlen1 inv1
      exact ⟨st + st1, sn1, hrn.trans hr1, by omega, hpc1, hx22_1, hx29_1, hx30_1,
        by omega, by omega, inv1⟩
  obtain ⟨st, s140, hrloop, hst, hpc140, hx22_140, _, _, _, _, inv140⟩ := hloop 5 (Nat.le_refl 5)
  have hpc140' : s140.pc = pcAt 140 := by simpa only [Nat.lt_irrefl, ite_false] using hpc140
  have htails_eq : tails ++ (List.range 5).flatMap (bin238StepTails trapdoor g1) = tails1 := rfl
  rw [htails_eq] at inv140
  exact ⟨1 + st, s140, h126'.trans hrloop, by omega, hpc140', hx22_140, inv140⟩

private theorem openRuns_rec_iter {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (ht : t < positions.card) (hpc : s.pc = pcAt 32)
    (hbd : fwdBytes.length ≤ 513 * t)
    (htbd : tails.length ≤ 5 * t)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let idx : Index := (positions.sort (· ≤ ·))[t]'(by simpa using ht)
    let fwd' := fwdBytes ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) idx
    let tails' := tails ++ recordTails (tdNode trapdoor) idx
    ∃ steps cycles s', OpenRuns s steps cycles s' ∧
      steps ≤ 776 ∧ cycles ≤ 788 ∧
      s'.pc = (if t + 1 < positions.card then pcAt 32 else pcAt 146) ∧
      fwd'.length ≤ 513 * (t + 1) ∧
      tails'.length ≤ 5 * (t + 1) ∧
      RecInv trapdoor positions (t + 1) fwd' tails' s' := by
  intro idx fwd' tails'
  have hcard := positions_card_le positions
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hft1 : FULL_TRIPLETS_1 = 1864135 := full_triplets_1_eq
  have hg1_le : (idx.val / 3) / 3 ≤ FULL_TRIPLETS_1 := by omega
  obtain ⟨s44, hrsalt, hpc44, hx8_44, inv44⟩ := openRuns_rec_salt ht hpc (by omega) (by omega) inv
  change s44.getReg .x8 = BitVec.ofNat 64 idx.val at hx8_44
  change RecInv trapdoor positions t (fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24) tails s44 at inv44
  have hlen44 : (fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24).length ≤ 513 * t + 24 := by
    simp only [List.length_append, bitsToBytes_length]; omega
  obtain ⟨st0, cy0, s68, hrl0, hst0, hcy0, hpc68, hx22_68, inv68⟩ :=
    openRuns_rec_l0 hpc44 idx hx8_44 (by omega) (by omega) inv44
  have hlen68 : (fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24 ++
      l0SiblingsProof (tdNode trapdoor) idx).length ≤ 513 * t + 88 := by
    have := l0SiblingsProof_length_le (tdNode trapdoor) idx
    simp only [List.length_append, bitsToBytes_length] at *; omega
  obtain ⟨st1, cy1, s97, hrl1, hst1, hcy1, hpc97, hx22_97, inv97⟩ :=
    openRuns_rec_l1 hpc68 idx hx22_68 (by omega) (by omega) inv68
  have hlen97 : (fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24 ++
      l0SiblingsProof (tdNode trapdoor) idx ++
      l1SiblingsProof (tdNode trapdoor) idx).length ≤ 513 * t + 152 := by
    have := l1SiblingsProof_length_le (tdNode trapdoor) idx
    simp only [List.length_append, bitsToBytes_length] at *; omega
  obtain ⟨st256, s112, hr256, hst256, hpc112, hx22_112, hx29_112, hlen112, inv112⟩ :=
    openRuns_rec_bin256 hg1_le hpc97 hx22_97 (by omega) (by omega) inv97
  obtain ⟨st240, s126, hr240, hst240, hpc126, hx22_126, hx29_126, hlen126, inv126⟩ :=
    openRuns_rec_bin240 hg1_le hpc112 hx22_112 hx29_112 (by omega) (by omega) inv112
  obtain ⟨st238, s140, hr238, hst238, hpc140, hx22_140, inv140⟩ :=
    openRuns_rec_bin238 hg1_le hpc126 hx22_126 hx29_126 (by omega) (by omega) inv126
  have happF : fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24 ++
      l0SiblingsProof (tdNode trapdoor) idx ++
      l1SiblingsProof (tdNode trapdoor) idx ++
      (List.range 3).flatMap (bin256StepFwd trapdoor ((idx.val / 3) / 3)) ++
      (List.range 4).flatMap (bin240StepFwd trapdoor ((idx.val / 3) / 3)) ++
      (List.range 5).flatMap (bin238StepFwd trapdoor ((idx.val / 3) / 3)) = fwd' := by
    simp only [fwd', recordFwd, ← binPathFwd_split trapdoor ((idx.val / 3) / 3), List.append_assoc]
  have happT : tails ++ binPathTails (tdNode trapdoor) ((idx.val / 3) / 3) = tails' := rfl
  rw [happF, happT] at inv140
  have hlen_recF : fwd'.length ≤ 513 * (t + 1) := by
    have hr := recordFwd_length_le_513 (tdNode trapdoor) (tdSalt trapdoor) idx
    simp only [fwd', List.length_append]; omega
  have hlen_recT : tails'.length ≤ 5 * (t + 1) := by
    have hr := recordTails_length_le_5 (tdNode trapdoor) idx
    simp only [tails', List.length_append]; omega
  -- Tail: 140..145 (6 steps; x22 is already capLeafNat idx.val)
  have hcap_lt : capLeafNat idx.val < 456 := capLeafOf_lt idx
  have h140 := step_ADD (by omega) hpc140 (rfl : openingInstr 140 = .base (.ADD .x6 .x21 .x22))
  let s141 := (s140.setReg .x6 (BitVec.ofNat 64 (4096 + capLeafNat idx.val))).setPC (pcAt 141)
  have h140' : OpenRuns s140 1 1 s141 := by
    have hr21 : s140.getReg .x21 = BitVec.ofNat 64 4096 := inv140.rx21
    have hr22 : s140.getReg .x22 = BitVec.ofNat 64 (capLeafNat idx.val) := hx22_140
    rw [hr21, hr22, bv64_ofNat_add] at h140; exact h140
  have h141 := step_ADDI (by omega) (rfl : s141.pc = pcAt 141)
    (rfl : openingInstr 141 = .base (.ADDI .x7 .x0 (1#12)))
  let s142 := (s141.setReg .x7 1#64).setPC (pcAt 142)
  have h141' : OpenRuns s141 1 1 s142 := by
    have hv : s141.getReg .x0 + signExtend12 (1#12) = 1#64 := by
      change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s142] using h141
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have haddr142 : s142.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (4096 + capLeafNat idx.val) := by
    change BitVec.ofNat 64 (4096 + capLeafNat idx.val) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h142 := step_SB (by omega) (rfl : s142.pc = pcAt 142)
    (rfl : openingInstr 142 = .base (.SB .x6 .x7 (0#12)))
    (by rw [haddr142]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s143 := (s142.setByte (BitVec.ofNat 64 (4096 + capLeafNat idx.val)) 1#8).setPC (pcAt 143)
  have h142' : OpenRuns s142 1 1 s143 := by
    have htr : (s142.getReg .x7).truncate 8 = 1#8 := by
      change (1#64 : Word).truncate 8 = 1#8; decide
    simpa only [haddr142, htr, s143] using h142
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have h143 := step_ADDI (by omega) (rfl : s143.pc = pcAt 143)
    (rfl : openingInstr 143 = .base (.ADDI .x24 .x24 (8#12)))
  let s144 := (s143.setReg .x24 (BitVec.ofNat 64 (6733261056 + 8 * (t + 1)))).setPC (pcAt 144)
  have h143' : OpenRuns s143 1 1 s144 := by
    have hr24 : s143.getReg .x24 = BitVec.ofNat 64 (6733261056 + 8 * t) := by
      simp only [s143, s142, s141, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x7 .x24 (by decide),
        getReg_setReg_ne' .x6 .x24 (by decide)]
      exact inv140.rx24
    have hv : s143.getReg .x24 + signExtend12 (8#12) =
        BitVec.ofNat 64 (6733261056 + 8 * (t + 1)) := by
      rw [hr24, hse8, bv64_ofNat_add]; congr 1
    simpa only [hv, s144] using h143
  have h144 := step_ADDI (by omega) (rfl : s144.pc = pcAt 144)
    (rfl : openingInstr 144 = .base (.ADDI .x27 .x27 (4095#12)))
  let s145 := (s144.setReg .x27 (BitVec.ofNat 64 (positions.card - (t + 1)))).setPC (pcAt 145)
  have h144' : OpenRuns s144 1 1 s145 := by
    have hr27 : s144.getReg .x27 = BitVec.ofNat 64 ((positions.card - (t + 1)) + 1) := by
      simp only [s144, s143, s142, s141, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x24 .x27 (by decide),
        getReg_setReg_ne' .x7 .x27 (by decide),
        getReg_setReg_ne' .x6 .x27 (by decide)]
      rw [inv140.rx27]; congr 1; omega
    rw [hr27, bv64_add_neg1] at h144; exact h144
  have hpres145 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x24 → r ≠ .x27 →
      s145.getReg r = s140.getReg r := fun r h6 h7 h24 h27 => by
    simp only [s145, s144, s143, s142, s141, MachineState.getReg_setPC, getReg_setByte,
      getReg_setReg_ne' .x27 r (Ne.symm h27),
      getReg_setReg_ne' .x24 r (Ne.symm h24),
      getReg_setReg_ne' .x7 r (Ne.symm h7),
      getReg_setReg_ne' .x6 r (Ne.symm h6)]
  have hmem145 : ∀ a, s145.getByte a =
      (s140.setByte (BitVec.ofNat 64 (4096 + capLeafNat idx.val)) 1#8).getByte a := fun a => by
    simp only [s145, s144, s143, s142, s141, getByte_setPC, getByte_setReg]; rfl
  have hro145 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s145 := by
    intro a ha
    simp only [s145, MachineState.getMem_setPC, MachineState.getMem_setReg, s144, s143]
    exact readOnly_setByte_cap (4096 + capLeafNat idx.val) 1#8 inv140.ro (by omega) (by omega) a ha
  have hw145 : WriterState s145 fwd' := by
    have hw' := writerState_setByte_outside (4096 + capLeafNat idx.val) 1#8 inv140.writer
      (by omega) (Or.inl (by omega)) (by omega)
    exact ⟨by rw [hpres145 .x25 (by decide) (by decide) (by decide) (by decide)]; exact inv140.writer.rx25,
      by rw [hpres145 .x13 (by decide) (by decide) (by decide) (by decide)]; exact inv140.writer.rx13,
      by rw [hpres145 .x14 (by decide) (by decide) (by decide) (by decide)]; exact inv140.writer.rx14,
      fun j hj => by rw [hpres145 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv140.writer.wbufLo j hj,
      fun j h1 h2 => by rw [hpres145 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv140.writer.wbufHi j h1 h2,
      fun j hj => by rw [hmem145]; exact hw'.memDwords j hj⟩
  have ht145 : TailState s145 tails' := by
    have htb : tailBufBase = 20000000000 := rfl
    have ht' := tailState_setByte_outside (4096 + capLeafNat idx.val) 1#8 inv140.tail (by omega) (by omega)
    exact ⟨by rw [hpres145 .x31 (by decide) (by decide) (by decide) (by decide)]; exact inv140.tail.rx31,
      by rw [hpres145 .x15 (by decide) (by decide) (by decide) (by decide)]; exact inv140.tail.rx15,
      by rw [hpres145 .x16 (by decide) (by decide) (by decide) (by decide)]; exact inv140.tail.rx16,
      by rw [hpres145 .x17 (by decide) (by decide) (by decide) (by decide)]; exact inv140.tail.rx17,
      fun j hj => by rw [hmem145]; exact ht'.memTail j hj⟩
  have hcap145 : ∀ c < 456, s145.getByte (BitVec.ofNat 64 (4096 + c)) =
      if capMark14Prefix positions (t + 1) c then 1#8 else 0#8 := by
    intro c hc
    rw [hmem145, set_byte_read]
    have hopen : openingIndex positions t = idx.val := by simp only [openingIndex, dif_pos ht]; rfl
    by_cases hceq : c = capLeafNat idx.val
    · subst hceq
      rw [if_pos rfl]
      have htr : capMark14Prefix positions (t + 1) (capLeafNat idx.val) = true := by
        simp only [capMark14Prefix, decide_eq_true_eq]
        exact ⟨t, by omega, by rw [hopen]⟩
      rw [htr]; rfl
    · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega)), inv140.cap14 c hc]
      have hsame : capMark14Prefix positions (t + 1) c = capMark14Prefix positions t c := by
        simp only [capMark14Prefix]
        by_cases hp : ∃ u < t, capLeafNat (openingIndex positions u) = c
        · have hp1 : ∃ u < t + 1, capLeafNat (openingIndex positions u) = c := by
            obtain ⟨u, hu, heq⟩ := hp; exact ⟨u, by omega, heq⟩
          rw [decide_eq_true hp, decide_eq_true hp1]
        · have hp1 : ¬ ∃ u < t + 1, capLeafNat (openingIndex positions u) = c := by
            rintro ⟨u, hu, heq⟩
            by_cases hut : u < t
            · exact hp ⟨u, hut, heq⟩
            · have hueq : u = t := by omega
              subst hueq; rw [hopen] at heq; exact hceq heq.symm
          rw [decide_eq_false hp, decide_eq_false hp1]
      rw [hsame]
  have hinv145 : RecInv trapdoor positions (t + 1) fwd' tails' s145 :=
    ⟨by rw [hpres145 .x2 (by decide) (by decide) (by decide) (by decide)]; exact inv140.rx2,
     by rw [hpres145 .x9 (by decide) (by decide) (by decide) (by decide)]; exact inv140.rx9,
     by rw [hpres145 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv140.rx18,
     by rw [hpres145 .x19 (by decide) (by decide) (by decide) (by decide)]; exact inv140.rx19,
     by rw [hpres145 .x20 (by decide) (by decide) (by decide) (by decide)]; exact inv140.rx20,
     by rw [hpres145 .x21 (by decide) (by decide) (by decide) (by decide)]; exact inv140.rx21,
     by simp only [s145, MachineState.getReg_setPC, getReg_setReg_ne' .x27 .x24 (by decide)]; rfl,
     by rw [hpres145 .x26 (by decide) (by decide) (by decide) (by decide)]; exact inv140.rx26,
     rfl, hro145, hw145, ht145, hcap145⟩
  have htail := (((h140'.trans h141').trans h142').trans h143').trans h144'
  have hbody := (((((hrsalt.trans hrl0).trans hrl1).trans hr256).trans hr240).trans hr238).trans htail
  by_cases hmore : t + 1 < positions.card
  · have h145 := step_BNE_taken (by omega) (rfl : s145.pc = pcAt 145)
      (rfl : openingInstr 145 = .base (.BNE .x27 .x0 (7740#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) ≠ BitVec.ofNat 64 0
          exact bv64_ofNat_ne (by omega) (by decide) (by omega))
      (by decide : pcAt 145 + signExtend13 (7740#13) = pcAt 32)
    exact ⟨32 + st0 + st1 + st256 + st240 + st238 + 5 + 1,
      32 + cy0 + cy1 + st256 + st240 + st238 + 5 + 1,
      s145.setPC (pcAt 32), hbody.trans h145, by omega, by omega, by rw [if_pos hmore]; rfl,
      hlen_recF, hlen_recT, hinv145.setPC (pcAt 32)⟩
  · have hdone : positions.card - (t + 1) = 0 := by omega
    have h145 := step_BNE_not_taken (by omega) (rfl : s145.pc = pcAt 145)
      (rfl : openingInstr 145 = .base (.BNE .x27 .x0 (7740#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) = BitVec.ofNat 64 0; rw [hdone])
    exact ⟨32 + st0 + st1 + st256 + st240 + st238 + 5 + 1,
      32 + cy0 + cy1 + st256 + st240 + st238 + 5 + 1,
      s145.setPC (pcAt 146), hbody.trans h145, by omega, by omega, by rw [if_neg hmore]; rfl,
      hlen_recF, hlen_recT, hinv145.setPC (pcAt 146)⟩

private theorem openRuns_rec_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s32 : MachineState}
    (hne : 0 < positions.card) (hpc : s32.pc = pcAt 32)
    (inv0 : RecInv trapdoor positions 0 [] [] s32) :
    let recFwd := (positions.sort (· ≤ ·)).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
    let recTails := (positions.sort (· ≤ ·)).flatMap (recordTails (tdNode trapdoor))
    ∃ steps cycles s146, OpenRuns s32 steps cycles s146 ∧
      steps ≤ 776 * positions.card ∧
      cycles ≤ 788 * positions.card ∧
      s146.pc = pcAt 146 ∧
      s146.getReg .x2 = BitVec.ofNat 64 68719475968 ∧
      s146.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s146.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s146.getReg .x26 = BitVec.ofNat 64 11162446080 ∧
      recFwd.length ≤ 513 * positions.card ∧
      recTails.length ≤ 5 * positions.card ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s146 ∧
      WriterState s146 recFwd ∧
      TailState s146 recTails ∧
      CapLevelMarks s146 positions 14 := by
  intro recFwd recTails
  have hloop : ∀ t ≤ positions.card,
      let curF := ((positions.sort (· ≤ ·)).take t).flatMap
        (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
      let curT := ((positions.sort (· ≤ ·)).take t).flatMap
        (recordTails (tdNode trapdoor))
      ∃ steps cycles st, OpenRuns s32 steps cycles st ∧
        steps ≤ 776 * t ∧ cycles ≤ 788 * t ∧
        st.pc = (if t < positions.card then pcAt 32 else pcAt 146) ∧
        curF.length ≤ 513 * t ∧
        curT.length ≤ 5 * t ∧
        RecInv trapdoor positions t curF curT st := by
    intro t ht
    induction t with
    | zero =>
      dsimp only
      simp only [List.take_zero, List.flatMap_nil, Nat.mul_zero]
      exact ⟨0, 0, s32, OpenRuns.refl s32, Nat.le_refl 0, Nat.le_refl 0,
        by rw [if_pos hne]; exact hpc, Nat.le_refl 0, Nat.le_refl 0, inv0⟩
    | succ t ih =>
      obtain ⟨st, cy, stState, hr, hst, hcy, hpct, hbdt, htbdt, invt⟩ := ih (by omega)
      have hpct' : stState.pc = pcAt 32 := by simpa only [show t < positions.card by omega, ite_true] using hpct
      obtain ⟨st1, cy1, stNext, hr1, hst1, hcy1, hpc1, hbd1, htbd1, inv1⟩ :=
        openRuns_rec_iter (by omega) hpct' hbdt htbdt invt
      have hlen : t < (positions.sort (· ≤ ·)).length := by simpa using (by omega : t < positions.card)
      have htakeF : ((positions.sort (· ≤ ·)).take (t + 1)).flatMap
            (recordFwd (tdNode trapdoor) (tdSalt trapdoor)) =
          ((positions.sort (· ≤ ·)).take t).flatMap
            (recordFwd (tdNode trapdoor) (tdSalt trapdoor)) ++
          recordFwd (tdNode trapdoor) (tdSalt trapdoor) ((positions.sort (· ≤ ·))[t]'hlen) := by
        rw [List.take_succ_eq_append_getElem hlen, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have htakeT : ((positions.sort (· ≤ ·)).take (t + 1)).flatMap
            (recordTails (tdNode trapdoor)) =
          ((positions.sort (· ≤ ·)).take t).flatMap
            (recordTails (tdNode trapdoor)) ++
          recordTails (tdNode trapdoor) ((positions.sort (· ≤ ·))[t]'hlen) := by
        rw [List.take_succ_eq_append_getElem hlen, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [← htakeF] at hbd1 inv1
      rw [← htakeT] at htbd1 inv1
      exact ⟨st + st1, cy + cy1, stNext, hr.trans hr1, by omega, by omega, hpc1, hbd1, htbd1, inv1⟩
  obtain ⟨steps, cycles, s146, hr, hst, hcy, hpc146, hbdEnd, htbdEnd, invEnd⟩ :=
    hloop positions.card (Nat.le_refl _)
  have hpc146' : s146.pc = pcAt 146 := by simpa only [Nat.lt_irrefl, ite_false] using hpc146
  have htakeAll : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) := by
    have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
    rw [← hlen, List.take_length]
  rw [htakeAll] at hbdEnd htbdEnd invEnd
  refine ⟨steps, cycles, s146, hr, hst, hcy, hpc146',
    invEnd.rx2, invEnd.rx9, invEnd.rx21, invEnd.rx26,
    hbdEnd, htbdEnd, invEnd.ro, invEnd.writer, invEnd.tail, ?_⟩
  intro idx hidx
  have hidx456 : idx < 456 := by rw [levelSize_14] at hidx; exact hidx
  have hmo14 : capMarkOff 14 = 0 := by decide
  rw [hmo14, Nat.add_zero, invEnd.cap14 idx hidx456, capMark14Prefix_card]

/-! ### 8. Cap Frontier Pass (`146..182`) -/

private def capPairFwd (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (l q : Nat) : List Byte :=
  let mL := capMark positions l (2 * q)
  let mR := capMark positions l (2 * q + 1)
  if mL = mR then []
  else if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) 29
  else bitsToBytes (tdNode trapdoor l (2 * q + 1)) 29

private def capPairTails (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (l q : Nat) : List (BitVec 6) :=
  let mL := capMark positions l (2 * q)
  let mR := capMark positions l (2 * q + 1)
  if mL = mR then []
  else if !mL then [tail6 (tdNode trapdoor l (2 * q))]
  else [tail6 (tdNode trapdoor l (2 * q + 1))]

private def capPairFrontier (positions : Positions) (l q : Nat) : Nat :=
  if capMark positions l (2 * q) != capMark positions l (2 * q + 1) then 1 else 0

private theorem sum_capPairFrontier_eq (positions : Positions) (l : Nat) :
    (∑ q ∈ Finset.range (levelSize l / 2), capPairFrontier positions l q) =
      levelFrontierCount positions l := by
  unfold levelFrontierCount capPairFrontier
  rw [Finset.card_filter]

private structure CapLvlInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (step : Nat) (fwdBytes : List Byte) (tails : List (BitVec 6))
    (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475968
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx26 : s.getReg .x26 = BitVec.ofNat 64 11162446080
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (14 + step))
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 23)
  boundFwd : fwdBytes.length ≤ 513 * positions.card +
    29 * (∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k))
  boundTails : tails.length ≤ 5 * positions.card +
    (∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k))
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  writer : WriterState s fwdBytes
  tail : TailState s tails
  capMarks : CapLevelMarks s positions (14 + step)

private structure CapPairInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (step q : Nat) (fwdBytes : List Byte) (tails : List (BitVec 6))
    (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475968
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase (14 + step))
  rx19 : s.getReg .x19 = BitVec.ofNat 64 (levelSize (14 + step))
  rx20 : s.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff (14 + step))
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx22 : s.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (14 + step + 1))
  rx23 : s.getReg .x23 = BitVec.ofNat 64 (levelSize (14 + step) / 2)
  rx24 : s.getReg .x24 = BitVec.ofNat 64 q
  rx26 : s.getReg .x26 = BitVec.ofNat 64 11162446080
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * (14 + step))
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 23)
  boundFwd : fwdBytes.length ≤ 513 * positions.card +
    29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
          (∑ j ∈ Finset.range q, capPairFrontier positions (14 + step) j))
  boundTails : tails.length ≤ 5 * positions.card +
    ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
     (∑ j ∈ Finset.range q, capPairFrontier positions (14 + step) j))
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  writer : WriterState s fwdBytes
  tail : TailState s tails
  curMarks : CapLevelMarks s positions (14 + step)
  nextMarks : ∀ j < q, s.getByte (BitVec.ofNat 64 (4096 + capMarkOff (14 + step + 1) + j)) =
    if capMark positions (14 + step + 1) j then 1#8 else 0#8

private theorem openRuns_cap_pair_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {step q : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hstep : step < 9) (hq : q < levelSize (14 + step) / 2) (hpc : s.pc = pcAt 157)
    (inv : CapPairInv trapdoor positions step q fwdBytes tails s) :
    let l := 14 + step
    let fwd1 := fwdBytes ++ capPairFwd trapdoor positions l q
    let tails1 := tails ++ capPairTails trapdoor positions l q
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 10 + 52 * capPairFrontier positions l q ∧
      s1.pc = (if q + 1 < levelSize l / 2 then pcAt 157 else pcAt 174) ∧
      CapPairInv trapdoor positions step (q + 1) fwd1 tails1 s1 := by
  intro l fwd1 tails1
  have hql : q < levelSize l / 2 := hq
  have hcur_inv : CapLevelMarks s positions l := inv.curMarks
  have hinv_bdF : fwdBytes.length ≤ 513 * positions.card +
      29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
            (∑ j ∈ Finset.range q, capPairFrontier positions l j)) := inv.boundFwd
  have hinv_bdT : tails.length ≤ 5 * positions.card +
      ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
       (∑ j ∈ Finset.range q, capPairFrontier positions l j)) := inv.boundTails
  have hcard := positions_card_le positions
  have hls_le := levelSize_le_max l (by omega)
  have hcm_bd := capMarkOff_bound l (by omega) (by omega)
  have hcm1_bd := capMarkOff_bound (l + 1) (by omega) (by omega)
  have hcm_disj := capMarkOff_step_disjoint l (by omega) (by omega)
  have hls1_eq := levelSize_step l (by omega)
  have hq_lt_next : q < levelSize (l + 1) := by omega
  set mL := capMark positions l (2 * q)
  set mR := capMark positions l (2 * q + 1)
  have h122 := step_SLLI (by omega) hpc (rfl : openingInstr 157 = .base (.SLLI .x6 .x24 (1#6)))
  let s123 := (s.setReg .x6 (BitVec.ofNat 64 (2 * q))).setPC (pcAt 158)
  have h122' : OpenRuns s 1 1 s123 := by
    have hv : s.getReg .x24 <<< (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (2 * q) := by
      rw [inv.rx24]; change BitVec.ofNat 64 q <<< 1 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hv, s123] using h122
  have h123 := step_ADD (by omega) (rfl : s123.pc = pcAt 158)
    (rfl : openingInstr 158 = .base (.ADD .x6 .x20 .x6))
  let s124 := (s123.setReg .x6 (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q))).setPC (pcAt 159)
  have h123' : OpenRuns s123 1 1 s124 := by
    have hr20 : s123.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) := inv.rx20
    rw [hr20] at h123
    simpa only [show s123.getReg .x6 = BitVec.ofNat 64 (2 * q) from rfl, bv64_ofNat_add, s124] using h123
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  have haddr124 : s124.getReg .x6 + signExtend12 (0#12) =
      BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) := by
    change BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h124 := step_LBU (by omega) (rfl : s124.pc = pcAt 159)
    (rfl : openingInstr 159 = .base (.LBU .x7 .x6 (0#12)))
    (by rw [haddr124]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s125 := (s124.setReg .x7 (if mL then 1#64 else 0#64)).setPC (pcAt 160)
  have h124' : OpenRuns s124 1 1 s125 := by
    have hb : s124.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q)) =
        if mL then 1#8 else 0#8 := hcur_inv (2 * q) (by omega)
    simpa only [haddr124, hb, bool_byte_zeroExtend mL, s125] using h124
  have haddr125 : s125.getReg .x6 + signExtend12 (1#12) =
      BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1)) := by
    change BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) + _ = _
    rw [hse1, bv64_ofNat_add, Nat.add_assoc]
  have h125 := step_LBU (by omega) (rfl : s125.pc = pcAt 160)
    (rfl : openingInstr 160 = .base (.LBU .x8 .x6 (1#12)))
    (by rw [haddr125]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s126 := (s125.setReg .x8 (if mR then 1#64 else 0#64)).setPC (pcAt 161)
  have h125' : OpenRuns s125 1 1 s126 := by
    have hb : s125.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1))) =
        if mR then 1#8 else 0#8 := hcur_inv (2 * q + 1) (by omega)
    simpa only [haddr125, hb, bool_byte_zeroExtend mR, s126] using h125
  have h126 := step_OR (by omega) (rfl : s126.pc = pcAt 161)
    (rfl : openingInstr 161 = .base (.OR .x11 .x7 .x8))
  let s127 := (s126.setReg .x11 (if (mL || mR) then 1#64 else 0#64)).setPC (pcAt 162)
  have h126' : OpenRuns s126 1 1 s127 := by
    simpa only [show s126.getReg .x7 = if mL then 1#64 else 0#64 from rfl,
      show s126.getReg .x8 = if mR then 1#64 else 0#64 from rfl,
      bool_word_or mL mR, s127] using h126
  have h127 := step_ADD (by omega) (rfl : s127.pc = pcAt 162)
    (rfl : openingInstr 162 = .base (.ADD .x6 .x22 .x24))
  let s128 := (s127.setReg .x6 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q))).setPC (pcAt 163)
  have h127' : OpenRuns s127 1 1 s128 := by
    have hr22 : s127.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) := inv.rx22
    have hr24 : s127.getReg .x24 = BitVec.ofNat 64 q := inv.rx24
    rw [hr22, hr24, bv64_ofNat_add] at h127; exact h127
  have haddr128 : s128.getReg .x6 + signExtend12 (0#12) =
      BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) := by
    change BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h128 := step_SB (by omega) (rfl : s128.pc = pcAt 163)
    (rfl : openingInstr 163 = .base (.SB .x6 .x11 (0#12)))
    (by rw [haddr128]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s129 := (s128.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q))
    (if (mL || mR) then 1#8 else 0#8)).setPC (pcAt 164)
  have h128' : OpenRuns s128 1 1 s129 := by
    simpa only [haddr128, show s128.getReg .x11 = if (mL || mR) then 1#64 else 0#64 from rfl,
      bool_word_truncate8 (mL || mR), s129] using h128
  have hpre : OpenRuns s 7 7 s129 :=
    (((((h122'.trans h123').trans h124').trans h125').trans h126').trans h127').trans h128'
  have hpres129 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x11 →
      s129.getReg r = s.getReg r := fun r h6 h7 h8 h11 => by
    simp only [s129, s128, s127, s126, s125, s124, s123,
      MachineState.getReg_setPC, getReg_setByte,
      getReg_setReg_ne' .x6 r (Ne.symm h6),
      getReg_setReg_ne' .x11 r (Ne.symm h11),
      getReg_setReg_ne' .x8 r (Ne.symm h8),
      getReg_setReg_ne' .x7 r (Ne.symm h7)]
  have hx7_129 : s129.getReg .x7 = if mL then 1#64 else 0#64 := by
    simp only [s129, MachineState.getReg_setPC, getReg_setByte]; rfl
  have hx8_129 : s129.getReg .x8 = if mR then 1#64 else 0#64 := by
    simp only [s129, MachineState.getReg_setPC, getReg_setByte]; rfl
  -- Bounds at s129
  have hfront_sum_le : (∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
      (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j) ≤ capFrontierCount positions := by
    have hq_le : (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j) ≤
        levelFrontierCount positions l := by
      rw [← sum_capPairFrontier_eq]
      exact sum_range_le_of_le (capPairFrontier positions l) (by omega)
    have hs_eq : (∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
        levelFrontierCount positions l =
        ∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (14 + k) := by
      rw [Finset.sum_range_succ]
    have hs_le : (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (14 + k)) ≤
        capFrontierCount positions := by
      unfold capFrontierCount
      exact sum_range_le_of_le (fun k => levelFrontierCount positions (14 + k)) (by omega)
    omega
  have hcap228 := cap_frontier_le_228 positions
  have hfwd_cap : fwdBytes.length ≤ 513 * 16777216 + 29 * 228 := by
    have h2 : (∑ j ∈ Finset.range q, capPairFrontier positions l j) ≤
        ∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j :=
      sum_range_le_of_le (capPairFrontier positions l) (by omega)
    omega
  have htails_cap : tails.length ≤ 5 * 16777216 + 228 := by
    have h2 : (∑ j ∈ Finset.range q, capPairFrontier positions l j) ≤
        ∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j :=
      sum_range_le_of_le (capPairFrontier positions l) (by omega)
    omega
  have hro129 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s129 := by
    intro a ha
    simp only [s129, MachineState.getMem_setPC]
    exact readOnly_setByte_cap (4096 + capMarkOff (l + 1) + q) _ inv.ro (by omega) (by omega) a ha
  have hw129 : WriterState s129 fwdBytes := by
    have hw' := writerState_setByte_outside (4096 + capMarkOff (l + 1) + q)
      (if (mL || mR) then 1#8 else 0#8) inv.writer (by omega) (Or.inl (by omega)) (by omega)
    exact ⟨by rw [hpres129 .x25 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx25,
      by rw [hpres129 .x13 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx13,
      by rw [hpres129 .x14 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx14,
      fun j hj => by rw [hpres129 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.wbufLo j hj,
      fun j h1 h2 => by rw [hpres129 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.wbufHi j h1 h2,
      fun j hj => by simp only [s129, getByte_setPC]; exact hw'.memDwords j hj⟩
  have ht129 : TailState s129 tails := by
    have htb : tailBufBase = 20000000000 := rfl
    have ht' := tailState_setByte_outside (4096 + capMarkOff (l + 1) + q)
      (if (mL || mR) then 1#8 else 0#8) inv.tail (by omega) (by omega)
    exact ⟨by rw [hpres129 .x31 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx31,
      by rw [hpres129 .x15 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx15,
      by rw [hpres129 .x16 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx16,
      by rw [hpres129 .x17 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx17,
      fun j hj => by simp only [s129, getByte_setPC]; exact ht'.memTail j hj⟩
  have hcur129 : CapLevelMarks s129 positions l := by
    intro idx hidx
    simp only [s129, getByte_setPC, set_byte_read]
    rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
    exact hcur_inv idx hidx
  have hnext129 : ∀ j < q + 1, s129.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + j)) =
      if capMark positions (l + 1) j then 1#8 else 0#8 := by
    intro j hj
    simp only [s129, getByte_setPC, set_byte_read]
    by_cases hjq : j = q
    · subst j
      have hlt : 2 * q + 1 < levelSize l := by omega
      rw [if_pos rfl]
      change (if (capMark positions l (2 * q) || capMark positions l (2 * q + 1)) then 1#8 else 0#8) = _
      rw [capMark_succ positions l q (by omega), if_pos hlt]
    · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
      exact inv.nextMarks j (by omega)
  -- Branch on mL = mR to reach pcAt 172
  have hto137 : ∃ n137 s137, OpenRuns s129 n137 n137 s137 ∧
      n137 ≤ 1 + 52 * capPairFrontier positions l q ∧
      s137.pc = pcAt 172 ∧
      s137.getReg .x2 = BitVec.ofNat 64 68719475968 ∧
      s137.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s137.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l) ∧
      s137.getReg .x19 = BitVec.ofNat 64 (levelSize l) ∧
      s137.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
      s137.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s137.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
      s137.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) ∧
      s137.getReg .x24 = BitVec.ofNat 64 q ∧
      s137.getReg .x26 = BitVec.ofNat 64 11162446080 ∧
      s137.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) ∧
      s137.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 23) ∧
      fwd1.length ≤ 513 * positions.card +
        29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
              (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) ∧
      tails1.length ≤ 5 * positions.card +
        ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
         (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s137 ∧
      WriterState s137 fwd1 ∧
      TailState s137 tails1 ∧
      CapLevelMarks s137 positions l ∧
      (∀ j < q + 1, s137.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + j)) =
        if capMark positions (l + 1) j then 1#8 else 0#8) := by
    by_cases hsame : mL = mR
    · have h129 := step_BEQ_taken (by omega) (rfl : s129.pc = pcAt 164)
        (rfl : openingInstr 164 = .base (.BEQ .x7 .x8 (32#13)))
        (by rw [hx7_129, hx8_129, hsame])
        (by decide : pcAt 164 + signExtend13 (32#13) = pcAt 172)
      have hf1 : fwd1 = fwdBytes := by
        change fwdBytes ++ (if mL = mR then [] else _) = _
        rw [if_pos hsame, List.append_nil]
      have ht1 : tails1 = tails := by
        change tails ++ (if mL = mR then [] else _) = _
        rw [if_pos hsame, List.append_nil]
      rw [hf1, ht1]
      have hlenF : fwdBytes.length ≤ 513 * positions.card +
          29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
                (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ]; omega
      have hlenT : tails.length ≤ 5 * positions.card +
          ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
           (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ]; omega
      exact ⟨1, s129.setPC (pcAt 172), h129, by omega, rfl,
        by rw [MachineState.getReg_setPC, hpres129 .x2 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx2,
        by rw [MachineState.getReg_setPC, hpres129 .x9 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx9,
        by rw [MachineState.getReg_setPC, hpres129 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx18,
        by rw [MachineState.getReg_setPC, hpres129 .x19 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx19,
        by rw [MachineState.getReg_setPC, hpres129 .x20 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx20,
        by rw [MachineState.getReg_setPC, hpres129 .x21 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx21,
        by rw [MachineState.getReg_setPC, hpres129 .x22 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx22,
        by rw [MachineState.getReg_setPC, hpres129 .x23 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx23,
        by rw [MachineState.getReg_setPC, hpres129 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24,
        by rw [MachineState.getReg_setPC, hpres129 .x26 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx26,
        by rw [MachineState.getReg_setPC, hpres129 .x29 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx29,
        by rw [MachineState.getReg_setPC, hpres129 .x30 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx30,
        hlenF, hlenT, hro129, hw129.of_eq, ht129.of_eq, hcur129, hnext129⟩
    · have hcpf : capPairFrontier positions l q = 1 := by
        change (if (mL != mR) = true then 1 else 0) = 1
        exact bool_bne_one_of_ne hsame
      have h129 := step_BEQ_not_taken (by omega) (rfl : s129.pc = pcAt 164)
        (rfl : openingInstr 164 = .base (.BEQ .x7 .x8 (32#13)))
        (by rw [hx7_129, hx8_129]; exact bool_word_ne_of_ne hsame)
      let s130 := s129.setPC (pcAt 165)
      have h130 := step_SLLI (by omega) (rfl : s130.pc = pcAt 165)
        (rfl : openingInstr 165 = .base (.SLLI .x6 .x24 (6#6)))
      let s131 := (s130.setReg .x6 (BitVec.ofNat 64 (64 * q))).setPC (pcAt 166)
      have h130' : OpenRuns s130 1 1 s131 := by
        have hr24 : s130.getReg .x24 = BitVec.ofNat 64 q := by
          rw [show s130.getReg .x24 = s129.getReg .x24 from rfl,
            hpres129 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24
        have hv : s130.getReg .x24 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * q) := by
          rw [hr24]; change BitVec.ofNat 64 q <<< 6 = _; rw [bv64_shl]; congr 1; omega
        simpa only [hv, s131] using h130
      have h131 := step_SLLI (by omega) (rfl : s131.pc = pcAt 166)
        (rfl : openingInstr 166 = .base (.SLLI .x11 .x24 (5#6)))
      let s132 := (s131.setReg .x11 (BitVec.ofNat 64 (32 * q))).setPC (pcAt 167)
      have h131' : OpenRuns s131 1 1 s132 := by
        have hr24 : s131.getReg .x24 = BitVec.ofNat 64 q := by
          simp only [s131, s130, MachineState.getReg_setPC,
            getReg_setReg_ne' .x6 .x24 (by decide)]
          rw [hpres129 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24
        have hv : s131.getReg .x24 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (32 * q) := by
          rw [hr24]; change BitVec.ofNat 64 q <<< 5 = _; rw [bv64_shl]; congr 1; omega
        simpa only [hv, s132] using h131
      have h132 := step_ADD (by omega) (rfl : s132.pc = pcAt 167)
        (rfl : openingInstr 167 = .base (.ADD .x10 .x6 .x11))
      let s133 := (s132.setReg .x10 (BitVec.ofNat 64 (96 * q))).setPC (pcAt 168)
      have h132' : OpenRuns s132 1 1 s133 := by
        have hv : s132.getReg .x6 + s132.getReg .x11 = BitVec.ofNat 64 (96 * q) := by
          change BitVec.ofNat 64 (64 * q) + BitVec.ofNat 64 (32 * q) = _
          rw [bv64_ofNat_add]; congr 1; omega
        simpa only [hv, s133] using h132
      have h133 := step_ADD (by omega) (rfl : s133.pc = pcAt 168)
        (rfl : openingInstr 168 = .base (.ADD .x10 .x18 .x10))
      let s134 := (s133.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q))).setPC (pcAt 169)
      have h133' : OpenRuns s133 1 1 s134 := by
        have hr18 : s133.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l) := by
          simp only [s133, s132, s131, s130, MachineState.getReg_setPC,
            getReg_setReg_ne' .x10 .x18 (by decide),
            getReg_setReg_ne' .x11 .x18 (by decide),
            getReg_setReg_ne' .x6 .x18 (by decide)]
          rw [hpres129 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx18
        rw [hr18] at h133
        simpa only [show s133.getReg .x10 = BitVec.ofNat 64 (96 * q) from rfl, bv64_ofNat_add, s134] using h133
      have hmid : OpenRuns s129 5 5 s134 := (((h129.trans h130').trans h131').trans h132').trans h133'
      have hlen_bdF : fwdBytes.length + 29 ≤ 513 * positions.card +
          29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
                (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ, hcpf]; omega
      have hlen_bdT : tails.length + 1 ≤ 5 * positions.card +
          ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
           (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ, hcpf]; omega
      have hr7_134 : s134.getReg .x7 = if mL then 1#64 else 0#64 := by
        simp only [s134, s133, s132, s131, s130, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 .x7 (by decide),
          getReg_setReg_ne' .x11 .x7 (by decide),
          getReg_setReg_ne' .x6 .x7 (by decide)]
        exact hx7_129
      have hpres134 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x11 →
          s134.getReg r = s129.getReg r := fun r h6 h7 _ h10 h11 => by
        simp only [s134, s133, s132, s131, s130, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 r (Ne.symm h10),
          getReg_setReg_ne' .x11 r (Ne.symm h11),
          getReg_setReg_ne' .x6 r (Ne.symm h6)]
      -- Split on mL = true vs mL = false to reach pcAt 171
      have hto136 : ∃ n136 s136 childIdx, OpenRuns s134 n136 n136 s136 ∧ n136 ≤ 2 ∧
          childIdx = (if !mL then 2 * q else 2 * q + 1) ∧
          childIdx < levelSize l ∧
          s136.pc = pcAt 171 ∧
          s136.getReg .x10 = BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l childIdx)) ∧
          (∀ r, r ≠ .x10 → s136.getReg r = s134.getReg r) ∧
          s136.mem = s134.mem := by
        by_cases hmL : mL = true
        · have h134 := step_BEQ_not_taken (by omega) (rfl : s134.pc = pcAt 169)
            (rfl : openingInstr 169 = .base (.BEQ .x7 .x0 (8#13)))
            (by rw [hr7_134, hmL]; change (1#64 : Word) ≠ 0#64; decide)
          let s135 := s134.setPC (pcAt 170)
          have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
          have h135 := step_ADDI (by omega) (rfl : s135.pc = pcAt 170)
            (rfl : openingInstr 170 = .base (.ADDI .x10 .x10 (32#12)))
          have hno : levelBase l + nodeOffset l (2 * q + 1) = levelBase l + 96 * q + 32 := by
            have hl2 : ¬ (l < 2) := by omega
            unfold nodeOffset; rw [if_neg hl2, gapOffset_odd]; omega
          let s136 := (s135.setReg .x10
            (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l (2 * q + 1))))).setPC (pcAt 171)
          have h135' : OpenRuns s135 1 1 s136 := by
            have hv : s135.getReg .x10 + signExtend12 (32#12) =
                BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l (2 * q + 1))) := by
              change BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) + _ = _
              rw [hse32, bv64_ofNat_add]; congr 1; omega
            simpa only [hv, s136] using h135
          refine ⟨2, s136, 2 * q + 1, h134.trans h135', by omega, by rw [hmL]; rfl, by omega, rfl, rfl,
            fun r hr => by simp only [s136, s135, MachineState.getReg_setPC,
              getReg_setReg_ne' .x10 r (Ne.symm hr)], rfl⟩
        · have hmLf : mL = false := Bool.eq_false_iff.mpr hmL
          have h134 := step_BEQ_taken (by omega) (rfl : s134.pc = pcAt 169)
            (rfl : openingInstr 169 = .base (.BEQ .x7 .x0 (8#13)))
            (by rw [hr7_134, hmLf]; rfl)
            (by decide : pcAt 169 + signExtend13 (8#13) = pcAt 171)
          have hno : levelBase l + nodeOffset l (2 * q) = levelBase l + 96 * q := by
            have hl2 : ¬ (l < 2) := by omega
            unfold nodeOffset; rw [if_neg hl2, gapOffset_even]
          refine ⟨1, s134.setPC (pcAt 171), 2 * q, h134, by omega, by rw [hmLf]; rfl, by omega, rfl,
            ?_, fun _ _ => rfl, rfl⟩
          change BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) = _
          rw [hno, Nat.add_assoc]
      obtain ⟨n136, s136, childIdx, hr136, hn136, hchildEq, hchildLt, hpc136, hx10_136, hreg136, hmem136⟩ := hto136
      have hro136 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s136 := by
        intro a ha; change s136.mem a = _; rw [hmem136]; exact hro129 a ha
      have hw136 : WriterState s136 fwdBytes :=
        ⟨by rw [hreg136 .x25 (by decide), hpres134 .x25 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw129.rx25,
         by rw [hreg136 .x13 (by decide), hpres134 .x13 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw129.rx13,
         by rw [hreg136 .x14 (by decide), hpres134 .x14 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw129.rx14,
         fun j hj => by rw [hreg136 .x12 (by decide), hpres134 .x12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw129.wbufLo j hj,
         fun j h1 h2 => by rw [hreg136 .x12 (by decide), hpres134 .x12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw129.wbufHi j h1 h2,
         fun j hj => by change extractByte (s136.mem _) _ = _; rw [hmem136]; exact hw129.memDwords j hj⟩
      have ht136 : TailState s136 tails :=
        ⟨by rw [hreg136 .x31 (by decide), hpres134 .x31 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht129.rx31,
         by rw [hreg136 .x15 (by decide), hpres134 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht129.rx15,
         by rw [hreg136 .x16 (by decide), hpres134 .x16 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht129.rx16,
         by rw [hreg136 .x17 (by decide), hpres134 .x17 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht129.rx17,
         fun j hj => by change extractByte (s136.mem _) _ = _; rw [hmem136]; exact ht129.memTail j hj⟩
      obtain ⟨stC, s137, hrcopy, hstC, hpc137, hreg137, hro137, hw137, ht137, hcap137⟩ :=
        openRuns_call_copy29_tail (callIdx := 171) (l := l) (nodeIdx := childIdx) (jOff := 464#21)
          (fwdBytes := fwdBytes) (tails := tails) (by omega) (by omega) hchildLt
          rfl (by decide) hpc136 hx10_136 (by omega) (by omega) hro136 hw136 ht136
      have hf1 : fwd1 = fwdBytes ++ bitsToBytes (tdNode trapdoor l childIdx) 29 := by
        change fwdBytes ++ (if mL = mR then []
          else if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) 29
          else bitsToBytes (tdNode trapdoor l (2 * q + 1)) 29) = _
        rw [if_neg hsame, hchildEq]
        by_cases hnot : (!mL) = true
        · rw [if_pos hnot, if_pos hnot]
        · rw [if_neg hnot, if_neg hnot]
      have ht1 : tails1 = tails ++ [tail6 (tdNode trapdoor l childIdx)] := by
        change tails ++ (if mL = mR then []
          else if !mL then [tail6 (tdNode trapdoor l (2 * q))]
          else [tail6 (tdNode trapdoor l (2 * q + 1))]) = _
        rw [if_neg hsame, hchildEq]
        by_cases hnot : (!mL) = true
        · rw [if_pos hnot, if_pos hnot]
        · rw [if_neg hnot, if_neg hnot]
      rw [hf1, ht1]
      have hpres137 : ∀ r, r = .x2 ∨ r = .x9 ∨ r = .x18 ∨ r = .x19 ∨ r = .x20 ∨ r = .x21 ∨
          r = .x22 ∨ r = .x23 ∨ r = .x24 ∨ r = .x26 ∨ r = .x29 ∨ r = .x30 →
          s137.getReg r = s.getReg r := fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (
          rw [hreg137 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg136 _ (by decide),
            hpres134 _ (by decide) (by decide) (by decide) (by decide) (by decide),
            hpres129 _ (by decide) (by decide) (by decide) (by decide)])
      refine ⟨5 + n136 + stC, s137, (hmid.trans hr136).trans hrcopy, by rw [hcpf]; omega, hpc137,
        by rw [hpres137 .x2 (by simp)]; exact inv.rx2,
        by rw [hpres137 .x9 (by simp)]; exact inv.rx9,
        by rw [hpres137 .x18 (by simp)]; exact inv.rx18,
        by rw [hpres137 .x19 (by simp)]; exact inv.rx19,
        by rw [hpres137 .x20 (by simp)]; exact inv.rx20,
        by rw [hpres137 .x21 (by simp)]; exact inv.rx21,
        by rw [hpres137 .x22 (by simp)]; exact inv.rx22,
        by rw [hpres137 .x23 (by simp)]; exact inv.rx23,
        by rw [hpres137 .x24 (by simp)]; exact inv.rx24,
        by rw [hpres137 .x26 (by simp)]; exact inv.rx26,
        by rw [hpres137 .x29 (by simp)]; exact inv.rx29,
        by rw [hpres137 .x30 (by simp)]; exact inv.rx30,
        by simp only [List.length_append, bitsToBytes_length]; exact hlen_bdF,
        by simp only [List.length_append, List.length_singleton]; exact hlen_bdT,
        hro137, hw137, ht137, ?_, ?_⟩
      · intro idx hidx
        rw [hcap137 (4096 + capMarkOff l + idx) (by omega)]
        change extractByte (s136.mem _) _ = _; rw [hmem136]; exact hcur129 idx hidx
      · intro j hj
        rw [hcap137 (4096 + capMarkOff (l + 1) + j) (by omega)]
        change extractByte (s136.mem _) _ = _; rw [hmem136]; exact hnext129 j hj
  obtain ⟨n137, s137, hr137, hn137, hpc137, hx2, hx9, hx18, hx19, hx20, hx21, hx22, hx23,
      hx24, hx26, hx29, hx30, hlenF1, hlenT1, hro137, hw137, ht137, hcur137, hnext137⟩ := hto137
  have h137 := step_ADDI (by omega) hpc137 (rfl : openingInstr 172 = .base (.ADDI .x24 .x24 (1#12)))
  let s138 := (s137.setReg .x24 (BitVec.ofNat 64 (q + 1))).setPC (pcAt 173)
  have h137' : OpenRuns s137 1 1 s138 := by
    rw [hx24, hse1, bv64_ofNat_add] at h137; exact h137
  have hmkInv : ∀ pc, CapPairInv trapdoor positions step (q + 1) fwd1 tails1 (s138.setPC pc) := fun pc =>
    ⟨hx2, hx9, hx18, hx19, hx20, hx21, hx22, hx23, rfl, hx26, hx29, hx30,
     hlenF1, hlenT1, hro137, hw137.of_eq, ht137.of_eq, hcur137, hnext137⟩
  by_cases hmore : q + 1 < levelSize l / 2
  · have h138 := step_BNE_taken (by omega) (rfl : s138.pc = pcAt 173)
      (rfl : openingInstr 173 = .base (.BNE .x24 .x23 (8128#13)))
      (by change BitVec.ofNat 64 (q + 1) ≠ s137.getReg .x23
          rw [hx23]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 173 + signExtend13 (8128#13) = pcAt 157)
    exact ⟨7 + n137 + 1 + 1, s138.setPC (pcAt 157), ((hpre.trans hr137).trans h137').trans h138,
      by omega, by rw [if_pos hmore]; rfl, hmkInv (pcAt 157)⟩
  · have hdone : q + 1 = levelSize l / 2 := by omega
    have h138 := step_BNE_not_taken (by omega) (rfl : s138.pc = pcAt 173)
      (rfl : openingInstr 173 = .base (.BNE .x24 .x23 (8128#13)))
      (by change BitVec.ofNat 64 (q + 1) = s137.getReg .x23; rw [hx23, hdone])
    exact ⟨7 + n137 + 1 + 1, s138.setPC (pcAt 174), ((hpre.trans hr137).trans h137').trans h138,
      by omega, by rw [if_neg hmore]; rfl, hmkInv (pcAt 174)⟩

private theorem openRuns_cap_lvl_iter {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {step : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hstep : step < 9) (hpc : s.pc = pcAt 148)
    (inv : CapLvlInv trapdoor positions step fwdBytes tails s) :
    let l := 14 + step
    let fwd1 := fwdBytes ++ capLevelFrontierFwd (tdNode trapdoor) positions l
    let tails1 := tails ++ capLevelFrontierTails (tdNode trapdoor) positions l
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 9 + 10 * (levelSize l / 2) + 52 * levelFrontierCount positions l +
        (if levelSize l % 2 = 0 then 4 else 9) ∧
      s1.pc = (if step + 1 < 9 then pcAt 148 else pcAt 183) ∧
      CapLvlInv trapdoor positions (step + 1) fwd1 tails1 s1 := by
  intro l fwd1 tails1
  have hls_ge2 := levelSize_ge_two l (by omega)
  have hls_le := levelSize_le_max l (by omega)
  have hls1_eq := levelSize_step l (by omega)
  have hcm_bd := capMarkOff_bound l (by omega) (by omega)
  have hcm1_bd := capMarkOff_bound (l + 1) (by omega) (by omega)
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have hse16 : signExtend12 (16#12) = BitVec.ofNat 64 16 := by decide
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have hse48 : signExtend12 (48#12) = BitVec.ofNat 64 48 := by decide
  -- Header: 113..121 (9 steps)
  have haddr113 : s.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475968 + 32 * l) := by
    rw [inv.rx29, hse0, bv64_ofNat_add, Nat.add_zero]
  have h113 := step_LD (by omega) hpc (rfl : openingInstr 148 = .base (.LD .x18 .x29 (0#12)))
    (by rw [haddr113]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s114 := (s.setReg .x18 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 149)
  have h113' : OpenRuns s 1 1 s114 := by
    have hm := readOnly_getMem_data_base inv.ro l (by omega)
    simpa only [haddr113, hm, s114] using h113
  have h114 := step_ADD (by omega) (rfl : s114.pc = pcAt 149)
    (rfl : openingInstr 149 = .base (.ADD .x18 .x9 .x18))
  let s115 := (s114.setReg .x18 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 150)
  have h114' : OpenRuns s114 1 1 s115 := by
    have hr9 : s114.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
    rw [hr9] at h114
    simpa only [show s114.getReg .x18 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s115] using h114
  have haddr115 : s115.getReg .x29 + signExtend12 (8#12) = BitVec.ofNat 64 (68719475968 + 32 * l + 8) := by
    have hr29 : s115.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := inv.rx29
    rw [hr29, hse8, bv64_ofNat_add]
  have h115 := step_LD (by omega) (rfl : s115.pc = pcAt 150)
    (rfl : openingInstr 150 = .base (.LD .x19 .x29 (8#12)))
    (by rw [haddr115]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s116 := (s115.setReg .x19 (BitVec.ofNat 64 (levelSize l))).setPC (pcAt 151)
  have h115' : OpenRuns s115 1 1 s116 := by
    have hm : s115.getMem (BitVec.ofNat 64 (68719475968 + 32 * l + 8)) = BitVec.ofNat 64 (levelSize l) :=
      readOnly_getMem_data_size inv.ro l (by omega)
    simpa only [haddr115, hm, s116] using h115
  have haddr116 : s116.getReg .x29 + signExtend12 (16#12) = BitVec.ofNat 64 (68719475968 + 32 * l + 16) := by
    have hr29 : s116.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := inv.rx29
    rw [hr29, hse16, bv64_ofNat_add]
  have h116 := step_LD (by omega) (rfl : s116.pc = pcAt 151)
    (rfl : openingInstr 151 = .base (.LD .x20 .x29 (16#12)))
    (by rw [haddr116]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s117 := (s116.setReg .x20 (BitVec.ofNat 64 (capMarkOff l))).setPC (pcAt 152)
  have h116' : OpenRuns s116 1 1 s117 := by
    have hm : s116.getMem (BitVec.ofNat 64 (68719475968 + 32 * l + 16)) = BitVec.ofNat 64 (capMarkOff l) :=
      readOnly_getMem_data_markOff inv.ro l (by omega)
    simpa only [haddr116, hm, s117] using h116
  have h117 := step_ADD (by omega) (rfl : s117.pc = pcAt 152)
    (rfl : openingInstr 152 = .base (.ADD .x20 .x21 .x20))
  let s118 := (s117.setReg .x20 (BitVec.ofNat 64 (4096 + capMarkOff l))).setPC (pcAt 153)
  have h117' : OpenRuns s117 1 1 s118 := by
    have hr21 : s117.getReg .x21 = BitVec.ofNat 64 4096 := inv.rx21
    rw [hr21] at h117
    simpa only [show s117.getReg .x20 = BitVec.ofNat 64 (capMarkOff l) from rfl, bv64_ofNat_add, s118] using h117
  have haddr118 : s118.getReg .x29 + signExtend12 (48#12) =
      BitVec.ofNat 64 (68719475968 + 32 * (l + 1) + 16) := by
    have hr29 : s118.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) := inv.rx29
    rw [hr29, hse48, bv64_ofNat_add]; congr 1
  have h118 := step_LD (by omega) (rfl : s118.pc = pcAt 153)
    (rfl : openingInstr 153 = .base (.LD .x22 .x29 (48#12)))
    (by rw [haddr118]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s119 := (s118.setReg .x22 (BitVec.ofNat 64 (capMarkOff (l + 1)))).setPC (pcAt 154)
  have h118' : OpenRuns s118 1 1 s119 := by
    have hm : s118.getMem (BitVec.ofNat 64 (68719475968 + 32 * (l + 1) + 16)) = BitVec.ofNat 64 (capMarkOff (l + 1)) :=
      readOnly_getMem_data_markOff inv.ro (l + 1) (by omega)
    simpa only [haddr118, hm, s119] using h118
  have h119 := step_ADD (by omega) (rfl : s119.pc = pcAt 154)
    (rfl : openingInstr 154 = .base (.ADD .x22 .x21 .x22))
  let s120 := (s119.setReg .x22 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1)))).setPC (pcAt 155)
  have h119' : OpenRuns s119 1 1 s120 := by
    have hr21 : s119.getReg .x21 = BitVec.ofNat 64 4096 := inv.rx21
    rw [hr21] at h119
    simpa only [show s119.getReg .x22 = BitVec.ofNat 64 (capMarkOff (l + 1)) from rfl,
      bv64_ofNat_add, s120] using h119
  have h120 := step_SRLI (by omega) (rfl : s120.pc = pcAt 155)
    (rfl : openingInstr 155 = .base (.SRLI .x23 .x19 (1#6)))
  let s121 := (s120.setReg .x23 (BitVec.ofNat 64 (levelSize l / 2))).setPC (pcAt 156)
  have h120' : OpenRuns s120 1 1 s121 := by
    have hv : s120.getReg .x19 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (levelSize l / 2) := by
      change BitVec.ofNat 64 (levelSize l) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s121] using h120
  have h121 := step_ADDI (by omega) (rfl : s121.pc = pcAt 156)
    (rfl : openingInstr 156 = .base (.ADDI .x24 .x0 (0#12)))
  let s122 := (s121.setReg .x24 (BitVec.ofNat 64 0)).setPC (pcAt 157)
  have h121' : OpenRuns s121 1 1 s122 := by
    have hv : s121.getReg .x0 + signExtend12 (0#12) = BitVec.ofNat 64 0 := by
      change (0#64 : Word) + signExtend12 (0#12) = BitVec.ofNat 64 0; decide
    simpa only [hv, s122] using h121
  have hhdr : OpenRuns s 9 9 s122 :=
    (((((((h113'.trans h114').trans h115').trans h116').trans h117').trans h118').trans h119').trans h120').trans h121'
  have hpairInv0 : CapPairInv trapdoor positions step 0 fwdBytes tails s122 :=
    ⟨inv.rx2, inv.rx9, rfl, rfl, rfl, inv.rx21, rfl, rfl, rfl, inv.rx26, inv.rx29, inv.rx30,
     by simpa using inv.boundFwd, by simpa using inv.boundTails,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.capMarks, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  -- Pair loop induction: q = 0 .. levelSize l / 2
  have hpairLoop : ∀ q ≤ levelSize l / 2,
      let curF := fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l)
      let curT := tails ++ (List.range q).flatMap (capPairTails trapdoor positions l)
      ∃ steps sq, OpenRuns s122 steps steps sq ∧
        steps ≤ 10 * q + 52 * (∑ j ∈ Finset.range q, capPairFrontier positions l j) ∧
        sq.pc = (if q < levelSize l / 2 then pcAt 157 else pcAt 174) ∧
        CapPairInv trapdoor positions step q curF curT sq := by
    intro q hq
    induction q with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero,
        Finset.sum_range_zero, Nat.add_zero]
      exact ⟨0, s122, OpenRuns.refl s122, Nat.le_refl 0, by rw [if_pos (by omega : 0 < levelSize l / 2)]; rfl, hpairInv0⟩
    | succ q ih =>
      obtain ⟨st, sq, hrq, hstq, hpcq, invq⟩ := ih (by omega)
      have hpcq' : sq.pc = pcAt 157 := by simpa only [show q < levelSize l / 2 by omega, ite_true] using hpcq
      obtain ⟨st1, sq1, hr1, hst1, hpc1, inv1⟩ :=
        openRuns_cap_pair_step hstep (show q < levelSize (14 + step) / 2 from by change q < levelSize l / 2; omega) hpcq' invq
      have hst1' : st1 ≤ 10 + 52 * capPairFrontier positions l q := hst1
      have happF : fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l) ++
            capPairFwd trapdoor positions l q =
          fwdBytes ++ (List.range (q + 1)).flatMap (capPairFwd trapdoor positions l) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      have happT : tails ++ (List.range q).flatMap (capPairTails trapdoor positions l) ++
            capPairTails trapdoor positions l q =
          tails ++ (List.range (q + 1)).flatMap (capPairTails trapdoor positions l) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      have inv1' : CapPairInv trapdoor positions step (q + 1)
          (fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l) ++
            capPairFwd trapdoor positions l q)
          (tails ++ (List.range q).flatMap (capPairTails trapdoor positions l) ++
            capPairTails trapdoor positions l q) sq1 := inv1
      rw [happF, happT] at inv1'
      refine ⟨st + st1, sq1, hrq.trans hr1, ?_, hpc1, inv1'⟩
      rw [Finset.sum_range_succ]; omega
  obtain ⟨stPairs, s139, hrPairs, hstPairs, hpc139, inv139⟩ :=
    hpairLoop (levelSize l / 2) (Nat.le_refl _)
  have hpc139' : s139.pc = pcAt 174 := by simpa only [Nat.lt_irrefl, ite_false] using hpc139
  rw [sum_capPairFrontier_eq] at hstPairs
  have hfwd1_eq : fwdBytes ++ (List.range (levelSize l / 2)).flatMap (capPairFwd trapdoor positions l) =
      fwd1 := rfl
  have htails1_eq : tails ++ (List.range (levelSize l / 2)).flatMap (capPairTails trapdoor positions l) =
      tails1 := rfl
  rw [hfwd1_eq, htails1_eq] at inv139
  have hcur139 : CapLevelMarks s139 positions l := inv139.curMarks
  have hboundF139 : fwd1.length ≤ 513 * positions.card +
      29 * (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (14 + k)) := by
    have h1 : fwd1.length ≤ 513 * positions.card +
        29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
              (∑ j ∈ Finset.range (levelSize (14 + step) / 2), capPairFrontier positions (14 + step) j)) :=
      inv139.boundFwd
    rw [sum_capPairFrontier_eq] at h1
    rw [Finset.sum_range_succ]; exact h1
  have hboundT139 : tails1.length ≤ 5 * positions.card +
      (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (14 + k)) := by
    have h1 : tails1.length ≤ 5 * positions.card +
        ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
         (∑ j ∈ Finset.range (levelSize (14 + step) / 2), capPairFrontier positions (14 + step) j)) :=
      inv139.boundTails
    rw [sum_capPairFrontier_eq] at h1
    rw [Finset.sum_range_succ]; exact h1
  -- Odd-promotion check: 139..145 → pcAt 181
  have h139 := step_ANDI (by omega) hpc139' (rfl : openingInstr 174 = .base (.ANDI .x6 .x19 (1#12)))
  let s140 := (s139.setReg .x6 (BitVec.ofNat 64 (levelSize l % 2))).setPC (pcAt 175)
  have h139' : OpenRuns s139 1 1 s140 := by
    rw [inv139.rx19, bv64_and1 (levelSize l) (by omega)] at h139; exact h139
  have hto146 : ∃ n146 s146, OpenRuns s140 n146 n146 s146 ∧
      n146 ≤ (if levelSize l % 2 = 0 then 1 else 6) ∧
      s146.pc = pcAt 181 ∧
      s146.getReg .x2 = BitVec.ofNat 64 68719475968 ∧
      s146.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s146.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s146.getReg .x26 = BitVec.ofNat 64 11162446080 ∧
      s146.getReg .x29 = BitVec.ofNat 64 (68719475968 + 32 * l) ∧
      s146.getReg .x30 = BitVec.ofNat 64 (68719475968 + 32 * 23) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s146 ∧
      WriterState s146 fwd1 ∧
      TailState s146 tails1 ∧
      CapLevelMarks s146 positions (l + 1) := by
    by_cases heven_sz : levelSize l % 2 = 0
    · have h140 := step_BEQ_taken (by omega) (rfl : s140.pc = pcAt 175)
        (rfl : openingInstr 175 = .base (.BEQ .x6 .x0 (24#13)))
        (by change BitVec.ofNat 64 (levelSize l % 2) = 0#64; rw [heven_sz])
        (by decide : pcAt 175 + signExtend13 (24#13) = pcAt 181)
      refine ⟨1, s140.setPC (pcAt 181), h140, by rw [if_pos heven_sz], rfl,
        inv139.rx2, inv139.rx9, inv139.rx21, inv139.rx26, inv139.rx29, inv139.rx30,
        inv139.ro, inv139.writer.of_eq, inv139.tail.of_eq, ?_⟩
      intro idx hidx
      exact inv139.nextMarks idx (by omega)
    · have h140 := step_BEQ_not_taken (by omega) (rfl : s140.pc = pcAt 175)
        (rfl : openingInstr 175 = .base (.BEQ .x6 .x0 (24#13)))
        (by change BitVec.ofNat 64 (levelSize l % 2) ≠ BitVec.ofNat 64 0
            exact bv64_ofNat_ne (by omega) (by decide) heven_sz)
      let s141 := s140.setPC (pcAt 176)
      have h141 := step_SLLI (by omega) (rfl : s141.pc = pcAt 176)
        (rfl : openingInstr 176 = .base (.SLLI .x7 .x23 (1#6)))
      let s142 := (s141.setReg .x7 (BitVec.ofNat 64 (2 * (levelSize l / 2)))).setPC (pcAt 177)
      have h141' : OpenRuns s141 1 1 s142 := by
        have hr23 : s141.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) := inv139.rx23
        have hv : s141.getReg .x23 <<< (1#6 : BitVec 6).toNat =
            BitVec.ofNat 64 (2 * (levelSize l / 2)) := by
          rw [hr23]; change BitVec.ofNat 64 (levelSize l / 2) <<< 1 = _
          rw [bv64_shl]; congr 1; omega
        simpa only [hv, s142] using h141
      have h142 := step_ADD (by omega) (rfl : s142.pc = pcAt 177)
        (rfl : openingInstr 177 = .base (.ADD .x7 .x20 .x7))
      let s143 := (s142.setReg .x7 (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * (levelSize l / 2)))).setPC
        (pcAt 178)
      have h142' : OpenRuns s142 1 1 s143 := by
        have hr20 : s142.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) := inv139.rx20
        rw [hr20] at h142
        simpa only [show s142.getReg .x7 = BitVec.ofNat 64 (2 * (levelSize l / 2)) from rfl,
          bv64_ofNat_add, s143] using h142
      have haddr143 : s143.getReg .x7 + signExtend12 (0#12) =
          BitVec.ofNat 64 (4096 + capMarkOff l + 2 * (levelSize l / 2)) := by
        change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
      have h143 := step_LBU (by omega) (rfl : s143.pc = pcAt 178)
        (rfl : openingInstr 178 = .base (.LBU .x8 .x7 (0#12)))
        (by rw [haddr143]; exact accessValid_ofNat _ 1 (by omega) (by omega))
      set mProm := capMark positions l (2 * (levelSize l / 2))
      let s144 := (s143.setReg .x8 (if mProm then 1#64 else 0#64)).setPC (pcAt 179)
      have h143' : OpenRuns s143 1 1 s144 := by
        have hb : s143.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * (levelSize l / 2))) =
            if mProm then 1#8 else 0#8 := hcur139 (2 * (levelSize l / 2)) (by omega)
        simpa only [haddr143, hb, bool_byte_zeroExtend mProm, s144] using h143
      have h144 := step_ADD (by omega) (rfl : s144.pc = pcAt 179)
        (rfl : openingInstr 179 = .base (.ADD .x7 .x22 .x23))
      let s145 := (s144.setReg .x7 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + levelSize l / 2))).setPC
        (pcAt 180)
      have h144' : OpenRuns s144 1 1 s145 := by
        have hr22 : s144.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) := inv139.rx22
        have hr23 : s144.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) := inv139.rx23
        rw [hr22, hr23, bv64_ofNat_add] at h144; exact h144
      have haddr145 : s145.getReg .x7 + signExtend12 (0#12) =
          BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + levelSize l / 2) := by
        change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
      have h145 := step_SB (by omega) (rfl : s145.pc = pcAt 180)
        (rfl : openingInstr 180 = .base (.SB .x7 .x8 (0#12)))
        (by rw [haddr145]; exact accessValid_ofNat _ 1 (by omega) (by omega))
      let s146 := (s145.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + levelSize l / 2))
        (if mProm then 1#8 else 0#8)).setPC (pcAt 181)
      have h145' : OpenRuns s145 1 1 s146 := by
        simpa only [haddr145, show s145.getReg .x8 = if mProm then 1#64 else 0#64 from rfl,
          bool_word_truncate8 mProm, s146] using h145
      have hcard := positions_card_le positions
      have hcap228 := cap_frontier_le_228 positions
      have hfront_le : (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (14 + k)) ≤ 228 := by
        have h1 : (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (14 + k)) ≤
            capFrontierCount positions := by
          unfold capFrontierCount
          exact sum_range_le_of_le (fun k => levelFrontierCount positions (14 + k)) (by omega)
        omega
      have hpres146 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s146.getReg r = s139.getReg r :=
        fun r h6 h7 h8 => by
          simp only [s146, s145, s144, s143, s142, s141, s140,
            MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x7 r (Ne.symm h7),
            getReg_setReg_ne' .x8 r (Ne.symm h8),
            getReg_setReg_ne' .x6 r (Ne.symm h6)]
      have hmem146 : ∀ a, s146.getByte a =
          (s139.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + levelSize l / 2))
            (if mProm then 1#8 else 0#8)).getByte a := fun a => by
        simp only [s146, s145, s144, s143, s142, s141, s140, getByte_setPC, getByte_setReg]; rfl
      refine ⟨6, s146, ((((h140.trans h141').trans h142').trans h143').trans h144').trans h145',
        by rw [if_neg heven_sz], rfl,
        by rw [hpres146 .x2 (by decide) (by decide) (by decide)]; exact inv139.rx2,
        by rw [hpres146 .x9 (by decide) (by decide) (by decide)]; exact inv139.rx9,
        by rw [hpres146 .x21 (by decide) (by decide) (by decide)]; exact inv139.rx21,
        by rw [hpres146 .x26 (by decide) (by decide) (by decide)]; exact inv139.rx26,
        by rw [hpres146 .x29 (by decide) (by decide) (by decide)]; exact inv139.rx29,
        by rw [hpres146 .x30 (by decide) (by decide) (by decide)]; exact inv139.rx30,
        ?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [s146, MachineState.getMem_setPC]
        exact readOnly_setByte_cap (4096 + capMarkOff (l + 1) + levelSize l / 2) _ inv139.ro
          (by omega) (by omega) a ha
      · have hw' := writerState_setByte_outside (4096 + capMarkOff (l + 1) + levelSize l / 2)
          (if mProm then 1#8 else 0#8) inv139.writer (by omega) (Or.inl (by omega)) (by omega)
        exact ⟨by rw [hpres146 .x25 (by decide) (by decide) (by decide)]; exact inv139.writer.rx25,
          by rw [hpres146 .x13 (by decide) (by decide) (by decide)]; exact inv139.writer.rx13,
          by rw [hpres146 .x14 (by decide) (by decide) (by decide)]; exact inv139.writer.rx14,
          fun j hj => by rw [hpres146 .x12 (by decide) (by decide) (by decide)]; exact inv139.writer.wbufLo j hj,
          fun j h1 h2 => by rw [hpres146 .x12 (by decide) (by decide) (by decide)]; exact inv139.writer.wbufHi j h1 h2,
          fun j hj => by rw [hmem146]; exact hw'.memDwords j hj⟩
      · have htb : tailBufBase = 20000000000 := rfl
        have ht' := tailState_setByte_outside (4096 + capMarkOff (l + 1) + levelSize l / 2)
          (if mProm then 1#8 else 0#8) inv139.tail (by omega) (by omega)
        exact ⟨by rw [hpres146 .x31 (by decide) (by decide) (by decide)]; exact inv139.tail.rx31,
          by rw [hpres146 .x15 (by decide) (by decide) (by decide)]; exact inv139.tail.rx15,
          by rw [hpres146 .x16 (by decide) (by decide) (by decide)]; exact inv139.tail.rx16,
          by rw [hpres146 .x17 (by decide) (by decide) (by decide)]; exact inv139.tail.rx17,
          fun j hj => by rw [hmem146]; exact ht'.memTail j hj⟩
      · intro idx hidx
        rw [hmem146, set_byte_read]
        by_cases hlast : idx = levelSize l / 2
        · subst hlast
          have hge : ¬ (2 * (levelSize l / 2) + 1 < levelSize l) := by omega
          have hlt : 2 * (levelSize l / 2) < levelSize l := by omega
          rw [if_pos rfl]
          change (if capMark positions l (2 * (levelSize l / 2)) then 1#8 else 0#8) = _
          rw [capMark_succ positions l (levelSize l / 2) (by omega), if_neg hge, if_pos hlt]
        · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
          exact inv139.nextMarks idx (by omega)
  obtain ⟨n146, s146, hr146, hn146, hpc146, hx2, hx9, hx21, hx26, hx29, hx30,
      hro146, hw146, ht146, hcm146⟩ := hto146
  -- Latch: 146..147
  have h146 := step_ADDI (by omega) hpc146 (rfl : openingInstr 181 = .base (.ADDI .x29 .x29 (32#12)))
  let s147 := (s146.setReg .x29 (BitVec.ofNat 64 (68719475968 + 32 * (14 + (step + 1))))).setPC (pcAt 182)
  have h146' : OpenRuns s146 1 1 s147 := by
    have hv : s146.getReg .x29 + signExtend12 (32#12) =
        BitVec.ofNat 64 (68719475968 + 32 * (14 + (step + 1))) := by
      rw [hx29, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s147] using h146
  have hmkInv : ∀ pc, CapLvlInv trapdoor positions (step + 1) fwd1 tails1 (s147.setPC pc) := fun pc =>
    ⟨hx2, hx9, hx21, hx26, rfl, hx30, hboundF139, hboundT139, hro146, hw146.of_eq, ht146.of_eq,
     by rw [show 14 + (step + 1) = l + 1 by omega]; exact hcm146⟩
  have hstep_bd : 9 + stPairs + 1 + n146 + 1 + 1 ≤
      9 + 10 * (levelSize l / 2) + 52 * levelFrontierCount positions l +
      (if levelSize l % 2 = 0 then 4 else 9) := by
    by_cases hmod : levelSize l % 2 = 0
    · rw [if_pos hmod] at hn146 ⊢; omega
    · rw [if_neg hmod] at hn146 ⊢; omega
  by_cases hmore : step + 1 < 9
  · have h147 := step_BNE_taken (by omega) (rfl : s147.pc = pcAt 182)
      (rfl : openingInstr 182 = .base (.BNE .x29 .x30 (8056#13)))
      (by change BitVec.ofNat 64 (68719475968 + 32 * (14 + (step + 1))) ≠ s146.getReg .x30
          rw [hx30]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 182 + signExtend13 (8056#13) = pcAt 148)
    exact ⟨9 + stPairs + 1 + n146 + 1 + 1, s147.setPC (pcAt 148),
      ((((hhdr.trans hrPairs).trans h139').trans hr146).trans h146').trans h147,
      hstep_bd, by rw [if_pos hmore]; rfl, hmkInv (pcAt 148)⟩
  · have hdone : 14 + (step + 1) = 23 := by omega
    have h147 := step_BNE_not_taken (by omega) (rfl : s147.pc = pcAt 182)
      (rfl : openingInstr 182 = .base (.BNE .x29 .x30 (8056#13)))
      (by change BitVec.ofNat 64 (68719475968 + 32 * (14 + (step + 1))) = s146.getReg .x30
          rw [hx30, hdone])
    exact ⟨9 + stPairs + 1 + n146 + 1 + 1, s147.setPC (pcAt 183),
      ((((hhdr.trans hrPairs).trans h139').trans hr146).trans h146').trans h147,
      hstep_bd, by rw [if_neg hmore]; rfl, hmkInv (pcAt 183)⟩

private theorem cap_const_cycles_sum :
    (∑ step ∈ Finset.range 9,
      (9 + 10 * (levelSize (14 + step) / 2) + if levelSize (14 + step) % 2 = 0 then 4 else 9)) =
      4682 := by
  decide

private theorem openRuns_cap_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {recFwd : List Byte} {recTails : List (BitVec 6)} {s111 : MachineState}
    (hpc : s111.pc = pcAt 146)
    (hx2 : s111.getReg .x2 = BitVec.ofNat 64 68719475968)
    (hx9 : s111.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx21 : s111.getReg .x21 = BitVec.ofNat 64 4096)
    (hx26 : s111.getReg .x26 = BitVec.ofNat 64 11162446080)
    (hbdF : recFwd.length ≤ 513 * positions.card)
    (hbdT : recTails.length ≤ 5 * positions.card)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s111)
    (hw : WriterState s111 recFwd)
    (ht : TailState s111 recTails)
    (hcap14 : CapLevelMarks s111 positions 14) :
    let allFwd := recFwd ++ capFrontierFwd (tdNode trapdoor) positions
    let allTails := recTails ++ capFrontierTails (tdNode trapdoor) positions
    ∃ steps s148, OpenRuns s111 steps steps s148 ∧
      steps ≤ 16540 ∧
      s148.pc = pcAt 183 ∧
      s148.getReg .x26 = BitVec.ofNat 64 11162446080 ∧
      WriterState s148 allFwd ∧
      TailState s148 allTails := by
  intro allFwd allTails
  have hse448 : signExtend12 (448#12) = BitVec.ofNat 64 448 := by decide
  have hse736 : signExtend12 (736#12) = BitVec.ofNat 64 736 := by decide
  have h111 := step_ADDI (by omega) hpc (rfl : openingInstr 146 = .base (.ADDI .x29 .x2 (448#12)))
  let s112 := (s111.setReg .x29 (BitVec.ofNat 64 (68719475968 + 32 * 14))).setPC (pcAt 147)
  have h111' : OpenRuns s111 1 1 s112 := by
    rw [hx2, hse448, bv64_ofNat_add] at h111; exact h111
  have h112 := step_ADDI (by omega) (rfl : s112.pc = pcAt 147)
    (rfl : openingInstr 147 = .base (.ADDI .x30 .x2 (736#12)))
  let s113 := (s112.setReg .x30 (BitVec.ofNat 64 (68719475968 + 32 * 23))).setPC (pcAt 148)
  have h112' : OpenRuns s112 1 1 s113 := by
    have hr2 : s112.getReg .x2 = BitVec.ofNat 64 68719475968 := hx2
    rw [hr2, hse736, bv64_ofNat_add] at h112; exact h112
  have hinv0 : CapLvlInv trapdoor positions 0 recFwd recTails s113 :=
    ⟨hx2, hx9, hx21, hx26, rfl, rfl, by simpa using hbdF, by simpa using hbdT, hro, hw.of_eq, ht.of_eq, hcap14⟩
  have hloop : ∀ k ≤ 9,
      let curF := recFwd ++ (List.range k).flatMap (fun step =>
        capLevelFrontierFwd (tdNode trapdoor) positions (14 + step))
      let curT := recTails ++ (List.range k).flatMap (fun step =>
        capLevelFrontierTails (tdNode trapdoor) positions (14 + step))
      ∃ steps sk, OpenRuns s113 steps steps sk ∧
        steps ≤ (∑ step ∈ Finset.range k,
          (9 + 10 * (levelSize (14 + step) / 2) + if levelSize (14 + step) % 2 = 0 then 4 else 9)) +
          52 * (∑ step ∈ Finset.range k, levelFrontierCount positions (14 + step)) ∧
        sk.pc = (if k < 9 then pcAt 148 else pcAt 183) ∧
        CapLvlInv trapdoor positions k curF curT sk := by
    intro k hk
    induction k with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Finset.sum_range_zero,
        Nat.mul_zero, Nat.add_zero]
      exact ⟨0, s113, OpenRuns.refl s113, Nat.le_refl 0, by rw [if_pos (by omega : 0 < 9)]; rfl, hinv0⟩
    | succ k ih =>
      obtain ⟨st, sk, hrk, hstk, hpck, invk⟩ := ih (by omega)
      have hpck' : sk.pc = pcAt 148 := by simpa only [show k < 9 by omega, ite_true] using hpck
      obtain ⟨st1, sk1, hr1, hst1, hpc1, inv1⟩ := openRuns_cap_lvl_iter (by omega) hpck' invk
      have happF : recFwd ++ (List.range k).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (14 + step)) ++
            capLevelFrontierFwd (tdNode trapdoor) positions (14 + k) =
          recFwd ++ (List.range (k + 1)).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (14 + step)) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      have happT : recTails ++ (List.range k).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (14 + step)) ++
            capLevelFrontierTails (tdNode trapdoor) positions (14 + k) =
          recTails ++ (List.range (k + 1)).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (14 + step)) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      rw [happF, happT] at inv1
      refine ⟨st + st1, sk1, hrk.trans hr1, ?_, hpc1, inv1⟩
      rw [Finset.sum_range_succ, Finset.sum_range_succ]; omega
  obtain ⟨stCap, s148, hrCap, hstCap, hpc148, inv148⟩ := hloop 9 (Nat.le_refl 9)
  have hpc148' : s148.pc = pcAt 183 := by simpa only [Nat.lt_irrefl, ite_false] using hpc148
  have hconst := cap_const_cycles_sum
  have hcap228 := cap_frontier_le_228 positions
  have hfront_eq : (∑ step ∈ Finset.range 9, levelFrontierCount positions (14 + step)) =
      capFrontierCount positions := rfl
  rw [hconst, hfront_eq] at hstCap
  have hallF_eq : recFwd ++ (List.range 9).flatMap (fun step =>
      capLevelFrontierFwd (tdNode trapdoor) positions (14 + step)) = allFwd := rfl
  have hallT_eq : recTails ++ (List.range 9).flatMap (fun step =>
      capLevelFrontierTails (tdNode trapdoor) positions (14 + step)) = allTails := rfl
  rw [hallF_eq, hallT_eq] at inv148
  exact ⟨2 + stCap, s148, (h111'.trans h112').trans hrCap, by omega, hpc148',
    inv148.rx26, inv148.writer, inv148.tail⟩

/-! ### 9. Top-Level Deterministic Opening Specification -/

private theorem submission_run_opening (s : Submission)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) :
    s.run .opening (trapdoor, positions) =
      execute (s.image .opening) (s.steps .opening)
        (s.initialState .opening (trapdoor, positions)) true := by
  unfold Submission.run
  dsimp only
  exact if_pos rfl

theorem opening_exec_spec (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    ∃ exec : Execution,
      submission.run .opening (trapdoor, positions) = pure exec ∧
      exec.exit = .success ∧
      exec.oracleCalls = 0 ∧
      (exec.state.getReg .x11).toNat =
        (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions).length ∧
      ProofPrefix exec.state (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions) ∧
      (positions.card = BATCH → exec.cycles ≤ 123000) := by
  have hsteps : submission.steps .opening = 274877906944 := rfl
  rw [submission_run_opening submission trapdoor positions]
  by_cases hempty : positions.card = 0
  · obtain ⟨s5, hr5, hpc5, _, _, _, _, _, hx27, _⟩ := openRuns_entry_prefix trapdoor positions
    have h5 := step_BEQ_taken (by omega) hpc5
      (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (792#13)))
      (by rw [hx27, hempty]; rfl)
      (by decide : pcAt 5 + signExtend13 (792#13) = pcAt 203)
    let s168 := s5.setPC (pcAt 203)
    obtain ⟨sHalt, hrepi, hpcH, hx5H, hx10H, hx11H, _⟩ :=
      openRuns_empty_epilogue (rfl : s168.pc = pcAt 203)
    have hexec := OpenRuns.halt (haltIdx := 206) (totalFuel := submission.steps .opening)
      ((hr5.trans h5).trans hrepi) (by omega) rfl hpcH hx5H hx10H (by rw [hsteps]; omega)
    have href : referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions = [] := by
      unfold referenceProof; rw [if_pos hempty]
    refine ⟨{ exit := .success, state := sHalt, cycles := 5 + 1 + 3 + 1, oracleCalls := 0 },
      hexec, rfl, rfl, ?_, ?_, ?_⟩
    · rw [href, hx11H]; rfl
    · rw [href]; intro j hj; exact absurd hj (Nat.not_lt_zero _)
    · intro hbatch
      change positions.card = 128 at hbatch
      omega
  · have hpos : 0 < positions.card := Nat.pos_of_ne_zero hempty
    have hcard := positions_card_le positions
    obtain ⟨s32, hr32, hpc32, hx2, hx9, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20,
        hx21, hx24, hx25, hx26, hx27, hx31, hmem32⟩ :=
      openRuns_entry_nonzero trapdoor positions hempty
    have hro32 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s32 := by
      intro a _; change s32.mem a = _; rw [hmem32]; rfl
    have hw0 : WriterState s32 [] :=
      ⟨by simpa using hx25, by simpa using hx13, by simpa using hx14,
       fun _ hj => absurd hj (Nat.not_lt_zero _),
       fun j _ hj => by rw [hx12]; apply BitVec.eq_of_getLsbD_eq; intro b _; simp,
       fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    have ht0 : TailState s32 [] :=
      ⟨hx31, by simpa using hx15, by simpa using hx16, by simpa using hx17,
       fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    have hinv0 : RecInv trapdoor positions 0 [] [] s32 :=
      ⟨hx2, hx9, hx18, hx19, hx20, hx21, by simpa using hx24, hx26, by simpa using hx27,
       hro32, hw0, ht0,
       fun c hc => by
         change extractByte (s32.mem _) _ = _
         rw [hmem32]
         have hz := opening_initial_zero_low trapdoor positions (4096 + c) (by omega)
         have hfalse : capMark14Prefix positions 0 c = false := by simp [capMark14Prefix]
         rw [hfalse, if_neg Bool.false_ne_true]; exact hz⟩
    obtain ⟨stRec, cyRec, s111, hrRec, hstRec, hcyRec, hpc111, hx2_111, hx9_111, hx21_111,
        hx26_111, hbdF111, hbdT111, hro111, hw111, ht111, hcap14⟩ :=
      openRuns_rec_all hpos hpc32 hinv0
    obtain ⟨stCap, s148, hrCap, hstCap, hpc148, hx26_148, hw148, ht148⟩ :=
      openRuns_cap_all hpc111 hx2_111 hx9_111 hx21_111 hx26_111 hbdF111 hbdT111
        hro111 hw111 ht111 hcap14
    set allFwd := referenceProofFwd (tdNode trapdoor) (tdSalt trapdoor) positions
    set allTails := referenceProofTails (tdNode trapdoor) positions
    change WriterState s148 allFwd at hw148
    change TailState s148 allTails at ht148
    have hlen_cap := referenceProof_length_le_cap (tdNode trapdoor) (tdSalt trapdoor) positions
    have htails_le : allTails.length ≤ 5 * positions.card + 228 :=
      referenceProofTails_length_le (tdNode trapdoor) positions
    have href_eq : allFwd ++ pack6BitsRev allTails =
        referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions := by
      unfold referenceProof; rw [if_neg hempty]
    have hlen_sum : allFwd.length + (pack6Bits allTails).length ≤ 8669633152 := by
      have h1 : (allFwd ++ pack6BitsRev allTails).length ≤ 8669633152 := by
        rw [href_eq]; exact hlen_cap
      simpa only [List.length_append, pack6BitsRev, List.length_reverse] using h1
    obtain ⟨stFl, s155, hrFl, hstFl, hpc155, hx10_155, hx26_155, hpr155, ht155⟩ :=
      openRuns_flush_wbuf hpc148 hx26_148 (by omega) (by omega) hw148 ht148
    obtain ⟨stFt, s158, hrFt, hstFt, hpc158, hx10_158, hx26_158, hx31_158, hx15_158, hpr158, htb158⟩ :=
      openRuns_flush_tail hpc155 hx10_155 hx26_155 (by omega) (by omega) hpr155 ht155
    obtain ⟨s164, hrRev, hpc164, hx10_164, hx26_164, hpr164⟩ :=
      openRuns_rev_tail hpc158 hx10_158 hx26_158 hx31_158 hx15_158 hlen_sum hpr158 htb158
    have hrev_eq : allFwd ++ (pack6Bits allTails).reverse =
        referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions := href_eq
    rw [hrev_eq] at hx10_164 hpr164
    obtain ⟨sHalt, hrFin, hpcH, hx5H, hx10H, hx11H, hmemH⟩ :=
      openRuns_finish hpc164 hx10_164 hx26_164
    have htot := (((((hr32.trans hrRec).trans hrCap).trans hrFl).trans hrFt).trans hrRev).trans hrFin
    have hpack_len : (pack6Bits allTails).length = (6 * allTails.length + 7) / 8 :=
      pack6Bits_length allTails
    have hpack_max : (pack6Bits allTails).length ≤ (6 * (5 * 16777216 + 228) + 7) / 8 := by
      rw [hpack_len]; exact Nat.div_le_div_right (by omega)
    have hfuel : 32 + stRec + stCap + stFl + stFt + (1 + 5 * (pack6Bits allTails).length) + 3 + 1 ≤
        submission.steps .opening := by
      rw [hsteps]; omega
    have hexec := OpenRuns.halt (haltIdx := 202) (totalFuel := submission.steps .opening)
      htot (by omega) rfl hpcH hx5H hx10H hfuel
    refine ⟨{ exit := .success, state := sHalt,
              cycles := 32 + cyRec + stCap + stFl + stFt + (1 + 5 * (pack6Bits allTails).length) + 3 + 1,
              oracleCalls := 0 },
      hexec, rfl, rfl, ?_, ?_, ?_⟩
    · change (sHalt.getReg .x11).toNat = _
      have hlen_cap' : (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions).length ≤ 8669633152 := hlen_cap
      rw [hx11H, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro j hj
      change extractByte (sHalt.mem _) _ = _
      rw [hmemH]
      exact hpr164 j hj
    · intro hbatch
      change positions.card = 128 at hbatch
      have hpack_128 : (pack6Bits allTails).length ≤ 651 := by
        rw [hpack_len]
        have h1 : allTails.length ≤ 5 * 128 + 228 := by rw [hbatch] at htails_le; exact htails_le
        have h2 := Nat.div_le_div_right (c := 8) (show 6 * allTails.length + 7 ≤ 6 * (5 * 128 + 228) + 7 by omega)
        omega
      change 32 + cyRec + stCap + stFl + stFt + (1 + 5 * (pack6Bits allTails).length) + 3 + 1 ≤ 123000
      omega

end CommitGolfCandidate
