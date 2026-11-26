import CommitGolfCandidate.MoonMemory

/-! Exact deterministic symbolic execution of the 254-word opening image with branchless
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
    (hhi : haltIdx < 254)
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

private theorem signExtend12_neg_add (imm : BitVec 12) (k : Nat)
    (h : signExtend12 imm + BitVec.ofNat 64 k = 0#64) (n : Nat) (hn : k ≤ n) :
    BitVec.ofNat 64 n + signExtend12 imm = BitVec.ofNat 64 (n - k) := by
  have hsplit : BitVec.ofNat 64 n = BitVec.ofNat 64 (n - k) + BitVec.ofNat 64 k := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel hn]
  rw [hsplit, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 k), h, BitVec.add_zero]

private theorem bv64_add_neg1 (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (4095#12) = BitVec.ofNat 64 n := by
  simpa only [Nat.add_sub_cancel] using signExtend12_neg_add (4095#12) 1 (by decide) (n + 1) (by omega)

private theorem bv64_add_neg8 (n : Nat) (h : 8 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4088#12) = BitVec.ofNat 64 (n - 8) :=
  signExtend12_neg_add (4088#12) 8 (by decide) n h

private theorem bv64_add_neg64 (n : Nat) (h : 64 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4032#12) = BitVec.ofNat 64 (n - 64) :=
  signExtend12_neg_add (4032#12) 64 (by decide) n h

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

private def tailAccLen (tails : List (BitVec 6)) : Nat :=
  (tails.foldl pack6Step ([], 0, 0)).1.length

private theorem tailAccLen_nil : tailAccLen [] = 0 := rfl

private theorem pack6_foldl_acc_mono (ts : List (BitVec 6)) :
    ∀ st : List Byte × Nat × Nat, st.1.length ≤ (ts.foldl pack6Step st).1.length := by
  induction ts with
  | nil => intro st; exact Nat.le_refl _
  | cons t rest ih =>
    intro ⟨acc, buf, cnt⟩
    simp only [List.foldl_cons]
    have hstep : acc.length ≤ (pack6Step (acc, buf, cnt) t).1.length := by
      unfold pack6Step; dsimp only; split_ifs <;> simp
    exact Nat.le_trans hstep (ih _)

private theorem tailAccLen_mono_append (a b : List (BitVec 6)) :
    tailAccLen a ≤ tailAccLen (a ++ b) := by
  unfold tailAccLen
  rw [List.foldl_append]
  exact pack6_foldl_acc_mono b _

private theorem tailAccLen_le_pack6Bits (tails : List (BitVec 6)) :
    tailAccLen tails ≤ (pack6Bits tails).length := by
  unfold tailAccLen pack6Bits pack6Finish
  rcases tails.foldl pack6Step ([], 0, 0) with ⟨acc, buf, cnt⟩
  dsimp only
  split_ifs <;> simp

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

private theorem levelSize_le_max (l : Nat) (hl : l ≤ 24) : levelSize l ≤ 16777216 := by
  interval_cases l <;> decide

private theorem nodeOffset_lt_treeBytes (l idx : Nat) (hl : l ≤ 24) (hidx : idx < levelSize l) :
    levelBase l + nodeOffset l idx + 32 ≤ treeBytes := by
  by_cases h24 : l < 24
  · have hg := gapOffset_lt_levelBytes l idx h24 hidx
    have hb := levelBase_bound l hl
    unfold nodeOffset
    omega
  · have hl24 : l = 24 := by omega
    subst hl24
    have hls : levelSize 24 = 1 := levelSize_24
    have hidx0 : idx = 0 := by omega
    subst hidx0
    decide

private theorem nodeOffset_align8 (l idx : Nat) : nodeOffset l idx % 8 = 0 := by
  unfold nodeOffset gapOffset
  omega

private theorem levelBase_align8 (l : Nat) (hl : l ≤ 24) : levelBase l % 8 = 0 := by
  interval_cases l <;> decide

private theorem saltOff_formula (i : Index) :
    rowOff + 72 + (184 * (i.val / 2) + 16 * (i.val % 2)) = saltOff i := by
  unfold saltOff PAIR_STRIDE
  split_ifs <;> omega

private theorem saltOff_align8 (i : Index) : saltOff i % 8 = 0 := by
  unfold saltOff PAIR_STRIDE
  rw [rowOff_eq]
  split_ifs <;> omega

private theorem capMarkOff_step_disjoint (l : Nat) (hl1 : 16 ≤ l) (hl2 : l ≤ 23) :
    capMarkOff l + levelSize l ≤ capMarkOff (l + 1) := by
  interval_cases l <;> decide

/-! ### 3. Single-Instruction Step Lemmas -/

private theorem step_ADDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ADDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_ADD {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ADD rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADD rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADD rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SUB {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SUB rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SUB rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SUB rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SLLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SLLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SLLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SLLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SRLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SRLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SRLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SRLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SLL {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SLL rd rs1 rs2)) :
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SRL rd rs1 rs2)) :
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.XORI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.XORI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.XORI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_ANDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ANDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ANDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ANDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_OR {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.OR rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.OR rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.OR rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_LD {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.LD rd rs1 off))
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SD rs1 rs2 off))
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.LBU rd rs1 off))
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SB rs1 rs2 off))
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
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

private theorem step_JAL {s : MachineState} {idx tgt : Nat} {rd : Reg} {off : BitVec 21}
    (hidx : idx < 254) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.JAL rd off))
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
    (hidx : idx < 254) (hpc : s.pc = pcAt idx)
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

/-- Read-only regions: trapdoor `[4294971424, 7449087968)`, indices `[7449087968, 7583305696)`,
and embedded metadata `[68719475936, 68719476736)`. -/
def ReadOnlyPreserved (s0 s : MachineState) : Prop :=
  ∀ addr : Word,
    (4294971424 ≤ addr.toNat ∧ addr.toNat < 7583305696) ∨
    (68719475936 ≤ addr.toNat ∧ addr.toNat < 68719476736) →
    s.getMem addr = s0.getMem addr

/-- Exact byte contents of the proof output prefix `[11878272992, 11878272992 + bytes.length)`. -/
def ProofPrefix (s : MachineState) (bytes : List Byte) : Prop :=
  ∀ j (hj : j < bytes.length),
    s.getByte (BitVec.ofNat 64 (11878272992 + j)) = bytes[j]

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
  rx25 : s.getReg .x25 = BitVec.ofNat 64 (11878272992 + 8 * (fwdBytes.length / 8))
  rx13 : s.getReg .x13 = BitVec.ofNat 64 (8 * (fwdBytes.length % 8))
  rx14 : s.getReg .x14 = BitVec.ofNat 64 (63 - 8 * (fwdBytes.length % 8))
  wbufLo : ∀ j (hj : j < fwdBytes.length % 8),
    (s.getReg .x12).extractLsb' (8 * j) 8 =
      fwdBytes[8 * (fwdBytes.length / 8) + j]'(by omega)
  wbufHi : ∀ j, fwdBytes.length % 8 ≤ j → j < 8 →
    (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8
  memDwords : ∀ j (hj : j < 8 * (fwdBytes.length / 8)),
    s.getByte (BitVec.ofNat 64 (11878272992 + j)) = fwdBytes[j]'(by omega)

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
    s.getMem (BitVec.ofNat 64 (7449087968 + 8 * ordinal)) =
      BitVec.ofNat 64 (openingIndex positions ordinal) := by
  have hcard := positions_card_le positions
  have haddr : (BitVec.ofNat 64 (7449087968 + 8 * ordinal)).toNat = 7449087968 + 8 * ordinal := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inl (by omega))]
  exact opening_initial_index trapdoor positions ordinal hord

private theorem readOnly_getMem_data_base {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 25) :
    s.getMem (BitVec.ofNat 64 (68719475936 + 32 * l)) = BitVec.ofNat 64 (levelBase l) := by
  have haddr : (BitVec.ofNat 64 (68719475936 + 32 * l)).toNat = 68719475936 + 32 * l := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), opening_initial_data_dword trapdoor positions (32 * l) (by omega)]
  exact openingData_dword_0 ⟨l, hl⟩

private theorem readOnly_getMem_data_size {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 25) :
    s.getMem (BitVec.ofNat 64 (68719475936 + 32 * l + 8)) = BitVec.ofNat 64 (levelSize l) := by
  have haddr : (BitVec.ofNat 64 (68719475936 + 32 * l + 8)).toNat = 68719475936 + 32 * l + 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), show 68719475936 + 32 * l + 8 = 68719475936 + (32 * l + 8) by omega,
    opening_initial_data_dword trapdoor positions (32 * l + 8) (by omega)]
  exact openingData_dword_1 ⟨l, hl⟩

private theorem readOnly_getMem_data_markOff {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 25) :
    s.getMem (BitVec.ofNat 64 (68719475936 + 32 * l + 16)) = BitVec.ofNat 64 (capMarkOff l) := by
  have haddr : (BitVec.ofNat 64 (68719475936 + 32 * l + 16)).toNat = 68719475936 + 32 * l + 16 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), show 68719475936 + 32 * l + 16 = 68719475936 + (32 * l + 16) by omega,
    opening_initial_data_dword trapdoor positions (32 * l + 16) (by omega)]
  exact openingData_dword_2 ⟨l, hl⟩

private theorem readOnly_getByte_trapdoor {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (off : Nat) (hoff : off < 3154116544) :
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
    (off j : Nat) (hal : off % 8 = 0) (hj : j < 8) (hbd : off + 8 ≤ 3154116544) :
    (s.getMem (BitVec.ofNat 64 (4294971424 + off))).extractLsb' (8 * j) 8 =
      trapdoor.extractLsb' (8 * (off + j)) 8 := by
  rw [getMem_extractByte (by omega) hj, Nat.add_assoc]
  exact readOnly_getByte_trapdoor hro (off + j) (by omega)

private theorem readOnly_setMem_proof {s0 s : MachineState} (dst : Nat) (val : Word)
    (hro : ReadOnlyPreserved s0 s) (hlo : 11878272992 ≤ dst) (hhi : dst + 8 ≤ 20354965184) :
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
    (hro : ReadOnlyPreserved s0 s) (hlo : 4096 ≤ dst) (hhi : dst < 4696) :
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
    (hro : ReadOnlyPreserved s0 s) (hlo : tailBufBase ≤ dst) (hhi : dst < 68719475936) :
    ReadOnlyPreserved s0 (s.setByte (BitVec.ofNat 64 dst) b) := by
  intro addr had
  have htb : tailBufBase = 25769803776 := rfl
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
    (b : BitVec 8) (hw : WriterState s fwdBytes) (hbd : fwdBytes.length ≤ 8476692192)
    (hout : dst < 11878272992 ∨ 20354965184 ≤ dst) (hdst : dst < 2 ^ 64) :
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
    (b : BitVec 8) (ht : TailState s tails) (htbd : tails.length ≤ 300000000)
    (hdst : dst < tailBufBase) :
    TailState (s.setByte (BitVec.ofNat 64 dst) b) tails :=
  ⟨by rw [getReg_setByte]; exact ht.rx31,
   by rw [getReg_setByte]; exact ht.rx15,
   by rw [getReg_setByte]; exact ht.rx16,
   by rw [getReg_setByte]; exact ht.rx17,
   fun j hj => by
     have htb : tailBufBase = 25769803776 := rfl
     have hlen := (pack6_foldl_bounds tails).2.2
     rw [set_byte_read, if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
     exact ht.memTail j hj⟩

private theorem tailState_of_mem_eq {s1 s2 : MachineState} {tails : List (BitVec 6)}
    (ht : TailState s1 tails) (htbd : tails.length ≤ 300000000)
    (hreg : ∀ r, r = .x15 ∨ r = .x16 ∨ r = .x17 ∨ r = .x31 → s2.getReg r = s1.getReg r)
    (hmem : ∀ q, tailBufBase ≤ q → q < 68719475936 →
      s2.getByte (BitVec.ofNat 64 q) = s1.getByte (BitVec.ofNat 64 q)) :
    TailState s2 tails :=
  ⟨by rw [hreg .x31 (by simp)]; exact ht.rx31,
   by rw [hreg .x15 (by simp)]; exact ht.rx15,
   by rw [hreg .x16 (by simp)]; exact ht.rx16,
   by rw [hreg .x17 (by simp)]; exact ht.rx17,
   fun j hj => by
     have htb : tailBufBase = 25769803776 := rfl
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


/-! ### 5. Branchless Dword Writer & Streaming 6-Bit Tail Subroutines (`172..296`) -/

private theorem openRuns_emit_dword {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base srcOff qBase k : Nat} {imm : BitVec 12}
    {cur chunk8 : List Byte}
    (hbase : base + 5 < 254)
    (himm : signExtend12 imm = BitVec.ofNat 64 (8 * k))
    (hi0 : openingInstr base = .base (.LD .x5 .x10 imm))
    (hi1 : openingInstr (base + 1) = .base (.SLL .x6 .x5 .x13))
    (hi2 : openingInstr (base + 2) = .base (.OR .x12 .x12 .x6))
    (hi3 : openingInstr (base + 3) = .base (.SD .x25 .x12 imm))
    (hi4 : openingInstr (base + 4) = .base (.SRLI .x5 .x5 (1#6)))
    (hi5 : openingInstr (base + 5) = .base (.SRL .x12 .x5 .x14))
    (hpc : s.pc = pcAt base)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (11878272992 + 8 * qBase))
    (hqeq : cur.length / 8 = qBase + k)
    (hx13 : s.getReg .x13 = BitVec.ofNat 64 (8 * (cur.length % 8)))
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (63 - 8 * (cur.length % 8)))
    (hwLo : ∀ j (hj : j < cur.length % 8),
      (s.getReg .x12).extractLsb' (8 * j) 8 = cur[8 * (cur.length / 8) + j]'(by omega))
    (hwHi : ∀ j, cur.length % 8 ≤ j → j < 8 →
      (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8)
    (hmem : ∀ j (hj : j < 8 * (cur.length / 8)),
      s.getByte (BitVec.ofNat 64 (11878272992 + j)) = cur[j]'(by omega))
    (hsrc_al : srcOff % 8 = 0)
    (hsrc_bd : srcOff + 8 * k + 8 ≤ 3154116544)
    (hcur_bd : cur.length + 8 ≤ 8476692192)
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
        s'.getByte (BitVec.ofNat 64 (11878272992 + j)) = cur'[j]'(by omega)) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475936 →
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
  have hdstAddr : s3.getReg .x25 + signExtend12 imm = BitVec.ofNat 64 (11878272992 + 8 * q) := by
    have hr25 : s3.getReg .x25 = BitVec.ofNat 64 (11878272992 + 8 * qBase) := hx25
    rw [hr25, himm, bv64_ofNat_add]; congr 1; omega
  have h3 := step_SD (by omega) (rfl : s3.pc = pcAt (base + 3)) hi3
    (by rw [hdstAddr]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s4 := (s3.setMem (BitVec.ofNat 64 (11878272992 + 8 * q)) wOut).setPC (pcAt (base + 4))
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
      (s.setMem (BitVec.ofNat 64 (11878272992 + 8 * q)) wOut).getByte a := fun a => by
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
    · rw [setMem_getByte_ofNat s (11878272992 + 8 * q) (11878272992 + j) wOut
        (by omega) (by omega) (by omega) (by omega)]
      rw [hmem j hlt, list_getElem_append_left cur chunk8 j (by omega)]
    · have hu : j - 8 * q < 8 := by omega
      have hadd : 11878272992 + 8 * q + (j - 8 * q) = 11878272992 + j := by omega
      rw [← hadd, setMem_getByte_inside s (11878272992 + 8 * q) (j - 8 * q) wOut (by omega) hu]
      rw [word_or_shl_byte w v r hr hwHi (j - 8 * q) hu]
      by_cases hur : j - 8 * q < r
      · rw [if_pos hur, hwLo (j - 8 * q) hur, list_getElem_append_left cur chunk8 j (by omega)]
        congr 1; omega
      · rw [if_neg hur, hv_byte (j - 8 * q - r) (by omega),
          list_getElem_append_right cur chunk8 j (by omega) (by omega)]
        congr 1; omega
  · intro addr had
    change (s.setMem (BitVec.ofNat 64 (11878272992 + 8 * q)) wOut).getMem addr = _
    exact readOnly_setMem_proof (11878272992 + 8 * q) wOut hro (by omega) (by omega) addr had
  · intro a ha
    rw [hmem6, setMem_getByte_ofNat s (11878272992 + 8 * q) a wOut
      (by omega) (by omega) (by omega) (by omega)]
  · intro a ha1 ha2
    have htb : tailBufBase = 25769803776 := rfl
    rw [hmem6, setMem_getByte_ofNat s (11878272992 + 8 * q) a wOut
      (by omega) (by omega) (by omega) (by omega)]

private theorem openRuns_emit_3dwords {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base srcOff : Nat}
    {fwdBytes chunk24 : List Byte}
    (hbase : base + 18 < 254)
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
    (hsrc_bd : srcOff + 24 ≤ 3154116544)
    (hbd : fwdBytes.length + 24 ≤ 8476692192)
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
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475936 →
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
  have hx25_3 : s3.getReg .x25 = BitVec.ofNat 64 (11878272992 + 8 * qBase) := by
    rw [hreg3 .x25 (by decide) (by decide) (by decide),
      hreg2 .x25 (by decide) (by decide) (by decide),
      hreg1 .x25 (by decide) (by decide) (by decide)]
    exact hw.rx25
  have hnew25 : s3.getReg .x25 + signExtend12 (24#12) =
      BitVec.ofNat 64 (11878272992 + 8 * ((fwdBytes ++ chunk24).length / 8)) := by
    rw [hx25_3, hse24, bv64_ofNat_add]; congr 1
    simp only [List.length_append, hclen]; omega
  let s4 := (s3.setReg .x25 (BitVec.ofNat 64 (11878272992 + 8 * ((fwdBytes ++ chunk24).length / 8)))).setPC
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
    (hbase : base + 10 < 254) (hm1 : 1 ≤ m) (hm2 : m < 8)
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
    (hbd : fwdBytes.length + m ≤ 8476692192)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (hclen : chunkM.length = m)
    (hx5 : ∀ j (hj : j < 8),
      (s.getReg .x5).extractLsb' (8 * j) 8 =
        if hj' : j < m then chunkM[j]'(by omega) else 0#8) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps = 6 + 5 * ((fwdBytes ++ chunkM).length / 8 - fwdBytes.length / 8) ∧
      s'.pc = pcAt (base + 11) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x25 →
        s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ chunkM) ∧
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475936 →
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
    refine ⟨6, s11, (hpre.trans h4).trans h10', by rw [hq']; omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
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
    have hdstAddr : s5.getReg .x25 + signExtend12 (0#12) = BitVec.ofNat 64 (11878272992 + 8 * q) := by
      have hr25 : s5.getReg .x25 = BitVec.ofNat 64 (11878272992 + 8 * q) := hw.rx25
      rw [hr25, hse0, bv64_ofNat_add, Nat.add_zero]
    have h5 := step_SD (by omega) (rfl : s5.pc = pcAt (base + 5)) hc.2.2.2.2.2.1
      (by rw [hdstAddr]; exact accessValid_ofNat _ 8 (by omega) (by omega))
    let s6 := (s5.setMem (BitVec.ofNat 64 (11878272992 + 8 * q)) wOut).setPC (pcAt (base + 6))
    have h5' : OpenRuns s5 1 1 s6 := by
      simpa only [hdstAddr, show s5.getReg .x12 = wOut from rfl, s6, show base + 5 + 1 = base + 6 by omega] using h5
    -- +6: ADDI x25, x25, 8
    have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
    have h6 := step_ADDI (by omega) (rfl : s6.pc = pcAt (base + 6)) hc.2.2.2.2.2.2.1
    let s7 := (s6.setReg .x25 (BitVec.ofNat 64 (11878272992 + 8 * (q + 1)))).setPC (pcAt (base + 7))
    have h6' : OpenRuns s6 1 1 s7 := by
      have hr25 : s6.getReg .x25 = BitVec.ofNat 64 (11878272992 + 8 * q) := by
        simp only [s6, MachineState.getReg_setPC, getReg_setMem]; exact hw.rx25
      have hv : s6.getReg .x25 + signExtend12 (8#12) = BitVec.ofNat 64 (11878272992 + 8 * (q + 1)) := by
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
        (s.setMem (BitVec.ofNat 64 (11878272992 + 8 * q)) wOut).getByte a := fun a => by
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
      rfl
    refine ⟨11, s11, hpre.trans htail_steps, by rw [hq']; omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
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
      change (s.setMem (BitVec.ofNat 64 (11878272992 + 8 * q)) wOut).getMem a = _
      exact readOnly_setMem_proof (11878272992 + 8 * q) wOut hro (by omega) (by omega) a ha
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
        · rw [setMem_getByte_ofNat s (11878272992 + 8 * q) (11878272992 + j) wOut
            (by omega) (by omega) (by omega) (by omega)]
          rw [hw.memDwords j hltq, list_getElem_append_left fwdBytes chunkM j (by omega)]
        · have hu : j - 8 * q < 8 := by omega
          have hadd : 11878272992 + 8 * q + (j - 8 * q) = 11878272992 + j := by omega
          rw [← hadd, setMem_getByte_inside s (11878272992 + 8 * q) (j - 8 * q) wOut (by omega) hu]
          rw [word_or_shl_byte w v r hr hw.wbufHi (j - 8 * q) hu]
          by_cases hur : j - 8 * q < r
          · rw [if_pos hur, hw.wbufLo (j - 8 * q) hur, list_getElem_append_left fwdBytes chunkM j (by omega)]
            congr 1; omega
          · rw [if_neg hur, hx5 (j - 8 * q - r) (by omega), dif_pos (by omega),
              list_getElem_append_right fwdBytes chunkM j (by omega) (by omega)]
            congr 1; omega
    · intro a ha
      rw [hmem11, setMem_getByte_ofNat s (11878272992 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]
    · intro a ha1 ha2
      have htb : tailBufBase = 25769803776 := rfl
      rw [hmem11, setMem_getByte_ofNat s (11878272992 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]

private theorem openRuns_push_tail6 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {d : Digest}
    (hpc : s.pc = pcAt 242)
    (hx11 : (s.getReg .x11).extractLsb' (8 * 5) 8 = d.extractLsb' (8 * 29) 8)
    (hfbd : fwdBytes.length ≤ 8476692192)
    (htbd : tails.length < 300000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps = 7 + 4 * (tailAccLen (tails ++ [tail6 d]) - tailAccLen tails) ∧
      s'.pc = pcAt 253 ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 →
        s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' fwdBytes ∧
      TailState s' (tails ++ [tail6 d]) ∧
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have htb : tailBufBase = 25769803776 := rfl
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
  -- 204: SRLI x5, x11, 40
  have h0 := step_SRLI (by omega) hpc (rfl : openingInstr 242 = .base (.SRLI .x5 .x11 (40#6)))
  let s1 := (s.setReg .x5 (s.getReg .x11 >>> 40)).setPC (pcAt 243)
  have h0' : OpenRuns s 1 1 s1 := by
    simpa only [show (40#6 : BitVec 6).toNat = 40 from rfl, s1] using h0
  -- 205: ANDI x5, x5, 63
  have h1 := step_ANDI (by omega) (rfl : s1.pc = pcAt 243)
    (rfl : openingInstr 243 = .base (.ANDI .x5 .x5 (63#12)))
  let s2 := (s1.setReg .x5 (BitVec.ofNat 64 t.toNat)).setPC (pcAt 244)
  have h1' : OpenRuns s1 1 1 s2 := by
    have hv := word_tail6_from_hi (s.getReg .x11) d hx11
    simpa only [show s1.getReg .x5 = s.getReg .x11 >>> 40 from rfl, hv, t, s2] using h1
  -- 206: SLL x6, x5, x17
  have h2 := step_SLL (by omega) (rfl : s2.pc = pcAt 244)
    (rfl : openingInstr 244 = .base (.SLL .x6 .x5 .x17))
  have hx17_mod : (s2.getReg .x17).toNat % 64 = tCnt := by
    have h : s2.getReg .x17 = BitVec.ofNat 64 tCnt := ht.rx17
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tCnt < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s3 := (s2.setReg .x6 (BitVec.ofNat 64 t.toNat <<< tCnt)).setPC (pcAt 245)
  have h2' : OpenRuns s2 1 1 s3 := by
    simpa only [show s2.getReg .x5 = BitVec.ofNat 64 t.toNat from rfl, hx17_mod, s3] using h2
  -- 207: OR x16, x16, x6
  set buf' := tBuf + t.toNat * 2 ^ tCnt
  have hbuf'_lt : buf' < 8192 := by
    have hmul : t.toNat * 2 ^ tCnt ≤ 63 * 128 := Nat.mul_le_mul (by omega) hpow
    change tBuf + t.toNat * 2 ^ tCnt < 8192
    omega
  have h3 := step_OR (by omega) (rfl : s3.pc = pcAt 245)
    (rfl : openingInstr 245 = .base (.OR .x16 .x16 .x6))
  let s4 := (s3.setReg .x16 (BitVec.ofNat 64 buf')).setPC (pcAt 246)
  have h3' : OpenRuns s3 1 1 s4 := by
    have hr16 : s3.getReg .x16 = BitVec.ofNat 64 tBuf := ht.rx16
    have hv : s3.getReg .x16 ||| s3.getReg .x6 = BitVec.ofNat 64 buf' := by
      rw [hr16]; exact tail_or_shl_eq_add tBuf tCnt t.toNat htCnt_lt htBuf_lt ht_lt
    simpa only [hv, s4] using h3
  -- 208: ADDI x17, x17, 6
  have hse6 : signExtend12 (6#12) = BitVec.ofNat 64 6 := by decide
  have h4 := step_ADDI (by omega) (rfl : s4.pc = pcAt 246)
    (rfl : openingInstr 246 = .base (.ADDI .x17 .x17 (6#12)))
  let s5 := (s4.setReg .x17 (BitVec.ofNat 64 (tCnt + 6))).setPC (pcAt 247)
  have h4' : OpenRuns s4 1 1 s5 := by
    have hr17 : s4.getReg .x17 = BitVec.ofNat 64 tCnt := ht.rx17
    rw [hr17, hse6, bv64_ofNat_add] at h4; exact h4
  -- 209: ADDI x7, x0, 8
  have h5 := step_ADDI (by omega) (rfl : s5.pc = pcAt 247)
    (rfl : openingInstr 247 = .base (.ADDI .x7 .x0 (8#12)))
  let s6 := (s5.setReg .x7 8#64).setPC (pcAt 248)
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
  · have h6 := step_BLTU_taken (by omega) (rfl : s6.pc = pcAt 248)
      (rfl : openingInstr 248 = .base (.BLTU .x17 .x7 (20#13)))
      (by rw [hx17_6, hx7_6]; exact hlt8)
      (by decide : pcAt 248 + signExtend13 (20#13) = pcAt 253)
    let s7 := s6.setPC (pcAt 253)
    have hpack : (tails ++ [t]).foldl pack6Step ([], 0, 0) = (acc, buf', tCnt + 6) := by
      rw [hfold_app]; unfold pack6Step; dsimp only; rw [if_neg (by omega)]
    have hacc_eq : tailAccLen (tails ++ [tail6 d]) = tailAccLen tails := by
      unfold tailAccLen; change ((tails ++ [t]).foldl pack6Step ([], 0, 0)).1.length = acc.length
      rw [hpack]
    refine ⟨7, s7, hpre.trans h6, by rw [hacc_eq]; omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
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
    have h6 := step_BLTU_not_taken (by omega) (rfl : s6.pc = pcAt 248)
      (rfl : openingInstr 248 = .base (.BLTU .x17 .x7 (20#13)))
      (by rw [hx17_6, hx7_6]; exact hge8)
    let s7 := s6.setPC (pcAt 249)
    -- 211: SB x15, x16, 0
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have haddr7 : s7.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + acc.length) := by
      have hr15 : s7.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := ht.rx15
      rw [hr15, hse0, bv64_ofNat_add, Nat.add_zero]
    have h7 := step_SB (by omega) (rfl : s7.pc = pcAt 249)
      (rfl : openingInstr 249 = .base (.SB .x15 .x16 (0#12)))
      (by rw [haddr7]; exact accessValid_ofNat _ 1 (by omega) (by omega))
    let s8 := (s7.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).setPC (pcAt 250)
    have h7' : OpenRuns s7 1 1 s8 := by
      have htr : (s7.getReg .x16).truncate 8 = BitVec.ofNat 8 buf' := by
        change (BitVec.ofNat 64 buf').truncate 8 = _
        exact bv64_ofNat_truncate8 buf' (by omega)
      simpa only [haddr7, htr, s8] using h7
    -- 212: ADDI x15, x15, 1
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have h8 := step_ADDI (by omega) (rfl : s8.pc = pcAt 250)
      (rfl : openingInstr 250 = .base (.ADDI .x15 .x15 (1#12)))
    let s9 := (s8.setReg .x15 (BitVec.ofNat 64 (tailBufBase + (acc ++ [BitVec.ofNat 8 buf']).length))).setPC (pcAt 251)
    have h8' : OpenRuns s8 1 1 s9 := by
      have hr15 : s8.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := by
        simp only [s8, MachineState.getReg_setPC, getReg_setByte]; exact ht.rx15
      have hv : s8.getReg .x15 + signExtend12 (1#12) =
          BitVec.ofNat 64 (tailBufBase + (acc ++ [BitVec.ofNat 8 buf']).length) := by
        rw [hr15, hse1, bv64_ofNat_add, List.length_append, List.length_singleton, Nat.add_assoc]
      simpa only [hv, s9] using h8
    -- 213: SRLI x16, x16, 8
    have h9 := step_SRLI (by omega) (rfl : s9.pc = pcAt 251)
      (rfl : openingInstr 251 = .base (.SRLI .x16 .x16 (8#6)))
    let s10 := (s9.setReg .x16 (BitVec.ofNat 64 (buf' / 256))).setPC (pcAt 252)
    have h9' : OpenRuns s9 1 1 s10 := by
      have hr16 : s9.getReg .x16 = BitVec.ofNat 64 buf' := by
        simp only [s9, s8, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x15 .x16 (by decide)]
        rfl
      have hv : s9.getReg .x16 >>> (8#6 : BitVec 6).toNat = BitVec.ofNat 64 (buf' / 256) := by
        rw [hr16]; change BitVec.ofNat 64 buf' >>> 8 = _
        rw [bv64_ushr buf' 8 (by omega), Nat.shiftRight_eq_div_pow]
      simpa only [hv, s10] using h9
    -- 214: ADDI x17, x17, 4088 (-8)
    have h10 := step_ADDI (by omega) (rfl : s10.pc = pcAt 252)
      (rfl : openingInstr 252 = .base (.ADDI .x17 .x17 (4088#12)))
    let s11 := (s10.setReg .x17 (BitVec.ofNat 64 (tCnt + 6 - 8))).setPC (pcAt 253)
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
    have hacc_eq : tailAccLen (tails ++ [tail6 d]) = tailAccLen tails + 1 := by
      unfold tailAccLen; change ((tails ++ [t]).foldl pack6Step ([], 0, 0)).1.length = acc.length + 1
      rw [hpack]; simp
    have hmem11 : ∀ a, s11.getByte a =
        (s.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).getByte a := fun a => by
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
      rfl
    have htot := hpre.trans ((((h6.trans h7').trans h8').trans h9').trans h10')
    refine ⟨11, s11, htot, by rw [hacc_eq]; omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
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
    (hcall : callIdx < 254)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 129)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 24 ≤ 3154116544)
    (hbd : fwdBytes.length + 24 ≤ 8476692192)
    (htbd : tails.length ≤ 300000000)
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
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have hr_jal := step_JAL hcall hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 129)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  have hw1 : WriterState s1 fwdBytes :=
    ⟨hw.rx25, hw.rx13, hw.rx14, hw.wbufLo, hw.wbufHi, hw.memDwords⟩
  obtain ⟨s2, hr_body, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    openRuns_emit_3dwords (base := 129) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := chunk)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (by exact hx10) hsrc_al hsrc_bd hbd hro1 hw1 hclen hchunk
  have hx1_2 : s2.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl
  have hr_ret := step_JALR_x0 (by omega) hpc2 (rfl : openingInstr 148 = .base (.JALR .x0 .x1 (0#12))) hx1_2
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

private theorem openRuns_emit_4dwords {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base srcOff : Nat}
    {fwdBytes chunk32 : List Byte}
    (hbase : base + 24 < 254)
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
    (hc3 : openingInstr (base + 18) = .base (.LD .x5 .x10 (24#12)) ∧
      openingInstr (base + 19) = .base (.SLL .x6 .x5 .x13) ∧
      openingInstr (base + 20) = .base (.OR .x12 .x12 .x6) ∧
      openingInstr (base + 21) = .base (.SD .x25 .x12 (24#12)) ∧
      openingInstr (base + 22) = .base (.SRLI .x5 .x5 (1#6)) ∧
      openingInstr (base + 23) = .base (.SRL .x12 .x5 .x14))
    (hadv : openingInstr (base + 24) = .base (.ADDI .x25 .x25 (32#12)))
    (hpc : s.pc = pcAt base)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0)
    (hsrc_bd : srcOff + 32 ≤ 3154116544)
    (hbd : fwdBytes.length + 32 ≤ 8476692192)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (hclen : chunk32.length = 32)
    (hchunk : ∀ j (hj : j < 32),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk32[j]'(by omega)) :
    ∃ s', OpenRuns s 25 25 s' ∧
      s'.pc = pcAt (base + 25) ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ chunk32) ∧
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475936 →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  let c0 := chunk32.take 8
  let c1 := (chunk32.drop 8).take 8
  let c2 := (chunk32.drop 16).take 8
  let c3 := chunk32.drop 24
  have hc0_len : c0.length = 8 := by simp [c0, hclen]
  have hc1_len : c1.length = 8 := by simp [c1, hclen]
  have hc2_len : c2.length = 8 := by simp [c2, hclen]
  have hc3_len : c3.length = 8 := by simp [c3, hclen]
  have hsplit : c0 ++ (c1 ++ (c2 ++ c3)) = chunk32 := by
    have h1 : c0 ++ chunk32.drop 8 = chunk32 := List.take_append_drop 8 chunk32
    have h2 : c1 ++ chunk32.drop 16 = chunk32.drop 8 := by
      simpa [c1, List.drop_drop] using List.take_append_drop 8 (chunk32.drop 8)
    have h3 : c2 ++ c3 = chunk32.drop 16 := by
      simpa [c2, c3, List.drop_drop] using List.take_append_drop 8 (chunk32.drop 16)
    rw [h3, h2, h1]
  have hcur_eq : (((fwdBytes ++ c0) ++ c1) ++ c2) ++ c3 = fwdBytes ++ chunk32 := by
    simp only [List.append_assoc, hsplit]
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
        simpa [c2, List.getElem_take, List.getElem_drop, Nat.add_assoc] using hchunk (16 + j) (by omega))
  have hlen3 : (((fwdBytes ++ c0) ++ c1) ++ c2).length = fwdBytes.length + 24 := by
    simp only [List.length_append, hc0_len, hc1_len, hc2_len]
  obtain ⟨s4, hr4, hpc4, hreg4, hwLo4, hwHi4, hmem4, hro4, hcap4, htail4⟩ :=
    openRuns_emit_dword (base := base + 18) (srcOff := srcOff) (qBase := qBase) (k := 3) (imm := 24#12)
      (cur := ((fwdBytes ++ c0) ++ c1) ++ c2) (chunk8 := c3) (by omega) (by decide)
      hc3.1 hc3.2.1 hc3.2.2.1 hc3.2.2.2.1 hc3.2.2.2.2.1 hc3.2.2.2.2.2
      (by simpa only [show base + 12 + 6 = base + 18 by omega] using hpc3)
      (by rw [hreg3 .x10 (by decide) (by decide) (by decide), hreg2 .x10 (by decide) (by decide) (by decide), hreg1 .x10 (by decide) (by decide) (by decide)]; exact hx10)
      (by rw [hreg3 .x25 (by decide) (by decide) (by decide), hreg2 .x25 (by decide) (by decide) (by decide), hreg1 .x25 (by decide) (by decide) (by decide)]; exact hw.rx25)
      (by omega)
      (by rw [hreg3 .x13 (by decide) (by decide) (by decide), hreg2 .x13 (by decide) (by decide) (by decide), hreg1 .x13 (by decide) (by decide) (by decide), hw.rx13]; congr 1; omega)
      (by rw [hreg3 .x14 (by decide) (by decide) (by decide), hreg2 .x14 (by decide) (by decide) (by decide), hreg1 .x14 (by decide) (by decide) (by decide), hw.rx14]; congr 1; omega)
      hwLo3 hwHi3 hmem3 hsrc_al (by omega) (by omega) hro3 hc3_len (fun j hj => by
        simpa [c3, List.getElem_drop, Nat.add_assoc] using hchunk (24 + j) (by omega))
  -- +24: ADDI x25, x25, 32
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have hadvStep := step_ADDI (by omega) (by simpa only [show base + 18 + 6 = base + 24 by omega] using hpc4) hadv
  have hpres4 : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → s4.getReg r = s.getReg r := fun r h5 h6 h12 => by
    rw [hreg4 r h5 h6 h12, hreg3 r h5 h6 h12, hreg2 r h5 h6 h12, hreg1 r h5 h6 h12]
  have hx25_4 : s4.getReg .x25 = BitVec.ofNat 64 (11878272992 + 8 * qBase) := by
    rw [hpres4 .x25 (by decide) (by decide) (by decide)]; exact hw.rx25
  have hnew25 : s4.getReg .x25 + signExtend12 (32#12) =
      BitVec.ofNat 64 (11878272992 + 8 * ((fwdBytes ++ chunk32).length / 8)) := by
    rw [hx25_4, hse32, bv64_ofNat_add]; congr 1
    simp only [List.length_append, hclen]; omega
  let s5 := (s4.setReg .x25 (BitVec.ofNat 64 (11878272992 + 8 * ((fwdBytes ++ chunk32).length / 8)))).setPC
    (pcAt (base + 25))
  have hadv' : OpenRuns s4 1 1 s5 := by
    simpa only [hnew25, s5, show base + 24 + 1 = base + 25 by omega] using hadvStep
  refine ⟨s5, (((hr1.trans hr2).trans hr3).trans hr4).trans hadv', rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h5 h6 h12 h25
    simp only [s5, MachineState.getReg_setPC, getReg_setReg_ne' .x25 r (Ne.symm h25)]
    exact hpres4 r h5 h6 h12
  · intro a ha
    simp only [s5, MachineState.getMem_setPC, MachineState.getMem_setReg]
    exact hro4 a ha
  · refine WriterState.castList hcur_eq ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcur_eq]; rfl
    · simp only [s5, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x13 (by decide)]
      rw [hpres4 .x13 (by decide) (by decide) (by decide), hw.rx13, hcur_eq]; congr 1
      simp only [List.length_append, hclen]; omega
    · simp only [s5, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x14 (by decide)]
      rw [hpres4 .x14 (by decide) (by decide) (by decide), hw.rx14, hcur_eq]; congr 1
      simp only [List.length_append, hclen]; omega
    · intro j hj
      simp only [s5, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x12 (by decide)]
      exact hwLo4 j hj
    · intro j h1 h2
      simp only [s5, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x12 (by decide)]
      exact hwHi4 j h1 h2
    · intro j hj
      simp only [s5, getByte_setPC, getByte_setReg]
      exact hmem4 j hj
  · intro a ha
    simp only [s5, getByte_setPC, getByte_setReg]
    rw [hcap4 a ha, hcap3 a ha, hcap2 a ha, hcap1 a ha]
  · intro a ha1 ha2
    simp only [s5, getByte_setPC, getByte_setReg]
    rw [htail4 a ha1 ha2, htail3 a ha1 ha2, htail2 a ha1 ha2, htail1 a ha1 ha2]

private theorem openRuns_call_copy32 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx srcOff : Nat} {jOff : BitVec 21}
    {fwdBytes chunk : List Byte} {tails : List (BitVec 6)}
    (hcall : callIdx < 254)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 149)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 32 ≤ 3154116544)
    (hbd : fwdBytes.length + 32 ≤ 8476692192)
    (htbd : tails.length ≤ 300000000)
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
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have hr_jal := step_JAL hcall hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 149)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  have hw1 : WriterState s1 fwdBytes :=
    ⟨hw.rx25, hw.rx13, hw.rx14, hw.wbufLo, hw.wbufHi, hw.memDwords⟩
  obtain ⟨s2, hr_body, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    openRuns_emit_4dwords (base := 149) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk32 := chunk)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl rfl (by exact hx10) hsrc_al hsrc_bd hbd hro1 hw1 hclen hchunk
  have hx1_2 : s2.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl
  have hr_ret := step_JALR_x0 (by omega) hpc2 (rfl : openingInstr 174 = .base (.JALR .x0 .x1 (0#12))) hx1_2
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

private theorem openRuns_call_copy30 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx srcOff : Nat} {jOff : BitVec 21}
    {fwdBytes chunk : List Byte} {tails : List (BitVec 6)}
    (hcall : callIdx < 254)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 175)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 32 ≤ 3154116544)
    (hbd : fwdBytes.length + 30 ≤ 8476692192)
    (htbd : tails.length ≤ 300000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails)
    (hclen : chunk.length = 30)
    (hchunk : ∀ j (hj : j < 30),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk[j]'(by omega)) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps = 15 + 5 * ((fwdBytes ++ chunk).length / 8 - fwdBytes.length / 8) ∧
      s'.pc = pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x25 →
        s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ chunk) ∧
      TailState s' tails ∧
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  let c24 := chunk.take 24
  let c6 := chunk.drop 24
  have hc24_len : c24.length = 24 := by simp [c24, hclen]
  have hc6_len : c6.length = 6 := by simp [c6, hclen]
  have hsplit : (fwdBytes ++ c24) ++ c6 = fwdBytes ++ chunk := by
    rw [List.append_assoc, List.take_append_drop]
  have hr_jal := step_JAL hcall hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 175)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  have hw1 : WriterState s1 fwdBytes :=
    ⟨hw.rx25, hw.rx13, hw.rx14, hw.wbufLo, hw.wbufHi, hw.memDwords⟩
  obtain ⟨s2, hr_3d, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    openRuns_emit_3dwords (base := 175) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := c24)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (by exact hx10) hsrc_al (by omega) (by omega)
      hro1 hw1 hc24_len (fun j hj => by simpa [c24, List.getElem_take] using hchunk j (by omega))
  -- 156: LD x5, 24(x10); 157: SLLI x5, x5, 16; 158: SRLI x5, x5, 16
  have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
  have hx10_2 : s2.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff) := by
    rw [hreg2 .x10 (by decide) (by decide) (by decide) (by decide)]; exact hx10
  have haddr156 : s2.getReg .x10 + signExtend12 (24#12) =
      BitVec.ofNat 64 (4294971424 + (srcOff + 24)) := by
    rw [hx10_2, hse24, bv64_ofNat_add, Nat.add_assoc]
  set v3 := s2.getMem (BitVec.ofNat 64 (4294971424 + (srcOff + 24)))
  have h156 := step_LD (by omega) hpc2 (rfl : openingInstr 194 = .base (.LD .x5 .x10 (24#12)))
    (by rw [haddr156]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s3 := (s2.setReg .x5 v3).setPC (pcAt 195)
  have h156' : OpenRuns s2 1 1 s3 := by simpa only [haddr156, v3, s3] using h156
  have h157 := step_SLLI (by omega) (rfl : s3.pc = pcAt 195)
    (rfl : openingInstr 195 = .base (.SLLI .x5 .x5 (16#6)))
  let s4 := (s3.setReg .x5 (v3 <<< 16)).setPC (pcAt 196)
  have h157' : OpenRuns s3 1 1 s4 := by
    simpa only [show s3.getReg .x5 = v3 from rfl, show (16#6 : BitVec 6).toNat = 16 from rfl, s4] using h157
  have h158 := step_SRLI (by omega) (rfl : s4.pc = pcAt 196)
    (rfl : openingInstr 196 = .base (.SRLI .x5 .x5 (16#6)))
  let s5 := (s4.setReg .x5 ((v3 <<< 16) >>> 16)).setPC (pcAt 197)
  have h158' : OpenRuns s4 1 1 s5 := by
    simpa only [show s4.getReg .x5 = v3 <<< 16 from rfl, show (16#6 : BitVec 6).toNat = 16 from rfl, s5] using h158
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
    openRuns_emit_partial (base := 197) (m := 6) (immBits := 48#12)
      (fwdBytes := fwdBytes ++ c24) (chunkM := c6)
      (by omega) (by omega) (by omega) (by decide) (by decide)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl (by simp only [List.length_append, hc24_len]; omega) hro5 hw5 hc6_len hx5_5
  -- 170: JALR x0, x1, 0
  have hx1_6 : s6.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hreg6 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s5, s4, s3, MachineState.getReg_setPC, getReg_setReg_ne' .x5 .x1 (by decide)]
    rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl
  have hret := step_JALR_x0 (by omega) hpc6 (rfl : openingInstr 208 = .base (.JALR .x0 .x1 (0#12))) hx1_6
  let s7 := s6.setPC (pcAt (callIdx + 1))
  rw [hsplit] at hw6 hstP
  have hlen24 : (fwdBytes ++ c24).length = fwdBytes.length + 24 := by simp [hc24_len]
  have hlen30 : (fwdBytes ++ chunk).length = fwdBytes.length + 30 := by simp [hclen]
  have hpres7 : ∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x25 →
      s7.getReg r = s.getReg r := fun r h1 h5 h6 h7 h12 h13 h14 h25 => by
    simp only [s7, MachineState.getReg_setPC]
    rw [hreg6 r h5 h6 h7 h12 h13 h14 h25]
    simp only [s5, s4, s3, MachineState.getReg_setPC, getReg_setReg_ne' .x5 r (Ne.symm h5)]
    rw [hreg2 r h5 h6 h12 h25]; exact getReg_setReg_ne' .x1 r (Ne.symm h1) s _
  have htot := (((((hr_jal.trans hr_3d).trans h156').trans h157').trans h158').trans hrP).trans hret
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
    (hcall : callIdx < 254)
    (hl : l ≤ 24) (hnode : nodeIdx < levelSize l)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 209)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l nodeIdx)))
    (hbd : fwdBytes.length + 29 ≤ 8476692192)
    (htbd : tails.length < 300000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    let d := tdNode trapdoor l nodeIdx
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps = 22 + 5 * ((fwdBytes ++ bitsToBytes d 29).length / 8 - fwdBytes.length / 8) +
        4 * (tailAccLen (tails ++ [tail6 d]) - tailAccLen tails) ∧
      s'.pc = pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
        r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ bitsToBytes d 29) ∧
      TailState s' (tails ++ [tail6 d]) ∧
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro d
  set srcOff := levelBase l + nodeOffset l nodeIdx
  have htb : treeBytes = 1610612672 := treeBytes_eq
  have hsrc_bd : srcOff + 32 ≤ 3154116544 := by
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
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 209)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  have hw1 : WriterState s1 fwdBytes :=
    ⟨hw.rx25, hw.rx13, hw.rx14, hw.wbufLo, hw.wbufHi, hw.memDwords⟩
  obtain ⟨s2, hr_3d, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    openRuns_emit_3dwords (base := 209) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := c24)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (by exact hx10) hsrc_al (by omega) (by omega)
      hro1 hw1 hc24_len (fun j hj => by
        simpa [c24, chunk, List.getElem_take] using chunk_tdNode trapdoor l nodeIdx 29 j (by omega) (by omega))
  -- 190: LD x11, 24(x10); 191: SLLI x5, x11, 24; 192: SRLI x5, x5, 24
  have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
  have hx10_2 : s2.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff) := by
    rw [hreg2 .x10 (by decide) (by decide) (by decide) (by decide)]; exact hx10
  have haddr190 : s2.getReg .x10 + signExtend12 (24#12) =
      BitVec.ofNat 64 (4294971424 + (srcOff + 24)) := by
    rw [hx10_2, hse24, bv64_ofNat_add, Nat.add_assoc]
  set v3 := s2.getMem (BitVec.ofNat 64 (4294971424 + (srcOff + 24)))
  have h190 := step_LD (by omega) hpc2 (rfl : openingInstr 228 = .base (.LD .x11 .x10 (24#12)))
    (by rw [haddr190]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s3 := (s2.setReg .x11 v3).setPC (pcAt 229)
  have h190' : OpenRuns s2 1 1 s3 := by simpa only [haddr190, v3, s3] using h190
  have h191 := step_SLLI (by omega) (rfl : s3.pc = pcAt 229)
    (rfl : openingInstr 229 = .base (.SLLI .x5 .x11 (24#6)))
  let s4 := (s3.setReg .x5 (v3 <<< 24)).setPC (pcAt 230)
  have h191' : OpenRuns s3 1 1 s4 := by
    simpa only [show s3.getReg .x11 = v3 from rfl, show (24#6 : BitVec 6).toNat = 24 from rfl, s4] using h191
  have h192 := step_SRLI (by omega) (rfl : s4.pc = pcAt 230)
    (rfl : openingInstr 230 = .base (.SRLI .x5 .x5 (24#6)))
  let s5 := (s4.setReg .x5 ((v3 <<< 24) >>> 24)).setPC (pcAt 231)
  have h192' : OpenRuns s4 1 1 s5 := by
    simpa only [show s4.getReg .x5 = v3 <<< 24 from rfl, show (24#6 : BitVec 6).toNat = 24 from rfl, s5] using h192
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
    openRuns_emit_partial (base := 231) (m := 5) (immBits := 40#12)
      (fwdBytes := fwdBytes ++ c24) (chunkM := c5)
      (by omega) (by omega) (by omega) (by decide) (by decide)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl (by simp only [List.length_append, hc24_len]; omega) hro5 hw5 hc5_len hx5_5
  rw [hsplit] at hw6 hstP
  -- 204..214: push 6-bit tail
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
  -- 215: JALR x0, x1, 0
  have hx1_7 : s7.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hreg7 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg6 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s5, s4, s3, MachineState.getReg_setPC,
      getReg_setReg_ne' .x5 .x1 (by decide), getReg_setReg_ne' .x11 .x1 (by decide)]
    rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl
  have hret := step_JALR_x0 (by omega) hpc7 (rfl : openingInstr 253 = .base (.JALR .x0 .x1 (0#12))) hx1_7
  let s8 := s7.setPC (pcAt (callIdx + 1))
  have hlen24 : (fwdBytes ++ c24).length = fwdBytes.length + 24 := by simp [hc24_len]
  have hlen29 : (fwdBytes ++ bitsToBytes d 29).length = fwdBytes.length + 29 := by simp [bitsToBytes_length]
  dsimp only [chunk] at hstP
  have hpres8 : ∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
      r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x25 → s8.getReg r = s.getReg r :=
    fun r h1 h5 h6 h7 h11 h12 h13 h14 h15 h16 h17 h25 => by
      simp only [s8, MachineState.getReg_setPC]
      rw [hreg7 r h5 h6 h7 h15 h16 h17, hreg6 r h5 h6 h7 h12 h13 h14 h25]
      simp only [s5, s4, s3, MachineState.getReg_setPC,
        getReg_setReg_ne' .x5 r (Ne.symm h5), getReg_setReg_ne' .x11 r (Ne.symm h11)]
      rw [hreg2 r h5 h6 h12 h25]; exact getReg_setReg_ne' .x1 r (Ne.symm h1) s _
  have htot := ((((((hr_jal.trans hr_3d).trans h190').trans h191').trans h192').trans hrP).trans hrT).trans hret
  refine ⟨1 + 19 + 1 + 1 + 1 + stP + stT + 1, s8, htot, by omega, rfl, hpres8, hro7,
    ⟨hw7.rx25, hw7.rx13, hw7.rx14, hw7.wbufLo, hw7.wbufHi, hw7.memDwords⟩,
    ⟨ht7.rx31, ht7.rx15, ht7.rx16, ht7.rx17, ht7.memTail⟩,
    fun a ha => by
      simp only [s8, getByte_setPC]
      rw [hcap7 a ha, hcap6 a ha]
      simp only [s5, s4, s3, getByte_setPC, getByte_setReg]
      rw [hcap2 a ha]; rfl⟩

/-! ### 6. Entry and Epilogue Blocks (`0..30`, `148..171`) -/

private theorem opening_initial_regs (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    s0.pc = pcAt 0 ∧
    s0.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
    s0.getReg .x12 = BitVec.ofNat 64 4294971424 ∧
    s0.getReg .x13 = BitVec.ofNat 64 7449087968 ∧
    s0.getReg .x15 = BitVec.ofNat 64 11878272992 ∧
    s0.getReg .x16 = BitVec.ofNat 64 positions.card := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  change BitVec.ofNat 64 (dataBase (submission.image .opening)) = _
  rw [opening_dataBase]

private theorem openRuns_entry_prefix (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ s5, OpenRuns s0 5 5 s5 ∧
      s5.pc = pcAt 5 ∧
      s5.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s5.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s5.getReg .x24 = BitVec.ofNat 64 7449087968 ∧
      s5.getReg .x25 = BitVec.ofNat 64 11878272992 ∧
      s5.getReg .x26 = BitVec.ofNat 64 11878272992 ∧
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
  let s2 := (s1.setReg .x24 (BitVec.ofNat 64 7449087968)).setPC (pcAt 2)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hr : s1.getReg .x13 = BitVec.ofNat 64 7449087968 := hx13
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 2)
    (rfl : openingInstr 2 = .base (.ADDI .x25 .x15 (0#12)))
  let s3 := (s2.setReg .x25 (BitVec.ofNat 64 11878272992)).setPC (pcAt 3)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hr : s2.getReg .x15 = BitVec.ofNat 64 11878272992 := hx15
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s3] using h3
  have h4 := step_ADDI (by omega) (rfl : s3.pc = pcAt 3)
    (rfl : openingInstr 3 = .base (.ADDI .x26 .x15 (0#12)))
  let s4 := (s3.setReg .x26 (BitVec.ofNat 64 11878272992)).setPC (pcAt 4)
  have h4' : OpenRuns s3 1 1 s4 := by
    have hr : s3.getReg .x15 = BitVec.ofNat 64 11878272992 := hx15
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s4] using h4
  have h5 := step_ADDI (by omega) (rfl : s4.pc = pcAt 4)
    (rfl : openingInstr 4 = .base (.ADDI .x27 .x16 (0#12)))
  let s5 := (s4.setReg .x27 (BitVec.ofNat 64 positions.card)).setPC (pcAt 5)
  have h5' : OpenRuns s4 1 1 s5 := by
    have hr : s4.getReg .x16 = BitVec.ofNat 64 positions.card := hx16
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s5] using h5
  exact ⟨s5, (((h1'.trans h2').trans h3').trans h4').trans h5',
    rfl, hx2, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem openRuns_empty_epilogue {s : MachineState} (hpc : s.pc = pcAt 125) :
    ∃ sHalt, OpenRuns s 3 3 sHalt ∧
      sHalt.pc = pcAt 128 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = 0#64 ∧
      sHalt.mem = s.mem := by
  have h1 := step_ADDI (by omega) hpc (rfl : openingInstr 125 = .base (.ADDI .x11 .x0 (0#12)))
  let s1 := (s.setReg .x11 0#64).setPC (pcAt 126)
  have h1' : OpenRuns s 1 1 s1 := by
    have hv : s.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s1] using h1
  have h2 := step_ADDI (by omega) (rfl : s1.pc = pcAt 126)
    (rfl : openingInstr 126 = .base (.ADDI .x5 .x0 (1#12)))
  let s2 := (s1.setReg .x5 1#64).setPC (pcAt 127)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x0 + signExtend12 (1#12) = 1#64 := by
      change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 127)
    (rfl : openingInstr 127 = .base (.ADDI .x10 .x0 (0#12)))
  let s3 := (s2.setReg .x10 0#64).setPC (pcAt 128)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hv : s2.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s3] using h3
  exact ⟨s3, (h1'.trans h2').trans h3', rfl, rfl, rfl, rfl, rfl⟩

private theorem openRuns_entry_nonzero (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (hne : positions.card ≠ 0) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ s20, OpenRuns s0 20 20 s20 ∧
      s20.pc = pcAt 20 ∧
      s20.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s20.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s20.getReg .x12 = 0#64 ∧
      s20.getReg .x13 = 0#64 ∧
      s20.getReg .x14 = BitVec.ofNat 64 63 ∧
      s20.getReg .x15 = BitVec.ofNat 64 tailBufBase ∧
      s20.getReg .x16 = 0#64 ∧
      s20.getReg .x17 = 0#64 ∧
      s20.getReg .x18 = BitVec.ofNat 64 (4294971424 + (rowOff + 72)) ∧
      s20.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s20.getReg .x24 = BitVec.ofNat 64 7449087968 ∧
      s20.getReg .x25 = BitVec.ofNat 64 11878272992 ∧
      s20.getReg .x26 = BitVec.ofNat 64 11878272992 ∧
      s20.getReg .x27 = BitVec.ofNat 64 positions.card ∧
      s20.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
      s20.mem = s0.mem := by
  intro s0
  obtain ⟨s5, hr5, hpc5, hx2, hx9, hx24, hx25, hx26, hx27, hmem5⟩ :=
    openRuns_entry_prefix trapdoor positions
  have hcard := positions_card_le positions
  have h6 := step_BEQ_not_taken (by omega) hpc5
    (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (480#13)))
    (by rw [hx27]; exact bv64_ofNat_ne (by omega) (by decide) hne)
  let s6 := s5.setPC (pcAt 6)
  -- 6..13: writer & tail-packer init
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
    (rfl : openingInstr 9 = .base (.ADDI .x31 .x0 (3#12)))
  let s10 := (s9.setReg .x31 (BitVec.ofNat 64 3)).setPC (pcAt 10)
  have h10' : OpenRuns s9 1 1 s10 := by
    have hv : s9.getReg .x0 + signExtend12 (3#12) = BitVec.ofNat 64 3 := by
      change (0#64 : Word) + signExtend12 (3#12) = BitVec.ofNat 64 3; decide
    simpa only [hv, s10] using h10
  have h11 := step_SLLI (by omega) (rfl : s10.pc = pcAt 10)
    (rfl : openingInstr 10 = .base (.SLLI .x31 .x31 (33#6)))
  let s11 := (s10.setReg .x31 (BitVec.ofNat 64 tailBufBase)).setPC (pcAt 11)
  have h11' : OpenRuns s10 1 1 s11 := by
    have hv : s10.getReg .x31 <<< (33#6 : BitVec 6).toNat = BitVec.ofNat 64 tailBufBase := by
      change BitVec.ofNat 64 3 <<< (33#6 : BitVec 6).toNat = BitVec.ofNat 64 25769803776; decide
    simpa only [hv, s11] using h11
  have h12 := step_ADDI (by omega) (rfl : s11.pc = pcAt 11)
    (rfl : openingInstr 11 = .base (.ADDI .x15 .x31 (0#12)))
  let s12 := (s11.setReg .x15 (BitVec.ofNat 64 tailBufBase)).setPC (pcAt 12)
  have h12' : OpenRuns s11 1 1 s12 := by
    have hv : s11.getReg .x31 + signExtend12 (0#12) = BitVec.ofNat 64 tailBufBase := by
      change BitVec.ofNat 64 25769803776 + signExtend12 (0#12) = BitVec.ofNat 64 25769803776; decide
    simpa only [hv, s12] using h12
  have h13 := step_ADDI (by omega) (rfl : s12.pc = pcAt 12)
    (rfl : openingInstr 12 = .base (.ADDI .x16 .x0 (0#12)))
  let s13 := (s12.setReg .x16 0#64).setPC (pcAt 13)
  have h13' : OpenRuns s12 1 1 s13 := by
    have hv : s12.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s13] using h13
  have h14 := step_ADDI (by omega) (rfl : s13.pc = pcAt 13)
    (rfl : openingInstr 13 = .base (.ADDI .x17 .x0 (0#12)))
  let s14 := (s13.setReg .x17 0#64).setPC (pcAt 14)
  have h14' : OpenRuns s13 1 1 s14 := by
    have hv : s13.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s14] using h14
  -- 14..19: salt base x18 = C_TD + rowOff + 72, capMarkBase x21 = 4096
  have h15 := step_ADDI (by omega) (rfl : s14.pc = pcAt 14)
    (rfl : openingInstr 14 = .base (.ADDI .x6 .x0 (1536#12)))
  let s15 := (s14.setReg .x6 (BitVec.ofNat 64 1536)).setPC (pcAt 15)
  have h15' : OpenRuns s14 1 1 s15 := by
    have hv : s14.getReg .x0 + signExtend12 (1536#12) = BitVec.ofNat 64 1536 := by
      change (0#64 : Word) + signExtend12 (1536#12) = BitVec.ofNat 64 1536; decide
    simpa only [hv, s15] using h15
  have h16 := step_SLLI (by omega) (rfl : s15.pc = pcAt 15)
    (rfl : openingInstr 15 = .base (.SLLI .x6 .x6 (20#6)))
  let s16 := (s15.setReg .x6 (BitVec.ofNat 64 1610612736)).setPC (pcAt 16)
  have h16' : OpenRuns s15 1 1 s16 := by
    have hv : s15.getReg .x6 <<< (20#6 : BitVec 6).toNat = BitVec.ofNat 64 1610612736 := by
      change BitVec.ofNat 64 1536 <<< (20#6 : BitVec 6).toNat = BitVec.ofNat 64 1610612736; decide
    simpa only [hv, s16] using h16
  have h17 := step_ADDI (by omega) (rfl : s16.pc = pcAt 16)
    (rfl : openingInstr 16 = .base (.ADDI .x6 .x6 (8#12)))
  let s17 := (s16.setReg .x6 (BitVec.ofNat 64 (rowOff + 72))).setPC (pcAt 17)
  have h17' : OpenRuns s16 1 1 s17 := by
    have hv : s16.getReg .x6 + signExtend12 (8#12) = BitVec.ofNat 64 (rowOff + 72) := by
      change BitVec.ofNat 64 1610612736 + signExtend12 (8#12) = BitVec.ofNat 64 (rowOff + 72)
      rw [rowOff_eq]; decide
    simpa only [hv, s17] using h17
  have h18 := step_ADD (by omega) (rfl : s17.pc = pcAt 17)
    (rfl : openingInstr 17 = .base (.ADD .x18 .x9 .x6))
  let s18 := (s17.setReg .x18 (BitVec.ofNat 64 (4294971424 + (rowOff + 72)))).setPC (pcAt 18)
  have h18' : OpenRuns s17 1 1 s18 := by
    have hr9 : s17.getReg .x9 = BitVec.ofNat 64 4294971424 := hx9
    simpa only [hr9, show s17.getReg .x6 = BitVec.ofNat 64 (rowOff + 72) from rfl, bv64_ofNat_add, s18] using h18
  have h19 := step_ADDI (by omega) (rfl : s18.pc = pcAt 18)
    (rfl : openingInstr 18 = .base (.ADDI .x21 .x0 (2#12)))
  let s19 := (s18.setReg .x21 (BitVec.ofNat 64 2)).setPC (pcAt 19)
  have h19' : OpenRuns s18 1 1 s19 := by
    have hv : s18.getReg .x0 + signExtend12 (2#12) = BitVec.ofNat 64 2 := by
      change (0#64 : Word) + signExtend12 (2#12) = BitVec.ofNat 64 2; decide
    simpa only [hv, s19] using h19
  have h20 := step_SLLI (by omega) (rfl : s19.pc = pcAt 19)
    (rfl : openingInstr 19 = .base (.SLLI .x21 .x21 (11#6)))
  let s20 := (s19.setReg .x21 (BitVec.ofNat 64 4096)).setPC (pcAt 20)
  have h20' : OpenRuns s19 1 1 s20 := by
    have hv : s19.getReg .x21 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096 := by
      change BitVec.ofNat 64 2 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096; decide
    simpa only [hv, s20] using h20
  have ha := ((((((hr5.trans h6).trans h7').trans h8').trans h9').trans h10').trans h11').trans h12'
  have hb := ((((((ha.trans h13').trans h14').trans h15').trans h16').trans h17').trans h18').trans h19'
  have htot := hb.trans h20'
  exact ⟨s20, htot, rfl, hx2, hx9, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx24, hx25,
    hx26, hx27, rfl, hmem5⟩

private theorem openRuns_flush_wbuf {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    (hpc : s.pc = pcAt 105)
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11878272992)
    (hfbd : fwdBytes.length ≤ 8476692192)
    (htbd : tails.length ≤ 300000000)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 37 ∧
      s'.pc = pcAt 112 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (11878272992 + fwdBytes.length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 11878272992 ∧
      ProofPrefix s' fwdBytes ∧
      TailState s' tails := by
  set q := fwdBytes.length / 8
  set r := fwdBytes.length % 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  -- 93: ADDI x10, x25, 0
  have h93 := step_ADDI (by omega) hpc (rfl : openingInstr 105 = .base (.ADDI .x10 .x25 (0#12)))
  let s1 := (s.setReg .x10 (BitVec.ofNat 64 (11878272992 + 8 * q))).setPC (pcAt 106)
  have h93' : OpenRuns s 1 1 s1 := by
    rw [hw.rx25, hse0, bv64_ofNat_add, Nat.add_zero] at h93; exact h93
  by_cases hr0 : r = 0
  · have h94 := step_BEQ_taken (by omega) (rfl : s1.pc = pcAt 106)
      (rfl : openingInstr 106 = .base (.BEQ .x13 .x0 (24#13)))
      (by have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13; rw [h, hr0]; rfl)
      (by decide : pcAt 106 + signExtend13 (24#13) = pcAt 112)
    let s2 := s1.setPC (pcAt 112)
    refine ⟨2, s2, h93'.trans h94, by omega, rfl, ?_, hx26, ?_,
      ⟨ht.rx31, ht.rx15, ht.rx16, ht.rx17, ht.memTail⟩⟩
    · change BitVec.ofNat 64 (11878272992 + 8 * q) = _
      congr 1; omega
    · intro j hj
      exact hw.memDwords j (by omega)
  · have hrpos : 0 < r := by omega
    have h94 := step_BEQ_not_taken (by omega) (rfl : s1.pc = pcAt 106)
      (rfl : openingInstr 106 = .base (.BEQ .x13 .x0 (24#13)))
      (by have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13
          rw [h]; exact bv64_ofNat_ne (by omega) (by decide) (by omega))
    let s2 := s1.setPC (pcAt 107)
    have hloop : ∀ k (hk : k ≤ r), ∃ sk, OpenRuns s2 (5 * k) (5 * k) sk ∧
        sk.pc = (if k < r then pcAt 107 else pcAt 112) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (11878272992 + 8 * q + k) ∧
        sk.getReg .x13 = BitVec.ofNat 64 (8 * (r - k)) ∧
        sk.getReg .x26 = BitVec.ofNat 64 11878272992 ∧
        (∀ j (hj : j < r - k), (sk.getReg .x12).extractLsb' (8 * j) 8 = fwdBytes[8 * q + k + j]'(by omega)) ∧
        (∀ j (hj : j < 8 * q + k), sk.getByte (BitVec.ofNat 64 (11878272992 + j)) = fwdBytes[j]'(by omega)) ∧
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
        have hpck' : sk.pc = pcAt 107 := by simpa only [show k < r by omega, ite_true] using hpck
        -- 95: SB x10, x12, 0
        have haddr : sk.getReg .x10 + signExtend12 (0#12) = BitVec.ofNat 64 (11878272992 + 8 * q + k) := by
          rw [hx10k, hse0, bv64_ofNat_add, Nat.add_zero]
        have ha := step_SB (by omega) hpck' (rfl : openingInstr 107 = .base (.SB .x10 .x12 (0#12)))
          (by rw [haddr]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        have hbyte0 : (sk.getReg .x12).truncate 8 = fwdBytes[8 * q + k]'(by omega) := by
          rw [word_truncate8_eq_extractLsb'0]
          simpa using hwLoK 0 (by omega)
        let sa := (sk.setByte (BitVec.ofNat 64 (11878272992 + 8 * q + k))
          (fwdBytes[8 * q + k]'(by omega))).setPC (pcAt 108)
        have ha' : OpenRuns sk 1 1 sa := by simpa only [haddr, hbyte0, sa] using ha
        -- 96: ADDI x10, x10, 1
        have hb := step_ADDI (by omega) (rfl : sa.pc = pcAt 108)
          (rfl : openingInstr 108 = .base (.ADDI .x10 .x10 (1#12)))
        let sb := (sa.setReg .x10 (BitVec.ofNat 64 (11878272992 + 8 * q + (k + 1)))).setPC (pcAt 109)
        have hb' : OpenRuns sa 1 1 sb := by
          have hr10 : sa.getReg .x10 = BitVec.ofNat 64 (11878272992 + 8 * q + k) := by
            simp only [sa, MachineState.getReg_setPC, getReg_setByte]; exact hx10k
          rw [hr10, hse1, bv64_ofNat_add, Nat.add_assoc] at hb; exact hb
        -- 97: SRLI x12, x12, 8
        have hc := step_SRLI (by omega) (rfl : sb.pc = pcAt 109)
          (rfl : openingInstr 109 = .base (.SRLI .x12 .x12 (8#6)))
        let sc := (sb.setReg .x12 (sk.getReg .x12 >>> 8)).setPC (pcAt 110)
        have hc' : OpenRuns sb 1 1 sc := by
          have hr12 : sb.getReg .x12 = sk.getReg .x12 := by
            simp only [sb, sa, MachineState.getReg_setPC, getReg_setByte,
              getReg_setReg_ne' .x10 .x12 (by decide)]
          simpa only [hr12, show (8#6 : BitVec 6).toNat = 8 from rfl, sc] using hc
        -- 98: ADDI x13, x13, 4088 (-8)
        have hd := step_ADDI (by omega) (rfl : sc.pc = pcAt 110)
          (rfl : openingInstr 110 = .base (.ADDI .x13 .x13 (4088#12)))
        let sd := (sc.setReg .x13 (BitVec.ofNat 64 (8 * (r - (k + 1))))).setPC (pcAt 111)
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
            sd.getByte (BitVec.ofNat 64 (11878272992 + j)) = fwdBytes[j]'(by omega) := by
          intro j hj
          simp only [sd, sc, sb, sa, getByte_setPC, getByte_setReg, set_byte_read]
          by_cases hlast : j = 8 * q + k
          · subst hlast
            rw [show 11878272992 + (8 * q + k) = 11878272992 + 8 * q + k by omega, if_pos rfl]
          · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
            exact hmemk j (by omega)
        have htd : TailState sd tails := by
          have htb : tailBufBase = 25769803776 := rfl
          have ht' := tailState_setByte_outside (11878272992 + 8 * q + k)
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
        have hx10_d : sd.getReg .x10 = BitVec.ofNat 64 (11878272992 + 8 * q + (k + 1)) := by
          simp only [sd, sc, sb, MachineState.getReg_setPC,
            getReg_setReg_ne' .x13 .x10 (by decide), getReg_setReg_ne' .x12 .x10 (by decide)]; rfl
        have hx26_d : sd.getReg .x26 = BitVec.ofNat 64 11878272992 := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x13 .x26 (by decide), getReg_setReg_ne' .x12 .x26 (by decide),
            getReg_setReg_ne' .x10 .x26 (by decide)]; exact hx26k
        -- 99: BNE x13, x0, 8176 (-16 -> 95)
        by_cases hmore : k + 1 < r
        · have he := step_BNE_taken (by omega) (rfl : sd.pc = pcAt 111)
            (rfl : openingInstr 111 = .base (.BNE .x13 .x0 (8176#13)))
            (by change BitVec.ofNat 64 (8 * (r - (k + 1))) ≠ BitVec.ofNat 64 0
                exact bv64_ofNat_ne (by omega) (by decide) (by omega))
            (by decide : pcAt 111 + signExtend13 (8176#13) = pcAt 107)
          exact ⟨sd.setPC (pcAt 107), by simpa only [Nat.mul_succ] using (hrk.trans hstep4).trans he,
            by rw [if_pos hmore]; rfl, hx10_d, rfl, hx26_d, hwLo_d, hmem_d, htd.of_eq⟩
        · have hdone : r - (k + 1) = 0 := by omega
          have he := step_BNE_not_taken (by omega) (rfl : sd.pc = pcAt 111)
            (rfl : openingInstr 111 = .base (.BNE .x13 .x0 (8176#13)))
            (by change BitVec.ofNat 64 (8 * (r - (k + 1))) = 0#64; rw [hdone])
          exact ⟨sd.setPC (pcAt 112), by simpa only [Nat.mul_succ] using (hrk.trans hstep4).trans he,
            by rw [if_neg hmore]; rfl, hx10_d, rfl, hx26_d, hwLo_d, hmem_d, htd.of_eq⟩
    obtain ⟨sf, hrf, hpcf, hx10f, _, hx26f, _, hmemf, htf⟩ := hloop r (Nat.le_refl r)
    have hpcf' : sf.pc = pcAt 112 := by simpa only [Nat.lt_irrefl, ite_false] using hpcf
    refine ⟨2 + 5 * r, sf, (h93'.trans h94).trans hrf, by omega, hpcf',
      by rw [hx10f]; congr 1; omega, hx26f,
      fun j hj => hmemf j (by omega), htf⟩

private theorem openRuns_flush_tail {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    (hpc : s.pc = pcAt 112)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (11878272992 + fwdBytes.length))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11878272992)
    (hfbd : fwdBytes.length ≤ 8476692192)
    (htbd : tails.length ≤ 300000000)
    (hpr : ProofPrefix s fwdBytes)
    (ht : TailState s tails) :
    let packed := pack6Bits tails
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 3 ∧
      s'.pc = pcAt 115 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (11878272992 + fwdBytes.length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 11878272992 ∧
      s'.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
      s'.getReg .x15 = BitVec.ofNat 64 (tailBufBase + packed.length) ∧
      ProofPrefix s' fwdBytes ∧
      TailBufPrefix s' packed := by
  intro packed
  have htb : tailBufBase = 25769803776 := rfl
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
  · have h100 := step_BEQ_taken (by omega) hpc
      (rfl : openingInstr 112 = .base (.BEQ .x17 .x0 (12#13)))
      (by rw [ht.rx17]; exact congrArg (BitVec.ofNat 64) hcnt0)
      (by decide : pcAt 112 + signExtend13 (12#13) = pcAt 115)
    have hpack_eq : packed = acc := by
      unfold packed pack6Bits pack6Finish
      change (if 0 < tCnt then _ else acc) = acc
      rw [if_neg (by omega)]
    rw [hpack_eq]
    exact ⟨1, s.setPC (pcAt 115), h100, by omega, rfl, hx10, hx26, ht.rx31, ht.rx15, hpr, ht.memTail⟩
  · have hpos : 0 < tCnt := by omega
    have hpack_eq : packed = acc ++ [BitVec.ofNat 8 tBuf] := by
      unfold packed pack6Bits pack6Finish
      change (if 0 < tCnt then acc ++ [BitVec.ofNat 8 tBuf] else acc) = _
      rw [if_pos hpos]
    have h100 := step_BEQ_not_taken (by omega) hpc
      (rfl : openingInstr 112 = .base (.BEQ .x17 .x0 (12#13)))
      (by rw [ht.rx17]; exact bv64_ofNat_ne (by omega) (by decide) hcnt0)
    let s1 := s.setPC (pcAt 113)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have haddr : s1.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + acc.length) := by
      have hr15 : s1.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := ht.rx15
      rw [hr15, hse0, bv64_ofNat_add, Nat.add_zero]
    have h101 := step_SB (by omega) (rfl : s1.pc = pcAt 113)
      (rfl : openingInstr 113 = .base (.SB .x15 .x16 (0#12)))
      (by rw [haddr]; exact accessValid_ofNat _ 1 (by omega) (by omega))
    let s2 := (s1.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 tBuf)).setPC (pcAt 114)
    have h101' : OpenRuns s1 1 1 s2 := by
      have htr : (s1.getReg .x16).truncate 8 = BitVec.ofNat 8 tBuf := by
        have hr16 : s1.getReg .x16 = BitVec.ofNat 64 tBuf := ht.rx16
        rw [hr16]; exact bv64_ofNat_truncate8 tBuf (by omega)
      simpa only [haddr, htr, s2] using h101
    have h102 := step_ADDI (by omega) (rfl : s2.pc = pcAt 114)
      (rfl : openingInstr 114 = .base (.ADDI .x15 .x15 (1#12)))
    let s3 := (s2.setReg .x15 (BitVec.ofNat 64 (tailBufBase + packed.length))).setPC (pcAt 115)
    have h102' : OpenRuns s2 1 1 s3 := by
      have hr15 : s2.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := by
        simp only [s2, MachineState.getReg_setPC, getReg_setByte]; exact ht.rx15
      have hv : s2.getReg .x15 + signExtend12 (1#12) = BitVec.ofNat 64 (tailBufBase + packed.length) := by
        rw [hr15, hse1, bv64_ofNat_add, hpack_eq, List.length_append, List.length_singleton, Nat.add_assoc]
      simpa only [hv, s3] using h102
    refine ⟨3, s3, (h100.trans h101').trans h102', Nat.le_refl 3, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
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
    (hpc : s.pc = pcAt 115)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (11878272992 + fwdBytes.length))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11878272992)
    (hx31 : s.getReg .x31 = BitVec.ofNat 64 tailBufBase)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + packed.length))
    (hbd : fwdBytes.length + packed.length ≤ 8476692192)
    (hpr : ProofPrefix s fwdBytes)
    (htail : TailBufPrefix s packed) :
    ∃ s', OpenRuns s (1 + 5 * packed.length) (1 + 5 * packed.length) s' ∧
      s'.pc = pcAt 121 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (11878272992 + (fwdBytes ++ packed.reverse).length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 11878272992 ∧
      ProofPrefix s' (fwdBytes ++ packed.reverse) := by
  have htb : tailBufBase = 25769803776 := rfl
  set m := packed.length
  by_cases hm0 : m = 0
  · have hnil : packed = [] := List.eq_nil_of_length_eq_zero hm0
    have h103 := step_BEQ_taken (by omega) hpc
      (rfl : openingInstr 115 = .base (.BEQ .x15 .x31 (24#13)))
      (by rw [hx15, hx31, hm0, Nat.add_zero])
      (by decide : pcAt 115 + signExtend13 (24#13) = pcAt 121)
    subst hnil
    exact ⟨s.setPC (pcAt 121),
      by rw [hm0, Nat.mul_zero, Nat.add_zero]; exact h103,
      rfl,
      by rw [List.reverse_nil, List.append_nil]; exact hx10,
      hx26,
      by rw [List.reverse_nil, List.append_nil]; exact hpr⟩
  · have hmpos : 0 < m := by omega
    have h103 := step_BEQ_not_taken (by omega) hpc
      (rfl : openingInstr 115 = .base (.BEQ .x15 .x31 (24#13)))
      (by rw [hx15, hx31]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
    let s1 := s.setPC (pcAt 116)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have hloop : ∀ u ≤ m, ∃ su, OpenRuns s1 (5 * u) (5 * u) su ∧
        su.pc = (if u < m then pcAt 116 else pcAt 121) ∧
        su.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (m - u)) ∧
        su.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
        su.getReg .x10 = BitVec.ofNat 64 (11878272992 + fwdBytes.length + u) ∧
        su.getReg .x26 = BitVec.ofNat 64 11878272992 ∧
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
        have hpcu' : su.pc = pcAt 116 := by simpa only [show u < m by omega, ite_true] using hpcu
        -- 104: ADDI x15, x15, 4095 (-1)
        have ha := step_ADDI (by omega) hpcu' (rfl : openingInstr 116 = .base (.ADDI .x15 .x15 (4095#12)))
        let sa := (su.setReg .x15 (BitVec.ofNat 64 (tailBufBase + (m - (u + 1))))).setPC (pcAt 117)
        have ha' : OpenRuns su 1 1 sa := by
          have hr15 : su.getReg .x15 = BitVec.ofNat 64 ((tailBufBase + (m - (u + 1))) + 1) := by
            rw [hx15u]; congr 1; omega
          rw [hr15, bv64_add_neg1] at ha; exact ha
        -- 105: LBU x6, 0(x15)
        have haddr6 : sa.getReg .x15 + signExtend12 (0#12) =
            BitVec.ofNat 64 (tailBufBase + (m - (u + 1))) := by
          change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
        have hb := step_LBU (by omega) (rfl : sa.pc = pcAt 117)
          (rfl : openingInstr 117 = .base (.LBU .x6 .x15 (0#12)))
          (by rw [haddr6]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        set bCur := packed[m - (u + 1)]'(by omega)
        let sb := (sa.setReg .x6 (bCur.zeroExtend 64)).setPC (pcAt 118)
        have hb' : OpenRuns sa 1 1 sb := by
          have hget : sa.getByte (BitVec.ofNat 64 (tailBufBase + (m - (u + 1)))) = bCur :=
            htailu (m - (u + 1)) (by omega)
          simpa only [haddr6, hget, sb] using hb
        -- 106: SB x10, x6, 0
        have haddr10 : sb.getReg .x10 + signExtend12 (0#12) =
            BitVec.ofNat 64 (11878272992 + fwdBytes.length + u) := by
          have hr10 : sb.getReg .x10 = BitVec.ofNat 64 (11878272992 + fwdBytes.length + u) := hx10u
          rw [hr10, hse0, bv64_ofNat_add, Nat.add_zero]
        have hc := step_SB (by omega) (rfl : sb.pc = pcAt 118)
          (rfl : openingInstr 118 = .base (.SB .x10 .x6 (0#12)))
          (by rw [haddr10]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        let sc := (sb.setByte (BitVec.ofNat 64 (11878272992 + fwdBytes.length + u)) bCur).setPC (pcAt 119)
        have hc' : OpenRuns sb 1 1 sc := by
          have htr : (sb.getReg .x6).truncate 8 = bCur := byte_zeroExtend_truncate8 bCur
          simpa only [haddr10, htr, sc] using hc
        -- 107: ADDI x10, x10, 1
        have hd := step_ADDI (by omega) (rfl : sc.pc = pcAt 119)
          (rfl : openingInstr 119 = .base (.ADDI .x10 .x10 (1#12)))
        let sd := (sc.setReg .x10 (BitVec.ofNat 64 (11878272992 + fwdBytes.length + (u + 1)))).setPC (pcAt 120)
        have hd' : OpenRuns sc 1 1 sd := by
          have hr10 : sc.getReg .x10 = BitVec.ofNat 64 (11878272992 + fwdBytes.length + u) := by
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
        have hx26_d : sd.getReg .x26 = BitVec.ofNat 64 11878272992 := by
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
            rw [show 11878272992 + (fwdBytes.length + u) = 11878272992 + fwdBytes.length + u by omega,
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
        -- 108: BNE x15, x31, 8176 (-16 -> 104)
        by_cases hmore : u + 1 < m
        · have he := step_BNE_taken (by omega) (rfl : sd.pc = pcAt 120)
            (rfl : openingInstr 120 = .base (.BNE .x15 .x31 (8176#13)))
            (by rw [hx15_d, hx31_d]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
            (by decide : pcAt 120 + signExtend13 (8176#13) = pcAt 116)
          exact ⟨sd.setPC (pcAt 116), by simpa only [Nat.mul_succ] using (hru.trans hstep4).trans he,
            by rw [if_pos hmore]; rfl, hx15_d, hx31_d, rfl, hx26_d, hpr_d, htail_d⟩
        · have hdone : m - (u + 1) = 0 := by omega
          have he := step_BNE_not_taken (by omega) (rfl : sd.pc = pcAt 120)
            (rfl : openingInstr 120 = .base (.BNE .x15 .x31 (8176#13)))
            (by rw [hx15_d, hx31_d, hdone, Nat.add_zero])
          exact ⟨sd.setPC (pcAt 121), by simpa only [Nat.mul_succ] using (hru.trans hstep4).trans he,
            by rw [if_neg hmore]; rfl, hx15_d, hx31_d, rfl, hx26_d, hpr_d, htail_d⟩
    obtain ⟨sf, hrf, hpcf, _, _, hx10f, hx26f, hprf, _⟩ := hloop m (Nat.le_refl m)
    have hpcf' : sf.pc = pcAt 121 := by simpa only [Nat.lt_irrefl, ite_false] using hpcf
    have htakeAll : packed.reverse.take m = packed.reverse := by
      rw [show m = packed.reverse.length by simp [m], List.take_length]
    rw [htakeAll] at hprf
    refine ⟨sf, h103.trans hrf, hpcf', ?_, hx26f, hprf⟩
    rw [hx10f]; congr 1; simp [m]; omega

private theorem openRuns_finish {s : MachineState} {proofLen : Nat}
    (hpc : s.pc = pcAt 121)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (11878272992 + proofLen))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11878272992) :
    ∃ sHalt, OpenRuns s 3 3 sHalt ∧
      sHalt.pc = pcAt 124 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = BitVec.ofNat 64 proofLen ∧
      sHalt.mem = s.mem := by
  have h1 := step_SUB (by omega) hpc (rfl : openingInstr 121 = .base (.SUB .x11 .x10 .x26))
  have hsub : s.getReg .x10 - s.getReg .x26 = BitVec.ofNat 64 proofLen := by
    rw [hx10, hx26, bv64_ofNat_sub _ _ (by omega), Nat.add_sub_cancel_left]
  let s1 := (s.setReg .x11 (BitVec.ofNat 64 proofLen)).setPC (pcAt 122)
  have h1' : OpenRuns s 1 1 s1 := by simpa only [hsub, s1] using h1
  have h2 := step_ADDI (by omega) (rfl : s1.pc = pcAt 122)
    (rfl : openingInstr 122 = .base (.ADDI .x5 .x0 (1#12)))
  let s2 := (s1.setReg .x5 1#64).setPC (pcAt 123)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x0 + signExtend12 (1#12) = 1#64 := by
      change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 123)
    (rfl : openingInstr 123 = .base (.ADDI .x10 .x0 (0#12)))
  let s3 := (s2.setReg .x10 0#64).setPC (pcAt 124)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hv : s2.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s3] using h3
  exact ⟨s3, (h1'.trans h2').trans h3', rfl, rfl, rfl, rfl, rfl⟩


/-! ### 7. Record Loop (`20..62`) -/

private def capLeafNat (i : Nat) : Nat := i >>> 16

private def capMark16Prefix (positions : Positions) (t idx : Nat) : Bool :=
  decide (∃ u < t, capLeafNat (openingIndex positions u) = idx)

private theorem capMark16Prefix_card (positions : Positions) (idx : Nat) :
    capMark16Prefix positions positions.card idx = capMark positions 16 idx := by
  simp only [capMark16Prefix, capMark_16]
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

/-- Loop invariant preserved across the record-loop body (`20..62`). -/
private structure RecInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (t : Nat) (fwdBytes : List Byte) (tails : List (BitVec 6))
    (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475936
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + (rowOff + 72))
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx24 : s.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * t)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 11878272992
  rx27 : s.getReg .x27 = BitVec.ofNat 64 (positions.card - t)
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  writer : WriterState s fwdBytes
  tail : TailState s tails
  cap16 : ∀ c < 256, s.getByte (BitVec.ofNat 64 (4096 + c)) =
    if capMark16Prefix positions t c then 1#8 else 0#8

private theorem RecInv.setPC {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState} (inv : RecInv trapdoor positions t fwdBytes tails s) (pc : Word) :
    RecInv trapdoor positions t fwdBytes tails (s.setPC pc) :=
  ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
   inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap16⟩

private theorem RecInv.after_sub {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes fwdBytes' : List Byte}
    {tails tails' : List (BitVec 6)} {s s' : MachineState}
    (inv : RecInv trapdoor positions t fwdBytes tails s)
    (hreg : ∀ r, r = .x2 ∨ r = .x9 ∨ r = .x18 ∨ r = .x21 ∨
      r = .x24 ∨ r = .x26 ∨ r = .x27 → s'.getReg r = s.getReg r)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s')
    (hw : WriterState s' fwdBytes')
    (ht : TailState s' tails')
    (hcap : ∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) :
    RecInv trapdoor positions t fwdBytes' tails' s' :=
  ⟨by rw [hreg .x2 (by simp)]; exact inv.rx2,
   by rw [hreg .x9 (by simp)]; exact inv.rx9,
   by rw [hreg .x18 (by simp)]; exact inv.rx18,
   by rw [hreg .x21 (by simp)]; exact inv.rx21,
   by rw [hreg .x24 (by simp)]; exact inv.rx24,
   by rw [hreg .x26 (by simp)]; exact inv.rx26,
   by rw [hreg .x27 (by simp)]; exact inv.rx27,
   hro, hw, ht,
   fun c hc => by rw [hcap (4096 + c) (by omega)]; exact inv.cap16 c hc⟩

private theorem openRuns_rec_salt {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (ht : t < positions.card) (hpc : s.pc = pcAt 20)
    (hbd : fwdBytes.length + 24 ≤ 8476692192)
    (htbd : tails.length ≤ 300000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let idx : Index := (positions.sort (· ≤ ·))[t]'(by simpa using ht)
    let fwd1 := fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24
    ∃ s1, OpenRuns s 32 32 s1 ∧
      s1.pc = pcAt 32 ∧
      s1.getReg .x22 = BitVec.ofNat 64 idx.val ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro idx fwd1
  have hcard := positions_card_le positions
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hopen : openingIndex positions t = idx.val := by simp only [openingIndex, dif_pos ht]; rfl
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have haddr20 : s.getReg .x24 + signExtend12 (0#12) = BitVec.ofNat 64 (7449087968 + 8 * t) := by
    rw [inv.rx24, hse0, bv64_ofNat_add, Nat.add_zero]
  have h20 := step_LD (by omega) hpc (rfl : openingInstr 20 = .base (.LD .x22 .x24 (0#12)))
    (by rw [haddr20]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s21 := (s.setReg .x22 (BitVec.ofNat 64 idx.val)).setPC (pcAt 21)
  have h20' : OpenRuns s 1 1 s21 := by
    have hmem := readOnly_getMem_index inv.ro t ht
    rw [hopen] at hmem
    simpa only [haddr20, hmem, s21] using h20
  have h21 := step_SRLI (by omega) (rfl : s21.pc = pcAt 21)
    (rfl : openingInstr 21 = .base (.SRLI .x6 .x22 (1#6)))
  let s22 := (s21.setReg .x6 (BitVec.ofNat 64 (idx.val / 2))).setPC (pcAt 22)
  have h21' : OpenRuns s21 1 1 s22 := by
    have hv : s21.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (idx.val / 2) := by
      change BitVec.ofNat 64 idx.val >>> 1 = _
      rw [bv64_ushr idx.val 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s22] using h21
  have h22 := step_SLLI (by omega) (rfl : s22.pc = pcAt 22)
    (rfl : openingInstr 22 = .base (.SLLI .x7 .x6 (7#6)))
  let s23 := (s22.setReg .x7 (BitVec.ofNat 64 (128 * (idx.val / 2)))).setPC (pcAt 23)
  have h22' : OpenRuns s22 1 1 s23 := by
    have hv : s22.getReg .x6 <<< (7#6 : BitVec 6).toNat = BitVec.ofNat 64 (128 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (idx.val / 2) <<< 7 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hv, s23] using h22
  have h23 := step_SLLI (by omega) (rfl : s23.pc = pcAt 23)
    (rfl : openingInstr 23 = .base (.SLLI .x10 .x6 (6#6)))
  let s24 := (s23.setReg .x10 (BitVec.ofNat 64 (64 * (idx.val / 2)))).setPC (pcAt 24)
  have h23' : OpenRuns s23 1 1 s24 := by
    have hv : s23.getReg .x6 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (idx.val / 2) <<< 6 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hv, s24] using h23
  have h24 := step_ADD (by omega) (rfl : s24.pc = pcAt 24)
    (rfl : openingInstr 24 = .base (.ADD .x7 .x7 .x10))
  let s25 := (s24.setReg .x7 (BitVec.ofNat 64 (192 * (idx.val / 2)))).setPC (pcAt 25)
  have h24' : OpenRuns s24 1 1 s25 := by
    have hv : s24.getReg .x7 + s24.getReg .x10 = BitVec.ofNat 64 (192 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (128 * (idx.val / 2)) + BitVec.ofNat 64 (64 * (idx.val / 2)) = _
      rw [bv64_ofNat_add]; congr 1; omega
    simpa only [hv, s25] using h24
  have h25 := step_SLLI (by omega) (rfl : s25.pc = pcAt 25)
    (rfl : openingInstr 25 = .base (.SLLI .x10 .x6 (3#6)))
  let s26 := (s25.setReg .x10 (BitVec.ofNat 64 (8 * (idx.val / 2)))).setPC (pcAt 26)
  have h25' : OpenRuns s25 1 1 s26 := by
    have hv : s25.getReg .x6 <<< (3#6 : BitVec 6).toNat = BitVec.ofNat 64 (8 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (idx.val / 2) <<< 3 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hv, s26] using h25
  have h26 := step_SUB (by omega) (rfl : s26.pc = pcAt 26)
    (rfl : openingInstr 26 = .base (.SUB .x7 .x7 .x10))
  let s27 := (s26.setReg .x7 (BitVec.ofNat 64 (184 * (idx.val / 2)))).setPC (pcAt 27)
  have h26' : OpenRuns s26 1 1 s27 := by
    have hv : s26.getReg .x7 - s26.getReg .x10 = BitVec.ofNat 64 (184 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (192 * (idx.val / 2)) - BitVec.ofNat 64 (8 * (idx.val / 2)) = _
      rw [bv64_ofNat_sub _ _ (by omega)]; congr 1; omega
    simpa only [hv, s27] using h26
  have h27 := step_ANDI (by omega) (rfl : s27.pc = pcAt 27)
    (rfl : openingInstr 27 = .base (.ANDI .x6 .x22 (1#12)))
  let s28 := (s27.setReg .x6 (BitVec.ofNat 64 (idx.val % 2))).setPC (pcAt 28)
  have h27' : OpenRuns s27 1 1 s28 := by
    have hv : s27.getReg .x22 &&& signExtend12 (1#12) = BitVec.ofNat 64 (idx.val % 2) := by
      change BitVec.ofNat 64 idx.val &&& signExtend12 (1#12) = _
      exact bv64_and1 idx.val (by omega)
    simpa only [hv, s28] using h27
  have h28 := step_SLLI (by omega) (rfl : s28.pc = pcAt 28)
    (rfl : openingInstr 28 = .base (.SLLI .x6 .x6 (4#6)))
  let s29 := (s28.setReg .x6 (BitVec.ofNat 64 (16 * (idx.val % 2)))).setPC (pcAt 29)
  have h28' : OpenRuns s28 1 1 s29 := by
    have hv : s28.getReg .x6 <<< (4#6 : BitVec 6).toNat = BitVec.ofNat 64 (16 * (idx.val % 2)) := by
      change BitVec.ofNat 64 (idx.val % 2) <<< 4 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hv, s29] using h28
  have h29 := step_ADD (by omega) (rfl : s29.pc = pcAt 29)
    (rfl : openingInstr 29 = .base (.ADD .x7 .x7 .x6))
  let s30 := (s29.setReg .x7 (BitVec.ofNat 64 (184 * (idx.val / 2) + 16 * (idx.val % 2)))).setPC (pcAt 30)
  have h29' : OpenRuns s29 1 1 s30 := by
    have hv : s29.getReg .x7 + s29.getReg .x6 =
        BitVec.ofNat 64 (184 * (idx.val / 2) + 16 * (idx.val % 2)) := by
      change BitVec.ofNat 64 (184 * (idx.val / 2)) + BitVec.ofNat 64 (16 * (idx.val % 2)) = _
      exact bv64_ofNat_add _ _
    simpa only [hv, s30] using h29
  have h30 := step_ADD (by omega) (rfl : s30.pc = pcAt 30)
    (rfl : openingInstr 30 = .base (.ADD .x10 .x18 .x7))
  let s31 := (s30.setReg .x10 (BitVec.ofNat 64 (4294971424 + saltOff idx))).setPC (pcAt 31)
  have h30' : OpenRuns s30 1 1 s31 := by
    have hr18 : s30.getReg .x18 = BitVec.ofNat 64 (4294971424 + (rowOff + 72)) := inv.rx18
    have hr7 : s30.getReg .x7 = BitVec.ofNat 64 (184 * (idx.val / 2) + 16 * (idx.val % 2)) := rfl
    have hsum : s30.getReg .x18 + s30.getReg .x7 = BitVec.ofNat 64 (4294971424 + saltOff idx) := by
      rw [hr18, hr7, bv64_ofNat_add, Nat.add_assoc, saltOff_formula idx]
    simpa only [hsum, s31] using h30
  have hinv31 : RecInv trapdoor positions t fwdBytes tails s31 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap16⟩
  have hsalt_bd : saltOff idx + 24 ≤ 3154116544 := by
    have h := saltOff_add_24_le idx
    rw [trapdoorBytes_eq] at h
    exact h
  obtain ⟨s32, hrcopy, hpc32, hreg32, hro32, hw32, ht32, hcap32⟩ :=
    openRuns_call_copy24 (callIdx := 31) (srcOff := saltOff idx) (jOff := 392#21)
      (fwdBytes := fwdBytes) (chunk := bitsToBytes (tdSalt trapdoor idx) 24) (tails := tails)
      (by omega) rfl (by decide) rfl rfl (saltOff_align8 idx) hsalt_bd hbd htbd
      hinv31.ro hinv31.writer hinv31.tail (bitsToBytes_length _ 24)
      (fun j hj => chunk_tdSalt trapdoor idx j hj)
  have hpre1 : OpenRuns s 6 6 s26 := ((((h20'.trans h21').trans h22').trans h23').trans h24').trans h25'
  have hpre2 : OpenRuns s26 5 5 s31 := (((h26'.trans h27').trans h28').trans h29').trans h30'
  refine ⟨s32, (hpre1.trans hpre2).trans hrcopy, hpc32, ?_, ?_⟩
  · rw [hreg32 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  · exact hinv31.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg32 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      hro32 hw32 ht32 hcap32

private def bin256StepFwd (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) (step : Nat) :
    List Byte :=
  bitsToBytes (tdNode trapdoor step ((i.val >>> step) ^^^ 1)) 32

private def bin240StepFwd (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) (step : Nat) :
    List Byte :=
  bitsToBytes (tdNode trapdoor (2 + step) ((i.val >>> (2 + step)) ^^^ 1)) 30

private def bin238StepFwd (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) (step : Nat) :
    List Byte :=
  bitsToBytes (tdNode trapdoor (5 + step) ((i.val >>> (5 + step)) ^^^ 1)) 29

private def bin238StepTails (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) (step : Nat) :
    List (BitVec 6) :=
  [tail6 (tdNode trapdoor (5 + step) ((i.val >>> (5 + step)) ^^^ 1))]

private theorem flatMap_range_congr {α : Type} (n : Nat) (f g : Nat → List α)
    (h : ∀ k < n, f k = g k) : (List.range n).flatMap f = (List.range n).flatMap g := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_append,
      List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.flatMap_nil,
      ih (fun k hk => h k (by omega)), h m (by omega)]

private theorem binPathFwd_split (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) :
    (List.range 2).flatMap (bin256StepFwd trapdoor i) ++
      (List.range 3).flatMap (bin240StepFwd trapdoor i) ++
      (List.range 11).flatMap (bin238StepFwd trapdoor i) =
    binPathFwd (tdNode trapdoor) i := by
  unfold binPathFwd
  rw [show (16 : Nat) = (2 + 3) + 11 from rfl, List.range_add, List.flatMap_append,
    List.range_add, List.flatMap_append, List.flatMap_map, List.flatMap_map]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) ?_ ?_) ?_
  · exact flatMap_range_congr 2 _ _ fun l hl => by
      simp [bin256StepFwd, levelFwdBytes, FIRST_240_LVL, hl]
  · exact flatMap_range_congr 3 _ _ fun step hstep => by
      simp only [bin240StepFwd, Function.comp, levelFwdBytes, FIRST_240_LVL, FIRST_238_LVL,
        show ¬ (2 + step < 2) by omega, show 2 + step < 5 by omega, ite_false, ite_true]
  · exact flatMap_range_congr 11 _ _ fun step hstep => by
      have h5 : 2 + 3 + step = 5 + step := by omega
      simp only [bin238StepFwd, Function.comp, h5, levelFwdBytes, FIRST_240_LVL, FIRST_238_LVL,
        show ¬ (5 + step < 2) by omega, show ¬ (5 + step < 5) by omega, ite_false]

private theorem openRuns_rec_bin256_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t step : Nat} {i : Index} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hstep : step < 2) (hpc : s.pc = pcAt 34)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (i.val >>> step))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * step))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2))
    (hbd : fwdBytes.length + 32 ≤ 8476692192)
    (htbd : tails.length ≤ 300000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ bin256StepFwd trapdoor i step
    ∃ s1, OpenRuns s 37 37 s1 ∧
      s1.pc = (if step + 1 < 2 then pcAt 34 else pcAt 45) ∧
      s1.getReg .x22 = BitVec.ofNat 64 (i.val >>> (step + 1)) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (step + 1)) ∧
      s1.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2) ∧
      fwd1.length = fwdBytes.length + 32 ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hi_lt : i.val < 16777216 := i.isLt
  have his_le : i.val >>> step ≤ i.val := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  set idx := i.val >>> step
  set sib := idx ^^^ 1
  have hsib_lt : sib < levelSize step := shiftRight_xor_one_lt i step (by omega)
  have hls_le := levelSize_le_max step (by omega)
  have hsib_lt64 : sib < 2 ^ 64 := by omega
  have h34 := step_XORI (by omega) hpc (rfl : openingInstr 34 = .base (.XORI .x28 .x22 (1#12)))
  let s35 := (s.setReg .x28 (BitVec.ofNat 64 sib)).setPC (pcAt 35)
  have h34' : OpenRuns s 1 1 s35 := by
    rw [hx22, bv64_xor1 idx (by omega)] at h34; exact h34
  have h35 := step_SRLI (by omega) (rfl : s35.pc = pcAt 35)
    (rfl : openingInstr 35 = .base (.SRLI .x6 .x28 (1#6)))
  let s36 := (s35.setReg .x6 (BitVec.ofNat 64 (sib / 2))).setPC (pcAt 36)
  have h35' : OpenRuns s35 1 1 s36 := by
    have hv : s35.getReg .x28 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (sib / 2) := by
      change BitVec.ofNat 64 sib >>> 1 = _
      rw [bv64_ushr sib 1 hsib_lt64, Nat.shiftRight_eq_div_pow]
    simpa only [hv, s36] using h35
  have h36 := step_ADD (by omega) (rfl : s36.pc = pcAt 36)
    (rfl : openingInstr 36 = .base (.ADD .x28 .x28 .x6))
  let s37 := (s36.setReg .x28 (BitVec.ofNat 64 (sib + sib / 2))).setPC (pcAt 37)
  have h36' : OpenRuns s36 1 1 s37 := by
    have hv : s36.getReg .x28 + s36.getReg .x6 = BitVec.ofNat 64 (sib + sib / 2) := by
      change BitVec.ofNat 64 sib + BitVec.ofNat 64 (sib / 2) = _; exact bv64_ofNat_add _ _
    simpa only [hv, s37] using h36
  have h37 := step_SLLI (by omega) (rfl : s37.pc = pcAt 37)
    (rfl : openingInstr 37 = .base (.SLLI .x28 .x28 (5#6)))
  let s38 := (s37.setReg .x28 (BitVec.ofNat 64 (nodeOffset step sib))).setPC (pcAt 38)
  have h37' : OpenRuns s37 1 1 s38 := by
    have hv : s37.getReg .x28 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (nodeOffset step sib) := by
      change BitVec.ofNat 64 (sib + sib / 2) <<< 5 = _
      rw [bv64_shl]; congr 1
      unfold nodeOffset gapOffset; omega
    simpa only [hv, s38] using h37
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have haddr38 : s38.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475936 + 32 * step) := by
    have hr29 : s38.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * step) := hx29
    rw [hr29, hse0, bv64_ofNat_add, Nat.add_zero]
  have h38 := step_LD (by omega) (rfl : s38.pc = pcAt 38)
    (rfl : openingInstr 38 = .base (.LD .x6 .x29 (0#12)))
    (by rw [haddr38]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s39 := (s38.setReg .x6 (BitVec.ofNat 64 (levelBase step))).setPC (pcAt 39)
  have h38' : OpenRuns s38 1 1 s39 := by
    have hmem : s38.getMem (BitVec.ofNat 64 (68719475936 + 32 * step)) = BitVec.ofNat 64 (levelBase step) :=
      readOnly_getMem_data_base inv.ro step (by omega)
    simpa only [haddr38, hmem, s39] using h38
  have h39 := step_ADD (by omega) (rfl : s39.pc = pcAt 39)
    (rfl : openingInstr 39 = .base (.ADD .x10 .x9 .x6))
  let s40 := (s39.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase step))).setPC (pcAt 40)
  have h39' : OpenRuns s39 1 1 s40 := by
    have hr9 : s39.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
    rw [hr9] at h39
    simpa only [show s39.getReg .x6 = BitVec.ofNat 64 (levelBase step) from rfl, bv64_ofNat_add, s40] using h39
  have h40 := step_ADD (by omega) (rfl : s40.pc = pcAt 40)
    (rfl : openingInstr 40 = .base (.ADD .x10 .x10 .x28))
  let s41 := (s40.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase step + nodeOffset step sib)))).setPC
    (pcAt 41)
  have h40' : OpenRuns s40 1 1 s41 := by
    have hv : s40.getReg .x10 + s40.getReg .x28 =
        BitVec.ofNat 64 (4294971424 + (levelBase step + nodeOffset step sib)) := by
      change BitVec.ofNat 64 (4294971424 + levelBase step) + BitVec.ofNat 64 (nodeOffset step sib) = _
      rw [bv64_ofNat_add, Nat.add_assoc]
    simpa only [hv, s41] using h40
  have hpre : OpenRuns s 7 7 s41 :=
    (((((h34'.trans h35').trans h36').trans h37').trans h38').trans h39').trans h40'
  have hinv41 : RecInv trapdoor positions t fwdBytes tails s41 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap16⟩
  have htb : treeBytes = 1610612672 := treeBytes_eq
  have hno_bd : levelBase step + nodeOffset step sib + 32 ≤ 3154116544 := by
    have := nodeOffset_lt_treeBytes step sib (by omega) hsib_lt; omega
  obtain ⟨s42, hrcopy, hpc42, hreg42, hro42, hw42, ht42, hcap42⟩ :=
    openRuns_call_copy32 (callIdx := 41) (srcOff := levelBase step + nodeOffset step sib) (jOff := 432#21)
      (fwdBytes := fwdBytes) (chunk := bitsToBytes (tdNode trapdoor step sib) 32) (tails := tails)
      (by omega) rfl (by decide) rfl rfl
      (by have h1 := levelBase_align8 step (by omega); have h2 := nodeOffset_align8 step sib; omega) hno_bd
      hbd htbd hinv41.ro hinv41.writer hinv41.tail (bitsToBytes_length _ 32)
      (fun j hj => chunk_tdNode trapdoor step sib 32 j (by omega) hj)
  have hinv42 : RecInv trapdoor positions t fwd1 tails s42 :=
    hinv41.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg42 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      hro42 hw42 ht42 hcap42
  have hx22_42 : s42.getReg .x22 = BitVec.ofNat 64 idx := by
    rw [hreg42 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hx22
  have hx29_42 : s42.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * step) := by
    rw [hreg42 .x29 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hx29
  have hx30_42 : s42.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2) := by
    rw [hreg42 .x30 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hx30
  have h42 := step_SRLI (by omega) hpc42 (rfl : openingInstr 42 = .base (.SRLI .x22 .x22 (1#6)))
  let s43 := (s42.setReg .x22 (BitVec.ofNat 64 (i.val >>> (step + 1)))).setPC (pcAt 43)
  have h42' : OpenRuns s42 1 1 s43 := by
    have hv : s42.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (i.val >>> (step + 1)) := by
      rw [hx22_42]; change BitVec.ofNat 64 (i.val >>> step) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), nat_ushr_ushr1]
    simpa only [hv, s43] using h42
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have h43 := step_ADDI (by omega) (rfl : s43.pc = pcAt 43)
    (rfl : openingInstr 43 = .base (.ADDI .x29 .x29 (32#12)))
  let s44 := (s43.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * (step + 1)))).setPC (pcAt 44)
  have h43' : OpenRuns s43 1 1 s44 := by
    have hr29 : s43.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * step) := hx29_42
    have hv : s43.getReg .x29 + signExtend12 (32#12) =
        BitVec.ofNat 64 (68719475936 + 32 * (step + 1)) := by
      rw [hr29, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s44] using h43
  have hinv44 : RecInv trapdoor positions t fwd1 tails s44 :=
    ⟨hinv42.rx2, hinv42.rx9, hinv42.rx18, hinv42.rx21, hinv42.rx24, hinv42.rx26, hinv42.rx27,
     hinv42.ro, hinv42.writer.of_eq, hinv42.tail.of_eq, hinv42.cap16⟩
  have hx22_44 : s44.getReg .x22 = BitVec.ofNat 64 (i.val >>> (step + 1)) := by
    simp only [s44, MachineState.getReg_setPC, getReg_setReg_ne' .x29 .x22 (by decide)]; rfl
  have hx30_44 : s44.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2) := by
    simp only [s44, s43, MachineState.getReg_setPC, getReg_setReg_ne' .x29 .x30 (by decide),
      getReg_setReg_ne' .x22 .x30 (by decide)]; exact hx30_42
  have hlen1 : fwd1.length = fwdBytes.length + 32 := by
    simp only [fwd1, bin256StepFwd, List.length_append, bitsToBytes_length]
  by_cases hmore : step + 1 < 2
  · have h44 := step_BNE_taken (by omega) (rfl : s44.pc = pcAt 44)
      (rfl : openingInstr 44 = .base (.BNE .x29 .x30 (8152#13)))
      (by rw [hx30_44]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 44 + signExtend13 (8152#13) = pcAt 34)
    exact ⟨s44.setPC (pcAt 34), (((hpre.trans hrcopy).trans h42').trans h43').trans h44,
      by rw [if_pos hmore]; rfl, hx22_44, rfl, hx30_44, hlen1, hinv44.setPC (pcAt 34)⟩
  · have hlast : step + 1 = 2 := by omega
    have h44 := step_BNE_not_taken (by omega) (rfl : s44.pc = pcAt 44)
      (rfl : openingInstr 44 = .base (.BNE .x29 .x30 (8152#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (step + 1)) = s44.getReg .x30; rw [hx30_44, hlast])
    exact ⟨s44.setPC (pcAt 45), (((hpre.trans hrcopy).trans h42').trans h43').trans h44,
      by rw [if_neg hmore]; rfl, hx22_44, rfl, hx30_44, hlen1, hinv44.setPC (pcAt 45)⟩

private theorem openRuns_rec_bin256 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {i : Index} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hpc : s.pc = pcAt 32)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 i.val)
    (hbd : fwdBytes.length + 64 ≤ 8476692192)
    (htbd : tails.length ≤ 300000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ (List.range 2).flatMap (bin256StepFwd trapdoor i)
    ∃ s1, OpenRuns s 76 76 s1 ∧
      s1.pc = pcAt 45 ∧
      s1.getReg .x22 = BitVec.ofNat 64 (i.val >>> 2) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 2) ∧
      fwd1.length = fwdBytes.length + 64 ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse64 : signExtend12 (64#12) = BitVec.ofNat 64 64 := by decide
  have h32 := step_ADDI (by omega) hpc (rfl : openingInstr 32 = .base (.ADDI .x29 .x2 (0#12)))
  let s33 := (s.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * 0))).setPC (pcAt 33)
  have h32' : OpenRuns s 1 1 s33 := by
    rw [inv.rx2, hse0, bv64_ofNat_add] at h32; exact h32
  have h33 := step_ADDI (by omega) (rfl : s33.pc = pcAt 33)
    (rfl : openingInstr 33 = .base (.ADDI .x30 .x2 (64#12)))
  let s34 := (s33.setReg .x30 (BitVec.ofNat 64 (68719475936 + 32 * 2))).setPC (pcAt 34)
  have h33' : OpenRuns s33 1 1 s34 := by
    have hr2 : s33.getReg .x2 = BitVec.ofNat 64 68719475936 := inv.rx2
    rw [hr2, hse64, bv64_ofNat_add] at h33; exact h33
  have hinv34 : RecInv trapdoor positions t fwdBytes tails s34 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap16⟩
  have hloop : ∀ n ≤ 2,
      let cur := fwdBytes ++ (List.range n).flatMap (bin256StepFwd trapdoor i)
      ∃ sn, OpenRuns s34 (37 * n) (37 * n) sn ∧
        sn.pc = (if n < 2 then pcAt 34 else pcAt 45) ∧
        sn.getReg .x22 = BitVec.ofNat 64 (i.val >>> n) ∧
        sn.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * n) ∧
        sn.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 2) ∧
        cur.length = fwdBytes.length + 32 * n ∧
        RecInv trapdoor positions t cur tails sn := by
    intro n hn
    induction n with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.add_zero]
      exact ⟨s34, OpenRuns.refl s34, by rw [if_pos (by omega : 0 < 2)]; rfl,
        by rw [Nat.shiftRight_zero]; exact hx22, rfl, rfl, trivial, hinv34⟩
    | succ n ih =>
      obtain ⟨sn, hrn, hpcn, hx22n, hx29n, hx30n, hlenn, invn⟩ := ih (by omega)
      have hpcn' : sn.pc = pcAt 34 := by simpa only [show n < 2 by omega, ite_true] using hpcn
      obtain ⟨sn1, hr1, hpc1, hx22_1, hx29_1, hx30_1, hlen1, inv1⟩ :=
        openRuns_rec_bin256_step (by omega) hpcn' hx22n hx29n hx30n (by omega) htbd invn
      have happ : fwdBytes ++ (List.range n).flatMap (bin256StepFwd trapdoor i) ++ bin256StepFwd trapdoor i n =
          fwdBytes ++ (List.range (n + 1)).flatMap (bin256StepFwd trapdoor i) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      rw [happ] at hlen1 inv1
      exact ⟨sn1, by simpa only [Nat.mul_succ] using hrn.trans hr1,
        hpc1, hx22_1, hx29_1, hx30_1, by omega, inv1⟩
  obtain ⟨s45, hrloop, hpc45, hx22_45, hx29_45, _, hlen45, inv45⟩ := hloop 2 (Nat.le_refl 2)
  have hpc45' : s45.pc = pcAt 45 := by simpa only [Nat.lt_irrefl, ite_false] using hpc45
  exact ⟨s45, (h32'.trans h33').trans hrloop, hpc45', hx22_45, hx29_45, hlen45, inv45⟩

private theorem openRuns_rec_bin240_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t step : Nat} {i : Index} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hstep : step < 3) (hpc : s.pc = pcAt 46)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (i.val >>> (2 + step)))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 5))
    (hbd : fwdBytes.length + 30 ≤ 8476692192)
    (htbd : tails.length ≤ 300000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ bin240StepFwd trapdoor i step
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps = 25 + 5 * (fwd1.length / 8 - fwdBytes.length / 8) ∧
      s1.pc = (if step + 1 < 3 then pcAt 46 else pcAt 57) ∧
      s1.getReg .x22 = BitVec.ofNat 64 (i.val >>> (2 + (step + 1))) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) ∧
      s1.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 5) ∧
      fwd1.length = fwdBytes.length + 30 ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hi_lt : i.val < 16777216 := i.isLt
  have his_le : i.val >>> (2 + step) ≤ i.val := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  set l := 2 + step
  set idx := i.val >>> l
  set sib := idx ^^^ 1
  have hsib_lt : sib < levelSize l := shiftRight_xor_one_lt i l (by omega)
  have hls_le := levelSize_le_max l (by omega)
  have hsib_lt64 : sib < 2 ^ 64 := by omega
  have h46 := step_XORI (by omega) hpc (rfl : openingInstr 46 = .base (.XORI .x28 .x22 (1#12)))
  let s47 := (s.setReg .x28 (BitVec.ofNat 64 sib)).setPC (pcAt 47)
  have h46' : OpenRuns s 1 1 s47 := by
    rw [hx22, bv64_xor1 idx (by omega)] at h46; exact h46
  have h47 := step_SRLI (by omega) (rfl : s47.pc = pcAt 47)
    (rfl : openingInstr 47 = .base (.SRLI .x6 .x28 (1#6)))
  let s48 := (s47.setReg .x6 (BitVec.ofNat 64 (sib / 2))).setPC (pcAt 48)
  have h47' : OpenRuns s47 1 1 s48 := by
    have hv : s47.getReg .x28 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (sib / 2) := by
      change BitVec.ofNat 64 sib >>> 1 = _
      rw [bv64_ushr sib 1 hsib_lt64, Nat.shiftRight_eq_div_pow]
    simpa only [hv, s48] using h47
  have h48 := step_ADD (by omega) (rfl : s48.pc = pcAt 48)
    (rfl : openingInstr 48 = .base (.ADD .x28 .x28 .x6))
  let s49 := (s48.setReg .x28 (BitVec.ofNat 64 (sib + sib / 2))).setPC (pcAt 49)
  have h48' : OpenRuns s48 1 1 s49 := by
    have hv : s48.getReg .x28 + s48.getReg .x6 = BitVec.ofNat 64 (sib + sib / 2) := by
      change BitVec.ofNat 64 sib + BitVec.ofNat 64 (sib / 2) = _; exact bv64_ofNat_add _ _
    simpa only [hv, s49] using h48
  have h49 := step_SLLI (by omega) (rfl : s49.pc = pcAt 49)
    (rfl : openingInstr 49 = .base (.SLLI .x28 .x28 (5#6)))
  let s50 := (s49.setReg .x28 (BitVec.ofNat 64 (nodeOffset l sib))).setPC (pcAt 50)
  have h49' : OpenRuns s49 1 1 s50 := by
    have hv : s49.getReg .x28 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (nodeOffset l sib) := by
      change BitVec.ofNat 64 (sib + sib / 2) <<< 5 = _
      rw [bv64_shl]; congr 1
      unfold nodeOffset gapOffset; omega
    simpa only [hv, s50] using h49
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have haddr50 : s50.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    have hr29 : s50.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := hx29
    rw [hr29, hse0, bv64_ofNat_add, Nat.add_zero]
  have h50 := step_LD (by omega) (rfl : s50.pc = pcAt 50)
    (rfl : openingInstr 50 = .base (.LD .x6 .x29 (0#12)))
    (by rw [haddr50]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s51 := (s50.setReg .x6 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 51)
  have h50' : OpenRuns s50 1 1 s51 := by
    have hmem : s50.getMem (BitVec.ofNat 64 (68719475936 + 32 * l)) = BitVec.ofNat 64 (levelBase l) :=
      readOnly_getMem_data_base inv.ro l (by omega)
    simpa only [haddr50, hmem, s51] using h50
  have h51 := step_ADD (by omega) (rfl : s51.pc = pcAt 51)
    (rfl : openingInstr 51 = .base (.ADD .x10 .x9 .x6))
  let s52 := (s51.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 52)
  have h51' : OpenRuns s51 1 1 s52 := by
    have hr9 : s51.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
    rw [hr9] at h51
    simpa only [show s51.getReg .x6 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s52] using h51
  have h52 := step_ADD (by omega) (rfl : s52.pc = pcAt 52)
    (rfl : openingInstr 52 = .base (.ADD .x10 .x10 .x28))
  let s53 := (s52.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)))).setPC
    (pcAt 53)
  have h52' : OpenRuns s52 1 1 s53 := by
    have hv : s52.getReg .x10 + s52.getReg .x28 =
        BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)) := by
      change BitVec.ofNat 64 (4294971424 + levelBase l) + BitVec.ofNat 64 (nodeOffset l sib) = _
      rw [bv64_ofNat_add, Nat.add_assoc]
    simpa only [hv, s53] using h52
  have hpre : OpenRuns s 7 7 s53 :=
    (((((h46'.trans h47').trans h48').trans h49').trans h50').trans h51').trans h52'
  have hinv53 : RecInv trapdoor positions t fwdBytes tails s53 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap16⟩
  have htb : treeBytes = 1610612672 := treeBytes_eq
  have hno_bd : levelBase l + nodeOffset l sib + 32 ≤ 3154116544 := by
    have := nodeOffset_lt_treeBytes l sib (by omega) hsib_lt; omega
  obtain ⟨stC, s54, hrcopy, hstC, hpc54, hreg54, hro54, hw54, ht54, hcap54⟩ :=
    openRuns_call_copy30 (callIdx := 53) (srcOff := levelBase l + nodeOffset l sib) (jOff := 488#21)
      (fwdBytes := fwdBytes) (chunk := bitsToBytes (tdNode trapdoor l sib) 30) (tails := tails)
      (by omega) rfl (by decide) rfl rfl
      (by have h1 := levelBase_align8 l (by omega); have h2 := nodeOffset_align8 l sib; omega) hno_bd
      hbd htbd hinv53.ro hinv53.writer hinv53.tail (bitsToBytes_length _ 30)
      (fun j hj => chunk_tdNode trapdoor l sib 30 j (by omega) hj)
  change stC = 15 + 5 * (fwd1.length / 8 - fwdBytes.length / 8) at hstC
  have hinv54 : RecInv trapdoor positions t fwd1 tails s54 :=
    hinv53.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg54 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      hro54 hw54 ht54 hcap54
  have hx22_54 : s54.getReg .x22 = BitVec.ofNat 64 idx := by
    rw [hreg54 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hx22
  have hx29_54 : s54.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    rw [hreg54 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hx29
  have hx30_54 : s54.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 5) := by
    rw [hreg54 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hx30
  have h54 := step_SRLI (by omega) hpc54 (rfl : openingInstr 54 = .base (.SRLI .x22 .x22 (1#6)))
  let s55 := (s54.setReg .x22 (BitVec.ofNat 64 (i.val >>> (2 + (step + 1))))).setPC (pcAt 55)
  have h54' : OpenRuns s54 1 1 s55 := by
    have hv : s54.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (i.val >>> (2 + (step + 1))) := by
      rw [hx22_54]; change BitVec.ofNat 64 (i.val >>> (2 + step)) >>> 1 = _
      rw [bv64_ushr (i.val >>> (2 + step)) 1 (Nat.lt_of_le_of_lt his_le (by omega)), nat_ushr_ushr1,
        show 2 + step + 1 = 2 + (step + 1) by omega]
    simpa only [hv, s55] using h54
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have h55 := step_ADDI (by omega) (rfl : s55.pc = pcAt 55)
    (rfl : openingInstr 55 = .base (.ADDI .x29 .x29 (32#12)))
  let s56 := (s55.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))))).setPC (pcAt 56)
  have h55' : OpenRuns s55 1 1 s56 := by
    have hr29 : s55.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := hx29_54
    have hv : s55.getReg .x29 + signExtend12 (32#12) =
        BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) := by
      rw [hr29, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s56] using h55
  have hinv56 : RecInv trapdoor positions t fwd1 tails s56 :=
    ⟨hinv54.rx2, hinv54.rx9, hinv54.rx18, hinv54.rx21, hinv54.rx24, hinv54.rx26, hinv54.rx27,
     hinv54.ro, hinv54.writer.of_eq, hinv54.tail.of_eq, hinv54.cap16⟩
  have hx22_56 : s56.getReg .x22 = BitVec.ofNat 64 (i.val >>> (2 + (step + 1))) := by
    simp only [s56, MachineState.getReg_setPC, getReg_setReg_ne' .x29 .x22 (by decide)]; rfl
  have hx30_56 : s56.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 5) := by
    simp only [s56, s55, MachineState.getReg_setPC, getReg_setReg_ne' .x29 .x30 (by decide),
      getReg_setReg_ne' .x22 .x30 (by decide)]; exact hx30_54
  have hlen1 : fwd1.length = fwdBytes.length + 30 := by
    simp only [fwd1, bin240StepFwd, List.length_append, bitsToBytes_length]
  by_cases hmore : step + 1 < 3
  · have h56 := step_BNE_taken (by omega) (rfl : s56.pc = pcAt 56)
      (rfl : openingInstr 56 = .base (.BNE .x29 .x30 (8152#13)))
      (by rw [hx30_56]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 56 + signExtend13 (8152#13) = pcAt 46)
    exact ⟨7 + stC + 1 + 1 + 1, s56.setPC (pcAt 46), (((hpre.trans hrcopy).trans h54').trans h55').trans h56,
      by omega, by rw [if_pos hmore]; rfl, hx22_56, rfl, hx30_56, hlen1, hinv56.setPC (pcAt 46)⟩
  · have hlast : step + 1 = 3 := by omega
    have h56 := step_BNE_not_taken (by omega) (rfl : s56.pc = pcAt 56)
      (rfl : openingInstr 56 = .base (.BNE .x29 .x30 (8152#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) = s56.getReg .x30; rw [hx30_56, hlast])
    exact ⟨7 + stC + 1 + 1 + 1, s56.setPC (pcAt 57), (((hpre.trans hrcopy).trans h54').trans h55').trans h56,
      by omega, by rw [if_neg hmore]; rfl, hx22_56, rfl, hx30_56, hlen1, hinv56.setPC (pcAt 57)⟩

private theorem openRuns_rec_bin240 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {i : Index} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hpc : s.pc = pcAt 45)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (i.val >>> 2))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 2))
    (hbd : fwdBytes.length + 90 ≤ 8476692192)
    (htbd : tails.length ≤ 300000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ (List.range 3).flatMap (bin240StepFwd trapdoor i)
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps = 76 + 5 * (fwd1.length / 8 - fwdBytes.length / 8) ∧
      s1.pc = pcAt 57 ∧
      s1.getReg .x22 = BitVec.ofNat 64 (i.val >>> 5) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 5) ∧
      fwd1.length = fwdBytes.length + 90 ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hse160 : signExtend12 (160#12) = BitVec.ofNat 64 160 := by decide
  have h45 := step_ADDI (by omega) hpc (rfl : openingInstr 45 = .base (.ADDI .x30 .x2 (160#12)))
  let s46 := (s.setReg .x30 (BitVec.ofNat 64 (68719475936 + 32 * 5))).setPC (pcAt 46)
  have h45' : OpenRuns s 1 1 s46 := by
    rw [inv.rx2, hse160, bv64_ofNat_add] at h45; exact h45
  have hinv46 : RecInv trapdoor positions t fwdBytes tails s46 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap16⟩
  have hloop : ∀ n ≤ 3,
      let cur := fwdBytes ++ (List.range n).flatMap (bin240StepFwd trapdoor i)
      ∃ steps sn, OpenRuns s46 steps steps sn ∧
        steps = 25 * n + 5 * (cur.length / 8 - fwdBytes.length / 8) ∧
        sn.pc = (if n < 3 then pcAt 46 else pcAt 57) ∧
        sn.getReg .x22 = BitVec.ofNat 64 (i.val >>> (2 + n)) ∧
        sn.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + n)) ∧
        sn.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 5) ∧
        cur.length = fwdBytes.length + 30 * n ∧
        RecInv trapdoor positions t cur tails sn := by
    intro n hn
    induction n with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.add_zero, Nat.sub_self]
      exact ⟨0, s46, OpenRuns.refl s46, rfl, by rw [if_pos (by omega : 0 < 3)]; rfl,
        hx22, hx29, rfl, trivial, hinv46⟩
    | succ n ih =>
      obtain ⟨st, sn, hrn, hstn, hpcn, hx22n, hx29n, hx30n, hlenn, invn⟩ := ih (by omega)
      have hpcn' : sn.pc = pcAt 46 := by simpa only [show n < 3 by omega, ite_true] using hpcn
      obtain ⟨st1, sn1, hr1, hst1, hpc1, hx22_1, hx29_1, hx30_1, hlen1, inv1⟩ :=
        openRuns_rec_bin240_step (by omega) hpcn' hx22n hx29n hx30n (by omega) htbd invn
      have happ : fwdBytes ++ (List.range n).flatMap (bin240StepFwd trapdoor i) ++ bin240StepFwd trapdoor i n =
          fwdBytes ++ (List.range (n + 1)).flatMap (bin240StepFwd trapdoor i) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      rw [happ] at hst1 hlen1 inv1
      have hq1 : fwdBytes.length / 8 ≤ (fwdBytes ++ (List.range n).flatMap (bin240StepFwd trapdoor i)).length / 8 :=
        Nat.div_le_div_right (by omega)
      have hq2 : (fwdBytes ++ (List.range n).flatMap (bin240StepFwd trapdoor i)).length / 8 ≤
          (fwdBytes ++ (List.range (n + 1)).flatMap (bin240StepFwd trapdoor i)).length / 8 :=
        Nat.div_le_div_right (by omega)
      exact ⟨st + st1, sn1, hrn.trans hr1, by omega, hpc1, hx22_1, hx29_1, hx30_1, by omega, inv1⟩
  obtain ⟨st, s57, hrloop, hst, hpc57, hx22_57, hx29_57, _, hlen57, inv57⟩ := hloop 3 (Nat.le_refl 3)
  have hpc57' : s57.pc = pcAt 57 := by simpa only [Nat.lt_irrefl, ite_false] using hpc57
  change st = 25 * 3 + 5 * (fwd1.length / 8 - fwdBytes.length / 8) at hst
  exact ⟨1 + st, s57, h45'.trans hrloop, by omega, hpc57', hx22_57, hx29_57, hlen57, inv57⟩

private theorem openRuns_rec_bin238_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t step : Nat} {i : Index} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hstep : step < 11) (hpc : s.pc = pcAt 58)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (i.val >>> (5 + step)))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (5 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16))
    (hbd : fwdBytes.length + 29 ≤ 8476692192)
    (htbd : tails.length < 300000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ bin238StepFwd trapdoor i step
    let tails1 := tails ++ bin238StepTails trapdoor i step
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps = 32 + 5 * (fwd1.length / 8 - fwdBytes.length / 8) +
        4 * (tailAccLen tails1 - tailAccLen tails) ∧
      s1.pc = (if step + 1 < 11 then pcAt 58 else pcAt 69) ∧
      s1.getReg .x22 = BitVec.ofNat 64 (i.val >>> (5 + (step + 1))) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (5 + (step + 1))) ∧
      s1.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) ∧
      fwd1.length = fwdBytes.length + 29 ∧
      tails1.length = tails.length + 1 ∧
      RecInv trapdoor positions t fwd1 tails1 s1 := by
  intro fwd1 tails1
  have hi_lt : i.val < 16777216 := i.isLt
  have his_le : i.val >>> (5 + step) ≤ i.val := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  set l := 5 + step
  set idx := i.val >>> l
  set sib := idx ^^^ 1
  have hsib_lt : sib < levelSize l := shiftRight_xor_one_lt i l (by omega)
  have hls_le := levelSize_le_max l (by omega)
  have hsib_lt64 : sib < 2 ^ 64 := by omega
  have h58 := step_XORI (by omega) hpc (rfl : openingInstr 58 = .base (.XORI .x28 .x22 (1#12)))
  let s59 := (s.setReg .x28 (BitVec.ofNat 64 sib)).setPC (pcAt 59)
  have h58' : OpenRuns s 1 1 s59 := by
    rw [hx22, bv64_xor1 idx (by omega)] at h58; exact h58
  have h59 := step_SRLI (by omega) (rfl : s59.pc = pcAt 59)
    (rfl : openingInstr 59 = .base (.SRLI .x6 .x28 (1#6)))
  let s60 := (s59.setReg .x6 (BitVec.ofNat 64 (sib / 2))).setPC (pcAt 60)
  have h59' : OpenRuns s59 1 1 s60 := by
    have hv : s59.getReg .x28 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (sib / 2) := by
      change BitVec.ofNat 64 sib >>> 1 = _
      rw [bv64_ushr sib 1 hsib_lt64, Nat.shiftRight_eq_div_pow]
    simpa only [hv, s60] using h59
  have h60 := step_ADD (by omega) (rfl : s60.pc = pcAt 60)
    (rfl : openingInstr 60 = .base (.ADD .x28 .x28 .x6))
  let s61 := (s60.setReg .x28 (BitVec.ofNat 64 (sib + sib / 2))).setPC (pcAt 61)
  have h60' : OpenRuns s60 1 1 s61 := by
    have hv : s60.getReg .x28 + s60.getReg .x6 = BitVec.ofNat 64 (sib + sib / 2) := by
      change BitVec.ofNat 64 sib + BitVec.ofNat 64 (sib / 2) = _; exact bv64_ofNat_add _ _
    simpa only [hv, s61] using h60
  have h61 := step_SLLI (by omega) (rfl : s61.pc = pcAt 61)
    (rfl : openingInstr 61 = .base (.SLLI .x28 .x28 (5#6)))
  let s62 := (s61.setReg .x28 (BitVec.ofNat 64 (nodeOffset l sib))).setPC (pcAt 62)
  have h61' : OpenRuns s61 1 1 s62 := by
    have hv : s61.getReg .x28 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (nodeOffset l sib) := by
      change BitVec.ofNat 64 (sib + sib / 2) <<< 5 = _
      rw [bv64_shl]; congr 1
      unfold nodeOffset gapOffset; omega
    simpa only [hv, s62] using h61
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have haddr62 : s62.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    have hr29 : s62.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := hx29
    rw [hr29, hse0, bv64_ofNat_add, Nat.add_zero]
  have h62 := step_LD (by omega) (rfl : s62.pc = pcAt 62)
    (rfl : openingInstr 62 = .base (.LD .x6 .x29 (0#12)))
    (by rw [haddr62]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s63 := (s62.setReg .x6 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 63)
  have h62' : OpenRuns s62 1 1 s63 := by
    have hmem : s62.getMem (BitVec.ofNat 64 (68719475936 + 32 * l)) = BitVec.ofNat 64 (levelBase l) :=
      readOnly_getMem_data_base inv.ro l (by omega)
    simpa only [haddr62, hmem, s63] using h62
  have h63 := step_ADD (by omega) (rfl : s63.pc = pcAt 63)
    (rfl : openingInstr 63 = .base (.ADD .x10 .x9 .x6))
  let s64 := (s63.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 64)
  have h63' : OpenRuns s63 1 1 s64 := by
    have hr9 : s63.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
    rw [hr9] at h63
    simpa only [show s63.getReg .x6 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s64] using h63
  have h64 := step_ADD (by omega) (rfl : s64.pc = pcAt 64)
    (rfl : openingInstr 64 = .base (.ADD .x10 .x10 .x28))
  let s65 := (s64.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)))).setPC
    (pcAt 65)
  have h64' : OpenRuns s64 1 1 s65 := by
    have hv : s64.getReg .x10 + s64.getReg .x28 =
        BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)) := by
      change BitVec.ofNat 64 (4294971424 + levelBase l) + BitVec.ofNat 64 (nodeOffset l sib) = _
      rw [bv64_ofNat_add, Nat.add_assoc]
    simpa only [hv, s65] using h64
  have hpre : OpenRuns s 7 7 s65 :=
    (((((h58'.trans h59').trans h60').trans h61').trans h62').trans h63').trans h64'
  have hinv65 : RecInv trapdoor positions t fwdBytes tails s65 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap16⟩
  obtain ⟨stC, s66, hrcopy, hstC, hpc66, hreg66, hro66, hw66, ht66, hcap66⟩ :=
    openRuns_call_copy29_tail (callIdx := 65) (l := l) (nodeIdx := sib) (jOff := 576#21)
      (fwdBytes := fwdBytes) (tails := tails) (by omega) (by omega) hsib_lt
      rfl (by decide) rfl rfl hbd htbd hinv65.ro hinv65.writer hinv65.tail
  change stC = 22 + 5 * (fwd1.length / 8 - fwdBytes.length / 8) +
    4 * (tailAccLen tails1 - tailAccLen tails) at hstC
  have hinv66 : RecInv trapdoor positions t fwd1 tails1 s66 :=
    hinv65.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg66 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      hro66 hw66 ht66 hcap66
  have hx22_66 : s66.getReg .x22 = BitVec.ofNat 64 idx := by
    rw [hreg66 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hx22
  have hx29_66 : s66.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    rw [hreg66 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hx29
  have hx30_66 : s66.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) := by
    rw [hreg66 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hx30
  have h66 := step_SRLI (by omega) hpc66 (rfl : openingInstr 66 = .base (.SRLI .x22 .x22 (1#6)))
  let s67 := (s66.setReg .x22 (BitVec.ofNat 64 (i.val >>> (5 + (step + 1))))).setPC (pcAt 67)
  have h66' : OpenRuns s66 1 1 s67 := by
    have hv : s66.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (i.val >>> (5 + (step + 1))) := by
      rw [hx22_66]; change BitVec.ofNat 64 (i.val >>> (5 + step)) >>> 1 = _
      rw [bv64_ushr (i.val >>> (5 + step)) 1 (Nat.lt_of_le_of_lt his_le (by omega)), nat_ushr_ushr1,
        show 5 + step + 1 = 5 + (step + 1) by omega]
    simpa only [hv, s67] using h66
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have h67 := step_ADDI (by omega) (rfl : s67.pc = pcAt 67)
    (rfl : openingInstr 67 = .base (.ADDI .x29 .x29 (32#12)))
  let s68 := (s67.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * (5 + (step + 1))))).setPC (pcAt 68)
  have h67' : OpenRuns s67 1 1 s68 := by
    have hr29 : s67.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := hx29_66
    have hv : s67.getReg .x29 + signExtend12 (32#12) =
        BitVec.ofNat 64 (68719475936 + 32 * (5 + (step + 1))) := by
      rw [hr29, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s68] using h67
  have hinv68 : RecInv trapdoor positions t fwd1 tails1 s68 :=
    ⟨hinv66.rx2, hinv66.rx9, hinv66.rx18, hinv66.rx21, hinv66.rx24, hinv66.rx26, hinv66.rx27,
     hinv66.ro, hinv66.writer.of_eq, hinv66.tail.of_eq, hinv66.cap16⟩
  have hx22_68 : s68.getReg .x22 = BitVec.ofNat 64 (i.val >>> (5 + (step + 1))) := by
    simp only [s68, MachineState.getReg_setPC, getReg_setReg_ne' .x29 .x22 (by decide)]; rfl
  have hx30_68 : s68.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) := by
    simp only [s68, s67, MachineState.getReg_setPC, getReg_setReg_ne' .x29 .x30 (by decide),
      getReg_setReg_ne' .x22 .x30 (by decide)]; exact hx30_66
  have hlen1 : fwd1.length = fwdBytes.length + 29 := by
    simp only [fwd1, bin238StepFwd, List.length_append, bitsToBytes_length]
  have htlen1 : tails1.length = tails.length + 1 := by
    simp only [tails1, bin238StepTails, List.length_append, List.length_singleton]
  by_cases hmore : step + 1 < 11
  · have h68 := step_BNE_taken (by omega) (rfl : s68.pc = pcAt 68)
      (rfl : openingInstr 68 = .base (.BNE .x29 .x30 (8152#13)))
      (by rw [hx30_68]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 68 + signExtend13 (8152#13) = pcAt 58)
    exact ⟨7 + stC + 1 + 1 + 1, s68.setPC (pcAt 58), (((hpre.trans hrcopy).trans h66').trans h67').trans h68,
      by omega, by rw [if_pos hmore]; rfl, hx22_68, rfl, hx30_68, hlen1, htlen1, hinv68.setPC (pcAt 58)⟩
  · have hlast : step + 1 = 11 := by omega
    have h68 := step_BNE_not_taken (by omega) (rfl : s68.pc = pcAt 68)
      (rfl : openingInstr 68 = .base (.BNE .x29 .x30 (8152#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (5 + (step + 1))) = s68.getReg .x30; rw [hx30_68, hlast])
    exact ⟨7 + stC + 1 + 1 + 1, s68.setPC (pcAt 69), (((hpre.trans hrcopy).trans h66').trans h67').trans h68,
      by omega, by rw [if_neg hmore]; rfl, hx22_68, rfl, hx30_68, hlen1, htlen1, hinv68.setPC (pcAt 69)⟩

private theorem openRuns_rec_bin238 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {i : Index} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hpc : s.pc = pcAt 57)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (i.val >>> 5))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * 5))
    (hbd : fwdBytes.length + 319 ≤ 8476692192)
    (htbd : tails.length + 11 ≤ 300000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ (List.range 11).flatMap (bin238StepFwd trapdoor i)
    let tails1 := tails ++ binPathTails (tdNode trapdoor) i
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps = 353 + 5 * (fwd1.length / 8 - fwdBytes.length / 8) +
        4 * (tailAccLen tails1 - tailAccLen tails) ∧
      s1.pc = pcAt 69 ∧
      s1.getReg .x22 = BitVec.ofNat 64 (i.val >>> 16) ∧
      RecInv trapdoor positions t fwd1 tails1 s1 := by
  intro fwd1 tails1
  have hse512 : signExtend12 (512#12) = BitVec.ofNat 64 512 := by decide
  have h57 := step_ADDI (by omega) hpc (rfl : openingInstr 57 = .base (.ADDI .x30 .x2 (512#12)))
  let s58 := (s.setReg .x30 (BitVec.ofNat 64 (68719475936 + 32 * 16))).setPC (pcAt 58)
  have h57' : OpenRuns s 1 1 s58 := by
    rw [inv.rx2, hse512, bv64_ofNat_add] at h57; exact h57
  have hinv58 : RecInv trapdoor positions t fwdBytes tails s58 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap16⟩
  have hloop : ∀ n ≤ 11,
      let curF := fwdBytes ++ (List.range n).flatMap (bin238StepFwd trapdoor i)
      let curT := tails ++ (List.range n).flatMap (bin238StepTails trapdoor i)
      ∃ steps sn, OpenRuns s58 steps steps sn ∧
        steps = 32 * n + 5 * (curF.length / 8 - fwdBytes.length / 8) +
          4 * (tailAccLen curT - tailAccLen tails) ∧
        sn.pc = (if n < 11 then pcAt 58 else pcAt 69) ∧
        sn.getReg .x22 = BitVec.ofNat 64 (i.val >>> (5 + n)) ∧
        sn.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (5 + n)) ∧
        sn.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) ∧
        curF.length = fwdBytes.length + 29 * n ∧
        curT.length = tails.length + n ∧
        RecInv trapdoor positions t curF curT sn := by
    intro n hn
    induction n with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.add_zero, Nat.sub_self]
      exact ⟨0, s58, OpenRuns.refl s58, rfl, by rw [if_pos (by omega : 0 < 11)]; rfl,
        hx22, hx29, rfl, trivial, trivial, hinv58⟩
    | succ n ih =>
      obtain ⟨st, sn, hrn, hstn, hpcn, hx22n, hx29n, hx30n, hlenn, htlenn, invn⟩ := ih (by omega)
      have hpcn' : sn.pc = pcAt 58 := by simpa only [show n < 11 by omega, ite_true] using hpcn
      obtain ⟨st1, sn1, hr1, hst1, hpc1, hx22_1, hx29_1, hx30_1, hlen1, htlen1, inv1⟩ :=
        openRuns_rec_bin238_step (by omega) hpcn' hx22n hx29n hx30n (by omega) (by omega) invn
      have happF : fwdBytes ++ (List.range n).flatMap (bin238StepFwd trapdoor i) ++ bin238StepFwd trapdoor i n =
          fwdBytes ++ (List.range (n + 1)).flatMap (bin238StepFwd trapdoor i) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      have happT : tails ++ (List.range n).flatMap (bin238StepTails trapdoor i) ++ bin238StepTails trapdoor i n =
          tails ++ (List.range (n + 1)).flatMap (bin238StepTails trapdoor i) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      have hq1 : fwdBytes.length / 8 ≤ (fwdBytes ++ (List.range n).flatMap (bin238StepFwd trapdoor i)).length / 8 :=
        Nat.div_le_div_right (by omega)
      have hq2 : (fwdBytes ++ (List.range n).flatMap (bin238StepFwd trapdoor i)).length / 8 ≤
          (fwdBytes ++ (List.range n).flatMap (bin238StepFwd trapdoor i) ++ bin238StepFwd trapdoor i n).length / 8 :=
        Nat.div_le_div_right (by simp)
      have ht1 : tailAccLen tails ≤ tailAccLen (tails ++ (List.range n).flatMap (bin238StepTails trapdoor i)) :=
        tailAccLen_mono_append _ _
      have ht2 : tailAccLen (tails ++ (List.range n).flatMap (bin238StepTails trapdoor i)) ≤
          tailAccLen (tails ++ (List.range n).flatMap (bin238StepTails trapdoor i) ++ bin238StepTails trapdoor i n) :=
        tailAccLen_mono_append _ _
      rw [happF] at hq2 hst1 hlen1 inv1
      rw [happT] at ht2 hst1 htlen1 inv1
      exact ⟨st + st1, sn1, hrn.trans hr1, by omega, hpc1, hx22_1, hx29_1, hx30_1,
        by omega, by omega, inv1⟩
  obtain ⟨st, s69, hrloop, hst, hpc69, hx22_69, _, _, _, _, inv69⟩ := hloop 11 (Nat.le_refl 11)
  have hpc69' : s69.pc = pcAt 69 := by simpa only [Nat.lt_irrefl, ite_false] using hpc69
  have htails_eq : tails ++ (List.range 11).flatMap (bin238StepTails trapdoor i) = tails1 := rfl
  rw [htails_eq] at hst inv69
  change st = 32 * 11 + 5 * (fwd1.length / 8 - fwdBytes.length / 8) +
    4 * (tailAccLen tails1 - tailAccLen tails) at hst
  exact ⟨1 + st, s69, h57'.trans hrloop, by omega, hpc69', hx22_69, inv69⟩

private theorem openRuns_rec_iter {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (ht : t < positions.card) (hpc : s.pc = pcAt 20)
    (hbd : fwdBytes.length ≤ 497 * t)
    (htbd : tails.length ≤ 11 * t)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let idx : Index := (positions.sort (· ≤ ·))[t]'(by simpa using ht)
    let fwd' := fwdBytes ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) idx
    let tails' := tails ++ recordTails (tdNode trapdoor) idx
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps = 488 + 5 * (fwd'.length / 8 - fwdBytes.length / 8) +
        4 * (tailAccLen tails' - tailAccLen tails) ∧
      s'.pc = (if t + 1 < positions.card then pcAt 20 else pcAt 75) ∧
      fwd'.length ≤ 497 * (t + 1) ∧
      tails'.length ≤ 11 * (t + 1) ∧
      RecInv trapdoor positions (t + 1) fwd' tails' s' := by
  intro idx fwd' tails'
  have hcard := positions_card_le positions
  have hidx_lt : idx.val < 16777216 := idx.isLt
  obtain ⟨s32, hrsalt, hpc32, hx22_32, inv32⟩ := openRuns_rec_salt ht hpc (by omega) (by omega) inv
  change s32.getReg .x22 = BitVec.ofNat 64 idx.val at hx22_32
  set fwdSalt := fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24
  change RecInv trapdoor positions t fwdSalt tails s32 at inv32
  have hlenSalt : fwdSalt.length = fwdBytes.length + 24 := by
    simp only [fwdSalt, List.length_append, bitsToBytes_length]
  obtain ⟨s45, hr256, hpc45, hx22_45, hx29_45, hlen45, inv45⟩ :=
    openRuns_rec_bin256 (i := idx) hpc32 hx22_32 (by omega) (by omega) inv32
  set fwd256 := fwdSalt ++ (List.range 2).flatMap (bin256StepFwd trapdoor idx)
  obtain ⟨st240, s57, hr240, hst240, hpc57, hx22_57, hx29_57, hlen57, inv57⟩ :=
    openRuns_rec_bin240 (i := idx) hpc45 hx22_45 hx29_45 (by omega) (by omega) inv45
  set fwd240 := fwd256 ++ (List.range 3).flatMap (bin240StepFwd trapdoor idx)
  obtain ⟨st238, s69, hr238, hst238, hpc69, hx22_69, inv69⟩ :=
    openRuns_rec_bin238 (i := idx) hpc57 hx22_57 hx29_57 (by omega) (by omega) inv57
  have happF : fwd240 ++ (List.range 11).flatMap (bin238StepFwd trapdoor idx) = fwd' := by
    simp only [fwd', fwd240, fwd256, fwdSalt, recordFwd, ← binPathFwd_split trapdoor idx, List.append_assoc]
  have happT : tails ++ binPathTails (tdNode trapdoor) idx = tails' := rfl
  rw [happF, happT] at hst238 inv69
  have hlen_recF : fwd'.length ≤ 497 * (t + 1) := by
    have hr := recordFwd_length (tdNode trapdoor) (tdSalt trapdoor) idx
    simp only [fwd', List.length_append]; omega
  have hlen_recT : tails'.length ≤ 11 * (t + 1) := by
    have hr := recordTails_length (tdNode trapdoor) idx
    simp only [tails', List.length_append]; omega
  have hqSalt : fwdSalt.length / 8 = fwdBytes.length / 8 + 3 := by omega
  have hq256 : fwd256.length / 8 = fwdSalt.length / 8 + 8 := by omega
  have hq1 : fwd256.length / 8 ≤ fwd240.length / 8 := Nat.div_le_div_right (by omega)
  have hq2 : fwd240.length / 8 ≤ fwd'.length / 8 := by
    apply Nat.div_le_div_right
    rw [← happF]
    simp only [List.length_append]
    omega
  -- Tail: 57..62
  have hcap_lt : capLeafNat idx.val < 256 := capLeafOf_lt idx
  have h57 := step_ADD (by omega) hpc69 (rfl : openingInstr 69 = .base (.ADD .x6 .x21 .x22))
  let s58 := (s69.setReg .x6 (BitVec.ofNat 64 (4096 + capLeafNat idx.val))).setPC (pcAt 70)
  have h57' : OpenRuns s69 1 1 s58 := by
    have hr21 : s69.getReg .x21 = BitVec.ofNat 64 4096 := inv69.rx21
    rw [hr21, hx22_69] at h57
    simpa only [capLeafNat, bv64_ofNat_add, s58] using h57
  have h58 := step_ADDI (by omega) (rfl : s58.pc = pcAt 70)
    (rfl : openingInstr 70 = .base (.ADDI .x7 .x0 (1#12)))
  let s59 := (s58.setReg .x7 1#64).setPC (pcAt 71)
  have h58' : OpenRuns s58 1 1 s59 := by
    have hv : s58.getReg .x0 + signExtend12 (1#12) = 1#64 := by
      change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s59] using h58
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have haddr59 : s59.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (4096 + capLeafNat idx.val) := by
    change BitVec.ofNat 64 (4096 + capLeafNat idx.val) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h59 := step_SB (by omega) (rfl : s59.pc = pcAt 71)
    (rfl : openingInstr 71 = .base (.SB .x6 .x7 (0#12)))
    (by rw [haddr59]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s60 := (s59.setByte (BitVec.ofNat 64 (4096 + capLeafNat idx.val)) 1#8).setPC (pcAt 72)
  have h59' : OpenRuns s59 1 1 s60 := by
    have htr : (s59.getReg .x7).truncate 8 = 1#8 := by
      change (1#64 : Word).truncate 8 = 1#8; decide
    simpa only [haddr59, htr, s60] using h59
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have h60 := step_ADDI (by omega) (rfl : s60.pc = pcAt 72)
    (rfl : openingInstr 72 = .base (.ADDI .x24 .x24 (8#12)))
  let s61 := (s60.setReg .x24 (BitVec.ofNat 64 (7449087968 + 8 * (t + 1)))).setPC (pcAt 73)
  have h60' : OpenRuns s60 1 1 s61 := by
    have hr24 : s60.getReg .x24 = BitVec.ofNat 64 (7449087968 + 8 * t) := by
      simp only [s60, s59, s58, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x7 .x24 (by decide),
        getReg_setReg_ne' .x6 .x24 (by decide)]
      exact inv69.rx24
    have hv : s60.getReg .x24 + signExtend12 (8#12) =
        BitVec.ofNat 64 (7449087968 + 8 * (t + 1)) := by
      rw [hr24, hse8, bv64_ofNat_add]; congr 1
    simpa only [hv, s61] using h60
  have h61 := step_ADDI (by omega) (rfl : s61.pc = pcAt 73)
    (rfl : openingInstr 73 = .base (.ADDI .x27 .x27 (4095#12)))
  let s62 := (s61.setReg .x27 (BitVec.ofNat 64 (positions.card - (t + 1)))).setPC (pcAt 74)
  have h61' : OpenRuns s61 1 1 s62 := by
    have hr27 : s61.getReg .x27 = BitVec.ofNat 64 ((positions.card - (t + 1)) + 1) := by
      simp only [s61, s60, s59, s58, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x24 .x27 (by decide),
        getReg_setReg_ne' .x7 .x27 (by decide),
        getReg_setReg_ne' .x6 .x27 (by decide)]
      rw [inv69.rx27]; congr 1; omega
    rw [hr27, bv64_add_neg1] at h61; exact h61
  have hpres62 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x24 → r ≠ .x27 →
      s62.getReg r = s69.getReg r := fun r h6 h7 h24 h27 => by
    simp only [s62, s61, s60, s59, s58, MachineState.getReg_setPC, getReg_setByte,
      getReg_setReg_ne' .x27 r (Ne.symm h27),
      getReg_setReg_ne' .x24 r (Ne.symm h24),
      getReg_setReg_ne' .x7 r (Ne.symm h7),
      getReg_setReg_ne' .x6 r (Ne.symm h6)]
  have hmem62 : ∀ a, s62.getByte a =
      (s69.setByte (BitVec.ofNat 64 (4096 + capLeafNat idx.val)) 1#8).getByte a := fun a => by
    simp only [s62, s61, s60, s59, s58, getByte_setPC, getByte_setReg]; rfl
  have hro62 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s62 := by
    intro a ha
    simp only [s62, MachineState.getMem_setPC, MachineState.getMem_setReg, s61, s60]
    exact readOnly_setByte_cap (4096 + capLeafNat idx.val) 1#8 inv69.ro (by omega) (by omega) a ha
  have hw62 : WriterState s62 fwd' := by
    have hw' := writerState_setByte_outside (4096 + capLeafNat idx.val) 1#8 inv69.writer
      (by omega) (Or.inl (by omega)) (by omega)
    exact ⟨by rw [hpres62 .x25 (by decide) (by decide) (by decide) (by decide)]; exact inv69.writer.rx25,
      by rw [hpres62 .x13 (by decide) (by decide) (by decide) (by decide)]; exact inv69.writer.rx13,
      by rw [hpres62 .x14 (by decide) (by decide) (by decide) (by decide)]; exact inv69.writer.rx14,
      fun j hj => by rw [hpres62 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv69.writer.wbufLo j hj,
      fun j h1 h2 => by rw [hpres62 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv69.writer.wbufHi j h1 h2,
      fun j hj => by rw [hmem62]; exact hw'.memDwords j hj⟩
  have ht62 : TailState s62 tails' := by
    have htb : tailBufBase = 25769803776 := rfl
    have ht' := tailState_setByte_outside (4096 + capLeafNat idx.val) 1#8 inv69.tail (by omega) (by omega)
    exact ⟨by rw [hpres62 .x31 (by decide) (by decide) (by decide) (by decide)]; exact inv69.tail.rx31,
      by rw [hpres62 .x15 (by decide) (by decide) (by decide) (by decide)]; exact inv69.tail.rx15,
      by rw [hpres62 .x16 (by decide) (by decide) (by decide) (by decide)]; exact inv69.tail.rx16,
      by rw [hpres62 .x17 (by decide) (by decide) (by decide) (by decide)]; exact inv69.tail.rx17,
      fun j hj => by rw [hmem62]; exact ht'.memTail j hj⟩
  have hcap62 : ∀ c < 256, s62.getByte (BitVec.ofNat 64 (4096 + c)) =
      if capMark16Prefix positions (t + 1) c then 1#8 else 0#8 := by
    intro c hc
    rw [hmem62, set_byte_read]
    have hopen : openingIndex positions t = idx.val := by simp only [openingIndex, dif_pos ht]; rfl
    by_cases hceq : c = capLeafNat idx.val
    · subst hceq
      rw [if_pos rfl]
      have htr : capMark16Prefix positions (t + 1) (capLeafNat idx.val) = true := by
        simp only [capMark16Prefix, decide_eq_true_eq]
        exact ⟨t, by omega, by rw [hopen]⟩
      rw [htr]; rfl
    · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega)), inv69.cap16 c hc]
      have hsame : capMark16Prefix positions (t + 1) c = capMark16Prefix positions t c := by
        simp only [capMark16Prefix]
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
  have hinv62 : RecInv trapdoor positions (t + 1) fwd' tails' s62 :=
    ⟨by rw [hpres62 .x2 (by decide) (by decide) (by decide) (by decide)]; exact inv69.rx2,
     by rw [hpres62 .x9 (by decide) (by decide) (by decide) (by decide)]; exact inv69.rx9,
     by rw [hpres62 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv69.rx18,
     by rw [hpres62 .x21 (by decide) (by decide) (by decide) (by decide)]; exact inv69.rx21,
     by simp only [s62, MachineState.getReg_setPC, getReg_setReg_ne' .x27 .x24 (by decide)]; rfl,
     by rw [hpres62 .x26 (by decide) (by decide) (by decide) (by decide)]; exact inv69.rx26,
     rfl, hro62, hw62, ht62, hcap62⟩
  have htail := ((((h57'.trans h58').trans h59').trans h60').trans h61')
  have hbody := (((hrsalt.trans hr256).trans hr240).trans hr238).trans htail
  by_cases hmore : t + 1 < positions.card
  · have h62 := step_BNE_taken (by omega) (rfl : s62.pc = pcAt 74)
      (rfl : openingInstr 74 = .base (.BNE .x27 .x0 (7976#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) ≠ BitVec.ofNat 64 0
          exact bv64_ofNat_ne (by omega) (by decide) (by omega))
      (by decide : pcAt 74 + signExtend13 (7976#13) = pcAt 20)
    exact ⟨32 + 76 + st240 + st238 + 5 + 1, s62.setPC (pcAt 20), hbody.trans h62,
      by omega, by rw [if_pos hmore]; rfl, hlen_recF, hlen_recT, hinv62.setPC (pcAt 20)⟩
  · have hdone : positions.card - (t + 1) = 0 := by omega
    have h62 := step_BNE_not_taken (by omega) (rfl : s62.pc = pcAt 74)
      (rfl : openingInstr 74 = .base (.BNE .x27 .x0 (7976#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) = BitVec.ofNat 64 0; rw [hdone])
    exact ⟨32 + 76 + st240 + st238 + 5 + 1, s62.setPC (pcAt 75), hbody.trans h62,
      by omega, by rw [if_neg hmore]; rfl, hlen_recF, hlen_recT, hinv62.setPC (pcAt 75)⟩

private theorem openRuns_rec_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s20 : MachineState}
    (hne : 0 < positions.card) (hpc : s20.pc = pcAt 20)
    (inv0 : RecInv trapdoor positions 0 [] [] s20) :
    let recFwd := (positions.sort (· ≤ ·)).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
    let recTails := (positions.sort (· ≤ ·)).flatMap (recordTails (tdNode trapdoor))
    ∃ steps s63, OpenRuns s20 steps steps s63 ∧
      steps = 488 * positions.card + 5 * (recFwd.length / 8) + 4 * tailAccLen recTails ∧
      s63.pc = pcAt 75 ∧
      s63.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s63.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s63.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s63.getReg .x26 = BitVec.ofNat 64 11878272992 ∧
      recFwd.length ≤ 497 * positions.card ∧
      recTails.length ≤ 11 * positions.card ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s63 ∧
      WriterState s63 recFwd ∧
      TailState s63 recTails ∧
      CapLevelMarks s63 positions 16 := by
  intro recFwd recTails
  have hloop : ∀ t ≤ positions.card,
      let curF := ((positions.sort (· ≤ ·)).take t).flatMap
        (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
      let curT := ((positions.sort (· ≤ ·)).take t).flatMap
        (recordTails (tdNode trapdoor))
      ∃ steps st, OpenRuns s20 steps steps st ∧
        steps = 488 * t + 5 * (curF.length / 8) + 4 * tailAccLen curT ∧
        st.pc = (if t < positions.card then pcAt 20 else pcAt 75) ∧
        curF.length ≤ 497 * t ∧
        curT.length ≤ 11 * t ∧
        RecInv trapdoor positions t curF curT st := by
    intro t ht
    induction t with
    | zero =>
      dsimp only
      simp only [List.take_zero, List.flatMap_nil, List.length_nil, tailAccLen_nil, Nat.mul_zero,
        Nat.zero_div, Nat.add_zero]
      exact ⟨0, s20, OpenRuns.refl s20, rfl,
        by rw [if_pos hne]; exact hpc, Nat.le_refl 0, Nat.le_refl 0, inv0⟩
    | succ t ih =>
      obtain ⟨st, stState, hr, hst, hpct, hbdt, htbdt, invt⟩ := ih (by omega)
      have hpct' : stState.pc = pcAt 20 := by simpa only [show t < positions.card by omega, ite_true] using hpct
      obtain ⟨st1, stNext, hr1, hst1, hpc1, hbd1, htbd1, inv1⟩ :=
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
      have hqmono : (((positions.sort (· ≤ ·)).take t).flatMap
            (recordFwd (tdNode trapdoor) (tdSalt trapdoor))).length / 8 ≤
          (((positions.sort (· ≤ ·)).take (t + 1)).flatMap
            (recordFwd (tdNode trapdoor) (tdSalt trapdoor))).length / 8 := by
        rw [htakeF]; exact Nat.div_le_div_right (by simp)
      have htmono : tailAccLen (((positions.sort (· ≤ ·)).take t).flatMap
            (recordTails (tdNode trapdoor))) ≤
          tailAccLen (((positions.sort (· ≤ ·)).take (t + 1)).flatMap
            (recordTails (tdNode trapdoor))) := by
        rw [htakeT]; exact tailAccLen_mono_append _ _
      rw [← htakeF] at hst1 hbd1 inv1
      rw [← htakeT] at hst1 htbd1 inv1
      exact ⟨st + st1, stNext, hr.trans hr1, by omega, hpc1, hbd1, htbd1, inv1⟩
  obtain ⟨steps, s63, hr, hst, hpc63, hbdEnd, htbdEnd, invEnd⟩ :=
    hloop positions.card (Nat.le_refl _)
  have hpc63' : s63.pc = pcAt 75 := by simpa only [Nat.lt_irrefl, ite_false] using hpc63
  have htakeAll : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) := by
    have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
    rw [← hlen, List.take_length]
  rw [htakeAll] at hst hbdEnd htbdEnd invEnd
  refine ⟨steps, s63, hr, hst, hpc63',
    invEnd.rx2, invEnd.rx9, invEnd.rx21, invEnd.rx26,
    hbdEnd, htbdEnd, invEnd.ro, invEnd.writer, invEnd.tail, ?_⟩
  intro idx hidx
  have hidx256 : idx < 256 := by rw [levelSize_16] at hidx; exact hidx
  have hmo16 : capMarkOff 16 = 0 := by decide
  rw [hmo16, Nat.add_zero, invEnd.cap16 idx hidx256, capMark16Prefix_card]

/-! ### 8. Cap Frontier Pass (`63..92`) -/

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
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475936
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx26 : s.getReg .x26 = BitVec.ofNat 64 11878272992
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (16 + step))
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 24)
  boundFwd : fwdBytes.length ≤ 497 * positions.card +
    29 * (∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k))
  boundTails : tails.length ≤ 11 * positions.card +
    (∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k))
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  writer : WriterState s fwdBytes
  tail : TailState s tails
  capMarks : CapLevelMarks s positions (16 + step)

private structure CapPairInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (step q : Nat) (fwdBytes : List Byte) (tails : List (BitVec 6))
    (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475936
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase (16 + step))
  rx19 : s.getReg .x19 = BitVec.ofNat 64 (levelSize (16 + step))
  rx20 : s.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff (16 + step))
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx22 : s.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (16 + step + 1))
  rx23 : s.getReg .x23 = BitVec.ofNat 64 (levelSize (16 + step) / 2)
  rx24 : s.getReg .x24 = BitVec.ofNat 64 q
  rx26 : s.getReg .x26 = BitVec.ofNat 64 11878272992
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (16 + step))
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 24)
  boundFwd : fwdBytes.length ≤ 497 * positions.card +
    29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
          (∑ j ∈ Finset.range q, capPairFrontier positions (16 + step) j))
  boundTails : tails.length ≤ 11 * positions.card +
    ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
     (∑ j ∈ Finset.range q, capPairFrontier positions (16 + step) j))
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  writer : WriterState s fwdBytes
  tail : TailState s tails
  curMarks : CapLevelMarks s positions (16 + step)
  nextMarks : ∀ j < q, s.getByte (BitVec.ofNat 64 (4096 + capMarkOff (16 + step + 1) + j)) =
    if capMark positions (16 + step + 1) j then 1#8 else 0#8

private theorem openRuns_cap_pair_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {step q : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hstep : step < 8) (hq : q < levelSize (16 + step) / 2) (hpc : s.pc = pcAt 86)
    (inv : CapPairInv trapdoor positions step q fwdBytes tails s) :
    let l := 16 + step
    let fwd1 := fwdBytes ++ capPairFwd trapdoor positions l q
    let tails1 := tails ++ capPairTails trapdoor positions l q
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 10 + 28 * capPairFrontier positions l q +
        5 * (fwd1.length / 8 - fwdBytes.length / 8) +
        4 * (tailAccLen tails1 - tailAccLen tails) ∧
      s1.pc = (if q + 1 < levelSize l / 2 then pcAt 86 else pcAt 103) ∧
      CapPairInv trapdoor positions step (q + 1) fwd1 tails1 s1 := by
  intro l fwd1 tails1
  have hql : q < levelSize l / 2 := hq
  have hcur_inv : CapLevelMarks s positions l := inv.curMarks
  have hinv_bdF : fwdBytes.length ≤ 497 * positions.card +
      29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
            (∑ j ∈ Finset.range q, capPairFrontier positions l j)) := inv.boundFwd
  have hinv_bdT : tails.length ≤ 11 * positions.card +
      ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
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
  have h74 := step_SLLI (by omega) hpc (rfl : openingInstr 86 = .base (.SLLI .x6 .x24 (1#6)))
  let s75 := (s.setReg .x6 (BitVec.ofNat 64 (2 * q))).setPC (pcAt 87)
  have h74' : OpenRuns s 1 1 s75 := by
    have hv : s.getReg .x24 <<< (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (2 * q) := by
      rw [inv.rx24]; change BitVec.ofNat 64 q <<< 1 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hv, s75] using h74
  have h75 := step_ADD (by omega) (rfl : s75.pc = pcAt 87)
    (rfl : openingInstr 87 = .base (.ADD .x6 .x20 .x6))
  let s76 := (s75.setReg .x6 (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q))).setPC (pcAt 88)
  have h75' : OpenRuns s75 1 1 s76 := by
    have hr20 : s75.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) := inv.rx20
    rw [hr20] at h75
    simpa only [show s75.getReg .x6 = BitVec.ofNat 64 (2 * q) from rfl, bv64_ofNat_add, s76] using h75
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  have haddr76 : s76.getReg .x6 + signExtend12 (0#12) =
      BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) := by
    change BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h76 := step_LBU (by omega) (rfl : s76.pc = pcAt 88)
    (rfl : openingInstr 88 = .base (.LBU .x7 .x6 (0#12)))
    (by rw [haddr76]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s77 := (s76.setReg .x7 (if mL then 1#64 else 0#64)).setPC (pcAt 89)
  have h76' : OpenRuns s76 1 1 s77 := by
    have hb : s76.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q)) =
        if mL then 1#8 else 0#8 := hcur_inv (2 * q) (by omega)
    simpa only [haddr76, hb, bool_byte_zeroExtend mL, s77] using h76
  have haddr77 : s77.getReg .x6 + signExtend12 (1#12) =
      BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1)) := by
    change BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) + _ = _
    rw [hse1, bv64_ofNat_add, Nat.add_assoc]
  have h77 := step_LBU (by omega) (rfl : s77.pc = pcAt 89)
    (rfl : openingInstr 89 = .base (.LBU .x8 .x6 (1#12)))
    (by rw [haddr77]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s78 := (s77.setReg .x8 (if mR then 1#64 else 0#64)).setPC (pcAt 90)
  have h77' : OpenRuns s77 1 1 s78 := by
    have hb : s77.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1))) =
        if mR then 1#8 else 0#8 := hcur_inv (2 * q + 1) (by omega)
    simpa only [haddr77, hb, bool_byte_zeroExtend mR, s78] using h77
  have h78 := step_OR (by omega) (rfl : s78.pc = pcAt 90)
    (rfl : openingInstr 90 = .base (.OR .x11 .x7 .x8))
  let s79 := (s78.setReg .x11 (if (mL || mR) then 1#64 else 0#64)).setPC (pcAt 91)
  have h78' : OpenRuns s78 1 1 s79 := by
    simpa only [show s78.getReg .x7 = if mL then 1#64 else 0#64 from rfl,
      show s78.getReg .x8 = if mR then 1#64 else 0#64 from rfl,
      bool_word_or mL mR, s79] using h78
  have h79 := step_ADD (by omega) (rfl : s79.pc = pcAt 91)
    (rfl : openingInstr 91 = .base (.ADD .x6 .x22 .x24))
  let s80 := (s79.setReg .x6 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q))).setPC (pcAt 92)
  have h79' : OpenRuns s79 1 1 s80 := by
    have hr22 : s79.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) := inv.rx22
    have hr24 : s79.getReg .x24 = BitVec.ofNat 64 q := inv.rx24
    rw [hr22, hr24, bv64_ofNat_add] at h79; exact h79
  have haddr80 : s80.getReg .x6 + signExtend12 (0#12) =
      BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) := by
    change BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h80 := step_SB (by omega) (rfl : s80.pc = pcAt 92)
    (rfl : openingInstr 92 = .base (.SB .x6 .x11 (0#12)))
    (by rw [haddr80]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s81 := (s80.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q))
    (if (mL || mR) then 1#8 else 0#8)).setPC (pcAt 93)
  have h80' : OpenRuns s80 1 1 s81 := by
    simpa only [haddr80, show s80.getReg .x11 = if (mL || mR) then 1#64 else 0#64 from rfl,
      bool_word_truncate8 (mL || mR), s81] using h80
  have hpre : OpenRuns s 7 7 s81 :=
    (((((h74'.trans h75').trans h76').trans h77').trans h78').trans h79').trans h80'
  have hpres81 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x11 →
      s81.getReg r = s.getReg r := fun r h6 h7 h8 h11 => by
    simp only [s81, s80, s79, s78, s77, s76, s75,
      MachineState.getReg_setPC, getReg_setByte,
      getReg_setReg_ne' .x6 r (Ne.symm h6),
      getReg_setReg_ne' .x11 r (Ne.symm h11),
      getReg_setReg_ne' .x8 r (Ne.symm h8),
      getReg_setReg_ne' .x7 r (Ne.symm h7)]
  have hx7_81 : s81.getReg .x7 = if mL then 1#64 else 0#64 := by
    simp only [s81, MachineState.getReg_setPC, getReg_setByte]; rfl
  have hx8_81 : s81.getReg .x8 = if mR then 1#64 else 0#64 := by
    simp only [s81, MachineState.getReg_setPC, getReg_setByte]; rfl
  -- Bounds at s81
  have hfront_sum_le : (∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
      (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j) ≤ capFrontierCount positions := by
    have hq_le : (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j) ≤
        levelFrontierCount positions l := by
      rw [← sum_capPairFrontier_eq]
      exact sum_range_le_of_le (capPairFrontier positions l) (by omega)
    have hs_eq : (∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
        levelFrontierCount positions l =
        ∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (16 + k) := by
      rw [Finset.sum_range_succ]
    have hs_le : (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (16 + k)) ≤
        capFrontierCount positions := by
      unfold capFrontierCount
      exact sum_range_le_of_le (fun k => levelFrontierCount positions (16 + k)) (by omega)
    omega
  have hcap128 := cap_frontier_le_128 positions
  have hfwd_cap : fwdBytes.length ≤ 497 * 16777216 + 29 * 128 := by
    have h2 : (∑ j ∈ Finset.range q, capPairFrontier positions l j) ≤
        ∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j :=
      sum_range_le_of_le (capPairFrontier positions l) (by omega)
    omega
  have htails_cap : tails.length ≤ 11 * 16777216 + 128 := by
    have h2 : (∑ j ∈ Finset.range q, capPairFrontier positions l j) ≤
        ∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j :=
      sum_range_le_of_le (capPairFrontier positions l) (by omega)
    omega
  have hro81 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s81 := by
    intro a ha
    simp only [s81, MachineState.getMem_setPC]
    exact readOnly_setByte_cap (4096 + capMarkOff (l + 1) + q) _ inv.ro (by omega) (by omega) a ha
  have hw81 : WriterState s81 fwdBytes := by
    have hw' := writerState_setByte_outside (4096 + capMarkOff (l + 1) + q)
      (if (mL || mR) then 1#8 else 0#8) inv.writer (by omega) (Or.inl (by omega)) (by omega)
    exact ⟨by rw [hpres81 .x25 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx25,
      by rw [hpres81 .x13 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx13,
      by rw [hpres81 .x14 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx14,
      fun j hj => by rw [hpres81 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.wbufLo j hj,
      fun j h1 h2 => by rw [hpres81 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.wbufHi j h1 h2,
      fun j hj => by simp only [s81, getByte_setPC]; exact hw'.memDwords j hj⟩
  have ht81 : TailState s81 tails := by
    have htb : tailBufBase = 25769803776 := rfl
    have ht' := tailState_setByte_outside (4096 + capMarkOff (l + 1) + q)
      (if (mL || mR) then 1#8 else 0#8) inv.tail (by omega) (by omega)
    exact ⟨by rw [hpres81 .x31 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx31,
      by rw [hpres81 .x15 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx15,
      by rw [hpres81 .x16 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx16,
      by rw [hpres81 .x17 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx17,
      fun j hj => by simp only [s81, getByte_setPC]; exact ht'.memTail j hj⟩
  have hcur81 : CapLevelMarks s81 positions l := by
    intro idx hidx
    simp only [s81, getByte_setPC, set_byte_read]
    rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
    exact hcur_inv idx hidx
  have hnext81 : ∀ j < q + 1, s81.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + j)) =
      if capMark positions (l + 1) j then 1#8 else 0#8 := by
    intro j hj
    simp only [s81, getByte_setPC, set_byte_read]
    by_cases hjq : j = q
    · subst j
      have hlt : 2 * q + 1 < levelSize l := by omega
      rw [if_pos rfl]
      change (if (capMark positions l (2 * q) || capMark positions l (2 * q + 1)) then 1#8 else 0#8) = _
      rw [capMark_succ positions l q (by omega), if_pos hlt]
    · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
      exact inv.nextMarks j (by omega)
  -- Branch on mL = mR to reach pcAt 101
  have hto89 : ∃ n89 s89, OpenRuns s81 n89 n89 s89 ∧
      n89 ≤ 1 + 28 * capPairFrontier positions l q +
        5 * (fwd1.length / 8 - fwdBytes.length / 8) +
        4 * (tailAccLen tails1 - tailAccLen tails) ∧
      s89.pc = pcAt 101 ∧
      s89.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s89.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s89.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l) ∧
      s89.getReg .x19 = BitVec.ofNat 64 (levelSize l) ∧
      s89.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
      s89.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s89.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
      s89.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) ∧
      s89.getReg .x24 = BitVec.ofNat 64 q ∧
      s89.getReg .x26 = BitVec.ofNat 64 11878272992 ∧
      s89.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) ∧
      s89.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 24) ∧
      fwd1.length ≤ 497 * positions.card +
        29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
              (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) ∧
      tails1.length ≤ 11 * positions.card +
        ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
         (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s89 ∧
      WriterState s89 fwd1 ∧
      TailState s89 tails1 ∧
      CapLevelMarks s89 positions l ∧
      (∀ j < q + 1, s89.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + j)) =
        if capMark positions (l + 1) j then 1#8 else 0#8) := by
    by_cases hsame : mL = mR
    · have h81 := step_BEQ_taken (by omega) (rfl : s81.pc = pcAt 93)
        (rfl : openingInstr 93 = .base (.BEQ .x7 .x8 (32#13)))
        (by rw [hx7_81, hx8_81, hsame])
        (by decide : pcAt 93 + signExtend13 (32#13) = pcAt 101)
      have hf1 : fwd1 = fwdBytes := by
        change fwdBytes ++ (if mL = mR then [] else _) = _
        rw [if_pos hsame, List.append_nil]
      have ht1 : tails1 = tails := by
        change tails ++ (if mL = mR then [] else _) = _
        rw [if_pos hsame, List.append_nil]
      rw [hf1, ht1]
      have hlenF : fwdBytes.length ≤ 497 * positions.card +
          29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
                (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ]; omega
      have hlenT : tails.length ≤ 11 * positions.card +
          ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
           (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ]; omega
      exact ⟨1, s81.setPC (pcAt 101), h81, by omega, rfl,
        by rw [MachineState.getReg_setPC, hpres81 .x2 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx2,
        by rw [MachineState.getReg_setPC, hpres81 .x9 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx9,
        by rw [MachineState.getReg_setPC, hpres81 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx18,
        by rw [MachineState.getReg_setPC, hpres81 .x19 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx19,
        by rw [MachineState.getReg_setPC, hpres81 .x20 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx20,
        by rw [MachineState.getReg_setPC, hpres81 .x21 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx21,
        by rw [MachineState.getReg_setPC, hpres81 .x22 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx22,
        by rw [MachineState.getReg_setPC, hpres81 .x23 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx23,
        by rw [MachineState.getReg_setPC, hpres81 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24,
        by rw [MachineState.getReg_setPC, hpres81 .x26 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx26,
        by rw [MachineState.getReg_setPC, hpres81 .x29 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx29,
        by rw [MachineState.getReg_setPC, hpres81 .x30 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx30,
        hlenF, hlenT, hro81, hw81.of_eq, ht81.of_eq, hcur81, hnext81⟩
    · have hcpf : capPairFrontier positions l q = 1 := by
        change (if (mL != mR) = true then 1 else 0) = 1
        exact bool_bne_one_of_ne hsame
      have h81 := step_BEQ_not_taken (by omega) (rfl : s81.pc = pcAt 93)
        (rfl : openingInstr 93 = .base (.BEQ .x7 .x8 (32#13)))
        (by rw [hx7_81, hx8_81]; exact bool_word_ne_of_ne hsame)
      let s82 := s81.setPC (pcAt 94)
      have h82 := step_SLLI (by omega) (rfl : s82.pc = pcAt 94)
        (rfl : openingInstr 94 = .base (.SLLI .x6 .x24 (6#6)))
      let s83 := (s82.setReg .x6 (BitVec.ofNat 64 (64 * q))).setPC (pcAt 95)
      have h82' : OpenRuns s82 1 1 s83 := by
        have hr24 : s82.getReg .x24 = BitVec.ofNat 64 q := by
          rw [show s82.getReg .x24 = s81.getReg .x24 from rfl,
            hpres81 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24
        have hv : s82.getReg .x24 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * q) := by
          rw [hr24]; change BitVec.ofNat 64 q <<< 6 = _; rw [bv64_shl]; congr 1; omega
        simpa only [hv, s83] using h82
      have h83 := step_SLLI (by omega) (rfl : s83.pc = pcAt 95)
        (rfl : openingInstr 95 = .base (.SLLI .x11 .x24 (5#6)))
      let s84 := (s83.setReg .x11 (BitVec.ofNat 64 (32 * q))).setPC (pcAt 96)
      have h83' : OpenRuns s83 1 1 s84 := by
        have hr24 : s83.getReg .x24 = BitVec.ofNat 64 q := by
          simp only [s83, s82, MachineState.getReg_setPC,
            getReg_setReg_ne' .x6 .x24 (by decide)]
          rw [hpres81 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24
        have hv : s83.getReg .x24 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (32 * q) := by
          rw [hr24]; change BitVec.ofNat 64 q <<< 5 = _; rw [bv64_shl]; congr 1; omega
        simpa only [hv, s84] using h83
      have h84 := step_ADD (by omega) (rfl : s84.pc = pcAt 96)
        (rfl : openingInstr 96 = .base (.ADD .x10 .x6 .x11))
      let s85 := (s84.setReg .x10 (BitVec.ofNat 64 (96 * q))).setPC (pcAt 97)
      have h84' : OpenRuns s84 1 1 s85 := by
        have hv : s84.getReg .x6 + s84.getReg .x11 = BitVec.ofNat 64 (96 * q) := by
          change BitVec.ofNat 64 (64 * q) + BitVec.ofNat 64 (32 * q) = _
          rw [bv64_ofNat_add]; congr 1; omega
        simpa only [hv, s85] using h84
      have h85 := step_ADD (by omega) (rfl : s85.pc = pcAt 97)
        (rfl : openingInstr 97 = .base (.ADD .x10 .x18 .x10))
      let s86 := (s85.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q))).setPC (pcAt 98)
      have h85' : OpenRuns s85 1 1 s86 := by
        have hr18 : s85.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l) := by
          simp only [s85, s84, s83, s82, MachineState.getReg_setPC,
            getReg_setReg_ne' .x10 .x18 (by decide),
            getReg_setReg_ne' .x11 .x18 (by decide),
            getReg_setReg_ne' .x6 .x18 (by decide)]
          rw [hpres81 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx18
        rw [hr18] at h85
        simpa only [show s85.getReg .x10 = BitVec.ofNat 64 (96 * q) from rfl, bv64_ofNat_add, s86] using h85
      have hmid : OpenRuns s81 5 5 s86 := (((h81.trans h82').trans h83').trans h84').trans h85'
      have hlen_bdF : fwdBytes.length + 29 ≤ 497 * positions.card +
          29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
                (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ, hcpf]; omega
      have hlen_bdT : tails.length + 1 ≤ 11 * positions.card +
          ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
           (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ, hcpf]; omega
      have hr7_86 : s86.getReg .x7 = if mL then 1#64 else 0#64 := by
        simp only [s86, s85, s84, s83, s82, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 .x7 (by decide),
          getReg_setReg_ne' .x11 .x7 (by decide),
          getReg_setReg_ne' .x6 .x7 (by decide)]
        exact hx7_81
      have hpres86 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x11 →
          s86.getReg r = s81.getReg r := fun r h6 h7 _ h10 h11 => by
        simp only [s86, s85, s84, s83, s82, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 r (Ne.symm h10),
          getReg_setReg_ne' .x11 r (Ne.symm h11),
          getReg_setReg_ne' .x6 r (Ne.symm h6)]
      -- Split on mL = true vs mL = false to reach pcAt 100
      have hto88 : ∃ n88 s88 childIdx, OpenRuns s86 n88 n88 s88 ∧ n88 ≤ 2 ∧
          childIdx = (if !mL then 2 * q else 2 * q + 1) ∧
          childIdx < levelSize l ∧
          s88.pc = pcAt 100 ∧
          s88.getReg .x10 = BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l childIdx)) ∧
          (∀ r, r ≠ .x10 → s88.getReg r = s86.getReg r) ∧
          s88.mem = s86.mem := by
        by_cases hmL : mL = true
        · have h86 := step_BEQ_not_taken (by omega) (rfl : s86.pc = pcAt 98)
            (rfl : openingInstr 98 = .base (.BEQ .x7 .x0 (8#13)))
            (by rw [hr7_86, hmL]; change (1#64 : Word) ≠ 0#64; decide)
          let s87 := s86.setPC (pcAt 99)
          have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
          have h87 := step_ADDI (by omega) (rfl : s87.pc = pcAt 99)
            (rfl : openingInstr 99 = .base (.ADDI .x10 .x10 (32#12)))
          have hno : levelBase l + nodeOffset l (2 * q + 1) = levelBase l + 96 * q + 32 := by
            unfold nodeOffset; rw [gapOffset_odd]; omega
          let s88 := (s87.setReg .x10
            (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l (2 * q + 1))))).setPC (pcAt 100)
          have h87' : OpenRuns s87 1 1 s88 := by
            have hv : s87.getReg .x10 + signExtend12 (32#12) =
                BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l (2 * q + 1))) := by
              change BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) + _ = _
              rw [hse32, bv64_ofNat_add]; congr 1; omega
            simpa only [hv, s88] using h87
          refine ⟨2, s88, 2 * q + 1, h86.trans h87', by omega, by rw [hmL]; rfl, by omega, rfl, rfl,
            fun r hr => by simp only [s88, s87, MachineState.getReg_setPC,
              getReg_setReg_ne' .x10 r (Ne.symm hr)], rfl⟩
        · have hmLf : mL = false := Bool.eq_false_iff.mpr hmL
          have h86 := step_BEQ_taken (by omega) (rfl : s86.pc = pcAt 98)
            (rfl : openingInstr 98 = .base (.BEQ .x7 .x0 (8#13)))
            (by rw [hr7_86, hmLf]; rfl)
            (by decide : pcAt 98 + signExtend13 (8#13) = pcAt 100)
          have hno : levelBase l + nodeOffset l (2 * q) = levelBase l + 96 * q := by
            unfold nodeOffset; rw [gapOffset_even]
          refine ⟨1, s86.setPC (pcAt 100), 2 * q, h86, by omega, by rw [hmLf]; rfl, by omega, rfl,
            ?_, fun _ _ => rfl, rfl⟩
          change BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) = _
          rw [hno, Nat.add_assoc]
      obtain ⟨n88, s88, childIdx, hr88, hn88, hchildEq, hchildLt, hpc88, hx10_88, hreg88, hmem88⟩ := hto88
      have hro88 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s88 := by
        intro a ha; change s88.mem a = _; rw [hmem88]; exact hro81 a ha
      have hw88 : WriterState s88 fwdBytes :=
        ⟨by rw [hreg88 .x25 (by decide), hpres86 .x25 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw81.rx25,
         by rw [hreg88 .x13 (by decide), hpres86 .x13 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw81.rx13,
         by rw [hreg88 .x14 (by decide), hpres86 .x14 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw81.rx14,
         fun j hj => by rw [hreg88 .x12 (by decide), hpres86 .x12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw81.wbufLo j hj,
         fun j h1 h2 => by rw [hreg88 .x12 (by decide), hpres86 .x12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw81.wbufHi j h1 h2,
         fun j hj => by change extractByte (s88.mem _) _ = _; rw [hmem88]; exact hw81.memDwords j hj⟩
      have ht88 : TailState s88 tails :=
        ⟨by rw [hreg88 .x31 (by decide), hpres86 .x31 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht81.rx31,
         by rw [hreg88 .x15 (by decide), hpres86 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht81.rx15,
         by rw [hreg88 .x16 (by decide), hpres86 .x16 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht81.rx16,
         by rw [hreg88 .x17 (by decide), hpres86 .x17 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht81.rx17,
         fun j hj => by change extractByte (s88.mem _) _ = _; rw [hmem88]; exact ht81.memTail j hj⟩
      obtain ⟨stC, s89, hrcopy, hstC, hpc89, hreg89, hro89, hw89, ht89, hcap89⟩ :=
        openRuns_call_copy29_tail (callIdx := 100) (l := l) (nodeIdx := childIdx) (jOff := 436#21)
          (fwdBytes := fwdBytes) (tails := tails) (by omega) (by omega) hchildLt
          rfl (by decide) hpc88 hx10_88 (by omega) (by omega) hro88 hw88 ht88
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
      have hpres89 : ∀ r, r = .x2 ∨ r = .x9 ∨ r = .x18 ∨ r = .x19 ∨ r = .x20 ∨ r = .x21 ∨
          r = .x22 ∨ r = .x23 ∨ r = .x24 ∨ r = .x26 ∨ r = .x29 ∨ r = .x30 →
          s89.getReg r = s.getReg r := fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (
          rw [hreg89 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg88 _ (by decide),
            hpres86 _ (by decide) (by decide) (by decide) (by decide) (by decide),
            hpres81 _ (by decide) (by decide) (by decide) (by decide)])
      refine ⟨5 + n88 + stC, s89, (hmid.trans hr88).trans hrcopy, by rw [hcpf]; omega, hpc89,
        by rw [hpres89 .x2 (by simp)]; exact inv.rx2,
        by rw [hpres89 .x9 (by simp)]; exact inv.rx9,
        by rw [hpres89 .x18 (by simp)]; exact inv.rx18,
        by rw [hpres89 .x19 (by simp)]; exact inv.rx19,
        by rw [hpres89 .x20 (by simp)]; exact inv.rx20,
        by rw [hpres89 .x21 (by simp)]; exact inv.rx21,
        by rw [hpres89 .x22 (by simp)]; exact inv.rx22,
        by rw [hpres89 .x23 (by simp)]; exact inv.rx23,
        by rw [hpres89 .x24 (by simp)]; exact inv.rx24,
        by rw [hpres89 .x26 (by simp)]; exact inv.rx26,
        by rw [hpres89 .x29 (by simp)]; exact inv.rx29,
        by rw [hpres89 .x30 (by simp)]; exact inv.rx30,
        by simp only [List.length_append, bitsToBytes_length]; exact hlen_bdF,
        by simp only [List.length_append, List.length_singleton]; exact hlen_bdT,
        hro89, hw89, ht89, ?_, ?_⟩
      · intro idx hidx
        rw [hcap89 (4096 + capMarkOff l + idx) (by omega)]
        change extractByte (s88.mem _) _ = _; rw [hmem88]; exact hcur81 idx hidx
      · intro j hj
        rw [hcap89 (4096 + capMarkOff (l + 1) + j) (by omega)]
        change extractByte (s88.mem _) _ = _; rw [hmem88]; exact hnext81 j hj
  obtain ⟨n89, s89, hr89, hn89, hpc89, hx2, hx9, hx18, hx19, hx20, hx21, hx22, hx23,
      hx24, hx26, hx29, hx30, hlenF1, hlenT1, hro89, hw89, ht89, hcur89, hnext89⟩ := hto89
  have h89 := step_ADDI (by omega) hpc89 (rfl : openingInstr 101 = .base (.ADDI .x24 .x24 (1#12)))
  let s90 := (s89.setReg .x24 (BitVec.ofNat 64 (q + 1))).setPC (pcAt 102)
  have h89' : OpenRuns s89 1 1 s90 := by
    rw [hx24, hse1, bv64_ofNat_add] at h89; exact h89
  have hmkInv : ∀ pc, CapPairInv trapdoor positions step (q + 1) fwd1 tails1 (s90.setPC pc) := fun pc =>
    ⟨hx2, hx9, hx18, hx19, hx20, hx21, hx22, hx23, rfl, hx26, hx29, hx30,
     hlenF1, hlenT1, hro89, hw89.of_eq, ht89.of_eq, hcur89, hnext89⟩
  by_cases hmore : q + 1 < levelSize l / 2
  · have h90 := step_BNE_taken (by omega) (rfl : s90.pc = pcAt 102)
      (rfl : openingInstr 102 = .base (.BNE .x24 .x23 (8128#13)))
      (by change BitVec.ofNat 64 (q + 1) ≠ s89.getReg .x23
          rw [hx23]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 102 + signExtend13 (8128#13) = pcAt 86)
    exact ⟨7 + n89 + 1 + 1, s90.setPC (pcAt 86), ((hpre.trans hr89).trans h89').trans h90,
      by omega, by rw [if_pos hmore]; rfl, hmkInv (pcAt 86)⟩
  · have hdone : q + 1 = levelSize l / 2 := by omega
    have h90 := step_BNE_not_taken (by omega) (rfl : s90.pc = pcAt 102)
      (rfl : openingInstr 102 = .base (.BNE .x24 .x23 (8128#13)))
      (by change BitVec.ofNat 64 (q + 1) = s89.getReg .x23; rw [hx23, hdone])
    exact ⟨7 + n89 + 1 + 1, s90.setPC (pcAt 103), ((hpre.trans hr89).trans h89').trans h90,
      by omega, by rw [if_neg hmore]; rfl, hmkInv (pcAt 103)⟩

private theorem openRuns_cap_lvl_iter {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {step : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hstep : step < 8) (hpc : s.pc = pcAt 77)
    (inv : CapLvlInv trapdoor positions step fwdBytes tails s) :
    let l := 16 + step
    let fwd1 := fwdBytes ++ capLevelFrontierFwd (tdNode trapdoor) positions l
    let tails1 := tails ++ capLevelFrontierTails (tdNode trapdoor) positions l
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 11 + 10 * (levelSize l / 2) + 28 * levelFrontierCount positions l +
        5 * (fwd1.length / 8 - fwdBytes.length / 8) +
        4 * (tailAccLen tails1 - tailAccLen tails) ∧
      s1.pc = (if step + 1 < 8 then pcAt 77 else pcAt 105) ∧
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
  -- Header: 65..73 (9 steps)
  have haddr65 : s.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    rw [inv.rx29, hse0, bv64_ofNat_add, Nat.add_zero]
  have h65 := step_LD (by omega) hpc (rfl : openingInstr 77 = .base (.LD .x18 .x29 (0#12)))
    (by rw [haddr65]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s66 := (s.setReg .x18 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 78)
  have h65' : OpenRuns s 1 1 s66 := by
    have hm := readOnly_getMem_data_base inv.ro l (by omega)
    simpa only [haddr65, hm, s66] using h65
  have h66 := step_ADD (by omega) (rfl : s66.pc = pcAt 78)
    (rfl : openingInstr 78 = .base (.ADD .x18 .x9 .x18))
  let s67 := (s66.setReg .x18 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 79)
  have h66' : OpenRuns s66 1 1 s67 := by
    have hr9 : s66.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
    rw [hr9] at h66
    simpa only [show s66.getReg .x18 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s67] using h66
  have haddr67 : s67.getReg .x29 + signExtend12 (8#12) = BitVec.ofNat 64 (68719475936 + 32 * l + 8) := by
    have hr29 : s67.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := inv.rx29
    rw [hr29, hse8, bv64_ofNat_add]
  have h67 := step_LD (by omega) (rfl : s67.pc = pcAt 79)
    (rfl : openingInstr 79 = .base (.LD .x19 .x29 (8#12)))
    (by rw [haddr67]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s68 := (s67.setReg .x19 (BitVec.ofNat 64 (levelSize l))).setPC (pcAt 80)
  have h67' : OpenRuns s67 1 1 s68 := by
    have hm : s67.getMem (BitVec.ofNat 64 (68719475936 + 32 * l + 8)) = BitVec.ofNat 64 (levelSize l) :=
      readOnly_getMem_data_size inv.ro l (by omega)
    simpa only [haddr67, hm, s68] using h67
  have haddr68 : s68.getReg .x29 + signExtend12 (16#12) = BitVec.ofNat 64 (68719475936 + 32 * l + 16) := by
    have hr29 : s68.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := inv.rx29
    rw [hr29, hse16, bv64_ofNat_add]
  have h68 := step_LD (by omega) (rfl : s68.pc = pcAt 80)
    (rfl : openingInstr 80 = .base (.LD .x20 .x29 (16#12)))
    (by rw [haddr68]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s69 := (s68.setReg .x20 (BitVec.ofNat 64 (capMarkOff l))).setPC (pcAt 81)
  have h68' : OpenRuns s68 1 1 s69 := by
    have hm : s68.getMem (BitVec.ofNat 64 (68719475936 + 32 * l + 16)) = BitVec.ofNat 64 (capMarkOff l) :=
      readOnly_getMem_data_markOff inv.ro l (by omega)
    simpa only [haddr68, hm, s69] using h68
  have h69 := step_ADD (by omega) (rfl : s69.pc = pcAt 81)
    (rfl : openingInstr 81 = .base (.ADD .x20 .x21 .x20))
  let s70 := (s69.setReg .x20 (BitVec.ofNat 64 (4096 + capMarkOff l))).setPC (pcAt 82)
  have h69' : OpenRuns s69 1 1 s70 := by
    have hr21 : s69.getReg .x21 = BitVec.ofNat 64 4096 := inv.rx21
    rw [hr21] at h69
    simpa only [show s69.getReg .x20 = BitVec.ofNat 64 (capMarkOff l) from rfl, bv64_ofNat_add, s70] using h69
  have haddr70 : s70.getReg .x29 + signExtend12 (48#12) =
      BitVec.ofNat 64 (68719475936 + 32 * (l + 1) + 16) := by
    have hr29 : s70.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := inv.rx29
    rw [hr29, hse48, bv64_ofNat_add]; congr 1
  have h70 := step_LD (by omega) (rfl : s70.pc = pcAt 82)
    (rfl : openingInstr 82 = .base (.LD .x22 .x29 (48#12)))
    (by rw [haddr70]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s71 := (s70.setReg .x22 (BitVec.ofNat 64 (capMarkOff (l + 1)))).setPC (pcAt 83)
  have h70' : OpenRuns s70 1 1 s71 := by
    have hm : s70.getMem (BitVec.ofNat 64 (68719475936 + 32 * (l + 1) + 16)) = BitVec.ofNat 64 (capMarkOff (l + 1)) :=
      readOnly_getMem_data_markOff inv.ro (l + 1) (by omega)
    simpa only [haddr70, hm, s71] using h70
  have h71 := step_ADD (by omega) (rfl : s71.pc = pcAt 83)
    (rfl : openingInstr 83 = .base (.ADD .x22 .x21 .x22))
  let s72 := (s71.setReg .x22 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1)))).setPC (pcAt 84)
  have h71' : OpenRuns s71 1 1 s72 := by
    have hr21 : s71.getReg .x21 = BitVec.ofNat 64 4096 := inv.rx21
    rw [hr21] at h71
    simpa only [show s71.getReg .x22 = BitVec.ofNat 64 (capMarkOff (l + 1)) from rfl,
      bv64_ofNat_add, s72] using h71
  have h72 := step_SRLI (by omega) (rfl : s72.pc = pcAt 84)
    (rfl : openingInstr 84 = .base (.SRLI .x23 .x19 (1#6)))
  let s73 := (s72.setReg .x23 (BitVec.ofNat 64 (levelSize l / 2))).setPC (pcAt 85)
  have h72' : OpenRuns s72 1 1 s73 := by
    have hv : s72.getReg .x19 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (levelSize l / 2) := by
      change BitVec.ofNat 64 (levelSize l) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s73] using h72
  have h73 := step_ADDI (by omega) (rfl : s73.pc = pcAt 85)
    (rfl : openingInstr 85 = .base (.ADDI .x24 .x0 (0#12)))
  let s74 := (s73.setReg .x24 (BitVec.ofNat 64 0)).setPC (pcAt 86)
  have h73' : OpenRuns s73 1 1 s74 := by
    have hv : s73.getReg .x0 + signExtend12 (0#12) = BitVec.ofNat 64 0 := by
      change (0#64 : Word) + signExtend12 (0#12) = BitVec.ofNat 64 0; decide
    simpa only [hv, s74] using h73
  have hhdr : OpenRuns s 9 9 s74 :=
    (((((((h65'.trans h66').trans h67').trans h68').trans h69').trans h70').trans h71').trans h72').trans h73'
  have hpairInv0 : CapPairInv trapdoor positions step 0 fwdBytes tails s74 :=
    ⟨inv.rx2, inv.rx9, rfl, rfl, rfl, inv.rx21, rfl, rfl, rfl, inv.rx26, inv.rx29, inv.rx30,
     by simpa using inv.boundFwd, by simpa using inv.boundTails,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.capMarks, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  -- Pair loop induction: q = 0 .. levelSize l / 2
  have hpairLoop : ∀ q ≤ levelSize l / 2,
      let curF := fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l)
      let curT := tails ++ (List.range q).flatMap (capPairTails trapdoor positions l)
      ∃ steps sq, OpenRuns s74 steps steps sq ∧
        steps ≤ 10 * q + 28 * (∑ j ∈ Finset.range q, capPairFrontier positions l j) +
          5 * (curF.length / 8 - fwdBytes.length / 8) +
          4 * (tailAccLen curT - tailAccLen tails) ∧
        sq.pc = (if q < levelSize l / 2 then pcAt 86 else pcAt 103) ∧
        CapPairInv trapdoor positions step q curF curT sq := by
    intro q hq
    induction q with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero,
        Finset.sum_range_zero, Nat.sub_self, Nat.add_zero]
      exact ⟨0, s74, OpenRuns.refl s74, Nat.le_refl 0, by rw [if_pos (by omega : 0 < levelSize l / 2)]; rfl, hpairInv0⟩
    | succ q ih =>
      obtain ⟨st, sq, hrq, hstq, hpcq, invq⟩ := ih (by omega)
      have hpcq' : sq.pc = pcAt 86 := by simpa only [show q < levelSize l / 2 by omega, ite_true] using hpcq
      obtain ⟨st1, sq1, hr1, hst1, hpc1, inv1⟩ :=
        openRuns_cap_pair_step hstep (show q < levelSize (16 + step) / 2 from by change q < levelSize l / 2; omega) hpcq' invq
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
      have hq1 : fwdBytes.length / 8 ≤ (fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l)).length / 8 :=
        Nat.div_le_div_right (by simp)
      have hq2 : (fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l)).length / 8 ≤
          (fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l) ++ capPairFwd trapdoor positions l q).length / 8 :=
        Nat.div_le_div_right (by simp)
      have ht1 : tailAccLen tails ≤ tailAccLen (tails ++ (List.range q).flatMap (capPairTails trapdoor positions l)) :=
        tailAccLen_mono_append _ _
      have ht2 : tailAccLen (tails ++ (List.range q).flatMap (capPairTails trapdoor positions l)) ≤
          tailAccLen (tails ++ (List.range q).flatMap (capPairTails trapdoor positions l) ++ capPairTails trapdoor positions l q) :=
        tailAccLen_mono_append _ _
      have hst1' : st1 ≤ 10 + 28 * capPairFrontier positions l q +
          5 * ((fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l) ++
            capPairFwd trapdoor positions l q).length / 8 -
            (fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l)).length / 8) +
          4 * (tailAccLen (tails ++ (List.range q).flatMap (capPairTails trapdoor positions l) ++
            capPairTails trapdoor positions l q) -
            tailAccLen (tails ++ (List.range q).flatMap (capPairTails trapdoor positions l))) := hst1
      have inv1' : CapPairInv trapdoor positions step (q + 1)
          (fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l) ++
            capPairFwd trapdoor positions l q)
          (tails ++ (List.range q).flatMap (capPairTails trapdoor positions l) ++
            capPairTails trapdoor positions l q) sq1 := inv1
      rw [happF] at hq2 hst1' inv1'
      rw [happT] at ht2 hst1' inv1'
      refine ⟨st + st1, sq1, hrq.trans hr1, ?_, hpc1, inv1'⟩
      rw [Finset.sum_range_succ]; omega
  obtain ⟨stPairs, s91, hrPairs, hstPairs, hpc91, inv91⟩ :=
    hpairLoop (levelSize l / 2) (Nat.le_refl _)
  have hpc91' : s91.pc = pcAt 103 := by simpa only [Nat.lt_irrefl, ite_false] using hpc91
  rw [sum_capPairFrontier_eq] at hstPairs
  have hfwd1_eq : fwdBytes ++ (List.range (levelSize l / 2)).flatMap (capPairFwd trapdoor positions l) =
      fwd1 := rfl
  have htails1_eq : tails ++ (List.range (levelSize l / 2)).flatMap (capPairTails trapdoor positions l) =
      tails1 := rfl
  rw [hfwd1_eq, htails1_eq] at hstPairs inv91
  have hboundF91 : fwd1.length ≤ 497 * positions.card +
      29 * (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (16 + k)) := by
    have h1 : fwd1.length ≤ 497 * positions.card +
        29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
              (∑ j ∈ Finset.range (levelSize (16 + step) / 2), capPairFrontier positions (16 + step) j)) :=
      inv91.boundFwd
    rw [sum_capPairFrontier_eq] at h1
    rw [Finset.sum_range_succ]; exact h1
  have hboundT91 : tails1.length ≤ 11 * positions.card +
      (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (16 + k)) := by
    have h1 : tails1.length ≤ 11 * positions.card +
        ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
         (∑ j ∈ Finset.range (levelSize (16 + step) / 2), capPairFrontier positions (16 + step) j)) :=
      inv91.boundTails
    rw [sum_capPairFrontier_eq] at h1
    rw [Finset.sum_range_succ]; exact h1
  -- Latch: 91..92 (all levels have even size, no odd-node promotion)
  have h91 := step_ADDI (by omega) hpc91' (rfl : openingInstr 103 = .base (.ADDI .x29 .x29 (32#12)))
  let s92 := (s91.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * (16 + (step + 1))))).setPC (pcAt 104)
  have h91' : OpenRuns s91 1 1 s92 := by
    have hv : s91.getReg .x29 + signExtend12 (32#12) =
        BitVec.ofNat 64 (68719475936 + 32 * (16 + (step + 1))) := by
      rw [inv91.rx29, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s92] using h91
  have hcm92 : CapLevelMarks s92 positions (l + 1) := by
    intro idx hidx
    rw [hls1_eq] at hidx
    exact inv91.nextMarks idx hidx
  have hmkInv : ∀ pc, CapLvlInv trapdoor positions (step + 1) fwd1 tails1 (s92.setPC pc) := fun pc =>
    ⟨inv91.rx2, inv91.rx9, inv91.rx21, inv91.rx26, rfl, inv91.rx30, hboundF91, hboundT91,
     inv91.ro, inv91.writer.of_eq, inv91.tail.of_eq,
     by rw [show 16 + (step + 1) = l + 1 by omega]; exact hcm92⟩
  by_cases hmore : step + 1 < 8
  · have h92 := step_BNE_taken (by omega) (rfl : s92.pc = pcAt 104)
      (rfl : openingInstr 104 = .base (.BNE .x29 .x30 (8084#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (16 + (step + 1))) ≠ s91.getReg .x30
          rw [inv91.rx30]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 104 + signExtend13 (8084#13) = pcAt 77)
    exact ⟨9 + stPairs + 1 + 1, s92.setPC (pcAt 77),
      ((hhdr.trans hrPairs).trans h91').trans h92,
      by omega, by rw [if_pos hmore]; rfl, hmkInv (pcAt 77)⟩
  · have hdone : 16 + (step + 1) = 24 := by omega
    have h92 := step_BNE_not_taken (by omega) (rfl : s92.pc = pcAt 104)
      (rfl : openingInstr 104 = .base (.BNE .x29 .x30 (8084#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (16 + (step + 1))) = s91.getReg .x30
          rw [inv91.rx30, hdone])
    exact ⟨9 + stPairs + 1 + 1, s92.setPC (pcAt 105),
      ((hhdr.trans hrPairs).trans h91').trans h92,
      by omega, by rw [if_neg hmore]; rfl, hmkInv (pcAt 105)⟩

private theorem cap_const_cycles_sum :
    (∑ step ∈ Finset.range 8, (11 + 10 * (levelSize (16 + step) / 2))) = 2638 := by
  decide

private theorem openRuns_cap_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {recFwd : List Byte} {recTails : List (BitVec 6)} {s63 : MachineState}
    (hpc : s63.pc = pcAt 75)
    (hx2 : s63.getReg .x2 = BitVec.ofNat 64 68719475936)
    (hx9 : s63.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx21 : s63.getReg .x21 = BitVec.ofNat 64 4096)
    (hx26 : s63.getReg .x26 = BitVec.ofNat 64 11878272992)
    (hbdF : recFwd.length ≤ 497 * positions.card)
    (hbdT : recTails.length ≤ 11 * positions.card)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s63)
    (hw : WriterState s63 recFwd)
    (ht : TailState s63 recTails)
    (hcap16 : CapLevelMarks s63 positions 16) :
    let allFwd := recFwd ++ capFrontierFwd (tdNode trapdoor) positions
    let allTails := recTails ++ capFrontierTails (tdNode trapdoor) positions
    ∃ steps s93, OpenRuns s63 steps steps s93 ∧
      steps ≤ 2640 + 28 * capFrontierCount positions +
        5 * (allFwd.length / 8 - recFwd.length / 8) +
        4 * (tailAccLen allTails - tailAccLen recTails) ∧
      s93.pc = pcAt 105 ∧
      s93.getReg .x26 = BitVec.ofNat 64 11878272992 ∧
      WriterState s93 allFwd ∧
      TailState s93 allTails := by
  intro allFwd allTails
  have hse512 : signExtend12 (512#12) = BitVec.ofNat 64 512 := by decide
  have hse768 : signExtend12 (768#12) = BitVec.ofNat 64 768 := by decide
  have h63 := step_ADDI (by omega) hpc (rfl : openingInstr 75 = .base (.ADDI .x29 .x2 (512#12)))
  let s64 := (s63.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * 16))).setPC (pcAt 76)
  have h63' : OpenRuns s63 1 1 s64 := by
    rw [hx2, hse512, bv64_ofNat_add] at h63; exact h63
  have h64 := step_ADDI (by omega) (rfl : s64.pc = pcAt 76)
    (rfl : openingInstr 76 = .base (.ADDI .x30 .x2 (768#12)))
  let s65 := (s64.setReg .x30 (BitVec.ofNat 64 (68719475936 + 32 * 24))).setPC (pcAt 77)
  have h64' : OpenRuns s64 1 1 s65 := by
    have hr2 : s64.getReg .x2 = BitVec.ofNat 64 68719475936 := hx2
    rw [hr2, hse768, bv64_ofNat_add] at h64; exact h64
  have hinv0 : CapLvlInv trapdoor positions 0 recFwd recTails s65 :=
    ⟨hx2, hx9, hx21, hx26, rfl, rfl, by simpa using hbdF, by simpa using hbdT, hro, hw.of_eq, ht.of_eq, hcap16⟩
  have hloop : ∀ k ≤ 8,
      let curF := recFwd ++ (List.range k).flatMap (fun step =>
        capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))
      let curT := recTails ++ (List.range k).flatMap (fun step =>
        capLevelFrontierTails (tdNode trapdoor) positions (16 + step))
      ∃ steps sk, OpenRuns s65 steps steps sk ∧
        steps ≤ (∑ step ∈ Finset.range k, (11 + 10 * (levelSize (16 + step) / 2))) +
          28 * (∑ step ∈ Finset.range k, levelFrontierCount positions (16 + step)) +
          5 * (curF.length / 8 - recFwd.length / 8) +
          4 * (tailAccLen curT - tailAccLen recTails) ∧
        sk.pc = (if k < 8 then pcAt 77 else pcAt 105) ∧
        CapLvlInv trapdoor positions k curF curT sk := by
    intro k hk
    induction k with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Finset.sum_range_zero,
        Nat.mul_zero, Nat.sub_self, Nat.add_zero]
      exact ⟨0, s65, OpenRuns.refl s65, Nat.le_refl 0, by rw [if_pos (by omega : 0 < 8)]; rfl, hinv0⟩
    | succ k ih =>
      obtain ⟨st, sk, hrk, hstk, hpck, invk⟩ := ih (by omega)
      have hpck' : sk.pc = pcAt 77 := by simpa only [show k < 8 by omega, ite_true] using hpck
      obtain ⟨st1, sk1, hr1, hst1, hpc1, inv1⟩ := openRuns_cap_lvl_iter (by omega) hpck' invk
      have happF : recFwd ++ (List.range k).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step)) ++
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + k) =
          recFwd ++ (List.range (k + 1)).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step)) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      have happT : recTails ++ (List.range k).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (16 + step)) ++
            capLevelFrontierTails (tdNode trapdoor) positions (16 + k) =
          recTails ++ (List.range (k + 1)).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (16 + step)) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      have hq1 : recFwd.length / 8 ≤ (recFwd ++ (List.range k).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))).length / 8 :=
        Nat.div_le_div_right (by simp)
      have hq2 : (recFwd ++ (List.range k).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))).length / 8 ≤
          (recFwd ++ (List.range k).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step)) ++
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + k)).length / 8 :=
        Nat.div_le_div_right (by simp)
      have ht1 : tailAccLen recTails ≤ tailAccLen (recTails ++ (List.range k).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (16 + step))) :=
        tailAccLen_mono_append _ _
      have ht2 : tailAccLen (recTails ++ (List.range k).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (16 + step))) ≤
          tailAccLen (recTails ++ (List.range k).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (16 + step)) ++
            capLevelFrontierTails (tdNode trapdoor) positions (16 + k)) :=
        tailAccLen_mono_append _ _
      rw [happF] at hq2 hst1 inv1
      rw [happT] at ht2 hst1 inv1
      refine ⟨st + st1, sk1, hrk.trans hr1, ?_, hpc1, inv1⟩
      rw [Finset.sum_range_succ, Finset.sum_range_succ]; omega
  obtain ⟨stCap, s93, hrCap, hstCap, hpc93, inv93⟩ := hloop 8 (Nat.le_refl 8)
  have hpc93' : s93.pc = pcAt 105 := by simpa only [Nat.lt_irrefl, ite_false] using hpc93
  have hconst := cap_const_cycles_sum
  have hfront_eq : (∑ step ∈ Finset.range 8, levelFrontierCount positions (16 + step)) =
      capFrontierCount positions := rfl
  have hallF_eq : recFwd ++ (List.range 8).flatMap (fun step =>
      capLevelFrontierFwd (tdNode trapdoor) positions (16 + step)) = allFwd := rfl
  have hallT_eq : recTails ++ (List.range 8).flatMap (fun step =>
      capLevelFrontierTails (tdNode trapdoor) positions (16 + step)) = allTails := rfl
  rw [hconst, hfront_eq, hallF_eq, hallT_eq] at hstCap
  rw [hallF_eq, hallT_eq] at inv93
  exact ⟨2 + stCap, s93, (h63'.trans h64').trans hrCap, by omega, hpc93',
    inv93.rx26, inv93.writer, inv93.tail⟩

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
      (positions.card = BATCH → exec.cycles ≤ 126000) := by
  have hsteps : submission.steps .opening = 274877906944 := rfl
  rw [submission_run_opening submission trapdoor positions]
  by_cases hempty : positions.card = 0
  · obtain ⟨s5, hr5, hpc5, _, _, _, _, _, hx27, _⟩ := openRuns_entry_prefix trapdoor positions
    have h5 := step_BEQ_taken (by omega) hpc5
      (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (480#13)))
      (by rw [hx27, hempty]; rfl)
      (by decide : pcAt 5 + signExtend13 (480#13) = pcAt 125)
    let s113 := s5.setPC (pcAt 125)
    obtain ⟨sHalt, hrepi, hpcH, hx5H, hx10H, hx11H, _⟩ :=
      openRuns_empty_epilogue (rfl : s113.pc = pcAt 125)
    have hexec := OpenRuns.halt (haltIdx := 128) (totalFuel := submission.steps .opening)
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
    obtain ⟨s20, hr20, hpc20, hx2, hx9, hx12, hx13, hx14, hx15, hx16, hx17, hx18,
        hx21, hx24, hx25, hx26, hx27, hx31, hmem20⟩ :=
      openRuns_entry_nonzero trapdoor positions hempty
    have hro20 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s20 := by
      intro a _; change s20.mem a = _; rw [hmem20]; rfl
    have hw0 : WriterState s20 [] :=
      ⟨by simpa using hx25, by simpa using hx13, by simpa using hx14,
       fun _ hj => absurd hj (Nat.not_lt_zero _),
       fun j _ hj => by rw [hx12]; apply BitVec.eq_of_getLsbD_eq; intro b _; simp,
       fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    have ht0 : TailState s20 [] :=
      ⟨hx31, by simpa using hx15, by simpa using hx16, by simpa using hx17,
       fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    have hinv0 : RecInv trapdoor positions 0 [] [] s20 :=
      ⟨hx2, hx9, hx18, hx21, by simpa using hx24, hx26, by simpa using hx27,
       hro20, hw0, ht0,
       fun c hc => by
         change extractByte (s20.mem _) _ = _
         rw [hmem20]
         have hz := opening_initial_zero_low trapdoor positions (4096 + c) (by omega)
         have hfalse : capMark16Prefix positions 0 c = false := by simp [capMark16Prefix]
         rw [hfalse, if_neg Bool.false_ne_true]; exact hz⟩
    obtain ⟨stRec, s63, hrRec, hstRec, hpc63, hx2_63, hx9_63, hx21_63,
        hx26_63, hbdF63, hbdT63, hro63, hw63, ht63, hcap16⟩ :=
      openRuns_rec_all hpos hpc20 hinv0
    obtain ⟨stCap, s93, hrCap, hstCap, hpc93, hx26_93, hw93, ht93⟩ :=
      openRuns_cap_all hpc63 hx2_63 hx9_63 hx21_63 hx26_63 hbdF63 hbdT63
        hro63 hw63 ht63 hcap16
    set recFwd := (positions.sort (· ≤ ·)).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
    set recTails := (positions.sort (· ≤ ·)).flatMap (recordTails (tdNode trapdoor))
    set allFwd := referenceProofFwd (tdNode trapdoor) (tdSalt trapdoor) positions
    set allTails := referenceProofTails (tdNode trapdoor) positions
    change WriterState s93 allFwd at hw93
    change TailState s93 allTails at ht93
    change stCap ≤ 2640 + 28 * capFrontierCount positions +
      5 * (allFwd.length / 8 - recFwd.length / 8) +
      4 * (tailAccLen allTails - tailAccLen recTails) at hstCap
    have hlen_cap := referenceProof_length_le_cap (tdNode trapdoor) (tdSalt trapdoor) positions
    have hcap128 := cap_frontier_le_128 positions
    have htails_le : allTails.length ≤ 11 * positions.card + 128 :=
      referenceProofTails_length_le (tdNode trapdoor) positions
    have href_eq : allFwd ++ pack6BitsRev allTails =
        referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions := by
      unfold referenceProof; rw [if_neg hempty]
    have hlen_sum : allFwd.length + (pack6Bits allTails).length ≤ 8476692192 := by
      have h1 : (allFwd ++ pack6BitsRev allTails).length ≤ 8476692192 := by
        rw [href_eq]; exact hlen_cap
      simpa only [List.length_append, pack6BitsRev, List.length_reverse] using h1
    obtain ⟨stFl, s100, hrFl, hstFl, hpc100, hx10_100, hx26_100, hpr100, ht100⟩ :=
      openRuns_flush_wbuf hpc93 hx26_93 (by omega) (by omega) hw93 ht93
    obtain ⟨stFt, s103, hrFt, hstFt, hpc103, hx10_103, hx26_103, hx31_103, hx15_103, hpr103, htb103⟩ :=
      openRuns_flush_tail hpc100 hx10_100 hx26_100 (by omega) (by omega) hpr100 ht100
    obtain ⟨s109, hrRev, hpc109, hx10_109, hx26_109, hpr109⟩ :=
      openRuns_rev_tail hpc103 hx10_103 hx26_103 hx31_103 hx15_103 hlen_sum hpr103 htb103
    have hrev_eq : allFwd ++ (pack6Bits allTails).reverse =
        referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions := href_eq
    rw [hrev_eq] at hx10_109 hpr109
    obtain ⟨sHalt, hrFin, hpcH, hx5H, hx10H, hx11H, hmemH⟩ :=
      openRuns_finish hpc109 hx10_109 hx26_109
    have htot := (((((hr20.trans hrRec).trans hrCap).trans hrFl).trans hrFt).trans hrRev).trans hrFin
    have hpack_len : (pack6Bits allTails).length = (6 * allTails.length + 7) / 8 :=
      pack6Bits_length allTails
    have hpack_max : (pack6Bits allTails).length ≤ (6 * (11 * 16777216 + 128) + 7) / 8 := by
      rw [hpack_len]; exact Nat.div_le_div_right (by omega)
    have hq_mono : recFwd.length / 8 ≤ allFwd.length / 8 :=
      Nat.div_le_div_right (by simp [allFwd, referenceProofFwd, recFwd])
    have ht_mono : tailAccLen recTails ≤ tailAccLen allTails :=
      tailAccLen_mono_append _ _
    have htacc_le : tailAccLen allTails ≤ (pack6Bits allTails).length :=
      tailAccLen_le_pack6Bits allTails
    have hq_max : allFwd.length / 8 ≤ 8476692192 / 8 := Nat.div_le_div_right (by omega)
    have hfuel : 20 + stRec + stCap + stFl + stFt + (1 + 5 * (pack6Bits allTails).length) + 3 + 1 ≤
        submission.steps .opening := by
      rw [hsteps]; omega
    have hexec := OpenRuns.halt (haltIdx := 124) (totalFuel := submission.steps .opening)
      htot (by omega) rfl hpcH hx5H hx10H hfuel
    refine ⟨{ exit := .success, state := sHalt,
              cycles := 20 + stRec + stCap + stFl + stFt + (1 + 5 * (pack6Bits allTails).length) + 3 + 1,
              oracleCalls := 0 },
      hexec, rfl, rfl, ?_, ?_, ?_⟩
    · change (sHalt.getReg .x11).toNat = _
      have hlen_cap' : (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions).length ≤ 8476692192 := hlen_cap
      rw [hx11H, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro j hj
      change extractByte (sHalt.mem _) _ = _
      rw [hmemH]
      exact hpr109 j hj
    · intro hbatch
      change positions.card = 128 at hbatch
      have hfwd_128 : allFwd.length ≤ 497 * 128 + 29 * 128 := by
        have hc := capFrontierFwd_length (tdNode trapdoor) positions
        have hall : allFwd.length = recFwd.length + (capFrontierFwd (tdNode trapdoor) positions).length := by
          simp [allFwd, referenceProofFwd, recFwd]
        omega
      have hq_128 : allFwd.length / 8 ≤ 8416 := by omega
      have hpack_128 : (pack6Bits allTails).length ≤ 1152 := by
        rw [hpack_len]
        have h1 : allTails.length ≤ 11 * 128 + 128 := by rw [hbatch] at htails_le; exact htails_le
        have h2 := Nat.div_le_div_right (c := 8) (show 6 * allTails.length + 7 ≤ 6 * (11 * 128 + 128) + 7 by omega)
        omega
      change 20 + stRec + stCap + stFl + stFt + (1 + 5 * (pack6Bits allTails).length) + 3 + 1 ≤ 126000
      omega

end CommitGolfCandidate
