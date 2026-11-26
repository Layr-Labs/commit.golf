import CommitGolfCandidate.MoonMemory

/-! Exact deterministic symbolic execution of the 262-word opening image with branchless
64-bit aligned dword-buffered proof writing and streaming variable-bit tail packing
(`packVarBitsRev`) over the `C = 14` (`683` cap leaves) variable-width hash-chain schedule.
Tracks registers, read-only input/table framing, capMark scratch bytes, forward proof bytes,
tail-stream scratch bytes, and exact step/cycle bounds (`≤ 160,000` at `k = 128`) with zero
oracle calls. -/
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
    (hhi : haltIdx < 262)
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

/-! ### 2. MachineState, BitVec, PackVar, and List Helpers -/

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
  have hse : signExtend12 (4095#12) = BitVec.ofNat 64 (2 ^ 64 - 1) := by decide
  rw [hse, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have heq : n + 1 + (2 ^ 64 - 1) = n + 2 ^ 64 := by omega
  rw [heq, Nat.add_mod_right]

private theorem bv64_add_neg8 (n : Nat) (h : 8 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4088#12) = BitVec.ofNat 64 (n - 8) := by
  have hse : signExtend12 (4088#12) = BitVec.ofNat 64 (2 ^ 64 - 8) := by decide
  rw [hse, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have heq : n + (2 ^ 64 - 8) = (n - 8) + 2 ^ 64 := by omega
  rw [heq, Nat.add_mod_right]

private theorem bv64_add_neg24 (n : Nat) (h : 24 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4072#12) = BitVec.ofNat 64 (n - 24) := by
  have hse : signExtend12 (4072#12) = BitVec.ofNat 64 (2 ^ 64 - 24) := by decide
  rw [hse, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have heq : n + (2 ^ 64 - 24) = (n - 24) + 2 ^ 64 := by omega
  rw [heq, Nat.add_mod_right]

private theorem bv64_add_neg64 (n : Nat) (h : 64 ≤ n) :
    BitVec.ofNat 64 n + signExtend12 (4032#12) = BitVec.ofNat 64 (n - 64) := by
  have hse : signExtend12 (4032#12) = BitVec.ofNat 64 (2 ^ 64 - 64) := by decide
  rw [hse, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have heq : n + (2 ^ 64 - 64) = (n - 64) + 2 ^ 64 := by omega
  rw [heq, Nat.add_mod_right]

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
    Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64)]
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
    Nat.mod_eq_of_lt (by decide : 1 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : a % 2 < 2 ^ 64)]
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

private theorem levelBodyBytes_range (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 23) :
    28 ≤ levelBodyBytes l ∧ levelBodyBytes l ≤ 30 := by
  interval_cases l <;> decide

private theorem levelBodyBytes_cap_le (l : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 23) :
    levelBodyBytes l ≤ 29 := by
  interval_cases l <;> decide

private theorem levelTailBits_cap_le (l : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 23) :
    levelTailBits l ≤ 6 := by
  interval_cases l <;> decide

private theorem levelMetaOC_bodyBytes (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 23) :
    BitVec.ofNat 64 (levelMetaOC l) &&& signExtend12 (255#12) =
      BitVec.ofNat 64 (levelBodyBytes l) := by
  interval_cases l <;> decide

private theorem levelMetaOC_tailBits (l : Nat) (hl1 : 2 ≤ l) (hl2 : l ≤ 23) :
    (BitVec.ofNat 64 (levelMetaOC l) >>> 8) &&& signExtend12 (255#12) =
      BitVec.ofNat 64 (levelTailBits l) := by
  interval_cases l <;> decide

private theorem mask_pow2_sub_one_getLsbD (tb b : Nat) (htb : tb < 8) (hb : b < 64) :
    (BitVec.ofNat 64 (2 ^ tb - 1)).getLsbD b = decide (b < tb) := by
  by_cases hb8 : b < 8
  · interval_cases tb <;> interval_cases b <;> decide
  · have hnot : ¬ (b < tb) := by omega
    rw [decide_eq_false hnot]
    simp only [BitVec.getLsbD_ofNat, hb, decide_true, Bool.true_and, Nat.testBit_eq_decide_div_mod_eq]
    have hlt : 2 ^ tb - 1 < 2 ^ b := by
      have hpow : 2 ^ tb ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
      have hpos : 1 ≤ 2 ^ tb := Nat.one_le_two_pow
      omega
    rw [Nat.div_eq_of_lt hlt]
    decide

private theorem word_tailVar_from_hi (v : Word) (d : Digest) (l : Nat)
    (hl1 : 2 ≤ l) (hl2 : l ≤ 23)
    (hv : ∀ j < 8, v.extractLsb' (8 * j) 8 = d.extractLsb' (8 * (24 + j)) 8) :
    (v >>> (8 * (levelBodyBytes l - 24))) &&& BitVec.ofNat 64 (2 ^ levelTailBits l - 1) =
      BitVec.ofNat 64 (tailChunkOf l d).2 := by
  have hbr := levelBodyBytes_range l hl1 hl2
  have htb : levelTailBits l < 8 := levelTailBits_lt_8 l
  set m := levelBodyBytes l - 24
  set tb := levelTailBits l
  have hm_lt : m < 8 := by omega
  have hm_add : 24 + m = levelBodyBytes l := by omega
  have hval_lt : (tailChunkOf l d).2 < 2 ^ tb := (tailChunkOf_valid l d).2
  have hpow8 : 2 ^ tb ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  have h128 : 2 ^ 7 = 128 := by decide
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    mask_pow2_sub_one_getLsbD tb b htb hb]
  by_cases hbt : b < tb
  · rw [decide_eq_true hbt, Bool.and_true]
    have hbyte := congrArg (fun x : Byte => x.getLsbD b) (hv m hm_lt)
    simp only [BitVec.getLsbD_extractLsb', show b < 8 by omega, decide_true, Bool.true_and,
      hm_add] at hbyte
    rw [hbyte]
    symm
    have hrhs : (BitVec.ofNat 64 (tailChunkOf l d).2).getLsbD b =
        (d.extractLsb' (8 * levelBodyBytes l) tb).getLsbD b := by
      simp only [BitVec.getLsbD, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : (tailChunkOf l d).2 < 2 ^ 64)]
      rfl
    rw [hrhs, BitVec.getLsbD_extractLsb']
    simp [hbt]
  · rw [decide_eq_false hbt, Bool.and_false]
    symm
    simp only [BitVec.getLsbD_ofNat, hb, decide_true, Bool.true_and,
      Nat.testBit_eq_decide_div_mod_eq]
    have hpow : 2 ^ tb ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
    have hdiv : (tailChunkOf l d).2 / 2 ^ b = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv]; decide

private theorem tailVar_or_shl_eq_add (tBuf tCnt tb tVal : Nat)
    (hcnt : tCnt < 8) (htb : tb < 8) (hbuf : tBuf < 2 ^ tCnt) (hval : tVal < 2 ^ tb) :
    BitVec.ofNat 64 tBuf ||| (BitVec.ofNat 64 tVal <<< tCnt) =
      BitVec.ofNat 64 (tBuf + tVal * 2 ^ tCnt) := by
  have hpowC : 2 ^ tCnt ≤ 128 := by
    have h1 : 2 ^ tCnt ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 7 = 128 := by decide
    omega
  have hpowB : 2 ^ tb ≤ 128 := by
    have h1 : 2 ^ tb ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
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

private theorem packVarStep_bounds (acc : List Byte) (buf cnt tot : Nat) (c : TailChunk)
    (hc1 : c.1 < 8) (hc2 : c.2 < 2 ^ c.1)
    (hcnt : cnt < 8) (hbuf : buf < 2 ^ cnt) (hbits : 8 * acc.length + cnt = tot) :
    let st := packVarStep (acc, buf, cnt) c
    st.2.2 < 8 ∧ st.2.1 < 2 ^ st.2.2 ∧ 8 * st.1.length + st.2.2 = tot + c.1 := by
  unfold packVarStep
  dsimp only
  split_ifs with hzero hge
  · rw [hzero]; simpa using And.intro hcnt (And.intro hbuf hbits)
  · dsimp only
    have hbuf' : buf + c.2 * 2 ^ cnt < 2 ^ (cnt + c.1) := by
      rw [Nat.pow_add]
      have hle : c.2 ≤ 2 ^ c.1 - 1 := by omega
      have hpos : 1 ≤ 2 ^ c.1 := Nat.one_le_two_pow
      calc
        buf + c.2 * 2 ^ cnt < 2 ^ cnt + (2 ^ c.1 - 1) * 2 ^ cnt := by
          have hm := Nat.mul_le_mul_right (2 ^ cnt) hle; omega
        _ = (1 + (2 ^ c.1 - 1)) * 2 ^ cnt := by ring
        _ = 2 ^ c.1 * 2 ^ cnt := by rw [Nat.add_sub_of_le hpos]
        _ = 2 ^ cnt * 2 ^ c.1 := by ring
    refine ⟨by omega, ?_, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (by decide : 0 < 256)]
      rw [show 2 ^ (cnt + c.1 - 8) * 256 = 2 ^ (cnt + c.1) by
        rw [show (256 : Nat) = 2 ^ 8 by decide, ← Nat.pow_add,
          show cnt + c.1 - 8 + 8 = cnt + c.1 by omega]]
      exact hbuf'
    · simp only [List.length_append, List.length_singleton]; omega
  · dsimp only
    have hbuf' : buf + c.2 * 2 ^ cnt < 2 ^ (cnt + c.1) := by
      rw [Nat.pow_add]
      have hle : c.2 ≤ 2 ^ c.1 - 1 := by omega
      have hpos : 1 ≤ 2 ^ c.1 := Nat.one_le_two_pow
      calc
        buf + c.2 * 2 ^ cnt < 2 ^ cnt + (2 ^ c.1 - 1) * 2 ^ cnt := by
          have hm := Nat.mul_le_mul_right (2 ^ cnt) hle; omega
        _ = (1 + (2 ^ c.1 - 1)) * 2 ^ cnt := by ring
        _ = 2 ^ c.1 * 2 ^ cnt := by rw [Nat.add_sub_of_le hpos]
        _ = 2 ^ cnt * 2 ^ c.1 := by ring
    exact ⟨by omega, hbuf', by omega⟩

private theorem packVar_foldl_bounds_aux (tails : List TailChunk)
    (hvalid : ∀ c ∈ tails, c.1 < 8 ∧ c.2 < 2 ^ c.1) :
    ∀ acc buf cnt tot,
      cnt < 8 → buf < 2 ^ cnt → 8 * acc.length + cnt = tot →
      let st := tails.foldl packVarStep (acc, buf, cnt)
      st.2.2 < 8 ∧ st.2.1 < 2 ^ st.2.2 ∧ 8 * st.1.length + st.2.2 = tot + totalTailBits tails := by
  induction tails with
  | nil =>
    intro acc buf cnt tot hcnt hbuf hbits
    simpa [totalTailBits] using And.intro hcnt (And.intro hbuf hbits)
  | cons c rest ih =>
    intro acc buf cnt tot hcnt hbuf hbits
    simp only [List.foldl_cons, totalTailBits_cons]
    have hc := hvalid c (by simp)
    have h1 := packVarStep_bounds acc buf cnt tot c hc.1 hc.2 hcnt hbuf hbits
    rcases hst : packVarStep (acc, buf, cnt) c with ⟨acc1, buf1, cnt1⟩
    rw [hst] at h1
    have h2 := ih (fun x hx => hvalid x (by simp [hx])) acc1 buf1 cnt1 (tot + c.1) h1.1 h1.2.1 h1.2.2
    simpa only [Nat.add_assoc] using h2

private theorem packVar_foldl_bounds (tails : List TailChunk)
    (hvalid : ∀ c ∈ tails, c.1 < 8 ∧ c.2 < 2 ^ c.1) :
    let st := tails.foldl packVarStep ([], 0, 0)
    st.2.2 < 8 ∧ st.2.1 < 2 ^ st.2.2 ∧ 8 * st.1.length + st.2.2 = totalTailBits tails := by
  simpa using packVar_foldl_bounds_aux tails hvalid [] 0 0 0 (by omega) (by decide) (by simp)

private theorem totalTailBits_le_7mul (tails : List TailChunk)
    (hvalid : ∀ c ∈ tails, c.1 < 8 ∧ c.2 < 2 ^ c.1) :
    totalTailBits tails ≤ 7 * tails.length := by
  induction tails with
  | nil => simp [totalTailBits]
  | cons c rest ih =>
    simp only [totalTailBits_cons, List.length_cons]
    have hc := (hvalid c (by simp)).1
    have hrest := ih (fun x hx => hvalid x (by simp [hx]))
    omega

private theorem list_map_sum_le' {α : Type} (l : List α) (f g : α → Nat)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := h a (by simp)
    have hrest := ih (fun x hx => h x (by simp [hx]))
    omega

private theorem recordFwd_length_le_470 (nodes : Nat → Nat → Digest) (salts : Index → Salt192)
    (i : Index) : (recordFwd nodes salts i).length ≤ 470 := by
  unfold recordFwd binPathFwd
  simp only [List.length_append, bitsToBytes_length, List.length_flatMap]
  have h0 := l0SiblingsProof_length_le nodes i
  have hb : (List.map (fun step => (if (((i.val / 3) >>> (step + 1)) ^^^ 1) < levelSize (2 + step)
      then bitsToBytes (nodes (2 + step) (((i.val / 3) >>> (step + 1)) ^^^ 1)) (levelBodyBytes (2 + step)) else []).length)
      (List.range 12)).sum ≤
      ((List.range 12).map (fun step => levelBodyBytes (2 + step))).sum :=
    list_map_sum_le' _ _ _ (fun step _ => by split <;> simp [bitsToBytes])
  have hc : ((List.range 12).map (fun step => levelBodyBytes (2 + step))).sum = 350 := by decide
  omega

private theorem recordTails_length_le_12 (nodes : Nat → Nat → Digest) (i : Index) :
    (recordTails nodes i).length ≤ 12 := by
  unfold recordTails binPathTails
  rw [List.length_flatMap]; dsimp only
  have hb : (List.map (fun step => (if (((i.val / 3) >>> (step + 1)) ^^^ 1) < levelSize (2 + step)
      then [tailChunkOf (2 + step) (nodes (2 + step) (((i.val / 3) >>> (step + 1)) ^^^ 1))] else []).length)
      (List.range 12)).sum ≤ ((List.range 12).map (fun _ => 1)).sum :=
    list_map_sum_le' _ _ _ (fun step _ => by split <;> simp)
  have hc : ((List.range 12).map (fun _ => 1)).sum = 12 := by decide
  omega

private theorem recordTails_bits_le_37 (nodes : Nat → Nat → Digest) (i : Index) :
    totalTailBits (recordTails nodes i) ≤ 37 := by
  have hflat : ∀ (l : List Nat) (f : Nat → List TailChunk),
      totalTailBits (l.flatMap f) = (l.map (fun x => totalTailBits (f x))).sum := by
    intro l f; induction l with
    | nil => simp [totalTailBits]
    | cons a r ih => simp only [List.flatMap_cons, totalTailBits_append, ih, List.map_cons, List.sum_cons]
  unfold recordTails binPathTails
  rw [hflat]; dsimp only
  have hb : (List.map (fun step => totalTailBits (if (((i.val / 3) >>> (step + 1)) ^^^ 1) < levelSize (2 + step)
      then [tailChunkOf (2 + step) (nodes (2 + step) (((i.val / 3) >>> (step + 1)) ^^^ 1))] else []))
      (List.range 12)).sum ≤ ((List.range 12).map (fun step => levelTailBits (2 + step))).sum :=
    list_map_sum_le' _ _ _ (fun step _ => by split <;> simp [totalTailBits, tailChunkOf])
  have hc : ((List.range 12).map (fun step => levelTailBits (2 + step))).sum = 37 := by decide
  omega

private theorem referenceProofTails_bits_le (nodes : Nat → Nat → Digest) (positions : Positions) :
    totalTailBits (referenceProofTails nodes positions) ≤ 37 * positions.card + 6 * capFrontierCount positions := by
  unfold referenceProofTails
  rw [totalTailBits_append]
  have hrec : totalTailBits ((positions.sort (· ≤ ·)).flatMap (recordTails nodes)) ≤ 37 * positions.card := by
    have hgen : ∀ l : List Index, totalTailBits (l.flatMap (recordTails nodes)) ≤ 37 * l.length := by
      intro l; induction l with
      | nil => simp [totalTailBits]
      | cons a r ih =>
        simp only [List.flatMap_cons, totalTailBits_append, List.length_cons]
        have ha := recordTails_bits_le_37 nodes a
        omega
    simpa [Finset.length_sort] using hgen (positions.sort (· ≤ ·))
  have hcap : totalTailBits (capFrontierTails nodes positions) ≤ 6 * capFrontierCount positions := by
    have hflat : ∀ (l : List Nat) (f : Nat → List TailChunk),
        totalTailBits (l.flatMap f) = (l.map (fun x => totalTailBits (f x))).sum := by
      intro l f; induction l with
      | nil => simp [totalTailBits]
      | cons a r ih => simp only [List.flatMap_cons, totalTailBits_append, ih, List.map_cons, List.sum_cons]
    have hsumR : ∀ (n : Nat) (f : Nat → Nat), ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
      intro n f; induction n with
      | zero => simp
      | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
          ih, Finset.sum_range_succ]
    unfold capFrontierTails capFrontierCount
    rw [hflat, hsumR, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro step hstep
    have hs : step < 10 := Finset.mem_range.mp hstep
    rw [capLevelFrontierTails_bits]
    exact Nat.mul_le_mul_right _ (levelTailBits_cap_le (14 + step) (by omega) (by omega))
  omega

private theorem referenceProofTails_length_le (nodes : Nat → Nat → Digest) (positions : Positions) :
    (referenceProofTails nodes positions).length ≤ 12 * positions.card + 342 := by
  unfold referenceProofTails
  rw [List.length_append]
  have hrec : ((positions.sort (· ≤ ·)).flatMap (recordTails nodes)).length ≤ 12 * positions.card := by
    have hgen : ∀ l : List Index, (l.flatMap (recordTails nodes)).length ≤ 12 * l.length := by
      intro l; induction l with
      | nil => simp
      | cons a r ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        have ha := recordTails_length_le_12 nodes a
        omega
    simpa [Finset.length_sort] using hgen (positions.sort (· ≤ ·))
  have hcap : (capFrontierTails nodes positions).length ≤ 342 := by
    have hsumR : ∀ (n : Nat) (f : Nat → Nat), ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
      intro n f; induction n with
      | zero => simp
      | succ n ih =>
        rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
          ih, Finset.sum_range_succ]
    have hlen : (capFrontierTails nodes positions).length = capFrontierCount positions := by
      unfold capFrontierTails capFrontierCount
      rw [List.length_flatMap, hsumR]
      apply Finset.sum_congr rfl
      intro step _
      unfold capLevelFrontierTails levelFrontierCount
      rw [List.length_flatMap, hsumR, Finset.card_filter]
      apply Finset.sum_congr rfl
      intro q _
      cases capMark positions (14 + step) (2 * q) <;>
        cases capMark positions (14 + step) (2 * q + 1) <;> simp
    rw [hlen]
    exact cap_frontier_le_342 positions
  omega

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
  by_cases h0 : l = 0
  · subst h0
    have hlb : levelBase 0 = 0 := rfl
    have hno : nodeOffset 0 idx = 32 * idx := rfl
    have hls : levelSize 0 = 16777216 := levelSize_0
    have htb : treeBytes = 1073742880 := treeBytes_eq
    omega
  · by_cases h24 : l < 24
    · have hno : nodeOffset l idx = gapOffset idx := by
        unfold nodeOffset; rw [if_neg h0]
      have hg := gapOffset_lt_levelBytes l idx (by omega) h24 hidx
      have hb := levelBase_bound l hl
      rw [hno]; omega
    · have hl24 : l = 24 := by omega
      subst hl24
      have hls : levelSize 24 = 1 := levelSize_24
      have hidx0 : idx = 0 := by omega
      subst hidx0
      decide

private theorem nodeOffset_align8 (l idx : Nat) : nodeOffset l idx % 8 = 0 := by
  unfold nodeOffset gapOffset
  split <;> omega

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

private theorem capMarkOff_step_disjoint (l : Nat) (hl1 : 14 ≤ l) (hl2 : l ≤ 23) :
    capMarkOff l + levelSize l ≤ capMarkOff (l + 1) := by
  interval_cases l <;> decide

/-! ### 3. Single-Instruction Step Lemmas -/

private theorem step_ADDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ADDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_ADD {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ADD rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADD rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADD rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SUB {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SUB rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SUB rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SUB rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SLLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SLLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SLLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SLLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SRLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SRLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SRLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SRLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SLL {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SLL rd rs1 rs2)) :
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SRL rd rs1 rs2)) :
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.XORI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.XORI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.XORI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_ANDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ANDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ANDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ANDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_AND {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.AND rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 &&& s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.AND rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.AND rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 &&& s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 &&& s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_OR {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.OR rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.OR rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.OR rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_DIVU {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.DIVU rd rs1 rs2)) :
    OpenRuns s 1 4 ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.DIVU rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.DIVU rd rs1 rs2)) =
      some ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_REMU {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.REMU rd rs1 rs2)) :
    OpenRuns s 1 4 ((s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.REMU rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.REMU rd rs1 rs2)) =
      some ((s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_LD {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.LD rd rs1 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SD rs1 rs2 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.LBU rd rs1 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SB rs1 rs2 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BGEU rs1 rs2 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BGEU rs1 rs2 off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.JAL rd off))
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
    (hidx : idx < 262) (hpc : s.pc = pcAt idx)
    (hi : openingInstr idx = .base (.JALR .x0 .x1 (0#12)))
    (hx1 : s.getReg .x1 = pcAt retIdx) :
    OpenRuns s 1 1 (s.setPC (pcAt retIdx)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.JALR .x0 .x1 (0#12))) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.JALR .x0 .x1 (0#12))) = some (s.setPC (pcAt retIdx)) := by
    change some ((s.setReg .x0 (s.pc + 4)).setPC ((s.getReg .x1 + signExtend12 (0#12)) &&& ~~~1#64)) = _
    rw [show s.setReg .x0 (s.pc + 4) = s from rfl, hx1, pcAt_jalr_return retIdx]
  exact OpenRuns.step hf hst

/-! ### 4. Memory Framing, Dword Writer, and Variable-Bit Tail Packer Predicates -/

/-- Read-only regions: trapdoor `[4294971424, 6912218176)`, indices `[6912218176, 7046435904)`,
and embedded metadata `[68719475728, 68719476736)`. -/
def ReadOnlyPreserved (s0 s : MachineState) : Prop :=
  ∀ addr : Word,
    (4294971424 ≤ addr.toNat ∧ addr.toNat < 7046435904) ∨
    (68719475728 ≤ addr.toNat ∧ addr.toNat < 68719476736) →
    s.getMem addr = s0.getMem addr

/-- Exact byte contents of the proof output prefix `[11341403200, 11341403200 + bytes.length)`. -/
def ProofPrefix (s : MachineState) (bytes : List Byte) : Prop :=
  ∀ j (hj : j < bytes.length),
    s.getByte (BitVec.ofNat 64 (11341403200 + j)) = bytes[j]

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
  rx25 : s.getReg .x25 = BitVec.ofNat 64 (11341403200 + 8 * (fwdBytes.length / 8))
  rx13 : s.getReg .x13 = BitVec.ofNat 64 (8 * (fwdBytes.length % 8))
  rx14 : s.getReg .x14 = BitVec.ofNat 64 (63 - 8 * (fwdBytes.length % 8))
  wbufLo : ∀ j (hj : j < fwdBytes.length % 8),
    (s.getReg .x12).extractLsb' (8 * j) 8 =
      fwdBytes[8 * (fwdBytes.length / 8) + j]'(by omega)
  wbufHi : ∀ j, fwdBytes.length % 8 ≤ j → j < 8 →
    (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8
  memDwords : ∀ j (hj : j < 8 * (fwdBytes.length / 8)),
    s.getByte (BitVec.ofNat 64 (11341403200 + j)) = fwdBytes[j]'(by omega)

/-- Exact state of the streaming variable-bit tail packer for emitted tail chunks. -/
private structure TailState (s : MachineState) (tails : List TailChunk) : Prop where
  valid : ∀ c ∈ tails, c.1 < 8 ∧ c.2 < 2 ^ c.1
  rx31 : s.getReg .x31 = BitVec.ofNat 64 tailBufBase
  rx15 : s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (tails.foldl packVarStep ([], 0, 0)).1.length)
  rx16 : s.getReg .x16 = BitVec.ofNat 64 (tails.foldl packVarStep ([], 0, 0)).2.1
  rx17 : s.getReg .x17 = BitVec.ofNat 64 (tails.foldl packVarStep ([], 0, 0)).2.2
  memTail : TailBufPrefix s (tails.foldl packVarStep ([], 0, 0)).1

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

private theorem TailState.of_eq {s1 s2 : MachineState} {tails : List TailChunk}
    (ht : TailState s1 tails)
    (h31 : s2.getReg .x31 = s1.getReg .x31 := by rfl)
    (h15 : s2.getReg .x15 = s1.getReg .x15 := by rfl)
    (h16 : s2.getReg .x16 = s1.getReg .x16 := by rfl)
    (h17 : s2.getReg .x17 = s1.getReg .x17 := by rfl)
    (hmem : ∀ a, s2.getByte a = s1.getByte a := by intro _; rfl) :
    TailState s2 tails :=
  ⟨ht.valid, h31.trans ht.rx31, h15.trans ht.rx15, h16.trans ht.rx16, h17.trans ht.rx17,
   fun j hj => by rw [hmem]; exact ht.memTail j hj⟩

private theorem readOnly_getMem_index {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (ordinal : Nat) (hord : ordinal < positions.card) :
    s.getMem (BitVec.ofNat 64 (6912218176 + 8 * ordinal)) =
      BitVec.ofNat 64 (openingIndex positions ordinal) := by
  have hcard := positions_card_le positions
  have haddr : (BitVec.ofNat 64 (6912218176 + 8 * ordinal)).toNat = 6912218176 + 8 * ordinal := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inl (by omega))]
  exact opening_initial_index trapdoor positions ordinal hord

private theorem readOnly_getMem_data_base {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 25) :
    s.getMem (BitVec.ofNat 64 (68719475728 + 40 * l)) = BitVec.ofNat 64 (levelBase l) := by
  have haddr : (BitVec.ofNat 64 (68719475728 + 40 * l)).toNat = 68719475728 + 40 * l := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), opening_initial_data_dword trapdoor positions (40 * l) (by omega)]
  exact openingData_dword_0 ⟨l, hl⟩

private theorem readOnly_getMem_data_size {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 25) :
    s.getMem (BitVec.ofNat 64 (68719475728 + 40 * l + 8)) = BitVec.ofNat 64 (levelSize l) := by
  have haddr : (BitVec.ofNat 64 (68719475728 + 40 * l + 8)).toNat = 68719475728 + 40 * l + 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), show 68719475728 + 40 * l + 8 = 68719475728 + (40 * l + 8) by omega,
    opening_initial_data_dword trapdoor positions (40 * l + 8) (by omega)]
  exact openingData_dword_1 ⟨l, hl⟩

private theorem readOnly_getMem_data_markOff {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 25) :
    s.getMem (BitVec.ofNat 64 (68719475728 + 40 * l + 16)) = BitVec.ofNat 64 (capMarkOff l) := by
  have haddr : (BitVec.ofNat 64 (68719475728 + 40 * l + 16)).toNat = 68719475728 + 40 * l + 16 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), show 68719475728 + 40 * l + 16 = 68719475728 + (40 * l + 16) by omega,
    opening_initial_data_dword trapdoor positions (40 * l + 16) (by omega)]
  exact openingData_dword_2 ⟨l, hl⟩

private theorem readOnly_getMem_data_meta {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (l : Nat) (hl : l < 25) :
    s.getMem (BitVec.ofNat 64 (68719475728 + 40 * l + 32)) = BitVec.ofNat 64 (levelMetaOC l) := by
  have haddr : (BitVec.ofNat 64 (68719475728 + 40 * l + 32)).toNat = 68719475728 + 40 * l + 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hro _ (Or.inr (by omega)), show 68719475728 + 40 * l + 32 = 68719475728 + (40 * l + 32) by omega,
    opening_initial_data_dword trapdoor positions (40 * l + 32) (by omega)]
  exact openingData_dword_4 ⟨l, hl⟩

private theorem readOnly_getByte_trapdoor {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (off : Nat) (hoff : off < 2617246752) :
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
    (off j : Nat) (hal : off % 8 = 0) (hj : j < 8) (hbd : off + 8 ≤ 2617246752) :
    (s.getMem (BitVec.ofNat 64 (4294971424 + off))).extractLsb' (8 * j) 8 =
      trapdoor.extractLsb' (8 * (off + j)) 8 := by
  rw [getMem_extractByte (by omega) hj, Nat.add_assoc]
  exact readOnly_getByte_trapdoor hro (off + j) (by omega)

private theorem readOnly_setMem_proof {s0 s : MachineState} (dst : Nat) (val : Word)
    (hro : ReadOnlyPreserved s0 s) (hlo : 11341403200 ≤ dst) (hhi : dst + 8 ≤ 19897793624) :
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
    (hro : ReadOnlyPreserved s0 s) (hlo : 4096 ≤ dst) (hhi : dst < 5512) :
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
    (hro : ReadOnlyPreserved s0 s) (hlo : tailBufBase ≤ dst) (hhi : dst < 68719475728) :
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
    (b : BitVec 8) (hw : WriterState s fwdBytes) (hbd : fwdBytes.length ≤ 8556390424)
    (hout : dst < 11341403200 ∨ 19897793624 ≤ dst) (hdst : dst < 2 ^ 64) :
    WriterState (s.setByte (BitVec.ofNat 64 dst) b) fwdBytes :=
  ⟨by rw [getReg_setByte]; exact hw.rx25,
   by rw [getReg_setByte]; exact hw.rx13,
   by rw [getReg_setByte]; exact hw.rx14,
   fun j hj => by rw [getReg_setByte]; exact hw.wbufLo j hj,
   fun j h1 h2 => by rw [getReg_setByte]; exact hw.wbufHi j h1 h2,
   fun j hj => by
     rw [set_byte_read, if_neg (bv64_ofNat_ne (by omega) hdst (by omega))]
     exact hw.memDwords j hj⟩

private theorem tailState_setByte_outside {s : MachineState} {tails : List TailChunk} (dst : Nat)
    (b : BitVec 8) (ht : TailState s tails) (htbd : tails.length ≤ 210000000)
    (hdst : dst < tailBufBase) :
    TailState (s.setByte (BitVec.ofNat 64 dst) b) tails :=
  ⟨ht.valid,
   by rw [getReg_setByte]; exact ht.rx31,
   by rw [getReg_setByte]; exact ht.rx15,
   by rw [getReg_setByte]; exact ht.rx16,
   by rw [getReg_setByte]; exact ht.rx17,
   fun j hj => by
     have htb : tailBufBase = 20000000000 := rfl
     have hlen := (packVar_foldl_bounds tails ht.valid).2.2
     have htot := totalTailBits_le_7mul tails ht.valid
     rw [set_byte_read, if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
     exact ht.memTail j hj⟩

private theorem tailState_of_mem_eq {s1 s2 : MachineState} {tails : List TailChunk}
    (ht : TailState s1 tails) (htbd : tails.length ≤ 210000000)
    (hreg : ∀ r, r = .x15 ∨ r = .x16 ∨ r = .x17 ∨ r = .x31 → s2.getReg r = s1.getReg r)
    (hmem : ∀ q, tailBufBase ≤ q → q < 68719475728 →
      s2.getByte (BitVec.ofNat 64 q) = s1.getByte (BitVec.ofNat 64 q)) :
    TailState s2 tails :=
  ⟨ht.valid,
   by rw [hreg .x31 (by simp)]; exact ht.rx31,
   by rw [hreg .x15 (by simp)]; exact ht.rx15,
   by rw [hreg .x16 (by simp)]; exact ht.rx16,
   by rw [hreg .x17 (by simp)]; exact ht.rx17,
   fun j hj => by
     have htb : tailBufBase = 20000000000 := rfl
     have hlen := (packVar_foldl_bounds tails ht.valid).2.2
     have htot := totalTailBits_le_7mul tails ht.valid
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

/-! ### 5. Branchless Dword Writer & Streaming Variable-Bit Tail Subroutines (`160..261`) -/

private theorem openRuns_emit_dword {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base srcOff qBase k : Nat} {imm : BitVec 12}
    {cur chunk8 : List Byte}
    (hbase : base + 5 < 262)
    (himm : signExtend12 imm = BitVec.ofNat 64 (8 * k))
    (hi0 : openingInstr base = .base (.LD .x5 .x10 imm))
    (hi1 : openingInstr (base + 1) = .base (.SLL .x6 .x5 .x13))
    (hi2 : openingInstr (base + 2) = .base (.OR .x12 .x12 .x6))
    (hi3 : openingInstr (base + 3) = .base (.SD .x25 .x12 imm))
    (hi4 : openingInstr (base + 4) = .base (.SRLI .x5 .x5 (1#6)))
    (hi5 : openingInstr (base + 5) = .base (.SRL .x12 .x5 .x14))
    (hpc : s.pc = pcAt base)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (11341403200 + 8 * qBase))
    (hqeq : cur.length / 8 = qBase + k)
    (hx13 : s.getReg .x13 = BitVec.ofNat 64 (8 * (cur.length % 8)))
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (63 - 8 * (cur.length % 8)))
    (hwLo : ∀ j (hj : j < cur.length % 8),
      (s.getReg .x12).extractLsb' (8 * j) 8 = cur[8 * (cur.length / 8) + j]'(by omega))
    (hwHi : ∀ j, cur.length % 8 ≤ j → j < 8 →
      (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8)
    (hmem : ∀ j (hj : j < 8 * (cur.length / 8)),
      s.getByte (BitVec.ofNat 64 (11341403200 + j)) = cur[j]'(by omega))
    (hsrc_al : srcOff % 8 = 0)
    (hsrc_bd : srcOff + 8 * k + 8 ≤ 2617246752)
    (hcur_bd : cur.length + 8 ≤ 8556390424)
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
        s'.getByte (BitVec.ofNat 64 (11341403200 + j)) = cur'[j]'(by omega)) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      (∀ q < 5512, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475728 →
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
  have hsrcAddr : s.getReg .x10 + signExtend12 imm =
      BitVec.ofNat 64 (4294971424 + (srcOff + 8 * k)) := by
    rw [hx10, himm, bv64_ofNat_add, Nat.add_assoc]
  have h0 := step_LD (by omega) hpc hi0
    (by rw [hsrcAddr]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s1 := (s.setReg .x5 v).setPC (pcAt (base + 1))
  have h0' : OpenRuns s 1 1 s1 := by simpa only [hsrcAddr, v, s1] using h0
  have h1 := step_SLL (by omega) (rfl : s1.pc = pcAt (base + 1)) hi1
  have hx13_mod : (s1.getReg .x13).toNat % 64 = 8 * r := by
    have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hx13
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s2 := (s1.setReg .x6 (v <<< (8 * r))).setPC (pcAt (base + 2))
  have h1' : OpenRuns s1 1 1 s2 := by
    simpa only [show s1.getReg .x5 = v from rfl, hx13_mod, s2, show base + 1 + 1 = base + 2 by omega] using h1
  set w := s.getReg .x12
  set wOut := w ||| (v <<< (8 * r))
  have h2 := step_OR (by omega) (rfl : s2.pc = pcAt (base + 2)) hi2
  let s3 := (s2.setReg .x12 wOut).setPC (pcAt (base + 3))
  have h2' : OpenRuns s2 1 1 s3 := by
    have hr12 : s2.getReg .x12 = w := rfl
    have hr6 : s2.getReg .x6 = v <<< (8 * r) := rfl
    simpa only [hr12, hr6, wOut, s3, show base + 2 + 1 = base + 3 by omega] using h2
  have hdstAddr : s3.getReg .x25 + signExtend12 imm = BitVec.ofNat 64 (11341403200 + 8 * q) := by
    have hr25 : s3.getReg .x25 = BitVec.ofNat 64 (11341403200 + 8 * qBase) := hx25
    rw [hr25, himm, bv64_ofNat_add]; congr 1; omega
  have h3 := step_SD (by omega) (rfl : s3.pc = pcAt (base + 3)) hi3
    (by rw [hdstAddr]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s4 := (s3.setMem (BitVec.ofNat 64 (11341403200 + 8 * q)) wOut).setPC (pcAt (base + 4))
  have h3' : OpenRuns s3 1 1 s4 := by
    simpa only [hdstAddr, show s3.getReg .x12 = wOut from rfl, s4, show base + 3 + 1 = base + 4 by omega] using h3
  have h4 := step_SRLI (by omega) (rfl : s4.pc = pcAt (base + 4)) hi4
  let s5 := (s4.setReg .x5 (v >>> 1)).setPC (pcAt (base + 5))
  have h4' : OpenRuns s4 1 1 s5 := by
    have hr5 : s4.getReg .x5 = v := by
      simp only [s4, MachineState.getReg_setPC, getReg_setMem, s3, s2, s1]
      rfl
    simpa only [hr5, show (1#6 : BitVec 6).toNat = 1 from rfl, s5, show base + 4 + 1 = base + 5 by omega] using h4
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
      (s.setMem (BitVec.ofNat 64 (11341403200 + 8 * q)) wOut).getByte a := fun a => by
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
    · rw [setMem_getByte_ofNat s (11341403200 + 8 * q) (11341403200 + j) wOut
        (by omega) (by omega) (by omega) (by omega)]
      rw [hmem j hlt, list_getElem_append_left cur chunk8 j (by omega)]
    · have hu : j - 8 * q < 8 := by omega
      have hadd : 11341403200 + 8 * q + (j - 8 * q) = 11341403200 + j := by omega
      rw [← hadd, setMem_getByte_inside s (11341403200 + 8 * q) (j - 8 * q) wOut (by omega) hu]
      rw [word_or_shl_byte w v r hr hwHi (j - 8 * q) hu]
      by_cases hur : j - 8 * q < r
      · rw [if_pos hur, hwLo (j - 8 * q) hur, list_getElem_append_left cur chunk8 j (by omega)]
        congr 1; omega
      · rw [if_neg hur, hv_byte (j - 8 * q - r) (by omega),
          list_getElem_append_right cur chunk8 j (by omega) (by omega)]
        congr 1; omega
  · intro addr had
    change (s.setMem (BitVec.ofNat 64 (11341403200 + 8 * q)) wOut).getMem addr = _
    exact readOnly_setMem_proof (11341403200 + 8 * q) wOut hro (by omega) (by omega) addr had
  · intro a ha
    rw [hmem6, setMem_getByte_ofNat s (11341403200 + 8 * q) a wOut
      (by omega) (by omega) (by omega) (by omega)]
  · intro a ha1 ha2
    have htb : tailBufBase = 20000000000 := rfl
    rw [hmem6, setMem_getByte_ofNat s (11341403200 + 8 * q) a wOut
      (by omega) (by omega) (by omega) (by omega)]

private theorem openRuns_emit_3dwords {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base srcOff : Nat}
    {fwdBytes chunk24 : List Byte}
    (hbase : base + 18 < 262)
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
    (hsrc_bd : srcOff + 24 ≤ 2617246752)
    (hbd : fwdBytes.length + 24 ≤ 8556390424)
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
      (∀ q < 5512, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475728 →
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
  have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
  have hadvStep := step_ADDI (by omega) (by simpa only [show base + 12 + 6 = base + 18 by omega] using hpc3) hadv
  have hx25_3 : s3.getReg .x25 = BitVec.ofNat 64 (11341403200 + 8 * qBase) := by
    rw [hreg3 .x25 (by decide) (by decide) (by decide),
      hreg2 .x25 (by decide) (by decide) (by decide),
      hreg1 .x25 (by decide) (by decide) (by decide)]
    exact hw.rx25
  have hnew25 : s3.getReg .x25 + signExtend12 (24#12) =
      BitVec.ofNat 64 (11341403200 + 8 * ((fwdBytes ++ chunk24).length / 8)) := by
    rw [hx25_3, hse24, bv64_ofNat_add]; congr 1
    simp only [List.length_append, hclen]; omega
  let s4 := (s3.setReg .x25 (BitVec.ofNat 64 (11341403200 + 8 * ((fwdBytes ++ chunk24).length / 8)))).setPC
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

/-- Variable-length (`1 ≤ m < 8`) partial dword append (`233..243`, length `8*m` in `x28`). -/
private theorem openRuns_emit_partial_var {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {m : Nat} {fwdBytes chunkM : List Byte}
    (hm1 : 1 ≤ m) (hm2 : m < 8)
    (hpc : s.pc = pcAt 233)
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 (8 * m))
    (hbd : fwdBytes.length + m ≤ 8556390424)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (hclen : chunkM.length = m)
    (hx5 : ∀ j (hj : j < 8),
      (s.getReg .x5).extractLsb' (8 * j) 8 =
        if hj' : j < m then chunkM[j]'(by omega) else 0#8) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 11 ∧
      s'.pc = pcAt 244 ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x25 →
        s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ chunkM) ∧
      (∀ q < 5512, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475728 →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  set r := fwdBytes.length % 8
  set q := fwdBytes.length / 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  set v := s.getReg .x5
  set w := s.getReg .x12
  set wOut := w ||| (v <<< (8 * r))
  -- 233: SLL x6, x5, x13
  have h0 := step_SLL (by omega) hpc (rfl : openingInstr 233 = .base (.SLL .x6 .x5 .x13))
  have hx13_mod : (s.getReg .x13).toNat % 64 = 8 * r := by
    rw [hw.rx13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s1 := (s.setReg .x6 (v <<< (8 * r))).setPC (pcAt 234)
  have h0' : OpenRuns s 1 1 s1 := by simpa only [hx13_mod, v, s1] using h0
  -- 234: OR x12, x12, x6
  have h1 := step_OR (by omega) (rfl : s1.pc = pcAt 234) (rfl : openingInstr 234 = .base (.OR .x12 .x12 .x6))
  let s2 := (s1.setReg .x12 wOut).setPC (pcAt 235)
  have h1' : OpenRuns s1 1 1 s2 := by
    simpa only [show s1.getReg .x12 = w from rfl, show s1.getReg .x6 = v <<< (8 * r) from rfl, wOut, s2] using h1
  -- 235: ADD x13, x13, x28
  have h2 := step_ADD (by omega) (rfl : s2.pc = pcAt 235) (rfl : openingInstr 235 = .base (.ADD .x13 .x13 .x28))
  let s3 := (s2.setReg .x13 (BitVec.ofNat 64 (8 * (r + m)))).setPC (pcAt 236)
  have h2' : OpenRuns s2 1 1 s3 := by
    have hr13 : s2.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13
    have hr28 : s2.getReg .x28 = BitVec.ofNat 64 (8 * m) := hx28
    have hv : s2.getReg .x13 + s2.getReg .x28 = BitVec.ofNat 64 (8 * (r + m)) := by
      rw [hr13, hr28, bv64_ofNat_add]; congr 1; omega
    simpa only [hv, s3] using h2
  -- 236: ADDI x6, x0, 64
  have h3 := step_ADDI (by omega) (rfl : s3.pc = pcAt 236) (rfl : openingInstr 236 = .base (.ADDI .x6 .x0 (64#12)))
  let s4 := (s3.setReg .x6 64#64).setPC (pcAt 237)
  have h3' : OpenRuns s3 1 1 s4 := by
    have hv : s3.getReg .x0 + signExtend12 (64#12) = 64#64 := by
      change (0#64 : Word) + signExtend12 (64#12) = 64#64; decide
    simpa only [hv, s4] using h3
  have hpre : OpenRuns s 4 4 s4 := ((h0'.trans h1').trans h2').trans h3'
  have hx13_4 : (s4.getReg .x13).toNat = 8 * (r + m) := by
    change (BitVec.ofNat 64 (8 * (r + m))).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx6_4 : (s4.getReg .x6).toNat = 64 := by
    change (64#64 : Word).toNat = 64; decide
  have hlen_app : (fwdBytes ++ chunkM).length = fwdBytes.length + m := by simp [hclen]
  by_cases hlt : r + m < 8
  · -- Branch taken: 237 -> 243
    have h4 := step_BLTU_taken (by omega) (rfl : s4.pc = pcAt 237)
      (rfl : openingInstr 237 = .base (.BLTU .x13 .x6 (24#13)))
      (by rw [hx13_4, hx6_4]; omega)
      (by decide : pcAt 237 + signExtend13 (24#13) = pcAt 243)
    let s10 := s4.setPC (pcAt 243)
    have h10 := step_XORI (by omega) (rfl : s10.pc = pcAt 243)
      (rfl : openingInstr 243 = .base (.XORI .x14 .x13 (63#12)))
    let s11 := (s10.setReg .x14 (BitVec.ofNat 64 (63 - 8 * (r + m)))).setPC (pcAt 244)
    have h10' : OpenRuns s10 1 1 s11 := by
      have hv : s10.getReg .x13 ^^^ signExtend12 (63#12) = BitVec.ofNat 64 (63 - 8 * (r + m)) := by
        change BitVec.ofNat 64 (8 * (r + m)) ^^^ signExtend12 (63#12) = _
        exact bv64_xor63_8mul (r + m) hlt
      simpa only [hv, s11] using h10
    have hq' : (fwdBytes ++ chunkM).length / 8 = q := by omega
    have hr' : (fwdBytes ++ chunkM).length % 8 = r + m := by omega
    refine ⟨6, s11, (hpre.trans h4).trans h10', by omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro reg _ h6 h12 h13 h14 _
      simp only [s11, s10, s4, s3, s2, s1, MachineState.getReg_setPC,
        getReg_setReg_ne' .x14 reg (Ne.symm h14),
        getReg_setReg_ne' .x6 reg (Ne.symm h6),
        getReg_setReg_ne' .x13 reg (Ne.symm h13),
        getReg_setReg_ne' .x12 reg (Ne.symm h12)]
    · intro a ha
      simp only [s11, s10, s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]
      exact hro a ha
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq']
        simp only [s11, s10, s4, s3, s2, s1, MachineState.getReg_setPC,
          getReg_setReg_ne' .x14 .x25 (by decide),
          getReg_setReg_ne' .x6 .x25 (by decide),
          getReg_setReg_ne' .x13 .x25 (by decide),
          getReg_setReg_ne' .x12 .x25 (by decide)]
        exact hw.rx25
      · rw [hr']
        simp only [s11, s10, s4, MachineState.getReg_setPC,
          getReg_setReg_ne' .x14 .x13 (by decide),
          getReg_setReg_ne' .x6 .x13 (by decide)]
        rfl
      · rw [hr']; rfl
      · intro j hj
        have h12 : s11.getReg .x12 = wOut := by
          simp only [s11, s10, s4, s3, MachineState.getReg_setPC,
            getReg_setReg_ne' .x14 .x12 (by decide),
            getReg_setReg_ne' .x6 .x12 (by decide),
            getReg_setReg_ne' .x13 .x12 (by decide)]
          rfl
        rw [h12, word_or_shl_byte w v r hr hw.wbufHi j (by omega)]
        by_cases hjr : j < r
        · rw [if_pos hjr, hw.wbufLo j hjr, list_getElem_append_left fwdBytes chunkM (8 * ((fwdBytes ++ chunkM).length / 8) + j) (by omega)]
          congr 1; omega
        · rw [if_neg hjr, hx5 (j - r) (by omega), dif_pos (by omega),
            list_getElem_append_right fwdBytes chunkM (8 * ((fwdBytes ++ chunkM).length / 8) + j) (by omega) (by omega)]
          congr 1; omega
      · intro j hj1 hj2
        have h12 : s11.getReg .x12 = wOut := by
          simp only [s11, s10, s4, s3, MachineState.getReg_setPC,
            getReg_setReg_ne' .x14 .x12 (by decide),
            getReg_setReg_ne' .x6 .x12 (by decide),
            getReg_setReg_ne' .x13 .x12 (by decide)]
          rfl
        rw [h12, word_or_shl_byte w v r hr hw.wbufHi j hj2, if_neg (by omega),
          hx5 (j - r) (by omega), dif_neg (by omega)]
      · intro j hj
        simp only [s11, s10, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
        rw [hw.memDwords j (by omega), list_getElem_append_left fwdBytes chunkM j (by omega)]
    · intro a _; simp only [s11, s10, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
    · intro a _ _; simp only [s11, s10, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
  · -- Branch not taken: spill dword at 238..243
    have hge : 8 ≤ r + m := by omega
    have hq' : (fwdBytes ++ chunkM).length / 8 = q + 1 := by omega
    have hr' : (fwdBytes ++ chunkM).length % 8 = r + m - 8 := by omega
    have h4 := step_BLTU_not_taken (by omega) (rfl : s4.pc = pcAt 237)
      (rfl : openingInstr 237 = .base (.BLTU .x13 .x6 (24#13)))
      (by rw [hx13_4, hx6_4]; omega)
    let s5 := s4.setPC (pcAt 238)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
    have hdstAddr : s5.getReg .x25 + signExtend12 (0#12) = BitVec.ofNat 64 (11341403200 + 8 * q) := by
      have hr25 : s5.getReg .x25 = BitVec.ofNat 64 (11341403200 + 8 * q) := hw.rx25
      rw [hr25, hse0, bv64_ofNat_add, Nat.add_zero]
    have h5 := step_SD (by omega) (rfl : s5.pc = pcAt 238)
      (rfl : openingInstr 238 = .base (.SD .x25 .x12 (0#12)))
      (by rw [hdstAddr]; exact accessValid_ofNat _ 8 (by omega) (by omega))
    let s6 := (s5.setMem (BitVec.ofNat 64 (11341403200 + 8 * q)) wOut).setPC (pcAt 239)
    have h5' : OpenRuns s5 1 1 s6 := by
      have hr12 : s5.getReg .x12 = wOut := by
        simp only [s5, s4, s3, MachineState.getReg_setPC,
          getReg_setReg_ne' .x6 .x12 (by decide), getReg_setReg_ne' .x13 .x12 (by decide)]
        rfl
      simpa only [hdstAddr, hr12, s6] using h5
    have h6 := step_ADDI (by omega) (rfl : s6.pc = pcAt 239)
      (rfl : openingInstr 239 = .base (.ADDI .x25 .x25 (8#12)))
    let s7 := (s6.setReg .x25 (BitVec.ofNat 64 (11341403200 + 8 * (q + 1)))).setPC (pcAt 240)
    have h6' : OpenRuns s6 1 1 s7 := by
      have hr25 : s6.getReg .x25 = BitVec.ofNat 64 (11341403200 + 8 * q) := by
        simp only [s6, MachineState.getReg_setPC, getReg_setMem]; exact hw.rx25
      have hv : s6.getReg .x25 + signExtend12 (8#12) = BitVec.ofNat 64 (11341403200 + 8 * (q + 1)) := by
        rw [hr25, hse8, bv64_ofNat_add]; exact congrArg (BitVec.ofNat 64) (by omega)
      simpa only [hv, s7] using h6
    have h7 := step_SRLI (by omega) (rfl : s7.pc = pcAt 240)
      (rfl : openingInstr 240 = .base (.SRLI .x5 .x5 (1#6)))
    let s8 := (s7.setReg .x5 (v >>> 1)).setPC (pcAt 241)
    have h7' : OpenRuns s7 1 1 s8 := by
      have hr5 : s7.getReg .x5 = v := by
        simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
          getReg_setReg_ne' .x25 .x5 (by decide), getReg_setReg_ne' .x6 .x5 (by decide),
          getReg_setReg_ne' .x13 .x5 (by decide), getReg_setReg_ne' .x12 .x5 (by decide)]
        rfl
      simpa only [hr5, show (1#6 : BitVec 6).toNat = 1 from rfl, s8] using h7
    set wNew := (v >>> 1) >>> (63 - 8 * r)
    have h8 := step_SRL (by omega) (rfl : s8.pc = pcAt 241)
      (rfl : openingInstr 241 = .base (.SRL .x12 .x5 .x14))
    have hx14_mod : (s8.getReg .x14).toNat % 64 = 63 - 8 * r := by
      have h : s8.getReg .x14 = BitVec.ofNat 64 (63 - 8 * r) := by
        simp only [s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
          getReg_setReg_ne' .x5 .x14 (by decide), getReg_setReg_ne' .x25 .x14 (by decide),
          getReg_setReg_ne' .x6 .x14 (by decide), getReg_setReg_ne' .x13 .x14 (by decide),
          getReg_setReg_ne' .x12 .x14 (by decide)]
        exact hw.rx14
      rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 63 - 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    let s9 := (s8.setReg .x12 wNew).setPC (pcAt 242)
    have h8' : OpenRuns s8 1 1 s9 := by
      simpa only [show s8.getReg .x5 = v >>> 1 from rfl, hx14_mod, wNew, s9] using h8
    have h9 := step_ADDI (by omega) (rfl : s9.pc = pcAt 242)
      (rfl : openingInstr 242 = .base (.ADDI .x13 .x13 (4032#12)))
    let s10 := (s9.setReg .x13 (BitVec.ofNat 64 (8 * (r + m - 8)))).setPC (pcAt 243)
    have h9' : OpenRuns s9 1 1 s10 := by
      have hr13 : s9.getReg .x13 = BitVec.ofNat 64 (8 * (r + m)) := by
        simp only [s9, s8, s7, s6, s5, s4, MachineState.getReg_setPC, getReg_setMem,
          getReg_setReg_ne' .x12 .x13 (by decide), getReg_setReg_ne' .x5 .x13 (by decide),
          getReg_setReg_ne' .x25 .x13 (by decide), getReg_setReg_ne' .x6 .x13 (by decide)]
        rfl
      have hv : s9.getReg .x13 + signExtend12 (4032#12) = BitVec.ofNat 64 (8 * (r + m - 8)) := by
        rw [hr13, bv64_add_neg64 (8 * (r + m)) (by omega)]; congr 1; omega
      simpa only [hv, s10] using h9
    have h10 := step_XORI (by omega) (rfl : s10.pc = pcAt 243)
      (rfl : openingInstr 243 = .base (.XORI .x14 .x13 (63#12)))
    let s11 := (s10.setReg .x14 (BitVec.ofNat 64 (63 - 8 * (r + m - 8)))).setPC (pcAt 244)
    have h10' : OpenRuns s10 1 1 s11 := by
      have hv : s10.getReg .x13 ^^^ signExtend12 (63#12) = BitVec.ofNat 64 (63 - 8 * (r + m - 8)) := by
        change BitVec.ofNat 64 (8 * (r + m - 8)) ^^^ signExtend12 (63#12) = _
        exact bv64_xor63_8mul (r + m - 8) (by omega)
      simpa only [hv, s11] using h10
    have htail_steps := (((((h4.trans h5').trans h6').trans h7').trans h8').trans h9').trans h10'
    have hmem11 : ∀ a, s11.getByte a =
        (s.setMem (BitVec.ofNat 64 (11341403200 + 8 * q)) wOut).getByte a := fun a => by
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
      rfl
    refine ⟨11, s11, hpre.trans htail_steps, Nat.le_refl 11, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro reg h5ne h6ne h12ne h13ne h14ne h25ne
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
        getReg_setReg_ne' .x14 reg (Ne.symm h14ne),
        getReg_setReg_ne' .x13 reg (Ne.symm h13ne),
        getReg_setReg_ne' .x12 reg (Ne.symm h12ne),
        getReg_setReg_ne' .x5 reg (Ne.symm h5ne),
        getReg_setReg_ne' .x25 reg (Ne.symm h25ne),
        getReg_setReg_ne' .x6 reg (Ne.symm h6ne)]
    · intro a ha
      change (s.setMem (BitVec.ofNat 64 (11341403200 + 8 * q)) wOut).getMem a = _
      exact readOnly_setMem_proof (11341403200 + 8 * q) wOut hro (by omega) (by omega) a ha
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hq']
        simp only [s11, s10, s9, s8, s7, MachineState.getReg_setPC,
          getReg_setReg_ne' .x14 .x25 (by decide), getReg_setReg_ne' .x13 .x25 (by decide),
          getReg_setReg_ne' .x12 .x25 (by decide), getReg_setReg_ne' .x5 .x25 (by decide)]
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
        · rw [setMem_getByte_ofNat s (11341403200 + 8 * q) (11341403200 + j) wOut
            (by omega) (by omega) (by omega) (by omega)]
          rw [hw.memDwords j hltq, list_getElem_append_left fwdBytes chunkM j (by omega)]
        · have hu : j - 8 * q < 8 := by omega
          have hadd : 11341403200 + 8 * q + (j - 8 * q) = 11341403200 + j := by omega
          rw [← hadd, setMem_getByte_inside s (11341403200 + 8 * q) (j - 8 * q) wOut (by omega) hu]
          rw [word_or_shl_byte w v r hr hw.wbufHi (j - 8 * q) hu]
          by_cases hur : j - 8 * q < r
          · rw [if_pos hur, hw.wbufLo (j - 8 * q) hur, list_getElem_append_left fwdBytes chunkM j (by omega)]
            congr 1; omega
          · rw [if_neg hur, hx5 (j - 8 * q - r) (by omega), dif_pos (by omega),
              list_getElem_append_right fwdBytes chunkM j (by omega) (by omega)]
            congr 1; omega
    · intro a ha
      rw [hmem11, setMem_getByte_ofNat s (11341403200 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]
    · intro a ha1 ha2
      have htb : tailBufBase = 20000000000 := rfl
      rw [hmem11, setMem_getByte_ofNat s (11341403200 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]

/-- Variable-bit (`0 ≤ tb < 8`) tail-chunk push (`244..260 -> 261`). -/
private theorem openRuns_push_tailVar {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {fwdBytes : List Byte} {tails : List TailChunk}
    {l : Nat} {d : Digest}
    (hl1 : 2 ≤ l) (hl2 : l ≤ 23)
    (hpc : s.pc = pcAt 244)
    (hx7 : s.getReg .x7 = BitVec.ofNat 64 (levelMetaOC l))
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 (8 * (levelBodyBytes l - 24)))
    (hx11 : ∀ j < 8, (s.getReg .x11).extractLsb' (8 * j) 8 = d.extractLsb' (8 * (24 + j)) 8)
    (hfbd : fwdBytes.length ≤ 8556390424)
    (htbd : tails.length < 210000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 17 ∧
      s'.pc = pcAt 261 ∧
      (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 →
        s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' fwdBytes ∧
      TailState s' (tails ++ [tailChunkOf l d]) ∧
      (∀ q < 5512, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have htbBase : tailBufBase = 20000000000 := rfl
  have hbr := levelBodyBytes_range l hl1 hl2
  set m := levelBodyBytes l - 24
  set tb := levelTailBits l
  set tc := tailChunkOf l d
  have htc_val : tc.1 < 8 ∧ tc.2 < 2 ^ tc.1 := tailChunkOf_valid l d
  have hvalid' : ∀ c ∈ tails ++ [tc], c.1 < 8 ∧ c.2 < 2 ^ c.1 := by
    intro c hc
    rcases List.mem_append.mp hc with h1 | h2
    · exact ht.valid c h1
    · simp only [List.mem_singleton] at h2; subst h2; exact htc_val
  set st := tails.foldl packVarStep ([], 0, 0)
  have hst_bd := packVar_foldl_bounds tails ht.valid
  have htot_le := totalTailBits_le_7mul tails ht.valid
  set acc := st.1
  set tBuf := st.2.1
  set tCnt := st.2.2
  have htCnt_lt : tCnt < 8 := hst_bd.1
  have htBuf_lt : tBuf < 2 ^ tCnt := hst_bd.2.1
  have hacc_len : 8 * acc.length + tCnt = totalTailBits tails := hst_bd.2.2
  have hfold_app : (tails ++ [tc]).foldl packVarStep ([], 0, 0) = packVarStep (acc, tBuf, tCnt) tc := by
    rw [List.foldl_append]; rfl
  -- 244: SRLI x7, x7, 8; 245: ANDI x7, x7, 255
  have h244 := step_SRLI (by omega) hpc (rfl : openingInstr 244 = .base (.SRLI .x7 .x7 (8#6)))
  let s1 := (s.setReg .x7 (BitVec.ofNat 64 (levelMetaOC l) >>> 8)).setPC (pcAt 245)
  have h244' : OpenRuns s 1 1 s1 := by
    simpa only [hx7, show (8#6 : BitVec 6).toNat = 8 from rfl, s1] using h244
  have h245 := step_ANDI (by omega) (rfl : s1.pc = pcAt 245)
    (rfl : openingInstr 245 = .base (.ANDI .x7 .x7 (255#12)))
  let s2 := (s1.setReg .x7 (BitVec.ofNat 64 tb)).setPC (pcAt 246)
  have h245' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x7 &&& signExtend12 (255#12) = BitVec.ofNat 64 tb :=
      levelMetaOC_tailBits l hl1 hl2
    simpa only [hv, s2] using h245
  by_cases htb0 : tb = 0
  · -- 246: BEQ x7, x0, 60 (-> 261)
    have h246 := step_BEQ_taken (by omega) (rfl : s2.pc = pcAt 246)
      (rfl : openingInstr 246 = .base (.BEQ .x7 .x0 (60#13)))
      (by change BitVec.ofNat 64 tb = 0#64; rw [htb0])
      (by decide : pcAt 246 + signExtend13 (60#13) = pcAt 261)
    let s3 := s2.setPC (pcAt 261)
    have hpack : (tails ++ [tc]).foldl packVarStep ([], 0, 0) = (acc, tBuf, tCnt) := by
      rw [hfold_app]; unfold packVarStep; dsimp only; change (if tb = 0 then _ else _) = _; rw [if_pos htb0]
    refine ⟨3, s3, (h244'.trans h245').trans h246, by omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro r _ _ h7ne _ _ _
      simp only [s3, s2, s1, MachineState.getReg_setPC, getReg_setReg_ne' .x7 r (Ne.symm h7ne)]
    · intro a ha
      simp only [s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
    · exact hw.of_eq
    · refine ⟨hvalid', ht.rx31, ?_, ?_, ?_, ?_⟩
      · rw [hpack]; exact ht.rx15
      · rw [hpack]; exact ht.rx16
      · rw [hpack]; exact ht.rx17
      · rw [hpack]; exact ht.memTail
    · intro a _; rfl
  · -- tb > 0: 246..260 -> 261
    have htb_lt : tb < 8 := levelTailBits_lt_8 l
    have hpowC : 2 ^ tCnt ≤ 128 := by
      have h1 : 2 ^ tCnt ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 2 ^ 7 = 128 := by decide
      omega
    have hpowB : 2 ^ tb ≤ 128 := by
      have h1 : 2 ^ tb ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 2 ^ 7 = 128 := by decide
      omega
    have h246 := step_BEQ_not_taken (by omega) (rfl : s2.pc = pcAt 246)
      (rfl : openingInstr 246 = .base (.BEQ .x7 .x0 (60#13)))
      (by change BitVec.ofNat 64 tb ≠ BitVec.ofNat 64 0; exact bv64_ofNat_ne (by omega) (by decide) htb0)
    -- Wrap 247..255 cleanly into an opaque intermediate state s12 at pcAt 256
    set buf' := tBuf + tc.2 * 2 ^ tCnt
    have hbuf'_lt : buf' < 16384 := by
      have htc2 : tc.2 < 2 ^ tb := htc_val.2
      have hmul : tc.2 * 2 ^ tCnt ≤ 127 * 128 := Nat.mul_le_mul (by omega) hpowC
      change tBuf + tc.2 * 2 ^ tCnt < 16384
      omega
    obtain ⟨s12, hrMid, hpc12, hreg12, hmem12, hx6_12, hx16_12, hx17_12⟩ :
        ∃ s12, OpenRuns (s2.setPC (pcAt 247)) 9 9 s12 ∧
          s12.pc = pcAt 256 ∧
          (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x16 → r ≠ .x17 → s12.getReg r = s2.getReg r) ∧
          s12.mem = s2.mem ∧
          s12.getReg .x6 = 8#64 ∧
          s12.getReg .x16 = BitVec.ofNat 64 buf' ∧
          s12.getReg .x17 = BitVec.ofNat 64 (tCnt + tb) := by
      let s3 := s2.setPC (pcAt 247)
      -- 247: SRL x5, x11, x28
      have h247 := step_SRL (by omega) (rfl : s3.pc = pcAt 247)
        (rfl : openingInstr 247 = .base (.SRL .x5 .x11 .x28))
      have hx28_mod : (s3.getReg .x28).toNat % 64 = 8 * m := by
        have h : s3.getReg .x28 = BitVec.ofNat 64 (8 * m) := hx28
        rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * m < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
      let s4 := (s3.setReg .x5 (s.getReg .x11 >>> (8 * m))).setPC (pcAt 248)
      have h247' : OpenRuns s3 1 1 s4 := by
        simpa only [show s3.getReg .x11 = s.getReg .x11 from rfl, hx28_mod, s4] using h247
      -- 248: ADDI x6, x0, 1
      have h248 := step_ADDI (by omega) (rfl : s4.pc = pcAt 248)
        (rfl : openingInstr 248 = .base (.ADDI .x6 .x0 (1#12)))
      let s5 := (s4.setReg .x6 (BitVec.ofNat 64 1)).setPC (pcAt 249)
      have h248' : OpenRuns s4 1 1 s5 := by
        have hv : s4.getReg .x0 + signExtend12 (1#12) = BitVec.ofNat 64 1 := by
          change (0#64 : Word) + signExtend12 (1#12) = BitVec.ofNat 64 1; decide
        simpa only [hv, s5] using h248
      -- 249: SLL x6, x6, x7
      have h249 := step_SLL (by omega) (rfl : s5.pc = pcAt 249)
        (rfl : openingInstr 249 = .base (.SLL .x6 .x6 .x7))
      have hx7_mod : (s5.getReg .x7).toNat % 64 = tb := by
        have h : s5.getReg .x7 = BitVec.ofNat 64 tb := rfl
        rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tb < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
      let s6 := (s5.setReg .x6 (BitVec.ofNat 64 (2 ^ tb))).setPC (pcAt 250)
      have h249' : OpenRuns s5 1 1 s6 := by
        have hv : s5.getReg .x6 <<< ((s5.getReg .x7).toNat % 64) = BitVec.ofNat 64 (2 ^ tb) := by
          rw [hx7_mod]; change BitVec.ofNat 64 1 <<< tb = _; rw [bv64_shl, Nat.one_mul]
        simpa only [hv, s6] using h249
      -- 250: ADDI x6, x6, -1
      have h250 := step_ADDI (by omega) (rfl : s6.pc = pcAt 250)
        (rfl : openingInstr 250 = .base (.ADDI .x6 .x6 (4095#12)))
      let s7 := (s6.setReg .x6 (BitVec.ofNat 64 (2 ^ tb - 1))).setPC (pcAt 251)
      have h250' : OpenRuns s6 1 1 s7 := by
        have hpos : 1 ≤ 2 ^ tb := Nat.one_le_two_pow
        have hr6 : s6.getReg .x6 = BitVec.ofNat 64 ((2 ^ tb - 1) + 1) := by
          change BitVec.ofNat 64 (2 ^ tb) = _; congr 1; omega
        rw [hr6, bv64_add_neg1] at h250; exact h250
      -- 251: AND x5, x5, x6
      have h251 := step_AND (by omega) (rfl : s7.pc = pcAt 251)
        (rfl : openingInstr 251 = .base (.AND .x5 .x5 .x6))
      let s8 := (s7.setReg .x5 (BitVec.ofNat 64 tc.2)).setPC (pcAt 252)
      have h251' : OpenRuns s7 1 1 s8 := by
        have hr5 : s7.getReg .x5 = s.getReg .x11 >>> (8 * m) := rfl
        have hr6 : s7.getReg .x6 = BitVec.ofNat 64 (2 ^ tb - 1) := rfl
        have hv : s7.getReg .x5 &&& s7.getReg .x6 = BitVec.ofNat 64 tc.2 := by
          rw [hr5, hr6]; exact word_tailVar_from_hi (s.getReg .x11) d l hl1 hl2 hx11
        simpa only [hv, s8] using h251
      -- 252: SLL x6, x5, x17
      have h252 := step_SLL (by omega) (rfl : s8.pc = pcAt 252)
        (rfl : openingInstr 252 = .base (.SLL .x6 .x5 .x17))
      have hx17_mod : (s8.getReg .x17).toNat % 64 = tCnt := by
        have h : s8.getReg .x17 = BitVec.ofNat 64 tCnt := ht.rx17
        rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tCnt < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
      let s9 := (s8.setReg .x6 (BitVec.ofNat 64 tc.2 <<< tCnt)).setPC (pcAt 253)
      have h252' : OpenRuns s8 1 1 s9 := by
        simpa only [show s8.getReg .x5 = BitVec.ofNat 64 tc.2 from rfl, hx17_mod, s9] using h252
      -- 253: OR x16, x16, x6
      have h253 := step_OR (by omega) (rfl : s9.pc = pcAt 253)
        (rfl : openingInstr 253 = .base (.OR .x16 .x16 .x6))
      let s10 := (s9.setReg .x16 (BitVec.ofNat 64 buf')).setPC (pcAt 254)
      have h253' : OpenRuns s9 1 1 s10 := by
        have hr16 : s9.getReg .x16 = BitVec.ofNat 64 tBuf := ht.rx16
        have hv : s9.getReg .x16 ||| s9.getReg .x6 = BitVec.ofNat 64 buf' := by
          rw [hr16]; exact tailVar_or_shl_eq_add tBuf tCnt tb tc.2 htCnt_lt htb_lt htBuf_lt htc_val.2
        simpa only [hv, s10] using h253
      -- 254: ADD x17, x17, x7
      have h254 := step_ADD (by omega) (rfl : s10.pc = pcAt 254)
        (rfl : openingInstr 254 = .base (.ADD .x17 .x17 .x7))
      let s11 := (s10.setReg .x17 (BitVec.ofNat 64 (tCnt + tb))).setPC (pcAt 255)
      have h254' : OpenRuns s10 1 1 s11 := by
        have hr17 : s10.getReg .x17 = BitVec.ofNat 64 tCnt := ht.rx17
        have hr7 : s10.getReg .x7 = BitVec.ofNat 64 tb := rfl
        rw [hr17, hr7, bv64_ofNat_add] at h254; exact h254
      -- 255: ADDI x6, x0, 8
      have h255 := step_ADDI (by omega) (rfl : s11.pc = pcAt 255)
        (rfl : openingInstr 255 = .base (.ADDI .x6 .x0 (8#12)))
      let s12 := (s11.setReg .x6 8#64).setPC (pcAt 256)
      have h255' : OpenRuns s11 1 1 s12 := by
        have hv : s11.getReg .x0 + signExtend12 (8#12) = 8#64 := by
          change (0#64 : Word) + signExtend12 (8#12) = 8#64; decide
        simpa only [hv, s12] using h255
      refine ⟨s12, (((((((h247'.trans h248').trans h249').trans h250').trans h251').trans h252').trans h253').trans h254').trans h255',
        rfl, ?_, rfl, rfl,
        by simp only [s12, s11, MachineState.getReg_setPC,
             getReg_setReg_ne' .x6 .x16 (by decide), getReg_setReg_ne' .x17 .x16 (by decide)]; rfl,
        by simp only [s12, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x17 (by decide)]; rfl⟩
      intro r h5ne h6ne h16ne h17ne
      simp only [s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, MachineState.getReg_setPC,
        getReg_setReg_ne' .x6 r (Ne.symm h6ne), getReg_setReg_ne' .x17 r (Ne.symm h17ne),
        getReg_setReg_ne' .x16 r (Ne.symm h16ne), getReg_setReg_ne' .x5 r (Ne.symm h5ne)]
    have hpre : OpenRuns s 12 12 s12 := ((h244'.trans h245').trans h246).trans hrMid
    have hx17_12_nat : (s12.getReg .x17).toNat = tCnt + tb := by
      rw [hx17_12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hx6_12' : (s12.getReg .x6).toNat = 8 := by rw [hx6_12]; decide
    have hpres12 : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x16 → r ≠ .x17 →
        s12.getReg r = s.getReg r := fun r h5 h6 h7 h16 h17 => by
      rw [hreg12 r h5 h6 h16 h17]
      simp only [s2, s1, MachineState.getReg_setPC, getReg_setReg_ne' .x7 r (Ne.symm h7)]
    by_cases hlt8 : tCnt + tb < 8
    · have h256 := step_BLTU_taken (by omega) hpc12
        (rfl : openingInstr 256 = .base (.BLTU .x17 .x6 (20#13)))
        (by rw [hx17_12_nat, hx6_12']; exact hlt8)
        (by decide : pcAt 256 + signExtend13 (20#13) = pcAt 261)
      let s13 := s12.setPC (pcAt 261)
      have hpack : (tails ++ [tc]).foldl packVarStep ([], 0, 0) = (acc, buf', tCnt + tb) := by
        rw [hfold_app]; unfold packVarStep; dsimp only
        change (if tb = 0 then _ else if 8 ≤ tCnt + tb then _ else _) = _
        rw [if_neg htb0, if_neg (by omega)]
        rfl
      refine ⟨13, s13, hpre.trans h256, by omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · intro r h5 h6 h7 _ h16 h17; exact hpres12 r h5 h6 h7 h16 h17
      · intro a ha; change s12.mem a = _; rw [hmem12]; exact hro a ha
      · exact hw.of_eq (h25 := hpres12 .x25 (by decide) (by decide) (by decide) (by decide) (by decide))
          (h13 := hpres12 .x13 (by decide) (by decide) (by decide) (by decide) (by decide))
          (h14 := hpres12 .x14 (by decide) (by decide) (by decide) (by decide) (by decide))
          (h12 := hpres12 .x12 (by decide) (by decide) (by decide) (by decide) (by decide))
          (hmem := fun a => by change extractByte (s12.mem _) _ = _; rw [hmem12]; rfl)
      · refine ⟨hvalid', ?_, ?_, ?_, ?_, ?_⟩
        · exact (hpres12 .x31 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht.rx31
        · rw [hpack]
          exact (hpres12 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht.rx15
        · rw [hpack]; exact hx16_12
        · rw [hpack]; exact hx17_12
        · rw [hpack]; intro j hj; change extractByte (s12.mem _) _ = _; rw [hmem12]; exact ht.memTail j hj
      · intro a _; change extractByte (s12.mem _) _ = _; rw [hmem12]; rfl
    · have hge8 : 8 ≤ tCnt + tb := by omega
      have h256 := step_BLTU_not_taken (by omega) hpc12
        (rfl : openingInstr 256 = .base (.BLTU .x17 .x6 (20#13)))
        (by rw [hx17_12_nat, hx6_12']; exact hge8)
      let s13 := s12.setPC (pcAt 257)
      have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
      have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
      have hx15_13 : s13.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) :=
        (hpres12 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht.rx15
      have haddr257 : s13.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + acc.length) := by
        rw [hx15_13, hse0, bv64_ofNat_add, Nat.add_zero]
      have h257 := step_SB (by omega) (rfl : s13.pc = pcAt 257)
        (rfl : openingInstr 257 = .base (.SB .x15 .x16 (0#12)))
        (by rw [haddr257]; exact accessValid_ofNat _ 1 (by omega) (by omega))
      let s14 := (s13.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).setPC (pcAt 258)
      have h257' : OpenRuns s13 1 1 s14 := by
        have htr : (s13.getReg .x16).truncate 8 = BitVec.ofNat 8 buf' := by
          rw [show s13.getReg .x16 = BitVec.ofNat 64 buf' from hx16_12]
          exact bv64_ofNat_truncate8 buf' (by omega)
        simpa only [haddr257, htr, s14] using h257
      have h258 := step_ADDI (by omega) (rfl : s14.pc = pcAt 258)
        (rfl : openingInstr 258 = .base (.ADDI .x15 .x15 (1#12)))
      let s15 := (s14.setReg .x15 (BitVec.ofNat 64 (tailBufBase + (acc ++ [BitVec.ofNat 8 buf']).length))).setPC (pcAt 259)
      have h258' : OpenRuns s14 1 1 s15 := by
        have hr15 : s14.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := by
          simp only [s14, MachineState.getReg_setPC, getReg_setByte]; exact hx15_13
        have hv : s14.getReg .x15 + signExtend12 (1#12) =
            BitVec.ofNat 64 (tailBufBase + (acc ++ [BitVec.ofNat 8 buf']).length) := by
          rw [hr15, hse1, bv64_ofNat_add, List.length_append, List.length_singleton, Nat.add_assoc]
        simpa only [hv, s15] using h258
      have h259 := step_SRLI (by omega) (rfl : s15.pc = pcAt 259)
        (rfl : openingInstr 259 = .base (.SRLI .x16 .x16 (8#6)))
      let s16 := (s15.setReg .x16 (BitVec.ofNat 64 (buf' / 256))).setPC (pcAt 260)
      have h259' : OpenRuns s15 1 1 s16 := by
        have hr16 : s15.getReg .x16 = BitVec.ofNat 64 buf' := by
          simp only [s15, s14, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x15 .x16 (by decide)]
          exact hx16_12
        have hv : s15.getReg .x16 >>> (8#6 : BitVec 6).toNat = BitVec.ofNat 64 (buf' / 256) := by
          rw [hr16]; change BitVec.ofNat 64 buf' >>> 8 = _
          rw [bv64_ushr buf' 8 (by omega), Nat.shiftRight_eq_div_pow]
        simpa only [hv, s16] using h259
      have h260 := step_ADDI (by omega) (rfl : s16.pc = pcAt 260)
        (rfl : openingInstr 260 = .base (.ADDI .x17 .x17 (4088#12)))
      let s17 := (s16.setReg .x17 (BitVec.ofNat 64 (tCnt + tb - 8))).setPC (pcAt 261)
      have h260' : OpenRuns s16 1 1 s17 := by
        have hr17 : s16.getReg .x17 = BitVec.ofNat 64 (tCnt + tb) := by
          simp only [s16, s15, s14, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x16 .x17 (by decide), getReg_setReg_ne' .x15 .x17 (by decide)]
          exact hx17_12
        rw [hr17, bv64_add_neg8 (tCnt + tb) hge8] at h260; exact h260
      have hpack : (tails ++ [tc]).foldl packVarStep ([], 0, 0) =
          (acc ++ [BitVec.ofNat 8 buf'], buf' / 256, tCnt + tb - 8) := by
        rw [hfold_app]; unfold packVarStep; dsimp only
        change (if tb = 0 then _ else if 8 ≤ tCnt + tb then _ else _) = _
        rw [if_neg htb0, if_pos hge8]
        rfl
      have hmem17 : ∀ a, s17.getByte a =
          (s.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).getByte a := fun a => by
        simp only [s17, s16, s15, s14, getByte_setPC, getByte_setReg]
        have hs13m : s13.mem = s.mem := hmem12
        simp only [MachineState.getByte, MachineState.setByte, MachineState.getMem, MachineState.setMem, hs13m]
      have hpres17 : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 →
          s17.getReg r = s.getReg r := fun r h5 h6 h7 h15 h16 h17 => by
        simp only [s17, s16, s15, s14, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x17 r (Ne.symm h17), getReg_setReg_ne' .x16 r (Ne.symm h16),
          getReg_setReg_ne' .x15 r (Ne.symm h15)]
        exact hpres12 r h5 h6 h7 h16 h17
      have htot := hpre.trans ((((h256.trans h257').trans h258').trans h259').trans h260')
      refine ⟨17, s17, htot, Nat.le_refl 17, rfl, hpres17, ?_, ?_, ?_, ?_⟩
      · intro a ha
        have hs13m : s13.mem = s.mem := hmem12
        have h1 := readOnly_setByte_tail (tailBufBase + acc.length) (BitVec.ofNat 8 buf') hro (by omega) (by omega) a ha
        have h17_14 : s17.getMem a = s14.getMem a := by
          simp only [s17, s16, s15, MachineState.getMem_setPC, MachineState.getMem_setReg]
        have h14_eq : s14.getMem a = (s.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).getMem a := by
          simp only [s14, MachineState.getMem_setPC, MachineState.setByte, MachineState.getMem, MachineState.setMem, hs13m]
          rfl
        exact (h17_14.trans h14_eq).trans h1
      · have hw' := writerState_setByte_outside (tailBufBase + acc.length) (BitVec.ofNat 8 buf')
          hw hfbd (Or.inr (by omega)) (by omega)
        exact ⟨(hpres17 .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw.rx25,
          (hpres17 .x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw.rx13,
          (hpres17 .x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hw.rx14,
          fun j hj => by
            rw [hpres17 .x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hw.wbufLo j hj,
          fun j h1 h2 => by
            rw [hpres17 .x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
            exact hw.wbufHi j h1 h2,
          fun j hj => by rw [hmem17]; exact hw'.memDwords j hj⟩
      · refine ⟨hvalid',
          (hpres17 .x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ht.rx31,
          ?_, ?_, ?_, ?_⟩
        · rw [hpack]
          simp only [s17, s16, MachineState.getReg_setPC,
            getReg_setReg_ne' .x17 .x15 (by decide), getReg_setReg_ne' .x16 .x15 (by decide)]; rfl
        · rw [hpack]
          simp only [s17, MachineState.getReg_setPC, getReg_setReg_ne' .x17 .x16 (by decide)]; rfl
        · rw [hpack]; rfl
        · rw [hpack]
          intro j hj
          rw [hmem17, set_byte_read]
          have hjlen : j < acc.length + 1 := by simpa using hj
          by_cases hlast : j = acc.length
          · subst hlast
            rw [if_pos rfl, list_getElem_append_right acc [BitVec.ofNat 8 buf'] acc.length (by omega) hj]
            simp
          · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega)),
              ht.memTail j (by omega), list_getElem_append_left acc [BitVec.ofNat 8 buf'] j (by omega)]
      · intro a ha
        rw [hmem17, set_byte_read, if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]

private theorem openRuns_call_copy24 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx srcOff : Nat} {jOff : BitVec 21}
    {fwdBytes chunk : List Byte} {tails : List TailChunk}
    (hcall : callIdx < 262)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 160)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 24 ≤ 2617246752)
    (hbd : fwdBytes.length + 24 ≤ 8556390424)
    (htbd : tails.length ≤ 210000000)
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
      (∀ q < 5512, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  have hr_jal := step_JAL hcall hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 160)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  have hw1 : WriterState s1 fwdBytes := hw.of_eq
  obtain ⟨s2, hr_body, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    openRuns_emit_3dwords (base := 160) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := chunk)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (by exact hx10) hsrc_al hsrc_bd hbd hro1 hw1 hclen hchunk
  have hx1_2 : s2.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl
  have hr_ret := step_JALR_x0 (by omega) hpc2 (rfl : openingInstr 179 = .base (.JALR .x0 .x1 (0#12))) hx1_2
  let s3 := s2.setPC (pcAt (callIdx + 1))
  have hpres : ∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → r ≠ .x25 →
      s3.getReg r = s.getReg r := fun r h1 h5 h6 h12 h25 => by
    simp only [s3, MachineState.getReg_setPC, hreg2 r h5 h6 h12 h25, s1,
      getReg_setReg_ne' .x1 r (Ne.symm h1)]
  refine ⟨s3, (hr_jal.trans hr_body).trans hr_ret, rfl, hpres, hro2,
    hw2.of_eq,
    tailState_of_mem_eq ht htbd (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact hpres _ (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun a ha1 ha2 => htail2 a ha1 ha2),
    fun a ha => hcap2 a ha⟩

private theorem openRuns_call_copy32 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx srcOff : Nat} {jOff : BitVec 21}
    {fwdBytes chunk : List Byte} {tails : List TailChunk}
    (hcall : callIdx < 262)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 180)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hsrc_al : srcOff % 8 = 0) (hsrc_bd : srcOff + 32 ≤ 2617246752)
    (hbd : fwdBytes.length + 32 ≤ 8556390424)
    (htbd : tails.length ≤ 210000000)
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
      (∀ q < 5512, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
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
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 180)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  set qBase := fwdBytes.length / 8
  have hw1 : WriterState s1 fwdBytes := hw.of_eq
  obtain ⟨s2, hr2, hpc2, hreg2, hwLo2, hwHi2, hmem2, hro2, hcap2, htail2⟩ :=
    openRuns_emit_dword (s := s1) (base := 180) (srcOff := srcOff) (qBase := qBase) (k := 0) (imm := 0#12)
      (cur := fwdBytes) (chunk8 := c0) (by omega) (by decide)
      rfl rfl rfl rfl rfl rfl rfl (by exact hx10) hw1.rx25 (by omega) hw1.rx13 hw1.rx14
      hw1.wbufLo hw1.wbufHi hw1.memDwords hsrc_al (by omega) (by omega) hro1 hc0_len
      (fun j hj => by simpa [c0, List.getElem_take] using hchunk j (by omega))
  have hlen2 : (fwdBytes ++ c0).length = fwdBytes.length + 8 := by simp [hc0_len]
  obtain ⟨s3, hr3, hpc3, hreg3, hwLo3, hwHi3, hmem3, hro3, hcap3, htail3⟩ :=
    openRuns_emit_dword (base := 186) (srcOff := srcOff) (qBase := qBase) (k := 1) (imm := 8#12)
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
    openRuns_emit_dword (base := 192) (srcOff := srcOff) (qBase := qBase) (k := 2) (imm := 16#12)
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
    openRuns_emit_dword (base := 198) (srcOff := srcOff) (qBase := qBase) (k := 3) (imm := 24#12)
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
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have hadv := step_ADDI (by omega) hpc5 (rfl : openingInstr 204 = .base (.ADDI .x25 .x25 (32#12)))
  have hnew25 : s5.getReg .x25 + signExtend12 (32#12) =
      BitVec.ofNat 64 (11341403200 + 8 * ((fwdBytes ++ chunk).length / 8)) := by
    rw [hpres5 .x25 (by decide) (by decide) (by decide)]
    have hx25_1 : s1.getReg .x25 = BitVec.ofNat 64 (11341403200 + 8 * qBase) := hw.rx25
    rw [hx25_1, hse32, bv64_ofNat_add]; congr 1
    simp only [List.length_append, hclen]; omega
  let s6 := (s5.setReg .x25 (BitVec.ofNat 64 (11341403200 + 8 * ((fwdBytes ++ chunk).length / 8)))).setPC (pcAt 205)
  have hadv' : OpenRuns s5 1 1 s6 := by simpa only [hnew25, s6] using hadv
  have hx1_6 : s6.getReg .x1 = pcAt (callIdx + 1) := by
    simp only [s6, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x1 (by decide)]
    rw [hpres5 .x1 (by decide) (by decide) (by decide)]; rfl
  have hret := step_JALR_x0 (by omega) (rfl : s6.pc = pcAt 205)
    (rfl : openingInstr 205 = .base (.JALR .x0 .x1 (0#12))) hx1_6
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

/-- Unified variable-width digest emitter `emitVar` (`206..261`, `≤ 57` steps) for every `2 ≤ l ≤ 23`. -/
private theorem openRuns_call_emitVar {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx l nodeIdx : Nat} {jOff : BitVec 21}
    {fwdBytes : List Byte} {tails : List TailChunk}
    (hcall : callIdx < 262)
    (hl1 : 2 ≤ l) (hl2 : l ≤ 23) (hnode : nodeIdx < levelSize l)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 206)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l nodeIdx)))
    (hx7 : s.getReg .x7 = BitVec.ofNat 64 (levelMetaOC l))
    (hbd : fwdBytes.length + levelBodyBytes l ≤ 8556390424)
    (htbd : tails.length < 210000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    let d := tdNode trapdoor l nodeIdx
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 57 ∧
      s'.pc = pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
        r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x25 → r ≠ .x28 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ bitsToBytes d (levelBodyBytes l)) ∧
      TailState s' (tails ++ [tailChunkOf l d]) ∧
      (∀ q < 5512, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro d
  have hbr := levelBodyBytes_range l hl1 hl2
  set bb := levelBodyBytes l
  set m := bb - 24
  have hm1 : 1 ≤ m := by omega
  have hm2 : m < 8 := by omega
  set srcOff := levelBase l + nodeOffset l nodeIdx
  have hsrc_al : srcOff % 8 = 0 := by
    have h1 := levelBase_align8 l (by omega); have h2 := nodeOffset_align8 l nodeIdx; omega
  have hsrc_bd : srcOff + 32 ≤ 2617246752 := by
    have htb : treeBytes = 1073742880 := treeBytes_eq
    have := nodeOffset_lt_treeBytes l nodeIdx (by omega) hnode; omega
  let chunk := bitsToBytes d bb
  have hclen : chunk.length = bb := bitsToBytes_length d bb
  let c24 := chunk.take 24
  let cM := chunk.drop 24
  have hc24_len : c24.length = 24 := by simp [c24, hclen]; omega
  have hcM_len : cM.length = m := by simp [cM, hclen, m]
  have hsplit : (fwdBytes ++ c24) ++ cM = fwdBytes ++ chunk := by
    rw [List.append_assoc, List.take_append_drop]
  -- 1. JAL -> 206, then emit_3dwords (206..224 -> 225)
  have hr_jal := step_JAL hcall hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 206)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  obtain ⟨s2, hr_3d, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    openRuns_emit_3dwords (base := 206) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := c24)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (by exact hx10) hsrc_al (by omega) (by omega)
      hro1 hw.of_eq hc24_len (fun j hj => by
        simpa [c24, chunk, List.getElem_take] using chunk_tdNode trapdoor l nodeIdx bb j (by omega) (by omega))
  -- 2. Wrap 225..232 (8 steps) into opaque state sM at pcAt 233
  set v3 := s2.getMem (BitVec.ofNat 64 (4294971424 + (srcOff + 24)))
  have hv3_byte : ∀ j < 8, v3.extractLsb' (8 * j) 8 = d.extractLsb' (8 * (24 + j)) 8 := by
    intro j hj
    rw [readOnly_getMem_trapdoor_byte hro2 (srcOff + 24) j (by omega) hj (by omega)]
    have hch := chunk_tdNode trapdoor l nodeIdx 32 (24 + j) (by omega) (by omega)
    simp only [bitsToBytes, List.getElem_map, List.getElem_range] at hch
    dsimp only [srcOff, d]
    simpa only [Nat.add_assoc] using hch
  obtain ⟨sM, hrM, hpcM, hregM, hmemM, hx11_M, hx28_M, hx5_M⟩ :
      ∃ sM, OpenRuns s2 8 8 sM ∧
        sM.pc = pcAt 233 ∧
        (∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x11 → r ≠ .x28 → sM.getReg r = s2.getReg r) ∧
        sM.mem = s2.mem ∧
        sM.getReg .x11 = v3 ∧
        sM.getReg .x28 = BitVec.ofNat 64 (8 * m) ∧
        (∀ j (hj : j < 8), (sM.getReg .x5).extractLsb' (8 * j) 8 =
          if hj' : j < m then cM[j]'(by omega) else 0#8) := by
    have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
    have hx10_2 : s2.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff) := by
      rw [hreg2 .x10 (by decide) (by decide) (by decide) (by decide)]; exact hx10
    have hx7_2 : s2.getReg .x7 = BitVec.ofNat 64 (levelMetaOC l) := by
      rw [hreg2 .x7 (by decide) (by decide) (by decide) (by decide)]; exact hx7
    have haddr225 : s2.getReg .x10 + signExtend12 (24#12) = BitVec.ofNat 64 (4294971424 + (srcOff + 24)) := by
      rw [hx10_2, hse24, bv64_ofNat_add, Nat.add_assoc]
    -- 225: LD x11, 24(x10)
    have h225 := step_LD (by omega) hpc2 (rfl : openingInstr 225 = .base (.LD .x11 .x10 (24#12)))
      (by rw [haddr225]; exact accessValid_ofNat _ 8 (by omega) (by omega))
    let t1 := (s2.setReg .x11 v3).setPC (pcAt 226)
    have h225' : OpenRuns s2 1 1 t1 := by simpa only [haddr225, v3, t1] using h225
    -- 226: ANDI x28, x7, 255
    have h226 := step_ANDI (by omega) (rfl : t1.pc = pcAt 226)
      (rfl : openingInstr 226 = .base (.ANDI .x28 .x7 (255#12)))
    let t2 := (t1.setReg .x28 (BitVec.ofNat 64 bb)).setPC (pcAt 227)
    have h226' : OpenRuns t1 1 1 t2 := by
      have hv : t1.getReg .x7 &&& signExtend12 (255#12) = BitVec.ofNat 64 bb := by
        have hr7 : t1.getReg .x7 = BitVec.ofNat 64 (levelMetaOC l) := hx7_2
        rw [hr7]; exact levelMetaOC_bodyBytes l hl1 hl2
      simpa only [hv, t2] using h226
    -- 227: ADDI x28, x28, 4072 (-24)
    have h227 := step_ADDI (by omega) (rfl : t2.pc = pcAt 227)
      (rfl : openingInstr 227 = .base (.ADDI .x28 .x28 (4072#12)))
    let t3 := (t2.setReg .x28 (BitVec.ofNat 64 m)).setPC (pcAt 228)
    have h227' : OpenRuns t2 1 1 t3 := by
      have hv : t2.getReg .x28 + signExtend12 (4072#12) = BitVec.ofNat 64 m :=
        bv64_add_neg24 bb (by omega)
      simpa only [hv, t3] using h227
    -- 228: SLLI x28, x28, 3
    have h228 := step_SLLI (by omega) (rfl : t3.pc = pcAt 228)
      (rfl : openingInstr 228 = .base (.SLLI .x28 .x28 (3#6)))
    let t4 := (t3.setReg .x28 (BitVec.ofNat 64 (8 * m))).setPC (pcAt 229)
    have h228' : OpenRuns t3 1 1 t4 := by
      have hv : t3.getReg .x28 <<< (3#6 : BitVec 6).toNat = BitVec.ofNat 64 (8 * m) := by
        change BitVec.ofNat 64 m <<< 3 = _; rw [bv64_shl]; congr 1; omega
      simpa only [hv, t4] using h228
    -- 229: ADDI x6, x0, 64
    have h229 := step_ADDI (by omega) (rfl : t4.pc = pcAt 229)
      (rfl : openingInstr 229 = .base (.ADDI .x6 .x0 (64#12)))
    let t5 := (t4.setReg .x6 (BitVec.ofNat 64 64)).setPC (pcAt 230)
    have h229' : OpenRuns t4 1 1 t5 := by
      have hv : t4.getReg .x0 + signExtend12 (64#12) = BitVec.ofNat 64 64 := by
        change (0#64 : Word) + signExtend12 (64#12) = BitVec.ofNat 64 64; decide
      simpa only [hv, t5] using h229
    -- 230: SUB x6, x6, x28
    have h230 := step_SUB (by omega) (rfl : t5.pc = pcAt 230)
      (rfl : openingInstr 230 = .base (.SUB .x6 .x6 .x28))
    let t6 := (t5.setReg .x6 (BitVec.ofNat 64 (8 * (8 - m)))).setPC (pcAt 231)
    have h230' : OpenRuns t5 1 1 t6 := by
      have hv : t5.getReg .x6 - t5.getReg .x28 = BitVec.ofNat 64 (8 * (8 - m)) := by
        change BitVec.ofNat 64 64 - BitVec.ofNat 64 (8 * m) = _
        rw [bv64_ofNat_sub 64 (8 * m) (by omega)]; congr 1; omega
      simpa only [hv, t6] using h230
    -- 231: SLL x5, x11, x6
    have hx6_mod : (t6.getReg .x6).toNat % 64 = 8 * (8 - m) := by
      change (BitVec.ofNat 64 (8 * (8 - m))).toNat % 64 = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * (8 - m) < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    have h231 := step_SLL (by omega) (rfl : t6.pc = pcAt 231)
      (rfl : openingInstr 231 = .base (.SLL .x5 .x11 .x6))
    let t7 := (t6.setReg .x5 (v3 <<< (8 * (8 - m)))).setPC (pcAt 232)
    have h231' : OpenRuns t6 1 1 t7 := by
      have hr11 : t6.getReg .x11 = v3 := rfl
      simpa only [hr11, hx6_mod, t7] using h231
    -- 232: SRL x5, x5, x6
    have h232 := step_SRL (by omega) (rfl : t7.pc = pcAt 232)
      (rfl : openingInstr 232 = .base (.SRL .x5 .x5 .x6))
    let t8 := (t7.setReg .x5 ((v3 <<< (8 * (8 - m))) >>> (8 * (8 - m)))).setPC (pcAt 233)
    have h232' : OpenRuns t7 1 1 t8 := by
      have hx6_7 : (t7.getReg .x6).toNat % 64 = 8 * (8 - m) := hx6_mod
      simpa only [show t7.getReg .x5 = v3 <<< (8 * (8 - m)) from rfl, hx6_7, t8] using h232
    refine ⟨t8, ((((((h225'.trans h226').trans h227').trans h228').trans h229').trans h230').trans h231').trans h232',
      rfl, ?_, rfl, rfl, rfl, ?_⟩
    · intro r h5 h6 h11 h28
      simp only [t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC,
        getReg_setReg_ne' .x5 r (Ne.symm h5), getReg_setReg_ne' .x6 r (Ne.symm h6),
        getReg_setReg_ne' .x28 r (Ne.symm h28), getReg_setReg_ne' .x11 r (Ne.symm h11)]
    · intro j hj
      change ((v3 <<< (8 * (8 - m))) >>> (8 * (8 - m))).extractLsb' (8 * j) 8 = _
      rw [word_mask_low_bytes v3 m (by omega) j hj]
      by_cases hjm : j < m
      · rw [if_pos hjm, dif_pos hjm, hv3_byte j hj]
        simp [cM, chunk, bitsToBytes, Nat.add_assoc]
      · rw [if_neg hjm, dif_neg hjm]
  -- 3. Partial dword append (233..243 -> 244)
  have hroM : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) sM := by
    intro a ha; change sM.mem a = _; rw [hmemM]; exact hro2 a ha
  have hwM : WriterState sM (fwdBytes ++ c24) :=
    hw2.of_eq (h25 := hregM .x25 (by decide) (by decide) (by decide) (by decide))
      (h13 := hregM .x13 (by decide) (by decide) (by decide) (by decide))
      (h14 := hregM .x14 (by decide) (by decide) (by decide) (by decide))
      (h12 := hregM .x12 (by decide) (by decide) (by decide) (by decide))
      (hmem := fun a => by change extractByte (sM.mem _) _ = _; rw [hmemM]; rfl)
  obtain ⟨stP, sP, hrP, hstP, hpcP, hregP, hroP, hwP, hcapP, htailP⟩ :=
    openRuns_emit_partial_var hm1 hm2 hpcM hx28_M
      (by simp only [List.length_append, hc24_len]; omega) hroM hwM hcM_len hx5_M
  rw [hsplit] at hwP
  -- 4. Variable-bit tail push (244..260 -> 261)
  have htP : TailState sP tails :=
    tailState_of_mem_eq ht (by omega)
      (fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl <;> (
          rw [hregP _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hregM _ (by decide) (by decide) (by decide) (by decide),
            hreg2 _ (by decide) (by decide) (by decide) (by decide)]; rfl))
      (fun a ha1 ha2 => by
        rw [htailP a ha1 ha2]; change extractByte (sM.mem _) _ = _; rw [hmemM]; exact htail2 a ha1 ha2)
  have hx7_P : sP.getReg .x7 = BitVec.ofNat 64 (levelMetaOC l) := by
    rw [hregP .x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hregM .x7 (by decide) (by decide) (by decide) (by decide),
      hreg2 .x7 (by decide) (by decide) (by decide) (by decide)]; exact hx7
  have hx28_P : sP.getReg .x28 = BitVec.ofNat 64 (8 * m) := by
    rw [hregP .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx28_M
  have hx11_P : ∀ j < 8, (sP.getReg .x11).extractLsb' (8 * j) 8 = d.extractLsb' (8 * (24 + j)) 8 := by
    rw [hregP .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hx11_M]
    exact hv3_byte
  obtain ⟨stT, sT, hrT, hstT, hpcT, hregT, hroT, hwT, htT, hcapT⟩ :=
    openRuns_push_tailVar hl1 hl2 hpcP hx7_P hx28_P hx11_P
      (by simp only [List.length_append, hclen]; exact hbd) htbd hroP hwP htP
  -- 5. 261: JALR x0, x1, 0
  have hx1_T : sT.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hregT .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hregP .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hregM .x1 (by decide) (by decide) (by decide) (by decide),
      hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl
  have hret := step_JALR_x0 (by omega) hpcT (rfl : openingInstr 261 = .base (.JALR .x0 .x1 (0#12))) hx1_T
  let sRet := sT.setPC (pcAt (callIdx + 1))
  have hpresRet : ∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
      r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x25 → r ≠ .x28 → sRet.getReg r = s.getReg r :=
    fun r h1 h5 h6 h7 h11 h12 h13 h14 h15 h16 h17 h25 h28 => by
      simp only [sRet, MachineState.getReg_setPC]
      rw [hregT r h5 h6 h7 h15 h16 h17, hregP r h5 h6 h12 h13 h14 h25,
        hregM r h5 h6 h11 h28, hreg2 r h5 h6 h12 h25]
      exact getReg_setReg_ne' .x1 r (Ne.symm h1) s _
  have htot := ((((hr_jal.trans hr_3d).trans hrM).trans hrP).trans hrT).trans hret
  refine ⟨1 + 19 + 8 + stP + stT + 1, sRet, htot, by omega, rfl, hpresRet, hroT,
    hwT.of_eq, htT.of_eq, fun a ha => by
      simp only [sRet, getByte_setPC]
      rw [hcapT a ha, hcapP a ha]
      change extractByte (sM.mem _) _ = _; rw [hmemM]; exact hcap2 a ha⟩

/-! ### 6. Entry and Epilogue Blocks (`0..30`, `136..159`) -/

private theorem opening_initial_regs (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    s0.pc = pcAt 0 ∧
    s0.getReg .x2 = BitVec.ofNat 64 68719475728 ∧
    s0.getReg .x12 = BitVec.ofNat 64 4294971424 ∧
    s0.getReg .x13 = BitVec.ofNat 64 6912218176 ∧
    s0.getReg .x15 = BitVec.ofNat 64 11341403200 ∧
    s0.getReg .x16 = BitVec.ofNat 64 positions.card := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  change BitVec.ofNat 64 (dataBase (submission.image .opening)) = _
  rw [opening_dataBase]

private theorem openRuns_entry_prefix (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ s5, OpenRuns s0 5 5 s5 ∧
      s5.pc = pcAt 5 ∧
      s5.getReg .x2 = BitVec.ofNat 64 68719475728 ∧
      s5.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s5.getReg .x24 = BitVec.ofNat 64 6912218176 ∧
      s5.getReg .x25 = BitVec.ofNat 64 11341403200 ∧
      s5.getReg .x26 = BitVec.ofNat 64 11341403200 ∧
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
  let s2 := (s1.setReg .x24 (BitVec.ofNat 64 6912218176)).setPC (pcAt 2)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hr : s1.getReg .x13 = BitVec.ofNat 64 6912218176 := hx13
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 2)
    (rfl : openingInstr 2 = .base (.ADDI .x25 .x15 (0#12)))
  let s3 := (s2.setReg .x25 (BitVec.ofNat 64 11341403200)).setPC (pcAt 3)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hr : s2.getReg .x15 = BitVec.ofNat 64 11341403200 := hx15
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s3] using h3
  have h4 := step_ADDI (by omega) (rfl : s3.pc = pcAt 3)
    (rfl : openingInstr 3 = .base (.ADDI .x26 .x15 (0#12)))
  let s4 := (s3.setReg .x26 (BitVec.ofNat 64 11341403200)).setPC (pcAt 4)
  have h4' : OpenRuns s3 1 1 s4 := by
    have hr : s3.getReg .x15 = BitVec.ofNat 64 11341403200 := hx15
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s4] using h4
  have h5 := step_ADDI (by omega) (rfl : s4.pc = pcAt 4)
    (rfl : openingInstr 4 = .base (.ADDI .x27 .x16 (0#12)))
  let s5 := (s4.setReg .x27 (BitVec.ofNat 64 positions.card)).setPC (pcAt 5)
  have h5' : OpenRuns s4 1 1 s5 := by
    have hr : s4.getReg .x16 = BitVec.ofNat 64 positions.card := hx16
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s5] using h5
  exact ⟨s5, (((h1'.trans h2').trans h3').trans h4').trans h5',
    rfl, hx2, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem openRuns_empty_epilogue {s : MachineState} (hpc : s.pc = pcAt 156) :
    ∃ sHalt, OpenRuns s 3 3 sHalt ∧
      sHalt.pc = pcAt 159 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = 0#64 ∧
      sHalt.mem = s.mem := by
  have h1 := step_ADDI (by omega) hpc (rfl : openingInstr 156 = .base (.ADDI .x11 .x0 (0#12)))
  let s1 := (s.setReg .x11 0#64).setPC (pcAt 157)
  have h1' : OpenRuns s 1 1 s1 := by
    have hv : s.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s1] using h1
  have h2 := step_ADDI (by omega) (rfl : s1.pc = pcAt 157)
    (rfl : openingInstr 157 = .base (.ADDI .x5 .x0 (1#12)))
  let s2 := (s1.setReg .x5 1#64).setPC (pcAt 158)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x0 + signExtend12 (1#12) = 1#64 := by
      change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 158)
    (rfl : openingInstr 158 = .base (.ADDI .x10 .x0 (0#12)))
  let s3 := (s2.setReg .x10 0#64).setPC (pcAt 159)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hv : s2.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s3] using h3
  exact ⟨s3, (h1'.trans h2').trans h3', rfl, rfl, rfl, rfl, rfl⟩

private theorem openRuns_entry_nonzero (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (hne : positions.card ≠ 0) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ s31, OpenRuns s0 31 31 s31 ∧
      s31.pc = pcAt 31 ∧
      s31.getReg .x2 = BitVec.ofNat 64 68719475728 ∧
      s31.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s31.getReg .x12 = 0#64 ∧
      s31.getReg .x13 = 0#64 ∧
      s31.getReg .x14 = BitVec.ofNat 64 63 ∧
      s31.getReg .x15 = BitVec.ofNat 64 tailBufBase ∧
      s31.getReg .x16 = 0#64 ∧
      s31.getReg .x17 = 0#64 ∧
      s31.getReg .x18 = BitVec.ofNat 64 (4294971424 + (rowOff + 72)) ∧
      s31.getReg .x19 = 3#64 ∧
      s31.getReg .x20 = BitVec.ofNat 64 FULL_TRIPLETS ∧
      s31.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s31.getReg .x24 = BitVec.ofNat 64 6912218176 ∧
      s31.getReg .x25 = BitVec.ofNat 64 11341403200 ∧
      s31.getReg .x26 = BitVec.ofNat 64 11341403200 ∧
      s31.getReg .x27 = BitVec.ofNat 64 positions.card ∧
      s31.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
      s31.mem = s0.mem := by
  intro s0
  obtain ⟨s5, hr5, hpc5, hx2, hx9, hx24, hx25, hx26, hx27, hmem5⟩ :=
    openRuns_entry_prefix trapdoor positions
  have hcard := positions_card_le positions
  have h6 := step_BEQ_not_taken (by omega) hpc5
    (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (604#13)))
    (by rw [hx27]; exact bv64_ofNat_ne (by omega) (by decide) hne)
  -- Wrap 6..17 into opaque state s18
  obtain ⟨s18, hr18, hpc18, hreg18, hmem18, hx12_18, hx13_18, hx14_18, hx15_18, hx16_18, hx17_18, hx31_18⟩ :
      ∃ s18, OpenRuns (s5.setPC (pcAt 6)) 12 12 s18 ∧
        s18.pc = pcAt 18 ∧
        (∀ r, r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x31 →
          s18.getReg r = s5.getReg r) ∧
        s18.mem = s5.mem ∧
        s18.getReg .x12 = 0#64 ∧ s18.getReg .x13 = 0#64 ∧ s18.getReg .x14 = BitVec.ofNat 64 63 ∧
        s18.getReg .x15 = BitVec.ofNat 64 tailBufBase ∧ s18.getReg .x16 = 0#64 ∧
        s18.getReg .x17 = 0#64 ∧ s18.getReg .x31 = BitVec.ofNat 64 tailBufBase := by
    let s6 := s5.setPC (pcAt 6)
    have h7 := step_ADDI (by omega) (rfl : s6.pc = pcAt 6) (rfl : openingInstr 6 = .base (.ADDI .x12 .x0 (0#12)))
    let s7 := (s6.setReg .x12 0#64).setPC (pcAt 7)
    have h7' : OpenRuns s6 1 1 s7 := by
      have hv : s6.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + _ = _; decide
      simpa only [hv, s7] using h7
    have h8 := step_ADDI (by omega) (rfl : s7.pc = pcAt 7) (rfl : openingInstr 7 = .base (.ADDI .x13 .x0 (0#12)))
    let s8 := (s7.setReg .x13 0#64).setPC (pcAt 8)
    have h8' : OpenRuns s7 1 1 s8 := by
      have hv : s7.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + _ = _; decide
      simpa only [hv, s8] using h8
    have h9 := step_ADDI (by omega) (rfl : s8.pc = pcAt 8) (rfl : openingInstr 8 = .base (.ADDI .x14 .x0 (63#12)))
    let s9 := (s8.setReg .x14 (BitVec.ofNat 64 63)).setPC (pcAt 9)
    have h9' : OpenRuns s8 1 1 s9 := by
      have hv : s8.getReg .x0 + signExtend12 (63#12) = BitVec.ofNat 64 63 := by change (0#64 : Word) + _ = _; decide
      simpa only [hv, s9] using h9
    have h10 := step_ADDI (by omega) (rfl : s9.pc = pcAt 9) (rfl : openingInstr 9 = .base (.ADDI .x31 .x0 (2#12)))
    let s10 := (s9.setReg .x31 (BitVec.ofNat 64 2)).setPC (pcAt 10)
    have h10' : OpenRuns s9 1 1 s10 := by
      have hv : s9.getReg .x0 + signExtend12 (2#12) = BitVec.ofNat 64 2 := by change (0#64 : Word) + _ = _; decide
      simpa only [hv, s10] using h10
    have h11 := step_SLLI (by omega) (rfl : s10.pc = pcAt 10) (rfl : openingInstr 10 = .base (.SLLI .x31 .x31 (11#6)))
    let s11 := (s10.setReg .x31 (BitVec.ofNat 64 4096)).setPC (pcAt 11)
    have h11' : OpenRuns s10 1 1 s11 := by
      have hv : s10.getReg .x31 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096 := by
        change BitVec.ofNat 64 2 <<< (11#6 : BitVec 6).toNat = _; decide
      simpa only [hv, s11] using h11
    have h12 := step_ADDI (by omega) (rfl : s11.pc = pcAt 11) (rfl : openingInstr 11 = .base (.ADDI .x31 .x31 (672#12)))
    let s12 := (s11.setReg .x31 (BitVec.ofNat 64 4768)).setPC (pcAt 12)
    have h12' : OpenRuns s11 1 1 s12 := by
      have hv : s11.getReg .x31 + signExtend12 (672#12) = BitVec.ofNat 64 4768 := by
        change BitVec.ofNat 64 4096 + _ = _; decide
      simpa only [hv, s12] using h12
    have h13 := step_SLLI (by omega) (rfl : s12.pc = pcAt 12) (rfl : openingInstr 12 = .base (.SLLI .x31 .x31 (11#6)))
    let s13 := (s12.setReg .x31 (BitVec.ofNat 64 9764864)).setPC (pcAt 13)
    have h13' : OpenRuns s12 1 1 s13 := by
      have hv : s12.getReg .x31 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 9764864 := by
        change BitVec.ofNat 64 4768 <<< (11#6 : BitVec 6).toNat = _; decide
      simpa only [hv, s13] using h13
    have h14 := step_ADDI (by omega) (rfl : s13.pc = pcAt 13) (rfl : openingInstr 13 = .base (.ADDI .x31 .x31 (761#12)))
    let s14 := (s13.setReg .x31 (BitVec.ofNat 64 9765625)).setPC (pcAt 14)
    have h14' : OpenRuns s13 1 1 s14 := by
      have hv : s13.getReg .x31 + signExtend12 (761#12) = BitVec.ofNat 64 9765625 := by
        change BitVec.ofNat 64 9764864 + _ = _; decide
      simpa only [hv, s14] using h14
    have h15 := step_SLLI (by omega) (rfl : s14.pc = pcAt 14) (rfl : openingInstr 14 = .base (.SLLI .x31 .x31 (11#6)))
    let s15 := (s14.setReg .x31 (BitVec.ofNat 64 tailBufBase)).setPC (pcAt 15)
    have h15' : OpenRuns s14 1 1 s15 := by
      have hv : s14.getReg .x31 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 tailBufBase := by
        change BitVec.ofNat 64 9765625 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 20000000000; decide
      simpa only [hv, s15] using h15
    have h16 := step_ADDI (by omega) (rfl : s15.pc = pcAt 15) (rfl : openingInstr 15 = .base (.ADDI .x15 .x31 (0#12)))
    let s16 := (s15.setReg .x15 (BitVec.ofNat 64 tailBufBase)).setPC (pcAt 16)
    have h16' : OpenRuns s15 1 1 s16 := by
      have hv : s15.getReg .x31 + signExtend12 (0#12) = BitVec.ofNat 64 tailBufBase := by
        change BitVec.ofNat 64 20000000000 + _ = BitVec.ofNat 64 20000000000; decide
      simpa only [hv, s16] using h16
    have h17 := step_ADDI (by omega) (rfl : s16.pc = pcAt 16) (rfl : openingInstr 16 = .base (.ADDI .x16 .x0 (0#12)))
    let s17 := (s16.setReg .x16 0#64).setPC (pcAt 17)
    have h17' : OpenRuns s16 1 1 s17 := by
      have hv : s16.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + _ = _; decide
      simpa only [hv, s17] using h17
    have h18 := step_ADDI (by omega) (rfl : s17.pc = pcAt 17) (rfl : openingInstr 17 = .base (.ADDI .x17 .x0 (0#12)))
    let s18 := (s17.setReg .x17 0#64).setPC (pcAt 18)
    have h18' : OpenRuns s17 1 1 s18 := by
      have hv : s17.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + _ = _; decide
      simpa only [hv, s18] using h18
    have ha := ((((h7'.trans h8').trans h9').trans h10').trans h11').trans h12'
    have hb := ((((ha.trans h13').trans h14').trans h15').trans h16').trans h17'
    refine ⟨s18, hb.trans h18', rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    intro r h12ne h13ne h14ne h15ne h16ne h17ne h31ne
    simp only [s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, MachineState.getReg_setPC,
      getReg_setReg_ne' .x17 r (Ne.symm h17ne), getReg_setReg_ne' .x16 r (Ne.symm h16ne),
      getReg_setReg_ne' .x15 r (Ne.symm h15ne), getReg_setReg_ne' .x31 r (Ne.symm h31ne),
      getReg_setReg_ne' .x14 r (Ne.symm h14ne), getReg_setReg_ne' .x13 r (Ne.symm h13ne),
      getReg_setReg_ne' .x12 r (Ne.symm h12ne)]
  -- 18..30: trapdoor/salt/triplet/cap constants
  have h19 := step_ADDI (by omega) hpc18 (rfl : openingInstr 18 = .base (.ADDI .x6 .x0 (256#12)))
  let s19 := (s18.setReg .x6 (BitVec.ofNat 64 256)).setPC (pcAt 19)
  have h19' : OpenRuns s18 1 1 s19 := by
    have hv : s18.getReg .x0 + signExtend12 (256#12) = BitVec.ofNat 64 256 := by change (0#64 : Word) + _ = _; decide
    simpa only [hv, s19] using h19
  have h20 := step_SLLI (by omega) (rfl : s19.pc = pcAt 19) (rfl : openingInstr 19 = .base (.SLLI .x6 .x6 (11#6)))
  let s20 := (s19.setReg .x6 (BitVec.ofNat 64 524288)).setPC (pcAt 20)
  have h20' : OpenRuns s19 1 1 s20 := by
    have hv : s19.getReg .x6 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 524288 := by
      change BitVec.ofNat 64 256 <<< (11#6 : BitVec 6).toNat = _; decide
    simpa only [hv, s20] using h20
  have h21 := step_SLLI (by omega) (rfl : s20.pc = pcAt 20) (rfl : openingInstr 20 = .base (.SLLI .x6 .x6 (11#6)))
  let s21 := (s20.setReg .x6 (BitVec.ofNat 64 1073741824)).setPC (pcAt 21)
  have h21' : OpenRuns s20 1 1 s21 := by
    have hv : s20.getReg .x6 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 1073741824 := by
      change BitVec.ofNat 64 524288 <<< (11#6 : BitVec 6).toNat = _; decide
    simpa only [hv, s21] using h21
  have h22 := step_ADDI (by omega) (rfl : s21.pc = pcAt 21) (rfl : openingInstr 21 = .base (.ADDI .x6 .x6 (1128#12)))
  let s22 := (s21.setReg .x6 (BitVec.ofNat 64 (rowOff + 72))).setPC (pcAt 22)
  have h22' : OpenRuns s21 1 1 s22 := by
    have hv : s21.getReg .x6 + signExtend12 (1128#12) = BitVec.ofNat 64 (rowOff + 72) := by
      change BitVec.ofNat 64 1073741824 + signExtend12 (1128#12) = BitVec.ofNat 64 (rowOff + 72)
      rw [rowOff_eq]; decide
    simpa only [hv, s22] using h22
  have h23 := step_ADD (by omega) (rfl : s22.pc = pcAt 22) (rfl : openingInstr 22 = .base (.ADD .x18 .x9 .x6))
  let s23 := (s22.setReg .x18 (BitVec.ofNat 64 (4294971424 + (rowOff + 72)))).setPC (pcAt 23)
  have h23' : OpenRuns s22 1 1 s23 := by
    have hr9 : s22.getReg .x9 = BitVec.ofNat 64 4294971424 :=
      (hreg18 .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx9
    simpa only [hr9, show s22.getReg .x6 = BitVec.ofNat 64 (rowOff + 72) from rfl, bv64_ofNat_add, s23] using h23
  have h24 := step_ADDI (by omega) (rfl : s23.pc = pcAt 23) (rfl : openingInstr 23 = .base (.ADDI .x19 .x0 (3#12)))
  let s24 := (s23.setReg .x19 3#64).setPC (pcAt 24)
  have h24' : OpenRuns s23 1 1 s24 := by
    have hv : s23.getReg .x0 + signExtend12 (3#12) = 3#64 := by change (0#64 : Word) + _ = _; decide
    simpa only [hv, s24] using h24
  have h25 := step_ADDI (by omega) (rfl : s24.pc = pcAt 24) (rfl : openingInstr 24 = .base (.ADDI .x20 .x0 (1#12)))
  let s25 := (s24.setReg .x20 (BitVec.ofNat 64 1)).setPC (pcAt 25)
  have h25' : OpenRuns s24 1 1 s25 := by
    have hv : s24.getReg .x0 + signExtend12 (1#12) = BitVec.ofNat 64 1 := by change (0#64 : Word) + _ = _; decide
    simpa only [hv, s25] using h25
  have h26 := step_SLLI (by omega) (rfl : s25.pc = pcAt 25) (rfl : openingInstr 25 = .base (.SLLI .x20 .x20 (11#6)))
  let s26 := (s25.setReg .x20 (BitVec.ofNat 64 2048)).setPC (pcAt 26)
  have h26' : OpenRuns s25 1 1 s26 := by
    have hv : s25.getReg .x20 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 2048 := by
      change BitVec.ofNat 64 1 <<< (11#6 : BitVec 6).toNat = _; decide
    simpa only [hv, s26] using h26
  have h27 := step_ADDI (by omega) (rfl : s26.pc = pcAt 26) (rfl : openingInstr 26 = .base (.ADDI .x20 .x20 (682#12)))
  let s27 := (s26.setReg .x20 (BitVec.ofNat 64 2730)).setPC (pcAt 27)
  have h27' : OpenRuns s26 1 1 s27 := by
    have hv : s26.getReg .x20 + signExtend12 (682#12) = BitVec.ofNat 64 2730 := by
      change BitVec.ofNat 64 2048 + _ = _; decide
    simpa only [hv, s27] using h27
  have h28 := step_SLLI (by omega) (rfl : s27.pc = pcAt 27) (rfl : openingInstr 27 = .base (.SLLI .x20 .x20 (11#6)))
  let s28 := (s27.setReg .x20 (BitVec.ofNat 64 5591040)).setPC (pcAt 28)
  have h28' : OpenRuns s27 1 1 s28 := by
    have hv : s27.getReg .x20 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 5591040 := by
      change BitVec.ofNat 64 2730 <<< (11#6 : BitVec 6).toNat = _; decide
    simpa only [hv, s28] using h28
  have h29 := step_ADDI (by omega) (rfl : s28.pc = pcAt 28) (rfl : openingInstr 28 = .base (.ADDI .x20 .x20 (1365#12)))
  let s29 := (s28.setReg .x20 (BitVec.ofNat 64 FULL_TRIPLETS)).setPC (pcAt 29)
  have h29' : OpenRuns s28 1 1 s29 := by
    have hv : s28.getReg .x20 + signExtend12 (1365#12) = BitVec.ofNat 64 FULL_TRIPLETS := by
      change BitVec.ofNat 64 5591040 + signExtend12 (1365#12) = BitVec.ofNat 64 FULL_TRIPLETS
      rw [full_triplets_eq]; decide
    simpa only [hv, s29] using h29
  have h30 := step_ADDI (by omega) (rfl : s29.pc = pcAt 29) (rfl : openingInstr 29 = .base (.ADDI .x21 .x0 (2#12)))
  let s30 := (s29.setReg .x21 (BitVec.ofNat 64 2)).setPC (pcAt 30)
  have h30' : OpenRuns s29 1 1 s30 := by
    have hv : s29.getReg .x0 + signExtend12 (2#12) = BitVec.ofNat 64 2 := by change (0#64 : Word) + _ = _; decide
    simpa only [hv, s30] using h30
  have h31 := step_SLLI (by omega) (rfl : s30.pc = pcAt 30) (rfl : openingInstr 30 = .base (.SLLI .x21 .x21 (11#6)))
  let s31 := (s30.setReg .x21 (BitVec.ofNat 64 4096)).setPC (pcAt 31)
  have h31' : OpenRuns s30 1 1 s31 := by
    have hv : s30.getReg .x21 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096 := by
      change BitVec.ofNat 64 2 <<< (11#6 : BitVec 6).toNat = _; decide
    simpa only [hv, s31] using h31
  have hc := (((((h19'.trans h20').trans h21').trans h22').trans h23').trans h24').trans h25'
  have hd := ((((hc.trans h26').trans h27').trans h28').trans h29').trans h30'
  have htot := ((hr5.trans h6).trans hr18).trans (hd.trans h31')
  have hpres31 : ∀ r, r ≠ .x6 → r ≠ .x18 → r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → s31.getReg r = s18.getReg r :=
    fun r h6ne h18ne h19ne h20ne h21ne => by
      simp only [s31, s30, s29, s28, s27, s26, s25, s24, s23, s22, s21, s20, s19, MachineState.getReg_setPC,
        getReg_setReg_ne' .x21 r (Ne.symm h21ne), getReg_setReg_ne' .x20 r (Ne.symm h20ne),
        getReg_setReg_ne' .x19 r (Ne.symm h19ne), getReg_setReg_ne' .x18 r (Ne.symm h18ne),
        getReg_setReg_ne' .x6 r (Ne.symm h6ne)]
  refine ⟨s31, htot, rfl,
    (hpres31 .x2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hreg18 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx2),
    (hpres31 .x9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hreg18 .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx9),
    (hpres31 .x12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx12_18,
    (hpres31 .x13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx13_18,
    (hpres31 .x14 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx14_18,
    (hpres31 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx15_18,
    (hpres31 .x16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx16_18,
    (hpres31 .x17 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx17_18,
    rfl, rfl, rfl, rfl,
    (hpres31 .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hreg18 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx24),
    (hpres31 .x25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hreg18 .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx25),
    (hpres31 .x26 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hreg18 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx26),
    (hpres31 .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hreg18 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx27),
    (hpres31 .x31 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx31_18,
    hmem18.trans hmem5⟩

private theorem openRuns_flush_wbuf {s : MachineState} {fwdBytes : List Byte} {tails : List TailChunk}
    (hpc : s.pc = pcAt 136)
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11341403200)
    (hfbd : fwdBytes.length ≤ 8556390424)
    (htbd : tails.length ≤ 210000000)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 37 ∧
      s'.pc = pcAt 143 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 11341403200 ∧
      ProofPrefix s' fwdBytes ∧
      TailState s' tails := by
  set q := fwdBytes.length / 8
  set r := fwdBytes.length % 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  -- 136: ADDI x10, x25, 0
  have h136 := step_ADDI (by omega) hpc (rfl : openingInstr 136 = .base (.ADDI .x10 .x25 (0#12)))
  let s1 := (s.setReg .x10 (BitVec.ofNat 64 (11341403200 + 8 * q))).setPC (pcAt 137)
  have h136' : OpenRuns s 1 1 s1 := by
    rw [hw.rx25, hse0, bv64_ofNat_add, Nat.add_zero] at h136; exact h136
  by_cases hr0 : r = 0
  · have h137 := step_BEQ_taken (by omega) (rfl : s1.pc = pcAt 137)
      (rfl : openingInstr 137 = .base (.BEQ .x13 .x0 (24#13)))
      (by have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13; rw [h, hr0]; rfl)
      (by decide : pcAt 137 + signExtend13 (24#13) = pcAt 143)
    let s2 := s1.setPC (pcAt 143)
    refine ⟨2, s2, h136'.trans h137, by omega, rfl, ?_, hx26, ?_, ht.of_eq⟩
    · change BitVec.ofNat 64 (11341403200 + 8 * q) = _
      congr 1; omega
    · intro j hj
      exact hw.memDwords j (by omega)
  · have hrpos : 0 < r := by omega
    have h137 := step_BEQ_not_taken (by omega) (rfl : s1.pc = pcAt 137)
      (rfl : openingInstr 137 = .base (.BEQ .x13 .x0 (24#13)))
      (by have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13
          rw [h]; exact bv64_ofNat_ne (by omega) (by decide) (by omega))
    let s2 := s1.setPC (pcAt 138)
    have hloop : ∀ k (hk : k ≤ r), ∃ sk, OpenRuns s2 (5 * k) (5 * k) sk ∧
        sk.pc = (if k < r then pcAt 138 else pcAt 143) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (11341403200 + 8 * q + k) ∧
        sk.getReg .x13 = BitVec.ofNat 64 (8 * (r - k)) ∧
        sk.getReg .x26 = BitVec.ofNat 64 11341403200 ∧
        (∀ j (hj : j < r - k), (sk.getReg .x12).extractLsb' (8 * j) 8 = fwdBytes[8 * q + k + j]'(by omega)) ∧
        (∀ j (hj : j < 8 * q + k), sk.getByte (BitVec.ofNat 64 (11341403200 + j)) = fwdBytes[j]'(by omega)) ∧
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
        have hpck' : sk.pc = pcAt 138 := by simpa only [show k < r by omega, ite_true] using hpck
        have haddr : sk.getReg .x10 + signExtend12 (0#12) = BitVec.ofNat 64 (11341403200 + 8 * q + k) := by
          rw [hx10k, hse0, bv64_ofNat_add, Nat.add_zero]
        have ha := step_SB (by omega) hpck' (rfl : openingInstr 138 = .base (.SB .x10 .x12 (0#12)))
          (by rw [haddr]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        have hbyte0 : (sk.getReg .x12).truncate 8 = fwdBytes[8 * q + k]'(by omega) := by
          rw [word_truncate8_eq_extractLsb'0]
          simpa using hwLoK 0 (by omega)
        let sa := (sk.setByte (BitVec.ofNat 64 (11341403200 + 8 * q + k))
          (fwdBytes[8 * q + k]'(by omega))).setPC (pcAt 139)
        have ha' : OpenRuns sk 1 1 sa := by simpa only [haddr, hbyte0, sa] using ha
        have hb := step_ADDI (by omega) (rfl : sa.pc = pcAt 139)
          (rfl : openingInstr 139 = .base (.ADDI .x10 .x10 (1#12)))
        let sb := (sa.setReg .x10 (BitVec.ofNat 64 (11341403200 + 8 * q + (k + 1)))).setPC (pcAt 140)
        have hb' : OpenRuns sa 1 1 sb := by
          have hr10 : sa.getReg .x10 = BitVec.ofNat 64 (11341403200 + 8 * q + k) := by
            simp only [sa, MachineState.getReg_setPC, getReg_setByte]; exact hx10k
          rw [hr10, hse1, bv64_ofNat_add, Nat.add_assoc] at hb; exact hb
        have hc := step_SRLI (by omega) (rfl : sb.pc = pcAt 140)
          (rfl : openingInstr 140 = .base (.SRLI .x12 .x12 (8#6)))
        let sc := (sb.setReg .x12 (sk.getReg .x12 >>> 8)).setPC (pcAt 141)
        have hc' : OpenRuns sb 1 1 sc := by
          have hr12 : sb.getReg .x12 = sk.getReg .x12 := by
            simp only [sb, sa, MachineState.getReg_setPC, getReg_setByte,
              getReg_setReg_ne' .x10 .x12 (by decide)]
          simpa only [hr12, show (8#6 : BitVec 6).toNat = 8 from rfl, sc] using hc
        have hd := step_ADDI (by omega) (rfl : sc.pc = pcAt 141)
          (rfl : openingInstr 141 = .base (.ADDI .x13 .x13 (4088#12)))
        let sd := (sc.setReg .x13 (BitVec.ofNat 64 (8 * (r - (k + 1))))).setPC (pcAt 142)
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
            sd.getByte (BitVec.ofNat 64 (11341403200 + j)) = fwdBytes[j]'(by omega) := by
          intro j hj
          simp only [sd, sc, sb, sa, getByte_setPC, getByte_setReg, set_byte_read]
          by_cases hlast : j = 8 * q + k
          · subst hlast
            rw [show 11341403200 + (8 * q + k) = 11341403200 + 8 * q + k by omega, if_pos rfl]
          · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
            exact hmemk j (by omega)
        have htd : TailState sd tails := by
          have htb : tailBufBase = 20000000000 := rfl
          have ht' := tailState_setByte_outside (11341403200 + 8 * q + k)
            (fwdBytes[8 * q + k]'(by omega)) htk htbd (by omega)
          exact ⟨htk.valid,
            by simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
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
        have hx10_d : sd.getReg .x10 = BitVec.ofNat 64 (11341403200 + 8 * q + (k + 1)) := by
          simp only [sd, sc, sb, MachineState.getReg_setPC,
            getReg_setReg_ne' .x13 .x10 (by decide), getReg_setReg_ne' .x12 .x10 (by decide)]; rfl
        have hx26_d : sd.getReg .x26 = BitVec.ofNat 64 11341403200 := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x13 .x26 (by decide), getReg_setReg_ne' .x12 .x26 (by decide),
            getReg_setReg_ne' .x10 .x26 (by decide)]; exact hx26k
        by_cases hmore : k + 1 < r
        · have he := step_BNE_taken (by omega) (rfl : sd.pc = pcAt 142)
            (rfl : openingInstr 142 = .base (.BNE .x13 .x0 (8176#13)))
            (by change BitVec.ofNat 64 (8 * (r - (k + 1))) ≠ BitVec.ofNat 64 0
                exact bv64_ofNat_ne (by omega) (by decide) (by omega))
            (by decide : pcAt 142 + signExtend13 (8176#13) = pcAt 138)
          exact ⟨sd.setPC (pcAt 138), by simpa only [Nat.mul_succ] using (hrk.trans hstep4).trans he,
            by rw [if_pos hmore]; rfl, hx10_d, rfl, hx26_d, hwLo_d, hmem_d, htd.of_eq⟩
        · have hdone : r - (k + 1) = 0 := by omega
          have he := step_BNE_not_taken (by omega) (rfl : sd.pc = pcAt 142)
            (rfl : openingInstr 142 = .base (.BNE .x13 .x0 (8176#13)))
            (by change BitVec.ofNat 64 (8 * (r - (k + 1))) = 0#64; rw [hdone])
          exact ⟨sd.setPC (pcAt 143), by simpa only [Nat.mul_succ] using (hrk.trans hstep4).trans he,
            by rw [if_neg hmore]; rfl, hx10_d, rfl, hx26_d, hwLo_d, hmem_d, htd.of_eq⟩
    obtain ⟨sf, hrf, hpcf, hx10f, _, hx26f, _, hmemf, htf⟩ := hloop r (Nat.le_refl r)
    have hpcf' : sf.pc = pcAt 143 := by simpa only [Nat.lt_irrefl, ite_false] using hpcf
    refine ⟨2 + 5 * r, sf, (h136'.trans h137).trans hrf, by omega, hpcf',
      by rw [hx10f]; congr 1; omega, hx26f,
      fun j hj => hmemf j (by omega), htf⟩

private theorem openRuns_flush_tail {s : MachineState} {fwdBytes : List Byte} {tails : List TailChunk}
    (hpc : s.pc = pcAt 143)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11341403200)
    (hfbd : fwdBytes.length ≤ 8556390424)
    (htbd : tails.length ≤ 210000000)
    (hpr : ProofPrefix s fwdBytes)
    (ht : TailState s tails) :
    let packed := packVarBits tails
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 3 ∧
      s'.pc = pcAt 146 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 11341403200 ∧
      s'.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
      s'.getReg .x15 = BitVec.ofNat 64 (tailBufBase + packed.length) ∧
      ProofPrefix s' fwdBytes ∧
      TailBufPrefix s' packed := by
  intro packed
  have htb : tailBufBase = 20000000000 := rfl
  set st := tails.foldl packVarStep ([], 0, 0)
  have hst_bd := packVar_foldl_bounds tails ht.valid
  have htot_le := totalTailBits_le_7mul tails ht.valid
  set acc := st.1
  set tBuf := st.2.1
  set tCnt := st.2.2
  have htCnt_lt : tCnt < 8 := hst_bd.1
  have htBuf_lt : tBuf < 2 ^ tCnt := hst_bd.2.1
  have hacc_len : 8 * acc.length + tCnt = totalTailBits tails := hst_bd.2.2
  have hpow : 2 ^ tCnt ≤ 128 := by
    have h1 : 2 ^ tCnt ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 7 = 128 := by decide
    omega
  by_cases hcnt0 : tCnt = 0
  · have h143 := step_BEQ_taken (by omega) hpc
      (rfl : openingInstr 143 = .base (.BEQ .x17 .x0 (12#13)))
      (by rw [ht.rx17]; exact congrArg (BitVec.ofNat 64) hcnt0)
      (by decide : pcAt 143 + signExtend13 (12#13) = pcAt 146)
    have hpack_eq : packed = acc := by
      unfold packed packVarBits packVarFinish
      change (if 0 < tCnt then _ else acc) = acc
      rw [if_neg (by omega)]
    rw [hpack_eq]
    exact ⟨1, s.setPC (pcAt 146), h143, by omega, rfl, hx10, hx26, ht.rx31, ht.rx15, hpr, ht.memTail⟩
  · have hpos : 0 < tCnt := by omega
    have hpack_eq : packed = acc ++ [BitVec.ofNat 8 tBuf] := by
      unfold packed packVarBits packVarFinish
      change (if 0 < tCnt then acc ++ [BitVec.ofNat 8 tBuf] else acc) = _
      rw [if_pos hpos]
    have h143 := step_BEQ_not_taken (by omega) hpc
      (rfl : openingInstr 143 = .base (.BEQ .x17 .x0 (12#13)))
      (by rw [ht.rx17]; exact bv64_ofNat_ne (by omega) (by decide) hcnt0)
    let s1 := s.setPC (pcAt 144)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have haddr : s1.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + acc.length) := by
      have hr15 : s1.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := ht.rx15
      rw [hr15, hse0, bv64_ofNat_add, Nat.add_zero]
    have h144 := step_SB (by omega) (rfl : s1.pc = pcAt 144)
      (rfl : openingInstr 144 = .base (.SB .x15 .x16 (0#12)))
      (by rw [haddr]; exact accessValid_ofNat _ 1 (by omega) (by omega))
    let s2 := (s1.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 tBuf)).setPC (pcAt 145)
    have h144' : OpenRuns s1 1 1 s2 := by
      have htr : (s1.getReg .x16).truncate 8 = BitVec.ofNat 8 tBuf := by
        have hr16 : s1.getReg .x16 = BitVec.ofNat 64 tBuf := ht.rx16
        rw [hr16]; exact bv64_ofNat_truncate8 tBuf (by omega)
      simpa only [haddr, htr, s2] using h144
    have h145 := step_ADDI (by omega) (rfl : s2.pc = pcAt 145)
      (rfl : openingInstr 145 = .base (.ADDI .x15 .x15 (1#12)))
    let s3 := (s2.setReg .x15 (BitVec.ofNat 64 (tailBufBase + packed.length))).setPC (pcAt 146)
    have h145' : OpenRuns s2 1 1 s3 := by
      have hr15 : s2.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := by
        simp only [s2, MachineState.getReg_setPC, getReg_setByte]; exact ht.rx15
      have hv : s2.getReg .x15 + signExtend12 (1#12) = BitVec.ofNat 64 (tailBufBase + packed.length) := by
        rw [hr15, hse1, bv64_ofNat_add, hpack_eq, List.length_append, List.length_singleton, Nat.add_assoc]
      simpa only [hv, s3] using h145
    refine ⟨3, s3, (h143.trans h144').trans h145', Nat.le_refl 3, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
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
    (hpc : s.pc = pcAt 146)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11341403200)
    (hx31 : s.getReg .x31 = BitVec.ofNat 64 tailBufBase)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + packed.length))
    (hbd : fwdBytes.length + packed.length ≤ 8556390424)
    (hpr : ProofPrefix s fwdBytes)
    (htail : TailBufPrefix s packed) :
    ∃ s', OpenRuns s (1 + 5 * packed.length) (1 + 5 * packed.length) s' ∧
      s'.pc = pcAt 152 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (11341403200 + (fwdBytes ++ packed.reverse).length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 11341403200 ∧
      ProofPrefix s' (fwdBytes ++ packed.reverse) := by
  have htb : tailBufBase = 20000000000 := rfl
  set m := packed.length
  by_cases hm0 : m = 0
  · have hnil : packed = [] := List.eq_nil_of_length_eq_zero hm0
    have h146 := step_BEQ_taken (by omega) hpc
      (rfl : openingInstr 146 = .base (.BEQ .x15 .x31 (24#13)))
      (by rw [hx15, hx31, hm0, Nat.add_zero])
      (by decide : pcAt 146 + signExtend13 (24#13) = pcAt 152)
    subst hnil
    exact ⟨s.setPC (pcAt 152),
      by rw [hm0, Nat.mul_zero, Nat.add_zero]; exact h146,
      rfl,
      by rw [List.reverse_nil, List.append_nil]; exact hx10,
      hx26,
      by rw [List.reverse_nil, List.append_nil]; exact hpr⟩
  · have hmpos : 0 < m := by omega
    have h146 := step_BEQ_not_taken (by omega) hpc
      (rfl : openingInstr 146 = .base (.BEQ .x15 .x31 (24#13)))
      (by rw [hx15, hx31]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
    let s1 := s.setPC (pcAt 147)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have hloop : ∀ u ≤ m, ∃ su, OpenRuns s1 (5 * u) (5 * u) su ∧
        su.pc = (if u < m then pcAt 147 else pcAt 152) ∧
        su.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (m - u)) ∧
        su.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
        su.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length + u) ∧
        su.getReg .x26 = BitVec.ofNat 64 11341403200 ∧
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
        have hpcu' : su.pc = pcAt 147 := by simpa only [show u < m by omega, ite_true] using hpcu
        have ha := step_ADDI (by omega) hpcu' (rfl : openingInstr 147 = .base (.ADDI .x15 .x15 (4095#12)))
        let sa := (su.setReg .x15 (BitVec.ofNat 64 (tailBufBase + (m - (u + 1))))).setPC (pcAt 148)
        have ha' : OpenRuns su 1 1 sa := by
          have hr15 : su.getReg .x15 = BitVec.ofNat 64 ((tailBufBase + (m - (u + 1))) + 1) := by
            rw [hx15u]; congr 1; omega
          rw [hr15, bv64_add_neg1] at ha; exact ha
        have haddr6 : sa.getReg .x15 + signExtend12 (0#12) =
            BitVec.ofNat 64 (tailBufBase + (m - (u + 1))) := by
          change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
        have hb := step_LBU (by omega) (rfl : sa.pc = pcAt 148)
          (rfl : openingInstr 148 = .base (.LBU .x6 .x15 (0#12)))
          (by rw [haddr6]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        set bCur := packed[m - (u + 1)]'(by omega)
        let sb := (sa.setReg .x6 (bCur.zeroExtend 64)).setPC (pcAt 149)
        have hb' : OpenRuns sa 1 1 sb := by
          have hget : sa.getByte (BitVec.ofNat 64 (tailBufBase + (m - (u + 1)))) = bCur :=
            htailu (m - (u + 1)) (by omega)
          simpa only [haddr6, hget, sb] using hb
        have haddr10 : sb.getReg .x10 + signExtend12 (0#12) =
            BitVec.ofNat 64 (11341403200 + fwdBytes.length + u) := by
          have hr10 : sb.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length + u) := hx10u
          rw [hr10, hse0, bv64_ofNat_add, Nat.add_zero]
        have hc := step_SB (by omega) (rfl : sb.pc = pcAt 149)
          (rfl : openingInstr 149 = .base (.SB .x10 .x6 (0#12)))
          (by rw [haddr10]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        let sc := (sb.setByte (BitVec.ofNat 64 (11341403200 + fwdBytes.length + u)) bCur).setPC (pcAt 150)
        have hc' : OpenRuns sb 1 1 sc := by
          have htr : (sb.getReg .x6).truncate 8 = bCur := byte_zeroExtend_truncate8 bCur
          simpa only [haddr10, htr, sc] using hc
        have hd := step_ADDI (by omega) (rfl : sc.pc = pcAt 150)
          (rfl : openingInstr 150 = .base (.ADDI .x10 .x10 (1#12)))
        let sd := (sc.setReg .x10 (BitVec.ofNat 64 (11341403200 + fwdBytes.length + (u + 1)))).setPC (pcAt 151)
        have hd' : OpenRuns sc 1 1 sd := by
          have hr10 : sc.getReg .x10 = BitVec.ofNat 64 (11341403200 + fwdBytes.length + u) := by
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
        have hx26_d : sd.getReg .x26 = BitVec.ofNat 64 11341403200 := by
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
            rw [show 11341403200 + (fwdBytes.length + u) = 11341403200 + fwdBytes.length + u by omega,
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
        by_cases hmore : u + 1 < m
        · have he := step_BNE_taken (by omega) (rfl : sd.pc = pcAt 151)
            (rfl : openingInstr 151 = .base (.BNE .x15 .x31 (8176#13)))
            (by rw [hx15_d, hx31_d]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
            (by decide : pcAt 151 + signExtend13 (8176#13) = pcAt 147)
          exact ⟨sd.setPC (pcAt 147), by simpa only [Nat.mul_succ] using (hru.trans hstep4).trans he,
            by rw [if_pos hmore]; rfl, hx15_d, hx31_d, rfl, hx26_d, hpr_d, htail_d⟩
        · have hdone : m - (u + 1) = 0 := by omega
          have he := step_BNE_not_taken (by omega) (rfl : sd.pc = pcAt 151)
            (rfl : openingInstr 151 = .base (.BNE .x15 .x31 (8176#13)))
            (by rw [hx15_d, hx31_d, hdone, Nat.add_zero])
          exact ⟨sd.setPC (pcAt 152), by simpa only [Nat.mul_succ] using (hru.trans hstep4).trans he,
            by rw [if_neg hmore]; rfl, hx15_d, hx31_d, rfl, hx26_d, hpr_d, htail_d⟩
    obtain ⟨sf, hrf, hpcf, _, _, hx10f, hx26f, hprf, _⟩ := hloop m (Nat.le_refl m)
    have hpcf' : sf.pc = pcAt 152 := by simpa only [Nat.lt_irrefl, ite_false] using hpcf
    have htakeAll : packed.reverse.take m = packed.reverse := by
      rw [show m = packed.reverse.length by simp [m], List.take_length]
    rw [htakeAll] at hprf
    refine ⟨sf, h146.trans hrf, hpcf', ?_, hx26f, hprf⟩
    rw [hx10f]; congr 1; simp [m]; omega

private theorem openRuns_finish {s : MachineState} {proofLen : Nat}
    (hpc : s.pc = pcAt 152)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (11341403200 + proofLen))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 11341403200) :
    ∃ sHalt, OpenRuns s 3 3 sHalt ∧
      sHalt.pc = pcAt 155 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = BitVec.ofNat 64 proofLen ∧
      sHalt.mem = s.mem := by
  have h1 := step_SUB (by omega) hpc (rfl : openingInstr 152 = .base (.SUB .x11 .x10 .x26))
  have hsub : s.getReg .x10 - s.getReg .x26 = BitVec.ofNat 64 proofLen := by
    rw [hx10, hx26, bv64_ofNat_sub _ _ (by omega), Nat.add_sub_cancel_left]
  let s1 := (s.setReg .x11 (BitVec.ofNat 64 proofLen)).setPC (pcAt 153)
  have h1' : OpenRuns s 1 1 s1 := by simpa only [hsub, s1] using h1
  have h2 := step_ADDI (by omega) (rfl : s1.pc = pcAt 153)
    (rfl : openingInstr 153 = .base (.ADDI .x5 .x0 (1#12)))
  let s2 := (s1.setReg .x5 1#64).setPC (pcAt 154)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x0 + signExtend12 (1#12) = 1#64 := by
      change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 154)
    (rfl : openingInstr 154 = .base (.ADDI .x10 .x0 (0#12)))
  let s3 := (s2.setReg .x10 0#64).setPC (pcAt 155)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hv : s2.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s3] using h3
  exact ⟨s3, (h1'.trans h2').trans h3', rfl, rfl, rfl, rfl, rfl⟩

/-! ### 7. Record Loop (`31..97`) -/

private def capLeafNat (i : Nat) : Nat := (i / 3) >>> 13

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

/-- Loop invariant preserved across the record-loop body (`31..97`). -/
private structure RecInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (t : Nat) (fwdBytes : List Byte) (tails : List TailChunk)
    (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475728
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + (rowOff + 72))
  rx19 : s.getReg .x19 = 3#64
  rx20 : s.getReg .x20 = BitVec.ofNat 64 FULL_TRIPLETS
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx24 : s.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * t)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 11341403200
  rx27 : s.getReg .x27 = BitVec.ofNat 64 (positions.card - t)
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  writer : WriterState s fwdBytes
  tail : TailState s tails
  cap14 : ∀ c < 683, s.getByte (BitVec.ofNat 64 (4096 + c)) =
    if capMark14Prefix positions t c then 1#8 else 0#8

private theorem RecInv.setPC {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List TailChunk}
    {s : MachineState} (inv : RecInv trapdoor positions t fwdBytes tails s) (pc : Word) :
    RecInv trapdoor positions t fwdBytes tails (s.setPC pc) :=
  ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
   inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩

private theorem RecInv.after_sub {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes fwdBytes' : List Byte}
    {tails tails' : List TailChunk} {s s' : MachineState}
    (inv : RecInv trapdoor positions t fwdBytes tails s)
    (hreg : ∀ r, r = .x2 ∨ r = .x9 ∨ r = .x18 ∨ r = .x19 ∨ r = .x20 ∨ r = .x21 ∨
      r = .x24 ∨ r = .x26 ∨ r = .x27 → s'.getReg r = s.getReg r)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s')
    (hw : WriterState s' fwdBytes')
    (ht : TailState s' tails')
    (hcap : ∀ q < 5512, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) :
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
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List TailChunk}
    {s : MachineState}
    (ht : t < positions.card) (hpc : s.pc = pcAt 31)
    (hbd : fwdBytes.length + 24 ≤ 8556390424)
    (htbd : tails.length ≤ 210000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let idx : Index := (positions.sort (· ≤ ·))[t]'(by simpa using ht)
    let fwd1 := fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24
    ∃ s1, OpenRuns s 32 32 s1 ∧
      s1.pc = pcAt 43 ∧
      s1.getReg .x8 = BitVec.ofNat 64 idx.val ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro idx fwd1
  have hcard := positions_card_le positions
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hopen : openingIndex positions t = idx.val := by simp only [openingIndex, dif_pos ht]; rfl
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have haddr31 : s.getReg .x24 + signExtend12 (0#12) = BitVec.ofNat 64 (6912218176 + 8 * t) := by
    rw [inv.rx24, hse0, bv64_ofNat_add, Nat.add_zero]
  have h31 := step_LD (by omega) hpc (rfl : openingInstr 31 = .base (.LD .x8 .x24 (0#12)))
    (by rw [haddr31]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s31 := (s.setReg .x8 (BitVec.ofNat 64 idx.val)).setPC (pcAt 32)
  have h31' : OpenRuns s 1 1 s31 := by
    have hmem := readOnly_getMem_index inv.ro t ht
    rw [hopen] at hmem
    simpa only [haddr31, hmem, s31] using h31
  have h32 := step_SRLI (by omega) (rfl : s31.pc = pcAt 32)
    (rfl : openingInstr 32 = .base (.SRLI .x6 .x8 (1#6)))
  let s32 := (s31.setReg .x6 (BitVec.ofNat 64 (idx.val / 2))).setPC (pcAt 33)
  have h32' : OpenRuns s31 1 1 s32 := by
    have hv : s31.getReg .x8 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (idx.val / 2) := by
      change BitVec.ofNat 64 idx.val >>> 1 = _
      rw [bv64_ushr idx.val 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s32] using h32
  have h33 := step_SLLI (by omega) (rfl : s32.pc = pcAt 33)
    (rfl : openingInstr 33 = .base (.SLLI .x7 .x6 (7#6)))
  let s33 := (s32.setReg .x7 (BitVec.ofNat 64 (128 * (idx.val / 2)))).setPC (pcAt 34)
  have h33' : OpenRuns s32 1 1 s33 := by
    have hv : s32.getReg .x6 <<< (7#6 : BitVec 6).toNat = BitVec.ofNat 64 (128 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (idx.val / 2) <<< 7 = _; rw [bv64_shl]; congr 1; omega
    simpa only [hv, s33] using h33
  have h34 := step_SLLI (by omega) (rfl : s33.pc = pcAt 34)
    (rfl : openingInstr 34 = .base (.SLLI .x10 .x6 (6#6)))
  let s34 := (s33.setReg .x10 (BitVec.ofNat 64 (64 * (idx.val / 2)))).setPC (pcAt 35)
  have h34' : OpenRuns s33 1 1 s34 := by
    have hv : s33.getReg .x6 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (idx.val / 2) <<< 6 = _; rw [bv64_shl]; congr 1; omega
    simpa only [hv, s34] using h34
  have h35 := step_ADD (by omega) (rfl : s34.pc = pcAt 35)
    (rfl : openingInstr 35 = .base (.ADD .x7 .x7 .x10))
  let s35 := (s34.setReg .x7 (BitVec.ofNat 64 (192 * (idx.val / 2)))).setPC (pcAt 36)
  have h35' : OpenRuns s34 1 1 s35 := by
    have hv : s34.getReg .x7 + s34.getReg .x10 = BitVec.ofNat 64 (192 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (128 * (idx.val / 2)) + BitVec.ofNat 64 (64 * (idx.val / 2)) = _
      rw [bv64_ofNat_add]; congr 1; omega
    simpa only [hv, s35] using h35
  have h36 := step_SLLI (by omega) (rfl : s35.pc = pcAt 36)
    (rfl : openingInstr 36 = .base (.SLLI .x10 .x6 (3#6)))
  let s36 := (s35.setReg .x10 (BitVec.ofNat 64 (8 * (idx.val / 2)))).setPC (pcAt 37)
  have h36' : OpenRuns s35 1 1 s36 := by
    have hv : s35.getReg .x6 <<< (3#6 : BitVec 6).toNat = BitVec.ofNat 64 (8 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (idx.val / 2) <<< 3 = _; rw [bv64_shl]; congr 1; omega
    simpa only [hv, s36] using h36
  have h37 := step_SUB (by omega) (rfl : s36.pc = pcAt 37)
    (rfl : openingInstr 37 = .base (.SUB .x7 .x7 .x10))
  let s37 := (s36.setReg .x7 (BitVec.ofNat 64 (184 * (idx.val / 2)))).setPC (pcAt 38)
  have h37' : OpenRuns s36 1 1 s37 := by
    have hv : s36.getReg .x7 - s36.getReg .x10 = BitVec.ofNat 64 (184 * (idx.val / 2)) := by
      change BitVec.ofNat 64 (192 * (idx.val / 2)) - BitVec.ofNat 64 (8 * (idx.val / 2)) = _
      rw [bv64_ofNat_sub _ _ (by omega)]; congr 1; omega
    simpa only [hv, s37] using h37
  have h38 := step_ANDI (by omega) (rfl : s37.pc = pcAt 38)
    (rfl : openingInstr 38 = .base (.ANDI .x6 .x8 (1#12)))
  let s38 := (s37.setReg .x6 (BitVec.ofNat 64 (idx.val % 2))).setPC (pcAt 39)
  have h38' : OpenRuns s37 1 1 s38 := by
    have hv : s37.getReg .x8 &&& signExtend12 (1#12) = BitVec.ofNat 64 (idx.val % 2) := by
      change BitVec.ofNat 64 idx.val &&& signExtend12 (1#12) = _
      exact bv64_and1 idx.val (by omega)
    simpa only [hv, s38] using h38
  have h39 := step_SLLI (by omega) (rfl : s38.pc = pcAt 39)
    (rfl : openingInstr 39 = .base (.SLLI .x6 .x6 (4#6)))
  let s39 := (s38.setReg .x6 (BitVec.ofNat 64 (16 * (idx.val % 2)))).setPC (pcAt 40)
  have h39' : OpenRuns s38 1 1 s39 := by
    have hv : s38.getReg .x6 <<< (4#6 : BitVec 6).toNat = BitVec.ofNat 64 (16 * (idx.val % 2)) := by
      change BitVec.ofNat 64 (idx.val % 2) <<< 4 = _; rw [bv64_shl]; congr 1; omega
    simpa only [hv, s39] using h39
  have h40 := step_ADD (by omega) (rfl : s39.pc = pcAt 40)
    (rfl : openingInstr 40 = .base (.ADD .x7 .x7 .x6))
  let s40 := (s39.setReg .x7 (BitVec.ofNat 64 (184 * (idx.val / 2) + 16 * (idx.val % 2)))).setPC (pcAt 41)
  have h40' : OpenRuns s39 1 1 s40 := by
    have hv : s39.getReg .x7 + s39.getReg .x6 =
        BitVec.ofNat 64 (184 * (idx.val / 2) + 16 * (idx.val % 2)) := by
      change BitVec.ofNat 64 (184 * (idx.val / 2)) + BitVec.ofNat 64 (16 * (idx.val % 2)) = _
      exact bv64_ofNat_add _ _
    simpa only [hv, s40] using h40
  have h41 := step_ADD (by omega) (rfl : s40.pc = pcAt 41)
    (rfl : openingInstr 41 = .base (.ADD .x10 .x18 .x7))
  let s41 := (s40.setReg .x10 (BitVec.ofNat 64 (4294971424 + saltOff idx))).setPC (pcAt 42)
  have h41' : OpenRuns s40 1 1 s41 := by
    have hr18 : s40.getReg .x18 = BitVec.ofNat 64 (4294971424 + (rowOff + 72)) := inv.rx18
    have hr7 : s40.getReg .x7 = BitVec.ofNat 64 (184 * (idx.val / 2) + 16 * (idx.val % 2)) := rfl
    have hsum : s40.getReg .x18 + s40.getReg .x7 = BitVec.ofNat 64 (4294971424 + saltOff idx) := by
      rw [hr18, hr7, bv64_ofNat_add, Nat.add_assoc, saltOff_formula idx]
    simpa only [hsum, s41] using h41
  have hinv41 : RecInv trapdoor positions t fwdBytes tails s41 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  have hsalt_bd : saltOff idx + 24 ≤ 2617246752 := by
    have h := saltOff_add_24_le idx
    rw [trapdoorBytes_eq] at h
    exact h
  obtain ⟨s43, hrcopy, hpc43, hreg43, hro43, hw43, ht43, hcap43⟩ :=
    openRuns_call_copy24 (callIdx := 42) (srcOff := saltOff idx) (jOff := 472#21)
      (fwdBytes := fwdBytes) (chunk := bitsToBytes (tdSalt trapdoor idx) 24) (tails := tails)
      (by omega) rfl (by decide) rfl rfl (saltOff_align8 idx) hsalt_bd hbd htbd
      hinv41.ro hinv41.writer hinv41.tail (bitsToBytes_length _ 24)
      (fun j hj => chunk_tdSalt trapdoor idx j hj)
  have hpre1 : OpenRuns s 6 6 s36 := ((((h31'.trans h32').trans h33').trans h34').trans h35').trans h36'
  have hpre2 : OpenRuns s36 5 5 s41 := (((h37'.trans h38').trans h39').trans h40').trans h41'
  refine ⟨s43, (hpre1.trans hpre2).trans hrcopy, hpc43, ?_, ?_⟩
  · rw [hreg43 .x8 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  · exact hinv41.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg43 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      hro43 hw43 ht43 hcap43

/-- Two consecutive `emit32` calls from `x28 + 32*k1`, `x28 + 32*k2` into the proof writer. -/
private theorem openRuns_l0_pair {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g k1 k2 a b c1 c2 : Nat} {j1 j2 : BitVec 21} {imm1 imm2 : BitVec 12}
    {fwdBytes : List Byte} {tails : List TailChunk} {s : MachineState}
    (hg : g < FULL_TRIPLETS) (hc1 : c1 + 4 < 262) (hc2 : c2 = c1 + 2)
    (hk1 : k1 < 3) (hk2 : k2 < 3)
    (ha : a = 3 * g + k1) (hb : b = 3 * g + k2)
    (hse1 : signExtend12 imm1 = BitVec.ofNat 64 (32 * k1))
    (hse2 : signExtend12 imm2 = BitVec.ofNat 64 (32 * k2))
    (hi0 : openingInstr c1 = .base (.ADDI .x10 .x28 imm1))
    (hi1 : openingInstr (c1 + 1) = .base (.JAL .x1 j1))
    (htgt1 : pcAt (c1 + 1) + signExtend21 j1 = pcAt 180)
    (hi2 : openingInstr c2 = .base (.ADDI .x10 .x28 imm2))
    (hi3 : openingInstr (c2 + 1) = .base (.JAL .x1 j2))
    (htgt2 : pcAt (c2 + 1) + signExtend21 j2 = pcAt 180)
    (hpc : s.pc = pcAt c1)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 g)
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 (4294971424 + 96 * g))
    (hbd_extra : fwdBytes.length + 64 ≤ 8556390424)
    (htbd : tails.length ≤ 210000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let chunk := bitsToBytes (tdNode trapdoor 0 a) 32 ++ bitsToBytes (tdNode trapdoor 0 b) 32
    ∃ s', OpenRuns s 56 56 s' ∧
      s'.pc = pcAt (c2 + 2) ∧
      s'.getReg .x22 = BitVec.ofNat 64 g ∧
      RecInv trapdoor positions t (fwdBytes ++ chunk) tails s' := by
  intro chunk
  have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
  have hls0 : levelSize 0 = 16777216 := levelSize_0
  have ha_lt : a < levelSize 0 := by omega
  have hb_lt : b < levelSize 0 := by omega
  have htb : treeBytes = 1073742880 := treeBytes_eq
  have hno_a : levelBase 0 + nodeOffset 0 a = 96 * g + 32 * k1 := by
    change 0 + 32 * a = _; omega
  have hno_b : levelBase 0 + nodeOffset 0 b = 96 * g + 32 * k2 := by
    change 0 + 32 * b = _; omega
  have ha_bd : levelBase 0 + nodeOffset 0 a + 32 ≤ 2617246752 := by
    have := nodeOffset_lt_treeBytes 0 a (by omega) ha_lt; omega
  have hb_bd : levelBase 0 + nodeOffset 0 b + 32 ≤ 2617246752 := by
    have := nodeOffset_lt_treeBytes 0 b (by omega) hb_lt; omega
  have hstep1 := step_ADDI (by omega) hpc hi0
  let s1 := (s.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase 0 + nodeOffset 0 a)))).setPC
    (pcAt (c1 + 1))
  have hstep1' : OpenRuns s 1 1 s1 := by
    have hsum : s.getReg .x28 + signExtend12 imm1 =
        BitVec.ofNat 64 (4294971424 + (levelBase 0 + nodeOffset 0 a)) := by
      rw [hx28, hse1, bv64_ofNat_add]; congr 1; omega
    simpa only [hsum, s1] using hstep1
  have hinv1 : RecInv trapdoor positions t fwdBytes tails s1 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  obtain ⟨s2, hrc1, hpc2, hreg2, hro2, hw2, ht2, hcap2⟩ :=
    openRuns_call_copy32 (callIdx := c1 + 1) (srcOff := levelBase 0 + nodeOffset 0 a) (jOff := j1)
      (fwdBytes := fwdBytes) (chunk := bitsToBytes (tdNode trapdoor 0 a) 32) (tails := tails)
      (by omega) hi1 htgt1 rfl rfl
      (by have := nodeOffset_align8 0 a; change (0 + nodeOffset 0 a) % 8 = 0; omega) ha_bd
      (by omega) htbd hinv1.ro hinv1.writer hinv1.tail (bitsToBytes_length _ 32)
      (fun j hj => chunk_tdNode trapdoor 0 a 32 j (by omega) hj)
  have hinv2 : RecInv trapdoor positions t (fwdBytes ++ bitsToBytes (tdNode trapdoor 0 a) 32) tails s2 :=
    hinv1.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg2 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      hro2 hw2 ht2 hcap2
  have hpc2' : s2.pc = pcAt c2 := by rw [hpc2]; congr 1; omega
  have hx28_2 : s2.getReg .x28 = BitVec.ofNat 64 (4294971424 + 96 * g) := by
    rw [hreg2 .x28 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx28
  have hx22_2 : s2.getReg .x22 = BitVec.ofNat 64 g := by
    rw [hreg2 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx22
  have hstep2 := step_ADDI (by omega) hpc2' hi2
  let s3 := (s2.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase 0 + nodeOffset 0 b)))).setPC
    (pcAt (c2 + 1))
  have hstep2' : OpenRuns s2 1 1 s3 := by
    have hsum : s2.getReg .x28 + signExtend12 imm2 =
        BitVec.ofNat 64 (4294971424 + (levelBase 0 + nodeOffset 0 b)) := by
      rw [hx28_2, hse2, bv64_ofNat_add]; congr 1; omega
    simpa only [hsum, s3] using hstep2
  have hinv3 : RecInv trapdoor positions t (fwdBytes ++ bitsToBytes (tdNode trapdoor 0 a) 32) tails s3 :=
    ⟨hinv2.rx2, hinv2.rx9, hinv2.rx18, hinv2.rx19, hinv2.rx20, hinv2.rx21, hinv2.rx24, hinv2.rx26,
     hinv2.rx27, hinv2.ro, hinv2.writer.of_eq, hinv2.tail.of_eq, hinv2.cap14⟩
  obtain ⟨s4, hrc2, hpc4, hreg4, hro4, hw4, ht4, hcap4⟩ :=
    openRuns_call_copy32 (callIdx := c2 + 1) (srcOff := levelBase 0 + nodeOffset 0 b) (jOff := j2)
      (fwdBytes := fwdBytes ++ bitsToBytes (tdNode trapdoor 0 a) 32)
      (chunk := bitsToBytes (tdNode trapdoor 0 b) 32) (tails := tails)
      (by omega) hi3 htgt2 rfl rfl
      (by have := nodeOffset_align8 0 b; change (0 + nodeOffset 0 b) % 8 = 0; omega) hb_bd
      (by simp only [List.length_append, bitsToBytes_length]; omega) htbd
      hinv3.ro hinv3.writer hinv3.tail (bitsToBytes_length _ 32)
      (fun j hj => chunk_tdNode trapdoor 0 b 32 j (by omega) hj)
  have hinv4 := hinv3.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg4 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      hro4 hw4 ht4 hcap4
  have happ : (fwdBytes ++ bitsToBytes (tdNode trapdoor 0 a) 32) ++ bitsToBytes (tdNode trapdoor 0 b) 32 =
      fwdBytes ++ chunk := List.append_assoc _ _ _
  rw [happ] at hinv4
  refine ⟨s4, ((hstep1'.trans hrc1).trans hstep2').trans hrc2, hpc4, ?_, hinv4⟩
  rw [hreg4 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx22_2

private theorem openRuns_rec_l0 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List TailChunk}
    {s : MachineState}
    (hpc : s.pc = pcAt 43)
    (idx : Index) (hx8 : s.getReg .x8 = BitVec.ofNat 64 idx.val)
    (hbd_extra : fwdBytes.length + 64 ≤ 8556390424)
    (htbd : tails.length ≤ 210000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ l0SiblingsProof (tdNode trapdoor) idx
    ∃ steps cycles s1, OpenRuns s steps cycles s1 ∧
      steps ≤ 67 ∧ cycles ≤ 73 ∧
      s1.pc = pcAt 67 ∧
      s1.getReg .x22 = BitVec.ofNat 64 (idx.val / 3) ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
  set g := idx.val / 3
  set r := idx.val % 3
  have hdiv := step_DIVU (by omega) hpc (rfl : openingInstr 43 = .base (.DIVU .x22 .x8 .x19))
  let s44 := (s.setReg .x22 (BitVec.ofNat 64 g)).setPC (pcAt 44)
  have hdiv' : OpenRuns s 1 4 s44 := by
    have hv : rv64_divu (s.getReg .x8) (s.getReg .x19) = BitVec.ofNat 64 g := by
      rw [hx8, inv.rx19, rv64_divu_three, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : idx.val < 2 ^ 64)]
    simpa only [hv, s44] using hdiv
  have hrem := step_REMU (by omega) (rfl : s44.pc = pcAt 44)
    (rfl : openingInstr 44 = .base (.REMU .x23 .x8 .x19))
  let s45 := (s44.setReg .x23 (BitVec.ofNat 64 r)).setPC (pcAt 45)
  have hrem' : OpenRuns s44 1 4 s45 := by
    have hv : rv64_remu (s44.getReg .x8) (s44.getReg .x19) = BitVec.ofNat 64 r := by
      have hr8 : s44.getReg .x8 = BitVec.ofNat 64 idx.val := hx8
      have hr19 : s44.getReg .x19 = 3#64 := inv.rx19
      rw [hr8, hr19, rv64_remu_three, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : idx.val < 2 ^ 64)]
    simpa only [hv, s45] using hrem
  have hinv45 : RecInv trapdoor positions t fwdBytes tails s45 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  by_cases hg : g = FULL_TRIPLETS
  · have hbeq := step_BEQ_taken (by omega) (rfl : s45.pc = pcAt 45)
      (rfl : openingInstr 45 = .base (.BEQ .x22 .x20 (88#13)))
      (by change BitVec.ofNat 64 g = s.getReg .x20; rw [hg, inv.rx20])
      (by decide : pcAt 45 + signExtend13 (88#13) = pcAt 67)
    have hfwd1 : fwd1 = fwdBytes := by
      change fwdBytes ++ (if g = FULL_TRIPLETS then [] else _) = fwdBytes
      rw [if_pos hg, List.append_nil]
    rw [hfwd1]
    exact ⟨3, 9, s45.setPC (pcAt 67), (hdiv'.trans hrem').trans hbeq, by omega, by omega,
      rfl, rfl, hinv45.setPC (pcAt 67)⟩
  · have hg_lt : g < FULL_TRIPLETS := by omega
    have hbeq := step_BEQ_not_taken (by omega) (rfl : s45.pc = pcAt 45)
      (rfl : openingInstr 45 = .base (.BEQ .x22 .x20 (88#13)))
      (by change BitVec.ofNat 64 g ≠ s.getReg .x20; rw [inv.rx20]
          exact bv64_ofNat_ne (by omega) (by omega) hg)
    let s46 := s45.setPC (pcAt 46)
    have h46 := step_SLLI (by omega) (rfl : s46.pc = pcAt 46)
      (rfl : openingInstr 46 = .base (.SLLI .x6 .x22 (6#6)))
    let s47 := (s46.setReg .x6 (BitVec.ofNat 64 (64 * g))).setPC (pcAt 47)
    have h46' : OpenRuns s46 1 1 s47 := by
      have hv : s46.getReg .x22 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * g) := by
        change BitVec.ofNat 64 g <<< 6 = _; rw [bv64_shl]; congr 1; omega
      simpa only [hv, s47] using h46
    have h47 := step_SLLI (by omega) (rfl : s47.pc = pcAt 47)
      (rfl : openingInstr 47 = .base (.SLLI .x7 .x22 (5#6)))
    let s48 := (s47.setReg .x7 (BitVec.ofNat 64 (32 * g))).setPC (pcAt 48)
    have h47' : OpenRuns s47 1 1 s48 := by
      have hv : s47.getReg .x22 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (32 * g) := by
        change BitVec.ofNat 64 g <<< 5 = _; rw [bv64_shl]; congr 1; omega
      simpa only [hv, s48] using h47
    have h48 := step_ADD (by omega) (rfl : s48.pc = pcAt 48)
      (rfl : openingInstr 48 = .base (.ADD .x28 .x6 .x7))
    let s49 := (s48.setReg .x28 (BitVec.ofNat 64 (96 * g))).setPC (pcAt 49)
    have h48' : OpenRuns s48 1 1 s49 := by
      have hv : s48.getReg .x6 + s48.getReg .x7 = BitVec.ofNat 64 (96 * g) := by
        change BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 (32 * g) = _
        rw [bv64_ofNat_add]; congr 1; omega
      simpa only [hv, s49] using h48
    have h49 := step_ADD (by omega) (rfl : s49.pc = pcAt 49)
      (rfl : openingInstr 49 = .base (.ADD .x28 .x9 .x28))
    let s50 := (s49.setReg .x28 (BitVec.ofNat 64 (4294971424 + 96 * g))).setPC (pcAt 50)
    have h49' : OpenRuns s49 1 1 s50 := by
      have hr9 : s49.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
      have hv : s49.getReg .x9 + s49.getReg .x28 = BitVec.ofNat 64 (4294971424 + 96 * g) := by
        rw [hr9]; change BitVec.ofNat 64 4294971424 + BitVec.ofNat 64 (96 * g) = _
        exact bv64_ofNat_add _ _
      simpa only [hv, s50] using h49
    have hpre : OpenRuns s 7 13 s50 :=
      (((((hdiv'.trans hrem').trans hbeq).trans h46').trans h47').trans h48').trans h49'
    have hinv50 : RecInv trapdoor positions t fwdBytes tails s50 :=
      ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
       inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
    by_cases hr0 : r = 0
    · have h50 := step_BEQ_taken (by omega) (rfl : s50.pc = pcAt 50)
        (rfl : openingInstr 50 = .base (.BEQ .x23 .x0 (32#13)))
        (by change BitVec.ofNat 64 r = 0#64; rw [hr0])
        (by decide : pcAt 50 + signExtend13 (32#13) = pcAt 58)
      obtain ⟨s62, hrpair, hpc62, hx22_62, inv62⟩ :=
        openRuns_l0_pair (c1 := 58) (c2 := 60) (j1 := 484#21) (j2 := 476#21)
          (imm1 := 32#12) (imm2 := 64#12) (k1 := 1) (k2 := 2) (a := 3 * g + 1) (b := 3 * g + 2)
          hg_lt (by omega) rfl (by omega) (by omega) rfl rfl (by decide) (by decide)
          rfl rfl (by decide) rfl rfl (by decide)
          rfl rfl rfl hbd_extra htbd (hinv50.setPC (pcAt 58))
      have h62 := step_JAL (by omega) hpc62 (rfl : openingInstr 62 = .base (.JAL .x0 (20#21)))
        (by decide : pcAt 62 + signExtend21 (20#21) = pcAt 67)
      have hfwd1 : fwd1 = fwdBytes ++ (bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32 ++
          bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32) := by
        change fwdBytes ++ (if g = FULL_TRIPLETS then [] else
          if r = 0 then bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32 ++
            bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32
          else _) = _
        rw [if_neg hg, if_pos hr0]
      rw [hfwd1]
      exact ⟨65, 71, (s62.setReg .x0 (pcAt 63)).setPC (pcAt 67),
        ((hpre.trans h50).trans hrpair).trans h62, by omega, by omega,
        rfl, hx22_62, inv62.setPC (pcAt 67)⟩
    · have h50 := step_BEQ_not_taken (by omega) (rfl : s50.pc = pcAt 50)
        (rfl : openingInstr 50 = .base (.BEQ .x23 .x0 (32#13)))
        (by change BitVec.ofNat 64 r ≠ BitVec.ofNat 64 0; exact bv64_ofNat_ne (by omega) (by decide) hr0)
      let s51 := s50.setPC (pcAt 51)
      have h51 := step_ADDI (by omega) (rfl : s51.pc = pcAt 51)
        (rfl : openingInstr 51 = .base (.ADDI .x7 .x0 (1#12)))
      let s52 := (s51.setReg .x7 (BitVec.ofNat 64 1)).setPC (pcAt 52)
      have h51' : OpenRuns s51 1 1 s52 := by
        have hv : s51.getReg .x0 + signExtend12 (1#12) = BitVec.ofNat 64 1 := by
          change (0#64 : Word) + signExtend12 (1#12) = BitVec.ofNat 64 1; decide
        simpa only [hv, s52] using h51
      have hinv52 : RecInv trapdoor positions t fwdBytes tails s52 :=
        ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
         inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
      by_cases hr1 : r = 1
      · have h52 := step_BEQ_taken (by omega) (rfl : s52.pc = pcAt 52)
          (rfl : openingInstr 52 = .base (.BEQ .x23 .x7 (44#13)))
          (by change BitVec.ofNat 64 r = BitVec.ofNat 64 1; rw [hr1])
          (by decide : pcAt 52 + signExtend13 (44#13) = pcAt 63)
        obtain ⟨s67, hrpair, hpc67, hx22_67, inv67⟩ :=
          openRuns_l0_pair (c1 := 63) (c2 := 65) (j1 := 464#21) (j2 := 456#21)
            (imm1 := 0#12) (imm2 := 64#12) (k1 := 0) (k2 := 2) (a := 3 * g) (b := 3 * g + 2)
            hg_lt (by omega) rfl (by omega) (by omega) (by omega) rfl (by decide) (by decide)
            rfl rfl (by decide) rfl rfl (by decide)
            rfl rfl rfl hbd_extra htbd (hinv52.setPC (pcAt 63))
        have hfwd1 : fwd1 = fwdBytes ++ (bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
            bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32) := by
          change fwdBytes ++ (if g = FULL_TRIPLETS then [] else
            if r = 0 then _ else
            if r = 1 then bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
              bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32
            else _) = _
          rw [if_neg hg, if_neg hr0, if_pos hr1]
        rw [hfwd1]
        exact ⟨66, 72, s67, (((hpre.trans h50).trans h51').trans h52).trans hrpair,
          by omega, by omega, hpc67, hx22_67, inv67⟩
      · have h52 := step_BEQ_not_taken (by omega) (rfl : s52.pc = pcAt 52)
          (rfl : openingInstr 52 = .base (.BEQ .x23 .x7 (44#13)))
          (by change BitVec.ofNat 64 r ≠ BitVec.ofNat 64 1; exact bv64_ofNat_ne (by omega) (by decide) hr1)
        obtain ⟨s57, hrpair, hpc57, hx22_57, inv57⟩ :=
          openRuns_l0_pair (c1 := 53) (c2 := 55) (j1 := 504#21) (j2 := 496#21)
            (imm1 := 0#12) (imm2 := 32#12) (k1 := 0) (k2 := 1) (a := 3 * g) (b := 3 * g + 1)
            hg_lt (by omega) rfl (by omega) (by omega) (by omega) rfl (by decide) (by decide)
            rfl rfl (by decide) rfl rfl (by decide)
            rfl rfl rfl hbd_extra htbd (hinv52.setPC (pcAt 53))
        have h57 := step_JAL (by omega) hpc57 (rfl : openingInstr 57 = .base (.JAL .x0 (40#21)))
          (by decide : pcAt 57 + signExtend21 (40#21) = pcAt 67)
        have hfwd1 : fwd1 = fwdBytes ++ (bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
            bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32) := by
          change fwdBytes ++ (if g = FULL_TRIPLETS then [] else
            if r = 0 then _ else
            if r = 1 then _ else
            bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
              bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32) = _
          rw [if_neg hg, if_neg hr0, if_neg hr1]
        rw [hfwd1]
        exact ⟨67, 73, (s57.setReg .x0 (pcAt 58)).setPC (pcAt 67),
          ((((hpre.trans h50).trans h51').trans h52).trans hrpair).trans h57,
          by omega, by omega, rfl, hx22_57, inv57.setPC (pcAt 67)⟩

private theorem openRuns_rec_l1 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g : Nat} {fwdBytes : List Byte} {tails : List TailChunk}
    {s : MachineState}
    (hg : g ≤ FULL_TRIPLETS) (hpc : s.pc = pcAt 67)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 g)
    (hbd : fwdBytes.length + 32 ≤ 8556390424)
    (htbd : tails.length ≤ 210000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ bitsToBytes (tdNode trapdoor 1 (g ^^^ 1)) 32
    ∃ s1, OpenRuns s 34 34 s1 ∧
      s1.pc = pcAt 75 ∧
      s1.getReg .x22 = BitVec.ofNat 64 g ∧
      RecInv trapdoor positions t fwd1 tails s1 := by
  intro fwd1
  have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
  have hls1 : levelSize 1 = 5592406 := levelSize_1
  set sib := g ^^^ 1
  have hsib_lt : sib < levelSize 1 := by
    rw [hls1]
    exact xor_one_lt_even (m := 2796203) (by omega)
  have h67 := step_XORI (by omega) hpc (rfl : openingInstr 67 = .base (.XORI .x28 .x22 (1#12)))
  let s68 := (s.setReg .x28 (BitVec.ofNat 64 sib)).setPC (pcAt 68)
  have h67' : OpenRuns s 1 1 s68 := by
    rw [hx22, bv64_xor1 g (by omega)] at h67; exact h67
  have h68 := step_SRLI (by omega) (rfl : s68.pc = pcAt 68)
    (rfl : openingInstr 68 = .base (.SRLI .x6 .x28 (1#6)))
  let s69 := (s68.setReg .x6 (BitVec.ofNat 64 (sib / 2))).setPC (pcAt 69)
  have h68' : OpenRuns s68 1 1 s69 := by
    have hv : s68.getReg .x28 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (sib / 2) := by
      change BitVec.ofNat 64 sib >>> 1 = _
      rw [bv64_ushr sib 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s69] using h68
  have h69 := step_ADD (by omega) (rfl : s69.pc = pcAt 69)
    (rfl : openingInstr 69 = .base (.ADD .x28 .x28 .x6))
  let s70 := (s69.setReg .x28 (BitVec.ofNat 64 (sib + sib / 2))).setPC (pcAt 70)
  have h69' : OpenRuns s69 1 1 s70 := by
    have hv : s69.getReg .x28 + s69.getReg .x6 = BitVec.ofNat 64 (sib + sib / 2) := by
      change BitVec.ofNat 64 sib + BitVec.ofNat 64 (sib / 2) = _
      exact bv64_ofNat_add _ _
    simpa only [hv, s70] using h69
  have h70 := step_SLLI (by omega) (rfl : s70.pc = pcAt 70)
    (rfl : openingInstr 70 = .base (.SLLI .x28 .x28 (5#6)))
  let s71 := (s70.setReg .x28 (BitVec.ofNat 64 (nodeOffset 1 sib))).setPC (pcAt 71)
  have h70' : OpenRuns s70 1 1 s71 := by
    have hv : s70.getReg .x28 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (nodeOffset 1 sib) := by
      change BitVec.ofNat 64 (sib + sib / 2) <<< 5 = _
      rw [bv64_shl]; congr 1
      change (sib + sib / 2) * 32 = gapOffset sib
      unfold gapOffset; omega
    simpa only [hv, s71] using h70
  have hse40 : signExtend12 (40#12) = BitVec.ofNat 64 40 := by decide
  have haddr71 : s71.getReg .x2 + signExtend12 (40#12) = BitVec.ofNat 64 (68719475728 + 40 * 1) := by
    have hr2 : s71.getReg .x2 = BitVec.ofNat 64 68719475728 := inv.rx2
    rw [hr2, hse40, bv64_ofNat_add]
  have h71 := step_LD (by omega) (rfl : s71.pc = pcAt 71)
    (rfl : openingInstr 71 = .base (.LD .x6 .x2 (40#12)))
    (by rw [haddr71]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s72 := (s71.setReg .x6 (BitVec.ofNat 64 (levelBase 1))).setPC (pcAt 72)
  have h71' : OpenRuns s71 1 1 s72 := by
    have hmem : s71.getMem (BitVec.ofNat 64 (68719475728 + 40 * 1)) = BitVec.ofNat 64 (levelBase 1) :=
      readOnly_getMem_data_base inv.ro 1 (by omega)
    simpa only [haddr71, hmem, s72] using h71
  have h72 := step_ADD (by omega) (rfl : s72.pc = pcAt 72)
    (rfl : openingInstr 72 = .base (.ADD .x10 .x9 .x6))
  let s73 := (s72.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase 1))).setPC (pcAt 73)
  have h72' : OpenRuns s72 1 1 s73 := by
    have hr9 : s72.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
    rw [hr9] at h72
    simpa only [show s72.getReg .x6 = BitVec.ofNat 64 (levelBase 1) from rfl, bv64_ofNat_add, s73] using h72
  have h73 := step_ADD (by omega) (rfl : s73.pc = pcAt 73)
    (rfl : openingInstr 73 = .base (.ADD .x10 .x10 .x28))
  let s74 := (s73.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase 1 + nodeOffset 1 sib)))).setPC
    (pcAt 74)
  have h73' : OpenRuns s73 1 1 s74 := by
    have hv : s73.getReg .x10 + s73.getReg .x28 =
        BitVec.ofNat 64 (4294971424 + (levelBase 1 + nodeOffset 1 sib)) := by
      change BitVec.ofNat 64 (4294971424 + levelBase 1) + BitVec.ofNat 64 (nodeOffset 1 sib) = _
      rw [bv64_ofNat_add, Nat.add_assoc]
    simpa only [hv, s74] using h73
  have hinv74 : RecInv trapdoor positions t fwdBytes tails s74 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  have htb : treeBytes = 1073742880 := treeBytes_eq
  have hno_bd : levelBase 1 + nodeOffset 1 sib + 32 ≤ 2617246752 := by
    have := nodeOffset_lt_treeBytes 1 sib (by omega) hsib_lt; omega
  obtain ⟨s75, hrcopy, hpc75, hreg75, hro75, hw75, ht75, hcap75⟩ :=
    openRuns_call_copy32 (callIdx := 74) (srcOff := levelBase 1 + nodeOffset 1 sib) (jOff := 424#21)
      (fwdBytes := fwdBytes) (chunk := bitsToBytes (tdNode trapdoor 1 sib) 32) (tails := tails)
      (by omega) rfl (by decide) rfl rfl
      (by have h1 := levelBase_align8 1 (by omega); have h2 := nodeOffset_align8 1 sib; omega) hno_bd
      hbd htbd hinv74.ro hinv74.writer hinv74.tail (bitsToBytes_length _ 32)
      (fun j hj => chunk_tdNode trapdoor 1 sib 32 j (by omega) hj)
  have htot := ((((((h67'.trans h68').trans h69').trans h70').trans h71').trans h72').trans h73').trans hrcopy
  refine ⟨s75, htot, hpc75, ?_,
    hinv74.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg75 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      hro75 hw75 ht75 hcap75⟩
  rw [hreg75 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx22

private def binStepFwd (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (g step : Nat) :
    List Byte :=
  let l := 2 + step
  let sib := (g >>> (step + 1)) ^^^ 1
  if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) (levelBodyBytes l) else []

private def binStepTails (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (g step : Nat) :
    List TailChunk :=
  let l := 2 + step
  let sib := (g >>> (step + 1)) ^^^ 1
  if sib < levelSize l then [tailChunkOf l (tdNode trapdoor l sib)] else []

private theorem openRuns_rec_bin_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g step : Nat} {fwdBytes : List Byte} {tails : List TailChunk}
    {s : MachineState}
    (hg : g ≤ FULL_TRIPLETS) (hstep : step < 12) (hpc : s.pc = pcAt 77)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (g >>> step))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14))
    (hbd : fwdBytes.length + 30 ≤ 8556390424)
    (htbd : tails.length < 210000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ binStepFwd trapdoor g step
    let tails1 := tails ++ binStepTails trapdoor g step
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 70 ∧
      s1.pc = (if step + 1 < 12 then pcAt 77 else pcAt 91) ∧
      s1.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + (step + 1))) ∧
      s1.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14) ∧
      fwd1.length ≤ fwdBytes.length + 30 ∧
      tails1.length ≤ tails.length + 1 ∧
      RecInv trapdoor positions t fwd1 tails1 s1 := by
  intro fwd1 tails1
  have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
  have hgs_le : g >>> step ≤ g := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  have hgs1_le : g >>> (step + 1) ≤ g := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  set l := 2 + step
  set idx := g >>> (step + 1)
  set sib := idx ^^^ 1
  have hbr := levelBodyBytes_range l (by omega) (by omega)
  have hsib_lt64 : sib < 2 ^ 64 := by
    rcases Nat.even_or_odd' idx with ⟨q, hq | hq⟩
    · rw [show sib = (2 * q) ^^^ 1 from by rw [← hq], xor_one_even]; omega
    · rw [show sib = (2 * q + 1) ^^^ 1 from by rw [← hq], xor_one_odd]; omega
  have hls_le := levelSize_le_max l (by omega)
  have h77 := step_SRLI (by omega) hpc (rfl : openingInstr 77 = .base (.SRLI .x22 .x22 (1#6)))
  let s78 := (s.setReg .x22 (BitVec.ofNat 64 idx)).setPC (pcAt 78)
  have h77' : OpenRuns s 1 1 s78 := by
    have hv : s.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 idx := by
      rw [hx22]; change BitVec.ofNat 64 (g >>> step) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), nat_ushr_ushr1]
    simpa only [hv, s78] using h77
  have h78 := step_XORI (by omega) (rfl : s78.pc = pcAt 78)
    (rfl : openingInstr 78 = .base (.XORI .x28 .x22 (1#12)))
  let s79 := (s78.setReg .x28 (BitVec.ofNat 64 sib)).setPC (pcAt 79)
  have h78' : OpenRuns s78 1 1 s79 := by
    have hv : s78.getReg .x22 ^^^ signExtend12 (1#12) = BitVec.ofNat 64 sib :=
      bv64_xor1 idx (by omega)
    simpa only [hv, s79] using h78
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have haddr79 : s79.getReg .x29 + signExtend12 (8#12) = BitVec.ofNat 64 (68719475728 + 40 * l + 8) := by
    have hr29 : s79.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) := hx29
    rw [hr29, hse8, bv64_ofNat_add]
  have h79 := step_LD (by omega) (rfl : s79.pc = pcAt 79)
    (rfl : openingInstr 79 = .base (.LD .x7 .x29 (8#12)))
    (by rw [haddr79]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s80 := (s79.setReg .x7 (BitVec.ofNat 64 (levelSize l))).setPC (pcAt 80)
  have h79' : OpenRuns s79 1 1 s80 := by
    have hmem : s79.getMem (BitVec.ofNat 64 (68719475728 + 40 * l + 8)) = BitVec.ofNat 64 (levelSize l) :=
      readOnly_getMem_data_size inv.ro l (by omega)
    simpa only [haddr79, hmem, s80] using h79
  have hpre : OpenRuns s 3 3 s80 := (h77'.trans h78').trans h79'
  have hx28_toNat : (s80.getReg .x28).toNat = sib := by
    change (BitVec.ofNat 64 sib).toNat = sib
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsib_lt64]
  have hx7_toNat : (s80.getReg .x7).toNat = levelSize l := by
    change (BitVec.ofNat 64 (levelSize l)).toNat = levelSize l
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hinv80 : RecInv trapdoor positions t fwdBytes tails s80 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  have hto89 : ∃ n89 s89, OpenRuns s80 n89 n89 s89 ∧ n89 ≤ 65 ∧
      s89.pc = pcAt 89 ∧
      s89.getReg .x22 = BitVec.ofNat 64 idx ∧
      s89.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) ∧
      s89.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14) ∧
      fwd1.length ≤ fwdBytes.length + 30 ∧
      tails1.length ≤ tails.length + 1 ∧
      RecInv trapdoor positions t fwd1 tails1 s89 := by
    by_cases hsib_lt : sib < levelSize l
    · have h80 := step_BGEU_not_taken (by omega) (rfl : s80.pc = pcAt 80)
        (rfl : openingInstr 80 = .base (.BGEU .x28 .x7 (36#13)))
        (by rw [hx28_toNat, hx7_toNat]; exact hsib_lt)
      let s81 := s80.setPC (pcAt 81)
      have h81 := step_SRLI (by omega) (rfl : s81.pc = pcAt 81)
        (rfl : openingInstr 81 = .base (.SRLI .x6 .x28 (1#6)))
      let s82 := (s81.setReg .x6 (BitVec.ofNat 64 (sib / 2))).setPC (pcAt 82)
      have h81' : OpenRuns s81 1 1 s82 := by
        have hv : s81.getReg .x28 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (sib / 2) := by
          change BitVec.ofNat 64 sib >>> 1 = _
          rw [bv64_ushr sib 1 hsib_lt64, Nat.shiftRight_eq_div_pow]
        simpa only [hv, s82] using h81
      have h82 := step_ADD (by omega) (rfl : s82.pc = pcAt 82)
        (rfl : openingInstr 82 = .base (.ADD .x28 .x28 .x6))
      let s83 := (s82.setReg .x28 (BitVec.ofNat 64 (sib + sib / 2))).setPC (pcAt 83)
      have h82' : OpenRuns s82 1 1 s83 := by
        have hv : s82.getReg .x28 + s82.getReg .x6 = BitVec.ofNat 64 (sib + sib / 2) := by
          change BitVec.ofNat 64 sib + BitVec.ofNat 64 (sib / 2) = _; exact bv64_ofNat_add _ _
        simpa only [hv, s83] using h82
      have h83 := step_SLLI (by omega) (rfl : s83.pc = pcAt 83)
        (rfl : openingInstr 83 = .base (.SLLI .x28 .x28 (5#6)))
      let s84 := (s83.setReg .x28 (BitVec.ofNat 64 (nodeOffset l sib))).setPC (pcAt 84)
      have h83' : OpenRuns s83 1 1 s84 := by
        have hv : s83.getReg .x28 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (nodeOffset l sib) := by
          change BitVec.ofNat 64 (sib + sib / 2) <<< 5 = _
          rw [bv64_shl]; congr 1
          have hl0 : l ≠ 0 := by omega
          unfold nodeOffset gapOffset
          rw [if_neg hl0]; omega
        simpa only [hv, s84] using h83
      have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
      have haddr84 : s84.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475728 + 40 * l) := by
        have hr29 : s84.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) := hx29
        rw [hr29, hse0, bv64_ofNat_add, Nat.add_zero]
      have h84 := step_LD (by omega) (rfl : s84.pc = pcAt 84)
        (rfl : openingInstr 84 = .base (.LD .x6 .x29 (0#12)))
        (by rw [haddr84]; exact accessValid_ofNat _ 8 (by omega) (by omega))
      let s85 := (s84.setReg .x6 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 85)
      have h84' : OpenRuns s84 1 1 s85 := by
        have hmem : s84.getMem (BitVec.ofNat 64 (68719475728 + 40 * l)) = BitVec.ofNat 64 (levelBase l) :=
          readOnly_getMem_data_base inv.ro l (by omega)
        simpa only [haddr84, hmem, s85] using h84
      have h85 := step_ADD (by omega) (rfl : s85.pc = pcAt 85)
        (rfl : openingInstr 85 = .base (.ADD .x10 .x9 .x6))
      let s86 := (s85.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 86)
      have h85' : OpenRuns s85 1 1 s86 := by
        have hr9 : s85.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
        rw [hr9] at h85
        simpa only [show s85.getReg .x6 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s86] using h85
      have h86 := step_ADD (by omega) (rfl : s86.pc = pcAt 86)
        (rfl : openingInstr 86 = .base (.ADD .x10 .x10 .x28))
      let s87 := (s86.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)))).setPC
        (pcAt 87)
      have h86' : OpenRuns s86 1 1 s87 := by
        have hv : s86.getReg .x10 + s86.getReg .x28 =
            BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)) := by
          change BitVec.ofNat 64 (4294971424 + levelBase l) + BitVec.ofNat 64 (nodeOffset l sib) = _
          rw [bv64_ofNat_add, Nat.add_assoc]
        simpa only [hv, s87] using h86
      have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
      have haddr87 : s87.getReg .x29 + signExtend12 (32#12) = BitVec.ofNat 64 (68719475728 + 40 * l + 32) := by
        have hr29 : s87.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) := hx29
        rw [hr29, hse32, bv64_ofNat_add]
      have h87 := step_LD (by omega) (rfl : s87.pc = pcAt 87)
        (rfl : openingInstr 87 = .base (.LD .x7 .x29 (32#12)))
        (by rw [haddr87]; exact accessValid_ofNat _ 8 (by omega) (by omega))
      let s88 := (s87.setReg .x7 (BitVec.ofNat 64 (levelMetaOC l))).setPC (pcAt 88)
      have h87' : OpenRuns s87 1 1 s88 := by
        have hmem : s87.getMem (BitVec.ofNat 64 (68719475728 + 40 * l + 32)) = BitVec.ofNat 64 (levelMetaOC l) :=
          readOnly_getMem_data_meta inv.ro l (by omega)
        simpa only [haddr87, hmem, s88] using h87
      have hinv88 : RecInv trapdoor positions t fwdBytes tails s88 :=
        ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
         inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
      obtain ⟨stC, s89, hrcopy, hstC, hpc89, hreg89, hro89, hw89, ht89, hcap89⟩ :=
        openRuns_call_emitVar (callIdx := 88) (l := l) (nodeIdx := sib) (jOff := 472#21)
          (fwdBytes := fwdBytes) (tails := tails) (by omega) (by omega) (by omega) hsib_lt
          rfl (by decide) rfl rfl rfl (by omega) htbd hinv88.ro hinv88.writer hinv88.tail
      have hf1 : fwd1 = fwdBytes ++ bitsToBytes (tdNode trapdoor l sib) (levelBodyBytes l) := by
        change fwdBytes ++ (if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) (levelBodyBytes l) else []) = _
        rw [if_pos hsib_lt]
      have ht1 : tails1 = tails ++ [tailChunkOf l (tdNode trapdoor l sib)] := by
        change tails ++ (if sib < levelSize l then [tailChunkOf l (tdNode trapdoor l sib)] else []) = _
        rw [if_pos hsib_lt]
      rw [hf1, ht1]
      refine ⟨8 + stC, s89,
        (((((((h80.trans h81').trans h82').trans h83').trans h84').trans h85').trans h86').trans h87').trans hrcopy,
        by omega, hpc89, ?_, ?_, ?_,
        by simp only [List.length_append, bitsToBytes_length]; omega,
        by simp only [List.length_append, List.length_singleton]; omega,
        hinv88.after_sub (fun r hr => by
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            exact hreg89 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
          hro89 hw89 ht89 hcap89⟩
      · exact (hreg89 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans rfl
      · rw [hreg89 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx29
      · rw [hreg89 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx30
    · have h80 := step_BGEU_taken (by omega) (rfl : s80.pc = pcAt 80)
        (rfl : openingInstr 80 = .base (.BGEU .x28 .x7 (36#13)))
        (by rw [hx28_toNat, hx7_toNat]; omega)
        (by decide : pcAt 80 + signExtend13 (36#13) = pcAt 89)
      have hf1 : fwd1 = fwdBytes := by
        change fwdBytes ++ (if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) (levelBodyBytes l) else []) = _
        rw [if_neg hsib_lt, List.append_nil]
      have ht1 : tails1 = tails := by
        change tails ++ (if sib < levelSize l then [tailChunkOf l (tdNode trapdoor l sib)] else []) = _
        rw [if_neg hsib_lt, List.append_nil]
      rw [hf1, ht1]
      exact ⟨1, s80.setPC (pcAt 89), h80, by omega, rfl, rfl, hx29, hx30, by omega, by omega,
        hinv80.setPC (pcAt 89)⟩
  obtain ⟨n89, s89, hr89, hn89, hpc89, hx22_89, hx29_89, hx30_89, hlen1, htlen1, inv89⟩ := hto89
  have hse40 : signExtend12 (40#12) = BitVec.ofNat 64 40 := by decide
  have h89 := step_ADDI (by omega) hpc89 (rfl : openingInstr 89 = .base (.ADDI .x29 .x29 (40#12)))
  let s90 := (s89.setReg .x29 (BitVec.ofNat 64 (68719475728 + 40 * (2 + (step + 1))))).setPC (pcAt 90)
  have h89' : OpenRuns s89 1 1 s90 := by
    have hv : s89.getReg .x29 + signExtend12 (40#12) =
        BitVec.ofNat 64 (68719475728 + 40 * (2 + (step + 1))) := by
      rw [hx29_89, hse40, bv64_ofNat_add]; congr 1
    simpa only [hv, s90] using h89
  have hinv90 : RecInv trapdoor positions t fwd1 tails1 s90 :=
    ⟨inv89.rx2, inv89.rx9, inv89.rx18, inv89.rx19, inv89.rx20, inv89.rx21, inv89.rx24,
     inv89.rx26, inv89.rx27, inv89.ro, inv89.writer.of_eq, inv89.tail.of_eq, inv89.cap14⟩
  by_cases hmore : step + 1 < 12
  · have h90 := step_BNE_taken (by omega) (rfl : s90.pc = pcAt 90)
      (rfl : openingInstr 90 = .base (.BNE .x29 .x30 (8140#13)))
      (by change BitVec.ofNat 64 (68719475728 + 40 * (2 + (step + 1))) ≠ s89.getReg .x30
          rw [hx30_89]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 90 + signExtend13 (8140#13) = pcAt 77)
    exact ⟨3 + n89 + 1 + 1, s90.setPC (pcAt 77), ((hpre.trans hr89).trans h89').trans h90,
      by omega, by rw [if_pos hmore]; rfl, hx22_89, rfl, hx30_89,
      hlen1, htlen1, hinv90.setPC (pcAt 77)⟩
  · have hlast : step + 1 = 12 := by omega
    have h90 := step_BNE_not_taken (by omega) (rfl : s90.pc = pcAt 90)
      (rfl : openingInstr 90 = .base (.BNE .x29 .x30 (8140#13)))
      (by change BitVec.ofNat 64 (68719475728 + 40 * (2 + (step + 1))) = s89.getReg .x30
          rw [hx30_89, hlast])
    exact ⟨3 + n89 + 1 + 1, s90.setPC (pcAt 91), ((hpre.trans hr89).trans h89').trans h90,
      by omega, by rw [if_neg hmore]; rfl, hx22_89, rfl, hx30_89,
      hlen1, htlen1, hinv90.setPC (pcAt 91)⟩

private theorem openRuns_rec_bin {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g : Nat} {fwdBytes : List Byte} {tails : List TailChunk}
    {s : MachineState}
    (hg : g ≤ FULL_TRIPLETS) (hpc : s.pc = pcAt 75)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 g)
    (hbd : fwdBytes.length + 360 ≤ 8556390424)
    (htbd : tails.length + 12 ≤ 210000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let fwd1 := fwdBytes ++ binPathFwd (tdNode trapdoor) g
    let tails1 := tails ++ binPathTails (tdNode trapdoor) g
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 842 ∧
      s1.pc = pcAt 91 ∧
      s1.getReg .x22 = BitVec.ofNat 64 (g >>> 12) ∧
      RecInv trapdoor positions t fwd1 tails1 s1 := by
  intro fwd1 tails1
  have hse80 : signExtend12 (80#12) = BitVec.ofNat 64 80 := by decide
  have hse560 : signExtend12 (560#12) = BitVec.ofNat 64 560 := by decide
  have h75 := step_ADDI (by omega) hpc (rfl : openingInstr 75 = .base (.ADDI .x29 .x2 (80#12)))
  let s76 := (s.setReg .x29 (BitVec.ofNat 64 (68719475728 + 40 * 2))).setPC (pcAt 76)
  have h75' : OpenRuns s 1 1 s76 := by
    rw [inv.rx2, hse80, bv64_ofNat_add] at h75; exact h75
  have h76 := step_ADDI (by omega) (rfl : s76.pc = pcAt 76)
    (rfl : openingInstr 76 = .base (.ADDI .x30 .x2 (560#12)))
  let s77 := (s76.setReg .x30 (BitVec.ofNat 64 (68719475728 + 40 * 14))).setPC (pcAt 77)
  have h76' : OpenRuns s76 1 1 s77 := by
    have hr2 : s76.getReg .x2 = BitVec.ofNat 64 68719475728 := inv.rx2
    rw [hr2, hse560, bv64_ofNat_add] at h76; exact h76
  have hinv77 : RecInv trapdoor positions t fwdBytes tails s77 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap14⟩
  have hloop : ∀ n ≤ 12,
      let curF := fwdBytes ++ (List.range n).flatMap (binStepFwd trapdoor g)
      let curT := tails ++ (List.range n).flatMap (binStepTails trapdoor g)
      ∃ steps sn, OpenRuns s77 steps steps sn ∧
        steps ≤ 70 * n ∧
        sn.pc = (if n < 12 then pcAt 77 else pcAt 91) ∧
        sn.getReg .x22 = BitVec.ofNat 64 (g >>> n) ∧
        sn.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (2 + n)) ∧
        sn.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 14) ∧
        curF.length ≤ fwdBytes.length + 30 * n ∧
        curT.length ≤ tails.length + n ∧
        RecInv trapdoor positions t curF curT sn := by
    intro n hn
    induction n with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.add_zero]
      exact ⟨0, s77, OpenRuns.refl s77, Nat.le_refl 0, by rw [if_pos (by omega : 0 < 12)]; rfl,
        by rw [Nat.shiftRight_zero]; exact hx22, rfl, rfl, Nat.le_refl _, Nat.le_refl _, hinv77⟩
    | succ n ih =>
      obtain ⟨st, sn, hrn, hstn, hpcn, hx22n, hx29n, hx30n, hlenn, htlenn, invn⟩ := ih (by omega)
      have hpcn' : sn.pc = pcAt 77 := by simpa only [show n < 12 by omega, ite_true] using hpcn
      obtain ⟨st1, sn1, hr1, hst1, hpc1, hx22_1, hx29_1, hx30_1, hlen1, htlen1, inv1⟩ :=
        openRuns_rec_bin_step hg (by omega) hpcn' hx22n hx29n hx30n (by omega) (by omega) invn
      have happF : fwdBytes ++ (List.range n).flatMap (binStepFwd trapdoor g) ++ binStepFwd trapdoor g n =
          fwdBytes ++ (List.range (n + 1)).flatMap (binStepFwd trapdoor g) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      have happT : tails ++ (List.range n).flatMap (binStepTails trapdoor g) ++ binStepTails trapdoor g n =
          tails ++ (List.range (n + 1)).flatMap (binStepTails trapdoor g) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      rw [happF] at hlen1 inv1
      rw [happT] at htlen1 inv1
      exact ⟨st + st1, sn1, hrn.trans hr1, by omega, hpc1, hx22_1, hx29_1, hx30_1,
        by omega, by omega, inv1⟩
  obtain ⟨st, s91, hrloop, hst, hpc91, hx22_91, _, _, _, _, inv91⟩ := hloop 12 (Nat.le_refl 12)
  have hpc91' : s91.pc = pcAt 91 := by simpa only [Nat.lt_irrefl, ite_false] using hpc91
  have hfwd_eq : fwdBytes ++ (List.range 12).flatMap (binStepFwd trapdoor g) = fwd1 := rfl
  have htails_eq : tails ++ (List.range 12).flatMap (binStepTails trapdoor g) = tails1 := rfl
  rw [hfwd_eq, htails_eq] at inv91
  exact ⟨2 + st, s91, (h75'.trans h76').trans hrloop, by omega, hpc91', hx22_91, inv91⟩

private theorem openRuns_rec_iter {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List TailChunk}
    {s : MachineState}
    (ht : t < positions.card) (hpc : s.pc = pcAt 31)
    (hbd : fwdBytes.length ≤ 470 * t)
    (htbd : tails.length ≤ 12 * t)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let idx : Index := (positions.sort (· ≤ ·))[t]'(by simpa using ht)
    let fwd' := fwdBytes ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) idx
    let tails' := tails ++ recordTails (tdNode trapdoor) idx
    ∃ steps cycles s', OpenRuns s steps cycles s' ∧
      steps ≤ 982 ∧ cycles ≤ 988 ∧
      s'.pc = (if t + 1 < positions.card then pcAt 31 else pcAt 98) ∧
      fwd'.length ≤ 470 * (t + 1) ∧
      tails'.length ≤ 12 * (t + 1) ∧
      RecInv trapdoor positions (t + 1) fwd' tails' s' := by
  intro idx fwd' tails'
  have hcard := positions_card_le positions
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
  have hg_le : idx.val / 3 ≤ FULL_TRIPLETS := by omega
  obtain ⟨s43, hrsalt, hpc43, hx8_43, inv43⟩ := openRuns_rec_salt ht hpc (by omega) (by omega) inv
  change s43.getReg .x8 = BitVec.ofNat 64 idx.val at hx8_43
  change RecInv trapdoor positions t (fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24) tails s43 at inv43
  have hlen43 : (fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24).length ≤ 470 * t + 24 := by
    simp only [List.length_append, bitsToBytes_length]; omega
  obtain ⟨st0, cy0, s67, hrl0, hst0, hcy0, hpc67, hx22_67, inv67⟩ :=
    openRuns_rec_l0 hpc43 idx hx8_43 (by omega) (by omega) inv43
  have hlen67 : (fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24 ++
      l0SiblingsProof (tdNode trapdoor) idx).length ≤ 470 * t + 88 := by
    have := l0SiblingsProof_length_le (tdNode trapdoor) idx
    simp only [List.length_append, bitsToBytes_length] at *; omega
  obtain ⟨s75, hrl1, hpc75, hx22_75, inv75⟩ :=
    openRuns_rec_l1 hg_le hpc67 hx22_67 (by omega) (by omega) inv67
  have hlen75 : (fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24 ++
      l0SiblingsProof (tdNode trapdoor) idx ++
      bitsToBytes (tdNode trapdoor 1 ((idx.val / 3) ^^^ 1)) 32).length ≤ 470 * t + 120 := by
    simp only [List.length_append, bitsToBytes_length] at *; omega
  obtain ⟨stBin, s91, hrBin, hstBin, hpc91, hx22_91, inv91⟩ :=
    openRuns_rec_bin hg_le hpc75 hx22_75 (by omega) (by omega) inv75
  have happF : fwdBytes ++ bitsToBytes (tdSalt trapdoor idx) 24 ++
      l0SiblingsProof (tdNode trapdoor) idx ++
      bitsToBytes (tdNode trapdoor 1 ((idx.val / 3) ^^^ 1)) 32 ++
      binPathFwd (tdNode trapdoor) (idx.val / 3) = fwd' := by
    simp only [fwd', recordFwd, List.append_assoc]
  have happT : tails ++ binPathTails (tdNode trapdoor) (idx.val / 3) = tails' := rfl
  rw [happF, happT] at inv91
  have hlen_recF : fwd'.length ≤ 470 * (t + 1) := by
    have hr := recordFwd_length_le_470 (tdNode trapdoor) (tdSalt trapdoor) idx
    simp only [fwd', List.length_append]; omega
  have hlen_recT : tails'.length ≤ 12 * (t + 1) := by
    have hr := recordTails_length_le_12 (tdNode trapdoor) idx
    simp only [tails', List.length_append]; omega
  -- Tail: 91..97
  have hcap_lt : capLeafNat idx.val < 683 := capLeafOf_lt idx
  have hg12_le : (idx.val / 3) >>> 12 ≤ idx.val / 3 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  have h91 := step_SRLI (by omega) hpc91 (rfl : openingInstr 91 = .base (.SRLI .x22 .x22 (1#6)))
  let s92 := (s91.setReg .x22 (BitVec.ofNat 64 (capLeafNat idx.val))).setPC (pcAt 92)
  have h91' : OpenRuns s91 1 1 s92 := by
    have hv : s91.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (capLeafNat idx.val) := by
      rw [hx22_91]; change BitVec.ofNat 64 ((idx.val / 3) >>> 12) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), nat_ushr_ushr1]; rfl
    simpa only [hv, s92] using h91
  have h92 := step_ADD (by omega) (rfl : s92.pc = pcAt 92)
    (rfl : openingInstr 92 = .base (.ADD .x6 .x21 .x22))
  let s93 := (s92.setReg .x6 (BitVec.ofNat 64 (4096 + capLeafNat idx.val))).setPC (pcAt 93)
  have h92' : OpenRuns s92 1 1 s93 := by
    have hr21 : s92.getReg .x21 = BitVec.ofNat 64 4096 := inv91.rx21
    rw [hr21] at h92
    simpa only [show s92.getReg .x22 = BitVec.ofNat 64 (capLeafNat idx.val) from rfl,
      bv64_ofNat_add, s93] using h92
  have h93 := step_ADDI (by omega) (rfl : s93.pc = pcAt 93)
    (rfl : openingInstr 93 = .base (.ADDI .x7 .x0 (1#12)))
  let s94 := (s93.setReg .x7 1#64).setPC (pcAt 94)
  have h93' : OpenRuns s93 1 1 s94 := by
    have hv : s93.getReg .x0 + signExtend12 (1#12) = 1#64 := by
      change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s94] using h93
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have haddr94 : s94.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (4096 + capLeafNat idx.val) := by
    change BitVec.ofNat 64 (4096 + capLeafNat idx.val) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h94 := step_SB (by omega) (rfl : s94.pc = pcAt 94)
    (rfl : openingInstr 94 = .base (.SB .x6 .x7 (0#12)))
    (by rw [haddr94]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s95 := (s94.setByte (BitVec.ofNat 64 (4096 + capLeafNat idx.val)) 1#8).setPC (pcAt 95)
  have h94' : OpenRuns s94 1 1 s95 := by
    have htr : (s94.getReg .x7).truncate 8 = 1#8 := by
      change (1#64 : Word).truncate 8 = 1#8; decide
    simpa only [haddr94, htr, s95] using h94
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have h95 := step_ADDI (by omega) (rfl : s95.pc = pcAt 95)
    (rfl : openingInstr 95 = .base (.ADDI .x24 .x24 (8#12)))
  let s96 := (s95.setReg .x24 (BitVec.ofNat 64 (6912218176 + 8 * (t + 1)))).setPC (pcAt 96)
  have h95' : OpenRuns s95 1 1 s96 := by
    have hr24 : s95.getReg .x24 = BitVec.ofNat 64 (6912218176 + 8 * t) := by
      simp only [s95, s94, s93, s92, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x7 .x24 (by decide),
        getReg_setReg_ne' .x6 .x24 (by decide),
        getReg_setReg_ne' .x22 .x24 (by decide)]
      exact inv91.rx24
    have hv : s95.getReg .x24 + signExtend12 (8#12) =
        BitVec.ofNat 64 (6912218176 + 8 * (t + 1)) := by
      rw [hr24, hse8, bv64_ofNat_add]; congr 1
    simpa only [hv, s96] using h95
  have h96 := step_ADDI (by omega) (rfl : s96.pc = pcAt 96)
    (rfl : openingInstr 96 = .base (.ADDI .x27 .x27 (4095#12)))
  let s97 := (s96.setReg .x27 (BitVec.ofNat 64 (positions.card - (t + 1)))).setPC (pcAt 97)
  have h96' : OpenRuns s96 1 1 s97 := by
    have hr27 : s96.getReg .x27 = BitVec.ofNat 64 ((positions.card - (t + 1)) + 1) := by
      simp only [s96, s95, s94, s93, s92, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x24 .x27 (by decide),
        getReg_setReg_ne' .x7 .x27 (by decide),
        getReg_setReg_ne' .x6 .x27 (by decide),
        getReg_setReg_ne' .x22 .x27 (by decide)]
      rw [inv91.rx27]; congr 1; omega
    rw [hr27, bv64_add_neg1] at h96; exact h96
  have hpres97 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x24 → r ≠ .x27 →
      s97.getReg r = s91.getReg r := fun r h6 h7 h22 h24 h27 => by
    simp only [s97, s96, s95, s94, s93, s92, MachineState.getReg_setPC, getReg_setByte,
      getReg_setReg_ne' .x27 r (Ne.symm h27), getReg_setReg_ne' .x24 r (Ne.symm h24),
      getReg_setReg_ne' .x7 r (Ne.symm h7), getReg_setReg_ne' .x6 r (Ne.symm h6),
      getReg_setReg_ne' .x22 r (Ne.symm h22)]
  have hmem97 : ∀ a, s97.getByte a =
      (s91.setByte (BitVec.ofNat 64 (4096 + capLeafNat idx.val)) 1#8).getByte a := fun a => by
    simp only [s97, s96, s95, s94, s93, s92, getByte_setPC, getByte_setReg]; rfl
  have hro97 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s97 := by
    intro a ha
    simp only [s97, MachineState.getMem_setPC, MachineState.getMem_setReg, s96, s95]
    exact readOnly_setByte_cap (4096 + capLeafNat idx.val) 1#8 inv91.ro (by omega) (by omega) a ha
  have hw97 : WriterState s97 fwd' := by
    have hw' := writerState_setByte_outside (4096 + capLeafNat idx.val) 1#8 inv91.writer
      (by omega) (Or.inl (by omega)) (by omega)
    exact ⟨by rw [hpres97 .x25 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.writer.rx25,
      by rw [hpres97 .x13 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.writer.rx13,
      by rw [hpres97 .x14 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.writer.rx14,
      fun j hj => by rw [hpres97 .x12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.writer.wbufLo j hj,
      fun j h1 h2 => by rw [hpres97 .x12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.writer.wbufHi j h1 h2,
      fun j hj => by rw [hmem97]; exact hw'.memDwords j hj⟩
  have ht97 : TailState s97 tails' := by
    have htb : tailBufBase = 20000000000 := rfl
    have ht' := tailState_setByte_outside (4096 + capLeafNat idx.val) 1#8 inv91.tail (by omega) (by omega)
    exact ⟨inv91.tail.valid,
      by rw [hpres97 .x31 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.tail.rx31,
      by rw [hpres97 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.tail.rx15,
      by rw [hpres97 .x16 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.tail.rx16,
      by rw [hpres97 .x17 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.tail.rx17,
      fun j hj => by rw [hmem97]; exact ht'.memTail j hj⟩
  have hcap97 : ∀ c < 683, s97.getByte (BitVec.ofNat 64 (4096 + c)) =
      if capMark14Prefix positions (t + 1) c then 1#8 else 0#8 := by
    intro c hc
    rw [hmem97, set_byte_read]
    have hopen : openingIndex positions t = idx.val := by simp only [openingIndex, dif_pos ht]; rfl
    by_cases hceq : c = capLeafNat idx.val
    · subst hceq
      rw [if_pos rfl]
      have htr : capMark14Prefix positions (t + 1) (capLeafNat idx.val) = true := by
        simp only [capMark14Prefix, decide_eq_true_eq]
        exact ⟨t, by omega, by rw [hopen]⟩
      rw [htr]; rfl
    · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega)), inv91.cap14 c hc]
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
  have hinv97 : RecInv trapdoor positions (t + 1) fwd' tails' s97 :=
    ⟨by rw [hpres97 .x2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.rx2,
     by rw [hpres97 .x9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.rx9,
     by rw [hpres97 .x18 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.rx18,
     by rw [hpres97 .x19 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.rx19,
     by rw [hpres97 .x20 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.rx20,
     by rw [hpres97 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.rx21,
     by simp only [s97, MachineState.getReg_setPC, getReg_setReg_ne' .x27 .x24 (by decide)]; rfl,
     by rw [hpres97 .x26 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv91.rx26,
     rfl, hro97, hw97, ht97, hcap97⟩
  have htail := (((((h91'.trans h92').trans h93').trans h94').trans h95').trans h96')
  have hbody := (((hrsalt.trans hrl0).trans hrl1).trans hrBin).trans htail
  by_cases hmore : t + 1 < positions.card
  · have h97 := step_BNE_taken (by omega) (rfl : s97.pc = pcAt 97)
      (rfl : openingInstr 97 = .base (.BNE .x27 .x0 (7928#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) ≠ BitVec.ofNat 64 0
          exact bv64_ofNat_ne (by omega) (by decide) (by omega))
      (by decide : pcAt 97 + signExtend13 (7928#13) = pcAt 31)
    exact ⟨32 + st0 + 34 + stBin + 6 + 1, 32 + cy0 + 34 + stBin + 6 + 1,
      s97.setPC (pcAt 31), hbody.trans h97, by omega, by omega, by rw [if_pos hmore]; rfl,
      hlen_recF, hlen_recT, hinv97.setPC (pcAt 31)⟩
  · have hdone : positions.card - (t + 1) = 0 := by omega
    have h97 := step_BNE_not_taken (by omega) (rfl : s97.pc = pcAt 97)
      (rfl : openingInstr 97 = .base (.BNE .x27 .x0 (7928#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) = BitVec.ofNat 64 0; rw [hdone])
    exact ⟨32 + st0 + 34 + stBin + 6 + 1, 32 + cy0 + 34 + stBin + 6 + 1,
      s97.setPC (pcAt 98), hbody.trans h97, by omega, by omega, by rw [if_neg hmore]; rfl,
      hlen_recF, hlen_recT, hinv97.setPC (pcAt 98)⟩

private theorem openRuns_rec_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s31 : MachineState}
    (hne : 0 < positions.card) (hpc : s31.pc = pcAt 31)
    (inv0 : RecInv trapdoor positions 0 [] [] s31) :
    let recFwd := (positions.sort (· ≤ ·)).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
    let recTails := (positions.sort (· ≤ ·)).flatMap (recordTails (tdNode trapdoor))
    ∃ steps cycles s98, OpenRuns s31 steps cycles s98 ∧
      steps ≤ 982 * positions.card ∧
      cycles ≤ 988 * positions.card ∧
      s98.pc = pcAt 98 ∧
      s98.getReg .x2 = BitVec.ofNat 64 68719475728 ∧
      s98.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s98.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s98.getReg .x26 = BitVec.ofNat 64 11341403200 ∧
      recFwd.length ≤ 470 * positions.card ∧
      recTails.length ≤ 12 * positions.card ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s98 ∧
      WriterState s98 recFwd ∧
      TailState s98 recTails ∧
      CapLevelMarks s98 positions 14 := by
  intro recFwd recTails
  have hloop : ∀ t ≤ positions.card,
      let curF := ((positions.sort (· ≤ ·)).take t).flatMap
        (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
      let curT := ((positions.sort (· ≤ ·)).take t).flatMap
        (recordTails (tdNode trapdoor))
      ∃ steps cycles st, OpenRuns s31 steps cycles st ∧
        steps ≤ 982 * t ∧ cycles ≤ 988 * t ∧
        st.pc = (if t < positions.card then pcAt 31 else pcAt 98) ∧
        curF.length ≤ 470 * t ∧
        curT.length ≤ 12 * t ∧
        RecInv trapdoor positions t curF curT st := by
    intro t ht
    induction t with
    | zero =>
      dsimp only
      simp only [List.take_zero, List.flatMap_nil, Nat.mul_zero]
      exact ⟨0, 0, s31, OpenRuns.refl s31, Nat.le_refl 0, Nat.le_refl 0,
        by rw [if_pos hne]; exact hpc, Nat.le_refl 0, Nat.le_refl 0, inv0⟩
    | succ t ih =>
      obtain ⟨st, cy, stState, hr, hst, hcy, hpct, hbdt, htbdt, invt⟩ := ih (by omega)
      have hpct' : stState.pc = pcAt 31 := by simpa only [show t < positions.card by omega, ite_true] using hpct
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
  obtain ⟨steps, cycles, s98, hr, hst, hcy, hpc98, hbdEnd, htbdEnd, invEnd⟩ :=
    hloop positions.card (Nat.le_refl _)
  have hpc98' : s98.pc = pcAt 98 := by simpa only [Nat.lt_irrefl, ite_false] using hpc98
  have htakeAll : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) := by
    have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
    rw [← hlen, List.take_length]
  rw [htakeAll] at hbdEnd htbdEnd invEnd
  refine ⟨steps, cycles, s98, hr, hst, hcy, hpc98',
    invEnd.rx2, invEnd.rx9, invEnd.rx21, invEnd.rx26,
    hbdEnd, htbdEnd, invEnd.ro, invEnd.writer, invEnd.tail, ?_⟩
  intro idx hidx
  have hidx683 : idx < 683 := by rw [levelSize_14] at hidx; exact hidx
  have hmo14 : capMarkOff 14 = 0 := by decide
  rw [hmo14, Nat.add_zero, invEnd.cap14 idx hidx683, capMark14Prefix_card]

/-! ### 8. Cap Frontier Pass (`98..135`, `10` levels `L14..L23`) -/

private def capPairFwd (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (l q : Nat) : List Byte :=
  let mL := capMark positions l (2 * q)
  let mR := capMark positions l (2 * q + 1)
  if mL = mR then []
  else if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) (levelBodyBytes l)
  else bitsToBytes (tdNode trapdoor l (2 * q + 1)) (levelBodyBytes l)

private def capPairTails (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (l q : Nat) : List TailChunk :=
  let mL := capMark positions l (2 * q)
  let mR := capMark positions l (2 * q + 1)
  if mL = mR then []
  else if !mL then [tailChunkOf l (tdNode trapdoor l (2 * q))]
  else [tailChunkOf l (tdNode trapdoor l (2 * q + 1))]

private def capPairFrontier (positions : Positions) (l q : Nat) : Nat :=
  if capMark positions l (2 * q) != capMark positions l (2 * q + 1) then 1 else 0

private theorem sum_capPairFrontier_eq (positions : Positions) (l : Nat) :
    (∑ q ∈ Finset.range (levelSize l / 2), capPairFrontier positions l q) =
      levelFrontierCount positions l := by
  unfold levelFrontierCount capPairFrontier
  rw [Finset.card_filter]

private structure CapLvlInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (step : Nat) (fwdBytes : List Byte) (tails : List TailChunk)
    (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475728
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx26 : s.getReg .x26 = BitVec.ofNat 64 11341403200
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (14 + step))
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 24)
  boundFwd : fwdBytes.length ≤ 470 * positions.card +
    29 * (∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k))
  boundTails : tails.length ≤ 12 * positions.card +
    (∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k))
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  writer : WriterState s fwdBytes
  tail : TailState s tails
  capMarks : CapLevelMarks s positions (14 + step)

private structure CapPairInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (step q : Nat) (fwdBytes : List Byte) (tails : List TailChunk)
    (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475728
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase (14 + step))
  rx19 : s.getReg .x19 = BitVec.ofNat 64 (levelSize (14 + step))
  rx20 : s.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff (14 + step))
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx22 : s.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (14 + step + 1))
  rx23 : s.getReg .x23 = BitVec.ofNat 64 (levelSize (14 + step) / 2)
  rx24 : s.getReg .x24 = BitVec.ofNat 64 q
  rx26 : s.getReg .x26 = BitVec.ofNat 64 11341403200
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * (14 + step))
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 24)
  boundFwd : fwdBytes.length ≤ 470 * positions.card +
    29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
          (∑ j ∈ Finset.range q, capPairFrontier positions (14 + step) j))
  boundTails : tails.length ≤ 12 * positions.card +
    ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
     (∑ j ∈ Finset.range q, capPairFrontier positions (14 + step) j))
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  writer : WriterState s fwdBytes
  tail : TailState s tails
  curMarks : CapLevelMarks s positions (14 + step)
  nextMarks : ∀ j < q, s.getByte (BitVec.ofNat 64 (4096 + capMarkOff (14 + step + 1) + j)) =
    if capMark positions (14 + step + 1) j then 1#8 else 0#8

private theorem openRuns_cap_pair_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {step q : Nat} {fwdBytes : List Byte} {tails : List TailChunk}
    {s : MachineState}
    (hstep : step < 10) (hq : q < levelSize (14 + step) / 2) (hpc : s.pc = pcAt 109)
    (inv : CapPairInv trapdoor positions step q fwdBytes tails s) :
    let l := 14 + step
    let fwd1 := fwdBytes ++ capPairFwd trapdoor positions l q
    let tails1 := tails ++ capPairTails trapdoor positions l q
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 10 + 64 * capPairFrontier positions l q ∧
      s1.pc = (if q + 1 < levelSize l / 2 then pcAt 109 else pcAt 127) ∧
      CapPairInv trapdoor positions step (q + 1) fwd1 tails1 s1 := by
  intro l fwd1 tails1
  have hql : q < levelSize l / 2 := hq
  have hcur_inv : CapLevelMarks s positions l := inv.curMarks
  have hinv_bdF : fwdBytes.length ≤ 470 * positions.card +
      29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
            (∑ j ∈ Finset.range q, capPairFrontier positions l j)) := inv.boundFwd
  have hinv_bdT : tails.length ≤ 12 * positions.card +
      ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
       (∑ j ∈ Finset.range q, capPairFrontier positions l j)) := inv.boundTails
  have hcard := positions_card_le positions
  have hls_le := levelSize_le_max l (by omega)
  have hbb_le := levelBodyBytes_cap_le l (by omega) (by omega)
  have hcm_bd := capMarkOff_bound l (by omega) (by omega)
  have hcm1_bd := capMarkOff_bound (l + 1) (by omega) (by omega)
  have hcm_disj := capMarkOff_step_disjoint l (by omega) (by omega)
  have hls1_eq := levelSize_step l (by omega)
  have hq_lt_next : q < levelSize (l + 1) := by omega
  set mL := capMark positions l (2 * q)
  set mR := capMark positions l (2 * q + 1)
  have h109 := step_SLLI (by omega) hpc (rfl : openingInstr 109 = .base (.SLLI .x6 .x24 (1#6)))
  let s110 := (s.setReg .x6 (BitVec.ofNat 64 (2 * q))).setPC (pcAt 110)
  have h109' : OpenRuns s 1 1 s110 := by
    have hv : s.getReg .x24 <<< (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (2 * q) := by
      rw [inv.rx24]; change BitVec.ofNat 64 q <<< 1 = _; rw [bv64_shl]; congr 1; omega
    simpa only [hv, s110] using h109
  have h110 := step_ADD (by omega) (rfl : s110.pc = pcAt 110)
    (rfl : openingInstr 110 = .base (.ADD .x6 .x20 .x6))
  let s111 := (s110.setReg .x6 (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q))).setPC (pcAt 111)
  have h110' : OpenRuns s110 1 1 s111 := by
    have hr20 : s110.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) := inv.rx20
    rw [hr20] at h110
    simpa only [show s110.getReg .x6 = BitVec.ofNat 64 (2 * q) from rfl, bv64_ofNat_add, s111] using h110
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  have haddr111 : s111.getReg .x6 + signExtend12 (0#12) =
      BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) := by
    change BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h111 := step_LBU (by omega) (rfl : s111.pc = pcAt 111)
    (rfl : openingInstr 111 = .base (.LBU .x7 .x6 (0#12)))
    (by rw [haddr111]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s112 := (s111.setReg .x7 (if mL then 1#64 else 0#64)).setPC (pcAt 112)
  have h111' : OpenRuns s111 1 1 s112 := by
    have hb : s111.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q)) =
        if mL then 1#8 else 0#8 := hcur_inv (2 * q) (by omega)
    simpa only [haddr111, hb, bool_byte_zeroExtend mL, s112] using h111
  have haddr112 : s112.getReg .x6 + signExtend12 (1#12) =
      BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1)) := by
    change BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) + _ = _
    rw [hse1, bv64_ofNat_add, Nat.add_assoc]
  have h112 := step_LBU (by omega) (rfl : s112.pc = pcAt 112)
    (rfl : openingInstr 112 = .base (.LBU .x8 .x6 (1#12)))
    (by rw [haddr112]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s113 := (s112.setReg .x8 (if mR then 1#64 else 0#64)).setPC (pcAt 113)
  have h112' : OpenRuns s112 1 1 s113 := by
    have hb : s112.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1))) =
        if mR then 1#8 else 0#8 := hcur_inv (2 * q + 1) (by omega)
    simpa only [haddr112, hb, bool_byte_zeroExtend mR, s113] using h112
  have h113 := step_OR (by omega) (rfl : s113.pc = pcAt 113)
    (rfl : openingInstr 113 = .base (.OR .x11 .x7 .x8))
  let s114 := (s113.setReg .x11 (if (mL || mR) then 1#64 else 0#64)).setPC (pcAt 114)
  have h113' : OpenRuns s113 1 1 s114 := by
    simpa only [show s113.getReg .x7 = if mL then 1#64 else 0#64 from rfl,
      show s113.getReg .x8 = if mR then 1#64 else 0#64 from rfl,
      bool_word_or mL mR, s114] using h113
  have h114 := step_ADD (by omega) (rfl : s114.pc = pcAt 114)
    (rfl : openingInstr 114 = .base (.ADD .x6 .x22 .x24))
  let s115 := (s114.setReg .x6 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q))).setPC (pcAt 115)
  have h114' : OpenRuns s114 1 1 s115 := by
    have hr22 : s114.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) := inv.rx22
    have hr24 : s114.getReg .x24 = BitVec.ofNat 64 q := inv.rx24
    rw [hr22, hr24, bv64_ofNat_add] at h114; exact h114
  have haddr115 : s115.getReg .x6 + signExtend12 (0#12) =
      BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) := by
    change BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h115 := step_SB (by omega) (rfl : s115.pc = pcAt 115)
    (rfl : openingInstr 115 = .base (.SB .x6 .x11 (0#12)))
    (by rw [haddr115]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s116 := (s115.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q))
    (if (mL || mR) then 1#8 else 0#8)).setPC (pcAt 116)
  have h115' : OpenRuns s115 1 1 s116 := by
    simpa only [haddr115, show s115.getReg .x11 = if (mL || mR) then 1#64 else 0#64 from rfl,
      bool_word_truncate8 (mL || mR), s116] using h115
  have hpre : OpenRuns s 7 7 s116 :=
    (((((h109'.trans h110').trans h111').trans h112').trans h113').trans h114').trans h115'
  have hpres116 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x11 →
      s116.getReg r = s.getReg r := fun r h6 h7 h8 h11 => by
    simp only [s116, s115, s114, s113, s112, s111, s110,
      MachineState.getReg_setPC, getReg_setByte,
      getReg_setReg_ne' .x6 r (Ne.symm h6), getReg_setReg_ne' .x11 r (Ne.symm h11),
      getReg_setReg_ne' .x8 r (Ne.symm h8), getReg_setReg_ne' .x7 r (Ne.symm h7)]
  have hx7_116 : s116.getReg .x7 = if mL then 1#64 else 0#64 := by
    simp only [s116, MachineState.getReg_setPC, getReg_setByte]; rfl
  have hx8_116 : s116.getReg .x8 = if mR then 1#64 else 0#64 := by
    simp only [s116, MachineState.getReg_setPC, getReg_setByte]; rfl
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
  have hcap342 := cap_frontier_le_342 positions
  have hfwd_cap : fwdBytes.length ≤ 470 * 16777216 + 29 * 342 := by
    have h2 : (∑ j ∈ Finset.range q, capPairFrontier positions l j) ≤
        ∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j :=
      sum_range_le_of_le (capPairFrontier positions l) (by omega)
    omega
  have htails_cap : tails.length ≤ 12 * 16777216 + 342 := by
    have h2 : (∑ j ∈ Finset.range q, capPairFrontier positions l j) ≤
        ∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j :=
      sum_range_le_of_le (capPairFrontier positions l) (by omega)
    omega
  have hro116 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s116 := by
    intro a ha
    simp only [s116, MachineState.getMem_setPC]
    exact readOnly_setByte_cap (4096 + capMarkOff (l + 1) + q) _ inv.ro (by omega) (by omega) a ha
  have hw116 : WriterState s116 fwdBytes := by
    have hw' := writerState_setByte_outside (4096 + capMarkOff (l + 1) + q)
      (if (mL || mR) then 1#8 else 0#8) inv.writer (by omega) (Or.inl (by omega)) (by omega)
    exact ⟨by rw [hpres116 .x25 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx25,
      by rw [hpres116 .x13 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx13,
      by rw [hpres116 .x14 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx14,
      fun j hj => by rw [hpres116 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.wbufLo j hj,
      fun j h1 h2 => by rw [hpres116 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.wbufHi j h1 h2,
      fun j hj => by simp only [s116, getByte_setPC]; exact hw'.memDwords j hj⟩
  have ht116 : TailState s116 tails := by
    have htb : tailBufBase = 20000000000 := rfl
    have ht' := tailState_setByte_outside (4096 + capMarkOff (l + 1) + q)
      (if (mL || mR) then 1#8 else 0#8) inv.tail (by omega) (by omega)
    exact ⟨inv.tail.valid,
      by rw [hpres116 .x31 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx31,
      by rw [hpres116 .x15 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx15,
      by rw [hpres116 .x16 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx16,
      by rw [hpres116 .x17 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx17,
      fun j hj => by simp only [s116, getByte_setPC]; exact ht'.memTail j hj⟩
  have hcur116 : CapLevelMarks s116 positions l := by
    intro idx hidx
    simp only [s116, getByte_setPC, set_byte_read]
    rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
    exact hcur_inv idx hidx
  have hnext116 : ∀ j < q + 1, s116.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + j)) =
      if capMark positions (l + 1) j then 1#8 else 0#8 := by
    intro j hj
    simp only [s116, getByte_setPC, set_byte_read]
    by_cases hjq : j = q
    · subst j
      have hlt : 2 * q + 1 < levelSize l := by omega
      rw [if_pos rfl]
      change (if (capMark positions l (2 * q) || capMark positions l (2 * q + 1)) then 1#8 else 0#8) = _
      rw [capMark_succ positions l q (by omega), if_pos hlt]
    · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
      exact inv.nextMarks j (by omega)
  -- Branch on mL = mR to reach pcAt 125
  have hto125 : ∃ n125 s125, OpenRuns s116 n125 n125 s125 ∧
      n125 ≤ 1 + 64 * capPairFrontier positions l q ∧
      s125.pc = pcAt 125 ∧
      s125.getReg .x2 = BitVec.ofNat 64 68719475728 ∧
      s125.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s125.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l) ∧
      s125.getReg .x19 = BitVec.ofNat 64 (levelSize l) ∧
      s125.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
      s125.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s125.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
      s125.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) ∧
      s125.getReg .x24 = BitVec.ofNat 64 q ∧
      s125.getReg .x26 = BitVec.ofNat 64 11341403200 ∧
      s125.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) ∧
      s125.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 24) ∧
      fwd1.length ≤ 470 * positions.card +
        29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
              (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) ∧
      tails1.length ≤ 12 * positions.card +
        ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
         (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s125 ∧
      WriterState s125 fwd1 ∧
      TailState s125 tails1 ∧
      CapLevelMarks s125 positions l ∧
      (∀ j < q + 1, s125.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + j)) =
        if capMark positions (l + 1) j then 1#8 else 0#8) := by
    by_cases hsame : mL = mR
    · have h116 := step_BEQ_taken (by omega) (rfl : s116.pc = pcAt 116)
        (rfl : openingInstr 116 = .base (.BEQ .x7 .x8 (36#13)))
        (by rw [hx7_116, hx8_116, hsame])
        (by decide : pcAt 116 + signExtend13 (36#13) = pcAt 125)
      have hf1 : fwd1 = fwdBytes := by
        change fwdBytes ++ (if mL = mR then [] else _) = _; rw [if_pos hsame, List.append_nil]
      have ht1 : tails1 = tails := by
        change tails ++ (if mL = mR then [] else _) = _; rw [if_pos hsame, List.append_nil]
      rw [hf1, ht1]
      refine ⟨1, s116.setPC (pcAt 125), h116, by omega, rfl,
        by rw [MachineState.getReg_setPC, hpres116 .x2 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx2,
        by rw [MachineState.getReg_setPC, hpres116 .x9 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx9,
        by rw [MachineState.getReg_setPC, hpres116 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx18,
        by rw [MachineState.getReg_setPC, hpres116 .x19 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx19,
        by rw [MachineState.getReg_setPC, hpres116 .x20 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx20,
        by rw [MachineState.getReg_setPC, hpres116 .x21 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx21,
        by rw [MachineState.getReg_setPC, hpres116 .x22 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx22,
        by rw [MachineState.getReg_setPC, hpres116 .x23 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx23,
        by rw [MachineState.getReg_setPC, hpres116 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24,
        by rw [MachineState.getReg_setPC, hpres116 .x26 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx26,
        by rw [MachineState.getReg_setPC, hpres116 .x29 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx29,
        by rw [MachineState.getReg_setPC, hpres116 .x30 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx30,
        ?_, ?_, hro116, hw116.of_eq, ht116.of_eq, hcur116, hnext116⟩
      · rw [Finset.sum_range_succ]; omega
      · rw [Finset.sum_range_succ]; omega
    · have hcpf : capPairFrontier positions l q = 1 := bool_bne_one_of_ne hsame
      have h116 := step_BEQ_not_taken (by omega) (rfl : s116.pc = pcAt 116)
        (rfl : openingInstr 116 = .base (.BEQ .x7 .x8 (36#13)))
        (by rw [hx7_116, hx8_116]; exact bool_word_ne_of_ne hsame)
      let s117 := s116.setPC (pcAt 117)
      have h117 := step_SLLI (by omega) (rfl : s117.pc = pcAt 117)
        (rfl : openingInstr 117 = .base (.SLLI .x6 .x24 (6#6)))
      let s118 := (s117.setReg .x6 (BitVec.ofNat 64 (64 * q))).setPC (pcAt 118)
      have h117' : OpenRuns s117 1 1 s118 := by
        have hr24 : s117.getReg .x24 = BitVec.ofNat 64 q := by
          rw [show s117.getReg .x24 = s116.getReg .x24 from rfl,
            hpres116 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24
        have hv : s117.getReg .x24 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * q) := by
          rw [hr24]; change BitVec.ofNat 64 q <<< 6 = _; rw [bv64_shl]; congr 1; omega
        simpa only [hv, s118] using h117
      have h118 := step_SLLI (by omega) (rfl : s118.pc = pcAt 118)
        (rfl : openingInstr 118 = .base (.SLLI .x11 .x24 (5#6)))
      let s119 := (s118.setReg .x11 (BitVec.ofNat 64 (32 * q))).setPC (pcAt 119)
      have h118' : OpenRuns s118 1 1 s119 := by
        have hr24 : s118.getReg .x24 = BitVec.ofNat 64 q := by
          simp only [s118, s117, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x24 (by decide)]
          rw [hpres116 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24
        have hv : s118.getReg .x24 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (32 * q) := by
          rw [hr24]; change BitVec.ofNat 64 q <<< 5 = _; rw [bv64_shl]; congr 1; omega
        simpa only [hv, s119] using h118
      have h119 := step_ADD (by omega) (rfl : s119.pc = pcAt 119)
        (rfl : openingInstr 119 = .base (.ADD .x10 .x6 .x11))
      let s120 := (s119.setReg .x10 (BitVec.ofNat 64 (96 * q))).setPC (pcAt 120)
      have h119' : OpenRuns s119 1 1 s120 := by
        have hv : s119.getReg .x6 + s119.getReg .x11 = BitVec.ofNat 64 (96 * q) := by
          change BitVec.ofNat 64 (64 * q) + BitVec.ofNat 64 (32 * q) = _
          rw [bv64_ofNat_add]; congr 1; omega
        simpa only [hv, s120] using h119
      have h120 := step_ADD (by omega) (rfl : s120.pc = pcAt 120)
        (rfl : openingInstr 120 = .base (.ADD .x10 .x18 .x10))
      let s121 := (s120.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q))).setPC (pcAt 121)
      have h120' : OpenRuns s120 1 1 s121 := by
        have hr18 : s120.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l) := by
          simp only [s120, s119, s118, s117, MachineState.getReg_setPC,
            getReg_setReg_ne' .x10 .x18 (by decide), getReg_setReg_ne' .x11 .x18 (by decide),
            getReg_setReg_ne' .x6 .x18 (by decide)]
          rw [hpres116 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx18
        rw [hr18] at h120
        simpa only [show s120.getReg .x10 = BitVec.ofNat 64 (96 * q) from rfl, bv64_ofNat_add, s121] using h120
      have hmid : OpenRuns s116 5 5 s121 := (((h116.trans h117').trans h118').trans h119').trans h120'
      have hlen_bdF : fwdBytes.length + levelBodyBytes l ≤ 470 * positions.card +
          29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
                (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ, hcpf]; omega
      have hlen_bdT : tails.length + 1 ≤ 12 * positions.card +
          ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
           (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ, hcpf]; omega
      have hr7_121 : s121.getReg .x7 = if mL then 1#64 else 0#64 := by
        simp only [s121, s120, s119, s118, s117, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 .x7 (by decide), getReg_setReg_ne' .x11 .x7 (by decide),
          getReg_setReg_ne' .x6 .x7 (by decide)]
        exact hx7_116
      have hpres121 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x11 →
          s121.getReg r = s116.getReg r := fun r h6 h7 _ h10 h11 => by
        simp only [s121, s120, s119, s118, s117, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 r (Ne.symm h10), getReg_setReg_ne' .x11 r (Ne.symm h11),
          getReg_setReg_ne' .x6 r (Ne.symm h6)]
      have hto123 : ∃ n123 s123 childIdx, OpenRuns s121 n123 n123 s123 ∧ n123 ≤ 2 ∧
          childIdx = (if !mL then 2 * q else 2 * q + 1) ∧
          childIdx < levelSize l ∧
          s123.pc = pcAt 123 ∧
          s123.getReg .x10 = BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l childIdx)) ∧
          (∀ r, r ≠ .x10 → s123.getReg r = s121.getReg r) ∧
          s123.mem = s121.mem := by
        by_cases hmL : mL = true
        · have h121 := step_BEQ_not_taken (by omega) (rfl : s121.pc = pcAt 121)
            (rfl : openingInstr 121 = .base (.BEQ .x7 .x0 (8#13)))
            (by rw [hr7_121, hmL]; change (1#64 : Word) ≠ 0#64; decide)
          let s122 := s121.setPC (pcAt 122)
          have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
          have h122 := step_ADDI (by omega) (rfl : s122.pc = pcAt 122)
            (rfl : openingInstr 122 = .base (.ADDI .x10 .x10 (32#12)))
          have hno : levelBase l + nodeOffset l (2 * q + 1) = levelBase l + 96 * q + 32 := by
            have hl0 : l ≠ 0 := by omega
            unfold nodeOffset; rw [if_neg hl0, gapOffset_odd]; omega
          let s123 := (s122.setReg .x10
            (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l (2 * q + 1))))).setPC (pcAt 123)
          have h122' : OpenRuns s122 1 1 s123 := by
            have hv : s122.getReg .x10 + signExtend12 (32#12) =
                BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l (2 * q + 1))) := by
              change BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) + _ = _
              rw [hse32, bv64_ofNat_add]; congr 1; omega
            simpa only [hv, s123] using h122
          refine ⟨2, s123, 2 * q + 1, h121.trans h122', by omega, by rw [hmL]; rfl, by omega, rfl, rfl,
            fun r hr => by simp only [s123, s122, MachineState.getReg_setPC,
              getReg_setReg_ne' .x10 r (Ne.symm hr)], rfl⟩
        · have hmLf : mL = false := Bool.eq_false_iff.mpr hmL
          have h121 := step_BEQ_taken (by omega) (rfl : s121.pc = pcAt 121)
            (rfl : openingInstr 121 = .base (.BEQ .x7 .x0 (8#13)))
            (by rw [hr7_121, hmLf]; rfl)
            (by decide : pcAt 121 + signExtend13 (8#13) = pcAt 123)
          have hno : levelBase l + nodeOffset l (2 * q) = levelBase l + 96 * q := by
            have hl0 : l ≠ 0 := by omega
            unfold nodeOffset; rw [if_neg hl0, gapOffset_even]
          refine ⟨1, s121.setPC (pcAt 123), 2 * q, h121, by omega, by rw [hmLf]; rfl, by omega, rfl,
            ?_, fun _ _ => rfl, rfl⟩
          change BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) = _
          rw [hno, Nat.add_assoc]
      obtain ⟨n123, s123, childIdx, hr123, hn123, hchildEq, hchildLt, hpc123, hx10_123, hreg123, hmem123⟩ := hto123
      -- 123: LD x7, 32(x29)
      have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
      have hx29_123 : s123.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) := by
        rw [hreg123 .x29 (by decide), hpres121 .x29 (by decide) (by decide) (by decide) (by decide) (by decide),
          hpres116 .x29 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx29
      have haddr123 : s123.getReg .x29 + signExtend12 (32#12) = BitVec.ofNat 64 (68719475728 + 40 * l + 32) := by
        rw [hx29_123, hse32, bv64_ofNat_add]
      have hro123 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s123 := by
        intro a ha; change s123.mem a = _; rw [hmem123]; exact hro116 a ha
      have h123 := step_LD (by omega) hpc123 (rfl : openingInstr 123 = .base (.LD .x7 .x29 (32#12)))
        (by rw [haddr123]; exact accessValid_ofNat _ 8 (by omega) (by omega))
      let s124 := (s123.setReg .x7 (BitVec.ofNat 64 (levelMetaOC l))).setPC (pcAt 124)
      have h123' : OpenRuns s123 1 1 s124 := by
        have hm : s123.getMem (BitVec.ofNat 64 (68719475728 + 40 * l + 32)) = BitVec.ofNat 64 (levelMetaOC l) :=
          readOnly_getMem_data_meta hro123 l (by omega)
        simpa only [haddr123, hm, s124] using h123
      have hro124 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s124 := by
        intro a ha; simp only [s124, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro123 a ha
      have hw124 : WriterState s124 fwdBytes :=
        ⟨by rw [show s124.getReg .x25 = s123.getReg .x25 from rfl, hreg123 .x25 (by decide),
              hpres121 .x25 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw116.rx25,
         by rw [show s124.getReg .x13 = s123.getReg .x13 from rfl, hreg123 .x13 (by decide),
              hpres121 .x13 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw116.rx13,
         by rw [show s124.getReg .x14 = s123.getReg .x14 from rfl, hreg123 .x14 (by decide),
              hpres121 .x14 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw116.rx14,
         fun j hj => by
           rw [show s124.getReg .x12 = s123.getReg .x12 from rfl, hreg123 .x12 (by decide),
             hpres121 .x12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw116.wbufLo j hj,
         fun j h1 h2 => by
           rw [show s124.getReg .x12 = s123.getReg .x12 from rfl, hreg123 .x12 (by decide),
             hpres121 .x12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw116.wbufHi j h1 h2,
         fun j hj => by
           simp only [s124, getByte_setPC, getByte_setReg]
           change extractByte (s123.mem _) _ = _; rw [hmem123]; exact hw116.memDwords j hj⟩
      have ht124 : TailState s124 tails :=
        ⟨ht116.valid,
         by rw [show s124.getReg .x31 = s123.getReg .x31 from rfl, hreg123 .x31 (by decide),
              hpres121 .x31 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht116.rx31,
         by rw [show s124.getReg .x15 = s123.getReg .x15 from rfl, hreg123 .x15 (by decide),
              hpres121 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht116.rx15,
         by rw [show s124.getReg .x16 = s123.getReg .x16 from rfl, hreg123 .x16 (by decide),
              hpres121 .x16 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht116.rx16,
         by rw [show s124.getReg .x17 = s123.getReg .x17 from rfl, hreg123 .x17 (by decide),
              hpres121 .x17 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht116.rx17,
         fun j hj => by
           simp only [s124, getByte_setPC, getByte_setReg]
           change extractByte (s123.mem _) _ = _; rw [hmem123]; exact ht116.memTail j hj⟩
      have hx10_124 : s124.getReg .x10 = BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l childIdx)) := hx10_123
      obtain ⟨stC, s125, hrcopy, hstC, hpc125, hreg125, hro125, hw125, ht125, hcap125⟩ :=
        openRuns_call_emitVar (callIdx := 124) (l := l) (nodeIdx := childIdx) (jOff := 328#21)
          (fwdBytes := fwdBytes) (tails := tails) (by omega) (by omega) (by omega) hchildLt
          rfl (by decide) rfl hx10_124 rfl (by omega) (by omega) hro124 hw124 ht124
      have hf1 : fwd1 = fwdBytes ++ bitsToBytes (tdNode trapdoor l childIdx) (levelBodyBytes l) := by
        change fwdBytes ++ (if mL = mR then []
          else if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) (levelBodyBytes l)
          else bitsToBytes (tdNode trapdoor l (2 * q + 1)) (levelBodyBytes l)) = _
        rw [if_neg hsame, hchildEq]
        by_cases hnot : (!mL) = true
        · rw [if_pos hnot, if_pos hnot]
        · rw [if_neg hnot, if_neg hnot]
      have ht1 : tails1 = tails ++ [tailChunkOf l (tdNode trapdoor l childIdx)] := by
        change tails ++ (if mL = mR then []
          else if !mL then [tailChunkOf l (tdNode trapdoor l (2 * q))]
          else [tailChunkOf l (tdNode trapdoor l (2 * q + 1))]) = _
        rw [if_neg hsame, hchildEq]
        by_cases hnot : (!mL) = true
        · rw [if_pos hnot, if_pos hnot]
        · rw [if_neg hnot, if_neg hnot]
      rw [hf1, ht1]
      have h124r : ∀ reg, reg ≠ .x7 → s124.getReg reg = s123.getReg reg := fun reg hne => by
        simp only [s124, MachineState.getReg_setPC, getReg_setReg_ne' .x7 reg (Ne.symm hne)]
      have hpres125 : ∀ r, r = .x2 ∨ r = .x9 ∨ r = .x18 ∨ r = .x19 ∨ r = .x20 ∨ r = .x21 ∨
          r = .x22 ∨ r = .x23 ∨ r = .x24 ∨ r = .x26 ∨ r = .x29 ∨ r = .x30 →
          s125.getReg r = s.getReg r := fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (
          rw [hreg125 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            h124r _ (by decide),
            hreg123 _ (by decide),
            hpres121 _ (by decide) (by decide) (by decide) (by decide) (by decide),
            hpres116 _ (by decide) (by decide) (by decide) (by decide)])
      refine ⟨5 + n123 + 1 + stC, s125, ((hmid.trans hr123).trans h123').trans hrcopy, by rw [hcpf]; omega, hpc125,
        by rw [hpres125 .x2 (by simp)]; exact inv.rx2,
        by rw [hpres125 .x9 (by simp)]; exact inv.rx9,
        by rw [hpres125 .x18 (by simp)]; exact inv.rx18,
        by rw [hpres125 .x19 (by simp)]; exact inv.rx19,
        by rw [hpres125 .x20 (by simp)]; exact inv.rx20,
        by rw [hpres125 .x21 (by simp)]; exact inv.rx21,
        by rw [hpres125 .x22 (by simp)]; exact inv.rx22,
        by rw [hpres125 .x23 (by simp)]; exact inv.rx23,
        by rw [hpres125 .x24 (by simp)]; exact inv.rx24,
        by rw [hpres125 .x26 (by simp)]; exact inv.rx26,
        by rw [hpres125 .x29 (by simp)]; exact inv.rx29,
        by rw [hpres125 .x30 (by simp)]; exact inv.rx30,
        by simp only [List.length_append, bitsToBytes_length]; exact hlen_bdF,
        by simp only [List.length_append, List.length_singleton]; exact hlen_bdT,
        hro125, hw125, ht125, ?_, ?_⟩
      · intro idx hidx
        rw [hcap125 (4096 + capMarkOff l + idx) (by omega)]
        simp only [s124, getByte_setPC, getByte_setReg]
        change extractByte (s123.mem _) _ = _; rw [hmem123]; exact hcur116 idx hidx
      · intro j hj
        rw [hcap125 (4096 + capMarkOff (l + 1) + j) (by omega)]
        simp only [s124, getByte_setPC, getByte_setReg]
        change extractByte (s123.mem _) _ = _; rw [hmem123]; exact hnext116 j hj
  obtain ⟨n125, s125, hr125, hn125, hpc125, hx2, hx9, hx18, hx19, hx20, hx21, hx22, hx23,
      hx24, hx26, hx29, hx30, hlenF1, hlenT1, hro125, hw125, ht125, hcur125, hnext125⟩ := hto125
  have h125 := step_ADDI (by omega) hpc125 (rfl : openingInstr 125 = .base (.ADDI .x24 .x24 (1#12)))
  let s126 := (s125.setReg .x24 (BitVec.ofNat 64 (q + 1))).setPC (pcAt 126)
  have h125' : OpenRuns s125 1 1 s126 := by
    rw [hx24, hse1, bv64_ofNat_add] at h125; exact h125
  have hmkInv : ∀ pc, CapPairInv trapdoor positions step (q + 1) fwd1 tails1 (s126.setPC pc) := fun pc =>
    ⟨hx2, hx9, hx18, hx19, hx20, hx21, hx22, hx23, rfl, hx26, hx29, hx30,
     hlenF1, hlenT1, hro125, hw125.of_eq, ht125.of_eq, hcur125, hnext125⟩
  by_cases hmore : q + 1 < levelSize l / 2
  · have h126 := step_BNE_taken (by omega) (rfl : s126.pc = pcAt 126)
      (rfl : openingInstr 126 = .base (.BNE .x24 .x23 (8124#13)))
      (by change BitVec.ofNat 64 (q + 1) ≠ s125.getReg .x23
          rw [hx23]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 126 + signExtend13 (8124#13) = pcAt 109)
    exact ⟨7 + n125 + 1 + 1, s126.setPC (pcAt 109), ((hpre.trans hr125).trans h125').trans h126,
      by omega, by rw [if_pos hmore]; rfl, hmkInv (pcAt 109)⟩
  · have hdone : q + 1 = levelSize l / 2 := by omega
    have h126 := step_BNE_not_taken (by omega) (rfl : s126.pc = pcAt 126)
      (rfl : openingInstr 126 = .base (.BNE .x24 .x23 (8124#13)))
      (by change BitVec.ofNat 64 (q + 1) = s125.getReg .x23; rw [hx23, hdone])
    exact ⟨7 + n125 + 1 + 1, s126.setPC (pcAt 127), ((hpre.trans hr125).trans h125').trans h126,
      by omega, by rw [if_neg hmore]; rfl, hmkInv (pcAt 127)⟩

private theorem openRuns_cap_lvl_iter {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {step : Nat} {fwdBytes : List Byte} {tails : List TailChunk}
    {s : MachineState}
    (hstep : step < 10) (hpc : s.pc = pcAt 100)
    (inv : CapLvlInv trapdoor positions step fwdBytes tails s) :
    let l := 14 + step
    let fwd1 := fwdBytes ++ capLevelFrontierFwd (tdNode trapdoor) positions l
    let tails1 := tails ++ capLevelFrontierTails (tdNode trapdoor) positions l
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 9 + 10 * (levelSize l / 2) + 64 * levelFrontierCount positions l +
        (if levelSize l % 2 = 0 then 4 else 9) ∧
      s1.pc = (if step + 1 < 10 then pcAt 100 else pcAt 136) ∧
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
  have hse40 : signExtend12 (40#12) = BitVec.ofNat 64 40 := by decide
  have hse56 : signExtend12 (56#12) = BitVec.ofNat 64 56 := by decide
  -- Header: 100..108 (9 steps)
  have haddr100 : s.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475728 + 40 * l) := by
    rw [inv.rx29, hse0, bv64_ofNat_add, Nat.add_zero]
  have h100 := step_LD (by omega) hpc (rfl : openingInstr 100 = .base (.LD .x18 .x29 (0#12)))
    (by rw [haddr100]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s101 := (s.setReg .x18 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 101)
  have h100' : OpenRuns s 1 1 s101 := by
    have hm := readOnly_getMem_data_base inv.ro l (by omega)
    simpa only [haddr100, hm, s101] using h100
  have h101 := step_ADD (by omega) (rfl : s101.pc = pcAt 101)
    (rfl : openingInstr 101 = .base (.ADD .x18 .x9 .x18))
  let s102 := (s101.setReg .x18 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 102)
  have h101' : OpenRuns s101 1 1 s102 := by
    have hr9 : s101.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
    rw [hr9] at h101
    simpa only [show s101.getReg .x18 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s102] using h101
  have haddr102 : s102.getReg .x29 + signExtend12 (8#12) = BitVec.ofNat 64 (68719475728 + 40 * l + 8) := by
    have hr29 : s102.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) := inv.rx29
    rw [hr29, hse8, bv64_ofNat_add]
  have h102 := step_LD (by omega) (rfl : s102.pc = pcAt 102)
    (rfl : openingInstr 102 = .base (.LD .x19 .x29 (8#12)))
    (by rw [haddr102]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s103 := (s102.setReg .x19 (BitVec.ofNat 64 (levelSize l))).setPC (pcAt 103)
  have h102' : OpenRuns s102 1 1 s103 := by
    have hm : s102.getMem (BitVec.ofNat 64 (68719475728 + 40 * l + 8)) = BitVec.ofNat 64 (levelSize l) :=
      readOnly_getMem_data_size inv.ro l (by omega)
    simpa only [haddr102, hm, s103] using h102
  have haddr103 : s103.getReg .x29 + signExtend12 (16#12) = BitVec.ofNat 64 (68719475728 + 40 * l + 16) := by
    have hr29 : s103.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) := inv.rx29
    rw [hr29, hse16, bv64_ofNat_add]
  have h103 := step_LD (by omega) (rfl : s103.pc = pcAt 103)
    (rfl : openingInstr 103 = .base (.LD .x20 .x29 (16#12)))
    (by rw [haddr103]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s104 := (s103.setReg .x20 (BitVec.ofNat 64 (capMarkOff l))).setPC (pcAt 104)
  have h103' : OpenRuns s103 1 1 s104 := by
    have hm : s103.getMem (BitVec.ofNat 64 (68719475728 + 40 * l + 16)) = BitVec.ofNat 64 (capMarkOff l) :=
      readOnly_getMem_data_markOff inv.ro l (by omega)
    simpa only [haddr103, hm, s104] using h103
  have h104 := step_ADD (by omega) (rfl : s104.pc = pcAt 104)
    (rfl : openingInstr 104 = .base (.ADD .x20 .x21 .x20))
  let s105 := (s104.setReg .x20 (BitVec.ofNat 64 (4096 + capMarkOff l))).setPC (pcAt 105)
  have h104' : OpenRuns s104 1 1 s105 := by
    have hr21 : s104.getReg .x21 = BitVec.ofNat 64 4096 := inv.rx21
    rw [hr21] at h104
    simpa only [show s104.getReg .x20 = BitVec.ofNat 64 (capMarkOff l) from rfl, bv64_ofNat_add, s105] using h104
  have haddr105 : s105.getReg .x29 + signExtend12 (56#12) =
      BitVec.ofNat 64 (68719475728 + 40 * (l + 1) + 16) := by
    have hr29 : s105.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) := inv.rx29
    rw [hr29, hse56, bv64_ofNat_add]; congr 1
  have h105 := step_LD (by omega) (rfl : s105.pc = pcAt 105)
    (rfl : openingInstr 105 = .base (.LD .x22 .x29 (56#12)))
    (by rw [haddr105]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s106 := (s105.setReg .x22 (BitVec.ofNat 64 (capMarkOff (l + 1)))).setPC (pcAt 106)
  have h105' : OpenRuns s105 1 1 s106 := by
    have hm : s105.getMem (BitVec.ofNat 64 (68719475728 + 40 * (l + 1) + 16)) = BitVec.ofNat 64 (capMarkOff (l + 1)) :=
      readOnly_getMem_data_markOff inv.ro (l + 1) (by omega)
    simpa only [haddr105, hm, s106] using h105
  have h106 := step_ADD (by omega) (rfl : s106.pc = pcAt 106)
    (rfl : openingInstr 106 = .base (.ADD .x22 .x21 .x22))
  let s107 := (s106.setReg .x22 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1)))).setPC (pcAt 107)
  have h106' : OpenRuns s106 1 1 s107 := by
    have hr21 : s106.getReg .x21 = BitVec.ofNat 64 4096 := inv.rx21
    rw [hr21] at h106
    simpa only [show s106.getReg .x22 = BitVec.ofNat 64 (capMarkOff (l + 1)) from rfl,
      bv64_ofNat_add, s107] using h106
  have h107 := step_SRLI (by omega) (rfl : s107.pc = pcAt 107)
    (rfl : openingInstr 107 = .base (.SRLI .x23 .x19 (1#6)))
  let s108 := (s107.setReg .x23 (BitVec.ofNat 64 (levelSize l / 2))).setPC (pcAt 108)
  have h107' : OpenRuns s107 1 1 s108 := by
    have hv : s107.getReg .x19 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (levelSize l / 2) := by
      change BitVec.ofNat 64 (levelSize l) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s108] using h107
  have h108 := step_ADDI (by omega) (rfl : s108.pc = pcAt 108)
    (rfl : openingInstr 108 = .base (.ADDI .x24 .x0 (0#12)))
  let s109 := (s108.setReg .x24 (BitVec.ofNat 64 0)).setPC (pcAt 109)
  have h108' : OpenRuns s108 1 1 s109 := by
    have hv : s108.getReg .x0 + signExtend12 (0#12) = BitVec.ofNat 64 0 := by
      change (0#64 : Word) + signExtend12 (0#12) = BitVec.ofNat 64 0; decide
    simpa only [hv, s109] using h108
  have hhdr : OpenRuns s 9 9 s109 :=
    (((((((h100'.trans h101').trans h102').trans h103').trans h104').trans h105').trans h106').trans h107').trans h108'
  have hpairInv0 : CapPairInv trapdoor positions step 0 fwdBytes tails s109 :=
    ⟨inv.rx2, inv.rx9, rfl, rfl, rfl, inv.rx21, rfl, rfl, rfl, inv.rx26, inv.rx29, inv.rx30,
     by simpa using inv.boundFwd, by simpa using inv.boundTails,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.capMarks, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  -- Pair loop induction
  have hpairLoop : ∀ q ≤ levelSize l / 2,
      let curF := fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l)
      let curT := tails ++ (List.range q).flatMap (capPairTails trapdoor positions l)
      ∃ steps sq, OpenRuns s109 steps steps sq ∧
        steps ≤ 10 * q + 64 * (∑ j ∈ Finset.range q, capPairFrontier positions l j) ∧
        sq.pc = (if q < levelSize l / 2 then pcAt 109 else pcAt 127) ∧
        CapPairInv trapdoor positions step q curF curT sq := by
    intro q hq
    induction q with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero,
        Finset.sum_range_zero, Nat.add_zero]
      exact ⟨0, s109, OpenRuns.refl s109, Nat.le_refl 0, by rw [if_pos (by omega : 0 < levelSize l / 2)]; rfl, hpairInv0⟩
    | succ q ih =>
      obtain ⟨st, sq, hrq, hstq, hpcq, invq⟩ := ih (by omega)
      have hpcq' : sq.pc = pcAt 109 := by simpa only [show q < levelSize l / 2 by omega, ite_true] using hpcq
      obtain ⟨st1, sq1, hr1, hst1, hpc1, inv1⟩ :=
        openRuns_cap_pair_step hstep (show q < levelSize (14 + step) / 2 from by change q < levelSize l / 2; omega) hpcq' invq
      have hst1' : st1 ≤ 10 + 64 * capPairFrontier positions l q := hst1
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
  obtain ⟨stPairs, s127, hrPairs, hstPairs, hpc127, inv127⟩ :=
    hpairLoop (levelSize l / 2) (Nat.le_refl _)
  have hpc127' : s127.pc = pcAt 127 := by simpa only [Nat.lt_irrefl, ite_false] using hpc127
  rw [sum_capPairFrontier_eq] at hstPairs
  have hfwd1_eq : fwdBytes ++ (List.range (levelSize l / 2)).flatMap (capPairFwd trapdoor positions l) =
      fwd1 := rfl
  have htails1_eq : tails ++ (List.range (levelSize l / 2)).flatMap (capPairTails trapdoor positions l) =
      tails1 := rfl
  rw [hfwd1_eq, htails1_eq] at inv127
  have hcur127 : CapLevelMarks s127 positions l := inv127.curMarks
  have hboundF127 : fwd1.length ≤ 470 * positions.card +
      29 * (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (14 + k)) := by
    have h1 : fwd1.length ≤ 470 * positions.card +
        29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
              (∑ j ∈ Finset.range (levelSize (14 + step) / 2), capPairFrontier positions (14 + step) j)) :=
      inv127.boundFwd
    rw [sum_capPairFrontier_eq] at h1
    rw [Finset.sum_range_succ]; exact h1
  have hboundT127 : tails1.length ≤ 12 * positions.card +
      (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (14 + k)) := by
    have h1 : tails1.length ≤ 12 * positions.card +
        ((∑ k ∈ Finset.range step, levelFrontierCount positions (14 + k)) +
         (∑ j ∈ Finset.range (levelSize (14 + step) / 2), capPairFrontier positions (14 + step) j)) :=
      inv127.boundTails
    rw [sum_capPairFrontier_eq] at h1
    rw [Finset.sum_range_succ]; exact h1
  -- Odd-promotion check: 127..133 -> 134
  have h127 := step_ANDI (by omega) hpc127' (rfl : openingInstr 127 = .base (.ANDI .x6 .x19 (1#12)))
  let s128 := (s127.setReg .x6 (BitVec.ofNat 64 (levelSize l % 2))).setPC (pcAt 128)
  have h127' : OpenRuns s127 1 1 s128 := by
    rw [inv127.rx19, bv64_and1 (levelSize l) (by omega)] at h127; exact h127
  have hto134 : ∃ n134 s134, OpenRuns s128 n134 n134 s134 ∧
      n134 ≤ (if levelSize l % 2 = 0 then 1 else 6) ∧
      s134.pc = pcAt 134 ∧
      s134.getReg .x2 = BitVec.ofNat 64 68719475728 ∧
      s134.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s134.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s134.getReg .x26 = BitVec.ofNat 64 11341403200 ∧
      s134.getReg .x29 = BitVec.ofNat 64 (68719475728 + 40 * l) ∧
      s134.getReg .x30 = BitVec.ofNat 64 (68719475728 + 40 * 24) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s134 ∧
      WriterState s134 fwd1 ∧
      TailState s134 tails1 ∧
      CapLevelMarks s134 positions (l + 1) := by
    by_cases heven_sz : levelSize l % 2 = 0
    · have h128 := step_BEQ_taken (by omega) (rfl : s128.pc = pcAt 128)
        (rfl : openingInstr 128 = .base (.BEQ .x6 .x0 (24#13)))
        (by change BitVec.ofNat 64 (levelSize l % 2) = 0#64; rw [heven_sz])
        (by decide : pcAt 128 + signExtend13 (24#13) = pcAt 134)
      refine ⟨1, s128.setPC (pcAt 134), h128, by rw [if_pos heven_sz], rfl,
        inv127.rx2, inv127.rx9, inv127.rx21, inv127.rx26, inv127.rx29, inv127.rx30,
        inv127.ro, inv127.writer.of_eq, inv127.tail.of_eq, ?_⟩
      intro idx hidx
      exact inv127.nextMarks idx (by omega)
    · have h128 := step_BEQ_not_taken (by omega) (rfl : s128.pc = pcAt 128)
        (rfl : openingInstr 128 = .base (.BEQ .x6 .x0 (24#13)))
        (by change BitVec.ofNat 64 (levelSize l % 2) ≠ BitVec.ofNat 64 0
            exact bv64_ofNat_ne (by omega) (by decide) heven_sz)
      let s129 := s128.setPC (pcAt 129)
      have h129 := step_SLLI (by omega) (rfl : s129.pc = pcAt 129)
        (rfl : openingInstr 129 = .base (.SLLI .x7 .x23 (1#6)))
      let s130 := (s129.setReg .x7 (BitVec.ofNat 64 (2 * (levelSize l / 2)))).setPC (pcAt 130)
      have h129' : OpenRuns s129 1 1 s130 := by
        have hr23 : s129.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) := inv127.rx23
        have hv : s129.getReg .x23 <<< (1#6 : BitVec 6).toNat =
            BitVec.ofNat 64 (2 * (levelSize l / 2)) := by
          rw [hr23]; change BitVec.ofNat 64 (levelSize l / 2) <<< 1 = _
          rw [bv64_shl]; congr 1; omega
        simpa only [hv, s130] using h129
      have h130 := step_ADD (by omega) (rfl : s130.pc = pcAt 130)
        (rfl : openingInstr 130 = .base (.ADD .x7 .x20 .x7))
      let s131 := (s130.setReg .x7 (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * (levelSize l / 2)))).setPC
        (pcAt 131)
      have h130' : OpenRuns s130 1 1 s131 := by
        have hr20 : s130.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) := inv127.rx20
        rw [hr20] at h130
        simpa only [show s130.getReg .x7 = BitVec.ofNat 64 (2 * (levelSize l / 2)) from rfl,
          bv64_ofNat_add, s131] using h130
      have haddr131 : s131.getReg .x7 + signExtend12 (0#12) =
          BitVec.ofNat 64 (4096 + capMarkOff l + 2 * (levelSize l / 2)) := by
        change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
      have h131 := step_LBU (by omega) (rfl : s131.pc = pcAt 131)
        (rfl : openingInstr 131 = .base (.LBU .x8 .x7 (0#12)))
        (by rw [haddr131]; exact accessValid_ofNat _ 1 (by omega) (by omega))
      set mProm := capMark positions l (2 * (levelSize l / 2))
      let s132 := (s131.setReg .x8 (if mProm then 1#64 else 0#64)).setPC (pcAt 132)
      have h131' : OpenRuns s131 1 1 s132 := by
        have hb : s131.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * (levelSize l / 2))) =
            if mProm then 1#8 else 0#8 := hcur127 (2 * (levelSize l / 2)) (by omega)
        simpa only [haddr131, hb, bool_byte_zeroExtend mProm, s132] using h131
      have h132 := step_ADD (by omega) (rfl : s132.pc = pcAt 132)
        (rfl : openingInstr 132 = .base (.ADD .x7 .x22 .x23))
      let s133 := (s132.setReg .x7 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + levelSize l / 2))).setPC
        (pcAt 133)
      have h132' : OpenRuns s132 1 1 s133 := by
        have hr22 : s132.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) := inv127.rx22
        have hr23 : s132.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) := inv127.rx23
        rw [hr22, hr23, bv64_ofNat_add] at h132; exact h132
      have haddr133 : s133.getReg .x7 + signExtend12 (0#12) =
          BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + levelSize l / 2) := by
        change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
      have h133 := step_SB (by omega) (rfl : s133.pc = pcAt 133)
        (rfl : openingInstr 133 = .base (.SB .x7 .x8 (0#12)))
        (by rw [haddr133]; exact accessValid_ofNat _ 1 (by omega) (by omega))
      let s134 := (s133.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + levelSize l / 2))
        (if mProm then 1#8 else 0#8)).setPC (pcAt 134)
      have h133' : OpenRuns s133 1 1 s134 := by
        simpa only [haddr133, show s133.getReg .x8 = if mProm then 1#64 else 0#64 from rfl,
          bool_word_truncate8 mProm, s134] using h133
      have hcard := positions_card_le positions
      have hcap342 := cap_frontier_le_342 positions
      have hfront_le : (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (14 + k)) ≤ 342 := by
        have h1 : (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (14 + k)) ≤
            capFrontierCount positions := by
          unfold capFrontierCount
          exact sum_range_le_of_le (fun k => levelFrontierCount positions (14 + k)) (by omega)
        omega
      have hpres134 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s134.getReg r = s127.getReg r :=
        fun r h6 h7 h8 => by
          simp only [s134, s133, s132, s131, s130, s129, s128,
            MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x7 r (Ne.symm h7), getReg_setReg_ne' .x8 r (Ne.symm h8),
            getReg_setReg_ne' .x6 r (Ne.symm h6)]
      have hmem134 : ∀ a, s134.getByte a =
          (s127.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + levelSize l / 2))
            (if mProm then 1#8 else 0#8)).getByte a := fun a => by
        simp only [s134, s133, s132, s131, s130, s129, s128, getByte_setPC, getByte_setReg]; rfl
      refine ⟨6, s134, ((((h128.trans h129').trans h130').trans h131').trans h132').trans h133',
        by rw [if_neg heven_sz], rfl,
        by rw [hpres134 .x2 (by decide) (by decide) (by decide)]; exact inv127.rx2,
        by rw [hpres134 .x9 (by decide) (by decide) (by decide)]; exact inv127.rx9,
        by rw [hpres134 .x21 (by decide) (by decide) (by decide)]; exact inv127.rx21,
        by rw [hpres134 .x26 (by decide) (by decide) (by decide)]; exact inv127.rx26,
        by rw [hpres134 .x29 (by decide) (by decide) (by decide)]; exact inv127.rx29,
        by rw [hpres134 .x30 (by decide) (by decide) (by decide)]; exact inv127.rx30,
        ?_, ?_, ?_, ?_⟩
      · intro a ha; simp only [s134, MachineState.getMem_setPC]
        exact readOnly_setByte_cap (4096 + capMarkOff (l + 1) + levelSize l / 2) _ inv127.ro
          (by omega) (by omega) a ha
      · have hw' := writerState_setByte_outside (4096 + capMarkOff (l + 1) + levelSize l / 2)
          (if mProm then 1#8 else 0#8) inv127.writer (by omega) (Or.inl (by omega)) (by omega)
        exact ⟨by rw [hpres134 .x25 (by decide) (by decide) (by decide)]; exact inv127.writer.rx25,
          by rw [hpres134 .x13 (by decide) (by decide) (by decide)]; exact inv127.writer.rx13,
          by rw [hpres134 .x14 (by decide) (by decide) (by decide)]; exact inv127.writer.rx14,
          fun j hj => by rw [hpres134 .x12 (by decide) (by decide) (by decide)]; exact inv127.writer.wbufLo j hj,
          fun j h1 h2 => by rw [hpres134 .x12 (by decide) (by decide) (by decide)]; exact inv127.writer.wbufHi j h1 h2,
          fun j hj => by rw [hmem134]; exact hw'.memDwords j hj⟩
      · have htb : tailBufBase = 20000000000 := rfl
        have ht' := tailState_setByte_outside (4096 + capMarkOff (l + 1) + levelSize l / 2)
          (if mProm then 1#8 else 0#8) inv127.tail (by omega) (by omega)
        exact ⟨inv127.tail.valid,
          by rw [hpres134 .x31 (by decide) (by decide) (by decide)]; exact inv127.tail.rx31,
          by rw [hpres134 .x15 (by decide) (by decide) (by decide)]; exact inv127.tail.rx15,
          by rw [hpres134 .x16 (by decide) (by decide) (by decide)]; exact inv127.tail.rx16,
          by rw [hpres134 .x17 (by decide) (by decide) (by decide)]; exact inv127.tail.rx17,
          fun j hj => by rw [hmem134]; exact ht'.memTail j hj⟩
      · intro idx hidx
        rw [hmem134, set_byte_read]
        by_cases hlast : idx = levelSize l / 2
        · subst hlast
          have hge : ¬ (2 * (levelSize l / 2) + 1 < levelSize l) := by omega
          have hlt : 2 * (levelSize l / 2) < levelSize l := by omega
          rw [if_pos rfl]
          change (if capMark positions l (2 * (levelSize l / 2)) then 1#8 else 0#8) = _
          rw [capMark_succ positions l (levelSize l / 2) (by omega), if_neg hge, if_pos hlt]
        · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
          exact inv127.nextMarks idx (by omega)
  obtain ⟨n134, s134, hr134, hn134, hpc134, hx2, hx9, hx21, hx26, hx29, hx30,
      hro134, hw134, ht134, hcm134⟩ := hto134
  -- Latch: 134..135
  have h134 := step_ADDI (by omega) hpc134 (rfl : openingInstr 134 = .base (.ADDI .x29 .x29 (40#12)))
  let s135 := (s134.setReg .x29 (BitVec.ofNat 64 (68719475728 + 40 * (14 + (step + 1))))).setPC (pcAt 135)
  have h134' : OpenRuns s134 1 1 s135 := by
    have hv : s134.getReg .x29 + signExtend12 (40#12) =
        BitVec.ofNat 64 (68719475728 + 40 * (14 + (step + 1))) := by
      rw [hx29, hse40, bv64_ofNat_add]; congr 1
    simpa only [hv, s135] using h134
  have hmkInv : ∀ pc, CapLvlInv trapdoor positions (step + 1) fwd1 tails1 (s135.setPC pc) := fun pc =>
    ⟨hx2, hx9, hx21, hx26, rfl, hx30, hboundF127, hboundT127, hro134, hw134.of_eq, ht134.of_eq,
     by rw [show 14 + (step + 1) = l + 1 by omega]; exact hcm134⟩
  have hstep_bd : 9 + stPairs + 1 + n134 + 1 + 1 ≤
      9 + 10 * (levelSize l / 2) + 64 * levelFrontierCount positions l +
      (if levelSize l % 2 = 0 then 4 else 9) := by
    by_cases hmod : levelSize l % 2 = 0
    · rw [if_pos hmod] at hn134 ⊢; omega
    · rw [if_neg hmod] at hn134 ⊢; omega
  by_cases hmore : step + 1 < 10
  · have h135 := step_BNE_taken (by omega) (rfl : s135.pc = pcAt 135)
      (rfl : openingInstr 135 = .base (.BNE .x29 .x30 (8052#13)))
      (by change BitVec.ofNat 64 (68719475728 + 40 * (14 + (step + 1))) ≠ s134.getReg .x30
          rw [hx30]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 135 + signExtend13 (8052#13) = pcAt 100)
    exact ⟨9 + stPairs + 1 + n134 + 1 + 1, s135.setPC (pcAt 100),
      ((((hhdr.trans hrPairs).trans h127').trans hr134).trans h134').trans h135,
      hstep_bd, by rw [if_pos hmore]; rfl, hmkInv (pcAt 100)⟩
  · have hdone : 14 + (step + 1) = 24 := by omega
    have h135 := step_BNE_not_taken (by omega) (rfl : s135.pc = pcAt 135)
      (rfl : openingInstr 135 = .base (.BNE .x29 .x30 (8052#13)))
      (by change BitVec.ofNat 64 (68719475728 + 40 * (14 + (step + 1))) = s134.getReg .x30
          rw [hx30, hdone])
    exact ⟨9 + stPairs + 1 + n134 + 1 + 1, s135.setPC (pcAt 136),
      ((((hhdr.trans hrPairs).trans h127').trans hr134).trans h134').trans h135,
      hstep_bd, by rw [if_neg hmore]; rfl, hmkInv (pcAt 136)⟩

private theorem cap_const_cycles_sum :
    (∑ step ∈ Finset.range 10,
      (9 + 10 * (levelSize (14 + step) / 2) + if levelSize (14 + step) % 2 = 0 then 4 else 9)) =
      6975 := by
  decide

private theorem openRuns_cap_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {recFwd : List Byte} {recTails : List TailChunk} {s98 : MachineState}
    (hpc : s98.pc = pcAt 98)
    (hx2 : s98.getReg .x2 = BitVec.ofNat 64 68719475728)
    (hx9 : s98.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx21 : s98.getReg .x21 = BitVec.ofNat 64 4096)
    (hx26 : s98.getReg .x26 = BitVec.ofNat 64 11341403200)
    (hbdF : recFwd.length ≤ 470 * positions.card)
    (hbdT : recTails.length ≤ 12 * positions.card)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s98)
    (hw : WriterState s98 recFwd)
    (ht : TailState s98 recTails)
    (hcap14 : CapLevelMarks s98 positions 14) :
    let allFwd := recFwd ++ capFrontierFwd (tdNode trapdoor) positions
    let allTails := recTails ++ capFrontierTails (tdNode trapdoor) positions
    ∃ steps s136, OpenRuns s98 steps steps s136 ∧
      steps ≤ 28865 ∧
      s136.pc = pcAt 136 ∧
      s136.getReg .x26 = BitVec.ofNat 64 11341403200 ∧
      WriterState s136 allFwd ∧
      TailState s136 allTails := by
  intro allFwd allTails
  have hse560 : signExtend12 (560#12) = BitVec.ofNat 64 560 := by decide
  have hse960 : signExtend12 (960#12) = BitVec.ofNat 64 960 := by decide
  have h98 := step_ADDI (by omega) hpc (rfl : openingInstr 98 = .base (.ADDI .x29 .x2 (560#12)))
  let s99 := (s98.setReg .x29 (BitVec.ofNat 64 (68719475728 + 40 * 14))).setPC (pcAt 99)
  have h98' : OpenRuns s98 1 1 s99 := by
    rw [hx2, hse560, bv64_ofNat_add] at h98; exact h98
  have h99 := step_ADDI (by omega) (rfl : s99.pc = pcAt 99)
    (rfl : openingInstr 99 = .base (.ADDI .x30 .x2 (960#12)))
  let s100 := (s99.setReg .x30 (BitVec.ofNat 64 (68719475728 + 40 * 24))).setPC (pcAt 100)
  have h99' : OpenRuns s99 1 1 s100 := by
    have hr2 : s99.getReg .x2 = BitVec.ofNat 64 68719475728 := hx2
    rw [hr2, hse960, bv64_ofNat_add] at h99; exact h99
  have hinv0 : CapLvlInv trapdoor positions 0 recFwd recTails s100 :=
    ⟨hx2, hx9, hx21, hx26, rfl, rfl, by simpa using hbdF, by simpa using hbdT, hro, hw.of_eq, ht.of_eq, hcap14⟩
  have hloop : ∀ k ≤ 10,
      let curF := recFwd ++ (List.range k).flatMap (fun step =>
        capLevelFrontierFwd (tdNode trapdoor) positions (14 + step))
      let curT := recTails ++ (List.range k).flatMap (fun step =>
        capLevelFrontierTails (tdNode trapdoor) positions (14 + step))
      ∃ steps sk, OpenRuns s100 steps steps sk ∧
        steps ≤ (∑ step ∈ Finset.range k,
          (9 + 10 * (levelSize (14 + step) / 2) + if levelSize (14 + step) % 2 = 0 then 4 else 9)) +
          64 * (∑ step ∈ Finset.range k, levelFrontierCount positions (14 + step)) ∧
        sk.pc = (if k < 10 then pcAt 100 else pcAt 136) ∧
        CapLvlInv trapdoor positions k curF curT sk := by
    intro k hk
    induction k with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Finset.sum_range_zero,
        Nat.mul_zero, Nat.add_zero]
      exact ⟨0, s100, OpenRuns.refl s100, Nat.le_refl 0, by rw [if_pos (by omega : 0 < 10)]; rfl, hinv0⟩
    | succ k ih =>
      obtain ⟨st, sk, hrk, hstk, hpck, invk⟩ := ih (by omega)
      have hpck' : sk.pc = pcAt 100 := by simpa only [show k < 10 by omega, ite_true] using hpck
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
  obtain ⟨stCap, s136, hrCap, hstCap, hpc136, inv136⟩ := hloop 10 (Nat.le_refl 10)
  have hpc136' : s136.pc = pcAt 136 := by simpa only [Nat.lt_irrefl, ite_false] using hpc136
  have hconst := cap_const_cycles_sum
  have hcap342 := cap_frontier_le_342 positions
  have hfront_eq : (∑ step ∈ Finset.range 10, levelFrontierCount positions (14 + step)) =
      capFrontierCount positions := rfl
  rw [hconst, hfront_eq] at hstCap
  have hallF_eq : recFwd ++ (List.range 10).flatMap (fun step =>
      capLevelFrontierFwd (tdNode trapdoor) positions (14 + step)) = allFwd := rfl
  have hallT_eq : recTails ++ (List.range 10).flatMap (fun step =>
      capLevelFrontierTails (tdNode trapdoor) positions (14 + step)) = allTails := rfl
  rw [hallF_eq, hallT_eq] at inv136
  exact ⟨2 + stCap, s136, (h98'.trans h99').trans hrCap, by omega, hpc136',
    inv136.rx26, inv136.writer, inv136.tail⟩

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
      (positions.card = BATCH → exec.cycles ≤ 160000) := by
  have hsteps : submission.steps .opening = 274877906944 := rfl
  rw [submission_run_opening submission trapdoor positions]
  by_cases hempty : positions.card = 0
  · obtain ⟨s5, hr5, hpc5, _, _, _, _, _, hx27, _⟩ := openRuns_entry_prefix trapdoor positions
    have h5 := step_BEQ_taken (by omega) hpc5
      (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (604#13)))
      (by rw [hx27, hempty]; rfl)
      (by decide : pcAt 5 + signExtend13 (604#13) = pcAt 156)
    let s156 := s5.setPC (pcAt 156)
    obtain ⟨sHalt, hrepi, hpcH, hx5H, hx10H, hx11H, _⟩ :=
      openRuns_empty_epilogue (rfl : s156.pc = pcAt 156)
    have hexec := OpenRuns.halt (haltIdx := 159) (totalFuel := submission.steps .opening)
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
    obtain ⟨s31, hr31, hpc31, hx2, hx9, hx12, hx13, hx14, hx15, hx16, hx17, hx18, hx19, hx20,
        hx21, hx24, hx25, hx26, hx27, hx31, hmem31⟩ :=
      openRuns_entry_nonzero trapdoor positions hempty
    have hro31 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s31 := by
      intro a _; change s31.mem a = _; rw [hmem31]; rfl
    have hw0 : WriterState s31 [] :=
      ⟨by simpa using hx25, by simpa using hx13, by simpa using hx14,
       fun _ hj => absurd hj (Nat.not_lt_zero _),
       fun j _ hj => by rw [hx12]; apply BitVec.eq_of_getLsbD_eq; intro b _; simp,
       fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    have ht0 : TailState s31 [] :=
      ⟨(fun _ h => by cases h), hx31, by simpa using hx15, by simpa using hx16, by simpa using hx17,
       fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    have hinv0 : RecInv trapdoor positions 0 [] [] s31 :=
      ⟨hx2, hx9, hx18, hx19, hx20, hx21, by simpa using hx24, hx26, by simpa using hx27,
       hro31, hw0, ht0,
       fun c hc => by
         change extractByte (s31.mem _) _ = _
         rw [hmem31]
         have hz := opening_initial_zero_low trapdoor positions (4096 + c) (by omega)
         have hfalse : capMark14Prefix positions 0 c = false := by simp [capMark14Prefix]
         rw [hfalse, if_neg Bool.false_ne_true]; exact hz⟩
    obtain ⟨stRec, cyRec, s98, hrRec, hstRec, hcyRec, hpc98, hx2_98, hx9_98, hx21_98,
        hx26_98, hbdF98, hbdT98, hro98, hw98, ht98, hcap14⟩ :=
      openRuns_rec_all hpos hpc31 hinv0
    obtain ⟨stCap, s136, hrCap, hstCap, hpc136, hx26_136, hw136, ht136⟩ :=
      openRuns_cap_all hpc98 hx2_98 hx9_98 hx21_98 hx26_98 hbdF98 hbdT98
        hro98 hw98 ht98 hcap14
    set allFwd := referenceProofFwd (tdNode trapdoor) (tdSalt trapdoor) positions
    set allTails := referenceProofTails (tdNode trapdoor) positions
    change WriterState s136 allFwd at hw136
    change TailState s136 allTails at ht136
    have hlen_cap := referenceProof_length_le_cap (tdNode trapdoor) (tdSalt trapdoor) positions
    have htails_le : allTails.length ≤ 12 * positions.card + 342 :=
      referenceProofTails_length_le (tdNode trapdoor) positions
    have htails_bits : totalTailBits allTails ≤ 37 * positions.card + 6 * capFrontierCount positions :=
      referenceProofTails_bits_le (tdNode trapdoor) positions
    have hcap342 := cap_frontier_le_342 positions
    have href_eq : allFwd ++ packVarBitsRev allTails =
        referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions := by
      unfold referenceProof; rw [if_neg hempty]
    have hlen_sum : allFwd.length + (packVarBits allTails).length ≤ 8556390424 := by
      have h1 : (allFwd ++ packVarBitsRev allTails).length ≤ 8556390424 := by
        rw [href_eq]; exact hlen_cap
      simpa only [List.length_append, packVarBitsRev, List.length_reverse] using h1
    obtain ⟨stFl, s143, hrFl, hstFl, hpc143, hx10_143, hx26_143, hpr143, ht143⟩ :=
      openRuns_flush_wbuf hpc136 hx26_136 (by omega) (by omega) hw136 ht136
    obtain ⟨stFt, s146, hrFt, hstFt, hpc146, hx10_146, hx26_146, hx31_146, hx15_146, hpr146, htb146⟩ :=
      openRuns_flush_tail hpc143 hx10_143 hx26_143 (by omega) (by omega) hpr143 ht143
    obtain ⟨s152, hrRev, hpc152, hx10_152, hx26_152, hpr152⟩ :=
      openRuns_rev_tail hpc146 hx10_146 hx26_146 hx31_146 hx15_146 hlen_sum hpr146 htb146
    have hrev_eq : allFwd ++ (packVarBits allTails).reverse =
        referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions := href_eq
    rw [hrev_eq] at hx10_152 hpr152
    obtain ⟨sHalt, hrFin, hpcH, hx5H, hx10H, hx11H, hmemH⟩ :=
      openRuns_finish hpc152 hx10_152 hx26_152
    have htot := (((((hr31.trans hrRec).trans hrCap).trans hrFl).trans hrFt).trans hrRev).trans hrFin
    have hpack_len : (packVarBits allTails).length = (totalTailBits allTails + 7) / 8 :=
      (packVarBits_spec allTails (referenceProofTails_valid (tdNode trapdoor) positions)).1
    have hpack_max : (packVarBits allTails).length ≤ (37 * 16777216 + 6 * 342 + 7) / 8 := by
      rw [hpack_len]; exact Nat.div_le_div_right (by omega)
    have hfuel : 31 + stRec + stCap + stFl + stFt + (1 + 5 * (packVarBits allTails).length) + 3 + 1 ≤
        submission.steps .opening := by
      rw [hsteps]; omega
    have hexec := OpenRuns.halt (haltIdx := 155) (totalFuel := submission.steps .opening)
      htot (by omega) rfl hpcH hx5H hx10H hfuel
    refine ⟨{ exit := .success, state := sHalt,
              cycles := 31 + cyRec + stCap + stFl + stFt + (1 + 5 * (packVarBits allTails).length) + 3 + 1,
              oracleCalls := 0 },
      hexec, rfl, rfl, ?_, ?_, ?_⟩
    · change (sHalt.getReg .x11).toNat = _
      have hlen_cap' : (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions).length ≤ 8556390424 := hlen_cap
      rw [hx11H, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro j hj
      change extractByte (sHalt.mem _) _ = _
      rw [hmemH]
      exact hpr152 j hj
    · intro hbatch
      change positions.card = 128 at hbatch
      have hpack_128 : (packVarBits allTails).length ≤ 849 := by
        rw [hpack_len]
        have h1 : totalTailBits allTails ≤ 37 * 128 + 6 * 342 := by
          rw [hbatch] at htails_bits; omega
        have h2 := Nat.div_le_div_right (c := 8) (show totalTailBits allTails + 7 ≤ 37 * 128 + 6 * 342 + 7 by omega)
        omega
      change 31 + cyRec + stCap + stFl + stFt + (1 + 5 * (packVarBits allTails).length) + 3 + 1 ≤ 160000
      omega

end CommitGolfCandidate
