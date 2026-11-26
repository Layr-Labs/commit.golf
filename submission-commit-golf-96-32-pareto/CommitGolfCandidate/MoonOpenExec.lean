import CommitGolfCandidate.MoonMemory

/-! Exact deterministic symbolic execution of the 203-word B1-Ultra-121 `opening` image:
- Pass 0 (`24..58`): packs bit 120 of each opened 121-bit salt into `packSaltTopBits`
- Pass 1 (`59..81`): emits 15 low salt bytes (`emit15`) + 16 uniform 238-bit siblings (`L0..L15`, `emit29_t6`)
  and marks `capMark[16][i >>> 16] = 1`
- Pass 2 (`82..111`): pure-binary cap frontier across 8 levels `L16..L23` (`emit29_t6`, ≤ 128 frontier nodes)
- Epilogue (`112..131`): flushes forward dword buffer + tail byte, appends reversed 6-bit tail stream
  (`pack6BitsRev`), and halts with exact proof length in `x11` (`≤ 66,672 B` and `≤ 136,000` cycles at `k = 128`). -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-! ### 1. Program Counter, Trapdoor Views, and Deterministic Multi-Step Relation -/

private def pcAt (idx : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * idx)

def tdNode (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (l idx : Nat) : Digest :=
  trapdoor.extractLsb' (8 * (levelBase l + nodeOffset l idx)) 256

def tdSalt (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) : Salt121 :=
  trapdoor.extractLsb' (8 * saltOff i) 121

/-- Deterministic multi-step execution of ordinary instructions in the opening image. -/
private def OpenRuns (s : MachineState) (steps cycles : Nat) (s' : MachineState) : Prop :=
  ∀ fuel : Nat,
    execute (submission.image .opening) (steps + fuel) s true =
      (do let result ← execute (submission.image .opening) fuel s' true
          return result.charge cycles 0)

private theorem OpenRuns.refl (s : MachineState) : OpenRuns s 0 0 s := by
  intro fuel; simp [Execution.charge]

private theorem OpenRuns.trans {s s1 s2 : MachineState} {n1 n2 c1 c2 : Nat}
    (h1 : OpenRuns s n1 c1 s1) (h2 : OpenRuns s1 n2 c2 s2) :
    OpenRuns s (n1 + n2) (c1 + c2) s2 := by
  intro fuel
  rw [Nat.add_assoc, h1 (n2 + fuel), h2 fuel]
  simp only [bind_assoc, pure_bind]
  congr 1; funext result
  simp [Execution.charge, Nat.add_assoc]

private theorem OpenRuns.step {s s' : MachineState} {instr : Instruction}
    (hf : fetch (submission.image .opening) s = some instr)
    (hs : ordinaryStep s instr = some s') :
    OpenRuns s 1 (instructionCycles instr) s' := by
  intro fuel
  rw [Nat.add_comm 1 fuel]
  exact execute_ordinary_step (submission.image .opening) instr s s' fuel true hf hs

private theorem OpenRuns.halt {s0 sHalt : MachineState} {haltIdx steps cycles totalFuel : Nat}
    (hrun : OpenRuns s0 steps cycles sHalt)
    (hhi : haltIdx < 203)
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

/-! ### 2. MachineState, BitVec, Pack6, Salt-Top, and List Helpers -/

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
  rw [← BitVec.ofNat_add]; congr 1

private theorem and_not_one_of_even (n : Nat) (heven : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  have hlow : BitVec.ofNat 64 n &&& 1#64 = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change (n % 2 ^ 64) &&& (2 ^ 1 - 1) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]; omega
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

private theorem bv64_ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro heq
  have hn := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hn
  exact hne hn

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
    rw [Nat.and_two_pow_sub_one_eq_mod]; omega
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
    rw [hw0]; simp [hb, hle, hnotlt, hlt64, hsub]

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
  apply BitVec.eq_of_getLsbD_eq; intro b hb; simp [BitVec.truncate, hb]

private theorem word_ushr8_extractLsb' (w : Word) (j : Nat) (hj : j + 1 < 8) :
    (w >>> 8).extractLsb' (8 * j) 8 = w.extractLsb' (8 * (j + 1)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ushiftRight, hb, decide_true, Bool.true_and]
  congr 1; omega

private theorem byte_zeroExtend_extractByte (b : Byte) (j : Nat) (hj : j < 8) :
    (b.zeroExtend 64).extractLsb' (8 * j) 8 = if j = 0 then b else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and]
  by_cases hj0 : j = 0
  · subst hj0
    simp only [ite_true, Nat.mul_zero, Nat.zero_add, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
      show k < 64 by omega, decide_true, Bool.true_and]
  · simp only [hj0, ite_false, BitVec.getLsbD_zero, BitVec.zeroExtend, BitVec.getLsbD_setWidth,
      show 8 * j + k < 64 by omega, decide_true, Bool.true_and]
    have hlt : b.toNat < 2 ^ (8 * j + k) :=
      Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by decide) (by omega))
    simp [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq, Nat.div_eq_of_lt hlt]

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
  · have hpow : 64 ≤ 2 ^ b := by
      have h1 : 2 ^ 6 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 2 ^ 6 = 64 := by decide
      omega
    have hm : (63#64 : Word).getLsbD b = false := by
      simp only [BitVec.getLsbD_ofNat, hb, decide_true, Bool.true_and, Nat.testBit_eq_decide_div_mod_eq]
      have hdiv : 63 / 2 ^ b = 0 := Nat.div_eq_of_lt (by omega)
      simp [hdiv]
    have hrhs : (BitVec.ofNat 64 (tail6 d).toNat).getLsbD b = false := by
      simp only [BitVec.getLsbD_ofNat, hb, decide_true, Bool.true_and, Nat.testBit_eq_decide_div_mod_eq]
      have hlt64 : (tail6 d).toNat < 64 := (tail6 d).isLt
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
  unfold pack6Step; dsimp only
  have ht : t.toNat < 64 := t.isLt
  have hbuf' : buf + t.toNat * 2 ^ cnt < 2 ^ (cnt + 6) := by
    rw [Nat.pow_add, show 2 ^ 6 = 64 by decide]
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
  · dsimp only; exact ⟨by omega, hbuf', by omega⟩

private theorem pack6_foldl_bounds_aux (tails : List (BitVec 6)) :
    ∀ acc buf cnt n,
      cnt < 8 → buf < 2 ^ cnt → 8 * acc.length + cnt = 6 * n →
      let st := tails.foldl pack6Step (acc, buf, cnt)
      st.2.2 < 8 ∧ st.2.1 < 2 ^ st.2.2 ∧ 8 * st.1.length + st.2.2 = 6 * (n + tails.length) := by
  induction tails with
  | nil => intro acc buf cnt n hcnt hbuf hbits; simpa using And.intro hcnt (And.intro hbuf hbits)
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
  unfold tailAccLen; rw [List.foldl_append]; exact pack6_foldl_acc_mono b _

private theorem tailAccLen_le_pack6Bits (tails : List (BitVec 6)) :
    tailAccLen tails ≤ (pack6Bits tails).length := by
  unfold tailAccLen pack6Bits pack6Finish
  rcases tails.foldl pack6Step ([], 0, 0) with ⟨acc, buf, cnt⟩
  dsimp only; split_ifs <;> simp

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
    · obtain ⟨u, hu, heq⟩ := ih hrest; exact ⟨u + 1, by simp; omega, heq⟩

private theorem sum_range_le_of_le (f : Nat → Nat) {a b : Nat} (h : a ≤ b) :
    (∑ i ∈ Finset.range a, f i) ≤ ∑ i ∈ Finset.range b, f i := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha; exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · rw [Finset.sum_range_succ]; exact Nat.le_trans (ih hab) (Nat.le_add_right _ _)
    · have ha : a = b + 1 := by omega
      subst ha; exact Nat.le_refl _

private theorem positions_card_le (positions : Positions) : positions.card ≤ 16777216 := by
  have h := Finset.card_le_univ positions; rw [Fintype.card_fin] at h; exact h

private theorem levelSize_le_max (l : Nat) (hl : l ≤ 24) : levelSize l ≤ 16777216 := by
  interval_cases l <;> decide

private theorem nodeOffset_lt_treeBytes (l idx : Nat) (hl : l ≤ 24) (hidx : idx < levelSize l) :
    levelBase l + nodeOffset l idx + 32 ≤ treeBytes := by
  by_cases h24 : l < 24
  · have hg := gapOffset_lt_levelBytes l idx h24 hidx
    have hb := levelBase_bound l hl
    unfold nodeOffset; omega
  · have hl24 : l = 24 := by omega
    subst hl24
    rw [levelSize_24] at hidx
    have hidx0 : idx = 0 := by omega
    subst hidx0
    decide

private theorem nodeOffset_align8 (l idx : Nat) : nodeOffset l idx % 8 = 0 := by
  unfold nodeOffset gapOffset; omega

private theorem levelBase_align8 (l : Nat) (hl : l ≤ 24) : levelBase l % 8 = 0 := by
  interval_cases l <;> decide

private theorem saltOff_align8 (i : Index) : saltOff i % 8 = 0 := by
  unfold saltOff; rw [saltsOff_eq]; omega

private theorem capMarkOff_step_disjoint (l : Nat) (hl1 : 16 ≤ l) (hl2 : l ≤ 23) :
    capMarkOff l + levelSize l ≤ capMarkOff (l + 1) := by
  interval_cases l <;> decide

private def partialSaltTopByte (salts : Index → Salt121) (positions : Positions) (b r : Nat) : Nat :=
  ∑ m ∈ Finset.range r, saltTopBitAt salts positions (8 * b + m) * 2 ^ m

private theorem partialSaltTopByte_zero (salts : Index → Salt121) (positions : Positions) (b : Nat) :
    partialSaltTopByte salts positions b 0 = 0 := by
  simp [partialSaltTopByte]

private theorem partialSaltTopByte_succ (salts : Index → Salt121) (positions : Positions) (b r : Nat) :
    partialSaltTopByte salts positions b (r + 1) =
      partialSaltTopByte salts positions b r + saltTopBitAt salts positions (8 * b + r) * 2 ^ r := by
  unfold partialSaltTopByte; rw [Finset.sum_range_succ]

private theorem partialSaltTopByte_lt (salts : Index → Salt121) (positions : Positions) (b r : Nat) :
    partialSaltTopByte salts positions b r < 2 ^ r := by
  induction r with
  | zero => simp [partialSaltTopByte]
  | succ r ih =>
    rw [partialSaltTopByte_succ, Nat.pow_succ]
    have hbit : saltTopBitAt salts positions (8 * b + r) ≤ 1 := by
      unfold saltTopBitAt; split_ifs <;> omega
    have hm := Nat.mul_le_mul_right (2 ^ r) hbit
    omega

private theorem partialSaltTopByte_8 (salts : Index → Salt121) (positions : Positions) (b : Nat) :
    BitVec.ofNat 8 (partialSaltTopByte salts positions b 8) = saltTopByte salts positions b := rfl

private theorem partialSaltTopByte_tail (salts : Index → Salt121) (positions : Positions)
    (hrem : 0 < positions.card % 8) :
    BitVec.ofNat 8 (partialSaltTopByte salts positions (positions.card / 8) (positions.card % 8)) =
      saltTopByte salts positions (positions.card / 8) := by
  unfold saltTopByte partialSaltTopByte
  congr 1
  have hle : positions.card % 8 ≤ 8 := by omega
  have hsplit : (∑ m ∈ Finset.range 8, saltTopBitAt salts positions (8 * (positions.card / 8) + m) * 2 ^ m) =
      (∑ m ∈ Finset.range (positions.card % 8),
        saltTopBitAt salts positions (8 * (positions.card / 8) + m) * 2 ^ m) +
      (∑ m ∈ Finset.range (8 - positions.card % 8),
        saltTopBitAt salts positions (8 * (positions.card / 8) + (positions.card % 8 + m)) *
          2 ^ (positions.card % 8 + m)) := by
    rw [← Finset.sum_range_add, Nat.add_sub_cancel' hle]
  have hzero : (∑ m ∈ Finset.range (8 - positions.card % 8),
      saltTopBitAt salts positions (8 * (positions.card / 8) + (positions.card % 8 + m)) *
        2 ^ (positions.card % 8 + m)) = 0 := by
    apply Finset.sum_eq_zero; intro m _
    unfold saltTopBitAt
    rw [dif_neg (by omega), Nat.zero_mul]
  omega

private theorem tdSalt_topBit_byte15 (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (i : Index) :
    (trapdoor.extractLsb' (8 * (saltOff i + 15)) 8).zeroExtend 64 &&& signExtend12 (1#12) =
      BitVec.ofNat 64 (if (tdSalt trapdoor i).getLsbD 120 then 1 else 0) := by
  have hse1 : signExtend12 (1#12) = 1#64 := by decide
  rw [hse1]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_and]
  by_cases hb0 : b = 0
  · subst hb0
    have hm : (1#64 : Word).getLsbD 0 = true := by decide
    rw [hm, Bool.and_true]
    simp only [BitVec.zeroExtend, BitVec.getLsbD_setWidth, show (0 : Nat) < 64 by decide,
      decide_true, Bool.true_and, BitVec.getLsbD_extractLsb', show (0 : Nat) < 8 by decide,
      Nat.add_zero, tdSalt, show (120 : Nat) < 121 by decide,
      show 8 * (saltOff i + 15) = 8 * saltOff i + 120 by omega]
    cases trapdoor.getLsbD (8 * saltOff i + 120) <;> decide
  · have hm : (1#64 : Word).getLsbD b = false := by
      simp only [BitVec.getLsbD_ofNat, hb, decide_true, Bool.true_and, Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ≤ 2 ^ b := by
        have h1 : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
        simpa using h1
      have hdiv : 1 / 2 ^ b = 0 := Nat.div_eq_of_lt (by omega)
      simp [hdiv]
    rw [hm, Bool.and_false]
    cases (tdSalt trapdoor i).getLsbD 120
    · simp
    · simp only [BitVec.getLsbD_ofNat, hb, decide_true, Bool.true_and, Nat.testBit_eq_decide_div_mod_eq]
      have hpow : 2 ≤ 2 ^ b := by
        have h1 : 2 ^ 1 ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
        simpa using h1
      have hdiv : 1 / 2 ^ b = 0 := Nat.div_eq_of_lt (by omega)
      simp [hdiv]

private theorem chunk_tdSalt15 (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index)
    (j : Nat) (hj : j < 15) :
    trapdoor.extractLsb' (8 * (saltOff i + j)) 8 =
      (bitsToBytes (salt121Word16 (tdSalt trapdoor i)) 15)[j]'(by simp [bitsToBytes]; exact hj) := by
  simp only [bitsToBytes, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    salt121Word16_getLsbD, tdSalt, show 8 * j + b < 121 by omega,
    show 8 * (saltOff i + j) + b = 8 * saltOff i + (8 * j + b) by omega]

private theorem chunk_tdNode (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (l idx n j : Nat) (hn : n ≤ 32) (hj : j < n) :
    trapdoor.extractLsb' (8 * (levelBase l + nodeOffset l idx + j)) 8 =
      (bitsToBytes (tdNode trapdoor l idx) n)[j]'(by simp [bitsToBytes]; exact hj) := by
  simp only [bitsToBytes, List.getElem_map, List.getElem_range, tdNode]
  rw [extractLsb'_extractLsb' trapdoor (8 * (levelBase l + nodeOffset l idx)) 256 (8 * j) 8 (by omega)]
  congr 1; omega

/-! ### 3. Single-Instruction Step Lemmas (203-word image) -/

private theorem step_ADDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ADDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_ADD {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ADD rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADD rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADD rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SUB {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SUB rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SUB rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SUB rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SLLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SLLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SLLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SLLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SRLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SRLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SRLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SRLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SLL {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SLL rd rs1 rs2)) :
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
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SRL rd rs1 rs2)) :
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
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.XORI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.XORI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.XORI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_ANDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ANDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ANDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ANDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_OR {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.OR rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.OR rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.OR rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_LD {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.LD rd rs1 off))
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
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SD rs1 rs2 off))
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
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.LBU rd rs1 off))
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
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SB rs1 rs2 off))
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
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
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
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
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
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
    (hne : s.getReg rs1 ≠ s.getReg rs2) (htgt : pcAt idx + signExtend13 off = pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (pcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BNE rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : (s.getReg rs1 != s.getReg rs2) = true := bne_iff_ne.mpr hne
  have hst : ordinaryStep s (.base (.BNE rs1 rs2 off)) = some (s.setPC (pcAt tgt)) := by
    change some (if (s.getReg rs1 != s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem step_BNE_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
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
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
    (hlt : (s.getReg rs1).toNat < (s.getReg rs2).toNat)
    (htgt : pcAt idx + signExtend13 off = pcAt tgt) :
    OpenRuns s 1 1 (s.setPC (pcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BLTU rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : BitVec.ult (s.getReg rs1) (s.getReg rs2) = true := by
    simp only [BitVec.ult, decide_eq_true_eq]; exact hlt
  have hst : ordinaryStep s (.base (.BLTU rs1 rs2 off)) = some (s.setPC (pcAt tgt)) := by
    change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem step_BLTU_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
    (hle : (s.getReg rs2).toNat ≤ (s.getReg rs1).toNat) :
    OpenRuns s 1 1 (s.setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BLTU rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true) := by
    simp only [BitVec.ult, decide_eq_true_eq]; omega
  have hst : ordinaryStep s (.base (.BLTU rs1 rs2 off)) = some (s.setPC (pcAt (idx + 1))) := by
    change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_JAL {s : MachineState} {idx tgt : Nat} {rd : Reg} {off : BitVec 21}
    (hidx : idx < 203) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.JAL rd off))
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
    (hidx : idx < 203) (hpc : s.pc = pcAt idx)
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

/-- Read-only regions: trapdoor `[4294971424, 6174019552)`, indices `[6174019552, 6308237280)`,
and embedded metadata `[68719475936, 68719476736)`. -/
private def ReadOnlyPreserved (s0 s : MachineState) : Prop :=
  ∀ addr : Word,
    (4294971424 ≤ addr.toNat ∧ addr.toNat < 6308237280) ∨
    (68719475936 ≤ addr.toNat ∧ addr.toNat < 68719476736) →
    s.getMem addr = s0.getMem addr

/-- Exact byte contents of the proof output prefix `[10603204576, 10603204576 + bytes.length)`. -/
def ProofPrefix (s : MachineState) (bytes : List Byte) : Prop :=
  ∀ j (hj : j < bytes.length),
    s.getByte (BitVec.ofNat 64 (10603204576 + j)) = bytes[j]

/-- Exact byte contents of the tail scratch prefix `[tailBufBase, tailBufBase + tailBytes.length)`. -/
private def TailBufPrefix (s : MachineState) (tailBytes : List Byte) : Prop :=
  ∀ j (hj : j < tailBytes.length),
    s.getByte (BitVec.ofNat 64 (tailBufBase + j)) = tailBytes[j]

/-- Level `l` cap-mark bytes in `[4096 + capMarkOff l, 4096 + capMarkOff l + levelSize l)`. -/
private def CapLevelMarks (s : MachineState) (positions : Positions) (l : Nat) : Prop :=
  ∀ idx < levelSize l,
    s.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + idx)) =
      if capMark positions l idx then 1#8 else 0#8

/-- Lighter writer state during Pass 0 (before `x14 := x13 ^^^ 63` sync at word 58). -/
private structure SaltWriterState (s : MachineState) (fwdBytes : List Byte) : Prop where
  rx25 : s.getReg .x25 = BitVec.ofNat 64 (10603204576 + 8 * (fwdBytes.length / 8))
  rx13 : s.getReg .x13 = BitVec.ofNat 64 (8 * (fwdBytes.length % 8))
  wbufLo : ∀ j (hj : j < fwdBytes.length % 8),
    (s.getReg .x12).extractLsb' (8 * j) 8 = fwdBytes[8 * (fwdBytes.length / 8) + j]'(by omega)
  wbufHi : ∀ j, fwdBytes.length % 8 ≤ j → j < 8 →
    (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8
  memDwords : ∀ j (hj : j < 8 * (fwdBytes.length / 8)),
    s.getByte (BitVec.ofNat 64 (10603204576 + j)) = fwdBytes[j]'(by omega)

/-- Exact state of the branchless 64-bit aligned dword-buffered writer for forward proof bytes. -/
private structure WriterState (s : MachineState) (fwdBytes : List Byte) : Prop where
  rx25 : s.getReg .x25 = BitVec.ofNat 64 (10603204576 + 8 * (fwdBytes.length / 8))
  rx13 : s.getReg .x13 = BitVec.ofNat 64 (8 * (fwdBytes.length % 8))
  rx14 : s.getReg .x14 = BitVec.ofNat 64 (63 - 8 * (fwdBytes.length % 8))
  wbufLo : ∀ j (hj : j < fwdBytes.length % 8),
    (s.getReg .x12).extractLsb' (8 * j) 8 = fwdBytes[8 * (fwdBytes.length / 8) + j]'(by omega)
  wbufHi : ∀ j, fwdBytes.length % 8 ≤ j → j < 8 →
    (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8
  memDwords : ∀ j (hj : j < 8 * (fwdBytes.length / 8)),
    s.getByte (BitVec.ofNat 64 (10603204576 + j)) = fwdBytes[j]'(by omega)

/-- Exact state of the streaming 6-bit tail packer for emitted 6-bit tails. -/
private structure TailState (s : MachineState) (tails : List (BitVec 6)) : Prop where
  rx31 : s.getReg .x31 = BitVec.ofNat 64 tailBufBase
  rx15 : s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (tails.foldl pack6Step ([], 0, 0)).1.length)
  rx16 : s.getReg .x16 = BitVec.ofNat 64 (tails.foldl pack6Step ([], 0, 0)).2.1
  rx17 : s.getReg .x17 = BitVec.ofNat 64 (tails.foldl pack6Step ([], 0, 0)).2.2
  memTail : TailBufPrefix s (tails.foldl pack6Step ([], 0, 0)).1

private theorem SaltWriterState.of_eq {s1 s2 : MachineState} {fwdBytes : List Byte}
    (hw : SaltWriterState s1 fwdBytes)
    (h25 : s2.getReg .x25 = s1.getReg .x25 := by rfl)
    (h13 : s2.getReg .x13 = s1.getReg .x13 := by rfl)
    (h12 : s2.getReg .x12 = s1.getReg .x12 := by rfl)
    (hmem : ∀ a, s2.getByte a = s1.getByte a := by intro _; rfl) :
    SaltWriterState s2 fwdBytes :=
  ⟨h25.trans hw.rx25, h13.trans hw.rx13,
   fun j hj => by rw [h12]; exact hw.wbufLo j hj,
   fun j h1 h2 => by rw [h12]; exact hw.wbufHi j h1 h2,
   fun j hj => by rw [hmem]; exact hw.memDwords j hj⟩

private theorem WriterState.cast_bytes {s : MachineState} {a b : List Byte}
    (h : a = b) (hw : WriterState s a) : WriterState s b := h ▸ hw

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
    s.getMem (BitVec.ofNat 64 (6174019552 + 8 * ordinal)) =
      BitVec.ofNat 64 (openingIndex positions ordinal) := by
  have hcard := positions_card_le positions
  have haddr : (BitVec.ofNat 64 (6174019552 + 8 * ordinal)).toNat = 6174019552 + 8 * ordinal := by
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
    (off : Nat) (hoff : off < 1879048128) :
    s.getByte (BitVec.ofNat 64 (4294971424 + off)) = trapdoor.extractLsb' (8 * off) 8 := by
  set a := 4294971424 + off
  have hdec : alignToDword (BitVec.ofNat 64 a) = BitVec.ofNat 64 (8 * (a / 8)) := by
    have h := alignToDword_ofNat_eq (8 * (a / 8)) (a % 8) (by omega) (by omega)
    simpa only [show 8 * (a / 8) + a % 8 = a by omega] using h
  have hmem : s.getMem (alignToDword (BitVec.ofNat 64 a)) =
      (submission.initialState .opening (trapdoor, positions)).getMem
        (alignToDword (BitVec.ofNat 64 a)) := by
    rw [hdec]; apply hro; left
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  change extractByte (s.getMem (alignToDword (BitVec.ofNat 64 a))) (byteOffset (BitVec.ofNat 64 a)) = _
  rw [hmem]
  exact opening_initial_trapdoor_byte trapdoor positions off hoff

private theorem readOnly_getMem_trapdoor_byte {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (off j : Nat) (hal : off % 8 = 0) (hj : j < 8) (hbd : off + 8 ≤ 1879048128) :
    (s.getMem (BitVec.ofNat 64 (4294971424 + off))).extractLsb' (8 * j) 8 =
      trapdoor.extractLsb' (8 * (off + j)) 8 := by
  rw [getMem_extractByte (by omega) hj, Nat.add_assoc]
  exact readOnly_getByte_trapdoor hro (off + j) (by omega)

private theorem readOnly_setMem_proof {s0 s : MachineState} (dst : Nat) (val : Word)
    (hro : ReadOnlyPreserved s0 s) (hlo : 10603204576 ≤ dst) (hhi : dst + 8 ≤ 18842918592) :
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
    intro heq; rw [hdec] at heq
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
    intro heq; rw [hdec] at heq
    have hn := congrArg BitVec.toNat heq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hn
    rcases had with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  simp only [MachineState.setByte, MachineState.getMem_setMem_ne hne]
  exact hro addr had

private theorem writerState_setByte_outside {s : MachineState} {fwdBytes : List Byte} (dst : Nat)
    (b : BitVec 8) (hw : WriterState s fwdBytes) (hbd : fwdBytes.length ≤ 8239714016)
    (hout : dst < 10603204576 ∨ 18842918592 ≤ dst) (hdst : dst < 2 ^ 64) :
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

/-! ### 5. Branchless Dword Writer & Streaming 6-Bit Tail Subroutines (`136..202`) -/

private theorem openRuns_emit_dword {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base srcOff qBase k : Nat} {imm : BitVec 12}
    {cur chunk8 : List Byte}
    (hbase : base + 5 < 203)
    (himm : signExtend12 imm = BitVec.ofNat 64 (8 * k))
    (hi0 : openingInstr base = .base (.LD .x5 .x10 imm))
    (hi1 : openingInstr (base + 1) = .base (.SLL .x6 .x5 .x13))
    (hi2 : openingInstr (base + 2) = .base (.OR .x12 .x12 .x6))
    (hi3 : openingInstr (base + 3) = .base (.SD .x25 .x12 imm))
    (hi4 : openingInstr (base + 4) = .base (.SRLI .x5 .x5 (1#6)))
    (hi5 : openingInstr (base + 5) = .base (.SRL .x12 .x5 .x14))
    (hpc : s.pc = pcAt base)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (10603204576 + 8 * qBase))
    (hqeq : cur.length / 8 = qBase + k)
    (hx13 : s.getReg .x13 = BitVec.ofNat 64 (8 * (cur.length % 8)))
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (63 - 8 * (cur.length % 8)))
    (hwLo : ∀ j (hj : j < cur.length % 8),
      (s.getReg .x12).extractLsb' (8 * j) 8 = cur[8 * (cur.length / 8) + j]'(by omega))
    (hwHi : ∀ j, cur.length % 8 ≤ j → j < 8 →
      (s.getReg .x12).extractLsb' (8 * j) 8 = 0#8)
    (hmem : ∀ j (hj : j < 8 * (cur.length / 8)),
      s.getByte (BitVec.ofNat 64 (10603204576 + j)) = cur[j]'(by omega))
    (hsrc_al : srcOff % 8 = 0)
    (hsrc_bd : srcOff + 8 * k + 8 ≤ 1879048128)
    (hcur_bd : cur.length + 8 ≤ 8239714016)
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
        s'.getByte (BitVec.ofNat 64 (10603204576 + j)) = cur'[j]'(by omega)) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475936 →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro cur'
  set r := cur.length % 8
  set q := cur.length / 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  have hcur'_len : cur'.length = cur.length + 8 := by simp [cur', hclen]
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
    simpa only [show s2.getReg .x12 = w from rfl, show s2.getReg .x6 = v <<< (8 * r) from rfl,
      wOut, s3, show base + 2 + 1 = base + 3 by omega] using h2
  have hdstAddr : s3.getReg .x25 + signExtend12 imm = BitVec.ofNat 64 (10603204576 + 8 * q) := by
    have hr25 : s3.getReg .x25 = BitVec.ofNat 64 (10603204576 + 8 * qBase) := hx25
    rw [hr25, himm, bv64_ofNat_add]; congr 1; omega
  have h3 := step_SD (by omega) (rfl : s3.pc = pcAt (base + 3)) hi3
    (by rw [hdstAddr]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s4 := (s3.setMem (BitVec.ofNat 64 (10603204576 + 8 * q)) wOut).setPC (pcAt (base + 4))
  have h3' : OpenRuns s3 1 1 s4 := by
    simpa only [hdstAddr, show s3.getReg .x12 = wOut from rfl, s4, show base + 3 + 1 = base + 4 by omega] using h3
  have h4 := step_SRLI (by omega) (rfl : s4.pc = pcAt (base + 4)) hi4
  let s5 := (s4.setReg .x5 (v >>> 1)).setPC (pcAt (base + 5))
  have h4' : OpenRuns s4 1 1 s5 := by
    have hr5 : s4.getReg .x5 = v := by simp only [s4, MachineState.getReg_setPC, getReg_setMem, s3, s2, s1]; rfl
    simpa only [hr5, show (1#6 : BitVec 6).toNat = 1 from rfl, s5, show base + 4 + 1 = base + 5 by omega] using h4
  set wNew := (v >>> 1) >>> (63 - 8 * r)
  have h5 := step_SRL (by omega) (rfl : s5.pc = pcAt (base + 5)) hi5
  have hx14_mod : (s5.getReg .x14).toNat % 64 = 63 - 8 * r := by
    have h : s5.getReg .x14 = BitVec.ofNat 64 (63 - 8 * r) := by
      simp only [s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
        getReg_setReg_ne' .x5 .x14 (by decide), getReg_setReg_ne' .x12 .x14 (by decide),
        getReg_setReg_ne' .x6 .x14 (by decide)]
      exact hx14
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 63 - 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s6 := (s5.setReg .x12 wNew).setPC (pcAt (base + 6))
  have h5' : OpenRuns s5 1 1 s6 := by
    simpa only [show s5.getReg .x5 = v >>> 1 from rfl, hx14_mod, wNew, s6,
      show base + 5 + 1 = base + 6 by omega] using h5
  have hmem6 : ∀ a, s6.getByte a =
      (s.setMem (BitVec.ofNat 64 (10603204576 + 8 * q)) wOut).getByte a := fun a => by
    simp only [s6, s5, s4, s3, s2, s1, getByte_setPC, getByte_setReg]; rfl
  refine ⟨s6, ((((h0'.trans h1').trans h2').trans h3').trans h4').trans h5', rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro reg h5ne h6ne h12ne
    simp only [s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
      getReg_setReg_ne' .x12 reg (Ne.symm h12ne), getReg_setReg_ne' .x5 reg (Ne.symm h5ne),
      getReg_setReg_ne' .x6 reg (Ne.symm h6ne)]
  · intro j hj
    have hlen_app : (cur ++ chunk8).length = cur.length + 8 := by simp [hclen]
    have hjr : j < r := by omega
    have hbyte := word_ushr1_ushr_byte v r hr j (by omega)
    rw [if_pos hjr, hv_byte (8 - r + j) (by omega)] at hbyte
    change wNew.extractLsb' (8 * j) 8 = _
    rw [hbyte, list_getElem_append_right cur chunk8 (8 * (cur'.length / 8) + j) (by omega) (by omega)]
    congr 1; omega
  · intro j hj1 hj2
    have hbyte := word_ushr1_ushr_byte v r hr j hj2
    rw [if_neg (by omega)] at hbyte; exact hbyte
  · intro j hj
    have hlen_app : (cur ++ chunk8).length = cur.length + 8 := by simp [hclen]
    rw [hmem6]
    by_cases hlt : j < 8 * q
    · rw [setMem_getByte_ofNat s (10603204576 + 8 * q) (10603204576 + j) wOut
        (by omega) (by omega) (by omega) (by omega)]
      rw [hmem j hlt, list_getElem_append_left cur chunk8 j (by omega)]
    · have hu : j - 8 * q < 8 := by omega
      have hadd : 10603204576 + 8 * q + (j - 8 * q) = 10603204576 + j := by omega
      rw [← hadd, setMem_getByte_inside s (10603204576 + 8 * q) (j - 8 * q) wOut (by omega) hu]
      rw [word_or_shl_byte w v r hr hwHi (j - 8 * q) hu]
      by_cases hur : j - 8 * q < r
      · rw [if_pos hur, hwLo (j - 8 * q) hur, list_getElem_append_left cur chunk8 j (by omega)]
        congr 1; omega
      · rw [if_neg hur, hv_byte (j - 8 * q - r) (by omega),
          list_getElem_append_right cur chunk8 j (by omega) (by omega)]
        congr 1; omega
  · intro addr had
    change (s.setMem (BitVec.ofNat 64 (10603204576 + 8 * q)) wOut).getMem addr = _
    exact readOnly_setMem_proof (10603204576 + 8 * q) wOut hro (by omega) (by omega) addr had
  · intro a ha
    rw [hmem6, setMem_getByte_ofNat s (10603204576 + 8 * q) a wOut
      (by omega) (by omega) (by omega) (by omega)]
  · intro a ha1 ha2
    have htb : tailBufBase = 25769803776 := rfl
    rw [hmem6, setMem_getByte_ofNat s (10603204576 + 8 * q) a wOut
      (by omega) (by omega) (by omega) (by omega)]

private theorem openRuns_emit_3dwords {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base srcOff : Nat}
    {fwdBytes chunk24 : List Byte}
    (hbase : base + 18 < 203)
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
    (hsrc_bd : srcOff + 24 ≤ 1879048128)
    (hbd : fwdBytes.length + 24 ≤ 8239714016)
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
      hpc2
      (by rw [hreg2 .x10 (by decide) (by decide) (by decide), hreg1 .x10 (by decide) (by decide) (by decide)]; exact hx10)
      (by rw [hreg2 .x25 (by decide) (by decide) (by decide), hreg1 .x25 (by decide) (by decide) (by decide)]; exact hw.rx25)
      (by omega)
      (by rw [hreg2 .x13 (by decide) (by decide) (by decide), hreg1 .x13 (by decide) (by decide) (by decide), hw.rx13]; congr 1; omega)
      (by rw [hreg2 .x14 (by decide) (by decide) (by decide), hreg1 .x14 (by decide) (by decide) (by decide), hw.rx14]; congr 1; omega)
      hwLo2 hwHi2 hmem2 hsrc_al (by omega) (by omega) hro2 hc2_len (fun j hj => by
        simpa [c2, List.getElem_drop, Nat.add_assoc] using hchunk (16 + j) (by omega))
  have hpres3 : ∀ r, r ≠ .x5 → r ≠ .x6 → r ≠ .x12 → s3.getReg r = s.getReg r := fun r h5 h6 h12 => by
    rw [hreg3 r h5 h6 h12, hreg2 r h5 h6 h12, hreg1 r h5 h6 h12]
  have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
  have h4 := step_ADDI (by omega) hpc3 hadv
  have hnew25 : s3.getReg .x25 + signExtend12 (24#12) =
      BitVec.ofNat 64 (10603204576 + 8 * ((fwdBytes ++ chunk24).length / 8)) := by
    rw [hpres3 .x25 (by decide) (by decide) (by decide), hw.rx25, hse24, bv64_ofNat_add]
    congr 1; simp only [List.length_append, hclen]; omega
  let s4 := (s3.setReg .x25 (BitVec.ofNat 64 (10603204576 + 8 * ((fwdBytes ++ chunk24).length / 8)))).setPC
    (pcAt (base + 19))
  have h4' : OpenRuns s3 1 1 s4 := by
    simpa only [hnew25, s4, show base + 18 + 1 = base + 19 by omega] using h4
  refine ⟨s4, ((hr1.trans hr2).trans hr3).trans h4', rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro r h5 h6 h12 h25
    simp only [s4, MachineState.getReg_setPC, getReg_setReg_ne' .x25 r (Ne.symm h25)]
    exact hpres3 r h5 h6 h12
  · intro a ha; simp only [s4, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro3 a ha
  · refine WriterState.cast_bytes hcur_eq ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcur_eq]; rfl
    · simp only [s4, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x13 (by decide)]
      rw [hpres3 .x13 (by decide) (by decide) (by decide), hw.rx13, hcur_eq]
      congr 1; simp only [List.length_append, hclen]; omega
    · simp only [s4, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x14 (by decide)]
      rw [hpres3 .x14 (by decide) (by decide) (by decide), hw.rx14, hcur_eq]
      congr 1; simp only [List.length_append, hclen]; omega
    · intro j hj
      simp only [s4, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x12 (by decide)]
      exact hwLo3 j hj
    · intro j h1 h2
      simp only [s4, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x12 (by decide)]
      exact hwHi3 j h1 h2
    · intro j hj; simp only [s4, getByte_setPC, getByte_setReg]; exact hmem3 j hj
  · intro a ha; simp only [s4, getByte_setPC, getByte_setReg]; rw [hcap3 a ha, hcap2 a ha, hcap1 a ha]
  · intro a ha1 ha2; simp only [s4, getByte_setPC, getByte_setReg]; rw [htail3 a ha1 ha2, htail2 a ha1 ha2, htail1 a ha1 ha2]

/-- Partial byte emission (`1 ≤ m < 8`) with exact telescoping step count `6 + 5 * Δq`. -/
private theorem openRuns_emit_partial {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base m : Nat} {immBits : BitVec 12}
    {fwdBytes chunkM : List Byte}
    (hbase : base + 10 < 203) (hm1 : 1 ≤ m) (hm2 : m < 8)
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
    (hbd : fwdBytes.length + m ≤ 8239714016)
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
  have h0 := step_SLL (by omega) hpc hc.1
  have hx13_mod : (s.getReg .x13).toNat % 64 = 8 * r := by
    rw [hw.rx13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s1 := (s.setReg .x6 (v <<< (8 * r))).setPC (pcAt (base + 1))
  have h0' : OpenRuns s 1 1 s1 := by simpa only [hx13_mod, v, s1] using h0
  have h1 := step_OR (by omega) (rfl : s1.pc = pcAt (base + 1)) hc.2.1
  let s2 := (s1.setReg .x12 wOut).setPC (pcAt (base + 2))
  have h1' : OpenRuns s1 1 1 s2 := by
    simpa only [show s1.getReg .x12 = w from rfl, show s1.getReg .x6 = v <<< (8 * r) from rfl,
      wOut, s2, show base + 1 + 1 = base + 2 by omega] using h1
  have h2 := step_ADDI (by omega) (rfl : s2.pc = pcAt (base + 2)) hc.2.2.1
  let s3 := (s2.setReg .x13 (BitVec.ofNat 64 (8 * (r + m)))).setPC (pcAt (base + 3))
  have h2' : OpenRuns s2 1 1 s3 := by
    have hr13 : s2.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13
    have hv : s2.getReg .x13 + signExtend12 immBits = BitVec.ofNat 64 (8 * (r + m)) := by
      rw [hr13, himm, bv64_ofNat_add]; congr 1; omega
    simpa only [hv, s3, show base + 2 + 1 = base + 3 by omega] using h2
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
  have hx7_4 : (s4.getReg .x7).toNat = 64 := by change (64#64 : Word).toNat = 64; decide
  have hlen_app : (fwdBytes ++ chunkM).length = fwdBytes.length + m := by simp [hclen]
  by_cases hlt : r + m < 8
  · have h4 := step_BLTU_taken (by omega) (rfl : s4.pc = pcAt (base + 4)) hc.2.2.2.2.1
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
        getReg_setReg_ne' .x14 reg (Ne.symm h14), getReg_setReg_ne' .x7 reg (Ne.symm h7),
        getReg_setReg_ne' .x13 reg (Ne.symm h13), getReg_setReg_ne' .x12 reg (Ne.symm h12),
        getReg_setReg_ne' .x6 reg (Ne.symm h6)]
    · intro a ha; simp only [s11, s10, s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
    · refine ⟨by rw [hq']; exact hw.rx25, by rw [hr']; rfl, by rw [hr']; rfl, ?_, ?_, ?_⟩
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
  · have hge : 8 ≤ r + m := by omega
    have hq' : (fwdBytes ++ chunkM).length / 8 = q + 1 := by omega
    have hr' : (fwdBytes ++ chunkM).length % 8 = r + m - 8 := by omega
    have h4 := step_BLTU_not_taken (by omega) (rfl : s4.pc = pcAt (base + 4)) hc.2.2.2.2.1
      (by rw [hx13_4, hx7_4]; omega)
    let s5 := s4.setPC (pcAt (base + 5))
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hdstAddr : s5.getReg .x25 + signExtend12 (0#12) = BitVec.ofNat 64 (10603204576 + 8 * q) := by
      have hr25 : s5.getReg .x25 = BitVec.ofNat 64 (10603204576 + 8 * q) := hw.rx25
      rw [hr25, hse0, bv64_ofNat_add, Nat.add_zero]
    have h5 := step_SD (by omega) (rfl : s5.pc = pcAt (base + 5)) hc.2.2.2.2.2.1
      (by rw [hdstAddr]; exact accessValid_ofNat _ 8 (by omega) (by omega))
    let s6 := (s5.setMem (BitVec.ofNat 64 (10603204576 + 8 * q)) wOut).setPC (pcAt (base + 6))
    have h5' : OpenRuns s5 1 1 s6 := by
      simpa only [hdstAddr, show s5.getReg .x12 = wOut from rfl, s6, show base + 5 + 1 = base + 6 by omega] using h5
    have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
    have h6 := step_ADDI (by omega) (rfl : s6.pc = pcAt (base + 6)) hc.2.2.2.2.2.2.1
    let s7 := (s6.setReg .x25 (BitVec.ofNat 64 (10603204576 + 8 * (q + 1)))).setPC (pcAt (base + 7))
    have h6' : OpenRuns s6 1 1 s7 := by
      have hr25 : s6.getReg .x25 = BitVec.ofNat 64 (10603204576 + 8 * q) := by
        simp only [s6, MachineState.getReg_setPC, getReg_setMem]; exact hw.rx25
      have hv : s6.getReg .x25 + signExtend12 (8#12) = BitVec.ofNat 64 (10603204576 + 8 * (q + 1)) := by
        rw [hr25, hse8, bv64_ofNat_add]; congr 1
      simpa only [hv, s7, show base + 6 + 1 = base + 7 by omega] using h6
    have h7 := step_SRLI (by omega) (rfl : s7.pc = pcAt (base + 7)) hc.2.2.2.2.2.2.2.1
    let s8 := (s7.setReg .x5 (v >>> 1)).setPC (pcAt (base + 8))
    have h7' : OpenRuns s7 1 1 s8 := by
      have hr5 : s7.getReg .x5 = v := by
        simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
          getReg_setReg_ne' .x25 .x5 (by decide), getReg_setReg_ne' .x7 .x5 (by decide),
          getReg_setReg_ne' .x13 .x5 (by decide), getReg_setReg_ne' .x12 .x5 (by decide),
          getReg_setReg_ne' .x6 .x5 (by decide)]; rfl
      simpa only [hr5, show (1#6 : BitVec 6).toNat = 1 from rfl, s8, show base + 7 + 1 = base + 8 by omega] using h7
    set wNew := (v >>> 1) >>> (63 - 8 * r)
    have h8 := step_SRL (by omega) (rfl : s8.pc = pcAt (base + 8)) hc.2.2.2.2.2.2.2.2.1
    have hx14_mod : (s8.getReg .x14).toNat % 64 = 63 - 8 * r := by
      have h : s8.getReg .x14 = BitVec.ofNat 64 (63 - 8 * r) := by
        simp only [s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
          getReg_setReg_ne' .x5 .x14 (by decide), getReg_setReg_ne' .x25 .x14 (by decide),
          getReg_setReg_ne' .x7 .x14 (by decide), getReg_setReg_ne' .x13 .x14 (by decide),
          getReg_setReg_ne' .x12 .x14 (by decide), getReg_setReg_ne' .x6 .x14 (by decide)]
        exact hw.rx14
      rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 63 - 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
    let s9 := (s8.setReg .x12 wNew).setPC (pcAt (base + 9))
    have h8' : OpenRuns s8 1 1 s9 := by
      simpa only [show s8.getReg .x5 = v >>> 1 from rfl, hx14_mod, wNew, s9,
        show base + 8 + 1 = base + 9 by omega] using h8
    have h9 := step_ADDI (by omega) (rfl : s9.pc = pcAt (base + 9)) hc.2.2.2.2.2.2.2.2.2.1
    let s10 := (s9.setReg .x13 (BitVec.ofNat 64 (8 * (r + m - 8)))).setPC (pcAt (base + 10))
    have h9' : OpenRuns s9 1 1 s10 := by
      have hr13 : s9.getReg .x13 = BitVec.ofNat 64 (8 * (r + m)) := by
        simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
          getReg_setReg_ne' .x12 .x13 (by decide), getReg_setReg_ne' .x5 .x13 (by decide),
          getReg_setReg_ne' .x25 .x13 (by decide), getReg_setReg_ne' .x7 .x13 (by decide)]; rfl
      have hv : s9.getReg .x13 + signExtend12 (4032#12) = BitVec.ofNat 64 (8 * (r + m - 8)) := by
        rw [hr13, bv64_add_neg64 (8 * (r + m)) (by omega)]; congr 1; omega
      simpa only [hv, s10, show base + 9 + 1 = base + 10 by omega] using h9
    have h10 := step_XORI (by omega) (rfl : s10.pc = pcAt (base + 10)) hc.2.2.2.2.2.2.2.2.2.2
    let s11 := (s10.setReg .x14 (BitVec.ofNat 64 (63 - 8 * (r + m - 8)))).setPC (pcAt (base + 11))
    have h10' : OpenRuns s10 1 1 s11 := by
      have hv : s10.getReg .x13 ^^^ signExtend12 (63#12) = BitVec.ofNat 64 (63 - 8 * (r + m - 8)) := by
        change BitVec.ofNat 64 (8 * (r + m - 8)) ^^^ signExtend12 (63#12) = _
        exact bv64_xor63_8mul (r + m - 8) (by omega)
      simpa only [hv, s11, show base + 10 + 1 = base + 11 by omega] using h10
    have hmem11 : ∀ a, s11.getByte a =
        (s.setMem (BitVec.ofNat 64 (10603204576 + 8 * q)) wOut).getByte a := fun a => by
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getByte_setPC, getByte_setReg]; rfl
    refine ⟨11, s11, hpre.trans ((((((h4.trans h5').trans h6').trans h7').trans h8').trans h9').trans h10'),
      by omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro reg h5ne h6ne h7ne h12ne h13ne h14ne h25ne
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
        getReg_setReg_ne' .x14 reg (Ne.symm h14ne), getReg_setReg_ne' .x13 reg (Ne.symm h13ne),
        getReg_setReg_ne' .x12 reg (Ne.symm h12ne), getReg_setReg_ne' .x5 reg (Ne.symm h5ne),
        getReg_setReg_ne' .x25 reg (Ne.symm h25ne), getReg_setReg_ne' .x7 reg (Ne.symm h7ne),
        getReg_setReg_ne' .x6 reg (Ne.symm h6ne)]
    · intro a ha
      change (s.setMem (BitVec.ofNat 64 (10603204576 + 8 * q)) wOut).getMem a = _
      exact readOnly_setMem_proof (10603204576 + 8 * q) wOut hro (by omega) (by omega) a ha
    · refine ⟨?_, ?_, by rw [hr']; rfl, ?_, ?_, ?_⟩
      · rw [hq']; simp only [s11, s10, s9, s8, s7, MachineState.getReg_setPC,
          getReg_setReg_ne' .x14 .x25 (by decide), getReg_setReg_ne' .x13 .x25 (by decide),
          getReg_setReg_ne' .x12 .x25 (by decide), getReg_setReg_ne' .x5 .x25 (by decide)]; rfl
      · rw [hr']; simp only [s11, s10, MachineState.getReg_setPC, getReg_setReg_ne' .x14 .x13 (by decide)]; rfl
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
        · rw [setMem_getByte_ofNat s (10603204576 + 8 * q) (10603204576 + j) wOut
            (by omega) (by omega) (by omega) (by omega)]
          rw [hw.memDwords j hltq, list_getElem_append_left fwdBytes chunkM j (by omega)]
        · have hu : j - 8 * q < 8 := by omega
          have hadd : 10603204576 + 8 * q + (j - 8 * q) = 10603204576 + j := by omega
          rw [← hadd, setMem_getByte_inside s (10603204576 + 8 * q) (j - 8 * q) wOut (by omega) hu]
          rw [word_or_shl_byte w v r hr hw.wbufHi (j - 8 * q) hu]
          by_cases hur : j - 8 * q < r
          · rw [if_pos hur, hw.wbufLo (j - 8 * q) hur, list_getElem_append_left fwdBytes chunkM j (by omega)]
            congr 1; omega
          · rw [if_neg hur, hx5 (j - 8 * q - r) (by omega), dif_pos (by omega),
              list_getElem_append_right fwdBytes chunkM j (by omega) (by omega)]
            congr 1; omega
    · intro a ha
      rw [hmem11, setMem_getByte_ofNat s (10603204576 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]
    · intro a ha1 ha2
      have htb : tailBufBase = 25769803776 := rfl
      rw [hmem11, setMem_getByte_ofNat s (10603204576 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]

/-- Streaming 6-bit tail push (`191..201`) with exact telescoping step count `7 + 4 * ΔtailAcc`. -/
private theorem openRuns_push_tail6 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {d : Digest}
    (hpc : s.pc = pcAt 191)
    (hx11 : (s.getReg .x11).extractLsb' (8 * 5) 8 = d.extractLsb' (8 * 29) 8)
    (hfbd : fwdBytes.length ≤ 8239714016)
    (htbd : tails.length < 300000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps = 7 + 4 * (tailAccLen (tails ++ [tail6 d]) - tailAccLen tails) ∧
      s'.pc = pcAt 202 ∧
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
  have h0 := step_SRLI (by omega) hpc (rfl : openingInstr 191 = .base (.SRLI .x5 .x11 (40#6)))
  let s1 := (s.setReg .x5 (s.getReg .x11 >>> 40)).setPC (pcAt 192)
  have h0' : OpenRuns s 1 1 s1 := by simpa only [show (40#6 : BitVec 6).toNat = 40 from rfl, s1] using h0
  have h1 := step_ANDI (by omega) (rfl : s1.pc = pcAt 192) (rfl : openingInstr 192 = .base (.ANDI .x5 .x5 (63#12)))
  let s2 := (s1.setReg .x5 (BitVec.ofNat 64 t.toNat)).setPC (pcAt 193)
  have h1' : OpenRuns s1 1 1 s2 := by
    have hv := word_tail6_from_hi (s.getReg .x11) d hx11
    simpa only [show s1.getReg .x5 = s.getReg .x11 >>> 40 from rfl, hv, t, s2] using h1
  have h2 := step_SLL (by omega) (rfl : s2.pc = pcAt 193) (rfl : openingInstr 193 = .base (.SLL .x6 .x5 .x17))
  have hx17_mod : (s2.getReg .x17).toNat % 64 = tCnt := by
    have h : s2.getReg .x17 = BitVec.ofNat 64 tCnt := ht.rx17
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : tCnt < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s3 := (s2.setReg .x6 (BitVec.ofNat 64 t.toNat <<< tCnt)).setPC (pcAt 194)
  have h2' : OpenRuns s2 1 1 s3 := by
    simpa only [show s2.getReg .x5 = BitVec.ofNat 64 t.toNat from rfl, hx17_mod, s3] using h2
  set buf' := tBuf + t.toNat * 2 ^ tCnt
  have hbuf'_lt : buf' < 8192 := by
    have hmul : t.toNat * 2 ^ tCnt ≤ 63 * 128 := Nat.mul_le_mul (by omega) hpow
    change tBuf + t.toNat * 2 ^ tCnt < 8192; omega
  have h3 := step_OR (by omega) (rfl : s3.pc = pcAt 194) (rfl : openingInstr 194 = .base (.OR .x16 .x16 .x6))
  let s4 := (s3.setReg .x16 (BitVec.ofNat 64 buf')).setPC (pcAt 195)
  have h3' : OpenRuns s3 1 1 s4 := by
    have hr16 : s3.getReg .x16 = BitVec.ofNat 64 tBuf := ht.rx16
    have hv : s3.getReg .x16 ||| s3.getReg .x6 = BitVec.ofNat 64 buf' := by
      rw [hr16]; exact tail_or_shl_eq_add tBuf tCnt t.toNat htCnt_lt htBuf_lt ht_lt
    simpa only [hv, s4] using h3
  have hse6 : signExtend12 (6#12) = BitVec.ofNat 64 6 := by decide
  have h4 := step_ADDI (by omega) (rfl : s4.pc = pcAt 195) (rfl : openingInstr 195 = .base (.ADDI .x17 .x17 (6#12)))
  let s5 := (s4.setReg .x17 (BitVec.ofNat 64 (tCnt + 6))).setPC (pcAt 196)
  have h4' : OpenRuns s4 1 1 s5 := by
    have hr17 : s4.getReg .x17 = BitVec.ofNat 64 tCnt := ht.rx17
    rw [hr17, hse6, bv64_ofNat_add] at h4; exact h4
  have h5 := step_ADDI (by omega) (rfl : s5.pc = pcAt 196) (rfl : openingInstr 196 = .base (.ADDI .x7 .x0 (8#12)))
  let s6 := (s5.setReg .x7 8#64).setPC (pcAt 197)
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
  · have h6 := step_BLTU_taken (by omega) (rfl : s6.pc = pcAt 197)
      (rfl : openingInstr 197 = .base (.BLTU .x17 .x7 (20#13)))
      (by rw [hx17_6, hx7_6]; exact hlt8)
      (by decide : pcAt 197 + signExtend13 (20#13) = pcAt 202)
    let s7 := s6.setPC (pcAt 202)
    have hpack : (tails ++ [t]).foldl pack6Step ([], 0, 0) = (acc, buf', tCnt + 6) := by
      rw [hfold_app]; unfold pack6Step; dsimp only; rw [if_neg (by omega)]
    have hta : tailAccLen (tails ++ [t]) = tailAccLen tails := by
      unfold tailAccLen; rw [hpack]
    refine ⟨7, s7, hpre.trans h6, by rw [hta]; omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro r h5ne h6ne h7ne _ h16ne h17ne
      simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC,
        getReg_setReg_ne' .x7 r (Ne.symm h7ne), getReg_setReg_ne' .x17 r (Ne.symm h17ne),
        getReg_setReg_ne' .x16 r (Ne.symm h16ne), getReg_setReg_ne' .x6 r (Ne.symm h6ne),
        getReg_setReg_ne' .x5 r (Ne.symm h5ne)]
    · intro a ha; simp only [s7, s6, s5, s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
    · exact ⟨hw.rx25, hw.rx13, hw.rx14, hw.wbufLo, hw.wbufHi, hw.memDwords⟩
    · refine ⟨ht.rx31, by rw [hpack]; exact ht.rx15, by rw [hpack]; rfl, by rw [hpack]; rfl, by rw [hpack]; exact ht.memTail⟩
    · intro a _; rfl
  · have hge8 : 8 ≤ tCnt + 6 := by omega
    have h6 := step_BLTU_not_taken (by omega) (rfl : s6.pc = pcAt 197)
      (rfl : openingInstr 197 = .base (.BLTU .x17 .x7 (20#13)))
      (by rw [hx17_6, hx7_6]; exact hge8)
    let s7 := s6.setPC (pcAt 198)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have haddr7 : s7.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + acc.length) := by
      have hr15 : s7.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := ht.rx15
      rw [hr15, hse0, bv64_ofNat_add, Nat.add_zero]
    have h7 := step_SB (by omega) (rfl : s7.pc = pcAt 198)
      (rfl : openingInstr 198 = .base (.SB .x15 .x16 (0#12)))
      (by rw [haddr7]; exact accessValid_ofNat _ 1 (by omega) (by omega))
    let s8 := (s7.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).setPC (pcAt 199)
    have h7' : OpenRuns s7 1 1 s8 := by
      have htr : (s7.getReg .x16).truncate 8 = BitVec.ofNat 8 buf' := by
        change (BitVec.ofNat 64 buf').truncate 8 = _
        exact bv64_ofNat_truncate8 buf' (by omega)
      simpa only [haddr7, htr, s8] using h7
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have h8 := step_ADDI (by omega) (rfl : s8.pc = pcAt 199) (rfl : openingInstr 199 = .base (.ADDI .x15 .x15 (1#12)))
    let s9 := (s8.setReg .x15 (BitVec.ofNat 64 (tailBufBase + (acc ++ [BitVec.ofNat 8 buf']).length))).setPC (pcAt 200)
    have h8' : OpenRuns s8 1 1 s9 := by
      have hr15 : s8.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := by
        simp only [s8, MachineState.getReg_setPC, getReg_setByte]; exact ht.rx15
      have hv : s8.getReg .x15 + signExtend12 (1#12) =
          BitVec.ofNat 64 (tailBufBase + (acc ++ [BitVec.ofNat 8 buf']).length) := by
        rw [hr15, hse1, bv64_ofNat_add, List.length_append, List.length_singleton, Nat.add_assoc]
      simpa only [hv, s9] using h8
    have h9 := step_SRLI (by omega) (rfl : s9.pc = pcAt 200) (rfl : openingInstr 200 = .base (.SRLI .x16 .x16 (8#6)))
    let s10 := (s9.setReg .x16 (BitVec.ofNat 64 (buf' / 256))).setPC (pcAt 201)
    have h9' : OpenRuns s9 1 1 s10 := by
      have hr16 : s9.getReg .x16 = BitVec.ofNat 64 buf' := by
        simp only [s9, s8, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne' .x15 .x16 (by decide)]; rfl
      have hv : s9.getReg .x16 >>> (8#6 : BitVec 6).toNat = BitVec.ofNat 64 (buf' / 256) := by
        rw [hr16]; change BitVec.ofNat 64 buf' >>> 8 = _
        rw [bv64_ushr buf' 8 (by omega), Nat.shiftRight_eq_div_pow]
      simpa only [hv, s10] using h9
    have h10 := step_ADDI (by omega) (rfl : s10.pc = pcAt 201) (rfl : openingInstr 201 = .base (.ADDI .x17 .x17 (4088#12)))
    let s11 := (s10.setReg .x17 (BitVec.ofNat 64 (tCnt + 6 - 8))).setPC (pcAt 202)
    have h10' : OpenRuns s10 1 1 s11 := by
      have hr17 : s10.getReg .x17 = BitVec.ofNat 64 (tCnt + 6) := by
        simp only [s10, s9, s8, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x16 .x17 (by decide), getReg_setReg_ne' .x15 .x17 (by decide)]; rfl
      rw [hr17, bv64_add_neg8 (tCnt + 6) hge8] at h10; exact h10
    have hpack : (tails ++ [t]).foldl pack6Step ([], 0, 0) =
        (acc ++ [BitVec.ofNat 8 buf'], buf' / 256, tCnt + 6 - 8) := by
      rw [hfold_app]; unfold pack6Step; dsimp only; rw [if_pos hge8]
    have hta : tailAccLen (tails ++ [t]) = tailAccLen tails + 1 := by
      unfold tailAccLen; rw [hpack]; simp [acc, st]
    have hmem11 : ∀ a, s11.getByte a =
        (s.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).getByte a := fun a => by
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, getByte_setPC, getByte_setReg]; rfl
    refine ⟨11, s11, hpre.trans ((((h6.trans h7').trans h8').trans h9').trans h10'), by rw [hta]; omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro r h5ne h6ne h7ne h15ne h16ne h17ne
      simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x17 r (Ne.symm h17ne), getReg_setReg_ne' .x16 r (Ne.symm h16ne),
        getReg_setReg_ne' .x15 r (Ne.symm h15ne), getReg_setReg_ne' .x7 r (Ne.symm h7ne),
        getReg_setReg_ne' .x6 r (Ne.symm h6ne), getReg_setReg_ne' .x5 r (Ne.symm h5ne)]
    · intro a ha
      change (s.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 buf')).getMem a = _
      exact readOnly_setByte_tail (tailBufBase + acc.length) _ hro (by omega) (by omega) a ha
    · have hw' := writerState_setByte_outside (tailBufBase + acc.length) (BitVec.ofNat 8 buf')
        hw hfbd (Or.inr (by omega)) (by omega)
      refine ⟨?_, ?_, ?_, ?_, ?_, fun j hj => by rw [hmem11]; exact hw'.memDwords j hj⟩
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x17 .x25 (by decide), getReg_setReg_ne' .x16 .x25 (by decide),
          getReg_setReg_ne' .x15 .x25 (by decide), getReg_setReg_ne' .x7 .x25 (by decide),
          getReg_setReg_ne' .x6 .x25 (by decide), getReg_setReg_ne' .x5 .x25 (by decide)]; exact hw.rx25
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x17 .x13 (by decide), getReg_setReg_ne' .x16 .x13 (by decide),
          getReg_setReg_ne' .x15 .x13 (by decide), getReg_setReg_ne' .x7 .x13 (by decide),
          getReg_setReg_ne' .x6 .x13 (by decide), getReg_setReg_ne' .x5 .x13 (by decide)]; exact hw.rx13
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x17 .x14 (by decide), getReg_setReg_ne' .x16 .x14 (by decide),
          getReg_setReg_ne' .x15 .x14 (by decide), getReg_setReg_ne' .x7 .x14 (by decide),
          getReg_setReg_ne' .x6 .x14 (by decide), getReg_setReg_ne' .x5 .x14 (by decide)]; exact hw.rx14
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
    · refine ⟨?_, ?_, ?_, by rw [hpack]; rfl, ?_⟩
      · simp only [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setByte,
          getReg_setReg_ne' .x17 .x31 (by decide), getReg_setReg_ne' .x16 .x31 (by decide),
          getReg_setReg_ne' .x15 .x31 (by decide), getReg_setReg_ne' .x7 .x31 (by decide),
          getReg_setReg_ne' .x6 .x31 (by decide), getReg_setReg_ne' .x5 .x31 (by decide)]; exact ht.rx31
      · rw [hpack]; simp only [s11, s10, s9, MachineState.getReg_setPC,
          getReg_setReg_ne' .x17 .x15 (by decide), getReg_setReg_ne' .x16 .x15 (by decide)]; rfl
      · rw [hpack]; simp only [s11, s10, MachineState.getReg_setPC, getReg_setReg_ne' .x17 .x16 (by decide)]; rfl
      · rw [hpack]; intro j hj
        rw [hmem11, set_byte_read]
        have hjlen : j < acc.length + 1 := by simpa using hj
        by_cases hlast : j = acc.length
        · subst hlast
          rw [if_pos rfl, list_getElem_append_right acc [BitVec.ofNat 8 buf'] acc.length (by omega) hj]; simp
        · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega)),
            ht.memTail j (by omega), list_getElem_append_left acc [BitVec.ofNat 8 buf'] j (by omega)]
    · intro a ha
      rw [hmem11, set_byte_read, if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]

/-- Call `emit15` (`136..157`): emits 15 low bytes of `salt121Word16 (tdSalt trapdoor i)`. -/
private theorem openRuns_call_emit15 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx : Nat} {jOff : BitVec 21}
    {i : Index} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    (hcall : callIdx < 203)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 136)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + saltOff i))
    (hbd : fwdBytes.length + 15 ≤ 8239714016)
    (htbd : tails.length ≤ 300000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    let chunk := bitsToBytes (salt121Word16 (tdSalt trapdoor i)) 15
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps = 13 + 5 * ((fwdBytes ++ chunk).length / 8 - fwdBytes.length / 8) ∧
      s'.pc = pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x25 →
        s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' (fwdBytes ++ chunk) ∧
      TailState s' tails ∧
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro chunk
  have hclen : chunk.length = 15 := bitsToBytes_length _ 15
  let c8 := chunk.take 8
  let c7 := chunk.drop 8
  have hc8_len : c8.length = 8 := by simp [c8, hclen]
  have hc7_len : c7.length = 7 := by simp [c7, hclen]
  have hsplit : (fwdBytes ++ c8) ++ c7 = fwdBytes ++ chunk := by
    rw [List.append_assoc, List.take_append_drop]
  have hso_bd : saltOff i + 16 ≤ 1879048128 := by
    have := saltOff_add_16_le i; rw [trapdoorBytes_eq] at this; exact this
  have hso_al := saltOff_align8 i
  have hr_jal := step_JAL hcall hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 136)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  set qBase := fwdBytes.length / 8
  obtain ⟨s2, hr2, hpc2, hreg2, hwLo2, hwHi2, hmem2, hro2, hcap2, htail2⟩ :=
    openRuns_emit_dword (s := s1) (base := 136) (srcOff := saltOff i) (qBase := qBase) (k := 0) (imm := 0#12)
      (cur := fwdBytes) (chunk8 := c8) (by omega) (by decide)
      rfl rfl rfl rfl rfl rfl rfl (by exact hx10) hw.rx25 (by omega) hw.rx13 hw.rx14
      hw.wbufLo hw.wbufHi hw.memDwords hso_al (by omega) (by omega) hro1 hc8_len
      (fun j hj => by simpa [c8, chunk, List.getElem_take] using chunk_tdSalt15 trapdoor i j (by omega))
  -- 142: ADDI x25, x25, 8
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have h142 := step_ADDI (by omega) hpc2 (rfl : openingInstr 142 = .base (.ADDI .x25 .x25 (8#12)))
  have hnew25 : s2.getReg .x25 + signExtend12 (8#12) =
      BitVec.ofNat 64 (10603204576 + 8 * ((fwdBytes ++ c8).length / 8)) := by
    rw [hreg2 .x25 (by decide) (by decide) (by decide)]
    have hr25 : s1.getReg .x25 = BitVec.ofNat 64 (10603204576 + 8 * qBase) := hw.rx25
    rw [hr25, hse8, bv64_ofNat_add]; congr 1; simp only [List.length_append, hc8_len]; omega
  let s3 := (s2.setReg .x25 (BitVec.ofNat 64 (10603204576 + 8 * ((fwdBytes ++ c8).length / 8)))).setPC (pcAt 143)
  have h142' : OpenRuns s2 1 1 s3 := by simpa only [hnew25, s3] using h142
  -- 143..145: LD x5, 8(x10); SLLI x5, x5, 8; SRLI x5, x5, 8
  have haddr143 : s3.getReg .x10 + signExtend12 (8#12) = BitVec.ofNat 64 (4294971424 + (saltOff i + 8)) := by
    simp only [s3, MachineState.getReg_setPC, getReg_setReg_ne' .x25 .x10 (by decide),
      hreg2 .x10 (by decide) (by decide) (by decide)]
    have hr10 : s1.getReg .x10 = BitVec.ofNat 64 (4294971424 + saltOff i) := hx10
    rw [hr10, hse8, bv64_ofNat_add, Nat.add_assoc]
  set v1 := s3.getMem (BitVec.ofNat 64 (4294971424 + (saltOff i + 8)))
  have h143 := step_LD (by omega) (rfl : s3.pc = pcAt 143)
    (rfl : openingInstr 143 = .base (.LD .x5 .x10 (8#12)))
    (by rw [haddr143]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s4 := (s3.setReg .x5 v1).setPC (pcAt 144)
  have h143' : OpenRuns s3 1 1 s4 := by simpa only [haddr143, v1, s4] using h143
  have h144 := step_SLLI (by omega) (rfl : s4.pc = pcAt 144) (rfl : openingInstr 144 = .base (.SLLI .x5 .x5 (8#6)))
  let s5 := (s4.setReg .x5 (v1 <<< 8)).setPC (pcAt 145)
  have h144' : OpenRuns s4 1 1 s5 := by
    simpa only [show s4.getReg .x5 = v1 from rfl, show (8#6 : BitVec 6).toNat = 8 from rfl, s5] using h144
  have h145 := step_SRLI (by omega) (rfl : s5.pc = pcAt 145) (rfl : openingInstr 145 = .base (.SRLI .x5 .x5 (8#6)))
  let s6 := (s5.setReg .x5 ((v1 <<< 8) >>> 8)).setPC (pcAt 146)
  have h145' : OpenRuns s5 1 1 s6 := by
    simpa only [show s5.getReg .x5 = v1 <<< 8 from rfl, show (8#6 : BitVec 6).toNat = 8 from rfl, s6] using h145
  have hro6 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s6 := by
    intro a ha; simp only [s6, s5, s4, s3, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro2 a ha
  have hw6 : WriterState s6 (fwdBytes ++ c8) := by
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [s6, s5, s4, s3, MachineState.getReg_setPC, getReg_setReg_ne' .x5 .x13 (by decide),
        getReg_setReg_ne' .x25 .x13 (by decide), hreg2 .x13 (by decide) (by decide) (by decide)]
      have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * (fwdBytes.length % 8)) := hw.rx13
      rw [h]; congr 1; simp only [List.length_append, hc8_len]; omega
    · simp only [s6, s5, s4, s3, MachineState.getReg_setPC, getReg_setReg_ne' .x5 .x14 (by decide),
        getReg_setReg_ne' .x25 .x14 (by decide), hreg2 .x14 (by decide) (by decide) (by decide)]
      have h : s1.getReg .x14 = BitVec.ofNat 64 (63 - 8 * (fwdBytes.length % 8)) := hw.rx14
      rw [h]; congr 1; simp only [List.length_append, hc8_len]; omega
    · intro j hj
      simp only [s6, s5, s4, s3, MachineState.getReg_setPC, getReg_setReg_ne' .x5 .x12 (by decide),
        getReg_setReg_ne' .x25 .x12 (by decide)]
      exact hwLo2 j hj
    · intro j h1 h2
      simp only [s6, s5, s4, s3, MachineState.getReg_setPC, getReg_setReg_ne' .x5 .x12 (by decide),
        getReg_setReg_ne' .x25 .x12 (by decide)]
      exact hwHi2 j h1 h2
    · intro j hj; simp only [s6, s5, s4, s3, getByte_setPC, getByte_setReg]; exact hmem2 j hj
  have hx5_6 : ∀ j (hj : j < 8),
      (s6.getReg .x5).extractLsb' (8 * j) 8 = if hj' : j < 7 then c7[j]'(by omega) else 0#8 := by
    intro j hj
    change ((v1 <<< (8 * (8 - 7))) >>> (8 * (8 - 7))).extractLsb' (8 * j) 8 = _
    rw [word_mask_low_bytes v1 7 (by omega) j hj]
    by_cases hj7 : j < 7
    · rw [if_pos hj7, dif_pos hj7]
      have hro3 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s3 := by
        intro a ha; simp only [s3, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro2 a ha
      rw [readOnly_getMem_trapdoor_byte hro3 (saltOff i + 8) j (by omega) hj (by omega)]
      simpa [c7, chunk, List.getElem_drop, Nat.add_assoc] using chunk_tdSalt15 trapdoor i (8 + j) (by omega)
    · rw [if_neg hj7, dif_neg hj7]
  -- 146..156: emit_partial m=7
  obtain ⟨stP, s7, hrP, hstP, hpc7, hreg7, hro7, hw7, hcap7, htail7⟩ :=
    openRuns_emit_partial (base := 146) (m := 7) (immBits := 56#12)
      (fwdBytes := fwdBytes ++ c8) (chunkM := c7)
      (by omega) (by omega) (by omega) (by decide) (by decide)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl (by simp only [List.length_append, hc8_len]; omega) hro6 hw6 hc7_len hx5_6
  rw [hsplit] at hw7 hstP
  -- 157: JALR x0, x1, 0
  have hx1_7 : s7.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hreg7 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s6, s5, s4, s3, MachineState.getReg_setPC, getReg_setReg_ne' .x5 .x1 (by decide),
      getReg_setReg_ne' .x25 .x1 (by decide), hreg2 .x1 (by decide) (by decide) (by decide)]; rfl
  have hret := step_JALR_x0 (by omega) hpc7 (rfl : openingInstr 157 = .base (.JALR .x0 .x1 (0#12))) hx1_7
  let s8 := s7.setPC (pcAt (callIdx + 1))
  have hpres8 : ∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 → r ≠ .x25 →
      s8.getReg r = s.getReg r := fun r h1 h5 h6 h7 h12 h13 h14 h25 => by
    simp only [s8, MachineState.getReg_setPC, hreg7 r h5 h6 h7 h12 h13 h14 h25,
      s6, s5, s4, s3, getReg_setReg_ne' .x5 r (Ne.symm h5), getReg_setReg_ne' .x25 r (Ne.symm h25),
      hreg2 r h5 h6 h12]
    exact getReg_setReg_ne' .x1 r (Ne.symm h1) s _
  have hq_eq : (fwdBytes ++ c8).length / 8 = fwdBytes.length / 8 + 1 := by
    simp only [List.length_append, hc8_len]; omega
  have hq_ge : fwdBytes.length / 8 + 1 ≤ (fwdBytes ++ chunk).length / 8 := by
    simp only [List.length_append, hclen]; omega
  refine ⟨1 + 6 + 1 + 1 + 1 + 1 + stP + 1, s8,
    ((((((hr_jal.trans hr2).trans h142').trans h143').trans h144').trans h145').trans hrP).trans hret,
    by rw [hstP, hq_eq]; omega, rfl, hpres8, hro7,
    ⟨hw7.rx25, hw7.rx13, hw7.rx14, hw7.wbufLo, hw7.wbufHi, hw7.memDwords⟩,
    tailState_of_mem_eq ht htbd (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl <;>
        exact hpres8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun a ha1 ha2 => by
        simp only [s8, getByte_setPC]; rw [htail7 a ha1 ha2]
        simp only [s6, s5, s4, s3, getByte_setPC, getByte_setReg]; exact htail2 a ha1 ha2),
    fun a ha => by
      simp only [s8, getByte_setPC]; rw [hcap7 a ha]
      simp only [s6, s5, s4, s3, getByte_setPC, getByte_setReg]; exact hcap2 a ha⟩

/-- Call `emit29_t6` (`158..202`): emits 29 low bytes + 6-bit tail of `tdNode trapdoor l nodeIdx`. -/
private theorem openRuns_call_emit29_t6 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx l nodeIdx : Nat} {jOff : BitVec 21}
    {fwdBytes : List Byte} {tails : List (BitVec 6)}
    (hcall : callIdx < 203) (hl : l ≤ 24) (hidx : nodeIdx < levelSize l)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt 158)
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l nodeIdx)))
    (hbd : fwdBytes.length + 29 ≤ 8239714016)
    (htbd : tails.length < 300000000)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    let d := tdNode trapdoor l nodeIdx
    let fwd' := fwdBytes ++ bitsToBytes d 29
    let tails' := tails ++ [tail6 d]
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps = 22 + 5 * (fwd'.length / 8 - fwdBytes.length / 8) + 4 * (tailAccLen tails' - tailAccLen tails) ∧
      s'.pc = pcAt (callIdx + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
        r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      WriterState s' fwd' ∧
      TailState s' tails' ∧
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  intro d fwd' tails'
  set srcOff := levelBase l + nodeOffset l nodeIdx
  let chunk := bitsToBytes d 29
  have hclen : chunk.length = 29 := bitsToBytes_length d 29
  let c24 := chunk.take 24
  let c5 := chunk.drop 24
  have hc24_len : c24.length = 24 := by simp [c24, hclen]
  have hc5_len : c5.length = 5 := by simp [c5, hclen]
  have hsplit : (fwdBytes ++ c24) ++ c5 = fwd' := by
    change (fwdBytes ++ c24) ++ c5 = fwdBytes ++ chunk
    rw [List.append_assoc, List.take_append_drop]
  have htb : treeBytes = 1610612672 := treeBytes_eq
  have hsrc_bd : srcOff + 32 ≤ 1879048128 := by
    have := nodeOffset_lt_treeBytes l nodeIdx hl hidx; omega
  have hsrc_al : srcOff % 8 = 0 := by
    have h1 := levelBase_align8 l hl
    have h2 := nodeOffset_align8 l nodeIdx; omega
  have hr_jal := step_JAL hcall hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt 158)
  have hro1 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  have hw1 : WriterState s1 fwdBytes := hw.of_eq
  obtain ⟨s2, hr_3d, hpc2, hreg2, hro2, hw2, hcap2, htail2⟩ :=
    openRuns_emit_3dwords (base := 158) (srcOff := srcOff) (fwdBytes := fwdBytes) (chunk24 := c24)
      (by omega) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl (by exact hx10) hsrc_al (by omega) (by omega)
      hro1 hw1 hc24_len (fun j hj => by
        simpa [c24, chunk, d, srcOff, List.getElem_take] using chunk_tdNode trapdoor l nodeIdx 29 j (by omega) (by omega))
  -- 177..179: LD x11, 24(x10); SLLI x5, x11, 24; SRLI x5, x5, 24
  have hse24 : signExtend12 (24#12) = BitVec.ofNat 64 24 := by decide
  have haddr177 : s2.getReg .x10 + signExtend12 (24#12) = BitVec.ofNat 64 (4294971424 + (srcOff + 24)) := by
    rw [hreg2 .x10 (by decide) (by decide) (by decide) (by decide)]
    have hr10 : s1.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff) := hx10
    rw [hr10, hse24, bv64_ofNat_add, Nat.add_assoc]
  set v3 := s2.getMem (BitVec.ofNat 64 (4294971424 + (srcOff + 24)))
  have h177 := step_LD (by omega) hpc2 (rfl : openingInstr 177 = .base (.LD .x11 .x10 (24#12)))
    (by rw [haddr177]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s3 := (s2.setReg .x11 v3).setPC (pcAt 178)
  have h177' : OpenRuns s2 1 1 s3 := by simpa only [haddr177, v3, s3] using h177
  have h178 := step_SLLI (by omega) (rfl : s3.pc = pcAt 178) (rfl : openingInstr 178 = .base (.SLLI .x5 .x11 (24#6)))
  let s4 := (s3.setReg .x5 (v3 <<< 24)).setPC (pcAt 179)
  have h178' : OpenRuns s3 1 1 s4 := by
    simpa only [show s3.getReg .x11 = v3 from rfl, show (24#6 : BitVec 6).toNat = 24 from rfl, s4] using h178
  have h179 := step_SRLI (by omega) (rfl : s4.pc = pcAt 179) (rfl : openingInstr 179 = .base (.SRLI .x5 .x5 (24#6)))
  let s5 := (s4.setReg .x5 ((v3 <<< 24) >>> 24)).setPC (pcAt 180)
  have h179' : OpenRuns s4 1 1 s5 := by
    simpa only [show s4.getReg .x5 = v3 <<< 24 from rfl, show (24#6 : BitVec 6).toNat = 24 from rfl, s5] using h179
  have hro5 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s5 := by
    intro a ha; simp only [s5, s4, s3, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro2 a ha
  have hw5 : WriterState s5 (fwdBytes ++ c24) := hw2.of_eq
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
  -- 180..190: emit_partial m=5
  obtain ⟨stP, s6, hrP, hstP, hpc6, hreg6, hro6, hw6, hcap6, htail6⟩ :=
    openRuns_emit_partial (base := 180) (m := 5) (immBits := 40#12)
      (fwdBytes := fwdBytes ++ c24) (chunkM := c5)
      (by omega) (by omega) (by omega) (by decide) (by decide)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl (by simp only [List.length_append, hc24_len]; omega) hro5 hw5 hc5_len hx5_5
  rw [hsplit] at hw6 hstP
  -- 191..201: push 6-bit tail
  have hx11_6 : (s6.getReg .x11).extractLsb' (8 * 5) 8 = d.extractLsb' (8 * 29) 8 := by
    have h11 : s6.getReg .x11 = v3 := by
      rw [hreg6 .x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
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
      rw [htail6 a ha1 ha2]; simp only [s5, s4, s3, getByte_setPC, getByte_setReg]; exact htail2 a ha1 ha2)
  have hfwd'_len : fwd'.length = fwdBytes.length + 29 := by
    simp only [fwd', List.length_append, bitsToBytes_length]
  obtain ⟨stT, s7, hrT, hstT, hpc7, hreg7, hro7, hw7, ht7, hcap7⟩ :=
    openRuns_push_tail6 hpc6 hx11_6 (by omega)
      htbd hro6 hw6 ht6
  -- 202: JALR x0, x1, 0
  have hx1_7 : s7.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hreg7 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg6 .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp only [s5, s4, s3, MachineState.getReg_setPC,
      getReg_setReg_ne' .x5 .x1 (by decide), getReg_setReg_ne' .x11 .x1 (by decide)]
    rw [hreg2 .x1 (by decide) (by decide) (by decide) (by decide)]; rfl
  have hret := step_JALR_x0 (by omega) hpc7 (rfl : openingInstr 202 = .base (.JALR .x0 .x1 (0#12))) hx1_7
  let s8 := s7.setPC (pcAt (callIdx + 1))
  have hpres8 : ∀ r, r ≠ .x1 → r ≠ .x5 → r ≠ .x6 → r ≠ .x7 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x14 →
      r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ .x25 → s8.getReg r = s.getReg r :=
    fun r h1 h5 h6 h7 h11 h12 h13 h14 h15 h16 h17 h25 => by
      simp only [s8, MachineState.getReg_setPC]
      rw [hreg7 r h5 h6 h7 h15 h16 h17, hreg6 r h5 h6 h7 h12 h13 h14 h25]
      simp only [s5, s4, s3, MachineState.getReg_setPC,
        getReg_setReg_ne' .x5 r (Ne.symm h5), getReg_setReg_ne' .x11 r (Ne.symm h11)]
      rw [hreg2 r h5 h6 h12 h25]; exact getReg_setReg_ne' .x1 r (Ne.symm h1) s _
  have hq_eq : (fwdBytes ++ c24).length / 8 = fwdBytes.length / 8 + 3 := by
    simp only [List.length_append, hc24_len]; omega
  have hq_ge : fwdBytes.length / 8 + 3 ≤ fwd'.length / 8 := by omega
  have hta_mono : tailAccLen tails ≤ tailAccLen (tails ++ [tail6 d]) := tailAccLen_mono_append _ _
  refine ⟨1 + 19 + 1 + 1 + 1 + stP + stT + 1, s8,
    ((((((hr_jal.trans hr_3d).trans h177').trans h178').trans h179').trans hrP).trans hrT).trans hret,
    by rw [hstP, hstT, hq_eq]; dsimp only [fwd', tails', d] at hq_ge hta_mono ⊢; omega, rfl, hpres8, hro7,
    hw7.of_eq, ht7.of_eq,
    fun a ha => by
      simp only [s8, getByte_setPC]; rw [hcap7 a ha, hcap6 a ha]
      simp only [s5, s4, s3, getByte_setPC, getByte_setReg]; exact hcap2 a ha⟩

/-! ### 6. Entry (`0..23`), Empty Epilogue (`132..135`), and Pass 0 (`24..58`: `packSaltTopBits`) -/

private theorem opening_initial_regs (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    s0.pc = pcAt 0 ∧
    s0.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
    s0.getReg .x12 = BitVec.ofNat 64 4294971424 ∧
    s0.getReg .x13 = BitVec.ofNat 64 6174019552 ∧
    s0.getReg .x15 = BitVec.ofNat 64 10603204576 ∧
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
      s5.getReg .x24 = BitVec.ofNat 64 6174019552 ∧
      s5.getReg .x25 = BitVec.ofNat 64 10603204576 ∧
      s5.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
      s5.getReg .x27 = BitVec.ofNat 64 positions.card ∧
      s5.mem = s0.mem := by
  intro s0
  obtain ⟨hpc0, hx2, hx12, hx13, hx15, hx16⟩ := opening_initial_regs trapdoor positions
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have h1 := step_ADDI (by omega) hpc0 (rfl : openingInstr 0 = .base (.ADDI .x9 .x12 (0#12)))
  let s1 := (s0.setReg .x9 (BitVec.ofNat 64 4294971424)).setPC (pcAt 1)
  have h1' : OpenRuns s0 1 1 s1 := by simpa only [hx12, hse0, bv64_ofNat_add, Nat.add_zero, s1] using h1
  have h2 := step_ADDI (by omega) (rfl : s1.pc = pcAt 1) (rfl : openingInstr 1 = .base (.ADDI .x24 .x13 (0#12)))
  let s2 := (s1.setReg .x24 (BitVec.ofNat 64 6174019552)).setPC (pcAt 2)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hr : s1.getReg .x13 = BitVec.ofNat 64 6174019552 := hx13
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 2) (rfl : openingInstr 2 = .base (.ADDI .x25 .x15 (0#12)))
  let s3 := (s2.setReg .x25 (BitVec.ofNat 64 10603204576)).setPC (pcAt 3)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hr : s2.getReg .x15 = BitVec.ofNat 64 10603204576 := hx15
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s3] using h3
  have h4 := step_ADDI (by omega) (rfl : s3.pc = pcAt 3) (rfl : openingInstr 3 = .base (.ADDI .x26 .x15 (0#12)))
  let s4 := (s3.setReg .x26 (BitVec.ofNat 64 10603204576)).setPC (pcAt 4)
  have h4' : OpenRuns s3 1 1 s4 := by
    have hr : s3.getReg .x15 = BitVec.ofNat 64 10603204576 := hx15
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s4] using h4
  have h5 := step_ADDI (by omega) (rfl : s4.pc = pcAt 4) (rfl : openingInstr 4 = .base (.ADDI .x27 .x16 (0#12)))
  let s5 := (s4.setReg .x27 (BitVec.ofNat 64 positions.card)).setPC (pcAt 5)
  have h5' : OpenRuns s4 1 1 s5 := by
    have hr : s4.getReg .x16 = BitVec.ofNat 64 positions.card := hx16
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s5] using h5
  exact ⟨s5, (((h1'.trans h2').trans h3').trans h4').trans h5', rfl, hx2, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem openRuns_empty_epilogue {s : MachineState} (hpc : s.pc = pcAt 132) :
    ∃ sHalt, OpenRuns s 3 3 sHalt ∧
      sHalt.pc = pcAt 135 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = 0#64 ∧
      sHalt.mem = s.mem := by
  have h1 := step_ADDI (by omega) hpc (rfl : openingInstr 132 = .base (.ADDI .x11 .x0 (0#12)))
  let s1 := (s.setReg .x11 0#64).setPC (pcAt 133)
  have h1' : OpenRuns s 1 1 s1 := by
    have hv : s.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s1] using h1
  have h2 := step_ADDI (by omega) (rfl : s1.pc = pcAt 133) (rfl : openingInstr 133 = .base (.ADDI .x5 .x0 (1#12)))
  let s2 := (s1.setReg .x5 1#64).setPC (pcAt 134)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x0 + signExtend12 (1#12) = 1#64 := by change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 134) (rfl : openingInstr 134 = .base (.ADDI .x10 .x0 (0#12)))
  let s3 := (s2.setReg .x10 0#64).setPC (pcAt 135)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hv : s2.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s3] using h3
  exact ⟨s3, (h1'.trans h2').trans h3', rfl, rfl, rfl, rfl, rfl⟩

private theorem openRuns_entry_nonzero (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (hne : positions.card ≠ 0) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ s24, OpenRuns s0 24 24 s24 ∧
      s24.pc = pcAt 24 ∧
      s24.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s24.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s24.getReg .x10 = 0#64 ∧
      s24.getReg .x11 = 0#64 ∧
      s24.getReg .x12 = 0#64 ∧
      s24.getReg .x13 = 0#64 ∧
      s24.getReg .x14 = BitVec.ofNat 64 63 ∧
      s24.getReg .x15 = BitVec.ofNat 64 tailBufBase ∧
      s24.getReg .x16 = 0#64 ∧
      s24.getReg .x17 = 0#64 ∧
      s24.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff) ∧
      s24.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s24.getReg .x24 = BitVec.ofNat 64 6174019552 ∧
      s24.getReg .x25 = BitVec.ofNat 64 10603204576 ∧
      s24.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
      s24.getReg .x27 = BitVec.ofNat 64 positions.card ∧
      s24.getReg .x28 = BitVec.ofNat 64 6174019552 ∧
      s24.getReg .x29 = BitVec.ofNat 64 positions.card ∧
      s24.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
      s24.mem = s0.mem := by
  intro s0
  obtain ⟨s5, hr5, hpc5, hx2, hx9, hx24, hx25, hx26, hx27, hmem5⟩ :=
    openRuns_entry_prefix trapdoor positions
  have hcard := positions_card_le positions
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have h6 := step_BEQ_not_taken (by omega) hpc5
    (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (508#13)))
    (by rw [hx27]; exact bv64_ofNat_ne (by omega) (by decide) hne)
  let s6 := s5.setPC (pcAt 6)
  have h7 := step_ADDI (by omega) (rfl : s6.pc = pcAt 6) (rfl : openingInstr 6 = .base (.ADDI .x12 .x0 (0#12)))
  let s7 := (s6.setReg .x12 0#64).setPC (pcAt 7)
  have h7' : OpenRuns s6 1 1 s7 := by
    have hv : s6.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s7] using h7
  have h8 := step_ADDI (by omega) (rfl : s7.pc = pcAt 7) (rfl : openingInstr 7 = .base (.ADDI .x13 .x0 (0#12)))
  let s8 := (s7.setReg .x13 0#64).setPC (pcAt 8)
  have h8' : OpenRuns s7 1 1 s8 := by
    have hv : s7.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s8] using h8
  have h9 := step_ADDI (by omega) (rfl : s8.pc = pcAt 8) (rfl : openingInstr 8 = .base (.ADDI .x14 .x0 (63#12)))
  let s9 := (s8.setReg .x14 (BitVec.ofNat 64 63)).setPC (pcAt 9)
  have h9' : OpenRuns s8 1 1 s9 := by
    have hv : s8.getReg .x0 + signExtend12 (63#12) = BitVec.ofNat 64 63 := by
      change (0#64 : Word) + signExtend12 (63#12) = BitVec.ofNat 64 63; decide
    simpa only [hv, s9] using h9
  have h10 := step_ADDI (by omega) (rfl : s9.pc = pcAt 9) (rfl : openingInstr 9 = .base (.ADDI .x31 .x0 (3#12)))
  let s10 := (s9.setReg .x31 3#64).setPC (pcAt 10)
  have h10' : OpenRuns s9 1 1 s10 := by
    have hv : s9.getReg .x0 + signExtend12 (3#12) = 3#64 := by change (0#64 : Word) + signExtend12 (3#12) = 3#64; decide
    simpa only [hv, s10] using h10
  have h11 := step_SLLI (by omega) (rfl : s10.pc = pcAt 10) (rfl : openingInstr 10 = .base (.SLLI .x31 .x31 (33#6)))
  let s11 := (s10.setReg .x31 (BitVec.ofNat 64 tailBufBase)).setPC (pcAt 11)
  have h11' : OpenRuns s10 1 1 s11 := by
    have hv : s10.getReg .x31 <<< (33#6 : BitVec 6).toNat = BitVec.ofNat 64 tailBufBase := by
      change (3#64 : Word) <<< (33#6 : BitVec 6).toNat = BitVec.ofNat 64 25769803776; decide
    simpa only [hv, s11] using h11
  have h12 := step_ADDI (by omega) (rfl : s11.pc = pcAt 11) (rfl : openingInstr 11 = .base (.ADDI .x15 .x31 (0#12)))
  let s12 := (s11.setReg .x15 (BitVec.ofNat 64 tailBufBase)).setPC (pcAt 12)
  have h12' : OpenRuns s11 1 1 s12 := by
    have hv : s11.getReg .x31 + signExtend12 (0#12) = BitVec.ofNat 64 tailBufBase := by
      change BitVec.ofNat 64 25769803776 + signExtend12 (0#12) = BitVec.ofNat 64 25769803776; decide
    simpa only [hv, s12] using h12
  have h13 := step_ADDI (by omega) (rfl : s12.pc = pcAt 12) (rfl : openingInstr 12 = .base (.ADDI .x16 .x0 (0#12)))
  let s13 := (s12.setReg .x16 0#64).setPC (pcAt 13)
  have h13' : OpenRuns s12 1 1 s13 := by
    have hv : s12.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s13] using h13
  have h14 := step_ADDI (by omega) (rfl : s13.pc = pcAt 13) (rfl : openingInstr 13 = .base (.ADDI .x17 .x0 (0#12)))
  let s14 := (s13.setReg .x17 0#64).setPC (pcAt 14)
  have h14' : OpenRuns s13 1 1 s14 := by
    have hv : s13.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s14] using h14
  have h15 := step_ADDI (by omega) (rfl : s14.pc = pcAt 14) (rfl : openingInstr 14 = .base (.ADDI .x6 .x0 (1536#12)))
  let s15 := (s14.setReg .x6 (BitVec.ofNat 64 1536)).setPC (pcAt 15)
  have h15' : OpenRuns s14 1 1 s15 := by
    have hv : s14.getReg .x0 + signExtend12 (1536#12) = BitVec.ofNat 64 1536 := by
      change (0#64 : Word) + signExtend12 (1536#12) = BitVec.ofNat 64 1536; decide
    simpa only [hv, s15] using h15
  have h16 := step_SLLI (by omega) (rfl : s15.pc = pcAt 15) (rfl : openingInstr 15 = .base (.SLLI .x6 .x6 (20#6)))
  let s16 := (s15.setReg .x6 (BitVec.ofNat 64 1610612736)).setPC (pcAt 16)
  have h16' : OpenRuns s15 1 1 s16 := by
    have hv : s15.getReg .x6 <<< (20#6 : BitVec 6).toNat = BitVec.ofNat 64 1610612736 := by
      change BitVec.ofNat 64 1536 <<< (20#6 : BitVec 6).toNat = BitVec.ofNat 64 1610612736; decide
    simpa only [hv, s16] using h16
  have h17 := step_ADDI (by omega) (rfl : s16.pc = pcAt 16) (rfl : openingInstr 16 = .base (.ADDI .x6 .x6 (4032#12)))
  let s17 := (s16.setReg .x6 (BitVec.ofNat 64 saltsOff)).setPC (pcAt 17)
  have h17' : OpenRuns s16 1 1 s17 := by
    have hv : s16.getReg .x6 + signExtend12 (4032#12) = BitVec.ofNat 64 saltsOff := by
      rw [saltsOff_eq]; change BitVec.ofNat 64 1610612736 + signExtend12 (4032#12) = BitVec.ofNat 64 1610612672; decide
    simpa only [hv, s17] using h17
  have h18 := step_ADD (by omega) (rfl : s17.pc = pcAt 17) (rfl : openingInstr 17 = .base (.ADD .x18 .x9 .x6))
  let s18 := (s17.setReg .x18 (BitVec.ofNat 64 (4294971424 + saltsOff))).setPC (pcAt 18)
  have h18' : OpenRuns s17 1 1 s18 := by
    have hr9 : s17.getReg .x9 = BitVec.ofNat 64 4294971424 := hx9
    simpa only [hr9, show s17.getReg .x6 = BitVec.ofNat 64 saltsOff from rfl, bv64_ofNat_add, s18] using h18
  have h19 := step_ADDI (by omega) (rfl : s18.pc = pcAt 18) (rfl : openingInstr 18 = .base (.ADDI .x21 .x0 (2#12)))
  let s19 := (s18.setReg .x21 (BitVec.ofNat 64 2)).setPC (pcAt 19)
  have h19' : OpenRuns s18 1 1 s19 := by
    have hv : s18.getReg .x0 + signExtend12 (2#12) = BitVec.ofNat 64 2 := by
      change (0#64 : Word) + signExtend12 (2#12) = BitVec.ofNat 64 2; decide
    simpa only [hv, s19] using h19
  have h20 := step_SLLI (by omega) (rfl : s19.pc = pcAt 19) (rfl : openingInstr 19 = .base (.SLLI .x21 .x21 (11#6)))
  let s20 := (s19.setReg .x21 (BitVec.ofNat 64 4096)).setPC (pcAt 20)
  have h20' : OpenRuns s19 1 1 s20 := by
    have hv : s19.getReg .x21 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096 := by
      change BitVec.ofNat 64 2 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096; decide
    simpa only [hv, s20] using h20
  have h21 := step_ADDI (by omega) (rfl : s20.pc = pcAt 20) (rfl : openingInstr 20 = .base (.ADDI .x28 .x24 (0#12)))
  let s21 := (s20.setReg .x28 (BitVec.ofNat 64 6174019552)).setPC (pcAt 21)
  have h21' : OpenRuns s20 1 1 s21 := by
    have hr24 : s20.getReg .x24 = BitVec.ofNat 64 6174019552 := hx24
    simpa only [hr24, hse0, bv64_ofNat_add, Nat.add_zero, s21] using h21
  have h22 := step_ADDI (by omega) (rfl : s21.pc = pcAt 21) (rfl : openingInstr 21 = .base (.ADDI .x29 .x27 (0#12)))
  let s22 := (s21.setReg .x29 (BitVec.ofNat 64 positions.card)).setPC (pcAt 22)
  have h22' : OpenRuns s21 1 1 s22 := by
    have hr27 : s21.getReg .x27 = BitVec.ofNat 64 positions.card := hx27
    simpa only [hr27, hse0, bv64_ofNat_add, Nat.add_zero, s22] using h22
  have h23 := step_ADDI (by omega) (rfl : s22.pc = pcAt 22) (rfl : openingInstr 22 = .base (.ADDI .x10 .x0 (0#12)))
  let s23 := (s22.setReg .x10 0#64).setPC (pcAt 23)
  have h23' : OpenRuns s22 1 1 s23 := by
    have hv : s22.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s23] using h23
  have h24 := step_ADDI (by omega) (rfl : s23.pc = pcAt 23) (rfl : openingInstr 23 = .base (.ADDI .x11 .x0 (0#12)))
  let s24 := (s23.setReg .x11 0#64).setPC (pcAt 24)
  have h24' : OpenRuns s23 1 1 s24 := by
    have hv : s23.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s24] using h24
  have ha := ((((((hr5.trans h6).trans h7').trans h8').trans h9').trans h10').trans h11').trans h12'
  have hb := ((((((ha.trans h13').trans h14').trans h15').trans h16').trans h17').trans h18').trans h19'
  have htot := ((((hb.trans h20').trans h21').trans h22').trans h23').trans h24'
  exact ⟨s24, htot, rfl, hx2, hx9, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hx24, hx25, hx26, hx27, rfl, rfl, rfl, hmem5⟩

/-- Shared 9-word byte-push block used at words `36..44` and `49..57` of Pass 0. -/
private theorem openRuns_salt_push_byte {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {base : Nat} {fwdBytes : List Byte} {b : Byte}
    (hbase : base + 8 < 203)
    (hbr : pcAt (base + 4) + signExtend13 (20#13) = pcAt (base + 9))
    (hc : openingInstr base = .base (.SLL .x6 .x10 .x13) ∧
      openingInstr (base + 1) = .base (.OR .x12 .x12 .x6) ∧
      openingInstr (base + 2) = .base (.ADDI .x13 .x13 (8#12)) ∧
      openingInstr (base + 3) = .base (.ADDI .x7 .x0 (64#12)) ∧
      openingInstr (base + 4) = .base (.BNE .x13 .x7 (20#13)) ∧
      openingInstr (base + 5) = .base (.SD .x25 .x12 (0#12)) ∧
      openingInstr (base + 6) = .base (.ADDI .x25 .x25 (8#12)) ∧
      openingInstr (base + 7) = .base (.ADDI .x12 .x0 (0#12)) ∧
      openingInstr (base + 8) = .base (.ADDI .x13 .x0 (0#12)))
    (hpc : s.pc = pcAt base)
    (hx10 : s.getReg .x10 = b.zeroExtend 64)
    (hbd : fwdBytes.length + 1 ≤ 8239714016)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hw : SaltWriterState s fwdBytes) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 9 ∧
      s'.pc = pcAt (base + 9) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x12 → r ≠ .x13 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      SaltWriterState s' (fwdBytes ++ [b]) ∧
      (∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) ∧
      (∀ q, tailBufBase ≤ q → q < 68719475936 →
        s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  set r := fwdBytes.length % 8
  set q := fwdBytes.length / 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  set v := b.zeroExtend 64
  set w := s.getReg .x12
  set wOut := w ||| (v <<< (8 * r))
  have h0 := step_SLL (by omega) hpc hc.1
  have hx13_mod : (s.getReg .x13).toNat % 64 = 8 * r := by
    rw [hw.rx13, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 8 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  let s1 := (s.setReg .x6 (v <<< (8 * r))).setPC (pcAt (base + 1))
  have h0' : OpenRuns s 1 1 s1 := by simpa only [hx10, hx13_mod, v, s1] using h0
  have h1 := step_OR (by omega) (rfl : s1.pc = pcAt (base + 1)) hc.2.1
  let s2 := (s1.setReg .x12 wOut).setPC (pcAt (base + 2))
  have h1' : OpenRuns s1 1 1 s2 := by
    simpa only [show s1.getReg .x12 = w from rfl, show s1.getReg .x6 = v <<< (8 * r) from rfl,
      wOut, s2, show base + 1 + 1 = base + 2 by omega] using h1
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have h2 := step_ADDI (by omega) (rfl : s2.pc = pcAt (base + 2)) hc.2.2.1
  let s3 := (s2.setReg .x13 (BitVec.ofNat 64 (8 * (r + 1)))).setPC (pcAt (base + 3))
  have h2' : OpenRuns s2 1 1 s3 := by
    have hr13 : s2.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13
    have hv : s2.getReg .x13 + signExtend12 (8#12) = BitVec.ofNat 64 (8 * (r + 1)) := by
      rw [hr13, hse8, bv64_ofNat_add]; exact congrArg (BitVec.ofNat 64) (by omega)
    simpa only [hv, s3, show base + 2 + 1 = base + 3 by omega] using h2
  have h3 := step_ADDI (by omega) (rfl : s3.pc = pcAt (base + 3)) hc.2.2.2.1
  let s4 := (s3.setReg .x7 64#64).setPC (pcAt (base + 4))
  have h3' : OpenRuns s3 1 1 s4 := by
    have hv : s3.getReg .x0 + signExtend12 (64#12) = 64#64 := by
      change (0#64 : Word) + signExtend12 (64#12) = 64#64; decide
    simpa only [hv, s4, show base + 3 + 1 = base + 4 by omega] using h3
  have hpre : OpenRuns s 4 4 s4 := ((h0'.trans h1').trans h2').trans h3'
  have hlen_app : (fwdBytes ++ [b]).length = fwdBytes.length + 1 := by simp
  by_cases hlt : r + 1 < 8
  · have h4 := step_BNE_taken (by omega) (rfl : s4.pc = pcAt (base + 4)) hc.2.2.2.2.1
      (by change BitVec.ofNat 64 (8 * (r + 1)) ≠ BitVec.ofNat 64 64
          exact bv64_ofNat_ne (by omega) (by decide) (by omega)) hbr
    let s9 := s4.setPC (pcAt (base + 9))
    have hq' : (fwdBytes ++ [b]).length / 8 = q := by omega
    have hr' : (fwdBytes ++ [b]).length % 8 = r + 1 := by omega
    refine ⟨5, s9, hpre.trans h4, by omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro reg h6 h7 h12 h13 _
      simp only [s9, s4, s3, s2, s1, MachineState.getReg_setPC,
        getReg_setReg_ne' .x7 reg (Ne.symm h7), getReg_setReg_ne' .x13 reg (Ne.symm h13),
        getReg_setReg_ne' .x12 reg (Ne.symm h12), getReg_setReg_ne' .x6 reg (Ne.symm h6)]
    · intro a ha; simp only [s9, s4, s3, s2, s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
    · refine ⟨by rw [hq']; exact hw.rx25, by rw [hr']; rfl, ?_, ?_, ?_⟩
      · intro j hj
        change wOut.extractLsb' (8 * j) 8 = _
        rw [word_or_shl_byte w v r hr hw.wbufHi j (by omega)]
        by_cases hjr : j < r
        · rw [if_pos hjr, hw.wbufLo j hjr,
            list_getElem_append_left fwdBytes [b] (8 * ((fwdBytes ++ [b]).length / 8) + j) (by omega)]
          congr 1; omega
        · have hj_eq : j = r := by omega
          subst hj_eq
          rw [if_neg (Nat.lt_irrefl _), Nat.sub_self, byte_zeroExtend_extractByte b 0 (by omega), if_pos rfl,
            list_getElem_append_right fwdBytes [b] (8 * ((fwdBytes ++ [b]).length / 8) + r) (by omega) (by omega)]
          simp [show 8 * ((fwdBytes ++ [b]).length / 8) + r - fwdBytes.length = 0 by omega]
      · intro j hj1 hj2
        change wOut.extractLsb' (8 * j) 8 = 0#8
        rw [word_or_shl_byte w v r hr hw.wbufHi j hj2, if_neg (by omega),
          byte_zeroExtend_extractByte b (j - r) (by omega), if_neg (by omega)]
      · intro j hj
        simp only [s9, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
        rw [hw.memDwords j (by omega), list_getElem_append_left fwdBytes [b] j (by omega)]
    · intro a _; simp only [s9, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
    · intro a _ _; simp only [s9, s4, s3, s2, s1, getByte_setPC, getByte_setReg]
  · have hr7 : r = 7 := by omega
    have hq' : (fwdBytes ++ [b]).length / 8 = q + 1 := by omega
    have hr' : (fwdBytes ++ [b]).length % 8 = 0 := by omega
    have h4 := step_BNE_not_taken (by omega) (rfl : s4.pc = pcAt (base + 4)) hc.2.2.2.2.1
      (by change BitVec.ofNat 64 (8 * (r + 1)) = 64#64; rw [hr7])
    let s5 := s4.setPC (pcAt (base + 5))
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hdstAddr : s5.getReg .x25 + signExtend12 (0#12) = BitVec.ofNat 64 (10603204576 + 8 * q) := by
      have hr25 : s5.getReg .x25 = BitVec.ofNat 64 (10603204576 + 8 * q) := hw.rx25
      rw [hr25, hse0, bv64_ofNat_add, Nat.add_zero]
    have h5 := step_SD (by omega) (rfl : s5.pc = pcAt (base + 5)) hc.2.2.2.2.2.1
      (by rw [hdstAddr]; exact accessValid_ofNat _ 8 (by omega) (by omega))
    let s6 := (s5.setMem (BitVec.ofNat 64 (10603204576 + 8 * q)) wOut).setPC (pcAt (base + 6))
    have h5' : OpenRuns s5 1 1 s6 := by
      simpa only [hdstAddr, show s5.getReg .x12 = wOut from rfl, s6, show base + 5 + 1 = base + 6 by omega] using h5
    have h6 := step_ADDI (by omega) (rfl : s6.pc = pcAt (base + 6)) hc.2.2.2.2.2.2.1
    let s7 := (s6.setReg .x25 (BitVec.ofNat 64 (10603204576 + 8 * (q + 1)))).setPC (pcAt (base + 7))
    have h6' : OpenRuns s6 1 1 s7 := by
      have hr25 : s6.getReg .x25 = BitVec.ofNat 64 (10603204576 + 8 * q) := by
        simp only [s6, MachineState.getReg_setPC, getReg_setMem]; exact hw.rx25
      have hv : s6.getReg .x25 + signExtend12 (8#12) = BitVec.ofNat 64 (10603204576 + 8 * (q + 1)) := by
        rw [hr25, hse8, bv64_ofNat_add]; congr 1
      simpa only [hv, s7, show base + 6 + 1 = base + 7 by omega] using h6
    have h7 := step_ADDI (by omega) (rfl : s7.pc = pcAt (base + 7)) hc.2.2.2.2.2.2.2.1
    let s8 := (s7.setReg .x12 0#64).setPC (pcAt (base + 8))
    have h7' : OpenRuns s7 1 1 s8 := by
      have hv : s7.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
      simpa only [hv, s8, show base + 7 + 1 = base + 8 by omega] using h7
    have h8 := step_ADDI (by omega) (rfl : s8.pc = pcAt (base + 8)) hc.2.2.2.2.2.2.2.2
    let s9 := (s8.setReg .x13 0#64).setPC (pcAt (base + 9))
    have h8' : OpenRuns s8 1 1 s9 := by
      have hv : s8.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
      simpa only [hv, s9, show base + 8 + 1 = base + 9 by omega] using h8
    have hmem9 : ∀ a, s9.getByte a =
        (s.setMem (BitVec.ofNat 64 (10603204576 + 8 * q)) wOut).getByte a := fun a => by
      simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, getByte_setPC, getByte_setReg]; rfl
    refine ⟨9, s9, hpre.trans ((((h4.trans h5').trans h6').trans h7').trans h8'), Nat.le_refl 9, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro reg h6ne h7ne h12ne h13ne h25ne
      simp only [s9, s8, s7, s6, s5, s4, s3, s2, s1, MachineState.getReg_setPC, getReg_setMem,
        getReg_setReg_ne' .x13 reg (Ne.symm h13ne), getReg_setReg_ne' .x12 reg (Ne.symm h12ne),
        getReg_setReg_ne' .x25 reg (Ne.symm h25ne), getReg_setReg_ne' .x7 reg (Ne.symm h7ne),
        getReg_setReg_ne' .x6 reg (Ne.symm h6ne)]
    · intro a ha
      change (s.setMem (BitVec.ofNat 64 (10603204576 + 8 * q)) wOut).getMem a = _
      exact readOnly_setMem_proof (10603204576 + 8 * q) wOut hro (by omega) (by omega) a ha
    · refine ⟨?_, by rw [hr']; rfl, fun j hj => by omega, ?_, ?_⟩
      · rw [hq']; simp only [s9, s8, s7, MachineState.getReg_setPC,
          getReg_setReg_ne' .x13 .x25 (by decide), getReg_setReg_ne' .x12 .x25 (by decide)]; rfl
      · intro j _ hj
        simp only [s9, s8, MachineState.getReg_setPC, getReg_setReg_ne' .x13 .x12 (by decide)]
        change (0#64 : Word).extractLsb' (8 * j) 8 = 0#8
        apply BitVec.eq_of_getLsbD_eq; intro k hk; simp
      · intro j hj
        rw [hmem9]
        by_cases hltq : j < 8 * q
        · rw [setMem_getByte_ofNat s (10603204576 + 8 * q) (10603204576 + j) wOut
            (by omega) (by omega) (by omega) (by omega)]
          rw [hw.memDwords j hltq, list_getElem_append_left fwdBytes [b] j (by omega)]
        · have hu : j - 8 * q < 8 := by omega
          have hadd : 10603204576 + 8 * q + (j - 8 * q) = 10603204576 + j := by omega
          rw [← hadd, setMem_getByte_inside s (10603204576 + 8 * q) (j - 8 * q) wOut (by omega) hu]
          rw [word_or_shl_byte w v r hr hw.wbufHi (j - 8 * q) hu]
          by_cases hur : j - 8 * q < r
          · rw [if_pos hur, hw.wbufLo (j - 8 * q) hur, list_getElem_append_left fwdBytes [b] j (by omega)]
            congr 1; omega
          · have hj_eq : j - 8 * q = r := by omega
            rw [if_neg hur, hj_eq, Nat.sub_self, byte_zeroExtend_extractByte b 0 (by omega), if_pos rfl,
              list_getElem_append_right fwdBytes [b] j (by omega) (by omega)]
            simp [show j - fwdBytes.length = 0 by omega]
    · intro a ha
      rw [hmem9, setMem_getByte_ofNat s (10603204576 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]
    · intro a ha1 ha2
      have htb : tailBufBase = 25769803776 := rfl
      rw [hmem9, setMem_getByte_ofNat s (10603204576 + 8 * q) a wOut
        (by omega) (by omega) (by omega) (by omega)]

/-- Pass 0 (`24..58`): emits `packSaltTopBits (tdSalt trapdoor) positions` and restores `WriterState`. -/
private theorem openRuns_salt_top {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s24 : MachineState}
    (hne : 0 < positions.card) (hpc : s24.pc = pcAt 24)
    (hx2 : s24.getReg .x2 = BitVec.ofNat 64 68719475936)
    (hx9 : s24.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx10 : s24.getReg .x10 = 0#64) (hx11 : s24.getReg .x11 = 0#64)
    (hx18 : s24.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff))
    (hx21 : s24.getReg .x21 = BitVec.ofNat 64 4096)
    (hx24 : s24.getReg .x24 = BitVec.ofNat 64 6174019552)
    (hx26 : s24.getReg .x26 = BitVec.ofNat 64 10603204576)
    (hx27 : s24.getReg .x27 = BitVec.ofNat 64 positions.card)
    (hx28 : s24.getReg .x28 = BitVec.ofNat 64 6174019552)
    (hx29 : s24.getReg .x29 = BitVec.ofNat 64 positions.card)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s24)
    (hsw : SaltWriterState s24 [])
    (ht0 : TailState s24 [])
    (hcap0 : ∀ q < 4696, s24.getByte (BitVec.ofNat 64 q) = 0#8) :
    let topBytes := packSaltTopBits (tdSalt trapdoor) positions
    ∃ steps s59, OpenRuns s24 steps steps s59 ∧
      steps ≤ 13 * positions.card + 11 * (positions.card / 8) + 11 ∧
      s59.pc = pcAt 59 ∧
      s59.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s59.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s59.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff) ∧
      s59.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s59.getReg .x24 = BitVec.ofNat 64 6174019552 ∧
      s59.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
      s59.getReg .x27 = BitVec.ofNat 64 positions.card ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s59 ∧
      WriterState s59 topBytes ∧
      TailState s59 [] ∧
      (∀ q < 4696, s59.getByte (BitVec.ofNat 64 q) = 0#8) := by
  intro topBytes
  have hcard := positions_card_le positions
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have hse15 : signExtend12 (15#12) = BitVec.ofNat 64 15 := by decide
  have hloop : ∀ u ≤ positions.card,
      let curBytes := (List.range (u / 8)).map (saltTopByte (tdSalt trapdoor) positions)
      ∃ steps su, OpenRuns s24 steps steps su ∧
        steps ≤ 13 * u + 11 * (u / 8) ∧
        su.pc = (if u < positions.card then pcAt 24 else pcAt 48) ∧
        su.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
        su.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
        su.getReg .x10 = BitVec.ofNat 64 (partialSaltTopByte (tdSalt trapdoor) positions (u / 8) (u % 8)) ∧
        su.getReg .x11 = BitVec.ofNat 64 (u % 8) ∧
        su.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff) ∧
        su.getReg .x21 = BitVec.ofNat 64 4096 ∧
        su.getReg .x24 = BitVec.ofNat 64 6174019552 ∧
        su.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
        su.getReg .x27 = BitVec.ofNat 64 positions.card ∧
        su.getReg .x28 = BitVec.ofNat 64 (6174019552 + 8 * u) ∧
        su.getReg .x29 = BitVec.ofNat 64 (positions.card - u) ∧
        ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) su ∧
        SaltWriterState su curBytes ∧
        TailState su [] ∧
        (∀ q < 4696, su.getByte (BitVec.ofNat 64 q) = 0#8) := by
    intro u hu
    induction u with
    | zero =>
      dsimp only
      simp only [Nat.zero_div, Nat.zero_mod, List.range_zero, List.map_nil, Nat.mul_zero,
        Nat.add_zero, Nat.sub_zero, partialSaltTopByte_zero]
      exact ⟨0, s24, OpenRuns.refl s24, Nat.le_refl 0, by rw [if_pos hne]; exact hpc,
        hx2, hx9, hx10, hx11, hx18, hx21, hx24, hx26, hx27, hx28, hx29, hro, hsw, ht0, hcap0⟩
    | succ u ih =>
      obtain ⟨st, su, hru, hstu, hpcu, hx2u, hx9u, hx10u, hx11u, hx18u, hx21u, hx24u, hx26u, hx27u,
        hx28u, hx29u, hrou, hswu, htu, hcapu⟩ := ih (by omega)
      have hpcu' : su.pc = pcAt 24 := by simpa only [show u < positions.card by omega, ite_true] using hpcu
      let idx : Index := (positions.sort (· ≤ ·))[u]'(by simpa using (by omega : u < positions.card))
      have hidx_lt : idx.val < 16777216 := idx.isLt
      have hopen : openingIndex positions u = idx.val := by
        simp only [openingIndex, dif_pos (show u < positions.card by omega)]; rfl
      have hso_bd : saltOff idx + 16 ≤ 1879048128 := by
        have := saltOff_add_16_le idx; rw [trapdoorBytes_eq] at this; exact this
      set bIdx := u / 8
      set r := u % 8
      have hr_lt : r < 8 := Nat.mod_lt u (by decide)
      have hbit_eq : saltTopBitAt (tdSalt trapdoor) positions (8 * bIdx + r) =
          if (tdSalt trapdoor idx).getLsbD 120 then 1 else 0 := by
        unfold saltTopBitAt
        have heq : 8 * bIdx + r = u := by omega
        simp only [heq, show u < positions.card by omega, dite_true]; rfl
      set bit := saltTopBitAt (tdSalt trapdoor) positions (8 * bIdx + r)
      have hbit_lt : bit < 64 := by rw [hbit_eq]; split_ifs <;> omega
      set acc := partialSaltTopByte (tdSalt trapdoor) positions bIdx r
      have hacc_lt : acc < 2 ^ r := partialSaltTopByte_lt _ _ _ _
      set acc' := partialSaltTopByte (tdSalt trapdoor) positions bIdx (r + 1)
      have hacc'_eq : acc' = acc + bit * 2 ^ r := partialSaltTopByte_succ _ _ _ _
      -- 24..34: 11 steps
      have haddr24 : su.getReg .x28 + signExtend12 (0#12) = BitVec.ofNat 64 (6174019552 + 8 * u) := by
        rw [hx28u, hse0, bv64_ofNat_add, Nat.add_zero]
      have h24 := step_LD (by omega) hpcu' (rfl : openingInstr 24 = .base (.LD .x5 .x28 (0#12)))
        (by rw [haddr24]; exact accessValid_ofNat _ 8 (by omega) (by omega))
      let sa1 := (su.setReg .x5 (BitVec.ofNat 64 idx.val)).setPC (pcAt 25)
      have h24' : OpenRuns su 1 1 sa1 := by
        have hm := readOnly_getMem_index hrou u (by omega); rw [hopen] at hm
        simpa only [haddr24, hm, sa1] using h24
      have h25 := step_SLLI (by omega) (rfl : sa1.pc = pcAt 25) (rfl : openingInstr 25 = .base (.SLLI .x5 .x5 (4#6)))
      let sa2 := (sa1.setReg .x5 (BitVec.ofNat 64 (16 * idx.val))).setPC (pcAt 26)
      have h25' : OpenRuns sa1 1 1 sa2 := by
        have hv : sa1.getReg .x5 <<< (4#6 : BitVec 6).toNat = BitVec.ofNat 64 (16 * idx.val) := by
          change BitVec.ofNat 64 idx.val <<< 4 = _; rw [bv64_shl]; congr 1; omega
        simpa only [hv, sa2] using h25
      have h26 := step_ADD (by omega) (rfl : sa2.pc = pcAt 26) (rfl : openingInstr 26 = .base (.ADD .x5 .x18 .x5))
      let sa3 := (sa2.setReg .x5 (BitVec.ofNat 64 (4294971424 + saltOff idx))).setPC (pcAt 27)
      have h26' : OpenRuns sa2 1 1 sa3 := by
        have hr18 : sa2.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff) := hx18u
        have hv : sa2.getReg .x18 + sa2.getReg .x5 = BitVec.ofNat 64 (4294971424 + saltOff idx) := by
          rw [hr18]; change BitVec.ofNat 64 (4294971424 + saltsOff) + BitVec.ofNat 64 (16 * idx.val) = _
          rw [bv64_ofNat_add, Nat.add_assoc]; rfl
        simpa only [hv, sa3] using h26
      have haddr27 : sa3.getReg .x5 + signExtend12 (15#12) = BitVec.ofNat 64 (4294971424 + (saltOff idx + 15)) := by
        change BitVec.ofNat 64 (4294971424 + saltOff idx) + _ = _
        rw [hse15, bv64_ofNat_add, Nat.add_assoc]
      have h27 := step_LBU (by omega) (rfl : sa3.pc = pcAt 27) (rfl : openingInstr 27 = .base (.LBU .x6 .x5 (15#12)))
        (by rw [haddr27]; exact accessValid_ofNat _ 1 (by omega) (by omega))
      let sa4 := (sa3.setReg .x6 ((trapdoor.extractLsb' (8 * (saltOff idx + 15)) 8).zeroExtend 64)).setPC (pcAt 28)
      have h27' : OpenRuns sa3 1 1 sa4 := by
        have hb : sa3.getByte (BitVec.ofNat 64 (4294971424 + (saltOff idx + 15))) =
            trapdoor.extractLsb' (8 * (saltOff idx + 15)) 8 :=
          readOnly_getByte_trapdoor hrou (saltOff idx + 15) (by omega)
        simpa only [haddr27, hb, sa4] using h27
      have h28 := step_ANDI (by omega) (rfl : sa4.pc = pcAt 28) (rfl : openingInstr 28 = .base (.ANDI .x6 .x6 (1#12)))
      let sa5 := (sa4.setReg .x6 (BitVec.ofNat 64 bit)).setPC (pcAt 29)
      have h28' : OpenRuns sa4 1 1 sa5 := by
        have hv : sa4.getReg .x6 &&& signExtend12 (1#12) = BitVec.ofNat 64 bit := by
          rw [show bit = if (tdSalt trapdoor idx).getLsbD 120 then 1 else 0 from hbit_eq]
          exact tdSalt_topBit_byte15 trapdoor idx
        simpa only [hv, sa5] using h28
      have h29 := step_SLL (by omega) (rfl : sa5.pc = pcAt 29) (rfl : openingInstr 29 = .base (.SLL .x6 .x6 .x11))
      have hx11_mod : (sa5.getReg .x11).toNat % 64 = r := by
        have hr11 : sa5.getReg .x11 = BitVec.ofNat 64 r := hx11u
        rw [hr11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : r < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
      let sa6 := (sa5.setReg .x6 (BitVec.ofNat 64 bit <<< r)).setPC (pcAt 30)
      have h29' : OpenRuns sa5 1 1 sa6 := by
        simpa only [show sa5.getReg .x6 = BitVec.ofNat 64 bit from rfl, hx11_mod, sa6] using h29
      have h30 := step_OR (by omega) (rfl : sa6.pc = pcAt 30) (rfl : openingInstr 30 = .base (.OR .x10 .x10 .x6))
      let sa7 := (sa6.setReg .x10 (BitVec.ofNat 64 acc')).setPC (pcAt 31)
      have h30' : OpenRuns sa6 1 1 sa7 := by
        have hr10 : sa6.getReg .x10 = BitVec.ofNat 64 acc := hx10u
        have hv : sa6.getReg .x10 ||| sa6.getReg .x6 = BitVec.ofNat 64 acc' := by
          rw [hr10, hacc'_eq]; exact tail_or_shl_eq_add acc r bit hr_lt hacc_lt hbit_lt
        simpa only [hv, sa7] using h30
      have h31 := step_ADDI (by omega) (rfl : sa7.pc = pcAt 31) (rfl : openingInstr 31 = .base (.ADDI .x11 .x11 (1#12)))
      let sa8 := (sa7.setReg .x11 (BitVec.ofNat 64 (r + 1))).setPC (pcAt 32)
      have h31' : OpenRuns sa7 1 1 sa8 := by
        have hr11 : sa7.getReg .x11 = BitVec.ofNat 64 r := hx11u
        rw [hr11, hse1, bv64_ofNat_add] at h31; exact h31
      have h32 := step_ADDI (by omega) (rfl : sa8.pc = pcAt 32) (rfl : openingInstr 32 = .base (.ADDI .x28 .x28 (8#12)))
      let sa9 := (sa8.setReg .x28 (BitVec.ofNat 64 (6174019552 + 8 * (u + 1)))).setPC (pcAt 33)
      have h32' : OpenRuns sa8 1 1 sa9 := by
        have hr28 : sa8.getReg .x28 = BitVec.ofNat 64 (6174019552 + 8 * u) := hx28u
        have hv : sa8.getReg .x28 + signExtend12 (8#12) = BitVec.ofNat 64 (6174019552 + 8 * (u + 1)) := by
          rw [hr28, hse8, bv64_ofNat_add]; congr 1
        simpa only [hv, sa9] using h32
      have h33 := step_ADDI (by omega) (rfl : sa9.pc = pcAt 33) (rfl : openingInstr 33 = .base (.ADDI .x29 .x29 (4095#12)))
      let sa10 := (sa9.setReg .x29 (BitVec.ofNat 64 (positions.card - (u + 1)))).setPC (pcAt 34)
      have h33' : OpenRuns sa9 1 1 sa10 := by
        have hr29 : sa9.getReg .x29 = BitVec.ofNat 64 ((positions.card - (u + 1)) + 1) := by
          have h : sa9.getReg .x29 = BitVec.ofNat 64 (positions.card - u) := hx29u
          rw [h]; congr 1; omega
        rw [hr29, bv64_add_neg1] at h33; exact h33
      have h34 := step_ADDI (by omega) (rfl : sa10.pc = pcAt 34) (rfl : openingInstr 34 = .base (.ADDI .x7 .x0 (8#12)))
      let sa11 := (sa10.setReg .x7 8#64).setPC (pcAt 35)
      have h34' : OpenRuns sa10 1 1 sa11 := by
        have hv : sa10.getReg .x0 + signExtend12 (8#12) = 8#64 := by change (0#64 : Word) + signExtend12 (8#12) = 8#64; decide
        simpa only [hv, sa11] using h34
      have hpre11 : OpenRuns su 11 11 sa11 :=
        (((((((((h24'.trans h25').trans h26').trans h27').trans h28').trans h29').trans h30').trans h31').trans h32').trans h33').trans h34'
      -- Branch at 35 -> pcAt 47
      have hto47 :
          let curBytes' := (List.range ((u + 1) / 8)).map (saltTopByte (tdSalt trapdoor) positions)
          ∃ stM s47, OpenRuns sa11 stM stM s47 ∧
            stM ≤ 1 + 11 * ((u + 1) / 8 - u / 8) ∧
            s47.pc = pcAt 47 ∧
            s47.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
            s47.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
            s47.getReg .x10 = BitVec.ofNat 64 (partialSaltTopByte (tdSalt trapdoor) positions ((u + 1) / 8) ((u + 1) % 8)) ∧
            s47.getReg .x11 = BitVec.ofNat 64 ((u + 1) % 8) ∧
            s47.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff) ∧
            s47.getReg .x21 = BitVec.ofNat 64 4096 ∧
            s47.getReg .x24 = BitVec.ofNat 64 6174019552 ∧
            s47.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
            s47.getReg .x27 = BitVec.ofNat 64 positions.card ∧
            s47.getReg .x28 = BitVec.ofNat 64 (6174019552 + 8 * (u + 1)) ∧
            s47.getReg .x29 = BitVec.ofNat 64 (positions.card - (u + 1)) ∧
            ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s47 ∧
            SaltWriterState s47 curBytes' ∧
            TailState s47 [] ∧
            (∀ q < 4696, s47.getByte (BitVec.ofNat 64 q) = 0#8) := by
        by_cases hlt8 : r + 1 < 8
        · have hdiv : (u + 1) / 8 = bIdx := by omega
          have hmod : (u + 1) % 8 = r + 1 := by omega
          have h35 := step_BNE_taken (by omega) (rfl : sa11.pc = pcAt 35)
            (rfl : openingInstr 35 = .base (.BNE .x11 .x7 (48#13)))
            (by change BitVec.ofNat 64 (r + 1) ≠ 8#64; exact bv64_ofNat_ne (by omega) (by decide) (by omega))
            (by decide : pcAt 35 + signExtend13 (48#13) = pcAt 47)
          refine ⟨1, sa11.setPC (pcAt 47), h35, by omega, rfl,
            hx2u, hx9u, by rw [hdiv, hmod]; rfl, by rw [hmod]; rfl,
            hx18u, hx21u, hx24u, hx26u, hx27u, rfl, rfl,
            hrou, by rw [hdiv]; exact hswu.of_eq, htu.of_eq, hcapu⟩
        · have hr7 : r = 7 := by omega
          have hdiv : (u + 1) / 8 = bIdx + 1 := by omega
          have hmod : (u + 1) % 8 = 0 := by omega
          have h35 := step_BNE_not_taken (by omega) (rfl : sa11.pc = pcAt 35)
            (rfl : openingInstr 35 = .base (.BNE .x11 .x7 (48#13)))
            (by change BitVec.ofNat 64 (r + 1) = 8#64; rw [hr7])
          let s36 := sa11.setPC (pcAt 36)
          have hacc'_lt : acc' < 256 := by
            have := partialSaltTopByte_lt (tdSalt trapdoor) positions bIdx (r + 1)
            rw [hr7] at this; change partialSaltTopByte (tdSalt trapdoor) positions bIdx (r + 1) < 256
            rw [hr7]; exact Nat.lt_of_lt_of_le this (by decide)
          have hbyte_eq : BitVec.ofNat 8 acc' = saltTopByte (tdSalt trapdoor) positions bIdx := by
            change BitVec.ofNat 8 (partialSaltTopByte (tdSalt trapdoor) positions bIdx (r + 1)) = _
            rw [hr7]; rfl
          have hx10_ze : s36.getReg .x10 = (saltTopByte (tdSalt trapdoor) positions bIdx).zeroExtend 64 := by
            rw [← hbyte_eq]; change BitVec.ofNat 64 acc' = (BitVec.ofNat 8 acc').zeroExtend 64
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt hacc'_lt, Nat.mod_eq_of_lt (by omega : acc' < 2 ^ 64)]
          have hsw36 : SaltWriterState s36 ((List.range bIdx).map (saltTopByte (tdSalt trapdoor) positions)) :=
            ⟨hswu.rx25, hswu.rx13, hswu.wbufLo, hswu.wbufHi, hswu.memDwords⟩
          obtain ⟨stP, s45, hrP, hstP, hpc45, hreg45, hro45, hsw45, hcap45, htail45⟩ :=
            openRuns_salt_push_byte (base := 36) (b := saltTopByte (tdSalt trapdoor) positions bIdx)
              (by omega) (by decide) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
              rfl hx10_ze (by simp; omega) hrou hsw36
          have h45 := step_ADDI (by omega) hpc45 (rfl : openingInstr 45 = .base (.ADDI .x10 .x0 (0#12)))
          let s46 := (s45.setReg .x10 0#64).setPC (pcAt 46)
          have h45' : OpenRuns s45 1 1 s46 := by
            have hv : s45.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
            simpa only [hv, s46] using h45
          have h46 := step_ADDI (by omega) (rfl : s46.pc = pcAt 46) (rfl : openingInstr 46 = .base (.ADDI .x11 .x0 (0#12)))
          let s47 := (s46.setReg .x11 0#64).setPC (pcAt 47)
          have h46' : OpenRuns s46 1 1 s47 := by
            have hv : s46.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
            simpa only [hv, s47] using h46
          have happ : (List.range bIdx).map (saltTopByte (tdSalt trapdoor) positions) ++
              [saltTopByte (tdSalt trapdoor) positions bIdx] =
              (List.range ((u + 1) / 8)).map (saltTopByte (tdSalt trapdoor) positions) := by
            rw [hdiv, List.range_succ, List.map_append, List.map_singleton]
          rw [happ] at hsw45
          have hpres47 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x13 → r ≠ .x25 →
              s47.getReg r = s36.getReg r := fun r h6 h7 h10 h11 h12 h13 h25 => by
            simp only [s47, s46, MachineState.getReg_setPC,
              getReg_setReg_ne' .x11 r (Ne.symm h11), getReg_setReg_ne' .x10 r (Ne.symm h10)]
            exact hreg45 r h6 h7 h12 h13 h25
          refine ⟨1 + stP + 1 + 1, s47, ((h35.trans hrP).trans h45').trans h46',
            by rw [hdiv]; omega, rfl,
            by rw [hpres47 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx2u,
            by rw [hpres47 .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx9u,
            by rw [hmod, partialSaltTopByte_zero]; rfl,
            by rw [hmod]; rfl,
            by rw [hpres47 .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx18u,
            by rw [hpres47 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx21u,
            by rw [hpres47 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx24u,
            by rw [hpres47 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx26u,
            by rw [hpres47 .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx27u,
            by rw [hpres47 .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl,
            by rw [hpres47 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl,
            by intro a ha; simp only [s47, s46, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro45 a ha,
            ⟨by simp only [s47, s46, MachineState.getReg_setPC, getReg_setReg_ne' .x11 .x25 (by decide),
                getReg_setReg_ne' .x10 .x25 (by decide)]; exact hsw45.rx25,
             by simp only [s47, s46, MachineState.getReg_setPC, getReg_setReg_ne' .x11 .x13 (by decide),
                getReg_setReg_ne' .x10 .x13 (by decide)]; exact hsw45.rx13,
             fun j hj => by
               simp only [s47, s46, MachineState.getReg_setPC, getReg_setReg_ne' .x11 .x12 (by decide),
                 getReg_setReg_ne' .x10 .x12 (by decide)]; exact hsw45.wbufLo j hj,
             fun j h1 h2 => by
               simp only [s47, s46, MachineState.getReg_setPC, getReg_setReg_ne' .x11 .x12 (by decide),
                 getReg_setReg_ne' .x10 .x12 (by decide)]; exact hsw45.wbufHi j h1 h2,
             fun j hj => by simp only [s47, s46, getByte_setPC, getByte_setReg]; exact hsw45.memDwords j hj⟩,
            tailState_of_mem_eq htu (by simp) (fun r hr => by
              rcases hr with rfl | rfl | rfl | rfl <;>
                exact hpres47 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
              (fun a ha1 ha2 => by simp only [s47, s46, getByte_setPC, getByte_setReg]; exact htail45 a ha1 ha2),
            fun a ha => by simp only [s47, s46, getByte_setPC, getByte_setReg]; rw [hcap45 a ha]; exact hcapu a ha⟩
      obtain ⟨stM, s47, hrM, hstM, hpc47, hx2_47, hx9_47, hx10_47, hx11_47, hx18_47, hx21_47,
        hx24_47, hx26_47, hx27_47, hx28_47, hx29_47, hro47, hsw47, ht47, hcap47⟩ := hto47
      -- 47: BNE x29, x0, 8100 (-92 -> 24)
      by_cases hmore : u + 1 < positions.card
      · have h47 := step_BNE_taken (by omega) hpc47 (rfl : openingInstr 47 = .base (.BNE .x29 .x0 (8100#13)))
          (by rw [hx29_47]; exact bv64_ofNat_ne (by omega) (by decide) (by omega))
          (by decide : pcAt 47 + signExtend13 (8100#13) = pcAt 24)
        exact ⟨st + 11 + stM + 1, s47.setPC (pcAt 24), ((hru.trans hpre11).trans hrM).trans h47,
          by omega, by simp only [hmore, ite_true]; rfl, hx2_47, hx9_47, hx10_47, hx11_47, hx18_47, hx21_47,
          hx24_47, hx26_47, hx27_47, hx28_47, hx29_47, hro47, hsw47.of_eq, ht47.of_eq, hcap47⟩
      · have hdone : positions.card - (u + 1) = 0 := by omega
        have h47 := step_BNE_not_taken (by omega) hpc47 (rfl : openingInstr 47 = .base (.BNE .x29 .x0 (8100#13)))
          (by rw [hx29_47, hdone]; rfl)
        exact ⟨st + 11 + stM + 1, s47.setPC (pcAt 48), ((hru.trans hpre11).trans hrM).trans h47,
          by omega, by simp only [hmore, ite_false]; rfl, hx2_47, hx9_47, hx10_47, hx11_47, hx18_47, hx21_47,
          hx24_47, hx26_47, hx27_47, hx28_47, hx29_47, hro47, hsw47.of_eq, ht47.of_eq, hcap47⟩
  obtain ⟨stL, s48, hrL, hstL, hpc48, hx2_48, hx9_48, hx10_48, hx11_48, hx18_48, hx21_48,
    hx24_48, hx26_48, hx27_48, _, _, hro48, hsw48, ht48, hcap48⟩ := hloop positions.card (Nat.le_refl _)
  have hpc48' : s48.pc = pcAt 48 := by simpa only [Nat.lt_irrefl, ite_false] using hpc48
  -- Post-loop tail flush (48..57 -> 58)
  have hto58 : ∃ stF s58, OpenRuns s48 stF stF s58 ∧
      stF ≤ 10 ∧ s58.pc = pcAt 58 ∧
      s58.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s58.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s58.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff) ∧
      s58.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s58.getReg .x24 = BitVec.ofNat 64 6174019552 ∧
      s58.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
      s58.getReg .x27 = BitVec.ofNat 64 positions.card ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s58 ∧
      SaltWriterState s58 topBytes ∧
      TailState s58 [] ∧
      (∀ q < 4696, s58.getByte (BitVec.ofNat 64 q) = 0#8) := by
    by_cases hrem0 : positions.card % 8 = 0
    · have h48 := step_BEQ_taken (by omega) hpc48' (rfl : openingInstr 48 = .base (.BEQ .x11 .x0 (40#13)))
        (by rw [hx11_48, hrem0]; rfl) (by decide : pcAt 48 + signExtend13 (40#13) = pcAt 58)
      have heq : (List.range (positions.card / 8)).map (saltTopByte (tdSalt trapdoor) positions) = topBytes := by
        unfold topBytes packSaltTopBits; rw [show (positions.card + 7) / 8 = positions.card / 8 by omega]
      rw [heq] at hsw48
      exact ⟨1, s48.setPC (pcAt 58), h48, by omega, rfl,
        hx2_48, hx9_48, hx18_48, hx21_48, hx24_48, hx26_48, hx27_48, hro48, hsw48.of_eq, ht48.of_eq, hcap48⟩
    · have hremPos : 0 < positions.card % 8 := by omega
      have h48 := step_BEQ_not_taken (by omega) hpc48' (rfl : openingInstr 48 = .base (.BEQ .x11 .x0 (40#13)))
        (by rw [hx11_48]; exact bv64_ofNat_ne (by omega) (by decide) hrem0)
      let s49 := s48.setPC (pcAt 49)
      have hacc_lt : partialSaltTopByte (tdSalt trapdoor) positions (positions.card / 8) (positions.card % 8) < 256 := by
        have h1 := partialSaltTopByte_lt (tdSalt trapdoor) positions (positions.card / 8) (positions.card % 8)
        have h2 : 2 ^ (positions.card % 8) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
        have h3 : 2 ^ 7 = 128 := by decide
        omega
      have hx10_ze : s49.getReg .x10 = (saltTopByte (tdSalt trapdoor) positions (positions.card / 8)).zeroExtend 64 := by
        rw [← partialSaltTopByte_tail (tdSalt trapdoor) positions hremPos]
        change s48.getReg .x10 = _
        rw [hx10_48]
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hacc_lt, Nat.mod_eq_of_lt (Nat.lt_trans hacc_lt (by omega : 256 < 2 ^ 64))]
      obtain ⟨stP, s58, hrP, hstP, hpc58, hreg58, hro58, hsw58, hcap58, htail58⟩ :=
        openRuns_salt_push_byte (base := 49) (b := saltTopByte (tdSalt trapdoor) positions (positions.card / 8))
          (by omega) (by decide) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
          rfl hx10_ze (by simp; omega) hro48 hsw48.of_eq
      have happ : (List.range (positions.card / 8)).map (saltTopByte (tdSalt trapdoor) positions) ++
          [saltTopByte (tdSalt trapdoor) positions (positions.card / 8)] = topBytes := by
        unfold topBytes packSaltTopBits
        rw [show (positions.card + 7) / 8 = positions.card / 8 + 1 by omega,
          List.range_succ, List.map_append, List.map_singleton]
      rw [happ] at hsw58
      refine ⟨1 + stP, s58, h48.trans hrP, by omega, hpc58,
        by rw [hreg58 .x2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx2_48,
        by rw [hreg58 .x9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx9_48,
        by rw [hreg58 .x18 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx18_48,
        by rw [hreg58 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx21_48,
        by rw [hreg58 .x24 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx24_48,
        by rw [hreg58 .x26 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx26_48,
        by rw [hreg58 .x27 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx27_48,
        hro58, hsw58,
        tailState_of_mem_eq ht48 (by simp) (fun r hr => by
          rcases hr with rfl | rfl | rfl | rfl <;>
            exact hreg58 _ (by decide) (by decide) (by decide) (by decide) (by decide)) htail58,
        fun a ha => (hcap58 a ha).trans (hcap48 a ha)⟩
  obtain ⟨stF, s58, hrF, hstF, hpc58, hx2_58, hx9_58, hx18_58, hx21_58, hx24_58, hx26_58, hx27_58,
    hro58, hsw58, ht58, hcap58⟩ := hto58
  -- 58: XORI x14, x13, 63 -> restores full WriterState
  have h58 := step_XORI (by omega) hpc58 (rfl : openingInstr 58 = .base (.XORI .x14 .x13 (63#12)))
  let s59 := (s58.setReg .x14 (BitVec.ofNat 64 (63 - 8 * (topBytes.length % 8)))).setPC (pcAt 59)
  have h58' : OpenRuns s58 1 1 s59 := by
    have hv : s58.getReg .x13 ^^^ signExtend12 (63#12) = BitVec.ofNat 64 (63 - 8 * (topBytes.length % 8)) := by
      rw [hsw58.rx13]; exact bv64_xor63_8mul (topBytes.length % 8) (Nat.mod_lt _ (by decide))
    simpa only [hv, s59] using h58
  refine ⟨stL + stF + 1, s59, (hrL.trans hrF).trans h58', by omega, rfl,
    hx2_58, hx9_58, hx18_58, hx21_58, hx24_58, hx26_58, hx27_58,
    by intro a ha; simp only [s59, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro58 a ha,
    ⟨hsw58.rx25, hsw58.rx13, rfl, hsw58.wbufLo, hsw58.wbufHi, hsw58.memDwords⟩,
    ht58.of_eq, hcap58⟩

/-! ### 7. Epilogue Blocks (`112..131`): Flush Forward Buffer, Flush Tail, Reverse Tail, Finish -/

private theorem openRuns_flush_wbuf {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    (hpc : s.pc = pcAt 112)
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 10603204576)
    (hfbd : fwdBytes.length ≤ 8239714016)
    (htbd : tails.length ≤ 300000000)
    (hw : WriterState s fwdBytes)
    (ht : TailState s tails) :
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 37 ∧
      s'.pc = pcAt 119 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (10603204576 + fwdBytes.length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
      ProofPrefix s' fwdBytes ∧
      TailState s' tails := by
  set q := fwdBytes.length / 8
  set r := fwdBytes.length % 8
  have hr : r < 8 := Nat.mod_lt _ (by decide)
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  have h112 := step_ADDI (by omega) hpc (rfl : openingInstr 112 = .base (.ADDI .x10 .x25 (0#12)))
  let s1 := (s.setReg .x10 (BitVec.ofNat 64 (10603204576 + 8 * q))).setPC (pcAt 113)
  have h112' : OpenRuns s 1 1 s1 := by
    rw [hw.rx25, hse0, bv64_ofNat_add, Nat.add_zero] at h112; exact h112
  by_cases hr0 : r = 0
  · have h113 := step_BEQ_taken (by omega) (rfl : s1.pc = pcAt 113)
      (rfl : openingInstr 113 = .base (.BEQ .x13 .x0 (24#13)))
      (by have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13; rw [h, hr0]; rfl)
      (by decide : pcAt 113 + signExtend13 (24#13) = pcAt 119)
    refine ⟨2, s1.setPC (pcAt 119), h112'.trans h113, by omega, rfl,
      by change BitVec.ofNat 64 (10603204576 + 8 * q) = _; congr 1; omega,
      hx26, fun j hj => hw.memDwords j (by omega), ht.of_eq⟩
  · have hrpos : 0 < r := by omega
    have h113 := step_BEQ_not_taken (by omega) (rfl : s1.pc = pcAt 113)
      (rfl : openingInstr 113 = .base (.BEQ .x13 .x0 (24#13)))
      (by have h : s1.getReg .x13 = BitVec.ofNat 64 (8 * r) := hw.rx13
          rw [h]; exact bv64_ofNat_ne (by omega) (by decide) (by omega))
    let s2 := s1.setPC (pcAt 114)
    have hloop : ∀ k (hk : k ≤ r), ∃ sk, OpenRuns s2 (5 * k) (5 * k) sk ∧
        sk.pc = (if k < r then pcAt 114 else pcAt 119) ∧
        sk.getReg .x10 = BitVec.ofNat 64 (10603204576 + 8 * q + k) ∧
        sk.getReg .x13 = BitVec.ofNat 64 (8 * (r - k)) ∧
        sk.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
        (∀ j (hj : j < r - k), (sk.getReg .x12).extractLsb' (8 * j) 8 = fwdBytes[8 * q + k + j]'(by omega)) ∧
        (∀ j (hj : j < 8 * q + k), sk.getByte (BitVec.ofNat 64 (10603204576 + j)) = fwdBytes[j]'(by omega)) ∧
        TailState sk tails := by
      intro k hk
      induction k with
      | zero =>
        refine ⟨s2, OpenRuns.refl s2, by rw [if_pos hrpos]; rfl,
          by rw [Nat.add_zero]; rfl, by rw [Nat.sub_zero]; exact hw.rx13, hx26,
          fun j hj => (hw.wbufLo j (by omega)).trans (by congr 1),
          fun j hj => hw.memDwords j (by omega), ht.of_eq⟩
      | succ k ih =>
        obtain ⟨sk, hrk, hpck, hx10k, hx13k, hx26k, hwLoK, hmemk, htk⟩ := ih (by omega)
        have hpck' : sk.pc = pcAt 114 := by simpa only [show k < r by omega, ite_true] using hpck
        have haddr : sk.getReg .x10 + signExtend12 (0#12) = BitVec.ofNat 64 (10603204576 + 8 * q + k) := by
          rw [hx10k, hse0, bv64_ofNat_add, Nat.add_zero]
        have ha := step_SB (by omega) hpck' (rfl : openingInstr 114 = .base (.SB .x10 .x12 (0#12)))
          (by rw [haddr]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        have hbyte0 : (sk.getReg .x12).truncate 8 = fwdBytes[8 * q + k]'(by omega) := by
          rw [word_truncate8_eq_extractLsb'0]; simpa using hwLoK 0 (by omega)
        let sa := (sk.setByte (BitVec.ofNat 64 (10603204576 + 8 * q + k)) (fwdBytes[8 * q + k]'(by omega))).setPC (pcAt 115)
        have ha' : OpenRuns sk 1 1 sa := by simpa only [haddr, hbyte0, sa] using ha
        have hb := step_ADDI (by omega) (rfl : sa.pc = pcAt 115) (rfl : openingInstr 115 = .base (.ADDI .x10 .x10 (1#12)))
        let sb := (sa.setReg .x10 (BitVec.ofNat 64 (10603204576 + 8 * q + (k + 1)))).setPC (pcAt 116)
        have hb' : OpenRuns sa 1 1 sb := by
          have hr10 : sa.getReg .x10 = BitVec.ofNat 64 (10603204576 + 8 * q + k) := by
            simp only [sa, MachineState.getReg_setPC, getReg_setByte]; exact hx10k
          rw [hr10, hse1, bv64_ofNat_add, Nat.add_assoc] at hb; exact hb
        have hc := step_SRLI (by omega) (rfl : sb.pc = pcAt 116) (rfl : openingInstr 116 = .base (.SRLI .x12 .x12 (8#6)))
        let sc := (sb.setReg .x12 (sk.getReg .x12 >>> 8)).setPC (pcAt 117)
        have hc' : OpenRuns sb 1 1 sc := by
          have hr12 : sb.getReg .x12 = sk.getReg .x12 := by
            simp only [sb, sa, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne' .x10 .x12 (by decide)]
          simpa only [hr12, show (8#6 : BitVec 6).toNat = 8 from rfl, sc] using hc
        have hd := step_ADDI (by omega) (rfl : sc.pc = pcAt 117) (rfl : openingInstr 117 = .base (.ADDI .x13 .x13 (4088#12)))
        let sd := (sc.setReg .x13 (BitVec.ofNat 64 (8 * (r - (k + 1))))).setPC (pcAt 118)
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
            sd.getByte (BitVec.ofNat 64 (10603204576 + j)) = fwdBytes[j]'(by omega) := by
          intro j hj
          simp only [sd, sc, sb, sa, getByte_setPC, getByte_setReg, set_byte_read]
          by_cases hlast : j = 8 * q + k
          · subst hlast; rw [show 10603204576 + (8 * q + k) = 10603204576 + 8 * q + k by omega, if_pos rfl]
          · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]; exact hmemk j (by omega)
        have htd : TailState sd tails := by
          have htb : tailBufBase = 25769803776 := rfl
          have ht' := tailState_setByte_outside (10603204576 + 8 * q + k)
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
            fun j hj => by simp only [sd, sc, sb, sa, getByte_setPC, getByte_setReg]; exact ht'.memTail j hj⟩
        have hwLo_d : ∀ j (hj : j < r - (k + 1)),
            (sd.getReg .x12).extractLsb' (8 * j) 8 = fwdBytes[8 * q + (k + 1) + j]'(by omega) := by
          intro j hj
          have h12 : sd.getReg .x12 = sk.getReg .x12 >>> 8 := by
            simp only [sd, sc, MachineState.getReg_setPC, getReg_setReg_ne' .x13 .x12 (by decide)]; rfl
          rw [h12, word_ushr8_extractLsb' _ j (by omega)]
          simpa only [show 8 * q + k + (j + 1) = 8 * q + (k + 1) + j by omega] using hwLoK (j + 1) (by omega)
        have hx10_d : sd.getReg .x10 = BitVec.ofNat 64 (10603204576 + 8 * q + (k + 1)) := by
          simp only [sd, sc, sb, MachineState.getReg_setPC,
            getReg_setReg_ne' .x13 .x10 (by decide), getReg_setReg_ne' .x12 .x10 (by decide)]; rfl
        have hx26_d : sd.getReg .x26 = BitVec.ofNat 64 10603204576 := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x13 .x26 (by decide), getReg_setReg_ne' .x12 .x26 (by decide),
            getReg_setReg_ne' .x10 .x26 (by decide)]; exact hx26k
        by_cases hmore : k + 1 < r
        · have he := step_BNE_taken (by omega) (rfl : sd.pc = pcAt 118)
            (rfl : openingInstr 118 = .base (.BNE .x13 .x0 (8176#13)))
            (by change BitVec.ofNat 64 (8 * (r - (k + 1))) ≠ BitVec.ofNat 64 0
                exact bv64_ofNat_ne (by omega) (by decide) (by omega))
            (by decide : pcAt 118 + signExtend13 (8176#13) = pcAt 114)
          exact ⟨sd.setPC (pcAt 114), by simpa only [Nat.mul_succ] using (hrk.trans hstep4).trans he,
            by rw [if_pos hmore]; rfl, hx10_d, rfl, hx26_d, hwLo_d, hmem_d, htd.of_eq⟩
        · have hdone : r - (k + 1) = 0 := by omega
          have he := step_BNE_not_taken (by omega) (rfl : sd.pc = pcAt 118)
            (rfl : openingInstr 118 = .base (.BNE .x13 .x0 (8176#13)))
            (by change BitVec.ofNat 64 (8 * (r - (k + 1))) = 0#64; rw [hdone])
          exact ⟨sd.setPC (pcAt 119), by simpa only [Nat.mul_succ] using (hrk.trans hstep4).trans he,
            by rw [if_neg hmore]; rfl, hx10_d, rfl, hx26_d, hwLo_d, hmem_d, htd.of_eq⟩
    obtain ⟨sf, hrf, hpcf, hx10f, _, hx26f, _, hmemf, htf⟩ := hloop r (Nat.le_refl r)
    have hpcf' : sf.pc = pcAt 119 := by simpa only [Nat.lt_irrefl, ite_false] using hpcf
    refine ⟨2 + 5 * r, sf, (h112'.trans h113).trans hrf, by omega, hpcf',
      by rw [hx10f]; congr 1; omega, hx26f, fun j hj => hmemf j (by omega), htf⟩

private theorem openRuns_flush_tail {s : MachineState} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    (hpc : s.pc = pcAt 119)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (10603204576 + fwdBytes.length))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 10603204576)
    (hfbd : fwdBytes.length ≤ 8239714016)
    (htbd : tails.length ≤ 300000000)
    (hpr : ProofPrefix s fwdBytes)
    (ht : TailState s tails) :
    let packed := pack6Bits tails
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps ≤ 3 ∧
      s'.pc = pcAt 122 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (10603204576 + fwdBytes.length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
      s'.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
      s'.getReg .x15 = BitVec.ofNat 64 (tailBufBase + packed.length) ∧
      ProofPrefix s' fwdBytes ∧
      TailBufPrefix s' packed := by
  intro packed
  have htb : tailBufBase = 25769803776 := rfl
  set st := tails.foldl pack6Step ([], 0, 0)
  have hst_bd := pack6_foldl_bounds tails
  set acc := st.1; set tBuf := st.2.1; set tCnt := st.2.2
  have htCnt_lt : tCnt < 8 := hst_bd.1
  have htBuf_lt : tBuf < 2 ^ tCnt := hst_bd.2.1
  have hacc_len : 8 * acc.length + tCnt = 6 * tails.length := hst_bd.2.2
  have hpow : 2 ^ tCnt ≤ 128 := by
    have h1 : 2 ^ tCnt ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    have h2 : 2 ^ 7 = 128 := by decide
    omega
  by_cases hcnt0 : tCnt = 0
  · have h119 := step_BEQ_taken (by omega) hpc (rfl : openingInstr 119 = .base (.BEQ .x17 .x0 (12#13)))
      (by rw [ht.rx17]; exact congrArg (BitVec.ofNat 64) hcnt0)
      (by decide : pcAt 119 + signExtend13 (12#13) = pcAt 122)
    have hpack_eq : packed = acc := by
      unfold packed pack6Bits pack6Finish; change (if 0 < tCnt then _ else acc) = acc; rw [if_neg (by omega)]
    rw [hpack_eq]
    exact ⟨1, s.setPC (pcAt 122), h119, by omega, rfl, hx10, hx26, ht.rx31, ht.rx15, hpr, ht.memTail⟩
  · have hpos : 0 < tCnt := by omega
    have hpack_eq : packed = acc ++ [BitVec.ofNat 8 tBuf] := by
      unfold packed pack6Bits pack6Finish; change (if 0 < tCnt then acc ++ [BitVec.ofNat 8 tBuf] else acc) = _; rw [if_pos hpos]
    have h119 := step_BEQ_not_taken (by omega) hpc (rfl : openingInstr 119 = .base (.BEQ .x17 .x0 (12#13)))
      (by rw [ht.rx17]; exact bv64_ofNat_ne (by omega) (by decide) hcnt0)
    let s1 := s.setPC (pcAt 120)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have haddr : s1.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + acc.length) := by
      have hr15 : s1.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := ht.rx15
      rw [hr15, hse0, bv64_ofNat_add, Nat.add_zero]
    have h120 := step_SB (by omega) (rfl : s1.pc = pcAt 120) (rfl : openingInstr 120 = .base (.SB .x15 .x16 (0#12)))
      (by rw [haddr]; exact accessValid_ofNat _ 1 (by omega) (by omega))
    let s2 := (s1.setByte (BitVec.ofNat 64 (tailBufBase + acc.length)) (BitVec.ofNat 8 tBuf)).setPC (pcAt 121)
    have h120' : OpenRuns s1 1 1 s2 := by
      have htr : (s1.getReg .x16).truncate 8 = BitVec.ofNat 8 tBuf := by
        have hr16 : s1.getReg .x16 = BitVec.ofNat 64 tBuf := ht.rx16
        rw [hr16]; exact bv64_ofNat_truncate8 tBuf (by omega)
      simpa only [haddr, htr, s2] using h120
    have h121 := step_ADDI (by omega) (rfl : s2.pc = pcAt 121) (rfl : openingInstr 121 = .base (.ADDI .x15 .x15 (1#12)))
    let s3 := (s2.setReg .x15 (BitVec.ofNat 64 (tailBufBase + packed.length))).setPC (pcAt 122)
    have h121' : OpenRuns s2 1 1 s3 := by
      have hr15 : s2.getReg .x15 = BitVec.ofNat 64 (tailBufBase + acc.length) := by
        simp only [s2, MachineState.getReg_setPC, getReg_setByte]; exact ht.rx15
      have hv : s2.getReg .x15 + signExtend12 (1#12) = BitVec.ofNat 64 (tailBufBase + packed.length) := by
        rw [hr15, hse1, bv64_ofNat_add, hpack_eq, List.length_append, List.length_singleton, Nat.add_assoc]
      simpa only [hv, s3] using h121
    refine ⟨3, s3, (h119.trans h120').trans h121', Nat.le_refl 3, rfl, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · simp only [s3, s2, s1, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne' .x15 .x10 (by decide)]; exact hx10
    · simp only [s3, s2, s1, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne' .x15 .x26 (by decide)]; exact hx26
    · simp only [s3, s2, s1, MachineState.getReg_setPC, getReg_setByte, getReg_setReg_ne' .x15 .x31 (by decide)]; exact ht.rx31
    · intro j hj
      simp only [s3, s2, s1, getByte_setPC, getByte_setReg, set_byte_read]
      rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]; exact hpr j hj
    · rw [hpack_eq]; intro j hj
      simp only [s3, s2, s1, getByte_setPC, getByte_setReg, set_byte_read]
      have hjlen : j < acc.length + 1 := by simpa using hj
      by_cases hlast : j = acc.length
      · subst hlast
        rw [if_pos rfl, list_getElem_append_right acc [BitVec.ofNat 8 tBuf] acc.length (by omega) hj]; simp
      · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega)),
          ht.memTail j (by omega), list_getElem_append_left acc [BitVec.ofNat 8 tBuf] j (by omega)]

private theorem openRuns_rev_tail {s : MachineState} {fwdBytes packed : List Byte}
    (hpc : s.pc = pcAt 122)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (10603204576 + fwdBytes.length))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 10603204576)
    (hx31 : s.getReg .x31 = BitVec.ofNat 64 tailBufBase)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 (tailBufBase + packed.length))
    (hbd : fwdBytes.length + packed.length ≤ 8239714016)
    (hpr : ProofPrefix s fwdBytes)
    (htail : TailBufPrefix s packed) :
    ∃ s', OpenRuns s (1 + 5 * packed.length) (1 + 5 * packed.length) s' ∧
      s'.pc = pcAt 128 ∧
      s'.getReg .x10 = BitVec.ofNat 64 (10603204576 + (fwdBytes ++ packed.reverse).length) ∧
      s'.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
      ProofPrefix s' (fwdBytes ++ packed.reverse) := by
  have htb : tailBufBase = 25769803776 := rfl
  set m := packed.length
  by_cases hm0 : m = 0
  · have hnil : packed = [] := List.eq_nil_of_length_eq_zero hm0
    have h122 := step_BEQ_taken (by omega) hpc (rfl : openingInstr 122 = .base (.BEQ .x15 .x31 (24#13)))
      (by rw [hx15, hx31, hm0, Nat.add_zero]) (by decide : pcAt 122 + signExtend13 (24#13) = pcAt 128)
    subst hnil
    exact ⟨s.setPC (pcAt 128), by rw [hm0, Nat.mul_zero, Nat.add_zero]; exact h122, rfl,
      by rw [List.reverse_nil, List.append_nil]; exact hx10, hx26,
      by rw [List.reverse_nil, List.append_nil]; exact hpr⟩
  · have hmpos : 0 < m := by omega
    have h122 := step_BEQ_not_taken (by omega) hpc (rfl : openingInstr 122 = .base (.BEQ .x15 .x31 (24#13)))
      (by rw [hx15, hx31]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
    let s1 := s.setPC (pcAt 123)
    have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
    have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
    have hloop : ∀ u ≤ m, ∃ su, OpenRuns s1 (5 * u) (5 * u) su ∧
        su.pc = (if u < m then pcAt 123 else pcAt 128) ∧
        su.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (m - u)) ∧
        su.getReg .x31 = BitVec.ofNat 64 tailBufBase ∧
        su.getReg .x10 = BitVec.ofNat 64 (10603204576 + fwdBytes.length + u) ∧
        su.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
        ProofPrefix su (fwdBytes ++ packed.reverse.take u) ∧
        TailBufPrefix su packed := by
      intro u hu
      induction u with
      | zero =>
        refine ⟨s1, OpenRuns.refl s1, by rw [if_pos hmpos]; rfl,
          by rw [Nat.sub_zero]; exact hx15, hx31, by rw [Nat.add_zero]; exact hx10, hx26,
          by rw [List.take_zero, List.append_nil]; exact hpr, htail⟩
      | succ u ih =>
        obtain ⟨su, hru, hpcu, hx15u, hx31u, hx10u, hx26u, hpru, htailu⟩ := ih (by omega)
        have hpcu' : su.pc = pcAt 123 := by simpa only [show u < m by omega, ite_true] using hpcu
        have ha := step_ADDI (by omega) hpcu' (rfl : openingInstr 123 = .base (.ADDI .x15 .x15 (4095#12)))
        let sa := (su.setReg .x15 (BitVec.ofNat 64 (tailBufBase + (m - (u + 1))))).setPC (pcAt 124)
        have ha' : OpenRuns su 1 1 sa := by
          have hr15 : su.getReg .x15 = BitVec.ofNat 64 ((tailBufBase + (m - (u + 1))) + 1) := by
            rw [hx15u]; congr 1; omega
          rw [hr15, bv64_add_neg1] at ha; exact ha
        have haddrB : sa.getReg .x15 + signExtend12 (0#12) = BitVec.ofNat 64 (tailBufBase + (m - (u + 1))) := by
          change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
        have hb := step_LBU (by omega) (rfl : sa.pc = pcAt 124) (rfl : openingInstr 124 = .base (.LBU .x6 .x15 (0#12)))
          (by rw [haddrB]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        set byteVal := packed[m - (u + 1)]'(by omega)
        let sb := (sa.setReg .x6 (byteVal.zeroExtend 64)).setPC (pcAt 125)
        have hb' : OpenRuns sa 1 1 sb := by
          have hget : sa.getByte (BitVec.ofNat 64 (tailBufBase + (m - (u + 1)))) = byteVal :=
            htailu (m - (u + 1)) (by omega)
          simpa only [haddrB, hget, sb] using hb
        have haddrC : sb.getReg .x10 + signExtend12 (0#12) = BitVec.ofNat 64 (10603204576 + fwdBytes.length + u) := by
          have hr10 : sb.getReg .x10 = BitVec.ofNat 64 (10603204576 + fwdBytes.length + u) := hx10u
          rw [hr10, hse0, bv64_ofNat_add, Nat.add_zero]
        have hc := step_SB (by omega) (rfl : sb.pc = pcAt 125) (rfl : openingInstr 125 = .base (.SB .x10 .x6 (0#12)))
          (by rw [haddrC]; exact accessValid_ofNat _ 1 (by omega) (by omega))
        let sc := (sb.setByte (BitVec.ofNat 64 (10603204576 + fwdBytes.length + u)) byteVal).setPC (pcAt 126)
        have hc' : OpenRuns sb 1 1 sc := by
          have htr : (sb.getReg .x6).truncate 8 = byteVal := by
            change (byteVal.zeroExtend 64).truncate 8 = byteVal
            apply BitVec.eq_of_toNat_eq
            simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (by have := byteVal.isLt; omega : byteVal.toNat < 2 ^ 64),
              Nat.mod_eq_of_lt byteVal.isLt]
          simpa only [haddrC, htr, sc] using hc
        have hd := step_ADDI (by omega) (rfl : sc.pc = pcAt 126) (rfl : openingInstr 126 = .base (.ADDI .x10 .x10 (1#12)))
        let sd := (sc.setReg .x10 (BitVec.ofNat 64 (10603204576 + fwdBytes.length + (u + 1)))).setPC (pcAt 127)
        have hd' : OpenRuns sc 1 1 sd := by
          have hr10 : sc.getReg .x10 = BitVec.ofNat 64 (10603204576 + fwdBytes.length + u) := by
            simp only [sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
              getReg_setReg_ne' .x6 .x10 (by decide), getReg_setReg_ne' .x15 .x10 (by decide)]; exact hx10u
          rw [hr10, hse1, bv64_ofNat_add, Nat.add_assoc] at hd; exact hd
        have hstep4 := ((ha'.trans hb').trans hc').trans hd'
        have hx15_d : sd.getReg .x15 = BitVec.ofNat 64 (tailBufBase + (m - (u + 1))) := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x10 .x15 (by decide), getReg_setReg_ne' .x6 .x15 (by decide)]; rfl
        have hx31_d : sd.getReg .x31 = BitVec.ofNat 64 tailBufBase := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x10 .x31 (by decide), getReg_setReg_ne' .x6 .x31 (by decide),
            getReg_setReg_ne' .x15 .x31 (by decide)]; exact hx31u
        have hx26_d : sd.getReg .x26 = BitVec.ofNat 64 10603204576 := by
          simp only [sd, sc, sb, sa, MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x10 .x26 (by decide), getReg_setReg_ne' .x6 .x26 (by decide),
            getReg_setReg_ne' .x15 .x26 (by decide)]; exact hx26u
        have hpr_d : ProofPrefix sd (fwdBytes ++ packed.reverse.take (u + 1)) := by
          have htake : packed.reverse.take (u + 1) = packed.reverse.take u ++ [byteVal] := by
            have hu_rev : u < packed.reverse.length := by simp [m]; omega
            rw [List.take_succ_eq_append_getElem hu_rev, List.getElem_reverse]
            have hidx : packed.length - 1 - u = packed.length - (u + 1) := by omega
            simp only [byteVal, m, hidx]
          rw [htake, ← List.append_assoc]
          intro j hj
          have hlen_pre : (fwdBytes ++ packed.reverse.take u).length = fwdBytes.length + u := by
            simp [m, Nat.min_eq_left (by omega : u ≤ m)]
          have hj_lt : j < fwdBytes.length + u + 1 := by simp [hlen_pre] at hj; omega
          simp only [sd, sc, sb, sa, getByte_setPC, getByte_setReg, set_byte_read]
          by_cases hlast : j = fwdBytes.length + u
          · subst hlast
            rw [show 10603204576 + (fwdBytes.length + u) = 10603204576 + fwdBytes.length + u by omega, if_pos rfl,
              list_getElem_append_right _ [byteVal] (fwdBytes.length + u) (by omega) hj]
            simp [hlen_pre]
          · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega)),
              list_getElem_append_left _ [byteVal] j (by omega)]
            exact hpru j (by omega)
        have htail_d : TailBufPrefix sd packed := by
          intro j hj
          simp only [sd, sc, sb, sa, getByte_setPC, getByte_setReg, set_byte_read]
          rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
          exact htailu j hj
        by_cases hmore : u + 1 < m
        · have he := step_BNE_taken (by omega) (rfl : sd.pc = pcAt 127)
            (rfl : openingInstr 127 = .base (.BNE .x15 .x31 (8176#13)))
            (by rw [hx15_d, hx31_d]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
            (by decide : pcAt 127 + signExtend13 (8176#13) = pcAt 123)
          exact ⟨sd.setPC (pcAt 123), by simpa only [Nat.mul_succ] using (hru.trans hstep4).trans he,
            by rw [if_pos hmore]; rfl, hx15_d, hx31_d, rfl, hx26_d, hpr_d, htail_d⟩
        · have hdone : m - (u + 1) = 0 := by omega
          have he := step_BNE_not_taken (by omega) (rfl : sd.pc = pcAt 127)
            (rfl : openingInstr 127 = .base (.BNE .x15 .x31 (8176#13)))
            (by rw [hx15_d, hx31_d, hdone, Nat.add_zero])
          exact ⟨sd.setPC (pcAt 128), by simpa only [Nat.mul_succ] using (hru.trans hstep4).trans he,
            by rw [if_neg hmore]; rfl, hx15_d, hx31_d, rfl, hx26_d, hpr_d, htail_d⟩
    obtain ⟨sf, hrf, hpcf, _, _, hx10f, hx26f, hprf, _⟩ := hloop m (Nat.le_refl m)
    have hpcf' : sf.pc = pcAt 128 := by simpa only [Nat.lt_irrefl, ite_false] using hpcf
    have htakeAll : packed.reverse.take m = packed.reverse := by
      rw [show m = packed.reverse.length by simp [m], List.take_length]
    rw [htakeAll] at hprf
    refine ⟨sf, h122.trans hrf, hpcf', by rw [hx10f]; congr 1; simp [m]; omega, hx26f, hprf⟩

private theorem openRuns_finish {s : MachineState} {proofLen : Nat}
    (hpc : s.pc = pcAt 128)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (10603204576 + proofLen))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 10603204576) :
    ∃ sHalt, OpenRuns s 3 3 sHalt ∧
      sHalt.pc = pcAt 131 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = BitVec.ofNat 64 proofLen ∧
      sHalt.mem = s.mem := by
  have h1 := step_SUB (by omega) hpc (rfl : openingInstr 128 = .base (.SUB .x11 .x10 .x26))
  have hsub : s.getReg .x10 - s.getReg .x26 = BitVec.ofNat 64 proofLen := by
    rw [hx10, hx26, bv64_ofNat_sub _ _ (by omega), Nat.add_sub_cancel_left]
  let s1 := (s.setReg .x11 (BitVec.ofNat 64 proofLen)).setPC (pcAt 129)
  have h1' : OpenRuns s 1 1 s1 := by simpa only [hsub, s1] using h1
  have h2 := step_ADDI (by omega) (rfl : s1.pc = pcAt 129) (rfl : openingInstr 129 = .base (.ADDI .x5 .x0 (1#12)))
  let s2 := (s1.setReg .x5 1#64).setPC (pcAt 130)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x0 + signExtend12 (1#12) = 1#64 := by change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 130) (rfl : openingInstr 130 = .base (.ADDI .x10 .x0 (0#12)))
  let s3 := (s2.setReg .x10 0#64).setPC (pcAt 131)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hv : s2.getReg .x0 + signExtend12 (0#12) = 0#64 := by change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s3] using h3
  exact ⟨s3, (h1'.trans h2').trans h3', rfl, rfl, rfl, rfl, rfl⟩

/-! ### 8. Pass 1: Record Loop (`59..81`, `L0..L15` pure-binary 238-bit siblings) -/

private def capMark16Prefix (positions : Positions) (t idx : Nat) : Bool :=
  decide (∃ u < t, (openingIndex positions u) >>> 16 = idx)

private theorem capMark16Prefix_card (positions : Positions) (idx : Nat) :
    capMark16Prefix positions positions.card idx = capMark positions 16 idx := by
  simp only [capMark16Prefix, capMark_16]
  by_cases hL : ∃ u < positions.card, (openingIndex positions u) >>> 16 = idx
  · have hR : ∃ i ∈ positions, capLeafOf i = idx := by
      obtain ⟨u, hu, heq⟩ := hL
      have hlen : u < (positions.sort (· ≤ ·)).length := by simpa using hu
      refine ⟨(positions.sort (· ≤ ·))[u]'hlen, (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem hlen), ?_⟩
      simpa only [capLeafOf, openingIndex, dif_pos hu] using heq
    simp [hL, hR]
  · have hR : ¬ ∃ i ∈ positions, capLeafOf i = idx := by
      rintro ⟨i, hi, heq⟩
      have hmem : i ∈ positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
      obtain ⟨u, hu, hget⟩ := list_mem_exists_getElem hmem
      have hu' : u < positions.card := by simpa using hu
      apply hL; refine ⟨u, hu', ?_⟩
      simp only [openingIndex, dif_pos hu', hget]; exact heq
    simp [hL, hR]

private structure RecInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (t : Nat) (fwdBytes : List Byte) (tails : List (BitVec 6))
    (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475936
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff)
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx24 : s.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * t)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 10603204576
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
    (hreg : ∀ r, r = .x2 ∨ r = .x9 ∨ r = .x18 ∨ r = .x21 ∨ r = .x24 ∨ r = .x26 ∨ r = .x27 →
      s'.getReg r = s.getReg r)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s')
    (hw : WriterState s' fwdBytes') (ht : TailState s' tails')
    (hcap : ∀ q < 4696, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) :
    RecInv trapdoor positions t fwdBytes' tails' s' :=
  ⟨by rw [hreg .x2 (by simp)]; exact inv.rx2,
   by rw [hreg .x9 (by simp)]; exact inv.rx9,
   by rw [hreg .x18 (by simp)]; exact inv.rx18,
   by rw [hreg .x21 (by simp)]; exact inv.rx21,
   by rw [hreg .x24 (by simp)]; exact inv.rx24,
   by rw [hreg .x26 (by simp)]; exact inv.rx26,
   by rw [hreg .x27 (by simp)]; exact inv.rx27,
   hro, hw, ht, fun c hc => by rw [hcap (4096 + c) (by omega)]; exact inv.cap16 c hc⟩

private theorem openRuns_rec_b238_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t l : Nat} {idx : Index} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hl : l < 16) (hpc : s.pc = pcAt 65)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (idx.val >>> l))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16))
    (hbd : fwdBytes.length + 29 ≤ 8239714016)
    (htbd : tails.length < 300000000)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let sib := (idx.val >>> l) ^^^ 1
    let fwd1 := fwdBytes ++ bitsToBytes (tdNode trapdoor l sib) 29
    let tails1 := tails ++ [tail6 (tdNode trapdoor l sib)]
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps = 32 + 5 * (fwd1.length / 8 - fwdBytes.length / 8) + 4 * (tailAccLen tails1 - tailAccLen tails) ∧
      s1.pc = (if l + 1 < 16 then pcAt 65 else pcAt 76) ∧
      s1.getReg .x22 = BitVec.ofNat 64 (idx.val >>> (l + 1)) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (l + 1)) ∧
      s1.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) ∧
      RecInv trapdoor positions t fwd1 tails1 s1 := by
  intro sib fwd1 tails1
  have hcur_lt : idx.val >>> l < 16777216 := by
    have hi : idx.val < 16777216 := idx.isLt
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hi
  have hsib_lt : sib < levelSize l := shiftRight_xor_one_lt idx l (by omega)
  have hls_le : levelSize l ≤ 16777216 := levelSize_le_max l (by omega)
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  -- 65..71: 7 steps
  have h65 := step_XORI (by omega) hpc (rfl : openingInstr 65 = .base (.XORI .x28 .x22 (1#12)))
  let s66 := (s.setReg .x28 (BitVec.ofNat 64 sib)).setPC (pcAt 66)
  have h65' : OpenRuns s 1 1 s66 := by
    rw [hx22, bv64_xor1 (idx.val >>> l) (by omega)] at h65; exact h65
  have h66 := step_SRLI (by omega) (rfl : s66.pc = pcAt 66) (rfl : openingInstr 66 = .base (.SRLI .x6 .x28 (1#6)))
  let s67 := (s66.setReg .x6 (BitVec.ofNat 64 (sib / 2))).setPC (pcAt 67)
  have h66' : OpenRuns s66 1 1 s67 := by
    have hv : s66.getReg .x28 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (sib / 2) := by
      change BitVec.ofNat 64 sib >>> 1 = _; rw [bv64_ushr sib 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s67] using h66
  have h67 := step_ADD (by omega) (rfl : s67.pc = pcAt 67) (rfl : openingInstr 67 = .base (.ADD .x28 .x28 .x6))
  let s68 := (s67.setReg .x28 (BitVec.ofNat 64 (sib + sib / 2))).setPC (pcAt 68)
  have h67' : OpenRuns s67 1 1 s68 := by
    have hv : s67.getReg .x28 + s67.getReg .x6 = BitVec.ofNat 64 (sib + sib / 2) := by
      change BitVec.ofNat 64 sib + BitVec.ofNat 64 (sib / 2) = _; exact bv64_ofNat_add _ _
    simpa only [hv, s68] using h67
  have h68 := step_SLLI (by omega) (rfl : s68.pc = pcAt 68) (rfl : openingInstr 68 = .base (.SLLI .x28 .x28 (5#6)))
  let s69 := (s68.setReg .x28 (BitVec.ofNat 64 (nodeOffset l sib))).setPC (pcAt 69)
  have h68' : OpenRuns s68 1 1 s69 := by
    have hv : s68.getReg .x28 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (nodeOffset l sib) := by
      change BitVec.ofNat 64 (sib + sib / 2) <<< 5 = _
      rw [bv64_shl]; unfold nodeOffset gapOffset; congr 1; omega
    simpa only [hv, s69] using h68
  have haddr69 : s69.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    have hr29 : s69.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := hx29
    rw [hr29, hse0, bv64_ofNat_add, Nat.add_zero]
  have h69 := step_LD (by omega) (rfl : s69.pc = pcAt 69) (rfl : openingInstr 69 = .base (.LD .x6 .x29 (0#12)))
    (by rw [haddr69]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s70 := (s69.setReg .x6 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 70)
  have h69' : OpenRuns s69 1 1 s70 := by
    have hm : s69.getMem (BitVec.ofNat 64 (68719475936 + 32 * l)) = BitVec.ofNat 64 (levelBase l) :=
      readOnly_getMem_data_base inv.ro l (by omega)
    simpa only [haddr69, hm, s70] using h69
  have h70 := step_ADD (by omega) (rfl : s70.pc = pcAt 70) (rfl : openingInstr 70 = .base (.ADD .x10 .x9 .x6))
  let s71 := (s70.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 71)
  have h70' : OpenRuns s70 1 1 s71 := by
    have hr9 : s70.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
    rw [hr9] at h70
    simpa only [show s70.getReg .x6 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s71] using h70
  have h71 := step_ADD (by omega) (rfl : s71.pc = pcAt 71) (rfl : openingInstr 71 = .base (.ADD .x10 .x10 .x28))
  let s72 := (s71.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)))).setPC (pcAt 72)
  have h71' : OpenRuns s71 1 1 s72 := by
    have hv : s71.getReg .x10 + s71.getReg .x28 = BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)) := by
      change BitVec.ofNat 64 (4294971424 + levelBase l) + BitVec.ofNat 64 (nodeOffset l sib) = _
      rw [bv64_ofNat_add, Nat.add_assoc]
    simpa only [hv, s72] using h71
  have hpre7 : OpenRuns s 7 7 s72 := (((((h65'.trans h66').trans h67').trans h68').trans h69').trans h70').trans h71'
  have hinv72 : RecInv trapdoor positions t fwdBytes tails s72 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap16⟩
  -- 72: JAL x1, 344 -> 158 (emit29_t6)
  obtain ⟨stC, s73, hrC, hstC, hpc73, hreg73, hro73, hw73, ht73, hcap73⟩ :=
    openRuns_call_emit29_t6 (callIdx := 72) (l := l) (nodeIdx := sib) (jOff := 344#21)
      (by omega) (by omega) hsib_lt rfl (by decide) rfl rfl hbd htbd hinv72.ro hinv72.writer hinv72.tail
  have hinv73 := hinv72.after_sub (fun r hr => by
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hreg73 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    hro73 hw73 ht73 hcap73
  have hx22_73 : s73.getReg .x22 = BitVec.ofNat 64 (idx.val >>> l) := by
    rw [hreg73 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx22
  have hx29_73 : s73.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    rw [hreg73 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx29
  have hx30_73 : s73.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) := by
    rw [hreg73 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hx30
  -- 73..75: SRLI x22, x22, 1; ADDI x29, x29, 32; BNE x29, x30, 8152 (-40 -> 65)
  have h73 := step_SRLI (by omega) hpc73 (rfl : openingInstr 73 = .base (.SRLI .x22 .x22 (1#6)))
  let s74 := (s73.setReg .x22 (BitVec.ofNat 64 (idx.val >>> (l + 1)))).setPC (pcAt 74)
  have h73' : OpenRuns s73 1 1 s74 := by
    have hv : s73.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (idx.val >>> (l + 1)) := by
      rw [hx22_73]; change BitVec.ofNat 64 (idx.val >>> l) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), nat_ushr_ushr1]
    simpa only [hv, s74] using h73
  have h74 := step_ADDI (by omega) (rfl : s74.pc = pcAt 74) (rfl : openingInstr 74 = .base (.ADDI .x29 .x29 (32#12)))
  let s75 := (s74.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * (l + 1)))).setPC (pcAt 75)
  have h74' : OpenRuns s74 1 1 s75 := by
    have hr29 : s74.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := hx29_73
    have hv : s74.getReg .x29 + signExtend12 (32#12) = BitVec.ofNat 64 (68719475936 + 32 * (l + 1)) := by
      rw [hr29, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s75] using h74
  have hinv75 : RecInv trapdoor positions t fwd1 tails1 s75 :=
    ⟨hinv73.rx2, hinv73.rx9, hinv73.rx18, hinv73.rx21, hinv73.rx24, hinv73.rx26, hinv73.rx27,
     hinv73.ro, hinv73.writer.of_eq, hinv73.tail.of_eq, hinv73.cap16⟩
  by_cases hmore : l + 1 < 16
  · have h75 := step_BNE_taken (by omega) (rfl : s75.pc = pcAt 75)
      (rfl : openingInstr 75 = .base (.BNE .x29 .x30 (8152#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (l + 1)) ≠ s73.getReg .x30
          rw [hx30_73]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 75 + signExtend13 (8152#13) = pcAt 65)
    exact ⟨7 + stC + 1 + 1 + 1, s75.setPC (pcAt 65), (((hpre7.trans hrC).trans h73').trans h74').trans h75,
      by rw [hstC]; dsimp only [fwd1, tails1]; omega, by simp only [hmore, ite_true]; rfl, rfl, rfl, hx30_73, hinv75.setPC (pcAt 65)⟩
  · have hdone : l + 1 = 16 := by omega
    have h75 := step_BNE_not_taken (by omega) (rfl : s75.pc = pcAt 75)
      (rfl : openingInstr 75 = .base (.BNE .x29 .x30 (8152#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (l + 1)) = s73.getReg .x30; rw [hx30_73, hdone])
    exact ⟨7 + stC + 1 + 1 + 1, s75.setPC (pcAt 76), (((hpre7.trans hrC).trans h73').trans h74').trans h75,
      by rw [hstC]; dsimp only [fwd1, tails1]; omega, by simp only [hmore, ite_false]; rfl, rfl, rfl, hx30_73, hinv75.setPC (pcAt 76)⟩

private theorem openRuns_rec_iter {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (ht : t < positions.card) (hpc : s.pc = pcAt 59)
    (hbd : fwdBytes.length ≤ (positions.card + 7) / 8 + 479 * t)
    (htbd : tails.length ≤ 16 * t)
    (inv : RecInv trapdoor positions t fwdBytes tails s) :
    let idx : Index := (positions.sort (· ≤ ·))[t]'(by simpa using ht)
    let fwd' := fwdBytes ++ recordFwd (tdNode trapdoor) (tdSalt trapdoor) idx
    let tails' := tails ++ recordTails (tdNode trapdoor) idx
    ∃ steps s', OpenRuns s steps steps s' ∧
      steps = 536 + 5 * (fwd'.length / 8 - fwdBytes.length / 8) + 4 * (tailAccLen tails' - tailAccLen tails) ∧
      s'.pc = (if t + 1 < positions.card then pcAt 59 else pcAt 82) ∧
      fwd'.length ≤ (positions.card + 7) / 8 + 479 * (t + 1) ∧
      tails'.length ≤ 16 * (t + 1) ∧
      RecInv trapdoor positions (t + 1) fwd' tails' s' := by
  intro idx fwd' tails'
  have hcard := positions_card_le positions
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hopen : openingIndex positions t = idx.val := by simp only [openingIndex, dif_pos ht]; rfl
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have hse512 : signExtend12 (512#12) = BitVec.ofNat 64 512 := by decide
  -- 59..61: LD x22, 0(x24); SLLI x6, x22, 4; ADD x10, x18, x6
  have haddr59 : s.getReg .x24 + signExtend12 (0#12) = BitVec.ofNat 64 (6174019552 + 8 * t) := by
    rw [inv.rx24, hse0, bv64_ofNat_add, Nat.add_zero]
  have h59 := step_LD (by omega) hpc (rfl : openingInstr 59 = .base (.LD .x22 .x24 (0#12)))
    (by rw [haddr59]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s60 := (s.setReg .x22 (BitVec.ofNat 64 idx.val)).setPC (pcAt 60)
  have h59' : OpenRuns s 1 1 s60 := by
    have hm := readOnly_getMem_index inv.ro t ht; rw [hopen] at hm
    simpa only [haddr59, hm, s60] using h59
  have h60 := step_SLLI (by omega) (rfl : s60.pc = pcAt 60) (rfl : openingInstr 60 = .base (.SLLI .x6 .x22 (4#6)))
  let s61 := (s60.setReg .x6 (BitVec.ofNat 64 (16 * idx.val))).setPC (pcAt 61)
  have h60' : OpenRuns s60 1 1 s61 := by
    have hv : s60.getReg .x22 <<< (4#6 : BitVec 6).toNat = BitVec.ofNat 64 (16 * idx.val) := by
      change BitVec.ofNat 64 idx.val <<< 4 = _; rw [bv64_shl]; congr 1; omega
    simpa only [hv, s61] using h60
  have h61 := step_ADD (by omega) (rfl : s61.pc = pcAt 61) (rfl : openingInstr 61 = .base (.ADD .x10 .x18 .x6))
  let s62 := (s61.setReg .x10 (BitVec.ofNat 64 (4294971424 + saltOff idx))).setPC (pcAt 62)
  have h61' : OpenRuns s61 1 1 s62 := by
    have hr18 : s61.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff) := inv.rx18
    have hv : s61.getReg .x18 + s61.getReg .x6 = BitVec.ofNat 64 (4294971424 + saltOff idx) := by
      rw [hr18]; change BitVec.ofNat 64 (4294971424 + saltsOff) + BitVec.ofNat 64 (16 * idx.val) = _
      rw [bv64_ofNat_add, Nat.add_assoc]; rfl
    simpa only [hv, s62] using h61
  -- 62: JAL x1, 296 -> 136 (emit15)
  let fwdS := fwdBytes ++ bitsToBytes (salt121Word16 (tdSalt trapdoor idx)) 15
  have hinv62 : RecInv trapdoor positions t fwdBytes tails s62 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx21, inv.rx24, inv.rx26, inv.rx27,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.cap16⟩
  obtain ⟨stS, s63, hrS, hstS, hpc63, hreg63, hro63, hw63, ht63, hcap63⟩ :=
    openRuns_call_emit15 (callIdx := 62) (jOff := 296#21) (i := idx)
      (by omega) rfl (by decide) rfl rfl (by omega) (by omega) hinv62.ro hinv62.writer hinv62.tail
  have hinv63 : RecInv trapdoor positions t fwdS tails s63 :=
    hinv62.after_sub (fun r hr => by
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hreg63 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      hro63 hw63 ht63 hcap63
  have hx22_63 : s63.getReg .x22 = BitVec.ofNat 64 idx.val := by
    rw [hreg63 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl
  -- 63..64: ADDI x29, x2, 0; ADDI x30, x2, 512
  have h63 := step_ADDI (by omega) hpc63 (rfl : openingInstr 63 = .base (.ADDI .x29 .x2 (0#12)))
  let s64 := (s63.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * 0))).setPC (pcAt 64)
  have h63' : OpenRuns s63 1 1 s64 := by
    rw [hinv63.rx2, hse0, bv64_ofNat_add, Nat.add_zero] at h63; exact h63
  have h64 := step_ADDI (by omega) (rfl : s64.pc = pcAt 64) (rfl : openingInstr 64 = .base (.ADDI .x30 .x2 (512#12)))
  let s65 := (s64.setReg .x30 (BitVec.ofNat 64 (68719475936 + 32 * 16))).setPC (pcAt 65)
  have h64' : OpenRuns s64 1 1 s65 := by
    have hr2 : s64.getReg .x2 = BitVec.ofNat 64 68719475936 := hinv63.rx2
    rw [hr2, hse512, bv64_ofNat_add] at h64; exact h64
  have hinv65 : RecInv trapdoor positions t fwdS tails s65 :=
    ⟨hinv63.rx2, hinv63.rx9, hinv63.rx18, hinv63.rx21, hinv63.rx24, hinv63.rx26, hinv63.rx27,
     hinv63.ro, hinv63.writer.of_eq, hinv63.tail.of_eq, hinv63.cap16⟩
  -- 65..75: 16 iterations of open_b238
  have hlenS : fwdS.length = fwdBytes.length + 15 := by simp [fwdS, bitsToBytes_length]
  have hloop16 : ∀ n ≤ 16,
      let curF := fwdS ++ (List.range n).flatMap (fun l => bitsToBytes (tdNode trapdoor l ((idx.val >>> l) ^^^ 1)) 29)
      let curT := tails ++ (List.range n).flatMap (fun l => [tail6 (tdNode trapdoor l ((idx.val >>> l) ^^^ 1))])
      ∃ steps sn, OpenRuns s65 steps steps sn ∧
        steps = 32 * n + 5 * (curF.length / 8 - fwdS.length / 8) + 4 * (tailAccLen curT - tailAccLen tails) ∧
        sn.pc = (if n < 16 then pcAt 65 else pcAt 76) ∧
        sn.getReg .x22 = BitVec.ofNat 64 (idx.val >>> n) ∧
        sn.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * n) ∧
        sn.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 16) ∧
        curF.length = fwdS.length + 29 * n ∧
        curT.length = tails.length + n ∧
        RecInv trapdoor positions t curF curT sn := by
    intro n hn
    induction n with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.add_zero,
        Nat.sub_self, Nat.shiftRight_zero]
      exact ⟨0, s65, OpenRuns.refl s65, rfl, by simp only [show (0 : Nat) < 16 by decide, ite_true]; rfl,
        by change s63.getReg .x22 = _; exact hx22_63,
        by change BitVec.ofNat 64 (68719475936 + 32 * 0) = _; rfl, rfl, trivial, trivial, hinv65⟩
    | succ n ih =>
      obtain ⟨st, sn, hrn, hstn, hpcn, hx22n, hx29n, hx30n, hlenF, hlenT, invn⟩ := ih (by omega)
      have hpcn' : sn.pc = pcAt 65 := by simpa only [show n < 16 by omega, ite_true] using hpcn
      obtain ⟨st1, sn1, hr1, hst1, hpc1, hx22_1, hx29_1, hx30_1, inv1⟩ :=
        openRuns_rec_b238_step (by omega) hpcn' hx22n hx29n hx30n (by omega) (by omega) invn
      have happF : fwdS ++ (List.range n).flatMap (fun l => bitsToBytes (tdNode trapdoor l ((idx.val >>> l) ^^^ 1)) 29) ++
            bitsToBytes (tdNode trapdoor n ((idx.val >>> n) ^^^ 1)) 29 =
          fwdS ++ (List.range (n + 1)).flatMap (fun l => bitsToBytes (tdNode trapdoor l ((idx.val >>> l) ^^^ 1)) 29) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      have happT : tails ++ (List.range n).flatMap (fun l => [tail6 (tdNode trapdoor l ((idx.val >>> l) ^^^ 1))]) ++
            [tail6 (tdNode trapdoor n ((idx.val >>> n) ^^^ 1))] =
          tails ++ (List.range (n + 1)).flatMap (fun l => [tail6 (tdNode trapdoor l ((idx.val >>> l) ^^^ 1))]) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      have hmonoF1 : fwdS.length / 8 ≤ (fwdS ++ (List.range n).flatMap (fun l => bitsToBytes (tdNode trapdoor l ((idx.val >>> l) ^^^ 1)) 29)).length / 8 :=
        Nat.div_le_div_right (by omega)
      have hmonoF2 : (fwdS ++ (List.range n).flatMap (fun l => bitsToBytes (tdNode trapdoor l ((idx.val >>> l) ^^^ 1)) 29)).length / 8 ≤
          (fwdS ++ (List.range (n + 1)).flatMap (fun l => bitsToBytes (tdNode trapdoor l ((idx.val >>> l) ^^^ 1)) 29)).length / 8 := by
        rw [← happF]; exact Nat.div_le_div_right (by simp)
      have hmonoT1 : tailAccLen tails ≤ tailAccLen (tails ++ (List.range n).flatMap (fun l => [tail6 (tdNode trapdoor l ((idx.val >>> l) ^^^ 1))])) :=
        tailAccLen_mono_append _ _
      have hmonoT2 : tailAccLen (tails ++ (List.range n).flatMap (fun l => [tail6 (tdNode trapdoor l ((idx.val >>> l) ^^^ 1))])) ≤
          tailAccLen (tails ++ (List.range (n + 1)).flatMap (fun l => [tail6 (tdNode trapdoor l ((idx.val >>> l) ^^^ 1))])) := by
        rw [← happT]; exact tailAccLen_mono_append _ _
      rw [happF] at hst1 inv1
      rw [happT] at hst1 inv1
      refine ⟨st + st1, sn1, hrn.trans hr1, by rw [hstn, hst1]; omega, hpc1, hx22_1, hx29_1, hx30_1, ?_, ?_, inv1⟩
      · rw [← happF, List.length_append, bitsToBytes_length, hlenF]; omega
      · rw [← happT, List.length_append, List.length_singleton, hlenT]; omega
  obtain ⟨st16, s76, hr16, hst16, hpc76, hx22_76, _, _, hlen16F, hlen16T, inv76⟩ := hloop16 16 (Nat.le_refl 16)
  have hpc76' : s76.pc = pcAt 76 := by simpa only [Nat.lt_irrefl, ite_false] using hpc76
  have happF_all : fwdS ++ (List.range 16).flatMap (fun l => bitsToBytes (tdNode trapdoor l ((idx.val >>> l) ^^^ 1)) 29) = fwd' := by
    simp only [fwdS, fwd', recordFwd, binPathFwd, List.append_assoc]
  have happT_all : tails ++ (List.range 16).flatMap (fun l => [tail6 (tdNode trapdoor l ((idx.val >>> l) ^^^ 1))]) = tails' := rfl
  rw [happF_all] at hst16 hlen16F inv76
  rw [happT_all] at hst16 hlen16T inv76
  have hlen_recF : fwd'.length ≤ (positions.card + 7) / 8 + 479 * (t + 1) := by omega
  have hlen_recT : tails'.length ≤ 16 * (t + 1) := by omega
  -- 76..81: mark cap16, advance x24, decrement x27, BNE
  have hcap_lt : idx.val >>> 16 < 256 := capLeafOf_lt idx
  have h76 := step_ADD (by omega) hpc76' (rfl : openingInstr 76 = .base (.ADD .x6 .x21 .x22))
  let s77 := (s76.setReg .x6 (BitVec.ofNat 64 (4096 + (idx.val >>> 16)))).setPC (pcAt 77)
  have h76' : OpenRuns s76 1 1 s77 := by
    rw [inv76.rx21, hx22_76, bv64_ofNat_add] at h76; exact h76
  have h77 := step_ADDI (by omega) (rfl : s77.pc = pcAt 77) (rfl : openingInstr 77 = .base (.ADDI .x7 .x0 (1#12)))
  let s78 := (s77.setReg .x7 1#64).setPC (pcAt 78)
  have h77' : OpenRuns s77 1 1 s78 := by
    have hv : s77.getReg .x0 + signExtend12 (1#12) = 1#64 := by change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s78] using h77
  have haddr78 : s78.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (4096 + (idx.val >>> 16)) := by
    change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h78 := step_SB (by omega) (rfl : s78.pc = pcAt 78) (rfl : openingInstr 78 = .base (.SB .x6 .x7 (0#12)))
    (by rw [haddr78]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s79 := (s78.setByte (BitVec.ofNat 64 (4096 + (idx.val >>> 16))) 1#8).setPC (pcAt 79)
  have h78' : OpenRuns s78 1 1 s79 := by
    have htr : (s78.getReg .x7).truncate 8 = 1#8 := by change (1#64 : Word).truncate 8 = 1#8; decide
    simpa only [haddr78, htr, s79] using h78
  have h79 := step_ADDI (by omega) (rfl : s79.pc = pcAt 79) (rfl : openingInstr 79 = .base (.ADDI .x24 .x24 (8#12)))
  let s80 := (s79.setReg .x24 (BitVec.ofNat 64 (6174019552 + 8 * (t + 1)))).setPC (pcAt 80)
  have h79' : OpenRuns s79 1 1 s80 := by
    have hr24 : s79.getReg .x24 = BitVec.ofNat 64 (6174019552 + 8 * t) := by
      simp only [s79, s78, s77, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x7 .x24 (by decide), getReg_setReg_ne' .x6 .x24 (by decide)]; exact inv76.rx24
    have hv : s79.getReg .x24 + signExtend12 (8#12) = BitVec.ofNat 64 (6174019552 + 8 * (t + 1)) := by
      rw [hr24, hse8, bv64_ofNat_add]; congr 1
    simpa only [hv, s80] using h79
  have h80 := step_ADDI (by omega) (rfl : s80.pc = pcAt 80) (rfl : openingInstr 80 = .base (.ADDI .x27 .x27 (4095#12)))
  let s81 := (s80.setReg .x27 (BitVec.ofNat 64 (positions.card - (t + 1)))).setPC (pcAt 81)
  have h80' : OpenRuns s80 1 1 s81 := by
    have hr27 : s80.getReg .x27 = BitVec.ofNat 64 ((positions.card - (t + 1)) + 1) := by
      simp only [s80, s79, s78, s77, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x24 .x27 (by decide), getReg_setReg_ne' .x7 .x27 (by decide),
        getReg_setReg_ne' .x6 .x27 (by decide)]
      rw [inv76.rx27]; congr 1; omega
    rw [hr27, bv64_add_neg1] at h80; exact h80
  have hpres81 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x24 → r ≠ .x27 → s81.getReg r = s76.getReg r :=
    fun r h6 h7 h24 h27 => by
      simp only [s81, s80, s79, s78, s77, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x27 r (Ne.symm h27), getReg_setReg_ne' .x24 r (Ne.symm h24),
        getReg_setReg_ne' .x7 r (Ne.symm h7), getReg_setReg_ne' .x6 r (Ne.symm h6)]
  have hmem81 : ∀ a, s81.getByte a = (s76.setByte (BitVec.ofNat 64 (4096 + (idx.val >>> 16))) 1#8).getByte a :=
    fun a => by simp only [s81, s80, s79, s78, s77, getByte_setPC, getByte_setReg]; rfl
  have hro81 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s81 := by
    intro a ha; simp only [s81, s80, s79, MachineState.getMem_setPC, MachineState.getMem_setReg]
    exact readOnly_setByte_cap (4096 + (idx.val >>> 16)) 1#8 inv76.ro (by omega) (by omega) a ha
  have hcard_rec := positions_card_le positions
  have hbd_rec' : fwd'.length ≤ 8239714016 := by
    have h1 : (positions.card + 7) / 8 ≤ 2097152 := by omega
    have h2 : 479 * (t + 1) ≤ 479 * 16777216 := Nat.mul_le_mul_left 479 (Nat.le_trans (Nat.succ_le_of_lt ht) hcard_rec)
    exact Nat.le_trans hlen_recF (Nat.le_trans (Nat.add_le_add h1 h2) (by decide))
  have hw81 : WriterState s81 fwd' := by
    have hw' := writerState_setByte_outside (4096 + (idx.val >>> 16)) 1#8 inv76.writer
      hbd_rec' (Or.inl (by omega)) (by omega)
    exact ⟨by rw [hpres81 .x25 (by decide) (by decide) (by decide) (by decide)]; exact inv76.writer.rx25,
      by rw [hpres81 .x13 (by decide) (by decide) (by decide) (by decide)]; exact inv76.writer.rx13,
      by rw [hpres81 .x14 (by decide) (by decide) (by decide) (by decide)]; exact inv76.writer.rx14,
      fun j hj => by rw [hpres81 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv76.writer.wbufLo j hj,
      fun j h1 h2 => by rw [hpres81 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv76.writer.wbufHi j h1 h2,
      fun j hj => by rw [hmem81]; exact hw'.memDwords j hj⟩
  have ht81 : TailState s81 tails' := by
    have htb : tailBufBase = 25769803776 := rfl
    have ht' := tailState_setByte_outside (4096 + (idx.val >>> 16)) 1#8 inv76.tail (by omega) (by omega)
    exact ⟨by rw [hpres81 .x31 (by decide) (by decide) (by decide) (by decide)]; exact inv76.tail.rx31,
      by rw [hpres81 .x15 (by decide) (by decide) (by decide) (by decide)]; exact inv76.tail.rx15,
      by rw [hpres81 .x16 (by decide) (by decide) (by decide) (by decide)]; exact inv76.tail.rx16,
      by rw [hpres81 .x17 (by decide) (by decide) (by decide) (by decide)]; exact inv76.tail.rx17,
      fun j hj => by rw [hmem81]; exact ht'.memTail j hj⟩
  have hcap81 : ∀ c < 256, s81.getByte (BitVec.ofNat 64 (4096 + c)) =
      if capMark16Prefix positions (t + 1) c then 1#8 else 0#8 := by
    intro c hc
    rw [hmem81, set_byte_read]
    by_cases hceq : c = idx.val >>> 16
    · subst hceq; rw [if_pos rfl]
      have htr : capMark16Prefix positions (t + 1) (idx.val >>> 16) = true := by
        simp only [capMark16Prefix, decide_eq_true_eq]; exact ⟨t, by omega, by rw [hopen]⟩
      rw [htr]; rfl
    · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega)), inv76.cap16 c hc]
      have hsame : capMark16Prefix positions (t + 1) c = capMark16Prefix positions t c := by
        simp only [capMark16Prefix]
        by_cases hp : ∃ u < t, openingIndex positions u >>> 16 = c
        · obtain ⟨u, hu, heq⟩ := hp
          rw [decide_eq_true ⟨u, by omega, heq⟩, decide_eq_true ⟨u, hu, heq⟩]
        · have hp1 : ¬ ∃ u < t + 1, openingIndex positions u >>> 16 = c := by
            rintro ⟨u, hu, heq⟩
            by_cases hut : u < t
            · exact hp ⟨u, hut, heq⟩
            · have hueq : u = t := by omega
              subst hueq; rw [hopen] at heq; exact hceq heq.symm
          rw [decide_eq_false hp, decide_eq_false hp1]
      rw [hsame]
  have hinv81 : RecInv trapdoor positions (t + 1) fwd' tails' s81 :=
    ⟨by rw [hpres81 .x2 (by decide) (by decide) (by decide) (by decide)]; exact inv76.rx2,
     by rw [hpres81 .x9 (by decide) (by decide) (by decide) (by decide)]; exact inv76.rx9,
     by rw [hpres81 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv76.rx18,
     by rw [hpres81 .x21 (by decide) (by decide) (by decide) (by decide)]; exact inv76.rx21,
     by simp only [s81, MachineState.getReg_setPC, getReg_setReg_ne' .x27 .x24 (by decide)]; rfl,
     by rw [hpres81 .x26 (by decide) (by decide) (by decide) (by decide)]; exact inv76.rx26,
     rfl, hro81, hw81, ht81, hcap81⟩
  have htail5 := (((h76'.trans h77').trans h78').trans h79').trans h80'
  have hbody := ((((((h59'.trans h60').trans h61').trans hrS).trans h63').trans h64').trans hr16).trans htail5
  have hfwdS_eq : fwdBytes ++ bitsToBytes (salt121Word16 (tdSalt trapdoor idx)) 15 = fwdS := rfl
  rw [hfwdS_eq] at hstS
  have hq_mono1 : fwdBytes.length / 8 ≤ fwdS.length / 8 := Nat.div_le_div_right (by omega)
  have hq_mono2 : fwdS.length / 8 ≤ fwd'.length / 8 := Nat.div_le_div_right (by omega)
  have ht_mono : tailAccLen tails ≤ tailAccLen tails' := tailAccLen_mono_append _ _
  by_cases hmore : t + 1 < positions.card
  · have h81 := step_BNE_taken (by omega) (rfl : s81.pc = pcAt 81)
      (rfl : openingInstr 81 = .base (.BNE .x27 .x0 (8104#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) ≠ BitVec.ofNat 64 0
          exact bv64_ofNat_ne (by omega) (by decide) (by omega))
      (by decide : pcAt 81 + signExtend13 (8104#13) = pcAt 59)
    exact ⟨3 + stS + 2 + st16 + 5 + 1, s81.setPC (pcAt 59), hbody.trans h81,
      by rw [hstS, hst16]; omega, by simp only [hmore, ite_true]; rfl, hlen_recF, hlen_recT, hinv81.setPC (pcAt 59)⟩
  · have hdone : positions.card - (t + 1) = 0 := by omega
    have h81 := step_BNE_not_taken (by omega) (rfl : s81.pc = pcAt 81)
      (rfl : openingInstr 81 = .base (.BNE .x27 .x0 (8104#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) = 0#64; rw [hdone])
    exact ⟨3 + stS + 2 + st16 + 5 + 1, s81.setPC (pcAt 82), hbody.trans h81,
      by rw [hstS, hst16]; omega, by simp only [hmore, ite_false]; rfl, hlen_recF, hlen_recT, hinv81.setPC (pcAt 82)⟩

private theorem openRuns_rec_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s59 : MachineState}
    (hne : 0 < positions.card) (hpc : s59.pc = pcAt 59)
    (inv0 : RecInv trapdoor positions 0 (packSaltTopBits (tdSalt trapdoor) positions) [] s59) :
    let fwd0 := packSaltTopBits (tdSalt trapdoor) positions
    let recFwd := fwd0 ++ (positions.sort (· ≤ ·)).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
    let recTails := (positions.sort (· ≤ ·)).flatMap (recordTails (tdNode trapdoor))
    ∃ steps s82, OpenRuns s59 steps steps s82 ∧
      steps = 536 * positions.card + 5 * (recFwd.length / 8 - fwd0.length / 8) + 4 * tailAccLen recTails ∧
      s82.pc = pcAt 82 ∧
      s82.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s82.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s82.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s82.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
      recFwd.length ≤ (positions.card + 7) / 8 + 479 * positions.card ∧
      recTails.length ≤ 16 * positions.card ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s82 ∧
      WriterState s82 recFwd ∧
      TailState s82 recTails ∧
      CapLevelMarks s82 positions 16 := by
  intro fwd0 recFwd recTails
  have hfwd0_len : fwd0.length = (positions.card + 7) / 8 := packSaltTopBits_length _ _
  have hloop : ∀ t ≤ positions.card,
      let curF := fwd0 ++ ((positions.sort (· ≤ ·)).take t).flatMap
        (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
      let curT := ((positions.sort (· ≤ ·)).take t).flatMap
        (recordTails (tdNode trapdoor))
      ∃ steps st, OpenRuns s59 steps steps st ∧
        steps = 536 * t + 5 * (curF.length / 8 - fwd0.length / 8) + 4 * tailAccLen curT ∧
        st.pc = (if t < positions.card then pcAt 59 else pcAt 82) ∧
        curF.length ≤ (positions.card + 7) / 8 + 479 * t ∧
        curT.length ≤ 16 * t ∧
        RecInv trapdoor positions t curF curT st := by
    intro t ht
    induction t with
    | zero =>
      dsimp only
      simp only [List.take_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.add_zero,
        Nat.sub_self, tailAccLen_nil]
      exact ⟨0, s59, OpenRuns.refl s59, rfl, by rw [if_pos hne]; exact hpc, by omega, Nat.le_refl 0, inv0⟩
    | succ t ih =>
      obtain ⟨st, stState, hr, hst, hpct, hbdt, htbdt, invt⟩ := ih (by omega)
      have hpct' : stState.pc = pcAt 59 := by simpa only [show t < positions.card by omega, ite_true] using hpct
      obtain ⟨st1, stNext, hr1, hst1, hpc1, hbd1, htbd1, inv1⟩ :=
        openRuns_rec_iter (by omega) hpct' hbdt htbdt invt
      have hlen : t < (positions.sort (· ≤ ·)).length := by simpa using (by omega : t < positions.card)
      have htakeF : fwd0 ++ ((positions.sort (· ≤ ·)).take (t + 1)).flatMap
            (recordFwd (tdNode trapdoor) (tdSalt trapdoor)) =
          (fwd0 ++ ((positions.sort (· ≤ ·)).take t).flatMap
            (recordFwd (tdNode trapdoor) (tdSalt trapdoor))) ++
          recordFwd (tdNode trapdoor) (tdSalt trapdoor) ((positions.sort (· ≤ ·))[t]'hlen) := by
        rw [List.take_succ_eq_append_getElem hlen, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      have htakeT : ((positions.sort (· ≤ ·)).take (t + 1)).flatMap
            (recordTails (tdNode trapdoor)) =
          ((positions.sort (· ≤ ·)).take t).flatMap
            (recordTails (tdNode trapdoor)) ++
          recordTails (tdNode trapdoor) ((positions.sort (· ≤ ·))[t]'hlen) := by
        rw [List.take_succ_eq_append_getElem hlen, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have hmonoF1 : fwd0.length / 8 ≤ (fwd0 ++ ((positions.sort (· ≤ ·)).take t).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))).length / 8 :=
        Nat.div_le_div_right (by simp)
      have hmonoF2 : (fwd0 ++ ((positions.sort (· ≤ ·)).take t).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))).length / 8 ≤
          (fwd0 ++ ((positions.sort (· ≤ ·)).take (t + 1)).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))).length / 8 := by
        rw [htakeF]; exact Nat.div_le_div_right (by simp)
      have hmonoT : tailAccLen (((positions.sort (· ≤ ·)).take t).flatMap (recordTails (tdNode trapdoor))) ≤
          tailAccLen (((positions.sort (· ≤ ·)).take (t + 1)).flatMap (recordTails (tdNode trapdoor))) := by
        rw [htakeT]; exact tailAccLen_mono_append _ _
      rw [← htakeF] at hst1 hbd1 inv1
      rw [← htakeT] at hst1 htbd1 inv1
      exact ⟨st + st1, stNext, hr.trans hr1, by rw [hst, hst1]; omega, hpc1, hbd1, htbd1, inv1⟩
  obtain ⟨steps, s82, hr, hst, hpc82, hbdEnd, htbdEnd, invEnd⟩ := hloop positions.card (Nat.le_refl _)
  have hpc82' : s82.pc = pcAt 82 := by simpa only [Nat.lt_irrefl, ite_false] using hpc82
  have htakeAll : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) := by
    have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
    rw [← hlen, List.take_length]
  rw [htakeAll] at hst hbdEnd htbdEnd invEnd
  refine ⟨steps, s82, hr, hst, hpc82',
    invEnd.rx2, invEnd.rx9, invEnd.rx21, invEnd.rx26,
    hbdEnd, htbdEnd, invEnd.ro, invEnd.writer, invEnd.tail, ?_⟩
  intro idx hidx
  have hidx256 : idx < 256 := by rw [levelSize_16] at hidx; exact hidx
  have hmo16 : capMarkOff 16 = 0 := by decide
  rw [hmo16, Nat.add_zero, invEnd.cap16 idx hidx256, capMark16Prefix_card]

/-! ### 9. Pass 2: Pure-Binary Cap Frontier (`82..111`, 8 levels `L16..L23`) -/

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
  rx26 : s.getReg .x26 = BitVec.ofNat 64 10603204576
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (16 + step))
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 24)
  boundFwd : fwdBytes.length ≤ (positions.card + 7) / 8 + 479 * positions.card +
    29 * (∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k))
  boundTails : tails.length ≤ 16 * positions.card +
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
  rx26 : s.getReg .x26 = BitVec.ofNat 64 10603204576
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (16 + step))
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 24)
  boundFwd : fwdBytes.length ≤ (positions.card + 7) / 8 + 479 * positions.card +
    29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
          (∑ j ∈ Finset.range q, capPairFrontier positions (16 + step) j))
  boundTails : tails.length ≤ 16 * positions.card +
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
    (hstep : step < 8) (hq : q < levelSize (16 + step) / 2) (hpc : s.pc = pcAt 93)
    (inv : CapPairInv trapdoor positions step q fwdBytes tails s) :
    let l := 16 + step
    let fwd1 := fwdBytes ++ capPairFwd trapdoor positions l q
    let tails1 := tails ++ capPairTails trapdoor positions l q
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 10 + 28 * capPairFrontier positions l q +
        5 * (fwd1.length / 8 - fwdBytes.length / 8) + 4 * (tailAccLen tails1 - tailAccLen tails) ∧
      s1.pc = (if q + 1 < levelSize l / 2 then pcAt 93 else pcAt 110) ∧
      CapPairInv trapdoor positions step (q + 1) fwd1 tails1 s1 := by
  intro l fwd1 tails1
  have hql : q < levelSize l / 2 := hq
  have hcur_inv : CapLevelMarks s positions l := inv.curMarks
  have hinv_bdF : fwdBytes.length ≤ (positions.card + 7) / 8 + 479 * positions.card +
      29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
            (∑ j ∈ Finset.range q, capPairFrontier positions l j)) := inv.boundFwd
  have hinv_bdT : tails.length ≤ 16 * positions.card +
      ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
       (∑ j ∈ Finset.range q, capPairFrontier positions l j)) := inv.boundTails
  have hcard := positions_card_le positions
  have hls_le := levelSize_le_max l (by omega)
  have hcm_bd := capMarkOff_bound l (by omega) (by omega)
  have hcm1_bd := capMarkOff_bound (l + 1) (by omega) (by omega)
  have hcm_disj := capMarkOff_step_disjoint l (by omega) (by omega)
  have hls1_eq := levelSize_step l (by omega)
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  set mL := capMark positions l (2 * q)
  set mR := capMark positions l (2 * q + 1)
  -- 93..99: 7 steps
  have h93 := step_SLLI (by omega) hpc (rfl : openingInstr 93 = .base (.SLLI .x6 .x24 (1#6)))
  let s94 := (s.setReg .x6 (BitVec.ofNat 64 (2 * q))).setPC (pcAt 94)
  have h93' : OpenRuns s 1 1 s94 := by
    have hv : s.getReg .x24 <<< (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (2 * q) := by
      rw [inv.rx24]; change BitVec.ofNat 64 q <<< 1 = _; rw [bv64_shl]; congr 1; omega
    simpa only [hv, s94] using h93
  have h94 := step_ADD (by omega) (rfl : s94.pc = pcAt 94) (rfl : openingInstr 94 = .base (.ADD .x6 .x20 .x6))
  let s95 := (s94.setReg .x6 (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q))).setPC (pcAt 95)
  have h94' : OpenRuns s94 1 1 s95 := by
    have hr20 : s94.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) := inv.rx20
    rw [hr20] at h94
    simpa only [show s94.getReg .x6 = BitVec.ofNat 64 (2 * q) from rfl, bv64_ofNat_add, s95] using h94
  have haddr95 : s95.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) := by
    change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h95 := step_LBU (by omega) (rfl : s95.pc = pcAt 95) (rfl : openingInstr 95 = .base (.LBU .x7 .x6 (0#12)))
    (by rw [haddr95]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s96 := (s95.setReg .x7 (if mL then 1#64 else 0#64)).setPC (pcAt 96)
  have h95' : OpenRuns s95 1 1 s96 := by
    have hb : s95.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q)) = if mL then 1#8 else 0#8 :=
      hcur_inv (2 * q) (by omega)
    simpa only [haddr95, hb, bool_byte_zeroExtend mL, s96] using h95
  have haddr96 : s96.getReg .x6 + signExtend12 (1#12) = BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1)) := by
    change BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) + _ = _
    rw [hse1, bv64_ofNat_add]; congr 1
  have h96 := step_LBU (by omega) (rfl : s96.pc = pcAt 96) (rfl : openingInstr 96 = .base (.LBU .x8 .x6 (1#12)))
    (by rw [haddr96]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s97 := (s96.setReg .x8 (if mR then 1#64 else 0#64)).setPC (pcAt 97)
  have h96' : OpenRuns s96 1 1 s97 := by
    have hb : s96.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1))) = if mR then 1#8 else 0#8 :=
      hcur_inv (2 * q + 1) (by omega)
    simpa only [haddr96, hb, bool_byte_zeroExtend mR, s97] using h96
  have h97 := step_OR (by omega) (rfl : s97.pc = pcAt 97) (rfl : openingInstr 97 = .base (.OR .x11 .x7 .x8))
  let s98 := (s97.setReg .x11 (if (mL || mR) then 1#64 else 0#64)).setPC (pcAt 98)
  have h97' : OpenRuns s97 1 1 s98 := by
    simpa only [show s97.getReg .x7 = if mL then 1#64 else 0#64 from rfl,
      show s97.getReg .x8 = if mR then 1#64 else 0#64 from rfl, bool_word_or mL mR, s98] using h97
  have h98 := step_ADD (by omega) (rfl : s98.pc = pcAt 98) (rfl : openingInstr 98 = .base (.ADD .x6 .x22 .x24))
  let s99 := (s98.setReg .x6 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q))).setPC (pcAt 99)
  have h98' : OpenRuns s98 1 1 s99 := by
    have hr22 : s98.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) := inv.rx22
    have hr24 : s98.getReg .x24 = BitVec.ofNat 64 q := inv.rx24
    rw [hr22, hr24, bv64_ofNat_add] at h98; exact h98
  have haddr99 : s99.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) := by
    change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h99 := step_SB (by omega) (rfl : s99.pc = pcAt 99) (rfl : openingInstr 99 = .base (.SB .x6 .x11 (0#12)))
    (by rw [haddr99]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s100 := (s99.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q))
    (if (mL || mR) then 1#8 else 0#8)).setPC (pcAt 100)
  have h99' : OpenRuns s99 1 1 s100 := by
    simpa only [haddr99, show s99.getReg .x11 = if (mL || mR) then 1#64 else 0#64 from rfl,
      bool_word_truncate8 (mL || mR), s100] using h99
  have hpre : OpenRuns s 7 7 s100 := (((((h93'.trans h94').trans h95').trans h96').trans h97').trans h98').trans h99'
  have hcap128 := cap_frontier_le_128 positions
  have hfront_le : (∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
      (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j) ≤ 128 := by
    have hq_le : (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j) ≤ levelFrontierCount positions (16 + step) := by
      change _ ≤ levelFrontierCount positions l
      rw [← sum_capPairFrontier_eq]; exact sum_range_le_of_le (capPairFrontier positions l) (by omega)
    have hsum_le : (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (16 + k)) ≤ capFrontierCount positions := by
      unfold capFrontierCount; exact sum_range_le_of_le (fun k => levelFrontierCount positions (16 + k)) (by omega)
    rw [Finset.sum_range_succ] at hsum_le; omega
  have hfront_q_le : (∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
      (∑ j ∈ Finset.range q, capPairFrontier positions l j) ≤ 128 := by
    have : (∑ j ∈ Finset.range q, capPairFrontier positions l j) ≤
        ∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j := by
      rw [Finset.sum_range_succ]; omega
    omega
  have hpres100 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x11 → s100.getReg r = s.getReg r :=
    fun r h6 h7 h8 h11 => by
      simp only [s100, s99, s98, s97, s96, s95, s94, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x6 r (Ne.symm h6), getReg_setReg_ne' .x11 r (Ne.symm h11),
        getReg_setReg_ne' .x8 r (Ne.symm h8), getReg_setReg_ne' .x7 r (Ne.symm h7)]
  have hmem100 : ∀ a, s100.getByte a =
      (s.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q)) (if (mL || mR) then 1#8 else 0#8)).getByte a :=
    fun a => by simp only [s100, s99, s98, s97, s96, s95, s94, getByte_setPC]; rfl
  have hro100 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s100 := by
    intro a ha; simp only [s100, MachineState.getMem_setPC]
    exact readOnly_setByte_cap (4096 + capMarkOff (l + 1) + q) _ inv.ro (by omega) (by omega) a ha
  have hw100 : WriterState s100 fwdBytes := by
    have hw' := writerState_setByte_outside (4096 + capMarkOff (l + 1) + q)
      (if (mL || mR) then 1#8 else 0#8) inv.writer
      (by omega) (Or.inl (by omega)) (by omega)
    exact ⟨by rw [hpres100 .x25 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx25,
      by rw [hpres100 .x13 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx13,
      by rw [hpres100 .x14 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.rx14,
      fun j hj => by rw [hpres100 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.wbufLo j hj,
      fun j h1 h2 => by rw [hpres100 .x12 (by decide) (by decide) (by decide) (by decide)]; exact inv.writer.wbufHi j h1 h2,
      fun j hj => by rw [hmem100]; exact hw'.memDwords j hj⟩
  have ht100 : TailState s100 tails := by
    have htb : tailBufBase = 25769803776 := rfl
    have ht' := tailState_setByte_outside (4096 + capMarkOff (l + 1) + q)
      (if (mL || mR) then 1#8 else 0#8) inv.tail (by omega) (by omega)
    exact ⟨by rw [hpres100 .x31 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx31,
      by rw [hpres100 .x15 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx15,
      by rw [hpres100 .x16 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx16,
      by rw [hpres100 .x17 (by decide) (by decide) (by decide) (by decide)]; exact inv.tail.rx17,
      fun j hj => by rw [hmem100]; exact ht'.memTail j hj⟩
  have hcur100 : CapLevelMarks s100 positions l := by
    intro idx hidx
    rw [hmem100, set_byte_read, if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
    exact hcur_inv idx hidx
  have hnext100 : ∀ j < q + 1, s100.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + j)) =
      if capMark positions (l + 1) j then 1#8 else 0#8 := by
    intro j hj
    rw [hmem100, set_byte_read]
    by_cases hjeq : j = q
    · subst hjeq
      have hdbl : levelSize l = 2 * levelSize (l + 1) := levelSize_double l (by omega)
      have hlt_l : 2 * j + 1 < levelSize l := by omega
      simp only [ite_true, capMark_succ positions l j (by omega), hlt_l, mL, mR]
    · have hne : BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + j) ≠ BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) :=
        bv64_ofNat_ne (by omega) (by omega) (by omega)
      simp only [hne, ite_false]; exact inv.nextMarks j (by omega)
  have hx7_100 : s100.getReg .x7 = if mL then 1#64 else 0#64 := by
    simp only [s100, s99, s98, s97, s96, MachineState.getReg_setPC, getReg_setByte,
      getReg_setReg_ne' .x6 .x7 (by decide), getReg_setReg_ne' .x11 .x7 (by decide),
      getReg_setReg_ne' .x8 .x7 (by decide)]; rfl
  have hx8_100 : s100.getReg .x8 = if mR then 1#64 else 0#64 := by
    simp only [s100, s99, s98, s97, MachineState.getReg_setPC, getReg_setByte,
      getReg_setReg_ne' .x6 .x8 (by decide), getReg_setReg_ne' .x11 .x8 (by decide)]; rfl
  -- Branch at 100 -> pcAt 108
  have hto108 : ∃ n108 s108, OpenRuns s100 n108 n108 s108 ∧
      n108 ≤ 1 + 28 * capPairFrontier positions l q +
        5 * (fwd1.length / 8 - fwdBytes.length / 8) + 4 * (tailAccLen tails1 - tailAccLen tails) ∧
      s108.pc = pcAt 108 ∧
      s108.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s108.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s108.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l) ∧
      s108.getReg .x19 = BitVec.ofNat 64 (levelSize l) ∧
      s108.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
      s108.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s108.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
      s108.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) ∧
      s108.getReg .x24 = BitVec.ofNat 64 q ∧
      s108.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
      s108.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) ∧
      s108.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 24) ∧
      fwd1.length ≤ (positions.card + 7) / 8 + 479 * positions.card +
        29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
              (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) ∧
      tails1.length ≤ 16 * positions.card +
        ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
         (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s108 ∧
      WriterState s108 fwd1 ∧
      TailState s108 tails1 ∧
      CapLevelMarks s108 positions l ∧
      (∀ j < q + 1, s108.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + j)) =
        if capMark positions (l + 1) j then 1#8 else 0#8) := by
    by_cases hsame : mL = mR
    · have h100 := step_BEQ_taken (by omega) (rfl : s100.pc = pcAt 100)
        (rfl : openingInstr 100 = .base (.BEQ .x7 .x8 (32#13)))
        (by rw [hx7_100, hx8_100, hsame])
        (by decide : pcAt 100 + signExtend13 (32#13) = pcAt 108)
      have hf1 : fwd1 = fwdBytes := by
        change fwdBytes ++ (if mL = mR then [] else _) = fwdBytes; rw [if_pos hsame, List.append_nil]
      have ht1 : tails1 = tails := by
        change tails ++ (if mL = mR then [] else _) = tails; rw [if_pos hsame, List.append_nil]
      rw [hf1, ht1]
      refine ⟨1, s100.setPC (pcAt 108), h100, by omega, rfl,
        by rw [MachineState.getReg_setPC, hpres100 .x2 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx2,
        by rw [MachineState.getReg_setPC, hpres100 .x9 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx9,
        by rw [MachineState.getReg_setPC, hpres100 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx18,
        by rw [MachineState.getReg_setPC, hpres100 .x19 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx19,
        by rw [MachineState.getReg_setPC, hpres100 .x20 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx20,
        by rw [MachineState.getReg_setPC, hpres100 .x21 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx21,
        by rw [MachineState.getReg_setPC, hpres100 .x22 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx22,
        by rw [MachineState.getReg_setPC, hpres100 .x23 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx23,
        by rw [MachineState.getReg_setPC, hpres100 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24,
        by rw [MachineState.getReg_setPC, hpres100 .x26 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx26,
        by rw [MachineState.getReg_setPC, hpres100 .x29 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx29,
        by rw [MachineState.getReg_setPC, hpres100 .x30 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx30,
        by rw [Finset.sum_range_succ]; omega, by rw [Finset.sum_range_succ]; omega,
        hro100, hw100.of_eq, ht100.of_eq, hcur100, hnext100⟩
    · have hcpf : capPairFrontier positions l q = 1 := bool_bne_one_of_ne hsame
      have hlen_bdF : fwdBytes.length + 29 ≤ (positions.card + 7) / 8 + 479 * positions.card +
          29 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
                (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ, hcpf]; omega
      have hlen_bdT : tails.length + 1 ≤ 16 * positions.card +
          ((∑ k ∈ Finset.range step, levelFrontierCount positions (16 + k)) +
           (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        rw [Finset.sum_range_succ, hcpf]; omega
      have h100 := step_BEQ_not_taken (by omega) (rfl : s100.pc = pcAt 100)
        (rfl : openingInstr 100 = .base (.BEQ .x7 .x8 (32#13)))
        (by rw [hx7_100, hx8_100]; exact bool_word_ne_of_ne hsame)
      let s101 := s100.setPC (pcAt 101)
      have h101 := step_SLLI (by omega) (rfl : s101.pc = pcAt 101) (rfl : openingInstr 101 = .base (.SLLI .x6 .x24 (6#6)))
      let s102 := (s101.setReg .x6 (BitVec.ofNat 64 (64 * q))).setPC (pcAt 102)
      have h101' : OpenRuns s101 1 1 s102 := by
        have hr24 : s101.getReg .x24 = BitVec.ofNat 64 q := by
          simp only [s101, MachineState.getReg_setPC]
          rw [hpres100 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24
        have hv : s101.getReg .x24 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * q) := by
          rw [hr24]; change BitVec.ofNat 64 q <<< 6 = _; rw [bv64_shl]; congr 1; omega
        simpa only [hv, s102] using h101
      have h102 := step_SLLI (by omega) (rfl : s102.pc = pcAt 102) (rfl : openingInstr 102 = .base (.SLLI .x11 .x24 (5#6)))
      let s103 := (s102.setReg .x11 (BitVec.ofNat 64 (32 * q))).setPC (pcAt 103)
      have h102' : OpenRuns s102 1 1 s103 := by
        have hr24 : s102.getReg .x24 = BitVec.ofNat 64 q := by
          simp only [s102, s101, MachineState.getReg_setPC, getReg_setReg_ne' .x6 .x24 (by decide)]
          rw [hpres100 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24
        have hv : s102.getReg .x24 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (32 * q) := by
          rw [hr24]; change BitVec.ofNat 64 q <<< 5 = _; rw [bv64_shl]; congr 1; omega
        simpa only [hv, s103] using h102
      have h103 := step_ADD (by omega) (rfl : s103.pc = pcAt 103) (rfl : openingInstr 103 = .base (.ADD .x10 .x6 .x11))
      let s104 := (s103.setReg .x10 (BitVec.ofNat 64 (96 * q))).setPC (pcAt 104)
      have h103' : OpenRuns s103 1 1 s104 := by
        have hv : s103.getReg .x6 + s103.getReg .x11 = BitVec.ofNat 64 (96 * q) := by
          change BitVec.ofNat 64 (64 * q) + BitVec.ofNat 64 (32 * q) = _; rw [bv64_ofNat_add]; congr 1; omega
        simpa only [hv, s104] using h103
      have h104 := step_ADD (by omega) (rfl : s104.pc = pcAt 104) (rfl : openingInstr 104 = .base (.ADD .x10 .x18 .x10))
      let s105 := (s104.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q))).setPC (pcAt 105)
      have h104' : OpenRuns s104 1 1 s105 := by
        have hr18 : s104.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l) := by
          simp only [s104, s103, s102, s101, MachineState.getReg_setPC,
            getReg_setReg_ne' .x10 .x18 (by decide), getReg_setReg_ne' .x11 .x18 (by decide),
            getReg_setReg_ne' .x6 .x18 (by decide)]
          rw [hpres100 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx18
        rw [hr18] at h104
        simpa only [show s104.getReg .x10 = BitVec.ofNat 64 (96 * q) from rfl, bv64_ofNat_add, s105] using h104
      have hmid : OpenRuns s100 5 5 s105 := (((h100.trans h101').trans h102').trans h103').trans h104'
      have hr7_105 : s105.getReg .x7 = if mL then 1#64 else 0#64 := by
        simp only [s105, s104, s103, s102, s101, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 .x7 (by decide), getReg_setReg_ne' .x11 .x7 (by decide),
          getReg_setReg_ne' .x6 .x7 (by decide)]; exact hx7_100
      have hpres105 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x11 → s105.getReg r = s100.getReg r :=
        fun r h6 _ _ h10 h11 => by
          simp only [s105, s104, s103, s102, s101, MachineState.getReg_setPC,
            getReg_setReg_ne' .x10 r (Ne.symm h10), getReg_setReg_ne' .x11 r (Ne.symm h11),
            getReg_setReg_ne' .x6 r (Ne.symm h6)]
      have hto107 : ∃ n107 s107 childIdx, OpenRuns s105 n107 n107 s107 ∧ n107 ≤ 2 ∧
          childIdx = (if !mL then 2 * q else 2 * q + 1) ∧ childIdx < levelSize l ∧
          s107.pc = pcAt 107 ∧
          s107.getReg .x10 = BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l childIdx)) ∧
          (∀ r, r ≠ .x10 → s107.getReg r = s105.getReg r) ∧ s107.mem = s105.mem := by
        by_cases hmL : mL = true
        · have h105 := step_BEQ_not_taken (by omega) (rfl : s105.pc = pcAt 105)
            (rfl : openingInstr 105 = .base (.BEQ .x7 .x0 (8#13)))
            (by rw [hr7_105, hmL]; change (1#64 : Word) ≠ 0#64; decide)
          let s106 := s105.setPC (pcAt 106)
          have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
          have h106 := step_ADDI (by omega) (rfl : s106.pc = pcAt 106) (rfl : openingInstr 106 = .base (.ADDI .x10 .x10 (32#12)))
          have hno : levelBase l + nodeOffset l (2 * q + 1) = levelBase l + 96 * q + 32 := by
            unfold nodeOffset; rw [gapOffset_odd]; omega
          let s107 := (s106.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l (2 * q + 1))))).setPC (pcAt 107)
          have h106' : OpenRuns s106 1 1 s107 := by
            have hv : s106.getReg .x10 + signExtend12 (32#12) =
                BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l (2 * q + 1))) := by
              change BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) + _ = _
              rw [hse32, bv64_ofNat_add]; congr 1; omega
            simpa only [hv, s107] using h106
          refine ⟨2, s107, 2 * q + 1, h105.trans h106', by omega, by rw [hmL]; rfl, by omega, rfl, rfl,
            fun r hr => by simp only [s107, s106, MachineState.getReg_setPC, getReg_setReg_ne' .x10 r (Ne.symm hr)], rfl⟩
        · have hmLf : mL = false := Bool.eq_false_iff.mpr hmL
          have h105 := step_BEQ_taken (by omega) (rfl : s105.pc = pcAt 105)
            (rfl : openingInstr 105 = .base (.BEQ .x7 .x0 (8#13)))
            (by rw [hr7_105, hmLf]; rfl) (by decide : pcAt 105 + signExtend13 (8#13) = pcAt 107)
          have hno : levelBase l + nodeOffset l (2 * q) = levelBase l + 96 * q := by
            unfold nodeOffset; rw [gapOffset_even]
          refine ⟨1, s105.setPC (pcAt 107), 2 * q, h105, by omega, by rw [hmLf]; rfl, by omega, rfl,
            by change BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) = _; rw [hno, Nat.add_assoc],
            fun _ _ => rfl, rfl⟩
      obtain ⟨n107, s107, childIdx, hr107, hn107, hchildEq, hchildLt, hpc107, hx10_107, hreg107, hmem107⟩ := hto107
      have hro107 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s107 := by
        intro a ha; change s107.mem a = _; rw [hmem107]; exact hro100 a ha
      have hw107 : WriterState s107 fwdBytes :=
        ⟨by rw [hreg107 .x25 (by decide), hpres105 .x25 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw100.rx25,
         by rw [hreg107 .x13 (by decide), hpres105 .x13 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw100.rx13,
         by rw [hreg107 .x14 (by decide), hpres105 .x14 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw100.rx14,
         fun j hj => by rw [hreg107 .x12 (by decide), hpres105 .x12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw100.wbufLo j hj,
         fun j h1 h2 => by rw [hreg107 .x12 (by decide), hpres105 .x12 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hw100.wbufHi j h1 h2,
         fun j hj => by change extractByte (s107.mem _) _ = _; rw [hmem107]; exact hw100.memDwords j hj⟩
      have ht107 : TailState s107 tails :=
        ⟨by rw [hreg107 .x31 (by decide), hpres105 .x31 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht100.rx31,
         by rw [hreg107 .x15 (by decide), hpres105 .x15 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht100.rx15,
         by rw [hreg107 .x16 (by decide), hpres105 .x16 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht100.rx16,
         by rw [hreg107 .x17 (by decide), hpres105 .x17 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ht100.rx17,
         fun j hj => by change extractByte (s107.mem _) _ = _; rw [hmem107]; exact ht100.memTail j hj⟩
      obtain ⟨stC, s108, hrcopy, hstC, hpc108, hreg108, hro108, hw108, ht108, hcap108⟩ :=
        openRuns_call_emit29_t6 (callIdx := 107) (l := l) (nodeIdx := childIdx) (jOff := 204#21)
          (by omega) (by omega) hchildLt rfl (by decide) hpc107 hx10_107 (by omega) (by omega) hro107 hw107 ht107
      have hf1 : fwd1 = fwdBytes ++ bitsToBytes (tdNode trapdoor l childIdx) 29 := by
        change fwdBytes ++ (if mL = mR then [] else if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) 29
          else bitsToBytes (tdNode trapdoor l (2 * q + 1)) 29) = _
        simp only [hsame, ite_false]; rw [hchildEq]
        by_cases hnot : (!mL) = true <;> simp [hnot]
      have ht1 : tails1 = tails ++ [tail6 (tdNode trapdoor l childIdx)] := by
        change tails ++ (if mL = mR then [] else if !mL then [tail6 (tdNode trapdoor l (2 * q))]
          else [tail6 (tdNode trapdoor l (2 * q + 1))]) = _
        simp only [hsame, ite_false]; rw [hchildEq]
        by_cases hnot : (!mL) = true <;> simp [hnot]
      rw [hf1, ht1]
      have hpres108 : ∀ r, r = .x2 ∨ r = .x9 ∨ r = .x18 ∨ r = .x19 ∨ r = .x20 ∨ r = .x21 ∨
          r = .x22 ∨ r = .x23 ∨ r = .x24 ∨ r = .x26 ∨ r = .x29 ∨ r = .x30 →
          s108.getReg r = s.getReg r := fun r hr => by
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (
          rw [hreg108 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg107 _ (by decide),
            hpres105 _ (by decide) (by decide) (by decide) (by decide) (by decide),
            hpres100 _ (by decide) (by decide) (by decide) (by decide)])
      refine ⟨5 + n107 + stC, s108, (hmid.trans hr107).trans hrcopy, by rw [hcpf, hstC]; omega, hpc108,
        by rw [hpres108 .x2 (by simp)]; exact inv.rx2,
        by rw [hpres108 .x9 (by simp)]; exact inv.rx9,
        by rw [hpres108 .x18 (by simp)]; exact inv.rx18,
        by rw [hpres108 .x19 (by simp)]; exact inv.rx19,
        by rw [hpres108 .x20 (by simp)]; exact inv.rx20,
        by rw [hpres108 .x21 (by simp)]; exact inv.rx21,
        by rw [hpres108 .x22 (by simp)]; exact inv.rx22,
        by rw [hpres108 .x23 (by simp)]; exact inv.rx23,
        by rw [hpres108 .x24 (by simp)]; exact inv.rx24,
        by rw [hpres108 .x26 (by simp)]; exact inv.rx26,
        by rw [hpres108 .x29 (by simp)]; exact inv.rx29,
        by rw [hpres108 .x30 (by simp)]; exact inv.rx30,
        by simp only [List.length_append, bitsToBytes_length]; exact hlen_bdF,
        by simp only [List.length_append, List.length_singleton]; exact hlen_bdT,
        hro108, hw108, ht108,
        fun idx hidx => by rw [hcap108 (4096 + capMarkOff l + idx) (by omega)]; change extractByte (s107.mem _) _ = _; rw [hmem107]; exact hcur100 idx hidx,
        fun j hj => by rw [hcap108 (4096 + capMarkOff (l + 1) + j) (by omega)]; change extractByte (s107.mem _) _ = _; rw [hmem107]; exact hnext100 j hj⟩
  obtain ⟨n108, s108, hr108, hn108, hpc108, hx2, hx9, hx18, hx19, hx20, hx21, hx22, hx23,
      hx24, hx26, hx29, hx30, hlenF1, hlenT1, hro108, hw108, ht108, hcur108, hnext108⟩ := hto108
  have h108 := step_ADDI (by omega) hpc108 (rfl : openingInstr 108 = .base (.ADDI .x24 .x24 (1#12)))
  let s109 := (s108.setReg .x24 (BitVec.ofNat 64 (q + 1))).setPC (pcAt 109)
  have h108' : OpenRuns s108 1 1 s109 := by rw [hx24, hse1, bv64_ofNat_add] at h108; exact h108
  have hmkInv : ∀ pc, CapPairInv trapdoor positions step (q + 1) fwd1 tails1 (s109.setPC pc) := fun pc =>
    ⟨hx2, hx9, hx18, hx19, hx20, hx21, hx22, hx23, rfl, hx26, hx29, hx30,
     hlenF1, hlenT1, hro108, hw108.of_eq, ht108.of_eq, hcur108, hnext108⟩
  by_cases hmore : q + 1 < levelSize l / 2
  · have h109 := step_BNE_taken (by omega) (rfl : s109.pc = pcAt 109)
      (rfl : openingInstr 109 = .base (.BNE .x24 .x23 (8128#13)))
      (by change BitVec.ofNat 64 (q + 1) ≠ s108.getReg .x23; rw [hx23]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 109 + signExtend13 (8128#13) = pcAt 93)
    exact ⟨7 + n108 + 1 + 1, s109.setPC (pcAt 93), ((hpre.trans hr108).trans h108').trans h109,
      by omega, by simp only [hmore, ite_true]; rfl, hmkInv (pcAt 93)⟩
  · have hdone : q + 1 = levelSize l / 2 := by omega
    have h109 := step_BNE_not_taken (by omega) (rfl : s109.pc = pcAt 109)
      (rfl : openingInstr 109 = .base (.BNE .x24 .x23 (8128#13)))
      (by change BitVec.ofNat 64 (q + 1) = s108.getReg .x23; rw [hx23, hdone])
    exact ⟨7 + n108 + 1 + 1, s109.setPC (pcAt 110), ((hpre.trans hr108).trans h108').trans h109,
      by omega, by simp only [hmore, ite_false]; rfl, hmkInv (pcAt 110)⟩

private theorem openRuns_cap_lvl_iter {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {step : Nat} {fwdBytes : List Byte} {tails : List (BitVec 6)}
    {s : MachineState}
    (hstep : step < 8) (hpc : s.pc = pcAt 84)
    (inv : CapLvlInv trapdoor positions step fwdBytes tails s) :
    let l := 16 + step
    let fwd1 := fwdBytes ++ capLevelFrontierFwd (tdNode trapdoor) positions l
    let tails1 := tails ++ capLevelFrontierTails (tdNode trapdoor) positions l
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 9 + 10 * (levelSize l / 2) + 2 + 28 * levelFrontierCount positions l +
        5 * (fwd1.length / 8 - fwdBytes.length / 8) + 4 * (tailAccLen tails1 - tailAccLen tails) ∧
      s1.pc = (if step + 1 < 8 then pcAt 84 else pcAt 112) ∧
      CapLvlInv trapdoor positions (step + 1) fwd1 tails1 s1 := by
  intro l fwd1 tails1
  have hls_ge2 := levelSize_ge_two l (by omega)
  have hls_le := levelSize_le_max l (by omega)
  have hls1_eq := levelSize_step l (by omega)
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have hse16 : signExtend12 (16#12) = BitVec.ofNat 64 16 := by decide
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have hse48 : signExtend12 (48#12) = BitVec.ofNat 64 48 := by decide
  -- Header: 84..92 (9 steps)
  have haddr84 : s.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    rw [inv.rx29, hse0, bv64_ofNat_add, Nat.add_zero]
  have h84 := step_LD (by omega) hpc (rfl : openingInstr 84 = .base (.LD .x18 .x29 (0#12)))
    (by rw [haddr84]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s85 := (s.setReg .x18 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 85)
  have h84' : OpenRuns s 1 1 s85 := by
    have hm := readOnly_getMem_data_base inv.ro l (by omega); simpa only [haddr84, hm, s85] using h84
  have h85 := step_ADD (by omega) (rfl : s85.pc = pcAt 85) (rfl : openingInstr 85 = .base (.ADD .x18 .x9 .x18))
  let s86 := (s85.setReg .x18 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 86)
  have h85' : OpenRuns s85 1 1 s86 := by
    have hr9 : s85.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
    rw [hr9] at h85
    simpa only [show s85.getReg .x18 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s86] using h85
  have haddr86 : s86.getReg .x29 + signExtend12 (8#12) = BitVec.ofNat 64 (68719475936 + 32 * l + 8) := by
    have hr29 : s86.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := inv.rx29
    rw [hr29, hse8, bv64_ofNat_add]
  have h86 := step_LD (by omega) (rfl : s86.pc = pcAt 86) (rfl : openingInstr 86 = .base (.LD .x19 .x29 (8#12)))
    (by rw [haddr86]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s87 := (s86.setReg .x19 (BitVec.ofNat 64 (levelSize l))).setPC (pcAt 87)
  have h86' : OpenRuns s86 1 1 s87 := by
    have hm : s86.getMem (BitVec.ofNat 64 (68719475936 + 32 * l + 8)) = BitVec.ofNat 64 (levelSize l) :=
      readOnly_getMem_data_size inv.ro l (by omega)
    simpa only [haddr86, hm, s87] using h86
  have haddr87 : s87.getReg .x29 + signExtend12 (16#12) = BitVec.ofNat 64 (68719475936 + 32 * l + 16) := by
    have hr29 : s87.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := inv.rx29
    rw [hr29, hse16, bv64_ofNat_add]
  have h87 := step_LD (by omega) (rfl : s87.pc = pcAt 87) (rfl : openingInstr 87 = .base (.LD .x20 .x29 (16#12)))
    (by rw [haddr87]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s88 := (s87.setReg .x20 (BitVec.ofNat 64 (capMarkOff l))).setPC (pcAt 88)
  have h87' : OpenRuns s87 1 1 s88 := by
    have hm : s87.getMem (BitVec.ofNat 64 (68719475936 + 32 * l + 16)) = BitVec.ofNat 64 (capMarkOff l) :=
      readOnly_getMem_data_markOff inv.ro l (by omega)
    simpa only [haddr87, hm, s88] using h87
  have h88 := step_ADD (by omega) (rfl : s88.pc = pcAt 88) (rfl : openingInstr 88 = .base (.ADD .x20 .x21 .x20))
  let s89 := (s88.setReg .x20 (BitVec.ofNat 64 (4096 + capMarkOff l))).setPC (pcAt 89)
  have h88' : OpenRuns s88 1 1 s89 := by
    have hr21 : s88.getReg .x21 = BitVec.ofNat 64 4096 := inv.rx21
    rw [hr21] at h88
    simpa only [show s88.getReg .x20 = BitVec.ofNat 64 (capMarkOff l) from rfl, bv64_ofNat_add, s89] using h88
  have haddr89 : s89.getReg .x29 + signExtend12 (48#12) = BitVec.ofNat 64 (68719475936 + 32 * (l + 1) + 16) := by
    have hr29 : s89.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := inv.rx29
    rw [hr29, hse48, bv64_ofNat_add]; congr 1
  have h89 := step_LD (by omega) (rfl : s89.pc = pcAt 89) (rfl : openingInstr 89 = .base (.LD .x22 .x29 (48#12)))
    (by rw [haddr89]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s90 := (s89.setReg .x22 (BitVec.ofNat 64 (capMarkOff (l + 1)))).setPC (pcAt 90)
  have h89' : OpenRuns s89 1 1 s90 := by
    have hm : s89.getMem (BitVec.ofNat 64 (68719475936 + 32 * (l + 1) + 16)) = BitVec.ofNat 64 (capMarkOff (l + 1)) :=
      readOnly_getMem_data_markOff inv.ro (l + 1) (by omega)
    simpa only [haddr89, hm, s90] using h89
  have h90 := step_ADD (by omega) (rfl : s90.pc = pcAt 90) (rfl : openingInstr 90 = .base (.ADD .x22 .x21 .x22))
  let s91 := (s90.setReg .x22 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1)))).setPC (pcAt 91)
  have h90' : OpenRuns s90 1 1 s91 := by
    have hr21 : s90.getReg .x21 = BitVec.ofNat 64 4096 := inv.rx21
    rw [hr21] at h90
    simpa only [show s90.getReg .x22 = BitVec.ofNat 64 (capMarkOff (l + 1)) from rfl, bv64_ofNat_add, s91] using h90
  have h91 := step_SRLI (by omega) (rfl : s91.pc = pcAt 91) (rfl : openingInstr 91 = .base (.SRLI .x23 .x19 (1#6)))
  let s92 := (s91.setReg .x23 (BitVec.ofNat 64 (levelSize l / 2))).setPC (pcAt 92)
  have h91' : OpenRuns s91 1 1 s92 := by
    have hv : s91.getReg .x19 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (levelSize l / 2) := by
      change BitVec.ofNat 64 (levelSize l) >>> 1 = _; rw [bv64_ushr _ 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s92] using h91
  have h92 := step_ADDI (by omega) (rfl : s92.pc = pcAt 92) (rfl : openingInstr 92 = .base (.ADDI .x24 .x0 (0#12)))
  let s93 := (s92.setReg .x24 (BitVec.ofNat 64 0)).setPC (pcAt 93)
  have h92' : OpenRuns s92 1 1 s93 := by
    have hv : s92.getReg .x0 + signExtend12 (0#12) = BitVec.ofNat 64 0 := by
      change (0#64 : Word) + signExtend12 (0#12) = BitVec.ofNat 64 0; decide
    simpa only [hv, s93] using h92
  have hhdr : OpenRuns s 9 9 s93 :=
    (((((((h84'.trans h85').trans h86').trans h87').trans h88').trans h89').trans h90').trans h91').trans h92'
  have hpairInv0 : CapPairInv trapdoor positions step 0 fwdBytes tails s93 :=
    ⟨inv.rx2, inv.rx9, rfl, rfl, rfl, inv.rx21, rfl, rfl, rfl, inv.rx26, inv.rx29, inv.rx30,
     by simpa using inv.boundFwd, by simpa using inv.boundTails,
     inv.ro, inv.writer.of_eq, inv.tail.of_eq, inv.capMarks, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  -- Pair loop: q = 0 .. levelSize l / 2
  have hpairLoop : ∀ q ≤ levelSize l / 2,
      let curF := fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l)
      let curT := tails ++ (List.range q).flatMap (capPairTails trapdoor positions l)
      ∃ steps sq, OpenRuns s93 steps steps sq ∧
        steps ≤ 10 * q + 28 * (∑ j ∈ Finset.range q, capPairFrontier positions l j) +
          5 * (curF.length / 8 - fwdBytes.length / 8) + 4 * (tailAccLen curT - tailAccLen tails) ∧
        sq.pc = (if q < levelSize l / 2 then pcAt 93 else pcAt 110) ∧
        CapPairInv trapdoor positions step q curF curT sq := by
    intro q hq
    induction q with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero,
        Finset.sum_range_zero, Nat.add_zero, Nat.sub_self]
      exact ⟨0, s93, OpenRuns.refl s93, Nat.le_refl 0, by simp only [show 0 < levelSize l / 2 by omega, ite_true]; rfl, hpairInv0⟩
    | succ q ih =>
      obtain ⟨st, sq, hrq, hstq, hpcq, invq⟩ := ih (by omega)
      have hpcq' : sq.pc = pcAt 93 := by simpa only [show q < levelSize l / 2 by omega, ite_true] using hpcq
      obtain ⟨st1, sq1, hr1, hst1, hpc1, inv1⟩ :=
        openRuns_cap_pair_step hstep (show q < levelSize (16 + step) / 2 from by change q < levelSize l / 2; omega) hpcq' invq
      have happF : fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l) ++
            capPairFwd trapdoor positions l q =
          fwdBytes ++ (List.range (q + 1)).flatMap (capPairFwd trapdoor positions l) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      have happT : tails ++ (List.range q).flatMap (capPairTails trapdoor positions l) ++
            capPairTails trapdoor positions l q =
          tails ++ (List.range (q + 1)).flatMap (capPairTails trapdoor positions l) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      have hmonoF1 : fwdBytes.length / 8 ≤ (fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l)).length / 8 :=
        Nat.div_le_div_right (by simp)
      have hmonoF2 : (fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l)).length / 8 ≤
          (fwdBytes ++ (List.range (q + 1)).flatMap (capPairFwd trapdoor positions l)).length / 8 := by
        rw [← happF]; exact Nat.div_le_div_right (by simp)
      have hmonoT1 : tailAccLen tails ≤ tailAccLen (tails ++ (List.range q).flatMap (capPairTails trapdoor positions l)) :=
        tailAccLen_mono_append _ _
      have hmonoT2 : tailAccLen (tails ++ (List.range q).flatMap (capPairTails trapdoor positions l)) ≤
          tailAccLen (tails ++ (List.range (q + 1)).flatMap (capPairTails trapdoor positions l)) := by
        rw [← happT]; exact tailAccLen_mono_append _ _
      have hst1' : st1 ≤ 10 + 28 * capPairFrontier positions l q +
          5 * ((fwdBytes ++ (List.range (q + 1)).flatMap (capPairFwd trapdoor positions l)).length / 8 -
               (fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l)).length / 8) +
          4 * (tailAccLen (tails ++ (List.range (q + 1)).flatMap (capPairTails trapdoor positions l)) -
               tailAccLen (tails ++ (List.range q).flatMap (capPairTails trapdoor positions l))) := by
        rw [← happF, ← happT]; exact hst1
      have inv1' : CapPairInv trapdoor positions step (q + 1)
          (fwdBytes ++ (List.range q).flatMap (capPairFwd trapdoor positions l) ++ capPairFwd trapdoor positions l q)
          (tails ++ (List.range q).flatMap (capPairTails trapdoor positions l) ++ capPairTails trapdoor positions l q) sq1 := inv1
      rw [happF, happT] at inv1'
      refine ⟨st + st1, sq1, hrq.trans hr1, ?_, hpc1, inv1'⟩
      rw [Finset.sum_range_succ]; omega
  obtain ⟨stPairs, s110, hrPairs, hstPairs, hpc110, inv110⟩ := hpairLoop (levelSize l / 2) (Nat.le_refl _)
  have hpc110' : s110.pc = pcAt 110 := by simpa only [Nat.lt_irrefl, ite_false] using hpc110
  rw [sum_capPairFrontier_eq] at hstPairs
  have hfwd1_eq : fwdBytes ++ (List.range (levelSize l / 2)).flatMap (capPairFwd trapdoor positions l) = fwd1 := rfl
  have htails1_eq : tails ++ (List.range (levelSize l / 2)).flatMap (capPairTails trapdoor positions l) = tails1 := rfl
  rw [hfwd1_eq, htails1_eq] at hstPairs inv110
  have hboundF110 : fwd1.length ≤ (positions.card + 7) / 8 + 479 * positions.card +
      29 * (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (16 + k)) := by
    have h1 := inv110.boundFwd; rw [sum_capPairFrontier_eq] at h1; rw [Finset.sum_range_succ]; exact h1
  have hboundT110 : tails1.length ≤ 16 * positions.card +
      (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (16 + k)) := by
    have h1 := inv110.boundTails; rw [sum_capPairFrontier_eq] at h1; rw [Finset.sum_range_succ]; exact h1
  -- Latch: 110..111 (NO odd-promotion check!)
  have h110 := step_ADDI (by omega) hpc110' (rfl : openingInstr 110 = .base (.ADDI .x29 .x29 (32#12)))
  let s111 := (s110.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * (16 + (step + 1))))).setPC (pcAt 111)
  have h110' : OpenRuns s110 1 1 s111 := by
    have hv : s110.getReg .x29 + signExtend12 (32#12) = BitVec.ofNat 64 (68719475936 + 32 * (16 + (step + 1))) := by
      rw [inv110.rx29, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s111] using h110
  have hcm111 : CapLevelMarks s111 positions (16 + (step + 1)) := by
    intro idx hidx
    have hidx' : idx < levelSize l / 2 := by rw [← hls1_eq]; exact hidx
    exact inv110.nextMarks idx hidx'
  have hmkInv : ∀ pc, CapLvlInv trapdoor positions (step + 1) fwd1 tails1 (s111.setPC pc) := fun pc =>
    ⟨inv110.rx2, inv110.rx9, inv110.rx21, inv110.rx26, rfl, inv110.rx30,
     hboundF110, hboundT110, inv110.ro, inv110.writer.of_eq, inv110.tail.of_eq, hcm111⟩
  by_cases hmore : step + 1 < 8
  · have h111 := step_BNE_taken (by omega) (rfl : s111.pc = pcAt 111)
      (rfl : openingInstr 111 = .base (.BNE .x29 .x30 (8084#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (16 + (step + 1))) ≠ s110.getReg .x30
          rw [inv110.rx30]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 111 + signExtend13 (8084#13) = pcAt 84)
    exact ⟨9 + stPairs + 1 + 1, s111.setPC (pcAt 84), ((hhdr.trans hrPairs).trans h110').trans h111,
      by omega, by simp only [hmore, ite_true]; rfl, hmkInv (pcAt 84)⟩
  · have hdone : 16 + (step + 1) = 24 := by omega
    have h111 := step_BNE_not_taken (by omega) (rfl : s111.pc = pcAt 111)
      (rfl : openingInstr 111 = .base (.BNE .x29 .x30 (8084#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (16 + (step + 1))) = s110.getReg .x30
          rw [inv110.rx30, hdone])
    exact ⟨9 + stPairs + 1 + 1, s111.setPC (pcAt 112), ((hhdr.trans hrPairs).trans h110').trans h111,
      by omega, by simp only [hmore, ite_false]; rfl, hmkInv (pcAt 112)⟩

private theorem cap_const_cycles_sum :
    (∑ step ∈ Finset.range 8, (9 + 10 * (levelSize (16 + step) / 2) + 2)) = 2638 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]; decide

private theorem openRuns_cap_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {recFwd : List Byte} {recTails : List (BitVec 6)} {s82 : MachineState}
    (hpc : s82.pc = pcAt 82)
    (hx2 : s82.getReg .x2 = BitVec.ofNat 64 68719475936)
    (hx9 : s82.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx21 : s82.getReg .x21 = BitVec.ofNat 64 4096)
    (hx26 : s82.getReg .x26 = BitVec.ofNat 64 10603204576)
    (hbdF : recFwd.length ≤ (positions.card + 7) / 8 + 479 * positions.card)
    (hbdT : recTails.length ≤ 16 * positions.card)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s82)
    (hw : WriterState s82 recFwd)
    (ht : TailState s82 recTails)
    (hcap16 : CapLevelMarks s82 positions 16) :
    let allFwd := recFwd ++ capFrontierFwd (tdNode trapdoor) positions
    let allTails := recTails ++ capFrontierTails (tdNode trapdoor) positions
    ∃ steps s112, OpenRuns s82 steps steps s112 ∧
      steps ≤ 6224 + 5 * (allFwd.length / 8 - recFwd.length / 8) +
        4 * (tailAccLen allTails - tailAccLen recTails) ∧
      s112.pc = pcAt 112 ∧
      s112.getReg .x26 = BitVec.ofNat 64 10603204576 ∧
      WriterState s112 allFwd ∧
      TailState s112 allTails := by
  intro allFwd allTails
  have hse512 : signExtend12 (512#12) = BitVec.ofNat 64 512 := by decide
  have hse768 : signExtend12 (768#12) = BitVec.ofNat 64 768 := by decide
  have h82 := step_ADDI (by omega) hpc (rfl : openingInstr 82 = .base (.ADDI .x29 .x2 (512#12)))
  let s83 := (s82.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * 16))).setPC (pcAt 83)
  have h82' : OpenRuns s82 1 1 s83 := by rw [hx2, hse512, bv64_ofNat_add] at h82; exact h82
  have h83 := step_ADDI (by omega) (rfl : s83.pc = pcAt 83) (rfl : openingInstr 83 = .base (.ADDI .x30 .x2 (768#12)))
  let s84 := (s83.setReg .x30 (BitVec.ofNat 64 (68719475936 + 32 * 24))).setPC (pcAt 84)
  have h83' : OpenRuns s83 1 1 s84 := by
    have hr2 : s83.getReg .x2 = BitVec.ofNat 64 68719475936 := hx2
    rw [hr2, hse768, bv64_ofNat_add] at h83; exact h83
  have hinv0 : CapLvlInv trapdoor positions 0 recFwd recTails s84 :=
    ⟨hx2, hx9, hx21, hx26, rfl, rfl, by simpa using hbdF, by simpa using hbdT, hro, hw.of_eq, ht.of_eq, hcap16⟩
  have hloop : ∀ k ≤ 8,
      let curF := recFwd ++ (List.range k).flatMap (fun step =>
        capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))
      let curT := recTails ++ (List.range k).flatMap (fun step =>
        capLevelFrontierTails (tdNode trapdoor) positions (16 + step))
      ∃ steps sk, OpenRuns s84 steps steps sk ∧
        steps ≤ (∑ step ∈ Finset.range k, (9 + 10 * (levelSize (16 + step) / 2) + 2)) +
          28 * (∑ step ∈ Finset.range k, levelFrontierCount positions (16 + step)) +
          5 * (curF.length / 8 - recFwd.length / 8) + 4 * (tailAccLen curT - tailAccLen recTails) ∧
        sk.pc = (if k < 8 then pcAt 84 else pcAt 112) ∧
        CapLvlInv trapdoor positions k curF curT sk := by
    intro k hk
    induction k with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Finset.sum_range_zero,
        Nat.mul_zero, Nat.add_zero, Nat.sub_self]
      exact ⟨0, s84, OpenRuns.refl s84, Nat.le_refl 0, by simp only [show (0 : Nat) < 8 by decide, ite_true]; rfl, hinv0⟩
    | succ k ih =>
      obtain ⟨st, sk, hrk, hstk, hpck, invk⟩ := ih (by omega)
      have hpck' : sk.pc = pcAt 84 := by simpa only [show k < 8 by omega, ite_true] using hpck
      obtain ⟨st1, sk1, hr1, hst1, hpc1, inv1⟩ := openRuns_cap_lvl_iter (by omega) hpck' invk
      have happF : recFwd ++ (List.range k).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step)) ++
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + k) =
          recFwd ++ (List.range (k + 1)).flatMap (fun step =>
            capLevelFrontierFwd (tdNode trapdoor) positions (16 + step)) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      have happT : recTails ++ (List.range k).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (16 + step)) ++
            capLevelFrontierTails (tdNode trapdoor) positions (16 + k) =
          recTails ++ (List.range (k + 1)).flatMap (fun step =>
            capLevelFrontierTails (tdNode trapdoor) positions (16 + step)) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      have hmonoF1 : recFwd.length / 8 ≤ (recFwd ++ (List.range k).flatMap (fun step =>
          capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))).length / 8 :=
        Nat.div_le_div_right (by simp)
      have hmonoF2 : (recFwd ++ (List.range k).flatMap (fun step =>
          capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))).length / 8 ≤
          (recFwd ++ (List.range (k + 1)).flatMap (fun step =>
          capLevelFrontierFwd (tdNode trapdoor) positions (16 + step))).length / 8 := by
        rw [← happF]; exact Nat.div_le_div_right (by simp)
      have hmonoT1 : tailAccLen recTails ≤ tailAccLen (recTails ++ (List.range k).flatMap (fun step =>
          capLevelFrontierTails (tdNode trapdoor) positions (16 + step))) :=
        tailAccLen_mono_append _ _
      have hmonoT2 : tailAccLen (recTails ++ (List.range k).flatMap (fun step =>
          capLevelFrontierTails (tdNode trapdoor) positions (16 + step))) ≤
          tailAccLen (recTails ++ (List.range (k + 1)).flatMap (fun step =>
          capLevelFrontierTails (tdNode trapdoor) positions (16 + step))) := by
        rw [← happT]; exact tailAccLen_mono_append _ _
      rw [happF, happT] at hst1 inv1
      refine ⟨st + st1, sk1, hrk.trans hr1, ?_, hpc1, inv1⟩
      rw [Finset.sum_range_succ, Finset.sum_range_succ]; omega
  obtain ⟨stCap, s112, hrCap, hstCap, hpc112, inv112⟩ := hloop 8 (Nat.le_refl 8)
  have hpc112' : s112.pc = pcAt 112 := by simpa only [Nat.lt_irrefl, ite_false] using hpc112
  have hconst := cap_const_cycles_sum
  have hcap128 := cap_frontier_le_128 positions
  have hfront_eq : (∑ step ∈ Finset.range 8, levelFrontierCount positions (16 + step)) =
      capFrontierCount positions := rfl
  rw [hconst, hfront_eq] at hstCap
  have hallF_eq : recFwd ++ (List.range 8).flatMap (fun step =>
      capLevelFrontierFwd (tdNode trapdoor) positions (16 + step)) = allFwd := rfl
  have hallT_eq : recTails ++ (List.range 8).flatMap (fun step =>
      capLevelFrontierTails (tdNode trapdoor) positions (16 + step)) = allTails := rfl
  rw [hallF_eq, hallT_eq] at hstCap inv112
  exact ⟨2 + stCap, s112, (h82'.trans h83').trans hrCap, by omega, hpc112',
    inv112.rx26, inv112.writer, inv112.tail⟩

/-! ### 10. Top-Level Deterministic Opening Specification -/

private theorem submission_run_opening (s : Submission)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) :
    s.run .opening (trapdoor, positions) =
      execute (s.image .opening) (s.steps .opening)
        (s.initialState .opening (trapdoor, positions)) true := by
  unfold Submission.run; dsimp only; simp only [ite_true]; rfl

theorem opening_exec_spec (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    ∃ exec : Execution,
      submission.run .opening (trapdoor, positions) = pure exec ∧
      exec.exit = .success ∧
      exec.oracleCalls = 0 ∧
      (exec.state.getReg .x11).toNat =
        (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions).length ∧
      ProofPrefix exec.state (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions) ∧
      (positions.card = BATCH → exec.cycles ≤ 136000) := by
  have hsteps : submission.steps .opening = 274877906944 := rfl
  rw [submission_run_opening submission trapdoor positions]
  by_cases hempty : positions.card = 0
  · obtain ⟨s5, hr5, hpc5, _, _, _, _, _, hx27, _⟩ := openRuns_entry_prefix trapdoor positions
    have h5 := step_BEQ_taken (by omega) hpc5 (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (508#13)))
      (by rw [hx27, hempty]; rfl) (by decide : pcAt 5 + signExtend13 (508#13) = pcAt 132)
    let s132 := s5.setPC (pcAt 132)
    obtain ⟨sHalt, hrepi, hpcH, hx5H, hx10H, hx11H, _⟩ := openRuns_empty_epilogue (rfl : s132.pc = pcAt 132)
    have hexec := OpenRuns.halt (haltIdx := 135) (totalFuel := submission.steps .opening)
      ((hr5.trans h5).trans hrepi) (by omega) rfl hpcH hx5H hx10H (by rw [hsteps]; omega)
    have href : referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions = [] := by
      unfold referenceProof; simp only [hempty, ite_true]
    refine ⟨{ exit := .success, state := sHalt, cycles := 5 + 1 + 3 + 1, oracleCalls := 0 },
      hexec, rfl, rfl, by rw [href, hx11H]; rfl, by rw [href]; intro j hj; exact absurd hj (Nat.not_lt_zero _),
      fun hbatch => by change positions.card = 128 at hbatch; omega⟩
  · have hpos : 0 < positions.card := Nat.pos_of_ne_zero hempty
    have hcard := positions_card_le positions
    obtain ⟨s24, hr24, hpc24, hx2, hx9, hx10, hx11, hx12, hx13, _, hx15, hx16, hx17, hx18,
        hx21, hx24, hx25, hx26, hx27, hx28, hx29, hx31, hmem24⟩ :=
      openRuns_entry_nonzero trapdoor positions hempty
    have hro24 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s24 := by
      intro a _; change s24.mem a = _; rw [hmem24]; rfl
    have hsw0 : SaltWriterState s24 [] :=
      ⟨by simpa using hx25, by simpa using hx13,
       fun _ hj => absurd hj (Nat.not_lt_zero _),
       fun j _ hj => by rw [hx12]; apply BitVec.eq_of_getLsbD_eq; intro b _; simp,
       fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    have ht0 : TailState s24 [] :=
      ⟨hx31, by simpa using hx15, by simpa using hx16, by simpa using hx17,
       fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
    have hcap0 : ∀ q < 4696, s24.getByte (BitVec.ofNat 64 q) = 0#8 := by
      intro q hq; change extractByte (s24.mem _) _ = _; rw [hmem24]
      exact opening_initial_zero_low trapdoor positions q (by omega)
    -- Pass 0: packSaltTopBits
    obtain ⟨st0, s59, hr0, hst0, hpc59, hx2_59, hx9_59, hx18_59, hx21_59, hx24_59, hx26_59, hx27_59,
        hro59, hw59, ht59, hcap59⟩ :=
      openRuns_salt_top hpos hpc24 hx2 hx9 hx10 hx11 hx18 hx21 hx24 hx26 hx27 hx28 hx29 hro24 hsw0 ht0 hcap0
    -- Pass 1: record loop
    have hinv59 : RecInv trapdoor positions 0 (packSaltTopBits (tdSalt trapdoor) positions) [] s59 :=
      ⟨hx2_59, hx9_59, hx18_59, hx21_59, by simpa using hx24_59, hx26_59, by simpa using hx27_59,
       hro59, hw59, ht59, fun c hc => by
         rw [hcap59 (4096 + c) (by omega)]
         have hfalse : capMark16Prefix positions 0 c = false := by
           simp [capMark16Prefix]
         rw [hfalse]; rfl⟩
    obtain ⟨st1, s82, hr1, hst1, hpc82, hx2_82, hx9_82, hx21_82, hx26_82, hbd1F, hbd1T,
        hro82, hw82, ht82, hcap16⟩ :=
      openRuns_rec_all hpos hpc59 hinv59
    -- Pass 2: cap frontier
    obtain ⟨st2, s112, hr2, hst2, hpc112, hx26_112, hw112, ht112⟩ :=
      openRuns_cap_all hpc82 hx2_82 hx9_82 hx21_82 hx26_82 hbd1F hbd1T hro82 hw82 ht82 hcap16
    set fwd0 := packSaltTopBits (tdSalt trapdoor) positions
    set recFwd := fwd0 ++ (positions.sort (· ≤ ·)).flatMap (recordFwd (tdNode trapdoor) (tdSalt trapdoor))
    set recTails := (positions.sort (· ≤ ·)).flatMap (recordTails (tdNode trapdoor))
    set allFwd := referenceProofFwd (tdNode trapdoor) (tdSalt trapdoor) positions
    set allTails := referenceProofTails (tdNode trapdoor) positions
    have hcap128 := cap_frontier_le_128 positions
    have hallFwd_len : allFwd.length ≤ (positions.card + 7) / 8 + 479 * positions.card + 3712 := by
      have hcapF := capFrontierFwd_length (tdNode trapdoor) positions
      change (recFwd ++ capFrontierFwd (tdNode trapdoor) positions).length ≤ _
      rw [List.length_append, hcapF]; omega
    have hallTails_len : allTails.length ≤ 16 * positions.card + 128 :=
      referenceProofTails_length_le (tdNode trapdoor) positions
    have hpack_len : (pack6Bits allTails).length = (6 * allTails.length + 7) / 8 := pack6Bits_length allTails
    have hpack_le : (pack6Bits allTails).length ≤ (6 * (16 * positions.card + 128) + 7) / 8 := by
      rw [hpack_len]; exact Nat.div_le_div_right (by omega)
    have hallFwd_eq : recFwd ++ capFrontierFwd (tdNode trapdoor) positions = allFwd := rfl
    have hallTails_eq : recTails ++ capFrontierTails (tdNode trapdoor) positions = allTails := rfl
    rw [hallFwd_eq] at hw112
    rw [hallTails_eq] at ht112
    rw [hallFwd_eq, hallTails_eq] at hst2
    -- Epilogue
    obtain ⟨stFl, s119, hrFl, hstFl, hpc119, hx10_119, hx26_119, hpr119, ht119⟩ :=
      openRuns_flush_wbuf hpc112 hx26_112 (by omega) (by omega) hw112 ht112
    obtain ⟨stFt, s122, hrFt, hstFt, hpc122, hx10_122, hx26_122, hx31_122, hx15_122, hpr122, htail122⟩ :=
      openRuns_flush_tail hpc119 hx10_119 hx26_119 (by omega) (by omega) hpr119 ht119
    obtain ⟨s128, hrRev, hpc128, hx10_128, hx26_128, hpr128⟩ :=
      openRuns_rev_tail hpc122 hx10_122 hx26_122 hx31_122 hx15_122 (by omega) hpr122 htail122
    obtain ⟨sHalt, hrFin, hpcH, hx5H, hx10H, hx11H, hmemH⟩ :=
      openRuns_finish hpc128 hx10_128 hx26_128
    have htot := ((((((hr24.trans hr0).trans hr1).trans hr2).trans hrFl).trans hrFt).trans hrRev).trans hrFin
    have hq_mono1 : fwd0.length / 8 ≤ recFwd.length / 8 := Nat.div_le_div_right (by simp [recFwd])
    have hq_mono2 : recFwd.length / 8 ≤ allFwd.length / 8 :=
      Nat.div_le_div_right (by
        have h : allFwd.length = recFwd.length + (capFrontierFwd (tdNode trapdoor) positions).length := by
          rw [← hallFwd_eq]; exact List.length_append
        omega)
    have ht_mono : tailAccLen recTails ≤ tailAccLen allTails := tailAccLen_mono_append _ _
    have hta_le : tailAccLen allTails ≤ (pack6Bits allTails).length := tailAccLen_le_pack6Bits allTails
    have hfuel : 24 + st0 + st1 + st2 + stFl + stFt + (1 + 5 * (pack6Bits allTails).length) + 3 + 1 ≤
        submission.steps .opening := by
      rw [hsteps]; omega
    have hexec := OpenRuns.halt (haltIdx := 131) (totalFuel := submission.steps .opening)
      htot (by omega) rfl hpcH hx5H hx10H hfuel
    have href : referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions =
        allFwd ++ (pack6Bits allTails).reverse := by
      unfold referenceProof; simp only [hempty, ite_false]; rfl
    have hlen_lt : (allFwd ++ (pack6Bits allTails).reverse).length < 2 ^ 64 := by
      rw [List.length_append, List.length_reverse]; omega
    refine ⟨{ exit := .success, state := sHalt,
              cycles := 24 + st0 + st1 + st2 + stFl + stFt + (1 + 5 * (pack6Bits allTails).length) + 3 + 1,
              oracleCalls := 0 },
      hexec, rfl, rfl, ?_, ?_, ?_⟩
    · rw [href, hx11H, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen_lt]
    · rw [href]
      intro j hj; change extractByte (sHalt.mem _) _ = _; rw [hmemH]; exact hpr128 j hj
    · intro hbatch
      dsimp only
      change positions.card = 128 at hbatch
      rw [hbatch] at hst0 hst1 hallFwd_len hpack_le
      have hdivF : allFwd.length / 8 ≤ 8130 := by omega
      have hpack128 : (pack6Bits allTails).length ≤ 1632 := by omega
      omega

end CommitGolfCandidate
