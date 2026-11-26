import CommitGolfCandidate.MoonMemory

/-! Exact deterministic symbolic execution of the 158-word pure 3-ary FIFO queue opening image
with 100% 64-bit aligned proof emission and self-similar `M = 143` cap frontier deduplication.
Tracks registers, read-only trapdoor/indices framing, cap-mark scratch bytes, proof output bytes,
and exact step/cycle bounds (`≤ 50,500` cycles at `k = 128`) with zero oracle calls. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-! ### 1. Trapdoor Views, Program Counter, and Multi-Step Relation -/

def tdNode (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (v : Nat) : Digest :=
  trapdoor.extractLsb' (8 * (32 * v)) 256

def tdSalt (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) : Salt192 :=
  trapdoor.extractLsb' (8 * saltOff i) 192

private def oPcAt (idx : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * idx)

private def OpenRuns (s : MachineState) (steps cycles : Nat) (s' : MachineState) : Prop :=
  ∀ fuel : Nat,
    execute (submission.image .opening) (steps + fuel) s true =
      (do let result ← execute (submission.image .opening) fuel s' true
          return result.charge cycles 0)

private theorem OpenRuns.refl (s : MachineState) : OpenRuns s 0 0 s := by
  intro fuel
  simp [Execution.charge]

private theorem OpenRuns.trans {s s1 s2 : MachineState} {n1 n2 c1 c2 : Nat}
    (h1 : OpenRuns s n1 c1 s1) (h2 : OpenRuns s1 n2 c2 s2) :
    OpenRuns s (n1 + n2) (c1 + c2) s2 := by
  intro fuel
  rw [Nat.add_assoc, h1 (n2 + fuel), h2 fuel]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext result
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
    (hhi : haltIdx < 158)
    (hi : openingInstr haltIdx = .base .ECALL)
    (hpc : sHalt.pc = oPcAt haltIdx)
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

/-! ### 2. MachineState, BitVec, and Byte Helpers -/

private theorem o_getReg_x0 (s : MachineState) : s.getReg .x0 = 0#64 := rfl

private theorem o_setReg_x0 (s : MachineState) (v : Word) : s.setReg .x0 v = s := rfl

private theorem o_getReg_setPC (s : MachineState) (v : Word) (r : Reg) :
    (s.setPC v).getReg r = s.getReg r := rfl

private theorem o_card_le (positions : Positions) : positions.card ≤ 16777216 := by
  have h := Finset.card_le_univ positions
  rw [Fintype.card_fin] at h
  exact h

private theorem o_getReg_setMem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

private theorem o_getReg_setByte (s : MachineState) (a : Word) (b : Byte) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by cases r <;> rfl

private theorem o_getByte_setReg (s : MachineState) (r : Reg) (v a : Word) :
    (s.setReg r v).getByte a = s.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem_setReg]

private theorem o_getByte_setPC (s : MachineState) (v a : Word) :
    (s.setPC v).getByte a = s.getByte a := by
  simp only [MachineState.getByte, MachineState.getMem_setPC]

private theorem oPcAt_add4 (idx : Nat) : oPcAt idx + 4 = oPcAt (idx + 1) := by
  unfold oPcAt
  change BitVec.ofNat 64 (0x1000 + 4 * idx) + BitVec.ofNat 64 4 = _
  rw [← BitVec.ofNat_add]
  congr 1

private theorem o_toNat_ofNat (a : Nat) (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

private theorem o_bv_add (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  (BitVec.ofNat_add a b).symm

private theorem o_bv_sub (a b : Nat) (hle : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have h : BitVec.ofNat 64 (a - b) + BitVec.ofNat 64 b = BitVec.ofNat 64 a := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel hle]
  have hc := congrArg (fun v : Word => v - BitVec.ofNat 64 b) h.symm
  simpa only [BitVec.add_sub_cancel] using hc

private theorem o_bv_shl (a k : Nat) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_mod (a % 2 ^ 64), Nat.mod_mod, ← Nat.mul_mod]

private theorem o_bv_shr (a k : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt ha]
  have hlt : a / 2 ^ k < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha
  rw [Nat.mod_eq_of_lt hlt]

private theorem o_bv_and1 (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a &&& signExtend12 (1#12) = BitVec.ofNat 64 (a % 2) := by
  have hse : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  rw [hse]
  apply BitVec.eq_of_toNat_eq
  have h1 : (1 : Nat) < 2 ^ 64 := by omega
  have hm : a % 2 < 2 ^ 64 := by omega
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hm]
  change a &&& (2 ^ 1 - 1) = a % 2 ^ 1
  exact Nat.and_two_pow_sub_one_eq_mod a 1

private theorem o_bv_add_neg1 (n : Nat) :
    BitVec.ofNat 64 (n + 1) + signExtend12 (4095#12) = BitVec.ofNat 64 n := by
  have hse : signExtend12 (4095#12) = (-1#64 : Word) := by decide
  rw [hse, ← o_bv_add n 1]
  change BitVec.ofNat 64 n + 1#64 + (-1#64 : Word) = BitVec.ofNat 64 n
  rw [BitVec.add_assoc, show (1#64 : Word) + (-1#64 : Word) = 0#64 by decide, BitVec.add_zero]

private theorem o_bv_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := by
  intro heq
  have hn := congrArg BitVec.toNat heq
  rw [o_toNat_ofNat a ha, o_toNat_ofNat b hb] at hn
  exact hne hn

private theorem o_se12_lt2048 (n : Nat) (hn : n < 2048) :
    signExtend12 (BitVec.ofNat 12 n) = BitVec.ofNat 64 n := by
  unfold signExtend12
  apply BitVec.eq_of_toNat_eq
  have h12 : n % 2 ^ 12 = n := Nat.mod_eq_of_lt (by omega)
  have h64 : n % 2 ^ 64 = n := Nat.mod_eq_of_lt (by omega)
  have hmsb : (BitVec.ofNat 12 n).msb = false := by
    rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat, h12]
    exact decide_eq_false (by omega)
  rw [BitVec.toNat_signExtend, if_neg (by rw [hmsb]; decide), Nat.add_zero,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat, h12, h64, o_toNat_ofNat n (by omega)]

private theorem o_accessValid (a w : Nat) (hle : a + w ≤ 68719476736) (hal : a % w = 0) :
    accessValid (BitVec.ofNat 64 a) w = true := by
  have ha : a < 2 ^ 64 := by omega
  simp only [accessValid, rangeValid, MEMORY_BYTES, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨by omega, hal⟩

private theorem o_bool_byte_zext (b : Bool) :
    (if b then (1#8 : Byte) else 0#8).zeroExtend 64 = if b then 1#64 else 0#64 := by
  cases b <;> decide

private theorem o_bool_word_or (a b : Bool) :
    (if a then (1#64 : Word) else 0#64) ||| (if b then 1#64 else 0#64) =
      if (a || b) then 1#64 else 0#64 := by
  cases a <;> cases b <;> decide

private theorem o_getMem_extractByte (s : MachineState) (addr j : Nat)
    (halign : addr % 8 = 0) (hj : j < 8) :
    (s.getMem (BitVec.ofNat 64 addr)).extractLsb' (8 * j) 8 =
      s.getByte (BitVec.ofNat 64 (addr + j)) := by
  have hal := alignToDword_ofNat_eq addr j hj halign
  have hbo : byteOffset (BitVec.ofNat 64 (addr + j)) = j := by
    unfold byteOffset
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    change ((addr + j) % 2 ^ 64) &&& (2 ^ 3 - 1) = j
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  simp only [MachineState.getByte, hal, hbo]
  apply BitVec.eq_of_toNat_eq
  simp only [extractByte, BitVec.truncate, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mul_comm 8 j]

private theorem o_extractLsb'_extractLsb' {w : Nat} (x : BitVec w) (base n j : Nat)
    (hj : j < n) :
    (x.extractLsb' (8 * base) (8 * n)).extractLsb' (8 * j) 8 =
      x.extractLsb' (8 * (base + j)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro b hb
  simp only [BitVec.getLsbD_extractLsb', hb, decide_true, Bool.true_and,
    show 8 * j + b < 8 * n by omega, show 8 * base + (8 * j + b) = 8 * (base + j) + b by omega]

private theorem o_bitsToBytes_getElem {w : Nat} (v : BitVec w) (n j : Nat) (hj : j < n) :
    (bitsToBytes v n)[j]'(by rw [bitsToBytes_length]; exact hj) = v.extractLsb' (8 * j) 8 := by
  simp [bitsToBytes]

private theorem o_getElem_append_left {α : Type} (l1 l2 : List α) (j : Nat) (hj : j < l1.length) :
    (l1 ++ l2)[j]'(by rw [List.length_append]; omega) = l1[j]'hj :=
  List.getElem_append_left hj

private theorem o_getElem_append_right {α : Type} (l1 l2 : List α) (j : Nat)
    (hge : l1.length ≤ j) (hj : j < (l1 ++ l2).length) :
    (l1 ++ l2)[j]'hj = l2[j - l1.length]'(by rw [List.length_append] at hj; omega) :=
  List.getElem_append_right hge

/-! ### 3. Single-Instruction Step Lemmas (`idx < 158`) -/

private theorem o_step_ADDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.ADDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (oPcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_ADD {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.ADD rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADD rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADD rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (oPcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SUB {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.SUB rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SUB rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SUB rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (oPcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SLLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.SLLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SLLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SLLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (oPcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SRLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.SRLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SRLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SRLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (oPcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_ANDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.ANDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ANDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ANDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (oPcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_OR {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.OR rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.OR rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.OR rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (oPcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_DIVU {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.DIVU rd rs1 rs2)) :
    OpenRuns s 1 4 ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.DIVU rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.DIVU rd rs1 rs2)) =
      some ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (oPcAt (idx + 1))) := by
    change some ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)) = _
    rw [hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_LD {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.LD rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    OpenRuns s 1 1 ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.LD rd rs1 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.LD rd rs1 off)) =
      some ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (oPcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 8 = true
            then some ((s.setReg rd (s.getMem (s.getReg rs1 + signExtend12 off))).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SD {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.SD rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 8 = true) :
    OpenRuns s 1 1 ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SD rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SD rs1 rs2 off)) =
      some ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (oPcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 8 = true
            then some ((s.setMem (s.getReg rs1 + signExtend12 off) (s.getReg rs2)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_LBU {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.LBU rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 1 = true) :
    OpenRuns s 1 1
      ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.LBU rd rs1 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.LBU rd rs1 off)) =
      some ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (oPcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 1 = true
            then some ((s.setReg rd ((s.getByte (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_SB {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.SB rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 1 = true) :
    OpenRuns s 1 1
      ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SB rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SB rs1 rs2 off)) =
      some ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (oPcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 1 = true
            then some ((s.setByte (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 8)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_BEQ_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
    (heq : s.getReg rs1 = s.getReg rs2) (htgt : oPcAt idx + signExtend13 off = oPcAt tgt) :
    OpenRuns s 1 1 (s.setPC (oPcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BEQ rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : (s.getReg rs1 == s.getReg rs2) = true := by rw [heq]; simp
  have hst : ordinaryStep s (.base (.BEQ rs1 rs2 off)) = some (s.setPC (oPcAt tgt)) := by
    change some (if (s.getReg rs1 == s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem o_step_BEQ_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
    (hne : s.getReg rs1 ≠ s.getReg rs2) :
    OpenRuns s 1 1 (s.setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BEQ rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : ¬ ((s.getReg rs1 == s.getReg rs2) = true) := by simp [hne]
  have hst : ordinaryStep s (.base (.BEQ rs1 rs2 off)) = some (s.setPC (oPcAt (idx + 1))) := by
    change some (if (s.getReg rs1 == s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_BNE_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
    (hne : s.getReg rs1 ≠ s.getReg rs2) (htgt : oPcAt idx + signExtend13 off = oPcAt tgt) :
    OpenRuns s 1 1 (s.setPC (oPcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BNE rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : (s.getReg rs1 != s.getReg rs2) = true := by simp [hne]
  have hst : ordinaryStep s (.base (.BNE rs1 rs2 off)) = some (s.setPC (oPcAt tgt)) := by
    change some (if (s.getReg rs1 != s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem o_step_BNE_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
    (heq : s.getReg rs1 = s.getReg rs2) :
    OpenRuns s 1 1 (s.setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BNE rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : ¬ ((s.getReg rs1 != s.getReg rs2) = true) := by rw [heq]; simp
  have hst : ordinaryStep s (.base (.BNE rs1 rs2 off)) = some (s.setPC (oPcAt (idx + 1))) := by
    change some (if (s.getReg rs1 != s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_BLTU_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
    (hlt : (s.getReg rs1).toNat < (s.getReg rs2).toNat)
    (htgt : oPcAt idx + signExtend13 off = oPcAt tgt) :
    OpenRuns s 1 1 (s.setPC (oPcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BLTU rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : BitVec.ult (s.getReg rs1) (s.getReg rs2) = true := by
    simp only [BitVec.ult, decide_eq_true_eq]; exact hlt
  have hst : ordinaryStep s (.base (.BLTU rs1 rs2 off)) = some (s.setPC (oPcAt tgt)) := by
    change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_pos hcond, hpc, htgt]
  exact OpenRuns.step hf hst

private theorem o_step_BLTU_not_taken {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.BLTU rs1 rs2 off))
    (hle : (s.getReg rs2).toNat ≤ (s.getReg rs1).toNat) :
    OpenRuns s 1 1 (s.setPC (oPcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.BLTU rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hcond : ¬ (BitVec.ult (s.getReg rs1) (s.getReg rs2) = true) := by
    simp only [BitVec.ult, decide_eq_true_eq]; omega
  have hst : ordinaryStep s (.base (.BLTU rs1 rs2 off)) = some (s.setPC (oPcAt (idx + 1))) := by
    change some (if BitVec.ult (s.getReg rs1) (s.getReg rs2) = true
                 then s.setPC (s.pc + signExtend13 off) else s.setPC (s.pc + 4)) = _
    rw [if_neg hcond, hpc, oPcAt_add4]
  exact OpenRuns.step hf hst

private theorem o_step_JAL_x0 {s : MachineState} {idx tgt : Nat} {off : BitVec 21}
    (hidx : idx < 158) (hpc : s.pc = oPcAt idx) (hi : openingInstr idx = .base (.JAL .x0 off))
    (htgt : oPcAt idx + signExtend21 off = oPcAt tgt) :
    OpenRuns s 1 1 (s.setPC (oPcAt tgt)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.JAL .x0 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.JAL .x0 off)) = some (s.setPC (oPcAt tgt)) := by
    change some ((s.setReg .x0 (s.pc + 4)).setPC (s.pc + signExtend21 off)) = _
    rw [o_setReg_x0, hpc, htgt]
  exact OpenRuns.step hf hst

/-! ### 4. Isolated Branch-Target Arithmetic & Standalone Backward-Branch Lemmas -/

private theorem o_tgt_0 : oPcAt 0 + signExtend13 (616#13) = oPcAt 154 := by decide
private theorem o_tgt_51 : oPcAt 51 + signExtend13 (12#13) = oPcAt 54 := by decide
private theorem o_tgt_53 : oPcAt 53 + signExtend21 (16#21) = oPcAt 57 := by decide
private theorem o_tgt_55 : oPcAt 55 + signExtend13 (8#13) = oPcAt 57 := by decide
private theorem o_tgt_75 : oPcAt 75 + signExtend13 (8064#13) = oPcAt 43 := by decide
private theorem o_tgt_79 : oPcAt 79 + signExtend13 (7968#13) = oPcAt 23 := by decide
private theorem o_tgt_92 : oPcAt 92 + signExtend13 (128#13) = oPcAt 124 := by decide
private theorem o_tgt_94 : oPcAt 94 + signExtend13 (40#13) = oPcAt 104 := by decide
private theorem o_tgt_104 : oPcAt 104 + signExtend13 (40#13) = oPcAt 114 := by decide
private theorem o_tgt_114 : oPcAt 114 + signExtend13 (40#13) = oPcAt 124 := by decide
private theorem o_tgt_127 : oPcAt 127 + signExtend13 (8032#13) = oPcAt 87 := by decide
private theorem o_tgt_129 : oPcAt 129 + signExtend13 (40#13) = oPcAt 139 := by decide
private theorem o_tgt_140 : oPcAt 140 + signExtend13 (40#13) = oPcAt 150 := by decide

private theorem o_step_75_back {s : MachineState} {v : Nat}
    (hpc : s.pc = oPcAt 75)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 v)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 CAP_LEAF_LO)
    (hlt : v < CAP_LEAF_LO) :
    OpenRuns s 1 1 (s.setPC (oPcAt 43)) := by
  have hc : CAP_LEAF_LO = 25165395 := capLeafLo_eq
  refine o_step_BLTU_taken (by decide) hpc rfl ?_ o_tgt_75
  rw [hx14, hx22, o_toNat_ofNat v (by omega), o_toNat_ofNat CAP_LEAF_LO (by omega)]
  exact hlt

private theorem o_step_75_done {s : MachineState} {v : Nat}
    (hpc : s.pc = oPcAt 75)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 v)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 CAP_LEAF_LO)
    (hv : v < 2 ^ 64) (hge : CAP_LEAF_LO ≤ v) :
    OpenRuns s 1 1 (s.setPC (oPcAt 76)) := by
  have hc : CAP_LEAF_LO = 25165395 := capLeafLo_eq
  refine o_step_BLTU_not_taken (by decide) hpc rfl ?_
  rw [hx14, hx22, o_toNat_ofNat v hv, o_toNat_ofNat CAP_LEAF_LO (by omega)]
  exact hge

private theorem o_step_79_back {s : MachineState} {a b : Nat}
    (hpc : s.pc = oPcAt 79)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 a)
    (hx18 : s.getReg .x18 = BitVec.ofNat 64 b)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    OpenRuns s 1 1 (s.setPC (oPcAt 23)) :=
  o_step_BNE_taken (by decide) hpc rfl (by rw [hx9, hx18]; exact o_bv_ne ha hb hne) o_tgt_79

private theorem o_step_79_done {s : MachineState} {a : Nat}
    (hpc : s.pc = oPcAt 79)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 a)
    (hx18 : s.getReg .x18 = BitVec.ofNat 64 a) :
    OpenRuns s 1 1 (s.setPC (oPcAt 80)) :=
  o_step_BNE_not_taken (by decide) hpc rfl (by rw [hx9, hx18])

private theorem o_step_127_back {s : MachineState} {a b : Nat}
    (hpc : s.pc = oPcAt 127)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 a)
    (hx16 : s.getReg .x16 = BitVec.ofNat 64 b)
    (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    OpenRuns s 1 1 (s.setPC (oPcAt 87)) :=
  o_step_BNE_taken (by decide) hpc rfl (by rw [hx15, hx16]; exact o_bv_ne ha hb hne) o_tgt_127

private theorem o_step_127_done {s : MachineState} {a : Nat}
    (hpc : s.pc = oPcAt 127)
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 a)
    (hx16 : s.getReg .x16 = BitVec.ofNat 64 a) :
    OpenRuns s 1 1 (s.setPC (oPcAt 128)) :=
  o_step_BNE_not_taken (by decide) hpc rfl (by rw [hx15, hx16])

/-! ### 5. State Invariants and Reusable Aligned Copy Blocks -/

private structure OpenFixed (positions : Positions) (s : MachineState) : Prop where
  x8  : s.getReg .x8  = BitVec.ofNat 64 4294971424
  x18 : s.getReg .x18 = BitVec.ofNat 64 (6643781664 + 8 * positions.card)
  x19 : s.getReg .x19 = BitVec.ofNat 64 11072966688
  x21 : s.getReg .x21 = BitVec.ofNat 64 LENGTH
  x22 : s.getReg .x22 = BitVec.ofNat 64 CAP_LEAF_LO
  x23 : s.getReg .x23 = BitVec.ofNat 64 (4294971424 + rowOff)
  x24 : s.getReg .x24 = BitVec.ofNat 64 4096
  x25 : s.getReg .x25 = BitVec.ofNat 64 3
  x27 : s.getReg .x27 = BitVec.ofNat 64 1

private def OpenReadOnly (s0 s : MachineState) : Prop :=
  ∀ a : Nat, 4294971424 ≤ a → a < 11072966688 →
    s.getByte (BitVec.ofNat 64 a) = s0.getByte (BitVec.ofNat 64 a)

private def OpenMarks (m : Nat → Bool) (s : MachineState) : Prop :=
  ∀ u < 429, s.getByte (BitVec.ofNat 64 (4096 + u)) = if m u then 1#8 else 0#8

private def OpenWritten (written : List Byte) (s : MachineState) : Prop :=
  ∀ j (hj : j < written.length),
    s.getByte (BitVec.ofNat 64 (11072966688 + j)) = written[j]'hj

private theorem OpenReadOnly.getMem_eq {s0 s : MachineState} (hro : OpenReadOnly s0 s)
    (addr : Nat) (hal : addr % 8 = 0) (hlo : 4294971424 ≤ addr) (hhi : addr + 8 ≤ 11072966688) :
    s.getMem (BitVec.ofNat 64 addr) = s0.getMem (BitVec.ofNat 64 addr) := by
  rw [← readBuffer_word s addr hal, ← readBuffer_word s0 addr hal]
  apply readBuffer_congr
  intro j hj
  exact hro (addr + j) (by omega) (by omega)

/-- Copy one 8-byte aligned doubleword (`LD tmp srcReg srcOff; SD dstReg tmp dstOff`). -/
private theorem o_copy_dword {s : MachineState} {idx : Nat} {tmp srcReg dstReg : Reg}
    {srcOff dstOff : Nat} {src dst : Nat}
    (hidx : idx + 1 < 158) (hpc : s.pc = oPcAt idx)
    (hso : srcOff < 2048) (hdo : dstOff < 2048)
    (hi0 : openingInstr idx = .base (.LD tmp srcReg (BitVec.ofNat 12 srcOff)))
    (hi1 : openingInstr (idx + 1) = .base (.SD dstReg tmp (BitVec.ofNat 12 dstOff)))
    (htmp0 : tmp ≠ .x0) (htmpDst : tmp ≠ dstReg)
    (hsrc : s.getReg srcReg = BitVec.ofNat 64 src)
    (hdst : s.getReg dstReg = BitVec.ofNat 64 dst)
    (hsAl : (src + srcOff) % 8 = 0) (hsBd : src + srcOff + 8 ≤ 68719476736)
    (hdAl : (dst + dstOff) % 8 = 0) (hdBd : dst + dstOff + 8 ≤ 68719476736) :
    ∃ s' : MachineState,
      OpenRuns s 2 2 s' ∧
      s'.pc = oPcAt (idx + 2) ∧
      (∀ r, r ≠ tmp → s'.getReg r = s.getReg r) ∧
      (∀ j < 8, s'.getByte (BitVec.ofNat 64 (dst + dstOff + j)) =
        s.getByte (BitVec.ofNat 64 (src + srcOff + j))) ∧
      (∀ a < 2 ^ 64, (a < dst + dstOff ∨ dst + dstOff + 8 ≤ a) →
        s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) := by
  have ha0 : s.getReg srcReg + signExtend12 (BitVec.ofNat 12 srcOff) =
      BitVec.ofNat 64 (src + srcOff) := by
    rw [hsrc, o_se12_lt2048 srcOff hso, o_bv_add]
  have hv0 : accessValid (s.getReg srcReg + signExtend12 (BitVec.ofNat 12 srcOff)) 8 = true := by
    rw [ha0]; exact o_accessValid _ 8 hsBd hsAl
  have hst0 := o_step_LD (by omega) hpc hi0 hv0
  let s1 := (s.setReg tmp (s.getMem (s.getReg srcReg + signExtend12 (BitVec.ofNat 12 srcOff)))).setPC (oPcAt (idx + 1))
  have ha1 : s1.getReg dstReg + signExtend12 (BitVec.ofNat 12 dstOff) =
      BitVec.ofNat 64 (dst + dstOff) := by
    simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ htmpDst,
      hdst, o_se12_lt2048 dstOff hdo, o_bv_add]
  have hv1 : accessValid (s1.getReg dstReg + signExtend12 (BitVec.ofNat 12 dstOff)) 8 = true := by
    rw [ha1]; exact o_accessValid _ 8 hdBd hdAl
  have hst1 := o_step_SD (by omega) rfl hi1 hv1
  let s2 := (s1.setMem (s1.getReg dstReg + signExtend12 (BitVec.ofNat 12 dstOff)) (s1.getReg tmp)).setPC (oPcAt (idx + 2))
  refine ⟨s2, hst0.trans hst1, rfl, ?_, ?_, ?_⟩
  · intro r hr
    simp only [s2, s1, MachineState.getReg_setPC, o_getReg_setMem]
    exact MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)
  · intro j hj
    have hv : s1.getReg tmp = s.getMem (BitVec.ofNat 64 (src + srcOff)) := by
      simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq htmp0, ha0]
    simp only [s2, o_getByte_setPC, ha1, hv]
    rw [setMem_getByte_inside s1 (dst + dstOff) j _ hdAl hj]
    exact o_getMem_extractByte s (src + srcOff) j hsAl hj
  · intro a ha hout
    simp only [s2, o_getByte_setPC, ha1]
    rw [setMem_getByte_ofNat s1 (dst + dstOff) a _ hdAl (by omega) ha hout]
    simp only [s1, o_getByte_setPC, o_getByte_setReg]

/-- Copy 24 bytes (3 aligned dwords) from `src` to `dst` (`x20`), advancing `x20 += 24` (`pc[36..42]`). -/
private theorem o_copy_24 {s : MachineState} {src dst : Nat}
    (hpc : s.pc = oPcAt 36)
    (hx7 : s.getReg .x7 = BitVec.ofNat 64 src)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 dst)
    (hsAl : src % 8 = 0) (hsBd : src + 24 ≤ 68719476736)
    (hdAl : dst % 8 = 0) (hdBd : dst + 24 ≤ 68719476736)
    (hdisj : src + 24 ≤ dst ∨ dst + 24 ≤ src) :
    ∃ s' : MachineState,
      OpenRuns s 7 7 s' ∧
      s'.pc = oPcAt 43 ∧
      s'.getReg .x20 = BitVec.ofNat 64 (dst + 24) ∧
      (∀ r, r ≠ .x28 → r ≠ .x20 → s'.getReg r = s.getReg r) ∧
      (∀ j < 24, s'.getByte (BitVec.ofNat 64 (dst + j)) = s.getByte (BitVec.ofNat 64 (src + j))) ∧
      (∀ a < 2 ^ 64, (a < dst ∨ dst + 24 ≤ a) →
        s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) := by
  obtain ⟨s1, hr1, hp1, hreg1, hin1, hout1⟩ := o_copy_dword (idx := 36) (tmp := .x28) (srcReg := .x7)
    (dstReg := .x20) (srcOff := 0) (dstOff := 0) (by decide) hpc (by decide) (by decide)
    rfl rfl (by decide) (by decide) hx7 hx20 (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s2, hr2, hp2, hreg2, hin2, hout2⟩ := o_copy_dword (idx := 38) (tmp := .x28) (srcReg := .x7)
    (dstReg := .x20) (srcOff := 8) (dstOff := 8) (by decide) hp1 (by decide) (by decide)
    rfl rfl (by decide) (by decide) ((hreg1 .x7 (by decide)).trans hx7)
    ((hreg1 .x20 (by decide)).trans hx20) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s3, hr3, hp3, hreg3, hin3, hout3⟩ := o_copy_dword (idx := 40) (tmp := .x28) (srcReg := .x7)
    (dstReg := .x20) (srcOff := 16) (dstOff := 16) (by decide) hp2 (by decide) (by decide)
    rfl rfl (by decide) (by decide) ((hreg2 .x7 (by decide)).trans ((hreg1 .x7 (by decide)).trans hx7))
    ((hreg2 .x20 (by decide)).trans ((hreg1 .x20 (by decide)).trans hx20))
    (by omega) (by omega) (by omega) (by omega)
  have hst42 := o_step_ADDI (idx := 42) (rd := .x20) (rs1 := .x20) (imm := 24#12) (by decide) hp3 rfl
  let s4 := (s3.setReg .x20 (s3.getReg .x20 + signExtend12 24#12)).setPC (oPcAt 43)
  have hx20_3 : s3.getReg .x20 = BitVec.ofNat 64 dst :=
    (hreg3 .x20 (by decide)).trans ((hreg2 .x20 (by decide)).trans ((hreg1 .x20 (by decide)).trans hx20))
  refine ⟨s4, (hr1.trans hr2).trans (hr3.trans hst42), rfl, ?_, ?_, ?_, ?_⟩
  · simp only [s4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      hx20_3, show signExtend12 24#12 = BitVec.ofNat 64 24 by decide, o_bv_add]
  · intro r h28 h20
    simp only [s4, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h20)]
    exact (hreg3 r h28).trans ((hreg2 r h28).trans (hreg1 r h28))
  · intro j hj
    simp only [s4, o_getByte_setPC, o_getByte_setReg]
    by_cases h8 : j < 8
    · have a3 := hout3 (dst + j) (by omega) (by omega)
      have a2 := hout2 (dst + j) (by omega) (by omega)
      have a1 := hin1 j h8
      simpa only [Nat.add_zero] using a3.trans (a2.trans a1)
    · by_cases h16 : j < 16
      · have a3 := hout3 (dst + j) (by omega) (by omega)
        have a2 := hin2 (j - 8) (by omega)
        have a1 := hout1 (src + j) (by omega) (by omega)
        have eq1 : dst + 8 + (j - 8) = dst + j := by omega
        have eq2 : src + 8 + (j - 8) = src + j := by omega
        rw [eq1, eq2] at a2
        exact a3.trans (a2.trans a1)
      · have a3 := hin3 (j - 16) (by omega)
        have a2 := hout2 (src + j) (by omega) (by omega)
        have a1 := hout1 (src + j) (by omega) (by omega)
        have eq1 : dst + 16 + (j - 16) = dst + j := by omega
        have eq2 : src + 16 + (j - 16) = src + j := by omega
        rw [eq1, eq2] at a3
        exact a3.trans (a2.trans a1)
  · intro a ha hout
    simp only [s4, o_getByte_setPC, o_getByte_setReg]
    exact (hout3 a ha (by omega)).trans ((hout2 a ha (by omega)).trans (hout1 a ha (by omega)))

/-- Copy 32 bytes (4 aligned dwords) from `srcReg + baseOff` to `x20 + dstOff` (`8` steps/cycles). -/
private theorem o_copy_32_raw {s : MachineState} {idx : Nat} {tmp srcReg : Reg}
    {baseOff dstOff src dst : Nat}
    (hidx : idx + 7 < 158) (hpc : s.pc = oPcAt idx)
    (hso : baseOff + 24 < 2048) (hdo : dstOff + 24 < 2048)
    (hi0 : openingInstr idx = .base (.LD tmp srcReg (BitVec.ofNat 12 baseOff)))
    (hi1 : openingInstr (idx + 1) = .base (.SD .x20 tmp (BitVec.ofNat 12 dstOff)))
    (hi2 : openingInstr (idx + 2) = .base (.LD tmp srcReg (BitVec.ofNat 12 (baseOff + 8))))
    (hi3 : openingInstr (idx + 3) = .base (.SD .x20 tmp (BitVec.ofNat 12 (dstOff + 8))))
    (hi4 : openingInstr (idx + 4) = .base (.LD tmp srcReg (BitVec.ofNat 12 (baseOff + 16))))
    (hi5 : openingInstr (idx + 5) = .base (.SD .x20 tmp (BitVec.ofNat 12 (dstOff + 16))))
    (hi6 : openingInstr (idx + 6) = .base (.LD tmp srcReg (BitVec.ofNat 12 (baseOff + 24))))
    (hi7 : openingInstr (idx + 7) = .base (.SD .x20 tmp (BitVec.ofNat 12 (dstOff + 24))))
    (htmp0 : tmp ≠ .x0) (htmpSrc : tmp ≠ srcReg) (htmp20 : tmp ≠ .x20)
    (hsrc : s.getReg srcReg = BitVec.ofNat 64 src)
    (hdst : s.getReg .x20 = BitVec.ofNat 64 dst)
    (hsAl : (src + baseOff) % 8 = 0) (hsBd : src + baseOff + 32 ≤ 68719476736)
    (hdAl : (dst + dstOff) % 8 = 0) (hdBd : dst + dstOff + 32 ≤ 68719476736)
    (hdisj : src + baseOff + 32 ≤ dst + dstOff ∨ dst + dstOff + 32 ≤ src + baseOff) :
    ∃ s' : MachineState,
      OpenRuns s 8 8 s' ∧
      s'.pc = oPcAt (idx + 8) ∧
      (∀ r, r ≠ tmp → s'.getReg r = s.getReg r) ∧
      (∀ j < 32, s'.getByte (BitVec.ofNat 64 (dst + dstOff + j)) =
        s.getByte (BitVec.ofNat 64 (src + baseOff + j))) ∧
      (∀ a < 2 ^ 64, (a < dst + dstOff ∨ dst + dstOff + 32 ≤ a) →
        s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) := by
  obtain ⟨s1, hr1, hp1, hreg1, hin1, hout1⟩ := o_copy_dword (idx := idx) (tmp := tmp)
    (srcReg := srcReg) (dstReg := .x20) (srcOff := baseOff) (dstOff := dstOff)
    (by omega) hpc (by omega) (by omega) hi0 hi1 htmp0 htmp20 hsrc hdst
    hsAl (by omega) hdAl (by omega)
  obtain ⟨s2, hr2, hp2, hreg2, hin2, hout2⟩ := o_copy_dword (idx := idx + 2) (tmp := tmp)
    (srcReg := srcReg) (dstReg := .x20) (srcOff := baseOff + 8) (dstOff := dstOff + 8)
    (by omega) hp1 (by omega) (by omega) hi2 hi3 htmp0 htmp20
    ((hreg1 srcReg htmpSrc.symm).trans hsrc) ((hreg1 .x20 htmp20.symm).trans hdst)
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s3, hr3, hp3, hreg3, hin3, hout3⟩ := o_copy_dword (idx := idx + 4) (tmp := tmp)
    (srcReg := srcReg) (dstReg := .x20) (srcOff := baseOff + 16) (dstOff := dstOff + 16)
    (by omega) hp2 (by omega) (by omega) hi4 hi5 htmp0 htmp20
    ((hreg2 srcReg htmpSrc.symm).trans ((hreg1 srcReg htmpSrc.symm).trans hsrc))
    ((hreg2 .x20 htmp20.symm).trans ((hreg1 .x20 htmp20.symm).trans hdst))
    (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s4, hr4, hp4, hreg4, hin4, hout4⟩ := o_copy_dword (idx := idx + 6) (tmp := tmp)
    (srcReg := srcReg) (dstReg := .x20) (srcOff := baseOff + 24) (dstOff := dstOff + 24)
    (by omega) hp3 (by omega) (by omega) hi6 hi7 htmp0 htmp20
    ((hreg3 srcReg htmpSrc.symm).trans ((hreg2 srcReg htmpSrc.symm).trans ((hreg1 srcReg htmpSrc.symm).trans hsrc)))
    ((hreg3 .x20 htmp20.symm).trans ((hreg2 .x20 htmp20.symm).trans ((hreg1 .x20 htmp20.symm).trans hdst)))
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨s4, (hr1.trans hr2).trans (hr3.trans hr4), hp4, ?_, ?_, ?_⟩
  · intro r hr
    exact (hreg4 r hr).trans ((hreg3 r hr).trans ((hreg2 r hr).trans (hreg1 r hr)))
  · intro j hj
    by_cases h8 : j < 8
    · exact (hout4 _ (by omega) (by omega)).trans
        ((hout3 _ (by omega) (by omega)).trans ((hout2 _ (by omega) (by omega)).trans (hin1 j h8)))
    · by_cases h16 : j < 16
      · have h2 := hin2 (j - 8) (by omega)
        have eq1 : dst + (dstOff + 8) + (j - 8) = dst + dstOff + j := by omega
        have eq2 : src + (baseOff + 8) + (j - 8) = src + baseOff + j := by omega
        rw [eq1, eq2] at h2
        exact (hout4 _ (by omega) (by omega)).trans
          ((hout3 _ (by omega) (by omega)).trans (h2.trans (hout1 _ (by omega) (by omega))))
      · by_cases h24 : j < 24
        · have h3 := hin3 (j - 16) (by omega)
          have eq1 : dst + (dstOff + 16) + (j - 16) = dst + dstOff + j := by omega
          have eq2 : src + (baseOff + 16) + (j - 16) = src + baseOff + j := by omega
          rw [eq1, eq2] at h3
          exact (hout4 _ (by omega) (by omega)).trans
            (h3.trans ((hout2 _ (by omega) (by omega)).trans (hout1 _ (by omega) (by omega))))
        · have h4 := hin4 (j - 24) (by omega)
          have eq1 : dst + (dstOff + 24) + (j - 24) = dst + dstOff + j := by omega
          have eq2 : src + (baseOff + 24) + (j - 24) = src + baseOff + j := by omega
          rw [eq1, eq2] at h4
          exact h4.trans ((hout3 _ (by omega) (by omega)).trans
            ((hout2 _ (by omega) (by omega)).trans (hout1 _ (by omega) (by omega))))
  · intro a ha hout
    exact (hout4 a ha (by omega)).trans ((hout3 a ha (by omega)).trans
      ((hout2 a ha (by omega)).trans (hout1 a ha (by omega))))

/-- Conditional 32-byte cap frontier copy (`BNE flagReg x0 +40; copy32; ADDI x20 x20 32`). -/
private theorem o_cap_cond_copy32 {s0 s : MachineState} {idx : Nat} {flagReg : Reg}
    {baseOff u : Nat} {trapdoor : BitVec (8 * submission.sizes.trapdoor)} {positions : Positions}
    {flag : Bool} {written : List Byte}
    (hs0 : s0 = submission.initialState .opening (trapdoor, positions))
    (hidx : idx + 9 < 158) (hpc : s.pc = oPcAt idx)
    (htgt : oPcAt idx + signExtend13 (40#13) = oPcAt (idx + 10))
    (hso : baseOff + 24 < 2048) (hso8 : baseOff % 8 = 0)
    (hiB : openingInstr idx = .base (.BNE flagReg .x0 (40#13)))
    (hi0 : openingInstr (idx + 1) = .base (.LD .x30 .x17 (BitVec.ofNat 12 baseOff)))
    (hi1 : openingInstr (idx + 2) = .base (.SD .x20 .x30 (BitVec.ofNat 12 0)))
    (hi2 : openingInstr (idx + 3) = .base (.LD .x30 .x17 (BitVec.ofNat 12 (baseOff + 8))))
    (hi3 : openingInstr (idx + 4) = .base (.SD .x20 .x30 (BitVec.ofNat 12 8)))
    (hi4 : openingInstr (idx + 5) = .base (.LD .x30 .x17 (BitVec.ofNat 12 (baseOff + 16))))
    (hi5 : openingInstr (idx + 6) = .base (.SD .x20 .x30 (BitVec.ofNat 12 16)))
    (hi6 : openingInstr (idx + 7) = .base (.LD .x30 .x17 (BitVec.ofNat 12 (baseOff + 24))))
    (hi7 : openingInstr (idx + 8) = .base (.SD .x20 .x30 (BitVec.ofNat 12 24)))
    (hiA : openingInstr (idx + 9) = .base (.ADDI .x20 .x20 (32#12)))
    (hflag : s.getReg flagReg = if flag then 1#64 else 0#64)
    (hx17 : s.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * u - baseOff))
    (huLo : baseOff ≤ 32 * u) (huHi : u < TREE_NODES)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length))
    (hwLen8 : written.length % 8 = 0) (hwCap : written.length + (if !flag then 32 else 0) ≤ proofCap)
    (hro : OpenReadOnly s0 s) (hw : OpenWritten written s) :
    let chunk := if !flag then bitsToBytes (tdNode trapdoor u) 32 else []
    let cost := if !flag then 10 else 1
    ∃ s' : MachineState,
      OpenRuns s cost cost s' ∧
      s'.pc = oPcAt (idx + 10) ∧
      s'.getReg .x20 = BitVec.ofNat 64 (11072966688 + (written ++ chunk).length) ∧
      (∀ r, r ≠ .x30 → r ≠ .x20 → s'.getReg r = s.getReg r) ∧
      OpenReadOnly s0 s' ∧
      OpenWritten (written ++ chunk) s' ∧
      (∀ a < 11072966688, s'.getByte (BitVec.ofNat 64 a) = s.getByte (BitVec.ofNat 64 a)) := by
  intro chunk cost
  cases flag with
  | true =>
    have hne : s.getReg flagReg ≠ s.getReg .x0 := by rw [hflag, o_getReg_x0]; decide
    have hst := o_step_BNE_taken (by omega) hpc hiB hne htgt
    refine ⟨s.setPC (oPcAt (idx + 10)), hst, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [chunk, Bool.not_true, Bool.false_eq_true, ite_false, List.append_nil, MachineState.getReg_setPC, hx20]
    · intro r _ _; exact o_getReg_setPC s _ r
    · intro a ha1 ha2; rw [o_getByte_setPC]; exact hro a ha1 ha2
    · intro j hj
      simp only [chunk, Bool.not_true, Bool.false_eq_true, ite_false, List.append_nil] at hj ⊢
      rw [o_getByte_setPC]; exact hw j hj
    · intro a _; exact o_getByte_setPC s _ _
  | false =>
    simp only [Bool.not_false, ite_true] at hwCap
    have heq : s.getReg flagReg = s.getReg .x0 := by simp [hflag, o_getReg_x0]
    have hstB := o_step_BNE_not_taken (by omega) hpc hiB heq
    let s1 := s.setPC (oPcAt (idx + 1))
    have htn := treeNodes_eq
    have hpc_cap : proofCap = 11140077536 := rfl
    have hsrc_eq : (4294971424 + 32 * u - baseOff) + baseOff = 4294971424 + 32 * u := by omega
    obtain ⟨s2, hr2, hp2, hreg2, hin2, hout2⟩ := o_copy_32_raw (s := s1) (idx := idx + 1)
      (tmp := .x30) (srcReg := .x17) (baseOff := baseOff) (dstOff := 0)
      (src := 4294971424 + 32 * u - baseOff) (dst := 11072966688 + written.length)
      (by omega) rfl hso (by decide) hi0 hi1 hi2 hi3 hi4 hi5 hi6 hi7
      (by decide) (by decide) (by decide) hx17 hx20
      (by rw [hsrc_eq]; omega) (by rw [hsrc_eq]; omega)
      (by omega) (by omega) (by rw [hsrc_eq]; omega)
    have hstA := o_step_ADDI (idx := idx + 9) (rd := .x20) (rs1 := .x20) (imm := 32#12)
      (by omega) hp2 hiA
    let s3 := (s2.setReg .x20 (s2.getReg .x20 + signExtend12 32#12)).setPC (oPcAt (idx + 10))
    have hx20_2 : s2.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length) :=
      (hreg2 .x20 (by decide)).trans hx20
    have hrun : OpenRuns s 10 10 s3 := by
      have h12 := hstB.trans hr2
      have h123 := h12.trans hstA
      simpa only [show 1 + 8 + 1 = 10 from rfl] using h123
    refine ⟨s3, hrun, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [s3, chunk, Bool.not_false, ite_true, List.length_append, bitsToBytes_length,
        MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx20_2,
        show signExtend12 32#12 = BitVec.ofNat 64 32 by decide, o_bv_add, Nat.add_assoc]
    · intro r h30 h20
      simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h20)]
      exact hreg2 r h30
    · intro a ha1 ha2
      simp only [s3, o_getByte_setPC, o_getByte_setReg]
      exact (hout2 a (by omega) (by omega)).trans (hro a ha1 ha2)
    · intro j hj
      simp only [s3, o_getByte_setPC, o_getByte_setReg]
      by_cases hlt : j < written.length
      · rw [o_getElem_append_left _ _ j hlt]
        exact (hout2 (11072966688 + j) (by omega) (by omega)).trans (hw j hlt)
      · have hge : written.length ≤ j := by omega
        rw [o_getElem_append_right _ _ j hge hj]
        simp only [chunk, Bool.not_false, ite_true] at hj ⊢
        have hk : j - written.length < 32 := by
          rw [List.length_append, bitsToBytes_length] at hj; omega
        rw [o_bitsToBytes_getElem _ 32 _ hk]
        have hcopy := hin2 (j - written.length) hk
        have ha1 : 11072966688 + written.length + 0 + (j - written.length) = 11072966688 + j := by omega
        have ha2 : 4294971424 + 32 * u - baseOff + baseOff + (j - written.length) =
            4294971424 + (32 * u + (j - written.length)) := by omega
        rw [ha1, ha2] at hcopy
        have hro_u := hro (4294971424 + (32 * u + (j - written.length))) (by omega) (by omega)
        have htd_b : s0.getByte (BitVec.ofNat 64 (4294971424 + (32 * u + (j - written.length)))) =
            trapdoor.extractLsb' (8 * (32 * u + (j - written.length))) 8 := by
          rw [hs0]
          exact opening_initial_trapdoor_byte trapdoor positions (32 * u + (j - written.length)) (by omega)
        have hex : (tdNode trapdoor u).extractLsb' (8 * (j - written.length)) 8 =
            trapdoor.extractLsb' (8 * (32 * u + (j - written.length))) 8 :=
          o_extractLsb'_extractLsb' trapdoor (32 * u) 32 (j - written.length) hk
        exact hcopy.trans (hro_u.trans (htd_b.trans hex.symm))
    · intro a ha
      simp only [s3, o_getByte_setPC, o_getByte_setReg]
      exact hout2 a (by omega) (by omega)

/-! ### 6. Prologue, Empty Case, and Epilogue -/

private theorem o_empty_run (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (hempty : positions.card = 0) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ sHalt : MachineState,
      OpenRuns s0 4 4 sHalt ∧
      sHalt.pc = oPcAt 157 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = 0#64 := by
  intro s0
  have hpc0 : s0.pc = oPcAt 0 := rfl
  have hx16 : s0.getReg .x16 = 0#64 := by
    change BitVec.ofNat 64 positions.card = 0#64
    rw [hempty]
  have h0 := o_step_BEQ_taken (s := s0) (idx := 0) (tgt := 154) (by decide) hpc0 rfl
    (by rw [hx16, o_getReg_x0]) o_tgt_0
  let s1 := s0.setPC (oPcAt 154)
  have h1 := o_step_ADDI (s := s1) (idx := 154) (rd := .x11) (rs1 := .x0) (imm := 0#12)
    (by decide) rfl rfl
  let s2 := (s1.setReg .x11 (s1.getReg .x0 + signExtend12 0#12)).setPC (oPcAt 155)
  have h2 := o_step_ADDI (s := s2) (idx := 155) (rd := .x5) (rs1 := .x0) (imm := 1#12)
    (by decide) rfl rfl
  let s3 := (s2.setReg .x5 (s2.getReg .x0 + signExtend12 1#12)).setPC (oPcAt 156)
  have h3 := o_step_ADDI (s := s3) (idx := 156) (rd := .x10) (rs1 := .x0) (imm := 0#12)
    (by decide) rfl rfl
  let s4 := (s3.setReg .x10 (s3.getReg .x0 + signExtend12 0#12)).setPC (oPcAt 157)
  refine ⟨s4, (h0.trans h1).trans (h2.trans h3), rfl, ?_, ?_, ?_⟩
  · simp only [s4, s3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, o_getReg_x0]; decide
  · simp only [s4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, o_getReg_x0]; decide
  · simp only [s4, s3, s2, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x11),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x5 ≠ .x11),
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, o_getReg_x0]; decide

private theorem o_prologue (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (hne : positions.card ≠ 0) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ s1 : MachineState,
      OpenRuns s0 23 23 s1 ∧
      s1.pc = oPcAt 23 ∧
      OpenFixed positions s1 ∧
      s1.getReg .x9 = BitVec.ofNat 64 6643781664 ∧
      s1.getReg .x20 = BitVec.ofNat 64 11072966688 ∧
      OpenReadOnly s0 s1 ∧
      OpenMarks (fun _ => false) s1 ∧
      OpenWritten [] s1 := by
  intro s0
  have hcard_le : positions.card ≤ 16777216 := o_card_le positions
  have hpc0 : s0.pc = oPcAt 0 := rfl
  have hx12 : s0.getReg .x12 = BitVec.ofNat 64 4294971424 := rfl
  have hx13 : s0.getReg .x13 = BitVec.ofNat 64 6643781664 := rfl
  have hx15 : s0.getReg .x15 = BitVec.ofNat 64 11072966688 := rfl
  have hx16 : s0.getReg .x16 = BitVec.ofNat 64 positions.card := rfl
  have h0 := o_step_BEQ_not_taken (s := s0) (idx := 0) (by decide) hpc0 rfl
    (by rw [hx16, o_getReg_x0]; exact o_bv_ne (by omega) (by omega) hne)
  let t1 := s0.setPC (oPcAt 1)
  have h1 := o_step_ADDI (s := t1) (idx := 1) (by decide) rfl rfl
  let t2 := (t1.setReg .x8 (t1.getReg .x12 + signExtend12 0#12)).setPC (oPcAt 2)
  have h2 := o_step_ADDI (s := t2) (idx := 2) (by decide) rfl rfl
  let t3 := (t2.setReg .x9 (t2.getReg .x13 + signExtend12 0#12)).setPC (oPcAt 3)
  have h3 := o_step_SLLI (s := t3) (idx := 3) (by decide) rfl rfl
  let t4 := (t3.setReg .x6 (t3.getReg .x16 <<< (3#6 : BitVec 6).toNat)).setPC (oPcAt 4)
  have h4 := o_step_ADD (s := t4) (idx := 4) (by decide) rfl rfl
  let t5 := (t4.setReg .x18 (t4.getReg .x9 + t4.getReg .x6)).setPC (oPcAt 5)
  have h5 := o_step_ADDI (s := t5) (idx := 5) (by decide) rfl rfl
  let t6 := (t5.setReg .x19 (t5.getReg .x15 + signExtend12 0#12)).setPC (oPcAt 6)
  have h6 := o_step_ADDI (s := t6) (idx := 6) (by decide) rfl rfl
  let t7 := (t6.setReg .x20 (t6.getReg .x15 + signExtend12 0#12)).setPC (oPcAt 7)
  have h7 := o_step_ADDI (s := t7) (idx := 7) (by decide) rfl rfl
  let t8 := (t7.setReg .x21 (t7.getReg .x0 + signExtend12 4#12)).setPC (oPcAt 8)
  have h8 := o_step_SLLI (s := t8) (idx := 8) (by decide) rfl rfl
  let t9 := (t8.setReg .x21 (t8.getReg .x21 <<< (11#6 : BitVec 6).toNat)).setPC (oPcAt 9)
  have h9 := o_step_SLLI (s := t9) (idx := 9) (by decide) rfl rfl
  let t10 := (t9.setReg .x21 (t9.getReg .x21 <<< (11#6 : BitVec 6).toNat)).setPC (oPcAt 10)
  have h10 := o_step_ADDI (s := t10) (idx := 10) (by decide) rfl rfl
  let t11 := (t10.setReg .x22 (t10.getReg .x0 + signExtend12 5#12)).setPC (oPcAt 11)
  have h11 := o_step_SLLI (s := t11) (idx := 11) (by decide) rfl rfl
  let t12 := (t11.setReg .x22 (t11.getReg .x22 <<< (11#6 : BitVec 6).toNat)).setPC (oPcAt 12)
  have h12 := o_step_ADDI (s := t12) (idx := 12) (by decide) rfl rfl
  let t13 := (t12.setReg .x22 (t12.getReg .x22 + signExtend12 2047#12)).setPC (oPcAt 13)
  have h13 := o_step_SLLI (s := t13) (idx := 13) (by decide) rfl rfl
  let t14 := (t13.setReg .x22 (t13.getReg .x22 <<< (11#6 : BitVec 6).toNat)).setPC (oPcAt 14)
  have h14 := o_step_ADDI (s := t14) (idx := 14) (by decide) rfl rfl
  let t15 := (t14.setReg .x22 (t14.getReg .x22 + signExtend12 1619#12)).setPC (oPcAt 15)
  have h15 := o_step_ADDI (s := t15) (idx := 15) (by decide) rfl rfl
  let t16 := (t15.setReg .x6 (t15.getReg .x0 + signExtend12 192#12)).setPC (oPcAt 16)
  have h16 := o_step_SLLI (s := t16) (idx := 16) (by decide) rfl rfl
  let t17 := (t16.setReg .x6 (t16.getReg .x6 <<< (11#6 : BitVec 6).toNat)).setPC (oPcAt 17)
  have h17 := o_step_SLLI (s := t17) (idx := 17) (by decide) rfl rfl
  let t18 := (t17.setReg .x6 (t17.getReg .x6 <<< (11#6 : BitVec 6).toNat)).setPC (oPcAt 18)
  have h18 := o_step_ADD (s := t18) (idx := 18) (by decide) rfl rfl
  let t19 := (t18.setReg .x23 (t18.getReg .x8 + t18.getReg .x6)).setPC (oPcAt 19)
  have h19 := o_step_ADDI (s := t19) (idx := 19) (by decide) rfl rfl
  let t20 := (t19.setReg .x24 (t19.getReg .x0 + signExtend12 2#12)).setPC (oPcAt 20)
  have h20 := o_step_SLLI (s := t20) (idx := 20) (by decide) rfl rfl
  let t21 := (t20.setReg .x24 (t20.getReg .x24 <<< (11#6 : BitVec 6).toNat)).setPC (oPcAt 21)
  have h21 := o_step_ADDI (s := t21) (idx := 21) (by decide) rfl rfl
  let t22 := (t21.setReg .x25 (t21.getReg .x0 + signExtend12 3#12)).setPC (oPcAt 22)
  have h22 := o_step_ADDI (s := t22) (idx := 22) (by decide) rfl rfl
  let t23 := (t22.setReg .x27 (t22.getReg .x0 + signExtend12 1#12)).setPC (oPcAt 23)
  have hrun : OpenRuns s0 23 23 t23 := by
    have a := ((h0.trans h1).trans (h2.trans h3)).trans ((h4.trans h5).trans (h6.trans h7))
    have b := ((h8.trans h9).trans (h10.trans h11)).trans ((h12.trans h13).trans (h14.trans h15))
    have c := ((h16.trans h17).trans (h18.trans h19)).trans ((h20.trans h21).trans h22)
    simpa only [show 8 + 8 + 7 = 23 from rfl] using (a.trans b).trans c
  have hbyte_eq : ∀ addr, t23.getByte addr = s0.getByte addr := fun addr => by
    simp only [t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10,
      t9, t8, t7, t6, t5, t4, t3, t2, t1, o_getByte_setPC, o_getByte_setReg]
  have hx8_2 : t2.getReg .x8 = BitVec.ofNat 64 4294971424 := by
    simp only [t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx12]
    decide
  have hx9_3 : t3.getReg .x9 = BitVec.ofNat 64 6643781664 := by
    simp only [t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x13), hx13]
    decide
  have hx6_4 : t4.getReg .x6 = BitVec.ofNat 64 (8 * positions.card) := by
    simp only [t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x16),
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x16), hx16,
      show (3#6 : BitVec 6).toNat = 3 by decide, o_bv_shl]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hx18_5 : t5.getReg .x18 = BitVec.ofNat 64 (6643781664 + 8 * positions.card) := by
    have hx9_4 : t4.getReg .x9 = BitVec.ofNat 64 6643781664 := by
      simp only [t4, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x9), hx9_3]
    simp only [t5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      hx9_4, hx6_4, o_bv_add]
  have hx19_6 : t6.getReg .x19 = BitVec.ofNat 64 11072966688 := by
    simp only [t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx15]
    decide
  have hx20_7 : t7.getReg .x20 = BitVec.ofNat 64 11072966688 := by
    simp only [t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx15]
    decide
  have hx21_10 : t10.getReg .x21 = BitVec.ofNat 64 LENGTH := by
    simp only [t10, t9, t8, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, o_getReg_x0]
    decide
  have hx22_15 : t15.getReg .x22 = BitVec.ofNat 64 CAP_LEAF_LO := by
    rw [capLeafLo_eq]
    simp only [t15, t14, t13, t12, t11, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, o_getReg_x0]
    decide
  have hx6_18 : t18.getReg .x6 = BitVec.ofNat 64 rowOff := by
    rw [rowOff_eq]
    simp only [t18, t17, t16, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, o_getReg_x0]
    decide
  have hx23_19 : t19.getReg .x23 = BitVec.ofNat 64 (4294971424 + rowOff) := by
    have hx8_18 : t18.getReg .x8 = BitVec.ofNat 64 4294971424 := by
      simp only [t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8, t7, t6, t5, t4, t3,
        MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
        reduceCtorEq, hx8_2]
    simp only [t19, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      hx8_18, hx6_18, o_bv_add]
  have hx24_21 : t21.getReg .x24 = BitVec.ofNat 64 4096 := by
    simp only [t21, t20, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, o_getReg_x0]
    decide
  have hx25_22 : t22.getReg .x25 = BitVec.ofNat 64 3 := by
    simp only [t22, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, o_getReg_x0]
    decide
  have hx27_23 : t23.getReg .x27 = BitVec.ofNat 64 1 := by
    simp only [t23, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, o_getReg_x0]
    decide
  refine ⟨t23, hrun, rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hx27_23⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8, t7,
      t6, t5, t4, t3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, hx8_2]
  · simp only [t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8, t7,
      t6, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, hx18_5]
  · simp only [t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8, t7,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, hx19_6]
  · simp only [t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, hx21_10]
  · simp only [t23, t22, t21, t20, t19, t18, t17, t16,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, hx22_15]
  · simp only [t23, t22, t21, t20, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, hx23_19]
  · simp only [t23, t22, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, hx24_21]
  · simp only [t23, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, hx25_22]
  · simp only [t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8, t7,
      t6, t5, t4, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, hx9_3]
  · simp only [t23, t22, t21, t20, t19, t18, t17, t16, t15, t14, t13, t12, t11, t10, t9, t8,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, hx20_7]
  · intro a _ _; exact hbyte_eq _
  · intro u hu
    simp only [hbyte_eq, Bool.false_eq_true, ite_false]
    exact opening_initial_zero_low trapdoor positions (4096 + u) (by omega)
  · intro j hj; simp at hj

private theorem o_epilogue {s : MachineState} {written : List Byte}
    (hpc : s.pc = oPcAt 150)
    (hx19 : s.getReg .x19 = BitVec.ofNat 64 11072966688)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length))
    (hcap : written.length ≤ proofCap) :
    ∃ sHalt : MachineState,
      OpenRuns s 3 3 sHalt ∧
      sHalt.pc = oPcAt 153 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      (sHalt.getReg .x11).toNat = written.length ∧
      (∀ addr, sHalt.getByte addr = s.getByte addr) := by
  have hpc_cap : proofCap = 11140077536 := rfl
  have h0 := o_step_SUB (s := s) (idx := 150) (by decide) hpc rfl
  let s1 := (s.setReg .x11 (s.getReg .x20 - s.getReg .x19)).setPC (oPcAt 151)
  have h1 := o_step_ADDI (s := s1) (idx := 151) (by decide) rfl rfl
  let s2 := (s1.setReg .x5 (s1.getReg .x0 + signExtend12 1#12)).setPC (oPcAt 152)
  have h2 := o_step_ADDI (s := s2) (idx := 152) (by decide) rfl rfl
  let s3 := (s2.setReg .x10 (s2.getReg .x0 + signExtend12 0#12)).setPC (oPcAt 153)
  refine ⟨s3, (h0.trans h1).trans h2, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [s3, s2, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x5),
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, o_getReg_x0]; decide
  · simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, o_getReg_x0]; decide
  · have hx11_1 : s1.getReg .x11 = BitVec.ofNat 64 written.length := by
      simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx20, hx19]
      rw [o_bv_sub _ _ (by omega), Nat.add_sub_cancel_left]
    have hx11_3 : s3.getReg .x11 = BitVec.ofNat 64 written.length := by
      simp only [s3, s2, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x10 ≠ .x11),
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x5 ≠ .x11), hx11_1]
    rw [hx11_3, o_toNat_ofNat _ (by omega)]
  · intro addr; simp only [s3, s2, s1, o_getByte_setPC, o_getByte_setReg]

/-! ### 7. Position Loop: Salt Copy, 3-ary Climb, and Cap-Leaf Marking (`pc[23..79]`) -/

private theorem o_step_salt {s0 s : MachineState}
    {trapdoor : BitVec (8 * submission.sizes.trapdoor)} {positions : Positions}
    {ord : Nat} {written : List Byte} {m : Nat → Bool}
    (hs0 : s0 = submission.initialState .opening (trapdoor, positions))
    (hord : ord < positions.card) (hpc : s.pc = oPcAt 23)
    (hfix : OpenFixed positions s)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * ord))
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length))
    (hwLen8 : written.length % 8 = 0) (hwCap : written.length + 24 ≤ proofCap)
    (hro : OpenReadOnly s0 s) (hm : OpenMarks m s) (hw : OpenWritten written s) :
    let i := (positions.sort (· ≤ ·))[ord]'(by simpa using hord)
    let written' := written ++ bitsToBytes (tdSalt trapdoor i) 24
    ∃ s' : MachineState,
      OpenRuns s 20 20 s' ∧
      s'.pc = oPcAt 43 ∧
      OpenFixed positions s' ∧
      s'.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * (ord + 1)) ∧
      s'.getReg .x14 = BitVec.ofNat 64 i.val ∧
      s'.getReg .x20 = BitVec.ofNat 64 (11072966688 + written'.length) ∧
      OpenReadOnly s0 s' ∧
      OpenMarks m s' ∧
      OpenWritten written' s' := by
  intro i written'
  have hi_lt : i.val < 16777216 := i.isLt
  have hcard_le : positions.card ≤ 16777216 := o_card_le positions
  have hpc_cap : proofCap = 11140077536 := rfl
  have hro_eq := rowOff_eq
  have htd_eq := trapdoorBytes_eq
  have ha23 : s.getReg .x9 + signExtend12 0#12 = BitVec.ofNat 64 (6643781664 + 8 * ord) := by
    rw [hx9, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
  have hv23 : accessValid (s.getReg .x9 + signExtend12 0#12) 8 = true := by
    rw [ha23]; exact o_accessValid _ 8 (by omega) (by omega)
  have h23 := o_step_LD (s := s) (idx := 23) (by decide) hpc rfl hv23
  let t1 := (s.setReg .x14 (s.getMem (s.getReg .x9 + signExtend12 0#12))).setPC (oPcAt 24)
  have hx14_1 : t1.getReg .x14 = BitVec.ofNat 64 i.val := by
    simp only [t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, ha23]
    rw [hro.getMem_eq _ (by omega) (by omega) (by omega), hs0,
      opening_initial_index trapdoor positions ord hord]
    simp only [openingIndex, dif_pos hord, i]
  have h24 := o_step_ADDI (s := t1) (idx := 24) (by decide) rfl rfl
  let t2 := (t1.setReg .x9 (t1.getReg .x9 + signExtend12 8#12)).setPC (oPcAt 25)
  have h25 := o_step_SRLI (s := t2) (idx := 25) (by decide) rfl rfl
  let t3 := (t2.setReg .x6 (t2.getReg .x14 >>> (1#6 : BitVec 6).toNat)).setPC (oPcAt 26)
  have h26 := o_step_SLLI (s := t3) (idx := 26) (by decide) rfl rfl
  let t4 := (t3.setReg .x7 (t3.getReg .x6 <<< (7#6 : BitVec 6).toNat)).setPC (oPcAt 27)
  have h27 := o_step_SLLI (s := t4) (idx := 27) (by decide) rfl rfl
  let t5 := (t4.setReg .x15 (t4.getReg .x6 <<< (6#6 : BitVec 6).toNat)).setPC (oPcAt 28)
  have h28 := o_step_ADD (s := t5) (idx := 28) (by decide) rfl rfl
  let t6 := (t5.setReg .x7 (t5.getReg .x7 + t5.getReg .x15)).setPC (oPcAt 29)
  have h29 := o_step_SLLI (s := t6) (idx := 29) (by decide) rfl rfl
  let t7 := (t6.setReg .x15 (t6.getReg .x6 <<< (3#6 : BitVec 6).toNat)).setPC (oPcAt 30)
  have h30 := o_step_SUB (s := t7) (idx := 30) (by decide) rfl rfl
  let t8 := (t7.setReg .x7 (t7.getReg .x7 - t7.getReg .x15)).setPC (oPcAt 31)
  have h31 := o_step_ADD (s := t8) (idx := 31) (by decide) rfl rfl
  let t9 := (t8.setReg .x7 (t8.getReg .x23 + t8.getReg .x7)).setPC (oPcAt 32)
  have h32 := o_step_ADDI (s := t9) (idx := 32) (by decide) rfl rfl
  let t10 := (t9.setReg .x7 (t9.getReg .x7 + signExtend12 72#12)).setPC (oPcAt 33)
  have h33 := o_step_ANDI (s := t10) (idx := 33) (by decide) rfl rfl
  let t11 := (t10.setReg .x15 (t10.getReg .x14 &&& signExtend12 1#12)).setPC (oPcAt 34)
  have h34 := o_step_SLLI (s := t11) (idx := 34) (by decide) rfl rfl
  let t12 := (t11.setReg .x15 (t11.getReg .x15 <<< (4#6 : BitVec 6).toNat)).setPC (oPcAt 35)
  have h35 := o_step_ADD (s := t12) (idx := 35) (by decide) rfl rfl
  let t13 := (t12.setReg .x7 (t12.getReg .x7 + t12.getReg .x15)).setPC (oPcAt 36)
  have hrun_addr : OpenRuns s 13 13 t13 := by
    have a := ((h23.trans h24).trans (h25.trans h26)).trans ((h27.trans h28).trans (h29.trans h30))
    have b := ((h31.trans h32).trans (h33.trans h34)).trans h35
    simpa only [show 8 + 5 = 13 from rfl] using a.trans b
  have hreg13 : ∀ r, r ≠ .x14 → r ≠ .x9 → r ≠ .x6 → r ≠ .x7 → r ≠ .x15 →
      t13.getReg r = s.getReg r := fun r h14 h9 h6 h7 h15 => by
    simp only [t13, t12, t11, t10, t9, t8, t7, t6, t5, t4, t3, t2, t1,
      MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h7),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h15),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h6),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h9),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h14)]
  have hbyte13 : ∀ addr, t13.getByte addr = s.getByte addr := fun addr => by
    simp only [t13, t12, t11, t10, t9, t8, t7, t6, t5, t4, t3, t2, t1,
      o_getByte_setPC, o_getByte_setReg]
  have hx9_13 : t13.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * (ord + 1)) := by
    have h9_2 : t2.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * (ord + 1)) := by
      simp only [t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x14 ≠ .x9), hx9,
        show signExtend12 8#12 = BitVec.ofNat 64 8 by decide, o_bv_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    simp only [t13, t12, t11, t10, t9, t8, t7, t6, t5, t4, t3,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, h9_2]
  have hx14_13 : t13.getReg .x14 = BitVec.ofNat 64 i.val := by
    simp only [t13, t12, t11, t10, t9, t8, t7, t6, t5, t4, t3, t2,
      MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true,
      reduceCtorEq, hx14_1]
  have hx6_3 : t3.getReg .x6 = BitVec.ofNat 64 (i.val / 2) := by
    have h14_2 : t2.getReg .x14 = BitVec.ofNat 64 i.val := by
      simp only [t2, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x9 ≠ .x14), hx14_1]
    simp only [t3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h14_2, show (1#6 : BitVec 6).toNat = 1 by decide, o_bv_shr i.val 1 (by omega), Nat.pow_one]
  have hx7_10 : t10.getReg .x7 = BitVec.ofNat 64 (4294971424 + rowOff + 184 * (i.val / 2) + 72) := by
    have h7_4 : t4.getReg .x7 = BitVec.ofNat 64 (128 * (i.val / 2)) := by
      simp only [t4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        hx6_3, show (7#6 : BitVec 6).toNat = 7 by decide, o_bv_shl]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have h15_5 : t5.getReg .x15 = BitVec.ofNat 64 (64 * (i.val / 2)) := by
      simp only [t5, t4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6), hx6_3,
        show (6#6 : BitVec 6).toNat = 6 by decide, o_bv_shl]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have h7_6 : t6.getReg .x7 = BitVec.ofNat 64 (192 * (i.val / 2)) := by
      have h7_5 : t5.getReg .x7 = BitVec.ofNat 64 (128 * (i.val / 2)) := by
        simp only [t5, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x15 ≠ .x7), h7_4]
      simp only [t6, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h7_5, h15_5, o_bv_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have h15_7 : t7.getReg .x15 = BitVec.ofNat 64 (8 * (i.val / 2)) := by
      have h6_6 : t6.getReg .x6 = BitVec.ofNat 64 (i.val / 2) := by
        simp only [t6, t5, t4, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
          not_false_eq_true, reduceCtorEq, hx6_3]
      simp only [t7, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h6_6, show (3#6 : BitVec 6).toNat = 3 by decide, o_bv_shl]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have h7_8 : t8.getReg .x7 = BitVec.ofNat 64 (184 * (i.val / 2)) := by
      have h7_7 : t7.getReg .x7 = BitVec.ofNat 64 (192 * (i.val / 2)) := by
        simp only [t7, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x15 ≠ .x7), h7_6]
      simp only [t8, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h7_7, h15_7]
      rw [o_bv_sub _ _ (by omega)]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have h23_8 : t8.getReg .x23 = BitVec.ofNat 64 (4294971424 + rowOff) := by
      simp only [t8, t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x23]
    simp only [t10, t9, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h23_8, h7_8, show signExtend12 72#12 = BitVec.ofNat 64 72 by decide, o_bv_add]
  have hx15_12 : t12.getReg .x15 = BitVec.ofNat 64 (16 * (i.val % 2)) := by
    have h14_10 : t10.getReg .x14 = BitVec.ofNat 64 i.val := by
      simp only [t10, t9, t8, t7, t6, t5, t4, t3, t2, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne, ne_eq, not_false_eq_true, reduceCtorEq, hx14_1]
    simp only [t12, t11, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h14_10, o_bv_and1 i.val (by omega), show (4#6 : BitVec 6).toNat = 4 by decide, o_bv_shl]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hx7_13 : t13.getReg .x7 = BitVec.ofNat 64 (4294971424 + saltOff i) := by
    have h7_12 : t12.getReg .x7 = BitVec.ofNat 64 (4294971424 + rowOff + 184 * (i.val / 2) + 72) := by
      simp only [t12, t11, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, hx7_10]
    simp only [t13, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h7_12, hx15_12, o_bv_add]
    unfold saltOff PAIR_STRIDE
    split_ifs <;> exact congrArg (BitVec.ofNat 64) (by omega)
  have hsalt_bd : saltOff i + 24 ≤ 2348810240 := by
    simpa only [htd_eq] using saltOff_add_24_le i
  have hsalt_al : (4294971424 + saltOff i) % 8 = 0 := by
    unfold saltOff PAIR_STRIDE; rw [hro_eq]; split_ifs <;> omega
  have hx20_13 : t13.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length) :=
    (hreg13 .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20
  obtain ⟨s', hrc, hpc', hx20', hregc, hinc, houtc⟩ := o_copy_24 (s := t13)
    (src := 4294971424 + saltOff i) (dst := 11072966688 + written.length)
    rfl hx7_13 hx20_13 hsalt_al (by omega) (by omega) (by omega) (by omega)
  have hrun : OpenRuns s 20 20 s' := by
    simpa only [show 13 + 7 = 20 from rfl] using hrun_addr.trans hrc
  have hfix' : OpenFixed positions s' := {
    x8 := (hregc .x8 (by decide) (by decide)).trans ((hreg13 .x8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x8)
    x18 := (hregc .x18 (by decide) (by decide)).trans ((hreg13 .x18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x18)
    x19 := (hregc .x19 (by decide) (by decide)).trans ((hreg13 .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x19)
    x21 := (hregc .x21 (by decide) (by decide)).trans ((hreg13 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21)
    x22 := (hregc .x22 (by decide) (by decide)).trans ((hreg13 .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x22)
    x23 := (hregc .x23 (by decide) (by decide)).trans ((hreg13 .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x23)
    x24 := (hregc .x24 (by decide) (by decide)).trans ((hreg13 .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x24)
    x25 := (hregc .x25 (by decide) (by decide)).trans ((hreg13 .x25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x25)
    x27 := (hregc .x27 (by decide) (by decide)).trans ((hreg13 .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x27)
  }
  refine ⟨s', hrun, hpc', hfix',
    (hregc .x9 (by decide) (by decide)).trans hx9_13,
    (hregc .x14 (by decide) (by decide)).trans hx14_13,
    by simpa only [written', List.length_append, bitsToBytes_length, Nat.add_assoc] using hx20',
    ?_, ?_, ?_⟩
  · intro a ha1 ha2
    exact (houtc a (by omega) (by omega)).trans ((hbyte13 _).trans (hro a ha1 ha2))
  · intro u hu
    exact (houtc (4096 + u) (by omega) (by omega)).trans ((hbyte13 _).trans (hm u hu))
  · intro j hj
    by_cases hlt : j < written.length
    · rw [o_getElem_append_left _ _ j hlt]
      exact (houtc (11072966688 + j) (by omega) (by omega)).trans ((hbyte13 _).trans (hw j hlt))
    · have hge : written.length ≤ j := by omega
      rw [o_getElem_append_right _ _ j hge hj]
      have hk : j - written.length < 24 := by
        rw [List.length_append, bitsToBytes_length] at hj; omega
      rw [o_bitsToBytes_getElem _ 24 _ hk]
      have hc := hinc (j - written.length) hk
      have ha1 : 11072966688 + written.length + (j - written.length) = 11072966688 + j := by omega
      have ha2 : 4294971424 + saltOff i + (j - written.length) = 4294971424 + (saltOff i + (j - written.length)) := by omega
      rw [ha1, ha2] at hc
      have hb0 : s0.getByte (BitVec.ofNat 64 (4294971424 + (saltOff i + (j - written.length)))) =
          trapdoor.extractLsb' (8 * (saltOff i + (j - written.length))) 8 := by
        rw [hs0]
        exact opening_initial_trapdoor_byte trapdoor positions (saltOff i + (j - written.length)) (by omega)
      have hex : (tdSalt trapdoor i).extractLsb' (8 * (j - written.length)) 8 =
          trapdoor.extractLsb' (8 * (saltOff i + (j - written.length))) 8 :=
        o_extractLsb'_extractLsb' trapdoor (saltOff i) 24 (j - written.length) hk
      exact hc.trans ((hbyte13 _).trans ((hro _ (by omega) (by omega)).trans (hb0.trans hex.symm)))

/-- Copy 64 bytes (`stepSiblingsProof`) from `x16` and `x17` to `x20`, advancing `x20 += 64` (`pc[57..73]`). -/
private theorem o_copy_sibs {s0 s : MachineState}
    {trapdoor : BitVec (8 * submission.sizes.trapdoor)} {positions : Positions}
    {u0 u1 : Nat} {written : List Byte} {m : Nat → Bool}
    (hs0 : s0 = submission.initialState .opening (trapdoor, positions))
    (hpc : s.pc = oPcAt 57)
    (hx16 : s.getReg .x16 = BitVec.ofNat 64 (4294971424 + 32 * u0))
    (hx17 : s.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * u1))
    (hu0 : u0 < TREE_NODES) (hu1 : u1 < TREE_NODES)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length))
    (hwLen8 : written.length % 8 = 0) (hwCap : written.length + 64 ≤ proofCap)
    (hro : OpenReadOnly s0 s) (hm : OpenMarks m s) (hw : OpenWritten written s) :
    let chunk := bitsToBytes (tdNode trapdoor u0) 32 ++ bitsToBytes (tdNode trapdoor u1) 32
    ∃ s' : MachineState,
      OpenRuns s 17 17 s' ∧
      s'.pc = oPcAt 74 ∧
      s'.getReg .x20 = BitVec.ofNat 64 (11072966688 + (written ++ chunk).length) ∧
      (∀ r, r ≠ .x28 → r ≠ .x20 → s'.getReg r = s.getReg r) ∧
      OpenReadOnly s0 s' ∧
      OpenMarks m s' ∧
      OpenWritten (written ++ chunk) s' := by
  intro chunk
  have htn := treeNodes_eq
  have hpc_cap : proofCap = 11140077536 := rfl
  obtain ⟨s1, hr1, hp1, hreg1, hin1, hout1⟩ := o_copy_32_raw (s := s) (idx := 57) (tmp := .x28)
    (srcReg := .x16) (baseOff := 0) (dstOff := 0)
    (src := 4294971424 + 32 * u0) (dst := 11072966688 + written.length)
    (by decide) hpc (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide) hx16 hx20
    (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s2, hr2, hp2, hreg2, hin2, hout2⟩ := o_copy_32_raw (s := s1) (idx := 65) (tmp := .x28)
    (srcReg := .x17) (baseOff := 0) (dstOff := 32)
    (src := 4294971424 + 32 * u1) (dst := 11072966688 + written.length)
    (by decide) hp1 (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) (by decide) (by decide)
    ((hreg1 .x17 (by decide)).trans hx17) ((hreg1 .x20 (by decide)).trans hx20)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hst73 := o_step_ADDI (s := s2) (idx := 73) (rd := .x20) (rs1 := .x20) (imm := 64#12)
    (by decide) hp2 rfl
  let s3 := (s2.setReg .x20 (s2.getReg .x20 + signExtend12 64#12)).setPC (oPcAt 74)
  have hx20_2 : s2.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length) :=
    (hreg2 .x20 (by decide)).trans ((hreg1 .x20 (by decide)).trans hx20)
  have hrun : OpenRuns s 17 17 s3 := by
    simpa only [show 8 + 8 + 1 = 17 from rfl] using (hr1.trans hr2).trans hst73
  refine ⟨s3, hrun, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [s3, chunk, List.length_append, bitsToBytes_length, MachineState.getReg_setPC,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx20_2,
      show signExtend12 64#12 = BitVec.ofNat 64 64 by decide, o_bv_add, Nat.add_assoc]
  · intro r h28 h20
    simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h20)]
    exact (hreg2 r h28).trans (hreg1 r h28)
  · intro a ha1 ha2
    simp only [s3, o_getByte_setPC, o_getByte_setReg]
    exact (hout2 a (by omega) (by omega)).trans ((hout1 a (by omega) (by omega)).trans (hro a ha1 ha2))
  · intro u hu
    simp only [s3, o_getByte_setPC, o_getByte_setReg]
    exact (hout2 (4096 + u) (by omega) (by omega)).trans
      ((hout1 (4096 + u) (by omega) (by omega)).trans (hm u hu))
  · intro j hj
    simp only [s3, o_getByte_setPC, o_getByte_setReg]
    by_cases hlt : j < written.length
    · rw [o_getElem_append_left _ _ j hlt]
      exact (hout2 (11072966688 + j) (by omega) (by omega)).trans
        ((hout1 (11072966688 + j) (by omega) (by omega)).trans (hw j hlt))
    · have hge : written.length ≤ j := by omega
      rw [o_getElem_append_right _ _ j hge hj]
      have hk : j - written.length < 64 := by
        simp only [chunk, List.length_append, bitsToBytes_length] at hj; omega
      by_cases h32 : j - written.length < 32
      · rw [o_getElem_append_left _ _ (j - written.length) (by rw [bitsToBytes_length]; exact h32),
          o_bitsToBytes_getElem _ 32 _ h32]
        have h1 := hin1 (j - written.length) h32
        have ha1 : 11072966688 + written.length + 0 + (j - written.length) = 11072966688 + j := by omega
        have ha2 : 4294971424 + 32 * u0 + 0 + (j - written.length) =
            4294971424 + (32 * u0 + (j - written.length)) := by omega
        rw [ha1, ha2] at h1
        have h2 := hout2 (11072966688 + j) (by omega) (by omega)
        have hb0 : s0.getByte (BitVec.ofNat 64 (4294971424 + (32 * u0 + (j - written.length)))) =
            trapdoor.extractLsb' (8 * (32 * u0 + (j - written.length))) 8 := by
          rw [hs0]; exact opening_initial_trapdoor_byte trapdoor positions _ (by omega)
        have hex := o_extractLsb'_extractLsb' trapdoor (32 * u0) 32 (j - written.length) h32
        exact h2.trans (h1.trans ((hro _ (by omega) (by omega)).trans (hb0.trans hex.symm)))
      · have hge32 : (bitsToBytes (tdNode trapdoor u0) 32).length ≤ j - written.length := by
          rw [bitsToBytes_length]; omega
        rw [o_getElem_append_right _ _ (j - written.length) hge32
          (by simp only [chunk, List.length_append, bitsToBytes_length]; omega)]
        have hk2 : j - written.length - 32 < 32 := by omega
        simp only [bitsToBytes_length]
        rw [o_bitsToBytes_getElem _ 32 _ hk2]
        have h2 := hin2 (j - written.length - 32) hk2
        have ha1 : 11072966688 + written.length + 32 + (j - written.length - 32) = 11072966688 + j := by omega
        have ha2 : 4294971424 + 32 * u1 + 0 + (j - written.length - 32) =
            4294971424 + (32 * u1 + (j - written.length - 32)) := by omega
        rw [ha1, ha2] at h2
        have h1 := hout1 (4294971424 + (32 * u1 + (j - written.length - 32))) (by omega) (by omega)
        have hb0 : s0.getByte (BitVec.ofNat 64 (4294971424 + (32 * u1 + (j - written.length - 32)))) =
            trapdoor.extractLsb' (8 * (32 * u1 + (j - written.length - 32))) 8 := by
          rw [hs0]; exact opening_initial_trapdoor_byte trapdoor positions _ (by omega)
        have hex := o_extractLsb'_extractLsb' trapdoor (32 * u1) 32 (j - written.length - 32) hk2
        exact h2.trans (h1.trans ((hro _ (by omega) (by omega)).trans (hb0.trans hex.symm)))

/-- One 3-ary climb iteration (`pc[43..75]`): emits `stepSiblingsProof (tdNode trapdoor) v`,
advances `x14 := parentNode v`, and branches to `pc[43]` (if `< CAP_LEAF_LO`) or `pc[76]`. -/
private theorem o_step_climb_one {s0 s : MachineState}
    {trapdoor : BitVec (8 * submission.sizes.trapdoor)} {positions : Positions}
    {v ord : Nat} {written : List Byte} {m : Nat → Bool}
    (hs0 : s0 = submission.initialState .opening (trapdoor, positions))
    (hv : v < CAP_LEAF_LO) (hpc : s.pc = oPcAt 43)
    (hfix : OpenFixed positions s)
    (hx9 : s.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * ord))
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 v)
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length))
    (hwLen8 : written.length % 8 = 0) (hwCap : written.length + 64 ≤ proofCap)
    (hro : OpenReadOnly s0 s) (hm : OpenMarks m s) (hw : OpenWritten written s) :
    let written' := written ++ stepSiblingsProof (tdNode trapdoor) v
    ∃ steps cycles s',
      steps ≤ 31 ∧ cycles ≤ 34 ∧
      OpenRuns s steps cycles s' ∧
      s'.pc = (if parentNode v < CAP_LEAF_LO then oPcAt 43 else oPcAt 76) ∧
      OpenFixed positions s' ∧
      s'.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * ord) ∧
      s'.getReg .x14 = BitVec.ofNat 64 (parentNode v) ∧
      s'.getReg .x20 = BitVec.ofNat 64 (11072966688 + written'.length) ∧
      OpenReadOnly s0 s' ∧
      OpenMarks m s' ∧
      OpenWritten written' s' := by
  intro written'
  have hcl := capLeafLo_eq
  have htn := treeNodes_eq
  have hlen : LENGTH = 16777216 := by decide
  let q := v / 3
  let t := 3 * q
  let r := v % 3
  have hv_eq : t + r = v := by omega
  have hr_lt : r < 3 := by omega
  have ht2_lt : t + 2 < TREE_NODES := by omega
  -- pc[43..50]: DIVU, SLLI, ADD, SUB, SLLI, ADD, ADDI x16, ADDI x17 (8 steps, 11 cycles)
  have h43 := o_step_DIVU (s := s) (idx := 43) (by decide) hpc rfl
  let a1 := (s.setReg .x6 (rv64_divu (s.getReg .x14) (s.getReg .x25))).setPC (oPcAt 44)
  have h44 := o_step_SLLI (s := a1) (idx := 44) (by decide) rfl rfl
  let a2 := (a1.setReg .x7 (a1.getReg .x6 <<< (1#6 : BitVec 6).toNat)).setPC (oPcAt 45)
  have h45 := o_step_ADD (s := a2) (idx := 45) (by decide) rfl rfl
  let a3 := (a2.setReg .x7 (a2.getReg .x7 + a2.getReg .x6)).setPC (oPcAt 46)
  have h46 := o_step_SUB (s := a3) (idx := 46) (by decide) rfl rfl
  let a4 := (a3.setReg .x15 (a3.getReg .x14 - a3.getReg .x7)).setPC (oPcAt 47)
  have h47 := o_step_SLLI (s := a4) (idx := 47) (by decide) rfl rfl
  let a5 := (a4.setReg .x7 (a4.getReg .x7 <<< (5#6 : BitVec 6).toNat)).setPC (oPcAt 48)
  have h48 := o_step_ADD (s := a5) (idx := 48) (by decide) rfl rfl
  let a6 := (a5.setReg .x7 (a5.getReg .x8 + a5.getReg .x7)).setPC (oPcAt 49)
  have h49 := o_step_ADDI (s := a6) (idx := 49) (by decide) rfl rfl
  let a7 := (a6.setReg .x16 (a6.getReg .x7 + signExtend12 0#12)).setPC (oPcAt 50)
  have h50 := o_step_ADDI (s := a7) (idx := 50) (by decide) rfl rfl
  let a8 := (a7.setReg .x17 (a7.getReg .x7 + signExtend12 64#12)).setPC (oPcAt 51)
  have hrun_a : OpenRuns s 8 11 a8 := by
    have p1 := (h43.trans h44).trans (h45.trans h46)
    have p2 := (h47.trans h48).trans (h49.trans h50)
    simpa only [show 4 + 4 = 8 from rfl, show 7 + 4 = 11 from rfl] using p1.trans p2
  have hreg_a : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x15 → reg ≠ .x16 → reg ≠ .x17 →
      a8.getReg reg = s.getReg reg := fun reg h6 h7 h15 h16 h17 => by
    simp only [a8, a7, a6, a5, a4, a3, a2, a1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h17),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h16),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h7),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h15),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h6)]
  have hbyte_a : ∀ addr, a8.getByte addr = s.getByte addr := fun addr => by
    simp only [a8, a7, a6, a5, a4, a3, a2, a1, o_getByte_setPC, o_getByte_setReg]
  have hx6_a1 : a1.getReg .x6 = BitVec.ofNat 64 q := by
    simp only [a1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      hx14, hfix.x25]
    change rv64_divu (BitVec.ofNat 64 v) 3#64 = _
    rw [rv64_divu_three, o_toNat_ofNat v (by omega)]
  have hx6_a8 : a8.getReg .x6 = BitVec.ofNat 64 q := by
    simp only [a8, a7, a6, a5, a4, a3, a2, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, hx6_a1]
  have hx7_a3 : a3.getReg .x7 = BitVec.ofNat 64 t := by
    have h7_2 : a2.getReg .x7 = BitVec.ofNat 64 (2 * q) := by
      simp only [a2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        hx6_a1, show (1#6 : BitVec 6).toNat = 1 by decide, o_bv_shl]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have h6_2 : a2.getReg .x6 = BitVec.ofNat 64 q := by
      simp only [a2, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x6), hx6_a1]
    simp only [a3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h7_2, h6_2, o_bv_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hx15_a8 : a8.getReg .x15 = BitVec.ofNat 64 r := by
    have h14_3 : a3.getReg .x14 = BitVec.ofNat 64 v := by
      simp only [a3, a2, a1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq, hx14]
    have h15_4 : a4.getReg .x15 = BitVec.ofNat 64 r := by
      simp only [a4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h14_3, hx7_a3]
      rw [o_bv_sub _ _ (by omega)]
      exact congrArg (BitVec.ofNat 64) (by omega)
    simp only [a8, a7, a6, a5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, h15_4]
  have hx7_a6 : a6.getReg .x7 = BitVec.ofNat 64 (4294971424 + 32 * t) := by
    have h7_4 : a4.getReg .x7 = BitVec.ofNat 64 t := by
      simp only [a4, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x15 ≠ .x7), hx7_a3]
    have h7_5 : a5.getReg .x7 = BitVec.ofNat 64 (32 * t) := by
      simp only [a5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h7_4, show (5#6 : BitVec 6).toNat = 5 by decide, o_bv_shl]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have h8_5 : a5.getReg .x8 = BitVec.ofNat 64 4294971424 := by
      simp only [a5, a4, a3, a2, a1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
        ne_eq, not_false_eq_true, reduceCtorEq, hfix.x8]
    simp only [a6, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h8_5, h7_5, o_bv_add]
  have hx7_a8 : a8.getReg .x7 = BitVec.ofNat 64 (4294971424 + 32 * t) := by
    simp only [a8, a7, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, hx7_a6]
  have hx16_a8 : a8.getReg .x16 = BitVec.ofNat 64 (4294971424 + 32 * t) := by
    have h16_7 : a7.getReg .x16 = BitVec.ofNat 64 (4294971424 + 32 * t) := by
      simp only [a7, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        hx7_a6, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
    simp only [a8, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x17 ≠ .x16), h16_7]
  have hx17_a8 : a8.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * (t + 2)) := by
    have h7_7 : a7.getReg .x7 = BitVec.ofNat 64 (4294971424 + 32 * t) := by
      simp only [a7, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x16 ≠ .x7), hx7_a6]
    simp only [a8, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h7_7, show signExtend12 64#12 = BitVec.ofNat 64 64 by decide, o_bv_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  -- pc[51..56]: select sibling pair (u0, u1) based on r = v % 3 (3 or 4 steps)
  let u0 := if r = 0 then t + 1 else t
  let u1 := if r = 0 then t + 2 else if r = 1 then t + 2 else t + 1
  have hsel : ∃ ksel b, ksel ≤ 4 ∧ OpenRuns a8 ksel ksel b ∧ b.pc = oPcAt 57 ∧
      b.getReg .x16 = BitVec.ofNat 64 (4294971424 + 32 * u0) ∧
      b.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * u1) ∧
      (∀ reg, reg ≠ .x15 → reg ≠ .x16 → reg ≠ .x17 → b.getReg reg = a8.getReg reg) ∧
      (∀ addr, b.getByte addr = a8.getByte addr) := by
    by_cases hr0 : r = 0
    · have h51 := o_step_BNE_not_taken (s := a8) (idx := 51) (by decide) rfl rfl
        (by rw [hx15_a8, hr0, o_getReg_x0])
      let b1 := a8.setPC (oPcAt 52)
      have h52 := o_step_ADDI (s := b1) (idx := 52) (by decide) rfl rfl
      let b2 := (b1.setReg .x16 (b1.getReg .x7 + signExtend12 32#12)).setPC (oPcAt 53)
      have h53 := o_step_JAL_x0 (s := b2) (idx := 53) (tgt := 57) (by decide) rfl rfl o_tgt_53
      let b3 := b2.setPC (oPcAt 57)
      refine ⟨3, b3, by omega, (h51.trans h52).trans h53, rfl, ?_, ?_, ?_, ?_⟩
      · simp only [b3, b2, b1, u0, hr0, ite_true, MachineState.getReg_setPC,
          MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx7_a8,
          show signExtend12 32#12 = BitVec.ofNat 64 32 by decide, o_bv_add]
        exact congrArg (BitVec.ofNat 64) (by omega)
      · simp only [b3, b2, b1, u1, hr0, ite_true, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x16 ≠ .x17), hx17_a8]
      · intro reg _ h16 _
        simp only [b3, b2, b1, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h16)]
      · intro addr; simp only [b3, b2, b1, o_getByte_setPC, o_getByte_setReg]
    · have h51 := o_step_BNE_taken (s := a8) (idx := 51) (tgt := 54) (by decide) rfl rfl
        (by rw [hx15_a8, o_getReg_x0]; exact o_bv_ne (by omega) (by omega) hr0) o_tgt_51
      let b1 := a8.setPC (oPcAt 54)
      have h54 := o_step_ADDI (s := b1) (idx := 54) (by decide) rfl rfl
      let b2 := (b1.setReg .x15 (b1.getReg .x15 + signExtend12 4095#12)).setPC (oPcAt 55)
      have hx15_b2 : b2.getReg .x15 = BitVec.ofNat 64 (r - 1) := by
        simp only [b2, b1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hx15_a8]
        have hr_eq : r = (r - 1) + 1 := by omega
        rw [hr_eq]; exact o_bv_add_neg1 (r - 1)
      by_cases hr1 : r = 1
      · have h55 := o_step_BEQ_taken (s := b2) (idx := 55) (tgt := 57) (by decide) rfl rfl
          (by rw [hx15_b2, hr1, o_getReg_x0]) o_tgt_55
        let b3 := b2.setPC (oPcAt 57)
        refine ⟨3, b3, by omega, (h51.trans h54).trans h55, rfl, ?_, ?_, ?_, ?_⟩
        · simp only [b3, b2, b1, u0, hr0, ite_false, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x15 ≠ .x16), hx16_a8]
        · simp only [b3, b2, b1, u1, hr1, ite_true, ite_self, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x15 ≠ .x17), hx17_a8]
        · intro reg h15 _ _
          simp only [b3, b2, b1, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h15)]
        · intro addr; simp only [b3, b2, b1, o_getByte_setPC, o_getByte_setReg]
      · have hr2 : r = 2 := by omega
        have h55 := o_step_BEQ_not_taken (s := b2) (idx := 55) (by decide) rfl rfl
          (by rw [hx15_b2, hr2, o_getReg_x0]; decide)
        let b3 := b2.setPC (oPcAt 56)
        have h56 := o_step_ADDI (s := b3) (idx := 56) (by decide) rfl rfl
        let b4 := (b3.setReg .x17 (b3.getReg .x7 + signExtend12 32#12)).setPC (oPcAt 57)
        refine ⟨4, b4, by omega, ((h51.trans h54).trans h55).trans h56, rfl, ?_, ?_, ?_, ?_⟩
        · simp only [b4, b3, b2, b1, u0, hr0, ite_false, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x17 ≠ .x16),
            MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x15 ≠ .x16), hx16_a8]
        · simp only [b4, b3, b2, b1, u1, hr0, hr1, ite_false, MachineState.getReg_setPC,
            MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
            MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x15 ≠ .x7), hx7_a8,
            show signExtend12 32#12 = BitVec.ofNat 64 32 by decide, o_bv_add]
          exact congrArg (BitVec.ofNat 64) (by omega)
        · intro reg h15 _ h17
          simp only [b4, b3, b2, b1, MachineState.getReg_setPC,
            MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h17),
            MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h15)]
        · intro addr; simp only [b4, b3, b2, b1, o_getByte_setPC, o_getByte_setReg]
  obtain ⟨ksel, b, hksel, hrun_sel, hpc_b, hx16_b, hx17_b, hreg_b, hbyte_b⟩ := hsel
  have hchunk_eq : bitsToBytes (tdNode trapdoor u0) 32 ++ bitsToBytes (tdNode trapdoor u1) 32 =
      stepSiblingsProof (tdNode trapdoor) v := by
    unfold stepSiblingsProof; dsimp only [u0, u1, t, q, r]
    split_ifs <;> rfl
  have hu0_lt : u0 < TREE_NODES := by dsimp only [u0]; split_ifs <;> omega
  have hu1_lt : u1 < TREE_NODES := by dsimp only [u1]; split_ifs <;> omega
  have hx20_b : b.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length) :=
    (hreg_b .x20 (by decide) (by decide) (by decide)).trans
      ((hreg_a .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx20)
  obtain ⟨c, hrun_c, hpc_c, hx20_c, hreg_c, hro_c, hm_c, hw_c⟩ := o_copy_sibs hs0 hpc_b hx16_b hx17_b
    hu0_lt hu1_lt hx20_b hwLen8 hwCap
    (fun a ha1 ha2 => (hbyte_b _).trans ((hbyte_a _).trans (hro a ha1 ha2)))
    (fun u hu => (hbyte_b _).trans ((hbyte_a _).trans (hm u hu)))
    (fun j hj => (hbyte_b _).trans ((hbyte_a _).trans (hw j hj)))
  -- pc[74]: ADD x14, x21, x6 -> parentNode v
  have h74 := o_step_ADD (s := c) (idx := 74) (by decide) hpc_c rfl
  let d := (c.setReg .x14 (c.getReg .x21 + c.getReg .x6)).setPC (oPcAt 75)
  have hreg_d : ∀ reg, reg ≠ .x6 → reg ≠ .x7 → reg ≠ .x14 → reg ≠ .x15 → reg ≠ .x16 →
      reg ≠ .x17 → reg ≠ .x20 → reg ≠ .x28 → d.getReg reg = s.getReg reg :=
    fun reg h6 h7 h14 h15 h16 h17 h20 h28 => by
      simp only [d, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h14)]
      exact (hreg_c reg h28 h20).trans
        ((hreg_b reg h15 h16 h17).trans (hreg_a reg h6 h7 h15 h16 h17))
  have hx14_d : d.getReg .x14 = BitVec.ofNat 64 (parentNode v) := by
    have h21_c : c.getReg .x21 = BitVec.ofNat 64 LENGTH :=
      (hreg_c .x21 (by decide) (by decide)).trans
        ((hreg_b .x21 (by decide) (by decide) (by decide)).trans
          ((hreg_a .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21))
    have h6_c : c.getReg .x6 = BitVec.ofNat 64 q :=
      (hreg_c .x6 (by decide) (by decide)).trans
        ((hreg_b .x6 (by decide) (by decide) (by decide)).trans hx6_a8)
    simp only [d, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h21_c, h6_c, o_bv_add]; rfl
  have hx22_d : d.getReg .x22 = BitVec.ofNat 64 CAP_LEAF_LO :=
    (hreg_d .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x22
  have hpar_lt : parentNode v < 2 ^ 64 := by unfold parentNode; omega
  -- pc[75]: standalone isolated backward branch BLTU x14, x22, -128
  let s' := d.setPC (if parentNode v < CAP_LEAF_LO then oPcAt 43 else oPcAt 76)
  have h75 : OpenRuns d 1 1 s' := by
    by_cases hlt : parentNode v < CAP_LEAF_LO
    · simpa only [s', hlt, ite_true] using o_step_75_back (s := d) rfl hx14_d hx22_d hlt
    · simpa only [s', hlt, ite_false] using o_step_75_done (s := d) rfl hx14_d hx22_d hpar_lt (by omega)
  have hrun_all := (((hrun_a.trans hrun_sel).trans hrun_c).trans h74).trans h75
  have hfix' : OpenFixed positions s' := {
    x8 := (o_getReg_setPC d _ .x8).trans ((hreg_d .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x8)
    x18 := (o_getReg_setPC d _ .x18).trans ((hreg_d .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x18)
    x19 := (o_getReg_setPC d _ .x19).trans ((hreg_d .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x19)
    x21 := (o_getReg_setPC d _ .x21).trans ((hreg_d .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21)
    x22 := (o_getReg_setPC d _ .x22).trans hx22_d
    x23 := (o_getReg_setPC d _ .x23).trans ((hreg_d .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x23)
    x24 := (o_getReg_setPC d _ .x24).trans ((hreg_d .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x24)
    x25 := (o_getReg_setPC d _ .x25).trans ((hreg_d .x25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x25)
    x27 := (o_getReg_setPC d _ .x27).trans ((hreg_d .x27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x27)
  }
  refine ⟨8 + ksel + 17 + 1 + 1, 11 + ksel + 17 + 1 + 1, s', by omega, by omega, hrun_all, rfl,
    hfix',
    (o_getReg_setPC d _ .x9).trans ((hreg_d .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hx9),
    (o_getReg_setPC d _ .x14).trans hx14_d,
    ?_, ?_, ?_, ?_⟩
  · simp only [s', d, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x14 ≠ .x20)]
    simpa only [written', hchunk_eq] using hx20_c
  · intro a ha1 ha2; simp only [s', d, o_getByte_setPC, o_getByte_setReg]; exact hro_c a ha1 ha2
  · intro u hu; simp only [s', d, o_getByte_setPC, o_getByte_setReg]; exact hm_c u hu
  · intro j hj; simp only [s', d, o_getByte_setPC, o_getByte_setReg]
    simpa only [written', hchunk_eq] using hw_c j (by simpa only [written', hchunk_eq] using hj)

/-- Complete 3-ary climb loop (`pc[43..75]`) from any `v < CAP_LEAF_LO` to `climbEndFrom v`. -/
private theorem o_climb_loop {s0 : MachineState}
    {trapdoor : BitVec (8 * submission.sizes.trapdoor)} {positions : Positions}
    {ord : Nat} {m : Nat → Bool}
    (hs0 : s0 = submission.initialState .opening (trapdoor, positions))
    (n : Nat) :
    ∀ (v : Nat) (s : MachineState) (written : List Byte),
      v < CAP_LEAF_LO →
      climbStepsFrom v = n →
      s.pc = oPcAt 43 →
      OpenFixed positions s →
      s.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * ord) →
      s.getReg .x14 = BitVec.ofNat 64 v →
      s.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length) →
      written.length % 8 = 0 →
      written.length + 64 * n ≤ proofCap →
      OpenReadOnly s0 s →
      OpenMarks m s →
      OpenWritten written s →
      let written' := written ++ climbProofFrom (tdNode trapdoor) v
      ∃ steps cycles s',
        steps ≤ 31 * n ∧ cycles ≤ 34 * n ∧
        OpenRuns s steps cycles s' ∧
        s'.pc = oPcAt 76 ∧
        OpenFixed positions s' ∧
        s'.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * ord) ∧
        s'.getReg .x14 = BitVec.ofNat 64 (climbEndFrom v) ∧
        s'.getReg .x20 = BitVec.ofNat 64 (11072966688 + written'.length) ∧
        OpenReadOnly s0 s' ∧
        OpenMarks m s' ∧
        OpenWritten written' s' := by
  induction n with
  | zero =>
    intro v _ _ hv hsteps
    rw [climbStepsFrom_of_lt hv] at hsteps
    omega
  | succ k ih =>
    intro v s written hv hsteps hpc hfix hx9 hx14 hx20 hw8 hwCap hro hm hw
    have hsteps_par : climbStepsFrom (parentNode v) = k := by
      rw [climbStepsFrom_of_lt hv] at hsteps; omega
    obtain ⟨st1, cy1, s1, hst1, hcy1, hr1, hpc1, hfix1, hx9_1, hx14_1, hx20_1, hro1, hm1, hw1⟩ :=
      o_step_climb_one hs0 hv hpc hfix hx9 hx14 hx20 hw8 (by omega) hro hm hw
    by_cases hpar : parentNode v < CAP_LEAF_LO
    · rw [if_pos hpar] at hpc1
      have hw1_8 : (written ++ stepSiblingsProof (tdNode trapdoor) v).length % 8 = 0 := by
        rw [List.length_append, stepSiblingsProof_length]; omega
      have hw1_cap : (written ++ stepSiblingsProof (tdNode trapdoor) v).length + 64 * k ≤ proofCap := by
        rw [List.length_append, stepSiblingsProof_length]; omega
      obtain ⟨st2, cy2, s2, hst2, hcy2, hr2, hpc2, hfix2, hx9_2, hx14_2, hx20_2, hro2, hm2, hw2⟩ :=
        ih (parentNode v) s1 (written ++ stepSiblingsProof (tdNode trapdoor) v) hpar hsteps_par
          hpc1 hfix1 hx9_1 hx14_1 hx20_1 hw1_8 hw1_cap hro1 hm1 hw1
      have hpf : written ++ stepSiblingsProof (tdNode trapdoor) v ++
          climbProofFrom (tdNode trapdoor) (parentNode v) =
          written ++ climbProofFrom (tdNode trapdoor) v := by
        rw [List.append_assoc, ← climbProofFrom_of_lt (tdNode trapdoor) hv]
      have hend : climbEndFrom (parentNode v) = climbEndFrom v :=
        (climbEndFrom_of_lt hv).symm
      refine ⟨st1 + st2, cy1 + cy2, s2, by omega, by omega, hr1.trans hr2, hpc2, hfix2, hx9_2,
        by rwa [hend] at hx14_2, by rwa [hpf] at hx20_2, hro2, hm2, by rwa [hpf] at hw2⟩
    · rw [if_neg hpar] at hpc1
      have hpar_ge : CAP_LEAF_LO ≤ parentNode v := by omega
      have hk0 : k = 0 := by rw [climbStepsFrom_of_ge hpar_ge] at hsteps_par; omega
      have hpf : written ++ stepSiblingsProof (tdNode trapdoor) v =
          written ++ climbProofFrom (tdNode trapdoor) v := by
        rw [climbProofFrom_of_lt (tdNode trapdoor) hv, climbProofFrom_of_ge (tdNode trapdoor) hpar_ge,
          List.append_nil]
      have hend : parentNode v = climbEndFrom v := by
        rw [climbEndFrom_of_lt hv, climbEndFrom_of_ge hpar_ge]
      refine ⟨st1, cy1, s1, by omega, by omega, hr1, hpc1, hfix1, hx9_1,
        by rwa [hend] at hx14_1, by rwa [hpf] at hx20_1, hro1, hm1, by rwa [hpf] at hw1⟩

private def openPosMark (positions : Positions) (n u : Nat) : Bool :=
  decide (u < 286 ∧ ∃ ord < n, ∃ h : ord < positions.card,
    capLeafOf ((positions.sort (· ≤ ·))[ord]'(by simpa using h)) = u)

private def openPosWritten (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (n : Nat) : List Byte :=
  ((positions.sort (· ≤ ·)).take n).flatMap (recordProof nodes salts)

private theorem openPosWritten_zero (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) : openPosWritten nodes salts positions 0 = [] := by
  simp [openPosWritten]

private theorem openPosWritten_succ (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (n : Nat) (hn : n < positions.card) :
    openPosWritten nodes salts positions (n + 1) =
      openPosWritten nodes salts positions n ++
        recordProof nodes salts ((positions.sort (· ≤ ·))[n]'(by simpa using hn)) := by
  unfold openPosWritten
  have hlt : n < (positions.sort (· ≤ ·)).length := by simpa using hn
  rw [List.take_succ_eq_append_getElem hlt, List.flatMap_append, List.flatMap_singleton]

private theorem openPosWritten_length_mod8 (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (n : Nat) :
    (openPosWritten nodes salts positions n).length % 8 = 0 := by
  unfold openPosWritten
  rw [List.length_flatMap]
  induction (positions.sort (· ≤ ·)).take n with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hrec : (recordProof nodes salts a).length % 8 = 0 := by
      unfold recordProof
      rw [List.length_append, bitsToBytes_length, climbProofFrom_length]
      omega
    omega

private theorem openPosWritten_length_le (nodes : Nat → Digest) (salts : Index → Salt192)
    (positions : Positions) (n : Nat) (hn : n ≤ positions.card) :
    (openPosWritten nodes salts positions n).length ≤ 664 * n := by
  induction n with
  | zero => simp [openPosWritten]
  | succ k ih =>
    rw [openPosWritten_succ nodes salts positions k (by omega), List.length_append]
    have h1 := ih (by omega)
    have h2 := recordProof_length_le_664 nodes salts ((positions.sort (· ≤ ·))[k]'(by rw [Finset.length_sort]; omega))
    omega

private theorem openPosMark_zero (positions : Positions) (u : Nat) :
    openPosMark positions 0 u = false := by
  simp [openPosMark]

private theorem openPosMark_succ (positions : Positions) (n : Nat) (hn : n < positions.card) (u : Nat) :
    openPosMark positions (n + 1) u =
      (if u = capLeafOf ((positions.sort (· ≤ ·))[n]'(by simpa using hn))
       then true else openPosMark positions n u) := by
  let c := capLeafOf ((positions.sort (· ≤ ·))[n]'(by simpa using hn))
  have hc_lt : c < 286 := by rw [← capLeaves_eq]; exact capLeafOf_lt _
  by_cases hu : u = c
  · rw [hu, if_pos rfl]
    simp only [openPosMark, decide_eq_true_eq]
    exact ⟨hc_lt, n, by omega, hn, rfl⟩
  · rw [if_neg hu]
    apply Bool.eq_iff_iff.mpr
    simp only [openPosMark, decide_eq_true_eq]
    constructor
    · rintro ⟨hlt, ord, hord1, hord2, heq⟩
      refine ⟨hlt, ord, ?_, hord2, heq⟩
      by_cases he : ord = n
      · subst he; exact (hu heq.symm).elim
      · omega
    · rintro ⟨hlt, ord, hord1, hord2, heq⟩
      exact ⟨hlt, ord, by omega, hord2, heq⟩

/-- Full position loop (`ord = 0 .. positions.card`, `pc[23..79]`). -/
private theorem o_pos_loop {s0 : MachineState}
    {trapdoor : BitVec (8 * submission.sizes.trapdoor)} {positions : Positions}
    (hs0 : s0 = submission.initialState .opening (trapdoor, positions))
    (hne : positions.card ≠ 0) (sInit : MachineState)
    (hpc0 : sInit.pc = oPcAt 23) (hfix0 : OpenFixed positions sInit)
    (hx9_0 : sInit.getReg .x9 = BitVec.ofNat 64 6643781664)
    (hx20_0 : sInit.getReg .x20 = BitVec.ofNat 64 11072966688)
    (hro0 : OpenReadOnly s0 sInit) (hm0 : OpenMarks (fun _ => false) sInit)
    (hw0 : OpenWritten [] sInit) :
    ∀ n ≤ positions.card,
      ∃ steps cycles sn,
        steps ≤ 334 * n ∧ cycles ≤ 364 * n ∧
        OpenRuns sInit steps cycles sn ∧
        sn.pc = (if n = positions.card then oPcAt 80 else oPcAt 23) ∧
        OpenFixed positions sn ∧
        sn.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * n) ∧
        sn.getReg .x20 = BitVec.ofNat 64
          (11072966688 + (openPosWritten (tdNode trapdoor) (tdSalt trapdoor) positions n).length) ∧
        OpenReadOnly s0 sn ∧
        OpenMarks (openPosMark positions n) sn ∧
        OpenWritten (openPosWritten (tdNode trapdoor) (tdSalt trapdoor) positions n) sn := by
  have hcard_le : positions.card ≤ 16777216 := o_card_le positions
  have hpc_cap : proofCap = 11140077536 := rfl
  have hcl := capLeafLo_eq
  intro n hn
  induction n with
  | zero =>
    refine ⟨0, 0, sInit, Nat.zero_le _, Nat.zero_le _, OpenRuns.refl sInit,
      by simp [Ne.symm hne, hpc0], hfix0, by simpa using hx9_0,
      by simpa [openPosWritten_zero] using hx20_0, hro0,
      fun u hu => by rw [openPosMark_zero]; exact hm0 u hu,
      by simpa [openPosWritten_zero] using hw0⟩
  | succ k ih =>
    obtain ⟨stK, cyK, sk, hstK, hcyK, hrK, hpcK, hfixK, hx9K, hx20K, hroK, hmK, hwK⟩ := ih (by omega)
    have hpc23 : sk.pc = oPcAt 23 := by rwa [if_neg (by omega : k ≠ positions.card)] at hpcK
    let i := (positions.sort (· ≤ ·))[k]'(by rw [Finset.length_sort]; omega)
    let wK := openPosWritten (tdNode trapdoor) (tdSalt trapdoor) positions k
    have hwK_8 : wK.length % 8 = 0 := openPosWritten_length_mod8 _ _ positions k
    have hwK_le : wK.length ≤ 664 * k := openPosWritten_length_le _ _ positions k (by omega)
    -- Step 1: salt copy (20 steps, 20 cycles)
    obtain ⟨s1, hr1, hpc1, hfix1, hx9_1, hx14_1, hx20_1, hro1, hm1, hw1⟩ :=
      o_step_salt hs0 (by omega) hpc23 hfixK hx9K hx20K hwK_8
        (by change wK.length + 24 ≤ proofCap; omega) hroK hmK hwK
    -- Step 2: 3-ary climb loop (≤ 310 steps, ≤ 340 cycles)
    have hi_lt : i.val < CAP_LEAF_LO := by
      have h1 : i.val < 16777216 := i.isLt; rw [capLeafLo_eq]; omega
    have hcs_le : climbStepsFrom i.val ≤ 10 := climbStepsFrom_le_10 i.val
    have hw1_8 : (wK ++ bitsToBytes (tdSalt trapdoor i) 24).length % 8 = 0 := by
      rw [List.length_append, bitsToBytes_length]; omega
    have hw1_cap : (wK ++ bitsToBytes (tdSalt trapdoor i) 24).length + 64 * climbStepsFrom i.val ≤ proofCap := by
      rw [List.length_append, bitsToBytes_length]; omega
    obtain ⟨stC, cyC, s2, hstC, hcyC, hrC, hpc2, hfix2, hx9_2, hx14_2, hx20_2, hro2, hm2, hw2⟩ :=
      o_climb_loop hs0 (climbStepsFrom i.val) i.val s1 (wK ++ bitsToBytes (tdSalt trapdoor i) 24)
        hi_lt rfl hpc1 hfix1 hx9_1 hx14_1 hx20_1 hw1_8 hw1_cap hro1 hm1 hw1
    -- Step 3: pc[76..78]: mark capLeafOf i (3 steps, 3 cycles)
    have h76 := o_step_SUB (s := s2) (idx := 76) (by decide) hpc2 rfl
    let s3 := (s2.setReg .x14 (s2.getReg .x14 - s2.getReg .x22)).setPC (oPcAt 77)
    have h77 := o_step_ADD (s := s3) (idx := 77) (by decide) rfl rfl
    let s4 := (s3.setReg .x6 (s3.getReg .x24 + s3.getReg .x14)).setPC (oPcAt 78)
    have hc_lt : capLeafOf i < 286 := by rw [← capLeaves_eq]; exact capLeafOf_lt i
    have hx14_3 : s3.getReg .x14 = BitVec.ofNat 64 (capLeafOf i) := by
      simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        hx14_2, hfix2.x22, climbEndFrom_eq_capLeafOf i]
      rw [o_bv_sub _ _ (by omega), Nat.add_sub_cancel_left]
    have hx6_4 : s4.getReg .x6 = BitVec.ofNat 64 (4096 + capLeafOf i) := by
      have h24_3 : s3.getReg .x24 = BitVec.ofNat 64 4096 := by
        simp only [s3, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x14 ≠ .x24), hfix2.x24]
      simp only [s4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h24_3, hx14_3, o_bv_add]
    have ha78 : s4.getReg .x6 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + capLeafOf i) := by
      rw [hx6_4, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
    have hv78 : accessValid (s4.getReg .x6 + signExtend12 0#12) 1 = true := by
      rw [ha78]; exact o_accessValid _ 1 (by omega) (by omega)
    have h78 := o_step_SB (s := s4) (idx := 78) (by decide) rfl rfl hv78
    let s5 := (s4.setByte (s4.getReg .x6 + signExtend12 0#12) ((s4.getReg .x27).truncate 8)).setPC (oPcAt 79)
    have hreg5 : ∀ r, r ≠ .x14 → r ≠ .x6 → s5.getReg r = s2.getReg r := fun r h14 h6 => by
      simp only [s5, s4, s3, MachineState.getReg_setPC, o_getReg_setByte,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h6),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h14)]
    -- Step 4: pc[79]: isolated backward branch BNE x9, x18, -224 (1 step, 1 cycle)
    let sn := s5.setPC (if k + 1 = positions.card then oPcAt 80 else oPcAt 23)
    have hx9_5 : s5.getReg .x9 = BitVec.ofNat 64 (6643781664 + 8 * (k + 1)) :=
      (hreg5 .x9 (by decide) (by decide)).trans hx9_2
    have hx18_5 : s5.getReg .x18 = BitVec.ofNat 64 (6643781664 + 8 * positions.card) :=
      (hreg5 .x18 (by decide) (by decide)).trans hfix2.x18
    have h79 : OpenRuns s5 1 1 sn := by
      by_cases hend : k + 1 = positions.card
      · simpa only [sn, hend, ite_true] using
          o_step_79_done (s := s5) rfl hx9_5 (by rwa [← hend] at hx18_5)
      · simpa only [sn, hend, ite_false] using
          o_step_79_back (s := s5) rfl hx9_5 hx18_5 (by omega) (by omega) (by omega)
    have hrun_all : OpenRuns sInit (stK + (20 + stC + 3 + 1)) (cyK + (20 + cyC + 3 + 1)) sn := by
      have hbody := ((hr1.trans hrC).trans ((h76.trans h77).trans h78)).trans h79
      simpa only [Nat.add_assoc] using hrK.trans hbody
    have hw_eq : wK ++ bitsToBytes (tdSalt trapdoor i) 24 ++ climbProofFrom (tdNode trapdoor) i.val =
        openPosWritten (tdNode trapdoor) (tdSalt trapdoor) positions (k + 1) := by
      rw [openPosWritten_succ _ _ positions k (by omega), List.append_assoc]; rfl
    have htrunc1 : (s4.getReg .x27).truncate 8 = 1#8 := by
      have h27 : s4.getReg .x27 = BitVec.ofNat 64 1 := by
        simp only [s4, s3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
          not_false_eq_true, reduceCtorEq, hfix2.x27]
      rw [h27]; decide
    have hfixN : OpenFixed positions sn := {
      x8 := (o_getReg_setPC s5 _ .x8).trans ((hreg5 .x8 (by decide) (by decide)).trans hfix2.x8)
      x18 := (o_getReg_setPC s5 _ .x18).trans hx18_5
      x19 := (o_getReg_setPC s5 _ .x19).trans ((hreg5 .x19 (by decide) (by decide)).trans hfix2.x19)
      x21 := (o_getReg_setPC s5 _ .x21).trans ((hreg5 .x21 (by decide) (by decide)).trans hfix2.x21)
      x22 := (o_getReg_setPC s5 _ .x22).trans ((hreg5 .x22 (by decide) (by decide)).trans hfix2.x22)
      x23 := (o_getReg_setPC s5 _ .x23).trans ((hreg5 .x23 (by decide) (by decide)).trans hfix2.x23)
      x24 := (o_getReg_setPC s5 _ .x24).trans ((hreg5 .x24 (by decide) (by decide)).trans hfix2.x24)
      x25 := (o_getReg_setPC s5 _ .x25).trans ((hreg5 .x25 (by decide) (by decide)).trans hfix2.x25)
      x27 := (o_getReg_setPC s5 _ .x27).trans ((hreg5 .x27 (by decide) (by decide)).trans hfix2.x27)
    }
    refine ⟨stK + (20 + stC + 3 + 1), cyK + (20 + cyC + 3 + 1), sn,
      by omega, by omega, hrun_all, rfl, hfixN,
      (o_getReg_setPC s5 _ .x9).trans hx9_5,
      ?_, ?_, ?_, ?_⟩
    · simp only [sn, MachineState.getReg_setPC]
      rw [hreg5 .x20 (by decide) (by decide), ← hw_eq]
      exact hx20_2
    · intro a ha1 ha2
      simp only [sn, s5, o_getByte_setPC, ha78, set_byte_read]
      rw [if_neg (o_bv_ne (by omega) (by omega) (by omega))]
      simp only [s4, s3, o_getByte_setPC, o_getByte_setReg]
      exact hro2 a ha1 ha2
    · intro u hu
      rw [openPosMark_succ positions k (by omega) u]
      simp only [sn, s5, o_getByte_setPC, ha78, htrunc1, set_byte_read]
      by_cases hueq : u = capLeafOf i
      · rw [hueq]; simp [i]
      · rw [if_neg (o_bv_ne (by omega) (by omega) (by omega)), if_neg hueq]
        simp only [s4, s3, o_getByte_setPC, o_getByte_setReg]
        exact hm2 u hu
    · intro j hj
      simp only [sn, s5, o_getByte_setPC, ha78, set_byte_read]
      have hpc_cap2 : (openPosWritten (tdNode trapdoor) (tdSalt trapdoor) positions (k + 1)).length ≤ proofCap := by
        have := openPosWritten_length_le (tdNode trapdoor) (tdSalt trapdoor) positions (k + 1) hn; omega
      rw [if_neg (o_bv_ne (by omega) (by omega) (by omega))]
      simp only [s4, s3, o_getByte_setPC, o_getByte_setReg]
      rw [hw_eq] at hw2
      exact hw2 j hj

/-! ### 8. Cap Frontier Loop and Root (`pc[80..149]`) -/

private def openCapMark (positions : Positions) (j u : Nat) : Bool :=
  if u < 286 + j then capMark positions u else false

private def openCapPrefix (nodes : Nat → Digest) (positions : Positions) (n : Nat) : List Byte :=
  (List.range n).flatMap (capNodeFrontierProof nodes positions)

private def openCapCountPrefix (positions : Positions) (n : Nat) : Nat :=
  ∑ j ∈ Finset.range n, capNodeFrontierCount positions j

private theorem openCapPrefix_zero (nodes : Nat → Digest) (positions : Positions) :
    openCapPrefix nodes positions 0 = [] := rfl

private theorem openCapPrefix_succ (nodes : Nat → Digest) (positions : Positions) (n : Nat) :
    openCapPrefix nodes positions (n + 1) =
      openCapPrefix nodes positions n ++ capNodeFrontierProof nodes positions n := by
  unfold openCapPrefix
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]

private theorem openCapPrefix_length (nodes : Nat → Digest) (positions : Positions) (n : Nat) :
    (openCapPrefix nodes positions n).length = 32 * openCapCountPrefix positions n := by
  induction n with
  | zero => simp [openCapPrefix, openCapCountPrefix]
  | succ k ih =>
    rw [openCapPrefix_succ, List.length_append, ih, capNodeFrontierProof_length]
    unfold openCapCountPrefix
    rw [Finset.sum_range_succ, Nat.mul_add]

private theorem openCapCountPrefix_le (positions : Positions) (n : Nat) (hn : n ≤ 143) :
    openCapCountPrefix positions n ≤ capFrontierCount positions := by
  unfold openCapCountPrefix capFrontierCount
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hn)

private theorem openPosMark_eq_openCapMark0 (positions : Positions) (u : Nat) :
    openPosMark positions positions.card u = openCapMark positions 0 u := by
  unfold openCapMark
  by_cases h286 : u < 286
  · rw [if_pos (by omega), capMark_leaf positions u h286]
    apply Bool.eq_iff_iff.mpr
    simp only [openPosMark, decide_eq_true_eq]
    constructor
    · rintro ⟨_, ord, hord, _, heq⟩
      exact ⟨(positions.sort (· ≤ ·))[ord]'(by simpa using hord),
        (Finset.mem_sort (· ≤ ·)).mp (List.getElem_mem _), heq⟩
    · rintro ⟨i, hi, heq⟩
      have hmem : i ∈ positions.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).mpr hi
      obtain ⟨ord, hord, hget⟩ := List.getElem_of_mem hmem
      have hord' : ord < positions.card := by simpa using hord
      exact ⟨h286, ord, hord', hord', by simpa [hget] using heq⟩
  · rw [if_neg (by omega)]
    simp [openPosMark, h286]

/-- Cap setup (`pc[80..86]`, 7 steps/cycles). -/
private theorem o_cap_setup {s : MachineState} {positions : Positions}
    (hpc : s.pc = oPcAt 80) (hfix : OpenFixed positions s) :
    ∃ s' : MachineState,
      OpenRuns s 7 7 s' ∧
      s'.pc = oPcAt 87 ∧
      OpenFixed positions s' ∧
      s'.getReg .x14 = BitVec.ofNat 64 4096 ∧
      s'.getReg .x15 = BitVec.ofNat 64 (4096 + 286) ∧
      s'.getReg .x16 = BitVec.ofNat 64 (4096 + 428) ∧
      s'.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * CAP_LEAF_LO) ∧
      s'.getReg .x20 = s.getReg .x20 ∧
      (∀ addr, s'.getByte addr = s.getByte addr) := by
  have h80 := o_step_ADDI (s := s) (idx := 80) (by decide) hpc rfl
  let t1 := (s.setReg .x14 (s.getReg .x24 + signExtend12 0#12)).setPC (oPcAt 81)
  have h81 := o_step_ADDI (s := t1) (idx := 81) (by decide) rfl rfl
  let t2 := (t1.setReg .x15 (t1.getReg .x24 + signExtend12 286#12)).setPC (oPcAt 82)
  have h82 := o_step_ADDI (s := t2) (idx := 82) (by decide) rfl rfl
  let t3 := (t2.setReg .x16 (t2.getReg .x24 + signExtend12 428#12)).setPC (oPcAt 83)
  have h83 := o_step_ADDI (s := t3) (idx := 83) (by decide) rfl rfl
  let t4 := (t3.setReg .x6 (t3.getReg .x0 + signExtend12 6#12)).setPC (oPcAt 84)
  have h84 := o_step_SLLI (s := t4) (idx := 84) (by decide) rfl rfl
  let t5 := (t4.setReg .x6 (t4.getReg .x6 <<< (11#6 : BitVec 6).toNat)).setPC (oPcAt 85)
  have h85 := o_step_ADDI (s := t5) (idx := 85) (by decide) rfl rfl
  let t6 := (t5.setReg .x6 (t5.getReg .x6 + signExtend12 1440#12)).setPC (oPcAt 86)
  have h86 := o_step_SUB (s := t6) (idx := 86) (by decide) rfl rfl
  let t7 := (t6.setReg .x17 (t6.getReg .x23 - t6.getReg .x6)).setPC (oPcAt 87)
  have hrun : OpenRuns s 7 7 t7 := by
    simpa only [show 4 + 3 = 7 from rfl] using
      ((h80.trans h81).trans (h82.trans h83)).trans ((h84.trans h85).trans h86)
  have hreg : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x6 → r ≠ .x17 →
      t7.getReg r = s.getReg r := fun r h14 h15 h16 h6 h17 => by
    simp only [t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h17),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h6),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h16),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h15),
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h14)]
  have hfix' : OpenFixed positions t7 := {
    x8 := (hreg .x8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x8
    x18 := (hreg .x18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x18
    x19 := (hreg .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x19
    x21 := (hreg .x21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x21
    x22 := (hreg .x22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x22
    x23 := (hreg .x23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x23
    x24 := (hreg .x24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x24
    x25 := (hreg .x25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x25
    x27 := (hreg .x27 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfix.x27
  }
  have hx6_6 : t6.getReg .x6 = BitVec.ofNat 64 13728 := by
    simp only [t6, t5, t4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      o_getReg_x0]; decide
  have hx23_6 : t6.getReg .x23 = BitVec.ofNat 64 (4294971424 + rowOff) := by
    simp only [t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      ne_eq, not_false_eq_true, reduceCtorEq, hfix.x23]
  refine ⟨t7, hrun, rfl, hfix', ?_, ?_, ?_, ?_,
    hreg .x20 (by decide) (by decide) (by decide) (by decide) (by decide),
    fun addr => by simp only [t7, t6, t5, t4, t3, t2, t1, o_getByte_setPC, o_getByte_setReg]⟩
  · simp only [t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x24]; decide
  · simp only [t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x24]; decide
  · simp only [t7, t6, t5, t4, t3, t2, t1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, hfix.x24]; decide
  · simp only [t7, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      hx23_6, hx6_6, rowOff_eq, capLeafLo_eq]
    decide

/-- One iteration `j < 142` of `open_cap_loop` (`pc[87..127]`). -/
private theorem o_cap_step {s0 s : MachineState}
    {trapdoor : BitVec (8 * submission.sizes.trapdoor)} {positions : Positions}
    {j : Nat} {written : List Byte}
    (hs0 : s0 = submission.initialState .opening (trapdoor, positions))
    (hj : j < 142) (hpc : s.pc = oPcAt 87)
    (hfix : OpenFixed positions s)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (4096 + 3 * j))
    (hx15 : s.getReg .x15 = BitVec.ofNat 64 (4096 + 286 + j))
    (hx16 : s.getReg .x16 = BitVec.ofNat 64 (4096 + 428))
    (hx17 : s.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * (CAP_LEAF_LO + 3 * j)))
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length))
    (hwLen8 : written.length % 8 = 0)
    (hwCap : written.length + 32 * capNodeFrontierCount positions j ≤ proofCap)
    (hro : OpenReadOnly s0 s) (hm : OpenMarks (openCapMark positions j) s)
    (hw : OpenWritten written s) :
    let written' := written ++ capNodeFrontierProof (tdNode trapdoor) positions j
    ∃ cost s',
      cost ≤ 14 + 9 * capNodeFrontierCount positions j ∧
      OpenRuns s cost cost s' ∧
      s'.pc = (if j + 1 = 142 then oPcAt 128 else oPcAt 87) ∧
      OpenFixed positions s' ∧
      s'.getReg .x14 = BitVec.ofNat 64 (4096 + 3 * (j + 1)) ∧
      s'.getReg .x15 = BitVec.ofNat 64 (4096 + 286 + (j + 1)) ∧
      s'.getReg .x16 = BitVec.ofNat 64 (4096 + 428) ∧
      s'.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * (CAP_LEAF_LO + 3 * (j + 1))) ∧
      s'.getReg .x20 = BitVec.ofNat 64 (11072966688 + written'.length) ∧
      OpenReadOnly s0 s' ∧
      OpenMarks (openCapMark positions (j + 1)) s' ∧
      OpenWritten written' s' := by
  intro written'
  have hcl := capLeafLo_eq
  have htn := treeNodes_eq
  let m0 := capMark positions (3 * j)
  let m1 := capMark positions (3 * j + 1)
  let m2 := capMark positions (3 * j + 2)
  have hm_eq : capMark positions (286 + j) = (m0 || m1 || m2) := capMark_internal positions j hj
  -- pc[87..91]: LBU x6, x7, x28; OR x29
  have ha87 : s.getReg .x14 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + 3 * j) := by
    rw [hx14, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
  have h87 := o_step_LBU (s := s) (idx := 87) (by decide) hpc rfl
    (by rw [ha87]; exact o_accessValid _ 1 (by omega) (by omega))
  let t1 := (s.setReg .x6 ((s.getByte (s.getReg .x14 + signExtend12 0#12)).zeroExtend 64)).setPC (oPcAt 88)
  have hx14_1 : t1.getReg .x14 = BitVec.ofNat 64 (4096 + 3 * j) := by
    simp only [t1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x14), hx14]
  have ha88 : t1.getReg .x14 + signExtend12 1#12 = BitVec.ofNat 64 (4096 + (3 * j + 1)) := by
    rw [hx14_1, show signExtend12 1#12 = BitVec.ofNat 64 1 by decide, o_bv_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have h88 := o_step_LBU (s := t1) (idx := 88) (by decide) rfl rfl
    (by rw [ha88]; exact o_accessValid _ 1 (by omega) (by omega))
  let t2 := (t1.setReg .x7 ((t1.getByte (t1.getReg .x14 + signExtend12 1#12)).zeroExtend 64)).setPC (oPcAt 89)
  have hx14_2 : t2.getReg .x14 = BitVec.ofNat 64 (4096 + 3 * j) := by
    simp only [t2, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x14), hx14_1]
  have ha89 : t2.getReg .x14 + signExtend12 2#12 = BitVec.ofNat 64 (4096 + (3 * j + 2)) := by
    rw [hx14_2, show signExtend12 2#12 = BitVec.ofNat 64 2 by decide, o_bv_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have h89 := o_step_LBU (s := t2) (idx := 89) (by decide) rfl rfl
    (by rw [ha89]; exact o_accessValid _ 1 (by omega) (by omega))
  let t3 := (t2.setReg .x28 ((t2.getByte (t2.getReg .x14 + signExtend12 2#12)).zeroExtend 64)).setPC (oPcAt 90)
  have h90 := o_step_OR (s := t3) (idx := 90) (by decide) rfl rfl
  let t4 := (t3.setReg .x29 (t3.getReg .x6 ||| t3.getReg .x7)).setPC (oPcAt 91)
  have h91 := o_step_OR (s := t4) (idx := 91) (by decide) rfl rfl
  let t5 := (t4.setReg .x29 (t4.getReg .x29 ||| t4.getReg .x28)).setPC (oPcAt 92)
  have hrun_hd : OpenRuns s 5 5 t5 := ((h87.trans h88).trans (h89.trans h90)).trans h91
  have hreg5 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → t5.getReg r = s.getReg r :=
    fun r h6 h7 h28 h29 => by
      simp only [t5, t4, t3, t2, t1, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h29),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h28),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h7),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h6)]
  have hbyte5 : ∀ addr, t5.getByte addr = s.getByte addr := fun addr => by
    simp only [t5, t4, t3, t2, t1, o_getByte_setPC, o_getByte_setReg]
  have hx6_5 : t5.getReg .x6 = if m0 then 1#64 else 0#64 := by
    have h6_1 : t1.getReg .x6 = if m0 then 1#64 else 0#64 := by
      have hcm : openCapMark positions j (3 * j) = m0 := by
        unfold openCapMark; simp [show 3 * j < 286 + j by omega, m0]
      simp only [t1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, ha87]
      rw [hm (3 * j) (by omega), hcm]
      exact o_bool_byte_zext m0
    simp only [t5, t4, t3, t2, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, h6_1]
  have hx7_5 : t5.getReg .x7 = if m1 then 1#64 else 0#64 := by
    have h7_2 : t2.getReg .x7 = if m1 then 1#64 else 0#64 := by
      have hcm : openCapMark positions j (3 * j + 1) = m1 := by
        unfold openCapMark; simp [show 3 * j + 1 < 286 + j by omega, m1]
      simp only [t2, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, ha88]
      simp only [t1, o_getByte_setPC, o_getByte_setReg]
      rw [hm (3 * j + 1) (by omega), hcm]
      exact o_bool_byte_zext m1
    simp only [t5, t4, t3, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, h7_2]
  have hx28_5 : t5.getReg .x28 = if m2 then 1#64 else 0#64 := by
    have h28_3 : t3.getReg .x28 = if m2 then 1#64 else 0#64 := by
      have hcm : openCapMark positions j (3 * j + 2) = m2 := by
        unfold openCapMark; simp [show 3 * j + 2 < 286 + j by omega, m2]
      simp only [t3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, ha89]
      simp only [t2, t1, o_getByte_setPC, o_getByte_setReg]
      rw [hm (3 * j + 2) (by omega), hcm]
      exact o_bool_byte_zext m2
    simp only [t5, t4, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
      not_false_eq_true, reduceCtorEq, h28_3]
  have hx29_5 : t5.getReg .x29 = if (m0 || m1 || m2) then 1#64 else 0#64 := by
    have h6_3 : t3.getReg .x6 = if m0 then 1#64 else 0#64 := by
      simpa only [t5, t4, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq] using hx6_5
    have h7_3 : t3.getReg .x7 = if m1 then 1#64 else 0#64 := by
      simpa only [t5, t4, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq] using hx7_5
    have h28_4 : t4.getReg .x28 = if m2 then 1#64 else 0#64 := by
      simpa only [t5, MachineState.getReg_setPC, MachineState.getReg_setReg_ne, ne_eq,
        not_false_eq_true, reduceCtorEq] using hx28_5
    have h29_4 : t4.getReg .x29 = if (m0 || m1) then 1#64 else 0#64 := by
      simp only [t4, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
        h6_3, h7_3, o_bool_word_or]
    simp only [t5, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq,
      h29_4, h28_4, o_bool_word_or]
  -- pc[92..123]: either skip (BEQ taken) or mark + 3 conditional 32B copies
  have hmid : ∃ kmid u,
      kmid ≤ 5 + 9 * capNodeFrontierCount positions j ∧
      OpenRuns t5 kmid kmid u ∧
      u.pc = oPcAt 124 ∧
      (∀ r, r ≠ .x20 → r ≠ .x30 → u.getReg r = t5.getReg r) ∧
      u.getReg .x20 = BitVec.ofNat 64 (11072966688 + written'.length) ∧
      OpenReadOnly s0 u ∧
      OpenMarks (openCapMark positions (j + 1)) u ∧
      OpenWritten written' u := by
    cases hpar : (m0 || m1 || m2) with
    | false =>
      have h92 := o_step_BEQ_taken (s := t5) (idx := 92) (tgt := 124) (by decide) rfl rfl
        (by rw [hx29_5, hpar, o_getReg_x0]; rfl) o_tgt_92
      have hpf_nil : capNodeFrontierProof (tdNode trapdoor) positions j = [] := by
        unfold capNodeFrontierProof; simp [hj, hm_eq, hpar]
      refine ⟨1, t5.setPC (oPcAt 124), by omega, h92, rfl,
        fun r _ _ => o_getReg_setPC t5 _ r,
        by simp only [written', hpf_nil, List.append_nil, MachineState.getReg_setPC]
           exact (hreg5 .x20 (by decide) (by decide) (by decide) (by decide)).trans hx20,
        fun a ha1 ha2 => by rw [o_getByte_setPC, hbyte5]; exact hro a ha1 ha2,
        ?_,
        fun i hi => by
          simp only [written', hpf_nil, List.append_nil] at hi ⊢
          rw [o_getByte_setPC, hbyte5]; exact hw i hi⟩
      intro u hu
      rw [o_getByte_setPC, hbyte5, hm u hu]
      unfold openCapMark
      by_cases hlt : u < 286 + j
      · simp [hlt, show u < 286 + (j + 1) by omega]
      · by_cases heq : u = 286 + j
        · subst heq; simp [hm_eq, hpar]
        · simp [hlt, show ¬ (u < 286 + (j + 1)) by omega]
    | true =>
      have h92 := o_step_BEQ_not_taken (s := t5) (idx := 92) (by decide) rfl rfl
        (by rw [hx29_5, hpar, o_getReg_x0]; decide)
      let u1 := t5.setPC (oPcAt 93)
      have hx15_u1 : u1.getReg .x15 = BitVec.ofNat 64 (4096 + 286 + j) :=
        (o_getReg_setPC t5 _ .x15).trans ((hreg5 .x15 (by decide) (by decide) (by decide) (by decide)).trans hx15)
      have ha93 : u1.getReg .x15 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + (286 + j)) := by
        rw [hx15_u1, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
        exact congrArg (BitVec.ofNat 64) (by omega)
      have h93 := o_step_SB (s := u1) (idx := 93) (by decide) rfl rfl
        (by rw [ha93]; exact o_accessValid _ 1 (by omega) (by omega))
      let u2 := (u1.setByte (u1.getReg .x15 + signExtend12 0#12) ((u1.getReg .x27).truncate 8)).setPC (oPcAt 94)
      have hreg_u2 : ∀ r, u2.getReg r = t5.getReg r := fun r => by
        simp only [u2, u1, MachineState.getReg_setPC, o_getReg_setByte]
      have hro_u2 : OpenReadOnly s0 u2 := fun a ha1 ha2 => by
        simp only [u2, o_getByte_setPC, ha93, set_byte_read]
        rw [if_neg (o_bv_ne (by omega) (by omega) (by omega))]
        simp only [u1, o_getByte_setPC, hbyte5]; exact hro a ha1 ha2
      have hm_u2 : OpenMarks (openCapMark positions (j + 1)) u2 := fun u hu => by
        simp only [u2, o_getByte_setPC, ha93, set_byte_read]
        have htr : (u1.getReg .x27).truncate 8 = 1#8 := by
          have h27 : u1.getReg .x27 = BitVec.ofNat 64 1 :=
            (o_getReg_setPC t5 _ .x27).trans
              ((hreg5 .x27 (by decide) (by decide) (by decide) (by decide)).trans hfix.x27)
          rw [h27]; decide
        rw [htr]
        unfold openCapMark
        by_cases hueq : u = 286 + j
        · subst hueq; simp [hm_eq, hpar]
        · rw [if_neg (o_bv_ne (by omega) (by omega) (by omega))]
          simp only [u1, o_getByte_setPC, hbyte5, hm u hu]
          unfold openCapMark
          by_cases hlt : u < 286 + j
          · simp [hlt, show u < 286 + (j + 1) by omega]
          · simp [hlt, show ¬ (u < 286 + (j + 1)) by omega]
      have hw_u2 : OpenWritten written u2 := fun i hi => by
        have hbd : i < proofCap := by omega
        have hpc_cap : proofCap = 11140077536 := rfl
        simp only [u2, o_getByte_setPC, ha93, set_byte_read,
          show BitVec.ofNat 64 (11072966688 + i) ≠ BitVec.ofNat 64 (4096 + (286 + j)) from o_bv_ne (by omega) (by omega) (by omega),
          ite_false]
        simp only [u1, o_getByte_setPC, hbyte5]; exact hw i hi
      have hcnt_eq : capNodeFrontierCount positions j =
          (if !m0 then 1 else 0) + (if !m1 then 1 else 0) + (if !m2 then 1 else 0) := by
        unfold capNodeFrontierCount; simp [hj, hm_eq, hpar, m0, m1, m2]
      have hx17_u2 : u2.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * (CAP_LEAF_LO + 3 * j)) :=
        (hreg_u2 .x17).trans ((hreg5 .x17 (by decide) (by decide) (by decide) (by decide)).trans hx17)
      have hx20_u2 : u2.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length) :=
        (hreg_u2 .x20).trans ((hreg5 .x20 (by decide) (by decide) (by decide) (by decide)).trans hx20)
      -- Conditional copy 0 (pc[94..103])
      let c0 := if !m0 then bitsToBytes (tdNode trapdoor (CAP_LEAF_LO + 3 * j)) 32 else []
      have hc0_len : c0.length = 32 * (if !m0 then 1 else 0) := by
        dsimp only [c0]; cases m0 <;> simp [bitsToBytes]
      obtain ⟨u3, hrc0, hpc3, hx20_3, hreg3, hro3, hw3, hlow3⟩ := o_cap_cond_copy32 hs0 (s := u2)
        (idx := 94) (flagReg := .x6) (baseOff := 0) (u := CAP_LEAF_LO + 3 * j) (flag := m0)
        (by decide) rfl o_tgt_94 (by decide) (by decide)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        ((hreg_u2 .x6).trans hx6_5) (by simpa using hx17_u2) (by omega) (by omega)
        hx20_u2 hwLen8 (by have h0 : (if !m0 then 32 else 0) = 32 * (if !m0 then 1 else 0) := by cases m0 <;> decide
                           omega) hro_u2 hw_u2
      -- Conditional copy 1 (pc[104..113])
      let c1 := if !m1 then bitsToBytes (tdNode trapdoor (CAP_LEAF_LO + 3 * j + 1)) 32 else []
      have hc1_len : c1.length = 32 * (if !m1 then 1 else 0) := by
        dsimp only [c1]; cases m1 <;> simp [bitsToBytes]
      have hx17_u3 : u3.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * (CAP_LEAF_LO + 3 * j + 1) - 32) := by
        rw [hreg3 .x17 (by decide) (by decide), hx17_u2]; exact congrArg (BitVec.ofNat 64) (Nat.eq_sub_of_add_eq (by ring))
      obtain ⟨u4, hrc1, hpc4, hx20_4, hreg4, hro4, hw4, hlow4⟩ := o_cap_cond_copy32 hs0 (s := u3)
        (idx := 104) (flagReg := .x7) (baseOff := 32) (u := CAP_LEAF_LO + 3 * j + 1) (flag := m1)
        (by decide) hpc3 o_tgt_104 (by decide) (by decide)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        ((hreg3 .x7 (by decide) (by decide)).trans ((hreg_u2 .x7).trans hx7_5))
        hx17_u3 (by omega) (by omega) hx20_3
        (by rw [List.length_append, hc0_len]; omega)
        (by have h1 : (if !m1 then 32 else 0) = 32 * (if !m1 then 1 else 0) := by cases m1 <;> decide
            rw [List.length_append, hc0_len, h1]; omega) hro3 hw3
      -- Conditional copy 2 (pc[114..123])
      let c2 := if !m2 then bitsToBytes (tdNode trapdoor (CAP_LEAF_LO + 3 * j + 2)) 32 else []
      have hx17_u4 : u4.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * (CAP_LEAF_LO + 3 * j + 2) - 64) := by
        rw [hreg4 .x17 (by decide) (by decide), hreg3 .x17 (by decide) (by decide), hx17_u2]
        exact congrArg (BitVec.ofNat 64) (Nat.eq_sub_of_add_eq (by ring))
      obtain ⟨u5, hrc2, hpc5, hx20_5, hreg5', hro5, hw5, hlow5⟩ := o_cap_cond_copy32 hs0 (s := u4)
        (idx := 114) (flagReg := .x28) (baseOff := 64) (u := CAP_LEAF_LO + 3 * j + 2) (flag := m2)
        (by decide) hpc4 o_tgt_114 (by decide) (by decide)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        ((hreg4 .x28 (by decide) (by decide)).trans ((hreg3 .x28 (by decide) (by decide)).trans ((hreg_u2 .x28).trans hx28_5)))
        hx17_u4 (by omega) (by omega) hx20_4
        (by rw [List.length_append, List.length_append, hc0_len, hc1_len]; omega)
        (by have h2 : (if !m2 then 32 else 0) = 32 * (if !m2 then 1 else 0) := by cases m2 <;> decide
            rw [List.length_append, List.length_append, hc0_len, hc1_len, h2]; omega) hro4 hw4
      have hpf_eq : written ++ c0 ++ c1 ++ c2 = written' := by
        dsimp only [written', c0, c1, c2]
        unfold capNodeFrontierProof
        simp only [hj, ite_true, hm_eq, hpar, List.append_assoc, m0, m1, m2]
      have hcost : 1 + 1 + (if !m0 then 10 else 1) + (if !m1 then 10 else 1) + (if !m2 then 10 else 1) ≤
          5 + 9 * capNodeFrontierCount positions j := by
        rw [hcnt_eq]; cases m0 <;> cases m1 <;> cases m2 <;> decide
      have hrun_m := (((h92.trans h93).trans hrc0).trans hrc1).trans hrc2
      refine ⟨_, u5, hcost, hrun_m, hpc5,
        fun r h20 h30 => (hreg5' r h30 h20).trans ((hreg4 r h30 h20).trans ((hreg3 r h30 h20).trans (hreg_u2 r))),
        by rwa [hpf_eq] at hx20_5, hro5,
        fun u hu => (hlow5 (4096 + u) (by omega)).trans ((hlow4 (4096 + u) (by omega)).trans
          ((hlow3 (4096 + u) (by omega)).trans (hm_u2 u hu))),
        by rwa [hpf_eq] at hw5⟩
  obtain ⟨kmid, u, hkmid, hrun_m, hpc_u, hreg_u, hx20_u, hro_u, hm_u, hw_u⟩ := hmid
  -- pc[124..127]: advance pointers and isolated backward branch
  have h124 := o_step_ADDI (s := u) (idx := 124) (by decide) hpc_u rfl
  let v1 := (u.setReg .x14 (u.getReg .x14 + signExtend12 3#12)).setPC (oPcAt 125)
  have h125 := o_step_ADDI (s := v1) (idx := 125) (by decide) rfl rfl
  let v2 := (v1.setReg .x15 (v1.getReg .x15 + signExtend12 1#12)).setPC (oPcAt 126)
  have h126 := o_step_ADDI (s := v2) (idx := 126) (by decide) rfl rfl
  let v3 := (v2.setReg .x17 (v2.getReg .x17 + signExtend12 96#12)).setPC (oPcAt 127)
  have hreg_v3 : ∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x17 → v3.getReg r = u.getReg r :=
    fun r h14 h15 h17 => by
      simp only [v3, v2, v1, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h17),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h15),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm h14)]
  have hx14_v3 : v3.getReg .x14 = BitVec.ofNat 64 (4096 + 3 * (j + 1)) := by
    have h14_u : u.getReg .x14 = BitVec.ofNat 64 (4096 + 3 * j) :=
      (hreg_u .x14 (by decide) (by decide)).trans ((hreg5 .x14 (by decide) (by decide) (by decide) (by decide)).trans hx14)
    simp only [v3, v2, v1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, h14_u,
      show signExtend12 3#12 = BitVec.ofNat 64 3 by decide, o_bv_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hx15_v3 : v3.getReg .x15 = BitVec.ofNat 64 (4096 + 286 + (j + 1)) := by
    have h15_u : u.getReg .x15 = BitVec.ofNat 64 (4096 + 286 + j) :=
      (hreg_u .x15 (by decide) (by decide)).trans ((hreg5 .x15 (by decide) (by decide) (by decide) (by decide)).trans hx15)
    simp only [v3, v2, v1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, h15_u,
      show signExtend12 1#12 = BitVec.ofNat 64 1 by decide, o_bv_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  have hx16_v3 : v3.getReg .x16 = BitVec.ofNat 64 (4096 + 428) :=
    (hreg_v3 .x16 (by decide) (by decide) (by decide)).trans
      ((hreg_u .x16 (by decide) (by decide)).trans
        ((hreg5 .x16 (by decide) (by decide) (by decide) (by decide)).trans hx16))
  have hx17_v3 : v3.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * (CAP_LEAF_LO + 3 * (j + 1))) := by
    have h17_u : u.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * (CAP_LEAF_LO + 3 * j)) :=
      (hreg_u .x17 (by decide) (by decide)).trans ((hreg5 .x17 (by decide) (by decide) (by decide) (by decide)).trans hx17)
    simp only [v3, v2, v1, MachineState.getReg_setPC, MachineState.getReg_setReg_ne,
      MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, h17_u,
      show signExtend12 96#12 = BitVec.ofNat 64 96 by decide, o_bv_add]
    exact congrArg (BitVec.ofNat 64) (by omega)
  let s' := v3.setPC (if j + 1 = 142 then oPcAt 128 else oPcAt 87)
  have h127 : OpenRuns v3 1 1 s' := by
    by_cases hend : j + 1 = 142
    · have h15_eq : v3.getReg .x15 = BitVec.ofNat 64 (4096 + 428) := by
        rw [hx15_v3]; exact congrArg (BitVec.ofNat 64) (by omega)
      simpa only [s', hend, ite_true] using o_step_127_done (s := v3) rfl h15_eq hx16_v3
    · simpa only [s', hend, ite_false] using
        o_step_127_back (s := v3) rfl hx15_v3 hx16_v3 (by omega) (by omega) (by omega)
  have hrun_all : OpenRuns s (5 + kmid + 4) (5 + kmid + 4) s' := by
    have htl := ((h124.trans h125).trans h126).trans h127
    simpa only [show 1 + 1 + 1 + 1 = 4 from rfl, Nat.add_assoc] using (hrun_hd.trans hrun_m).trans htl
  have hfix' : OpenFixed positions s' := {
    x8 := (o_getReg_setPC v3 _ .x8).trans ((hreg_v3 .x8 (by decide) (by decide) (by decide)).trans ((hreg_u .x8 (by decide) (by decide)).trans ((hreg5 .x8 (by decide) (by decide) (by decide) (by decide)).trans hfix.x8)))
    x18 := (o_getReg_setPC v3 _ .x18).trans ((hreg_v3 .x18 (by decide) (by decide) (by decide)).trans ((hreg_u .x18 (by decide) (by decide)).trans ((hreg5 .x18 (by decide) (by decide) (by decide) (by decide)).trans hfix.x18)))
    x19 := (o_getReg_setPC v3 _ .x19).trans ((hreg_v3 .x19 (by decide) (by decide) (by decide)).trans ((hreg_u .x19 (by decide) (by decide)).trans ((hreg5 .x19 (by decide) (by decide) (by decide) (by decide)).trans hfix.x19)))
    x21 := (o_getReg_setPC v3 _ .x21).trans ((hreg_v3 .x21 (by decide) (by decide) (by decide)).trans ((hreg_u .x21 (by decide) (by decide)).trans ((hreg5 .x21 (by decide) (by decide) (by decide) (by decide)).trans hfix.x21)))
    x22 := (o_getReg_setPC v3 _ .x22).trans ((hreg_v3 .x22 (by decide) (by decide) (by decide)).trans ((hreg_u .x22 (by decide) (by decide)).trans ((hreg5 .x22 (by decide) (by decide) (by decide) (by decide)).trans hfix.x22)))
    x23 := (o_getReg_setPC v3 _ .x23).trans ((hreg_v3 .x23 (by decide) (by decide) (by decide)).trans ((hreg_u .x23 (by decide) (by decide)).trans ((hreg5 .x23 (by decide) (by decide) (by decide) (by decide)).trans hfix.x23)))
    x24 := (o_getReg_setPC v3 _ .x24).trans ((hreg_v3 .x24 (by decide) (by decide) (by decide)).trans ((hreg_u .x24 (by decide) (by decide)).trans ((hreg5 .x24 (by decide) (by decide) (by decide) (by decide)).trans hfix.x24)))
    x25 := (o_getReg_setPC v3 _ .x25).trans ((hreg_v3 .x25 (by decide) (by decide) (by decide)).trans ((hreg_u .x25 (by decide) (by decide)).trans ((hreg5 .x25 (by decide) (by decide) (by decide) (by decide)).trans hfix.x25)))
    x27 := (o_getReg_setPC v3 _ .x27).trans ((hreg_v3 .x27 (by decide) (by decide) (by decide)).trans ((hreg_u .x27 (by decide) (by decide)).trans ((hreg5 .x27 (by decide) (by decide) (by decide) (by decide)).trans hfix.x27)))
  }
  refine ⟨5 + kmid + 4, s', by omega, hrun_all, rfl, hfix',
    (o_getReg_setPC v3 _ .x14).trans hx14_v3,
    (o_getReg_setPC v3 _ .x15).trans hx15_v3,
    (o_getReg_setPC v3 _ .x16).trans hx16_v3,
    (o_getReg_setPC v3 _ .x17).trans hx17_v3,
    (o_getReg_setPC v3 _ .x20).trans ((hreg_v3 .x20 (by decide) (by decide) (by decide)).trans hx20_u),
    fun a ha1 ha2 => by simp only [s', v3, v2, v1, o_getByte_setPC, o_getByte_setReg]; exact hro_u a ha1 ha2,
    fun x hx => by simp only [s', v3, v2, v1, o_getByte_setPC, o_getByte_setReg]; exact hm_u x hx,
    fun x hx => by simp only [s', v3, v2, v1, o_getByte_setPC, o_getByte_setReg]; exact hw_u x hx⟩

/-- Full 142-iteration cap loop (`pc[87..127]`). -/
private theorem o_cap_loop {s0 : MachineState}
    {trapdoor : BitVec (8 * submission.sizes.trapdoor)} {positions : Positions}
    {base : List Byte}
    (hs0 : s0 = submission.initialState .opening (trapdoor, positions))
    (hbase8 : base.length % 8 = 0)
    (hbaseCap : base.length + 32 * capFrontierCount positions ≤ proofCap)
    (sInit : MachineState) (hpc0 : sInit.pc = oPcAt 87) (hfix0 : OpenFixed positions sInit)
    (hx14_0 : sInit.getReg .x14 = BitVec.ofNat 64 4096)
    (hx15_0 : sInit.getReg .x15 = BitVec.ofNat 64 (4096 + 286))
    (hx16_0 : sInit.getReg .x16 = BitVec.ofNat 64 (4096 + 428))
    (hx17_0 : sInit.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * CAP_LEAF_LO))
    (hx20_0 : sInit.getReg .x20 = BitVec.ofNat 64 (11072966688 + base.length))
    (hro0 : OpenReadOnly s0 sInit) (hm0 : OpenMarks (openCapMark positions 0) sInit)
    (hw0 : OpenWritten base sInit) :
    ∀ n ≤ 142,
      ∃ cost sn,
        cost ≤ 14 * n + 9 * openCapCountPrefix positions n ∧
        OpenRuns sInit cost cost sn ∧
        sn.pc = (if n = 142 then oPcAt 128 else oPcAt 87) ∧
        OpenFixed positions sn ∧
        sn.getReg .x14 = BitVec.ofNat 64 (4096 + 3 * n) ∧
        sn.getReg .x15 = BitVec.ofNat 64 (4096 + 286 + n) ∧
        sn.getReg .x16 = BitVec.ofNat 64 (4096 + 428) ∧
        sn.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * (CAP_LEAF_LO + 3 * n)) ∧
        sn.getReg .x20 = BitVec.ofNat 64
          (11072966688 + (base ++ openCapPrefix (tdNode trapdoor) positions n).length) ∧
        OpenReadOnly s0 sn ∧
        OpenMarks (openCapMark positions n) sn ∧
        OpenWritten (base ++ openCapPrefix (tdNode trapdoor) positions n) sn := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨0, sInit, Nat.zero_le _, OpenRuns.refl sInit, by simp [hpc0], hfix0,
      by simpa using hx14_0, by simpa using hx15_0, hx16_0, by simpa using hx17_0,
      by simpa [openCapPrefix_zero] using hx20_0, hro0, hm0,
      by simpa [openCapPrefix_zero] using hw0⟩
  | succ k ih =>
    obtain ⟨cK, sk, hcK, hrK, hpcK, hfixK, hx14K, hx15K, hx16K, hx17K, hx20K, hroK, hmK, hwK⟩ := ih (by omega)
    have hpc87 : sk.pc = oPcAt 87 := by simpa only [show k ≠ 142 by omega, ite_false] using hpcK
    have hlen_k : (base ++ openCapPrefix (tdNode trapdoor) positions k).length =
        base.length + 32 * openCapCountPrefix positions k := by
      rw [List.length_append, openCapPrefix_length]
    have hcnt_succ : openCapCountPrefix positions (k + 1) =
        openCapCountPrefix positions k + capNodeFrontierCount positions k := by
      unfold openCapCountPrefix; exact Finset.sum_range_succ _ k
    have hcnt_le : openCapCountPrefix positions (k + 1) ≤ capFrontierCount positions :=
      openCapCountPrefix_le positions (k + 1) (by omega)
    obtain ⟨c1, sn, hc1, hr1, hpcN, hfixN, hx14N, hx15N, hx16N, hx17N, hx20N, hroN, hmN, hwN⟩ :=
      o_cap_step hs0 (by omega) hpc87 hfixK hx14K hx15K hx16K hx17K hx20K
        (by rw [hlen_k]; omega) (by rw [hlen_k]; omega) hroK hmK hwK
    have hpf : base ++ openCapPrefix (tdNode trapdoor) positions k ++
        capNodeFrontierProof (tdNode trapdoor) positions k =
        base ++ openCapPrefix (tdNode trapdoor) positions (k + 1) := by
      rw [openCapPrefix_succ, List.append_assoc]
    refine ⟨cK + c1, sn, by omega, hrK.trans hr1, hpcN, hfixN, hx14N, hx15N, hx16N, hx17N,
      by rwa [hpf] at hx20N, hroN, hmN, by rwa [hpf] at hwN⟩

/-- Cap root (`j = 142`, `pc[128..149]`, when `positions.Nonempty`). -/
private theorem o_root {s0 s : MachineState}
    {trapdoor : BitVec (8 * submission.sizes.trapdoor)} {positions : Positions}
    {written : List Byte}
    (hs0 : s0 = submission.initialState .opening (trapdoor, positions))
    (hne : positions.Nonempty) (hpc : s.pc = oPcAt 128)
    (hfix : OpenFixed positions s)
    (hx14 : s.getReg .x14 = BitVec.ofNat 64 (4096 + 426))
    (hx17 : s.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * (CAP_LEAF_LO + 426)))
    (hx20 : s.getReg .x20 = BitVec.ofNat 64 (11072966688 + written.length))
    (hwLen8 : written.length % 8 = 0)
    (hwCap : written.length + 32 * capNodeFrontierCount positions 142 ≤ proofCap)
    (hro : OpenReadOnly s0 s) (hm : OpenMarks (openCapMark positions 142) s)
    (hw : OpenWritten written s) :
    let written' := written ++ capNodeFrontierProof (tdNode trapdoor) positions 142
    ∃ cost s',
      cost ≤ 4 + 9 * capNodeFrontierCount positions 142 ∧
      OpenRuns s cost cost s' ∧
      s'.pc = oPcAt 150 ∧
      s'.getReg .x19 = BitVec.ofNat 64 11072966688 ∧
      s'.getReg .x20 = BitVec.ofNat 64 (11072966688 + written'.length) ∧
      OpenWritten written' s' := by
  intro written'
  have hcl := capLeafLo_eq
  have htn := treeNodes_eq
  have h428 := capMark_428_eq_true positions hne
  let m0 := capMark positions 426
  let m1 := capMark positions 427
  have hcnt : capNodeFrontierCount positions 142 = (if !m0 then 1 else 0) + (if !m1 then 1 else 0) := by
    unfold capNodeFrontierCount; simp [h428, m0, m1]
  have ha128 : s.getReg .x14 + signExtend12 0#12 = BitVec.ofNat 64 (4096 + 426) := by
    rw [hx14, show signExtend12 0#12 = 0#64 by decide, BitVec.add_zero]
  have h128 := o_step_LBU (s := s) (idx := 128) (by decide) hpc rfl
    (by rw [ha128]; exact o_accessValid _ 1 (by omega) (by omega))
  let s1 := (s.setReg .x6 ((s.getByte (s.getReg .x14 + signExtend12 0#12)).zeroExtend 64)).setPC (oPcAt 129)
  have hx6_1 : s1.getReg .x6 = if m0 then 1#64 else 0#64 := by
    have hm426 : openCapMark positions 142 426 = m0 := by
      unfold openCapMark; simp [m0]
    simp only [s1, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, ha128]
    rw [hm 426 (by omega), hm426]
    exact o_bool_byte_zext m0
  let c0 := if !m0 then bitsToBytes (tdNode trapdoor (CAP_LEAF_LO + 426)) 32 else []
  have hc0_len : c0.length = 32 * (if !m0 then 1 else 0) := by
    dsimp only [c0]; cases m0 <;> simp [bitsToBytes]
  obtain ⟨s2, hr0, hpc2, hx20_2, hreg2, hro2, hw2, hlow2⟩ := o_cap_cond_copy32 hs0 (s := s1)
    (idx := 129) (flagReg := .x6) (baseOff := 0) (u := CAP_LEAF_LO + 426) (flag := m0)
    (by decide) rfl o_tgt_129 (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hx6_1
    (by simp only [s1, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x17), hx17]; simp)
    (by omega) (by omega)
    (by simp only [s1, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x20), hx20])
    hwLen8 (by have hm0_32 : (if !m0 then 32 else 0) = 32 * (if !m0 then 1 else 0) := by cases m0 <;> decide
               omega)
    (fun a ha1 ha2 => by simp only [s1, o_getByte_setPC, o_getByte_setReg]; exact hro a ha1 ha2)
    (fun i hi => by simp only [s1, o_getByte_setPC, o_getByte_setReg]; exact hw i hi)
  have hx14_2 : s2.getReg .x14 = BitVec.ofNat 64 (4096 + 426) := by
    rw [hreg2 .x14 (by decide) (by decide)]
    simp only [s1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x14), hx14]
  have ha139 : s2.getReg .x14 + signExtend12 1#12 = BitVec.ofNat 64 (4096 + 427) := by
    rw [hx14_2, show signExtend12 1#12 = BitVec.ofNat 64 1 by decide, o_bv_add]
  have h139 := o_step_LBU (s := s2) (idx := 139) (by decide) hpc2 rfl
    (by rw [ha139]; exact o_accessValid _ 1 (by omega) (by omega))
  let s3 := (s2.setReg .x7 ((s2.getByte (s2.getReg .x14 + signExtend12 1#12)).zeroExtend 64)).setPC (oPcAt 140)
  have hx7_3 : s3.getReg .x7 = if m1 then 1#64 else 0#64 := by
    have hm427 : openCapMark positions 142 427 = m1 := by
      unfold openCapMark; simp [m1]
    simp only [s3, MachineState.getReg_setPC, MachineState.getReg_setReg_eq, ne_eq, not_false_eq_true, reduceCtorEq, ha139]
    rw [hlow2 (4096 + 427) (by omega)]
    simp only [s1, o_getByte_setPC, o_getByte_setReg, hm 427 (by omega), hm427]
    exact o_bool_byte_zext m1
  have hx17_3 : s3.getReg .x17 = BitVec.ofNat 64 (4294971424 + 32 * (CAP_LEAF_LO + 427) - 32) := by
    simp only [s3, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x17)]
    rw [hreg2 .x17 (by decide) (by decide)]
    simp only [s1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x17), hx17]
    exact congrArg (BitVec.ofNat 64) (Nat.eq_sub_of_add_eq (by ring))
  let c1 := if !m1 then bitsToBytes (tdNode trapdoor (CAP_LEAF_LO + 427)) 32 else []
  obtain ⟨s4, hr1, hpc4, hx20_4, hreg4, _, hw4, _⟩ := o_cap_cond_copy32 hs0 (s := s3)
    (written := written ++ c0)
    (idx := 140) (flagReg := .x7) (baseOff := 32) (u := CAP_LEAF_LO + 427) (flag := m1)
    (by decide) rfl o_tgt_140 (by decide) (by decide)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    hx7_3 hx17_3 (by omega) (by omega)
    (by simp only [s3, MachineState.getReg_setPC,
          MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x20), hx20_2]; rfl)
    (by rw [List.length_append, hc0_len]; omega)
    (by have hm1_32 : (if !m1 then 32 else 0) = 32 * (if !m1 then 1 else 0) := by cases m1 <;> decide
        rw [List.length_append, hc0_len, hm1_32]; omega)
    (fun a ha1 ha2 => by simp only [s3, o_getByte_setPC, o_getByte_setReg]; exact hro2 a ha1 ha2)
    (fun i hi => by simp only [s3, o_getByte_setPC, o_getByte_setReg]; exact hw2 i hi)
  have hpf_eq : written ++ c0 ++ c1 = written' := by
    dsimp only [written', c0, c1]
    unfold capNodeFrontierProof
    simp only [show ¬ (142 < 142) by omega, ite_false, ite_true, h428, List.append_assoc, m0, m1]
  have hcost : 1 + (if !m0 then 10 else 1) + 1 + (if !m1 then 10 else 1) ≤
      4 + 9 * capNodeFrontierCount positions 142 := by
    rw [hcnt]; cases m0 <;> cases m1 <;> decide
  have hx19_4 : s4.getReg .x19 = BitVec.ofNat 64 11072966688 := by
    rw [hreg4 .x19 (by decide) (by decide)]
    simp only [s3, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x7 ≠ .x19)]
    rw [hreg2 .x19 (by decide) (by decide)]
    simp only [s1, MachineState.getReg_setPC,
      MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x6 ≠ .x19), hfix.x19]
  refine ⟨_, s4, hcost, ((h128.trans hr0).trans h139).trans hr1, hpc4, hx19_4,
    by rw [← hpf_eq]; exact hx20_4, by rw [← hpf_eq]; exact hw4⟩

/-! ### 9. Main Opening Execution Specification (`opening_exec_spec`) -/

private theorem submission_run_opening (s : Submission)
    (trapdoor : BitVec (8 * s.sizes.trapdoor)) (positions : Positions) :
    s.run .opening (trapdoor, positions) =
      execute (s.image .opening) (s.steps .opening)
        (s.initialState .opening (trapdoor, positions)) true := by
  unfold Submission.run
  dsimp only
  rfl

private theorem capFrontierProof_eq_openCapPrefix (nodes : Nat → Digest) (positions : Positions) :
    capFrontierProof nodes positions = openCapPrefix nodes positions 143 := rfl

theorem opening_exec_spec (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    ∃ exec : Execution,
      submission.run .opening (trapdoor, positions) = pure exec ∧
      exec.exit = Riscv.Exit.success ∧
      exec.oracleCalls = 0 ∧
      (exec.state.getReg .x11).toNat =
        (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions).length ∧
      (∀ j (hj : j < (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions).length),
        exec.state.getByte (BitVec.ofNat 64 (11072966688 + j)) =
          (referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions)[j]'hj) ∧
      (positions.card = BATCH → exec.cycles ≤ 50500) := by
  have hsteps_open : submission.steps .opening = 274877906944 := rfl
  rw [submission_run_opening submission trapdoor positions]
  by_cases hempty : positions.card = 0
  · obtain ⟨sHalt, hrun, hpc, hx5, hx10, hx11⟩ := o_empty_run trapdoor positions hempty
    have hhalt := OpenRuns.halt hrun (haltIdx := 157) (totalFuel := submission.steps .opening)
      (by decide) rfl hpc hx5 hx10 (by rw [hsteps_open]; omega)
    refine ⟨{ exit := .success, state := sHalt, cycles := 5, oracleCalls := 0 },
      hhalt, rfl, rfl, ?_, ?_, ?_⟩
    · unfold referenceProof; simp [hempty, hx11]
    · intro j hj; unfold referenceProof at hj; simp [hempty] at hj
    · intro hcard; change positions.card = 128 at hcard; omega
  · have hne : positions.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hempty)
    have hcard_le : positions.card ≤ 16777216 := o_card_le positions
    let s0 := submission.initialState .opening (trapdoor, positions)
    obtain ⟨s1, hr1, hpc1, hfix1, hx9_1, hx20_1, hro1, hm1, hw1⟩ := o_prologue trapdoor positions hempty
    obtain ⟨stP, cyP, s2, hstP, hcyP, hr2, hpc2, hfix2, _, hx20_2, hro2, hm2, hw2⟩ :=
      o_pos_loop (s0 := s0) rfl hempty s1 hpc1 hfix1 hx9_1 hx20_1 hro1 hm1 hw1 positions.card le_rfl
    have hpc80 : s2.pc = oPcAt 80 := by simpa only [ite_true] using hpc2
    obtain ⟨s3, hr3, hpc3, hfix3, hx14_3, hx15_3, hx16_3, hx17_3, hx20_3, hbyte3⟩ :=
      o_cap_setup hpc80 hfix2
    let base := openPosWritten (tdNode trapdoor) (tdSalt trapdoor) positions positions.card
    have hbase_eq : base = (positions.sort (· ≤ ·)).flatMap (recordProof (tdNode trapdoor) (tdSalt trapdoor)) := by
      unfold base openPosWritten
      rw [show positions.card = (positions.sort (· ≤ ·)).length by simp, List.take_length]
    have hpf_full : base ++ openCapPrefix (tdNode trapdoor) positions 142 ++
        capNodeFrontierProof (tdNode trapdoor) positions 142 =
        referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions := by
      unfold referenceProof
      simp only [hempty, ite_false]
      rw [hbase_eq, List.append_assoc, capFrontierProof_eq_openCapPrefix, ← openCapPrefix_succ]
    have hbaseCap : base.length + 32 * capFrontierCount positions ≤ proofCap := by
      have hlen_full := referenceProof_length_le_cap (tdNode trapdoor) (tdSalt trapdoor) positions
      rw [← hpf_full, List.append_assoc, List.length_append, ← openCapPrefix_succ,
        openCapPrefix_length] at hlen_full
      exact hlen_full
    obtain ⟨cCap, s4, hcCap, hr4, hpc4, hfix4, hx14_4, _, _, hx17_4, hx20_4, hro4, hm4, hw4⟩ :=
      o_cap_loop (s0 := s0) (base := base) rfl (openPosWritten_length_mod8 _ _ positions _)
        hbaseCap s3 hpc3 hfix3 hx14_3 hx15_3 hx16_3 hx17_3 (hx20_3.trans hx20_2)
        (fun a ha1 ha2 => (hbyte3 _).trans (hro2 a ha1 ha2))
        (fun u hu => (hbyte3 _).trans (by rw [← openPosMark_eq_openCapMark0]; exact hm2 u hu))
        (fun j hj => (hbyte3 _).trans (hw2 j hj)) 142 le_rfl
    have hpc128 : s4.pc = oPcAt 128 := by simpa only [ite_true] using hpc4
    have hcnt_143 : openCapCountPrefix positions 142 + capNodeFrontierCount positions 142 =
        capFrontierCount positions := by
      unfold openCapCountPrefix capFrontierCount
      exact (Finset.sum_range_succ _ 142).symm
    have hw4_8 : (base ++ openCapPrefix (tdNode trapdoor) positions 142).length % 8 = 0 := by
      rw [List.length_append, openCapPrefix_length]
      have hbase8 : base.length % 8 = 0 :=
        openPosWritten_length_mod8 (tdNode trapdoor) (tdSalt trapdoor) positions positions.card
      omega
    have hw4_cap : (base ++ openCapPrefix (tdNode trapdoor) positions 142).length +
        32 * capNodeFrontierCount positions 142 ≤ proofCap := by
      rw [List.length_append, openCapPrefix_length]; omega
    obtain ⟨cRoot, s5, hcRoot, hr5, hpc5, hx19_5, hx20_5, hw5⟩ :=
      o_root (s0 := s0) rfl hne hpc128 hfix4
        (by simpa only [show 3 * 142 = 426 from rfl] using hx14_4)
        (by simpa only [show 3 * 142 = 426 from rfl] using hx17_4)
        hx20_4 hw4_8 hw4_cap hro4 hm4 hw4
    rw [hpf_full] at hx20_5 hw5
    obtain ⟨sHalt, hr6, hpcH, hx5H, hx10H, hx11H, hbyteH⟩ :=
      o_epilogue hpc5 hx19_5 hx20_5 (referenceProof_length_le_cap (tdNode trapdoor) (tdSalt trapdoor) positions)
    have hrun_tot := ((((hr1.trans hr2).trans hr3).trans hr4).trans hr5).trans hr6
    have hfront_le := capFrontierCount_le_191 positions
    have hsteps_le : 23 + stP + 7 + cCap + cRoot + 3 + 1 ≤ submission.steps .opening := by
      rw [hsteps_open]; omega
    have hhalt := OpenRuns.halt hrun_tot (haltIdx := 153) (totalFuel := submission.steps .opening)
      (by decide) rfl hpcH hx5H hx10H hsteps_le
    refine ⟨{ exit := .success, state := sHalt, cycles := 23 + cyP + 7 + cCap + cRoot + 3 + 1, oracleCalls := 0 },
      hhalt, rfl, rfl, hx11H,
      fun j hj => (hbyteH _).trans (hw5 j hj), ?_⟩
    intro hcard
    change positions.card = 128 at hcard
    dsimp only
    omega

end CommitGolfCandidate
