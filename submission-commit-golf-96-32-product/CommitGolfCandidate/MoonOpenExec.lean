import CommitGolfCandidate.MoonMemory

/-! Exact deterministic symbolic execution of the 209-word opening image.
Tracks registers, read-only input/table framing, capMark scratch bytes, emitted proof bytes,
and exact step/cycle bounds with zero oracle calls. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-! ### 1. Program Counter, Trapdoor Views, and Deterministic Multi-Step Relation -/

def pcAt (idx : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * idx)

def tdNode (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (l idx : Nat) : Digest :=
  trapdoor.extractLsb' (8 * (levelBase l + nodeOffset l idx)) 256

def tdSalt (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index) : Salt128 :=
  trapdoor.extractLsb' (8 * (saltsOff + 16 * i.val)) 128

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

theorem OpenRuns.halt {s0 sHalt : MachineState} {steps cycles totalFuel : Nat}
    (hrun : OpenRuns s0 steps cycles sHalt)
    (hpc : sHalt.pc = pcAt 127)
    (hx5 : sHalt.getReg .x5 = 1#64)
    (hx10 : sHalt.getReg .x10 = 0#64)
    (hfuel : steps + 1 ≤ totalFuel) :
    execute (submission.image .opening) totalFuel s0 true =
      pure { exit := .success, state := sHalt, cycles := cycles + 1, oracleCalls := 0 } := by
  have hf : fetch (submission.image .opening) sHalt = some (.base .ECALL) :=
    opening_fetch sHalt 127 (by omega) hpc
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

/-! ### 2. MachineState, BitVec, and List Helpers -/

private theorem getReg_setReg_ne' (r r' : Reg) (h : r ≠ r') (s : MachineState) (v : Word) :
    (s.setReg r v).getReg r' = s.getReg r' :=
  MachineState.getReg_setReg_ne s r r' v h

private theorem getReg_setMem (s : MachineState) (a v : Word) (r : Reg) :
    (s.setMem a v).getReg r = s.getReg r := by cases r <;> rfl

private theorem getReg_setByte (s : MachineState) (a : Word) (b : BitVec 8) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by cases r <;> rfl

private theorem getReg_setHalfword (s : MachineState) (a : Word) (h : BitVec 16) (r : Reg) :
    (s.setHalfword a h).getReg r = s.getReg r := by cases r <;> rfl

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

private theorem bv16_zeroExtend_truncate (h : BitVec 16) :
    (h.zeroExtend 64).truncate 16 = h := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate, BitVec.zeroExtend, BitVec.toNat_setWidth]
  have hlt : h.toNat < 2 ^ 16 := h.isLt
  rw [Nat.mod_eq_of_lt (by omega : h.toNat < 2 ^ 64), Nat.mod_eq_of_lt hlt]

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

private theorem signExtend12_two_mul (j : Nat) (hj : j ≤ 16) :
    signExtend12 (BitVec.ofNat 12 (2 * j)) = BitVec.ofNat 64 (2 * j) := by
  interval_cases j <;> decide

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

private theorem nodeOffset_even (l idx : Nat) : nodeOffset l idx % 2 = 0 := by
  unfold nodeOffset gapOffset
  split <;> omega

private theorem levelBase_even (l : Nat) (hl : l ≤ 24) : levelBase l % 2 = 0 := by
  interval_cases l <;> decide

private theorem capMarkOff_step_disjoint (l : Nat) (hl1 : 15 ≤ l) (hl2 : l ≤ 23) :
    capMarkOff l + levelSize l ≤ capMarkOff (l + 1) := by
  interval_cases l <;> decide

/-! ### 3. Single-Instruction Step Lemmas -/

private theorem step_ADDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ADDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_ADD {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ADD rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ADD rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ADD rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 + s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SUB {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SUB rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SUB rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SUB rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 - s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SLLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SLLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SLLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SLLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 <<< shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SRLI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {shamt : BitVec 6}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SRLI rd rs1 shamt)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SRLI rd rs1 shamt)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SRLI rd rs1 shamt)) =
      some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 >>> shamt.toNat)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_XORI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.XORI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.XORI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.XORI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ^^^ signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_ANDI {s : MachineState} {idx : Nat} {rd rs1 : Reg} {imm : BitVec 12}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.ANDI rd rs1 imm)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.ANDI rd rs1 imm)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.ANDI rd rs1 imm)) =
      some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 &&& signExtend12 imm)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_OR {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.OR rd rs1 rs2)) :
    OpenRuns s 1 1 ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.OR rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.OR rd rs1 rs2)) =
      some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (s.getReg rs1 ||| s.getReg rs2)).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_DIVU {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.DIVU rd rs1 rs2)) :
    OpenRuns s 1 4 ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.DIVU rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.DIVU rd rs1 rs2)) =
      some ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (rv64_divu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_REMU {s : MachineState} {idx : Nat} {rd rs1 rs2 : Reg}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.REMU rd rs1 rs2)) :
    OpenRuns s 1 4 ((s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.REMU rd rs1 rs2)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.REMU rd rs1 rs2)) =
      some ((s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))).setPC (pcAt (idx + 1))) := by
    change some ((s.setReg rd (rv64_remu (s.getReg rs1) (s.getReg rs2))).setPC (s.pc + 4)) = _
    rw [hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_LD {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.LD rd rs1 off))
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

private theorem step_LBU {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.LBU rd rs1 off))
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

private theorem step_LHU {s : MachineState} {idx : Nat} {rd rs1 : Reg} {off : BitVec 12}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.LHU rd rs1 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 2 = true) :
    OpenRuns s 1 1
      ((s.setReg rd ((s.getHalfword (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.LHU rd rs1 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.LHU rd rs1 off)) =
      some ((s.setReg rd ((s.getHalfword (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 2 = true
            then some ((s.setReg rd ((s.getHalfword (s.getReg rs1 + signExtend12 off)).zeroExtend 64)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_SB {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SB rs1 rs2 off))
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

private theorem step_SH {s : MachineState} {idx : Nat} {rs1 rs2 : Reg} {off : BitVec 12}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.SH rs1 rs2 off))
    (hvalid : accessValid (s.getReg rs1 + signExtend12 off) 2 = true) :
    OpenRuns s 1 1
      ((s.setHalfword (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 16)).setPC (pcAt (idx + 1))) := by
  have hf : fetch (submission.image .opening) s = some (.base (.SH rs1 rs2 off)) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.SH rs1 rs2 off)) =
      some ((s.setHalfword (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 16)).setPC (pcAt (idx + 1))) := by
    change (if accessValid (s.getReg rs1 + signExtend12 off) 2 = true
            then some ((s.setHalfword (s.getReg rs1 + signExtend12 off) ((s.getReg rs2).truncate 16)).setPC (s.pc + 4))
            else none) = _
    rw [if_pos hvalid, hpc, pcAt_add4]
  exact OpenRuns.step hf hst

private theorem step_BEQ_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
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
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BEQ rs1 rs2 off))
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
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
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
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BNE rs1 rs2 off))
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

private theorem step_BGEU_taken {s : MachineState} {idx tgt : Nat} {rs1 rs2 : Reg} {off : BitVec 13}
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BGEU rs1 rs2 off))
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
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.BGEU rs1 rs2 off))
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
    (hidx : idx < 209) (hpc : s.pc = pcAt idx) (hi : openingInstr idx = .base (.JAL rd off))
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
    (hidx : idx < 209) (hpc : s.pc = pcAt idx)
    (hi : openingInstr idx = .base (.JALR .x0 .x1 (0#12)))
    (hx1 : s.getReg .x1 = pcAt retIdx) :
    OpenRuns s 1 1 (s.setPC (pcAt retIdx)) := by
  have hf : fetch (submission.image .opening) s = some (.base (.JALR .x0 .x1 (0#12))) := by
    rw [opening_fetch s idx hidx hpc, hi]
  have hst : ordinaryStep s (.base (.JALR .x0 .x1 (0#12))) = some (s.setPC (pcAt retIdx)) := by
    change some ((s.setReg .x0 (s.pc + 4)).setPC ((s.getReg .x1 + signExtend12 (0#12)) &&& ~~~1#64)) = _
    rw [show s.setReg .x0 (s.pc + 4) = s from rfl, hx1, pcAt_jalr_return retIdx]
  exact OpenRuns.step hf hst

/-! ### 4. Memory Framing Predicates -/

/-- Read-only regions: trapdoor `[4294971424, 5637149760)`, indices `[5637149760, 5771367488)`,
and embedded metadata `[68719475936, 68719476736)`. -/
def ReadOnlyPreserved (s0 s : MachineState) : Prop :=
  ∀ addr : Word,
    (4294971424 ≤ addr.toNat ∧ addr.toNat < 5771367488) ∨
    (68719475936 ≤ addr.toNat ∧ addr.toNat < 68719476736) →
    s.getMem addr = s0.getMem addr

/-- Exact byte contents of the proof output prefix `[10066334784, 10066334784 + bytes.length)`. -/
def ProofPrefix (s : MachineState) (bytes : List Byte) : Prop :=
  ∀ j (hj : j < bytes.length),
    s.getByte (BitVec.ofNat 64 (10066334784 + j)) = bytes[j]

/-- Level `l` cap-mark bytes in `[4096 + capMarkOff l, 4096 + capMarkOff l + levelSize l)`. -/
def CapLevelMarks (s : MachineState) (positions : Positions) (l : Nat) : Prop :=
  ∀ idx < levelSize l,
    s.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + idx)) =
      if capMark positions l idx then 1#8 else 0#8

private theorem readOnly_getMem_index {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState}
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (ordinal : Nat) (hord : ordinal < positions.card) :
    s.getMem (BitVec.ofNat 64 (5637149760 + 8 * ordinal)) =
      BitVec.ofNat 64 (openingIndex positions ordinal) := by
  have hcard := positions_card_le positions
  have haddr : (BitVec.ofNat 64 (5637149760 + 8 * ordinal)).toNat = 5637149760 + 8 * ordinal := by
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
    (off : Nat) (hoff : off < 1342178336) :
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

private theorem readOnly_setHalfword_proof {s0 s : MachineState} (dst : Nat) (h : BitVec 16)
    (hro : ReadOnlyPreserved s0 s) (hlo : 10066334784 ≤ dst) (hhi : dst < 18488507480) :
    ReadOnlyPreserved s0 (s.setHalfword (BitVec.ofNat 64 dst) h) := by
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
  simp only [MachineState.setHalfword, MachineState.getMem_setMem_ne hne]
  exact hro addr had

private theorem readOnly_setByte_cap {s0 s : MachineState} (dst : Nat) (b : BitVec 8)
    (hro : ReadOnlyPreserved s0 s) (hlo : 4096 ≤ dst) (hhi : dst < 4896) :
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

private theorem proofPrefix_setByte_cap {s : MachineState} {bytes : List Byte} (dst : Nat)
    (b : BitVec 8) (hp : ProofPrefix s bytes) (hbd : bytes.length ≤ 8422172696)
    (hlo : 4096 ≤ dst) (hhi : dst < 4896) :
    ProofPrefix (s.setByte (BitVec.ofNat 64 dst) b) bytes := by
  intro j hj
  rw [set_byte_read, if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
  exact hp j hj

private theorem chunk_tdSalt (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (i : Index)
    (j : Nat) (hj : j < 16) :
    trapdoor.extractLsb' (8 * (saltsOff + 16 * i.val + j)) 8 =
      (bitsToBytes (tdSalt trapdoor i) 16)[j]'(by simp [bitsToBytes]; exact hj) := by
  simp only [bitsToBytes, List.getElem_map, List.getElem_range, tdSalt]
  rw [extractLsb'_extractLsb' trapdoor (8 * (saltsOff + 16 * i.val)) 128 (8 * j) 8 (by omega)]
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

/-! ### 5. Parametric Halfword-Copy Subroutines (`copy16`, `copy30`, `copy32`) -/

private theorem openRuns_copy_halfword {s0 s : MachineState} {idx src dst j : Nat}
    (hidx : idx + 1 < 209) (hj : j < 16) (hpc : s.pc = pcAt idx)
    (hi0 : openingInstr idx = .base (.LHU .x6 .x10 (BitVec.ofNat 12 (2 * j))))
    (hi1 : openingInstr (idx + 1) = .base (.SH .x25 .x6 (BitVec.ofNat 12 (2 * j))))
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 dst)
    (hs_al : src % 2 = 0) (hd_al : dst % 2 = 0)
    (hs_bd : src + 2 * j + 2 ≤ 68719476736)
    (hd_lo : 10066334784 ≤ dst) (hd_hi : dst + 2 * j + 2 ≤ 18488507480)
    (hro : ReadOnlyPreserved s0 s) :
    ∃ s', OpenRuns s 2 2 s' ∧
      s'.pc = pcAt (idx + 2) ∧
      (∀ r, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved s0 s' ∧
      (∀ q < 2 ^ 64, s'.getByte (BitVec.ofNat 64 q) =
        if q = dst + 2 * j then s.getByte (BitVec.ofNat 64 (src + 2 * j))
        else if q = dst + 2 * j + 1 then s.getByte (BitVec.ofNat 64 (src + 2 * j + 1))
        else s.getByte (BitVec.ofNat 64 q)) := by
  have hse := signExtend12_two_mul j (by omega)
  have hsrcAddr : s.getReg .x10 + signExtend12 (BitVec.ofNat 12 (2 * j)) =
      BitVec.ofNat 64 (src + 2 * j) := by
    rw [hx10, hse, bv64_ofNat_add]
  have hvalid1 : accessValid (s.getReg .x10 + signExtend12 (BitVec.ofNat 12 (2 * j))) 2 = true := by
    rw [hsrcAddr]
    exact accessValid_ofNat (src + 2 * j) 2 hs_bd (by omega)
  have hr1 := step_LHU (by omega) hpc hi0 hvalid1
  let s1 := (s.setReg .x6 ((s.getHalfword (BitVec.ofNat 64 (src + 2 * j))).zeroExtend 64)).setPC
    (pcAt (idx + 1))
  have hr1' : OpenRuns s 1 1 s1 := by simpa only [hsrcAddr, s1] using hr1
  have hdstAddr : s1.getReg .x25 + signExtend12 (BitVec.ofNat 12 (2 * j)) =
      BitVec.ofNat 64 (dst + 2 * j) := by
    have hx25' : s1.getReg .x25 = BitVec.ofNat 64 dst := hx25
    rw [hx25', hse, bv64_ofNat_add]
  have hvalid2 : accessValid (s1.getReg .x25 + signExtend12 (BitVec.ofNat 12 (2 * j))) 2 = true := by
    rw [hdstAddr]
    exact accessValid_ofNat (dst + 2 * j) 2 (by omega) (by omega)
  have hr2 := step_SH hidx (rfl : s1.pc = pcAt (idx + 1)) hi1 hvalid2
  have hx6_trunc : (s1.getReg .x6).truncate 16 = s.getHalfword (BitVec.ofNat 64 (src + 2 * j)) :=
    bv16_zeroExtend_truncate _
  let s2 := (s1.setHalfword (BitVec.ofNat 64 (dst + 2 * j))
    (s.getHalfword (BitVec.ofNat 64 (src + 2 * j)))).setPC (pcAt (idx + 2))
  have hr2' : OpenRuns s1 1 1 s2 := by
    simpa only [hdstAddr, hx6_trunc, s2, show idx + 1 + 1 = idx + 2 by omega] using hr2
  refine ⟨s2, hr1'.trans hr2', rfl, ?_, ?_, ?_⟩
  · intro r hr
    simp only [s2, MachineState.getReg_setPC, getReg_setHalfword, s1]
    exact getReg_setReg_ne' .x6 r (Ne.symm hr) s _
  · intro addr had
    simp only [s2, MachineState.getMem_setPC]
    exact readOnly_setHalfword_proof (dst + 2 * j) _ (by
      intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha)
      (by omega) (by omega) addr had
  · intro q hq
    simp only [s2, getByte_setPC]
    have hmem1 : ∀ a, s1.getByte a = s.getByte a := fun a => by
      simp only [s1, getByte_setPC, getByte_setReg]
    have hhw1 : s1.getHalfword (BitVec.ofNat 64 (src + 2 * j)) =
        s.getHalfword (BitVec.ofNat 64 (src + 2 * j)) := rfl
    have hsrc_al' : (BitVec.ofNat 64 (src + 2 * j)).toNat % 2 = 0 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : src + 2 * j < 2 ^ 64)]; omega
    have hdst_al' : (BitVec.ofNat 64 (dst + 2 * j)).toNat % 2 = 0 := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : dst + 2 * j < 2 ^ 64)]; omega
    rw [← hhw1, copyHalfword_getByte s1 (BitVec.ofNat 64 (src + 2 * j))
      (BitVec.ofNat 64 (dst + 2 * j)) (BitVec.ofNat 64 q) hsrc_al' hdst_al']
    rw [hmem1, hmem1, hmem1]
    have hsrc1 : BitVec.ofNat 64 (src + 2 * j) + 1#64 = BitVec.ofNat 64 (src + 2 * j + 1) := by
      change BitVec.ofNat 64 (src + 2 * j) + BitVec.ofNat 64 1 = _
      exact bv64_ofNat_add _ _
    have hdst1 : BitVec.ofNat 64 (dst + 2 * j) + 1#64 = BitVec.ofNat 64 (dst + 2 * j + 1) := by
      change BitVec.ofNat 64 (dst + 2 * j) + BitVec.ofNat 64 1 = _
      exact bv64_ofNat_add _ _
    rw [hsrc1, hdst1]
    by_cases hq0 : q = dst + 2 * j
    · subst hq0; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (bv64_ofNat_ne hq (by omega) hq0), if_neg hq0]
      by_cases hq1 : q = dst + 2 * j + 1
      · subst hq1; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (bv64_ofNat_ne hq (by omega) hq1), if_neg hq1]

private theorem openRuns_copy_body {s0 s : MachineState} {base m src dst : Nat}
    (hm : m ≤ 16) (hbase : base + 2 * m < 209)
    (hcode : ∀ j < m,
      openingInstr (base + 2 * j) = .base (.LHU .x6 .x10 (BitVec.ofNat 12 (2 * j))) ∧
      openingInstr (base + 2 * j + 1) = .base (.SH .x25 .x6 (BitVec.ofNat 12 (2 * j))))
    (hpc : s.pc = pcAt base)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 src)
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 dst)
    (hs_al : src % 2 = 0) (hd_al : dst % 2 = 0)
    (hdisj : src + 2 * m ≤ dst)
    (hd_lo : 10066334784 ≤ dst) (hd_hi : dst + 2 * m ≤ 18488507480)
    (hro : ReadOnlyPreserved s0 s) :
    ∀ k ≤ m, ∃ s', OpenRuns s (2 * k) (2 * k) s' ∧
      s'.pc = pcAt (base + 2 * k) ∧
      (∀ r, r ≠ .x6 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved s0 s' ∧
      (∀ q < 2 ^ 64, s'.getByte (BitVec.ofNat 64 q) =
        if dst ≤ q ∧ q < dst + 2 * k then s.getByte (BitVec.ofNat 64 (src + (q - dst)))
        else s.getByte (BitVec.ofNat 64 q)) := by
  intro k hk
  induction k with
  | zero =>
    refine ⟨s, OpenRuns.refl s, hpc, fun _ _ => rfl, hro, ?_⟩
    intro q _
    rw [if_neg (by omega)]
  | succ k ih =>
    obtain ⟨sk, hrk, hpck, hregk, hrok, hbytek⟩ := ih (by omega)
    have hci := hcode k (by omega)
    obtain ⟨sk1, hrstep, hpc1, hreg1, hro1, hbyte1⟩ :=
      openRuns_copy_halfword (idx := base + 2 * k) (src := src) (dst := dst) (j := k)
        (by omega) (by omega) hpck hci.1 hci.2
        (by rw [hregk .x10 (by decide), hx10])
        (by rw [hregk .x25 (by decide), hx25])
        hs_al hd_al (by omega) hd_lo (by omega) hrok
    refine ⟨sk1, ?_, ?_, ?_, hro1, ?_⟩
    · simpa only [Nat.mul_succ] using hrk.trans hrstep
    · simpa only [Nat.mul_succ, Nat.add_assoc] using hpc1
    · intro r hr
      rw [hreg1 r hr, hregk r hr]
    · intro q hq
      rw [hbyte1 q hq]
      by_cases hq0 : q = dst + 2 * k
      · subst hq0
        rw [if_pos rfl, if_pos (by omega), hbytek (src + 2 * k) (by omega),
          if_neg (by omega), show src + (dst + 2 * k - dst) = src + 2 * k by omega]
      · rw [if_neg hq0]
        by_cases hq1 : q = dst + 2 * k + 1
        · subst hq1
          rw [if_pos rfl, if_pos (by omega), hbytek (src + 2 * k + 1) (by omega),
            if_neg (by omega), show src + (dst + 2 * k + 1 - dst) = src + 2 * k + 1 by omega]
        · rw [if_neg hq1, hbytek q hq]
          by_cases hin : dst ≤ q ∧ q < dst + 2 * k
          · rw [if_pos hin, if_pos (by omega)]
          · rw [if_neg hin, if_neg (by omega)]

private theorem openRuns_call_copy_to_proof {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s : MachineState} {callIdx copyBase m srcOff : Nat}
    {jOff : BitVec 21} {bytes chunk : List Byte}
    (hm : m ≤ 16) (hcall : callIdx + 1 < 209) (hbase : copyBase + 2 * m < 209)
    (hjal : openingInstr callIdx = .base (.JAL .x1 jOff))
    (htgt : pcAt callIdx + signExtend21 jOff = pcAt copyBase)
    (hcode : ∀ j < m,
      openingInstr (copyBase + 2 * j) = .base (.LHU .x6 .x10 (BitVec.ofNat 12 (2 * j))) ∧
      openingInstr (copyBase + 2 * j + 1) = .base (.SH .x25 .x6 (BitVec.ofNat 12 (2 * j))))
    (hretI : openingInstr (copyBase + 2 * m) = .base (.JALR .x0 .x1 (0#12)))
    (hadvI : openingInstr (callIdx + 1) = .base (.ADDI .x25 .x25 (BitVec.ofNat 12 (2 * m))))
    (hpc : s.pc = pcAt callIdx)
    (hx10 : s.getReg .x10 = BitVec.ofNat 64 (4294971424 + srcOff))
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (10066334784 + bytes.length))
    (hsrc_al : srcOff % 2 = 0) (hsrc_bd : srcOff + 2 * m ≤ 1342178336)
    (hbytes_al : bytes.length % 2 = 0) (hbytes_bd : bytes.length + 2 * m ≤ 8422172696)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s)
    (hproof : ProofPrefix s bytes)
    (hclen : chunk.length = 2 * m)
    (hchunk : ∀ j (hj : j < 2 * m),
      trapdoor.extractLsb' (8 * (srcOff + j)) 8 = chunk[j]'(by omega)) :
    ∃ s', OpenRuns s (2 * m + 3) (2 * m + 3) s' ∧
      s'.pc = pcAt (callIdx + 2) ∧
      s'.getReg .x25 = BitVec.ofNat 64 (10066334784 + (bytes ++ chunk).length) ∧
      (∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x25 → s'.getReg r = s.getReg r) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s' ∧
      ProofPrefix s' (bytes ++ chunk) ∧
      (∀ q < 4896, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) := by
  let s0 := submission.initialState .opening (trapdoor, positions)
  have hr_jal := step_JAL (by omega) hpc hjal htgt
  let s1 := (s.setReg .x1 (pcAt (callIdx + 1))).setPC (pcAt copyBase)
  have hro1 : ReadOnlyPreserved s0 s1 := by
    intro a ha; simp only [s1, MachineState.getMem_setPC, MachineState.getMem_setReg]; exact hro a ha
  obtain ⟨s2, hr_body, hpc2, hreg2, hro2, hbyte2⟩ :=
    openRuns_copy_body (s0 := s0) (s := s1) (base := copyBase) (m := m)
      (src := 4294971424 + srcOff) (dst := 10066334784 + bytes.length)
      hm hbase hcode rfl (by exact hx10) (by exact hx25)
      (by omega) (by omega) (by omega) (by omega) (by omega) hro1 m (Nat.le_refl m)
  have hx1_2 : s2.getReg .x1 = pcAt (callIdx + 1) := by
    rw [hreg2 .x1 (by decide)]; rfl
  have hr_ret := step_JALR_x0 hbase hpc2 hretI hx1_2
  let s3 := s2.setPC (pcAt (callIdx + 1))
  have hr_adv := step_ADDI hcall (rfl : s3.pc = pcAt (callIdx + 1)) hadvI
  have hx25_3 : s3.getReg .x25 = BitVec.ofNat 64 (10066334784 + bytes.length) := by
    simp only [s3, MachineState.getReg_setPC, hreg2 .x25 (by decide)]; exact hx25
  have hse := signExtend12_two_mul m hm
  have hnew25 : s3.getReg .x25 + signExtend12 (BitVec.ofNat 12 (2 * m)) =
      BitVec.ofNat 64 (10066334784 + (bytes ++ chunk).length) := by
    rw [hx25_3, hse, bv64_ofNat_add, List.length_append, hclen, Nat.add_assoc]
  let s4 := (s3.setReg .x25 (BitVec.ofNat 64 (10066334784 + (bytes ++ chunk).length))).setPC
    (pcAt (callIdx + 2))
  have hr_adv' : OpenRuns s3 1 1 s4 := by
    simpa only [hnew25, s4, show callIdx + 1 + 1 = callIdx + 2 by omega] using hr_adv
  have htot : OpenRuns s (2 * m + 3) (2 * m + 3) s4 := by
    have h := ((hr_jal.trans hr_body).trans hr_ret).trans hr_adv'
    simpa only [show 1 + 2 * m + 1 + 1 = 2 * m + 3 by omega] using h
  refine ⟨s4, htot, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro r hr1 hr6 hr25
    simp only [s4, MachineState.getReg_setPC, getReg_setReg_ne' .x25 r (Ne.symm hr25),
      s3, hreg2 r hr6, s1, getReg_setReg_ne' .x1 r (Ne.symm hr1)]
  · intro a ha
    simp only [s4, MachineState.getMem_setPC, MachineState.getMem_setReg, s3]
    exact hro2 a ha
  · intro j hj
    have hj_len : j < bytes.length + 2 * m := by rw [List.length_append, hclen] at hj; exact hj
    simp only [s4, getByte_setPC, getByte_setReg, s3]
    rw [hbyte2 (10066334784 + j) (by omega)]
    by_cases hlt : j < bytes.length
    · rw [if_neg (by omega)]
      simp only [s1, getByte_setPC, getByte_setReg]
      rw [hproof j hlt, list_getElem_append_left bytes chunk j hlt]
    · rw [if_pos (by omega)]
      simp only [s1, getByte_setPC, getByte_setReg]
      have hidxEq : 4294971424 + srcOff + (10066334784 + j - (10066334784 + bytes.length)) =
          4294971424 + (srcOff + (j - bytes.length)) := by omega
      rw [hidxEq, readOnly_getByte_trapdoor hro (srcOff + (j - bytes.length)) (by omega)]
      rw [list_getElem_append_right bytes chunk j (by omega) hj]
      exact hchunk (j - bytes.length) (by omega)
  · intro q hq
    simp only [s4, getByte_setPC, getByte_setReg, s3]
    rw [hbyte2 q (by omega), if_neg (by omega)]
    simp only [s1, getByte_setPC, getByte_setReg]

private theorem copy16_code : ∀ j < 8,
    openingInstr (128 + 2 * j) = .base (.LHU .x6 .x10 (BitVec.ofNat 12 (2 * j))) ∧
    openingInstr (128 + 2 * j + 1) = .base (.SH .x25 .x6 (BitVec.ofNat 12 (2 * j))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩

private theorem copy30_code : ∀ j < 15,
    openingInstr (145 + 2 * j) = .base (.LHU .x6 .x10 (BitVec.ofNat 12 (2 * j))) ∧
    openingInstr (145 + 2 * j + 1) = .base (.SH .x25 .x6 (BitVec.ofNat 12 (2 * j))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩

private theorem copy32_code : ∀ j < 16,
    openingInstr (176 + 2 * j) = .base (.LHU .x6 .x10 (BitVec.ofNat 12 (2 * j))) ∧
    openingInstr (176 + 2 * j + 1) = .base (.SH .x25 .x6 (BitVec.ofNat 12 (2 * j))) := by
  intro j hj; interval_cases j <;> exact ⟨rfl, rfl⟩

/-! ### 6. Epilogue and Entry Blocks -/

private theorem openRuns_epilogue {s : MachineState} {proofLen : Nat}
    (hpc : s.pc = pcAt 124)
    (hx25 : s.getReg .x25 = BitVec.ofNat 64 (10066334784 + proofLen))
    (hx26 : s.getReg .x26 = BitVec.ofNat 64 10066334784) :
    ∃ sHalt, OpenRuns s 3 3 sHalt ∧
      sHalt.pc = pcAt 127 ∧
      sHalt.getReg .x5 = 1#64 ∧
      sHalt.getReg .x10 = 0#64 ∧
      sHalt.getReg .x11 = BitVec.ofNat 64 proofLen ∧
      sHalt.mem = s.mem := by
  have h1 := step_SUB (by omega) hpc (rfl : openingInstr 124 = .base (.SUB .x11 .x25 .x26))
  have hsub : s.getReg .x25 - s.getReg .x26 = BitVec.ofNat 64 proofLen := by
    rw [hx25, hx26, bv64_ofNat_sub _ _ (by omega), Nat.add_sub_cancel_left]
  let s1 := (s.setReg .x11 (BitVec.ofNat 64 proofLen)).setPC (pcAt 125)
  have h1' : OpenRuns s 1 1 s1 := by simpa only [hsub, s1] using h1
  have h2 := step_ADDI (by omega) (rfl : s1.pc = pcAt 125)
    (rfl : openingInstr 125 = .base (.ADDI .x5 .x0 (1#12)))
  let s2 := (s1.setReg .x5 1#64).setPC (pcAt 126)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hv : s1.getReg .x0 + signExtend12 (1#12) = 1#64 := by
      change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 126)
    (rfl : openingInstr 126 = .base (.ADDI .x10 .x0 (0#12)))
  let s3 := (s2.setReg .x10 0#64).setPC (pcAt 127)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hv : s2.getReg .x0 + signExtend12 (0#12) = 0#64 := by
      change (0#64 : Word) + signExtend12 (0#12) = 0#64; decide
    simpa only [hv, s3] using h3
  exact ⟨s3, (h1'.trans h2').trans h3', rfl, rfl, rfl, rfl, rfl⟩

private theorem opening_initial_regs (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    s0.pc = pcAt 0 ∧
    s0.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
    s0.getReg .x12 = BitVec.ofNat 64 4294971424 ∧
    s0.getReg .x13 = BitVec.ofNat 64 5637149760 ∧
    s0.getReg .x15 = BitVec.ofNat 64 10066334784 ∧
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
      s5.getReg .x24 = BitVec.ofNat 64 5637149760 ∧
      s5.getReg .x25 = BitVec.ofNat 64 10066334784 ∧
      s5.getReg .x26 = BitVec.ofNat 64 10066334784 ∧
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
  let s2 := (s1.setReg .x24 (BitVec.ofNat 64 5637149760)).setPC (pcAt 2)
  have h2' : OpenRuns s1 1 1 s2 := by
    have hr : s1.getReg .x13 = BitVec.ofNat 64 5637149760 := hx13
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s2] using h2
  have h3 := step_ADDI (by omega) (rfl : s2.pc = pcAt 2)
    (rfl : openingInstr 2 = .base (.ADDI .x25 .x15 (0#12)))
  let s3 := (s2.setReg .x25 (BitVec.ofNat 64 10066334784)).setPC (pcAt 3)
  have h3' : OpenRuns s2 1 1 s3 := by
    have hr : s2.getReg .x15 = BitVec.ofNat 64 10066334784 := hx15
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s3] using h3
  have h4 := step_ADDI (by omega) (rfl : s3.pc = pcAt 3)
    (rfl : openingInstr 3 = .base (.ADDI .x26 .x15 (0#12)))
  let s4 := (s3.setReg .x26 (BitVec.ofNat 64 10066334784)).setPC (pcAt 4)
  have h4' : OpenRuns s3 1 1 s4 := by
    have hr : s3.getReg .x15 = BitVec.ofNat 64 10066334784 := hx15
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s4] using h4
  have h5 := step_ADDI (by omega) (rfl : s4.pc = pcAt 4)
    (rfl : openingInstr 4 = .base (.ADDI .x27 .x16 (0#12)))
  let s5 := (s4.setReg .x27 (BitVec.ofNat 64 positions.card)).setPC (pcAt 5)
  have h5' : OpenRuns s4 1 1 s5 := by
    have hr : s4.getReg .x16 = BitVec.ofNat 64 positions.card := hx16
    simpa only [hr, hse0, bv64_ofNat_add, Nat.add_zero, s5] using h5
  exact ⟨s5, (((h1'.trans h2').trans h3').trans h4').trans h5',
    rfl, hx2, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem openRuns_entry_nonzero (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (hne : positions.card ≠ 0) :
    let s0 := submission.initialState .opening (trapdoor, positions)
    ∃ s19, OpenRuns s0 19 19 s19 ∧
      s19.pc = pcAt 19 ∧
      s19.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s19.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s19.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff) ∧
      s19.getReg .x19 = 3#64 ∧
      s19.getReg .x20 = BitVec.ofNat 64 FULL_TRIPLETS ∧
      s19.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s19.getReg .x24 = BitVec.ofNat 64 5637149760 ∧
      s19.getReg .x25 = BitVec.ofNat 64 10066334784 ∧
      s19.getReg .x26 = BitVec.ofNat 64 10066334784 ∧
      s19.getReg .x27 = BitVec.ofNat 64 positions.card ∧
      s19.mem = s0.mem := by
  intro s0
  obtain ⟨s5, hr5, hpc5, hx2, hx9, hx24, hx25, hx26, hx27, hmem5⟩ :=
    openRuns_entry_prefix trapdoor positions
  have hcard := positions_card_le positions
  have h6 := step_BEQ_not_taken (by omega) hpc5
    (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (476#13)))
    (by rw [hx27]; exact bv64_ofNat_ne (by omega) (by decide) hne)
  let s6 := s5.setPC (pcAt 6)
  have h7 := step_ADDI (by omega) (rfl : s6.pc = pcAt 6)
    (rfl : openingInstr 6 = .base (.ADDI .x6 .x0 (256#12)))
  let s7 := (s6.setReg .x6 (BitVec.ofNat 64 256)).setPC (pcAt 7)
  have h7' : OpenRuns s6 1 1 s7 := by
    have hv : s6.getReg .x0 + signExtend12 (256#12) = BitVec.ofNat 64 256 := by
      change (0#64 : Word) + signExtend12 (256#12) = BitVec.ofNat 64 256; decide
    simpa only [hv, s7] using h7
  have h8 := step_SLLI (by omega) (rfl : s7.pc = pcAt 7)
    (rfl : openingInstr 7 = .base (.SLLI .x6 .x6 (11#6)))
  let s8 := (s7.setReg .x6 (BitVec.ofNat 64 524288)).setPC (pcAt 8)
  have h8' : OpenRuns s7 1 1 s8 := by
    have hv : s7.getReg .x6 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 524288 := by
      change BitVec.ofNat 64 256 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 524288; decide
    simpa only [hv, s8] using h8
  have h9 := step_SLLI (by omega) (rfl : s8.pc = pcAt 8)
    (rfl : openingInstr 8 = .base (.SLLI .x6 .x6 (11#6)))
  let s9 := (s8.setReg .x6 (BitVec.ofNat 64 1073741824)).setPC (pcAt 9)
  have h9' : OpenRuns s8 1 1 s9 := by
    have hv : s8.getReg .x6 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 1073741824 := by
      change BitVec.ofNat 64 524288 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 1073741824; decide
    simpa only [hv, s9] using h9
  have h10 := step_ADDI (by omega) (rfl : s9.pc = pcAt 9)
    (rfl : openingInstr 9 = .base (.ADDI .x6 .x6 (1056#12)))
  let s10 := (s9.setReg .x6 (BitVec.ofNat 64 saltsOff)).setPC (pcAt 10)
  have h10' : OpenRuns s9 1 1 s10 := by
    have hv : s9.getReg .x6 + signExtend12 (1056#12) = BitVec.ofNat 64 saltsOff := by
      change BitVec.ofNat 64 1073741824 + signExtend12 (1056#12) = BitVec.ofNat 64 saltsOff
      rw [saltsOff_eq]; decide
    simpa only [hv, s10] using h10
  have h11 := step_ADD (by omega) (rfl : s10.pc = pcAt 10)
    (rfl : openingInstr 10 = .base (.ADD .x18 .x9 .x6))
  let s11 := (s10.setReg .x18 (BitVec.ofNat 64 (4294971424 + saltsOff))).setPC (pcAt 11)
  have h11' : OpenRuns s10 1 1 s11 := by
    have hr9 : s10.getReg .x9 = BitVec.ofNat 64 4294971424 := hx9
    simpa only [hr9, show s10.getReg .x6 = BitVec.ofNat 64 saltsOff from rfl, bv64_ofNat_add, s11] using h11
  have h12 := step_ADDI (by omega) (rfl : s11.pc = pcAt 11)
    (rfl : openingInstr 11 = .base (.ADDI .x19 .x0 (3#12)))
  let s12 := (s11.setReg .x19 3#64).setPC (pcAt 12)
  have h12' : OpenRuns s11 1 1 s12 := by
    have hv : s11.getReg .x0 + signExtend12 (3#12) = 3#64 := by
      change (0#64 : Word) + signExtend12 (3#12) = 3#64; decide
    simpa only [hv, s12] using h12
  have h13 := step_ADDI (by omega) (rfl : s12.pc = pcAt 12)
    (rfl : openingInstr 12 = .base (.ADDI .x20 .x0 (1#12)))
  let s13 := (s12.setReg .x20 (BitVec.ofNat 64 1)).setPC (pcAt 13)
  have h13' : OpenRuns s12 1 1 s13 := by
    have hv : s12.getReg .x0 + signExtend12 (1#12) = BitVec.ofNat 64 1 := by
      change (0#64 : Word) + signExtend12 (1#12) = BitVec.ofNat 64 1; decide
    simpa only [hv, s13] using h13
  have h14 := step_SLLI (by omega) (rfl : s13.pc = pcAt 13)
    (rfl : openingInstr 13 = .base (.SLLI .x20 .x20 (11#6)))
  let s14 := (s13.setReg .x20 (BitVec.ofNat 64 2048)).setPC (pcAt 14)
  have h14' : OpenRuns s13 1 1 s14 := by
    have hv : s13.getReg .x20 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 2048 := by
      change BitVec.ofNat 64 1 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 2048; decide
    simpa only [hv, s14] using h14
  have h15 := step_ADDI (by omega) (rfl : s14.pc = pcAt 14)
    (rfl : openingInstr 14 = .base (.ADDI .x20 .x20 (682#12)))
  let s15 := (s14.setReg .x20 (BitVec.ofNat 64 2730)).setPC (pcAt 15)
  have h15' : OpenRuns s14 1 1 s15 := by
    have hv : s14.getReg .x20 + signExtend12 (682#12) = BitVec.ofNat 64 2730 := by
      change BitVec.ofNat 64 2048 + signExtend12 (682#12) = BitVec.ofNat 64 2730; decide
    simpa only [hv, s15] using h15
  have h16 := step_SLLI (by omega) (rfl : s15.pc = pcAt 15)
    (rfl : openingInstr 15 = .base (.SLLI .x20 .x20 (11#6)))
  let s16 := (s15.setReg .x20 (BitVec.ofNat 64 5591040)).setPC (pcAt 16)
  have h16' : OpenRuns s15 1 1 s16 := by
    have hv : s15.getReg .x20 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 5591040 := by
      change BitVec.ofNat 64 2730 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 5591040; decide
    simpa only [hv, s16] using h16
  have h17 := step_ADDI (by omega) (rfl : s16.pc = pcAt 16)
    (rfl : openingInstr 16 = .base (.ADDI .x20 .x20 (1365#12)))
  let s17 := (s16.setReg .x20 (BitVec.ofNat 64 FULL_TRIPLETS)).setPC (pcAt 17)
  have h17' : OpenRuns s16 1 1 s17 := by
    have hv : s16.getReg .x20 + signExtend12 (1365#12) = BitVec.ofNat 64 FULL_TRIPLETS := by
      change BitVec.ofNat 64 5591040 + signExtend12 (1365#12) = BitVec.ofNat 64 FULL_TRIPLETS
      rw [full_triplets_eq]; decide
    simpa only [hv, s17] using h17
  have h18 := step_ADDI (by omega) (rfl : s17.pc = pcAt 17)
    (rfl : openingInstr 17 = .base (.ADDI .x21 .x0 (2#12)))
  let s18 := (s17.setReg .x21 (BitVec.ofNat 64 2)).setPC (pcAt 18)
  have h18' : OpenRuns s17 1 1 s18 := by
    have hv : s17.getReg .x0 + signExtend12 (2#12) = BitVec.ofNat 64 2 := by
      change (0#64 : Word) + signExtend12 (2#12) = BitVec.ofNat 64 2; decide
    simpa only [hv, s18] using h18
  have h19 := step_SLLI (by omega) (rfl : s18.pc = pcAt 18)
    (rfl : openingInstr 18 = .base (.SLLI .x21 .x21 (11#6)))
  let s19 := (s18.setReg .x21 (BitVec.ofNat 64 4096)).setPC (pcAt 19)
  have h19' : OpenRuns s18 1 1 s19 := by
    have hv : s18.getReg .x21 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096 := by
      change BitVec.ofNat 64 2 <<< (11#6 : BitVec 6).toNat = BitVec.ofNat 64 4096; decide
    simpa only [hv, s19] using h19
  have h5_12 := ((((((hr5.trans h6).trans h7').trans h8').trans h9').trans h10').trans h11').trans h12'
  have htot := ((((((h5_12.trans h13').trans h14').trans h15').trans h16').trans h17').trans h18').trans h19'
  exact ⟨s19, htot, rfl, hx2, hx9, rfl, rfl, rfl, rfl, hx24, hx25, hx26, hx27, hmem5⟩

/-! ### 7. Record Loop (`19..85`) -/

private def capLeafNat (i : Nat) : Nat := (i / 3) >>> 14

private def capMark15Prefix (positions : Positions) (t idx : Nat) : Bool :=
  decide (∃ u < t, capLeafNat (openingIndex positions u) = idx)

private theorem capMark15Prefix_card (positions : Positions) (idx : Nat) :
    capMark15Prefix positions positions.card idx = capMark positions 15 idx := by
  simp only [capMark15Prefix, capMark_15]
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

/-- Loop invariant preserved across the record-loop body (`19..79`). -/
private structure RecInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (t : Nat) (bytes : List Byte) (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475936
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff)
  rx19 : s.getReg .x19 = 3#64
  rx20 : s.getReg .x20 = BitVec.ofNat 64 FULL_TRIPLETS
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx24 : s.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * t)
  rx25 : s.getReg .x25 = BitVec.ofNat 64 (10066334784 + bytes.length)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 10066334784
  rx27 : s.getReg .x27 = BitVec.ofNat 64 (positions.card - t)
  evenLen : bytes.length % 2 = 0
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  proof : ProofPrefix s bytes
  cap15 : ∀ c < 342, s.getByte (BitVec.ofNat 64 (4096 + c)) =
    if capMark15Prefix positions t c then 1#8 else 0#8

private theorem RecInv.setPC {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {bytes : List Byte} {s : MachineState}
    (inv : RecInv trapdoor positions t bytes s) (pc : Word) :
    RecInv trapdoor positions t bytes (s.setPC pc) :=
  ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx25,
   inv.rx26, inv.rx27, inv.evenLen, inv.ro, inv.proof, inv.cap15⟩

private theorem RecInv.after_copy {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {bytes chunk : List Byte} {s s' : MachineState}
    (inv : RecInv trapdoor positions t bytes s)
    (hx25 : s'.getReg .x25 = BitVec.ofNat 64 (10066334784 + (bytes ++ chunk).length))
    (hreg : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x25 → s'.getReg r = s.getReg r)
    (heven : chunk.length % 2 = 0)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s')
    (hpr : ProofPrefix s' (bytes ++ chunk))
    (hcap : ∀ q < 4896, s'.getByte (BitVec.ofNat 64 q) = s.getByte (BitVec.ofNat 64 q)) :
    RecInv trapdoor positions t (bytes ++ chunk) s' :=
  ⟨by rw [hreg .x2 (by decide) (by decide) (by decide)]; exact inv.rx2,
   by rw [hreg .x9 (by decide) (by decide) (by decide)]; exact inv.rx9,
   by rw [hreg .x18 (by decide) (by decide) (by decide)]; exact inv.rx18,
   by rw [hreg .x19 (by decide) (by decide) (by decide)]; exact inv.rx19,
   by rw [hreg .x20 (by decide) (by decide) (by decide)]; exact inv.rx20,
   by rw [hreg .x21 (by decide) (by decide) (by decide)]; exact inv.rx21,
   by rw [hreg .x24 (by decide) (by decide) (by decide)]; exact inv.rx24,
   hx25,
   by rw [hreg .x26 (by decide) (by decide) (by decide)]; exact inv.rx26,
   by rw [hreg .x27 (by decide) (by decide) (by decide)]; exact inv.rx27,
   by simp only [List.length_append]; have := inv.evenLen; omega,
   hro, hpr,
   fun c hc => by rw [hcap (4096 + c) (by omega)]; exact inv.cap15 c hc⟩

private theorem openRuns_rec_salt {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {bytes : List Byte} {s : MachineState}
    (ht : t < positions.card) (hpc : s.pc = pcAt 19)
    (hbd : bytes.length + 16 ≤ 8422172696)
    (inv : RecInv trapdoor positions t bytes s) :
    let idx : Index := (positions.sort (· ≤ ·))[t]'(by simpa using ht)
    let bytes1 := bytes ++ bitsToBytes (tdSalt trapdoor idx) 16
    ∃ s1, OpenRuns s 22 22 s1 ∧
      s1.pc = pcAt 24 ∧
      s1.getReg .x8 = BitVec.ofNat 64 idx.val ∧
      RecInv trapdoor positions t bytes1 s1 := by
  intro idx bytes1
  have hcard := positions_card_le positions
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hopen : openingIndex positions t = idx.val := by simp only [openingIndex, dif_pos ht]; rfl
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have haddr19 : s.getReg .x24 + signExtend12 (0#12) = BitVec.ofNat 64 (5637149760 + 8 * t) := by
    rw [inv.rx24, hse0, bv64_ofNat_add, Nat.add_zero]
  have hld := step_LD (by omega) hpc (rfl : openingInstr 19 = .base (.LD .x8 .x24 (0#12)))
    (by rw [haddr19]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s19 := (s.setReg .x8 (BitVec.ofNat 64 idx.val)).setPC (pcAt 20)
  have hld' : OpenRuns s 1 1 s19 := by
    have hmem := readOnly_getMem_index inv.ro t ht
    rw [hopen] at hmem
    simpa only [haddr19, hmem, s19] using hld
  have hsll := step_SLLI (by omega) (rfl : s19.pc = pcAt 20)
    (rfl : openingInstr 20 = .base (.SLLI .x7 .x8 (4#6)))
  let s20 := (s19.setReg .x7 (BitVec.ofNat 64 (16 * idx.val))).setPC (pcAt 21)
  have hsll' : OpenRuns s19 1 1 s20 := by
    have hsh : s19.getReg .x8 <<< (4#6 : BitVec 6).toNat = BitVec.ofNat 64 (16 * idx.val) := by
      change BitVec.ofNat 64 idx.val <<< 4 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hsh, s20] using hsll
  have hadd := step_ADD (by omega) (rfl : s20.pc = pcAt 21)
    (rfl : openingInstr 21 = .base (.ADD .x10 .x18 .x7))
  let s21 := (s20.setReg .x10 (BitVec.ofNat 64 (4294971424 + (saltsOff + 16 * idx.val)))).setPC (pcAt 22)
  have hadd' : OpenRuns s20 1 1 s21 := by
    have hr18 : s20.getReg .x18 = BitVec.ofNat 64 (4294971424 + saltsOff) := inv.rx18
    have hr7 : s20.getReg .x7 = BitVec.ofNat 64 (16 * idx.val) := rfl
    have hsum : s20.getReg .x18 + s20.getReg .x7 =
        BitVec.ofNat 64 (4294971424 + (saltsOff + 16 * idx.val)) := by
      rw [hr18, hr7, bv64_ofNat_add]; congr 1; omega
    simpa only [hsum, s21] using hadd
  have hinv21 : RecInv trapdoor positions t bytes s21 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx25,
     inv.rx26, inv.rx27, inv.evenLen, inv.ro, inv.proof, inv.cap15⟩
  have hsalts : saltsOff = 1073742880 := saltsOff_eq
  obtain ⟨s24, hrcopy, hpc24, hx25_24, hreg24, hro24, hpr24, hcap24⟩ :=
    openRuns_call_copy_to_proof (callIdx := 22) (copyBase := 128) (m := 8)
      (srcOff := saltsOff + 16 * idx.val) (jOff := 424#21)
      (bytes := bytes) (chunk := bitsToBytes (tdSalt trapdoor idx) 16)
      (by omega) (by omega) (by omega) rfl (by decide) copy16_code rfl rfl
      rfl rfl hinv21.rx25 (by omega) (by omega) hinv21.evenLen hbd
      hinv21.ro hinv21.proof (bitsToBytes_length _ 16)
      (fun j hj => chunk_tdSalt trapdoor idx j hj)
  refine ⟨s24, ((hld'.trans hsll').trans hadd').trans hrcopy, hpc24, ?_, ?_⟩
  · rw [hreg24 .x8 (by decide) (by decide) (by decide)]; rfl
  · exact hinv21.after_copy hx25_24 hreg24 (by simp only [bitsToBytes_length]) hro24 hpr24 hcap24

/-- Two consecutive `copy32` calls from `x28 + 32*k1`, `x28 + 32*k2` into the proof buffer. -/
private theorem openRuns_l0_pair {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g k1 k2 a b c1 c2 : Nat} {j1 j2 : BitVec 21} {imm1 imm2 : BitVec 12}
    {bytes : List Byte} {s : MachineState}
    (hg : g < FULL_TRIPLETS) (hc1 : c1 + 5 < 209) (hc2 : c2 = c1 + 3)
    (hk1 : k1 < 3) (hk2 : k2 < 3)
    (ha : a = 3 * g + k1) (hb : b = 3 * g + k2)
    (hse1 : signExtend12 imm1 = BitVec.ofNat 64 (32 * k1))
    (hse2 : signExtend12 imm2 = BitVec.ofNat 64 (32 * k2))
    (hi0 : openingInstr c1 = .base (.ADDI .x10 .x28 imm1))
    (hi1 : openingInstr (c1 + 1) = .base (.JAL .x1 j1))
    (htgt1 : pcAt (c1 + 1) + signExtend21 j1 = pcAt 176)
    (hi2 : openingInstr (c1 + 2) = .base (.ADDI .x25 .x25 (32#12)))
    (hi3 : openingInstr c2 = .base (.ADDI .x10 .x28 imm2))
    (hi4 : openingInstr (c2 + 1) = .base (.JAL .x1 j2))
    (htgt2 : pcAt (c2 + 1) + signExtend21 j2 = pcAt 176)
    (hi5 : openingInstr (c2 + 2) = .base (.ADDI .x25 .x25 (32#12)))
    (hpc : s.pc = pcAt c1)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 g)
    (hx28 : s.getReg .x28 = BitVec.ofNat 64 (4294971424 + 96 * g))
    (hbd_extra : bytes.length + 64 ≤ 8422172696)
    (inv : RecInv trapdoor positions t bytes s) :
    let chunk := bitsToBytes (tdNode trapdoor 0 a) 32 ++ bitsToBytes (tdNode trapdoor 0 b) 32
    ∃ s', OpenRuns s 72 72 s' ∧
      s'.pc = pcAt (c2 + 3) ∧
      s'.getReg .x22 = BitVec.ofNat 64 g ∧
      RecInv trapdoor positions t (bytes ++ chunk) s' := by
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
  have ha_bd : levelBase 0 + nodeOffset 0 a + 32 ≤ 1342178336 := by
    have := nodeOffset_lt_treeBytes 0 a (by omega) ha_lt; omega
  have hb_bd : levelBase 0 + nodeOffset 0 b + 32 ≤ 1342178336 := by
    have := nodeOffset_lt_treeBytes 0 b (by omega) hb_lt; omega
  -- First sibling
  have hstep1 := step_ADDI (by omega) hpc hi0
  let s1 := (s.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase 0 + nodeOffset 0 a)))).setPC
    (pcAt (c1 + 1))
  have hstep1' : OpenRuns s 1 1 s1 := by
    have hsum : s.getReg .x28 + signExtend12 imm1 =
        BitVec.ofNat 64 (4294971424 + (levelBase 0 + nodeOffset 0 a)) := by
      rw [hx28, hse1, bv64_ofNat_add]; congr 1; omega
    simpa only [hsum, s1] using hstep1
  have hinv1 : RecInv trapdoor positions t bytes s1 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx25,
     inv.rx26, inv.rx27, inv.evenLen, inv.ro, inv.proof, inv.cap15⟩
  obtain ⟨s2, hrc1, hpc2, hx25_2, hreg2, hro2, hpr2, hcap2⟩ :=
    openRuns_call_copy_to_proof (callIdx := c1 + 1) (copyBase := 176) (m := 16)
      (srcOff := levelBase 0 + nodeOffset 0 a) (jOff := j1)
      (bytes := bytes) (chunk := bitsToBytes (tdNode trapdoor 0 a) 32)
      (by omega) (by omega) (by omega) hi1 htgt1 copy32_code rfl
      (by simpa only [show c1 + 1 + 1 = c1 + 2 by omega] using hi2)
      rfl rfl hinv1.rx25
      (by have := nodeOffset_even 0 a; change (0 + nodeOffset 0 a) % 2 = 0; omega) ha_bd
      hinv1.evenLen (by omega) hinv1.ro hinv1.proof (bitsToBytes_length _ 32)
      (fun j hj => chunk_tdNode trapdoor 0 a 32 j (by omega) hj)
  have hinv2 : RecInv trapdoor positions t (bytes ++ bitsToBytes (tdNode trapdoor 0 a) 32) s2 :=
    hinv1.after_copy hx25_2 hreg2 (by simp only [bitsToBytes_length]) hro2 hpr2 hcap2
  -- Second sibling
  have hpc2' : s2.pc = pcAt c2 := by rw [hpc2]; congr 1; omega
  have hx28_2 : s2.getReg .x28 = BitVec.ofNat 64 (4294971424 + 96 * g) := by
    rw [hreg2 .x28 (by decide) (by decide) (by decide)]; exact hx28
  have hx22_2 : s2.getReg .x22 = BitVec.ofNat 64 g := by
    rw [hreg2 .x22 (by decide) (by decide) (by decide)]; exact hx22
  have hstep2 := step_ADDI (by omega) hpc2' hi3
  let s3 := (s2.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase 0 + nodeOffset 0 b)))).setPC
    (pcAt (c2 + 1))
  have hstep2' : OpenRuns s2 1 1 s3 := by
    have hsum : s2.getReg .x28 + signExtend12 imm2 =
        BitVec.ofNat 64 (4294971424 + (levelBase 0 + nodeOffset 0 b)) := by
      rw [hx28_2, hse2, bv64_ofNat_add]; congr 1; omega
    simpa only [hsum, s3] using hstep2
  have hinv3 : RecInv trapdoor positions t (bytes ++ bitsToBytes (tdNode trapdoor 0 a) 32) s3 :=
    ⟨hinv2.rx2, hinv2.rx9, hinv2.rx18, hinv2.rx19, hinv2.rx20, hinv2.rx21, hinv2.rx24, hinv2.rx25,
     hinv2.rx26, hinv2.rx27, hinv2.evenLen, hinv2.ro, hinv2.proof, hinv2.cap15⟩
  obtain ⟨s4, hrc2, hpc4, hx25_4, hreg4, hro4, hpr4, hcap4⟩ :=
    openRuns_call_copy_to_proof (callIdx := c2 + 1) (copyBase := 176) (m := 16)
      (srcOff := levelBase 0 + nodeOffset 0 b) (jOff := j2)
      (bytes := bytes ++ bitsToBytes (tdNode trapdoor 0 a) 32)
      (chunk := bitsToBytes (tdNode trapdoor 0 b) 32)
      (by omega) (by omega) (by omega) hi4 htgt2 copy32_code rfl
      (by simpa only [show c2 + 1 + 1 = c2 + 2 by omega] using hi5)
      rfl rfl hinv3.rx25
      (by have := nodeOffset_even 0 b; change (0 + nodeOffset 0 b) % 2 = 0; omega) hb_bd
      hinv3.evenLen (by simp only [List.length_append, bitsToBytes_length]; omega)
      hinv3.ro hinv3.proof (bitsToBytes_length _ 32)
      (fun j hj => chunk_tdNode trapdoor 0 b 32 j (by omega) hj)
  have hinv4 := hinv3.after_copy hx25_4 hreg4 (by simp only [bitsToBytes_length]) hro4 hpr4 hcap4
  have happ : (bytes ++ bitsToBytes (tdNode trapdoor 0 a) 32) ++ bitsToBytes (tdNode trapdoor 0 b) 32 =
      bytes ++ chunk := List.append_assoc _ _ _
  rw [happ] at hinv4
  refine ⟨s4, ((hstep1'.trans hrc1).trans hstep2').trans hrc2, hpc4, ?_, hinv4⟩
  rw [hreg4 .x22 (by decide) (by decide) (by decide)]; exact hx22_2

private theorem openRuns_rec_l0 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {bytes : List Byte} {s : MachineState}
    (hpc : s.pc = pcAt 24)
    (idx : Index) (hx8 : s.getReg .x8 = BitVec.ofNat 64 idx.val)
    (hbd_extra : bytes.length + 64 ≤ 8422172696)
    (inv : RecInv trapdoor positions t bytes s) :
    let bytes1 := bytes ++ l0SiblingsProof (tdNode trapdoor) idx
    ∃ steps cycles s1, OpenRuns s steps cycles s1 ∧
      steps ≤ 83 ∧ cycles ≤ 89 ∧
      s1.pc = pcAt 54 ∧
      s1.getReg .x22 = BitVec.ofNat 64 (idx.val / 3) ∧
      RecInv trapdoor positions t bytes1 s1 := by
  intro bytes1
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
  set g := idx.val / 3
  set r := idx.val % 3
  have hdiv := step_DIVU (by omega) hpc (rfl : openingInstr 24 = .base (.DIVU .x22 .x8 .x19))
  let s25 := (s.setReg .x22 (BitVec.ofNat 64 g)).setPC (pcAt 25)
  have hdiv' : OpenRuns s 1 4 s25 := by
    have hv : rv64_divu (s.getReg .x8) (s.getReg .x19) = BitVec.ofNat 64 g := by
      rw [hx8, inv.rx19, rv64_divu_three, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : idx.val < 2 ^ 64)]
    simpa only [hv, s25] using hdiv
  have hrem := step_REMU (by omega) (rfl : s25.pc = pcAt 25)
    (rfl : openingInstr 25 = .base (.REMU .x23 .x8 .x19))
  let s26 := (s25.setReg .x23 (BitVec.ofNat 64 r)).setPC (pcAt 26)
  have hrem' : OpenRuns s25 1 4 s26 := by
    have hv : rv64_remu (s25.getReg .x8) (s25.getReg .x19) = BitVec.ofNat 64 r := by
      have hr8 : s25.getReg .x8 = BitVec.ofNat 64 idx.val := hx8
      have hr19 : s25.getReg .x19 = 3#64 := inv.rx19
      rw [hr8, hr19, rv64_remu_three, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : idx.val < 2 ^ 64)]
    simpa only [hv, s26] using hrem
  have hinv26 : RecInv trapdoor positions t bytes s26 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx25,
     inv.rx26, inv.rx27, inv.evenLen, inv.ro, inv.proof, inv.cap15⟩
  by_cases hg : g = FULL_TRIPLETS
  · have hbeq := step_BEQ_taken (by omega) (rfl : s26.pc = pcAt 26)
      (rfl : openingInstr 26 = .base (.BEQ .x22 .x20 (112#13)))
      (by change BitVec.ofNat 64 g = s.getReg .x20; rw [hg, inv.rx20])
      (by decide : pcAt 26 + signExtend13 (112#13) = pcAt 54)
    have hbytes1 : bytes1 = bytes := by
      change bytes ++ (if g = FULL_TRIPLETS then [] else _) = bytes
      rw [if_pos hg, List.append_nil]
    rw [hbytes1]
    exact ⟨3, 9, s26.setPC (pcAt 54), (hdiv'.trans hrem').trans hbeq, by omega, by omega,
      rfl, rfl, hinv26.setPC (pcAt 54)⟩
  · have hg_lt : g < FULL_TRIPLETS := by omega
    have hbeq := step_BEQ_not_taken (by omega) (rfl : s26.pc = pcAt 26)
      (rfl : openingInstr 26 = .base (.BEQ .x22 .x20 (112#13)))
      (by change BitVec.ofNat 64 g ≠ s.getReg .x20; rw [inv.rx20]
          exact bv64_ofNat_ne (by omega) (by omega) hg)
    let s27 := s26.setPC (pcAt 27)
    have h27 := step_SLLI (by omega) (rfl : s27.pc = pcAt 27)
      (rfl : openingInstr 27 = .base (.SLLI .x6 .x22 (6#6)))
    let s28 := (s27.setReg .x6 (BitVec.ofNat 64 (64 * g))).setPC (pcAt 28)
    have h27' : OpenRuns s27 1 1 s28 := by
      have hv : s27.getReg .x22 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * g) := by
        change BitVec.ofNat 64 g <<< 6 = _; rw [bv64_shl]; congr 1; omega
      simpa only [hv, s28] using h27
    have h28 := step_SLLI (by omega) (rfl : s28.pc = pcAt 28)
      (rfl : openingInstr 28 = .base (.SLLI .x7 .x22 (5#6)))
    let s29 := (s28.setReg .x7 (BitVec.ofNat 64 (32 * g))).setPC (pcAt 29)
    have h28' : OpenRuns s28 1 1 s29 := by
      have hv : s28.getReg .x22 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (32 * g) := by
        change BitVec.ofNat 64 g <<< 5 = _; rw [bv64_shl]; congr 1; omega
      simpa only [hv, s29] using h28
    have h29 := step_ADD (by omega) (rfl : s29.pc = pcAt 29)
      (rfl : openingInstr 29 = .base (.ADD .x28 .x6 .x7))
    let s30 := (s29.setReg .x28 (BitVec.ofNat 64 (96 * g))).setPC (pcAt 30)
    have h29' : OpenRuns s29 1 1 s30 := by
      have hv : s29.getReg .x6 + s29.getReg .x7 = BitVec.ofNat 64 (96 * g) := by
        change BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 (32 * g) = _
        rw [bv64_ofNat_add]; congr 1; omega
      simpa only [hv, s30] using h29
    have h30 := step_ADD (by omega) (rfl : s30.pc = pcAt 30)
      (rfl : openingInstr 30 = .base (.ADD .x28 .x9 .x28))
    let s31 := (s30.setReg .x28 (BitVec.ofNat 64 (4294971424 + 96 * g))).setPC (pcAt 31)
    have h30' : OpenRuns s30 1 1 s31 := by
      have hr9 : s30.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
      have hv : s30.getReg .x9 + s30.getReg .x28 = BitVec.ofNat 64 (4294971424 + 96 * g) := by
        rw [hr9]; change BitVec.ofNat 64 4294971424 + BitVec.ofNat 64 (96 * g) = _
        exact bv64_ofNat_add _ _
      simpa only [hv, s31] using h30
    have hpre : OpenRuns s 7 13 s31 :=
      (((((hdiv'.trans hrem').trans hbeq).trans h27').trans h28').trans h29').trans h30'
    have hinv31 : RecInv trapdoor positions t bytes s31 :=
      ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx25,
       inv.rx26, inv.rx27, inv.evenLen, inv.ro, inv.proof, inv.cap15⟩
    by_cases hr0 : r = 0
    · have h31 := step_BEQ_taken (by omega) (rfl : s31.pc = pcAt 31)
        (rfl : openingInstr 31 = .base (.BEQ .x23 .x0 (40#13)))
        (by change BitVec.ofNat 64 r = 0#64; rw [hr0])
        (by decide : pcAt 31 + signExtend13 (40#13) = pcAt 41)
      let s41 := s31.setPC (pcAt 41)
      obtain ⟨s47, hrpair, hpc47, hx22_47, inv47⟩ :=
        openRuns_l0_pair (c1 := 41) (c2 := 44) (j1 := 536#21) (j2 := 524#21)
          (imm1 := 32#12) (imm2 := 64#12) (k1 := 1) (k2 := 2) (a := 3 * g + 1) (b := 3 * g + 2)
          hg_lt (by omega) rfl (by omega) (by omega) rfl rfl (by decide) (by decide)
          rfl rfl (by decide) rfl rfl rfl (by decide) rfl
          rfl rfl rfl hbd_extra (hinv31.setPC (pcAt 41))
      have h47 := step_JAL (by omega) hpc47 (rfl : openingInstr 47 = .base (.JAL .x0 (28#21)))
        (by decide : pcAt 47 + signExtend21 (28#21) = pcAt 54)
      have hbytes1 : bytes1 = bytes ++ (bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32 ++
          bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32) := by
        change bytes ++ (if g = FULL_TRIPLETS then [] else
          if r = 0 then bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32 ++
            bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32
          else _) = _
        rw [if_neg hg, if_pos hr0]
      rw [hbytes1]
      exact ⟨81, 87, (s47.setReg .x0 (pcAt 48)).setPC (pcAt 54),
        ((hpre.trans h31).trans hrpair).trans h47, by omega, by omega,
        rfl, hx22_47, inv47.setPC (pcAt 54)⟩
    · have h31 := step_BEQ_not_taken (by omega) (rfl : s31.pc = pcAt 31)
        (rfl : openingInstr 31 = .base (.BEQ .x23 .x0 (40#13)))
        (by change BitVec.ofNat 64 r ≠ BitVec.ofNat 64 0; exact bv64_ofNat_ne (by omega) (by decide) hr0)
      let s32 := s31.setPC (pcAt 32)
      have h32 := step_ADDI (by omega) (rfl : s32.pc = pcAt 32)
        (rfl : openingInstr 32 = .base (.ADDI .x7 .x0 (1#12)))
      let s33 := (s32.setReg .x7 (BitVec.ofNat 64 1)).setPC (pcAt 33)
      have h32' : OpenRuns s32 1 1 s33 := by
        have hv : s32.getReg .x0 + signExtend12 (1#12) = BitVec.ofNat 64 1 := by
          change (0#64 : Word) + signExtend12 (1#12) = BitVec.ofNat 64 1; decide
        simpa only [hv, s33] using h32
      have hinv33 : RecInv trapdoor positions t bytes s33 :=
        ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx25,
         inv.rx26, inv.rx27, inv.evenLen, inv.ro, inv.proof, inv.cap15⟩
      by_cases hr1 : r = 1
      · have h33 := step_BEQ_taken (by omega) (rfl : s33.pc = pcAt 33)
          (rfl : openingInstr 33 = .base (.BEQ .x23 .x7 (60#13)))
          (by change BitVec.ofNat 64 r = BitVec.ofNat 64 1; rw [hr1])
          (by decide : pcAt 33 + signExtend13 (60#13) = pcAt 48)
        let s48 := s33.setPC (pcAt 48)
        obtain ⟨s54, hrpair, hpc54, hx22_54, inv54⟩ :=
          openRuns_l0_pair (c1 := 48) (c2 := 51) (j1 := 508#21) (j2 := 496#21)
            (imm1 := 0#12) (imm2 := 64#12) (k1 := 0) (k2 := 2) (a := 3 * g) (b := 3 * g + 2)
            hg_lt (by omega) rfl (by omega) (by omega) (by omega) rfl (by decide) (by decide)
            rfl rfl (by decide) rfl rfl rfl (by decide) rfl
            rfl rfl rfl hbd_extra (hinv33.setPC (pcAt 48))
        have hbytes1 : bytes1 = bytes ++ (bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
            bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32) := by
          change bytes ++ (if g = FULL_TRIPLETS then [] else
            if r = 0 then _ else
            if r = 1 then bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
              bitsToBytes (tdNode trapdoor 0 (3 * g + 2)) 32
            else _) = _
          rw [if_neg hg, if_neg hr0, if_pos hr1]
        rw [hbytes1]
        exact ⟨82, 88, s54, (((hpre.trans h31).trans h32').trans h33).trans hrpair,
          by omega, by omega, hpc54, hx22_54, inv54⟩
      · have h33 := step_BEQ_not_taken (by omega) (rfl : s33.pc = pcAt 33)
          (rfl : openingInstr 33 = .base (.BEQ .x23 .x7 (60#13)))
          (by change BitVec.ofNat 64 r ≠ BitVec.ofNat 64 1; exact bv64_ofNat_ne (by omega) (by decide) hr1)
        let s34 := s33.setPC (pcAt 34)
        obtain ⟨s40, hrpair, hpc40, hx22_40, inv40⟩ :=
          openRuns_l0_pair (c1 := 34) (c2 := 37) (j1 := 564#21) (j2 := 552#21)
            (imm1 := 0#12) (imm2 := 32#12) (k1 := 0) (k2 := 1) (a := 3 * g) (b := 3 * g + 1)
            hg_lt (by omega) rfl (by omega) (by omega) (by omega) rfl (by decide) (by decide)
            rfl rfl (by decide) rfl rfl rfl (by decide) rfl
            rfl rfl rfl hbd_extra (hinv33.setPC (pcAt 34))
        have h40 := step_JAL (by omega) hpc40 (rfl : openingInstr 40 = .base (.JAL .x0 (56#21)))
          (by decide : pcAt 40 + signExtend21 (56#21) = pcAt 54)
        have hbytes1 : bytes1 = bytes ++ (bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
            bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32) := by
          change bytes ++ (if g = FULL_TRIPLETS then [] else
            if r = 0 then _ else
            if r = 1 then _ else
            bitsToBytes (tdNode trapdoor 0 (3 * g)) 32 ++
              bitsToBytes (tdNode trapdoor 0 (3 * g + 1)) 32) = _
          rw [if_neg hg, if_neg hr0, if_neg hr1]
        rw [hbytes1]
        exact ⟨83, 89, (s40.setReg .x0 (pcAt 41)).setPC (pcAt 54),
          ((((hpre.trans h31).trans h32').trans h33).trans hrpair).trans h40,
          by omega, by omega, rfl, hx22_40, inv40.setPC (pcAt 54)⟩

private theorem openRuns_rec_l1 {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g : Nat} {bytes : List Byte} {s : MachineState}
    (hg : g ≤ FULL_TRIPLETS) (hpc : s.pc = pcAt 54)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 g)
    (hbd : bytes.length + 32 ≤ 8422172696)
    (inv : RecInv trapdoor positions t bytes s) :
    let bytes1 := bytes ++ bitsToBytes (tdNode trapdoor 1 (g ^^^ 1)) 32
    ∃ s1, OpenRuns s 42 42 s1 ∧
      s1.pc = pcAt 63 ∧
      s1.getReg .x22 = BitVec.ofNat 64 g ∧
      RecInv trapdoor positions t bytes1 s1 := by
  intro bytes1
  have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
  have hls1 : levelSize 1 = 5592406 := levelSize_1
  set sib := g ^^^ 1
  have hsib_lt : sib < levelSize 1 := by
    rw [hls1]
    exact xor_one_lt_even (m := 2796203) (by omega)
  have h54 := step_XORI (by omega) hpc (rfl : openingInstr 54 = .base (.XORI .x28 .x22 (1#12)))
  let s55 := (s.setReg .x28 (BitVec.ofNat 64 sib)).setPC (pcAt 55)
  have h54' : OpenRuns s 1 1 s55 := by
    rw [hx22, bv64_xor1 g (by omega)] at h54; exact h54
  have h55 := step_SRLI (by omega) (rfl : s55.pc = pcAt 55)
    (rfl : openingInstr 55 = .base (.SRLI .x6 .x28 (1#6)))
  let s56 := (s55.setReg .x6 (BitVec.ofNat 64 (sib / 2))).setPC (pcAt 56)
  have h55' : OpenRuns s55 1 1 s56 := by
    have hv : s55.getReg .x28 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (sib / 2) := by
      change BitVec.ofNat 64 sib >>> 1 = _
      rw [bv64_ushr sib 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s56] using h55
  have h56 := step_ADD (by omega) (rfl : s56.pc = pcAt 56)
    (rfl : openingInstr 56 = .base (.ADD .x28 .x28 .x6))
  let s57 := (s56.setReg .x28 (BitVec.ofNat 64 (sib + sib / 2))).setPC (pcAt 57)
  have h56' : OpenRuns s56 1 1 s57 := by
    have hv : s56.getReg .x28 + s56.getReg .x6 = BitVec.ofNat 64 (sib + sib / 2) := by
      change BitVec.ofNat 64 sib + BitVec.ofNat 64 (sib / 2) = _
      exact bv64_ofNat_add _ _
    simpa only [hv, s57] using h56
  have h57 := step_SLLI (by omega) (rfl : s57.pc = pcAt 57)
    (rfl : openingInstr 57 = .base (.SLLI .x28 .x28 (5#6)))
  let s58 := (s57.setReg .x28 (BitVec.ofNat 64 (nodeOffset 1 sib))).setPC (pcAt 58)
  have h57' : OpenRuns s57 1 1 s58 := by
    have hv : s57.getReg .x28 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (nodeOffset 1 sib) := by
      change BitVec.ofNat 64 (sib + sib / 2) <<< 5 = _
      rw [bv64_shl]; congr 1
      change (sib + sib / 2) * 32 = gapOffset sib
      unfold gapOffset; omega
    simpa only [hv, s58] using h57
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have haddr58 : s58.getReg .x2 + signExtend12 (32#12) = BitVec.ofNat 64 (68719475936 + 32 * 1) := by
    have hr2 : s58.getReg .x2 = BitVec.ofNat 64 68719475936 := inv.rx2
    rw [hr2, hse32, bv64_ofNat_add]
  have h58 := step_LD (by omega) (rfl : s58.pc = pcAt 58)
    (rfl : openingInstr 58 = .base (.LD .x6 .x2 (32#12)))
    (by rw [haddr58]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s59 := (s58.setReg .x6 (BitVec.ofNat 64 (levelBase 1))).setPC (pcAt 59)
  have h58' : OpenRuns s58 1 1 s59 := by
    have hmem : s58.getMem (BitVec.ofNat 64 (68719475936 + 32 * 1)) = BitVec.ofNat 64 (levelBase 1) :=
      readOnly_getMem_data_base inv.ro 1 (by omega)
    simpa only [haddr58, hmem, s59] using h58
  have h59 := step_ADD (by omega) (rfl : s59.pc = pcAt 59)
    (rfl : openingInstr 59 = .base (.ADD .x10 .x9 .x6))
  let s60 := (s59.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase 1))).setPC (pcAt 60)
  have h59' : OpenRuns s59 1 1 s60 := by
    have hr9 : s59.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
    rw [hr9] at h59
    simpa only [show s59.getReg .x6 = BitVec.ofNat 64 (levelBase 1) from rfl, bv64_ofNat_add, s60] using h59
  have h60 := step_ADD (by omega) (rfl : s60.pc = pcAt 60)
    (rfl : openingInstr 60 = .base (.ADD .x10 .x10 .x28))
  let s61 := (s60.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase 1 + nodeOffset 1 sib)))).setPC
    (pcAt 61)
  have h60' : OpenRuns s60 1 1 s61 := by
    have hv : s60.getReg .x10 + s60.getReg .x28 =
        BitVec.ofNat 64 (4294971424 + (levelBase 1 + nodeOffset 1 sib)) := by
      change BitVec.ofNat 64 (4294971424 + levelBase 1) + BitVec.ofNat 64 (nodeOffset 1 sib) = _
      rw [bv64_ofNat_add, Nat.add_assoc]
    simpa only [hv, s61] using h60
  have hinv61 : RecInv trapdoor positions t bytes s61 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx25,
     inv.rx26, inv.rx27, inv.evenLen, inv.ro, inv.proof, inv.cap15⟩
  have htb : treeBytes = 1073742880 := treeBytes_eq
  have hno_bd : levelBase 1 + nodeOffset 1 sib + 32 ≤ 1342178336 := by
    have := nodeOffset_lt_treeBytes 1 sib (by omega) hsib_lt; omega
  obtain ⟨s63, hrcopy, hpc63, hx25_63, hreg63, hro63, hpr63, hcap63⟩ :=
    openRuns_call_copy_to_proof (callIdx := 61) (copyBase := 176) (m := 16)
      (srcOff := levelBase 1 + nodeOffset 1 sib) (jOff := 460#21)
      (bytes := bytes) (chunk := bitsToBytes (tdNode trapdoor 1 sib) 32)
      (by omega) (by omega) (by omega) rfl (by decide) copy32_code rfl rfl
      rfl rfl hinv61.rx25
      (by have h1 := levelBase_even 1 (by omega); have h2 := nodeOffset_even 1 sib; omega) hno_bd
      hinv61.evenLen hbd hinv61.ro hinv61.proof (bitsToBytes_length _ 32)
      (fun j hj => chunk_tdNode trapdoor 1 sib 32 j (by omega) hj)
  have htot := ((((((h54'.trans h55').trans h56').trans h57').trans h58').trans h59').trans h60').trans hrcopy
  refine ⟨s63, htot, hpc63, ?_,
    hinv61.after_copy hx25_63 hreg63 (by simp only [bitsToBytes_length]) hro63 hpr63 hcap63⟩
  rw [hreg63 .x22 (by decide) (by decide) (by decide)]; exact hx22

private def binStepBytes (trapdoor : BitVec (8 * submission.sizes.trapdoor)) (g step : Nat) :
    List Byte :=
  let l := 2 + step
  let sib := (g >>> (step + 1)) ^^^ 1
  if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 30 else []

private theorem openRuns_rec_bin_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g step : Nat} {bytes : List Byte} {s : MachineState}
    (hg : g ≤ FULL_TRIPLETS) (hstep : step < 13) (hpc : s.pc = pcAt 65)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 (g >>> step))
    (hx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + step)))
    (hx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15))
    (hbd : bytes.length + 30 ≤ 8422172696)
    (inv : RecInv trapdoor positions t bytes s) :
    let bytes1 := bytes ++ binStepBytes trapdoor g step
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 45 ∧
      s1.pc = (if step + 1 < 13 then pcAt 65 else pcAt 79) ∧
      s1.getReg .x22 = BitVec.ofNat 64 (g >>> (step + 1)) ∧
      s1.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) ∧
      s1.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) ∧
      bytes1.length ≤ bytes.length + 30 ∧
      RecInv trapdoor positions t bytes1 s1 := by
  intro bytes1
  have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
  have hg_lt : g < 2 ^ 64 := by omega
  have hgs_le : g >>> step ≤ g := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  have hgs1_le : g >>> (step + 1) ≤ g := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  set l := 2 + step
  set idx := g >>> (step + 1)
  set sib := idx ^^^ 1
  have hsib_lt64 : sib < 2 ^ 64 := by
    rcases Nat.even_or_odd' idx with ⟨q, hq | hq⟩
    · rw [show sib = (2 * q) ^^^ 1 from by rw [← hq], xor_one_even]; omega
    · rw [show sib = (2 * q + 1) ^^^ 1 from by rw [← hq], xor_one_odd]; omega
  have hls_le := levelSize_le_max l (by omega)
  have h65 := step_SRLI (by omega) hpc (rfl : openingInstr 65 = .base (.SRLI .x22 .x22 (1#6)))
  let s66 := (s.setReg .x22 (BitVec.ofNat 64 idx)).setPC (pcAt 66)
  have h65' : OpenRuns s 1 1 s66 := by
    have hv : s.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 idx := by
      rw [hx22]; change BitVec.ofNat 64 (g >>> step) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), nat_ushr_ushr1]
    simpa only [hv, s66] using h65
  have h66 := step_XORI (by omega) (rfl : s66.pc = pcAt 66)
    (rfl : openingInstr 66 = .base (.XORI .x28 .x22 (1#12)))
  let s67 := (s66.setReg .x28 (BitVec.ofNat 64 sib)).setPC (pcAt 67)
  have h66' : OpenRuns s66 1 1 s67 := by
    have hv : s66.getReg .x22 ^^^ signExtend12 (1#12) = BitVec.ofNat 64 sib :=
      bv64_xor1 idx (by omega)
    simpa only [hv, s67] using h66
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have haddr67 : s67.getReg .x29 + signExtend12 (8#12) = BitVec.ofNat 64 (68719475936 + 32 * l + 8) := by
    have hr29 : s67.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := hx29
    rw [hr29, hse8, bv64_ofNat_add]
  have h67 := step_LD (by omega) (rfl : s67.pc = pcAt 67)
    (rfl : openingInstr 67 = .base (.LD .x7 .x29 (8#12)))
    (by rw [haddr67]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s68 := (s67.setReg .x7 (BitVec.ofNat 64 (levelSize l))).setPC (pcAt 68)
  have h67' : OpenRuns s67 1 1 s68 := by
    have hmem : s67.getMem (BitVec.ofNat 64 (68719475936 + 32 * l + 8)) = BitVec.ofNat 64 (levelSize l) :=
      readOnly_getMem_data_size inv.ro l (by omega)
    simpa only [haddr67, hmem, s68] using h67
  have hpre : OpenRuns s 3 3 s68 := (h65'.trans h66').trans h67'
  have hx28_toNat : (s68.getReg .x28).toNat = sib := by
    change (BitVec.ofNat 64 sib).toNat = sib
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsib_lt64]
  have hx7_toNat : (s68.getReg .x7).toNat = levelSize l := by
    change (BitVec.ofNat 64 (levelSize l)).toNat = levelSize l
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hinv68 : RecInv trapdoor positions t bytes s68 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx25,
     inv.rx26, inv.rx27, inv.evenLen, inv.ro, inv.proof, inv.cap15⟩
  have hto77 : ∃ n77 s77, OpenRuns s68 n77 n77 s77 ∧ n77 ≤ 40 ∧
      s77.pc = pcAt 77 ∧
      s77.getReg .x22 = BitVec.ofNat 64 idx ∧
      s77.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) ∧
      s77.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) ∧
      bytes1.length ≤ bytes.length + 30 ∧
      RecInv trapdoor positions t bytes1 s77 := by
    by_cases hsib_lt : sib < levelSize l
    · have h68 := step_BGEU_not_taken (by omega) (rfl : s68.pc = pcAt 68)
        (rfl : openingInstr 68 = .base (.BGEU .x28 .x7 (36#13)))
        (by rw [hx28_toNat, hx7_toNat]; exact hsib_lt)
      let s69 := s68.setPC (pcAt 69)
      have h69 := step_SRLI (by omega) (rfl : s69.pc = pcAt 69)
        (rfl : openingInstr 69 = .base (.SRLI .x6 .x28 (1#6)))
      let s70 := (s69.setReg .x6 (BitVec.ofNat 64 (sib / 2))).setPC (pcAt 70)
      have h69' : OpenRuns s69 1 1 s70 := by
        have hv : s69.getReg .x28 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (sib / 2) := by
          change BitVec.ofNat 64 sib >>> 1 = _
          rw [bv64_ushr sib 1 hsib_lt64, Nat.shiftRight_eq_div_pow]
        simpa only [hv, s70] using h69
      have h70 := step_ADD (by omega) (rfl : s70.pc = pcAt 70)
        (rfl : openingInstr 70 = .base (.ADD .x28 .x28 .x6))
      let s71 := (s70.setReg .x28 (BitVec.ofNat 64 (sib + sib / 2))).setPC (pcAt 71)
      have h70' : OpenRuns s70 1 1 s71 := by
        have hv : s70.getReg .x28 + s70.getReg .x6 = BitVec.ofNat 64 (sib + sib / 2) := by
          change BitVec.ofNat 64 sib + BitVec.ofNat 64 (sib / 2) = _; exact bv64_ofNat_add _ _
        simpa only [hv, s71] using h70
      have h71 := step_SLLI (by omega) (rfl : s71.pc = pcAt 71)
        (rfl : openingInstr 71 = .base (.SLLI .x28 .x28 (5#6)))
      let s72 := (s71.setReg .x28 (BitVec.ofNat 64 (nodeOffset l sib))).setPC (pcAt 72)
      have h71' : OpenRuns s71 1 1 s72 := by
        have hv : s71.getReg .x28 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (nodeOffset l sib) := by
          change BitVec.ofNat 64 (sib + sib / 2) <<< 5 = _
          rw [bv64_shl]; congr 1
          have hl0 : l ≠ 0 := by omega
          unfold nodeOffset gapOffset
          rw [if_neg hl0]; omega
        simpa only [hv, s72] using h71
      have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
      have haddr72 : s72.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475936 + 32 * l) := by
        have hr29 : s72.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := hx29
        rw [hr29, hse0, bv64_ofNat_add, Nat.add_zero]
      have h72 := step_LD (by omega) (rfl : s72.pc = pcAt 72)
        (rfl : openingInstr 72 = .base (.LD .x6 .x29 (0#12)))
        (by rw [haddr72]; exact accessValid_ofNat _ 8 (by omega) (by omega))
      let s73 := (s72.setReg .x6 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 73)
      have h72' : OpenRuns s72 1 1 s73 := by
        have hmem : s72.getMem (BitVec.ofNat 64 (68719475936 + 32 * l)) = BitVec.ofNat 64 (levelBase l) :=
          readOnly_getMem_data_base inv.ro l (by omega)
        simpa only [haddr72, hmem, s73] using h72
      have h73 := step_ADD (by omega) (rfl : s73.pc = pcAt 73)
        (rfl : openingInstr 73 = .base (.ADD .x10 .x9 .x6))
      let s74 := (s73.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 74)
      have h73' : OpenRuns s73 1 1 s74 := by
        have hr9 : s73.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
        rw [hr9] at h73
        simpa only [show s73.getReg .x6 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s74] using h73
      have h74 := step_ADD (by omega) (rfl : s74.pc = pcAt 74)
        (rfl : openingInstr 74 = .base (.ADD .x10 .x10 .x28))
      let s75 := (s74.setReg .x10 (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)))).setPC
        (pcAt 75)
      have h74' : OpenRuns s74 1 1 s75 := by
        have hv : s74.getReg .x10 + s74.getReg .x28 =
            BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l sib)) := by
          change BitVec.ofNat 64 (4294971424 + levelBase l) + BitVec.ofNat 64 (nodeOffset l sib) = _
          rw [bv64_ofNat_add, Nat.add_assoc]
        simpa only [hv, s75] using h74
      have hinv75 : RecInv trapdoor positions t bytes s75 :=
        ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx25,
         inv.rx26, inv.rx27, inv.evenLen, inv.ro, inv.proof, inv.cap15⟩
      have htb : treeBytes = 1073742880 := treeBytes_eq
      have hno_bd : levelBase l + nodeOffset l sib + 30 ≤ 1342178336 := by
        have := nodeOffset_lt_treeBytes l sib (by omega) hsib_lt; omega
      obtain ⟨s77, hrcopy, hpc77, hx25_77, hreg77, hro77, hpr77, hcap77⟩ :=
        openRuns_call_copy_to_proof (callIdx := 75) (copyBase := 145) (m := 15)
          (srcOff := levelBase l + nodeOffset l sib) (jOff := 280#21)
          (bytes := bytes) (chunk := bitsToBytes (tdNode trapdoor l sib) 30)
          (by omega) (by omega) (by omega) rfl (by decide) copy30_code rfl rfl
          rfl rfl hinv75.rx25
          (by have h1 := levelBase_even l (by omega); have h2 := nodeOffset_even l sib; omega) hno_bd
          hinv75.evenLen hbd hinv75.ro hinv75.proof (bitsToBytes_length _ 30)
          (fun j hj => chunk_tdNode trapdoor l sib 30 j (by omega) hj)
      have hb1 : bytes1 = bytes ++ bitsToBytes (tdNode trapdoor l sib) 30 := by
        change bytes ++ (if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 30 else []) = _
        rw [if_pos hsib_lt]
      rw [hb1]
      refine ⟨40, s77, ((((((h68.trans h69').trans h70').trans h71').trans h72').trans h73').trans h74').trans hrcopy,
        Nat.le_refl 40, hpc77, ?_, ?_, ?_,
        by simp only [List.length_append, bitsToBytes_length]; omega,
        hinv75.after_copy hx25_77 hreg77 (by simp only [bitsToBytes_length]) hro77 hpr77 hcap77⟩
      · rw [hreg77 .x22 (by decide) (by decide) (by decide)]; rfl
      · rw [hreg77 .x29 (by decide) (by decide) (by decide)]; exact hx29
      · rw [hreg77 .x30 (by decide) (by decide) (by decide)]; exact hx30
    · have h68 := step_BGEU_taken (by omega) (rfl : s68.pc = pcAt 68)
        (rfl : openingInstr 68 = .base (.BGEU .x28 .x7 (36#13)))
        (by rw [hx28_toNat, hx7_toNat]; omega)
        (by decide : pcAt 68 + signExtend13 (36#13) = pcAt 77)
      have hb1 : bytes1 = bytes := by
        change bytes ++ (if sib < levelSize l then bitsToBytes (tdNode trapdoor l sib) 30 else []) = _
        rw [if_neg hsib_lt, List.append_nil]
      rw [hb1]
      exact ⟨1, s68.setPC (pcAt 77), h68, by omega, rfl, rfl, hx29, hx30, by omega,
        hinv68.setPC (pcAt 77)⟩
  obtain ⟨n77, s77, hr77, hn77, hpc77, hx22_77, hx29_77, hx30_77, hlen1, inv77⟩ := hto77
  have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
  have h77 := step_ADDI (by omega) hpc77 (rfl : openingInstr 77 = .base (.ADDI .x29 .x29 (32#12)))
  let s78 := (s77.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))))).setPC (pcAt 78)
  have h77' : OpenRuns s77 1 1 s78 := by
    have hv : s77.getReg .x29 + signExtend12 (32#12) =
        BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) := by
      rw [hx29_77, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s78] using h77
  have hinv78 : RecInv trapdoor positions t bytes1 s78 :=
    ⟨inv77.rx2, inv77.rx9, inv77.rx18, inv77.rx19, inv77.rx20, inv77.rx21, inv77.rx24, inv77.rx25,
     inv77.rx26, inv77.rx27, inv77.evenLen, inv77.ro, inv77.proof, inv77.cap15⟩
  by_cases hmore : step + 1 < 13
  · have h78 := step_BNE_taken (by omega) (rfl : s78.pc = pcAt 78)
      (rfl : openingInstr 78 = .base (.BNE .x29 .x30 (8140#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) ≠ s77.getReg .x30
          rw [hx30_77]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 78 + signExtend13 (8140#13) = pcAt 65)
    exact ⟨3 + n77 + 1 + 1, s78.setPC (pcAt 65), ((hpre.trans hr77).trans h77').trans h78,
      by omega, by rw [if_pos hmore]; rfl, hx22_77, rfl, hx30_77, hlen1, hinv78.setPC (pcAt 65)⟩
  · have hlast : step + 1 = 13 := by omega
    have h78 := step_BNE_not_taken (by omega) (rfl : s78.pc = pcAt 78)
      (rfl : openingInstr 78 = .base (.BNE .x29 .x30 (8140#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (2 + (step + 1))) = s77.getReg .x30
          rw [hx30_77, hlast])
    exact ⟨3 + n77 + 1 + 1, s78.setPC (pcAt 79), ((hpre.trans hr77).trans h77').trans h78,
      by omega, by rw [if_neg hmore]; rfl, hx22_77, rfl, hx30_77, hlen1, hinv78.setPC (pcAt 79)⟩

private theorem openRuns_rec_bin {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t g : Nat} {bytes : List Byte} {s : MachineState}
    (hg : g ≤ FULL_TRIPLETS) (hpc : s.pc = pcAt 63)
    (hx22 : s.getReg .x22 = BitVec.ofNat 64 g)
    (hbd : bytes.length + 390 ≤ 8422172696)
    (inv : RecInv trapdoor positions t bytes s) :
    let bytes1 := bytes ++ binPathProof (tdNode trapdoor) g
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 587 ∧
      s1.pc = pcAt 79 ∧
      s1.getReg .x22 = BitVec.ofNat 64 (g >>> 13) ∧
      RecInv trapdoor positions t bytes1 s1 := by
  intro bytes1
  have hse64 : signExtend12 (64#12) = BitVec.ofNat 64 64 := by decide
  have hse480 : signExtend12 (480#12) = BitVec.ofNat 64 480 := by decide
  have h63 := step_ADDI (by omega) hpc (rfl : openingInstr 63 = .base (.ADDI .x29 .x2 (64#12)))
  let s64 := (s.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * 2))).setPC (pcAt 64)
  have h63' : OpenRuns s 1 1 s64 := by
    rw [inv.rx2, hse64, bv64_ofNat_add] at h63; exact h63
  have h64 := step_ADDI (by omega) (rfl : s64.pc = pcAt 64)
    (rfl : openingInstr 64 = .base (.ADDI .x30 .x2 (480#12)))
  let s65 := (s64.setReg .x30 (BitVec.ofNat 64 (68719475936 + 32 * 15))).setPC (pcAt 65)
  have h64' : OpenRuns s64 1 1 s65 := by
    have hr2 : s64.getReg .x2 = BitVec.ofNat 64 68719475936 := inv.rx2
    rw [hr2, hse480, bv64_ofNat_add] at h64; exact h64
  have hinv65 : RecInv trapdoor positions t bytes s65 :=
    ⟨inv.rx2, inv.rx9, inv.rx18, inv.rx19, inv.rx20, inv.rx21, inv.rx24, inv.rx25,
     inv.rx26, inv.rx27, inv.evenLen, inv.ro, inv.proof, inv.cap15⟩
  have hloop : ∀ n ≤ 13,
      let cur := bytes ++ (List.range n).flatMap (binStepBytes trapdoor g)
      ∃ steps sn, OpenRuns s65 steps steps sn ∧
        steps ≤ 45 * n ∧
        sn.pc = (if n < 13 then pcAt 65 else pcAt 79) ∧
        sn.getReg .x22 = BitVec.ofNat 64 (g >>> n) ∧
        sn.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (2 + n)) ∧
        sn.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 15) ∧
        cur.length ≤ bytes.length + 30 * n ∧
        RecInv trapdoor positions t cur sn := by
    intro n hn
    induction n with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero, Nat.add_zero]
      exact ⟨0, s65, OpenRuns.refl s65, Nat.le_refl 0, by rw [if_pos (by omega : 0 < 13)]; rfl,
        by rw [Nat.shiftRight_zero]; exact hx22, rfl, rfl, Nat.le_refl _, hinv65⟩
    | succ n ih =>
      obtain ⟨st, sn, hrn, hstn, hpcn, hx22n, hx29n, hx30n, hlenn, invn⟩ := ih (by omega)
      have hpcn' : sn.pc = pcAt 65 := by simpa only [show n < 13 by omega, ite_true] using hpcn
      obtain ⟨st1, sn1, hr1, hst1, hpc1, hx22_1, hx29_1, hx30_1, hlen1, inv1⟩ :=
        openRuns_rec_bin_step hg (by omega) hpcn' hx22n hx29n hx30n (by omega) invn
      have happ : bytes ++ (List.range n).flatMap (binStepBytes trapdoor g) ++ binStepBytes trapdoor g n =
          bytes ++ (List.range (n + 1)).flatMap (binStepBytes trapdoor g) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      rw [happ] at hlen1 inv1
      exact ⟨st + st1, sn1, hrn.trans hr1, by omega, hpc1, hx22_1, hx29_1, hx30_1, by omega, inv1⟩
  obtain ⟨st, s79, hrloop, hst, hpc79, hx22_79, _, _, _, inv79⟩ := hloop 13 (Nat.le_refl 13)
  have hpc79' : s79.pc = pcAt 79 := by simpa only [Nat.lt_irrefl, ite_false] using hpc79
  have hbytes_eq : bytes ++ (List.range 13).flatMap (binStepBytes trapdoor g) = bytes1 := rfl
  rw [hbytes_eq] at inv79
  exact ⟨2 + st, s79, (h63'.trans h64').trans hrloop, by omega, hpc79', hx22_79, inv79⟩

private theorem openRuns_rec_iter {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {t : Nat} {bytes : List Byte} {s : MachineState}
    (ht : t < positions.card) (hpc : s.pc = pcAt 19)
    (hbd : bytes.length ≤ 502 * t)
    (inv : RecInv trapdoor positions t bytes s) :
    let idx : Index := (positions.sort (· ≤ ·))[t]'(by simpa using ht)
    let bytes' := bytes ++ recordProof (tdNode trapdoor) (tdSalt trapdoor) idx
    ∃ steps cycles s', OpenRuns s steps cycles s' ∧
      steps ≤ 741 ∧ cycles ≤ 747 ∧
      s'.pc = (if t + 1 < positions.card then pcAt 19 else pcAt 86) ∧
      bytes'.length ≤ 502 * (t + 1) ∧
      RecInv trapdoor positions (t + 1) bytes' s' := by
  intro idx bytes'
  have hcard := positions_card_le positions
  have hidx_lt : idx.val < 16777216 := idx.isLt
  have hft : FULL_TRIPLETS = 5592405 := full_triplets_eq
  have hg_le : idx.val / 3 ≤ FULL_TRIPLETS := by omega
  obtain ⟨s24, hrsalt, hpc24, hx8_24, inv24⟩ := openRuns_rec_salt ht hpc (by omega) inv
  have inv24' : RecInv trapdoor positions t (bytes ++ bitsToBytes (tdSalt trapdoor idx) 16) s24 := inv24
  have hlen24 : (bytes ++ bitsToBytes (tdSalt trapdoor idx) 16).length ≤ 502 * t + 16 := by
    simp only [List.length_append, bitsToBytes_length]; omega
  obtain ⟨st0, cy0, s54, hrl0, hst0, hcy0, hpc54, hx22_54, inv54⟩ :=
    openRuns_rec_l0 hpc24 idx hx8_24 (by omega) inv24'
  have hlen54 : (bytes ++ bitsToBytes (tdSalt trapdoor idx) 16 ++
      l0SiblingsProof (tdNode trapdoor) idx).length ≤ 502 * t + 80 := by
    have := l0SiblingsProof_length_le (tdNode trapdoor) idx
    simp only [List.length_append, bitsToBytes_length] at *; omega
  obtain ⟨s63, hrl1, hpc63, hx22_63, inv63⟩ :=
    openRuns_rec_l1 hg_le hpc54 hx22_54 (by omega) inv54
  have hlen63 : (bytes ++ bitsToBytes (tdSalt trapdoor idx) 16 ++
      l0SiblingsProof (tdNode trapdoor) idx ++
      bitsToBytes (tdNode trapdoor 1 ((idx.val / 3) ^^^ 1)) 32).length ≤ 502 * t + 112 := by
    simp only [List.length_append, bitsToBytes_length] at *; omega
  obtain ⟨stbin, s79, hrbin, hstbin, hpc79, hx22_79, inv79⟩ :=
    openRuns_rec_bin hg_le hpc63 hx22_63 (by omega) inv63
  have happ : bytes ++ bitsToBytes (tdSalt trapdoor idx) 16 ++
      l0SiblingsProof (tdNode trapdoor) idx ++
      bitsToBytes (tdNode trapdoor 1 ((idx.val / 3) ^^^ 1)) 32 ++
      binPathProof (tdNode trapdoor) (idx.val / 3) = bytes' := by
    simp only [bytes', recordProof, List.append_assoc]
  rw [happ] at inv79
  have hlen_rec : bytes'.length ≤ 502 * (t + 1) := by
    have hr := recordProof_length_le_502 (tdNode trapdoor) (tdSalt trapdoor) idx
    simp only [bytes', List.length_append]; omega
  -- Tail: 79..85
  have hcap_lt : capLeafNat idx.val < 342 := capLeafOf_lt idx
  have hg13_le : (idx.val / 3) >>> 13 ≤ idx.val / 3 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
  have h79 := step_SRLI (by omega) hpc79 (rfl : openingInstr 79 = .base (.SRLI .x22 .x22 (1#6)))
  let s80 := (s79.setReg .x22 (BitVec.ofNat 64 (capLeafNat idx.val))).setPC (pcAt 80)
  have h79' : OpenRuns s79 1 1 s80 := by
    have hv : s79.getReg .x22 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (capLeafNat idx.val) := by
      rw [hx22_79]; change BitVec.ofNat 64 ((idx.val / 3) >>> 13) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), nat_ushr_ushr1]
      rfl
    simpa only [hv, s80] using h79
  have h80 := step_ADD (by omega) (rfl : s80.pc = pcAt 80)
    (rfl : openingInstr 80 = .base (.ADD .x6 .x21 .x22))
  let s81 := (s80.setReg .x6 (BitVec.ofNat 64 (4096 + capLeafNat idx.val))).setPC (pcAt 81)
  have h80' : OpenRuns s80 1 1 s81 := by
    have hr21 : s80.getReg .x21 = BitVec.ofNat 64 4096 := inv79.rx21
    rw [hr21] at h80
    simpa only [show s80.getReg .x22 = BitVec.ofNat 64 (capLeafNat idx.val) from rfl,
      bv64_ofNat_add, s81] using h80
  have h81 := step_ADDI (by omega) (rfl : s81.pc = pcAt 81)
    (rfl : openingInstr 81 = .base (.ADDI .x7 .x0 (1#12)))
  let s82 := (s81.setReg .x7 1#64).setPC (pcAt 82)
  have h81' : OpenRuns s81 1 1 s82 := by
    have hv : s81.getReg .x0 + signExtend12 (1#12) = 1#64 := by
      change (0#64 : Word) + signExtend12 (1#12) = 1#64; decide
    simpa only [hv, s82] using h81
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have haddr82 : s82.getReg .x6 + signExtend12 (0#12) = BitVec.ofNat 64 (4096 + capLeafNat idx.val) := by
    change BitVec.ofNat 64 (4096 + capLeafNat idx.val) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h82 := step_SB (by omega) (rfl : s82.pc = pcAt 82)
    (rfl : openingInstr 82 = .base (.SB .x6 .x7 (0#12)))
    (by rw [haddr82]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s83 := (s82.setByte (BitVec.ofNat 64 (4096 + capLeafNat idx.val)) 1#8).setPC (pcAt 83)
  have h82' : OpenRuns s82 1 1 s83 := by
    have ht : (s82.getReg .x7).truncate 8 = 1#8 := by
      change (1#64 : Word).truncate 8 = 1#8; decide
    simpa only [haddr82, ht, s83] using h82
  have hse8 : signExtend12 (8#12) = BitVec.ofNat 64 8 := by decide
  have h83 := step_ADDI (by omega) (rfl : s83.pc = pcAt 83)
    (rfl : openingInstr 83 = .base (.ADDI .x24 .x24 (8#12)))
  let s84 := (s83.setReg .x24 (BitVec.ofNat 64 (5637149760 + 8 * (t + 1)))).setPC (pcAt 84)
  have h83' : OpenRuns s83 1 1 s84 := by
    have hr24 : s83.getReg .x24 = BitVec.ofNat 64 (5637149760 + 8 * t) := by
      simp only [s83, s82, s81, s80, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x7 .x24 (by decide),
        getReg_setReg_ne' .x6 .x24 (by decide),
        getReg_setReg_ne' .x22 .x24 (by decide)]
      exact inv79.rx24
    have hv : s83.getReg .x24 + signExtend12 (8#12) =
        BitVec.ofNat 64 (5637149760 + 8 * (t + 1)) := by
      rw [hr24, hse8, bv64_ofNat_add]; congr 1
    simpa only [hv, s84] using h83
  have h84 := step_ADDI (by omega) (rfl : s84.pc = pcAt 84)
    (rfl : openingInstr 84 = .base (.ADDI .x27 .x27 (4095#12)))
  let s85 := (s84.setReg .x27 (BitVec.ofNat 64 (positions.card - (t + 1)))).setPC (pcAt 85)
  have h84' : OpenRuns s84 1 1 s85 := by
    have hr27 : s84.getReg .x27 = BitVec.ofNat 64 ((positions.card - (t + 1)) + 1) := by
      simp only [s84, s83, s82, s81, s80, MachineState.getReg_setPC, getReg_setByte,
        getReg_setReg_ne' .x24 .x27 (by decide),
        getReg_setReg_ne' .x7 .x27 (by decide),
        getReg_setReg_ne' .x6 .x27 (by decide),
        getReg_setReg_ne' .x22 .x27 (by decide)]
      rw [inv79.rx27]; congr 1; omega
    rw [hr27, bv64_add_neg1] at h84; exact h84
  have hro85 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s85 := by
    intro a ha
    simp only [s85, MachineState.getMem_setPC, MachineState.getMem_setReg, s84, s83]
    exact readOnly_setByte_cap (4096 + capLeafNat idx.val) 1#8 inv79.ro (by omega) (by omega) a ha
  have hpr85 : ProofPrefix s85 bytes' := by
    intro j hj
    simp only [s85, getByte_setPC, getByte_setReg, s84, s83]
    exact proofPrefix_setByte_cap (4096 + capLeafNat idx.val) 1#8 inv79.proof (by omega) (by omega) (by omega) j hj
  have hcap85 : ∀ c < 342, s85.getByte (BitVec.ofNat 64 (4096 + c)) =
      if capMark15Prefix positions (t + 1) c then 1#8 else 0#8 := by
    intro c hc
    simp only [s85, getByte_setPC, getByte_setReg, s84, s83, set_byte_read]
    have hopen : openingIndex positions t = idx.val := by simp only [openingIndex, dif_pos ht]; rfl
    by_cases hceq : c = capLeafNat idx.val
    · subst hceq
      rw [if_pos rfl]
      have htr : capMark15Prefix positions (t + 1) (capLeafNat idx.val) = true := by
        simp only [capMark15Prefix, decide_eq_true_eq]
        exact ⟨t, by omega, by rw [hopen]⟩
      rw [htr]; rfl
    · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
      simp only [s82, s81, s80, getByte_setPC, getByte_setReg, inv79.cap15 c hc]
      have hsame : capMark15Prefix positions (t + 1) c = capMark15Prefix positions t c := by
        simp only [capMark15Prefix]
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
  have hpres85 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x22 → r ≠ .x24 → r ≠ .x27 →
      s85.getReg r = s79.getReg r := fun r h6 h7 h22 h24 h27 => by
    simp only [s85, s84, s83, s82, s81, s80, MachineState.getReg_setPC, getReg_setByte,
      getReg_setReg_ne' .x27 r (Ne.symm h27),
      getReg_setReg_ne' .x24 r (Ne.symm h24),
      getReg_setReg_ne' .x7 r (Ne.symm h7),
      getReg_setReg_ne' .x6 r (Ne.symm h6),
      getReg_setReg_ne' .x22 r (Ne.symm h22)]
  have hinv85 : RecInv trapdoor positions (t + 1) bytes' s85 :=
    ⟨by rw [hpres85 .x2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv79.rx2,
     by rw [hpres85 .x9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv79.rx9,
     by rw [hpres85 .x18 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv79.rx18,
     by rw [hpres85 .x19 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv79.rx19,
     by rw [hpres85 .x20 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv79.rx20,
     by rw [hpres85 .x21 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv79.rx21,
     by simp only [s85, MachineState.getReg_setPC, getReg_setReg_ne' .x27 .x24 (by decide)]; rfl,
     by rw [hpres85 .x25 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv79.rx25,
     by rw [hpres85 .x26 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv79.rx26,
     rfl, inv79.evenLen, hro85, hpr85, hcap85⟩
  have htail := (((((h79'.trans h80').trans h81').trans h82').trans h83').trans h84')
  have hbody := (((hrsalt.trans hrl0).trans hrl1).trans hrbin).trans htail
  by_cases hmore : t + 1 < positions.card
  · have h85 := step_BNE_taken (by omega) (rfl : s85.pc = pcAt 85)
      (rfl : openingInstr 85 = .base (.BNE .x27 .x0 (7928#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) ≠ BitVec.ofNat 64 0
          exact bv64_ofNat_ne (by omega) (by decide) (by omega))
      (by decide : pcAt 85 + signExtend13 (7928#13) = pcAt 19)
    exact ⟨22 + st0 + 42 + stbin + 6 + 1, 22 + cy0 + 42 + stbin + 6 + 1, s85.setPC (pcAt 19),
      hbody.trans h85, by omega, by omega, by rw [if_pos hmore]; rfl, hlen_rec, hinv85.setPC (pcAt 19)⟩
  · have hdone : positions.card - (t + 1) = 0 := by omega
    have h85 := step_BNE_not_taken (by omega) (rfl : s85.pc = pcAt 85)
      (rfl : openingInstr 85 = .base (.BNE .x27 .x0 (7928#13)))
      (by change BitVec.ofNat 64 (positions.card - (t + 1)) = BitVec.ofNat 64 0; rw [hdone])
    exact ⟨22 + st0 + 42 + stbin + 6 + 1, 22 + cy0 + 42 + stbin + 6 + 1, s85.setPC (pcAt 86),
      hbody.trans h85, by omega, by omega, by rw [if_neg hmore]; rfl, hlen_rec, hinv85.setPC (pcAt 86)⟩

private theorem openRuns_rec_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {s19 : MachineState}
    (hne : 0 < positions.card) (hpc : s19.pc = pcAt 19)
    (inv0 : RecInv trapdoor positions 0 [] s19) :
    let recBytes := (positions.sort (· ≤ ·)).flatMap (recordProof (tdNode trapdoor) (tdSalt trapdoor))
    ∃ steps cycles s86, OpenRuns s19 steps cycles s86 ∧
      steps ≤ 741 * positions.card ∧
      cycles ≤ 747 * positions.card ∧
      s86.pc = pcAt 86 ∧
      s86.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s86.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s86.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s86.getReg .x25 = BitVec.ofNat 64 (10066334784 + recBytes.length) ∧
      s86.getReg .x26 = BitVec.ofNat 64 10066334784 ∧
      recBytes.length % 2 = 0 ∧
      recBytes.length ≤ 502 * positions.card ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s86 ∧
      ProofPrefix s86 recBytes ∧
      CapLevelMarks s86 positions 15 := by
  intro recBytes
  have hloop : ∀ t ≤ positions.card,
      let cur := ((positions.sort (· ≤ ·)).take t).flatMap
        (recordProof (tdNode trapdoor) (tdSalt trapdoor))
      ∃ steps cycles st, OpenRuns s19 steps cycles st ∧
        steps ≤ 741 * t ∧ cycles ≤ 747 * t ∧
        st.pc = (if t < positions.card then pcAt 19 else pcAt 86) ∧
        cur.length ≤ 502 * t ∧
        RecInv trapdoor positions t cur st := by
    intro t ht
    induction t with
    | zero =>
      dsimp only
      simp only [List.take_zero, List.flatMap_nil, Nat.mul_zero]
      exact ⟨0, 0, s19, OpenRuns.refl s19, Nat.le_refl 0, Nat.le_refl 0,
        by rw [if_pos hne]; exact hpc, Nat.le_refl 0, inv0⟩
    | succ t ih =>
      obtain ⟨st, cy, stState, hr, hst, hcy, hpct, hbdt, invt⟩ := ih (by omega)
      have hpct' : stState.pc = pcAt 19 := by simpa only [show t < positions.card by omega, ite_true] using hpct
      obtain ⟨st1, cy1, stNext, hr1, hst1, hcy1, hpc1, hbd1, inv1⟩ :=
        openRuns_rec_iter (by omega) hpct' hbdt invt
      have hlen : t < (positions.sort (· ≤ ·)).length := by simpa using (by omega : t < positions.card)
      have htake : ((positions.sort (· ≤ ·)).take (t + 1)).flatMap
            (recordProof (tdNode trapdoor) (tdSalt trapdoor)) =
          ((positions.sort (· ≤ ·)).take t).flatMap
            (recordProof (tdNode trapdoor) (tdSalt trapdoor)) ++
          recordProof (tdNode trapdoor) (tdSalt trapdoor) ((positions.sort (· ≤ ·))[t]'hlen) := by
        rw [List.take_succ_eq_append_getElem hlen, List.flatMap_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [← htake] at hbd1 inv1
      exact ⟨st + st1, cy + cy1, stNext, hr.trans hr1, by omega, by omega, hpc1, hbd1, inv1⟩
  obtain ⟨steps, cycles, s86, hr, hst, hcy, hpc86, hbdEnd, invEnd⟩ :=
    hloop positions.card (Nat.le_refl _)
  have hpc86' : s86.pc = pcAt 86 := by simpa only [Nat.lt_irrefl, ite_false] using hpc86
  have htakeAll : (positions.sort (· ≤ ·)).take positions.card = positions.sort (· ≤ ·) := by
    have hlen : (positions.sort (· ≤ ·)).length = positions.card := by simp
    rw [← hlen, List.take_length]
  rw [htakeAll] at hbdEnd invEnd
  refine ⟨steps, cycles, s86, hr, hst, hcy, hpc86',
    invEnd.rx2, invEnd.rx9, invEnd.rx21, invEnd.rx25, invEnd.rx26,
    invEnd.evenLen, hbdEnd, invEnd.ro, invEnd.proof, ?_⟩
  intro idx hidx
  have hidx342 : idx < 342 := by rw [levelSize_15] at hidx; exact hidx
  have hmo15 : capMarkOff 15 = 0 := by decide
  rw [hmo15, Nat.add_zero, invEnd.cap15 idx hidx342, capMark15Prefix_card]

/-! ### 8. Cap Frontier Pass (`86..123`) -/

private def capPairBytes (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (l q : Nat) : List Byte :=
  let mL := capMark positions l (2 * q)
  let mR := capMark positions l (2 * q + 1)
  if mL = mR then []
  else if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) 30
  else bitsToBytes (tdNode trapdoor l (2 * q + 1)) 30

private def capPairFrontier (positions : Positions) (l q : Nat) : Nat :=
  if capMark positions l (2 * q) != capMark positions l (2 * q + 1) then 1 else 0

private theorem sum_capPairFrontier_eq (positions : Positions) (l : Nat) :
    (∑ q ∈ Finset.range (levelSize l / 2), capPairFrontier positions l q) =
      levelFrontierCount positions l := by
  unfold levelFrontierCount capPairFrontier
  rw [Finset.card_filter]

private structure CapLvlInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (step : Nat) (bytes : List Byte) (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475936
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx25 : s.getReg .x25 = BitVec.ofNat 64 (10066334784 + bytes.length)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 10066334784
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (15 + step))
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 24)
  evenLen : bytes.length % 2 = 0
  boundLen : bytes.length ≤ 502 * positions.card +
    30 * (∑ k ∈ Finset.range step, levelFrontierCount positions (15 + k))
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  proof : ProofPrefix s bytes
  capMarks : CapLevelMarks s positions (15 + step)

private structure CapPairInv (trapdoor : BitVec (8 * submission.sizes.trapdoor))
    (positions : Positions) (step q : Nat) (bytes : List Byte) (s : MachineState) : Prop where
  rx2 : s.getReg .x2 = BitVec.ofNat 64 68719475936
  rx9 : s.getReg .x9 = BitVec.ofNat 64 4294971424
  rx18 : s.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase (15 + step))
  rx19 : s.getReg .x19 = BitVec.ofNat 64 (levelSize (15 + step))
  rx20 : s.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff (15 + step))
  rx21 : s.getReg .x21 = BitVec.ofNat 64 4096
  rx22 : s.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (15 + step + 1))
  rx23 : s.getReg .x23 = BitVec.ofNat 64 (levelSize (15 + step) / 2)
  rx24 : s.getReg .x24 = BitVec.ofNat 64 q
  rx25 : s.getReg .x25 = BitVec.ofNat 64 (10066334784 + bytes.length)
  rx26 : s.getReg .x26 = BitVec.ofNat 64 10066334784
  rx29 : s.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * (15 + step))
  rx30 : s.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 24)
  evenLen : bytes.length % 2 = 0
  boundLen : bytes.length ≤ 502 * positions.card +
    30 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (15 + k)) +
          (∑ j ∈ Finset.range q, capPairFrontier positions (15 + step) j))
  ro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s
  proof : ProofPrefix s bytes
  curMarks : CapLevelMarks s positions (15 + step)
  nextMarks : ∀ j < q, s.getByte (BitVec.ofNat 64 (4096 + capMarkOff (15 + step + 1) + j)) =
    if capMark positions (15 + step + 1) j then 1#8 else 0#8

private theorem openRuns_cap_pair_step {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {step q : Nat} {bytes : List Byte} {s : MachineState}
    (hstep : step < 9) (hq : q < levelSize (15 + step) / 2) (hpc : s.pc = pcAt 97)
    (inv : CapPairInv trapdoor positions step q bytes s) :
    let l := 15 + step
    let bytes1 := bytes ++ capPairBytes trapdoor positions l q
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 10 + 39 * capPairFrontier positions l q ∧
      s1.pc = (if q + 1 < levelSize l / 2 then pcAt 97 else pcAt 115) ∧
      CapPairInv trapdoor positions step (q + 1) bytes1 s1 := by
  intro l bytes1
  have hql : q < levelSize l / 2 := hq
  have hcur_inv : CapLevelMarks s positions l := inv.curMarks
  have hinv_bd : bytes.length ≤ 502 * positions.card +
      30 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (15 + k)) +
            (∑ j ∈ Finset.range q, capPairFrontier positions l j)) := inv.boundLen
  have hcard := positions_card_le positions
  have hls_le := levelSize_le_max l (by omega)
  have hcm_bd := capMarkOff_bound l (by omega) (by omega)
  have hcm1_bd := capMarkOff_bound (l + 1) (by omega) (by omega)
  have hcm_disj := capMarkOff_step_disjoint l (by omega) (by omega)
  have hls1_eq := levelSize_step l (by omega)
  have hq_lt_next : q < levelSize (l + 1) := by omega
  set mL := capMark positions l (2 * q)
  set mR := capMark positions l (2 * q + 1)
  have h97 := step_SLLI (by omega) hpc (rfl : openingInstr 97 = .base (.SLLI .x6 .x24 (1#6)))
  let s98 := (s.setReg .x6 (BitVec.ofNat 64 (2 * q))).setPC (pcAt 98)
  have h97' : OpenRuns s 1 1 s98 := by
    have hv : s.getReg .x24 <<< (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (2 * q) := by
      rw [inv.rx24]; change BitVec.ofNat 64 q <<< 1 = _
      rw [bv64_shl]; congr 1; omega
    simpa only [hv, s98] using h97
  have h98 := step_ADD (by omega) (rfl : s98.pc = pcAt 98)
    (rfl : openingInstr 98 = .base (.ADD .x6 .x20 .x6))
  let s99 := (s98.setReg .x6 (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q))).setPC (pcAt 99)
  have h98' : OpenRuns s98 1 1 s99 := by
    have hr20 : s98.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) := inv.rx20
    rw [hr20] at h98
    simpa only [show s98.getReg .x6 = BitVec.ofNat 64 (2 * q) from rfl, bv64_ofNat_add, s99] using h98
  have hse0 : signExtend12 (0#12) = BitVec.ofNat 64 0 := by decide
  have hse1 : signExtend12 (1#12) = BitVec.ofNat 64 1 := by decide
  have haddr99 : s99.getReg .x6 + signExtend12 (0#12) =
      BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) := by
    change BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h99 := step_LBU (by omega) (rfl : s99.pc = pcAt 99)
    (rfl : openingInstr 99 = .base (.LBU .x7 .x6 (0#12)))
    (by rw [haddr99]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s100 := (s99.setReg .x7 (if mL then 1#64 else 0#64)).setPC (pcAt 100)
  have h99' : OpenRuns s99 1 1 s100 := by
    have hb : s99.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q)) =
        if mL then 1#8 else 0#8 := hcur_inv (2 * q) (by omega)
    simpa only [haddr99, hb, bool_byte_zeroExtend mL, s100] using h99
  have haddr100 : s100.getReg .x6 + signExtend12 (1#12) =
      BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1)) := by
    change BitVec.ofNat 64 (4096 + capMarkOff l + 2 * q) + _ = _
    rw [hse1, bv64_ofNat_add, Nat.add_assoc]
  have h100 := step_LBU (by omega) (rfl : s100.pc = pcAt 100)
    (rfl : openingInstr 100 = .base (.LBU .x8 .x6 (1#12)))
    (by rw [haddr100]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s101 := (s100.setReg .x8 (if mR then 1#64 else 0#64)).setPC (pcAt 101)
  have h100' : OpenRuns s100 1 1 s101 := by
    have hb : s100.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + (2 * q + 1))) =
        if mR then 1#8 else 0#8 := hcur_inv (2 * q + 1) (by omega)
    simpa only [haddr100, hb, bool_byte_zeroExtend mR, s101] using h100
  have h101 := step_OR (by omega) (rfl : s101.pc = pcAt 101)
    (rfl : openingInstr 101 = .base (.OR .x11 .x7 .x8))
  let s102 := (s101.setReg .x11 (if (mL || mR) then 1#64 else 0#64)).setPC (pcAt 102)
  have h101' : OpenRuns s101 1 1 s102 := by
    simpa only [show s101.getReg .x7 = if mL then 1#64 else 0#64 from rfl,
      show s101.getReg .x8 = if mR then 1#64 else 0#64 from rfl,
      bool_word_or mL mR, s102] using h101
  have h102 := step_ADD (by omega) (rfl : s102.pc = pcAt 102)
    (rfl : openingInstr 102 = .base (.ADD .x6 .x22 .x24))
  let s103 := (s102.setReg .x6 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q))).setPC (pcAt 103)
  have h102' : OpenRuns s102 1 1 s103 := by
    have hr22 : s102.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) := inv.rx22
    have hr24 : s102.getReg .x24 = BitVec.ofNat 64 q := inv.rx24
    rw [hr22, hr24, bv64_ofNat_add] at h102; exact h102
  have haddr103 : s103.getReg .x6 + signExtend12 (0#12) =
      BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) := by
    change BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q) + _ = _
    rw [hse0, bv64_ofNat_add, Nat.add_zero]
  have h103 := step_SB (by omega) (rfl : s103.pc = pcAt 103)
    (rfl : openingInstr 103 = .base (.SB .x6 .x11 (0#12)))
    (by rw [haddr103]; exact accessValid_ofNat _ 1 (by omega) (by omega))
  let s104 := (s103.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + q))
    (if (mL || mR) then 1#8 else 0#8)).setPC (pcAt 104)
  have h103' : OpenRuns s103 1 1 s104 := by
    simpa only [haddr103, show s103.getReg .x11 = if (mL || mR) then 1#64 else 0#64 from rfl,
      bool_word_truncate8 (mL || mR), s104] using h103
  have hpre : OpenRuns s 7 7 s104 :=
    (((((h97'.trans h98').trans h99').trans h100').trans h101').trans h102').trans h103'
  have hpres104 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x11 →
      s104.getReg r = s.getReg r := fun r h6 h7 h8 h11 => by
    simp only [s104, s103, s102, s101, s100, s99, s98,
      MachineState.getReg_setPC, getReg_setByte,
      getReg_setReg_ne' .x6 r (Ne.symm h6),
      getReg_setReg_ne' .x11 r (Ne.symm h11),
      getReg_setReg_ne' .x8 r (Ne.symm h8),
      getReg_setReg_ne' .x7 r (Ne.symm h7)]
  have hx7_104 : s104.getReg .x7 = if mL then 1#64 else 0#64 := by
    simp only [s104, MachineState.getReg_setPC, getReg_setByte]; rfl
  have hx8_104 : s104.getReg .x8 = if mR then 1#64 else 0#64 := by
    simp only [s104, MachineState.getReg_setPC, getReg_setByte]; rfl
  -- Memory properties at s104
  have hfront_sum_le : (∑ k ∈ Finset.range step, levelFrontierCount positions (15 + k)) +
      (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j) ≤ capFrontierCount positions := by
    have hq_le : (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j) ≤
        levelFrontierCount positions l := by
      rw [← sum_capPairFrontier_eq]
      exact sum_range_le_of_le (capPairFrontier positions l) (by omega)
    have hs_eq : (∑ k ∈ Finset.range step, levelFrontierCount positions (15 + k)) +
        levelFrontierCount positions l =
        ∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (15 + k) := by
      rw [Finset.sum_range_succ]
    have hs_le : (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (15 + k)) ≤
        capFrontierCount positions := by
      unfold capFrontierCount
      exact sum_range_le_of_le (fun k => levelFrontierCount positions (15 + k)) (by omega)
    omega
  have hcap171 := cap_frontier_le_171 positions
  have hbytes_cap : bytes.length ≤ 502 * 16777216 + 30 * 171 := by
    have h1 := hinv_bd
    have h2 : (∑ j ∈ Finset.range q, capPairFrontier positions l j) ≤
        ∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j :=
      sum_range_le_of_le (capPairFrontier positions l) (by omega)
    omega
  have hro104 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s104 := by
    intro a ha
    simp only [s104, MachineState.getMem_setPC]
    exact readOnly_setByte_cap (4096 + capMarkOff (l + 1) + q) _ inv.ro (by omega) (by omega) a ha
  have hpr104 : ProofPrefix s104 bytes := by
    intro j hj
    simp only [s104, getByte_setPC]
    exact proofPrefix_setByte_cap (4096 + capMarkOff (l + 1) + q) _ inv.proof (by omega)
      (by omega) (by omega) j hj
  have hcur104 : CapLevelMarks s104 positions l := by
    intro idx hidx
    simp only [s104, getByte_setPC, set_byte_read]
    rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
    exact hcur_inv idx hidx
  have hnext104 : ∀ j < q + 1, s104.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + j)) =
      if capMark positions (l + 1) j then 1#8 else 0#8 := by
    intro j hj
    simp only [s104, getByte_setPC, set_byte_read]
    by_cases hjq : j = q
    · subst j
      have hlt : 2 * q + 1 < levelSize l := by omega
      rw [if_pos rfl]
      change (if (capMark positions l (2 * q) || capMark positions l (2 * q + 1)) then 1#8 else 0#8) = _
      rw [capMark_succ positions l q (by omega), if_pos hlt]
    · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
      exact inv.nextMarks j (by omega)
  -- Branch on mL = mR to reach pcAt 113
  have hto113 : ∃ n113 s113, OpenRuns s104 n113 n113 s113 ∧
      n113 ≤ 1 + 39 * capPairFrontier positions l q ∧
      s113.pc = pcAt 113 ∧
      s113.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s113.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s113.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l) ∧
      s113.getReg .x19 = BitVec.ofNat 64 (levelSize l) ∧
      s113.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) ∧
      s113.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s113.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) ∧
      s113.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) ∧
      s113.getReg .x24 = BitVec.ofNat 64 q ∧
      s113.getReg .x25 = BitVec.ofNat 64 (10066334784 + bytes1.length) ∧
      s113.getReg .x26 = BitVec.ofNat 64 10066334784 ∧
      s113.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) ∧
      s113.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 24) ∧
      bytes1.length % 2 = 0 ∧
      bytes1.length ≤ 502 * positions.card +
        30 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (15 + k)) +
              (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s113 ∧
      ProofPrefix s113 bytes1 ∧
      CapLevelMarks s113 positions l ∧
      (∀ j < q + 1, s113.getByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + j)) =
        if capMark positions (l + 1) j then 1#8 else 0#8) := by
    by_cases hsame : mL = mR
    · have h104 := step_BEQ_taken (by omega) (rfl : s104.pc = pcAt 104)
        (rfl : openingInstr 104 = .base (.BEQ .x7 .x8 (36#13)))
        (by rw [hx7_104, hx8_104, hsame])
        (by decide : pcAt 104 + signExtend13 (36#13) = pcAt 113)
      have hb1 : bytes1 = bytes := by
        change bytes ++ (if mL = mR then [] else _) = _
        rw [if_pos hsame, List.append_nil]
      rw [hb1]
      have hlen_le : bytes.length ≤ 502 * positions.card +
          30 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (15 + k)) +
                (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        have h1 := hinv_bd
        rw [Finset.sum_range_succ]; omega
      exact ⟨1, s104.setPC (pcAt 113), h104, by omega, rfl,
        by rw [MachineState.getReg_setPC, hpres104 .x2 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx2,
        by rw [MachineState.getReg_setPC, hpres104 .x9 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx9,
        by rw [MachineState.getReg_setPC, hpres104 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx18,
        by rw [MachineState.getReg_setPC, hpres104 .x19 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx19,
        by rw [MachineState.getReg_setPC, hpres104 .x20 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx20,
        by rw [MachineState.getReg_setPC, hpres104 .x21 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx21,
        by rw [MachineState.getReg_setPC, hpres104 .x22 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx22,
        by rw [MachineState.getReg_setPC, hpres104 .x23 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx23,
        by rw [MachineState.getReg_setPC, hpres104 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24,
        by rw [MachineState.getReg_setPC, hpres104 .x25 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx25,
        by rw [MachineState.getReg_setPC, hpres104 .x26 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx26,
        by rw [MachineState.getReg_setPC, hpres104 .x29 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx29,
        by rw [MachineState.getReg_setPC, hpres104 .x30 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx30,
        inv.evenLen, hlen_le, hro104, hpr104, hcur104, hnext104⟩
    · have hcpf : capPairFrontier positions l q = 1 := by
        change (if (mL != mR) = true then 1 else 0) = 1
        exact bool_bne_one_of_ne hsame
      have h104 := step_BEQ_not_taken (by omega) (rfl : s104.pc = pcAt 104)
        (rfl : openingInstr 104 = .base (.BEQ .x7 .x8 (36#13)))
        (by rw [hx7_104, hx8_104]; exact bool_word_ne_of_ne hsame)
      let s105 := s104.setPC (pcAt 105)
      have h105 := step_SLLI (by omega) (rfl : s105.pc = pcAt 105)
        (rfl : openingInstr 105 = .base (.SLLI .x6 .x24 (6#6)))
      let s106 := (s105.setReg .x6 (BitVec.ofNat 64 (64 * q))).setPC (pcAt 106)
      have h105' : OpenRuns s105 1 1 s106 := by
        have hr24 : s105.getReg .x24 = BitVec.ofNat 64 q := by
          rw [show s105.getReg .x24 = s104.getReg .x24 from rfl,
            hpres104 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24
        have hv : s105.getReg .x24 <<< (6#6 : BitVec 6).toNat = BitVec.ofNat 64 (64 * q) := by
          rw [hr24]; change BitVec.ofNat 64 q <<< 6 = _; rw [bv64_shl]; congr 1; omega
        simpa only [hv, s106] using h105
      have h106 := step_SLLI (by omega) (rfl : s106.pc = pcAt 106)
        (rfl : openingInstr 106 = .base (.SLLI .x11 .x24 (5#6)))
      let s107 := (s106.setReg .x11 (BitVec.ofNat 64 (32 * q))).setPC (pcAt 107)
      have h106' : OpenRuns s106 1 1 s107 := by
        have hr24 : s106.getReg .x24 = BitVec.ofNat 64 q := by
          simp only [s106, s105, MachineState.getReg_setPC,
            getReg_setReg_ne' .x6 .x24 (by decide)]
          rw [hpres104 .x24 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24
        have hv : s106.getReg .x24 <<< (5#6 : BitVec 6).toNat = BitVec.ofNat 64 (32 * q) := by
          rw [hr24]; change BitVec.ofNat 64 q <<< 5 = _; rw [bv64_shl]; congr 1; omega
        simpa only [hv, s107] using h106
      have h107 := step_ADD (by omega) (rfl : s107.pc = pcAt 107)
        (rfl : openingInstr 107 = .base (.ADD .x10 .x6 .x11))
      let s108 := (s107.setReg .x10 (BitVec.ofNat 64 (96 * q))).setPC (pcAt 108)
      have h107' : OpenRuns s107 1 1 s108 := by
        have hv : s107.getReg .x6 + s107.getReg .x11 = BitVec.ofNat 64 (96 * q) := by
          change BitVec.ofNat 64 (64 * q) + BitVec.ofNat 64 (32 * q) = _
          rw [bv64_ofNat_add]; congr 1; omega
        simpa only [hv, s108] using h107
      have h108 := step_ADD (by omega) (rfl : s108.pc = pcAt 108)
        (rfl : openingInstr 108 = .base (.ADD .x10 .x18 .x10))
      let s109 := (s108.setReg .x10 (BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q))).setPC (pcAt 109)
      have h108' : OpenRuns s108 1 1 s109 := by
        have hr18 : s108.getReg .x18 = BitVec.ofNat 64 (4294971424 + levelBase l) := by
          simp only [s108, s107, s106, s105, MachineState.getReg_setPC,
            getReg_setReg_ne' .x10 .x18 (by decide),
            getReg_setReg_ne' .x11 .x18 (by decide),
            getReg_setReg_ne' .x6 .x18 (by decide)]
          rw [hpres104 .x18 (by decide) (by decide) (by decide) (by decide)]; exact inv.rx18
        rw [hr18] at h108
        simpa only [show s108.getReg .x10 = BitVec.ofNat 64 (96 * q) from rfl, bv64_ofNat_add, s109] using h108
      have hmid : OpenRuns s104 5 5 s109 := (((h104.trans h105').trans h106').trans h107').trans h108'
      have htb : treeBytes = 1073742880 := treeBytes_eq
      have hlen_bd : bytes.length + 30 ≤ 502 * positions.card +
          30 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (15 + k)) +
                (∑ j ∈ Finset.range (q + 1), capPairFrontier positions l j)) := by
        have h1 := hinv_bd
        rw [Finset.sum_range_succ, hcpf]; omega
      have hlen_cap : bytes.length + 30 ≤ 8422172696 := by omega
      have hr7_109 : s109.getReg .x7 = if mL then 1#64 else 0#64 := by
        simp only [s109, s108, s107, s106, s105, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 .x7 (by decide),
          getReg_setReg_ne' .x11 .x7 (by decide),
          getReg_setReg_ne' .x6 .x7 (by decide)]
        exact hx7_104
      have hpres109 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x11 →
          s109.getReg r = s.getReg r := fun r h6 h7 h8 h10 h11 => by
        simp only [s109, s108, s107, s106, s105, MachineState.getReg_setPC,
          getReg_setReg_ne' .x10 r (Ne.symm h10),
          getReg_setReg_ne' .x11 r (Ne.symm h11),
          getReg_setReg_ne' .x6 r (Ne.symm h6)]
        exact hpres104 r h6 h7 h8 h11
      -- Split on mL = true vs mL = false
      have hto111 : ∃ n111 s111 childIdx, OpenRuns s109 n111 n111 s111 ∧ n111 ≤ 2 ∧
          childIdx = (if !mL then 2 * q else 2 * q + 1) ∧
          childIdx < levelSize l ∧
          s111.pc = pcAt 111 ∧
          s111.getReg .x10 = BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l childIdx)) ∧
          (∀ r, r ≠ .x10 → s111.getReg r = s109.getReg r) ∧
          s111.mem = s109.mem := by
        by_cases hmL : mL = true
        · have h109 := step_BEQ_not_taken (by omega) (rfl : s109.pc = pcAt 109)
            (rfl : openingInstr 109 = .base (.BEQ .x7 .x0 (8#13)))
            (by rw [hr7_109, hmL]; change (1#64 : Word) ≠ 0#64; decide)
          let s110 := s109.setPC (pcAt 110)
          have hse32 : signExtend12 (32#12) = BitVec.ofNat 64 32 := by decide
          have h110 := step_ADDI (by omega) (rfl : s110.pc = pcAt 110)
            (rfl : openingInstr 110 = .base (.ADDI .x10 .x10 (32#12)))
          have hno : levelBase l + nodeOffset l (2 * q + 1) = levelBase l + 96 * q + 32 := by
            have hl0 : l ≠ 0 := by omega
            unfold nodeOffset; rw [if_neg hl0, gapOffset_odd]; omega
          let s111 := (s110.setReg .x10
            (BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l (2 * q + 1))))).setPC (pcAt 111)
          have h110' : OpenRuns s110 1 1 s111 := by
            have hv : s110.getReg .x10 + signExtend12 (32#12) =
                BitVec.ofNat 64 (4294971424 + (levelBase l + nodeOffset l (2 * q + 1))) := by
              change BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) + _ = _
              rw [hse32, bv64_ofNat_add]; congr 1; omega
            simpa only [hv, s111] using h110
          refine ⟨2, s111, 2 * q + 1, h109.trans h110', by omega, by rw [hmL]; rfl, by omega, rfl, rfl,
            fun r hr => by simp only [s111, s110, MachineState.getReg_setPC,
              getReg_setReg_ne' .x10 r (Ne.symm hr)], rfl⟩
        · have hmLf : mL = false := Bool.eq_false_iff.mpr hmL
          have h109 := step_BEQ_taken (by omega) (rfl : s109.pc = pcAt 109)
            (rfl : openingInstr 109 = .base (.BEQ .x7 .x0 (8#13)))
            (by rw [hr7_109, hmLf]; rfl)
            (by decide : pcAt 109 + signExtend13 (8#13) = pcAt 111)
          have hno : levelBase l + nodeOffset l (2 * q) = levelBase l + 96 * q := by
            have hl0 : l ≠ 0 := by omega
            unfold nodeOffset; rw [if_neg hl0, gapOffset_even]
          refine ⟨1, s109.setPC (pcAt 111), 2 * q, h109, by omega, by rw [hmLf]; rfl, by omega, rfl,
            ?_, fun _ _ => rfl, rfl⟩
          change BitVec.ofNat 64 (4294971424 + levelBase l + 96 * q) = _
          rw [hno, Nat.add_assoc]
      obtain ⟨n111, s111, childIdx, hr111, hn111, hchildEq, hchildLt, hpc111, hx10_111, hreg111, hmem111⟩ := hto111
      have hro111 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s111 := by
        intro a ha; change s111.mem a = _; rw [hmem111]; exact hro104 a ha
      have hpr111 : ProofPrefix s111 bytes := by
        intro j hj
        change extractByte (s111.mem _) _ = _; rw [hmem111]; exact hpr104 j hj
      have hx25_111 : s111.getReg .x25 = BitVec.ofNat 64 (10066334784 + bytes.length) := by
        rw [hreg111 .x25 (by decide),
          hpres109 .x25 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact inv.rx25
      have hno_bd : levelBase l + nodeOffset l childIdx + 30 ≤ 1342178336 := by
        have := nodeOffset_lt_treeBytes l childIdx (by omega) hchildLt; omega
      obtain ⟨s113, hrcopy, hpc113, hx25_113, hreg113, hro113, hpr113, hcap113⟩ :=
        openRuns_call_copy_to_proof (callIdx := 111) (copyBase := 145) (m := 15)
          (srcOff := levelBase l + nodeOffset l childIdx) (jOff := 136#21)
          (bytes := bytes) (chunk := bitsToBytes (tdNode trapdoor l childIdx) 30)
          (by omega) (by omega) (by omega) rfl (by decide) copy30_code rfl rfl
          hpc111 hx10_111 hx25_111
          (by have h1 := levelBase_even l (by omega); have h2 := nodeOffset_even l childIdx; omega) hno_bd
          inv.evenLen hlen_cap hro111 hpr111 (bitsToBytes_length _ 30)
          (fun j hj => chunk_tdNode trapdoor l childIdx 30 j (by omega) hj)
      have hb1 : bytes1 = bytes ++ bitsToBytes (tdNode trapdoor l childIdx) 30 := by
        change bytes ++ (if mL = mR then []
          else if !mL then bitsToBytes (tdNode trapdoor l (2 * q)) 30
          else bitsToBytes (tdNode trapdoor l (2 * q + 1)) 30) = _
        rw [if_neg hsame, hchildEq]
        by_cases hnot : (!mL) = true
        · rw [if_pos hnot, if_pos hnot]
        · rw [if_neg hnot, if_neg hnot]
      rw [hb1]
      have hpres113 : ∀ r, r ≠ .x1 → r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x10 → r ≠ .x11 → r ≠ .x25 →
          s113.getReg r = s.getReg r := fun r h1 h6 h7 h8 h10 h11 h25 => by
        rw [hreg113 r h1 h6 h25, hreg111 r h10, hpres109 r h6 h7 h8 h10 h11]
      refine ⟨5 + n111 + 33, s113, (hmid.trans hr111).trans hrcopy, by rw [hcpf]; omega, hpc113,
        by rw [hpres113 .x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx2,
        by rw [hpres113 .x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx9,
        by rw [hpres113 .x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx18,
        by rw [hpres113 .x19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx19,
        by rw [hpres113 .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx20,
        by rw [hpres113 .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx21,
        by rw [hpres113 .x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx22,
        by rw [hpres113 .x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx23,
        by rw [hpres113 .x24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx24,
        hx25_113,
        by rw [hpres113 .x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx26,
        by rw [hpres113 .x29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx29,
        by rw [hpres113 .x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact inv.rx30,
        by simp only [List.length_append, bitsToBytes_length]; have := inv.evenLen; omega,
        by simp only [List.length_append, bitsToBytes_length]; exact hlen_bd,
        hro113, hpr113, ?_, ?_⟩
      · intro idx hidx
        rw [hcap113 (4096 + capMarkOff l + idx) (by omega)]
        change extractByte (s111.mem _) _ = _; rw [hmem111]; exact hcur104 idx hidx
      · intro j hj
        rw [hcap113 (4096 + capMarkOff (l + 1) + j) (by omega)]
        change extractByte (s111.mem _) _ = _; rw [hmem111]; exact hnext104 j hj
  obtain ⟨n113, s113, hr113, hn113, hpc113, hx2, hx9, hx18, hx19, hx20, hx21, hx22, hx23,
      hx24, hx25, hx26, hx29, hx30, heven1, hlen1, hro113, hpr113, hcur113, hnext113⟩ := hto113
  have h113 := step_ADDI (by omega) hpc113 (rfl : openingInstr 113 = .base (.ADDI .x24 .x24 (1#12)))
  let s114 := (s113.setReg .x24 (BitVec.ofNat 64 (q + 1))).setPC (pcAt 114)
  have h113' : OpenRuns s113 1 1 s114 := by
    rw [hx24, hse1, bv64_ofNat_add] at h113; exact h113
  have hmkInv : ∀ pc, CapPairInv trapdoor positions step (q + 1) bytes1 (s114.setPC pc) := fun pc =>
    ⟨hx2, hx9, hx18, hx19, hx20, hx21, hx22, hx23, rfl, hx25, hx26, hx29, hx30,
     heven1, hlen1, hro113, hpr113, hcur113, hnext113⟩
  by_cases hmore : q + 1 < levelSize l / 2
  · have h114 := step_BNE_taken (by omega) (rfl : s114.pc = pcAt 114)
      (rfl : openingInstr 114 = .base (.BNE .x24 .x23 (8124#13)))
      (by change BitVec.ofNat 64 (q + 1) ≠ s113.getReg .x23
          rw [hx23]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 114 + signExtend13 (8124#13) = pcAt 97)
    exact ⟨7 + n113 + 1 + 1, s114.setPC (pcAt 97), ((hpre.trans hr113).trans h113').trans h114,
      by omega, by rw [if_pos hmore]; rfl, hmkInv (pcAt 97)⟩
  · have hdone : q + 1 = levelSize l / 2 := by omega
    have h114 := step_BNE_not_taken (by omega) (rfl : s114.pc = pcAt 114)
      (rfl : openingInstr 114 = .base (.BNE .x24 .x23 (8124#13)))
      (by change BitVec.ofNat 64 (q + 1) = s113.getReg .x23; rw [hx23, hdone])
    exact ⟨7 + n113 + 1 + 1, s114.setPC (pcAt 115), ((hpre.trans hr113).trans h113').trans h114,
      by omega, by rw [if_neg hmore]; rfl, hmkInv (pcAt 115)⟩

private theorem openRuns_cap_lvl_iter {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {step : Nat} {bytes : List Byte} {s : MachineState}
    (hstep : step < 9) (hpc : s.pc = pcAt 88)
    (inv : CapLvlInv trapdoor positions step bytes s) :
    let l := 15 + step
    let bytes1 := bytes ++ capLevelFrontierProof (tdNode trapdoor) positions l
    ∃ steps s1, OpenRuns s steps steps s1 ∧
      steps ≤ 9 + 10 * (levelSize l / 2) + 39 * levelFrontierCount positions l +
        (if levelSize l % 2 = 0 then 4 else 9) ∧
      s1.pc = (if step + 1 < 9 then pcAt 88 else pcAt 124) ∧
      CapLvlInv trapdoor positions (step + 1) bytes1 s1 := by
  intro l bytes1
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
  -- Header: 88..96 (9 steps)
  have haddr88 : s.getReg .x29 + signExtend12 (0#12) = BitVec.ofNat 64 (68719475936 + 32 * l) := by
    rw [inv.rx29, hse0, bv64_ofNat_add, Nat.add_zero]
  have h88 := step_LD (by omega) hpc (rfl : openingInstr 88 = .base (.LD .x18 .x29 (0#12)))
    (by rw [haddr88]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s89 := (s.setReg .x18 (BitVec.ofNat 64 (levelBase l))).setPC (pcAt 89)
  have h88' : OpenRuns s 1 1 s89 := by
    have hm := readOnly_getMem_data_base inv.ro l (by omega)
    simpa only [haddr88, hm, s89] using h88
  have h89 := step_ADD (by omega) (rfl : s89.pc = pcAt 89)
    (rfl : openingInstr 89 = .base (.ADD .x18 .x9 .x18))
  let s90 := (s89.setReg .x18 (BitVec.ofNat 64 (4294971424 + levelBase l))).setPC (pcAt 90)
  have h89' : OpenRuns s89 1 1 s90 := by
    have hr9 : s89.getReg .x9 = BitVec.ofNat 64 4294971424 := inv.rx9
    rw [hr9] at h89
    simpa only [show s89.getReg .x18 = BitVec.ofNat 64 (levelBase l) from rfl, bv64_ofNat_add, s90] using h89
  have haddr90 : s90.getReg .x29 + signExtend12 (8#12) = BitVec.ofNat 64 (68719475936 + 32 * l + 8) := by
    have hr29 : s90.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := inv.rx29
    rw [hr29, hse8, bv64_ofNat_add]
  have h90 := step_LD (by omega) (rfl : s90.pc = pcAt 90)
    (rfl : openingInstr 90 = .base (.LD .x19 .x29 (8#12)))
    (by rw [haddr90]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s91 := (s90.setReg .x19 (BitVec.ofNat 64 (levelSize l))).setPC (pcAt 91)
  have h90' : OpenRuns s90 1 1 s91 := by
    have hm : s90.getMem (BitVec.ofNat 64 (68719475936 + 32 * l + 8)) = BitVec.ofNat 64 (levelSize l) :=
      readOnly_getMem_data_size inv.ro l (by omega)
    simpa only [haddr90, hm, s91] using h90
  have haddr91 : s91.getReg .x29 + signExtend12 (16#12) = BitVec.ofNat 64 (68719475936 + 32 * l + 16) := by
    have hr29 : s91.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := inv.rx29
    rw [hr29, hse16, bv64_ofNat_add]
  have h91 := step_LD (by omega) (rfl : s91.pc = pcAt 91)
    (rfl : openingInstr 91 = .base (.LD .x20 .x29 (16#12)))
    (by rw [haddr91]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s92 := (s91.setReg .x20 (BitVec.ofNat 64 (capMarkOff l))).setPC (pcAt 92)
  have h91' : OpenRuns s91 1 1 s92 := by
    have hm : s91.getMem (BitVec.ofNat 64 (68719475936 + 32 * l + 16)) = BitVec.ofNat 64 (capMarkOff l) :=
      readOnly_getMem_data_markOff inv.ro l (by omega)
    simpa only [haddr91, hm, s92] using h91
  have h92 := step_ADD (by omega) (rfl : s92.pc = pcAt 92)
    (rfl : openingInstr 92 = .base (.ADD .x20 .x21 .x20))
  let s93 := (s92.setReg .x20 (BitVec.ofNat 64 (4096 + capMarkOff l))).setPC (pcAt 93)
  have h92' : OpenRuns s92 1 1 s93 := by
    have hr21 : s92.getReg .x21 = BitVec.ofNat 64 4096 := inv.rx21
    rw [hr21] at h92
    simpa only [show s92.getReg .x20 = BitVec.ofNat 64 (capMarkOff l) from rfl, bv64_ofNat_add, s93] using h92
  have haddr93 : s93.getReg .x29 + signExtend12 (48#12) =
      BitVec.ofNat 64 (68719475936 + 32 * (l + 1) + 16) := by
    have hr29 : s93.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) := inv.rx29
    rw [hr29, hse48, bv64_ofNat_add]; congr 1
  have h93 := step_LD (by omega) (rfl : s93.pc = pcAt 93)
    (rfl : openingInstr 93 = .base (.LD .x22 .x29 (48#12)))
    (by rw [haddr93]; exact accessValid_ofNat _ 8 (by omega) (by omega))
  let s94 := (s93.setReg .x22 (BitVec.ofNat 64 (capMarkOff (l + 1)))).setPC (pcAt 94)
  have h93' : OpenRuns s93 1 1 s94 := by
    have hm : s93.getMem (BitVec.ofNat 64 (68719475936 + 32 * (l + 1) + 16)) = BitVec.ofNat 64 (capMarkOff (l + 1)) :=
      readOnly_getMem_data_markOff inv.ro (l + 1) (by omega)
    simpa only [haddr93, hm, s94] using h93
  have h94 := step_ADD (by omega) (rfl : s94.pc = pcAt 94)
    (rfl : openingInstr 94 = .base (.ADD .x22 .x21 .x22))
  let s95 := (s94.setReg .x22 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1)))).setPC (pcAt 95)
  have h94' : OpenRuns s94 1 1 s95 := by
    have hr21 : s94.getReg .x21 = BitVec.ofNat 64 4096 := inv.rx21
    rw [hr21] at h94
    simpa only [show s94.getReg .x22 = BitVec.ofNat 64 (capMarkOff (l + 1)) from rfl,
      bv64_ofNat_add, s95] using h94
  have h95 := step_SRLI (by omega) (rfl : s95.pc = pcAt 95)
    (rfl : openingInstr 95 = .base (.SRLI .x23 .x19 (1#6)))
  let s96 := (s95.setReg .x23 (BitVec.ofNat 64 (levelSize l / 2))).setPC (pcAt 96)
  have h95' : OpenRuns s95 1 1 s96 := by
    have hv : s95.getReg .x19 >>> (1#6 : BitVec 6).toNat = BitVec.ofNat 64 (levelSize l / 2) := by
      change BitVec.ofNat 64 (levelSize l) >>> 1 = _
      rw [bv64_ushr _ 1 (by omega), Nat.shiftRight_eq_div_pow]
    simpa only [hv, s96] using h95
  have h96 := step_ADDI (by omega) (rfl : s96.pc = pcAt 96)
    (rfl : openingInstr 96 = .base (.ADDI .x24 .x0 (0#12)))
  let s97 := (s96.setReg .x24 (BitVec.ofNat 64 0)).setPC (pcAt 97)
  have h96' : OpenRuns s96 1 1 s97 := by
    have hv : s96.getReg .x0 + signExtend12 (0#12) = BitVec.ofNat 64 0 := by
      change (0#64 : Word) + signExtend12 (0#12) = BitVec.ofNat 64 0; decide
    simpa only [hv, s97] using h96
  have hhdr : OpenRuns s 9 9 s97 :=
    (((((((h88'.trans h89').trans h90').trans h91').trans h92').trans h93').trans h94').trans h95').trans h96'
  have hpairInv0 : CapPairInv trapdoor positions step 0 bytes s97 :=
    ⟨inv.rx2, inv.rx9, rfl, rfl, rfl, inv.rx21, rfl, rfl, rfl, inv.rx25, inv.rx26, inv.rx29, inv.rx30,
     inv.evenLen, by simpa using inv.boundLen, inv.ro, inv.proof, inv.capMarks,
     fun _ hj => absurd hj (Nat.not_lt_zero _)⟩
  -- Pair loop induction: q = 0 .. levelSize l / 2
  have hpairLoop : ∀ q ≤ levelSize l / 2,
      let cur := bytes ++ (List.range q).flatMap (capPairBytes trapdoor positions l)
      ∃ steps sq, OpenRuns s97 steps steps sq ∧
        steps ≤ 10 * q + 39 * (∑ j ∈ Finset.range q, capPairFrontier positions l j) ∧
        sq.pc = (if q < levelSize l / 2 then pcAt 97 else pcAt 115) ∧
        CapPairInv trapdoor positions step q cur sq := by
    intro q hq
    induction q with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Nat.mul_zero,
        Finset.sum_range_zero, Nat.add_zero]
      exact ⟨0, s97, OpenRuns.refl s97, Nat.le_refl 0, by rw [if_pos (by omega : 0 < levelSize l / 2)]; rfl, hpairInv0⟩
    | succ q ih =>
      obtain ⟨st, sq, hrq, hstq, hpcq, invq⟩ := ih (by omega)
      have hpcq' : sq.pc = pcAt 97 := by simpa only [show q < levelSize l / 2 by omega, ite_true] using hpcq
      obtain ⟨st1, sq1, hr1, hst1, hpc1, inv1⟩ :=
        openRuns_cap_pair_step hstep (show q < levelSize (15 + step) / 2 from by change q < levelSize l / 2; omega) hpcq' invq
      have hst1' : st1 ≤ 10 + 39 * capPairFrontier positions l q := hst1
      have happ : bytes ++ (List.range q).flatMap (capPairBytes trapdoor positions l) ++
            capPairBytes trapdoor positions l q =
          bytes ++ (List.range (q + 1)).flatMap (capPairBytes trapdoor positions l) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      have inv1' : CapPairInv trapdoor positions step (q + 1)
          (bytes ++ (List.range q).flatMap (capPairBytes trapdoor positions l) ++
            capPairBytes trapdoor positions l q) sq1 := inv1
      rw [happ] at inv1'
      refine ⟨st + st1, sq1, hrq.trans hr1, ?_, hpc1, inv1'⟩
      rw [Finset.sum_range_succ]; omega
  obtain ⟨stPairs, s115, hrPairs, hstPairs, hpc115, inv115⟩ :=
    hpairLoop (levelSize l / 2) (Nat.le_refl _)
  have hpc115' : s115.pc = pcAt 115 := by simpa only [Nat.lt_irrefl, ite_false] using hpc115
  rw [sum_capPairFrontier_eq] at hstPairs
  have hbytes1_eq : bytes ++ (List.range (levelSize l / 2)).flatMap (capPairBytes trapdoor positions l) =
      bytes1 := rfl
  rw [hbytes1_eq] at inv115
  have hcur115 : CapLevelMarks s115 positions l := inv115.curMarks
  have hbound115 : bytes1.length ≤ 502 * positions.card +
      30 * (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (15 + k)) := by
    have h1 : bytes1.length ≤ 502 * positions.card +
        30 * ((∑ k ∈ Finset.range step, levelFrontierCount positions (15 + k)) +
              (∑ j ∈ Finset.range (levelSize (15 + step) / 2), capPairFrontier positions (15 + step) j)) :=
      inv115.boundLen
    rw [sum_capPairFrontier_eq] at h1
    rw [Finset.sum_range_succ]; exact h1
  -- Odd-promotion check: 115..121 → pcAt 122
  have h115 := step_ANDI (by omega) hpc115' (rfl : openingInstr 115 = .base (.ANDI .x6 .x19 (1#12)))
  let s116 := (s115.setReg .x6 (BitVec.ofNat 64 (levelSize l % 2))).setPC (pcAt 116)
  have h115' : OpenRuns s115 1 1 s116 := by
    rw [inv115.rx19, bv64_and1 (levelSize l) (by omega)] at h115; exact h115
  have hto122 : ∃ n122 s122, OpenRuns s116 n122 n122 s122 ∧
      n122 ≤ (if levelSize l % 2 = 0 then 1 else 6) ∧
      s122.pc = pcAt 122 ∧
      s122.getReg .x2 = BitVec.ofNat 64 68719475936 ∧
      s122.getReg .x9 = BitVec.ofNat 64 4294971424 ∧
      s122.getReg .x21 = BitVec.ofNat 64 4096 ∧
      s122.getReg .x25 = BitVec.ofNat 64 (10066334784 + bytes1.length) ∧
      s122.getReg .x26 = BitVec.ofNat 64 10066334784 ∧
      s122.getReg .x29 = BitVec.ofNat 64 (68719475936 + 32 * l) ∧
      s122.getReg .x30 = BitVec.ofNat 64 (68719475936 + 32 * 24) ∧
      ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s122 ∧
      ProofPrefix s122 bytes1 ∧
      CapLevelMarks s122 positions (l + 1) := by
    by_cases heven_sz : levelSize l % 2 = 0
    · have h116 := step_BEQ_taken (by omega) (rfl : s116.pc = pcAt 116)
        (rfl : openingInstr 116 = .base (.BEQ .x6 .x0 (24#13)))
        (by change BitVec.ofNat 64 (levelSize l % 2) = 0#64; rw [heven_sz])
        (by decide : pcAt 116 + signExtend13 (24#13) = pcAt 122)
      refine ⟨1, s116.setPC (pcAt 122), h116, by rw [if_pos heven_sz], rfl,
        inv115.rx2, inv115.rx9, inv115.rx21, inv115.rx25, inv115.rx26, inv115.rx29, inv115.rx30,
        inv115.ro, inv115.proof, ?_⟩
      intro idx hidx
      exact inv115.nextMarks idx (by omega)
    · have h116 := step_BEQ_not_taken (by omega) (rfl : s116.pc = pcAt 116)
        (rfl : openingInstr 116 = .base (.BEQ .x6 .x0 (24#13)))
        (by change BitVec.ofNat 64 (levelSize l % 2) ≠ BitVec.ofNat 64 0
            exact bv64_ofNat_ne (by omega) (by decide) heven_sz)
      let s117 := s116.setPC (pcAt 117)
      have h117 := step_SLLI (by omega) (rfl : s117.pc = pcAt 117)
        (rfl : openingInstr 117 = .base (.SLLI .x7 .x23 (1#6)))
      let s118 := (s117.setReg .x7 (BitVec.ofNat 64 (2 * (levelSize l / 2)))).setPC (pcAt 118)
      have h117' : OpenRuns s117 1 1 s118 := by
        have hr23 : s117.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) := inv115.rx23
        have hv : s117.getReg .x23 <<< (1#6 : BitVec 6).toNat =
            BitVec.ofNat 64 (2 * (levelSize l / 2)) := by
          rw [hr23]; change BitVec.ofNat 64 (levelSize l / 2) <<< 1 = _
          rw [bv64_shl]; congr 1; omega
        simpa only [hv, s118] using h117
      have h118 := step_ADD (by omega) (rfl : s118.pc = pcAt 118)
        (rfl : openingInstr 118 = .base (.ADD .x7 .x20 .x7))
      let s119 := (s118.setReg .x7 (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * (levelSize l / 2)))).setPC
        (pcAt 119)
      have h118' : OpenRuns s118 1 1 s119 := by
        have hr20 : s118.getReg .x20 = BitVec.ofNat 64 (4096 + capMarkOff l) := inv115.rx20
        rw [hr20] at h118
        simpa only [show s118.getReg .x7 = BitVec.ofNat 64 (2 * (levelSize l / 2)) from rfl,
          bv64_ofNat_add, s119] using h118
      have haddr119 : s119.getReg .x7 + signExtend12 (0#12) =
          BitVec.ofNat 64 (4096 + capMarkOff l + 2 * (levelSize l / 2)) := by
        change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
      have h119 := step_LBU (by omega) (rfl : s119.pc = pcAt 119)
        (rfl : openingInstr 119 = .base (.LBU .x8 .x7 (0#12)))
        (by rw [haddr119]; exact accessValid_ofNat _ 1 (by omega) (by omega))
      set mProm := capMark positions l (2 * (levelSize l / 2))
      let s120 := (s119.setReg .x8 (if mProm then 1#64 else 0#64)).setPC (pcAt 120)
      have h119' : OpenRuns s119 1 1 s120 := by
        have hb : s119.getByte (BitVec.ofNat 64 (4096 + capMarkOff l + 2 * (levelSize l / 2))) =
            if mProm then 1#8 else 0#8 := hcur115 (2 * (levelSize l / 2)) (by omega)
        simpa only [haddr119, hb, bool_byte_zeroExtend mProm, s120] using h119
      have h120 := step_ADD (by omega) (rfl : s120.pc = pcAt 120)
        (rfl : openingInstr 120 = .base (.ADD .x7 .x22 .x23))
      let s121 := (s120.setReg .x7 (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + levelSize l / 2))).setPC
        (pcAt 121)
      have h120' : OpenRuns s120 1 1 s121 := by
        have hr22 : s120.getReg .x22 = BitVec.ofNat 64 (4096 + capMarkOff (l + 1)) := inv115.rx22
        have hr23 : s120.getReg .x23 = BitVec.ofNat 64 (levelSize l / 2) := inv115.rx23
        rw [hr22, hr23, bv64_ofNat_add] at h120; exact h120
      have haddr121 : s121.getReg .x7 + signExtend12 (0#12) =
          BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + levelSize l / 2) := by
        change BitVec.ofNat 64 _ + _ = _; rw [hse0, bv64_ofNat_add, Nat.add_zero]
      have h121 := step_SB (by omega) (rfl : s121.pc = pcAt 121)
        (rfl : openingInstr 121 = .base (.SB .x7 .x8 (0#12)))
        (by rw [haddr121]; exact accessValid_ofNat _ 1 (by omega) (by omega))
      let s122 := (s121.setByte (BitVec.ofNat 64 (4096 + capMarkOff (l + 1) + levelSize l / 2))
        (if mProm then 1#8 else 0#8)).setPC (pcAt 122)
      have h121' : OpenRuns s121 1 1 s122 := by
        simpa only [haddr121, show s121.getReg .x8 = if mProm then 1#64 else 0#64 from rfl,
          bool_word_truncate8 mProm, s122] using h121
      have hcard := positions_card_le positions
      have hcap171 := cap_frontier_le_171 positions
      have hfront_le : (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (15 + k)) ≤ 171 := by
        have h1 : (∑ k ∈ Finset.range (step + 1), levelFrontierCount positions (15 + k)) ≤
            capFrontierCount positions := by
          unfold capFrontierCount
          exact sum_range_le_of_le (fun k => levelFrontierCount positions (15 + k)) (by omega)
        omega
      have hpres122 : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → s122.getReg r = s115.getReg r :=
        fun r h6 h7 h8 => by
          simp only [s122, s121, s120, s119, s118, s117, s116,
            MachineState.getReg_setPC, getReg_setByte,
            getReg_setReg_ne' .x7 r (Ne.symm h7),
            getReg_setReg_ne' .x8 r (Ne.symm h8),
            getReg_setReg_ne' .x6 r (Ne.symm h6)]
      refine ⟨6, s122, ((((h116.trans h117').trans h118').trans h119').trans h120').trans h121',
        by rw [if_neg heven_sz], rfl,
        by rw [hpres122 .x2 (by decide) (by decide) (by decide)]; exact inv115.rx2,
        by rw [hpres122 .x9 (by decide) (by decide) (by decide)]; exact inv115.rx9,
        by rw [hpres122 .x21 (by decide) (by decide) (by decide)]; exact inv115.rx21,
        by rw [hpres122 .x25 (by decide) (by decide) (by decide)]; exact inv115.rx25,
        by rw [hpres122 .x26 (by decide) (by decide) (by decide)]; exact inv115.rx26,
        by rw [hpres122 .x29 (by decide) (by decide) (by decide)]; exact inv115.rx29,
        by rw [hpres122 .x30 (by decide) (by decide) (by decide)]; exact inv115.rx30,
        ?_, ?_, ?_⟩
      · intro a ha; simp only [s122, MachineState.getMem_setPC]
        exact readOnly_setByte_cap (4096 + capMarkOff (l + 1) + levelSize l / 2) _ inv115.ro
          (by omega) (by omega) a ha
      · intro j hj; simp only [s122, getByte_setPC]
        exact proofPrefix_setByte_cap (4096 + capMarkOff (l + 1) + levelSize l / 2) _ inv115.proof
          (by omega) (by omega) (by omega) j hj
      · intro idx hidx
        simp only [s122, getByte_setPC, set_byte_read]
        by_cases hlast : idx = levelSize l / 2
        · subst hlast
          have hge : ¬ (2 * (levelSize l / 2) + 1 < levelSize l) := by omega
          have hlt : 2 * (levelSize l / 2) < levelSize l := by omega
          rw [if_pos rfl]
          change (if capMark positions l (2 * (levelSize l / 2)) then 1#8 else 0#8) = _
          rw [capMark_succ positions l (levelSize l / 2) (by omega), if_neg hge, if_pos hlt]
        · rw [if_neg (bv64_ofNat_ne (by omega) (by omega) (by omega))]
          exact inv115.nextMarks idx (by omega)
  obtain ⟨n122, s122, hr122, hn122, hpc122, hx2, hx9, hx21, hx25, hx26, hx29, hx30,
      hro122, hpr122, hcm122⟩ := hto122
  -- Latch: 122..123
  have h122 := step_ADDI (by omega) hpc122 (rfl : openingInstr 122 = .base (.ADDI .x29 .x29 (32#12)))
  let s123 := (s122.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * (15 + (step + 1))))).setPC (pcAt 123)
  have h122' : OpenRuns s122 1 1 s123 := by
    have hv : s122.getReg .x29 + signExtend12 (32#12) =
        BitVec.ofNat 64 (68719475936 + 32 * (15 + (step + 1))) := by
      rw [hx29, hse32, bv64_ofNat_add]; congr 1
    simpa only [hv, s123] using h122
  have hmkInv : ∀ pc, CapLvlInv trapdoor positions (step + 1) bytes1 (s123.setPC pc) := fun pc =>
    ⟨hx2, hx9, hx21, hx25, hx26, rfl, hx30, inv115.evenLen, hbound115, hro122, hpr122,
     by rw [show 15 + (step + 1) = l + 1 by omega]; exact hcm122⟩
  have hstep_bd : 9 + stPairs + 1 + n122 + 1 + 1 ≤
      9 + 10 * (levelSize l / 2) + 39 * levelFrontierCount positions l +
      (if levelSize l % 2 = 0 then 4 else 9) := by
    by_cases hmod : levelSize l % 2 = 0
    · rw [if_pos hmod] at hn122 ⊢; omega
    · rw [if_neg hmod] at hn122 ⊢; omega
  by_cases hmore : step + 1 < 9
  · have h123 := step_BNE_taken (by omega) (rfl : s123.pc = pcAt 123)
      (rfl : openingInstr 123 = .base (.BNE .x29 .x30 (8052#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (15 + (step + 1))) ≠ s122.getReg .x30
          rw [hx30]; exact bv64_ofNat_ne (by omega) (by omega) (by omega))
      (by decide : pcAt 123 + signExtend13 (8052#13) = pcAt 88)
    exact ⟨9 + stPairs + 1 + n122 + 1 + 1, s123.setPC (pcAt 88),
      ((((hhdr.trans hrPairs).trans h115').trans hr122).trans h122').trans h123,
      hstep_bd, by rw [if_pos hmore]; rfl, hmkInv (pcAt 88)⟩
  · have hdone : 15 + (step + 1) = 24 := by omega
    have h123 := step_BNE_not_taken (by omega) (rfl : s123.pc = pcAt 123)
      (rfl : openingInstr 123 = .base (.BNE .x29 .x30 (8052#13)))
      (by change BitVec.ofNat 64 (68719475936 + 32 * (15 + (step + 1))) = s122.getReg .x30
          rw [hx30, hdone])
    exact ⟨9 + stPairs + 1 + n122 + 1 + 1, s123.setPC (pcAt 124),
      ((((hhdr.trans hrPairs).trans h115').trans hr122).trans h122').trans h123,
      hstep_bd, by rw [if_neg hmore]; rfl, hmkInv (pcAt 124)⟩

private theorem cap_const_cycles_sum :
    (∑ step ∈ Finset.range 9,
      (9 + 10 * (levelSize (15 + step) / 2) + if levelSize (15 + step) % 2 = 0 then 4 else 9)) =
      3547 := by
  decide

private theorem openRuns_cap_all {trapdoor : BitVec (8 * submission.sizes.trapdoor)}
    {positions : Positions} {recBytes : List Byte} {s86 : MachineState}
    (hpc : s86.pc = pcAt 86)
    (hx2 : s86.getReg .x2 = BitVec.ofNat 64 68719475936)
    (hx9 : s86.getReg .x9 = BitVec.ofNat 64 4294971424)
    (hx21 : s86.getReg .x21 = BitVec.ofNat 64 4096)
    (hx25 : s86.getReg .x25 = BitVec.ofNat 64 (10066334784 + recBytes.length))
    (hx26 : s86.getReg .x26 = BitVec.ofNat 64 10066334784)
    (heven : recBytes.length % 2 = 0)
    (hbd : recBytes.length ≤ 502 * positions.card)
    (hro : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s86)
    (hpr : ProofPrefix s86 recBytes)
    (hcap15 : CapLevelMarks s86 positions 15) :
    let allBytes := recBytes ++ capFrontierProof (tdNode trapdoor) positions
    ∃ steps s124, OpenRuns s86 steps steps s124 ∧
      steps ≤ 10218 ∧
      s124.pc = pcAt 124 ∧
      s124.getReg .x25 = BitVec.ofNat 64 (10066334784 + allBytes.length) ∧
      s124.getReg .x26 = BitVec.ofNat 64 10066334784 ∧
      ProofPrefix s124 allBytes := by
  intro allBytes
  have hse480 : signExtend12 (480#12) = BitVec.ofNat 64 480 := by decide
  have hse768 : signExtend12 (768#12) = BitVec.ofNat 64 768 := by decide
  have h86 := step_ADDI (by omega) hpc (rfl : openingInstr 86 = .base (.ADDI .x29 .x2 (480#12)))
  let s87 := (s86.setReg .x29 (BitVec.ofNat 64 (68719475936 + 32 * 15))).setPC (pcAt 87)
  have h86' : OpenRuns s86 1 1 s87 := by
    rw [hx2, hse480, bv64_ofNat_add] at h86; exact h86
  have h87 := step_ADDI (by omega) (rfl : s87.pc = pcAt 87)
    (rfl : openingInstr 87 = .base (.ADDI .x30 .x2 (768#12)))
  let s88 := (s87.setReg .x30 (BitVec.ofNat 64 (68719475936 + 32 * 24))).setPC (pcAt 88)
  have h87' : OpenRuns s87 1 1 s88 := by
    have hr2 : s87.getReg .x2 = BitVec.ofNat 64 68719475936 := hx2
    rw [hr2, hse768, bv64_ofNat_add] at h87; exact h87
  have hinv0 : CapLvlInv trapdoor positions 0 recBytes s88 :=
    ⟨hx2, hx9, hx21, hx25, hx26, rfl, rfl, heven, by simpa using hbd, hro, hpr, hcap15⟩
  have hloop : ∀ k ≤ 9,
      let cur := recBytes ++ (List.range k).flatMap (fun step =>
        capLevelFrontierProof (tdNode trapdoor) positions (15 + step))
      ∃ steps sk, OpenRuns s88 steps steps sk ∧
        steps ≤ (∑ step ∈ Finset.range k,
          (9 + 10 * (levelSize (15 + step) / 2) + if levelSize (15 + step) % 2 = 0 then 4 else 9)) +
          39 * (∑ step ∈ Finset.range k, levelFrontierCount positions (15 + step)) ∧
        sk.pc = (if k < 9 then pcAt 88 else pcAt 124) ∧
        CapLvlInv trapdoor positions k cur sk := by
    intro k hk
    induction k with
    | zero =>
      dsimp only
      simp only [List.range_zero, List.flatMap_nil, List.append_nil, Finset.sum_range_zero,
        Nat.mul_zero, Nat.add_zero]
      exact ⟨0, s88, OpenRuns.refl s88, Nat.le_refl 0, by rw [if_pos (by omega : 0 < 9)]; rfl, hinv0⟩
    | succ k ih =>
      obtain ⟨st, sk, hrk, hstk, hpck, invk⟩ := ih (by omega)
      have hpck' : sk.pc = pcAt 88 := by simpa only [show k < 9 by omega, ite_true] using hpck
      obtain ⟨st1, sk1, hr1, hst1, hpc1, inv1⟩ := openRuns_cap_lvl_iter (by omega) hpck' invk
      have happ : recBytes ++ (List.range k).flatMap (fun step =>
            capLevelFrontierProof (tdNode trapdoor) positions (15 + step)) ++
            capLevelFrontierProof (tdNode trapdoor) positions (15 + k) =
          recBytes ++ (List.range (k + 1)).flatMap (fun step =>
            capLevelFrontierProof (tdNode trapdoor) positions (15 + step)) := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.append_assoc]
      rw [happ] at inv1
      refine ⟨st + st1, sk1, hrk.trans hr1, ?_, hpc1, inv1⟩
      rw [Finset.sum_range_succ, Finset.sum_range_succ]; omega
  obtain ⟨stCap, s124, hrCap, hstCap, hpc124, inv124⟩ := hloop 9 (Nat.le_refl 9)
  have hpc124' : s124.pc = pcAt 124 := by simpa only [Nat.lt_irrefl, ite_false] using hpc124
  have hconst := cap_const_cycles_sum
  have hcap171 := cap_frontier_le_171 positions
  have hfront_eq : (∑ step ∈ Finset.range 9, levelFrontierCount positions (15 + step)) =
      capFrontierCount positions := rfl
  rw [hconst, hfront_eq] at hstCap
  have hall_eq : recBytes ++ (List.range 9).flatMap (fun step =>
      capLevelFrontierProof (tdNode trapdoor) positions (15 + step)) = allBytes := rfl
  rw [hall_eq] at inv124
  exact ⟨2 + stCap, s124, (h86'.trans h87').trans hrCap, by omega, hpc124',
    inv124.rx25, inv124.rx26, inv124.proof⟩

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
      (positions.card = BATCH → exec.cycles ≤ 105867) := by
  have hsteps : submission.steps .opening = 68719476736 := rfl
  rw [submission_run_opening submission trapdoor positions]
  by_cases hempty : positions.card = 0
  · obtain ⟨s5, hr5, hpc5, _, _, _, hx25, hx26, hx27, _⟩ := openRuns_entry_prefix trapdoor positions
    have h5 := step_BEQ_taken (by omega) hpc5
      (rfl : openingInstr 5 = .base (.BEQ .x27 .x0 (476#13)))
      (by rw [hx27, hempty]; rfl)
      (by decide : pcAt 5 + signExtend13 (476#13) = pcAt 124)
    let s124 := s5.setPC (pcAt 124)
    obtain ⟨sHalt, hrepi, hpcH, hx5H, hx10H, hx11H, _⟩ :=
      openRuns_epilogue (proofLen := 0) (rfl : s124.pc = pcAt 124)
        (by rw [Nat.add_zero]; exact hx25) hx26
    have hexec := OpenRuns.halt (totalFuel := submission.steps .opening)
      ((hr5.trans h5).trans hrepi) hpcH hx5H hx10H (by rw [hsteps]; omega)
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
    obtain ⟨s19, hr19, hpc19, hx2, hx9, hx18, hx19, hx20, hx21, hx24, hx25, hx26, hx27, hmem19⟩ :=
      openRuns_entry_nonzero trapdoor positions hempty
    have hro19 : ReadOnlyPreserved (submission.initialState .opening (trapdoor, positions)) s19 := by
      intro a _; change s19.mem a = _; rw [hmem19]; rfl
    have hinv0 : RecInv trapdoor positions 0 [] s19 :=
      ⟨hx2, hx9, hx18, hx19, hx20, hx21, by simpa using hx24, by simpa using hx25, hx26,
       by simpa using hx27, by decide, hro19,
       fun _ hj => absurd hj (Nat.not_lt_zero _),
       fun c hc => by
         change extractByte (s19.mem _) _ = _
         rw [hmem19]
         have hz := opening_initial_zero_low trapdoor positions (4096 + c) (by omega)
         have hfalse : capMark15Prefix positions 0 c = false := by
           simp [capMark15Prefix]
         rw [hfalse, if_neg Bool.false_ne_true]; exact hz⟩
    obtain ⟨stRec, cyRec, s86, hrRec, hstRec, hcyRec, hpc86, hx2_86, hx9_86, hx21_86, hx25_86,
        hx26_86, heven86, hbd86, hro86, hpr86, hcap15⟩ :=
      openRuns_rec_all hpos hpc19 hinv0
    obtain ⟨stCap, s124, hrCap, hstCap, hpc124, hx25_124, hx26_124, hpr124⟩ :=
      openRuns_cap_all hpc86 hx2_86 hx9_86 hx21_86 hx25_86 hx26_86 heven86 hbd86 hro86 hpr86 hcap15
    have href_eq : (positions.sort (· ≤ ·)).flatMap
          (recordProof (tdNode trapdoor) (tdSalt trapdoor)) ++
          capFrontierProof (tdNode trapdoor) positions =
        referenceProof (tdNode trapdoor) (tdSalt trapdoor) positions := by
      unfold referenceProof; rw [if_neg hempty]
    rw [href_eq] at hx25_124 hpr124
    obtain ⟨sHalt, hrepi, hpcH, hx5H, hx10H, hx11H, hmemH⟩ :=
      openRuns_epilogue hpc124 hx25_124 hx26_124
    have htot := ((hr19.trans hrRec).trans hrCap).trans hrepi
    have hfuel : 19 + stRec + stCap + 3 + 1 ≤ submission.steps .opening := by rw [hsteps]; omega
    have hexec := OpenRuns.halt (totalFuel := submission.steps .opening) htot hpcH hx5H hx10H hfuel
    have hlen_cap := referenceProof_length_le_cap (tdNode trapdoor) (tdSalt trapdoor) positions
    change _ ≤ 8422172696 at hlen_cap
    refine ⟨{ exit := .success, state := sHalt, cycles := 19 + cyRec + stCap + 3 + 1, oracleCalls := 0 },
      hexec, rfl, rfl, ?_, ?_, ?_⟩
    · rw [hx11H, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · intro j hj
      change extractByte (sHalt.mem _) _ = _
      rw [hmemH]
      exact hpr124 j hj
    · intro hbatch
      change positions.card = 128 at hbatch
      change 19 + cyRec + stCap + 3 + 1 ≤ 105867
      omega

end CommitGolfCandidate
